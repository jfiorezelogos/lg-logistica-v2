# backend.py
# backend.py
from __future__ import annotations

import json
import logging
import os
import random
import threading
import time
import traceback
import unicodedata
import uuid
from calendar import monthrange
from collections import Counter, defaultdict
from collections.abc import Callable, Iterable, Mapping, MutableMapping, Sequence
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from contextlib import suppress
from datetime import UTC, date, datetime, time as dtime, timedelta
from decimal import ROUND_HALF_UP, Decimal, InvalidOperation
from json import JSONDecodeError
from typing import Any, Protocol, TypedDict, cast, overload
from uuid import uuid4
from zoneinfo import ZoneInfo

import certifi
import pandas as pd
import requests
import urllib3
from colorama import init
from dateutil.parser import parse as parse_date
from unidecode import unidecode

from common.errors import UserError
from common.http_client import http_get
from common.settings import settings

# Inicializa colorama no console (efeito só em TTY/CLI)
init(autoreset=True)

# SSL e warnings HTTP (efeito de processo, não-UI)
os.environ["SSL_CERT_FILE"] = certifi.where()
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# Config de APIs externas (backend)
BASE_URL_GURU = "https://digitalmanager.guru/api/v2"
HEADERS_GURU = {
    "Authorization": f"Bearer {settings.API_KEY_GURU}",
    "Content-Type": "application/json",
}

# ===================== CONFIGURAÇÕES (backend) =====================


class _CliCfg(Protocol):
    input_path: str
    output_dir: str
    dry_run: bool


def caminho_base() -> str:
    """Diretório onde está o main.py (independe do cwd)."""
    return os.path.dirname(os.path.abspath(__file__))


def _load_payload_from_arg(value: str) -> dict[Any, Any]:
    """Aceita JSON inline OU caminho para arquivo .json/.yaml/.yml contendo a config.

    Se for caminho, tentamos carregar; caso contrário, tratamos como JSON string.
    """
    try:
        is_path = os.path.exists(value)

        if is_path:
            # arquivo
            with open(value, encoding="utf-8") as f:
                txt = f.read()
            try:
                parsed: Any = json.loads(txt)
            except json.JSONDecodeError as e:
                raise UserError(
                    "Arquivo de configuração não é JSON válido",
                    code="BAD_JSON_FILE",
                    data={"path": value},
                ) from e
        else:
            # JSON inline
            parsed = json.loads(value)

        if not isinstance(parsed, dict):
            if is_path:
                raise UserError(
                    "Arquivo de configuração deve ser um objeto JSON",
                    code="BAD_JSON_FILE",
                    data={"path": value},
                )
            raise UserError(
                "Configuração inline deve ser um objeto JSON",
                code="BAD_JSON",
                data={"value": value},
            )

        return cast(dict[Any, Any], parsed)

    except json.JSONDecodeError as e:
        # fallback geral para JSON inline inválido
        raise UserError("JSON inválido em --config", code="BAD_JSON", data={"value": value}) from e


# Recursos de sincronização/limite (backend)
limite_gpt = threading.Semaphore(4)
controle_rate_limit = {"lock": threading.Lock(), "ultimo_acesso": time.time()}

# Logging básico compartilhado (sem UI)
log_path = os.path.join(caminho_base(), "sistema.log")
formatter = logging.Formatter("[%(asctime)s] %(levelname)s: %(message)s", datefmt="%H:%M:%S")
logger = logging.getLogger("logistica")
logger.setLevel(logging.INFO)

if not logger.handlers:
    # 📁 Log em arquivo
    file_handler = logging.FileHandler(log_path, encoding="utf-8")
    file_handler.setFormatter(formatter)
    logger.addHandler(file_handler)

    # 🖥️ Log no console
    console_handler = logging.StreamHandler()
    console_handler.setFormatter(formatter)
    logger.addHandler(console_handler)

# Estado/modelos de dados (backend)
dados: dict[str, Any] = {}
estado = {
    "transacoes_obtidas": False,
    "linhas_planilha": [],
    "numero_pedido_bling": None,
    "skus_info": {},
    "cancelador_global": threading.Event(),
}
linhas_planilha: list[dict[str, Any]] = []
total_etapas = 0
progresso_total = 0
transacoes_obtidas = False
transportadoras_var: dict[str, Any] = {}
transportadoras_lista = ["CORREIOS", "GFL", "GOL", "JET", "LOG"]
skus_path = os.path.join(caminho_base(), "skus.json")
transacoes: list[dict[str, Any]] = []
enderecos_para_revisar: list[dict[str, Any]] = []

# Inicializa o dicionário de SKUs a partir de arquivo JSON.
if os.path.exists(skus_path):
    with open(skus_path, encoding="utf-8") as f:
        skus_info = json.load(f)
else:
    skus_info = {
        "Leviatã, de Thomas Hobbes": {"sku": "L002A", "peso": 1.10},
        "O Príncipe, Maquiavél": {"sku": "B002A", "peso": 0.70},
        "Isagoge, de Porfírio": {"sku": "B001A", "peso": 0.70},
        "Virgílio, o Pai do Ocidente": {"sku": "L001A", "peso": 0.50},
        "Heráclito": {"sku": "B003A", "peso": 0.70},
    }
    with open(skus_path, "w", encoding="utf-8") as f:
        json.dump(skus_info, f, indent=4, ensure_ascii=False)

# Helpers datetime
TZ_APP = ZoneInfo("America/Sao_Paulo")


def utc_now() -> datetime:
    return datetime.now(UTC)


def local_now() -> datetime:
    return datetime.now(TZ_APP)


def aware_local(
    y: int,
    m: int,
    d: int,
    hh: int = 0,
    mm: int = 0,
    ss: int = 0,
    us: int = 0,
) -> datetime:
    return datetime(y, m, d, hh, mm, ss, us, tzinfo=TZ_APP)


def aware_utc(
    y: int,
    m: int,
    d: int,
    hh: int = 0,
    mm: int = 0,
    ss: int = 0,
    us: int = 0,
) -> datetime:
    return datetime(y, m, d, hh, mm, ss, us, tzinfo=UTC)


def from_ts_utc(ts: float) -> datetime:
    if ts > 1e12:  # ms -> s
        ts /= 1000.0
    return datetime.fromtimestamp(ts, tz=UTC)


def ensure_aware_local(dt: datetime) -> datetime:
    return dt if dt.tzinfo else dt.replace(tzinfo=TZ_APP)


def ensure_aware_utc(dt: datetime) -> datetime:
    return dt if dt.tzinfo else dt.replace(tzinfo=UTC)


# Serializações para endpoints (NÃO muda nomes dos parâmetros!)
def to_rfc3339_z(dt: datetime) -> str:
    """Yyyy-mm-ddTHH:MM:SSZ (UTC)"""
    return ensure_aware_utc(dt).astimezone(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")


def to_date_yyyy_mm_dd(dt: datetime) -> str:
    """Yyyy-mm-dd (sem tz), quando o endpoint espera só data."""
    return ensure_aware_local(dt).date().isoformat()


def to_br_date(ddmmyyyy_dt: datetime) -> str:
    """Dd/mm/yyyy para UI/relatórios."""
    return ensure_aware_local(ddmmyyyy_dt).strftime("%d/%m/%Y")


# ================= Helpers de data (UTC aware) =================


def _aware_utc(dt: datetime) -> datetime:
    """Garante datetime UTC-aware (nunca retorna None)."""
    return dt.replace(tzinfo=UTC) if dt.tzinfo is None else dt.astimezone(UTC)


@overload
def _as_dt(value: datetime) -> datetime: ...
@overload
def _as_dt(value: date) -> datetime: ...
@overload
def _as_dt(value: str) -> datetime: ...


def _as_dt(value: str | date | datetime) -> datetime:
    if isinstance(value, datetime):
        return value
    if isinstance(value, date):
        return datetime.combine(value, dtime.min)
    if isinstance(value, str):
        try:
            return datetime.fromisoformat(value)
        except ValueError:
            d = date.fromisoformat(value)
            return datetime.combine(d, dtime.min)
    raise TypeError(f"Tipo não suportado: {type(value)!r}")


def _first_day_next_month(dt: datetime) -> datetime:
    dt = _aware_utc(dt)
    y, m = dt.year, dt.month
    return datetime(y + (m // 12), 1 if m == 12 else m + 1, 1, tzinfo=UTC)


def _last_moment_of_month(y: int, m: int) -> datetime:
    if m == 12:
        return datetime(y, 12, 31, 23, 59, 59, 999_999, tzinfo=UTC)
    nxt = datetime(y, m + 1, 1, tzinfo=UTC)
    return nxt - timedelta(microseconds=1)


def _inicio_mes_por_data(dt: datetime) -> datetime:
    dt = _aware_utc(dt)
    return datetime(dt.year, dt.month, 1, tzinfo=UTC)


def _inicio_bimestre_por_data(dt: datetime) -> datetime:
    dt = _aware_utc(dt)
    # bimestres: (1-2), (3-4), (5-6), (7-8), (9-10), (11-12)
    m_ini = dt.month if dt.month % 2 == 1 else dt.month - 1
    return datetime(dt.year, m_ini, 1, tzinfo=UTC)


def _fim_bimestre_por_data(dt: datetime) -> datetime:
    dt = _aware_utc(dt)
    m_end = dt.month if dt.month % 2 == 0 else dt.month + 1
    y = dt.year
    if m_end == 13:
        y, m_end = y + 1, 1
    return _last_moment_of_month(y, m_end)


LIMITE_INFERIOR = datetime(2024, 10, 1, tzinfo=UTC)


def buscar_todos_produtos_guru() -> list[dict[str, Any]]:
    url = f"{BASE_URL_GURU}/products"
    headers = HEADERS_GURU
    produtos: list[dict[str, Any]] = []
    cursor: str | None = None
    pagina = 1

    while True:
        try:
            params: dict[str, Any] = {"limit": 100}
            if cursor:
                params["cursor"] = cursor

            r = http_get(url, headers=headers, params=params, timeout=10)
            if r.status_code != 200:
                print(f"[❌ Guru] Erro {r.status_code} ao buscar produtos: {r.text}")
                break

            data: dict[str, Any] = r.json()
            pagina_dados = data.get("data", [])
            print(f"[📄 Página {pagina}] {len(pagina_dados)} produtos encontrados")

            produtos += pagina_dados  # esperado: list[dict[str, Any]]
            cursor = data.get("next_cursor")

            if not cursor:
                break

            pagina += 1

        except Exception as e:
            print(f"[❌ Guru] Exceção ao buscar produtos: {e}")
            break

    print(f"[✅ Guru] Total de produtos carregados: {len(produtos)}")
    return produtos


def obter_ids_assinaturas_por_duracao(
    skus_info: Mapping[str, Mapping[str, Any]],
) -> tuple[dict[str, list[str]], dict[str, dict[str, str]]]:
    assinaturas: dict[str, list[str]] = {
        "mensal": [],
        "bimestral": [],
        "anual": [],
        "bianual": [],
        "trianual": [],
    }
    # mapa auxiliar: guru_id -> {"recorrencia":..., "periodicidade":...}
    guru_meta: dict[str, dict[str, str]] = {}

    for _nome, info in skus_info.items():
        if (info.get("tipo") or "").lower() == "assinatura":
            ids = info.get("guru_ids", [])
            dur = (info.get("recorrencia") or "").lower()
            per = (info.get("periodicidade") or "").lower()
            for gid in ids:
                if dur in assinaturas:
                    assinaturas[dur].append(str(gid))
                guru_meta[str(gid)] = {"recorrencia": dur, "periodicidade": per}

    return assinaturas, guru_meta


def gerar_uuid() -> str:
    return str(uuid.uuid4())


ASSINATURAS, GURU_META = obter_ids_assinaturas_por_duracao(skus_info)

ASSINATURAS_MENSAIS = ASSINATURAS.get("mensal", [])
ASSINATURAS_BIMESTRAIS = ASSINATURAS.get("bimestral", [])
ASSINATURAS_ANUAIS = ASSINATURAS.get("anual", [])
ASSINATURAS_BIANUAIS = ASSINATURAS.get("bianual", [])
ASSINATURAS_TRIANUAIS = ASSINATURAS.get("trianual", [])


def dividir_busca_em_periodos(
    data_inicio: str | date | datetime,
    data_fim: str | date | datetime,
) -> list[tuple[str, str]]:
    """Divide o intervalo em blocos com fins em abr/ago/dez.

    Retorna lista de tuplas (YYYY-MM-DD, YYYY-MM-DD). Internamente usa datetime aware (UTC).
    """
    ini = _as_dt(data_inicio)
    if not ini.tzinfo:
        ini = ini.replace(tzinfo=UTC)
    end = _as_dt(data_fim)
    if not end.tzinfo:
        end = end.replace(tzinfo=UTC)

    blocos: list[tuple[str, str]] = []
    atual = ini

    while atual <= end:
        ano = atual.year
        mes = atual.month

        # Blocos: jan-abr, mai-ago, set-dez
        fim_mes = 4 if mes <= 4 else (8 if mes <= 8 else 12)

        ultimo_dia = monthrange(ano, fim_mes)[1]
        fim_bloco = datetime(ano, fim_mes, ultimo_dia, 23, 59, 59, tzinfo=UTC)

        fim_bloco = min(fim_bloco, end)

        blocos.append((atual.date().isoformat(), fim_bloco.date().isoformat()))

        # avança para o próximo bloco
        proximo_mes = fim_mes + 1
        proximo_ano = ano
        if proximo_mes > 12:
            proximo_mes = 1
            proximo_ano += 1
        atual = datetime(proximo_ano, proximo_mes, 1, tzinfo=UTC)

    return blocos


class HasIsSet(Protocol):
    def is_set(self) -> bool: ...


def buscar_transacoes_com_retry(
    *args: Any,
    cancelador: Any = None,
    tentativas: int = 3,
    **kwargs: Any,
) -> list[dict[str, Any]]:
    for tentativa in range(tentativas):
        if cancelador and cancelador.is_set():
            print("[🚫] Cancelado dentro de buscar_transacoes_com_retry.")
            return []
        try:
            resultado = buscar_transacoes_individuais(*args, cancelador=cancelador, **kwargs)
            return cast(list[dict[str, Any]], resultado)  # ⬅️ evita "no-any-return"
        except TransientGuruError as e:
            print(f"[⚠️ Retry {tentativa+1}/{tentativas}] {e}")
            if tentativa < tentativas - 1:
                espera = (2**tentativa) + random.random()
                time.sleep(espera)
            else:
                print("[❌] Falhou após retries; retornando vazio.")
                return []
    return []


def buscar_transacoes_produtos(
    dados: Mapping[str, Any],
    *,
    atualizar: Callable[[str, int, int], Any] | None = None,
    cancelador: HasIsSet | None = None,
    estado: MutableMapping[str, Any] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, Any], dict[str, Any]]:  # ← dict no 3º item
    print("[🔍 buscar_transacoes_produtos] Início da função")

    transacoes: list[dict[str, Any]] = []
    if estado is None:
        estado = {}
    estado["transacoes_com_erro"] = []

    inicio = dados["inicio"]
    fim = dados["fim"]
    produtos_ids: list[str] = [str(pid) for pid in (dados.get("produtos_ids") or []) if pid]

    if not produtos_ids:
        print("[⚠️] Nenhum produto selecionado para busca.")
        return [], {}, dict(dados)  # ← CONVERTE

    intervalos = cast(list[tuple[str, str]], dividir_busca_em_periodos(inicio, fim))
    tarefas: list[tuple[str, str, str]] = [
        (product_id, ini, fim) for product_id in produtos_ids for (ini, fim) in intervalos
    ]

    print(f"[📦] Total de tarefas para produtos: {len(tarefas)}")

    if cancelador and cancelador.is_set():
        if atualizar:
            atualizar("⛔ Busca cancelada pelo usuário", 1, 1)
        return [], {}, dict(dados)  # ← CONVERTE

    with ThreadPoolExecutor(max_workers=12) as executor:
        futures = [executor.submit(buscar_transacoes_com_retry, *args, cancelador=cancelador) for args in tarefas]
        total_futures = len(futures)
        concluidos = 0

        while futures:
            if cancelador and cancelador.is_set():
                print("[🚫] Cancelado durante busca de produtos.")
                for f in futures:
                    f.cancel()
                return transacoes, {}, dict(dados)  # ← CONVERTE

            done, not_done = wait(futures, timeout=0.5, return_when=FIRST_COMPLETED)

            for future in done:
                try:
                    resultado = future.result()
                    if isinstance(resultado, list):
                        for item in resultado:
                            if isinstance(item, dict):
                                transacoes.append(item)
                            elif isinstance(item, list):
                                for subitem in item:
                                    if isinstance(subitem, dict):
                                        transacoes.append(subitem)
                                    else:
                                        print(f"[⚠️] Ignorado item aninhado não-dict: {type(subitem)}")
                            else:
                                print(f"[⚠️] Ignorado item inesperado: {type(item)}")
                    else:
                        print(f"[⚠️] Resultado inesperado: {type(resultado)}")
                except Exception as e:
                    erro_msg = f"Erro ao buscar transações de produto: {e!s}"
                    print(f"❌ {erro_msg}")
                    estado["transacoes_com_erro"].append(erro_msg)
                concluidos += 1
                if atualizar:
                    with suppress(Exception):
                        atualizar("🔄 Coletando transações de produtos...", concluidos, total_futures)

            futures = list(not_done)

    print(f"[✅ buscar_transacoes_produtos] Finalizado - {len(transacoes)} transações coletadas")
    return transacoes, {}, dict(dados)


# --- Utilitário simples (backend) ---
def bimestre_do_mes(mes: int) -> int:
    return 1 + (int(mes) - 1) // 2


# --- Cálculo de períodos e regras (backend) ---
from __future__ import annotations

import calendar
import json
import os
from datetime import UTC, datetime

# depende no backend:
# - bimestre_do_mes(mes: int) -> int


def bounds_do_periodo(ano: int, mes: int, periodicidade: str) -> tuple[datetime, datetime, int]:
    periodicidade = (periodicidade or "").strip().lower()

    if periodicidade == "mensal":
        dt_ini = datetime(ano, mes, 1, 0, 0, 0, tzinfo=UTC)
        last_day = calendar.monthrange(ano, mes)[1]
        dt_end = datetime(ano, mes, last_day, 23, 59, 59, tzinfo=UTC)
        periodo = mes
    else:  # bimestral
        bim = bimestre_do_mes(mes)
        m1 = 1 + (bim - 1) * 2
        m2 = m1 + 1
        dt_ini = datetime(ano, m1, 1, 0, 0, 0, tzinfo=UTC)
        last_day = calendar.monthrange(ano, m2)[1]
        dt_end = datetime(ano, m2, last_day, 23, 59, 59, tzinfo=UTC)
        periodo = bim

    return dt_ini, dt_end, periodo


def dentro_periodo_selecionado(dados: dict, data_pedido: datetime) -> bool:
    """True se data_pedido (ordered_at) estiver dentro do período (Ano/Mês + Periodicidade).

    - NÃO aplica para modo 'produtos'.
    - Usa ordered_at_ini_periodo/ordered_at_end_periodo se existirem; senão, deriva via bounds_do_periodo.
    - Converte TUDO para datetime *aware* (UTC) antes de comparar.
    - Logs defensivos sem referenciar variáveis ainda não definidas.
    """

    def _aware_utc(dt: datetime | None) -> datetime | None:
        if dt is None:
            return None
        return dt.replace(tzinfo=UTC) if dt.tzinfo is None else dt.astimezone(UTC)

    def _to_dt(val: object) -> datetime | None:
        """Converte val -> datetime (UTC aware). Aceita datetime/ISO/timestamp s|ms/QDateTime."""
        if val is None:
            return None
        if isinstance(val, datetime):
            return _aware_utc(val)
        if isinstance(val, (int, float)):
            try:
                v = float(val)
                if v > 1e12:  # ms -> s
                    v /= 1000.0
                return datetime.fromtimestamp(v, tz=UTC)
            except Exception:
                return None
        if isinstance(val, str):
            try:
                dt = parse_date(val)
                return _aware_utc(dt)
            except Exception:
                return None
        if hasattr(val, "toPyDateTime"):
            try:
                return _aware_utc(val.toPyDateTime())
            except Exception:
                return None
        return None

    try:
        if not isinstance(dados, dict):
            return False

        modo_local = (str(dados.get("modo") or dados.get("modo_busca") or "")).strip().lower()
        if modo_local == "produtos":
            return False

        dp = _to_dt(data_pedido)
        if dp is None:
            print(f"[DEBUG dentro_periodo] data_pedido inválido: {data_pedido!r}")
            return False

        # janela explícita
        ini = _to_dt(dados.get("ordered_at_ini_periodo"))
        end = _to_dt(dados.get("ordered_at_end_periodo"))

        # derivada
        if ini is None or end is None:
            ano_s = dados.get("ano")
            mes_s = dados.get("mes")
            periodicidade = (str(dados.get("periodicidade") or "bimestral")).strip().lower()

            if ano_s is None or mes_s is None:
                print(f"[DEBUG dentro_periodo] sem contexto suficiente (ano={ano_s}, mes={mes_s})")
                return False

            try:
                ano_i = int(ano_s)
                mes_i = int(mes_s)
            except Exception:
                print(f"[DEBUG dentro_periodo] sem contexto suficiente (ano={ano_s}, mes={mes_s})")
                return False

            try:
                ini_calc, end_calc, _ = bounds_do_periodo(ano_i, mes_i, periodicidade)
            except Exception as e:
                print(f"[DEBUG janela-skip] bounds_do_periodo erro: {e}")
                return False

            ini = _to_dt(ini_calc)
            end = _to_dt(end_calc)

        if ini is None or end is None:
            print(f"[DEBUG dentro_periodo] janela inválida ini={ini!r} end={end!r}")
            return False

        print(f"[DEBUG dentro_periodo] dp={dp} ini={ini} end={end}")

        try:
            return ini <= dp <= end
        except Exception as e:
            print(
                f"[DEBUG dentro_periodo] comparação falhou: {type(e).__name__}: {e} "
                f"(types: ini={type(ini)}, dp={type(dp)}, end={type(end)})"
            )
            return False

    except Exception as e:
        print(f"[DEBUG janela-skip] {type(e).__name__}: {e}")
        return False


def _carregar_regras(estado: MutableMapping[str, Any]) -> list[dict[str, Any]]:
    if isinstance(estado.get("rules"), list):
        return cast(list[dict[str, Any]], estado["rules"])

    # fallback leve (não explode se não houver arquivo)
    try:
        config_path = os.path.join(os.path.dirname(__file__), "config_ofertas.json")
        if os.path.exists(config_path):
            with open(config_path, encoding="utf-8") as f:
                cfg: dict[str, Any] = json.load(f)
                regras = cfg.get("rules") or cfg.get("regras") or []
                if isinstance(regras, list):
                    estado["rules"] = regras  # cache para próximas chamadas
                    return regras
    except Exception:
        pass

    return []


def coletar_ids_assinaturas_por_periodicidade(
    skus_info: Mapping[str, Mapping[str, Any]],
    periodicidade_sel: str,
) -> dict[str, list[str]]:
    """Retorna dict com listas de product_ids (Guru) das assinaturas filtradas pela periodicidade
    ('mensal' | 'bimestral').

    Keys: 'anuais', 'bianuais', 'trianuais', 'bimestrais', 'mensais', 'todos'
    """
    periodicidade_sel = (periodicidade_sel or "").strip().lower()
    mapa_tipo: dict[str, str] = {
        "anual": "anuais",
        "bianual": "bianuais",
        "trianual": "trianuais",
        "bimestral": "bimestrais",
        "mensal": "mensais",
    }

    ids_por_tipo: dict[str, list[str]] = {k: [] for k in ["anuais", "bianuais", "trianuais", "bimestrais", "mensais"]}
    todos: set[str] = set()

    for _nome, info in skus_info.items():
        if str(info.get("tipo", "")).lower() != "assinatura":
            continue
        if str(info.get("periodicidade", "")).lower() != periodicidade_sel:
            continue

        duracao = str(info.get("recorrencia", "")).lower()
        chave_tipo = mapa_tipo.get(duracao)
        if not chave_tipo:
            continue

        guru_ids: Sequence[Any] = cast(Sequence[Any], info.get("guru_ids", []))
        for gid in guru_ids:
            gid_str = str(gid).strip()
            if gid_str:
                ids_por_tipo[chave_tipo].append(gid_str)
                todos.add(gid_str)

    # dedup
    for k in list(ids_por_tipo.keys()):
        ids_por_tipo[k] = list(dict.fromkeys(ids_por_tipo[k]))
    ids_por_tipo["todos"] = list(todos)
    return ids_por_tipo


def buscar_transacoes_assinaturas(
    dados: dict[str, Any],
    *,
    atualizar: Callable[[str, int, int], Any] | None = None,
    cancelador: HasIsSet | None = None,
    estado: dict[str, Any] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, Any], dict[str, Any]]:
    print("[🔍 buscar_transacoes_assinaturas] Início da função")

    transacoes: list[dict[str, Any]] = []
    if estado is None:
        estado = {}
    estado["transacoes_com_erro"] = []

    # ⚙️ contexto
    periodicidade_sel: str = (
        (str(dados.get("periodicidade") or dados.get("periodicidade_selecionada") or "")).strip().lower()
    )
    if periodicidade_sel not in ("mensal", "bimestral"):
        periodicidade_sel = "bimestral"

    # garanta que o mapeamento está no estado
    estado.setdefault("skus_info", {})
    skus_info: dict[str, dict[str, Any]] = cast(dict[str, dict[str, Any]], estado.get("skus_info", {}))

    # ✅ IDs por periodicidade a partir do SKUs.json
    ids_map: dict[str, list[str]] = coletar_ids_assinaturas_por_periodicidade(skus_info, periodicidade_sel)
    dados["ids_planos_todos"] = ids_map.get("todos", [])

    # 🗓 período indicado na UI
    dt_ini_sel: datetime | None = (
        dados.get("ordered_at_ini_periodo")
        or dados.get("ordered_at_ini_anual")
        or dados.get("ordered_at_ini_bimestral")
    )
    dt_end_sel: datetime | None = (
        dados.get("ordered_at_end_periodo")
        or dados.get("ordered_at_end_anual")
        or dados.get("ordered_at_end_bimestral")
    )

    if not dt_ini_sel or not dt_end_sel:
        raise ValueError("ordered_at_ini / ordered_at_end não informados para o período selecionado.")

    # ================= Normaliza período selecionado =================
    end_sel = _as_dt(dt_end_sel)
    if periodicidade_sel == "mensal":
        ini_sel = _inicio_mes_por_data(end_sel)
        end_sel = _last_moment_of_month(end_sel.year, end_sel.month)
    else:  # "bimestral"
        ini_sel = _inicio_bimestre_por_data(end_sel)
        end_sel = _fim_bimestre_por_data(end_sel)

    # ================= Constrói intervalos =================
    intervalos_mensais: list[tuple[str, str]] = (
        dividir_busca_em_periodos(ini_sel, end_sel) if periodicidade_sel == "mensal" else []
    )
    intervalos_bimestrais: list[tuple[str, str]] = (
        dividir_busca_em_periodos(ini_sel, end_sel) if periodicidade_sel == "bimestral" else []
    )

    # Multi-ano: início = (primeiro dia do mês seguinte ao fim selecionado) - N anos, limitado por LIMITE_INFERIOR
    inicio_base = _first_day_next_month(end_sel)

    def _janela_multi_ano(n_anos: int) -> list[tuple[str, str]]:
        ini = datetime(inicio_base.year - n_anos, inicio_base.month, 1, tzinfo=UTC)
        ini = max(ini, LIMITE_INFERIOR)
        return cast(list[tuple[str, str]], dividir_busca_em_periodos(ini, end_sel))

    # ================= Modo do período (PERÍODO vs TODAS) =================
    try:
        modo_sel_norm = unidecode((dados.get("modo_periodo") or "").strip().upper())
    except Exception:
        modo_sel_norm = (dados.get("modo_periodo") or "").strip().upper().replace("Í", "I").replace("É", "E")

    if modo_sel_norm == "PERIODO":
        # somente o mês/bimestre selecionado
        intervalos_anuais = dividir_busca_em_periodos(ini_sel, end_sel)
        intervalos_bianuais = dividir_busca_em_periodos(ini_sel, end_sel)
        intervalos_trianuais = dividir_busca_em_periodos(ini_sel, end_sel)
    else:
        # janelas de 1, 2 e 3 anos retroativas
        intervalos_anuais = _janela_multi_ano(1)
        intervalos_bianuais = _janela_multi_ano(2)
        intervalos_trianuais = _janela_multi_ano(3)

    # ================= Executor =================
    def executar_lote(
        tarefas: Sequence[tuple[str, str, str, str]],
        label_progresso: str,
    ) -> bool:
        if not tarefas:
            return True
        max_workers = min(12, len(tarefas))
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = [
                executor.submit(
                    buscar_transacoes_com_retry,
                    pid,
                    ini,
                    fim,
                    cancelador=cancelador,
                    tipo_assinatura=tipo_ass,
                )
                for (pid, ini, fim, tipo_ass) in tarefas
            ]
            total_futures = len(futures)
            concluidos = 0
            while futures:
                if cancelador and cancelador.is_set():
                    for f in futures:
                        f.cancel()
                    return False
                done, not_done = wait(futures, timeout=0.5, return_when=FIRST_COMPLETED)
                for future in done:
                    try:
                        resultado = future.result()
                        transacoes.extend(cast(list[dict[str, Any]], resultado))
                    except Exception as e:
                        erro_msg = f"Erro ao buscar transações ({label_progresso}): {e!s}"
                        print(f"❌ {erro_msg}")
                        estado["transacoes_com_erro"].append(erro_msg)
                    finally:
                        concluidos += 1
                        if atualizar:
                            with suppress(Exception):
                                atualizar(f"🔄 {label_progresso}", concluidos, total_futures)
                futures = list(not_done)
        return True

    # ================= Tarefas (AGREGADAS) =================
    todas_tarefas: list[tuple[str, str, str, str]] = []

    print("[1️⃣] Gerando tarefas para anuais...")
    t: list[tuple[str, str, str, str]] = [
        (pid, ini, fim, "anuais") for pid in ids_map.get("anuais", []) for (ini, fim) in intervalos_anuais
    ]
    todas_tarefas.extend(t)

    print("[1.1️⃣] Gerando tarefas para bianuais...")
    t = [(pid, ini, fim, "bianuais") for pid in ids_map.get("bianuais", []) for (ini, fim) in intervalos_bianuais]
    todas_tarefas.extend(t)

    print("[1.2️⃣] Gerando tarefas para trianuais...")
    t = [(pid, ini, fim, "trianuais") for pid in ids_map.get("trianuais", []) for (ini, fim) in intervalos_trianuais]
    todas_tarefas.extend(t)

    print("[2️⃣] Gerando tarefas para bimestrais...]")
    t = [(pid, ini, fim, "bimestrais") for pid in ids_map.get("bimestrais", []) for (ini, fim) in intervalos_bimestrais]
    todas_tarefas.extend(t)

    print("[3️⃣] Gerando tarefas para mensais...")
    t = [(pid, ini, fim, "mensais") for pid in ids_map.get("mensais", []) for (ini, fim) in intervalos_mensais]
    todas_tarefas.extend(t)

    # ---- executa tudo de uma vez no mesmo pool ----
    total_tarefas = len(todas_tarefas)
    print(f"[🧵] Disparando {total_tarefas} tarefas no executor único...")

    if total_tarefas == 0:
        print("[INFO] Nenhuma tarefa gerada para o período/periodicidade selecionados.")
        print(f"[✅ buscar_transacoes_assinaturas] Finalizado - {len(transacoes)} transações")
        return transacoes, {}, dados

    ok = executar_lote(todas_tarefas, "Coletando transações...")
    if not ok:
        print("[⛔] Execução interrompida por cancelamento.")
        return transacoes, {}, dados

    print(f"[✅ buscar_transacoes_assinaturas] Finalizado - {len(transacoes)} transações")
    return transacoes, {}, dados


# --- Erros/Low-level HTTP (backend) ---
class TransientGuruError(Exception):
    """Erro transitório ao buscar a PRIMEIRA página; deve acionar retry externo."""


def buscar_transacoes_individuais(
    product_id: str,
    inicio: str,
    fim: str,
    *,
    cancelador: HasIsSet | None = None,
    tipo_assinatura: str | None = None,
    timeout: tuple[float, float] = (3.0, 15.0),  # (connect, read)
    max_page_retries: int = 2,  # tentativas por página
) -> list[dict[str, Any]]:
    if cancelador and cancelador.is_set():
        print("[🚫] Cancelado no início de buscar_transacoes_individuais")
        return []

    print(f"[🔎 buscar_transacoes_individuais] Início - Produto: {product_id}, Período: {inicio} → {fim}")

    resultado: list[dict[str, Any]] = []
    cursor: str | None = None
    pagina_count = 0
    total_transacoes = 0
    erro_final = False

    session = requests.Session()

    while True:
        if cancelador and cancelador.is_set():
            print("[🚫] Cancelado no meio da busca individual")
            break

        params: dict[str, Any] = {
            "transaction_status[]": ["approved"],
            "ordered_at_ini": inicio,
            "ordered_at_end": fim,
            "product_id": product_id,
        }
        if cursor:
            params["cursor"] = cursor

        data: Mapping[str, Any] | None = None
        last_exc: Exception | None = None

        # === tentativas por página ===
        for tentativa in range(max_page_retries + 1):
            if cancelador and cancelador.is_set():
                print("[🚫] Cancelado durante tentativa de página")
                break
            try:
                r: requests.Response = session.get(
                    f"{BASE_URL_GURU}/transactions",
                    headers=HEADERS_GURU,
                    params=params,
                    timeout=timeout,
                )
                if r.status_code != 200:
                    raise requests.HTTPError(f"HTTP {r.status_code}")
                data = cast(Mapping[str, Any], r.json())
                break  # sucesso
            except Exception as e:
                last_exc = e
                if tentativa < max_page_retries:
                    espera = (1.5**tentativa) + random.random()
                    print(
                        f"[⏳] Tentativa {tentativa+1}/{max_page_retries+1} falhou para {product_id} ({e}); novo retry em {espera:.1f}s"
                    )
                    time.sleep(espera)
                else:
                    print(f"❌ Falha ao obter página para {product_id} após {max_page_retries+1} tentativas: {e}")

        # Se não conseguiu obter esta página:
        if data is None:
            if pagina_count == 0 and total_transacoes == 0:
                # falhou logo de cara → deixa o wrapper decidir (retry externo)
                raise TransientGuruError(f"Falha inicial ao buscar transações do produto {product_id}: {last_exc}")
            else:
                # falhou depois de já ter coletado algo → devolve parciais
                erro_final = True
                break

        pagina = cast(list[dict[str, Any]], data.get("data", []) or [])
        print(f"[📄 Página {pagina_count+1}] {len(pagina)} assinaturas encontradas")

        for t in pagina:
            if cancelador and cancelador.is_set():
                print("[🚫] Cancelado durante processamento da página")
                break
            if tipo_assinatura:
                t["tipo_assinatura"] = tipo_assinatura
            resultado.append(t)

        total_transacoes += len(pagina)
        pagina_count += 1
        cursor = cast(str | None, data.get("next_cursor"))
        if not cursor:
            break

    status = "Concluído" if not erro_final else "Concluído (parcial)"
    print(
        f"[✅ buscar_transacoes_individuais] {status} - Produto {product_id} | Total: {total_transacoes} transações em {pagina_count} página(s)"
    )
    return resultado


def _caminho_config_ofertas() -> str:
    return os.path.join(os.path.dirname(__file__), "config_ofertas.json")


def _ler_json_seguro(path: str, default: Any) -> Any:
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        return default
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except JSONDecodeError:
        return default


# === Canoniza: sempre expor/salvar em "rules", mas aceitar "regras" legado ===
class RegrasConfig(TypedDict):
    rules: list[dict[str, Any]]


def _normalizar_cfg(cfg: Mapping[str, Any]) -> RegrasConfig:
    cfg = dict(cfg or {})  # tolera objetos Mapping
    rules = cfg.get("rules")
    if rules is None:
        rules = cfg.get("regras")  # legado
    if not isinstance(rules, list):
        rules = []
    return {"rules": cast(list[dict[str, Any]], rules)}


def carregar_config_ofertas() -> RegrasConfig:
    path = _caminho_config_ofertas()
    raw: Mapping[str, Any] = _ler_json_seguro(path, {"rules": []})
    return _normalizar_cfg(raw)


def salvar_config_ofertas(cfg: Mapping[str, Any]) -> None:
    path = _caminho_config_ofertas()
    os.makedirs(os.path.dirname(path), exist_ok=True)
    cfg_norm = _normalizar_cfg(cfg)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(cfg_norm, f, indent=2, ensure_ascii=False)


def carregar_regras(config_path: str | None = None) -> list[dict[str, Any]]:
    path = config_path or _caminho_config_ofertas()
    data: Mapping[str, Any] = _ler_json_seguro(path, {"rules": []})
    return cast(list[dict[str, Any]], _normalizar_cfg(data)["rules"])


def salvar_regras(config_path: str, rules: Sequence[Mapping[str, Any]] | None) -> None:
    os.makedirs(os.path.dirname(config_path), exist_ok=True)
    with open(config_path, "w", encoding="utf-8") as f:
        json.dump({"rules": list(rules or [])}, f, indent=2, ensure_ascii=False)


# Use o mesmo caminho e normalize ao ler
def obter_regras_config(path: str | None = None) -> list[dict[str, Any]]:
    path = path or _caminho_config_ofertas()
    try:
        with open(path, encoding="utf-8") as f:
            cfg: dict[str, Any] = json.load(f)
    except FileNotFoundError:
        print(f"[⚠️] {path} não encontrado")
        return []
    except Exception as e:
        print(f"[⚠️ ERRO ao ler {path}]: {e}")
        return []
    return cast(list[dict[str, Any]], _normalizar_cfg(cfg)["rules"])


# Passe a escrever em "rules" e a usar as chaves do seu JSON atual: applies_to/action/cupom
def adicionar_regra_config(regra: dict[str, Any]) -> None:
    cfg = carregar_config_ofertas()
    rules: list[dict[str, Any]] = list(cfg.get("rules") or [])

    def _canon(r: Mapping[str, Any]) -> dict[str, Any]:
        return {
            "applies_to": r.get("applies_to"),
            "cupom": r.get("cupom"),
            "alvo": r.get("alvo"),
            "assinaturas": sorted(r.get("assinaturas") or []),
            "action": r.get("action"),
        }

    base_nova = _canon(regra)
    for r in rules:
        if _canon(r) == base_nova:
            return  # já existe

    if not regra.get("id"):
        regra = dict(regra)
        regra["id"] = str(uuid4())

    rules.append(regra)
    salvar_config_ofertas({"rules": rules})


def remover_regra_config(regra_id: str) -> None:
    cfg = carregar_config_ofertas()
    rules = [r for r in (cfg.get("rules") or []) if r.get("id") != regra_id]
    salvar_config_ofertas({"rules": rules})


def formatar_valor(valor: float) -> str:
    return f"{valor:.2f}".replace(".", ",")


def recebe_box_do_periodo(ordered_at_end_anchor: datetime, data_check: datetime, periodicidade: str) -> bool:
    """Verifica se data_check cai no mês/bimestre ancorado em ordered_at_end_anchor (UTC-aware)."""
    periodicidade = (periodicidade or "bimestral").strip().lower()

    def _aware_utc(dt: datetime | None) -> datetime | None:
        if dt is None:
            return None
        return dt.replace(tzinfo=UTC) if dt.tzinfo is None else dt.astimezone(UTC)

    anchor = _aware_utc(ordered_at_end_anchor)
    dc = _aware_utc(data_check)
    if anchor is None or dc is None:
        return False

    ano = anchor.year
    mes = anchor.month

    if periodicidade == "mensal":
        inicio = datetime(ano, mes, 1, 0, 0, 0, tzinfo=UTC)
        prox_ini = (
            datetime(ano + 1, 1, 1, 0, 0, 0, tzinfo=UTC)
            if mes == 12
            else datetime(ano, mes + 1, 1, 0, 0, 0, tzinfo=UTC)
        )
        fim = prox_ini - timedelta(seconds=1)
        return inicio <= dc <= fim

    # bimestral (padrão)
    primeiro_mes = ((mes - 1) // 2) * 2 + 1  # 1,3,5,7,9,11
    inicio = datetime(ano, primeiro_mes, 1, 0, 0, 0, tzinfo=UTC)
    if primeiro_mes + 1 == 12:
        prox_ini = datetime(ano + 1, 1, 1, 0, 0, 0, tzinfo=UTC)
        fim_dia = prox_ini - timedelta(days=1)
        fim = datetime(fim_dia.year, fim_dia.month, fim_dia.day, 23, 59, 59, tzinfo=UTC)
    else:
        prox_ini = datetime(ano, primeiro_mes + 2, 1, 0, 0, 0, tzinfo=UTC)
        fim = prox_ini - timedelta(seconds=1)
    return inicio <= dc <= fim


def eh_indisponivel(produto_nome: str, *, sku: str | None = None) -> bool:
    if not produto_nome and not sku:
        return False

    from backend import estado  # import local para evitar ciclos (ajuste se necessário)

    skus: Mapping[str, Mapping[str, Any]] = cast(Mapping[str, Mapping[str, Any]], estado.get("skus_info") or {})
    info: Mapping[str, Any] | None = skus.get(produto_nome)

    # fallback por normalização do nome
    if info is None and produto_nome:
        alvo = unidecode(str(produto_nome)).lower().strip()
        for nome, i in skus.items():
            if unidecode(nome).lower().strip() == alvo:
                info = i
                break

    # tenta por SKU
    if info is None and sku:
        sku_norm = (sku or "").strip().upper()
        for i in skus.values():
            if str(i.get("sku", "")).strip().upper() == sku_norm:
                info = i
                break

    return bool(info and info.get("indisponivel", False))


def normalizar(texto: Any) -> str:
    s = str(texto or "")
    s = unicodedata.normalize("NFD", s)
    s = s.encode("ascii", "ignore").decode("utf-8")
    return s.lower()


def encontrar_nome_padrao(nome_busca: str, skus_info: Mapping[str, Any]) -> str | None:
    nome_norm = normalizar(nome_busca)
    for nome_padrao in skus_info:
        if normalizar(nome_padrao) in nome_norm:
            return str(nome_padrao)
    return None


def desmembrar_produto_combo(
    valores: Mapping[str, Any],
    linha_base: dict[str, Any],
    skus_info: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """
    - valores["produto_principal"] = nome do combo
    - valores["valor_total"]       = total do combo (float/int ou string com vírgula)
    - skus_info[nome_combo]["composto_de"] = [SKUs...]
    - skus_info[produto_simples]["sku"] = SKU do produto simples
    """
    nome_combo: str = str(valores.get("produto_principal", ""))
    info_combo: Mapping[str, Any] = skus_info.get(nome_combo, {})
    skus_componentes: list[str] = [str(s).strip() for s in (info_combo.get("composto_de", []) or []) if str(s).strip()]

    # Se não há componentes, retorna a linha original
    if not skus_componentes:
        return [linha_base]

    # Helper: parse total (aceita 12,34 / 12.34 / 1.234,56)
    def _to_dec(v: Any) -> Decimal:
        if v is None:
            return Decimal("0.00")
        if isinstance(v, (int, float)):
            return Decimal(str(v)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        s = str(v).strip()
        s = s.replace(".", "").replace(",", ".")
        try:
            return Decimal(s).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        except InvalidOperation:
            return Decimal("0.00")

    total = _to_dec(valores.get("valor_total"))
    n = len(skus_componentes)

    # Se total <= 0, cria itens com 0,00
    if total <= Decimal("0.00"):
        linhas = []
        for sku in skus_componentes:
            nome_item = next(
                (nome for nome, info in skus_info.items() if str(info.get("sku", "")) == sku),
                sku,
            )
            nova = linha_base.copy()
            nova["Produto"] = nome_item
            nova["SKU"] = sku
            nova["Valor Unitário"] = "0,00"
            nova["Valor Total"] = "0,00"
            nova["Combo"] = nome_combo  # opcional
            nova["indisponivel"] = "S" if eh_indisponivel(nome_item, sku=sku) else ""
            linhas.append(nova)
        return linhas

    # Rateio uniforme com distribuição de centavos (garante soma == total)
    quota = (total / n).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
    subtotal = quota * (n - 1)
    ultimo = (total - subtotal).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)

    def _fmt(d: Decimal) -> str:
        return f"{d:.2f}".replace(".", ",")

    linhas = []
    for i, sku in enumerate(skus_componentes):
        nome_item = next((nome for nome, info in skus_info.items() if info.get("sku") == sku), sku)
        valor_item = quota if i < n - 1 else ultimo
        nova = linha_base.copy()
        nova["Produto"] = nome_item
        nova["SKU"] = sku
        nova["Valor Unitário"] = _fmt(valor_item)
        nova["Valor Total"] = _fmt(valor_item)
        nova["Combo"] = nome_combo  # opcional
        # marca indisponível se necessário
        nova["indisponivel"] = "S" if eh_indisponivel(nome_item, sku=sku) else ""
        linhas.append(nova)

    return linhas


def _fmt_br_date(value: Any) -> str:
    """Formata em dd/mm/yyyy aceitando datetime/date/str."""
    # datetime / date
    if hasattr(value, "strftime"):
        try:
            return value.strftime("%d/%m/%Y")
        except Exception:
            pass
    # string (já formatada ou ISO) → devolve como veio
    if isinstance(value, str):
        return value
    # fallback neutro
    return ""


def gerar_linha_base(
    contact: Mapping[str, Any],
    valores: Mapping[str, Any],
    transacao: Mapping[str, Any],
    *,
    tipo_plano: str = "",
    subscription_id: str = "",
    cupom_valido: str = "",
    data_emissao: str | date | datetime | None = None,
) -> dict[str, Any]:
    telefone = contact.get("phone_number", "")
    data_pedido_fmt = _fmt_br_date(valores.get("data_pedido"))

    # ← sempre “hoje”, ignorando 'data_emissao' e qualquer outro valor
    data_emissao_fmt = date.today().strftime("%d/%m/%Y")

    return {
        # Comprador
        "Nome Comprador": contact.get("name", ""),
        "Data": data_emissao_fmt,
        "CPF/CNPJ Comprador": contact.get("doc", ""),
        "Endereço Comprador": contact.get("address", ""),
        "Número Comprador": contact.get("address_number", ""),
        "Complemento Comprador": contact.get("address_comp", ""),
        "Bairro Comprador": contact.get("address_district", ""),
        "CEP Comprador": contact.get("address_zip_code", ""),
        "Cidade Comprador": contact.get("address_city", ""),
        "UF Comprador": contact.get("address_state", ""),
        "Telefone Comprador": telefone,
        "Celular Comprador": telefone,
        "E-mail Comprador": contact.get("email", ""),
        # Entrega
        "Nome Entrega": contact.get("name", ""),
        "Endereço Entrega": contact.get("address", ""),
        "Número Entrega": contact.get("address_number", ""),
        "Complemento Entrega": contact.get("address_comp", ""),
        "Bairro Entrega": contact.get("address_district", ""),
        "CEP Entrega": contact.get("address_zip_code", ""),
        "Cidade Entrega": contact.get("address_city", ""),
        "UF Entrega": contact.get("address_state", ""),
        # Pedido
        "Un": "UN",
        "Quantidade": "1",
        "SKU": "",
        "subscription_id": subscription_id or "",
        "product_id": transacao.get("product", {}).get("internal_id", ""),
        "Plano Assinatura": tipo_plano or "",
        "periodicidade": valores.get("periodicidade", ""),
        "Cupom": cupom_valido,
        # Extras padrão
        "Número pedido": "",
        "Total Pedido": "",
        "Valor Frete Pedido": "",
        "Valor Desconto Pedido": "",
        "Outras despesas": "",
        "Transportadora": "",
        "Serviço": "",
        "Tipo Frete": "",
        "Observações": "",
        "Qtd Parcela": "",
        "Data Prevista": "",
        "Vendedor": "",
        "Forma Pagamento": valores.get("forma_pagamento", ""),
        "ID Forma Pagamento": "",
        "transaction_id": valores.get("transaction_id", ""),
        "indisponivel": "",
        "Data Pedido": data_pedido_fmt,
    }


def processar_planilha(
    transacoes: Sequence[Mapping[str, Any] | Sequence[Mapping[str, Any]]],
    dados: Mapping[str, Any],
    atualizar_etapa: Callable[[str, int, int], Any] | None,
    skus_info: Mapping[str, Mapping[str, Any]],
    cancelador: HasIsSet,
    estado: MutableMapping[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, dict[str, int]]]:

    estado.setdefault("df_planilha_parcial", pd.DataFrame())
    estado.setdefault("mapa_transaction_id_por_linha", {})
    estado.setdefault("brindes_indisp_set", set())
    estado.setdefault("embutidos_indisp_set", set())
    estado.setdefault("boxes_indisp_set", set())

    # ✅ valida cancelador
    if cancelador is None or not hasattr(cancelador, "is_set"):
        raise ValueError(f"'cancelador' inválido: {cancelador}")

    # contagem consistente em TODO retorno
    tipos = ["anuais", "bimestrais", "bianuais", "trianuais", "mensais"]
    contagem = {tipo: {"assinaturas": 0, "embutidos": 0, "cupons": 0} for tipo in tipos}

    if cancelador.is_set():
        print("[🚫 CANCELADOR ATIVADO] Cancelando antes de processar qualquer transação")
        return [], contagem

    linhas_planilha: list[dict[str, Any]] = []
    offset = len(estado["df_planilha_parcial"])

    def _ckey(tp: str) -> str:
        t = (tp or "").strip().lower()
        if t in contagem:
            return t
        aliases = {
            "anual": "anuais",
            "bianual": "bianuais",
            "trianual": "trianuais",
            "bimestral": "bimestrais",
            "mensal": "mensais",
        }
        return aliases.get(t, "bimestrais")  # fallback seguro

    # helper: append + mapeamento transaction_id
    def _append_linha(linha: dict[str, Any], transaction_id: str) -> None:
        linhas_planilha.append(linha)
        estado["mapa_transaction_id_por_linha"][offset + len(linhas_planilha) - 1] = transaction_id

    # helper: flag de indisponível
    def _flag_indisp(nome: str, sku: str | None = None) -> str:
        try:
            return "S" if eh_indisponivel(nome, sku=sku) else ""
        except Exception:
            return ""

    # helper: janela segura (não explode se faltar ano/mês/ini/end)
    def _aplica_janela(dados_local: Mapping[str, Any], dt: datetime) -> bool:
        try:
            return bool(dentro_periodo_selecionado(cast(dict[Any, Any], dados_local), dt))
        except Exception as e:
            print(f"[DEBUG janela-skip] Ignorando janela por falta de contexto: {e}")
            return False

    # helper: normaliza para timestamp
    def _to_ts(val: Any) -> float | None:
        if val is None:
            return None
        if isinstance(val, (int, float)):
            v = float(val)
            if v > 1e12:
                v /= 1000.0
            return v
        if isinstance(val, datetime):
            dt = val if val.tzinfo else val.replace(tzinfo=UTC)
            return dt.timestamp()
        if hasattr(val, "toPyDateTime"):
            try:
                dt = cast(datetime, val.toPyDateTime())
                dt = dt if dt.tzinfo else dt.replace(tzinfo=UTC)
                return dt.timestamp()
            except Exception:
                return None
        if isinstance(val, str):
            try:
                dt = parse_date(val)
                dt = dt if getattr(dt, "tzinfo", None) else dt.replace(tzinfo=UTC)
                return dt.timestamp()
            except Exception:
                return None
        return None

    # flatten defensivo
    transacoes_corrigidas: list[Mapping[str, Any]] = []
    for idx, t in enumerate(transacoes):
        if isinstance(t, dict):
            transacoes_corrigidas.append(t)
        elif isinstance(t, list):
            print(f"[⚠️ processar_planilha] Corrigindo lista aninhada em transacoes[{idx}]")
            for sub in t:
                if isinstance(sub, dict):
                    transacoes_corrigidas.append(sub)
                else:
                    print(f"[⚠️ Ignorado] Item inesperado do tipo {type(sub)} dentro de transacoes[{idx}]")
        else:
            print(f"[⚠️ Ignorado] transacoes[{idx}] é do tipo {type(t)} e será ignorado")

    transacoes = transacoes_corrigidas
    total_transacoes = len(transacoes)

    ids_planos_validos: Sequence[str] = cast(Sequence[str], dados.get("ids_planos_todos", []))
    modo = (dados.get("modo", "assinaturas") or "").strip().lower()
    ofertas_embutidas = dados.get("ofertas_embutidas", {}) or {}
    modo_periodo_sel = (dados.get("modo_periodo") or "").strip().upper()
    print(
        f"[DEBUG processar_planilha] Iniciando processamento: total_transacoes={len(transacoes)} modo={modo} modo_periodo={modo_periodo_sel}"
    )

    def is_transacao_principal(trans: Mapping[str, Any], ids_validos: Sequence[str]) -> bool:
        pid = trans.get("product", {}).get("internal_id", "")
        is_bump = bool(trans.get("is_order_bump", 0))
        return pid in ids_validos and not is_bump

    from backend import (
        calcular_valores_pedido,
        desmembrar_produto_combo,
        formatar_valor,
        gerar_linha_base,  # movida p/ backend
    )

    # =========================
    # 🔀 MODO PRODUTOS (avulso)
    # =========================
    if modo == "produtos":
        print(f"[DEBUG produtos] total_transacoes={total_transacoes}")
        for i, transacao in enumerate(transacoes):
            if cancelador.is_set():
                return [], contagem
            try:
                valores = calcular_valores_pedido(
                    transacao, dados, cast(Mapping[str, Any], skus_info), usar_valor_fixo=False
                )
                if not valores or not isinstance(valores, dict):
                    raise ValueError("[⚠️ calcular_valores_pedido retornou None/ inválido]")
                if not valores.get("transaction_id"):
                    raise ValueError(f"Valores inválidos retornados: {valores}")

                print(
                    f"[DEBUG produtos:item] i={i} id={valores.get('transaction_id')} "
                    f"produto='{valores.get('produto_principal')}' "
                    f"valor_total={valores.get('valor_total')}"
                )

                contact = transacao.get("contact", {})
                nome_produto = valores["produto_principal"]
                info_combo = skus_info.get(nome_produto, {})
                sku_produto = info_combo.get("sku", "")

                linha_base = gerar_linha_base(contact, valores, transacao)
                linha_base.update(
                    {
                        "Produto": nome_produto,
                        "subscription_id": "",
                        "SKU": sku_produto,
                        "Valor Unitário": formatar_valor(valores["valor_unitario"]),
                        "Valor Total": formatar_valor(valores["valor_total"]),
                        "indisponivel": ("S" if eh_indisponivel(nome_produto, sku=sku_produto) else "N"),
                    }
                )

                print(f"[DEBUG produtos:combo] i={i} composto_de={bool(info_combo.get('composto_de'))}")

                if info_combo.get("composto_de"):
                    mapeado = bool(info_combo.get("guru_ids")) and bool(info_combo.get("shopify_ids"))
                    indisponivel_combo = eh_indisponivel(nome_produto, sku=sku_produto)

                    if indisponivel_combo and mapeado:
                        linha_base["indisponivel"] = "S"
                        _append_linha(linha_base, valores["transaction_id"])
                    else:
                        for linha_item in desmembrar_produto_combo(valores, linha_base, skus_info):
                            linha_item["indisponivel"] = (
                                "S"
                                if eh_indisponivel(
                                    str(linha_item.get("Produto") or ""),
                                    sku=str(linha_item.get("SKU") or ""),
                                )
                                else "N"
                            )
                            _append_linha(linha_item, valores["transaction_id"])
                else:
                    _append_linha(linha_base, valores["transaction_id"])

            except Exception as e:
                print(f"[❌ ERRO] Transação {transacao.get('id')}: {e}")
                traceback.print_exc()

            try:
                if callable(atualizar_etapa):
                    atualizar_etapa("📦 Processando transações", i + 1, total_transacoes)
            except Exception as e:
                print(f"[❌ ERRO ao atualizar progresso]: {e}")
                traceback.print_exc()

    else:
        # =========================
        # 🧠 MODO ASSINATURAS
        # =========================
        transacoes_por_assinatura: dict[Any, list[Mapping[str, Any]]] = defaultdict(list)
        for trans in transacoes:
            subscription_info = trans.get("subscription")
            if isinstance(subscription_info, dict):
                sid = subscription_info.get("id")
                if sid:
                    transacoes_por_assinatura[sid].append(trans)

        total_assinaturas = len(transacoes_por_assinatura)
        for i, (subscription_id, grupo_transacoes) in enumerate(transacoes_por_assinatura.items()):
            if cancelador.is_set():
                return [], contagem

            def safe_parse_date(t: Mapping[str, Any]) -> datetime:
                try:
                    s = str(t.get("ordered_at") or t.get("created_at") or "1900-01-01")
                    dt = parse_date(s)
                    return dt.astimezone(UTC) if dt.tzinfo else dt.replace(tzinfo=UTC)
                except Exception:
                    return datetime(1900, 1, 1, tzinfo=UTC)

            print(f"[DEBUG assinatura] subscription_id={subscription_id} qtd_transacoes={len(grupo_transacoes)}")
            grupo_ordenado = sorted(grupo_transacoes, key=safe_parse_date)
            transacao_base = grupo_ordenado[-1]
            tipo_plano = transacao_base.get("tipo_assinatura", "bimestrais")
            print(
                f"[DEBUG assinatura] subscription_id={subscription_id} primeira={grupo_ordenado[0].get('ordered_at') or grupo_ordenado[0].get('created_at')} ultima={grupo_ordenado[-1].get('ordered_at') or grupo_ordenado[-1].get('created_at')}"
            )
            transacoes_principais = [t for t in grupo_ordenado if is_transacao_principal(t, ids_planos_validos)]
            produtos_distintos = {t.get("product", {}).get("internal_id") for t in transacoes_principais}

            usar_valor_fixo = len(produtos_distintos) > 1 or transacao_base.get("invoice", {}).get("type") == "upgrade"

            if not transacoes_principais:
                print(f"[⚠️ AVISO] Nenhuma transação principal encontrada para assinatura {subscription_id}")

            if usar_valor_fixo:
                valor_total_principal = 0.0
            elif transacoes_principais:
                valor_total_principal = sum(float(t.get("payment", {}).get("total", 0)) for t in transacoes_principais)
            else:
                valor_total_principal = float(transacao_base.get("payment", {}).get("total", 0))

            transacao = transacao_base.copy()
            transacao.setdefault("payment", {})
            transacao["payment"]["total"] = valor_total_principal
            transacao["tipo_assinatura"] = tipo_plano
            transacao["subscription"] = {"id": subscription_id}

            product_base = cast(Mapping[str, Any], transacao_base.get("product", cast(Mapping[str, Any], {})))
            transacao.setdefault("product", {})
            if "offer" not in transacao["product"] and product_base.get("offer"):
                transacao["product"]["offer"] = product_base["offer"]

            try:
                print(
                    f"[DEBUG calcular_valores_pedido] subscription_id={subscription_id} transacao_id={transacao.get('id')} ordered_at={transacao.get('ordered_at')} created_at={transacao.get('created_at')}"
                )
                valores = calcular_valores_pedido(
                    transacao, dados, cast(Mapping[str, Any], skus_info), usar_valor_fixo=usar_valor_fixo
                )
                if not isinstance(valores, dict) or not valores.get("transaction_id"):
                    raise ValueError(f"Valores inválidos retornados: {valores}")

                periodicidade_atual = (
                    dados.get("periodicidade_selecionada")
                    or dados.get("periodicidade")
                    or valores.get("periodicidade")
                    or ""
                )
                periodicidade_atual = str(periodicidade_atual).strip().lower()

                data_fim_periodo = dados.get("ordered_at_end_periodo")
                data_pedido = valores["data_pedido"]

                payment_base = transacao_base.get("payment") or {}
                coupon = payment_base.get("coupon") or {}
                cupom_usado = (coupon.get("coupon_code") or "").strip()
                if valores.get("usou_cupom"):
                    contagem[_ckey(tipo_plano)]["cupons"] += 1

                contact = transacao.get("contact", {})
                linha = gerar_linha_base(
                    contact,
                    valores,
                    transacao,
                    tipo_plano=tipo_plano,
                    subscription_id=subscription_id,
                    cupom_valido=cupom_usado,
                )

                nome_produto_principal = (dados.get("box_nome") or "").strip() or valores["produto_principal"]
                if eh_indisponivel(nome_produto_principal):
                    estado["boxes_indisp_set"].add(nome_produto_principal)

                linha["Produto"] = nome_produto_principal
                linha["SKU"] = skus_info.get(nome_produto_principal, {}).get("sku", "")
                linha["Valor Unitário"] = formatar_valor(valores["valor_unitario"])
                linha["Valor Total"] = formatar_valor(valores["valor_total"])
                linha["periodicidade"] = periodicidade_atual
                linha["indisponivel"] = _flag_indisp(
                    nome_produto_principal, skus_info.get(nome_produto_principal, {}).get("sku", "")
                )

                def calcular_periodo(periodicidade: str, data_ref: datetime) -> int | str:
                    if periodicidade == "mensal":
                        return data_ref.month
                    elif periodicidade == "bimestral":
                        return 1 + ((data_ref.month - 1) // 2)
                    else:
                        return ""

                if modo_periodo_sel == "TODAS":
                    linha["periodo"] = calcular_periodo(periodicidade_atual, data_pedido)
                elif dados.get("periodo"):
                    linha["periodo"] = dados["periodo"]
                else:
                    mes_ref = data_fim_periodo if isinstance(data_fim_periodo, datetime) else data_pedido
                    linha["periodo"] = calcular_periodo(periodicidade_atual, mes_ref)

                _append_linha(linha, valores["transaction_id"])

                if not _aplica_janela(dados, data_pedido):
                    valores["brindes_extras"] = []

                for br in valores.get("brindes_extras") or []:
                    brinde_nome = str(br.get("nome", "")).strip() if isinstance(br, dict) else str(br).strip()
                    if not brinde_nome:
                        continue
                    sku_b = skus_info.get(brinde_nome, {}).get("sku", "")
                    linha_b = linha.copy()
                    linha_b.update(
                        {
                            "Produto": brinde_nome,
                            "SKU": sku_b,
                            "Valor Unitário": "0,00",
                            "Valor Total": "0,00",
                            "indisponivel": _flag_indisp(brinde_nome, sku_b),
                            "subscription_id": subscription_id,
                        }
                    )
                    if linha_b["indisponivel"] == "S":
                        estado["brindes_indisp_set"].add(brinde_nome)
                    _append_linha(linha_b, valores["transaction_id"])

                oferta_id = transacao.get("product", {}).get("offer", {}).get("id")
                oferta_id_clean = str(oferta_id).strip()
                ofertas_normalizadas = {str(k).strip(): v for k, v in ofertas_embutidas.items()}
                nome_embutido_oferta = str(ofertas_normalizadas.get(oferta_id_clean) or "")

                data_pedido_ts = _to_ts(data_pedido)
                ini_ts = _to_ts(dados.get("embutido_ini_ts"))
                end_ts = _to_ts(dados.get("embutido_end_ts"))

                if (
                    nome_embutido_oferta
                    and data_pedido_ts is not None
                    and ini_ts is not None
                    and end_ts is not None
                    and ini_ts <= data_pedido_ts <= end_ts
                    and _aplica_janela(dados, data_pedido)
                ):
                    sku_embutido = skus_info.get(nome_embutido_oferta, {}).get("sku", "")
                    linha_embutido = linha.copy()
                    linha_embutido.update(
                        {
                            "Produto": nome_embutido_oferta,
                            "SKU": sku_embutido,
                            "Valor Unitário": "0,00",
                            "Valor Total": "0,00",
                            "indisponivel": _flag_indisp(nome_embutido_oferta, sku_embutido),
                            "subscription_id": subscription_id,
                        }
                    )
                    if linha_embutido["indisponivel"] == "S":
                        estado["embutidos_indisp_set"].add(nome_embutido_oferta)
                    _append_linha(linha_embutido, valores["transaction_id"])
                    contagem[_ckey(tipo_plano)]["embutidos"] += 1

                contagem[_ckey(tipo_plano)]["assinaturas"] += 1

            except Exception as e:
                print(f"[❌ ERRO] Transação {transacao.get('id')}: {e}")
                traceback.print_exc()

            try:
                if callable(atualizar_etapa):
                    atualizar_etapa("📦 Processando transações", i + 1, total_assinaturas or 1)
            except Exception as e:
                print(f"[❌ ERRO ao atualizar progresso]: {e}")
                traceback.print_exc()

    # ===== saída/merge =====
    try:
        print(f"[DEBUG produtos:planilha] linhas_coletadas={len(linhas_planilha)}")
        df_novas = pd.DataFrame(linhas_planilha)
    except Exception as e:
        print(f"[DEBUG produtos:df_error] {type(e).__name__}: {e}")
        if linhas_planilha:
            amostra = linhas_planilha[-1]
            print(f"[DEBUG produtos:ultima_linha] keys={list(amostra.keys())}")
        raise

    df_novas = padronizar_planilha_importada(df_novas)

    if "indisponivel" in df_novas.columns:
        df_novas["indisponivel"] = df_novas["indisponivel"].map(
            lambda x: "S" if str(x).strip().lower() in {"s", "sim", "true", "1"} else ""
        )
    else:
        df_novas["indisponivel"] = [""] * len(df_novas)

    df_antigas = estado.get("df_planilha_parcial")
    if df_antigas is not None and not df_antigas.empty:
        estado["df_planilha_parcial"] = pd.concat([df_antigas, df_novas], ignore_index=True)
    else:
        estado["df_planilha_parcial"] = df_novas

    if callable(atualizar_etapa):
        atualizar_etapa("✅ Processamento concluído", total_transacoes, total_transacoes or 1)

    # ✅ Em vez de emitir mensagem (UI), só guardamos os avisos para o frontend exibir
    msgs: list[str] = []
    try:
        if estado.get("boxes_indisp_set"):
            lst_boxes = ", ".join(sorted(estado["boxes_indisp_set"]))
            msgs.append(
                f"Produtos principais indisponíveis: {lst_boxes} (serão marcados e ignorados na etapa de lotes)."
            )
        if estado.get("brindes_indisp_set"):
            lst_brindes = ", ".join(sorted(estado["brindes_indisp_set"]))
            msgs.append(f"Brindes indisponíveis: {lst_brindes} (serão ignorados na etapa de lotes).")
        if estado.get("embutidos_indisp_set"):
            lst_embutidos = ", ".join(sorted(estado["embutidos_indisp_set"]))
            msgs.append(f"Embutidos indisponíveis: {lst_embutidos} (serão ignorados na etapa de lotes).")
    finally:
        # frontend pode ler e decidir como exibir
        estado["avisos_indisponibilidade_msgs"] = msgs

    return linhas_planilha, contagem


def _norm(s: str) -> str:
    return unidecode((s or "").strip().lower())


class RegrasAplicadas(TypedDict, total=False):
    override_box: str | None
    brindes_extra: list[dict[str, Any]]


def aplicar_regras_transaction(
    transacao: Mapping[str, Any],
    dados: Mapping[str, Any],
    _skus_info: Mapping[str, Any],
    base_produto_principal: str,
) -> RegrasAplicadas:
    """Aplica regras de config_ofertas.json (alterar_box / adicionar_brindes)."""
    regras: Sequence[Mapping[str, Any]] = obter_regras_config() or []
    res_override: str | None = None
    res_override_score = -1
    brindes_raw: list[dict[str, Any] | str] = []

    # --- contexto da transação ---
    payment: Mapping[str, Any] = transacao.get("payment") or {}
    coupon: Mapping[str, Any] = payment.get("coupon") or {}
    coupon_code_norm: str = _norm(str(coupon.get("coupon_code") or ""))

    tipo_ass: str = str(transacao.get("tipo_assinatura") or "").strip().lower()  # anuais, bianuais, ...
    periodicidade: str = str(dados.get("periodicidade_selecionada") or dados.get("periodicidade") or "").strip().lower()

    def _labels_assinatura(tipo: str, per: str) -> set[str]:
        base: list[str] = []
        if tipo == "bianuais":
            base.append("Assinatura 2 anos")
        elif tipo == "trianuais":
            base.append("Assinatura 3 anos")
        elif tipo == "anuais":
            base.append("Assinatura Anual")
        elif tipo == "bimestrais":
            base.append("Assinatura Bimestral")
        elif tipo == "mensais":
            base.append("Assinatura Mensal")
        out: set[str] = set()
        for b in base or ["Assinatura"]:
            out.add(f"{b} ({per})" if per else b)
        return {_norm(x) for x in out}

    labels_alvo = _labels_assinatura(tipo_ass, periodicidade)
    base_prod_norm = _norm(base_produto_principal)

    def _assinatura_match(lista: Sequence[str] | None) -> tuple[bool, int]:
        """Retorna (casou?, score). Score maior = mais específico."""
        if not lista:
            return True, 0
        tokens_genericos = {"anual", "2 anos", "3 anos", "mensal", "bimestral"}
        best = -1
        casou = False
        alvo_concat = " ".join(sorted(labels_alvo))
        for it in lista:
            itn = _norm(it or "")
            if not itn:
                casou, best = True, max(best, 0)
                continue
            if itn in labels_alvo:
                casou, best = True, max(best, 3)
                continue
            if itn == base_prod_norm:
                casou, best = True, max(best, 2)
                continue
            if itn in tokens_genericos and itn in alvo_concat:
                casou, best = True, max(best, 1)
        return casou, (best if best >= 0 else -1)

    for r in regras:
        if str(r.get("applies_to") or "").strip().lower() != "cupom":
            continue

        cupom_cfg: Mapping[str, Any] = r.get("cupom") or {}
        alvo_cupom = _norm(str(cupom_cfg.get("nome") or ""))
        if not alvo_cupom or alvo_cupom != coupon_code_norm:
            continue

        assinaturas_lista = r.get("assinaturas") or []
        ok, score = _assinatura_match(assinaturas_lista)
        if not ok:
            continue

        action: Mapping[str, Any] = r.get("action") or {}
        atype = str(action.get("type") or "").strip().lower()

        if atype == "adicionar_brindes":
            items = action.get("brindes") or []
            if isinstance(items, list):
                for b in items:
                    if isinstance(b, (dict, str)):
                        brindes_raw.append(b)

        elif atype == "alterar_box":
            box = str(action.get("box") or "").strip()
            if box and score > res_override_score:
                res_override = box
                res_override_score = score

    override_norm = _norm(res_override or base_produto_principal)
    uniq: list[dict[str, Any]] = []
    seen: set[str] = set()

    for b in brindes_raw:
        if isinstance(b, dict):
            nb = str(b.get("nome", "")).strip()
            if not nb:
                continue
            payload: dict[str, Any] = dict(b)
        else:
            nb = b.strip()
            if not nb:
                continue
            payload = {"nome": nb}

        nbn = _norm(nb)
        if nbn in (base_prod_norm, override_norm):
            continue
        if nbn in seen:
            continue
        seen.add(nbn)
        uniq.append(payload)

    return RegrasAplicadas(override_box=res_override, brindes_extra=uniq)


class SKUInfo(TypedDict, total=False):
    sku: str
    peso: float | int
    periodicidade: str
    guru_ids: Sequence[str]


# dicionário vindo do skus.json
SKUs = Mapping[str, SKUInfo]


class RetornoPedido(TypedDict):
    transaction_id: str
    id_oferta: str
    produto_principal: str
    sku_principal: str
    peso_principal: float | int
    valor_unitario: float
    valor_total: float
    total_pedido: float
    valor_embutido: float
    incluir_embutido: bool
    embutido: str
    brindes_extras: Sequence[dict[str, Any]]
    data_pedido: datetime
    forma_pagamento: str
    usou_cupom: bool
    tipo_plano: str
    periodicidade: str
    divisor: int


def calcular_valores_pedido(
    transacao: Mapping[str, Any],
    dados: Mapping[str, Any],
    skus_info: SKUs,
    usar_valor_fixo: bool = False,
) -> RetornoPedido:
    def _to_ts(val: Any) -> float | None:
        if val is None:
            return None
        if isinstance(val, int | float):
            return float(val)
        if isinstance(val, datetime):
            try:
                return val.timestamp()
            except Exception:
                return None
        if isinstance(val, str):
            try:
                dt = parse_date(val)
                if getattr(dt, "tzinfo", None):
                    dt = dt.replace(tzinfo=None)
                return dt.timestamp()
            except Exception:
                return None
        return None

    modo: str = str(dados.get("modo") or "").strip().lower()

    transaction_id: str = str(transacao.get("id", ""))
    product: Mapping[str, Any] = cast(Mapping[str, Any], transacao.get("product") or {})
    internal_id: str = str(product.get("internal_id") or "").strip()
    offer: Mapping[str, Any] = cast(Mapping[str, Any], product.get("offer") or {})
    id_oferta: str = str(offer.get("id", ""))

    print(f"[DEBUG calcular_valores_pedido] id={transaction_id} internal_id={internal_id} modo={modo}")

    invoice: Mapping[str, Any] = cast(Mapping[str, Any], transacao.get("invoice") or {})
    is_upgrade: bool = invoice.get("type") == "upgrade"

    # 🔐 data_pedido robusta (timestamp seg/ms ou ISO; normaliza para naive)
    ts = (cast(Mapping[str, Any], transacao.get("dates") or {})).get("ordered_at")
    if ts is not None:
        try:
            val_f = float(ts)
            if val_f > 1e12:  # ms → s
                val_f /= 1000.0
            data_pedido: datetime = datetime.fromtimestamp(val_f, tz=UTC)
        except Exception:
            s = str(transacao.get("ordered_at") or transacao.get("created_at") or "1970-01-01")
            dt = parse_date(s)
            data_pedido = dt.replace(tzinfo=None) if getattr(dt, "tzinfo", None) else dt
    else:
        s = str(transacao.get("ordered_at") or transacao.get("created_at") or "1970-01-01")
        dt = parse_date(s)
        data_pedido = dt.replace(tzinfo=None) if getattr(dt, "tzinfo", None) else dt

    payment: Mapping[str, Any] = cast(Mapping[str, Any], transacao.get("payment") or {})
    try:
        valor_total_pago: float = float(payment.get("total") or 0)
    except Exception:
        valor_total_pago = 0.0

    coupon_info_raw: Any = payment.get("coupon", {})
    coupon_info: Mapping[str, Any] = coupon_info_raw if isinstance(coupon_info_raw, dict) else {}
    cupom: str = str(coupon_info.get("coupon_code") or "").strip().lower()
    incidence_type: str = str(coupon_info.get("incidence_type") or "").strip().lower()

    # 🔎 produto principal (via internal_id → skus_info) com fallbacks
    produto_principal: str | None = None
    if internal_id:
        for nome, info in skus_info.items():
            try:
                if internal_id in (info.get("guru_ids") or []):
                    produto_principal = nome
                    break
            except Exception:
                pass

    if not produto_principal:
        nome_prod_api = str(product.get("name") or "").strip()
        if nome_prod_api in skus_info:
            produto_principal = nome_prod_api

    if not produto_principal:
        nome_box = str(dados.get("box_nome") or "").strip()
        if nome_box:
            produto_principal = nome_box

    if not produto_principal:
        try:
            produto_principal = next(iter(skus_info.keys()))
            print(
                f"[⚠️ calcular_valores_pedido] internal_id '{internal_id}' sem match; usando fallback '{produto_principal}'."
            )
        except StopIteration:
            print(f"[⚠️ calcular_valores_pedido] skus_info vazio; retornando estrutura mínima para '{transaction_id}'.")
            return RetornoPedido(
                transaction_id=transaction_id,
                id_oferta=id_oferta,
                produto_principal="",
                sku_principal="",
                peso_principal=0,
                valor_unitario=round(valor_total_pago, 2),
                valor_total=round(valor_total_pago, 2),
                total_pedido=round(valor_total_pago, 2),
                valor_embutido=0.0,
                incluir_embutido=False,
                embutido="",
                brindes_extras=[],
                data_pedido=data_pedido,
                forma_pagamento=str(payment.get("method", "") or ""),
                usou_cupom=bool(cupom),
                tipo_plano="",
                periodicidade="",
                divisor=1,
            )

    info_produto: SKUInfo = skus_info.get(produto_principal, {}) or {}
    sku_principal: str = str(info_produto.get("sku", "") or "")
    peso_principal: float | int = cast(float | int, info_produto.get("peso", 0))

    # 🚫 Sem regras para 'produtos' OU quando não tiver assinatura
    if modo == "produtos" or not transacao.get("subscription"):
        return RetornoPedido(
            transaction_id=transaction_id,
            id_oferta=id_oferta,
            produto_principal=produto_principal,
            sku_principal=sku_principal,
            peso_principal=peso_principal,
            valor_unitario=round(valor_total_pago, 2),
            valor_total=round(valor_total_pago, 2),
            total_pedido=round(valor_total_pago, 2),
            valor_embutido=0.0,
            incluir_embutido=False,
            embutido="",
            brindes_extras=[],
            data_pedido=data_pedido,
            forma_pagamento=str(payment.get("method", "") or ""),
            usou_cupom=bool(cupom),
            tipo_plano="",
            periodicidade="",
            divisor=1,
        )

    # =========================
    # ASSINATURAS
    # =========================
    # ✅ janela/regras protegidas
    try:
        print(f"[DEBUG janela-check] id={transaction_id} data_pedido={data_pedido}")
        aplica_regras_neste_periodo: bool = bool(
            dentro_periodo_selecionado(
                cast(dict[Any, Any], dados),  # <-- converte Mapping -> dict p/ mypy
                data_pedido,
            )
        )
    except Exception as e:
        print(f"[DEBUG janela-skip] Erro em dentro_periodo_selecionado: {e}")
        aplica_regras_neste_periodo = False

    # Regras/cupom/override só se dentro do período
    if aplica_regras_neste_periodo:
        try:
            regras_aplicadas: RegrasAplicadas = cast(
                RegrasAplicadas,
                aplicar_regras_transaction(
                    cast(dict[Any, Any], transacao),  # <-- Mapping -> dict
                    cast(dict[Any, Any], dados),  # <-- Mapping -> dict
                    cast(dict[Any, Any], skus_info),  # <-- Mapping[str, SKUInfo] -> dict[Any, Any]
                    produto_principal,
                )
                or {},
            )
        except Exception as e:
            print(f"[⚠️ regras] Erro em aplicar_regras_transaction: {e}")
            regras_aplicadas = RegrasAplicadas()
    else:
        regras_aplicadas = RegrasAplicadas()

    override_box: str | None = cast(str | None, regras_aplicadas.get("override_box"))
    brindes_extra_por_regra: Sequence[dict[str, Any]] = regras_aplicadas.get("brindes_extra", []) or []

    if override_box:
        produto_principal = override_box
        info_produto = skus_info.get(produto_principal, {}) or {}
        sku_principal = str(info_produto.get("sku", "") or "")
        peso_principal = cast(float | int, info_produto.get("peso", 0))

    tipo_assinatura: str = str(transacao.get("tipo_assinatura", "") or "")

    # Cupons personalizados só se dentro do período
    if aplica_regras_neste_periodo:
        if tipo_assinatura == "anuais":
            prod_custom = (cast(Mapping[str, Any], dados.get("cupons_personalizados_anual") or {})).get(cupom)
        elif tipo_assinatura == "bimestrais":
            prod_custom = (cast(Mapping[str, Any], dados.get("cupons_personalizados_bimestral") or {})).get(cupom)
        else:
            prod_custom = None
        if prod_custom and prod_custom in skus_info:
            produto_principal = cast(str, prod_custom)
            info_produto = skus_info.get(produto_principal, {}) or {}
            sku_principal = str(info_produto.get("sku", "") or "")
            peso_principal = cast(float | int, info_produto.get("peso", 0))

    # periodicidade: override manual → produto → inferência
    periodicidade: str = (
        str(
            dados.get("periodicidade_selecionada")
            or dados.get("periodicidade")
            or info_produto.get("periodicidade")
            or ("mensal" if tipo_assinatura == "mensais" else "bimestral")
            or ""
        )
        .strip()
        .lower()
    )

    # embutido via oferta (respeita timestamps E a janela)
    ofertas_embutidas = cast(Mapping[str, Any], dados.get("ofertas_embutidas") or {})
    nome_embutido: str = str(ofertas_embutidas.get(str(id_oferta).strip(), "") or "")

    ini_ts = _to_ts(dados.get("embutido_ini_ts"))
    end_ts = _to_ts(dados.get("embutido_end_ts"))
    dp_ts = _to_ts(data_pedido)

    incluir_embutido: bool = bool(
        nome_embutido
        and dp_ts is not None
        and ini_ts is not None
        and end_ts is not None
        and ini_ts <= dp_ts <= end_ts
        and aplica_regras_neste_periodo
    )
    valor_embutido: float = 0.0

    # 💰 tabela para assinaturas multi-ano
    tabela_valores: Mapping[tuple[str, str], float] = {
        ("anuais", "mensal"): 960,
        ("anuais", "bimestral"): 480,
        ("bianuais", "mensal"): 1920,
        ("bianuais", "bimestral"): 960,
        ("trianuais", "mensal"): 2880,
        ("trianuais", "bimestral"): 1440,
    }

    # Cálculo do valor da assinatura
    if is_upgrade or usar_valor_fixo:
        valor_assinatura = float(tabela_valores.get((tipo_assinatura, periodicidade), valor_total_pago))
        if incidence_type == "percent":
            try:
                desconto = float(coupon_info.get("incidence_value") or 0)
            except Exception:
                desconto = 0.0
            valor_assinatura = round(valor_assinatura * (1 - desconto / 100), 2)
        incluir_embutido = False
        valor_embutido = 0.0

    elif tipo_assinatura in ("anuais", "bianuais", "trianuais"):
        valor_assinatura = float(tabela_valores.get((tipo_assinatura, periodicidade), valor_total_pago))
        if incidence_type == "percent":
            try:
                desconto = float(coupon_info.get("incidence_value") or 0)
            except Exception:
                desconto = 0.0
            valor_assinatura = round(valor_assinatura * (1 - desconto / 100), 2)
        valor_embutido = max(0.0, round(valor_total_pago - valor_assinatura, 2))

    else:
        # Não é assinatura multi-ano → usa valor pago mesmo
        valor_assinatura = float(valor_total_pago)
        incluir_embutido = False
        valor_embutido = 0.0

    # divisor conforme período/periodicidade (com guarda)
    if tipo_assinatura == "trianuais":
        divisor = 36 if periodicidade == "mensal" else 18
    elif tipo_assinatura == "bianuais":
        divisor = 24 if periodicidade == "mensal" else 12
    elif tipo_assinatura == "anuais":
        divisor = 12 if periodicidade == "mensal" else 6
    elif tipo_assinatura == "bimestrais":
        divisor = 2 if periodicidade == "mensal" else 1
    elif tipo_assinatura == "mensais":
        divisor = 1
    else:
        divisor = 1

    divisor = max(int(divisor or 1), 1)
    valor_unitario: float = round(valor_assinatura / divisor, 2)
    valor_total: float = valor_unitario
    total_pedido: float = round(valor_unitario + (valor_embutido if incluir_embutido else 0.0), 2)

    return RetornoPedido(
        transaction_id=transaction_id,
        id_oferta=id_oferta,
        produto_principal=produto_principal,
        sku_principal=sku_principal,
        peso_principal=peso_principal,
        valor_unitario=valor_unitario,
        valor_total=valor_total,
        total_pedido=total_pedido,
        valor_embutido=valor_embutido,
        incluir_embutido=incluir_embutido,
        embutido=nome_embutido,
        brindes_extras=brindes_extra_por_regra,
        data_pedido=data_pedido,
        forma_pagamento=str(payment.get("method", "") or ""),
        usou_cupom=bool(cupom),
        tipo_plano=tipo_assinatura,
        periodicidade=periodicidade,
        divisor=divisor,
    )


def montar_resumo_final(
    linhas: Sequence[Mapping[str, Any]] | None,
    contagem: Mapping[str, Any] | None,
    estado: Mapping[str, Any] | None,
    modo: str = "assinaturas",
) -> tuple[str, str]:
    """
    Retorna (titulo, corpo) do resumo.
    """

    def _is_zero(v: Any) -> bool:
        s = str(v or "").strip()
        if not s:
            return False
        try:
            s_norm = s.replace(".", "").replace(",", ".")
            return abs(float(s_norm)) < 1e-9
        except Exception:
            return False

    def _pega_bloco(cont: Mapping[str, Any] | None, chaves: Iterable[str]) -> Mapping[str, Any]:
        if not cont:
            return {}
        for k in chaves:
            v = cont.get(k)
            if v is not None:
                return v or {}
        return {}

    def _normaliza_swaps(raw: Any) -> list[tuple[str, str, int]]:
        out: list[tuple[str, str, int]] = []
        if not raw:
            return out
        from collections import Counter as _Ctr

        if isinstance(raw, _Ctr):
            raw = dict(raw)
        if isinstance(raw, dict):
            aninhado = all(isinstance(v, dict) for v in raw.values())
            if aninhado:
                for de, sub in raw.items():
                    for para, qtd in (sub or {}).items():
                        try:
                            q = int(qtd or 0)
                        except Exception:
                            q = 0
                        if q > 0:
                            out.append((str(de), str(para), q))
                return out
            for k, qtd in raw.items():
                try:
                    q = int(qtd or 0)
                except Exception:
                    q = 0
                if q <= 0:
                    continue
                if isinstance(k, (tuple, list)) and len(k) == 2:
                    de, para = k
                else:
                    de_s, para_s = str(k), "?"
                    ks = str(k).split("->")
                    if len(ks) == 2:
                        de_s, para_s = ks[0].strip(), ks[1].strip()
                    else:
                        ks = str(k).split("→")
                        if len(ks) == 2:
                            de_s, para_s = ks[0].strip(), ks[1].strip()
                    de, para = de_s, para_s
                out.append((str(de), str(para), q))
        return out

    modo = (modo or "").strip().lower()
    linhas_seq: Sequence[Mapping[str, Any]] = linhas or []
    total_linhas = len(linhas_seq)

    produtos_ctr: Counter[str] = Counter()
    for lin in linhas_seq:
        if isinstance(lin, dict):
            nome = lin.get("Produto") or lin.get("produto") or lin.get("nome_produto") or ""
            nome = str(nome).strip()
            if nome:
                produtos_ctr[nome] += 1

    if modo == "produtos":
        titulo = "Resumo da Exportação (Produtos)"
        msg: list[str] = [f"📦 Linhas adicionadas: {total_linhas}"]
        if produtos_ctr:
            msg.append("\n🧾 Produtos adicionados:")
            for nome, qtd in produtos_ctr.most_common():
                msg.append(f"  - {nome}: {qtd}")
        else:
            msg.append("\n🧾 Produtos adicionados: 0")
        return titulo, "\n".join(msg)

    titulo = "Resumo da Exportação"
    resumo = f"📦 Linhas adicionadas: {total_linhas}\n\n📘 Assinaturas:\n"
    TIPOS: list[tuple[str, list[str]]] = [
        ("mensais", ["mensais", "mensal"]),
        ("bimestrais", ["bimestrais", "bimestral"]),
        ("anuais", ["anuais", "anual"]),
        ("bianuais", ["bianuais", "bianual"]),
        ("trianuais", ["trianuais", "trianual"]),
    ]

    for label, chaves in TIPOS:
        dados_bloco = _pega_bloco(contagem, chaves)
        assin = int(dados_bloco.get("assinaturas", 0) or 0)
        cupons = int(dados_bloco.get("cupons", 0) or 0)
        resumo += f"  - {label.capitalize()}: {assin} (cupons: {cupons})\n"

    extras_ctr: Counter[str] = Counter()
    for lin in linhas_seq:
        if not isinstance(lin, dict):
            continue
        nome = str(lin.get("Produto") or lin.get("produto") or "").strip()
        if not nome:
            continue
        if _is_zero(lin.get("Valor Unitário")) and _is_zero(lin.get("Valor Total")):
            extras_ctr[nome] += 1
    if extras_ctr:
        resumo += "\n🎁 Itens extras (brindes/embutidos):\n"
        for nome, qtd in extras_ctr.most_common():
            resumo += f"  - {nome}: {qtd}\n"

    swaps_raw = (estado or {}).get("alteracoes_box_detalhes") or (contagem or {}).get("alteracoes_box_detalhes")
    swaps_list = _normaliza_swaps(swaps_raw)
    if swaps_list:
        resumo += "\n🔁 Trocas de box (detalhes):\n"
        for de, para, qtd in sorted(swaps_list, key=lambda x: (-x[2], x[0], x[1])):
            resumo += f"  - {de} → {para}: {qtd}\n"
    else:
        tem_trocas = any(int(_pega_bloco(contagem, ch).get("alteracoes_box", 0) or 0) > 0 for _, ch in TIPOS)
        if tem_trocas:
            resumo += "\n🔁 Trocas de box (totais):\n"
            for label, chaves in TIPOS:
                dados_bloco = _pega_bloco(contagem, chaves)
                trocas = int(dados_bloco.get("alteracoes_box", 0) or 0)
                resumo += f"  - {label.capitalize()}: {trocas}\n"

    if produtos_ctr:
        resumo += "\n🧾 Produtos adicionados (todas as linhas):\n"
        for nome, qtd in produtos_ctr.most_common():
            resumo += f"  - {nome}: {qtd}\n"

    return titulo, resumo

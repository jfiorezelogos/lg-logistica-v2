from __future__ import annotations  # <- PRIMEIRA LINHA

# Imports da biblioteca padrão
import argparse
import calendar
import json
import logging
import os
import platform
import random
import re
import shutil
import subprocess
import sys
import threading
import time
import traceback
import unicodedata
import uuid
import xml.etree.ElementTree as ET
import zipfile
from calendar import monthrange
from collections import Counter, OrderedDict, defaultdict
from collections.abc import Callable, Hashable, Iterable, Mapping, MutableMapping, Sequence
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from contextlib import AbstractContextManager, suppress
from datetime import UTC, date, datetime, time as dtime, timedelta
from decimal import ROUND_HALF_UP, Decimal, InvalidOperation
from json import JSONDecodeError
from logging import Logger
from os import PathLike
from pathlib import Path
from threading import Event
from typing import TYPE_CHECKING, Any, Literal, Protocol, TypedDict, cast, overload
from zoneinfo import ZoneInfo

# Terceiros
import certifi
import openai
import pandas as pd
import requests
import urllib3
from brazilcep import exceptions, get_address_from_cep
from colorama import init
from dateutil.parser import parse as parse_date
from dateutil.relativedelta import relativedelta
from fpdf import FPDF
from openai import RateLimitError
from PyQt5 import QtCore
from PyQt5.QtCore import (
    QCoreApplication,
    QDate,
    QEvent,
    QModelIndex,
    QObject,
    QRunnable,
    Qt,
    QThread,
    QThreadPool,
    QTimer,
    pyqtBoundSignal,
    pyqtSignal,
    pyqtSlot,
)
from PyQt5.QtGui import QGuiApplication, QKeySequence
from PyQt5.QtWidgets import (
    QAbstractItemView,
    QApplication,
    QButtonGroup,
    QCheckBox,
    QComboBox,
    QDateEdit,
    QDesktopWidget,
    QDialog,
    QDialogButtonBox,
    QFileDialog,
    QGroupBox,
    QHBoxLayout,
    QHeaderView,
    QInputDialog,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QMessageBox,
    QProgressBar,
    QPushButton,
    QRadioButton,
    QShortcut,
    QSpinBox,
    QTableWidget,
    QTableWidgetItem,
    QTabWidget,
    QVBoxLayout,
    QWidget,
)
from reportlab.lib.pagesizes import A4
from reportlab.lib.units import mm
from reportlab.pdfgen import canvas
from unidecode import unidecode

# Seus módulos
from common.cli_safe import safe_cli

# Bootstrap de config (sem input_path)
from common.config_bootstrap import AppConfig, load_config, load_env
from common.errors import ExternalError, UserError
from common.http_client import http_get, http_post
from common.logging_setup import get_correlation_id, set_correlation_id
from common.paths import app_root, default_log_file, user_data_dir_path
from common.settings import settings
from common.validation import ensure_paths, validate_config

# 1) carrega variáveis de ambiente (.env se existir)
load_env()

# 2) carrega config (sem input_path) e resolve output_dir
CFG: AppConfig
CFG, CFG_PATH = load_config()
logger = logging.getLogger(__name__)
logger.info("config carregada", extra={"config_path": str(CFG_PATH), "output_dir": CFG.get("output_dir")})

init(autoreset=True)

os.environ["SSL_CERT_FILE"] = certifi.where()
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

BASE_URL_GURU = "https://digitalmanager.guru/api/v2"
HEADERS_GURU = {
    "Authorization": f"Bearer {settings.API_KEY_GURU}",
    "Content-Type": "application/json",
}

# ===================== CONFIGURAÇÕES =====================

# --------------------- UI / COMUNICADOR ------------------


class Comunicador(QObject):
    mostrar_mensagem = pyqtSignal(str, str, str)
    atualizar_progresso = pyqtSignal(str, int, int)


@pyqtSlot(str, str, str)
def slot_mostrar_mensagem(
    tipo: Literal["erro", "info", "warn", "warning"],
    titulo: str,
    texto: str,
) -> None:
    msg = QMessageBox()
    if tipo in ("erro",):
        msg.setIcon(QMessageBox.Critical)
    elif tipo in ("info",):
        msg.setIcon(QMessageBox.Information)
    else:  # "warn" / "warning" (ou qualquer outro → Warning)
        msg.setIcon(QMessageBox.Warning)
    msg.setWindowTitle(titulo)
    msg.setText(texto)
    msg.exec_()  # se migrar para PyQt6: use msg.exec()


comunicador_global = Comunicador()

comunicador_global.mostrar_mensagem.connect(slot_mostrar_mensagem)

# --------------------- BACKEND/PATH ----------------------


dados: dict[str, Any] = {}


# --------------------------------BACKEND / ESTADOS PLANILHA-------------------
linhas_planilha: list[dict[str, Any]] = []
transacoes: list[dict[str, Any]] = []
transacoes_obtidas = False

# -------------------------------UI/Flags de progresso / etapas-----------------
estado = {
    "transacoes_obtidas": False,
    "linhas_planilha": [],
    "numero_pedido_bling": None,
    "skus_info": {},
    "cancelador_global": threading.Event(),
}
barra_progresso = None

# -------------------------------BACKEND / TRANSPORTADORAS----------------------
transportadoras_var: dict[str, Any] = {}
transportadoras_lista = ["CORREIOS", "GFL", "GOL", "JET", "LOG"]

# -------------------------------BACKEND / SKUS--------------------------------
SKUS_FILENAME = "skus.json"

# 1) caminho do usuário (Windows: %LOCALAPPDATA%\lg-logistica\) — via common.paths
skus_path = user_data_dir_path() / SKUS_FILENAME

# 2) se ainda não existir, tentar "semear" a partir de um skus.json que venha no app (somente leitura)
seed_path = app_root() / SKUS_FILENAME  # se você versionar um skus.json "padrão" dentro do projeto

if skus_path.exists():
    skus_info = json.loads(Path(skus_path).read_text(encoding="utf-8"))
else:
    if seed_path.exists():
        # copia o seed para a área do usuário
        skus_path.write_bytes(seed_path.read_bytes())
        skus_info = json.loads(Path(skus_path).read_text(encoding="utf-8"))
    else:
        # cria um default mínimo e salva no diretório do usuário
        skus_info = {
            "Leviatã, de Thomas Hobbes": {"sku": "L002A", "peso": 1.10},
            "O Príncipe, Maquiavél": {"sku": "B002A", "peso": 0.70},
            "Isagoge, de Porfírio": {"sku": "B001A", "peso": 0.70},
            "Virgílio, o Pai do Ocidente": {"sku": "L001A", "peso": 0.50},
            "Heráclito": {"sku": "B003A", "peso": 0.70},
        }
        Path(skus_path).write_text(json.dumps(skus_info, indent=4, ensure_ascii=False), encoding="utf-8")

# Helpers datetime
TZ_APP = ZoneInfo("America/Sao_Paulo")


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


def ensure_aware_local(dt: datetime) -> datetime:
    return dt if dt.tzinfo else dt.replace(tzinfo=TZ_APP)


def to_date_yyyy_mm_dd(dt: datetime) -> str:
    """Yyyy-mm-dd (sem tz), quando o endpoint espera só data."""
    return ensure_aware_local(dt).date().isoformat()


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

# Mapear produtos do Guru


def coletar_ofertas_produto(product_id: str) -> list[dict[str, Any]]:
    url = f"{BASE_URL_GURU}/products/{product_id}/offers"
    headers = HEADERS_GURU
    ofertas: list[dict[str, Any]] = []
    cursor: str | None = None
    pagina = 1

    while True:
        try:
            params: dict[str, Any] = {"limit": 100}
            if cursor:
                params["cursor"] = cursor

            r = http_get(url, headers=headers, params=params, timeout=10)
            if r.status_code != 200:
                print(f"[❌ Guru] Erro {r.status_code} ao buscar ofertas do produto {product_id}: {r.text}")
                break

            data: dict[str, Any] = r.json()
            pagina_dados = data.get("data", [])
            print(f"[📄 Página {pagina}] {len(pagina_dados)} ofertas encontradas para produto {product_id}")

            ofertas += pagina_dados
            cursor = data.get("next_cursor")

            if not cursor:
                break

            pagina += 1

        except Exception as e:
            print(f"[❌ Guru] Exceção ao buscar ofertas do produto {product_id}: {e}")
            break

    print(f"[✅ Guru] Total de ofertas carregadas para o produto {product_id}: {len(ofertas)}")
    return ofertas


def coletar_produtos_guru() -> list[dict[str, Any]]:
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


def esta_no_ultimo_mes(
    ordered_at: datetime | None,
    duracao_meses: int | None,
    *,
    referencia: datetime | None = None,
) -> bool:
    """
    Janela do último mês (via TRANSACTIONS):
      [ordered_at + duracao_meses - 30d, ordered_at + duracao_meses]
    """
    if not ordered_at or not duracao_meses or duracao_meses <= 0:
        return False

    # referência timezone-aware em UTC (corrige DTZ003)
    if referencia is None:
        referencia = datetime.now(UTC)  # <- em <3.11: datetime.now(UTC)
    elif referencia.tzinfo is None:
        referencia = referencia.replace(tzinfo=UTC)

    # normaliza ordered_at para UTC-aware
    if ordered_at.tzinfo is None:
        ordered_at = ordered_at.replace(tzinfo=UTC)
    else:
        ordered_at = ordered_at.astimezone(UTC)

    data_fim = ordered_at + relativedelta(months=duracao_meses)
    janela_ini = data_fim - timedelta(days=30)
    return janela_ini <= referencia <= data_fim


def fetch_all_subscriptions() -> list[dict]:
    """Coleta todas as assinaturas do Guru, com paginação via cursor, aceitando Response ou dict."""
    headers = {
        "Authorization": f"Bearer {settings.API_KEY_GURU}",
        "Content-Type": "application/json",
    }

    cursor = None
    out: list[dict] = []

    while True:
        # monta URL com ou sem cursor
        url = f"{BASE_URL_GURU}/subscriptions"
        if cursor:
            url += f"?cursor={cursor}"

        resp = http_get(url, headers=headers)  # pode ser Response OU dict

        # --- normaliza para dict JSON ---
        try:
            data = resp if isinstance(resp, dict) else resp.json()
        except Exception:
            data = {}

        # ✅ formato confirmado: {"data": [ ... ]}
        items = data.get("data", [])
        if not isinstance(items, list):
            items = []

        # acumula resultados
        out.extend(items)

        # paginação por cursor
        cursor = data.get("next_cursor")
        has_more = bool(data.get("has_more_pages")) and not bool(data.get("on_last_page"))

        # critério de parada
        if not cursor or not has_more or not items:
            break

    return out


# ----------------- Mapeamentos auxiliares -----------------

_DUR_LABEL_TO_MONTHS: dict[str, int] = {
    # duração (rotulo → meses)
    "mensal": 1,
    "bimestral": 2,
    "trimestral": 3,
    "semestral": 6,
    "anual": 12,
    "18meses": 18,  # adição do usuário
    "bianual": 24,
    "trianual": 36,
}


def duration_label_to_months(label: str | None) -> int | None:
    if not label:
        return None
    return _DUR_LABEL_TO_MONTHS.get(label.strip().lower())


def periodicidade_normaliza(raw: str | None) -> str | None:
    if not raw:
        return None
    s = raw.strip().lower()
    if s in {"mensal", "bimestral"}:
        return s
    return None  # evita ruídos


def resolve_plano_por_product_id(
    product_id: str,
    skus_info: Mapping[str, Mapping[str, Any]],
) -> tuple[int | None, str | None]:
    """
    Retorna (duracao_em_meses, periodicidade) com base no product_id usando o skus.json.
    Aceita rótulos 'mensal','bimestral','semestral','anual','18meses','bianual','trianual'.
    """
    for _nome, info in skus_info.items():
        try:
            guru_ids = info.get("guru_ids") or []
            if str(product_id) in [str(g).strip() for g in guru_ids]:
                # duração pode estar como rótulo ou número/meses
                dur_label = (
                    (info.get("duracao") or info.get("duração") or info.get("duration_label") or "").strip().lower()
                )
                dur_num = info.get("duracao_meses") or info.get("duration_months")
                per = (info.get("periodicidade") or info.get("periodicidade_envio") or "").strip().lower()

                dur_meses = None
                if isinstance(dur_num, int) and dur_num > 0:
                    dur_meses = dur_num
                elif dur_label:
                    dur_meses = duration_label_to_months(dur_label)

                per_norm = periodicidade_normaliza(per)
                return (dur_meses, per_norm)
        except Exception:
            pass
    return (None, None)


# ----------------- Índices de subscriptions -----------------


def build_subscriptions_index(
    subscriptions: list[dict[str, Any]],
    skus_info: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    """
    Retorna dict por subscription_code:
      {
        subscription_code: {
          "active": bool,
          "product_id": str,
          "product_name": str,
          "duracao_meses": int | None,
          "periodicidade": "mensal" | "bimestral" | None
        }
      }
    """
    idx: dict[str, dict[str, Any]] = {}
    for item in subscriptions:
        data = item.get("data") or item  # robusto a formatos
        code = str(data.get("subscription_code") or data.get("code") or "").strip()
        if not code:
            continue
        last_status = str(data.get("last_status") or "").strip().lower()
        prod = data.get("product") or {}
        prod_id = str(prod.get("id") or "").strip()
        prod_name = str(prod.get("name") or "").strip()

        dur_meses, per = resolve_plano_por_product_id(prod_id, skus_info)

        idx[code] = {
            "active": last_status == "active",
            "product_id": prod_id,
            "product_name": prod_name,
            "duracao_meses": dur_meses,
            "periodicidade": per,
        }
    return idx


def mapear_assinaturas(
    skus_info: Mapping[str, Mapping[str, Any]],
) -> tuple[dict[str, list[str]], dict[str, dict[str, str]]]:
    assinaturas: dict[str, list[str]] = {
        "mensal": [],
        "bimestral": [],
        "trimestral": [],
        "semestral": [],
        "anual": [],
        "18meses": [],
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


def iniciar_mapeamento_produtos_guru(
    skus_info: Mapping[str, MutableMapping[str, Any]],
    produtos_guru: Sequence[Mapping[str, Any]] | None,
    skus_path: Path,
) -> None:
    class DialogoMapeamento(QDialog):
        def __init__(self) -> None:
            super().__init__()
            self.setWindowTitle("Mapear Produtos do Guru para Produtos Internos")
            self.setMinimumSize(800, 500)
            self.main_layout = QVBoxLayout(self)

            # mantém referências
            self.skus_info: MutableMapping[str, Any] = cast(MutableMapping[str, Any], skus_info)

            # helper para is_hidden
            def _is_hidden(p: Mapping[str, Any]) -> bool:
                raw = p.get("is_hidden", 0)
                # aceita 0/1, "0"/"1", True/False
                if isinstance(raw, str):
                    raw = raw.strip().lower()
                    if raw in {"true", "t", "yes", "y"}:
                        return True
                    if raw in {"false", "f", "no", "n", ""}:
                        return False
                    if raw.isdigit():
                        return int(raw) != 0
                    return bool(raw)  # fallback
                if isinstance(raw, int | float):  # ← antes: (int, float)
                    return int(raw) != 0
                return bool(raw)

            # filtra produtos visíveis (is_hidden = 0)
            base_produtos = [dict(p) for p in (produtos_guru or [])]
            visiveis = [p for p in base_produtos if not _is_hidden(p)]

            self.produtos: list[dict[str, Any]] = visiveis
            self.produtos_restantes: list[dict[str, Any]] = list(self.produtos)

            # Seletor de produto interno (não permite digitar)
            linha_nome: QHBoxLayout = QHBoxLayout()
            linha_nome.addWidget(QLabel("Selecionar produto interno:"))
            self.combo_nome_interno = QComboBox()
            self.combo_nome_interno.setEditable(False)
            linha_nome.addWidget(self.combo_nome_interno)
            self.main_layout.addLayout(linha_nome)

            # Lista de produtos do Guru
            self.lista = QListWidget()
            self.lista.setSelectionMode(QListWidget.MultiSelection)
            self.main_layout.addWidget(QLabel("Selecione os produtos do Guru a associar:"))
            self.main_layout.addWidget(self.lista)

            # Tipo: assinatura, produto, combo, brinde
            linha_tipo: QHBoxLayout = QHBoxLayout()
            self.radio_produto = QRadioButton("Produto")
            self.radio_assinatura = QRadioButton("Assinatura")
            self.radio_combo = QRadioButton("Combo")
            self.radio_brinde = QRadioButton("Brinde")
            self.radio_produto.setChecked(True)
            self.grupo_tipo = QButtonGroup()
            for rb in (self.radio_produto, self.radio_assinatura, self.radio_combo, self.radio_brinde):
                self.grupo_tipo.addButton(rb)
            linha_tipo.addWidget(QLabel("Tipo:"))
            linha_tipo.addWidget(self.radio_produto)
            linha_tipo.addWidget(self.radio_assinatura)
            linha_tipo.addWidget(self.radio_combo)
            linha_tipo.addWidget(self.radio_brinde)
            self.main_layout.addLayout(linha_tipo)

            # Assinatura: duração + periodicidade
            self.widget_assinatura = QWidget()
            linha_assin: QHBoxLayout = QHBoxLayout(self.widget_assinatura)
            self.combo_duracao = QComboBox()
            self.combo_duracao.addItems(
                ["mensal", "bimestral", "trimestral", "semestral", "anual", "18meses", "bianual", "trianual"]
            )
            linha_assin.addWidget(QLabel("Duração do plano:"))
            linha_assin.addWidget(self.combo_duracao)

            self.combo_periodicidade = QComboBox()
            self.combo_periodicidade.addItems(["mensal", "bimestral"])
            linha_assin.addWidget(QLabel("Periodicidade (envio):"))
            linha_assin.addWidget(self.combo_periodicidade)
            self.main_layout.addWidget(self.widget_assinatura)

            self.widget_assinatura.setVisible(self.radio_assinatura.isChecked())

            # Recarrega nomes internos quando muda o tipo
            self.radio_assinatura.toggled.connect(lambda _checked: self._on_tipo_changed())
            self.radio_produto.toggled.connect(lambda _checked: self._on_tipo_changed())
            self.radio_combo.toggled.connect(lambda _checked: self._on_tipo_changed())
            self.radio_brinde.toggled.connect(lambda _checked: self._on_tipo_changed())

            # Botões
            botoes: QHBoxLayout = QHBoxLayout()
            self.btn_salvar = QPushButton("Salvar e Próximo")
            self.btn_cancelar = QPushButton("Cancelar")
            botoes.addWidget(self.btn_salvar)
            botoes.addWidget(self.btn_cancelar)
            self.main_layout.addLayout(botoes)

            self.btn_salvar.clicked.connect(self.salvar_selecao)
            self.btn_cancelar.clicked.connect(self.reject)

            # Inicializa listas e combo
            self._recarregar_combo_interno()
            self.iniciar()

            # Preencher combo "Produto (Guru)" apenas com visíveis
            # (se quiser manter esse seletor em outra parte da UI)
            # Exemplo: se você tiver combo_produto_guru aqui, adicione:
            # self.combo_produto_guru = QComboBox()
            # for p in self.produtos:  # já filtrados
            #     texto = f'{p.get("name","") or p.get("id","")}  [{p.get("id","")}]'
            #     self.combo_produto_guru.addItem(texto, p.get("id"))

        # ----- helpers -----
        def _on_tipo_changed(self) -> None:
            self.widget_assinatura.setVisible(self.radio_assinatura.isChecked())
            self._recarregar_combo_interno()

        def _nomes_internos_para_tipo(self) -> list[str]:
            if self.radio_assinatura.isChecked():
                tipo_alvo = "assinatura"
            elif self.radio_combo.isChecked():
                tipo_alvo = "combo"
            elif self.radio_brinde.isChecked():
                tipo_alvo = "brinde"
            else:
                tipo_alvo = "produto"

            return sorted(
                [
                    n
                    for n, info in self.skus_info.items()
                    if str(cast(Mapping[str, Any], info).get("tipo", "")).strip().lower() == tipo_alvo
                ]
            )

        def _recarregar_combo_interno(self) -> None:
            self.combo_nome_interno.blockSignals(True)
            self.combo_nome_interno.clear()
            self.combo_nome_interno.addItems(self._nomes_internos_para_tipo())
            self.combo_nome_interno.blockSignals(False)

        # ----- UI data -----
        def iniciar(self) -> None:
            self.lista.clear()
            termo = ""  # sem filtro por enquanto
            for p in self.produtos:  # já filtrados por is_hidden = 0
                titulo = (p.get("name") or "").strip()
                product_id = str(p.get("id") or "").strip()
                market_id = str(p.get("marketplace_id") or "").strip()
                if not titulo and not market_id and not product_id:
                    continue

                alvo = unidecode(f"{titulo} {market_id}".lower())
                if termo and termo not in alvo:
                    continue

                label = f"{titulo} (id:{market_id})" if market_id else f"{titulo} (id:{product_id})"
                item = QListWidgetItem(label)
                item.setData(QtCore.Qt.ItemDataRole.UserRole, product_id)
                item.setData(QtCore.Qt.ItemDataRole.UserRole + 1, market_id)
                item.setToolTip(f"marketplace_id: {market_id or '-'}\nproduct_id: {product_id or '-'}")
                self.lista.addItem(item)

        # ----- salvar -----
        def salvar_selecao(self) -> None:
            nome_base_raw = self.combo_nome_interno.currentText().strip()
            if not nome_base_raw:
                QMessageBox.warning(self, "Aviso", "Você precisa selecionar um produto interno.")
                return

            itens = self.lista.selectedItems()
            if not itens:
                QMessageBox.warning(self, "Aviso", "Você precisa selecionar ao menos um produto do Guru.")
                return

            novos_ids: list[str] = [str(it.data(QtCore.Qt.ItemDataRole.UserRole) or "").strip() for it in itens]
            novos_ids = [gid for gid in novos_ids if gid]

            is_assinatura = self.radio_assinatura.isChecked()
            is_combo = self.radio_combo.isChecked()
            is_brinde = self.radio_brinde.isChecked()

            # ---- normalizadores auxiliares ----
            DUR_LABEL_TO_MONTHS = {
                "mensal": 1,
                "bimestral": 2,
                "trimestral": 3,
                "semestral": 6,
                "anual": 12,
                "18meses": 18,
                "bianual": 24,
                "trianual": 36,
            }
            PERIODS_OK = {"mensal", "bimestral"}

            if is_assinatura:
                duracao_lbl = (self.combo_duracao.currentText() or "").strip().lower()
                periodicidade = (self.combo_periodicidade.currentText() or "").strip().lower()

                if periodicidade not in PERIODS_OK:
                    QMessageBox.warning(self, "Aviso", "Periodicidade inválida. Selecione 'mensal' ou 'bimestral'.")
                    return
                if duracao_lbl not in DUR_LABEL_TO_MONTHS:
                    QMessageBox.warning(self, "Aviso", f"Duração inválida: {duracao_lbl}")
                    return

                nome_base = re.sub(
                    r"(?:\s*(?:\((?:mensal|bimestral)\)|-\s*(?:mensal|bimestral)))+$",
                    "",
                    nome_base_raw,
                    flags=re.IGNORECASE,
                ).strip()

                dest_key = f"{nome_base} ({periodicidade})"
            else:
                duracao_lbl = None
                periodicidade = None
                dest_key = nome_base_raw

            if is_assinatura and dest_key != nome_base_raw and nome_base_raw in self.skus_info:
                legado = cast(Mapping[str, Any], self.skus_info.pop(nome_base_raw) or {})
                alvo = cast(MutableMapping[str, Any], self.skus_info.setdefault(dest_key, {}))
                for k_list in ("guru_ids", "shopify_ids", "composto_de"):
                    v = cast(Sequence[Any] | None, legado.get(k_list))
                    if v:
                        alvo.setdefault(k_list, [])
                        for x in v:
                            if x not in alvo[k_list]:
                                alvo[k_list].append(x)
                for k, v in legado.items():
                    if k not in ("guru_ids", "shopify_ids", "composto_de"):
                        alvo.setdefault(k, v)

            entrada = cast(MutableMapping[str, Any], self.skus_info.setdefault(dest_key, {}))
            if is_assinatura:
                entrada["tipo"] = "assinatura"
                entrada["recorrencia"] = duracao_lbl
                entrada["duracao_meses"] = DUR_LABEL_TO_MONTHS[cast(str, duracao_lbl)]
                entrada["periodicidade"] = periodicidade  # "mensal" | "bimestral"
                entrada.setdefault("sku", "")
                entrada.setdefault("peso", 0.0)
                entrada.setdefault("composto_de", [])
            else:
                if is_combo:
                    entrada["tipo"] = "combo"
                elif is_brinde:
                    entrada["tipo"] = "brinde"
                else:
                    entrada["tipo"] = "produto"

                entrada.pop("recorrencia", None)
                entrada.pop("duracao_meses", None)
                entrada.pop("periodicidade", None)
                entrada.setdefault("sku", entrada.get("sku", ""))
                entrada.setdefault("peso", entrada.get("peso", 0.0))
                entrada.setdefault("composto_de", entrada.get("composto_de", []))

            entrada.setdefault("guru_ids", [])
            ja = set(map(str, cast(Sequence[Any], entrada["guru_ids"])))
            for gid in novos_ids:
                if gid and gid not in ja:
                    entrada["guru_ids"].append(gid)
                    ja.add(gid)

            with open(skus_path, "w", encoding="utf-8") as f:
                json.dump(self.skus_info, f, indent=4, ensure_ascii=False)

            QMessageBox.information(self, "Sucesso", f"'{dest_key}' mapeado com sucesso!")
            self.lista.clearSelection()
            self.iniciar()

    dlg = DialogoMapeamento()
    dlg.exec_()


############################################
# Diálogo de Edição de Regra
############################################


def gerar_uuid() -> str:
    return str(uuid.uuid4())


# === Canoniza: sempre expor/salvar em "rules", mas aceitar "regras" legado ===
class RegrasConfig(TypedDict):
    rules: list[dict[str, Any]]


class RuleEditorDialog(QDialog):
    """Editor de uma regra individual.

    Cria/edita um dict no formato:
      { "id": "...", "applies_to": "oferta"|"cupom", ... }
    """

    def __init__(
        self,
        parent: QWidget | None,
        skus_info: Mapping[str, Any],
        regra: dict[str, Any] | None = None,
        produtos_guru: list[dict[str, Any]] | None = None,
    ) -> None:
        super().__init__(parent)
        self.setWindowTitle("Regra (Oferta/Cupom)")
        self.setMinimumWidth(600)

        self.skus_info: Mapping[str, Any] = skus_info
        self.regra: dict[str, Any] = regra or {}
        self.produtos_guru: list[dict[str, Any]] = produtos_guru or []

        layout: QVBoxLayout = QVBoxLayout(self)

        # ====== Aplica a: oferta | cupom ======
        linha_aplica: QHBoxLayout = QHBoxLayout()
        lbl_aplica = QLabel("Aplica a:")
        self.combo_aplica = QComboBox()
        self.combo_aplica.addItems(["oferta", "cupom"])
        linha_aplica.addWidget(lbl_aplica)
        linha_aplica.addWidget(self.combo_aplica)
        layout.addLayout(linha_aplica)

        # ====== CUPOM ======
        self.widget_cupom = QWidget()
        layout_cupom: QHBoxLayout = QHBoxLayout(self.widget_cupom)
        layout_cupom.setContentsMargins(0, 0, 0, 0)
        layout_cupom.addWidget(QLabel("Cupom:"))
        self.input_cupom = QLineEdit()
        layout_cupom.addWidget(self.input_cupom)

        # ====== OFERTA ======
        self.widget_oferta = QWidget()
        layout_oferta: QVBoxLayout = QVBoxLayout(self.widget_oferta)
        layout_oferta.setContentsMargins(0, 0, 0, 0)

        linha_prod: QHBoxLayout = QHBoxLayout()
        linha_prod.addWidget(QLabel("Produto (Guru):"))
        self.combo_produto_guru = QComboBox()
        self.combo_produto_guru.setEditable(True)

        # Preencher produtos do Guru se fornecidos (opcional)
        for p in self.produtos_guru:
            texto = f'{p.get("name","") or p.get("id","")}  [{p.get("id","")}]'
            self.combo_produto_guru.addItem(texto, p.get("id"))

        linha_prod.addWidget(self.combo_produto_guru)

        btn_carregar_ofertas = QPushButton("Carregar ofertas")
        btn_carregar_ofertas.clicked.connect(self._carregar_ofertas)
        linha_prod.addWidget(btn_carregar_ofertas)

        layout_oferta.addLayout(linha_prod)

        linha_oferta: QHBoxLayout = QHBoxLayout()
        linha_oferta.addWidget(QLabel("Oferta:"))
        self.combo_oferta = QComboBox()
        linha_oferta.addWidget(self.combo_oferta)
        layout_oferta.addLayout(linha_oferta)

        # ====== Assinaturas (só para CUPOM) ======
        self.widget_assinaturas = QGroupBox("Assinaturas (apenas para CUPOM)")
        layout_ass: QVBoxLayout = QVBoxLayout(self.widget_assinaturas)
        self.lista_assinaturas = QListWidget()
        self.lista_assinaturas.setSelectionMode(QAbstractItemView.MultiSelection)

        assinaturas = [
            n for n, info in self.skus_info.items() if cast(Mapping[str, Any], info).get("tipo") == "assinatura"
        ]
        for nome in sorted(assinaturas):
            self.lista_assinaturas.addItem(QListWidgetItem(nome))
        layout_ass.addWidget(self.lista_assinaturas)

        # ====== Ação ======
        caixa_acao = QGroupBox("Ação")
        layout_acao: QVBoxLayout = QVBoxLayout(caixa_acao)

        linha_tipo: QHBoxLayout = QHBoxLayout()
        linha_tipo.addWidget(QLabel("Tipo de ação:"))
        self.combo_acao = QComboBox()
        self.combo_acao.addItems(["alterar_box", "adicionar_brindes"])
        linha_tipo.addWidget(self.combo_acao)
        layout_acao.addLayout(linha_tipo)

        # alterar_box → escolher box (produtos simples)
        self.widget_alterar = QWidget()
        layout_alt: QHBoxLayout = QHBoxLayout(self.widget_alterar)
        layout_alt.setContentsMargins(0, 0, 0, 0)
        layout_alt.addWidget(QLabel("Box substituto:"))
        self.combo_box = QComboBox()
        produtos_simples = [
            n
            for n, info in self.skus_info.items()
            if cast(Mapping[str, Any], info).get("tipo") != "assinatura"
            and not cast(Mapping[str, Any], info).get("composto_de")
        ]
        self.combo_box.addItems(sorted(produtos_simples))
        layout_alt.addWidget(self.combo_box)

        # adicionar_brindes → múltiplos itens simples (qualquer item NÃO-assinatura e NÃO-combo)
        self.widget_brindes = QWidget()
        layout_br: QVBoxLayout = QVBoxLayout(self.widget_brindes)
        layout_br.setContentsMargins(0, 0, 0, 0)
        self.lista_brindes = QListWidget()
        self.lista_brindes.setSelectionMode(QAbstractItemView.MultiSelection)

        itens_simples_para_brinde = [
            n
            for n, info in self.skus_info.items()
            if str(cast(Mapping[str, Any], info).get("tipo", "")).lower() != "assinatura"
            and not cast(Mapping[str, Any], info).get("composto_de")  # exclui combos
        ]
        for nome in sorted(itens_simples_para_brinde):
            self.lista_brindes.addItem(QListWidgetItem(nome))

        layout_br.addWidget(QLabel("Brindes a adicionar (produtos simples):"))
        layout_br.addWidget(self.lista_brindes)

        layout_acao.addWidget(self.widget_alterar)
        layout_acao.addWidget(self.widget_brindes)

        # ====== Montagem/ordem no diálogo ======
        layout.addWidget(self.widget_cupom)
        layout.addWidget(self.widget_oferta)
        layout.addWidget(self.widget_assinaturas)
        layout.addWidget(caixa_acao)

        # Botões OK/Cancelar
        btns = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        btns.accepted.connect(self._accept)
        btns.rejected.connect(self.reject)
        layout.addWidget(btns)

        # sinais
        self.combo_aplica.currentTextChanged.connect(self._toggle_aplica)
        self.combo_acao.currentTextChanged.connect(self._toggle_acao)

        # preencher se edição
        self._hydrate(self.regra)
        self._toggle_aplica(self.combo_aplica.currentText())
        self._toggle_acao(self.combo_acao.currentText())

    def _hydrate(self, regra: Mapping[str, Any]) -> None:
        applies_to = cast(str, regra.get("applies_to", "oferta"))
        self.combo_aplica.setCurrentText(applies_to)

        if applies_to == "cupom":
            self.input_cupom.setText(str((regra.get("cupom") or {}).get("nome", "")))

        if applies_to == "oferta":
            prod_id = str((regra.get("oferta") or {}).get("produto_id", "") or "")
            oferta_id = str((regra.get("oferta") or {}).get("oferta_id", "") or "")
            idx_prod = max(0, self.combo_produto_guru.findData(prod_id))
            self.combo_produto_guru.setCurrentIndex(idx_prod)

            if prod_id:
                self._carregar_ofertas()
                oferta_id = str((regra.get("oferta") or {}).get("oferta_id", "") or "")
                idx_of = self.combo_oferta.findData(oferta_id)

                if idx_of == -1 and oferta_id:
                    nome_existente = str((regra.get("oferta") or {}).get("nome", "") or "")
                    display = f"{(nome_existente or oferta_id)} [{oferta_id}]"
                    self.combo_oferta.addItem(display, oferta_id)
                    idx_of = self.combo_oferta.count() - 1
                    self.combo_oferta.setItemData(idx_of, nome_existente or "", int(Qt.UserRole) + 1)

                self.combo_oferta.setCurrentIndex(max(0, idx_of))

        # assinaturas
        assinaturas = cast(list[str], regra.get("assinaturas", []) or [])
        if assinaturas:
            selecionadas = set(assinaturas)
            for i in range(self.lista_assinaturas.count()):
                item = self.lista_assinaturas.item(i)
                if item is None:
                    continue
                if item.text() in selecionadas:
                    item.setSelected(True)

        # ação
        action = cast(Mapping[str, Any], regra.get("action", {}) or {})
        self.combo_acao.setCurrentText(str(action.get("type", "alterar_box")))

        if action.get("type") == "alterar_box":
            box = str(action.get("box", "") or "")
            idx = max(0, self.combo_box.findText(box))
            self.combo_box.setCurrentIndex(idx)

        if action.get("type") == "adicionar_brindes":
            brindes = cast(list[str], action.get("brindes", []) or [])
            selecionadas = set(brindes)
            for i in range(self.lista_brindes.count()):
                it = self.lista_brindes.item(i)
                if it is None:
                    continue
                if it.text() in selecionadas:
                    it.setSelected(True)

    def _toggle_aplica(self, applies_to: str) -> None:
        is_cupom = applies_to == "cupom"
        self.widget_cupom.setVisible(is_cupom)
        self.widget_assinaturas.setVisible(is_cupom)

        is_oferta = applies_to == "oferta"
        self.widget_oferta.setVisible(is_oferta)

    def _toggle_acao(self, tipo: str) -> None:
        self.widget_alterar.setVisible(tipo == "alterar_box")
        self.widget_brindes.setVisible(tipo == "adicionar_brindes")

    def _carregar_ofertas(self) -> None:
        prod_data = self.combo_produto_guru.currentData()
        prod_id = str(prod_data) if prod_data is not None else ""
        if not prod_id:
            txt = self.combo_produto_guru.currentText()
            if "[" in txt and "]" in txt:
                prod_id = txt.split("[")[-1].split("]")[0].strip()

        self.combo_oferta.clear()
        if not prod_id:
            return

        ofertas = coletar_ofertas_produto(prod_id) or []
        for o in ofertas:
            oid = str(o.get("id", "") or "")
            nome = str(o.get("name") or oid or "Oferta")
            self.combo_oferta.addItem(f"{nome} [{oid}]", oid)
            idx = self.combo_oferta.count() - 1
            self.combo_oferta.setItemData(idx, nome, Qt.UserRole + 1)

    def _accept(self) -> None:
        applies_to = self.combo_aplica.currentText()

        # ===== Validação =====
        if applies_to == "cupom":
            cupom = self.input_cupom.text().strip()
            if not cupom:
                QMessageBox.warning(self, "Validação", "Informe o nome do cupom.")
                return
        elif applies_to == "oferta":
            prod_data = self.combo_produto_guru.currentData()
            prod_id = str(prod_data) if prod_data is not None else ""
            if not prod_id:
                txt_prod = self.combo_produto_guru.currentText()
                if "[" in txt_prod and "]" in txt_prod:
                    prod_id = txt_prod.split("[")[-1].split("]")[0].strip()
            of_data = self.combo_oferta.currentData()
            of_id = str(of_data) if of_data is not None else ""
            if not (prod_id and of_id):
                QMessageBox.warning(self, "Validação", "Selecione produto e oferta do Guru.")
                return

        action_type = self.combo_acao.currentText()
        if action_type == "alterar_box":
            if not self.combo_box.currentText().strip():
                QMessageBox.warning(self, "Validação", "Selecione o box substituto.")
                return
        else:
            brindes_sel = [it.text() for it in self.lista_brindes.selectedItems()]
            if not brindes_sel:
                QMessageBox.warning(self, "Validação", "Selecione ao menos um brinde.")
                return
            # valida: todos os selecionados devem ser NÃO-assinatura e NÃO-combo
            invalidos = []
            for b in brindes_sel:
                inf = cast(Mapping[str, Any], self.skus_info.get(b, {}))
                tipo_b = str(inf.get("tipo", "")).lower()
                eh_assin = tipo_b == "assinatura"
                eh_combo = bool(inf.get("composto_de"))
                if eh_assin or eh_combo:
                    invalidos.append(b)
            if invalidos:
                QMessageBox.warning(
                    self,
                    "Validação",
                    "Os itens a seguir não podem ser usados como brinde (assinatura/combo): " + ", ".join(invalidos),
                )
                return

        # ===== Construção do objeto da regra =====
        rid = self.regra.get("id")
        if not rid:
            try:
                rid = gerar_uuid()
            except NameError:
                import uuid

                rid = str(uuid.uuid4())

        regra_nova: dict[str, Any] = {
            "id": rid,
            "applies_to": applies_to,
            "action": {"type": action_type},
        }

        if applies_to == "cupom":
            cupom_nome = self.input_cupom.text().strip().upper()
            regra_nova["cupom"] = {"nome": cupom_nome}

            assin_sel = [it.text() for it in self.lista_assinaturas.selectedItems()]
            _seen: set[str] = set()
            regra_nova["assinaturas"] = list(dict.fromkeys(assin_sel))

        else:  # oferta
            idx_of = self.combo_oferta.currentIndex()
            of_nome = self.combo_oferta.itemData(idx_of, Qt.UserRole + 1)
            if not of_nome:
                of_text = (self.combo_oferta.currentText() or "").strip()
                of_nome = of_text.split("[", 1)[0].strip() if "[" in of_text else of_text

            # prod_id / of_id já validados acima
            prod_id = str(self.combo_produto_guru.currentData() or "").strip() or prod_id
            of_id = str(self.combo_oferta.currentData() or "").strip()

            regra_nova["oferta"] = {
                "produto_id": prod_id,
                "oferta_id": of_id,
                "nome": str(of_nome or ""),
            }

        if action_type == "alterar_box":
            regra_nova["action"]["box"] = self.combo_box.currentText().strip()
        else:
            brs = [it.text() for it in self.lista_brindes.selectedItems()]
            regra_nova["action"]["brindes"] = list(dict.fromkeys(brs))

        self.regra = regra_nova
        self.accept()

    def get_regra(self) -> dict[str, Any]:
        return self.regra


class RuleManagerDialog(QDialog):
    def __init__(
        self,
        parent: QWidget | None,
        estado: MutableMapping[str, Any],
        skus_info: Any,
        config_path: str,
    ) -> None:
        super().__init__(parent)
        self.setWindowTitle("⚖️ Regras (oferta/cupom)")
        self.setMinimumSize(900, 600)

        self.estado: MutableMapping[str, Any] = estado
        self.skus_info: Any = skus_info
        self.config_path: str = config_path

        # garante que estado["rules"] exista
        self.estado.setdefault("rules", carregar_regras(self.config_path))

        # índices auxiliares
        self._prod_index: dict[str, dict[str, Any]] = {}
        self._offer_index: dict[str, dict[str, Any]] = {}

        layout: QVBoxLayout = QVBoxLayout(self)

        # 🔎 Barra de busca
        linha_busca: QHBoxLayout = QHBoxLayout()
        self.input_search = QLineEdit(self)
        self.input_search.setPlaceholderText("Buscar por cupom / oferta / tipo de ação...")
        linha_busca.addWidget(QLabel("Pesquisar:"))
        linha_busca.addWidget(self.input_search)
        layout.addLayout(linha_busca)

        # ===== Abas com tabelas =====
        self.tabs: QTabWidget = QTabWidget(self)
        layout.addWidget(self.tabs)

        # --- Aba: Cupons
        self.tab_cupons: QWidget = QWidget(self)
        v_cupons: QVBoxLayout = QVBoxLayout(self.tab_cupons)
        self.tbl_cupons: QTableWidget = QTableWidget(self.tab_cupons)
        self.tbl_cupons.setColumnCount(4)
        self.tbl_cupons.setHorizontalHeaderLabels(["Cupom", "Tipo de ação", "Box/Brindes", "Plano"])
        self.tbl_cupons.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.tbl_cupons.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.tbl_cupons.setSelectionMode(QAbstractItemView.SingleSelection)
        self.tbl_cupons.setEditTriggers(QAbstractItemView.NoEditTriggers)
        v_cupons.addWidget(self.tbl_cupons)
        self.tabs.addTab(self.tab_cupons, "Cupons")

        # --- Aba: Ofertas
        self.tab_ofertas: QWidget = QWidget(self)
        v_ofertas: QVBoxLayout = QVBoxLayout(self.tab_ofertas)
        self.tbl_ofertas: QTableWidget = QTableWidget(self.tab_ofertas)
        self.tbl_ofertas.setColumnCount(2)
        self.tbl_ofertas.setHorizontalHeaderLabels(["Nome da oferta", "Brinde"])
        self.tbl_ofertas.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.tbl_ofertas.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.tbl_ofertas.setSelectionMode(QAbstractItemView.SingleSelection)
        self.tbl_ofertas.setEditTriggers(QAbstractItemView.NoEditTriggers)
        v_ofertas.addWidget(self.tbl_ofertas)
        self.tabs.addTab(self.tab_ofertas, "Ofertas")

        # ===== Botões =====
        linha_btns: QHBoxLayout = QHBoxLayout()
        self.btn_add = QPushButton("+ Adicionar")
        self.btn_edit = QPushButton("✏️ Editar")
        self.btn_dup = QPushButton("📄 Duplicar")
        self.btn_del = QPushButton("🗑️ Remover")
        self.btn_up = QPushButton("⬆️ Subir")
        self.btn_down = QPushButton("⬇️ Descer")
        self.btn_salvar = QPushButton("💾 Salvar")
        linha_btns.addWidget(self.btn_add)
        linha_btns.addWidget(self.btn_edit)
        linha_btns.addWidget(self.btn_dup)
        linha_btns.addWidget(self.btn_del)
        linha_btns.addStretch(1)
        linha_btns.addWidget(self.btn_up)
        linha_btns.addWidget(self.btn_down)
        linha_btns.addWidget(self.btn_salvar)
        layout.addLayout(linha_btns)

        # mapas (linha -> índice global em estado["rules"])
        self._map_cupons: list[int] = []
        self._map_ofertas: list[int] = []

        # Conexões
        self.btn_add.clicked.connect(self._add)
        self.btn_edit.clicked.connect(self._edit)
        self.btn_dup.clicked.connect(self._dup)
        self.btn_del.clicked.connect(self._del)
        self.btn_up.clicked.connect(self._up)
        self.btn_down.clicked.connect(self._down)
        self.btn_salvar.clicked.connect(self._salvar)
        self.input_search.textChanged.connect(lambda _txt: self._refresh_tables(self.input_search.text()))

        # índices e preenchimento
        self._build_indices()
        self._refresh_tables()

    # ---------- índices / helpers ----------
    def _build_indices(self) -> None:
        """Monta índices de produto/oferta a partir do estado."""
        produtos = self.estado.get("produtos_guru") or []
        self._prod_index = {}
        self._offer_index = {}

        for p in produtos:
            pid = str(p.get("id") or p.get("product_id") or "")
            if pid:
                self._prod_index[pid] = p
            for o in p.get("offers") or []:
                oid = str(o.get("id") or o.get("oferta_id") or "")
                if oid:
                    self._offer_index[oid] = o

        for o in self.estado.get("ofertas_guru") or []:
            oid = str(o.get("id") or o.get("oferta_id") or "")
            if oid and oid not in self._offer_index:
                self._offer_index[oid] = o

    def _label_produto(self, produto_id: str) -> str:
        """Exibe marketplace_id - nome; fallback para product_id se faltar."""
        p = self._prod_index.get(str(produto_id))
        if not p:
            return f"{produto_id or '?'}"
        mkt = p.get("marketplace_id") or p.get("shopify_id") or p.get("marketplaceId")
        nome = p.get("title") or p.get("name") or p.get("nome") or f"Produto {produto_id}"
        return f"{mkt} - {nome}" if mkt else f"{produto_id} - {nome}"

    def _label_oferta(self, oferta_id: object) -> str:
        oid = str(oferta_id or "")
        o = self._offer_index.get(oid)
        nome = o.get("name") if o else None
        if not nome:
            nome = (o or {}).get("nome") or (o or {}).get("title")
        return nome or oid or "?"

    def _format_assinaturas(self, r: Mapping[str, Any]) -> str:
        raw = (
            r.get("assinaturas")
            or (r.get("cupom") or {}).get("assinaturas")
            or (r.get("oferta") or {}).get("assinaturas")
            or []
        )
        if isinstance(raw, str):
            raw = [raw]

        def pretty(s: str) -> str:
            if not s:
                return ""
            t = str(s).strip()
            t = re.sub(r"\s*\(.*?\)\s*", "", t, flags=re.I)  # remove parênteses
            t = re.sub(r"^\s*assinatura\s+", "", t, flags=re.I)
            t = re.split(r"\s*[\u2013\u2014-]\s*", t)[0].strip()
            m = re.search(r"(\d+)\s*anos?", t, flags=re.I)
            if m:
                return f"{int(m.group(1))} anos"
            if re.search(r"\banual\b", t, flags=re.I):
                return "Anual"
            if re.search(r"\bbimestral\b", t, flags=re.I):
                return "Bimestral"
            if re.search(r"\bmensal\b", t, flags=re.I):
                return "Mensal"
            return t.title()

        vistos: set[str] = set()
        out: list[str] = []
        for item in raw:
            ptxt = pretty(str(item))
            k = ptxt.lower()
            if ptxt and k not in vistos:
                vistos.add(k)
                out.append(ptxt)
        return ", ".join(out)

    def _tipo_acao(self, a: dict[str, Any] | None) -> str:
        return (a or {}).get("type") or (a or {}).get("acao") or ""

    def _coletar_brindes(self, action: dict[str, Any] | None) -> list[dict[str, Any]]:
        if not action:
            return []
        keys = ["brindes", "gifts", "add_items", "add", "extras", "itens", "items"]
        val = next((action.get(k) for k in keys if action.get(k) is not None), None)
        if val is None:
            return []
        if isinstance(val, dict):
            val = [val]
        itens: list[dict[str, Any]] = []
        for g in val:
            if isinstance(g, str):
                itens.append({"nome": g.strip(), "qtd": 1})
            elif isinstance(g, dict):
                qtd = g.get("qtd") or g.get("qty") or g.get("quantidade") or 1
                pid = g.get("produto_id")
                nome = (
                    (g.get("nome") or "").strip()
                    or (self._label_produto(str(pid)) if pid is not None else "").strip()
                    or (g.get("sku") or "").strip()
                    or "?"
                )
                itens.append({"nome": nome, "qtd": int(qtd)})
        agg: OrderedDict[str, int] = OrderedDict()
        for it in itens:
            agg[it["nome"]] = agg.get(it["nome"], 0) + it["qtd"]
        return [{"nome": k, "qtd": v} for k, v in agg.items()]

    def _pegar_box(self, action: dict[str, Any] | None) -> str:
        if not action:
            return ""
        for k in ["novo_box", "box", "replace_box", "swap_box", "box_name"]:
            if action.get(k):
                return str(action[k]).strip()
        return ""

    # ---------- chaves / upsert / dedup ----------
    def _rule_key(self, r: Mapping[str, Any]) -> tuple[str, str, str]:
        """
        Chave de upsert/dedup:
        - cupom:  ("cupom", CUPOM.NOME (upper/trim), action.type)
        - oferta: ("oferta", oferta.oferta_id,          action.type)
        """
        applies = (r.get("applies_to") or "oferta").strip().lower()
        a = r.get("action") or {}
        action_type = str(a.get("type") or a.get("acao") or "").strip().lower()
        if applies == "cupom":
            cupom_nome = str((r.get("cupom") or {}).get("nome") or "").strip().upper()
            return ("cupom", cupom_nome, action_type)
        else:
            of = r.get("oferta") or {}
            oferta_id = str(of.get("oferta_id") or of.get("id") or "").strip()
            return ("oferta", oferta_id, action_type)

    def _index_by_key(self) -> dict[tuple[str, str, str], int]:
        """Mapeia chave -> índice em estado['rules'] (última ocorrência vence)."""
        idx: dict[tuple[str, str, str], int] = {}
        for i, r in enumerate(self.estado.get("rules", [])):
            idx[self._rule_key(r)] = i
        return idx

    def _upsert_rule(self, nova: dict[str, Any]) -> int:
        """
        Insere ou substitui regra por chave composta (retorna índice final).
        Mantém agrupamento por applies_to: se substituir, preserva a posição;
        se inserir, coloca ao fim do grupo correspondente.
        """
        key = self._rule_key(nova)
        rules = self.estado.setdefault("rules", [])
        bykey = self._index_by_key()

        if key in bykey:
            i = bykey[key]
            rules[i] = nova
            return i

        applies = key[0]  # "cupom" | "oferta"
        insert_pos = len(rules)
        for j in range(len(rules) - 1, -1, -1):
            if (rules[j].get("applies_to") or "oferta").strip().lower() == applies:
                insert_pos = j + 1
                break
        rules.insert(insert_pos, nova)
        return insert_pos

    def _dedup_inplace(self) -> None:
        """Remove duplicados por chave mantendo a última ocorrência."""
        seen: set[tuple[str, str, str]] = set()
        deduped: list[dict[str, Any]] = []
        for r in reversed(self.estado.get("rules", [])):
            k = self._rule_key(r)
            if k in seen:
                continue
            seen.add(k)
            deduped.append(r)
        deduped.reverse()
        self.estado["rules"] = deduped

    # ---------- UI refresh ----------
    def _refresh_tables(self, query: str = "") -> None:
        # reconstruir índices caso o estado tenha sido atualizado externamente
        self._build_indices()

        q = (query or "").strip().lower()

        # zera as tabelas e mapas
        self.tbl_cupons.setRowCount(0)
        self.tbl_ofertas.setRowCount(0)
        self._map_cupons = []
        self._map_ofertas = []

        for i, r in enumerate(self.estado["rules"]):
            a = r.get("action") or {}
            applies = (r.get("applies_to") or "oferta").strip().lower()

            if applies == "cupom":
                cupom = ((r.get("cupom") or {}).get("nome") or "").strip()
                tipo = self._tipo_acao(a) or ""
                box = self._pegar_box(a)
                if self._tipo_acao(a) == "adicionar_brindes":
                    brindes = self._coletar_brindes(a)
                    box_ou_brindes = " | ".join(f"{b['qtd']}x {b['nome']}" for b in brindes) or "—"
                else:
                    box_ou_brindes = box or "—"
                plano = self._format_assinaturas(r) or "—"

                # 🔍 filtro
                alvo = f"{cupom} {tipo} {box_ou_brindes} {plano}".lower()
                if q and q not in alvo:
                    continue

                row = self.tbl_cupons.rowCount()
                self.tbl_cupons.insertRow(row)
                self.tbl_cupons.setItem(row, 0, QTableWidgetItem(cupom or "—"))
                self.tbl_cupons.setItem(row, 1, QTableWidgetItem(tipo or "—"))
                self.tbl_cupons.setItem(row, 2, QTableWidgetItem(box_ou_brindes))
                self.tbl_cupons.setItem(row, 3, QTableWidgetItem(plano))
                self._map_cupons.append(i)

            else:
                of = r.get("oferta") or {}
                nome = (of.get("nome") or self._label_oferta(of.get("oferta_id")) or "—").strip()
                tipo = self._tipo_acao(a) or ""
                brinde = ""
                if tipo == "adicionar_brindes":
                    brindes = self._coletar_brindes(a)
                    brinde = " | ".join(f"{b['qtd']}x {b['nome']}" for b in brindes) or "—"
                brinde = brinde or "—"

                # 🔍 filtro
                alvo = f"{nome} {brinde} {tipo}".lower()
                if q and q not in alvo:
                    continue

                row = self.tbl_ofertas.rowCount()
                self.tbl_ofertas.insertRow(row)
                self.tbl_ofertas.setItem(row, 0, QTableWidgetItem(nome))
                self.tbl_ofertas.setItem(row, 1, QTableWidgetItem(brinde))
                self._map_ofertas.append(i)

    # ---------- helpers de seleção ----------
    def _current_table_and_map(self) -> tuple[QTableWidget, list[int]]:
        if self.tabs.currentWidget() is self.tab_cupons:
            return self.tbl_cupons, self._map_cupons
        return self.tbl_ofertas, self._map_ofertas

    def _selected_index(self) -> int | None:
        table, idx_map = self._current_table_and_map()
        row = table.currentRow()
        if row < 0 or row >= len(idx_map):
            return None
        return idx_map[row]

    # ---------- ações ----------
    def _add(self) -> None:
        dlg = RuleEditorDialog(self, self.skus_info, regra=None, produtos_guru=self.estado.get("produtos_guru"))
        if dlg.exec_() == QDialog.Accepted:
            idx = self._upsert_rule(dlg.get_regra())
            self._refresh_tables(self.input_search.text())
            self._reselect(idx)

    def _edit(self) -> None:
        idx = self._selected_index()
        if idx is None:
            return
        regra = self.estado["rules"][idx]
        dlg = RuleEditorDialog(self, self.skus_info, regra=regra, produtos_guru=self.estado.get("produtos_guru"))
        if dlg.exec_() == QDialog.Accepted:
            idx2 = self._upsert_rule(dlg.get_regra())
            self._refresh_tables(self.input_search.text())
            self._reselect(idx2)

    def _dup(self) -> None:
        idx = self._selected_index()
        if idx is None:
            return
        r = json.loads(json.dumps(self.estado["rules"][idx]))  # deep copy
        r["id"] = gerar_uuid()
        # duplicar SEM upsert (intencional, pois é uma cópia)
        self.estado["rules"].insert(idx + 1, r)
        self._refresh_tables(self.input_search.text())
        self._reselect(idx + 1)

    def _del(self) -> None:
        idx = self._selected_index()
        if idx is None:
            return
        if (
            QMessageBox.question(self, "Confirmar", "Excluir esta regra?", QMessageBox.Yes | QMessageBox.No)
            == QMessageBox.Yes
        ):
            del self.estado["rules"][idx]
            self._refresh_tables(self.input_search.text())

    def _up(self) -> None:
        idx = self._selected_index()
        if idx is None:
            return
        self._move_relative_in_group(idx, -1)

    def _down(self) -> None:
        idx = self._selected_index()
        if idx is None:
            return
        self._move_relative_in_group(idx, +1)

    def _salvar(self) -> None:
        try:
            # dedup por chave composta, mantendo a última edição
            self._dedup_inplace()
            salvar_regras(self.config_path, self.estado["rules"])
            QMessageBox.information(self, "Salvo", "Regras salvas em config_ofertas.json.")
        except Exception as e:
            QMessageBox.critical(self, "Erro", f"Falha ao salvar: {e}")

    # ---------- movimento preservando o agrupamento ----------
    def _move_relative_in_group(self, idx_global: int, delta: int) -> None:
        """Move a regra idx_global para cima/baixo, trocando apenas com vizinhos do MESMO grupo (applies_to)."""
        if not -1 <= delta <= 1 or delta == 0:
            return
        rules = self.estado["rules"]
        if not 0 <= idx_global < len(rules):
            return
        group = (rules[idx_global].get("applies_to") or "oferta").strip().lower()
        j = idx_global + delta
        while 0 <= j < len(rules) and (rules[j].get("applies_to") or "oferta").strip().lower() != group:
            j += delta
        if 0 <= j < len(rules):
            rules[idx_global], rules[j] = rules[j], rules[idx_global]
            self._refresh_tables(self.input_search.text())
            self._reselect(j)

    def _reselect(self, idx_global: int) -> None:
        """Após refresh, reposiciona a seleção na aba/tabela correspondente a idx_global."""
        r = self.estado["rules"][idx_global]
        if (r.get("applies_to") or "oferta").strip().lower() == "cupom":
            for row, gi in enumerate(self._map_cupons):
                if gi == idx_global:
                    self.tabs.setCurrentWidget(self.tab_cupons)
                    self.tbl_cupons.setCurrentCell(row, 0)
                    return
        else:
            for row, gi in enumerate(self._map_ofertas):
                if gi == idx_global:
                    self.tabs.setCurrentWidget(self.tab_ofertas)
                    self.tbl_ofertas.setCurrentCell(row, 0)
                    return


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


def iniciar_gerenciador_regras(
    estado: MutableMapping[str, Any],
    skus_info: Any,
) -> None:
    config_path = os.path.join(os.path.dirname(__file__), "config_ofertas.json")
    # opcional: carregar produtos do Guru para o editor
    try:
        estado["produtos_guru"] = coletar_produtos_guru()
    except Exception:
        estado["produtos_guru"] = []
    dlg = RuleManagerDialog(None, estado, skus_info, config_path)
    dlg.exec_()


# Gerenciamento de barra de progresso na interface.


# helper opcional para usar no timeout
def with_suppress_close(gerenciador: GerenciadorProgresso) -> None:
    with suppress(Exception):
        gerenciador.fechar()


class GerenciadorProgresso(QObject):
    atualizar_signal = pyqtSignal(str, int, int)
    finalizado_signal = pyqtSignal()

    def __init__(
        self,
        *,
        titulo: str = "Progresso",
        com_percentual: bool = True,
        estado_global: MutableMapping[str, Any] | None = None,
        logger_obj: Logger | None = None,
    ) -> None:
        super().__init__()

        self.cancelado: bool = False
        self.com_percentual: bool = com_percentual
        self._ja_fechado: bool = False
        self.janela_feita: bool = False

        # estado como dict-like mutável
        self.estado: MutableMapping[str, Any] = (
            cast(MutableMapping[str, Any], estado_global) if estado_global is not None else {}
        )
        self.logger: Logger | None = logger_obj

        try:
            self.janela: QDialog = QDialog()
            self.janela.setWindowTitle(titulo)
            self.janela.setFixedSize(500, 160)
            self.janela.setAttribute(QtCore.Qt.WidgetAttribute.WA_DeleteOnClose, True)

            layout: QVBoxLayout = QVBoxLayout(self.janela)

            self.label_status: QLabel = QLabel("Iniciando...")
            self.label_status.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
            layout.addWidget(self.label_status)

            self.barra: QProgressBar = QProgressBar()
            if not self.com_percentual:
                self.barra.setRange(0, 0)
            layout.addWidget(self.barra)

            self.botao_cancelar: QPushButton = QPushButton("Cancelar")
            self.botao_cancelar.clicked.connect(self.cancelar)
            layout.addWidget(self.botao_cancelar)

            # Stubs do PyQt às vezes não aceitam o kwarg 'type' -> silenciar para mypy
            self.atualizar_signal.connect(self._atualizar_seguro)

            self.janela.show()
            self.janela.raise_()
            self.janela.activateWindow()
            self.janela.showNormal()

            screen = QGuiApplication.primaryScreen().availableGeometry()
            x = screen.center().x() - self.janela.width() // 2
            y = screen.center().y() - self.janela.height() // 2
            self.janela.move(x, y)

            QApplication.processEvents()

        except Exception as e:
            if self.logger:
                self.logger.exception("Erro ao inicializar janela de progresso")
            else:
                print(f"[❌] Erro ao inicializar janela: {e}")

    def cancelar(self) -> None:
        self.cancelado = True
        self.label_status.setText("Cancelado pelo usuário.")
        self.botao_cancelar.setEnabled(False)

        cancelador = self.estado.get("cancelador_global")
        if isinstance(cancelador, Event):
            cancelador.set()
        else:
            self._log_warning("[🛑] Cancelamento detectado, mas sem Event válido.")

        print("[🛑] Cancelamento solicitado.")

    def atualizar(self, texto: str, atual: int | None = None, total: int | None = None) -> None:
        self.atualizar_signal.emit(texto, atual or 0, total or 0)

    def _atualizar_seguro(self, texto: str, atual: int, total: int) -> None:
        self.label_status.setText(texto)

        if not self.com_percentual:
            QApplication.processEvents()
            return

        if total == 0:
            self.barra.setRange(0, 0)
        else:
            self.barra.setRange(0, 100)
            progresso = min(100, max(1, int(100 * atual / total))) if total else 0
            self.barra.setValue(progresso)

        QApplication.processEvents()

    def fechar(self) -> None:
        if self._ja_fechado:
            self._log_info("[🔁] Janela já havia sido fechada. Ignorando.")
            return
        self._ja_fechado = True
        self._log_info("[🔚 GerenciadorProgresso] Preparando para fechar a janela...")

        def encerrar() -> None:
            try:
                if self.janela and self.janela.isVisible():
                    self._log_info("[🧼] Ocultando janela de progresso...")
                    self.janela.hide()
                if self.janela:
                    self._log_info("[✅] Fechando janela de progresso...")
                    self.janela.close()
            except Exception as e:
                self._log_exception(f"[❌] Erro ao fechar janela: {e}")

        app = cast(QCoreApplication, QCoreApplication.instance())  # para mypy: não é None aqui
        if QThread.currentThread() == app.thread():
            encerrar()
        else:
            QTimer.singleShot(0, encerrar)

    def _log_info(self, msg: str) -> None:
        if self.logger:
            self.logger.info(msg)
        else:
            print(msg)

    def _log_warning(self, msg: str) -> None:
        if self.logger:
            self.logger.warning(msg)
        else:
            print(msg)

    def _log_exception(self, msg: str) -> None:
        if self.logger:
            self.logger.exception(msg)
        else:
            print(msg)


##############################################
# Integração com a API do Digital Manager Guru
##############################################

ASSINATURAS, GURU_META = mapear_assinaturas(skus_info)

ASSINATURAS_MENSAIS = ASSINATURAS.get("mensal", [])
ASSINATURAS_BIMESTRAIS = ASSINATURAS.get("bimestral", [])
ASSINATURAS_TRIMESTRAIS = ASSINATURAS.get("trimestral", [])
ASSINATURAS_ANUAIS = ASSINATURAS.get("anual", [])
ASSINATURAS_SEMESTRAIS = ASSINATURAS.get("semestral", [])
ASSINATURAS_18MESES = ASSINATURAS.get("18meses", [])
ASSINATURAS_BIANUAIS = ASSINATURAS.get("bianual", [])
ASSINATURAS_TRIANUAIS = ASSINATURAS.get("trianual", [])


def bimestre_do_mes(mes: int) -> int:
    return 1 + (int(mes) - 1) // 2


def dividir_periodos_coleta_api_guru(
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

        if fim_bloco > end:
            fim_bloco = end

        blocos.append((atual.date().isoformat(), fim_bloco.date().isoformat()))

        # avança para o próximo bloco
        proximo_mes = fim_mes + 1
        proximo_ano = ano
        if proximo_mes > 12:
            proximo_mes = 1
            proximo_ano += 1
        atual = datetime(proximo_ano, proximo_mes, 1, tzinfo=UTC)

    return blocos


def calcular_periodo_assinatura(ano: int, mes: int, periodicidade: str) -> tuple[datetime, datetime, int]:
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


def validar_regras_pedido_assinatura(dados: dict, data_pedido: datetime) -> bool:
    """
    Retorna True se a data do pedido estiver dentro do período da assinatura,
    permitindo aplicar regras de ofertas/cupons configuradas.

    - NÃO aplica para modo 'produtos'.
    - Usa ordered_at_ini_periodo/ordered_at_end_periodo se existirem; senão, deriva via calcular_periodo_assinatura.
    - Converte TUDO para datetime *aware* (UTC) antes de comparar.
    - Logs defensivos sem referenciar variáveis ainda não definidas.
    """

    def _aware_utc(dt: datetime | None) -> datetime | None:
        if dt is None:
            return None
        # Se vier naive, marca como UTC; se vier com tz, converte para UTC
        return dt.replace(tzinfo=UTC) if dt.tzinfo is None else dt.astimezone(UTC)

    def _to_dt(val: object) -> datetime | None:
        """Converte val -> datetime (UTC aware).

        Aceita datetime/ISO/timestamp s|ms/QDateTime.
        """
        if val is None:
            return None
        if isinstance(val, datetime):
            return _aware_utc(val)
        if isinstance(val, int | float):
            try:
                v = float(val)
                if v > 1e12:  # ms -> s
                    v /= 1000.0
                return datetime.fromtimestamp(v, tz=UTC)
            except Exception:
                return None
        if isinstance(val, str):
            try:
                dt = parse_date(val)  # mantém a função existente
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

        # 0) normaliza a data da transação ANTES de qualquer print/comparação
        dp = _to_dt(data_pedido)
        if dp is None:
            print(f"[DEBUG dentro_periodo] data_pedido inválido: {data_pedido!r}")
            return False

        # 1) tenta janela explícita
        ini = _to_dt(dados.get("ordered_at_ini_periodo"))
        end = _to_dt(dados.get("ordered_at_end_periodo"))

        # 2) deriva via ano/mês/periodicidade, se necessário
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
                ini_calc, end_calc, _ = calcular_periodo_assinatura(ano_i, mes_i, periodicidade)
            except Exception as e:
                print(f"[DEBUG janela-skip] calcular_periodo_assinatura erro: {e}")
                return False

            ini = _to_dt(ini_calc)
            end = _to_dt(end_calc)

        if ini is None or end is None:
            print(f"[DEBUG dentro_periodo] janela inválida ini={ini!r} end={end!r}")
            return False

        # Log consolidado (agora com TUDO definido)
        print(f"[DEBUG dentro_periodo] dp={dp} ini={ini} end={end}")

        # 3) comparação segura (todos UTC aware)
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


def exibir_resumo_coleta_guru(
    linhas: Sequence[Mapping[str, Any]] | None,
    contagem: Mapping[str, Any] | None,
    estado: Mapping[str, Any] | None,
    modo: str = "assinaturas",
) -> None:
    """
    - modo="produtos": mostra total e lista de produtos adicionados (nome -> qtd).
    - modo≠"produtos": além do bloco de assinaturas, mostra:
        . Itens extras (brindes/embutidos): nome -> qtd
        . Trocas de box: detalhes (se disponíveis) ou totais por período.
    """

    def _is_zero(v: Any) -> bool:
        s = str(v or "").strip()
        if not s:
            return False
        try:
            # lida com "0,00", "0.00", "0", etc.
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
                # garante dict-like
                return v or {}
        return {}

    def _normaliza_swaps(raw: Any) -> list[tuple[str, str, int]]:
        """
        Aceita:
          - dict {("De","Para"): qtd}  OU  {"De → Para": qtd}
          - dict {"De": {"Para": qtd, ...}, ...}
          - Counter com chaves como acima
        Retorna lista [(de, para, qtd), ...]
        """
        out: list[tuple[str, str, int]] = []
        if not raw:
            return out

        if isinstance(raw, Counter):
            raw = dict(raw)

        if isinstance(raw, dict):
            # formato aninhado: {"De": {"Para": qtd}}
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

            # formato plano: chaves tuple ou string "De → Para"/"De->Para"
            for k, qtd in raw.items():
                try:
                    q = int(qtd or 0)
                except Exception:
                    q = 0
                if q <= 0:
                    continue
                if isinstance(k, tuple | list) and len(k) == 2:
                    de, para = k
                else:
                    # tenta separar por seta
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

    try:
        modo = (modo or "").strip().lower()
        linhas_seq: Sequence[Mapping[str, Any]] = linhas or []
        total_linhas = len(linhas_seq)

        # ---- Contagem geral de produtos por nome (todas as linhas)
        produtos_ctr: Counter[str] = Counter()
        for lin in linhas_seq:
            if isinstance(lin, dict):
                nome = lin.get("Produto") or lin.get("produto") or lin.get("nome_produto") or ""
                nome = str(nome).strip()
                if nome:
                    produtos_ctr[nome] += 1

        # ---------- MODO PRODUTOS ----------
        if modo == "produtos":
            msg: list[str] = [f"📦 Linhas adicionadas: {total_linhas}"]
            if produtos_ctr:
                msg.append("\n🧾 Produtos adicionados:")
                for nome, qtd in produtos_ctr.most_common():
                    msg.append(f"  - {nome}: {qtd}")
            else:
                msg.append("\n🧾 Produtos adicionados: 0")

            comunicador_global.mostrar_mensagem.emit("info", "Resumo da Exportação (Produtos)", "\n".join(msg))
            return

        # ---------- MODO ASSINATURAS ----------
        resumo = f"📦 Linhas adicionadas: {total_linhas}\n\n📘 Assinaturas:\n"

        TIPOS: list[tuple[str, list[str]]] = [
            ("mensais", ["mensais", "mensal"]),
            ("bimestrais", ["bimestrais", "bimestral"]),
            ("trimestrais", ["trimestrais", "trimestral"]),
            ("semestrais", ["semestrais", "semestral"]),
            ("anuais", ["anuais", "anual"]),
            ("18meses", ["18meses", "18meses"]),
            ("bianuais", ["bianuais", "bianual"]),
            ("trianuais", ["trianuais", "trianual"]),
        ]

        # 📘 Assinaturas + cupons por período
        for label, chaves in TIPOS:
            dados = _pega_bloco(contagem, chaves)
            assin = int(dados.get("assinaturas", 0) or 0)
            cupons = int(dados.get("cupons", 0) or 0)
            resumo += f"  - {label.capitalize()}: {assin} (cupons: {cupons})\n"

        # 🎁 Itens extras (brindes/embutidos) - computa a partir das linhas com valor 0
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

        # 🔁 Trocas de box
        swaps_raw = (estado or {}).get("alteracoes_box_detalhes") or (contagem or {}).get("alteracoes_box_detalhes")
        swaps_list = _normaliza_swaps(swaps_raw)

        if swaps_list:
            resumo += "\n🔁 Trocas de box (detalhes):\n"
            for de, para, qtd in sorted(swaps_list, key=lambda x: (-x[2], x[0], x[1])):
                resumo += f"  - {de} → {para}: {qtd}\n"
        else:
            # totais por período, se houver
            tem_trocas = any(int(_pega_bloco(contagem, ch).get("alteracoes_box", 0) or 0) > 0 for _, ch in TIPOS)
            if tem_trocas:
                resumo += "\n🔁 Trocas de box (totais):\n"
                for label, chaves in TIPOS:
                    dados = _pega_bloco(contagem, chaves)
                    trocas = int(dados.get("alteracoes_box", 0) or 0)
                    resumo += f"  - {label.capitalize()}: {trocas}\n"

        # 🧾 Lista geral de produtos adicionados (principal + desmembrados + extras)
        if produtos_ctr:
            resumo += "\n🧾 Produtos adicionados (todas as linhas):\n"
            for nome, qtd in produtos_ctr.most_common():
                resumo += f"  - {nome}: {qtd}\n"

        comunicador_global.mostrar_mensagem.emit("info", "Resumo da Exportação", resumo)

    except Exception as e:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro ao exibir resumo", str(e))


# --------------------------------- UI / CONTROLADOR COLETA GURU -----------------------------------------


class CanceladorLike(Protocol):
    def set(self) -> Any: ...


class _CancelamentoFilter(QObject):
    def __init__(self, cancelador: Any, parent: QObject | None) -> None:
        super().__init__(parent)
        self._cancelador = cancelador

    def eventFilter(self, _obj: QObject | None, event: QEvent | None) -> bool:
        if event is None:
            return False

        # QEvent.Type.Close é o enum correto nas stubs
        if event.type() == QEvent.Type.Close:
            setter = getattr(self._cancelador, "set", None)
            if callable(setter):
                try:
                    setter()
                except Exception:
                    pass
            # não bloqueia o fechamento
            return False

        return False


def configurar_cancelamento_em_janela(janela: QObject, cancelador: CanceladorLike) -> None:
    filtro = _CancelamentoFilter(cancelador, janela)  # parent=janela
    janela.installEventFilter(filtro)


class WorkerControllerGuru(QObject):
    iniciar_worker_signal = pyqtSignal()

    def __init__(
        self,
        dados: Mapping[str, Any],
        estado: MutableMapping[str, Any],
        skus_info: Any,
    ) -> None:
        super().__init__()
        self.dados: Mapping[str, Any] = dados
        self.estado: MutableMapping[str, Any] = estado
        self.skus_info: Any = skus_info
        self.iniciar_worker_signal.connect(self.iniciar_worker)

        # ✅ garante atributo para o mypy e para o runtime
        self._timer: QTimer | None = None

    def iniciar_worker(self) -> None:
        try:
            gerenciador = GerenciadorProgresso(
                titulo="🚚 Progresso da Exportação",
                com_percentual=True,
                estado_global=self.estado,
                logger_obj=logger,
            )
            QApplication.processEvents()
            print("[✅ iniciar_worker] Gerenciador de progresso iniciado.")

            configurar_cancelamento_em_janela(gerenciador.janela, self.estado["cancelador_global"])
            print("[✅ iniciar_worker] Cancelamento configurado.")

            self.estado["worker_thread"] = WorkerThreadGuru(self.dados, self.estado, self.skus_info, gerenciador)
            worker: WorkerThreadGuru = cast(WorkerThreadGuru, self.estado["worker_thread"])

            worker.avisar_usuario.connect(
                lambda titulo, msg: comunicador_global.mostrar_mensagem.emit("aviso", titulo, msg)
            )

            def on_erro(msg: str) -> None:
                comunicador_global.mostrar_mensagem.emit(
                    "erro", "Erro", f"Ocorreu um erro durante a exportação:\n{msg}"
                )
                with suppress(Exception):
                    gerenciador.fechar()

            worker.erro.connect(on_erro)

            # (opcional) se você quer um "failsafe" para fechar a UI após X ms:
            if self._timer is None:
                self._timer = QTimer(self)
                self._timer.setSingleShot(True)
                self._timer.timeout.connect(lambda: with_suppress_close(gerenciador))
                # defina um intervalo se fizer sentido (ex.: 30s)
                # self._timer.start(30_000)

            def ao_finalizar_worker(linhas: list[Any], contagem: dict[str, Any]) -> None:
                try:
                    exibir_resumo_coleta_guru(
                        linhas,
                        contagem,
                        self.estado,
                        modo=(cast(str, self.dados.get("modo") or "")).lower(),
                    )
                finally:
                    # ✅ acesso seguro ao _timer
                    if self._timer is not None:
                        with suppress(Exception):
                            self._timer.stop()
                            self._timer.deleteLater()
                        self._timer = None
                    with suppress(Exception):
                        gerenciador.fechar()

            worker.finalizado.connect(ao_finalizar_worker)
            # worker.finished.connect(gerenciador.fechar)  # opcional

            worker.start()
            print("[🧵 iniciar_worker] Thread iniciada.")
        except Exception as e:
            print("[❌ ERRO EM iniciar_worker]:", e)
            print(traceback.format_exc())
            comunicador_global.mostrar_mensagem.emit("erro", "Erro", f"Falha ao iniciar a exportação:\n{e!s}")


class WorkerThreadGuru(QThread):
    # sinais esperados pelo Controller
    finalizado = pyqtSignal(list, dict)
    erro = pyqtSignal(str)
    avisar_usuario = pyqtSignal(str, str)

    # sinais para progresso/fechamento seguro entre threads
    progresso = pyqtSignal(str, int, int)
    fechar_ui = pyqtSignal()

    def __init__(
        self,
        dados: Mapping[str, Any],  # aceita qualquer mapeamento (sem cópia)
        estado: MutableMapping[str, Any],  # mutável (dict-like)
        skus_info: Any,
        gerenciador: GerenciadorProgresso,
    ) -> None:
        super().__init__()
        self.dados: Mapping[str, Any] = dados
        self.estado: MutableMapping[str, Any] = estado
        self.skus_info: Any = skus_info
        self.gerenciador: GerenciadorProgresso = gerenciador

        # Mantém Qt.QueuedConnection, mas silencia o stub do PyQt para mypy
        self.progresso.connect(self.gerenciador.atualizar)
        self.fechar_ui.connect(self.gerenciador.fechar)

        self._parent_correlation_id = get_correlation_id()

    def run(self) -> None:
        set_correlation_id(self._parent_correlation_id)

        novas_linhas: list[Any] = []
        contagem: dict[str, Any] = {}

        try:
            logger.info("worker_started", extra={"modo": self.dados.get("modo")})

            # tipagem apenas: Optional[Event] + union-attr ignore
            cancelador: Event | None = cast(Event | None, self.estado.get("cancelador_global"))
            if hasattr(cancelador, "is_set") and cancelador.is_set():  # type: ignore[union-attr]
                logger.warning("worker_cancelled_early")
                return

            modo = (cast(str, self.dados.get("modo") or "assinaturas")).strip().lower()

            # buscamos em ramos separados, mas NÃO atribuimos a dados_final ainda
            if modo == "assinaturas":
                self.progresso.emit("🔄 Buscando transações de assinaturas...", 0, 0)
                transacoes, _, dados_final_map = gerenciar_coleta_vendas_assinaturas(
                    cast(dict[str, Any], self.dados),  # tipagem
                    atualizar=self.progresso.emit,
                    cancelador=cast(Event, self.estado["cancelador_global"]),  # tipagem
                    estado=cast(dict[str, Any], self.estado),  # tipagem
                )

            elif modo == "produtos":
                self.progresso.emit("🔄 Buscando transações de produtos...", 0, 0)
                transacoes, _, dados_final_map = coletar_vendas_produtos(
                    cast(dict[str, Any], self.dados),
                    atualizar=self.progresso.emit,
                    cancelador=cast(Event, self.estado["cancelador_global"]),
                    estado=cast(dict[str, Any], self.estado),
                )

            else:
                raise ValueError(f"Modo de busca desconhecido: {modo}")

            # Unificação de tipo: Mapping -> dict UMA única vez
            if not isinstance(dados_final_map, Mapping):
                raise ValueError("Dados inválidos retornados da busca.")
            dados_final: dict[str, Any] = dict(dados_final_map)

            if cast(Event, self.estado["cancelador_global"]).is_set():
                logger.warning("worker_cancelled_after_fetch")
                return

            self.progresso.emit("📦 Processando transações", 0, 100)

            if not isinstance(transacoes, list) or not isinstance(dados_final, dict):
                raise ValueError("Dados inválidos retornados da busca.")

            logger.info(
                "worker_received_transactions",
                extra={"qtd": len(transacoes), "modo": modo},
            )

            # montar_planilha_vendas_guru pode devolver Mapping; usamos var intermediária
            novas_linhas, contagem_map = montar_planilha_vendas_guru(
                transacoes=transacoes,
                dados=dados_final,
                atualizar_etapa=self.progresso.emit,
                skus_info=self.skus_info,
                cancelador=cast(Event, self.estado["cancelador_global"]),
                estado=cast(dict[str, Any], self.estado),
            )

            if not isinstance(contagem_map, Mapping):
                raise ValueError("Retorno inválido de montar_planilha_vendas_guru (esperado Mapping).")
            contagem = dict(contagem_map)  # Mapping -> dict (sem reanotar)

            if cast(Event, self.estado["cancelador_global"]).is_set():
                logger.warning("worker_cancelled_after_process")
                return

            self.progresso.emit("✅ Finalizando...", 100, 100)

            if not isinstance(novas_linhas, list) or not isinstance(contagem, dict):
                raise ValueError("Retorno inválido de montar_planilha_vendas_guru.")

            if "linhas_planilha" not in self.estado or not isinstance(self.estado["linhas_planilha"], list):
                self.estado["linhas_planilha"] = []
            self.estado["linhas_planilha"].extend(novas_linhas)
            self.estado["transacoes_obtidas"] = True

            logger.info("worker_success", extra={"linhas_adicionadas": len(novas_linhas)})

        except Exception as e:
            logger.exception("worker_error", extra={"err": str(e)})
            self.erro.emit(str(e))

        finally:
            logger.info("worker_finished")
            self.progresso.emit("✅ Finalizado com sucesso", 1, 1)
            self.fechar_ui.emit()

            erros = self.estado.get("transacoes_com_erro", [])
            if isinstance(erros, list) and erros:
                mensagem = (
                    f"{len(erros)} transações apresentaram erro durante o processo.\n"
                    "Elas foram ignoradas e não estão na planilha.\n\n"
                    "IDs com erro:\n" + "\n".join(erros[:10])
                )
                if len(erros) > 10:
                    mensagem += f"\n...e mais {len(erros) - 10} transações."
                self.avisar_usuario.emit("Aviso: Erros na busca", mensagem)

            self.finalizado.emit(novas_linhas, contagem)


class HasIsSet(Protocol):
    def is_set(self) -> bool: ...


class TransientGuruError(Exception):
    """Erro transitório ao buscar a PRIMEIRA página; deve acionar retry externo."""


def coletar_vendas(
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
        print("[🚫] Cancelado no início de coletar_vendas")
        return []

    print(f"[🔎 coletar_vendas] Início - Produto: {product_id}, Período: {inicio} → {fim}")

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
        print(f"[📄 Página {pagina_count+1}] {len(pagina)} vendas encontradas")

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
        f"[✅ coletar_vendas] {status} - Produto {product_id} | Total: {total_transacoes} transações em {pagina_count} página(s)"
    )
    return resultado


def coletar_vendas_com_retry(
    *args: Any,
    cancelador: Any = None,
    tentativas: int = 3,
    **kwargs: Any,
) -> list[dict[str, Any]]:
    for tentativa in range(tentativas):
        if cancelador and cancelador.is_set():
            print("[🚫] Cancelado dentro de coletar_vendas_com_retry.")
            return []
        try:
            resultado = coletar_vendas(*args, cancelador=cancelador, **kwargs)
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


def iniciar_coleta_vendas_produtos(
    box_nome_input: QComboBox,
    transportadoras_var: Mapping[str, QCheckBox],
    skus_info: Mapping[str, Mapping[str, Any]],
    estado: MutableMapping[str, Any],
) -> None:
    dialog = QDialog()
    dialog.setWindowTitle("🔍 Buscar Produtos Aprovados")
    layout = QVBoxLayout(dialog)

    def obter_periodo_bimestre_atual() -> tuple[QDate, QDate]:
        hoje = QDate.currentDate()
        mes = hoje.month()
        ano = hoje.year()

        bimestre = (mes - 1) // 2
        primeiro_mes = 1 + bimestre * 2  # 1, 3, 5, 7, 9, 11

        data_ini = QDate(ano, primeiro_mes, 1)

        if primeiro_mes + 2 > 12:
            data_fim = QDate(ano + 1, 1, 1).addDays(-1)  # até 31/12
        else:
            data_fim = QDate(ano, primeiro_mes + 2, 1).addDays(-1)  # último dia do 2º mês

        return data_ini, data_fim

    # 🗓 Intervalo de datas
    linha_datas = QHBoxLayout()
    data_ini_input = QDateEdit()
    data_fim_input = QDateEdit()
    data_ini_input.setCalendarPopup(True)
    data_fim_input.setCalendarPopup(True)

    data_ini_bim, data_fim_bim = obter_periodo_bimestre_atual()
    data_ini_input.setDate(data_ini_bim)
    data_fim_input.setDate(data_fim_bim)

    linha_datas.addWidget(QLabel("Data inicial:"))
    linha_datas.addWidget(data_ini_input)
    linha_datas.addWidget(QLabel("Data final:"))
    linha_datas.addWidget(data_fim_input)
    layout.addLayout(linha_datas)

    # 📦 Produto específico ou todos
    linha_produto = QHBoxLayout()
    produto_input = QComboBox()
    produto_input.addItem("Todos os produtos")

    produtos_simples = [nome for nome, info in skus_info.items() if info.get("tipo") != "assinatura"]
    produto_input.addItems(sorted(produtos_simples))

    linha_produto.addWidget(QLabel("Produto a buscar:"))
    linha_produto.addWidget(produto_input)
    layout.addLayout(linha_produto)

    # 🔘 Botões
    botoes = QHBoxLayout()
    btn_ok = QPushButton("Buscar")
    btn_cancelar = QPushButton("Cancelar")
    botoes.addWidget(btn_ok)
    botoes.addWidget(btn_cancelar)
    layout.addLayout(botoes)

    def executar() -> None:
        # QDate -> date
        data_ini_py = data_ini_input.date().toPyDate()
        data_fim_py = data_fim_input.date().toPyDate()
        nome_produto = (produto_input.currentText() or "").strip()

        if data_ini_py > data_fim_py:
            QMessageBox.warning(dialog, "Erro", "A data inicial não pode ser posterior à data final.")
            return

        dialog.accept()

        # Converte para string ISO "YYYY-MM-DD" para casar com a tipagem de preparar_coleta_vendas_produtos
        data_ini_s = data_ini_py.isoformat()
        data_fim_s = data_fim_py.isoformat()

        preparar_coleta_vendas_produtos(
            data_ini=data_ini_s,
            data_fim=data_fim_s,
            nome_produto=None if nome_produto == "Todos os produtos" else nome_produto,
            box_nome_input=box_nome_input,
            transportadoras_var=transportadoras_var,
            estado=estado,
            skus_info=skus_info,
        )

    btn_ok.clicked.connect(executar)
    btn_cancelar.clicked.connect(dialog.reject)

    dialog.exec_()


def preparar_coleta_vendas_produtos(
    data_ini: str,
    data_fim: str,
    nome_produto: str | None,
    box_nome_input: QComboBox,
    transportadoras_var: Mapping[str, QCheckBox],
    estado: MutableMapping[str, Any],
    skus_info: Mapping[str, Mapping[str, Any]],
) -> None:
    print(f"[🔎] Iniciando busca de produtos de {data_ini} a {data_fim}")
    produtos_alvo: dict[str, Mapping[str, Any]] = {}

    # 🎯 Seleciona produtos válidos
    if nome_produto:
        info = skus_info.get(nome_produto, {})
        if info.get("tipo") == "assinatura":
            QMessageBox.warning(None, "Erro", f"'{nome_produto}' é uma assinatura. Selecione apenas produtos.")
            return
        produtos_alvo[nome_produto] = info
    else:
        produtos_alvo = {nome: info for nome, info in skus_info.items() if info.get("tipo") != "assinatura"}

    produtos_ids: list[str] = []
    for info in produtos_alvo.values():
        gids: Sequence[Any] = cast(Sequence[Any], info.get("guru_ids", []))
        for gid in gids:
            s = str(gid).strip()
            if s:
                produtos_ids.append(s)

    if not produtos_ids:
        QMessageBox.warning(None, "Aviso", "Nenhum produto com IDs válidos encontrados.")
        return

    dados: dict[str, Any] = {
        "modo": "produtos",  # ← ajuste mantido
        "inicio": data_ini,
        "fim": data_fim,
        "produtos_ids": produtos_ids,
        "box_nome": (box_nome_input.currentText() or "").strip(),
        "transportadoras_permitidas": [nome for nome, cb in transportadoras_var.items() if cb.isChecked()],
    }

    wt = estado.get("worker_thread")
    if wt is not None and hasattr(wt, "isRunning") and wt.isRunning():
        print("[⚠️] Uma execução já está em andamento.")
        return

    estado.setdefault("etapas_finalizadas", {})
    estado.setdefault("df_planilha_parcial", pd.DataFrame())
    estado.setdefault("brindes_indisp_set", set())
    estado.setdefault("embutidos_indisp_set", set())
    estado.setdefault("linhas_planilha", [])
    estado.setdefault("mapa_transaction_id_por_linha", {})

    if not isinstance(estado.get("cancelador_global"), threading.Event):
        estado["cancelador_global"] = threading.Event()

    estado["cancelador_global"].clear()
    estado["dados_busca"] = dict(dados)  # cópia simples

    print("[🚀 preparar_coleta_vendas_produtos] Enviando para WorkerControllerGuru...")

    try:
        controller = WorkerControllerGuru(dados, estado, skus_info)  # tipos permanecem aceitos
        estado["worker_controller"] = controller
        controller.iniciar_worker_signal.emit()
    except Exception as e:
        print("[❌ ERRO EM iniciar_worker via sinal]:", e)
        print(traceback.format_exc())
        comunicador_global.mostrar_mensagem.emit("erro", "Erro", f"Ocorreu um erro ao iniciar a exportação:\n{e!s}")


def coletar_vendas_produtos(
    dados: Mapping[str, Any],
    *,
    atualizar: Callable[[str, int, int], Any] | None = None,
    cancelador: HasIsSet | None = None,
    estado: MutableMapping[str, Any] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, Any], dict[str, Any]]:  # ← dict no 3º item
    print("[🔍 coletar_vendas_produtos] Início da função")

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

    intervalos = cast(list[tuple[str, str]], dividir_periodos_coleta_api_guru(inicio, fim))
    tarefas: list[tuple[str, str, str]] = [
        (product_id, ini, fim) for product_id in produtos_ids for (ini, fim) in intervalos
    ]

    print(f"[📦] Total de tarefas para produtos: {len(tarefas)}")

    if cancelador and cancelador.is_set():
        if atualizar:
            atualizar("⛔ Busca cancelada pelo usuário", 1, 1)
        return [], {}, dict(dados)  # ← CONVERTE

    with ThreadPoolExecutor(max_workers=12) as executor:
        futures = [executor.submit(coletar_vendas_com_retry, *args, cancelador=cancelador) for args in tarefas]
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

    print(f"[✅ coletar_vendas_produtos] Finalizado - {len(transacoes)} transações coletadas")
    return transacoes, {}, dict(dados)


def ler_regras_assinaturas(estado: MutableMapping[str, Any]) -> list[dict[str, Any]]:
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
                    # cache no estado p/ próximas chamadas
                    estado["rules"] = regras
                    return regras
    except Exception:
        pass

    return []  # sem regras


def produto_indisponivel(produto_nome: str, *, sku: str | None = None) -> bool:
    if not produto_nome and not sku:
        return False

    # estado["skus_info"] pode vir sem tipo -> cast para Mapping esperado
    skus: Mapping[str, Mapping[str, Any]] = cast(Mapping[str, Mapping[str, Any]], estado.get("skus_info") or {})
    info: Mapping[str, Any] | None = skus.get(produto_nome)

    # fallback por normalização do nome
    if info is None and produto_nome:
        alvo = unidecode(str(produto_nome)).lower().strip()
        for nome, i in skus.items():
            if unidecode(nome).lower().strip() == alvo:
                info = i
                break

    # NOVO: se não achou por nome, tenta por SKU
    if info is None and sku:
        sku_norm = (sku or "").strip().upper()
        for i in skus.values():
            if str(i.get("sku", "")).strip().upper() == sku_norm:
                info = i
                break

    return bool(info and info.get("indisponivel", False))


def iniciar_busca_assinaturas(
    ano: int | str,
    mes: int | str,
    modo_periodo: str,
    box_nome_input: QComboBox,
    _transportadoras_var: Any,
    estado: MutableMapping[str, Any],
    skus_info: Mapping[str, Mapping[str, Any]],
    *,
    periodicidade_selecionada: str,
) -> None:
    # normaliza periodicidade
    periodicidade: str = (periodicidade_selecionada or "").strip().lower()
    if periodicidade not in ("mensal", "bimestral"):
        periodicidade = "bimestral"

    # calcula janelas do período
    dt_ini, dt_end, periodo = calcular_periodo_assinatura(int(ano), int(mes), periodicidade)
    box_nome: str = (box_nome_input.currentText() or "").strip()

    # bloqueia box indisponivel
    if box_nome and produto_indisponivel(box_nome):
        comunicador_global.mostrar_mensagem.emit(
            "erro",
            "Box indisponivel",
            f"O box selecionado (“{box_nome}”) está marcado como indisponivel no SKUs.",
        )
        return

    # carrega regras ativas
    regras: list[dict[str, Any]] = ler_regras_assinaturas(estado)

    # monta o payload de execução (o WorkerThreadGuru usa isso direto)
    dados: dict[str, Any] = {
        "modo": "assinaturas",
        "ano": int(ano),
        "mes": int(mes),
        "periodicidade": periodicidade,
        "periodo": int(periodo),  # mês (mensal) ou bimestre (bimestral)
        "ordered_at_ini_periodo": dt_ini,
        "ordered_at_end_periodo": dt_end,
        "box_nome": box_nome,
        "rules": regras,  # regras já resolvidas em memória
        "embutido_ini_ts": dt_ini.timestamp(),
        "embutido_end_ts": dt_end.timestamp(),
        "modo_periodo": (modo_periodo or "").strip().upper(),  # "PERÍODO" | "TODAS"
    }

    _subs_raw = fetch_all_subscriptions()
    subs_idx = build_subscriptions_index(_subs_raw, skus_info)
    estado["subscriptions_idx"] = subs_idx

    # guarda contexto p/ outras partes da UI
    estado["contexto_busca_assinaturas"] = dados
    estado["skus_info"] = cast(Mapping[str, Mapping[str, Any]], skus_info)

    # ---- dispara em QThread via WorkerControllerGuru ----
    # garante Event de cancelamento
    if not isinstance(estado.get("cancelador_global"), threading.Event):
        estado["cancelador_global"] = threading.Event()
    estado["cancelador_global"].clear()

    # evita execuções concorrentes
    wt = estado.get("worker_thread")
    if wt is not None and wt.isRunning():
        comunicador_global.mostrar_mensagem.emit("aviso", "Em andamento", "Já existe uma exportação em andamento.")
        return

    # mantém referência do controller para não ser coletado
    controller = WorkerControllerGuru(dados, estado, skus_info)
    estado["worker_controller"] = controller

    # pode chamar o slot direto (ou emitir o sinal, como preferir)
    controller.iniciar_worker()
    # alternativa: controller.iniciar_worker_signal.emit()


def mapear_periodicidade_assinaturas(
    skus_info: Mapping[str, Mapping[str, Any]],
    periodicidade_sel: str,
) -> dict[str, list[str]]:
    """
    Retorna dict com listas de product_ids (Guru) das ASSINATURAS filtradas pela periodicidade ('mensal'|'bimestral').

    Chaves de saída (por DURAÇÃO):
      'mensais' (1m), 'bimestrais' (2m), 'semestrais' (6m), 'anuais' (12m), '18meses' (18m), 'bianuais' (24m), 'trianuais' (36m),
      e 'todos' (conjunto de todos os IDs).

    Observação:
      - 'periodicidade' (mensal | bimestral) é critério de filtro.
      - 'recorrencia'/'duracao'/'duracao_meses' determinam a DURAÇÃO (bucket de saída).
    """
    # normaliza periodicidade de filtro
    periodicidade_sel = (periodicidade_sel or "").strip().lower()
    if periodicidade_sel not in {"mensal", "bimestral"}:
        # mantém comportamento antigo: se vier algo fora, não filtra (ou defina um default se preferir)
        periodicidade_sel = periodicidade_sel or ""

    # buckets de saída inicializados
    ids_por_tipo: dict[str, list[str]] = {
        "mensais": [],
        "bimestrais": [],
        "trimestrais": [],
        "semestrais": [],
        "anuais": [],
        "18meses": [],
        "bianuais": [],
        "trianuais": [],
    }
    todos: set[str] = set()

    def _inferir_periodicidade(info: Mapping[str, Any]) -> str:
        # 1) explícito no SKU
        per = str(info.get("periodicidade") or info.get("periodicidade_envio") or "").strip().lower()
        # duração não é periodicidade; se veio "semestral", "18meses", etc., ignore
        if per not in {"mensal", "bimestral"}:
            per = ""

        # 2) fallback por marketplace_id (ex.: ...-MES / ...-BIM)
        if not per:
            mp = str(info.get("marketplace_id") or info.get("marketplace") or "").strip().upper()
            if mp.endswith("-MES"):
                per = "mensal"
            elif mp.endswith("-BIM"):
                per = "bimestral"

        # 3) se ainda vazio, você pode definir default (opcional). Aqui não forçamos.
        return per

    def _bucket_duracao(info: Mapping[str, Any]) -> str | None:
        # pode vir como número:
        dur_num = info.get("duracao_meses") or info.get("duration_months")
        if isinstance(dur_num, int | float) and dur_num > 0:
            m = int(dur_num)
            return {
                1: "mensais",
                2: "bimestrais",
                3: "trimestrais",
                6: "semestrais",
                12: "anuais",
                18: "18meses",
                24: "bianuais",
                36: "trianuais",
            }.get(m, None)

        # ...ou como rótulo/texto:
        dur_label = (
            str(
                info.get("recorrencia")
                or info.get("duracao")
                or info.get("duração")
                or info.get("duration_label")
                or ""
            )
            .strip()
            .lower()
        )

        mapa_tipo = {
            "mensal": "mensais",
            "bimestral": "bimestrais",
            "trimestrais": "trimestrais",
            "semestral": "semestrais",
            "anual": "anuais",
            "18meses": "18meses",
            "bianual": "bianuais",
            "trianual": "trianuais",
        }
        return mapa_tipo.get(dur_label)

    for _nome, info in skus_info.items():
        try:
            if str(info.get("tipo", "")).strip().lower() != "assinatura":
                continue

            # filtro por periodicidade (se fornecido)
            per = _inferir_periodicidade(info)
            if periodicidade_sel and per != periodicidade_sel:
                continue

            bucket = _bucket_duracao(info)
            if not bucket:
                # sem bucket de duração -> ignora (ou escolha um default, se fizer sentido)
                continue

            guru_ids = info.get("guru_ids") or []
            for gid in guru_ids:
                gid_str = str(gid).strip()
                if not gid_str:
                    continue
                # evita KeyError e já agrupa
                ids_por_tipo.setdefault(bucket, []).append(gid_str)
                todos.add(gid_str)
        except Exception:
            # não deixa 1 SKU ruim derrubar o mapeamento inteiro
            continue

    # dedup e "todos"
    for k, v in list(ids_por_tipo.items()):
        # mantém a ordem de primeira ocorrência
        ids_por_tipo[k] = list(dict.fromkeys(v))
    ids_por_tipo["todos"] = list(todos)

    return ids_por_tipo


def gerenciar_coleta_vendas_assinaturas(
    dados: dict[str, Any],
    *,
    atualizar: Callable[[str, int, int], Any] | None = None,
    cancelador: HasIsSet | None = None,
    estado: dict[str, Any] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, Any], dict[str, Any]]:
    print("[🔍 gerenciar_coleta_vendas_assinaturas] Início da função")

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
    ids_map: dict[str, list[str]] = mapear_periodicidade_assinaturas(skus_info, periodicidade_sel)
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
    # Observação: dividir_periodos_coleta_api_guru aceita date/datetime e retorna ("YYYY-MM-DD","YYYY-MM-DD")
    intervalos_mensais: list[tuple[str, str]] = (
        dividir_periodos_coleta_api_guru(ini_sel, end_sel) if periodicidade_sel == "mensal" else []
    )
    intervalos_bimestrais: list[tuple[str, str]] = (
        dividir_periodos_coleta_api_guru(ini_sel, end_sel) if periodicidade_sel == "bimestral" else []
    )

    # Multi-ano: início = (primeiro dia do mês seguinte ao fim selecionado) - N anos, limitado por LIMITE_INFERIOR
    inicio_base = _first_day_next_month(end_sel)

    def _janela_multi_ano(n_anos: int) -> list[tuple[str, str]]:
        ini = datetime(inicio_base.year - n_anos, inicio_base.month, 1, tzinfo=UTC)
        ini = max(ini, LIMITE_INFERIOR)
        return cast(list[tuple[str, str]], dividir_periodos_coleta_api_guru(ini, end_sel))

    def _janela_multi_meses(n_meses: int) -> list[tuple[str, str]]:
        ini = (inicio_base - relativedelta(months=n_meses)).replace(day=1)
        ini = max(ini, LIMITE_INFERIOR)
        return cast(list[tuple[str, str]], dividir_periodos_coleta_api_guru(ini, end_sel))

    # ================= Modo do período (PERÍODO vs TODAS) =================
    try:
        modo_sel_norm = unidecode((dados.get("modo_periodo") or "").strip().upper())
    except Exception:
        # fallback sem unidecode
        modo_sel_norm = (dados.get("modo_periodo") or "").strip().upper().replace("Í", "I").replace("É", "E")

    if modo_sel_norm == "PERIODO":
        # FIX (1): só o mês/bimestre selecionado
        base_intervalos = dividir_periodos_coleta_api_guru(ini_sel, end_sel)
        intervalos_anuais = base_intervalos
        intervalos_bianuais = base_intervalos
        intervalos_trianuais = base_intervalos
        intervalos_semestrais = base_intervalos

    else:
        # TODAS: janelas de 1, 2 e 3 anos retroativas
        intervalos_anuais = _janela_multi_ano(1)
        intervalos_bianuais = _janela_multi_ano(2)
        intervalos_trianuais = _janela_multi_ano(3)
        intervalos_semestrais = _janela_multi_meses(6)

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
                    coletar_vendas_com_retry,
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

    print("[1.2️⃣] Gerando tarefas para trianuais...")
    t = [(pid, ini, fim, "trianuais") for pid in ids_map.get("trianuais", []) for (ini, fim) in intervalos_trianuais]
    todas_tarefas.extend(t)

    print("[1.1️⃣] Gerando tarefas para bianuais...")
    t = [(pid, ini, fim, "bianuais") for pid in ids_map.get("bianuais", []) for (ini, fim) in intervalos_bianuais]
    todas_tarefas.extend(t)

    print("[1️⃣] Gerando tarefas para anuais...")
    t = [(pid, ini, fim, "anuais") for pid in ids_map.get("anuais", []) for (ini, fim) in intervalos_anuais]
    todas_tarefas.extend(t)

    print("[1.05️⃣] Gerando tarefas para semestrais...")
    t = [(pid, ini, fim, "semestrais") for pid in ids_map.get("semestrais", []) for (ini, fim) in intervalos_semestrais]
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
        print(f"[✅ gerenciar_coleta_vendas_assinaturas] Finalizado - {len(transacoes)} transações")
        return transacoes, {}, dados

    ok = executar_lote(todas_tarefas, "Coletando transações...")
    if not ok:
        print("[⛔] Execução interrompida por cancelamento.")
        return transacoes, {}, dados

    print(f"[✅ gerenciar_coleta_vendas_assinaturas] Finalizado - {len(transacoes)} transações")
    return transacoes, {}, dados


# Processar planilha DMG


class SKUInfo(TypedDict, total=False):
    sku: str
    peso: float | int
    periodicidade: str
    guru_ids: Sequence[str]


# dicionário vindo do skus.json
SKUs = Mapping[str, SKUInfo]


class AplicarRegrasAssinaturas(TypedDict, total=False):
    override_box: str | None
    brindes_extra: list[dict[str, Any]]


def formatar_valor(valor: float) -> str:
    return f"{valor:.2f}".replace(".", ",")


def _norm(s: str) -> str:
    return unidecode((s or "").strip().lower())


def padronizar_planilha_bling(df: pd.DataFrame, preservar_extras: bool = True) -> pd.DataFrame:
    colunas_padrao = [
        "Número pedido",
        "Nome Comprador",
        "Data",
        "CPF/CNPJ Comprador",
        "Endereço Comprador",
        "Bairro Comprador",
        "Número Comprador",
        "Complemento Comprador",
        "CEP Comprador",
        "Cidade Comprador",
        "UF Comprador",
        "Telefone Comprador",
        "Celular Comprador",
        "E-mail Comprador",
        "Produto",
        "SKU",
        "Un",
        "Quantidade",
        "Valor Unitário",
        "Valor Total",
        "Total Pedido",
        "Valor Frete Pedido",
        "Valor Desconto Pedido",
        "Outras despesas",
        "Nome Entrega",
        "Endereço Entrega",
        "Número Entrega",
        "Complemento Entrega",
        "Cidade Entrega",
        "UF Entrega",
        "CEP Entrega",
        "Bairro Entrega",
        "Transportadora",
        "Serviço",
        "Tipo Frete",
        "Observações",
        "Qtd Parcela",
        "Data Prevista",
        "Vendedor",
        "Forma Pagamento",
        "ID Forma Pagamento",
        "transaction_id",
        "subscription_id",
        "product_id",
        "Plano Assinatura",
        "Cupom",
        "periodicidade",
        "periodo",
        "indisponivel",
        "ID Lote",
        "Data Pedido",
        "is_upgrade",
    ]

    df_out = df.copy()

    # garante todas as colunas padrão
    for coluna in colunas_padrao:
        if coluna not in df_out.columns:
            df_out[coluna] = ""

    # reordena pelas padrão
    base = df_out[colunas_padrao]

    if not preservar_extras:
        return base

    # preserva quaisquer colunas extras ao final (na ordem atual)
    extras = [c for c in df_out.columns if c not in colunas_padrao]
    if extras:
        return pd.concat([base, df_out[extras]], axis=1)

    return base


def gerar_linha_base_planilha(
    contact: Mapping[str, Any],
    valores: Mapping[str, Any],
    transacao: Mapping[str, Any],
    tipo_plano: str = "",
    subscription_id: str = "",
    cupom_valido: str = "",
    *,
    is_upgrade: bool = False,  # ← NOVO
) -> dict[str, Any]:
    telefone = contact.get("phone_number", "")
    return {
        # Comprador
        "Nome Comprador": contact.get("name", ""),
        "Data": QDate.currentDate().toString("dd/MM/yyyy"),
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
        "transaction_id": valores["transaction_id"],
        "indisponivel": "",
        "Data Pedido": valores["data_pedido"].strftime("%d/%m/%Y"),
        "is_upgrade": "S" if is_upgrade else "",
    }


def desmembrar_combo_planilha(
    valores: Mapping[str, Any],
    linha_base: dict[str, Any],
    skus_info: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """
    - valores["produto_principal"] = nome do combo
    - valores["valor_total"]       = total do combo (float/int ou string com vírgula)
    - skus_info[nome_combo]["composto_de"] = componentes (str | dict) - "SKU", "SKU x 2", {"sku":"...", "qtd":2}
    - skus_info[item]["tipo"]      = "produto" | "brinde" | "combo" | "assinatura"
    - skus_info[nome_combo]["divisor"]     = opcional (int>=1)
    """

    # ------- helpers -------
    def _to_dec(v: Any) -> Decimal:
        if v is None:
            return Decimal("0.00")
        if isinstance(v, int | float):  # ← antes: (int, float)
            return Decimal(str(v)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        s = str(v).strip().replace(".", "").replace(",", ".")
        try:
            return Decimal(s).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        except InvalidOperation:
            return Decimal("0.00")

    def _fmt(d: Decimal) -> str:
        return f"{d:.2f}".replace(".", ",")

    def _info_by_sku_code(sku_code: str) -> tuple[str, Mapping[str, Any]]:
        for nome, info in skus_info.items():
            if str(info.get("sku", "")).strip() == sku_code:
                return nome, info
        return sku_code, {}

    def _is_brinde_sku_code(sku_code: str) -> bool:
        _, info = _info_by_sku_code(sku_code)
        return str(info.get("tipo", "")).strip().lower() == "brinde"

    def _parse_compostos(raw: Any) -> list[tuple[str, int]]:
        out: list[tuple[str, int]] = []
        if isinstance(raw, str):
            parts = [s.strip() for s in re.split(r"[;,]", raw) if s.strip()]
        elif isinstance(raw, list):
            parts = raw
        else:
            parts = []
        for c in parts:
            if isinstance(c, dict):
                sku = str(c.get("sku") or c.get("SKU") or "").strip()
                try:
                    q = int(c.get("qtd") or c.get("quantity") or 1)
                except Exception:
                    q = 1
                if sku:
                    out.append((sku, max(1, q)))
            elif isinstance(c, str):
                m = re.match(r"^\s*([A-Za-z0-9._\-]+)\s*(?:[xX\*]\s*(\d+))?\s*$", c)
                if m:
                    sku = m.group(1).strip()
                    q = int(m.group(2)) if m.group(2) else 1
                    out.append((sku, max(1, q)))
        return out

    def _get_divisor_explicito(info_combo: Mapping[str, Any]) -> int | None:
        raw = info_combo.get("divisor")
        if isinstance(raw, int):
            return raw if raw >= 1 else None
        if isinstance(raw, str) and raw.strip().isdigit():
            v = int(raw.strip())
            return v if v >= 1 else None
        return None

    def _get_transaction_id(linha: Mapping[str, Any]) -> str:
        # cobre variações comuns de nome em planilhas
        candidatos = [
            "transaction_id",
            "Transaction ID",
            "TRANSACTION_ID",
            "ID Transação",
            "id transação",
            "Id Transação",
            "Id transação",
            "id_transacao",
            "id-transacao",
        ]
        for k in candidatos:
            if k in linha and linha[k] is not None and str(linha[k]).strip():
                return str(linha[k]).strip()
        return ""  # no seu fluxo, tende a existir

    def _finalizar_linha(nova: dict[str, Any], nome_combo: str) -> dict[str, Any]:
        # marca e padroniza campos usados pelo pipeline
        nova["Combo"] = nome_combo
        nova["is_combo"] = True  # todas as linhas geradas por desmembramento são combos
        nova["sku"] = str(nova.get("SKU", "")).strip()  # espelha para minúsculo
        if "transaction_id" not in nova or not str(nova["transaction_id"]).strip():
            nova["transaction_id"] = _get_transaction_id(linha_base)
        return nova

    # ------- dados de entrada -------
    nome_combo: str = str(valores.get("produto_principal", ""))
    info_combo: Mapping[str, Any] = skus_info.get(nome_combo, {}) or {}
    componentes: list[tuple[str, int]] = _parse_compostos(info_combo.get("composto_de") or [])

    # 🔹 marca combos explicitamente, mesmo sem componentes
    eh_combo = str(info_combo.get("tipo", "")).strip().lower() == "combo"

    if not componentes:
        lb = linha_base.copy()
        lb["is_combo"] = eh_combo  # True se tipo == "combo"
        return [lb]

    total_combo = _to_dec(valores.get("valor_total"))

    # separa cobrados (não-brinde) e brindes
    cobrados: list[tuple[str, int]] = []
    brindes: list[tuple[str, int]] = []
    for sku_code, qtd in componentes:
        (brindes if _is_brinde_sku_code(sku_code) else cobrados).append((sku_code, qtd))

    unidades_cobradas = sum(q for _, q in cobrados)
    linhas: list[dict[str, Any]] = []

    # Caso sem total ou sem itens cobrados → tudo zero
    if total_combo <= Decimal("0.00") or unidades_cobradas == 0:
        for sku_code, _qtd in componentes:
            nome_item, _ = _info_by_sku_code(sku_code)
            nova = linha_base.copy()
            nova["Produto"] = nome_item
            nova["SKU"] = sku_code
            nova["Valor Unitário"] = "0,00"
            nova["Valor Total"] = "0,00"
            try:
                nova["indisponivel"] = "S" if produto_indisponivel(nome_item, sku=sku_code) else ""
            except Exception:
                pass
            linhas.append(_finalizar_linha(nova, nome_combo))
        return linhas

    # ---- comportamento com/sem divisor explícito ----
    divisor_expl = _get_divisor_explicito(info_combo)
    if divisor_expl is not None:
        # ✅ MODO 1: DIVISOR EXPLÍCITO — NÃO fechar total agora.
        valor_unit_bruto = total_combo / Decimal(divisor_expl)
        valor_unit = valor_unit_bruto.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)

        for sku_code, qtd in cobrados:
            nome_item, _ = _info_by_sku_code(sku_code)
            total_item = (valor_unit * Decimal(qtd)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)

            nova = linha_base.copy()
            nova["Produto"] = nome_item
            nova["SKU"] = sku_code
            nova["Valor Unitário"] = _fmt(valor_unit)
            nova["Valor Total"] = _fmt(total_item)
            try:
                nova["indisponivel"] = "S" if produto_indisponivel(nome_item, sku=sku_code) else ""
            except Exception:
                pass
            linhas.append(_finalizar_linha(nova, nome_combo))

    else:
        # ✅ MODO 2: FALLBACK — rateio por unidades não-brinde e FECHA o total no último item.
        divisor_fallback = max(1, unidades_cobradas)
        valor_unit_bruto = total_combo / Decimal(divisor_fallback)

        soma_parcial = Decimal("0.00")
        for idx, (sku_code, qtd) in enumerate(cobrados):
            nome_item, _ = _info_by_sku_code(sku_code)
            if idx < len(cobrados) - 1:
                total_item = (valor_unit_bruto * Decimal(qtd)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
                soma_parcial += total_item
                valor_unit = valor_unit_bruto.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
            else:
                total_item = (total_combo - soma_parcial).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
                valor_unit = valor_unit_bruto.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)

            nova = linha_base.copy()
            nova["Produto"] = nome_item
            nova["SKU"] = sku_code
            nova["Valor Unitário"] = _fmt(valor_unit)
            nova["Valor Total"] = _fmt(total_item)
            try:
                nova["indisponivel"] = "S" if produto_indisponivel(nome_item, sku=sku_code) else ""
            except Exception:
                pass
            linhas.append(_finalizar_linha(nova, nome_combo))

    # Brindes sempre 0,00
    for sku_code, _qtd in brindes:
        nome_item, _ = _info_by_sku_code(sku_code)
        nova = linha_base.copy()
        nova["Produto"] = nome_item
        nova["SKU"] = sku_code
        nova["Valor Unitário"] = "0,00"
        nova["Valor Total"] = "0,00"
        try:
            nova["indisponivel"] = "S" if produto_indisponivel(nome_item, sku=sku_code) else ""
        except Exception:
            pass
        linhas.append(_finalizar_linha(nova, nome_combo))

    return linhas


def montar_planilha_vendas_guru(
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
    tipos = ["mensais", "bimestrais", "semestrais", "anuais", "bianuais", "trianuais"]
    contagem = {tipo: {"assinaturas": 0, "embutidos": 0, "cupons": 0} for tipo in tipos}

    if cancelador.is_set():
        print("[🚫 CANCELADOR ATIVADO] Cancelando antes de processar qualquer transação")
        return [], contagem

    linhas_planilha = []
    offset = len(estado["df_planilha_parcial"])

    def _ckey(tp: str) -> str:
        t = (tp or "").strip().lower()
        if t in contagem:
            return t
        aliases = {
            "semestral": "semestrais",
            "anual": "anuais",
            "18meses": "18meses",
            "bianual": "bianuais",
            "trianual": "trianuais",
            "trimestral": "trimestrais",
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
            return "S" if produto_indisponivel(nome, sku=sku) else ""
        except Exception:
            return ""

    # helper: janela segura (não explode se faltar ano/mês/ini/end)
    def _aplica_janela(dados_local: Mapping[str, Any], dt: datetime) -> bool:
        try:
            # validar_regras_pedido_assinatura espera dict[Any, Any]
            return bool(validar_regras_pedido_assinatura(cast(dict[Any, Any], dados_local), dt))
        except Exception as e:
            print(f"[DEBUG janela-skip] Ignorando janela por falta de contexto: {e}")
            # Sem contexto de período → NÃO aplica regras
            return False

    # helper: normaliza para timestamp
    def _to_ts(val: Any) -> float | None:
        """Converte val -> timestamp (segundos desde epoch, UTC).

        Aceita:
        - None -> None
        - int/float (ms ou s) -> float(s)
        - datetime (naive/aware) -> float(s) [naive assume UTC]
        - str (parse_date) -> float(s) [naive assume UTC]
        - objetos com .toPyDateTime() -> float(s)
        """
        if val is None:
            return None

        if isinstance(val, int | float):
            v = float(val)
            if v > 1e12:  # ms -> s
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
    transacoes_corrigidas = []

    for idx, t in enumerate(transacoes):
        if isinstance(t, dict):
            transacoes_corrigidas.append(t)
        elif isinstance(t, list):
            print(f"[⚠️ montar_planilha_vendas_guru] Corrigindo lista aninhada em transacoes[{idx}]")
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
        f"[DEBUG montar_planilha_vendas_guru] Iniciando processamento: total_transacoes={len(transacoes)} modo={modo} modo_periodo={modo_periodo_sel}"
    )

    def is_transacao_principal(trans: Mapping[str, Any], ids_validos: Sequence[str]) -> bool:
        pid = trans.get("product", {}).get("internal_id", "")
        is_bump = bool(trans.get("is_order_bump", 0))
        return pid in ids_validos and not is_bump

    # =========================
    # 🔀 MODO PRODUTOS (avulso)
    # =========================
    if modo == "produtos":
        print(f"[DEBUG produtos] total_transacoes={total_transacoes}")
        for i, transacao in enumerate(transacoes):
            if cancelador.is_set():
                return [], contagem
            try:
                valores = calcular_valores_pedidos(
                    transacao, dados, cast(Mapping[str, SKUInfo], skus_info), usar_valor_fixo=False
                )
                if not valores or not isinstance(valores, dict):
                    raise ValueError("[⚠️ calcular_valores_pedidos retornou None/ inválido]")
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
                eh_combo = str(info_combo.get("tipo", "")).strip().lower() == "combo"  # ← marcação explícita

                linha_base = gerar_linha_base_planilha(contact, valores, transacao)
                linha_base.update(
                    {
                        "Produto": nome_produto,
                        "subscription_id": "",
                        "SKU": sku_produto,
                        "Valor Unitário": formatar_valor(valores["valor_unitario"]),
                        "Valor Total": formatar_valor(valores["valor_total"]),
                        "indisponivel": ("S" if produto_indisponivel(nome_produto, sku=sku_produto) else "N"),
                    }
                )

                print(f"[DEBUG produtos:combo] i={i} composto_de={bool(info_combo.get('composto_de'))}")

                if info_combo.get("composto_de"):
                    mapeado = bool(info_combo.get("guru_ids")) and bool(info_combo.get("shopify_ids"))
                    indisponivel_combo = produto_indisponivel(nome_produto, sku=sku_produto)

                    # 🚫 regra: combo indisponível + mapeado → não desmembrar
                    if indisponivel_combo and mapeado:
                        linha_base["indisponivel"] = "S"
                        if eh_combo:
                            linha_base["is_combo"] = True  # ← marca combo mesmo sem desmembrar
                        _append_linha(linha_base, valores["transaction_id"])
                    else:
                        for linha_item in desmembrar_combo_planilha(valores, linha_base, skus_info):
                            linha_item["indisponivel"] = (
                                "S"
                                if produto_indisponivel(
                                    str(linha_item.get("Produto") or ""),
                                    sku=str(linha_item.get("SKU") or ""),
                                )
                                else "N"
                            )
                            _append_linha(linha_item, valores["transaction_id"])
                else:
                    # ✅ sem composto_de: ainda pode ser tipo="combo"
                    if eh_combo:
                        linha_base["is_combo"] = True
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
        transacoes_por_assinatura = defaultdict(list)
        for trans in transacoes:
            subscription_info = trans.get("subscription")
            if isinstance(subscription_info, dict):
                sid = subscription_info.get("id")
                if sid:
                    transacoes_por_assinatura[sid].append(trans)

        # Índice vindo de iniciar_busca_assinaturas()
        subs_idx = estado.get("subscriptions_idx", {}) or {}

        total_assinaturas = len(transacoes_por_assinatura)
        for i, (subscription_id, grupo_transacoes) in enumerate(transacoes_por_assinatura.items()):
            if cancelador.is_set():
                return [], contagem

            def safe_parse_date(t: Mapping[str, Any]) -> datetime:
                try:
                    s = str(t.get("ordered_at") or t.get("created_at") or "1900-01-01")
                    dt = parse_date(s)
                    # Normaliza para UTC aware
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
            invoice_type = str(transacao_base.get("invoice", {}).get("type", "")).strip().lower()
            is_upgrade = invoice_type == "upgrade"
            transacoes_principais = [t for t in grupo_ordenado if is_transacao_principal(t, ids_planos_validos)]
            produtos_distintos = {t.get("product", {}).get("internal_id") for t in transacoes_principais}

            usar_valor_fixo = len(produtos_distintos) > 1 or is_upgrade

            if not transacoes_principais:
                print(f"[⚠️ AVISO] Nenhuma transação principal encontrada para assinatura {subscription_id}")

            if usar_valor_fixo:
                valor_total_principal = 0.0
            elif transacoes_principais:
                valor_total_principal = sum(float(t.get("payment", {}).get("total", 0)) for t in transacoes_principais)
            else:
                valor_total_principal = float(transacao_base.get("payment", {}).get("total", 0))

            # monta transação "sintética"
            transacao = transacao_base.copy()
            transacao.setdefault("payment", {})
            transacao["payment"]["total"] = valor_total_principal
            transacao["tipo_assinatura"] = tipo_plano
            transacao["subscription"] = {"id": subscription_id}

            # 👇 garante o dict e só copia offer se existir no base
            product_base = cast(Mapping[str, Any], transacao_base.get("product", cast(Mapping[str, Any], {})))
            transacao.setdefault("product", {})
            if "offer" not in transacao["product"] and product_base.get("offer"):
                transacao["product"]["offer"] = product_base["offer"]

            # --- REGRAS DE /subscriptions ---
            info_sub = subs_idx.get(str(subscription_id))
            if info_sub:
                ativo = bool(info_sub.get("active"))
                dur_meses = info_sub.get("duracao_meses")  # ex.: 1,2,6,12,18,24,36
                periodicidade_sub = (
                    (info_sub.get("periodicidade") or "").strip().lower()
                )  # "mensal"/"bimestral" (ou "semestral" se mapeado)

                # ordered_at de referência para janela do último mês
                ordered_at_ref = safe_parse_date(transacao_base)

                # Se NÃO estiver ativa, só deixamos passar se estiver no último mês do ciclo
                if not ativo and not esta_no_ultimo_mes(ordered_at_ref, dur_meses):
                    print(
                        f"[WORKER] SKIP inativa fora do último mês (transactions): sid={subscription_id} dur={dur_meses} ordered_at={ordered_at_ref}"
                    )
                    continue

                # Se o /subscriptions trouxe periodicidade, persistimos na transação
                if periodicidade_sub:
                    transacao["periodicidade"] = periodicidade_sub  # fica disponível para cálculos seguintes

            try:
                print(
                    f"[DEBUG calcular_valores_pedidos] subscription_id={subscription_id} transacao_id={transacao.get('id')} ordered_at={transacao.get('ordered_at')} created_at={transacao.get('created_at')}"
                )
                valores = calcular_valores_pedidos(
                    transacao,
                    dados,
                    cast(Mapping[str, SKUInfo], skus_info),
                    usar_valor_fixo=usar_valor_fixo,
                )
                if not isinstance(valores, dict) or not valores.get("transaction_id"):
                    raise ValueError(f"Valores inválidos retornados: {valores}")

                # periodicidade usada para coluna/periodo
                periodicidade_atual = (
                    dados.get("periodicidade_selecionada")
                    or dados.get("periodicidade")
                    or valores.get("periodicidade")
                    or ""
                )
                periodicidade_atual = str(periodicidade_atual).strip().lower()

                # prevalece o que veio do /subscriptions, se existir
                if info_sub and str(info_sub.get("periodicidade") or "").strip():
                    periodicidade_atual = str(info_sub["periodicidade"]).strip().lower()

                data_fim_periodo = dados.get("ordered_at_end_periodo")
                data_pedido = valores["data_pedido"]

                # cupom (apenas para exibição/controle)
                payment_base = transacao_base.get("payment") or {}
                coupon = payment_base.get("coupon") or {}
                cupom_usado = (coupon.get("coupon_code") or "").strip()
                if valores.get("usou_cupom"):
                    contagem[_ckey(tipo_plano)]["cupons"] += 1

                # linha base (principal)
                contact = transacao.get("contact", {})
                linha = gerar_linha_base_planilha(
                    contact,
                    valores,
                    transacao,
                    tipo_plano=tipo_plano,
                    subscription_id=subscription_id,
                    cupom_valido=cupom_usado,
                    is_upgrade=is_upgrade,
                )

                nome_produto_principal = (dados.get("box_nome") or "").strip() or valores["produto_principal"]
                if produto_indisponivel(nome_produto_principal):
                    estado["boxes_indisp_set"].add(nome_produto_principal)

                linha["Produto"] = nome_produto_principal
                linha["SKU"] = skus_info.get(nome_produto_principal, {}).get("sku", "")
                linha["Valor Unitário"] = formatar_valor(valores["valor_unitario"])
                linha["Valor Total"] = formatar_valor(valores["valor_total"])
                linha["periodicidade"] = periodicidade_atual
                linha["indisponivel"] = _flag_indisp(
                    nome_produto_principal, skus_info.get(nome_produto_principal, {}).get("sku", "")
                )

                # (opcional) guardar duração em meses detectada via /subscriptions
                if info_sub and info_sub.get("duracao_meses"):
                    try:
                        linha["duracao_meses"] = int(info_sub["duracao_meses"])  # ex.: 18
                    except Exception:
                        pass

                # período
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

                # ✅ NUNCA aplicar brindes fora da janela
                if not _aplica_janela(dados, data_pedido):
                    valores["brindes_extras"] = []

                # 🎁 brindes extras (somente dentro da janela)
                for br in valores.get("brindes_extras") or []:
                    # normaliza: aceita dict {"nome": "..."} ou string direta
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
                            "subscription_id": subscription_id,  # garante nas derivadas
                        }
                    )
                    if linha_b["indisponivel"] == "S":
                        estado["brindes_indisp_set"].add(brinde_nome)
                    _append_linha(linha_b, valores["transaction_id"])

                # 📦 embutido por oferta - exige validade + dentro da janela
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
                    and _aplica_janela(dados, data_pedido)  # 👈 janela SEMPRE exigida
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
                    # usa total de assinaturas para a barra neste modo
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

    # ⚠️ não dropar 'indisponivel' nem 'subscription_id'
    df_novas = padronizar_planilha_bling(df_novas)

    # normaliza "indisponivel"
    if "indisponivel" in df_novas.columns:
        df_novas["indisponivel"] = df_novas["indisponivel"].map(
            lambda x: "S" if str(x).strip().lower() in {"s", "sim", "true", "1"} else ""
        )
    else:
        df_novas["indisponivel"] = [""] * len(df_novas)

    # sanity opcional: garantir subscription_id em todas as novas linhas
    if "subscription_id" in df_novas.columns and df_novas["subscription_id"].astype(str).str.strip().eq("").any():
        faltantes = df_novas[df_novas["subscription_id"].astype(str).str.strip().eq("")]
        print(f"[⚠️ SANIDADE] {len(faltantes)} linha(s) sem subscription_id; verifique geração de linhas derivadas.")
        print("Índices das linhas afetadas:", list(faltantes.index))
        print("Amostra das linhas sem subscription_id:")
        print(faltantes.head(5).to_dict(orient="records"))

    df_antigas = estado.get("df_planilha_parcial")
    if df_antigas is not None and not df_antigas.empty:
        estado["df_planilha_parcial"] = pd.concat([df_antigas, df_novas], ignore_index=True)
    else:
        estado["df_planilha_parcial"] = df_novas

    if callable(atualizar_etapa):
        atualizar_etapa("✅ Processamento concluído", total_transacoes, total_transacoes or 1)

    # 🔧 aviso agregado
    try:
        msgs = []
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
        if msgs and comunicador_global is not None:
            comunicador_global.mostrar_mensagem.emit("aviso", "Itens indisponíveis", "\n".join(msgs))
    except Exception:
        pass

    return linhas_planilha, contagem


def aplicar_regras_assinaturas(
    transacao: Mapping[str, Any],
    dados: Mapping[str, Any],
    _skus_info: Mapping[str, Any],
    base_produto_principal: str,
) -> AplicarRegrasAssinaturas:
    """Lê config_ofertas.json e aplica:

      - override da box (action.type == 'alterar_box')
      - brindes extras (action.type == 'adicionar_brindes')

    Compatível com rótulos do JSON como:
      "Assinatura 2 anos (bimestral)", "Assinatura Anual (mensal)",
      "Assinatura Bimestral (bimestral)" etc.
    Sem mudar o JSON.
    """
    regras: Sequence[Mapping[str, Any]] = obter_regras_config() or []
    res_override: str | None = None
    res_override_score: int = -1
    brindes_raw: list[dict[str, Any] | str] = []

    # --- contexto da transação ---
    payment: Mapping[str, Any] = transacao.get("payment") or {}
    coupon: Mapping[str, Any] = payment.get("coupon") or {}
    coupon_code_norm: str = _norm(str(coupon.get("coupon_code") or ""))

    tipo_ass: str = str(transacao.get("tipo_assinatura") or "").strip().lower()  # anuais, bianuais, ...
    periodicidade: str = str(dados.get("periodicidade_selecionada") or dados.get("periodicidade") or "").strip().lower()

    # Mapeia tipo_ass + periodicidade -> rótulos usados no JSON
    def _labels_assinatura(tipo: str, per: str) -> set[str]:
        # exemplos no JSON:
        # "Assinatura 2 anos (bimestral)", "Assinatura 3 anos (mensal)",
        # "Assinatura Anual (bimestral)", "Assinatura Bimestral (bimestral)"
        base: list[str] = []
        if tipo == "semestrais":
            base.append("Assinatura Semestral")
        elif tipo == "18meses":
            base.append("Assinatura 18 Meses")
        elif tipo == "bianuais":
            base.append("Assinatura 2 anos")
        elif tipo == "trianuais":
            base.append("Assinatura 3 anos")
        elif tipo == "anuais":
            base.append("Assinatura Anual")
        elif tipo == "bimestrais":
            base.append("Assinatura Bimestral")
        elif tipo == "trimestrais":
            base.append("Assinatura Trimestral")
        elif tipo == "mensais":
            base.append("Assinatura Mensal")
        out: set[str] = set()
        for b in base or ["Assinatura"]:
            out.add(f"{b} ({per})" if per else b)
        return {_norm(x) for x in out}

    labels_alvo: set[str] = _labels_assinatura(tipo_ass, periodicidade)
    base_prod_norm: str = _norm(base_produto_principal)

    def _assinatura_match(lista: Sequence[str] | None) -> tuple[bool, int]:
        """Retorna (casou?, score). Score maior = mais específico.

        Regras:
          - lista vazia => aplica (score 0)
          - se qualquer item da lista bate exatamente com um dos rótulos conhecidos -> score 3
          - se item corresponde ao nome do box atual -> score 2
          - se item contém tokens genéricos (anual / 2 anos / 3 anos / mensal / bimestral) presentes no rótulo -> score 1
        """
        if not lista:
            return True, 0

        tokens_genericos = {"semestral", "18meses", "anual", "2 anos", "3 anos", "mensal", "bimestral", "trimestral"}
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
        alvo_cupom: str = _norm(str(cupom_cfg.get("nome") or ""))
        if not alvo_cupom or alvo_cupom != coupon_code_norm:
            continue

        assinaturas_lista = r.get("assinaturas") or []
        ok, score = _assinatura_match(assinaturas_lista)
        if not ok:
            continue

        action: Mapping[str, Any] = r.get("action") or {}
        atype = str(action.get("type") or "").strip().lower()

        if atype == "adicionar_brindes":
            # pode vir lista de strings ou de objetos
            items = action.get("brindes") or []
            if isinstance(items, list):
                for b in items:
                    if isinstance(b, dict | str):
                        brindes_raw.append(b)

        elif atype == "alterar_box":
            box = str(action.get("box") or "").strip()
            if box and score > res_override_score:
                res_override = box
                res_override_score = score

    # Normalização final: remove duplicatas e ignora iguais ao box atual/override.
    override_norm = _norm(res_override or base_produto_principal)
    uniq: list[dict[str, Any]] = []
    seen: set[str] = set()

    for b in brindes_raw:
        if isinstance(b, dict):
            nb = str(b.get("nome", "")).strip()
            payload: dict[str, Any] = dict(b)
            if not nb:
                # se não veio 'nome', tenta usar 'nome' a partir de outra chave, senão pula
                continue
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

    return AplicarRegrasAssinaturas(override_box=res_override, brindes_extra=uniq)


class CalcularPedido(TypedDict):
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


def calcular_valores_pedidos(
    transacao: Mapping[str, Any],
    dados: Mapping[str, Any],
    skus_info: SKUs,
    usar_valor_fixo: bool = False,
) -> CalcularPedido:
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

    print(f"[DEBUG calcular_valores_pedidos] id={transaction_id} internal_id={internal_id} modo={modo}")

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
                f"[⚠️ calcular_valores_pedidos] internal_id '{internal_id}' sem match; usando fallback '{produto_principal}'."
            )
        except StopIteration:
            print(f"[⚠️ calcular_valores_pedidos] skus_info vazio; retornando estrutura mínima para '{transaction_id}'.")
            return CalcularPedido(
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
        return CalcularPedido(
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
            validar_regras_pedido_assinatura(
                cast(dict[Any, Any], dados),  # <-- converte Mapping -> dict p/ mypy
                data_pedido,
            )
        )
    except Exception as e:
        print(f"[DEBUG janela-skip] Erro em validar_regras_pedido_assinatura: {e}")
        aplica_regras_neste_periodo = False

    # Regras/cupom/override só se dentro do período
    if aplica_regras_neste_periodo:
        try:
            regras_aplicadas: AplicarRegrasAssinaturas = cast(
                AplicarRegrasAssinaturas,
                aplicar_regras_assinaturas(
                    cast(dict[Any, Any], transacao),  # <-- Mapping -> dict
                    cast(dict[Any, Any], dados),  # <-- Mapping -> dict
                    cast(dict[Any, Any], skus_info),  # <-- Mapping[str, SKUInfo] -> dict[Any, Any]
                    produto_principal,
                )
                or {},
            )
        except Exception as e:
            print(f"[⚠️ regras] Erro em aplicar_regras_assinaturas: {e}")
            regras_aplicadas = AplicarRegrasAssinaturas()
    else:
        regras_aplicadas = AplicarRegrasAssinaturas()

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
    elif tipo_assinatura == "18meses":
        divisor = 18 if periodicidade == "mensal" else 9
    elif tipo_assinatura == "anuais":
        divisor = 12 if periodicidade == "mensal" else 6
    elif tipo_assinatura == "semestrais":
        divisor = 6 if periodicidade == "mensal" else 3
    elif tipo_assinatura == "trimestrais":
        divisor = 3 if periodicidade == "mensal" else 1
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

    return CalcularPedido(
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


# Registrar envios por planilha


def registrar_envios_planilha_guru() -> None:
    # QFileDialog.getOpenFileName -> tuple[str, str]
    caminho_tuple: tuple[str, str] = QFileDialog.getOpenFileName(
        cast(QWidget, None),
        "Selecionar planilha de envios já realizados",
        "",
        "Planilhas (*.xlsx *.xls *.csv)",
    )
    caminho_arquivo: str = caminho_tuple[0]
    if not caminho_arquivo:
        return

    try:
        # df de entrada
        if caminho_arquivo.endswith((".xls", ".xlsx")):
            df: pd.DataFrame = pd.read_excel(caminho_arquivo)
        else:
            df = pd.read_csv(caminho_arquivo)
        df.columns = pd.Index([str(c).strip().lower() for c in df.columns])

        # valida colunas mínimas
        tem_transacao: bool = "id transação" in df.columns
        tem_assinatura: bool = "assinatura código" in df.columns
        if not tem_transacao and not tem_assinatura:
            comunicador_global.mostrar_mensagem.emit(
                "erro",
                "Erro",
                "A planilha deve conter a coluna 'id transação' e/ou 'assinatura código'.",
            )
            return

        # normaliza colunas derivadas (evita usar Series em expressão booleana)
        if tem_transacao:
            df["transaction_id"] = df["id transação"].astype(str).str.strip()
        else:
            df["transaction_id"] = ""

        if tem_assinatura:
            df["subscription_id"] = df["assinatura código"].astype(str).str.strip()
        else:
            df["subscription_id"] = ""

        # ===== Pergunta ano/mês =====
        ano_atual: int = int(QDate.currentDate().year())
        mes_padrao: int = int(QDate.currentDate().month())

        ano_sel, ok1 = QInputDialog.getInt(
            cast(QWidget, None),
            "Selecionar Ano",
            "Ano do envio:",
            value=ano_atual,
            min=2020,
            max=2035,
        )
        if not ok1:
            return
        ano: int = int(ano_sel)

        mes_sel, ok2 = QInputDialog.getInt(
            cast(QWidget, None),
            "Selecionar Mês",
            "Mês (1 a 12):",
            value=mes_padrao,
            min=1,
            max=12,
        )
        if not ok2:
            return
        mes: int = int(mes_sel)

        bimestre: int = 1 + (mes - 1) // 2

        # ===== Pergunta periodicidade =====
        periodicidades: list[str] = ["mensal", "bimestral"]
        periodicidade_sel, okp = QInputDialog.getItem(
            cast(QWidget, None),
            "periodicidade",
            "Periodicidade dos registros:",
            periodicidades,
            editable=False,
        )
        if not okp:
            return
        periodicidade: str = str(periodicidade_sel)

        registros_assinaturas: list[dict[str, Any]] = []
        registros_produtos: list[dict[str, Any]] = []
        registro_em: str = local_now().strftime("%Y-%m-%d %H:%M:%S")

        # ===== Montagem dos registros =====
        for _, r in df.iterrows():
            sid: str = str(r.get("subscription_id", "")).strip()
            tid: str = str(r.get("transaction_id", "")).strip()

            if sid:
                periodo: int = mes if periodicidade == "mensal" else bimestre
                registros_assinaturas.append(
                    {
                        "subscription_id": sid,
                        "ano": ano,
                        "periodicidade": periodicidade,
                        "periodo": periodo,
                        "registro_em": registro_em,
                    }
                )
            elif tid:
                registros_produtos.append(
                    {
                        "transaction_id": tid,
                        "registro_em": registro_em,
                    }
                )

        if not registros_assinaturas and not registros_produtos:
            comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhum registro válido encontrado para salvar.")
            return

        caminho_excel: str = os.path.join(os.path.dirname(__file__), "Envios", "envios_log.xlsx")
        os.makedirs(os.path.dirname(caminho_excel), exist_ok=True)

        if registros_assinaturas:
            verificar_duplicidade_no_log(
                caminho_excel,
                registros_assinaturas,
                sheet_name="assinaturas",
            )
        if registros_produtos:
            verificar_duplicidade_no_log(
                caminho_excel,
                registros_produtos,
                sheet_name="produtos",
            )

        total: int = len(registros_assinaturas) + len(registros_produtos)
        comunicador_global.mostrar_mensagem.emit(
            "info",
            "Importação concluída",
            f"{total} registro(s) foram adicionados ao log de envios.",
        )

    except Exception as e:
        comunicador_global.mostrar_mensagem.emit(
            "erro",
            "Erro",
            f"Erro ao importar a planilha:\n{e}",
        )


# Importar pedidos por planilha


def importar_planilha_pedidos_guru() -> None:
    # QFileDialog.getOpenFileName -> tuple[str, str]
    caminho_tuple: tuple[str, str] = QFileDialog.getOpenFileName(
        None,
        "Selecione a planilha de pedidos",
        "",
        "Arquivos CSV (*.csv);;Arquivos Excel (*.xlsx)",
    )
    caminho: str = caminho_tuple[0]
    if not caminho:
        return

    # df de entrada
    try:
        if caminho.endswith(".csv"):
            df: pd.DataFrame = pd.read_csv(caminho, sep=";", encoding="utf-8", quotechar='"', dtype=str)
        else:
            df = pd.read_excel(caminho, dtype=str)  # lê tudo como string p/ evitar auto-conversões
    except Exception as e:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro", f"Erro ao carregar planilha: {e}")
        return

    # ===== Selecionar produto a partir do skus.json =====
    skus_map: Mapping[str, dict[str, Any]] = cast(Mapping[str, dict[str, Any]], skus_info)
    nomes_produtos: list[str] = sorted(skus_map.keys())

    # QInputDialog.getItem -> tuple[str, bool]
    produto_nome_sel, ok = QInputDialog.getItem(
        cast(QWidget, None),
        "Selecionar Produto",
        "Escolha o nome do produto para todas as linhas:",
        nomes_produtos,
        editable=False,
    )
    produto_nome: str = str(produto_nome_sel)
    if not ok or not produto_nome:
        return

    info_produto: dict[str, Any] | None = skus_map.get(produto_nome)
    if not info_produto:
        comunicador_global.mostrar_mensagem.emit(
            "erro", "Produto não encontrado", f"'{produto_nome}' não está no skus.json"
        )
        return

    sku: str = str(info_produto.get("sku", ""))

    # ===== Helpers =====

    def remove_milhar_pt(s: str) -> str:
        """
        Remove apenas pontos que são separadores de milhar no padrão PT-BR.
        Ex.: '2.349,92' -> '2349,92' ; '1.997,52' -> '1997,52'
        (não mexe em outros pontos que não estejam nessa posição)
        """
        if not isinstance(s, str):
            s = str(s) if s is not None else ""
        s = s.strip()
        # ponto antes de exatamente 3 dígitos e seguido de vírgula ou fim
        return re.sub(r"\.(?=\d{3}(?:,|$))", "", s)

    def parse_money(val: Any) -> float:
        """
        Converte '2.349,92' / '2349,92' -> 2349.92 (float), sem jamais perder escala.
        """
        if pd.isna(val) or str(val).strip() == "":
            return 0.0
        s = remove_milhar_pt(str(val))
        s = s.replace(",", ".")
        try:
            return round(float(s), 2)
        except Exception:
            return 0.0

    def fmt_brl(num: float | int | None) -> str:
        """2349.92 -> '2349,92' (sem separador de milhar)."""
        if num is None or (isinstance(num, float) and pd.isna(num)):
            return ""
        try:
            return f"{float(num):.2f}".replace(".", ",")
        except Exception:
            return ""

    def limpar(valor: Any) -> str:
        return "" if pd.isna(valor) else str(valor).strip()

    def eh_assinatura(nome_produto: str) -> bool:
        return "assinatura" in (str(nome_produto) or "").lower()

    def inferir_periodicidade(id_produto: str) -> str:
        txt = (str(id_produto) or "").upper()
        if "-MES" in txt:
            return "mensal"
        if "-BIM" in txt:
            return "bimestral"
        return "bimestral"  # padrão

    def inferir_tipo_assinatura(nome_produto: str) -> str:
        s = (str(nome_produto) or "").lower()
        if "3 anos" in s or "3 ano" in s or "3anos" in s:
            return "trianuais"
        if "2 anos" in s or "2 ano" in s or "2anos" in s:
            return "bianuais"
        if "anual" in s:
            return "anuais"
        if "18 meses" in s:
            return "18meses"
        if "semestral" in s:
            return "semestrais"
        if "trimestral" in s:
            return "trimestrais"
        if "bimestral" in s:
            return "bimestrais"
        if "mensal" in s:
            return "mensais"
        return "anuais"  # fallback

    # 🧮 Tabela multi-ano
    TABELA_VALORES: dict[tuple[str, str], int] = {
        ("anuais", "mensal"): 960,
        ("anuais", "bimestral"): 480,
        ("bianuais", "mensal"): 1920,
        ("bianuais", "bimestral"): 960,
        ("trianuais", "mensal"): 2880,
        ("trianuais", "bimestral"): 1440,
        ("18meses", "mensal"): 1440,
        ("semestrais", "mensal"): 480,
        ("trimestrais", "mensal"): 294,
        ("bimestrais", "bimestral"): 98,
        ("mensais", "mensal"): 98,
    }

    def divisor_para(tipo_assinatura: str, periodicidade: str) -> int:
        ta = (tipo_assinatura or "").lower().strip()
        per = (periodicidade or "").lower().strip()
        if ta == "trianuais":
            return 36 if per == "mensal" else 18
        if ta == "bianuais":
            return 24 if per == "mensal" else 12
        if ta == "18meses":
            return 18 if per == "mensal" else 9
        if ta == "anuais":
            return 12 if per == "mensal" else 6
        if ta == "semestrais":
            return 6 if per == "mensal" else 3
        if ta == "trimestrais":
            return 3 if per == "mensal" else 1
        if ta == "bimestrais":
            return 2 if per == "mensal" else 1
        if ta == "mensais":
            return 1
        return 1

    registros: list[dict[str, Any]] = []

    # df.iterrows() -> (index: Any, linha: pd.Series)
    for _, linha in df.iterrows():
        # protege contra linhas vazias
        if pd.isna(linha.get("email contato")) and pd.isna(linha.get("nome contato")):
            continue

        try:
            # campos base da planilha Guru
            valor_venda_str: str = remove_milhar_pt(
                str(linha.get("valor venda", "")).strip()
            )  # '2.349,92' -> '2349,92'
            valor_venda: float = parse_money(valor_venda_str)  # -> 2349.92

            nome_prod: str = str(linha.get("nome produto", ""))
            id_prod: str = str(linha.get("id produto", ""))
            assinatura_codigo: str = (
                str(linha.get("assinatura código") or linha.get("assinatura codigo") or "")
            ).strip()

            is_assin: bool = eh_assinatura(nome_prod)
            periodicidade: str = inferir_periodicidade(id_prod) if is_assin else ""
            tipo_ass: str = inferir_tipo_assinatura(nome_prod) if is_assin else ""

            # Fallback de preços: assinatura sem "assinatura código"
            usar_fallback: bool = bool(is_assin and assinatura_codigo == "")

            # Base para aplicar divisor
            if is_assin:
                if usar_fallback and tipo_ass in {"anuais", "bianuais", "trianuais"}:
                    base: float = float(TABELA_VALORES.get((tipo_ass, periodicidade), valor_venda))
                else:
                    base = float(valor_venda)
                div: int = divisor_para(tipo_ass, periodicidade)
                valor_unitario_f: float = round(base / max(div, 1), 2)
                valor_total_item_f: float = valor_unitario_f  # qtd = 1
            else:
                valor_unitario_f = valor_venda
                valor_total_item_f = valor_venda

            total_pedido_f: float = valor_venda  # sempre o valor efetivamente pago

            cpf: str = limpar(linha.get("doc contato")).zfill(11)
            cep: str = limpar(linha.get("cep contato")).zfill(8)[:8]
            telefone: str = limpar(linha.get("telefone contato"))

            data_pedido_raw: Any = linha.get("data pedido", "")
            try:
                data_pedido: str = pd.to_datetime(data_pedido_raw, dayfirst=True).strftime("%d/%m/%Y")
            except Exception:
                data_pedido = QDate.currentDate().toString("dd/MM/yyyy")

            registros.append(
                {
                    "Número pedido": "",
                    "Nome Comprador": limpar(linha.get("nome contato")),
                    "Data": QDate.currentDate().toString("dd/MM/yyyy"),
                    "CPF/CNPJ Comprador": cpf,
                    "Endereço Comprador": limpar(linha.get("logradouro contato")),
                    "Bairro Comprador": limpar(linha.get("bairro contato")),
                    "Número Comprador": limpar(linha.get("número contato")),
                    "Complemento Comprador": limpar(linha.get("complemento contato")),
                    "CEP Comprador": cep,
                    "Cidade Comprador": limpar(linha.get("cidade contato")),
                    "UF Comprador": limpar(linha.get("estado contato")),
                    "Telefone Comprador": telefone,
                    "Celular Comprador": telefone,
                    "E-mail Comprador": limpar(linha.get("email contato")),
                    "Produto": produto_nome,
                    "SKU": sku,
                    "Un": "UN",
                    "Quantidade": "1",
                    # >>> valores BR prontos (sem milhar, vírgula decimal) <<<
                    "Valor Unitário": fmt_brl(valor_unitario_f),
                    "Valor Total": fmt_brl(valor_total_item_f),
                    "Total Pedido": fmt_brl(total_pedido_f),
                    "Valor Frete Pedido": "",
                    "Valor Desconto Pedido": "",
                    "Outras despesas": "",
                    "Nome Entrega": limpar(linha.get("nome contato")),
                    "Endereço Entrega": limpar(linha.get("logradouro contato")),
                    "Número Entrega": limpar(linha.get("número contato")),
                    "Complemento Entrega": limpar(linha.get("complemento contato")),
                    "Cidade Entrega": limpar(linha.get("cidade contato")),
                    "UF Entrega": limpar(linha.get("estado contato")),
                    "CEP Entrega": cep,
                    "Bairro Entrega": limpar(linha.get("bairro contato")),
                    "Transportadora": "",
                    "Serviço": "",
                    "Tipo Frete": "0 - Frete por conta do Remetente (CIF)",
                    "Observações": "",
                    "Qtd Parcela": "",
                    "Data Prevista": "",
                    "Vendedor": "",
                    "Forma Pagamento": limpar(linha.get("pagamento")),
                    "ID Forma Pagamento": "",
                    "transaction_id": limpar(linha.get("id transação")),
                    "indisponivel": "S" if produto_indisponivel(produto_nome) else "",
                    # metadados úteis para auditoria
                    "periodicidade": periodicidade,
                    "Plano Assinatura": tipo_ass if is_assin else "",
                    "assinatura_codigo": assinatura_codigo,
                    "Data Pedido": data_pedido,
                }
            )
        except Exception as e:
            print(f"❌ Erro ao processar linha: {e}")

    if not registros:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhum registro foi importado.")
        return

    df_importado: pd.DataFrame = pd.DataFrame(registros)

    # Padroniza colunas (NÃO mexe mais em monetários aqui)
    df_importado = padronizar_planilha_bling(df_importado)

    # Garante novamente o formato BR sem milhar (caso algo mexa depois)
    for col in ["Valor Unitário", "Valor Total", "Total Pedido"]:
        if col in df_importado.columns:
            df_importado[col] = (
                df_importado[col].astype(str).str.replace(".", "", regex=False)
            )  # remove milhar residual
            # se houver perdido vírgula, repõe 2 casas (somente quando a string for só dígitos)
            df_importado[col] = df_importado[col].apply(
                lambda s: (f"{float(s.replace(',', '.')):.2f}".replace(".", ",")) if re.search(r"\d", s) else s
            )

    # estado é global e possivelmente sem tipo -> cast local
    estado_map: dict[str, Any] = cast(dict[str, Any], estado)
    if "df_planilha_parcial" not in estado_map:
        estado_map["df_planilha_parcial"] = pd.DataFrame()

    estado_map["df_planilha_parcial"] = pd.concat([estado_map["df_planilha_parcial"], df_importado], ignore_index=True)
    estado_map["transacoes_obtidas"] = True

    comunicador_global.mostrar_mensagem.emit(
        "info",
        "Importado com sucesso",
        f"{len(df_importado)} registros adicionados à planilha parcial.",
    )


# Importação brindes do comercial


def importar_brindes_comercial(skus_info: dict[str, Any]) -> None:
    caminho, _ = QFileDialog.getOpenFileName(
        None, "Selecionar planilha do comercial", "", "Planilhas Excel (*.xlsx *.xls)"
    )
    if caminho:
        incluir_brindes_comercial(caminho, skus_info)


# captura CÓDIGO dentro de parênteses, p.ex. (L002A)

SKU_RE = re.compile(r"\(([A-Za-z0-9._\-]+)\)")


def _build_sku_index(skus_info: Mapping[str, Any]) -> dict[str, str]:
    """Constrói um índice SKU (UPPER) -> nome_padrao a partir do skus_info.

    Espera-se skus_info no formato: {nome_padrao: {"sku": "...", ...}, ...}
    """
    idx = {}
    for nome_padrao, info in (skus_info or {}).items():
        sku = str((info or {}).get("sku", "")).strip()
        if sku:
            idx[sku.upper()] = nome_padrao
    return idx


def _extract_first_sku(texto: str) -> str:
    """Extrai o PRIMEIRO SKU encontrado no texto no padrão 'Nome (SKU)'.

    Retorna string (pode ser "").
    """
    if not texto:
        return ""
    m = SKU_RE.search(str(texto))
    return (m.group(1) if m else "").strip()


def _extract_all_skus(texto: str) -> list:
    """Extrai TODOS os SKUs de uma string possivelmente com múltiplos nomes, ex.: 'Heráclito
    (B003A), David Hume (B004A), Leviatã (L002A)' -> ['B003A','B004A','L002A']"""
    if not texto:
        return []
    return [m.strip() for m in SKU_RE.findall(str(texto)) if m and str(m).strip()]


def incluir_brindes_comercial(
    caminho_planilha_comercial: str,
    skus_info: Mapping[str, Any],
) -> None:
    try:
        df_comercial: pd.DataFrame = pd.read_excel(caminho_planilha_comercial)
    except Exception as e:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro", f"Erro ao ler a planilha do comercial: {e}")
        return

    # normalização básica
    df_comercial.columns = df_comercial.columns.str.strip().str.lower()
    if "subscription_id" not in df_comercial.columns:
        comunicador_global.mostrar_mensagem.emit(
            "erro", "Erro", "A planilha do comercial precisa ter a coluna 'subscription_id'."
        )
        return
    df_comercial = df_comercial.dropna(subset=["subscription_id"])

    # df parcial (destino)
    df_saida_any: Any = estado.get("df_planilha_parcial")
    if not isinstance(df_saida_any, pd.DataFrame) or df_saida_any.empty:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro", "Planilha parcial não carregada.")
        return
    df_saida: pd.DataFrame = df_saida_any

    # garante colunas usadas
    for col in ("subscription_id", "SKU", "Produto"):
        if col not in df_saida.columns:
            df_saida[col] = ""

    # índice SKU -> nome_padrao
    sku_index: dict[str, str] = _build_sku_index(skus_info)
    if not sku_index:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro", "Índice de SKUs vazio no skus_info.")
        return

    # ---------- escolha do BOX ORIGINAL (apenas por SKU) ----------
    lista_skus = sorted(sku_index.keys(), key=str.casefold)

    parent_widget: QWidget = cast(QWidget, QApplication.activeWindow() or QWidget())
    opcao_escolhida, ok = QInputDialog.getItem(
        parent_widget,
        "Box original (SKU)",
        "Selecione o SKU do BOX ORIGINAL (produto a ser substituído):",
        lista_skus,
        0,
        False,
    )
    if not ok or not str(opcao_escolhida).strip():
        comunicador_global.mostrar_mensagem.emit("aviso", "Cancelado", "Operação cancelada pelo usuário.")
        return

    sku_box_original = str(opcao_escolhida).strip()

    novas_linhas: list[pd.Series] = []

    # ---------- processa cada linha da planilha comercial ----------
    for _, row in df_comercial.iterrows():
        subscription_id = str(row.get("subscription_id", "")).strip()
        if not subscription_id:
            continue

        # 1) SUBSTITUIÇÃO do box principal (NÃO cria linha)
        sku_box_novo = _extract_first_sku(str(row.get("box_principal", "")).strip())
        if sku_box_novo:
            # nome_padrao a partir do SKU; se não existir, usa o próprio texto do comercial como fallback
            nome_padrao_box_novo = sku_index.get(sku_box_novo.upper())
            mask_sub = df_saida["subscription_id"].astype(str).str.strip() == subscription_id
            mask_box_original = df_saida["SKU"].astype(str).str.strip().str.upper() == sku_box_original.upper()
            idx_alvo = df_saida[mask_sub & mask_box_original].index

            for idx in idx_alvo:
                if nome_padrao_box_novo:
                    df_saida.at[idx, "Produto"] = nome_padrao_box_novo
                df_saida.at[idx, "SKU"] = sku_box_novo  # substitui pelo novo SKU

        # 2) BRINDES: cria NOVA LINHA por SKU (dedup por subscription_id + SKU)
        brindes_str = str(row.get("brindes", "")).strip()
        if not brindes_str:
            continue

        skus_brindes: list[str] = _extract_all_skus(brindes_str)
        if not skus_brindes:
            continue

        mask_sub = df_saida["subscription_id"].astype(str).str.strip() == subscription_id
        linhas_base = df_saida[mask_sub]

        for sku_brinde in skus_brindes:
            sku_brinde_norm = str(sku_brinde).strip()
            if not sku_brinde_norm:
                continue

            # deduplicação por (subscription_id, SKU)
            ja_existe = not df_saida[
                mask_sub & (df_saida["SKU"].astype(str).str.strip().str.upper() == sku_brinde_norm.upper())
            ].empty
            if ja_existe:
                continue

            # cria a NOVA linha do brinde
            if not linhas_base.empty:
                base = linhas_base.iloc[0].copy()
                # nome do produto a partir do índice SKU -> nome_padrao
                nome_padrao_brinde = sku_index.get(sku_brinde_norm.upper())
                if nome_padrao_brinde:
                    base["Produto"] = nome_padrao_brinde
                base["SKU"] = sku_brinde_norm

                if "Valor Unitário" in base.index:
                    base["Valor Unitário"] = 0.0
                if "Valor Total" in base.index:
                    base["Valor Total"] = 0.0

                base["subscription_id"] = subscription_id
                if "transaction_id" in base.index:
                    base["transaction_id"] = ""

                if "Quantidade" in base.index and (
                    pd.isna(base["Quantidade"]) or str(base["Quantidade"]).strip() == ""
                ):
                    base["Quantidade"] = 1

                novas_linhas.append(base)

    # concatena novas linhas (se houver) e salva
    if novas_linhas:
        df_novas = pd.DataFrame(novas_linhas)
        df_final = pd.concat([df_saida, df_novas], ignore_index=True)
        estado["df_planilha_parcial"] = df_final
        comunicador_global.mostrar_mensagem.emit("info", "Sucesso", f"{len(novas_linhas)} brinde(s) adicionados.")
    else:
        estado["df_planilha_parcial"] = df_saida
        comunicador_global.mostrar_mensagem.emit("info", "Sucesso", "Substituições realizadas (nenhum brinde novo).")


# Geração e controle de logs de envios DMG


def remover_pedidos_enviados() -> None:
    # estado é global
    df_any: Any = estado.get("df_planilha_parcial")
    if not isinstance(df_any, pd.DataFrame) or df_any.empty:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhuma planilha carregada para filtrar.")
        return
    df_orig: pd.DataFrame = df_any

    # -- cópia de trabalho com nomes normalizados (não toca df_orig) --
    df: pd.DataFrame = df_orig.copy()
    df.columns = df.columns.str.strip()
    df.columns = df.columns.str.lower()

    # 🔒 elimina colunas duplicadas por nome normalizado (mantém a 1ª ocorrência)
    if df.columns.duplicated().any():
        df = df.loc[:, ~df.columns.duplicated(keep="first")]

    # helper para coalescer colunas por "nome lógico" (após normalização)
    def col_series(_df: pd.DataFrame, logical_name: str, default: Any = "") -> pd.Series[Any]:
        cols = [c for c in _df.columns if c.strip().lower() == logical_name]
        if not cols:
            # aqui o mypy já sabe que é Series[Any]
            return pd.Series([default] * len(_df), index=_df.index)

        if len(cols) == 1:
            s: pd.Series[Any] = _df[cols[0]]
        else:
            # pega a 1ª não-nula na horizontal entre colunas duplicadas
            s = cast(pd.Series[Any], _df[cols].bfill(axis=1).iloc[:, 0])

        return s

    # aliases só na cópia de trabalho (após deduplicar colunas)
    if "assinatura código" in df.columns and "subscription_id" not in df.columns:
        df["subscription_id"] = df["assinatura código"]
    if "id transação" in df.columns and "transaction_id" not in df.columns:
        df["transaction_id"] = df["id transação"]

    # ---------------------------
    # Normalização de campos base
    # ---------------------------
    def _norm_tx(x: Any) -> str:
        return str(x).strip()  # mantém hífens

    def _norm_sku(x: Any) -> str:
        return str(x).strip().upper()  # SKU maiúsculo

    def _key_no_plus(tx: str, sku: str) -> str:
        return f"{_norm_tx(tx)}{_norm_sku(sku)}"  # sem separador

    def _key_with_plus(tx: str, sku: str) -> str:
        return f"{_norm_tx(tx)}+{_norm_sku(sku)}"  # com '+'

    # ✅ SKU / IDs
    df["sku"] = col_series(df, "sku", "").astype(str).fillna("").map(_norm_sku)
    df["subscription_id"] = col_series(df, "subscription_id", "").astype(str).fillna("").str.strip()
    df["transaction_id"] = col_series(df, "transaction_id", "").astype(str).fillna("").map(_norm_tx)

    # ✅ periodicidade / periodo
    df["periodicidade"] = col_series(df, "periodicidade", "").astype(str).str.lower().str.strip().replace({"nan": ""})
    df["periodo"] = pd.to_numeric(col_series(df, "periodo", -1), errors="coerce").fillna(-1).astype(int)

    # ✅ is_combo (normaliza para bool-like)
    def _to_bool(v: Any) -> bool:
        s = str(v).strip().lower()
        return s in {"true", "1", "s", "sim", "t", "y", "yes"}

    df["is_combo"] = col_series(df, "is_combo", False).map(_to_bool).fillna(False)

    # seleção do período (passa QWidget, não None)
    ano_atual: int = QDate.currentDate().year()
    mes_padrao: int = QDate.currentDate().month()
    parent_widget: QWidget = cast(QWidget, QApplication.activeWindow() or QWidget())

    ano, ok1 = QInputDialog.getInt(
        parent_widget, "Selecionar Ano", "Ano do envio:", value=ano_atual, min=2020, max=2035
    )
    if not ok1:
        return
    mes, ok2 = QInputDialog.getInt(parent_widget, "Selecionar Mês", "Mês (1 a 12):", value=mes_padrao, min=1, max=12)
    if not ok2:
        return
    bimestre: int = 1 + (mes - 1) // 2

    # carrega log
    caminho_excel = os.path.join(os.path.dirname(__file__), "Envios", "envios_log.xlsx")
    assinaturas_existentes: set[tuple[str, int, str, int]] = set()
    produtos_existentes: set[str] = set()
    combos_existentes: set[str] = set()  # aceita chave com e sem '+'

    if os.path.exists(caminho_excel):
        try:
            xls_all = pd.read_excel(caminho_excel, sheet_name=None)
            assinaturas_df = xls_all.get("assinaturas", pd.DataFrame())
            produtos_df = xls_all.get("produtos", pd.DataFrame())
            combos_df = xls_all.get("combos", pd.DataFrame())

            # ----- assinaturas -----
            for col in ("subscription_id", "periodicidade", "periodo", "ano"):
                if col not in assinaturas_df.columns:
                    assinaturas_df[col] = "" if col in ("subscription_id", "periodicidade") else -1
            assinaturas_df["subscription_id"] = assinaturas_df["subscription_id"].astype(str).str.strip()
            assinaturas_df["periodicidade"] = assinaturas_df["periodicidade"].astype(str).str.lower().str.strip()
            assinaturas_df["periodo"] = pd.to_numeric(assinaturas_df["periodo"], errors="coerce").fillna(-1).astype(int)
            assinaturas_df["ano"] = pd.to_numeric(assinaturas_df["ano"], errors="coerce").fillna(-1).astype(int)
            assinaturas_existentes = {
                (str(row["subscription_id"]), int(row["ano"]), str(row["periodicidade"]), int(row["periodo"]))
                for _, row in assinaturas_df.iterrows()
                if str(row.get("subscription_id", "")).strip() != ""
            }

            # ----- produtos (legacy por transaction_id inteiro) -----
            if "transaction_id" in produtos_df.columns:
                produtos_existentes = {_norm_tx(v) for v in produtos_df["transaction_id"].astype(str).tolist()}
            else:
                produtos_existentes = set()

            # ----- combos (dedup por transaction_id + sku) -----
            combos_existentes = set()
            if not combos_df.empty:
                # 1) Se houver chave_dedup, aceita como veio e também sem '+'
                if "chave_dedup" in combos_df.columns:
                    for raw in combos_df["chave_dedup"].astype(str):
                        val = str(raw).strip()
                        if not val:
                            continue
                        combos_existentes.add(val)
                        combos_existentes.add(val.replace("+", ""))  # tolera variação
                # 2) Se houver colunas separadas, monta as duas variantes
                if {"transaction_id", "sku"}.issubset(combos_df.columns):
                    for _, r in combos_df.iterrows():
                        tx = _norm_tx(r.get("transaction_id", ""))
                        sk = _norm_sku(r.get("sku", ""))
                        if tx and sk:
                            combos_existentes.add(_key_no_plus(tx, sk))
                            combos_existentes.add(_key_with_plus(tx, sk))

        except Exception as e:
            print(f"[⚠️] Erro ao ler Excel: {e}")

    linhas_antes: int = len(df)

    # ------------------------------------------------------------
    # Decisão de remoção: roteia pela flag is_combo
    # ------------------------------------------------------------
    def deve_remover(row: pd.Series) -> bool:
        id_sub = str(row.get("subscription_id", "")).strip()
        id_trans = _norm_tx(row.get("transaction_id", ""))
        sku_row = _norm_sku(row.get("sku", ""))
        is_combo = bool(row.get("is_combo", False))

        # 0) Combos: consultar SOMENTE a aba "combos"
        if is_combo:
            if id_trans and sku_row:
                k1 = _key_no_plus(id_trans, sku_row)  # ex.: a037...L008A
                k2 = _key_with_plus(id_trans, sku_row)  # ex.: a037...+L008A
                return (k1 in combos_existentes) or (k2 in combos_existentes)
            return False  # sem tx/sku não dá para deduplicar combo

        # 1) Assinaturas (por periodicidade/periodo/ano) — só se não for combo
        if id_sub:
            per = str(row.get("periodicidade", "")).strip().lower()
            if per == "mensal":
                per_num = mes
            elif per == "bimestral":
                per_num = bimestre
            else:
                return False
            if (id_sub, int(ano), per, int(per_num)) in assinaturas_existentes:
                return True

        # 2) Produtos (legacy): consultar SOMENTE a aba "produtos" por transaction_id
        if id_trans:
            return id_trans in produtos_existentes

        return False

    mask_remover: pd.Series = df.apply(deve_remover, axis=1).astype(bool)

    # -- aplica a máscara no DataFrame ORIGINAL, preservando schema/casos/acentos --
    df_filtrado: pd.DataFrame = df_orig.loc[~mask_remover].copy()

    removidas: int = linhas_antes - len(df_filtrado)
    estado["df_planilha_parcial"] = df_filtrado

    comunicador_global.mostrar_mensagem.emit(
        "info",
        "Filtragem concluída",
        f"{removidas} linha(s) removida(s) com base nos registros anteriores.",
    )


def registrar_envios(
    df: pd.DataFrame,
    ano: int,
    periodicidade: str,
    periodo: int,
) -> None:
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Não há dados para registrar.")
        return

    df = df.copy()
    # ✅ Garantias
    for col in ("indisponivel", "subscription_id", "origem", "transaction_id", "sku", "is_combo", "id_line_item"):
        if col not in df.columns:
            df[col] = ""

    df["indisponivel"] = df["indisponivel"].astype(str)
    df["subscription_id"] = df["subscription_id"].astype(str).str.strip()
    df["origem"] = df["origem"].astype(str).str.lower().str.strip()
    df["transaction_id"] = df["transaction_id"].astype(str).str.strip()
    df["id_line_item"] = df["id_line_item"].astype(str).str.strip()
    df["sku"] = df["sku"].astype(str).str.strip()

    # normaliza is_combo → bool
    def _to_bool(v: Any) -> bool:
        s = str(v).strip().lower()
        return s in {"true", "1", "s", "sim", "y", "yes"}

    df["is_combo"] = df["is_combo"].map(_to_bool) if "is_combo" in df.columns else False

    # Remove indisponíveis de cara
    df = df[~df["indisponivel"].str.upper().eq("S")].copy()
    if df.empty:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhum registro válido após remover indisponíveis.")
        return

    registros_assinaturas: list[dict[str, Any]] = []
    registros_produtos: list[dict[str, Any]] = []
    registros_combos: list[dict[str, Any]] = []
    registro_em: str = local_now().strftime("%Y-%m-%d %H:%M:%S")
    tem_id_lote: bool = "ID Lote" in df.columns
    ignorados_sem_id: int = 0

    for _, r in df.iterrows():
        is_combo = bool(r.get("is_combo", False))
        origem = str(r.get("origem", "")).strip().lower()
        id_sub = str(r.get("subscription_id", "")).strip()
        id_trans = str(r.get("transaction_id", "")).strip()
        id_line = str(r.get("id_line_item", "")).strip()
        sku = str(r.get("sku", "")).strip()

        # 1) Assinaturas
        if id_sub:
            registros_assinaturas.append(
                {
                    "subscription_id": id_sub,
                    "ano": ano,
                    "periodicidade": periodicidade,
                    "periodo": periodo,
                    "registro_em": registro_em,
                }
            )
            continue

        # 2) Combos → usar id_line_item quando existir (prioritário)
        if is_combo and sku:
            chosen_id = id_line if id_line else id_trans
            if chosen_id:
                rec: dict[str, Any] = {
                    "chave_dedup": f"{chosen_id}+{sku}",
                    "transaction_id": chosen_id,  # ← fica como id_line_item quando existir
                    "sku": sku,
                    "registro_em": registro_em,
                }
                if tem_id_lote:
                    rec["id_lote"] = str(r.get("ID Lote", "")).strip()
                registros_combos.append(rec)
            else:
                ignorados_sem_id += 1
            continue

        # 3) Produtos (legacy) — NÃO registrar avulsos da Shopify
        if (not is_combo) and id_trans and origem != "shopify":
            rec = {"transaction_id": id_trans, "registro_em": registro_em}
            if tem_id_lote:
                rec["id_lote"] = str(r.get("ID Lote", "")).strip()
            registros_produtos.append(rec)
            continue

        # 4) Demais casos ignorados
        ignorados_sem_id += 1

    if not (registros_assinaturas or registros_produtos or registros_combos):
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhum registro válido encontrado para salvar.")
        return

    caminho_excel = os.path.join(os.path.dirname(__file__), "Envios", "envios_log.xlsx")
    os.makedirs(os.path.dirname(caminho_excel), exist_ok=True)

    if registros_assinaturas:
        verificar_duplicidade_no_log(caminho_excel, registros_assinaturas, sheet_name="assinaturas")
    if registros_produtos:
        verificar_duplicidade_no_log(caminho_excel, registros_produtos, sheet_name="produtos")
    if registros_combos:
        verificar_duplicidade_no_log(caminho_excel, registros_combos, sheet_name="combos")

    total = len(registros_assinaturas) + len(registros_produtos) + len(registros_combos)
    msg = f"{total} registro(s) foram adicionados ao log."
    if registros_assinaturas:
        msg += f"\n  . Assinaturas: {len(registros_assinaturas)}"
    if registros_produtos:
        msg += f"\n  . Produtos: {len(registros_produtos)}"
    if registros_combos:
        msg += f"\n  . Combos (itens): {len(registros_combos)}"
    if ignorados_sem_id:
        msg += f"\n  . Ignorados (sem id_line_item/transaction_id ou avulsos Shopify): {ignorados_sem_id}"
    comunicador_global.mostrar_mensagem.emit("info", "Registro concluído", msg)


def iniciar_registro_envios() -> None:
    # mypy: leia como objeto e só depois tipa corretamente
    df_any: Any = estado.get("df_planilha_parcial")
    if not isinstance(df_any, pd.DataFrame) or df_any.empty:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhuma planilha carregada.")
        return
    df: pd.DataFrame = df_any

    ano_atual: int = QDate.currentDate().year()
    mes_padrao: int = QDate.currentDate().month()

    # mypy/stubs do PyQt exigem QWidget, não None
    parent_widget: QWidget = cast(QWidget, QApplication.activeWindow() or QWidget())

    ano, ok1 = QInputDialog.getInt(
        parent_widget, "Selecionar Ano", "Ano do envio:", value=ano_atual, min=2020, max=2035
    )
    if not ok1:
        return

    mes, ok2 = QInputDialog.getInt(parent_widget, "Selecionar Mês", "Mês (1 a 12):", value=mes_padrao, min=1, max=12)
    if not ok2:
        return

    bimestre: int = 1 + (mes - 1) // 2
    dff: pd.DataFrame = df.copy()

    # helper para booleanos textuais
    def _to_bool(v: Any) -> bool:
        s = str(v).strip().lower()
        return s in {"true", "1", "s", "sim", "t", "y", "yes"}

    # ✅ Garantias básicas (inclui is_combo)
    for col in ("indisponivel", "periodicidade", "subscription_id", "origem", "is_combo"):
        if col not in dff.columns:
            dff[col] = ""

    dff["indisponivel"] = dff["indisponivel"].astype(str)
    dff["periodicidade"] = dff["periodicidade"].astype(str).str.lower().replace({"nan": ""})
    dff["subscription_id"] = dff["subscription_id"].astype(str).str.strip()
    dff["origem"] = dff["origem"].astype(str).str.lower().str.strip()
    dff["is_combo"] = dff["is_combo"].map(_to_bool)

    # 🚫 Remover indisponíveis
    mask_validos = ~dff["indisponivel"].str.upper().eq("S")
    dff = dff[mask_validos].copy()
    if dff.empty:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhum registro válido após remover indisponíveis.")
        return

    # 🔹 Assinaturas
    df_mensal = dff[dff["periodicidade"].eq("mensal")].copy()
    df_bimestral = dff[dff["periodicidade"].eq("bimestral")].copy()
    # 🔹 Produtos (inclui combos e produtos avulsos)
    mask_prod = dff["subscription_id"].eq("") | dff["origem"].eq("produtos")
    df_produtos = dff[mask_prod].copy()

    if not df_mensal.empty:
        registrar_envios(df_mensal, ano, "mensal", mes)
    if not df_bimestral.empty:
        registrar_envios(df_bimestral, ano, "bimestral", bimestre)
    if not df_produtos.empty:
        registrar_envios(df_produtos, ano, "produtos", 0)

    estado["ultimo_log"] = {"ano": ano, "mes": mes, "bimestre": bimestre}

    comunicador_global.mostrar_mensagem.emit(
        "info",
        "Registro concluído",
        f"Registros salvos para {mes:02d}/{ano} (mensal), bimestre {bimestre}/{ano}"
        f"{' e produtos' if not df_produtos.empty else ''}.",
    )


def verificar_duplicidade_no_log(
    caminho: str | PathLike[str],
    novos: Sequence[Mapping[str, Any]] | pd.DataFrame,
    sheet_name: Literal["produtos", "assinaturas", "combos"],
) -> int:
    """Salva/atualiza uma planilha Excel garantindo que não haja duplicados na aba indicada. Retorna
    a quantidade de registros efetivamente adicionados.

    - caminho: caminho do arquivo .xlsx
    - novos: sequência de registros (dict-like) ou um DataFrame já pronto
    - sheet_name: "produtos" | "assinaturas" | "combos"
    """
    caminho_str = os.fspath(caminho)

    # normaliza entrada para DataFrame
    if isinstance(novos, pd.DataFrame):
        novos_df: pd.DataFrame = novos.copy()
    else:
        novos_df = pd.DataFrame(list(novos))

    # garante colunas mínimas por aba e chave de dedup
    if sheet_name == "produtos":
        if "transaction_id" not in novos_df.columns:
            novos_df["transaction_id"] = ""
        chave_unica: list[str] = ["transaction_id"]

    elif sheet_name == "assinaturas":
        for col in ("subscription_id", "ano", "periodicidade", "periodo"):
            if col not in novos_df.columns:
                novos_df[col] = "" if col in ("subscription_id", "periodicidade") else -1
        chave_unica = ["subscription_id", "ano", "periodicidade", "periodo"]

    elif sheet_name == "combos":
        # precisa de transaction_id + sku; chave_dedup = "transaction_id+sku"
        for col in ("transaction_id", "sku"):
            if col not in novos_df.columns:
                novos_df[col] = ""
        if "chave_dedup" not in novos_df.columns:
            novos_df["chave_dedup"] = (
                novos_df["transaction_id"].astype(str).str.strip() + "+" + novos_df["sku"].astype(str).str.strip()
            )
        chave_unica = ["chave_dedup"]

    else:
        raise ValueError(f"Aba desconhecida: {sheet_name!r}")

    escritor_existente = os.path.exists(caminho_str)
    todas_abas: dict[str, pd.DataFrame] = {}

    if escritor_existente:
        try:
            lidas = pd.read_excel(caminho_str, sheet_name=None)
            todas_abas = dict(lidas) if isinstance(lidas, dict) else {}
            existentes: pd.DataFrame = todas_abas.get(sheet_name, pd.DataFrame())
            tamanho_antes = len(existentes)

            combinado = pd.concat([existentes, novos_df], ignore_index=True)
            combinado = combinado.drop_duplicates(subset=chave_unica, keep="first")
            tamanho_depois = len(combinado)
        except Exception as e:
            print(f"[⚠️] Erro ao ler aba {sheet_name}: {e}")
            combinado = novos_df
            tamanho_antes = 0
            tamanho_depois = len(novos_df)
    else:
        combinado = novos_df
        tamanho_antes = 0
        tamanho_depois = len(novos_df)

    todas_abas[sheet_name] = combinado

    adicionados = tamanho_depois - tamanho_antes

    try:
        with pd.ExcelWriter(caminho_str, engine="openpyxl", mode="w") as writer:
            for aba, dfw in todas_abas.items():
                dfw.to_excel(writer, sheet_name=aba, index=False)
        print(f"[💾] {adicionados} novo(s) registro(s) adicionado(s) em '{sheet_name}'")
    except Exception as e:
        print(f"[❌] Erro ao salvar Excel: {e}")

    return adicionados


# Integração com a API da Shopify

# API SHOPIFY


def obter_api_shopify_version(now: datetime | None = None) -> str:
    """Retorna a versão trimestral da Shopify API (YYYY-01/04/07/10).
    Usa datetime aware (UTC por padrão). 'now' é opcional (útil para testes).
    """
    dt = now or datetime.now(UTC)
    y, m = dt.year, dt.month
    q_start = ((m - 1) // 3) * 3 + 1  # 1, 4, 7, 10
    return f"{y}-{q_start:02d}"


API_VERSION = obter_api_shopify_version()
GRAPHQL_URL = f"https://{settings.SHOP_URL}/admin/api/{API_VERSION}/graphql.json"

# ESTADOS


class _DadosTemp(TypedDict, total=False):
    cpfs: dict[str, Any]
    bairros: dict[str, Any]
    enderecos: dict[str, Any]


# Inicializa/garante o tipo de estado["dados_temp"] apenas aqui
dt = cast(_DadosTemp, estado.setdefault("dados_temp", {}))
dt.setdefault("cpfs", {})
dt.setdefault("bairros", {})
dt.setdefault("enderecos", {})

# Controle de taxa global
controle_threading_shopify = {"lock": threading.Lock(), "ultimo_acesso": time.time()}
min_intervalo_graphql = 0.1  # 100ms (100 chamadas/s)

# aux


def normalizar_order_id(valor: str | int) -> str:
    if isinstance(valor, str):
        valor = valor.strip()
        if "gid://" in valor and "/" in valor:
            return valor.split("/")[-1]  # ✅ extrai apenas o número
        return valor
    elif isinstance(valor, int):
        return str(valor)
    return str(valor).strip()


# Classes de Sinalização (Signals)


class _SinalFinalizacao(Protocol):
    finalizado: pyqtBoundSignal


# Classes de Runnable (Executando operações em threads)


class SinaisFulfill(QObject):
    if TYPE_CHECKING:
        concluido: pyqtBoundSignal
        erro: pyqtBoundSignal
    else:
        concluido = pyqtSignal(str, int)
        erro = pyqtSignal(str, str)


class _SinaisFulfill(Protocol):
    concluido: pyqtBoundSignal  # .emit(str, int)
    erro: pyqtBoundSignal


class _FulfillmentOrderLineItem(TypedDict):
    id: str
    quantity: int


class _FulfillmentByOrder(TypedDict):
    fulfillmentOrderId: str
    fulfillmentOrderLineItems: list[_FulfillmentOrderLineItem]


class FulfillPedidoRunnable(QRunnable):
    def __init__(self, order_id: str, itens_line_ids: list[str] | set[str]) -> None:
        super().__init__()

        # Guardamos o "order_id" da planilha (transaction_id) e utilizaremos diretamente como Order GID.
        self._order_id_planilha: str = str(order_id or "").strip()

        def _only_digits(x: str) -> str:
            return "".join(ch for ch in str(x) if ch.isdigit())

        # IDs da planilha chegam como números puros (line_item_id).
        planilha_nums = {_only_digits(item) for item in itens_line_ids if item}
        planilha_gids = {f"gid://shopify/LineItem/{n}" for n in planilha_nums}

        # Matching: aceitar número puro e GID (do LineItem).
        self._planilha_ids_match: set[str] = planilha_nums | planilha_gids
        self._planilha_nums: set[str] = planilha_nums

        self.signals: _SinaisFulfill = SinaisFulfill()

    @pyqtSlot()
    def run(self) -> None:
        try:
            print(
                f"[▶] Iniciando fulfillment (order_id_planilha={self._order_id_planilha} "
                f"itens={sorted(self._planilha_nums)[:10]}{'…' if len(self._planilha_nums) > 10 else ''})"
            )

            # --- validações ---
            digits_only = "".join(ch for ch in self._order_id_planilha if ch.isdigit())
            if not digits_only:
                raise RuntimeError("Order ID inválido na planilha (sem dígitos).")

            if not self._planilha_nums:
                raise RuntimeError("Nenhum id_line_item fornecido.")

            headers: dict[str, str] = {
                "Content-Type": "application/json",
                "X-Shopify-Access-Token": settings.SHOPIFY_TOKEN,
            }

            # rate limit global
            ctrl = cast(MutableMapping[str, Any], controle_threading_shopify)
            lock = cast(Any, ctrl["lock"])
            with lock:
                delta = float(time.time() - cast(float, ctrl.get("ultimo_acesso", 0.0)))
                if delta < min_intervalo_graphql:
                    time.sleep(min_intervalo_graphql - delta)
                ctrl["ultimo_acesso"] = time.time()

            # === (1) Order.id direto da planilha ===
            order_gid_resolvido = f"gid://shopify/Order/{int(digits_only)}"
            print(f"[🔧] Order direto da planilha: id={order_gid_resolvido}")

            # === (2) Query corrigida (assignedLocation.location.id) ===
            query_fo = """
            query($orderId: ID!) {
            order(id: $orderId) {
                id
                name
                displayFulfillmentStatus
                fulfillmentOrders(first: 20) {
                edges {
                    node {
                    id
                    status
                    requestStatus
                    assignedLocation {
                        name
                        location { id }
                    }
                    supportedActions { action }
                    lineItems(first: 10) {
                        edges {
                        node {
                            id
                            remainingQuantity
                            totalQuantity
                            lineItem {
                            id
                            sku
                            name
                            }
                        }
                        }
                    }
                    }
                }
                }
            }
            }
            """

            def _fetch_all_fos(sess: requests.Session, order_gid: str) -> list[dict[str, Any]]:
                fos: list[dict[str, Any]] = []
                after: str | None = None
                while True:
                    r = sess.post(
                        GRAPHQL_URL,
                        json={"query": query_fo, "variables": {"orderId": order_gid, "first": 50, "after": after}},
                        timeout=10,
                        verify=False,
                    )
                    r.raise_for_status()
                    j = cast(dict[str, Any], r.json())
                    conn = ((j.get("data") or {}).get("order") or {}).get("fulfillmentOrders") or {}
                    edges = cast(list[dict[str, Any]], conn.get("edges") or [])
                    for e in edges:
                        node_fo = cast(dict[str, Any], (e.get("node") or {}))
                        li_conn = node_fo.get("lineItems") or {}
                        li_edges = cast(list[dict[str, Any]], li_conn.get("edges") or [])
                        li_has_next = bool((li_conn.get("pageInfo") or {}).get("hasNextPage"))

                        # pagina lineItems se necessário
                        while li_has_next:
                            li_after = (li_conn.get("pageInfo") or {}).get("endCursor")
                            q_li_more = """
                            query($foId: ID!, $first: Int!, $after: String) {
                              node(id: $foId) {
                                ... on FulfillmentOrder {
                                  lineItems(first: $first, after: $after) {
                                    edges {
                                      cursor
                                      node {
                                        id
                                        remainingQuantity
                                        totalQuantity
                                        lineItem { id }
                                      }
                                    }
                                    pageInfo { hasNextPage endCursor }
                                  }
                                }
                              }
                            }
                            """
                            r_li = sess.post(
                                GRAPHQL_URL,
                                json={
                                    "query": q_li_more,
                                    "variables": {"foId": node_fo.get("id"), "first": 100, "after": li_after},
                                },
                                timeout=10,
                                verify=False,
                            )
                            r_li.raise_for_status()
                            j_li = cast(dict[str, Any], r_li.json())
                            n_li = ((j_li.get("data") or {}).get("node") or {}).get("lineItems") or {}
                            li_edges.extend(cast(list[dict[str, Any]], n_li.get("edges") or []))
                            li_has_next = bool((n_li.get("pageInfo") or {}).get("hasNextPage"))
                            li_conn = n_li

                        node_fo["lineItems"] = {"edges": li_edges}
                        fos.append(node_fo)

                    if not bool((conn.get("pageInfo") or {}).get("hasNextPage")):
                        break
                    after = (conn.get("pageInfo") or {}).get("endCursor")
                return fos

            with requests.Session() as sess:
                sess.headers.update(headers)
                fos_all = _fetch_all_fos(sess, order_gid_resolvido)

            print(f"[i] FOs encontrados para order={order_gid_resolvido}: {len(fos_all)}")

            # === (3) Montar payloads agrupando por localização ===
            payloads_por_location: dict[str, list[dict[str, Any]]] = {}
            encontrados: set[str] = set()
            sem_remaining_itens: list[str] = []
            motivos_fo: list[str] = []

            for node_fo in fos_all:
                fo_id = str(node_fo.get("id") or "")
                status = str(node_fo.get("status") or "").upper()
                request_status = str(node_fo.get("requestStatus") or "").upper()
                loc_obj = node_fo.get("assignedLocation") or {}
                loc_gid = str(((loc_obj.get("location") or {}).get("id")) or "")
                loc_name = str(loc_obj.get("name") or "-")

                print(f"[FO] id={fo_id} status={status} requestStatus={request_status} loc={loc_name}")

                if status in {"CANCELLED", "CLOSED", "ON_HOLD", "INCOMPLETE"}:
                    msg = f"FO {fo_id} pulado: status={status}"
                    motivos_fo.append(msg)
                    print("[•]", msg)
                    continue

                if status not in {"OPEN", "IN_PROGRESS"}:
                    msg = f"FO {fo_id} pulado: status {status} não apto"
                    motivos_fo.append(msg)
                    print("[•]", msg)
                    continue

                holds_list = cast(list[dict[str, Any]], node_fo.get("fulfillmentHolds") or [])
                if holds_list:
                    reasons = [str(h.get("reason") or "") for h in holds_list]
                    disp = [str(h.get("displayReason") or "") for h in holds_list]
                    msg = f"FO {fo_id} HOLD ({', '.join(reasons) or '-'}) display={'; '.join(disp) or '-'}"
                    motivos_fo.append(msg)
                    print("[•]", msg)
                    continue

                sa_raw = node_fo.get("supportedActions")
                supported: set[str] = set()
                if isinstance(sa_raw, list):
                    supported = {
                        str((a or {}).get("action") or "").upper() if isinstance(a, dict) else str(a).upper()
                        for a in sa_raw
                    }
                print(f"[FO] supportedActions={sorted(supported) or '-'}")
                if "CREATE_FULFILLMENT" not in supported:
                    msg = f"FO {fo_id} sem CREATE_FULFILLMENT"
                    motivos_fo.append(msg)
                    print("[•]", msg)
                    continue

                li_edges = cast(list[dict[str, Any]], ((node_fo.get("lineItems") or {}).get("edges") or []))
                print(f"[FO] lineItems: {len(li_edges)}")

                items: list[dict[str, Any]] = []
                for li in li_edges:
                    li_node = cast(dict[str, Any], li.get("node") or {})
                    foli_gid = str(li_node.get("id", "") or "")
                    line_item_gid = str((li_node.get("lineItem") or {}).get("id", "") or "")
                    line_item_num = "".join(ch for ch in line_item_gid if ch.isdigit())
                    remaining = int(li_node.get("remainingQuantity") or 0)
                    total = int(li_node.get("totalQuantity") or 0)
                    candidatos = {c for c in (line_item_gid, line_item_num) if c}
                    match = bool(self._planilha_ids_match.intersection(candidatos))

                    print(
                        f"[LI] foli={foli_gid.split('/')[-1]} lineItem={line_item_num or '-'} remaining={remaining} total={total} match={'Y' if match else 'N'}"
                    )

                    if match:
                        if remaining > 0:
                            items.append({"id": foli_gid, "quantity": remaining})
                            encontrados.add(line_item_num)
                        else:
                            sem_remaining_itens.append(line_item_num)

                if items:
                    payloads_por_location.setdefault(loc_gid, []).append(
                        {"fulfillmentOrderId": fo_id, "fulfillmentOrderLineItems": items}
                    )
                else:
                    print(f"[FO] nenhum item apto (match + remaining>0) para FO {fo_id}")

            # === (4) Se nada apto ===
            if not any(payloads_por_location.values()):
                msg = "Nada a enviar"
                partes: list[str] = []
                if sem_remaining_itens:
                    partes.append("IDs encontrados sem remaining: " + ", ".join(sem_remaining_itens))
                if motivos_fo:
                    partes.append("FOs pulados: " + " | ".join(motivos_fo[:3]))
                if partes:
                    msg += " (" + "; ".join(partes) + ")"
                print(f"[✖] {msg}")
                self.signals.erro.emit(self._order_id_planilha, msg)
                return

            # === (5) fulfillmentCreate ===
            mutation = """
            mutation fulfillmentCreate($fulfillment: FulfillmentInput!) {
              fulfillmentCreate(fulfillment: $fulfillment) {
                fulfillment { id status }
                userErrors { field message }
              }
            }
            """

            enviados_total = 0

            with requests.Session() as sess:
                sess.headers.update(headers)

                for loc_gid, fo_payloads in payloads_por_location.items():
                    if not fo_payloads:
                        continue

                    payload = {
                        "query": mutation,
                        "variables": {
                            "fulfillment": {
                                "notifyCustomer": False,
                                "lineItemsByFulfillmentOrder": fo_payloads,
                            }
                        },
                    }
                    print(
                        f"[→] Enviando fulfillmentCreate: location={loc_gid.split('/')[-1]} FO_count={len(fo_payloads)}"
                    )
                    r2 = sess.post(GRAPHQL_URL, json=payload, timeout=10, verify=False)
                    r2.raise_for_status()
                    resp = cast(dict[str, Any], r2.json())
                    user_errors = ((resp.get("data") or {}).get("fulfillmentCreate") or {}).get("userErrors") or []
                    if user_errors:
                        errs = "; ".join(f"{e.get('message')}" for e in user_errors)
                        print(f"[⚠] userErrors (loc={loc_gid.split('/')[-1]}): {errs}")
                        self.signals.erro.emit(self._order_id_planilha, f"[loc {loc_gid.split('/')[-1]}] {errs}")
                        continue

                    enviados_grupo = sum(
                        int(item["quantity"]) for fo in fo_payloads for item in fo["fulfillmentOrderLineItems"]
                    )
                    enviados_total += enviados_grupo
                    print(f"[✅] fulfillmentCreate OK (loc={loc_gid.split('/')[-1]}): enviados={enviados_grupo}")

            if enviados_total == 0:
                raise RuntimeError("Nenhum fulfillment criado (todas as locations retornaram userErrors)")

            print(f"[✅] Total enviado no pedido: {enviados_total} (order_gID={order_gid_resolvido})")
            self.signals.concluido.emit(self._order_id_planilha, enviados_total)

        except Exception as e:
            err = str(e)
            print(f"[✖] Exceção fulfillment order(planilha)={self._order_id_planilha}: {err}")
            self.signals.erro.emit(self._order_id_planilha, err)


def normalizar_texto(texto: Any) -> str:
    s = str(texto or "")
    s = unicodedata.normalize("NFD", s)
    s = s.encode("ascii", "ignore").decode("utf-8")
    return s.lower()


def registrar_log_norm_enderecos(pedido_id: str, dados: Mapping[str, Any]) -> None:
    """
    Registra no logger os dados de endereço de um pedido:
      - campos de entrada (raw)
      - campos normalizados (resultado final)
    """
    try:
        logger.info(
            "endereco_normalizado",
            extra={
                "pedido_id": pedido_id,
                "entrada": {
                    "raw_address1": dados.get("raw_address1"),
                    "raw_address2": dados.get("raw_address2"),
                    "endereco_base": dados.get("endereco_base"),
                    "numero_calc": dados.get("numero"),
                    "complemento_calc": dados.get("complemento"),
                    "precisa_contato": dados.get("precisa_contato"),
                    "logradouro_oficial": dados.get("logradouro_oficial"),
                    "bairro_oficial": dados.get("bairro_oficial"),
                },
                "resultado": {
                    "endereco": dados.get("Endereço") or dados.get("endereco"),
                    "numero": dados.get("Número") or dados.get("numero"),
                    "complemento": dados.get("Complemento") or dados.get("complemento"),
                },
            },
        )
    except Exception as e:
        logger.warning("falha_ao_registrar_log_norm_enderecos", extra={"pedido_id": pedido_id, "erro": str(e)})


class EnderecoResultado(TypedDict, total=False):
    endereco_base: str
    numero: str
    complemento: str
    precisa_contato: str  # "SIM" | "NÃO"
    logradouro_oficial: str
    bairro_oficial: str
    raw_address1: str
    raw_address2: str


class NormalizarEndereco(QRunnable):
    def __init__(
        self,
        order_id: str,
        endereco_raw: str | None,
        complemento_raw: str | None,
        callback: Callable[[str, EnderecoResultado], None],
        sinal_finalizacao: _SinalFinalizacao | None,
        estado: MutableMapping[str, Any],
    ) -> None:
        super().__init__()
        self.order_id: str = normalizar_order_id(order_id)
        self.endereco_raw: str = (endereco_raw or "").strip()
        self.complemento_raw: str = (complemento_raw or "").strip()
        self.callback: Callable[[str, EnderecoResultado], None] = callback
        self.sinal_finalizacao: _SinalFinalizacao | None = sinal_finalizacao
        self.estado: MutableMapping[str, Any] = estado

    @pyqtSlot()
    def run(self) -> None:
        pedido_id = self.order_id  # já normalizado
        try:
            logger.info("addr_norm_thread_started", extra={"order_id": pedido_id})

            # cancelador
            cancelador = cast(threading.Event | None, self.estado.get("cancelador_global"))

            if cast(bool, self.estado.get("finalizou_endereco", False)):
                logger.debug("addr_norm_skipped_already_finished", extra={"order_id": pedido_id})
                return

            if cancelador is not None and cancelador.is_set():
                logger.info("addr_norm_cancelled_early", extra={"order_id": pedido_id})
                return

            # CEP (opcional, com cache)
            cep = str(self.estado.get("cep_por_pedido", {}).get(pedido_id, "")).replace("-", "").strip()
            logradouro_cep = ""
            bairro_cep = ""

            if not cep:
                logger.warning("addr_norm_missing_cep", extra={"order_id": pedido_id})
            else:
                cep_info_cache = cast(dict[str, Any], self.estado.get("cep_info_por_pedido", {})).get(pedido_id)
                if isinstance(cep_info_cache, dict) and cep_info_cache:
                    logradouro_cep = str(cep_info_cache.get("street", "") or "")
                    bairro_cep = str(cep_info_cache.get("district", "") or "")
                    logger.debug("addr_norm_cep_cache_hit", extra={"order_id": pedido_id})
                else:
                    try:
                        cep_info = buscar_cep_com_timeout(cep)  # Dict[str, Any]
                        logradouro_cep = str(cep_info.get("street", "") or "")
                        bairro_cep = str(cep_info.get("district", "") or "")
                        self.estado.setdefault("cep_info_por_pedido", {})[pedido_id] = cep_info
                        logger.debug("addr_norm_cep_fetched", extra={"order_id": pedido_id})
                    except Exception as e:
                        logger.error("addr_norm_cep_error", extra={"order_id": pedido_id, "err": str(e)})

            if cancelador is not None and cancelador.is_set():
                logger.info("addr_norm_cancelled_mid", extra={"order_id": pedido_id})
                return

            # idealmente ponha este regex no topo do módulo:
            _NUM_RE = re.compile(r"\b(\d{1,5}[A-Za-z]?)\b")

            # Heurística: endereço já parece completo?
            precisa: bool = False  # default; pode ser alterado nos ramos abaixo

            if "," in self.endereco_raw:
                # Regra nova: "endereço, número" => não chama GPT
                partes = [p.strip() for p in self.endereco_raw.split(",", 1)]
                base = partes[0].strip(" ,.-")
                pos_virgula = partes[1] if len(partes) > 1 else ""

                m = _NUM_RE.search(pos_virgula)
                numero = m.group(1) if m else "s/n"

                complemento = (self.complemento_raw or "").strip()
                if not complemento:
                    complemento = "-"

                precisa = numero == "s/n"

                logger.debug(
                    "addr_norm_direct_split",
                    extra={"order_id": pedido_id, "base": base, "numero": numero},
                )
            else:
                # Usa GPT; fallback por regex apenas se der erro na requisição
                try:
                    resposta = cast(
                        Mapping[str, Any],
                        normalizar_enderecos_gpt(
                            address1=self.endereco_raw,
                            address2=self.complemento_raw,
                            logradouro_cep=logradouro_cep,
                            bairro_cep=bairro_cep,
                        ),
                    )
                except Exception:
                    # Se sua normalizar_enderecos_gpt já encapsula try/except, este bloco não roda.
                    # De todo modo, mantemos a proteção aqui:
                    a1 = (self.endereco_raw or "").strip()
                    a2 = (self.complemento_raw or "").strip()
                    base = a1.strip(" ,.-")
                    m = _NUM_RE.search(a1)
                    numero = m.group(1) if m else "s/n"
                    complemento = a2 if a2 else "-"
                    precisa = numero == "s/n"
                else:
                    # resposta GPT OK
                    base = str(resposta.get("base", "") or "").strip()
                    numero = str(resposta.get("numero", "") or "").strip()
                    complemento = str(resposta.get("complemento", "") or "").strip()
                    precisa = bool(resposta.get("precisa_contato", False))

                    # Defaults exigidos
                    if not numero:
                        numero = "s/n"
                        precisa = True
                    if not complemento:
                        complemento = "-"

                    # Evita 'complemento' igual ao número
                    if complemento.strip() == numero.strip():
                        complemento = "-"

                    # Segurança adicional com logradouro do CEP
                    if logradouro_cep:
                        base_normalizada = normalizar_texto(base)
                        logradouro_normalizado = normalizar_texto(logradouro_cep)
                        if logradouro_normalizado not in base_normalizada:
                            base = logradouro_cep.strip()

            resultado: EnderecoResultado = {
                "endereco_base": base,
                "numero": numero,
                "complemento": complemento,
                "precisa_contato": "SIM" if precisa else "NÃO",
                "logradouro_oficial": logradouro_cep,
                "bairro_oficial": bairro_cep,
                "raw_address1": self.endereco_raw,
                "raw_address2": self.complemento_raw,
            }

            registrar_log_norm_enderecos(pedido_id, resultado)
            self.callback(pedido_id, resultado)

        except Exception as e:
            logger.exception("addr_norm_exception", extra={"order_id": pedido_id, "err": str(e)})
            fallback: EnderecoResultado = {
                "endereco_base": self.endereco_raw,
                "numero": "s/n",
                "complemento": self.complemento_raw,
                "precisa_contato": "SIM",
                "logradouro_oficial": "",
                "bairro_oficial": "",
            }
            try:
                self.callback(pedido_id, fallback)
            except Exception as cb_err:
                logger.exception(
                    "addr_norm_callback_fallback_error",
                    extra={"order_id": pedido_id, "err": str(cb_err)},
                )

        finally:
            try:
                pendentes = cast(set[str], self.estado.get("endereco_pendentes", set()))
                if pedido_id in pendentes:
                    pendentes.discard(pedido_id)
                    # mantém de volta no estado para não perder a referência de tipo
                    self.estado["endereco_pendentes"] = pendentes
                    logger.debug("addr_norm_pending_removed", extra={"order_id": pedido_id})
                else:
                    logger.debug("addr_norm_pending_already_gone", extra={"order_id": pedido_id})
            except Exception as e:
                logger.exception("addr_norm_pending_remove_error", extra={"order_id": pedido_id, "err": str(e)})

            # dentro do finally de NormalizarEndereco.run
            if self.sinal_finalizacao is not None:
                try:
                    # resultado: dict com os campos normalizados desse pedido
                    self.sinal_finalizacao.finalizado.emit(pedido_id, resultado)
                    logger.debug("addr_norm_final_signal", extra={"order_id": pedido_id})
                except Exception as e:
                    logger.exception("addr_norm_final_signal_error", extra={"order_id": pedido_id, "err": str(e)})


# Funções auxiliares shopify


busca_cep_lock = threading.Lock()


def buscar_cep_com_timeout(cep: str, timeout: int = 5) -> dict[str, Any]:
    """Consulta um CEP com timeout.

    Retorna um dicionário de endereço ou {} em caso de erro.
    """
    try:
        # sem lock global, sem sleep serializador
        return get_address_from_cep(cep, timeout=timeout)
    except exceptions.CEPNotFound:
        print(f"⚠️ CEP {cep} não encontrado.")
    except Exception as e:
        print(f"❌ Erro ao consultar o CEP {cep}: {e}")
    return {}


# Funções de Fluxo


class VerificadorDeEtapa(QObject):
    def __init__(
        self,
        estado: MutableMapping[str, Any],
        chave: str,
        total_esperado: int,
        get_pendentes: Callable[[], set[Any] | None],
        callback_final: Callable[[], None] | None = None,
        intervalo_ms: int = 300,
        timeout: int = 60,
        max_intervalo_ms: int = 5000,
        log_cada_n_checks: int = 10,
    ) -> None:
        super().__init__()
        self.estado: MutableMapping[str, Any] = estado
        self.chave: str = chave
        self.total_esperado: int = int(total_esperado)
        self.get_pendentes: Callable[[], set[Any] | None] = get_pendentes
        self.callback_final: Callable[[], None] | None = callback_final

        # controle de temporização
        self.intervalo_inicial_ms: int = max(50, int(intervalo_ms))
        self.intervalo_atual_ms: int = self.intervalo_inicial_ms
        self.max_intervalo_ms: int = int(max_intervalo_ms)
        self.timeout: int = int(timeout)

        # book-keeping
        self.contador: int = 0
        self._encerrado: bool = False
        self._ultimo_len: int | None = None
        self._ultimo_tick_com_progresso: float = time.monotonic()
        self._timer: QTimer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.timeout.connect(self._verificar)

        # logging
        self._log_cada_n: int = max(1, int(log_cada_n_checks))
        self._parent_correlation_id: str = get_correlation_id()

    def iniciar(self) -> None:
        set_correlation_id(self._parent_correlation_id)
        logger.info(
            "monitor_start",
            extra={
                "chave": self.chave,
                "intervalo_ms": self.intervalo_inicial_ms,
                "timeout_s": self.timeout,
                "total_esperado": self.total_esperado,
            },
        )
        self.estado.setdefault("etapas_finalizadas", {})
        self.estado[f"finalizou_{self.chave}"] = False
        self.estado["etapas_finalizadas"][self.chave] = False
        QTimer.singleShot(0, self._verificar)

    def _reagendar(self) -> None:
        if self._encerrado:
            return
        self._timer.start(self.intervalo_atual_ms)

    def _verificar(self) -> None:
        if self._encerrado:
            return

        self.contador += 1
        pendentes_raw = self.get_pendentes() or set()
        pendentes: set[Any] = cast(set[Any], pendentes_raw)
        lp: int = len(pendentes)

        # pode não existir em testes ou cenários específicos; mantém default compatível
        cancel_event = self.estado.get("cancelador_global", threading.Event())
        cancelado: bool = bool(cancel_event.is_set())

        # timeout real em segundos (não em número de checks)
        if (time.monotonic() - self._ultimo_tick_com_progresso) > self.timeout and cancelado:
            logger.warning("monitor_timeout_cancelled", extra={"chave": self.chave})
            self._encerrar()
            return

        # log só quando muda ou a cada N checks
        if self._ultimo_len is None or lp != self._ultimo_len or (self.contador % self._log_cada_n == 0):
            logger.info(
                "monitor_tick",
                extra={
                    "chave": self.chave,
                    "count": self.contador,
                    "pendentes": lp,
                    "cancelado": cancelado,
                },
            )

        # finalizou?
        if lp == 0:
            logger.info("monitor_done", extra={"chave": self.chave})
            self.estado[f"finalizou_{self.chave}"] = True
            self.estado["etapas_finalizadas"][self.chave] = True
            self._encerrar()

            if callable(self.callback_final) and not cancelado:
                try:
                    logger.info("monitor_callback_final", extra={"chave": self.chave})
                    self.callback_final()
                except Exception as e:
                    logger.exception("monitor_callback_final_error", extra={"chave": self.chave, "err": str(e)})
            return

        # se já foi marcada como finalizada por outro caminho, encerra
        if bool(self.estado.get(f"finalizou_{self.chave}", False)):
            self._encerrar()
            return

        # backoff: só aumenta se não houve progresso
        if self._ultimo_len is None or lp < self._ultimo_len:
            # houve progresso → reset backoff
            self.intervalo_atual_ms = self.intervalo_inicial_ms
            self._ultimo_tick_com_progresso = time.monotonic()
        else:
            # sem progresso → dobra, limitado ao máximo
            self.intervalo_atual_ms = min(self.max_intervalo_ms, int(self.intervalo_atual_ms * 2))

        self._ultimo_len = lp
        self._reagendar()

    def _encerrar(self) -> None:
        if self._encerrado:
            return
        self._encerrado = True
        with suppress(Exception):
            self._timer.stop()
        logger.info("monitor_closed", extra={"chave": self.chave})


class SinaisObterCpf(QObject):
    resultado = pyqtSignal(str, str)  # pedido_id, cpf
    erro = pyqtSignal(str, str)  # pedido_id, erro


class ObterCpfShopifyRunnable(QRunnable):
    def __init__(
        self,
        order_id: str,
        estado: MutableMapping[str, Any],
        sinal_finalizacao: _SinalFinalizacao | None = None,
    ) -> None:
        super().__init__()
        self.order_id: str = normalizar_order_id(order_id)
        self.estado: MutableMapping[str, Any] = estado
        self.signals: SinaisObterCpf = SinaisObterCpf()
        self.sinal_finalizacao: _SinalFinalizacao | None = sinal_finalizacao
        self._parent_correlation_id: str = get_correlation_id()

    @pyqtSlot()
    def run(self) -> None:
        set_correlation_id(self._parent_correlation_id)
        logger.info("cpf_lookup_start", extra={"order_id": self.order_id})
        cpf: str = ""
        try:
            if self.estado["cancelador_global"].is_set():
                logger.warning("cpf_lookup_cancelled_early", extra={"order_id": self.order_id})
                return

            order_gid = f"gid://shopify/Order/{self.order_id}"
            query: dict[str, str] = {
                "query": f"""
                {{
                    order(id: \"{order_gid}\") {{
                        localizationExtensions(first: 5) {{
                            edges {{
                                node {{
                                    purpose
                                    title
                                    value
                                }}
                            }}
                        }}
                    }}
                }}
                """
            }

            headers: dict[str, str] = {
                "Content-Type": "application/json",
                "X-Shopify-Access-Token": settings.SHOPIFY_TOKEN,
            }

            # ---- Tipagem explícita do controle/lock e do timestamp ----
            ctrl: MutableMapping[str, Any] = cast(MutableMapping[str, Any], controle_threading_shopify)
            lock_cm: AbstractContextManager[Any] = cast(AbstractContextManager[Any], ctrl["lock"])
            with lock_cm:
                ultimo: float = float(cast(Any, ctrl.get("ultimo_acesso", 0.0)))
                agora: float = time.time()
                delta: float = agora - ultimo
                if delta < min_intervalo_graphql:
                    time.sleep(min_intervalo_graphql - delta)
                ctrl["ultimo_acesso"] = agora

            if self.estado["cancelador_global"].is_set():
                logger.warning("cpf_lookup_cancelled_mid", extra={"order_id": self.order_id})
                return

            with requests.Session() as sess:
                sess.headers.update(headers)
                resp = sess.post(GRAPHQL_URL, json=query, timeout=6, verify=False)

            if self.estado["cancelador_global"].is_set():
                logger.warning("cpf_lookup_cancelled_mid", extra={"order_id": self.order_id})
                return

            if resp.status_code == 200:
                data: dict[str, Any] = resp.json()
                edges: list[dict[str, Any]] = (
                    data.get("data", {}).get("order", {}).get("localizationExtensions", {}).get("edges", [])
                )
                for edge in edges:
                    node: dict[str, Any] = edge.get("node", {})
                    if node.get("purpose") == "TAX" and "cpf" in str(node.get("title", "")).lower():
                        cpf = re.sub(r"\D", "", str(node.get("value", "")))[:11]
                        break
            else:
                logger.warning(
                    "cpf_lookup_http_error",
                    extra={"order_id": self.order_id, "status": resp.status_code},
                )

            self.signals.resultado.emit(self.order_id, cpf)

        except Exception as e:
            logger.exception("cpf_lookup_exception", extra={"order_id": self.order_id, "err": str(e)})
            self.signals.resultado.emit(self.order_id, cpf)

        finally:
            try:
                self.estado["cpf_pendentes"].discard(self.order_id)
                logger.debug("cpf_lookup_popped_from_pending", extra={"order_id": self.order_id})
            except Exception as e:
                logger.exception(
                    "cpf_lookup_pending_discard_error",
                    extra={"order_id": self.order_id, "err": str(e)},
                )

            if self.sinal_finalizacao:
                try:
                    self.sinal_finalizacao.finalizado.emit(self.order_id, {})
                    logger.debug("cpf_lookup_final_signal", extra={"order_id": self.order_id})
                except Exception as e:
                    logger.exception("cpf_lookup_final_signal_error", extra={"order_id": self.order_id, "err": str(e)})


def iniciar_busca_cpfs(
    estado: MutableMapping[str, Any],
    gerenciador: GerenciadorProgresso | None,
    depois: Callable[[], None] | None = None,
) -> None:
    df_any = estado.get("df_temp")

    # mypy: só usa quando não for None
    if gerenciador is not None:
        gerenciador.atualizar("🔍 Coletando CPF dos pedidos...", 0, 0)

    if not isinstance(df_any, pd.DataFrame) or df_any.empty:
        logger.warning("[⚠️] Não há dados de pedidos coletados.")
        return
    df_temp: pd.DataFrame = df_any

    estado.setdefault("etapas_finalizadas", {})
    cancelador = estado.get("cancelador_global")
    if cancelador is not None and cancelador.is_set():
        logger.info("[🛑] Cancelamento detectado antes de iniciar busca de CPFs.")
        if gerenciador is not None:
            gerenciador.fechar()
        return

    # 🔍 Quais pedidos ainda sem CPF
    serie_cpf = df_temp["CPF/CNPJ Comprador"].fillna("").astype(str)
    faltando_cpf = serie_cpf.str.strip() == ""
    pedidos_faltantes = df_temp.loc[faltando_cpf, "transaction_id"].dropna().astype(str).str.strip().tolist()

    if not pedidos_faltantes:
        logger.info("[✅] Todos os CPFs já foram coletados.")
        if callable(depois) and not (cancelador is not None and cancelador.is_set()):
            depois()
        return

    # ✅ Normaliza e remove duplicados UMA vez só
    pendentes_set: set[str] = {normalizar_order_id(pid) for pid in pedidos_faltantes}
    estado["cpf_pendentes"] = pendentes_set
    estado["cpf_total_esperado"] = len(pendentes_set)

    # 🔁 Inicia threads de coleta (evita duplicados)
    pool = QThreadPool.globalInstance()

    def continuar_para_bairros() -> None:
        if cancelador is not None and cancelador.is_set():
            if gerenciador is not None:
                gerenciador.fechar()
            return
        # iniciar_busca_bairros aceita gerenciador opcional
        iniciar_busca_bairros(estado, gerenciador, depois=depois)

    # Adapter para o sinal resultado -> marcar_cpf_coletado sem keywords
    def _on_cpf_ok(pedido_id: str, cpf: str) -> None:
        estado_dict: dict[Any, Any] = cast(dict[Any, Any], estado)
        if gerenciador is None:
            # assinatura sem gerenciador
            marcar_cpf_coletado(pedido_id, cpf, estado_dict)
        else:
            # assinatura com gerenciador
            marcar_cpf_coletado(pedido_id, cpf, estado_dict, gerenciador)

    for pedido_id in pendentes_set:
        if cancelador is not None and cancelador.is_set():
            break
        runnable = ObterCpfShopifyRunnable(pedido_id, estado)
        # conecta sem passar keywords não suportadas
        runnable.signals.resultado.connect(_on_cpf_ok)
        pool.start(runnable)

    # ✅ Verificador com intervalo inicial maior (use com backoff na classe)
    estado["verificador_cpf"] = VerificadorDeEtapa(
        estado=estado,
        chave="cpf",
        total_esperado=estado["cpf_total_esperado"],
        get_pendentes=lambda: estado.get("cpf_pendentes", set()),
        callback_final=continuar_para_bairros,  # encadeia próximo passo aqui
        intervalo_ms=1000,
        # max_intervalo_ms=8000,
        # log_cada_n_checks=20,
    )
    estado["verificador_cpf"].iniciar()


class BuscarBairroRunnable(QRunnable):
    def __init__(
        self,
        order_id: str,
        cep: str,
        df: pd.DataFrame,
        callback: Callable[[str, str], None],
        estado: MutableMapping[str, Any],
        sinal_finalizacao: _SinalFinalizacao | None = None,
    ) -> None:
        super().__init__()
        self.order_id: str = normalizar_order_id(order_id)
        self.cep: str = cep
        self.df: pd.DataFrame = df
        self.callback: Callable[[str, str], None] = callback
        self.estado: MutableMapping[str, Any] = estado
        self.sinal_finalizacao: _SinalFinalizacao | None = sinal_finalizacao
        self._parent_correlation_id: str = get_correlation_id()

    @pyqtSlot()
    def run(self) -> None:
        set_correlation_id(self._parent_correlation_id)
        logger.info("bairro_lookup_start", extra={"order_id": self.order_id})
        try:
            cancelador = cast(threading.Event | None, self.estado.get("cancelador_global"))
            if cancelador is not None and cancelador.is_set():
                logger.warning("bairro_lookup_cancelled_early", extra={"order_id": self.order_id})
                return

            cep_limpo = re.sub(r"\D", "", self.cep)
            if len(cep_limpo) != 8:
                raise ValueError("CEP inválido")

            endereco: dict[str, Any] = buscar_cep_com_timeout(cep_limpo)

            if cancelador is not None and cancelador.is_set():
                logger.warning("bairro_lookup_cancelled_after_fetch", extra={"order_id": self.order_id})
                return

            bairro = cast(str, (endereco.get("district") or "")).strip()
            cidade = cast(str, (endereco.get("city") or "")).strip()
            uf = cast(str, (endereco.get("uf") or "")).strip()

            # Seleciona as linhas do pedido
            idx = self.df["transaction_id"].astype(str).str.strip() == self.order_id

            if bairro:
                self.df.loc[idx, "Bairro Comprador"] = bairro
                self.df.loc[idx, "Bairro Entrega"] = bairro
            if cidade:
                self.df.loc[idx, "Cidade Comprador"] = cidade
                self.df.loc[idx, "Cidade Entrega"] = cidade
            if uf:
                self.df.loc[idx, "UF Comprador"] = uf
                self.df.loc[idx, "UF Entrega"] = uf

            if cancelador is not None and cancelador.is_set():
                logger.warning("bairro_lookup_cancelled_before_callback", extra={"order_id": self.order_id})
                return

            # callback(pid, bairro)
            self.callback(self.order_id, bairro or "")

        except Exception:
            cancelador = cast(threading.Event | None, self.estado.get("cancelador_global"))
            if cancelador is not None and cancelador.is_set():
                logger.warning("bairro_lookup_cancelled_during_exception", extra={"order_id": self.order_id})
                return

            logger.exception("bairro_lookup_error", extra={"order_id": self.order_id})
            self.callback(self.order_id, "")

        finally:
            try:
                pendentes = cast(set[str], self.estado.get("bairro_pendentes", set()))
                pendentes.discard(self.order_id)
                self.estado["bairro_pendentes"] = pendentes  # mantém no estado
                logger.debug("bairro_lookup_popped_from_pending", extra={"order_id": self.order_id})
            except Exception as e:
                logger.exception(
                    "bairro_lookup_pending_discard_error",
                    extra={"order_id": self.order_id, "err": str(e)},
                )

            if self.sinal_finalizacao is not None:
                try:
                    self.sinal_finalizacao.finalizado.emit(self.order_id, {})
                    logger.debug("bairro_lookup_final_signal", extra={"order_id": self.order_id})
                except Exception as e:
                    logger.exception(
                        "bairro_lookup_final_signal_error", extra={"order_id": self.order_id, "err": str(e)}
                    )


def iniciar_busca_bairros(
    estado: MutableMapping[str, Any],
    gerenciador: GerenciadorProgresso | None,
    depois: Callable[[], None] | None = None,
) -> None:
    df_any = estado.get("df_temp")
    if not isinstance(df_any, pd.DataFrame) or df_any.empty:
        logger.warning("[⚠️] Nenhuma planilha temporária encontrada.")
        return
    df: pd.DataFrame = df_any

    # mypy: só chama se não for None
    if gerenciador is not None:
        gerenciador.atualizar("📍 Buscando bairros dos pedidos...", 0, 0)

    estado.setdefault("etapas_finalizadas", {})
    if estado["cancelador_global"].is_set():
        logger.info("[🛑] Cancelamento detectado antes da busca de bairros.")
        if gerenciador is not None:
            gerenciador.fechar()
        return

    # Garante coluna e evita .str em NaN
    if "Bairro Comprador" not in df.columns:
        df["Bairro Comprador"] = ""

    serie_bairro = df["Bairro Comprador"].fillna("").astype(str)
    faltando = serie_bairro.str.strip() == ""

    # Só precisamos de transaction_id e CEP; remove NaN e duplicados de id
    pendentes_df = (
        df.loc[faltando, ["transaction_id", "CEP Comprador"]]
        .dropna(subset=["transaction_id"])  # mantém linhas com CEP NaN se quiser outra estratégia
        .drop_duplicates(subset="transaction_id")
    )

    total = len(pendentes_df)
    if total == 0:
        logger.info("[✅] Nenhum bairro para buscar.")
        if callable(depois):
            depois()
        return

    logger.info(f"[📍] Buscando bairro para {total} pedidos.")

    # Conjunto de pendentes normalizado
    pendentes_set: set[str] = {normalizar_order_id(pid) for pid in pendentes_df["transaction_id"].astype(str)}
    estado["bairro_total_esperado"] = len(pendentes_set)
    estado["bairro_pendentes"] = set(pendentes_set)  # cópia defensiva

    pool = QThreadPool.globalInstance()

    # Adapter sem keywords e com casts para mypy
    def _on_bairro_ok(pid: str, bairro: str) -> None:
        # marcar_bairro_coletado espera estado: dict[Any, Any]
        estado_dict: dict[Any, Any] = cast(dict[Any, Any], estado)
        # Se o slot exige GerenciadorProgresso (não-opcional), só chamamos quando houver
        if gerenciador is None:
            # Sem gerenciador, apenas atualiza estruturas e segue (ou loga)
            marcar_bairro_coletado(pid, bairro, estado_dict)  # tipo: ignore[call-arg]
        else:
            marcar_bairro_coletado(pid, bairro, estado_dict, gerenciador)  # tipo: ignore[call-arg]

        # Se quiser ainda executar 'depois' quando cada item finalizar, pode guardar no estado
        if callable(depois):
            # opcional: deixe para o verificador final chamar apenas uma vez
            pass

    # Dispara runnables
    for _, linha in pendentes_df.iterrows():
        if estado["cancelador_global"].is_set():
            logger.info("[🛑] Cancelamento detectado durante o disparo de tarefas de bairro.")
            break

        pedido_id = normalizar_order_id(str(linha["transaction_id"]))
        cep = "" if pd.isna(linha["CEP Comprador"]) else str(linha["CEP Comprador"]).strip()

        runnable = BuscarBairroRunnable(
            pedido_id,
            cep,
            df,
            _on_bairro_ok,  # ✅ sem keywords e sem 'depois'
            estado,
        )
        pool.start(runnable)

    # Se o próximo passo exige GerenciadorProgresso não-opcional, garanta aqui
    if gerenciador is None:
        logger.warning("[i] 'gerenciador' ausente; não é possível iniciar normalização de endereços.")
        return

    # Verificador persistente
    estado["verificador_bairro"] = VerificadorDeEtapa(
        estado=estado,
        chave="bairro",
        total_esperado=estado["bairro_total_esperado"],
        get_pendentes=lambda: estado.get("bairro_pendentes", set()),
        callback_final=lambda: iniciar_normalizacao_enderecos(  # ✅ tipo esperado
            estado, gerenciador  # mypy: GerenciadorProgresso garantido
        ),
        intervalo_ms=800,
    )
    estado["verificador_bairro"].iniciar()


class FinalizarNormalizacaoSignal(QObject):
    if TYPE_CHECKING:
        finalizado: pyqtBoundSignal  # o mypy enxerga bound
    else:
        finalizado = pyqtSignal(str, dict)  # runtime


def iniciar_normalizacao_enderecos(
    estado: MutableMapping[str, Any],
    gerenciador: GerenciadorProgresso,
    depois: Callable[[], None] | None = None,
) -> None:
    # gate idempotente
    if estado.get("_once_iniciar_normalizacao_enderecos"):
        logger.info("[🧪] Normalização de endereços já iniciada - ignorando repetição.")
        return
    estado["_once_iniciar_normalizacao_enderecos"] = True

    jp = estado.get("janela_principal")
    visivel = getattr(jp, "isVisible", lambda: None)()
    logger.info(f"[🧪] Visibilidade da janela principal: {visivel}")
    logger.info(f"[🧪] iniciar_normalizacao_enderecos recebeu gerenciador: {id(gerenciador)}")

    if not estado.get("gerenciador_progresso"):
        estado["gerenciador_progresso"] = gerenciador
    else:
        gerenciador = estado["gerenciador_progresso"]

    estado.setdefault("etapas_finalizadas", {})
    estado.setdefault("enderecos_normalizados", {})

    df_any = estado.get("df_temp")
    gerenciador.atualizar("📦 Normalizando endereços...", 0, 0)
    if not isinstance(df_any, pd.DataFrame) or df_any.empty:
        logger.warning("[⚠️] Nenhuma planilha temporária encontrada.")
        return
    df: pd.DataFrame = df_any

    if estado["cancelador_global"].is_set():
        if gerenciador:
            gerenciador.fechar()
        return

    # blindagem de colunas
    for col in ("Endereço Entrega", "Complemento Entrega"):
        if col not in df.columns:
            df[col] = ""

    pendentes_df = (
        df.drop_duplicates(subset="transaction_id")
        .loc[:, ["transaction_id", "Endereço Entrega", "Complemento Entrega"]]
        .dropna(subset=["transaction_id"])
    )

    total = len(pendentes_df)
    if total == 0:
        logger.info("[✅] Nenhum endereço para normalizar.")
        estado["etapas_finalizadas"]["endereco"] = True
        estado["finalizou_endereco"] = True
        try:
            finalizar_coleta_shopify(estado, gerenciador)
        except Exception:
            logger.exception("[❌] Erro ao finalizar no caminho zero-pendentes")
        if callable(depois):
            try:
                depois()
            except Exception:
                logger.exception("[❌] Erro no 'depois()' após zero-pendentes")
        return

    logger.info(f"[📦] Normalizando {total} endereços.")

    pendentes_set = {normalizar_order_id(str(pid)) for pid in pendentes_df["transaction_id"].astype(str)}
    estado["endereco_total_esperado"] = len(pendentes_set)
    estado["endereco_pendentes"] = set(pendentes_set)

    logger.info(f"[🧪] Iniciando {len(pendentes_set)} NormalizarEndereco(s)...")

    pool = QThreadPool.globalInstance()
    for _, linha in pendentes_df.iterrows():
        if estado["cancelador_global"].is_set():
            logger.info("[🛑] Cancelamento detectado durante o disparo de normalizações de endereço.")
            break

        pedido_id = normalizar_order_id(str(linha["transaction_id"]))
        endereco_raw = "" if pd.isna(linha["Endereço Entrega"]) else str(linha["Endereço Entrega"])
        complemento_raw = "" if pd.isna(linha.get("Complemento Entrega")) else str(linha.get("Complemento Entrega"))

        runnable = NormalizarEndereco(
            pedido_id,
            endereco_raw,
            complemento_raw,
            lambda pid, dados: ao_finalizar_endereco(str(pid), dict(dados), estado, gerenciador, depois),
            sinal_finalizacao=cast(_SinalFinalizacao, FinalizarNormalizacaoSignal()),
            estado=estado,
        )

        _pool = pool or QThreadPool.globalInstance()
        _pool.start(runnable)

    estado["verificador_endereco"] = VerificadorDeEtapa(
        estado=estado,
        chave="endereco",
        total_esperado=estado["endereco_total_esperado"],
        get_pendentes=lambda: estado.get("endereco_pendentes", set()),
        callback_final=lambda: finalizar_coleta_shopify(estado, gerenciador),
        intervalo_ms=800,
    )
    estado["verificador_endereco"].iniciar()


def ao_finalizar_endereco(
    pedido_id: str,
    endereco_dict: Mapping[str, Any],
    estado: MutableMapping[str, Any],
    gerenciador: GerenciadorProgresso | None,
    depois_callback: Callable[[], None] | None,
) -> None:
    # Proteção contra chamadas após finalização
    if estado.get("finalizou_endereco"):
        logger.debug(f"[🛑] Ignorando ao_finalizar_endereco para {pedido_id} - etapa já foi finalizada.")
        return

    pedido_id = normalizar_order_id(pedido_id)
    logger.info(f"[🧪] ao_finalizar_endereco chamado para {pedido_id} - gerenciador={id(gerenciador)}")

    estado.setdefault("enderecos_normalizados", {})
    estado.setdefault("endereco_pendentes", set())

    if estado.get("cancelador_global", threading.Event()).is_set():
        logger.warning(f"[🛑] Cancelado antes de processar endereço do pedido {pedido_id}.")
        return

    # Evita reprocessar pedidos já removidos
    if pedido_id not in estado["endereco_pendentes"]:
        logger.debug(f"[🟡] Pedido {pedido_id} já finalizado ou não está nos pendentes. Ignorando.")
        return

    # Registra o endereço normalizado e remove da lista de pendentes
    estado["enderecos_normalizados"][pedido_id] = dict(endereco_dict)  # cópia defensiva
    estado["endereco_pendentes"].remove(pedido_id)

    total: int = int(estado.get("endereco_total_esperado", 0))
    atual: int = total - len(estado["endereco_pendentes"])
    logger.info(f"[📦] Endereços normalizados: {atual}/{total}")

    # Se todos foram normalizados, finaliza a etapa
    if not estado["endereco_pendentes"]:
        if not estado.get("finalizou_endereco", False):
            logger.info("[✅] Todos os endereços finalizados.")
            estado["etapas_finalizadas"]["endereco"] = True
            estado["finalizou_endereco"] = True

            consolidar_planilha_shopify(estado, gerenciador)

            if callable(depois_callback):
                logger.info("[📞] Chamando `depois()` após normalização.")
                try:
                    depois_callback()
                except Exception as e:
                    logger.exception(f"[❌] Erro ao executar `depois()` após normalização: {e}")
        else:
            logger.debug("[🟡] ao_finalizar_endereco ignorado - etapa já finalizada.")


def validar_endereco(address1: str) -> bool:
    if not address1 or "," not in address1:
        return False

    partes = [p.strip() for p in address1.split(",")]
    if len(partes) < 2:
        return False

    # Verifica se a segunda parte tem ao menos um número
    return any(char.isdigit() for char in partes[1])


def acionar_coleta_pedidos_shopify(estado: MutableMapping[str, Any]) -> None:
    gerenciador: GerenciadorProgresso = GerenciadorProgresso(
        titulo="🔎 Buscando pedidos na Shopify",
        com_percentual=False,
        estado_global=estado,
        logger_obj=logger,
    )
    estado["gerenciador_progresso"] = gerenciador
    gerenciador.atualizar("🔄 Buscando pedidos pagos na Shopify...", 0, 0)

    data_inicio: str = estado["entrada_data_inicio"].date().toString("dd/MM/yyyy")
    fulfillment_status: str = estado["combo_status"].currentText()
    produto_alvo: str | None = estado["combo_produto"].currentText() if estado["check_produto"].isChecked() else None
    skus_info: Mapping[str, Any] = estado["skus_info"]

    iniciar_coleta_pedidos_shopify(
        estado=estado,
        gerenciador=gerenciador,
        data_inicio_str=data_inicio,
        produto_alvo=produto_alvo,
        skus_info=skus_info,
        fulfillment_status=fulfillment_status,
        depois=lambda: iniciar_normalizacao_enderecos(estado, gerenciador),
    )


class SinaisBuscarPedidos(QObject):
    resultado = pyqtSignal(list)  # Lista de pedidos
    erro = pyqtSignal(str)


Pedido = dict[str, Any]
ThrottleStatus = dict[str, float]


class ColetarPedidosShopify(QRunnable):
    def __init__(
        self,
        data_inicio_str: str,
        estado: MutableMapping[str, Any],
        fulfillment_status: str = "any",
    ) -> None:
        super().__init__()
        self.data_inicio_str: str = data_inicio_str
        self.fulfillment_status: str = fulfillment_status
        self.sinais: SinaisBuscarPedidos = SinaisBuscarPedidos()
        self.estado: MutableMapping[str, Any] = estado
        self._parent_correlation_id: str = get_correlation_id()

        # ✅ salva o modo selecionado para uso no montar_planilha_shopify
        self.estado["fulfillment_status_selecionado"] = (fulfillment_status or "any").strip().lower()

        # memória de custos/limites para rate-limit pró-ativo
        self._ultimo_requested_cost: float = 150.0  # palpite inicial
        self._ultimo_throttle_status: ThrottleStatus | None = None

        # garante estruturas básicas no estado (evita KeyError)
        self.estado.setdefault("dados_temp", {})
        self.estado["dados_temp"].setdefault("cpfs", {})
        self.estado["dados_temp"].setdefault("bairros", {})
        self.estado["dados_temp"].setdefault("enderecos", {})
        self.estado["dados_temp"].setdefault("status_fulfillment", {})
        self.estado["dados_temp"].setdefault("fretes", {})
        self.estado["dados_temp"].setdefault("descontos", {})
        self.estado["dados_temp"].setdefault("itens_por_pedido", {})

    # ---- helpers de log/limite ----
    def _log_erro(
        self,
        titulo: str,
        detalhe: str | None = None,
        exc: Exception | None = None,
        resp: requests.Response | None = None,
        extra_ctx: dict[str, Any] | None = None,
    ) -> None:
        print("\n" + "═" * 80)
        print(f"[❌] {titulo}")
        if detalhe:
            print(f"[📝] Detalhe: {detalhe}")

        ctx: dict[str, Any] = {
            "cursor": (extra_ctx or {}).get("cursor"),
            "fulfillment_status": (self.fulfillment_status or "").strip().lower(),
            "query": (extra_ctx or {}).get("query"),
        }
        try:
            print(f"[INFO] Contexto: {json.dumps(ctx, ensure_ascii=False)}")
        except Exception:
            print(f"[INFO] Contexto: {ctx}")

        if resp is not None:
            print(f"[🌐] HTTP {resp.status_code}")
            try:
                body_text = resp.text
                if len(body_text) > 2000:
                    body_text = body_text[:2000] + "…(truncado)"
                print(f"[📦] Body: {body_text}")
            except Exception as e_body:
                print(f"[⚠️] Falha ao ler body: {e_body}")

            with suppress(Exception):
                print(f"[📬] Headers: {dict(resp.headers)}")

            try:
                payload = resp.json()
                if isinstance(payload, dict) and "errors" in payload:
                    print("[🧩] GraphQL errors:")
                    for i, err in enumerate(payload.get("errors", []), start=1):
                        if not isinstance(err, dict):
                            continue
                        print(f"   {i:02d}. {err.get('message')}")
                        if "extensions" in err:
                            print(f"       extensions: {err.get('extensions')}")
                        if "locations" in err:
                            print(f"       locations: {err.get('locations')}")
                        if "path" in err:
                            print(f"       path: {err.get('path')}")
            except Exception:
                pass

        if exc is not None:
            print("[🐛] Traceback:")
            traceback.print_exc()

        print("═" * 80 + "\n")

        msg_ui = titulo
        if detalhe:
            msg_ui += f" - {detalhe}"
        self.sinais.erro.emit(f"❌ {msg_ui}")

    def _calc_wait_seconds(self, throttle_status: Mapping[str, Any] | None, needed: float) -> float:
        if not throttle_status:
            return 0.0
        try:
            available = float(throttle_status.get("currentlyAvailable", 0) or 0)
            restore = float(throttle_status.get("restoreRate", 0) or 0)
        except Exception:
            return 0.0
        if available >= needed or restore <= 0:
            return 0.0
        deficit = needed - available
        return max(0.0, deficit / restore)

    def _esperar_creditos_se_preciso(self) -> None:
        needed = max(50.0, float(self._ultimo_requested_cost or 100.0))
        wait_s = self._calc_wait_seconds(self._ultimo_throttle_status, needed)
        if wait_s > 0:
            print(f"⏳ Aguardando {wait_s:.2f}s para recuperar créditos (precisa ~{needed:.0f}).")
            time.sleep(wait_s)

    def _atualizar_custos(self, payload: Mapping[str, Any]) -> None:
        extensions = cast(dict[str, Any], (payload or {}).get("extensions", {}))
        cost = cast(dict[str, Any], extensions.get("cost", {}) or {})
        req_cost = cost.get("requestedQueryCost")
        act_cost = cost.get("actualQueryCost")
        if req_cost is not None:
            self._ultimo_requested_cost = float(req_cost)
        elif act_cost is not None:
            self._ultimo_requested_cost = float(act_cost)

        throttle = cast(dict[str, Any], cost.get("throttleStatus") or {})
        if throttle:
            self._ultimo_throttle_status = {
                "maximumAvailable": float(throttle.get("maximumAvailable", 0) or 0.0),
                "currentlyAvailable": float(throttle.get("currentlyAvailable", 0) or 0.0),
                "restoreRate": float(throttle.get("restoreRate", 0) or 0.0),
            }
        else:
            self._ultimo_throttle_status = None

    # ---- helpers de combo/sku ----
    def _buscar_info_por_sku(self, skus_info: dict[str, Any], sku: str) -> dict[str, Any] | None:
        sku_norm = (sku or "").strip().upper()
        if not sku_norm:
            return None
        for info in skus_info.values():
            try:
                v = str(info.get("sku", "")).strip().upper()
            except Exception:
                v = ""
            if v and v == sku_norm:
                return cast(dict[str, Any], info)
        return None

    def _expandir_line_items_por_regras(
        self,
        pedido: Pedido,
        skus_info: dict[str, Any],
    ) -> list[dict[str, Any]]:
        """Retorna uma lista de dicts "itens_expandidos" a partir de pedido.lineItems:

        - Se não for combo: [{'sku', 'quantity', 'line_item_id'}]
        - Se combo indisponível e mapeado: [{'sku', 'quantity', 'line_item_id', 'combo_indisponivel': True}]
        - Se combo normal: componentes multiplicados, todos com o MESMO 'line_item_id' do line item original.
        (anota unit_price_hint: 0.0 p/ brinde; {"_combo_divisor": N} p/ não-brinde)
        """

        def _to_bool(v: Any) -> bool:
            s = str(v).strip().lower()
            return s in {"true", "1", "s", "sim", "y", "yes"}

        itens_expandidos: list[dict[str, Any]] = []
        li_edges = cast(list[dict[str, Any]], (pedido.get("lineItems") or {}).get("edges", []) or [])
        for li_edge in li_edges:
            node = cast(dict[str, Any], li_edge.get("node") or {})

            # Shopify LineItem GID -> normaliza para id numérico/string curta do seu projeto
            line_item_gid = str(node.get("id", "") or "")
            line_item_id = normalizar_order_id(line_item_gid)

            sku_li = str(node.get("sku", "") or "").strip()
            qty_li = int(node.get("quantity") or 0)
            if qty_li <= 0:
                continue

            info = self._buscar_info_por_sku(skus_info, sku_li)
            # normaliza para sempre ter um dict; isso tira o Optional da jogada para o mypy
            info_dict: dict[str, Any] = info or {}

            tipo_info = str(info_dict.get("tipo", "")).strip().lower()

            # não é combo
            eh_combo = bool(info_dict) and (tipo_info == "combo" or info_dict.get("composto_de"))
            if not eh_combo:
                itens_expandidos.append(
                    {
                        "sku": sku_li,
                        "quantity": qty_li,
                        "is_combo": False,
                        "line_item_id": line_item_id,  # ✅ precisa para fulfillment
                    }
                )
                continue

            # combo → aplicar regra de pré-venda (não desmembrar)
            mapeado = bool(info_dict.get("guru_ids")) and bool(info_dict.get("shopify_ids"))
            indisponivel = _to_bool(info_dict.get("indisponivel", ""))  # ← parse seguro
            if indisponivel and mapeado:
                itens_expandidos.append(
                    {
                        "sku": sku_li,
                        "quantity": qty_li,
                        "is_combo": True,
                        "combo_indisponivel": True,
                        "line_item_id": line_item_id,  # ✅ ainda assim carregamos o id
                    }
                )
                continue

            # desmembrar componentes → TODOS herdam o mesmo line_item_id
            raw_comp = info_dict.get("composto_de") or []

            # Normaliza para lista de componentes "por combo" (sem multiplicar por qty_li ainda)
            if isinstance(raw_comp, str):
                # permite "SKU1, SKU2 x 2; SKU3*3"
                comp_list_any: list[Any] = [s.strip() for s in re.split(r"[;,]", raw_comp) if s.strip()]
            elif isinstance(raw_comp, list):
                comp_list_any = raw_comp
            else:
                comp_list_any = []

            comp_norm: list[tuple[str, int]] = []
            for comp in comp_list_any:
                comp_sku = ""
                comp_qty = 1

                if isinstance(comp, dict):
                    comp_sku = str(comp.get("sku") or comp.get("SKU") or "").strip()
                    try:
                        comp_qty = int(comp.get("qtd") or comp.get("quantity") or 1)
                    except Exception:
                        comp_qty = 1

                elif isinstance(comp, str):
                    # aceita "SKU", "SKU x 2", "SKU*2"
                    m = re.match(r"^\s*([A-Za-z0-9._\-]+)\s*(?:[xX\*]\s*(\d+))?\s*$", comp)
                    if m:
                        comp_sku = m.group(1).strip()
                        if m.group(2):
                            comp_qty = int(m.group(2))

                else:
                    logger.warning(
                        "componente_tipo_inesperado",
                        extra={"tipo": type(comp).__name__, "combo": sku_li},
                    )
                    continue

                if comp_sku:
                    comp_norm.append((comp_sku, max(1, comp_qty)))

            if not comp_norm:
                # fallback: sem componentes válidos, mantém o combo “inteiro”
                itens_expandidos.append(
                    {
                        "sku": sku_li,
                        "quantity": qty_li,
                        "is_combo": True,
                        "combo_sem_componentes": True,
                        "line_item_id": line_item_id,  # ✅ mantém id
                    }
                )
                continue

            # === calcular divisor efetivo do combo e anotar unit_price_hint por componente ===
            try:
                # aceita divisor como int ou string numérica; válido se >= 1
                cfg_div_raw = info_dict.get("divisor", None)
                cfg_div: int | None
                if isinstance(cfg_div_raw, int):
                    cfg_div = cfg_div_raw if cfg_div_raw >= 1 else None
                elif isinstance(cfg_div_raw, str) and cfg_div_raw.strip().isdigit():
                    cfg_div = int(cfg_div_raw.strip())
                    if cfg_div < 1:
                        cfg_div = None
                else:
                    cfg_div = None

                def _is_brinde(sku_: str) -> bool:
                    _inf = self._buscar_info_por_sku(skus_info, sku_) or {}
                    _inf_dict: Mapping[str, Any] = _inf or {}
                    return str(_inf_dict.get("tipo", "")).strip().lower() == "brinde"

                total_nao_brinde = sum(q for (s, q) in comp_norm if not _is_brinde(s))
                if cfg_div is not None:
                    divisor_efetivo = cfg_div
                else:
                    divisor_efetivo = max(1, total_nao_brinde)

                # adiciona os componentes multiplicando pela quantidade do line item (qty_li),
                # marcando a dica de preço por item:
                for comp_sku, comp_qty in comp_norm:
                    quantidade_total = comp_qty * qty_li
                    if quantidade_total <= 0:
                        continue

                    if _is_brinde(comp_sku):
                        unit_price_hint: Any = 0.0
                    else:
                        unit_price_hint = {"_combo_divisor": divisor_efetivo}

                    itens_expandidos.append(
                        {
                            "sku": comp_sku,
                            "quantity": quantidade_total,
                            "from_combo": sku_li,
                            "is_combo": True,
                            "line_item_id": line_item_id,  # ✅ mesmo id p/ todas as linhas do combo
                            "unit_price_hint": unit_price_hint,
                        }
                    )
            except Exception:
                # fallback sem hints
                for comp_sku, comp_qty in comp_norm:
                    quantidade_total = comp_qty * qty_li
                    if quantidade_total <= 0:
                        continue
                    itens_expandidos.append(
                        {
                            "sku": comp_sku,
                            "quantity": quantidade_total,
                            "from_combo": sku_li,
                            "is_combo": True,
                            "line_item_id": line_item_id,
                        }
                    )

        return itens_expandidos

    @pyqtSlot()
    def run(self) -> None:
        set_correlation_id(self._parent_correlation_id)

        logger.info(
            "coleta_lookup_start",
            extra={
                "data_inicio": self.data_inicio_str,
                "fulfillment_status": (self.fulfillment_status or "").strip().lower(),
            },
        )

        cancelador = cast(threading.Event | None, self.estado.get("cancelador_global"))
        if cancelador is not None and cancelador.is_set():
            logger.warning("shopify_fetch_cancelled_early")
            return

        # valida data início
        try:
            data_inicio = datetime.strptime(self.data_inicio_str, "%d/%m/%Y").replace(tzinfo=TZ_APP)
        except Exception as e:
            self._log_erro("Data inválida", detalhe=str(e), exc=e)
            return

        cursor: str | None = None
        pedidos: list[Pedido] = []

        # ------- Fulfillment status: só "any" ou "unfulfilled" -------
        fs = (self.fulfillment_status or "").strip().lower()

        # Monta a search query base
        filtros: list[str] = ["financial_status:paid"]
        if fs == "unfulfilled":
            filtros.append("fulfillment_status:unfulfilled")

        # ✅ filtro de data somente por INÍCIO (ligado por padrão)
        if cast(bool, self.estado.get("usar_filtro_data", True)):
            filtros.append(f'created_at:>={data_inicio.strftime("%Y-%m-%d")}')

        query_str = " ".join(filtros)
        logger.debug("shopify_query", extra={"query": query_str})

        # Query usando variável $search (evita problemas de escape)
        query_template: str = """
        query($cursor: String, $search: String) {
          orders(first: 50, after: $cursor, query: $search) {
            pageInfo { hasNextPage endCursor }
            edges {
              node {
                id
                name
                createdAt
                displayFulfillmentStatus
                currentTotalDiscountsSet { shopMoney { amount } }
                customer { email firstName lastName }  # mantido se você usa nome/email
                shippingAddress {
                  name
                  address1
                  address2
                  city
                  zip
                  provinceCode
                  phone
                }
                billingAddress {
                  name
                  firstName
                  lastName
                  address1
                  address2
                  city
                  zip
                  provinceCode
                  phone
                }
                shippingLine { discountedPriceSet { shopMoney { amount } } }
                lineItems(first: 10) {
                  edges {
                    node {
                      id
                      title
                      quantity
                      sku
                      product { id }
                      discountedTotalSet { shopMoney { amount } }
                    }
                  }
                }
                fulfillmentOrders(first: 10) {
                  edges {
                    node {
                      id
                      status
                      lineItems(first: 10) {
                        edges {
                          node {
                            id
                            remainingQuantity
                            lineItem { id }
                          }
                        }
                      }
                    }
                  }
                }
                localizationExtensions(first: 5) {
                  edges { node { purpose title value } }
                }
              }
            }
          }
        }
        """

        headers: dict[str, str] = {
            "Content-Type": "application/json",
            "X-Shopify-Access-Token": settings.SHOPIFY_TOKEN,
        }

        # helpers locais para fallback de endereço
        def _is_valid_addr(a: Mapping[str, Any]) -> bool:
            return bool((a or {}).get("address1") or (a or {}).get("city") or (a or {}).get("zip"))

        def _coalesce_shipping_or_billing(p: Mapping[str, Any]) -> dict[str, Any]:
            ship = cast(dict[str, Any], p.get("shippingAddress") or {}) or {}
            bill = cast(dict[str, Any], p.get("billingAddress") or {}) or {}
            if _is_valid_addr(ship):
                # completa com billing se faltar phone/nome
                if not ship.get("phone") and bill.get("phone"):
                    ship["phone"] = bill.get("phone")
                if not ship.get("name"):
                    nome_b = (bill.get("name") or "").strip()
                    if not nome_b:
                        fn = (bill.get("firstName") or "").strip()
                        ln = (bill.get("lastName") or "").strip()
                        nome_b = f"{fn} {ln}".strip()
                    if nome_b:
                        ship["name"] = nome_b
                return ship
            return bill

        while True:
            if cancelador is not None and cancelador.is_set():
                logger.warning("shopify_fetch_cancelled_midloop")
                break

            self._esperar_creditos_se_preciso()

            # --- chamada HTTP ---
            try:
                with requests.Session() as sess:
                    sess.headers.update(headers)
                    resp = sess.post(
                        GRAPHQL_URL,
                        json={
                            "query": query_template,
                            "variables": {"cursor": cursor, "search": query_str},
                        },
                        timeout=8,
                        verify=False,
                    )
            except requests.exceptions.Timeout as e:
                self._log_erro("Timeout na requisição", exc=e, extra_ctx={"cursor": cursor, "query": query_str})
                return
            except requests.exceptions.RequestException as e:
                self._log_erro(
                    "Exceção de rede/requests",
                    exc=e,
                    extra_ctx={"cursor": cursor, "query": query_str},
                )
                return

            if cancelador is not None and cancelador.is_set():
                logger.warning("shopify_fetch_cancelled_after_request")
                break

            # --- HTTP status ---
            if resp.status_code == 429:
                retry = int(resp.headers.get("Retry-After", "2"))
                logger.warning("shopify_http_429", extra={"retry_after": retry})
                time.sleep(retry)
                continue
            if resp.status_code != 200:
                self._log_erro(
                    f"Erro HTTP {resp.status_code}",
                    detalhe=resp.text[:200],
                    resp=resp,
                    extra_ctx={"cursor": cursor, "query": query_str},
                )
                return

            # --- JSON ---
            try:
                payload = cast(dict[str, Any], resp.json())
            except ValueError as e:
                self._log_erro(
                    "Resposta não é JSON válido",
                    detalhe=str(e),
                    resp=resp,
                    extra_ctx={"cursor": cursor, "query": query_str},
                )
                return

            # custos/throttle
            self._atualizar_custos(payload)

            # --- Erros GraphQL? ---
            if "errors" in payload:
                first = payload["errors"][0] if payload["errors"] else {}
                code = ""
                if isinstance(first, dict):
                    code = ((first.get("extensions") or {}).get("code") or "").upper()

                if code == "THROTTLED":
                    needed = float(self._ultimo_requested_cost or 100.0)
                    wait_s = self._calc_wait_seconds(self._ultimo_throttle_status, needed)
                    if wait_s <= 0:
                        wait_s = 1.5
                    print(f"⏳ THROTTLED - aguardando {wait_s:.2f}s e tentando novamente...")
                    time.sleep(wait_s)
                    continue

                if code == "MAX_COST_EXCEEDED":
                    self._log_erro(
                        "MAX_COST_EXCEEDED: custo por query acima de 1000",
                        resp=resp,
                        extra_ctx={"cursor": cursor, "query": query_str},
                    )
                    return

                self._log_erro(
                    "Erros do GraphQL retornados",
                    resp=resp,
                    extra_ctx={"cursor": cursor, "query": query_str},
                )
                return

            data = cast(dict[str, Any], (payload.get("data") or {})).get("orders", {}) or {}
            novos: list[Pedido] = []

            for edge in cast(list[dict[str, Any]], data.get("edges", []) or []):
                if cancelador is not None and cancelador.is_set():
                    logger.warning("shopify_fetch_cancelled_processing")
                    break

                pedido = cast(Pedido, edge.get("node", {}))
                if not pedido:
                    continue

                # ⬇️ Fallback de endereço: shippingAddress válido ou billingAddress
                try:
                    endereco_resolvido = _coalesce_shipping_or_billing(pedido)
                    if endereco_resolvido:
                        pedido["shippingAddress"] = endereco_resolvido  # mantém interface do restante do pipeline
                except Exception:
                    pass

                # --- EXPANSÃO DE ITENS: prioridade por SKU e regra de combo ---
                skus_info = cast(dict[str, Any], self.estado.get("skus_info", {}))
                itens_expandidos = self._expandir_line_items_por_regras(pedido, skus_info)
                pedido["itens_expandidos"] = itens_expandidos  # para uso posterior

                # CPF via localizationExtensions
                cpf = ""
                try:
                    extensoes = cast(dict[str, Any], pedido.get("localizationExtensions") or {}).get("edges", []) or []
                    for ext in cast(list[dict[str, Any]], extensoes):
                        node = cast(dict[str, Any], ext.get("node", {}) or {})
                        if node.get("purpose") == "TAX" and "cpf" in (node.get("title", "") or "").lower():
                            cpf = re.sub(r"\D", "", node.get("value", "") or "")[:11]
                            break
                except Exception as e:
                    self._log_erro(
                        "Falha ao extrair CPF de um pedido",
                        detalhe=f"Pedido {pedido.get('name', '')}: {e}",
                        exc=e,
                        extra_ctx={"cursor": cursor, "query": query_str},
                    )

                pedido["cpf_extraido"] = cpf
                novos.append(pedido)

            pedidos.extend(novos)

            page_info = cast(dict[str, Any], data.get("pageInfo") or {})
            if not page_info.get("hasNextPage"):
                break
            cursor = cast(str | None, page_info.get("endCursor"))

        if cancelador is not None and cancelador.is_set():
            logger.warning("shopify_fetch_cancelled_end")
            return

        logger.info("shopify_fetch_done", extra={"qtd_pedidos": len(pedidos)})

        # Armazenando os dados coletados temporariamente no estado
        dados_temp = cast(dict[str, Any], self.estado["dados_temp"])
        for pedido in pedidos:
            pid_raw = cast(str, pedido.get("id", ""))
            pedido_id = normalizar_order_id(pid_raw)
            dados_temp["cpfs"][pedido_id] = pedido.get("cpf_extraido", "")
            dados_temp["bairros"][pedido_id] = ""

            end = cast(dict[str, Any], pedido.get("shippingAddress") or {})
            dados_temp["enderecos"][pedido_id] = {
                "endereco_base": end.get("address1", ""),
                "numero": end.get("address2", ""),
                "complemento": end.get("provinceCode", ""),
            }

            # status fulfillment
            status_fulfillment = (cast(str, pedido.get("displayFulfillmentStatus") or "")).strip().upper()
            dados_temp["status_fulfillment"][pedido_id] = status_fulfillment

            # frete
            valor_frete_any = (
                cast(dict[str, Any], (pedido.get("shippingLine") or {})).get("discountedPriceSet") or {}
            ).get("shopMoney", {})
            valor_frete = 0.0
            try:
                amount = cast(dict[str, Any], valor_frete_any).get("amount")
                valor_frete = float(amount) if amount is not None else 0.0
            except Exception:
                valor_frete = 0.0
            dados_temp["fretes"][pedido_id] = valor_frete

            # desconto
            valor_desc_any = cast(dict[str, Any], (pedido.get("currentTotalDiscountsSet") or {})).get("shopMoney") or {}
            valor_desconto = 0.0
            try:
                amount_d = cast(dict[str, Any], valor_desc_any).get("amount")
                valor_desconto = float(amount_d) if amount_d is not None else 0.0
            except Exception:
                valor_desconto = 0.0
            dados_temp["descontos"][pedido_id] = valor_desconto

            # salva os itens expandidos por pedido (se existirem)
            itens_expandidos = cast(list[dict[str, Any]], pedido.get("itens_expandidos") or [])
            cast(dict[str, Any], dados_temp["itens_por_pedido"])[pedido_id] = itens_expandidos

        # sinais PyQt
        self.sinais.resultado.emit(pedidos)


def iniciar_coleta_pedidos_shopify(
    estado: MutableMapping[str, Any],
    gerenciador: GerenciadorProgresso,
    data_inicio_str: str,
    produto_alvo: str | None = None,
    skus_info: Mapping[str, Any] | None = None,
    fulfillment_status: str = "any",
    depois: Callable[[], None] | None = None,
) -> None:
    print("[🧪] iniciar_coleta_pedidos_shopify recebeu depois =", depois)
    logger.info(f"[🧪] Threads ativas no pool: {QThreadPool.globalInstance().activeThreadCount()}")

    # Salva o gerenciador original apenas se ainda não existir
    if "gerenciador_progresso" not in estado or not estado["gerenciador_progresso"]:
        estado["gerenciador_progresso"] = gerenciador
    else:
        gerenciador = estado["gerenciador_progresso"]

    if estado.get("processando_pedidos", False):
        print("[⚠️] O processamento dos pedidos já está em andamento. Processamento ignorado.")
        return

    estado["processando_pedidos"] = True

    pool = QThreadPool.globalInstance()
    pool.waitForDone(100)  # espera 100ms por qualquer thread pendente
    pool.setMaxThreadCount(30)

    logger.info(f"[⚙️] Reset QThreadPool: ativas = {pool.activeThreadCount()}")

    estado.setdefault("dados_temp", {})
    estado["dados_temp"].setdefault("cpfs", {})
    estado["dados_temp"].setdefault("bairros", {})
    estado["dados_temp"].setdefault("enderecos", {})
    estado.setdefault("df_temp", pd.DataFrame())

    # Mostra a janela
    QTimer.singleShot(100, gerenciador.janela.show)

    print("[🧪 estado id antes do runnable]:", id(estado))
    runnable = ColetarPedidosShopify(data_inicio_str, estado, fulfillment_status)

    runnable.sinais.resultado.connect(
        lambda pedidos: montar_planilha_shopify(pedidos, produto_alvo, skus_info or {}, estado, gerenciador, depois)
    )
    runnable.sinais.erro.connect(lambda _msg: tratar_erro_coleta_shopify(gerenciador))

    QThreadPool.globalInstance().start(runnable)


openai_client = openai.OpenAI(api_key=settings.OPENAI_API_KEY)


class GPTRateLimiter:
    def __init__(self, max_concorrentes: int = 4, intervalo_minimo: float = 0.3) -> None:
        self._semaforo: threading.BoundedSemaphore = threading.BoundedSemaphore(value=max_concorrentes)
        self._lock: threading.Lock = threading.Lock()
        self._ultima_chamada: float = 0.0
        self._intervalo_minimo: float = intervalo_minimo  # em segundos

    def chamar(self, prompt: str, openai_client: Any, model: str = "gpt-4o") -> dict[str, Any]:
        with self._semaforo:
            with self._lock:
                agora = time.time()
                tempo_decorrido = agora - self._ultima_chamada
                if tempo_decorrido < self._intervalo_minimo:
                    time.sleep(self._intervalo_minimo - tempo_decorrido)
                self._ultima_chamada = time.time()

            for tentativa in range(3):
                try:
                    response = openai_client.chat.completions.create(
                        model=model,
                        messages=[{"role": "user", "content": prompt}],
                        temperature=0,
                        timeout=10,
                    )
                    conteudo: str = response.choices[0].message.content.strip()
                    json_inicio: int = conteudo.find("{")
                    json_fim: int = conteudo.rfind("}") + 1
                    if json_inicio >= 0 and json_fim > json_inicio:
                        return cast(dict[str, Any], json.loads(conteudo[json_inicio:json_fim]))
                    else:
                        raise ValueError("❌ JSON não encontrado na resposta da API.")
                except RateLimitError:
                    espera = 2**tentativa
                    print(f"[⏳ GPT] Limite temporário. Tentando novamente em {espera}s...")
                    time.sleep(espera)
                except Exception as e:
                    print(f"[❌ GPT] Erro: {e}")
                    break

        # Fallback seguro
        raise RuntimeError("gpt_request_failed")


gpt_limiter = GPTRateLimiter(max_concorrentes=2, intervalo_minimo=1.5)


class EnderecoLLM(TypedDict):
    base: str
    numero: str
    complemento: str
    precisa_contato: bool


def normalizar_enderecos_gpt(
    address1: str,
    address2: str,
    logradouro_cep: str,
    bairro_cep: str,
) -> EnderecoLLM:
    import json
    import re
    from typing import cast

    def _fallback_regex(addr1: str, addr2: str) -> EnderecoLLM:
        a1 = (addr1 or "").strip()
        a2 = (addr2 or "").strip()
        m = re.search(r"\b(\d{1,5}[A-Za-z]?)\b", a1)
        if m:
            numero = m.group(1)
            base = a1[: m.start()].strip(" ,.-")
        else:
            numero = "s/n"
            base = a1.strip(" ,.-")
        complemento = a2 or "-"
        if bairro_cep and complemento != "-":
            complemento = re.sub(re.escape(str(bairro_cep)), "", complemento, flags=re.IGNORECASE).strip(" ,.-") or "-"
        if base and complemento.lower().startswith(base.lower()):
            complemento = complemento[len(base) :].strip(" ,.-") or "-"
        return EnderecoLLM(base=base, numero=numero, complemento=complemento, precisa_contato=(numero == "s/n"))

    prompt = f"""
Responda com um JSON contendo:

- base: nome oficial da rua (logradouro). Use `logradouro_cep` se existir. Caso contrário, extraia de `address1`.
- numero: número do imóvel. Deve ser um número puro (ex: "123") ou número com uma única letra (ex: "456B"). Use "s/n" se não houver número claro. O número deve aparecer logo após o nome da rua. **Nunca inclua bairros, nomes de edifícios, siglas ou outras palavras no número.**
- complemento: tudo que estiver em `address1` e `address2` que **não seja** o `base`, o `numero` ou o `bairro_cep`.
- precisa_contato: true apenas se `numero` for "s/n" e o cep nao for de Brasília-DF

Regras importantes:
- Nunca repita `base` no `complemento`.
- Nunca inclua palavras no `numero`. Se houver algo como "123 Edf. Império", o número é apenas "123", e "Edf. Império" vai para o `complemento`.
- Nunca inclua `bairro_cep` no `complemento`.
- Use apenas as informações de `address1`, `address2` e `logradouro_cep`.
- Termos como "Lote", "Quadra", "Conjunto", "Casa", "Lote", "Chácara", "QD", "CJ" ou similares não são número. Se forem encontrados junto ao logradouro, o número deve ser "s/n", e essas informações vão para o complemento.

### Exemplos:

ex.1: address1: "Rua Octávio Mangabeira 123", address2: "Ed. Beverly Hills Apto 101"  
→ base: "Rua Octávio Mangabeira"  
→ numero: "123"  
→ complemento: "Ed. Beverly Hills Apto 101"

ex.2: address1: "222 sul Alameda 25 Lote 2", address2: "Apt 606 A"  
→ base: "Alameda 25"  
→ numero: "222"  
→ complemento: "Apt 606 A, Lote 2"

ex.3: address1: "Rua 55 Norte", address2: "Lote 42 Uno Residence Apt 201"  
→ base: "Rua 55 Norte"  
→ numero: "s/n"  
→ complemento: "Lote 42 Uno Residence Apt 201"

ex.4: address1: "QD 6 CONJUNTO 3 CASA 7", address2: "Próx. à polícia civil"  
→ base: ""  
→ numero: "s/n"  
→ complemento: "QD 6 CONJUNTO 3 CASA 7, Próx. à polícia civil"

ex.5: address1: "Av. das Américas Lote 22 QD 3", address2: "Bloco C Apto 301"  
→ base: "Av. das Américas"  
→ numero: "s/n"  
→ complemento: "Lote 22 QD 3, Bloco C Apto 301"

---

Dados fornecidos:
address1: {address1}
address2: {address2}
logradouro_cep: {logradouro_cep}
bairro_cep: {bairro_cep}

Formato de resposta:
{{"base": "...", "numero": "...", "complemento": "...", "precisa_contato": false}}
""".strip()

    # >>> ajuste essencial: capturar erro de requisição e cair no fallback
    try:
        resp = gpt_limiter.chamar(prompt, openai_client)
    except Exception:
        return _fallback_regex(address1, address2)

    if isinstance(resp, dict):
        data = resp
    else:
        txt = str(resp or "").strip()
        if ("Responda com um JSON" in txt) or ("Dados fornecidos:" in txt):
            return _fallback_regex(address1, address2)
        try:
            data = json.loads(cast(str, txt))
        except Exception:
            return _fallback_regex(address1, address2)

    base = str(data.get("base", "") or "").strip()
    numero = str(data.get("numero", "") or "").strip()
    complemento = str(data.get("complemento", "") or "").strip()
    precisa_contato = bool(data.get("precisa_contato", False))

    if not numero and not complemento:
        return _fallback_regex(address1, address2)

    if not numero or not re.match(r"^\d+[A-Za-z]?$", numero):
        numero = "s/n"
        precisa_contato = True

    if not complemento:
        complemento = "-"

    if bairro_cep and complemento != "-":
        complemento = re.sub(re.escape(str(bairro_cep)), "", complemento, flags=re.IGNORECASE).strip(" ,.-") or "-"

    if base and complemento.lower().startswith(base.lower()):
        complemento = complemento[len(base) :].strip(" ,.-") or "-"

    if "Responda com um JSON" in f"{base} {numero} {complemento}":
        return _fallback_regex(address1, address2)

    return EnderecoLLM(
        base=base,
        numero=numero,
        complemento=complemento,
        precisa_contato=precisa_contato,
    )


def finalizar_coleta_shopify(
    estado: MutableMapping[str, Any],
    gerenciador: GerenciadorProgresso | None = None,
) -> None:
    gerenciador = gerenciador or estado.get("gerenciador_progresso")
    logger.info(f"[🔚] Finalizando processo de normalização... gerenciador={id(gerenciador)}")

    if estado.get("cancelador_global", threading.Event()).is_set():
        logger.warning("[🛑] Cancelamento detectado durante finalização.")
        return

    try:
        if gerenciador:
            logger.info("[✅] Atualizando barra final...")
            gerenciador.atualizar("✅ Atualização concluída!", 1, 1)

            logger.info("[🧪] Fechando gerenciador com QTimer.singleShot(0)")
            QTimer.singleShot(0, gerenciador.fechar)
        else:
            logger.warning("[⚠️] Nenhum gerenciador fornecido para fechar.")
    except Exception as e:
        logger.exception(f"[❌] Erro ao tentar fechar gerenciador: {e}")

    finalizar_threads_ativas()
    finalizar_estados_coleta_shopify(estado)


def finalizar_threads_ativas() -> None:
    pool = QThreadPool.globalInstance()
    pool.waitForDone(5000)  # Espera até 5s

    while pool.activeThreadCount() > 0:
        logger.warning(f"[⚠️] Ainda há {pool.activeThreadCount()} threads ativas no pool - aguardando...")
        time.sleep(0.5)
        pool.waitForDone(500)

    pool.clear()
    pool.setMaxThreadCount(30)
    logger.info("[✅] QThreadPool limpo com sucesso.")


def finalizar_estados_coleta_shopify(estado: MutableMapping[str, Any]) -> None:
    logger.info("[🧼] Limpando verificadores e pendentes do estado...")

    estado.setdefault("etapas_finalizadas", {})  # ✅ garante existência do dicionário

    for chave in ["cpf", "bairro", "endereco"]:
        estado[f"verificador_{chave}"] = None
        estado[f"finalizou_{chave}"] = False
        estado["etapas_finalizadas"][chave] = False
        estado[f"{chave}_pendentes"] = set()

    estado["enderecos_normalizados"] = {}
    estado.setdefault("dados_temp", {})
    estado["dados_temp"].setdefault("cpfs", {})
    estado["dados_temp"].setdefault("bairros", {})
    estado["dados_temp"].setdefault("enderecos", {})
    estado["processando_pedidos"] = False

    logger.info("[✅] Estado limpo com sucesso.")


def ajustar_telefone_planilha(tel: str | None) -> str:
    """Remove caracteres não numéricos de um telefone e corta o prefixo '55'."""
    return re.sub(r"\D", "", tel or "").removeprefix("55")


def consolidar_planilha_shopify(
    estado: MutableMapping[str, Any],
    gerenciador: GerenciadorProgresso | None,
) -> None:
    def encerrar_se_cancelado(mensagem: str) -> bool:
        if estado.get("cancelador_global", threading.Event()).is_set():
            logger.warning(f"[🛑] {mensagem}")
            if gerenciador:
                gerenciador.fechar()
            return True
        return False

    if encerrar_se_cancelado("Cancelamento detectado antes de atualizar a planilha."):
        return

    # garante skus_info disponível para produto_indisponivel
    estado.setdefault("skus_info", {})

    etapas: Mapping[str, Any] = estado.get("etapas_finalizadas", {})
    if not (etapas.get("cpf") and etapas.get("bairro") and etapas.get("endereco")):
        logger.warning(f"[⚠️] Dados incompletos! Etapas: {etapas}")
        return

    df_any = estado.get("df_temp")
    if not isinstance(df_any, pd.DataFrame) or df_any.empty:
        logger.warning("[⚠️] DataFrame temporário não encontrado.")
        return
    df: pd.DataFrame = df_any

    logger.info("[✅] Todos os dados foram coletados. Atualizando a planilha...")

    # -- preenchimentos por pedido (CPF, bairro, endereço) --
    for pedido_id, cpf in estado.get("dados_temp", {}).get("cpfs", {}).items():
        if encerrar_se_cancelado("Cancelamento durante preenchimento de CPF."):
            return
        pid = normalizar_order_id(pedido_id)
        idx = df["transaction_id"].astype(str).str.strip() == pid
        df.loc[idx, "CPF/CNPJ Comprador"] = cpf

    for pedido_id, bairro in estado.get("dados_temp", {}).get("bairros", {}).items():
        if encerrar_se_cancelado("Cancelamento durante preenchimento de bairro."):
            return
        pid = normalizar_order_id(pedido_id)
        idx = df["transaction_id"].astype(str).str.strip() == pid
        df.loc[idx, "Bairro Comprador"] = bairro

    for pedido_id, endereco in estado.get("enderecos_normalizados", {}).items():
        if encerrar_se_cancelado("Cancelamento durante preenchimento de endereço."):
            return
        pid = normalizar_order_id(pedido_id)
        idx = df["transaction_id"].astype(str).str.strip() == pid
        df.loc[idx, "Endereço Comprador"] = endereco.get("endereco_base", "")
        df.loc[idx, "Número Comprador"] = endereco.get("numero", "")
        df.loc[idx, "Complemento Comprador"] = endereco.get("complemento", "")
        df.loc[idx, "Precisa Contato"] = endereco.get("precisa_contato", "")
        df.loc[idx, "Endereço Entrega"] = endereco.get("endereco_base", "")
        df.loc[idx, "Número Entrega"] = endereco.get("numero", "")
        df.loc[idx, "Complemento Entrega"] = endereco.get("complemento", "")
        df.loc[idx, "Bairro Entrega"] = estado.get("dados_temp", {}).get("bairros", {}).get(pid, "")

    # telefones normalizados
    for col in ["Telefone Comprador", "Celular Comprador"]:
        if col in df.columns:
            df[col] = df[col].apply(ajustar_telefone_planilha)

    # ---------- indisponibilidade com preferência por SKU ----------
    try:
        _skus_info: dict[str, Any] = estado.get("skus_info", {})  # mapeamento do skus.json
        # garante colunas para a verificação
        if "SKU" not in df.columns:
            df["SKU"] = ""
        if "Produto" not in df.columns:
            df["Produto"] = ""
        # aplica preferência por SKU; fallback por nome
        df["indisponivel"] = [
            "S" if produto_indisponivel(str(nome or ""), sku=str(sku or "")) else "N"
            for sku, nome in zip(df["SKU"], df["Produto"], strict=False)
        ]
    except Exception as e:
        logger.exception(f"[⚠️] Falha ao calcular 'indisponivel' (preferência por SKU): {e}")

    # ---------- preencher id_line_item por SKU a partir da coleta ----------
    try:
        itens_por_pedido: dict[str, list[dict[str, Any]]] = (
            estado.get("dados_temp", {}).get("itens_por_pedido", {}) or {}
        )
        if "id_line_item" not in df.columns:
            df["id_line_item"] = ""

        # normalizações auxiliares
        df["transaction_id"] = df["transaction_id"].astype(str).str.strip()
        df["SKU"] = df["SKU"].astype(str).str.strip()
        # cria uma cópia normalizada para map por SKU
        df["_SKU_NORM_TMP"] = df["SKU"].str.upper()

        for pedido_id, itens in itens_por_pedido.items():
            pid = normalizar_order_id(pedido_id)
            idx_pedido = df["transaction_id"].eq(pid)
            if not idx_pedido.any():
                continue

            # monta mapa SKU->line_item_id (primeira ocorrência prevalece)
            sku_to_lineid: dict[str, str] = {}
            for it in itens:
                sku = str(it.get("sku", "")).strip().upper()
                li = str(it.get("line_item_id", "")).strip()
                if sku and li and sku not in sku_to_lineid:
                    sku_to_lineid[sku] = li

            if not sku_to_lineid:
                continue

            # aplica mapeamento no bloco do pedido
            df.loc[idx_pedido, "id_line_item"] = (
                df.loc[idx_pedido, "_SKU_NORM_TMP"].map(sku_to_lineid).fillna(df.loc[idx_pedido, "id_line_item"])
            )

        # limpa coluna auxiliar
        df.drop(columns=["_SKU_NORM_TMP"], inplace=True)
    except Exception as e:
        logger.exception(f"[erro] Falha ao preencher id_line_item por SKU: {e}")

    # 🔁 restaura frete, status e desconto capturados em montar_planilha_shopify (se existirem)
    if "fretes_shopify" in estado:
        estado.setdefault("dados_temp", {})["fretes"] = estado["fretes_shopify"]
    if "status_fulfillment_shopify" in estado:
        estado.setdefault("dados_temp", {})["status_fulfillment"] = estado["status_fulfillment_shopify"]
    if "descontos_shopify" in estado:
        estado.setdefault("dados_temp", {})["descontos"] = estado["descontos_shopify"]

    estado["df_planilha_parcial"] = df
    logger.info(f"[✅] Planilha atualizada com {len(df)} linhas.")


def montar_planilha_shopify(
    pedidos: Iterable[Mapping[str, Any]],
    produto_alvo: str | None,
    skus_info: Mapping[str, Mapping[str, Any]],
    estado: MutableMapping[str, Any],
    gerenciador: GerenciadorProgresso,
    depois: Callable[[], None] | None,
) -> None:
    print("[🧪] montar_planilha_shopify recebeu depois =", depois)
    estado["df_temp"] = pd.DataFrame()
    df_temp: pd.DataFrame = estado.get("df_temp", pd.DataFrame())

    # modo de coleta: "any" (tudo) ou "unfulfilled" (somente pendentes)
    modo_fs: str = (estado.get("fulfillment_status_selecionado") or "any").strip().lower()

    # Filtro por produto específico (se marcado)
    ids_filtrados: set[str] = set()
    if produto_alvo and skus_info:
        alvo = produto_alvo.strip().lower()
        for nome_produto, dados in skus_info.items():
            if alvo in nome_produto.lower():
                ids_filtrados.update(map(str, dados.get("shopify_ids", [])))

    # índice auxiliar: SKU -> nome
    def nome_por_sku(sku: str) -> str:
        sku_u = (sku or "").strip().upper()
        for nome, dados in skus_info.items():
            if str(dados.get("sku", "")).strip().upper() == sku_u:
                return nome
        return sku  # fallback: usa o próprio SKU

    linhas_geradas: list[dict[str, Any]] = []
    for pedido in pedidos:
        # --- dados básicos do pedido (robustos a None) ---
        cust: Mapping[str, Any] = pedido.get("customer") or {}
        first = (cust.get("firstName") or "").strip()
        last = (cust.get("lastName") or "").strip()
        nome_cliente = f"{first} {last}".strip()
        email: str = cust.get("email") or ""
        endereco: Mapping[str, Any] = pedido.get("shippingAddress") or {}  # pode vir None
        telefone: str = endereco.get("phone", "") or ""
        transaction_id: str = str(pedido.get("id") or "").split("/")[-1]

        # --- frete / status / desconto ---
        valor_frete_any = (
            ((pedido.get("shippingLine") or {}).get("discountedPriceSet") or {}).get("shopMoney", {})
        ).get("amount")
        try:
            valor_frete: float = float(valor_frete_any) if valor_frete_any is not None else 0.0
        except Exception:
            valor_frete = 0.0

        status_fulfillment: str = (pedido.get("displayFulfillmentStatus") or "").strip().upper()

        valor_desconto_any = ((pedido.get("currentTotalDiscountsSet") or {}).get("shopMoney") or {}).get("amount")
        try:
            valor_desconto: float = float(valor_desconto_any) if valor_desconto_any is not None else 0.0
        except Exception:
            valor_desconto = 0.0

        estado.setdefault("dados_temp", {}).setdefault("fretes", {})[transaction_id] = valor_frete
        estado.setdefault("dados_temp", {}).setdefault("status_fulfillment", {})[transaction_id] = status_fulfillment
        estado.setdefault("dados_temp", {}).setdefault("descontos", {})[transaction_id] = valor_desconto

        print(
            f"[🧾] Pedido {transaction_id} → Status: {status_fulfillment} | Frete: {valor_frete} | Desconto: {valor_desconto}"
        )

        # --- mapa remainingQuantity por lineItem.id (a partir de fulfillmentOrders) ---
        remaining_por_line: dict[str, int] = {}
        try:
            fo_edges = (pedido.get("fulfillmentOrders") or {}).get("edges") or []
            for fo_e in fo_edges:
                fo_node = fo_e.get("node") or {}
                li_edges = ((fo_node.get("lineItems") or {}).get("edges")) or []
                for li_e in li_edges:
                    li_node = li_e.get("node") or {}
                    gid = (li_node.get("lineItem") or {}).get("id") or ""
                    lid = str(gid).split("/")[-1] if gid else ""
                    rq = int(li_node.get("remainingQuantity") or 0)
                    if lid:
                        remaining_por_line[lid] = max(remaining_por_line.get(lid, 0), rq)
        except Exception:
            remaining_por_line = {}

        total_remaining_pedido = sum(remaining_por_line.values())
        estado.setdefault("dados_temp", {}).setdefault("remaining_totais", {})[transaction_id] = int(
            total_remaining_pedido
        )

        # --- CEP por pedido ---
        estado.setdefault("cep_por_pedido", {})[transaction_id] = (
            (endereco.get("zip", "") or "").replace("-", "").strip()
        )

        # --- processar line items ---
        line_edges = (pedido.get("lineItems") or {}).get("edges", [])
        # pega itens expandidos que o coletor já montou
        itens_expandidos_all = list(pedido.get("itens_expandidos") or [])

        for item_edge in line_edges:
            item = item_edge.get("node") or {}
            product_id_raw = (item.get("product") or {}).get("id", "")
            if not product_id_raw:
                continue

            product_id = str(product_id_raw).split("/")[-1]
            if ids_filtrados and product_id not in ids_filtrados:
                continue

            # Descobre nome do produto e SKU a partir do mapeamento do skus.json (para o line item original)
            nome_produto = ""
            sku_item = ""
            for nome_local, dados in skus_info.items():
                if product_id in map(str, dados.get("shopify_ids", [])):
                    nome_produto = nome_local
                    sku_item = str(dados.get("sku", ""))
                    break

            base_qtd = int(item.get("quantity") or 0)
            valor_total_linha = float(
                ((item.get("discountedTotalSet") or {}).get("shopMoney") or {}).get("amount") or 0
            )
            valor_unit_line: float = round(valor_total_linha / base_qtd, 2) if base_qtd else 0.0
            id_line_item: str = str(item.get("id", "")).split("/")[-1]

            # Quantidade a gerar conforme o modo selecionado
            if modo_fs == "unfulfilled":
                remaining = int(remaining_por_line.get(id_line_item, 0))
                if remaining <= 0:
                    continue
                qtd_a_gerar_line = remaining
            else:
                qtd_a_gerar_line = base_qtd if base_qtd > 0 else 0

            # Itens expandidos deste line_item (se houver)
            itens_expandidos = [it for it in itens_expandidos_all if str(it.get("line_item_id", "")) == id_line_item]

            if itens_expandidos:
                # === USAR COMPONENTES EXPANDIDOS ===
                # Preço por combo (1 unidade do line item)
                total_por_combo = (valor_total_linha / base_qtd) if base_qtd else 0.0

                for it in itens_expandidos:
                    comp_sku = str(it.get("sku", "")).strip()
                    if not comp_sku:
                        continue

                    # quantidade total do componente considerando remaining/base_qtd
                    qtd_total_component = 0
                    try:
                        qtd_por_combo = int(it.get("quantity", 0)) // max(1, base_qtd)
                    except Exception:
                        qtd_por_combo = 1
                    qtd_total_component = qtd_por_combo * qtd_a_gerar_line

                    if qtd_total_component <= 0:
                        continue

                    # nome e indisponível por componente
                    nome_comp = nome_por_sku(comp_sku)
                    indisp_comp = "S" if produto_indisponivel(nome_comp, sku=comp_sku) else "N"

                    # preço unitário do componente
                    unit_hint = it.get("unit_price_hint", None)
                    if unit_hint == 0.0:
                        valor_unit_comp = 0.0
                    elif isinstance(unit_hint, dict) and "_combo_divisor" in unit_hint:
                        div = int(unit_hint.get("_combo_divisor") or 1)
                        div = max(1, div)
                        valor_unit_comp = round((total_por_combo / div), 2)
                    else:
                        # fallback: reparte igualmente por qtd_por_combo se desejar, ou usa do line item
                        valor_unit_comp = valor_unit_line

                    # gera 1 linha por unidade
                    for _ in range(qtd_total_component):
                        linha: dict[str, Any] = {
                            "Número pedido": pedido.get("name", ""),
                            "Nome Comprador": nome_cliente,
                            "Data": local_now().strftime("%d/%m/%Y"),
                            "CPF/CNPJ Comprador": "",
                            "Endereço Comprador": endereco.get("address1", ""),
                            "Bairro Comprador": endereco.get("district", ""),
                            "Número Comprador": endereco.get("number", ""),
                            "Complemento Comprador": endereco.get("address2", ""),
                            "CEP Comprador": endereco.get("zip", ""),
                            "Cidade Comprador": endereco.get("city", ""),
                            "UF Comprador": endereco.get("provinceCode", ""),
                            "Telefone Comprador": telefone,
                            "Celular Comprador": telefone,
                            "E-mail Comprador": email,
                            "Produto": nome_comp,
                            "SKU": comp_sku,
                            "Un": "UN",
                            "Quantidade": "1",
                            "Valor Unitário": f"{valor_unit_comp:.2f}".replace(".", ","),
                            "Valor Total": f"{valor_unit_comp:.2f}".replace(".", ","),
                            "Total Pedido": "",
                            "Valor Frete Pedido": f"{valor_frete:.2f}".replace(".", ","),
                            "Valor Desconto Pedido": f"{valor_desconto:.2f}".replace(".", ","),
                            "Outras despesas": "",
                            "Nome Entrega": nome_cliente,
                            "Endereço Entrega": endereco.get("address1", ""),
                            "Número Entrega": endereco.get("number", ""),
                            "Complemento Entrega": endereco.get("address2", ""),
                            "Cidade Entrega": endereco.get("city", ""),
                            "UF Entrega": endereco.get("provinceCode", ""),
                            "CEP Entrega": endereco.get("zip", ""),
                            "Bairro Entrega": endereco.get("district", ""),
                            "Transportadora": "",
                            "Serviço": "",
                            "Tipo Frete": "0 - Frete por conta do Remetente (CIF)",
                            "Observações": "",
                            "Qtd Parcela": "",
                            "Data Prevista": "",
                            "Vendedor": "",
                            "Forma Pagamento": "",
                            "ID Forma Pagamento": "",
                            "transaction_id": transaction_id,
                            "id_line_item": id_line_item,
                            "id_produto": product_id,  # id do produto do combo original (ok)
                            "indisponivel": indisp_comp,
                            "Precisa Contato": "SIM",
                            "Data Pedido": (pedido.get("createdAt") or "")[:10],
                            # flags úteis
                            "is_combo": bool(it.get("is_combo", False)),
                            "from_combo": it.get("from_combo", ""),
                        }
                        linhas_geradas.append(linha)
            else:
                # === FALLBACK: SEM EXPANSÃO → usa o line item original ===
                indisponivel_flag = "S" if produto_indisponivel(nome_produto) else "N"
                for _ in range(qtd_a_gerar_line):
                    linha: dict[str, Any] = {
                        "Número pedido": pedido.get("name", ""),
                        "Nome Comprador": nome_cliente,
                        "Data": local_now().strftime("%d/%m/%Y"),
                        "CPF/CNPJ Comprador": "",
                        "Endereço Comprador": endereco.get("address1", ""),
                        "Bairro Comprador": endereco.get("district", ""),
                        "Número Comprador": endereco.get("number", ""),
                        "Complemento Comprador": endereco.get("address2", ""),
                        "CEP Comprador": endereco.get("zip", ""),
                        "Cidade Comprador": endereco.get("city", ""),
                        "UF Comprador": endereco.get("provinceCode", ""),
                        "Telefone Comprador": telefone,
                        "Celular Comprador": telefone,
                        "E-mail Comprador": email,
                        "Produto": nome_produto,
                        "SKU": sku_item,
                        "Un": "UN",
                        "Quantidade": "1",
                        "Valor Unitário": f"{valor_unit_line:.2f}".replace(".", ","),
                        "Valor Total": f"{valor_unit_line:.2f}".replace(".", ","),
                        "Total Pedido": "",
                        "Valor Frete Pedido": f"{valor_frete:.2f}".replace(".", ","),
                        "Valor Desconto Pedido": f"{valor_desconto:.2f}".replace(".", ","),
                        "Outras despesas": "",
                        "Nome Entrega": nome_cliente,
                        "Endereço Entrega": endereco.get("address1", ""),
                        "Número Entrega": endereco.get("number", ""),
                        "Complemento Entrega": endereco.get("address2", ""),
                        "Cidade Entrega": endereco.get("city", ""),
                        "UF Entrega": endereco.get("provinceCode", ""),
                        "CEP Entrega": endereco.get("zip", ""),
                        "Bairro Entrega": endereco.get("district", ""),
                        "Transportadora": "",
                        "Serviço": "",
                        "Tipo Frete": "0 - Frete por conta do Remetente (CIF)",
                        "Observações": "",
                        "Qtd Parcela": "",
                        "Data Prevista": "",
                        "Vendedor": "",
                        "Forma Pagamento": "",
                        "ID Forma Pagamento": "",
                        "transaction_id": transaction_id,
                        "id_line_item": id_line_item,
                        "id_produto": product_id,
                        "indisponivel": indisponivel_flag,
                        "Precisa Contato": "SIM",
                        "Data Pedido": (pedido.get("createdAt") or "")[:10],
                        "is_combo": False,
                    }
                    linhas_geradas.append(linha)

    if linhas_geradas:
        df_novo = pd.DataFrame(linhas_geradas)
        df_temp = pd.concat([df_temp, df_novo], ignore_index=True)
        estado["df_temp"] = df_temp
        print(f"[✅] {len(linhas_geradas)} itens adicionados ao df_temp.")
        print(f"[📊] Total atual no df_temp: {len(df_temp)} linhas.")
    else:
        print("[⚠️] Nenhum item foi adicionado - possivelmente nenhum item corresponde ao filtro.")

    logger.info(f"[✅] {len(linhas_geradas)} itens adicionados ao df_temp.")
    logger.info(f"[📊] Total atual no df_temp: {len(estado['df_temp'])} linhas.")

    estado["etapas_finalizadas"] = {"cpf": False, "bairro": False, "endereco": False}
    estado["finalizou_cpfs"] = False
    estado["finalizou_bairros"] = False
    estado["finalizou_enderecos"] = False

    # 🆕 Preserva os dados extras após montar df_temp
    estado["fretes_shopify"] = estado.get("dados_temp", {}).get("fretes", {}).copy()
    estado["status_fulfillment_shopify"] = estado.get("dados_temp", {}).get("status_fulfillment", {}).copy()
    estado["descontos_shopify"] = estado.get("dados_temp", {}).get("descontos", {}).copy()

    logger.info("[🚀] Iniciando fluxo de coleta de CPFs após montar_planilha_shopify.")
    gerenciador.atualizar("📦 Processando transações recebidas...", 0, 0)
    iniciar_busca_cpfs(estado, estado.get("gerenciador_progresso"), depois)


def marcar_cpf_coletado(
    pedido_id: str,
    cpf: str,
    estado: dict,
    gerenciador: Any | None = None,
) -> None:
    pedido_id = normalizar_order_id(pedido_id)
    estado.setdefault("cpf_pendentes", set())
    estado.setdefault("dados_temp", {}).setdefault("cpfs", {})

    if estado.get("cancelador_global", threading.Event()).is_set():
        logger.warning(f"[INFO] Cancelamento detectado durante marcar_cpf_coletado → pedido {pedido_id}")
        if gerenciador:
            gerenciador.fechar()
        return

    if pedido_id not in estado["cpf_pendentes"]:
        logger.debug(f"[DBG] Pedido {pedido_id} já removido de cpf_pendentes ou não pertence ao conjunto. Ignorando.")
        return

    estado["cpf_pendentes"].discard(pedido_id)
    estado["dados_temp"]["cpfs"][pedido_id] = cpf

    total = estado.get("cpf_total_esperado", 0)
    atual = total - len(estado["cpf_pendentes"])
    logger.info(f"[OK] CPF {atual}/{total} coletado para pedido {pedido_id}")


def marcar_bairro_coletado(
    pedido_id: str,
    bairro: str,
    estado: dict,
    gerenciador: Any | None = None,
) -> None:
    pedido_id = normalizar_order_id(pedido_id)
    estado.setdefault("bairro_pendentes", set())
    estado.setdefault("dados_temp", {}).setdefault("bairros", {})

    # Cancela cedo se necessário (coerente com marcar_cpf_coletado)
    if estado.get("cancelador_global", threading.Event()).is_set():
        logger.warning(f"[🛑] Cancelamento detectado durante marcar_bairro_coletado → pedido {pedido_id}")
        if gerenciador:
            gerenciador.fechar()
        return

    if pedido_id in estado["bairro_pendentes"]:
        estado["bairro_pendentes"].discard(pedido_id)
        estado["dados_temp"]["bairros"][pedido_id] = bairro

        total = estado.get("bairro_total_esperado", 0)
        atual = total - len(estado["bairro_pendentes"])
        logger.info(f"[📍] Bairros: {atual}/{total}")
    else:
        logger.debug(f"[🟡] Pedido {pedido_id} já processado ou inexistente em pendentes.")


def tratar_erro_coleta_shopify(gerenciador: GerenciadorProgresso) -> None:
    app: QCoreApplication | None = QCoreApplication.instance()
    if app is not None and QThread.currentThread() == app.thread():
        gerenciador.fechar()
    else:
        QTimer.singleShot(0, gerenciador.fechar)


# Funções de mapeamento dos produtos da Loja


def mapear_produtos_shopify(
    skus_info: MutableMapping[str, Any],
    produtos_shopify: Sequence[Mapping[str, Any]],
    skus_path: Path,
) -> None:
    class DialogoMapeamento(QDialog):
        def __init__(self) -> None:
            super().__init__()
            self.setWindowTitle("Mapear SKUs com Produtos da Shopify")
            self.setMinimumSize(900, 560)

            layout = QVBoxLayout(self)

            # --- seletor de produto interno (sem texto livre) ---
            linha_sel = QHBoxLayout()
            linha_sel.addWidget(QLabel("Produto interno:"))
            self.combo_interno = QComboBox()
            self.combo_interno.setEditable(False)
            self.combo_interno.addItems(sorted(skus_info.keys()))
            self.combo_interno.currentTextChanged.connect(self._popular_lista)
            linha_sel.addWidget(self.combo_interno)

            # filtro opcional por SKU da Shopify
            linha_sel.addWidget(QLabel("Filtrar SKU (Shopify):"))
            self.input_busca = QLineEdit()
            self.input_busca.setPlaceholderText("ex.: B050A, L002A…")
            self.input_busca.textChanged.connect(self._popular_lista)
            linha_sel.addStretch(1)
            layout.addLayout(linha_sel)

            # lista (multi-seleção) de itens/variantes da Shopify
            self.lista = QListWidget()
            self.lista.setSelectionMode(QAbstractItemView.MultiSelection)
            layout.addWidget(QLabel("Selecione os itens/variantes da Shopify para mapear:"))
            layout.addWidget(self.lista)

            # botões
            botoes = QHBoxLayout()
            self.btn_salvar = QPushButton("Salvar mapeamento")
            self.btn_concluir = QPushButton("Concluir")
            botoes.addStretch(1)
            botoes.addWidget(self.btn_salvar)
            botoes.addWidget(self.btn_concluir)
            layout.addLayout(botoes)

            self.btn_salvar.clicked.connect(self._salvar)
            self.btn_concluir.clicked.connect(self.accept)

            # atalhos
            self._sc_save = QShortcut(QKeySequence("Ctrl+S"), self)
            self._sc_save.activated.connect(self._salvar)

            # dados de entrada
            self.skus_info: MutableMapping[str, Any] = skus_info
            self.entries = self._flatten_shopify(produtos_shopify or [])

            # primeira carga
            self._popular_lista()

        # ---------- helpers ----------
        @staticmethod
        def _norm_sku(s: str) -> str:
            return re.sub(r"[^A-Za-z0-9]", "", (s or "").strip().upper())

        def _sku_interno_atual(self) -> str:
            interno = self.combo_interno.currentText().strip()
            if interno and interno in self.skus_info:
                return str(self.skus_info[interno].get("sku", "") or "")
            return ""

        def _flatten_shopify(
            self,
            produtos: Sequence[Mapping[str, Any]],
        ) -> list[dict[str, Any]]:
            """Normaliza produtos/variantes da Shopify em itens planos com: {'display', 'sku', 'id',
            'product_id', 'variant_id'}"""
            out: list[dict[str, Any]] = []
            for p in produtos:
                titulo = str(p.get("title") or p.get("name") or "").strip()
                pid = p.get("id") or p.get("product_id")
                variants_any = p.get("variants") or []
                variants: Sequence[Mapping[str, Any]] = (
                    cast(Sequence[Mapping[str, Any]], variants_any) if isinstance(variants_any, list) else []
                )

                if variants:
                    for v in variants:
                        vid = v.get("id")
                        vsku = str(v.get("sku") or "").strip()
                        disp = f"{titulo}  (SKU: {vsku or '-'})  [id: {vid or pid}]"
                        out.append(
                            {
                                "display": disp,
                                "sku": vsku,
                                "id": (vid or pid),
                                "product_id": pid,
                                "variant_id": vid,
                            }
                        )
                else:
                    vsku = str(p.get("sku") or "").strip()
                    disp = f"{titulo}  (SKU: {vsku or '-'})  [id: {pid}]"
                    out.append(
                        {
                            "display": disp,
                            "sku": vsku,
                            "id": pid,
                            "product_id": pid,
                            "variant_id": None,
                        }
                    )

            return [e for e in out if e.get("id") is not None]

        # ---------- UI ----------
        def _popular_lista(self) -> None:
            self.lista.clear()

            sku_interno = self._sku_interno_atual()
            filtro_user = self.input_busca.text().strip()

            norm_interno = self._norm_sku(sku_interno)
            norm_filtro = self._norm_sku(filtro_user)

            def match(e: dict) -> bool:
                esk = self._norm_sku(e.get("sku", ""))
                # bater por SKU interno; filtro é refinamento opcional
                ok_interno = True if not norm_interno else (esk == norm_interno or (norm_interno in esk))
                ok_filtro = True if not norm_filtro else (norm_filtro in esk)
                return ok_interno and ok_filtro

            candidatos = [e for e in self.entries if match(e)]
            if not candidatos and not (norm_interno or norm_filtro):
                candidatos = self.entries  # fallback: evita tela vazia

            for e in candidatos:
                it = QListWidgetItem(e["display"])
                it.setData(QtCore.Qt.ItemDataRole.UserRole, e["id"])
                it.setData(QtCore.Qt.ItemDataRole.UserRole + 1, e.get("sku", ""))
                self.lista.addItem(it)

        # ---------- salvar ----------
        def _salvar(self) -> None:
            interno = self.combo_interno.currentText().strip()
            if not interno:
                QMessageBox.warning(self, "Aviso", "Selecione o produto interno.")
                return
            if interno not in self.skus_info:
                QMessageBox.warning(self, "Aviso", "Produto interno inválido.")
                return

            itens = self.lista.selectedItems()
            if not itens:
                QMessageBox.information(self, "Aviso", "Nenhum item selecionado.")
                return

            ids_sel: list[str] = []
            for it in itens:
                val = str(it.data(int(Qt.UserRole)) or "").strip()
                if val:
                    ids_sel.append(val)

            entrada = self.skus_info.setdefault(interno, {})
            entrada.setdefault("shopify_ids", [])
            ja = set(map(str, entrada["shopify_ids"]))
            for sid in ids_sel:
                if sid not in ja:
                    # armazene como int quando possível
                    try:
                        entrada["shopify_ids"].append(int(sid))
                    except Exception:
                        entrada["shopify_ids"].append(sid)
                    ja.add(sid)

            try:
                with open(skus_path, "w", encoding="utf-8") as f:
                    json.dump(self.skus_info, f, indent=4, ensure_ascii=False)
            except Exception as e:
                QMessageBox.warning(self, "Aviso", f"Não foi possível salvar: {e}")
                return

            QMessageBox.information(self, "Sucesso", f"Mapeados {len(ids_sel)} item(ns) para '{interno}'.")

    dlg = DialogoMapeamento()
    dlg.exec_()


class ProductShopifyVariant(TypedDict):
    product_id: int
    variant_id: int
    title: str
    sku: str


def iniciar_mapeamento_produtos_shopify(skus_info: Mapping[str, Any]) -> None:
    produtos: list[ProductShopifyVariant] = buscar_produtos_shopify()
    if not produtos:
        QMessageBox.warning(None, "Erro", "Nenhum produto retornado da Shopify.")
        return

    # Se o diálogo precisa mutar, faça cast localmente:
    mapear_produtos_shopify(
        cast(MutableMapping[str, Any], skus_info),  # só se realmente for mutado lá dentro
        produtos,
        skus_path,
    )


def buscar_produtos_shopify() -> list[ProductShopifyVariant]:
    url: str | None = f"https://{settings.SHOP_URL}/admin/api/{API_VERSION}/products.json?limit=250"
    headers: dict[str, str] = {
        "X-Shopify-Access-Token": settings.SHOPIFY_TOKEN,
        "Content-Type": "application/json",
    }

    todos: list[ProductShopifyVariant] = []
    pagina_atual: int = 1

    while url:
        resp = http_get(url, headers=headers, verify=False)  # tipo do resp vem do requests
        if resp.status_code != 200:
            print(f"❌ Erro Shopify {resp.status_code}: {resp.text}")
            break

        produtos_json: list[dict[str, Any]] = resp.json().get("products", [])
        print(f"📄 Página {pagina_atual}: {len(produtos_json)} produtos retornados")

        for produto in produtos_json:
            id_produto_any: Any = produto.get("id")
            if id_produto_any is None:
                continue
            try:
                id_produto: int = int(id_produto_any)
            except (TypeError, ValueError):
                continue

            titulo_produto: str = str(produto.get("title", "")).strip()
            variants: list[dict[str, Any]] = produto.get("variants", []) or []

            for variante in variants:
                variant_id_any: Any = variante.get("id")
                if variant_id_any is None:
                    continue
                try:
                    variant_id: int = int(variant_id_any)
                except (TypeError, ValueError):
                    continue

                sku: str = str(variante.get("sku", "")).strip()

                todos.append(
                    ProductShopifyVariant(
                        product_id=id_produto,
                        variant_id=variant_id,
                        title=titulo_produto,
                        sku=sku,
                    )
                )

        pagina_atual += 1

        link: str = resp.headers.get("Link", "") or ""
        if 'rel="next"' in link:
            partes = link.split(",")
            next_url_parts = [p.split(";")[0].strip().strip("<>") for p in partes if 'rel="next"' in p]
            url = next_url_parts[0] if next_url_parts else None
        else:
            break

    return todos


# Função para marcar itens como processados


def processar_lineitems_shopify(df: pd.DataFrame | None) -> None:
    if df is None or df.empty:
        print("⚠️ Nenhuma planilha carregada.")
        return

    total_fulfilled: dict[str, int] = {"count": 0}
    erros: list[tuple[str, str]] = []

    pool: QThreadPool = QThreadPool.globalInstance()

    # groupby retorna (chave, DataFrame)
    for order_id_any, grupo in df.groupby("transaction_id"):
        order_id: str = str(order_id_any)

        records: list[dict[Hashable, Any]] = grupo.to_dict("records")

        planilha_line_ids: set[str] = {
            f"gid://shopify/LineItem/{int(rec['id_line_item'])}" for rec in records if rec.get("id_line_item")
        }

        runnable = FulfillPedidoRunnable(order_id, planilha_line_ids)

        def sucesso(oid: str, qtd: int) -> None:
            total_fulfilled["count"] += qtd
            print(f"✅ Pedido {oid} → {qtd} item(ns) enviados.")

        def falha(oid: str, msg: str) -> None:
            erros.append((oid, msg))
            print(f"❌ Erro no pedido {oid}: {msg}")

        runnable.signals.concluido.connect(sucesso)
        runnable.signals.erro.connect(falha)

        pool.start(runnable)

    print("🚚 Fulfillments iniciados. Acompanhe no console.")


# Cotação de fretes


def aplicar_lotes(df: pd.DataFrame, estado: dict | None = None, lote_inicial: int = 1) -> pd.DataFrame:
    df_resultado = df.copy()

    # ✅ Garante as colunas EXATAS usadas aqui (sem alias/canônico)
    requeridas = [
        "E-mail Comprador",
        "CPF/CNPJ Comprador",
        "CEP Entrega",
        "indisponivel",
        "SKU",
        "transaction_id",
        "ID Lote",
    ]
    for col in requeridas:
        if col not in df_resultado.columns:
            df_resultado[col] = ""

    # Normalizações simples
    df_resultado["ID Lote"] = df_resultado["ID Lote"].fillna("")
    if "SKU" in df_resultado.columns:
        df_resultado["SKU"] = df_resultado["SKU"].astype(str).str.strip().str.upper()

    # -- filtro de itens válidos para lote (indisponivel == "S" fora)
    mask_validos = ~df_resultado["indisponivel"].astype(str).str.upper().eq("S")
    excluidos = int((~mask_validos).sum())
    if excluidos:
        print(f"[INFO] Removendo {excluidos} item(ns) marcados como indisponíveis.")
    df_resultado = df_resultado[mask_validos].copy()

    print("\n[🚧] Atribuindo ID Lote por email + cpf + cep...")

    # 🔑 chave do lote: email + cpf + cep
    emails = df_resultado["E-mail Comprador"].fillna("").astype(str).str.lower().str.strip()
    cpfs = df_resultado["CPF/CNPJ Comprador"].fillna("").astype(str).str.replace(r"\D", "", regex=True)
    ceps = df_resultado["CEP Entrega"].fillna("").astype(str).str.replace(r"\D", "", regex=True)

    df_resultado["chave_lote"] = emails + "_" + cpfs + "_" + ceps

    # Fallbacks da chave
    mask_vazia = emails.eq("") & cpfs.eq("") & ceps.eq("")

    # se email/cpf/cep estão vazios → tenta usar transaction_id
    df_resultado.loc[mask_vazia, "chave_lote"] = df_resultado.loc[mask_vazia, "transaction_id"].astype(str).str.strip()

    # se ainda assim chave ficou vazia (ex.: transaction_id também faltando), usa o índice
    mask_ainda_vazia = df_resultado["chave_lote"].eq("")
    df_resultado.loc[mask_ainda_vazia, "chave_lote"] = df_resultado.loc[mask_ainda_vazia].index.astype(str).to_list()

    if df_resultado.empty:
        print("\n[✅] Nenhum item válido para lote/cotação após remoção dos indisponíveis.\n")
        return df_resultado.drop(columns=["chave_lote"], errors="ignore")

    agrupado = df_resultado.groupby("chave_lote", dropna=False)

    # Dados auxiliares (se existirem)
    fretes = estado.get("dados_temp", {}).get("fretes", {}) if estado else {}
    status = estado.get("dados_temp", {}).get("status_fulfillment", {}) if estado else {}
    descontos = estado.get("dados_temp", {}).get("descontos", {}) if estado else {}

    # Garante colunas de saída (vamos escrever os totais do lote nelas)
    if "Valor Frete Pedido" not in df_resultado.columns:
        df_resultado["Valor Frete Pedido"] = ""
    if "Valor Desconto Pedido" not in df_resultado.columns:
        df_resultado["Valor Desconto Pedido"] = ""
    if "Valor Frete Lote" not in df_resultado.columns:
        df_resultado["Valor Frete Lote"] = ""
    if "Valor Desconto Lote" not in df_resultado.columns:
        df_resultado["Valor Desconto Lote"] = ""

    # Evita cast repetido em loop
    df_resultado["transaction_id_str"] = df_resultado["transaction_id"].astype(str)

    lote_atual = lote_inicial

    # iterar desempacotando (chave, subdf)
    for _chave, subdf in agrupado:
        indices = list(subdf.index)
        id_lote_str = f"L{lote_atual:04d}"
        df_resultado.loc[indices, "ID Lote"] = id_lote_str

        # Calcula os totais do lote somando por pedido (partials viram 0)
        pedidos_do_lote = subdf["transaction_id_str"].unique()
        frete_total = 0.0
        desconto_total = 0.0

        for pid in pedidos_do_lote:
            pid_norm = normalizar_order_id(pid)
            status_atual = (status.get(pid_norm, "") or "").upper()
            is_partial = status_atual == "PARTIALLY_FULFILLED"

            frete_val = 0.0 if is_partial else float(fretes.get(pid_norm, 0.0) or 0.0)
            desc_val = 0.0 if is_partial else float(descontos.get(pid_norm, 0.0) or 0.0)

            frete_total += frete_val
            desconto_total += desc_val

            print(
                f"[🧾] Pedido {pid_norm} | Status: {status_atual} | Frete usado: {frete_val} | Desconto usado: {desc_val}"
            )

        # 🔁 APLICA o TOTAL DO LOTE nas colunas *Pedido* (substitui valores anteriores)
        df_resultado.loc[indices, "Valor Frete Pedido"] = f"{frete_total:.2f}".replace(".", ",")
        df_resultado.loc[indices, "Valor Desconto Pedido"] = f"{desconto_total:.2f}".replace(".", ",")

        # (opcional) mantém colunas de lote em sincronia
        df_resultado.loc[indices, "Valor Frete Lote"] = f"{frete_total:.2f}".replace(".", ",")
        df_resultado.loc[indices, "Valor Desconto Lote"] = f"{desconto_total:.2f}".replace(".", ",")

        print(
            f"🔸 {id_lote_str} → {len(indices)} item(ns) | Frete total LOTE: R$ {frete_total:.2f} | Desconto total LOTE: R$ {desconto_total:.2f}"
        )
        lote_atual += 1

    # limpeza
    df_resultado.drop(columns=["chave_lote", "transaction_id_str"], inplace=True, errors="ignore")

    # Se quiser remover as colunas de lote (já que Pedido = Lote), descomente:
    # df_resultado.drop(columns=["Valor Frete Lote", "Valor Desconto Lote"], inplace=True, errors="ignore")

    print("\n[✅] Todos os lotes atribuídos e totais aplicados nas colunas de Pedido.\n")
    return df_resultado


def padronizar_transportadora_servico(
    row: Mapping[str, Any],
) -> tuple[str, str]:
    nome_original = str(row.get("Transportadora", "")).strip().upper()

    mapeamento: dict[str, tuple[str, str]] = {
        "JET": ("JET EXPRESS BRAZIL LTDA", "jet"),
        "GOL": ("GOL LINHAS AEREAS SA", "E-GOLLOG"),
        "LOG": ("LOGGI", "loggi"),
        "COR": ("CORREIOS", "correios"),
        "GFL": ("GFL TRANSPORTES", "gfl"),
        "AZUL": ("AZUL CARGO EXPRESS", "azul"),
        "LATAM": ("LATAM CARGO", "latam"),
    }

    for chave, (nome_bling, servico_bling) in mapeamento.items():
        if chave in nome_original:
            return nome_bling, servico_bling

    return str(row.get("Transportadora", "")), str(row.get("Serviço", ""))


def gerar_payload_cotacao(
    cep: str | int,
    total_pedido: float | str,
    peso_total: float | str,
) -> dict[str, Any]:
    cep_limpo = re.sub(r"\D", "", str(cep)).zfill(8)

    return {
        "zipcode": cep_limpo,
        "amount": round(float(str(total_pedido).replace(",", ".")), 2),
        "skus": [
            {
                "sku": "B050A",  # SKU simbólico fixo
                "price": round(float(str(total_pedido).replace(",", ".")), 2),
                "quantity": 1,
                "length": 24,
                "width": 16,
                "height": 3,
                "weight": round(float(str(peso_total).replace(",", ".")), 3),
            }
        ],
    }


def cotar_fretes(
    trans_id: str | int,
    linhas: Sequence[Mapping[str, Any]],
    selecionadas: Sequence[str] | None,
) -> tuple[str, str, str, float] | None:
    """Faz a cotação de frete para um LOTE (agrupado por e-mail + CPF + CEP). 'trans_id' aqui é o
    identificador do LOTE (ex.: 'L0001'), não de transação.

    Retorna: (lote_id, nome_transportadora, servico, valor) ou None.
    """
    try:
        lote_id: str = str(trans_id).strip()

        # 0) normaliza transportadoras selecionadas
        nomes_aceitos: set[str] = {str(s).strip().upper() for s in (selecionadas or []) if str(s).strip()}
        if not nomes_aceitos:
            msg = f"Nenhuma transportadora selecionada para o lote {lote_id}."
            print(f"[⚠️] {msg}")
            with suppress(Exception):
                comunicador_global.mostrar_mensagem.emit("aviso", "Cotação de Frete", msg)
            return None

        # 1) garantir que há exatamente um ID Lote válido nas linhas
        lotes_presentes: set[str] = {str(row.get("ID Lote") or "").strip() for row in linhas}
        lotes_presentes.discard("")  # remove vazios
        if len(lotes_presentes) != 1:
            vistos = sorted(lotes_presentes) or ["nenhum"]
            msg = f"Lote inconsistente: esperava 1 ID Lote, mas encontrei {vistos}."
            print(f"[⚠️] {msg} (grupo solicitado: {lote_id})")
            with suppress(Exception):
                comunicador_global.mostrar_mensagem.emit(
                    "aviso", "Cotação de Frete", f"{msg}\nGrupo solicitado: {lote_id}"
                )
                pass
            return None

        # filtra só as linhas do lote selecionado
        linhas_validas: list[Mapping[str, Any]] = [
            row for row in linhas if str(row.get("ID Lote") or "").strip() == lote_id
        ]
        if not linhas_validas:
            print(f"[⚠️] Lote {lote_id} ignorado: nenhuma linha válida.")
            return None

        # 2) CEP (usa a primeira linha do lote)
        cep: str = str(linhas_validas[0].get("CEP Entrega") or "").strip()
        if not cep:
            msg = f"Lote {lote_id} ignorado: CEP não encontrado."
            print(f"[⚠️] {msg}")
        with suppress(Exception):
            comunicador_global.mostrar_mensagem.emit("aviso", "Cotação de Frete", msg)
            return None

        # 3) total do lote (somando itens com valor > 0; fallback por preco_fallback do SKU)
        total: float = 0.0
        for row in linhas_validas:
            try:
                valor = float(str(row.get("Valor Total", "0")).replace(",", "."))
                if valor > 0:
                    total += valor
                else:
                    sku = str(row.get("SKU", "")).strip()
                    for info in skus_info.values():  # usa skus_info global
                        if str(info.get("sku", "")).strip().upper() == sku.upper():
                            total += float(info.get("preco_fallback", 0) or 0)
                            break
            except Exception as e:
                print(f"[⚠️] Erro ao calcular valor de {row.get('Produto')}: {e}")

        # 4) peso total (somando pesos por SKU)
        peso: float = 0.0
        for row in linhas_validas:
            sku = str(row.get("SKU", "")).strip()
            achou = False
            for info in skus_info.values():
                if str(info.get("sku", "")).strip().upper() == sku.upper():
                    peso += float(info.get("peso", 0.0) or 0.0)
                    achou = True
                    break
            if not achou and sku:
                print(f"[⚠️] SKU '{sku}' não encontrado no skus_info para o lote {lote_id}")

        itens: int = len(linhas_validas)
        print(f"[🔎] Lote {lote_id} - CEP: {cep} | Itens: {itens} | Peso: {peso:.3f} kg | Total: R$ {total:.2f}")

        if total <= 0 or peso <= 0:
            msg = f"Lote {lote_id} ignorado: total ou peso inválido."
            print(f"[❌] {msg}")
            with suppress(Exception):
                comunicador_global.mostrar_mensagem.emit("aviso", "Cotação de Frete", msg)
            return None

        # 5) cotação (API/formatos já corretos segundo seu ambiente)
        payload: dict[str, Any] = gerar_payload_cotacao(cep, total, peso)

        # 💡 Substituição: http_post com retries/backoff e respeito a 429/5xx
        try:
            r = http_post(
                settings.FRETEBARATO_URL,
                headers={"Content-Type": "application/json"},
                json=payload,
                timeout=(5, 30),  # mesmo padrão do DEFAULT_TIMEOUT
            )
        except ExternalError as e:
            print(f"[❌] Lote {lote_id}: falha ao chamar FreteBarato ({e.code}) - retryable={e.retryable}")
            return None

        data: dict[str, Any] = r.json()
        quotes_raw = data.get("quotes", []) or []
        quotes: list[Mapping[str, Any]] = quotes_raw if isinstance(quotes_raw, list) else []  # robustez de tipo
        print(f"[📦] Lote {lote_id} - {len(quotes)} cotações recebidas")

        # filtra por transportadoras selecionadas
        opcoes: list[Mapping[str, Any]] = [q for q in quotes if str(q.get("name", "")).strip().upper() in nomes_aceitos]
        print(f"[🔎] Lote {lote_id} - {len(opcoes)} compatíveis com selecionadas: {sorted(nomes_aceitos)}")

        if not opcoes:
            print(f"[⚠️] Lote {lote_id} - Nenhum frete aceito pelas transportadoras selecionadas.")
            return None

        melhor = sorted(opcoes, key=lambda x: float(x.get("price", 0) or 0))[0]
        print(
            f"[✅] Lote {lote_id} - Frete: {melhor['name']} ({melhor.get('service','')}) - R$ {float(melhor['price']):.2f}"
        )
        return (
            lote_id,
            str(melhor["name"]),
            str(melhor.get("service", "")),
            float(melhor["price"]),
        )

    except Exception as e:
        print(f"[❌] Erro ao cotar frete para lote {trans_id}: {e}")
        return None


class HasIsChecked(Protocol):
    def isChecked(self) -> bool: ...


def iniciar_cotacao_fretes(
    estado: MutableMapping[str, Any],
    transportadoras_var: Mapping[str, HasIsChecked],
    barra_progresso_frete: QProgressBar,
) -> None:
    print("[🧪 estado id dentro da cotação]:", id(estado))

    df = estado.get("df_planilha_parcial")
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhuma planilha carregada para cotação de frete.")
        return

    # 🔎 Transportadoras selecionadas
    selecionadas: list[str] = [k for k, var in transportadoras_var.items() if var.isChecked()]
    if not selecionadas:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhuma transportadora selecionada.")
        return

    print("[🧪 FRETES]", estado.get("dados_temp", {}).get("fretes", {}))
    print("[🧪 STATUS]", estado.get("dados_temp", {}).get("status_fulfillment", {}))
    if "transaction_id" in df.columns:
        print("[🧪 ID transações planilha]", df["transaction_id"].unique())

    # 🔁 (Re)atribui ID Lote antes de cotar
    df = aplicar_lotes(df, cast(dict[Any, Any], estado))
    estado["df_planilha_parcial"] = df
    print("[⚙️] ID Lote atribuído antes da cotação.")

    # Agrupa por lote (apenas lotes válidos, não vazios)
    pedidos_por_lote: dict[str, list[dict[str, Any]]] = {}
    for _, linha in df.iterrows():
        lote = str(linha.get("ID Lote") or "").strip()
        if lote:
            pedidos_por_lote.setdefault(lote, []).append(linha.to_dict())

    ids_lotes: list[tuple[str, list[dict[str, Any]]]] = list(pedidos_por_lote.items())
    total: int = len(ids_lotes)
    fretes_aplicados: list[tuple[str, str, float]] = []

    print(f"[📦] Iniciando cotação de {total} lotes.")
    barra_progresso_frete.setVisible(True)
    barra_progresso_frete.setMaximum(total)
    barra_progresso_frete.setValue(0)

    def processar_proxima(index: int = 0) -> None:
        if index >= total:
            barra_progresso_frete.setVisible(False)
            estado["df_planilha_parcial"] = df

            if fretes_aplicados:
                resumo = "📦 Médias de frete por transportadora/serviço:\n\n"
                agrupados: dict[str, list[float]] = {}
                total_fretes: float = 0.0

                for nome, servico, valor in fretes_aplicados:
                    chave = f"{nome} - {servico}"
                    agrupados.setdefault(chave, []).append(valor)
                    total_fretes += valor

                for chave, valores in agrupados.items():
                    media = sum(valores) / len(valores)
                    resumo += f"{chave}: R$ {media:.2f} ({len(valores)} pedidos)\n"

                resumo += f"\n💰 Custo total de fretes: R$ {total_fretes:.2f}"
                comunicador_global.mostrar_mensagem.emit("info", "✅ Cotações finalizadas", resumo)
            else:
                comunicador_global.mostrar_mensagem.emit(
                    "info", "✅ Cotações finalizadas", "Nenhum frete foi aplicado."
                )
            return

        lote_id, linhas = ids_lotes[index]
        print(f"[🌀] Cotando lote {lote_id} com {len(linhas)} item(ns)")

        resultado = cotar_fretes(lote_id, linhas, selecionadas)
        if resultado:
            # resultado esperado: (lote_id, nome_transportadora, nome_servico, valor_frete, ...)
            nome_transportadora, nome_servico, valor_frete = resultado[1:]
            fretes_aplicados.append((nome_transportadora, nome_servico, float(valor_frete)))

            # Atualiza diretamente no DataFrame para todo o lote
            df.loc[df["ID Lote"] == lote_id, "Transportadora"] = nome_transportadora
            df.loc[df["ID Lote"] == lote_id, "Serviço"] = nome_servico
        else:
            print(f"[⚠️] Lote {lote_id} não teve frete aplicado.")

        barra_progresso_frete.setValue(index + 1)
        QApplication.processEvents()
        QTimer.singleShot(100, lambda: processar_proxima(index + 1))

    processar_proxima()


# Visualização de planilhas e logs na interface


class VisualizadorPlanilha(QDialog):
    def __init__(
        self,
        df: pd.DataFrame,
        estado: MutableMapping[str, Any] | None = None,
        caminho_log: str | PathLike[str] | None = None,
    ) -> None:
        super().__init__()
        self.setWindowTitle("📋 Visualizador de Planilha")
        self.setMinimumSize(1000, 600)

        self.df: pd.DataFrame = df.copy()
        if "Cupom" not in self.df.columns:
            # garantir coluna existirá como string
            self.df["Cupom"] = ""

        self.estado: MutableMapping[str, Any] | None = estado
        self.caminho_log: str | PathLike[str] | None = caminho_log

        layout: QVBoxLayout = QVBoxLayout(self)

        # 🔍 Campo de busca
        linha_busca: QHBoxLayout = QHBoxLayout()
        linha_busca.addWidget(QLabel("🔎 Buscar:"))
        self.campo_busca: QLineEdit = QLineEdit()
        linha_busca.addWidget(self.campo_busca)
        layout.addLayout(linha_busca)
        self.campo_busca.textChanged.connect(self.filtrar_tabela)

        # 📋 Tabela
        self.tabela: QTableWidget = QTableWidget()
        self.tabela.setColumnCount(len(self.df.columns))
        self.tabela.setRowCount(len(self.df))
        self.tabela.setHorizontalHeaderLabels(self.df.columns.astype(str).tolist())
        self.tabela.setEditTriggers(QAbstractItemView.DoubleClicked)
        self.tabela.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.tabela.setAlternatingRowColors(True)
        self.tabela.setSortingEnabled(True)

        # preencher células
        nlin: int = len(self.df)
        _ncol: int = len(self.df.columns)
        for i in range(nlin):
            for j, col in enumerate(list(self.df.columns)):
                valor: str = str(self.df.iloc[i, j])
                item: QTableWidgetItem = QTableWidgetItem(valor)
                if col in ["Data", "Data Pedido"]:
                    try:
                        dt = datetime.strptime(valor, "%d/%m/%Y").replace(tzinfo=TZ_APP)
                        item.setData(int(Qt.UserRole), dt)
                    except Exception:
                        pass
                self.tabela.setItem(i, j, item)

        self.tabela.resizeColumnsToContents()
        layout.addWidget(self.tabela)

        # ⌨️ Atalho DELETE para remover linhas com confirmação
        atalho_delete: QShortcut = QShortcut(QKeySequence(int(Qt.Key_Delete)), self.tabela)
        atalho_delete.activated.connect(self.remover_linhas_selecionadas)

        # 🔘 Botões
        linha_botoes: QHBoxLayout = QHBoxLayout()

        btn_remover: QPushButton = QPushButton("🗑️ Remover linha selecionada")
        btn_remover.clicked.connect(self.remover_linhas_selecionadas)
        linha_botoes.addWidget(btn_remover)

        btn_salvar: QPushButton = QPushButton("💾 Salvar alterações")
        btn_salvar.clicked.connect(self.salvar_edicoes)
        linha_botoes.addWidget(btn_salvar)

        layout.addLayout(linha_botoes)

        self.showMaximized()

    def filtrar_tabela(self) -> None:
        termo: str = self.campo_busca.text().lower().strip()
        for row in range(self.tabela.rowCount()):
            mostrar = False
            for col in range(self.tabela.columnCount()):
                item = self.tabela.item(row, col)
                if item and termo in item.text().lower():
                    mostrar = True
                    break
            self.tabela.setRowHidden(row, not mostrar)

    def remover_linhas_selecionadas(self) -> None:
        # selectedIndexes() -> Sequence[QModelIndex]; convertemos para set de ints
        idxs: Sequence[QModelIndex] = self.tabela.selectedIndexes()
        linhas: list[int] = sorted({idx.row() for idx in idxs}, reverse=True)
        if not linhas:
            return

        resposta: int = QMessageBox.question(
            self,
            "Confirmar remoção",
            f"Deseja realmente remover {len(linhas)} linha(s) selecionada(s)?",
            QMessageBox.Yes | QMessageBox.No,
        )

        if resposta == QMessageBox.Yes:
            for linha in linhas:
                self.tabela.removeRow(linha)

    def salvar_edicoes(self) -> None:
        nova_df_rows: list[list[str]] = []
        for i in range(self.tabela.rowCount()):
            linha_vals: list[str] = []
            for j in range(self.tabela.columnCount()):
                item = self.tabela.item(i, j)
                linha_vals.append(item.text() if item else "")
            nova_df_rows.append(linha_vals)

        self.df = pd.DataFrame(nova_df_rows, columns=self.df.columns)

        if self.caminho_log:
            try:
                with open(self.caminho_log, "w", encoding="utf-8") as f:
                    json.dump(self.df.to_dict(orient="records"), f, ensure_ascii=False, indent=2)
                comunicador_global.mostrar_mensagem.emit("info", "Sucesso", "Alterações salvas no log.")
            except Exception as e:
                comunicador_global.mostrar_mensagem.emit("erro", "Erro", f"Falha ao salvar alterações:\n{e!s}")
        else:
            comunicador_global.mostrar_mensagem.emit(
                "info", "Alterações salvas", "Alterações salvas na planilha em memória."
            )

        if self.estado is not None:
            self.estado["df_planilha_parcial"] = self.df.copy()

        self.accept()


def editar_planilha(estado: MutableMapping[str, Any]) -> None:
    df = estado.get("df_planilha_parcial")
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit("info", "Aviso", "Nenhuma planilha carregada.")
        return

    dialog = VisualizadorPlanilha(df)
    if dialog.exec_():
        estado["df_planilha_parcial"] = dialog.df.copy()


def exibir_planilha(df: pd.DataFrame | None) -> None:
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhuma planilha carregada.")
        return
    VisualizadorPlanilha(df).exec_()


# Processamento e exportação da planilha para o Bling


def abrir_no_sistema(path: str) -> None:
    if sys.platform.startswith("win"):
        os.startfile(path)
    elif sys.platform == "darwin":
        subprocess.Popen(["open", path])
    else:
        subprocess.Popen(["xdg-open", path])


def exportar_planilha_bling() -> None:
    # estado.get() retorna Any -> cast p/ Optional[pd.DataFrame]
    df: pd.DataFrame | None = cast(pd.DataFrame | None, estado.get("df_planilha_parcial"))

    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro", "Nenhuma planilha parcial carregada.")
        return

    # QFileDialog.getSaveFileName -> Tuple[str, str]
    caminho: str
    _filtro: str
    caminho, _filtro = cast(
        tuple[str, str],
        QFileDialog.getSaveFileName(None, "Salvar Planilha", "", "Planilhas Excel (*.xlsx)"),
    )

    if caminho:
        # salvar_planilha_bling é sua função existente
        salvar_planilha_bling(df, caminho)


def resetar_planilha() -> None:
    resposta: int = QMessageBox.question(
        None,
        "Confirmação",
        "Deseja realmente limpar os dados da planilha?",
        QMessageBox.Yes | QMessageBox.No,
    )

    if resposta == QMessageBox.Yes:
        estado["linhas_planilha"] = []
        estado["df_planilha_parcial"] = pd.DataFrame()
        estado["transacoes_obtidas"] = False

        if "tabela_widget" in estado and estado["tabela_widget"] is not None:
            # deixe claro p/ o mypy que é um QTableWidget
            tabela = cast(QTableWidget, estado["tabela_widget"])
            tabela.setRowCount(0)

        comunicador_global.mostrar_mensagem.emit("info", "Limpo", "Planilha foi limpa.")


def gerar_pdf_producao_logistica(
    df: pd.DataFrame,  # tabela de dados
    data_envio: date | datetime | str,  # aceita date/datetime/str
    bimestre: int,  # 1..6
    ano: int,  # ex.: 2025
    caminho_planilha: str | PathLike[str],  # caminho/Path
) -> None:
    # 🔁 Agrupa os produtos por Número pedido (pedido final)
    agrupado: dict[str, int] = {}

    # mypy-friendly: descompacta o groupby
    for _chave, grupo_df in df.groupby("Número pedido"):
        # grupo_df: pd.DataFrame
        produtos = grupo_df["Produto"].dropna().tolist()
        produtos = [p.strip() for p in produtos if isinstance(p, str) and p.strip()]
        if not produtos:
            continue
        chave = " + ".join(sorted(produtos))
        agrupado.setdefault(chave, 0)
        agrupado[chave] += 1

    # 📊 Contagem total por produto individual
    produtos_totais: Counter[str] = Counter()
    for conjunto, qtd in agrupado.items():
        for produto in conjunto.split(" + "):
            produtos_totais[produto] += qtd

    # 🔎 Normaliza data_envio para algo com .strftime (sempre datetime aware no TZ_APP)
    if isinstance(data_envio, str):
        try:
            # 1) tenta ISO (com ou sem tz)
            dt = datetime.fromisoformat(data_envio)
        except ValueError:
            try:
                # 2) tenta parsing flexível (dd/mm/yyyy, etc.) já existente no projeto
                dt = parse_date(data_envio, dayfirst=True)
            except Exception:
                # 3) fallback: agora local (aware)
                data_envio_dt = local_now()
            else:
                data_envio_dt = ensure_aware_local(dt)
        else:
            data_envio_dt = ensure_aware_local(dt)
    elif isinstance(data_envio, date) and not isinstance(data_envio, datetime):
        # veio só date → transforma em LOCAL-aware 00:00
        data_envio_dt = aware_local(data_envio.year, data_envio.month, data_envio.day)
    else:
        # já é datetime → garante que esteja local-aware
        data_envio_dt = ensure_aware_local(data_envio)

    # 🧾 Caminho do PDF
    nome_arquivo = f"{data_envio_dt.strftime('%d%m%Y')}_logos_resumo_logistica_{bimestre}_{ano}.pdf"
    pasta_destino = os.path.dirname(os.fspath(caminho_planilha))
    caminho_pdf = os.path.join(pasta_destino, nome_arquivo)

    # 🖨️ Criação do PDF
    pdf = FPDF()
    pdf.add_page()
    pdf.set_font("Arial", "B", 14)
    pdf.cell(0, 10, "Editora Logos - Logística", ln=True, align="C")
    pdf.set_font("Arial", "", 12)
    pdf.cell(
        0,
        10,
        f"Resumo de Produção - {data_envio_dt.strftime('%d/%m/%Y')} - {bimestre}/{ano}",
        ln=True,
        align="C",
    )
    pdf.ln(10)

    # 📦 Total por produto individual
    pdf.set_font("Arial", "B", 12)
    pdf.cell(0, 10, "Total por Produto Individual:", ln=True)
    pdf.set_font("Arial", "", 11)
    for produto, qtd in produtos_totais.items():
        pdf.cell(0, 8, f"{qtd} x {produto}", ln=True)

    # 📦 Total por conjunto de produtos (pedido)
    pdf.ln(6)
    pdf.set_font("Arial", "B", 12)
    pdf.cell(0, 10, "Total por Conjunto de Produtos (Pedido):", ln=True)
    pdf.set_font("Arial", "", 11)
    for conjunto, qtd in agrupado.items():
        pdf.cell(0, 8, f"{qtd} x {conjunto}", ln=True)

    # 🎁 Produtos extras por cupom
    produtos_extras = df[df["Valor Total"] == "0,00"]
    if not produtos_extras.empty:
        pdf.ln(10)
        pdf.set_font("Arial", "B", 12)
        pdf.cell(0, 10, "Produtos Extras por Cupom (R$ 0,00):", ln=True)
        pdf.set_font("Arial", "", 11)

        contagem_extras = produtos_extras["Produto"].value_counts()
        for nome_produto, qtd in contagem_extras.items():
            pdf.cell(0, 8, f"{qtd} x {nome_produto}", ln=True)

    # 💾 Salva e abre
    pdf.output(caminho_pdf)
    abrir_no_sistema(caminho_pdf)


def salvar_planilha_bling(df: pd.DataFrame, output_path: str) -> None:
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro", "Nenhuma planilha foi carregada.")
        return

    df_final = df.copy()

    # Garante colunas usadas adiante
    if "Transportadora" not in df_final.columns:
        df_final["Transportadora"] = ""
    if "Serviço" not in df_final.columns:
        df_final["Serviço"] = ""
    if "Produto" not in df_final.columns:
        df_final["Produto"] = ""

    # Agrupa produtos por lote (se houver ID Lote)
    df_final["Produto"] = df_final["Produto"].astype(str).str.strip()
    df_final["Transportadora"] = df_final["Transportadora"].astype(str).str.strip()

    if "ID Lote" in df_final.columns:
        grupos = (
            df_final.groupby("ID Lote")["Produto"]
            .apply(lambda x: " + ".join(sorted(set(map(str, x)))))
            .rename("Conjunto Produtos")
        )
        df_final = df_final.merge(grupos, on="ID Lote", how="left")
    else:
        df_final["Conjunto Produtos"] = ""

    # Ordena: Transportadora > Conjunto > Nome
    if "Nome Comprador" in df_final.columns:
        df_final.sort_values(by=["Transportadora", "Conjunto Produtos", "Nome Comprador"], inplace=True)
    else:
        df_final.sort_values(by=["Transportadora", "Conjunto Produtos"], inplace=True)

    # Numeração por lote (se houver)
    if "ID Lote" in df_final.columns:
        parent = QApplication.activeWindow() or QWidget()
        numero_inicial, ok = QInputDialog.getInt(
            parent, "Número Inicial", "Informe o número inicial do pedido:", value=8000, min=1
        )
        if not ok:
            return

        df_final["Número pedido"] = ""
        lotes_ordenados = (
            df_final[["ID Lote", "Transportadora", "Conjunto Produtos"]]
            .drop_duplicates()
            .sort_values(by=["Transportadora", "Conjunto Produtos"])
            .reset_index(drop=True)
        )
        unique_lotes = lotes_ordenados["ID Lote"].tolist()
        mapa_lotes = {lote: numero_inicial + i for i, lote in enumerate(unique_lotes)}
        df_final["Número pedido"] = df_final["ID Lote"].map(mapa_lotes)
    else:
        df_final["Número pedido"] = ""

    # Converte valores e calcula Total Pedido
    # Aceita tanto entradas com vírgula quanto floats; evita quebrar se já for número
    if df_final["Valor Total"].dtype != "float64" and df_final["Valor Total"].dtype != "int64":
        df_final["Valor Total"] = df_final["Valor Total"].astype(str).str.replace(",", ".", regex=False)
    df_final["Valor Total"] = pd.to_numeric(df_final["Valor Total"], errors="coerce")

    # Máscara para pedidos válidos (nem NaN nem "")
    tem_pedido_valido = df_final["Número pedido"].notna() & df_final["Número pedido"].astype(str).str.strip().ne("")

    if tem_pedido_valido.any():
        # soma por pedido apenas nas linhas válidas
        total_por_pedido = (
            df_final.loc[tem_pedido_valido]
            .groupby("Número pedido", sort=False)["Valor Total"]
            .sum()
            .reset_index(name="Total Pedido")
        )

        # Evita coluna duplicada antes de mesclar
        if "Total Pedido" in df_final.columns:
            df_final.drop(columns=["Total Pedido"], inplace=True, errors="ignore")

        df_final = pd.merge(df_final, total_por_pedido, on="Número pedido", how="left")
    else:
        df_final["Total Pedido"] = pd.NA

    # Aviso sobre frete ausente (não bloqueia exportação)
    faltando_frete = df_final[
        df_final["Transportadora"].isnull()
        | df_final["Transportadora"].eq("")
        | df_final["Serviço"].isnull()
        | df_final["Serviço"].eq("")
    ]
    if not faltando_frete.empty:
        comunicador_global.mostrar_mensagem.emit(
            "aviso",
            "Aviso: pedidos sem frete",
            f"{len(faltando_frete)} item(ns) estão sem frete cotado. Eles serão exportados mesmo assim.",
        )

    # >>> A PARTIR DAQUI, FORMATAÇÃO APENAS PARA EXIBIÇÃO/EXPORTAÇÃO <<<
    # Mantém números como floats; se quiser saída com vírgula para o Excel apenas visualmente,
    # use formatos no Excel ou formate aqui em string (mas isso vira texto no arquivo).
    # Abaixo mantém como string com vírgula (se você realmente precisar assim):
    df_final["Valor Total"] = df_final["Valor Total"].map(
        lambda x: f"{x:.2f}".replace(".", ",") if pd.notnull(x) else ""
    )
    df_final["Total Pedido"] = df_final["Total Pedido"].map(
        lambda x: f"{x:.2f}".replace(".", ",") if pd.notnull(x) else ""
    )

    # PDF (usa periodo/ano de ultimo_log; se não houver, fallback)
    try:
        df_para_pdf = df_final.copy()
        data_envio_str = df_para_pdf["Data"].dropna().iloc[0]
        data_envio = datetime.strptime(data_envio_str, "%d/%m/%Y").replace(tzinfo=TZ_APP)

        raw_info = estado.get("ultimo_log") if isinstance(estado, dict) else None
        info = cast(dict[str, Any], raw_info or {})
        periodo = info.get("periodo", info.get("bimestre", 1))
        ano_pdf = info.get("ano", data_envio.year)
        gerar_pdf_producao_logistica(df_para_pdf, data_envio, periodo, ano_pdf, output_path)
    except Exception as e:
        print(f"[⚠️] Erro ao gerar PDF: {e}")

    # Reposiciona Total Pedido após Valor Total
    colunas = df_final.columns.tolist()
    if "Total Pedido" in colunas and "Valor Total" in colunas:
        colunas.remove("Total Pedido")
        idx = colunas.index("Valor Total") + 1
        colunas.insert(idx, "Total Pedido")
        df_final = df_final[colunas]

    # Padroniza frete
    df_final[["Transportadora", "Serviço"]] = df_final.apply(
        lambda row: pd.Series(padronizar_transportadora_servico(row)), axis=1
    )

    estado["df_planilha_exportada"] = df_final.copy()

    # Remove colunas internas antes de exportar
    colunas_remover = ["Conjunto Produtos", "ID Lote", "indisponivel"]
    df_para_exportar = df_final.drop(columns=colunas_remover, errors="ignore")

    try:
        df_para_exportar.to_excel(output_path, index=False)
        comunicador_global.mostrar_mensagem.emit("info", "Sucesso", f"Planilha exportada para:\n{output_path}")
    except Exception as e:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro ao salvar", f"{e}")


# Interface para edição de produtos.


def gerar_chave_assinatura(nome: str, periodicidade: str) -> str:
    """
    Gera a chave única de uma assinatura no formato
    "<nome> - <periodicidade>", garantindo fallback seguro.
    """
    p = (periodicidade or "").strip().lower()
    if p not in ("mensal", "bimestral"):
        p = "bimestral"  # fallback
    return f"{nome.strip()} - {p}"


def abrir_editor_produtos(box_nome_input: QComboBox | None = None) -> None:
    estado.setdefault("skus_info", {})
    skus_info: MutableMapping[str, Any] = cast(MutableMapping[str, Any], estado["skus_info"])
    dialog: QDialog = QDialog()
    dialog.setWindowTitle("Editor de SKUs")
    dialog.setGeometry(100, 100, 1100, 650)
    layout: QVBoxLayout = QVBoxLayout(dialog)

    tabs: QTabWidget = QTabWidget()
    tab_produtos: QWidget = QWidget()
    tab_assinaturas: QWidget = QWidget()
    tab_combos: QWidget = QWidget()
    tab_brindes: QWidget = QWidget()  # ← NOVO

    # 📦 Produtos
    tabela_prod: QTableWidget = QTableWidget()
    tabela_prod.setColumnCount(7)
    tabela_prod.setHorizontalHeaderLabels(
        ["Nome", "SKU", "Peso", "Guru IDs", "Shopify IDs", "Preço Fallback", "Indisp."]
    )

    # 📬 Assinaturas
    tabela_assin: QTableWidget = QTableWidget()
    tabela_assin.setColumnCount(6)
    tabela_assin.setHorizontalHeaderLabels(
        ["Nome", "Duração", "Periodicidade", "Guru IDs", "Preço Fallback", "Indisp."]
    )

    # 📚 Combos
    tabela_combo: QTableWidget = QTableWidget()
    tabela_combo.setColumnCount(8)  # + "Divisor"
    tabela_combo.setHorizontalHeaderLabels(
        ["Nome", "SKU", "Composto de", "Guru IDs", "Shopify IDs", "Preço Fallback", "Divisor", "Indisp."]
    )

    # 🎁 Brindes (simples: Nome, SKU, Observações, Guru IDs, Shopify IDs, Indisp.)
    tabela_brinde: QTableWidget = QTableWidget()
    tabela_brinde.setColumnCount(6)
    tabela_brinde.setHorizontalHeaderLabels(["Nome", "SKU", "Observações", "Guru IDs", "Shopify IDs", "Indisp."])

    for tabela in [tabela_prod, tabela_assin, tabela_combo, tabela_brinde]:
        header = tabela.horizontalHeader()
        if header is not None:
            header.setSectionResizeMode(QHeaderView.Stretch)

    layout_prod: QVBoxLayout = QVBoxLayout(tab_produtos)
    layout_prod.addWidget(tabela_prod)
    layout_assin: QVBoxLayout = QVBoxLayout(tab_assinaturas)
    layout_assin.addWidget(tabela_assin)
    layout_combo: QVBoxLayout = QVBoxLayout(tab_combos)
    layout_combo.addWidget(tabela_combo)
    layout_brinde: QVBoxLayout = QVBoxLayout(tab_brindes)
    layout_brinde.addWidget(tabela_brinde)

    def _mk_checkbox(checked: bool = False) -> QCheckBox:
        cb: QCheckBox = QCheckBox()
        cb.setChecked(bool(checked))
        cb.setStyleSheet("margin-left: 8px;")  # só pra ficar bonitinho
        return cb

    def _get_checkbox(table: QTableWidget, row: int, col: int) -> bool:
        w = table.cellWidget(row, col)
        return bool(w.isChecked()) if isinstance(w, QCheckBox) else False

    # util: formatar composto_de para exibição (combos)
    def _fmt_composto(raw: Any) -> str:
        if isinstance(raw, str):
            parts: list[Any] = [s.strip() for s in re.split(r"[;,]", raw) if s.strip()]
        elif isinstance(raw, list):
            parts = raw
        else:
            parts = []
        out: list[str] = []
        for c in parts:
            if isinstance(c, str):
                out.append(c.strip())
            elif isinstance(c, dict):
                sku_c = str(c.get("sku") or c.get("SKU") or "").strip()
                try:
                    q = int(c.get("qtd") or c.get("quantity") or 1)
                except Exception:
                    q = 1
                out.append(f"{sku_c} x {q}" if q != 1 else sku_c)
        return ", ".join([s for s in out if s])

    # util: parse da string da coluna "Composto de" para lista normalizada (combos)
    def _parse_composto_to_list(composto_str: str) -> list[dict[str, Any] | str]:
        itens: list[dict[str, Any] | str] = []
        tokens = [s.strip() for s in re.split(r"[;,]", composto_str) if s.strip()]
        for tok in tokens:
            m = re.match(r"^\s*([A-Za-z0-9._\-]+)\s*(?:[xX\*]\s*(\d+))?\s*$", tok)
            if m:
                sku = m.group(1).strip()
                qtd = int(m.group(2)) if m.group(2) else 1
                itens.append({"sku": sku, "qtd": max(1, qtd)})
            else:
                itens.append(tok)  # fallback
        return itens

    # Funções para adicionar nova linha
    def adicionar_produto() -> None:
        row: int = tabela_prod.rowCount()
        tabela_prod.insertRow(row)
        for col in range(6):
            tabela_prod.setItem(row, col, QTableWidgetItem(""))
        tabela_prod.setCellWidget(row, 6, _mk_checkbox(False))  # Indisp.

    def adicionar_assinatura() -> None:
        row: int = tabela_assin.rowCount()
        tabela_assin.insertRow(row)
        for col in range(5):
            tabela_assin.setItem(row, col, QTableWidgetItem(""))
        tabela_assin.setCellWidget(row, 5, _mk_checkbox(False))  # Indisp.

    def adicionar_combo() -> None:
        row: int = tabela_combo.rowCount()
        tabela_combo.insertRow(row)
        for col in range(7):  # inclui "Divisor" na posição 6
            tabela_combo.setItem(row, col, QTableWidgetItem(""))
        tabela_combo.setCellWidget(row, 7, _mk_checkbox(False))  # Indisp.

    def adicionar_brinde() -> None:
        row: int = tabela_brinde.rowCount()
        tabela_brinde.insertRow(row)
        for col in range(5):  # até Shopify IDs
            tabela_brinde.setItem(row, col, QTableWidgetItem(""))
        tabela_brinde.setCellWidget(row, 5, _mk_checkbox(False))  # Indisp.

    # 🧹 Funções para remover linha selecionada
    def remover_produto() -> None:
        row: int = tabela_prod.currentRow()
        if row >= 0:
            tabela_prod.removeRow(row)

    def remover_assinatura() -> None:
        row: int = tabela_assin.currentRow()
        if row >= 0:
            tabela_assin.removeRow(row)

    def remover_combo() -> None:
        row: int = tabela_combo.currentRow()
        if row >= 0:
            tabela_combo.removeRow(row)

    def remover_brinde() -> None:
        row: int = tabela_brinde.currentRow()
        if row >= 0:
            tabela_brinde.removeRow(row)

    # 📦 Botões Produtos
    layout_botoes_prod: QHBoxLayout = QHBoxLayout()
    btn_novo_prod: QPushButton = QPushButton("+ Novo Produto")
    btn_novo_prod.clicked.connect(adicionar_produto)
    btn_remover_prod: QPushButton = QPushButton("🗑️ Remover Selecionado")
    btn_remover_prod.clicked.connect(remover_produto)
    layout_botoes_prod.addWidget(btn_novo_prod)
    layout_botoes_prod.addWidget(btn_remover_prod)
    layout_prod.addLayout(layout_botoes_prod)

    # 📬 Botões Assinaturas
    layout_botoes_assin: QHBoxLayout = QHBoxLayout()
    btn_nova_assin: QPushButton = QPushButton("+ Nova Assinatura")
    btn_nova_assin.clicked.connect(adicionar_assinatura)
    btn_remover_assin: QPushButton = QPushButton("🗑️ Remover Selecionado")
    btn_remover_assin.clicked.connect(remover_assinatura)
    layout_botoes_assin.addWidget(btn_nova_assin)
    layout_botoes_assin.addWidget(btn_remover_assin)
    layout_assin.addLayout(layout_botoes_assin)

    # 📚 Botões Combos
    layout_botoes_combo: QHBoxLayout = QHBoxLayout()
    btn_novo_combo: QPushButton = QPushButton("+ Novo Combo")
    btn_novo_combo.clicked.connect(adicionar_combo)
    btn_remover_combo: QPushButton = QPushButton("🗑️ Remover Selecionado")
    btn_remover_combo.clicked.connect(remover_combo)
    layout_botoes_combo.addWidget(btn_novo_combo)
    layout_botoes_combo.addWidget(btn_remover_combo)
    layout_combo.addLayout(layout_botoes_combo)

    # 🎁 Botões Brindes
    layout_botoes_brinde: QHBoxLayout = QHBoxLayout()
    btn_novo_brinde: QPushButton = QPushButton("+ Novo Brinde")
    btn_novo_brinde.clicked.connect(adicionar_brinde)
    btn_remover_brinde: QPushButton = QPushButton("🗑️ Remover Selecionado")
    btn_remover_brinde.clicked.connect(remover_brinde)
    layout_botoes_brinde.addWidget(btn_novo_brinde)
    layout_botoes_brinde.addWidget(btn_remover_brinde)
    layout_brinde.addLayout(layout_botoes_brinde)

    tabs.addTab(tab_produtos, "📦 Produtos")
    tabs.addTab(tab_assinaturas, "📬 Assinaturas")
    tabs.addTab(tab_combos, "📚 Combos")
    tabs.addTab(tab_brindes, "🎁 Brindes")  # ← NOVO
    layout.addWidget(tabs)

    def carregar_skus() -> dict[str, Any]:
        if os.path.exists(skus_path):
            with open(skus_path, encoding="utf-8") as f:
                return cast(dict[str, Any], json.load(f))
        return {}

    def preencher_tabelas(skus_dict: dict[str, Any]) -> None:
        tabela_prod.setRowCount(0)
        tabela_assin.setRowCount(0)
        tabela_combo.setRowCount(0)
        tabela_brinde.setRowCount(0)

        for nome, info in skus_dict.items():
            tipo = str(info.get("tipo", "")).lower()

            # ASSINATURAS
            if tipo == "assinatura":
                row = tabela_assin.rowCount()
                tabela_assin.insertRow(row)

                nome_base: str = nome.split(" - ")[0]
                periodicidade: str = info.get("periodicidade") or (nome.split(" - ")[1] if " - " in nome else "")

                tabela_assin.setItem(row, 0, QTableWidgetItem(nome_base))
                tabela_assin.setItem(row, 1, QTableWidgetItem(info.get("recorrencia", "")))
                tabela_assin.setItem(row, 2, QTableWidgetItem(periodicidade))
                tabela_assin.setItem(row, 3, QTableWidgetItem(", ".join(info.get("guru_ids", []))))
                tabela_assin.setItem(row, 4, QTableWidgetItem(str(info.get("preco_fallback", ""))))
                tabela_assin.setCellWidget(row, 5, _mk_checkbox(bool(info.get("indisponivel", False))))

            # COMBOS
            elif tipo == "combo":
                row = tabela_combo.rowCount()
                tabela_combo.insertRow(row)

                comp_str = _fmt_composto(info.get("composto_de") or [])
                guru_ids = info.get("guru_ids") or []
                if not isinstance(guru_ids, list):
                    guru_ids = [guru_ids]
                guru_str = ", ".join(str(x) for x in guru_ids if x is not None)

                shopify_ids = info.get("shopify_ids") or []
                if not isinstance(shopify_ids, list):
                    shopify_ids = [shopify_ids]
                shopify_str = ", ".join(str(x) for x in shopify_ids if x is not None)

                divisor_val = info.get("divisor", "")
                divisor_str = "" if divisor_val in (None, "") else str(divisor_val)

                tabela_combo.setItem(row, 0, QTableWidgetItem(nome))
                tabela_combo.setItem(row, 1, QTableWidgetItem(info.get("sku", "")))
                tabela_combo.setItem(row, 2, QTableWidgetItem(comp_str))
                tabela_combo.setItem(row, 3, QTableWidgetItem(guru_str))
                tabela_combo.setItem(row, 4, QTableWidgetItem(shopify_str))
                tabela_combo.setItem(row, 5, QTableWidgetItem(str(info.get("preco_fallback", ""))))
                tabela_combo.setItem(row, 6, QTableWidgetItem(divisor_str))
                tabela_combo.setCellWidget(row, 7, _mk_checkbox(bool(info.get("indisponivel", False))))

            # BRINDES
            elif tipo == "brinde":
                row = tabela_brinde.rowCount()
                tabela_brinde.insertRow(row)

                obs = str(info.get("obs", ""))  # campo livre opcional
                guru_ids = info.get("guru_ids") or []
                if not isinstance(guru_ids, list):
                    guru_ids = [guru_ids]
                guru_str = ", ".join(str(x) for x in guru_ids if x is not None)

                shopify_ids = info.get("shopify_ids") or []
                if not isinstance(shopify_ids, list):
                    shopify_ids = [shopify_ids]
                shopify_str = ", ".join(str(x) for x in shopify_ids if x is not None)

                tabela_brinde.setItem(row, 0, QTableWidgetItem(nome))
                tabela_brinde.setItem(row, 1, QTableWidgetItem(info.get("sku", "")))
                tabela_brinde.setItem(row, 2, QTableWidgetItem(obs))
                tabela_brinde.setItem(row, 3, QTableWidgetItem(guru_str))
                tabela_brinde.setItem(row, 4, QTableWidgetItem(shopify_str))
                tabela_brinde.setCellWidget(row, 5, _mk_checkbox(bool(info.get("indisponivel", False))))

            # PRODUTOS
            else:
                row = tabela_prod.rowCount()
                tabela_prod.insertRow(row)
                tabela_prod.setItem(row, 0, QTableWidgetItem(nome))
                tabela_prod.setItem(row, 1, QTableWidgetItem(info.get("sku", "")))
                tabela_prod.setItem(row, 2, QTableWidgetItem(str(info.get("peso", 0.0))))
                tabela_prod.setItem(row, 3, QTableWidgetItem(", ".join(info.get("guru_ids", []))))
                tabela_prod.setItem(row, 4, QTableWidgetItem(", ".join(str(i) for i in info.get("shopify_ids", []))))
                tabela_prod.setItem(row, 5, QTableWidgetItem(str(info.get("preco_fallback", ""))))
                tabela_prod.setCellWidget(row, 6, _mk_checkbox(bool(info.get("indisponivel", False))))

    def salvar_tabelas() -> None:
        skus: dict[str, Any] = {}

        # --- PRODUTOS ---
        for row in range(tabela_prod.rowCount()):

            def get(col: int, _row: int = row) -> str:
                item = tabela_prod.item(_row, col)
                return item.text().strip() if item else ""

            nome, sku, peso_str, guru, shopify, preco_str = map(get, range(6))
            if not nome:
                continue

            try:
                peso: float = float(peso_str)
            except (ValueError, TypeError):
                peso = 0.0

            try:
                preco_p: float | None = float(preco_str) if preco_str else None
            except (ValueError, TypeError):
                preco_p = None

            skus[nome] = {
                "sku": sku,
                "peso": peso,
                "guru_ids": [x.strip() for x in guru.split(",") if x.strip()],
                "shopify_ids": [int(x.strip()) for x in shopify.split(",") if x.strip().isdigit()],
                "tipo": "produto",
                "composto_de": [],
                "indisponivel": _get_checkbox(tabela_prod, row, 6),
            }
            if preco_p is not None:
                skus[nome]["preco_fallback"] = preco_p

        # --- ASSINATURAS ---
        for row in range(tabela_assin.rowCount()):

            def get(col: int, _row: int = row) -> str:
                item = tabela_assin.item(_row, col)
                return item.text().strip() if item else ""

            nome_base, recorrencia, periodicidade, guru, preco_str = map(get, range(5))
            if not nome_base:
                continue

            key: str = gerar_chave_assinatura(nome_base, periodicidade)

            try:
                preco_a: float | None = float(preco_str) if preco_str else None
            except (ValueError, TypeError):
                preco_a = None

            guru_ids: list[str] = [x.strip() for x in guru.split(",") if x.strip()]

            skus[key] = {
                "tipo": "assinatura",
                "recorrencia": recorrencia,
                "periodicidade": periodicidade,
                "guru_ids": guru_ids,
                "shopify_ids": [],
                "composto_de": [],
                "sku": "",
                "peso": 0.0,
                "indisponivel": _get_checkbox(tabela_assin, row, 5),
            }
            if preco_a is not None:
                skus[key]["preco_fallback"] = preco_a

        # --- COMBOS ---
        for row in range(tabela_combo.rowCount()):

            def get(col: int, _row: int = row) -> str:
                item = tabela_combo.item(_row, col)
                return item.text().strip() if item else ""

            # Agora lendo 7 colunas de texto (0..6) para capturar também o divisor
            nome, sku, composto, guru, shopify, preco_str, divisor_str = map(get, range(7))
            if not nome:
                continue

            try:
                preco_c: float | None = float(preco_str) if preco_str else None
            except (ValueError, TypeError):
                preco_c = None

            # divisor opcional (>=1), se inválido → ignorado (fallback p/ contagem de não-brindes)
            try:
                divisor: int | None = int(divisor_str) if divisor_str else None
                if divisor is not None and divisor < 1:
                    divisor = None
            except (ValueError, TypeError):
                divisor = None

            skus[nome] = {
                "sku": sku,
                "peso": 0.0,
                "tipo": "combo",
                "composto_de": _parse_composto_to_list(composto),
                "guru_ids": [x.strip() for x in guru.split(",") if x.strip()],
                "shopify_ids": [int(x.strip()) for x in shopify.split(",") if x.strip().isdigit()],
                "indisponivel": _get_checkbox(tabela_combo, row, 7),
            }
            if preco_c is not None:
                skus[nome]["preco_fallback"] = preco_c
            if divisor is not None:
                skus[nome]["divisor"] = divisor  # <— NOVO

        # --- BRINDES ---
        for row in range(tabela_brinde.rowCount()):

            def get(col: int, _row: int = row) -> str:
                item = tabela_brinde.item(_row, col)
                return item.text().strip() if item else ""

            nome, sku, obs, guru, shopify = map(get, range(5))
            if not nome:
                continue

            skus[nome] = {
                "tipo": "brinde",
                "sku": sku,
                "obs": obs,  # campo livre opcional
                "peso": 0.0,  # normalmente irrelevante p/ brinde
                "guru_ids": [x.strip() for x in guru.split(",") if x.strip()],
                "shopify_ids": [int(x.strip()) for x in shopify.split(",") if x.strip().isdigit()],
                "composto_de": [],
                "indisponivel": _get_checkbox(tabela_brinde, row, 5),
            }

        with open(skus_path, "w", encoding="utf-8") as f:
            json.dump(skus, f, indent=4, ensure_ascii=False)

        skus_info.clear()
        skus_info.update(skus)

        if box_nome_input:
            box_nome_input.clear()
            box_nome_input.addItems(sorted(skus.keys()))

        QMessageBox.information(dialog, "Sucesso", "SKUs salvos com sucesso!")

    # Botão salvar
    botoes: QHBoxLayout = QHBoxLayout()
    btn_salvar: QPushButton = QPushButton("💾 Salvar SKUs")
    btn_salvar.clicked.connect(salvar_tabelas)
    botoes.addWidget(btn_salvar)
    layout.addLayout(botoes)

    skus_dict: dict[str, Any] = carregar_skus()
    preencher_tabelas(skus_dict)
    dialog.exec_()


# Montar PDF de auxílio com XMLs


def obter_nfes_zip(caminho_zip: str, pasta_destino: str = "/tmp/xmls_extraidos") -> list[str]:
    """Extrai arquivos .xml de um ZIP para a pasta destino e retorna os caminhos extraídos."""
    # Limpa a pasta antes de extrair
    if os.path.exists(pasta_destino):
        shutil.rmtree(pasta_destino)
    os.makedirs(pasta_destino)

    with zipfile.ZipFile(caminho_zip, "r") as zip_ref:
        nomes_extraidos: list[str] = [
            zip_ref.extract(nome, path=pasta_destino) for nome in zip_ref.namelist() if nome.endswith(".xml")
        ]
    return nomes_extraidos


def ler_dados_nfes(
    caminho_xml: str,
) -> tuple[str | None, str | None, str | None, list[str]]:
    """Lê dados essenciais de uma NF-e em XML.

    Retorna: (nNF, xNome, transportadora, produtos)
    """
    try:
        tree = ET.parse(caminho_xml)
        root = tree.getroot()
        ns = {"nfe": "http://www.portalfiscal.inf.br/nfe"}
        infNFe = root.find(".//nfe:infNFe", ns)

        nNF: str | None = infNFe.findtext("nfe:ide/nfe:nNF", namespaces=ns) if infNFe else None
        xNome: str | None = infNFe.findtext("nfe:dest/nfe:xNome", namespaces=ns) if infNFe else None
        xNomeTransportadora: str | None = (
            infNFe.findtext("nfe:transp/nfe:transporta/nfe:xNome", namespaces=ns) if infNFe else None
        ) or "Sem Transportadora"

        produtos: list[str] = []
        if infNFe is not None:
            for det in infNFe.findall("nfe:det", ns):
                xProd = det.findtext("nfe:prod/nfe:xProd", namespaces=ns)
                if xProd:
                    produtos.append(xProd.strip())

        return nNF, xNome, xNomeTransportadora, produtos

    except Exception as e:
        print(f"Erro ao processar {caminho_xml}: {e}")
        return None, None, None, []


def organizar_nfes_por_transportadora(
    lista_xml: Sequence[str],
) -> dict[str, dict[str, dict[str, Any]]]:
    """{ transportadora: { nNF: {"xNome": str, "produtos": list[str]} } }"""
    agrupado: dict[str, dict[str, dict[str, Any]]] = defaultdict(
        lambda: defaultdict(lambda: {"xNome": "", "produtos": []})
    )

    for caminho in lista_xml:
        nNF, xNome, transportadora, produtos = ler_dados_nfes(caminho)  # nNF/transportadora podem ser None
        # garanta chaves válidas:
        if not nNF or not transportadora:
            continue

        nome_dest = xNome or ""  # xNome pode ser None -> converte para str
        produtos = produtos or []  # segurança (já é list[str], mas evita None acidental)

        agrupado[transportadora][nNF]["xNome"] = nome_dest
        agrupado[transportadora][nNF]["produtos"].extend(produtos)

    return agrupado


def salvar_pdfs_nfes_producao(
    dados_por_transportadora: Mapping[str, Mapping[str, dict[str, Any]]],
    pasta_destino: str = "/tmp/pdfs_por_transportadora",
) -> list[str]:
    os.makedirs(pasta_destino, exist_ok=True)
    caminhos: list[str] = []

    for transportadora, notas in dados_por_transportadora.items():
        # Sanitizar nome para nome de arquivo
        nome_arquivo = f"{transportadora.replace(' ', '_').replace('/', '-')}.pdf"
        caminho_pdf = os.path.join(pasta_destino, nome_arquivo)

        c = canvas.Canvas(caminho_pdf, pagesize=A4)
        _largura, altura = A4
        margem_sup = 10 * mm
        margem_inf = 10 * mm
        y = altura - margem_sup

        for nNF, dados in sorted(notas.items()):
            if y < margem_inf + 25 * mm:
                c.showPage()
                y = altura - margem_sup

            c.setFont("Helvetica-Bold", 10)
            c.drawString(15 * mm, y, f"NF {nNF} - Destinatário: {dados['xNome']}")
            y -= 5 * mm

            c.setFont("Helvetica", 9)
            for produto in dados["produtos"]:
                if y < margem_inf + 10 * mm:
                    c.showPage()
                    y = altura - margem_sup
                c.drawString(20 * mm, y, f"- 1x {produto}")
                y -= 4 * mm

            y -= 5 * mm  # espaço entre NF-es

        c.save()
        caminhos.append(caminho_pdf)

    return caminhos


def gerar_pdfs_nfes_producao(estado: MutableMapping[str, Any]) -> None:
    try:
        # QFileDialog.getOpenFileName -> tuple[str, str]
        caminho_zip_tuple: tuple[str, str] = QFileDialog.getOpenFileName(
            None, "Selecionar Arquivo ZIP", "", "ZIP Files (*.zip)"
        )
        caminho_zip: str = caminho_zip_tuple[0]
        if not caminho_zip:
            return

        # Se suas funções já têm tipos melhores, troque Sequence/Mapping por eles
        lista_xmls: Sequence[str] = cast(Sequence[str], obter_nfes_zip(caminho_zip))

        dados_agrupados: Mapping[str, Any] = cast(Mapping[str, Any], organizar_nfes_por_transportadora(lista_xmls))
        # Se você pretende mutar depois em outro lugar, materializa como dict
        estado["dados_agrupados_nfe"] = dict(dados_agrupados)

        # QFileDialog.getExistingDirectory -> str
        pasta_pdf: str = cast(str, QFileDialog.getExistingDirectory(None, "Selecionar pasta para salvar os PDFs"))
        if not pasta_pdf:
            return

        pdfs_gerados: Sequence[str] = cast(Sequence[str], salvar_pdfs_nfes_producao(dados_agrupados, pasta_pdf))

        if not pdfs_gerados:
            QMessageBox.information(None, "Aviso", "Nenhum PDF foi gerado.")
            return

        # Tenta abrir a pasta de destino (sem quebrar se falhar)
        try:
            if platform.system() == "Darwin":
                subprocess.run(["open", pasta_pdf], check=False)
            elif platform.system() == "Windows":
                abrir_no_sistema(pasta_pdf)
            else:
                subprocess.run(["xdg-open", pasta_pdf], check=False)
        except Exception as e:
            QMessageBox.warning(None, "Aviso", f"PDFs gerados, mas não foi possível abrir a pasta.\nErro: {e}")

    except Exception as e:
        QMessageBox.critical(None, "Erro ao processar XMLs", str(e))


# Design da interface


def criar_grupo_guru(
    estado: MutableMapping[str, Any],
    skus_info: Mapping[str, MutableMapping[str, Any]],
    transportadoras_var: Any,
) -> QGroupBox:
    group = QGroupBox("Digital Manager Guru")
    group.setObjectName("grupo_guru")
    group.setAttribute(QtCore.Qt.WidgetAttribute.WA_StyledBackground, True)

    outer_layout = QVBoxLayout(group)
    inner_widget = QWidget()
    layout = QVBoxLayout(inner_widget)
    layout.setContentsMargins(0, 0, 0, 0)

    # 🗓️ Filtros
    linha_filtros = QHBoxLayout()
    ano_spin = QSpinBox()
    ano_spin.setRange(2020, 2035)
    ano_spin.setValue(QDate.currentDate().year())
    linha_filtros.addWidget(QLabel("Ano:"))
    linha_filtros.addWidget(ano_spin)

    combo_mes = QComboBox()
    combo_mes.addItems([str(i) for i in range(1, 13)])
    combo_mes.setCurrentIndex(QDate.currentDate().month() - 1)
    linha_filtros.addWidget(QLabel("Mês:"))
    linha_filtros.addWidget(combo_mes)

    combo_periodicidade = QComboBox()
    combo_periodicidade.addItems(["mensal", "bimestral"])
    linha_filtros.addWidget(QLabel("Periodicidade:"))
    linha_filtros.addWidget(combo_periodicidade)

    combo_filtro = QComboBox()
    combo_filtro.addItems(["PERÍODO", "TODAS"])
    linha_filtros.addWidget(QLabel("Tipo:"))
    linha_filtros.addWidget(combo_filtro)
    layout.addLayout(linha_filtros)

    # 📦 Box - apenas produtos simples (nao-assinatura e nao-composto)
    produtos_simples = [
        nome
        for nome, info in skus_info.items()
        if info.get("tipo") != "assinatura"
        and not info.get("composto_de")
        and not info.get("indisponivel", False)  # ← NOVO
    ]
    box_nome_input = QComboBox()
    box_nome_input.addItems(sorted(produtos_simples))
    linha_box = QHBoxLayout()
    linha_box.addWidget(QLabel("📦 Box do Período:"))
    linha_box.addWidget(box_nome_input)
    layout.addLayout(linha_box)

    # 🔘 Botões principais
    linha_botoes = QHBoxLayout()
    btn_buscar_assinaturas = QPushButton("🔍 Buscar Assinaturas")
    btn_buscar_produtos = QPushButton("🔍 Buscar Produtos")
    btn_importar = QPushButton("📥 Importar do Guru")
    linha_botoes.addWidget(btn_buscar_assinaturas)
    linha_botoes.addWidget(btn_buscar_produtos)
    linha_botoes.addWidget(btn_importar)
    layout.addLayout(linha_botoes)

    # 🔗 Conexões
    btn_buscar_assinaturas.clicked.connect(
        lambda: iniciar_busca_assinaturas(
            ano_spin.value(),
            int(combo_mes.currentText()),
            combo_filtro.currentText(),  # "PERÍODO" ou "TODAS"
            box_nome_input,
            transportadoras_var,
            estado,
            skus_info,
            periodicidade_selecionada=combo_periodicidade.currentText().strip().lower(),
        )
    )

    btn_importar.clicked.connect(importar_planilha_pedidos_guru)

    # 🔁 Ações de visualização que permanecem aqui
    linha_acoes_guru = QHBoxLayout()
    layout.addLayout(linha_acoes_guru)

    # ⚙️ Regras & mapeamentos (mantém aqui)
    linha_config = QHBoxLayout()

    btn_rules = QPushButton("⚙️ Gerenciar Regras")
    btn_rules.clicked.connect(lambda: iniciar_gerenciador_regras(estado, skus_info))
    linha_config.addWidget(btn_rules)

    def recarregar_regras_assinaturas() -> None:
        try:
            config_path = os.path.join(os.path.dirname(__file__), "config_ofertas.json")
            regras: list[dict[str, Any]] = []
            if os.path.exists(config_path):
                with open(config_path, encoding="utf-8") as f:
                    cfg = json.load(f)
                    regras = cfg.get("rules") or cfg.get("regras") or []
            if isinstance(regras, list):
                estado["rules"] = regras
                comunicador_global.mostrar_mensagem.emit("info", "Regras", "Regras recarregadas.")
            else:
                comunicador_global.mostrar_mensagem.emit("aviso", "Regras", "Arquivo sem lista de regras.")
        except Exception as e:
            comunicador_global.mostrar_mensagem.emit("erro", "Regras", f"Falha ao recarregar: {e}")

    btn_reload_rules = QPushButton("↺ Recarregar Regras")
    btn_reload_rules.clicked.connect(recarregar_regras_assinaturas)
    linha_config.addWidget(btn_reload_rules)

    skus_path = Path(os.path.join(os.path.dirname(__file__), "skus.json"))

    btn_mapear_guru = QPushButton("🔗 Mapear produtos do Guru")
    btn_mapear_guru.clicked.connect(
        lambda: iniciar_mapeamento_produtos_guru(skus_info, coletar_produtos_guru(), skus_path)
    )
    linha_config.addWidget(btn_mapear_guru)

    btn_editar = QPushButton("✏️ Editar Produtos")
    btn_editar.clicked.connect(lambda: abrir_editor_produtos(None))
    linha_config.addWidget(btn_editar)

    layout.addLayout(linha_config)

    btn_buscar_produtos.clicked.connect(
        lambda: iniciar_coleta_vendas_produtos(box_nome_input, transportadoras_var, skus_info, estado)
    )

    outer_layout.addWidget(inner_widget)
    return group


def criar_grupo_shopify(
    estado: MutableMapping[str, Any],
    skus_info: Mapping[str, MutableMapping[str, Any]],
) -> QGroupBox:
    group = QGroupBox("🛒 Shopify")
    group.setObjectName("grupo_shopify")
    group.setAttribute(QtCore.Qt.WidgetAttribute.WA_StyledBackground, True)

    outer_layout = QVBoxLayout(group)
    inner_widget = QWidget()
    layout = QVBoxLayout(inner_widget)
    layout.setContentsMargins(0, 0, 0, 0)

    # Widgets
    linha1 = QHBoxLayout()
    entrada_data_inicio = QDateEdit()
    entrada_data_inicio.setCalendarPopup(True)
    entrada_data_inicio.setDate(QDate.currentDate().addDays(-7))
    linha1.addWidget(QLabel("Data de início da busca:"))
    linha1.addWidget(entrada_data_inicio)

    combo_status = QComboBox()
    combo_status.addItems(["any", "unfulfilled"])
    combo_status.setCurrentText("any")
    linha1.addWidget(QLabel("Status:"))
    linha1.addWidget(combo_status)
    layout.addLayout(linha1)

    linha2 = QHBoxLayout()
    check_produto = QCheckBox("Deseja buscar um produto específico?")
    combo_produto = QComboBox()
    combo_produto.addItems(sorted([n for n, i in skus_info.items() if not i.get("indisponivel", False)]))
    combo_produto.setVisible(False)
    check_produto.stateChanged.connect(lambda val: combo_produto.setVisible(bool(val)))
    linha2.addWidget(QLabel("Produto:"))
    linha2.addWidget(check_produto)
    linha2.addWidget(combo_produto)
    layout.addLayout(linha2)

    # Botões
    linha_btns = QHBoxLayout()

    # 🔗 NOVO: Mapear produtos da loja (ficará na seção Shopify)
    btn_mapear_shopify = QPushButton("🔗 Mapear produtos da loja")
    btn_mapear_shopify.clicked.connect(lambda: iniciar_mapeamento_produtos_shopify(skus_info))
    linha_btns.addWidget(btn_mapear_shopify)

    btn_buscar = QPushButton("🔍 Buscar pedidos da loja")
    btn_fulfill = QPushButton("📝 Marcar como processados")
    linha_btns.addWidget(btn_buscar)
    linha_btns.addWidget(btn_fulfill)
    layout.addLayout(linha_btns)

    # Salva widgets no estado
    estado["entrada_data_inicio"] = entrada_data_inicio
    estado["combo_status"] = combo_status
    estado["combo_produto"] = combo_produto
    estado["check_produto"] = check_produto

    # Conecta ao fluxo externo
    btn_buscar.clicked.connect(lambda: acionar_coleta_pedidos_shopify(estado))
    btn_fulfill.clicked.connect(
        lambda: (
            processar_lineitems_shopify(estado.get("df_planilha_exportada"))
            if estado.get("df_planilha_exportada") is not None and not estado["df_planilha_exportada"].empty
            else comunicador_global.mostrar_mensagem.emit("erro", "Erro", "Você deve exportar a planilha antes.")
        )
    )

    outer_layout.addWidget(inner_widget)
    return group


def criar_grupo_fretes(
    estado: MutableMapping[str, Any],
    transportadoras_var: Any,
) -> QGroupBox:
    group = QGroupBox("🚚 Cotação de Fretes")
    group.setObjectName("grupo_fretes")
    group.setAttribute(QtCore.Qt.WidgetAttribute.WA_StyledBackground, True)

    outer_layout = QVBoxLayout(group)

    inner_widget = QWidget()
    layout = QVBoxLayout(inner_widget)
    layout.setContentsMargins(0, 0, 0, 0)

    linha_transportadoras = QHBoxLayout()
    nomes = ["GOL", "LOG", "GFL", "JET", "COR"]
    for nome in nomes:
        cb = QCheckBox(nome)
        cb.setChecked(nome in ["GOL", "JET"])
        transportadoras_var[nome] = cb
        linha_transportadoras.addWidget(cb)
    layout.addLayout(linha_transportadoras)

    barra_progresso = QProgressBar()
    barra_progresso.setVisible(False)
    layout.addWidget(barra_progresso)

    btn_cotar = QPushButton("🚚 Cotar Agora")
    btn_cotar.clicked.connect(lambda: iniciar_cotacao_fretes(estado, transportadoras_var, barra_progresso))
    layout.addWidget(btn_cotar)

    outer_layout.addWidget(inner_widget)
    return group


def criar_grupo_controle(estado: MutableMapping[str, Any]) -> QGroupBox:
    group = QGroupBox("📋 Controle e Registro")
    group.setObjectName("grupo_exportacao")
    group.setAttribute(QtCore.Qt.WidgetAttribute.WA_StyledBackground, True)

    outer_layout = QVBoxLayout(group)

    inner_widget = QWidget()
    layout = QVBoxLayout(inner_widget)
    layout.setContentsMargins(0, 0, 0, 0)

    # - Visualização -
    linha_visualizacao = QHBoxLayout()

    btn_ver_planilha = QPushButton("✏️ Editar Planilha Parcial")
    btn_ver_planilha.clicked.connect(lambda: editar_planilha(estado))
    linha_visualizacao.addWidget(btn_ver_planilha)

    btn_filtrar_enviados = QPushButton("🧲 Filtrar enviados")
    btn_filtrar_enviados.clicked.connect(remover_pedidos_enviados)
    linha_visualizacao.addWidget(btn_filtrar_enviados)

    layout.addLayout(linha_visualizacao)

    # - Registro e complementos -
    linha_registros = QHBoxLayout()

    btn_registrar = QPushButton("📝 Registrar Envios")
    btn_registrar.clicked.connect(
        lambda: (
            iniciar_registro_envios()
            if QMessageBox.question(
                None,
                "Confirmar Registro",
                "Deseja realmente adicionar esses pedidos ao registro de envios?",
                QMessageBox.Yes | QMessageBox.No,
            )
            == QMessageBox.Yes
            else None
        )
    )
    linha_registros.addWidget(btn_registrar)

    btn_importar_envios = QPushButton("📥 Registrar envios por planilha")
    btn_importar_envios.clicked.connect(registrar_envios_planilha_guru)
    linha_registros.addWidget(btn_importar_envios)

    btn_adicionar_brindes = QPushButton("📄 Adicionar Brindes do Comercial")
    btn_adicionar_brindes.clicked.connect(lambda: importar_brindes_comercial(estado.get("skus_info", {})))
    linha_registros.addWidget(btn_adicionar_brindes)

    layout.addLayout(linha_registros)

    # - Exportação e limpeza -
    linha_export = QHBoxLayout()

    btn_obter_planilha = QPushButton("💾 Exportar Planilha")
    btn_obter_planilha.clicked.connect(lambda: exportar_planilha_bling())
    linha_export.addWidget(btn_obter_planilha)

    btn_zip = QPushButton("📁 Selecionar ZIP de NF-es")
    btn_zip.clicked.connect(lambda: gerar_pdfs_nfes_producao(estado))
    linha_export.addWidget(btn_zip)

    btn_resetar_planilha = QPushButton("🗑️ Limpar Planilha")
    btn_resetar_planilha.clicked.connect(resetar_planilha)
    linha_export.addWidget(btn_resetar_planilha)

    layout.addLayout(linha_export)

    outer_layout.addWidget(inner_widget)
    return group


def abrir_interface(
    estado: MutableMapping[str, Any],
    skus_info: MutableMapping[str, MutableMapping[str, Any]],
) -> None:
    for info in skus_info.values():
        info.setdefault("indisponivel", False)
    estado["skus_info"] = skus_info

    app = QApplication.instance()
    if not isinstance(app, QApplication):
        app = QApplication([])

    app.setStyleSheet(
        """
        QWidget { font-family: 'Segoe UI', sans-serif; font-size: 11pt; }
        QGroupBox { border: 1px solid #ccc; border-radius: 8px; margin-top: 10px; }
        QGroupBox::title { subcontrol-origin: margin; subcontrol-position: top left; padding: 0 10px; font-weight: bold; color: #333; }
        QPushButton { background-color: #e0e7ff; border: 1px solid #aab; border-radius: 6px; padding: 6px 12px; }
        QPushButton:hover { background-color: #cdd9ff; }
        QComboBox, QSpinBox, QDateEdit, QTextEdit, QLineEdit { background-color: #ffffff; border: 1px solid #ccc; border-radius: 4px; padding: 4px; }

        /* Estilo por seção */
        QGroupBox#grupo_guru { background-color: #fff1dc; border: 1px solid #e0b97e; border-radius: 8px; margin-top: 10px; }
        QGroupBox#grupo_shopify { background-color: #e8f4fc; border: 1px solid #a5c8e2; border-radius: 8px; margin-top: 10px; }
        QGroupBox#grupo_fretes { background-color: #f4f4f4; border: 1px solid #bbbbbb; border-radius: 8px; margin-top: 10px; }
        QGroupBox#grupo_exportacao { background-color: #f0ffe0; border: 1px solid #bbddaa; border-radius: 8px; margin-top: 10px; }
    """
    )

    janela = QWidget()
    janela.setWindowTitle("Editora Logos: Sistema de Logística v1")
    largura = 800
    altura = 700
    tela = QDesktopWidget().availableGeometry().center()
    janela.setGeometry(0, 0, largura, altura)
    janela.move(tela.x() - largura // 2, tela.y() - altura // 2)
    estado["janela_principal"] = janela
    estado["cancelador_global"] = (
        estado.get("cancelador_global")
        if isinstance(estado.get("cancelador_global"), threading.Event)
        else threading.Event()
    )
    estado.setdefault("linhas_planilha", [])
    estado.setdefault("transacoes_obtidas", False)

    # 🔽 Carrega regras do config_ofertas.json (novo formato)
    try:
        config_path = os.path.join(os.path.dirname(__file__), "config_ofertas.json")
        if os.path.exists(config_path):
            with open(config_path, encoding="utf-8") as f:
                cfg = json.load(f)
                regras = cfg.get("rules") or cfg.get("regras") or []
                if isinstance(regras, list):
                    estado["rules"] = regras
    except Exception as e:
        print(f"[⚠️ ERRO ao carregar rules do config_ofertas.json]: {e}")

    if not isinstance(estado.get("rules"), list):
        estado["rules"] = []

    layout_principal = QVBoxLayout(janela)

    # Agora tudo fica na principal:
    layout_principal.addWidget(criar_grupo_guru(estado, skus_info, transportadoras_var))
    layout_principal.addWidget(criar_grupo_shopify(estado, skus_info))
    layout_principal.addWidget(criar_grupo_fretes(estado, transportadoras_var))
    layout_principal.addWidget(criar_grupo_controle(estado))

    janela.show()
    app.exec_()


def run_gui() -> int:
    """
    Inicializa a interface gráfica garantindo logging e correlation_id.
    Usa o mesmo arquivo de log configurado globalmente (%LOCALAPPDATA%\\lg-logistica\\Logs\\sistema.log).
    """
    logger = logging.getLogger("gui")

    # Se o logging ainda não foi configurado (fallback)
    if not logger.handlers:
        from common.logging_setup import setup_logging

        log_file = default_log_file()
        setup_logging(level=logging.INFO, json_console=True, file_path=str(log_file))
        logger.info("logging inicializado manualmente (fallback)", extra={"log_file": str(log_file)})

    # Gera um id único por execução (para rastreamento no log)
    set_correlation_id()

    logger.info("abrindo interface gráfica")
    abrir_interface(estado, skus_info)
    return 0


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


@safe_cli
def main(argv: list[str] | None = None) -> int:
    """
    Entry point com tratamento de erros padronizado pelo @safe_cli.

    - GUI (padrão): abre a interface
    - CLI: recebe JSON inline ou arquivo .json com a configuração
    """

    parser = argparse.ArgumentParser(
        prog="lg-logistica",
        description="Aplicação de logística (GUI por padrão; CLI opcional).",
    )
    parser.add_argument(
        "--mode",
        choices=["gui", "cli"],
        default="gui",
        help="Modo de execução: gui (padrão) ou cli.",
    )
    parser.add_argument(
        "--config",
        help="(CLI) JSON inline ou caminho para arquivo .json com a configuração.",
    )
    parser.add_argument(
        "--debug",
        action="store_true",
        help="Mostra detalhes de erro (equivalente a DEBUG=1).",
    )

    args = parser.parse_args(argv)

    # apenas gera um correlation_id (logging já é configurado via sitecustomize)
    from common.logging_setup import set_correlation_id

    set_correlation_id()

    logger = logging.getLogger("main")
    logger.info("modo de execução", extra={"mode": args.mode})

    # ------------------ GUI ------------------
    if args.mode == "gui":
        return run_gui()

    # ------------------ CLI ------------------
    if not args.config:
        raise UserError(
            "Uso (CLI): --mode cli --config '<json>' | --config caminho/para/config.json",
            code="USAGE",
        )

    payload = _load_payload_from_arg(args.config)
    cfg = validate_config(payload)
    ensure_paths(cfg)

    # log básico confirmando config válida
    logger.info("config CLI validada", extra={"output_dir": cfg.output_dir})

    # placeholder: executar orquestrador, se existir
    # from app.runner import run_from_cfg
    # return int(run_from_cfg(cfg) or 0)

    # provisório: apenas confirmar
    print(f"OK (CLI): output_dir={cfg.output_dir} (dry_run={cfg.dry_run})")
    return 0


if __name__ == "__main__":
    # importante: agora passamos SEMPRE pelo safe_cli
    raise SystemExit(main())

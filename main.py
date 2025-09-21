# Imports da biblioteca padrão
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
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timedelta
from decimal import ROUND_HALF_UP, Decimal, InvalidOperation
from functools import partial
from json import JSONDecodeError
from threading import Event
from uuid import uuid4

import certifi
import openai
import pandas as pd
import requests
import urllib3
from brazilcep import exceptions, get_address_from_cep
from colorama import init
from dateutil.parser import parse as parse_date
from fpdf import FPDF
from openai import RateLimitError
from PyQt5.QtCore import (
    QCoreApplication,
    QDate,
    QObject,
    QRunnable,
    Qt,
    QThread,
    QThreadPool,
    QTimer,
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

from common.cli_safe import safe_cli
from common.errors import ExternalError, UserError
from common.http_client import http_get, http_post
from common.logging_setup import get_correlation_id, set_correlation_id, setup_logging
from common.settings import settings
from common.validation import ensure_paths, validate_config

init(autoreset=True)

os.environ["SSL_CERT_FILE"] = certifi.where()
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

BASE_URL_GURU = "https://digitalmanager.guru/api/v2"
HEADERS_GURU = {
    "Authorization": f"Bearer {settings.API_KEY_GURU}",
    "Content-Type": "application/json",
}

# ===================== CONFIGURAÇÕES =====================


class Comunicador(QObject):
    mostrar_mensagem = pyqtSignal(str, str, str)
    atualizar_progresso = pyqtSignal(str, int, int)


comunicador_global = Comunicador()


def run_gui() -> int:
    # ativa JSON no console e também loga no arquivo existente
    setup_logging(
        level=logging.INFO, json_console=True, file_path=os.path.join(caminho_base(), "sistema.log")
    )
    set_correlation_id()  # gera um id para essa execução
    abrir_interface(estado, skus_info)
    return 0


def _load_payload_from_arg(value: str) -> dict:
    """
    Aceita JSON inline OU caminho para arquivo .json/.yaml/.yml contendo a config.
    Se for caminho, tentamos carregar; caso contrário, tratamos como JSON string.
    """
    import json
    import os

    try:
        # caminho de arquivo?
        if os.path.exists(value):
            # suporte básico a JSON; se quiser YAML, adicione pyyaml aqui depois
            with open(value, encoding="utf-8") as f:
                txt = f.read()
            try:
                return json.loads(txt)
            except json.JSONDecodeError as e:
                raise UserError(
                    "Arquivo de configuração não é JSON válido",
                    code="BAD_JSON_FILE",
                    data={"path": value},
                ) from e
        # JSON inline
        return json.loads(value)
    except json.JSONDecodeError as e:
        raise UserError("JSON inválido em --config", code="BAD_JSON", data={"value": value}) from e


@safe_cli
def main(argv: list[str] | None = None) -> int:
    """
    Entry point F-I-N-O com tratamento de erros padronizado pelo cli_safe.
    - Modo padrão: GUI
    - Modo CLI: valida entrada e executa orquestração (quando existir)
    """
    import argparse

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

    # inicia logging e correlation id
    setup_logging(
        level=logging.INFO, json_console=True, file_path=os.path.join(caminho_base(), "sistema.log")
    )
    set_correlation_id()

    if args.mode == "gui":
        return run_gui()

    # --- CLI ---
    if not args.config:
        raise UserError(
            "Uso (CLI): --mode cli --config '<json>' | --config caminho/para/config.json",
            code="USAGE",
        )

    payload = _load_payload_from_arg(args.config)
    cfg = validate_config(payload)
    ensure_paths(cfg)

    # caso você já tenha um orquestrador (vamos criar no Passo 3/4):
    # from app.runner import run_from_cfg
    # return int(run_from_cfg(cfg) or 0)

    # provisório: confirme a entrada válida e retorne sucesso
    print(f"OK (CLI): {cfg.input_path} -> {cfg.output_dir} (dry_run={cfg.dry_run})")
    return 0


def slot_mostrar_mensagem(tipo, titulo, texto):
    msg = QMessageBox()
    if tipo == "erro":
        msg.setIcon(QMessageBox.Critical)
    elif tipo == "info":
        msg.setIcon(QMessageBox.Information)
    else:
        msg.setIcon(QMessageBox.Warning)
    msg.setWindowTitle(titulo)
    msg.setText(texto)
    msg.exec_()


comunicador_global.mostrar_mensagem.connect(slot_mostrar_mensagem)


def caminho_base():
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(__file__)


limite_gpt = threading.Semaphore(4)

controle_rate_limit = {"lock": threading.Lock(), "ultimo_acesso": time.time()}

log_path = os.path.join(caminho_base(), "sistema.log")

# 🔄 Formato comum
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

dados = {}
estado = {
    "transacoes_obtidas": False,
    "linhas_planilha": [],
    "numero_pedido_bling": None,
    "skus_info": {},
    "cancelador_global": threading.Event(),
}
linhas_planilha = []
total_etapas = 0
progresso_total = 0
transacoes_obtidas = False
transportadoras_var = {}
transportadoras_lista = ["CORREIOS", "GFL", "GOL", "JET", "LOG"]
skus_path = os.path.join(caminho_base(), "skus.json")
janela_progresso = None
texto_label = None
barra_progresso = None
transacoes = []
enderecos_para_revisar = []  # ← Lista global

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

# Mapear produtos do Guru


def buscar_todos_produtos_guru():
    url = f"{BASE_URL_GURU}/products"
    headers = HEADERS_GURU
    produtos = []
    cursor = None
    pagina = 1

    while True:
        try:
            params = {"limit": 100}
            if cursor:
                params["cursor"] = cursor

            r = http_get(url, headers=headers, params=params, timeout=10)
            if r.status_code != 200:
                print(f"[❌ Guru] Erro {r.status_code} ao buscar produtos: {r.text}")
                break

            data = r.json()
            pagina_dados = data.get("data", [])
            print(f"[📄 Página {pagina}] {len(pagina_dados)} produtos encontrados")

            produtos += pagina_dados
            cursor = data.get("next_cursor")

            if not cursor:
                break

            pagina += 1

        except Exception as e:
            print(f"[❌ Guru] Exceção ao buscar produtos: {e}")
            break

    print(f"[✅ Guru] Total de produtos carregados: {len(produtos)}")
    return produtos


def mapear_skus_com_produtos_guru(skus_info):
    produtos_guru = buscar_todos_produtos_guru()
    if not produtos_guru:
        QMessageBox.warning(None, "Erro", "Nenhum produto retornado do Guru.")
        return
    abrir_dialogo_mapeamento_guru(skus_info, produtos_guru, skus_path)


def abrir_dialogo_mapeamento_guru(skus_info, produtos_guru, skus_path):
    class DialogoMapeamento(QDialog):
        def __init__(self):
            super().__init__()
            self.setWindowTitle("Mapear Produtos do Guru para Produtos Internos")
            self.setMinimumSize(800, 500)
            self.layout = QVBoxLayout(self)

            # Campo para digitar nome interno
            linha_nome = QHBoxLayout()
            linha_nome.addWidget(QLabel("Nome interno:"))
            self.input_nome = QLineEdit()
            self.input_nome.textChanged.connect(self.iniciar)
            linha_nome.addWidget(self.input_nome)
            self.layout.addLayout(linha_nome)

            # Lista de produtos do Guru
            self.lista = QListWidget()
            self.lista.setSelectionMode(QListWidget.MultiSelection)
            self.layout.addWidget(QLabel("Selecione os produtos do Guru a associar:"))
            self.layout.addWidget(self.lista)

            # Tipo: assinatura ou produto
            linha_tipo = QHBoxLayout()
            self.radio_produto = QRadioButton("Produto")
            self.radio_assinatura = QRadioButton("Assinatura")
            self.radio_produto.setChecked(True)
            self.grupo_tipo = QButtonGroup()
            self.grupo_tipo.addButton(self.radio_produto)
            self.grupo_tipo.addButton(self.radio_assinatura)
            linha_tipo.addWidget(QLabel("Tipo:"))
            linha_tipo.addWidget(self.radio_produto)
            linha_tipo.addWidget(self.radio_assinatura)
            self.layout.addLayout(linha_tipo)

            # Assinatura: duração + periodicidade
            self.widget_assinatura = QWidget()
            linha_assin = QHBoxLayout(self.widget_assinatura)
            self.combo_duracao = QComboBox()
            # duração do plano (tempo contratado)
            self.combo_duracao.addItems(["mensal", "bimestral", "anual", "bianual", "trianual"])
            linha_assin.addWidget(QLabel("Duração do plano:"))
            linha_assin.addWidget(self.combo_duracao)

            self.combo_periodicidade = QComboBox()
            # periodicidade = frequência de envio (mensal/bimestral)
            self.combo_periodicidade.addItems(["mensal", "bimestral"])
            linha_assin.addWidget(QLabel("Periodicidade (envio):"))
            linha_assin.addWidget(self.combo_periodicidade)
            self.layout.addWidget(self.widget_assinatura)

            self.widget_assinatura.setVisible(self.radio_assinatura.isChecked())
            self.radio_assinatura.toggled.connect(
                lambda checked: self.widget_assinatura.setVisible(checked)
            )

            # Botões
            botoes = QHBoxLayout()
            self.btn_salvar = QPushButton("Salvar e Próximo")
            self.btn_cancelar = QPushButton("Cancelar")
            botoes.addWidget(self.btn_salvar)
            botoes.addWidget(self.btn_cancelar)
            self.layout.addLayout(botoes)

            self.btn_salvar.clicked.connect(self.salvar_selecao)
            self.btn_cancelar.clicked.connect(self.reject)

            self.produtos = produtos_guru
            self.produtos_restantes = produtos_guru.copy()
            self.iniciar()

        def iniciar(self):
            self.lista.clear()
            termo = unidecode(self.input_nome.text().strip().lower())

            for p in self.produtos:
                titulo = (p.get("name") or "").strip()
                product_id = str(p.get("id") or "").strip()  # UUID técnico (o que salvamos)
                market_id = str(p.get("marketplace_id") or "").strip()  # ID humano (o que exibimos)
                if not titulo and not market_id and not product_id:
                    continue

                # filtro por nome e marketplace_id
                alvo = unidecode(f"{titulo} {market_id}".lower())
                if termo and termo not in alvo:
                    continue

                # exibe marketplace_id; fallback para product_id se não houver
                label = f"{titulo} (id:{market_id})" if market_id else f"{titulo} (id:{product_id})"

                item = QListWidgetItem(label)
                item.setData(Qt.UserRole, product_id)  # 🔒 salvaremos este ID
                item.setData(Qt.UserRole + 1, market_id)  # 👀 apenas informativo
                item.setToolTip(
                    f"marketplace_id: {market_id or '-'}\nproduct_id: {product_id or '-'}"
                )
                self.lista.addItem(item)

        def salvar_selecao(self):
            import re

            nome_base_raw = self.input_nome.text().strip()
            if not nome_base_raw:
                QMessageBox.warning(self, "Aviso", "Você precisa informar um nome interno.")
                return

            itens = self.lista.selectedItems()
            if not itens:
                QMessageBox.warning(
                    self, "Aviso", "Você precisa selecionar ao menos um produto do Guru."
                )
                return

            # IDs técnicos do Guru que vamos mapear
            novos_ids = [str(it.data(Qt.UserRole) or "").strip() for it in itens]
            novos_ids = [gid for gid in novos_ids if gid]

            is_assinatura = self.radio_assinatura.isChecked()
            if is_assinatura:
                duracao = self.combo_duracao.currentText().strip().lower()
                periodicidade = self.combo_periodicidade.currentText().strip().lower()
                if not periodicidade:
                    QMessageBox.warning(self, "Aviso", "Selecione a periodicidade da assinatura.")
                    return
                # remove eventual sufixo já digitado pelo operador: " (mensal)" / " (bimestral)"
                nome_base = re.sub(
                    r"\s*\((mensal|bimestral)\)\s*$", "", nome_base_raw, flags=re.IGNORECASE
                ).strip()
                dest_key = f"{nome_base} ({periodicidade})"  # 🔑 SEMPRE com sufixo
            else:
                duracao = None
                periodicidade = None
                # para produto simples, não mexe no nome
                dest_key = nome_base_raw

            # 🧹 Migra legado SEM sufixo → chave com sufixo (só para assinatura)
            if is_assinatura and dest_key != nome_base_raw and nome_base_raw in skus_info:
                legado = skus_info.pop(nome_base_raw) or {}
                alvo = skus_info.setdefault(dest_key, {})
                for k_list in ("guru_ids", "shopify_ids", "composto_de"):
                    if legado.get(k_list):
                        alvo.setdefault(k_list, [])
                        for v in legado[k_list]:
                            if v not in alvo[k_list]:
                                alvo[k_list].append(v)
                for k, v in legado.items():
                    if k not in ("guru_ids", "shopify_ids", "composto_de"):
                        alvo.setdefault(k, v)

            # 📌 Cria/atualiza SOMENTE a chave final (dest_key)
            entrada = skus_info.setdefault(dest_key, {})
            if is_assinatura:
                entrada["tipo"] = "assinatura"
                entrada["recorrencia"] = duracao
                entrada["periodicidade"] = periodicidade
                # mantém estrutura padrão
                entrada.setdefault("sku", "")
                entrada.setdefault("peso", 0.0)
                entrada.setdefault("composto_de", [])
            else:
                entrada["tipo"] = "produto"
                entrada.pop("recorrencia", None)
                entrada.pop("periodicidade", None)

            entrada.setdefault("guru_ids", [])
            ja = set(map(str, entrada["guru_ids"]))
            for gid in novos_ids:
                if gid and gid not in ja:
                    entrada["guru_ids"].append(gid)
                    ja.add(gid)

            with open(skus_path, "w", encoding="utf-8") as f:
                json.dump(skus_info, f, indent=4, ensure_ascii=False)

            QMessageBox.information(self, "Sucesso", f"'{dest_key}' mapeado com sucesso!")
            self.input_nome.clear()
            self.lista.clearSelection()
            self.iniciar()

    dlg = DialogoMapeamento()
    dlg.exec_()


def obter_ids_assinaturas_por_duracao(skus_info):
    assinaturas = {
        "mensal": [],
        "bimestral": [],
        "anual": [],
        "bianual": [],
        "trianual": [],
    }
    # mapa auxiliar: guru_id -> {"recorrencia":..., "periodicidade":...}
    guru_meta = {}

    for info in skus_info.items():
        if info.get("tipo") == "assinatura":
            ids = info.get("guru_ids", [])
            dur = (info.get("recorrencia") or "").lower()
            per = (info.get("periodicidade") or "").lower()
            for gid in ids:
                if dur in assinaturas:
                    assinaturas[dur].append(gid)
                guru_meta[str(gid)] = {"recorrencia": dur, "periodicidade": per}

    return assinaturas, guru_meta


def gerar_uuid():
    return str(uuid.uuid4())


############################################
# Diálogo de Edição de Regra
############################################


class RuleEditorDialog(QDialog):
    """
    Editor de uma regra individual.
    Cria/edita um dict no formato:

    {
      "id": "uuid",
      "applies_to": "oferta"|"cupom",
      "oferta": {"produto_id":"ID_GURU", "oferta_id":"UUID_OFERTA"},
      "cupom": {"nome":"NOME_DO_CUPOM"},
      "assinaturas": ["SKU_ASSINATURA_1", ...],    # só quando applies_to=="cupom"
      "action": {
        "type": "alterar_box"|"adicionar_brindes",
        "box": "NomeDoBox",                        # se alterar_box
        "brindes": ["ITEM_EXTRA_1", ...]           # se adicionar_brindes
      }
    }
    """

    def __init__(self, parent, skus_info, regra=None, produtos_guru=None):
        super().__init__(parent)
        self.setWindowTitle("Regra (Oferta/Cupom)")
        self.setMinimumWidth(600)

        self.skus_info = skus_info
        self.regra = regra or {}
        self.produtos_guru = produtos_guru or []  # opcional: lista de produtos do Guru

        layout = QVBoxLayout(self)

        # ====== Aplica a: oferta | cupom ======
        linha_aplica = QHBoxLayout()
        lbl_aplica = QLabel("Aplica a:")
        self.combo_aplica = QComboBox()
        self.combo_aplica.addItems(["oferta", "cupom"])
        linha_aplica.addWidget(lbl_aplica)
        linha_aplica.addWidget(self.combo_aplica)
        layout.addLayout(linha_aplica)

        # ====== CUPOM ======
        self.widget_cupom = QWidget()
        layout_cupom = QHBoxLayout(self.widget_cupom)
        layout_cupom.setContentsMargins(0, 0, 0, 0)
        layout_cupom.addWidget(QLabel("Cupom:"))
        self.input_cupom = QLineEdit()
        layout_cupom.addWidget(self.input_cupom)

        # ====== OFERTA ======
        self.widget_oferta = QWidget()
        layout_oferta = QVBoxLayout(self.widget_oferta)
        layout_oferta.setContentsMargins(0, 0, 0, 0)

        linha_prod = QHBoxLayout()
        linha_prod.addWidget(QLabel("Produto (Guru):"))
        self.combo_produto_guru = QComboBox()
        self.combo_produto_guru.setEditable(True)  # facilita achar por nome/ID
        # Preencher produtos do Guru se fornecidos (opcional)
        for p in self.produtos_guru or []:
            # p pode ser {"id":"...", "nome":"..."}
            texto = f'{p.get("name","") or p.get("id","")}  [{p.get("id","")}]'
            self.combo_produto_guru.addItem(texto, p.get("id"))
        linha_prod.addWidget(self.combo_produto_guru)

        btn_carregar_ofertas = QPushButton("Carregar ofertas")
        btn_carregar_ofertas.clicked.connect(self._carregar_ofertas)
        linha_prod.addWidget(btn_carregar_ofertas)

        layout_oferta.addLayout(linha_prod)

        linha_oferta = QHBoxLayout()
        linha_oferta.addWidget(QLabel("Oferta:"))
        self.combo_oferta = QComboBox()
        linha_oferta.addWidget(self.combo_oferta)
        layout_oferta.addLayout(linha_oferta)

        # ====== Assinaturas (só para CUPOM) ======
        self.widget_assinaturas = QGroupBox("Assinaturas (apenas para CUPOM)")
        layout_ass = QVBoxLayout(self.widget_assinaturas)
        self.lista_assinaturas = QListWidget()
        self.lista_assinaturas.setSelectionMode(QAbstractItemView.MultiSelection)

        assinaturas = [n for n, info in self.skus_info.items() if info.get("tipo") == "assinatura"]
        for nome in sorted(assinaturas):
            item = QListWidgetItem(nome)
            self.lista_assinaturas.addItem(item)
        layout_ass.addWidget(self.lista_assinaturas)

        # ====== Ação ======
        caixa_acao = QGroupBox("Ação")
        layout_acao = QVBoxLayout(caixa_acao)

        linha_tipo = QHBoxLayout()
        linha_tipo.addWidget(QLabel("Tipo de ação:"))
        self.combo_acao = QComboBox()
        self.combo_acao.addItems(["alterar_box", "adicionar_brindes"])
        linha_tipo.addWidget(self.combo_acao)
        layout_acao.addLayout(linha_tipo)

        # alterar_box → escolher box (produtos simples)
        self.widget_alterar = QWidget()
        layout_alt = QHBoxLayout(self.widget_alterar)
        layout_alt.setContentsMargins(0, 0, 0, 0)
        layout_alt.addWidget(QLabel("Box substituto:"))
        self.combo_box = QComboBox()
        produtos_simples = [
            n
            for n, info in self.skus_info.items()
            if info.get("tipo") != "assinatura" and not info.get("composto_de")
        ]
        self.combo_box.addItems(sorted(produtos_simples))
        layout_alt.addWidget(self.combo_box)

        # adicionar_brindes → múltiplos brindes (qualquer item não-assinatura)
        self.widget_brindes = QWidget()
        layout_br = QVBoxLayout(self.widget_brindes)
        layout_br.setContentsMargins(0, 0, 0, 0)
        self.lista_brindes = QListWidget()
        self.lista_brindes.setSelectionMode(QAbstractItemView.MultiSelection)
        brindes = [
            n
            for n, info in self.skus_info.items()
            if info.get("tipo") != "assinatura"  # pode incluir compostos, se desejar filtre mais
        ]
        for nome in sorted(brindes):
            self.lista_brindes.addItem(QListWidgetItem(nome))
        layout_br.addWidget(QLabel("Brindes a adicionar:"))
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

    def _hydrate(self, regra):
        # defaults
        applies_to = regra.get("applies_to", "oferta")
        self.combo_aplica.setCurrentText(applies_to)

        if applies_to == "cupom":
            self.input_cupom.setText(regra.get("cupom", {}).get("nome", ""))

        if applies_to == "oferta":
            prod_id = (regra.get("oferta") or {}).get("produto_id", "")
            oferta_id = (regra.get("oferta") or {}).get("oferta_id", "")
            # Selecionar produto no combo (se existir na lista)
            idx_prod = max(0, self.combo_produto_guru.findData(prod_id))
            self.combo_produto_guru.setCurrentIndex(idx_prod)
            # Carregar ofertas desse produto e selecionar
            if prod_id:
                self._carregar_ofertas()
                oferta_id = (regra.get("oferta") or {}).get("oferta_id", "")
                idx_of = self.combo_oferta.findData(oferta_id)

                if idx_of == -1 and oferta_id:
                    # Se a API não trouxe a oferta, adiciona uma entrada usando o nome já salvo no JSON
                    nome_existente = (regra.get("oferta") or {}).get("nome", "")
                    display = f"{(nome_existente or oferta_id)} [{oferta_id}]"
                    self.combo_oferta.addItem(display, oferta_id)
                    idx_of = self.combo_oferta.count() - 1
                    # guarda o nome no role extra para o _accept usar
                    self.combo_oferta.setItemData(idx_of, nome_existente or "", Qt.UserRole + 1)

                self.combo_oferta.setCurrentIndex(max(0, idx_of))

        # assinaturas
        assinaturas = regra.get("assinaturas", [])
        if assinaturas:
            for i in range(self.lista_assinaturas.count()):
                item = self.lista_assinaturas.item(i)
                if item.text() in assinaturas:
                    item.setSelected(True)

        # ação
        action = regra.get("action", {}) or {}
        self.combo_acao.setCurrentText(action.get("type", "alterar_box"))

        if action.get("type") == "alterar_box":
            box = action.get("box", "")
            idx = max(0, self.combo_box.findText(box))
            self.combo_box.setCurrentIndex(idx)

        if action.get("type") == "adicionar_brindes":
            brindes = action.get("brindes", []) or []
            for i in range(self.lista_brindes.count()):
                it = self.lista_brindes.item(i)
                if it.text() in brindes:
                    it.setSelected(True)

    def _toggle_aplica(self, applies_to):
        is_cupom = applies_to == "cupom"
        self.widget_cupom.setVisible(is_cupom)
        self.widget_assinaturas.setVisible(is_cupom)

        is_oferta = applies_to == "oferta"
        self.widget_oferta.setVisible(is_oferta)

    def _toggle_acao(self, tipo):
        self.widget_alterar.setVisible(tipo == "alterar_box")
        self.widget_brindes.setVisible(tipo == "adicionar_brindes")

    def _carregar_ofertas(self):
        prod_id = self.combo_produto_guru.currentData()
        if not prod_id:
            txt = self.combo_produto_guru.currentText()
            if "[" in txt and "]" in txt:
                prod_id = txt.split("[")[-1].split("]")[0].strip()

        self.combo_oferta.clear()
        if not prod_id:
            return

        ofertas = buscar_ofertas_do_produto(prod_id) or []
        for o in ofertas:
            oid = o.get("id", "")
            nome = o.get("name") or oid or "Oferta"
            # texto visível + userData padrão = id
            self.combo_oferta.addItem(f"{nome} [{oid}]", oid)
            # guarda o nome real em um role extra
            idx = self.combo_oferta.count() - 1
            self.combo_oferta.setItemData(idx, nome, Qt.UserRole + 1)

    def _accept(self):
        applies_to = self.combo_aplica.currentText()

        # ===== Validação =====
        if applies_to == "cupom":
            cupom = self.input_cupom.text().strip()
            if not cupom:
                QMessageBox.warning(self, "Validação", "Informe o nome do cupom.")
                return
        elif applies_to == "oferta":
            # produto_id pode vir do .data() ou do texto "[id]"
            prod_id = self.combo_produto_guru.currentData()
            if not prod_id:
                txt_prod = self.combo_produto_guru.currentText()
                if "[" in txt_prod and "]" in txt_prod:
                    prod_id = txt_prod.split("[")[-1].split("]")[0].strip()
            of_id = self.combo_oferta.currentData()
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

        # ===== Construção do objeto da regra =====
        rid = self.regra.get("id")
        if not rid:
            try:
                rid = gerar_uuid()
            except NameError:
                import uuid as _uuid

                rid = str(_uuid.uuid4())

        regra_nova = {"id": rid, "applies_to": applies_to, "action": {"type": action_type}}

        if applies_to == "cupom":
            # Normaliza cupom para evitar duplicadas
            cupom_nome = self.input_cupom.text().strip().upper()
            regra_nova["cupom"] = {"nome": cupom_nome}

            # Assinaturas (dedupe preservando ordem)
            assin_sel = [it.text() for it in self.lista_assinaturas.selectedItems()]
            seen = set()
            regra_nova["assinaturas"] = [x for x in assin_sel if not (x in seen or seen.add(x))]

        else:  # oferta
            # Usa o nome salvo no role extra; fallback pro texto visível se necessário
            idx_of = self.combo_oferta.currentIndex()
            of_nome = self.combo_oferta.itemData(idx_of, Qt.UserRole + 1)
            if not of_nome:
                of_text = (self.combo_oferta.currentText() or "").strip()
                of_nome = of_text.split("[", 1)[0].strip() if "[" in of_text else of_text

            regra_nova["oferta"] = {
                "produto_id": prod_id,
                "oferta_id": of_id,
                "nome": of_nome or "",
            }

        if action_type == "alterar_box":
            regra_nova["action"]["box"] = self.combo_box.currentText().strip()
        else:
            # Brindes (dedupe preservando ordem)
            brs = [it.text() for it in self.lista_brindes.selectedItems()]
            seen_b = set()
            regra_nova["action"]["brindes"] = [x for x in brs if not (x in seen_b or seen_b.add(x))]

        self.regra = regra_nova
        self.accept()

    def get_regra(self):
        return self.regra


############################################
# Diálogo principal: gerenciador de regras
############################################


class RuleManagerDialog(QDialog):
    def __init__(self, parent, estado, skus_info, config_path):
        super().__init__(parent)
        self.setWindowTitle("⚖️ Regras (oferta/cupom)")
        self.setMinimumSize(800, 600)

        self.estado = estado
        self.skus_info = skus_info
        self.config_path = config_path

        # garante que estado["rules"] exista
        self.estado.setdefault("rules", carregar_regras(self.config_path))

        # 🔎 índices auxiliares para rótulos bonitos
        self._build_indices()

        layout = QVBoxLayout(self)

        # Lista de regras
        self.lista = QListWidget()
        self.lista.setSelectionMode(QAbstractItemView.SingleSelection)
        layout.addWidget(self.lista)

        # Botões
        linha_btns = QHBoxLayout()
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

        # Conexões
        self.btn_add.clicked.connect(self._add)
        self.btn_edit.clicked.connect(self._edit)
        self.btn_dup.clicked.connect(self._dup)
        self.btn_del.clicked.connect(self._del)
        self.btn_up.clicked.connect(self._up)
        self.btn_down.clicked.connect(self._down)
        self.btn_salvar.clicked.connect(self._salvar)

        # preencher
        self._refresh_list()

    # ---------- índices / helpers ----------
    def _build_indices(self):
        """Monta índices de produto/oferta a partir do estado."""
        produtos = self.estado.get("produtos_guru") or []
        self._prod_index = {}  # {product_id: produto_dict}
        self._offer_index = {}  # {offer_id: oferta_dict}

        for p in produtos:
            pid = str(p.get("id") or p.get("product_id") or "")
            if pid:
                self._prod_index[pid] = p
            for o in p.get("offers") or []:
                oid = str(o.get("id") or o.get("oferta_id") or "")
                if oid:
                    self._offer_index[oid] = o

        # Também aceita um flat no estado (caso exista):
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

    def _label_oferta(self, oferta_id: str) -> str:
        """Exibe o nome da oferta; fallback para o id."""
        o = self._offer_index.get(str(oferta_id))
        nome = o.get("name") if o else None
        if not nome:
            nome = (o or {}).get("nome") or (o or {}).get("title")
        return nome or str(oferta_id) or "?"

    def _format_assinaturas(self, r):
        """
        Converte nomes de assinatura para rótulos curtos:
        - "Assinatura Anual (mensal)"   -> "Anual"
        - "Assinatura 2 anos (mensal)"  -> "2 anos"
        - "Assinatura 3 anos (mensal)"  -> "3 anos"
        - "Assinatura Bimestral (...)"  -> "Bimestral"
        - "Assinatura Mensal (...)"     -> "Mensal"
        Aceita lista/str e procura em r, r['cupom'] e r['oferta'].
        """
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
            # remove parênteses e conteúdos
            t = re.sub(r"\s*\(.*?\)\s*", "", t, flags=re.I)
            # remove prefixo "Assinatura" e corta por tracos (-)
            t = re.sub(r"^\s*assinatura\s+", "", t, flags=re.I)
            t = re.split(r"\s*[\u2013\u2014-]\s*", t)[0].strip()

            # "2 anos", "3 anos", etc.
            m = re.search(r"(\d+)\s*anos?", t, flags=re.I)
            if m:
                return f"{int(m.group(1))} anos"

            # palavras-chave
            if re.search(r"\banual\b", t, flags=re.I):
                return "Anual"
            if re.search(r"\bbimestral\b", t, flags=re.I):
                return "Bimestral"
            if re.search(r"\bmensal\b", t, flags=re.I):
                return "Mensal"

            # fallback
            return t.title()

        vistos = set()
        out = []
        for item in raw:
            p = pretty(item)
            k = p.lower()
            if p and k not in vistos:
                vistos.add(k)
                out.append(p)
        return ", ".join(out)

    def _rule_title(self, r):
        # prefixo
        if r.get("applies_to") == "cupom":
            nome = ((r.get("cupom") or {}).get("nome") or "").strip()
            prefixo = f"[CUPOM:{nome or '?'}]"
        else:
            of = r.get("oferta") or {}
            oferta_lbl = (
                of.get("nome")  # 1) usa nome salvo no JSON
                or self._label_oferta(of.get("oferta_id"))  # 2) fallback para label pelo ID
                or of.get("oferta_id")  # 3) fallback para o próprio ID
                or "?"
            )
            prefixo = f"[OFERTA:{oferta_lbl}]"

        a = r.get("action") or {}
        partes = []

        # 🎁 Brindes (agrega itens iguais somando quantidades)
        def coletar_brindes(action):
            keys = ["brindes", "gifts", "add_items", "add", "extras", "itens", "items"]
            val = next((action.get(k) for k in keys if action.get(k) is not None), None)
            if val is None:
                return []
            if isinstance(val, dict):
                val = [val]
            itens = []
            for g in val:
                if isinstance(g, str):
                    itens.append({"nome": g.strip(), "qtd": 1})
                elif isinstance(g, dict):
                    qtd = g.get("qtd") or g.get("qty") or g.get("quantidade") or 1
                    nome = (
                        (g.get("nome") or "").strip()
                        or (self._label_produto(g.get("produto_id")) or "").strip()
                        or (g.get("sku") or "").strip()
                        or "?"
                    )
                    itens.append({"nome": nome, "qtd": int(qtd)})
            # agrega preservando ordem de primeira aparição
            agg = OrderedDict()
            for it in itens:
                agg[it["nome"]] = agg.get(it["nome"], 0) + it["qtd"]
            return [{"nome": k, "qtd": v} for k, v in agg.items()]

        brindes = coletar_brindes(a)
        if brindes:
            partes.append("🎁 " + " | ".join(f"{b['qtd']}x {b['nome']}" for b in brindes))

        # 📦 Box
        def pegar_box(action):
            for k in ["novo_box", "box", "replace_box", "swap_box", "box_name"]:
                if action.get(k):
                    return str(action[k]).strip()
            return None

        box = pegar_box(a)
        if box:
            partes.append(f"📦 BOX → {box}")

        # 🧾 Assinaturas (curtas)
        alvos = self._format_assinaturas(r)
        if alvos:
            partes.append(f"Assinaturas: {alvos}")

        if not partes:
            partes.append(str(a.get("type") or "?"))

        return f"{prefixo}  " + "  •  ".join(partes)

    def _refresh_list(self):
        # reconstruir índices caso o estado tenha sido atualizado externamente
        self._build_indices()
        self.lista.clear()
        for r in self.estado["rules"]:
            item = QListWidgetItem(self._rule_title(r))
            item.setData(Qt.UserRole, r)
            self.lista.addItem(item)

    def _selected_index(self):
        row = self.lista.currentRow()
        return row if row >= 0 else None

    # ---------- ações ----------
    def _add(self):
        dlg = RuleEditorDialog(
            self, self.skus_info, regra=None, produtos_guru=self.estado.get("produtos_guru")
        )
        if dlg.exec_() == QDialog.Accepted:
            self.estado["rules"].append(dlg.get_regra())
            self._refresh_list()

    def _edit(self):
        idx = self._selected_index()
        if idx is None:
            return
        regra = self.estado["rules"][idx]
        dlg = RuleEditorDialog(
            self, self.skus_info, regra=regra, produtos_guru=self.estado.get("produtos_guru")
        )
        if dlg.exec_() == QDialog.Accepted:
            self.estado["rules"][idx] = dlg.get_regra()
            self._refresh_list()
            self.lista.setCurrentRow(idx)

    def _dup(self):
        idx = self._selected_index()
        if idx is None:
            return
        r = json.loads(json.dumps(self.estado["rules"][idx]))  # deep copy
        r["id"] = gerar_uuid()
        self.estado["rules"].insert(idx + 1, r)
        self._refresh_list()
        self.lista.setCurrentRow(idx + 1)

    def _del(self):
        idx = self._selected_index()
        if idx is None:
            return
        if (
            QMessageBox.question(
                self, "Confirmar", "Excluir esta regra?", QMessageBox.Yes | QMessageBox.No
            )
            == QMessageBox.Yes
        ):
            del self.estado["rules"][idx]
            self._refresh_list()

    def _up(self):
        idx = self._selected_index()
        if idx is None or idx == 0:
            return
        self.estado["rules"][idx - 1], self.estado["rules"][idx] = (
            self.estado["rules"][idx],
            self.estado["rules"][idx - 1],
        )
        self._refresh_list()
        self.lista.setCurrentRow(idx - 1)

    def _down(self):
        idx = self._selected_index()
        if idx is None or idx == len(self.estado["rules"]) - 1:
            return
        self.estado["rules"][idx + 1], self.estado["rules"][idx] = (
            self.estado["rules"][idx],
            self.estado["rules"][idx + 1],
        )
        self._refresh_list()
        self.lista.setCurrentRow(idx + 1)

    def _salvar(self):
        try:
            salvar_regras(self.config_path, self.estado["rules"])
            QMessageBox.information(self, "Salvo", "Regras salvas em config_ofertas.json.")
        except Exception as e:
            QMessageBox.critical(self, "Erro", f"Falha ao salvar: {e}")


############################################
# Função para abrir o gerenciador (wire)
############################################


def abrir_mapeador_regras(estado, skus_info):
    config_path = os.path.join(os.path.dirname(__file__), "config_ofertas.json")
    # opcional: carregar produtos do Guru para o editor
    try:
        estado["produtos_guru"] = buscar_todos_produtos_guru()
    except Exception:
        estado["produtos_guru"] = []
    dlg = RuleManagerDialog(None, estado, skus_info, config_path)
    dlg.exec_()


def buscar_ofertas_do_produto(product_id):
    url = f"{BASE_URL_GURU}/products/{product_id}/offers"
    headers = HEADERS_GURU
    ofertas = []
    cursor = None
    pagina = 1

    while True:
        try:
            params = {"limit": 100}
            if cursor:
                params["cursor"] = cursor

            r = http_get(url, headers=headers, params=params, timeout=10)
            if r.status_code != 200:
                print(
                    f"[❌ Guru] Erro {r.status_code} ao buscar ofertas do produto {product_id}: {r.text}"
                )
                break

            data = r.json()
            pagina_dados = data.get("data", [])
            print(
                f"[📄 Página {pagina}] {len(pagina_dados)} ofertas encontradas para produto {product_id}"
            )

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


ASSINATURAS, GURU_META = obter_ids_assinaturas_por_duracao(skus_info)

ASSINATURAS_MENSAIS = ASSINATURAS.get("mensal", [])
ASSINATURAS_BIMESTRAIS = ASSINATURAS.get("bimestral", [])
ASSINATURAS_ANUAIS = ASSINATURAS.get("anual", [])
ASSINATURAS_BIANUAIS = ASSINATURAS.get("bianual", [])
ASSINATURAS_TRIANUAIS = ASSINATURAS.get("trianual", [])

# API SHOPIFY


def obter_api_shopify_version():
    hoje = datetime.today()
    if hoje.month <= 3:
        return f"{hoje.year}-01"
    elif hoje.month <= 6:
        return f"{hoje.year}-04"
    elif hoje.month <= 9:
        return f"{hoje.year}-07"
    else:
        return f"{hoje.year}-10"


API_VERSION = obter_api_shopify_version()
GRAPHQL_URL = f"https://{settings.SHOP_URL}/admin/api/{API_VERSION}/graphql.json"
estado.setdefault("dados_temp", {})
estado["dados_temp"].setdefault("cpfs", {})
estado["dados_temp"].setdefault("bairros", {})
estado["dados_temp"].setdefault("enderecos", {})

# Controle de taxa global
controle_shopify = {"lock": threading.Lock(), "ultimo_acesso": time.time()}
MIN_INTERVALO_GRAPHQL = 0.1  # 100ms (100 chamadas/s)

# API OPENAI

client = openai.OpenAI(api_key=settings.OPENAI_API_KEY)


# Gerenciamento de barra de progresso na interface.
class GerenciadorProgresso(QObject):
    atualizar_signal = pyqtSignal(str, int, int)
    finalizado_signal = pyqtSignal()

    def __init__(
        self, *, titulo="Progresso", com_percentual=True, estado_global=None, logger_obj=None
    ):
        super().__init__()

        self.cancelado = False
        self.com_percentual = com_percentual
        self._ja_fechado = False
        self.janela_feita = False

        self.estado = estado_global or {}
        self.logger = logger_obj

        try:
            self.janela = QDialog()
            self.janela.setWindowTitle(titulo)
            self.janela.setFixedSize(500, 160)
            self.janela.setAttribute(Qt.WA_DeleteOnClose, True)

            layout = QVBoxLayout(self.janela)

            self.label_status = QLabel("Iniciando...")
            self.label_status.setAlignment(Qt.AlignCenter)
            layout.addWidget(self.label_status)

            self.barra = QProgressBar()
            if not self.com_percentual:
                self.barra.setRange(0, 0)
            layout.addWidget(self.barra)

            self.botao_cancelar = QPushButton("Cancelar")
            self.botao_cancelar.clicked.connect(self.cancelar)
            layout.addWidget(self.botao_cancelar)

            self.atualizar_signal.connect(self._atualizar_seguro, Qt.QueuedConnection)

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

    def cancelar(self):
        self.cancelado = True
        self.label_status.setText("Cancelado pelo usuário.")
        self.botao_cancelar.setEnabled(False)

        cancelador = self.estado.get("cancelador_global")
        if isinstance(cancelador, Event):
            cancelador.set()
        else:
            self._log_warning("[🛑] Cancelamento detectado, mas sem Event válido.")

        print("[🛑] Cancelamento solicitado.")

    def atualizar(self, texto, atual=None, total=None):
        self.atualizar_signal.emit(texto, atual or 0, total or 0)

    def _atualizar_seguro(self, texto, atual, total):
        self.label_status.setText(texto)

        if not self.com_percentual:
            QApplication.processEvents()
            return

        if total == 0:
            self.barra.setRange(0, 0)
        else:
            self.barra.setRange(0, 100)
            progresso = min(100, max(1, int(100 * atual / total)))
            self.barra.setValue(progresso)

        QApplication.processEvents()

    def fechar(self):
        if self._ja_fechado:
            self._log_info("[🔁] Janela já havia sido fechada. Ignorando.")
            return
        self._ja_fechado = True
        self._log_info("[🔚 GerenciadorProgresso] Preparando para fechar a janela...")

        def encerrar():
            try:
                if self.janela and self.janela.isVisible():
                    self._log_info("[🧼] Ocultando janela de progresso...")
                    self.janela.hide()
                if self.janela:
                    self._log_info("[✅] Fechando janela de progresso...")
                    self.janela.close()
            except Exception as e:
                self._log_exception(f"[❌] Erro ao fechar janela: {e}")

        if QThread.currentThread() == QCoreApplication.instance().thread():
            encerrar()
        else:
            QTimer.singleShot(0, encerrar)

    def _log_info(self, msg):
        if self.logger:
            self.logger.info(msg)
        else:
            print(msg)

    def _log_warning(self, msg):
        if self.logger:
            self.logger.warning(msg)
        else:
            print(msg)

    def _log_exception(self, msg):
        if self.logger:
            self.logger.exception(msg)
        else:
            print(msg)


def iniciar_progresso(titulo="Progresso", com_percentual=True, estado_global=None, logger_obj=None):
    if QApplication.instance() is None:
        raise RuntimeError("QApplication ainda não foi iniciado.")

    gerenciador = GerenciadorProgresso(
        titulo=titulo,
        com_percentual=com_percentual,
        estado_global=estado_global,
        logger_obj=logger_obj,
    )
    QApplication.processEvents()
    return gerenciador


# Integração com a API do Digital Manager Guru


class WorkerController(QObject):
    iniciar_worker_signal = pyqtSignal()

    def __init__(self, dados, estado, skus_info):
        super().__init__()
        self.dados = dados
        self.estado = estado
        self.skus_info = skus_info
        self.iniciar_worker_signal.connect(self.iniciar_worker)

    def iniciar_worker(self):
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

            self.estado["worker_thread"] = WorkerThread(
                self.dados, self.estado, self.skus_info, gerenciador
            )
            worker = self.estado["worker_thread"]

            # avisos e erros
            worker.avisar_usuario.connect(
                lambda titulo, msg: comunicador_global.mostrar_mensagem.emit("aviso", titulo, msg)
            )

            def on_erro(msg):
                comunicador_global.mostrar_mensagem.emit(
                    "erro", "Erro", f"Ocorreu um erro durante a exportação:\n{msg}"
                )
                try:
                    gerenciador.fechar()
                except Exception:
                    pass

            worker.erro.connect(on_erro)

            # finalização
            def ao_finalizar_worker(linhas, contagem):
                try:
                    exibir_resumo_final(
                        linhas, contagem, self.estado, modo=(self.dados.get("modo") or "").lower()
                    )
                finally:
                    try:
                        gerenciador.fechar()
                    except Exception:
                        pass

            worker.finalizado.connect(ao_finalizar_worker)

            # (opcional) fallback extra - pode ser removido se preferir evitar chamadas duplicadas de fechar
            # worker.finished.connect(gerenciador.fechar)

            worker.start()
            print("[🧵 iniciar_worker] Thread iniciada.")

        except Exception as e:
            print("[❌ ERRO EM iniciar_worker]:", e)
            import traceback

            print(traceback.format_exc())
            comunicador_global.mostrar_mensagem.emit(
                "erro", "Erro", f"Falha ao iniciar a exportação:\n{e!s}"
            )


class WorkerThread(QThread):
    # sinais já esperados pelo Controller
    finalizado = pyqtSignal(list, dict)
    erro = pyqtSignal(str)
    avisar_usuario = pyqtSignal(str, str)

    # sinais para progresso/fechamento seguro entre threads
    progresso = pyqtSignal(str, int, int)
    fechar_ui = pyqtSignal()

    def __init__(self, dados, estado, skus_info, gerenciador):
        super().__init__()
        self.dados = dados
        self.estado = estado
        self.skus_info = skus_info
        self.gerenciador = gerenciador

        # 🔒 garante queued connection entre threads
        self.progresso.connect(self.gerenciador.atualizar, type=Qt.QueuedConnection)
        self.fechar_ui.connect(self.gerenciador.fechar, type=Qt.QueuedConnection)

        # 🔗 captura o correlation_id do contexto da thread principal
        self._parent_correlation_id = get_correlation_id()

    def run(self):
        # 🔗 reata o correlation_id dentro desta thread
        set_correlation_id(self._parent_correlation_id)

        novas_linhas: list = []
        contagem: dict = {}

        try:
            logger.info("worker_started", extra={"modo": self.dados.get("modo")})

            cancelador = self.estado.get("cancelador_global")
            if hasattr(cancelador, "is_set") and cancelador.is_set():
                logger.warning("worker_cancelled_early")
                return

            modo = (self.dados.get("modo") or "assinaturas").strip().lower()

            if modo == "assinaturas":
                self.progresso.emit("🔄 Buscando transações de assinaturas...", 0, 0)
                transacoes, _, dados_final = buscar_transacoes_assinaturas(
                    self.dados,
                    atualizar=self.progresso.emit,
                    cancelador=self.estado["cancelador_global"],
                    estado=self.estado,
                )

            elif modo == "produtos":
                self.progresso.emit("🔄 Buscando transações de produtos...", 0, 0)
                transacoes, _, dados_final = buscar_transacoes_produtos(
                    self.dados,
                    atualizar=self.progresso.emit,
                    cancelador=self.estado["cancelador_global"],
                    estado=self.estado,
                )
            else:
                raise ValueError(f"Modo de busca desconhecido: {modo}")

            if self.estado["cancelador_global"].is_set():
                logger.warning("worker_cancelled_after_fetch")
                return

            self.progresso.emit("📦 Processando transações", 0, 100)

            if not isinstance(transacoes, list) or not isinstance(dados_final, dict):
                raise ValueError("Dados inválidos retornados da busca.")

            logger.info(
                "worker_received_transactions",
                extra={"qtd": len(transacoes), "modo": modo},
            )

            novas_linhas, contagem = processar_planilha(
                transacoes=transacoes,
                dados=dados_final,
                atualizar_etapa=self.progresso.emit,
                skus_info=self.skus_info,
                cancelador=self.estado["cancelador_global"],
                estado=self.estado,
            )

            if self.estado["cancelador_global"].is_set():
                logger.warning("worker_cancelled_after_process")
                return

            self.progresso.emit("✅ Finalizando...", 100, 100)

            if not isinstance(novas_linhas, list) or not isinstance(contagem, dict):
                raise ValueError("Retorno inválido de processar_planilha.")

            if "linhas_planilha" not in self.estado or not isinstance(
                self.estado["linhas_planilha"], list
            ):
                self.estado["linhas_planilha"] = []
            self.estado["linhas_planilha"].extend(novas_linhas)
            self.estado["transacoes_obtidas"] = True

            logger.info(
                "worker_success",
                extra={"linhas_adicionadas": len(novas_linhas)},
            )

        except Exception as e:
            # log estruturado + stacktrace
            logger.exception("worker_error", extra={"err": str(e)})
            self.erro.emit(str(e))

        finally:
            logger.info("worker_finished")
            # Atualização e fechamento via sinais (thread-safe)
            self.progresso.emit("✅ Finalizado com sucesso", 1, 1)
            self.fechar_ui.emit()

            # aviso agregado de erros - só se for lista e não vazia
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


def dividir_busca_em_periodos(data_inicio, data_fim):
    blocos = []
    atual = (
        data_inicio
        if isinstance(data_inicio, datetime)
        else datetime.combine(data_inicio, datetime.min.time())
    )
    data_fim = (
        data_fim
        if isinstance(data_fim, datetime)
        else datetime.combine(data_fim, datetime.max.time())
    )

    while atual <= data_fim:
        mes = atual.month
        ano = atual.year

        if mes in [1, 2, 3, 4]:
            fim_mes = 4
        elif mes in [5, 6, 7, 8]:
            fim_mes = 8
        else:
            fim_mes = 12

        ultimo_dia = monthrange(ano, fim_mes)[1]
        fim_bloco = datetime(ano, fim_mes, ultimo_dia)

        fim_bloco = min(fim_bloco, data_fim)

        blocos.append((atual.strftime("%Y-%m-%d"), fim_bloco.strftime("%Y-%m-%d")))

        # Avança para o primeiro dia do próximo bloco
        proximo_mes = fim_mes + 1
        proximo_ano = ano
        if proximo_mes > 12:
            proximo_mes = 1
            proximo_ano += 1

        atual = datetime(proximo_ano, proximo_mes, 1)

    return blocos


def requisicao_com_retry(
    url, headers=None, params=None, tentativas=3, backoff_base=2, tratar_422_como_vazio=False
):
    ultima_resposta = None

    for tentativa in range(tentativas):
        try:
            with controle_rate_limit["lock"]:
                agora = time.time()
                decorrido = agora - controle_rate_limit["ultimo_acesso"]
                if decorrido < 0.2:
                    time.sleep(0.2 - decorrido)
                controle_rate_limit["ultimo_acesso"] = time.time()

            resposta = http_get(url, headers=headers, params=params, timeout=6)
            ultima_resposta = resposta

            if resposta.status_code == 200:
                return resposta

            elif resposta.status_code == 422 and tratar_422_como_vazio:
                print(f"[INFO] Nenhum resultado para os parâmetros: {params}")
                return None

            elif resposta.status_code == 429:
                print(f"[⏳ Retry {tentativa + 1}/3] Limite atingido (429). Aguardando...")

            else:
                print(f"[❌] Status inesperado: {resposta.status_code}")

        except Exception as e:
            print(f"[⚠️ Erro] {e}")

        time.sleep(backoff_base * (tentativa + 1))

    if tratar_422_como_vazio and ultima_resposta and ultima_resposta.status_code == 422:
        return None
    raise Exception("⚠️ Todas as tentativas falharam.")


def iniciar_busca_produtos(box_nome_input, transportadoras_var, skus_info, estado):

    dialog = QDialog()
    dialog.setWindowTitle("🔍 Buscar Produtos Aprovados")
    layout = QVBoxLayout(dialog)

    def obter_periodo_bimestre_atual():
        hoje = datetime.today()
        mes = hoje.month
        ano = hoje.year
        bimestre = (mes - 1) // 2
        primeiro_mes = 1 + bimestre * 2

        data_ini = QDate(ano, primeiro_mes, 1)

        if primeiro_mes + 2 > 12:
            data_fim = QDate(ano + 1, 1, 1).addDays(-1)
        else:
            data_fim = QDate(ano, primeiro_mes + 2, 1).addDays(-1)

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

    produtos_simples = [
        nome for nome, info in skus_info.items() if info.get("tipo") != "assinatura"
    ]
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

    def executar():
        data_ini = data_ini_input.date().toPyDate()
        data_fim = data_fim_input.date().toPyDate()
        nome_produto = produto_input.currentText().strip()

        if data_ini > data_fim:
            QMessageBox.warning(
                dialog, "Erro", "A data inicial não pode ser posterior à data final."
            )
            return

        dialog.accept()

        executar_busca_produtos(
            data_ini=data_ini,
            data_fim=data_fim,
            nome_produto=None if nome_produto == "Todos os produtos" else nome_produto,
            box_nome_input=box_nome_input,
            transportadoras_var=transportadoras_var,
            estado=estado,
            skus_info=skus_info,
        )

    btn_ok.clicked.connect(executar)
    btn_cancelar.clicked.connect(dialog.reject)

    dialog.exec_()


def executar_busca_produtos(
    data_ini, data_fim, nome_produto, box_nome_input, transportadoras_var, estado, skus_info
):
    print(f"[🔎] Iniciando busca de produtos de {data_ini} a {data_fim}")
    produtos_alvo = {}

    # 🎯 Seleciona produtos válidos
    if nome_produto:
        info = skus_info.get(nome_produto, {})
        if info.get("tipo") == "assinatura":
            QMessageBox.warning(
                None, "Erro", f"'{nome_produto}' é uma assinatura. Selecione apenas produtos."
            )
            return
        produtos_alvo[nome_produto] = info
    else:
        produtos_alvo = {
            nome: info for nome, info in skus_info.items() if info.get("tipo") != "assinatura"
        }

    produtos_ids = []
    for info in produtos_alvo.values():
        produtos_ids.extend(info.get("guru_ids", []))

    if not produtos_ids:
        QMessageBox.warning(None, "Aviso", "Nenhum produto com IDs válidos encontrados.")
        return

    dados = {
        "modo": "produtos",  # ← AQUI está o ajuste necessário
        "inicio": data_ini,
        "fim": data_fim,
        "produtos_ids": produtos_ids,
        "box_nome": box_nome_input.currentText().strip(),
        "transportadoras_permitidas": [
            nome for nome, cb in transportadoras_var.items() if cb.isChecked()
        ],
    }

    if estado.get("worker_thread") and estado["worker_thread"].isRunning():
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
    estado["dados_busca"] = dados.copy()

    print("[🚀 executar_busca_produtos] Enviando para WorkerController...")

    try:
        controller = WorkerController(dados, estado, skus_info)
        estado["worker_controller"] = controller
        controller.iniciar_worker_signal.emit()
    except Exception as e:
        print("[❌ ERRO EM iniciar_worker via sinal]:", e)
        import traceback

        print(traceback.format_exc())
        comunicador_global.mostrar_mensagem.emit(
            "erro", "Erro", f"Ocorreu um erro ao iniciar a exportação:\n{e!s}"
        )


def buscar_transacoes_produtos(dados, *, atualizar=None, cancelador=None, estado=None):
    print("[🔍 buscar_transacoes_produtos] Início da função")

    transacoes = []
    estado["transacoes_com_erro"] = []

    inicio = dados["inicio"]
    fim = dados["fim"]
    produtos_ids = [pid for pid in dados.get("produtos_ids", []) if pid]

    if not produtos_ids:
        print("[⚠️] Nenhum produto selecionado para busca.")
        return [], {}, dados

    intervalos = dividir_busca_em_periodos(inicio, fim)
    tarefas = [(product_id, ini, fim) for product_id in produtos_ids for ini, fim in intervalos]

    print(f"[📦] Total de tarefas para produtos: {len(tarefas)}")

    if cancelador.is_set():
        if atualizar:
            atualizar("⛔ Busca cancelada pelo usuário", 1, 1)
        return [], {}, dados

    with ThreadPoolExecutor(max_workers=12) as executor:
        futures = [
            executor.submit(buscar_transacoes_com_retry, *args, cancelador=cancelador)
            for args in tarefas
        ]
        total_futures = len(futures)
        concluidos = 0

        while futures:
            if cancelador.is_set():
                print("[🚫] Cancelado durante busca de produtos.")
                for f in futures:
                    f.cancel()
                return transacoes, {}, dados

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
                                        print(
                                            f"[⚠️] Ignorado item aninhado não-dict: {type(subitem)}"
                                        )
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
                    atualizar("🔄 Coletando transações de produtos...", concluidos, total_futures)

            futures = list(not_done)

    print(f"[✅ buscar_transacoes_produtos] Finalizado - {len(transacoes)} transações coletadas")
    return transacoes, {}, dados


def bimestre_do_mes(mes: int) -> int:
    return 1 + (int(mes) - 1) // 2


def bounds_do_periodo(ano: int, mes: int, periodicidade: str):
    periodicidade = (periodicidade or "").strip().lower()
    if periodicidade == "mensal":
        dt_ini = datetime(ano, mes, 1, 0, 0, 0)
        last_day = calendar.monthrange(ano, mes)[1]
        dt_end = datetime(ano, mes, last_day, 23, 59, 59)
        periodo = mes
    else:  # bimestral
        bim = bimestre_do_mes(mes)
        m1 = 1 + (bim - 1) * 2
        m2 = m1 + 1
        dt_ini = datetime(ano, m1, 1, 0, 0, 0)
        last_day = calendar.monthrange(ano, m2)[1]
        dt_end = datetime(ano, m2, last_day, 23, 59, 59)
        periodo = bim
    return dt_ini, dt_end, periodo


def dentro_periodo_selecionado(dados: dict, data_pedido: datetime) -> bool:
    """
    True se data_pedido (ordered_at) estiver dentro do período (Ano/Mês + Periodicidade).
    - NÃO aplica para modo 'produtos'.
    - Usa ordered_at_ini_periodo/ordered_at_end_periodo se existirem; senão, deriva via bounds_do_periodo.
    - Converte TUDO para datetime naive antes de comparar.
    - Logs defensivos sem referenciar variáveis ainda não definidas.
    """
    from datetime import datetime

    def _naive(dt):
        try:
            return dt.replace(tzinfo=None)
        except Exception:
            return dt

    def _to_dt(val):
        """Converte val -> datetime naive (aceita datetime/ISO/timestamp s|ms/QDateTime)."""
        if val is None:
            return None
        if isinstance(val, datetime):
            return _naive(val)
        if isinstance(val, int | float):
            try:
                v = float(val)
                if v > 1e12:  # ms -> s
                    v /= 1000.0
                return datetime.fromtimestamp(v)
            except Exception:
                return None
        if isinstance(val, str):
            try:
                dt = parse_date(val)
                return _naive(dt)
            except Exception:
                return None
        if hasattr(val, "toPyDateTime"):
            try:
                return _naive(val.toPyDateTime())
            except Exception:
                return None
        return None

    try:
        if not isinstance(dados, dict):
            return False

        modo_local = (dados.get("modo") or dados.get("modo_busca") or "").strip().lower()
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
            ano = dados.get("ano")
            mes = dados.get("mes")
            periodicidade = (dados.get("periodicidade") or "bimestral").strip().lower()

            try:
                ano_i = int(ano)
                mes_i = int(mes)
            except Exception:
                print(f"[DEBUG dentro_periodo] sem contexto suficiente (ano={ano}, mes={mes})")
                return False

            try:
                ini_calc, end_calc, _ = bounds_do_periodo(ano_i, mes_i, periodicidade)
                ini = _to_dt(ini_calc)
                end = _to_dt(end_calc)
            except Exception as e:
                print(f"[DEBUG janela-skip] bounds_do_periodo erro: {e}")
                return False

        if ini is None or end is None:
            print(f"[DEBUG dentro_periodo] janela inválida ini={ini!r} end={end!r}")
            return False

        # Log consolidado (agora com TUDO definido)
        print(f"[DEBUG dentro_periodo] dp={dp} ini={ini} end={end}")

        # 3) comparação segura
        try:
            return ini <= dp <= end
        except Exception as e:
            # Se der TypeError, loga os tipos para depurar
            print(
                f"[DEBUG dentro_periodo] comparação falhou: {type(e).__name__}: {e} "
                f"(types: ini={type(ini)}, dp={type(dp)}, end={type(end)})"
            )
            return False

    except Exception as e:
        print(f"[DEBUG janela-skip] {type(e).__name__}: {e}")
        return False


def _carregar_regras(estado):
    """
    Retorna a lista de regras ativa.
    Preferência: estado["rules"]; fallback: ler de config_ofertas.json (se existir).
    """
    if isinstance(estado.get("rules"), list):
        return estado["rules"]

    # fallback leve (não explode se não houver arquivo)
    try:
        config_path = os.path.join(os.path.dirname(__file__), "config_ofertas.json")
        if os.path.exists(config_path):
            with open(config_path, encoding="utf-8") as f:
                cfg = json.load(f)
                regras = cfg.get("rules") or cfg.get("regras") or []
                if isinstance(regras, list):
                    # cache no estado p/ próximas chamadas
                    estado["rules"] = regras
                    return regras
    except Exception:
        pass

    return []  # sem regras


def iniciar_busca_assinaturas(
    ano,
    mes,
    modo_periodo,
    box_nome_input,
    estado,
    skus_info,
    *,
    periodicidade_selecionada,  # "mensal" | "bimestral"
):
    # normaliza periodicidade
    periodicidade = (periodicidade_selecionada or "").strip().lower()
    if periodicidade not in ("mensal", "bimestral"):
        periodicidade = "bimestral"

    # calcula janelas do período
    dt_ini, dt_end, periodo = bounds_do_periodo(int(ano), int(mes), periodicidade)
    box_nome = (box_nome_input.currentText() or "").strip()

    # bloqueia box indisponivel
    if box_nome and eh_indisponivel(box_nome):
        comunicador_global.mostrar_mensagem.emit(
            "erro",
            "Box indisponivel",
            f"O box selecionado (“{box_nome}”) está marcado como indisponivel no SKUs.",
        )
        return

    # carrega regras ativas
    regras = _carregar_regras(estado)

    # monta o payload de execução (o WorkerThread usa isso direto)
    dados = {
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

    # guarda contexto p/ outras partes da UI
    estado["contexto_busca_assinaturas"] = dados
    estado["skus_info"] = skus_info  # garante acesso dentro do Worker

    # ---- dispara em QThread via WorkerController ----
    # garante Event de cancelamento
    if not isinstance(estado.get("cancelador_global"), threading.Event):
        estado["cancelador_global"] = threading.Event()
    estado["cancelador_global"].clear()

    # evita execuções concorrentes
    if estado.get("worker_thread") and estado["worker_thread"].isRunning():
        comunicador_global.mostrar_mensagem.emit(
            "aviso", "Em andamento", "Já existe uma exportação em andamento."
        )
        return

    # mantém referência do controller para não ser coletado
    controller = WorkerController(dados, estado, skus_info)
    estado["worker_controller"] = controller

    # pode chamar o slot direto (ou emitir o sinal, como preferir)
    controller.iniciar_worker()
    # alternativa: controller.iniciar_worker_signal.emit()


def coletar_ids_assinaturas_por_periodicidade(skus_info: dict, periodicidade_sel: str):
    """
    Retorna dict com listas de product_ids (Guru) das assinaturas filtradas
    pela periodicidade ('mensal' | 'bimestral').
    Keys: 'anuais', 'bianuais', 'trianuais', 'bimestrais', 'mensais', 'todos'
    """
    periodicidade_sel = (periodicidade_sel or "").strip().lower()
    mapa_tipo = {
        "anual": "anuais",
        "bianual": "bianuais",
        "trianual": "trianuais",
        "bimestral": "bimestrais",
        "mensal": "mensais",
    }

    ids_por_tipo = {k: [] for k in ["anuais", "bianuais", "trianuais", "bimestrais", "mensais"]}
    todos = set()

    for info in (skus_info or {}).items():
        if (info.get("tipo") or "").lower() != "assinatura":
            continue
        if (info.get("periodicidade") or "").lower() != periodicidade_sel:
            continue

        duracao = (info.get("recorrencia") or "").lower()
        chave_tipo = mapa_tipo.get(duracao)
        if not chave_tipo:
            continue

        for gid in info.get("guru_ids", []):
            gid = str(gid).strip()
            if gid:
                ids_por_tipo[chave_tipo].append(gid)
                todos.add(gid)

    # dedup
    for k in ids_por_tipo:
        ids_por_tipo[k] = list(dict.fromkeys(ids_por_tipo[k]))
    ids_por_tipo["todos"] = list(todos)
    return ids_por_tipo


def buscar_transacoes_assinaturas(dados, *, atualizar=None, cancelador=None, estado=None):
    print("[🔍 buscar_transacoes_assinaturas] Início da função")

    transacoes = []
    if estado is None:
        estado = {}
    estado["transacoes_com_erro"] = []

    # ⚙️ contexto
    periodicidade_sel = (
        (dados.get("periodicidade") or dados.get("periodicidade_selecionada") or "").strip().lower()
    )
    if periodicidade_sel not in ("mensal", "bimestral"):
        periodicidade_sel = "bimestral"

    # garanta que o mapeamento está no estado
    estado.setdefault("skus_info", estado.get("skus_info", {}))
    skus_info = estado.get("skus_info", {})

    # ✅ IDs por periodicidade a partir do SKUs.json
    ids_map = coletar_ids_assinaturas_por_periodicidade(skus_info, periodicidade_sel)
    dados["ids_planos_todos"] = ids_map.get("todos", [])

    # 🗓 período indicado na UI
    dt_ini_sel = (
        dados.get("ordered_at_ini_periodo")
        or dados.get("ordered_at_ini_anual")
        or dados.get("ordered_at_ini_bimestral")
    )
    dt_end_sel = (
        dados.get("ordered_at_end_periodo")
        or dados.get("ordered_at_end_anual")
        or dados.get("ordered_at_end_bimestral")
    )

    if not dt_ini_sel or not dt_end_sel:
        raise ValueError(
            "ordered_at_ini / ordered_at_end não informados para o período selecionado."
        )

    # ================= Helpers de data =================
    def _as_dt(x):
        return x if isinstance(x, datetime) else datetime.fromisoformat(str(x))

    def _first_day_next_month(dt):
        y, m = dt.year, dt.month
        return datetime(y + (m // 12), 1 if m == 12 else m + 1, 1)

    def _last_moment_of_month(y, m):
        if m == 12:
            return datetime(y, 12, 31, 23, 59, 59, 999999)
        nxt = datetime(y, m + 1, 1)
        return nxt - timedelta(microseconds=1)

    def _inicio_mes_por_data(dt):
        return datetime(dt.year, dt.month, 1)

    def _inicio_bimestre_por_data(dt):
        # bimestres: (1-2), (3-4), (5-6), (7-8), (9-10), (11-12)
        m_ini = dt.month if dt.month % 2 == 1 else dt.month - 1
        return datetime(dt.year, m_ini, 1)

    def _fim_bimestre_por_data(dt):
        m_end = dt.month if dt.month % 2 == 0 else dt.month + 1
        y = dt.year
        if m_end == 13:
            y += 1
            m_end = 1
        return _last_moment_of_month(y, m_end)

    LIMITE_INFERIOR = datetime(2024, 10, 1)

    # ================= Normaliza período selecionado =================
    end_sel = _as_dt(dt_end_sel)
    if periodicidade_sel == "mensal":
        ini_sel = _inicio_mes_por_data(end_sel)
        end_sel = _last_moment_of_month(end_sel.year, end_sel.month)
    else:  # "bimestral"
        ini_sel = _inicio_bimestre_por_data(end_sel)
        end_sel = _fim_bimestre_por_data(end_sel)

    # ================= Constrói intervalos =================
    # Mensais e bimestrais: sempre o período selecionado (mês ou bimestre)
    intervalos_mensais = (
        dividir_busca_em_periodos(ini_sel, end_sel) if periodicidade_sel == "mensal" else []
    )
    intervalos_bimestrais = (
        dividir_busca_em_periodos(ini_sel, end_sel) if periodicidade_sel == "bimestral" else []
    )

    # Multi-ano: início = (primeiro dia do mês seguinte ao fim selecionado) - N anos, limitado por LIMITE_INFERIOR
    inicio_base = _first_day_next_month(end_sel)

    def _janela_multi_ano(n_anos):
        ini = datetime(inicio_base.year - n_anos, inicio_base.month, 1)
        ini = max(ini, LIMITE_INFERIOR)
        return dividir_busca_em_periodos(ini, end_sel)

    # ================= Modo do período (PERÍODO vs TODAS) =================
    # normaliza acentos para aceitar "PERÍODO" e "PERIODO"
    try:
        from unidecode import unidecode

        modo_sel_norm = unidecode((dados.get("modo_periodo") or "").strip().upper())
    except Exception:
        # fallback sem unidecode
        modo_sel_norm = (
            (dados.get("modo_periodo") or "").strip().upper().replace("Í", "I").replace("É", "E")
        )

    if modo_sel_norm == "PERIODO":
        # FIX (1): quando é PERÍODO/PERIODO, até os multi-ano buscam SÓ o mês/bimestre selecionado
        intervalos_anuais = dividir_busca_em_periodos(ini_sel, end_sel)
        intervalos_bianuais = dividir_busca_em_periodos(ini_sel, end_sel)
        intervalos_trianuais = dividir_busca_em_periodos(ini_sel, end_sel)
    else:
        # TODAS: mantém comportamento original (janelas de 1, 2 e 3 anos retroativas)
        intervalos_anuais = _janela_multi_ano(1)
        intervalos_bianuais = _janela_multi_ano(2)
        intervalos_trianuais = _janela_multi_ano(3)

    # ================= Executor =================
    def executar_lote(tarefas, label_progresso):
        # FIX (2): evita crash quando não há tarefas
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
                        transacoes.extend(resultado)
                    except Exception as e:
                        erro_msg = f"Erro ao buscar transações ({label_progresso}): {e!s}"
                        print(f"❌ {erro_msg}")
                        estado["transacoes_com_erro"].append(erro_msg)
                    finally:
                        concluidos += 1
                        if atualizar:
                            try:
                                atualizar(f"🔄 {label_progresso}", concluidos, total_futures)
                            except Exception:
                                pass
                futures = list(not_done)
        return True

    # ================= Tarefas (AGREGADAS) =================
    todas_tarefas = []

    print("[1️⃣] Gerando tarefas para anuais...")
    t = [
        (pid, ini, fim, "anuais")
        for pid in ids_map.get("anuais", [])
        for (ini, fim) in intervalos_anuais
    ]
    print(f"[📦] Total de tarefas anuais: {len(t)}")
    todas_tarefas.extend(t)

    print("[1.1️⃣] Gerando tarefas para bianuais...")
    t = [
        (pid, ini, fim, "bianuais")
        for pid in ids_map.get("bianuais", [])
        for (ini, fim) in intervalos_bianuais
    ]
    print(f"[📦] Total de tarefas bianuais: {len(t)}")
    todas_tarefas.extend(t)

    print("[1.2️⃣] Gerando tarefas para trianuais...")
    t = [
        (pid, ini, fim, "trianuais")
        for pid in ids_map.get("trianuais", [])
        for (ini, fim) in intervalos_trianuais
    ]
    print(f"[📦] Total de tarefas trianuais: {len(t)}")
    todas_tarefas.extend(t)

    print("[2️⃣] Gerando tarefas para bimestrais...]")
    t = [
        (pid, ini, fim, "bimestrais")
        for pid in ids_map.get("bimestrais", [])
        for (ini, fim) in intervalos_bimestrais
    ]
    print(f"[📦] Total de tarefas bimestrais: {len(t)}")
    todas_tarefas.extend(t)

    print("[3️⃣] Gerando tarefas para mensais...")
    t = [
        (pid, ini, fim, "mensais")
        for pid in ids_map.get("mensais", [])
        for (ini, fim) in intervalos_mensais
    ]
    print(f"[📦] Total de tarefas mensais: {len(t)}")
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


class TransientGuruError(Exception):
    """Erro transitório ao buscar a PRIMEIRA página; deve acionar retry externo."""

    pass


def buscar_transacoes_individuais(
    product_id,
    inicio,
    fim,
    *,
    cancelador=None,
    tipo_assinatura=None,
    timeout=(3, 15),  # (connect, read)
    max_page_retries=2,  # tentativas por página
):
    if cancelador and cancelador.is_set():
        print("[🚫] Cancelado no início de buscar_transacoes_individuais")
        return []

    print(
        f"[🔎 buscar_transacoes_individuais] Início - Produto: {product_id}, Período: {inicio} → {fim}"
    )

    resultado = []
    cursor = None
    pagina_count = 0
    total_transacoes = 0
    erro_final = False

    session = requests.Session()

    while True:
        if cancelador and cancelador.is_set():
            print("[🚫] Cancelado no meio da busca individual")
            break

        params = {
            "transaction_status[]": ["approved"],
            "ordered_at_ini": inicio,
            "ordered_at_end": fim,
            "product_id": product_id,
        }
        if cursor:
            params["cursor"] = cursor

        data = None
        last_exc = None

        # === tentativas por página ===
        for tentativa in range(max_page_retries + 1):
            if cancelador and cancelador.is_set():
                print("[🚫] Cancelado durante tentativa de página")
                break
            try:
                r = session.get(
                    f"{BASE_URL_GURU}/transactions",
                    headers=HEADERS_GURU,
                    params=params,
                    timeout=timeout,
                )
                if r.status_code != 200:
                    raise requests.HTTPError(f"HTTP {r.status_code}")
                data = r.json()
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
                    print(
                        f"❌ Falha ao obter página para {product_id} após {max_page_retries+1} tentativas: {e}"
                    )

        # Se não conseguiu obter esta página:
        if data is None:
            if pagina_count == 0 and total_transacoes == 0:
                # falhou logo de cara → deixa o wrapper decidir (retry externo)
                raise TransientGuruError(
                    f"Falha inicial ao buscar transações do produto {product_id}: {last_exc}"
                )
            else:
                # falhou depois de já ter coletado algo → devolve parciais
                erro_final = True
                break

        pagina = data.get("data", []) or []
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
        cursor = data.get("next_cursor")
        if not cursor:
            break

    status = "Concluído" if not erro_final else "Concluído (parcial)"
    print(
        f"[✅ buscar_transacoes_individuais] {status} - Produto {product_id} | Total: {total_transacoes} transações em {pagina_count} página(s)"
    )
    return resultado


def buscar_transacoes_com_retry(*args, cancelador=None, tentativas=3, **kwargs):
    for tentativa in range(tentativas):
        if cancelador and cancelador.is_set():
            print("[🚫] Cancelado dentro de buscar_transacoes_com_retry.")
            return []
        try:
            return buscar_transacoes_individuais(*args, cancelador=cancelador, **kwargs)
        except TransientGuruError as e:
            print(f"[⚠️ Retry {tentativa+1}/{tentativas}] {e}")
            if tentativa < tentativas - 1:
                espera = (2**tentativa) + random.random()
                time.sleep(espera)
            else:
                print("[❌] Falhou após retries; retornando vazio.")
                return []


# Funções auxiliares DMG

# ===== Regras (config_ofertas.json) =====


def _caminho_config_ofertas():
    return os.path.join(os.path.dirname(__file__), "config_ofertas.json")


def _ler_json_seguro(path, default):
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        return default
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except JSONDecodeError:
        return default


# === Canoniza: sempre expor/salvar em "rules", mas aceitar "regras" legado ===
def _normalizar_cfg(cfg: dict) -> dict:
    cfg = cfg or {}
    rules = cfg.get("rules")
    if rules is None:
        rules = cfg.get("regras")  # legado
    if not isinstance(rules, list):
        rules = []
    return {"rules": rules}


def carregar_config_ofertas():
    path = _caminho_config_ofertas()
    cfg = _ler_json_seguro(path, {"rules": []})
    return _normalizar_cfg(cfg)


def salvar_config_ofertas(cfg: dict):
    path = _caminho_config_ofertas()
    os.makedirs(os.path.dirname(path), exist_ok=True)
    cfg_norm = _normalizar_cfg(cfg)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(cfg_norm, f, indent=2, ensure_ascii=False)


def carregar_regras(config_path=None):
    path = config_path or _caminho_config_ofertas()
    data = _ler_json_seguro(path, {"rules": []})
    return _normalizar_cfg(data)["rules"]


def salvar_regras(config_path, rules):
    os.makedirs(os.path.dirname(config_path), exist_ok=True)
    with open(config_path, "w", encoding="utf-8") as f:
        json.dump({"rules": rules or []}, f, indent=2, ensure_ascii=False)


# Use o mesmo caminho e normalize ao ler
def obter_regras_config(path=None):
    path = path or _caminho_config_ofertas()
    try:
        with open(path, encoding="utf-8") as f:
            cfg = json.load(f)
    except FileNotFoundError:
        print(f"[⚠️] {path} não encontrado")
        return []
    except Exception as e:
        print(f"[⚠️ ERRO ao ler {path}]: {e}")
        return []
    return _normalizar_cfg(cfg)["rules"]


# Passe a escrever em "rules" e a usar as chaves do seu JSON atual: applies_to/action/cupom
def adicionar_regra_config(regra: dict):
    cfg = carregar_config_ofertas()
    rules = list(cfg.get("rules") or [])

    # dedup por conteúdo
    def _canon(r):
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


def remover_regra_config(regra_id: str):
    cfg = carregar_config_ofertas()
    rules = [r for r in (cfg.get("rules") or []) if r.get("id") != regra_id]
    salvar_config_ofertas({"rules": rules})


def formatar_valor(valor):
    return f"{valor:.2f}".replace(".", ",")


def recebe_box_do_periodo(
    ordered_at_end_anchor: datetime, data_check: datetime, periodicidade: str
) -> bool:
    periodicidade = (periodicidade or "bimestral").lower()

    if periodicidade == "mensal":
        ano = ordered_at_end_anchor.year
        mes = ordered_at_end_anchor.month
        inicio = datetime(ano, mes, 1)
        fim = (
            (datetime(ano + 1, 1, 1) - timedelta(seconds=1))
            if mes == 12
            else (datetime(ano, mes + 1, 1) - timedelta(seconds=1))
        )
        return inicio <= data_check <= fim

    # bimestral (padrão)
    mes = ordered_at_end_anchor.month
    ano = ordered_at_end_anchor.year
    primeiro_mes = ((mes - 1) // 2) * 2 + 1
    inicio = datetime(ano, primeiro_mes, 1)
    fim = (
        (datetime(ano + 1, 1, 1) - timedelta(days=1))
        if primeiro_mes + 1 == 12
        else (datetime(ano, primeiro_mes + 2, 1) - timedelta(seconds=1))
    )
    return inicio <= data_check <= fim


def configurar_cancelamento_em_janela(janela, cancelador):
    def ao_fechar(event):
        if hasattr(cancelador, "set"):
            cancelador.set()
        event.accept()

    janela.closeEvent = ao_fechar


def eh_indisponivel(produto_nome: str) -> bool:
    """
    Compat: mantém o nome antigo, mas agora retorna True
    se o produto estiver marcado como indisponivel no skus.json.
    """
    if not produto_nome:
        return False

    skus = estado.get("skus_info") or {}
    info = skus.get(produto_nome)

    # fallback por normalização de nome (sem acento/caixa) caso a chave não bata 1:1
    if info is None:
        alvo = unidecode(str(produto_nome)).lower().strip()
        for nome, i in skus.items():
            if unidecode(nome).lower().strip() == alvo:
                info = i
                break

    return bool(info and info.get("indisponivel", False))


def normalizar(texto):
    texto = unicodedata.normalize("NFD", texto)
    texto = texto.encode("ascii", "ignore").decode("utf-8")
    return texto.lower()


def encontrar_nome_padrao(nome_busca, skus_info):
    nome_norm = normalizar(nome_busca)
    for nome_padrao in skus_info:
        if normalizar(nome_padrao) in nome_norm:
            return nome_padrao
    return None


# Processar planilha DMG


def gerar_linha_base(
    contact, valores, transacao, tipo_plano="", subscription_id="", cupom_valido=""
):
    telefone = contact.get("phone_number", "")
    return {
        # Comprador
        "Nome Comprador": contact.get("name", ""),
        "Data Pedido": valores["data_pedido"].strftime("%d/%m/%Y"),
        "Data": datetime.today().strftime("%d/%m/%Y"),
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
    }


def desmembrar_produto_combo(valores, linha_base, skus_info):
    """
    - valores["produto_principal"] = nome do combo
    - valores["valor_total"]       = total do combo (float/int ou string com vírgula)
    - skus_info[nome_combo]["composto_de"] = [SKUs...]
    - skus_info[produto_simples]["sku"] = SKU do produto simples
    """
    nome_combo = valores.get("produto_principal", "")
    info_combo = skus_info.get(nome_combo, {})
    skus_componentes = [s for s in info_combo.get("composto_de", []) if str(s).strip()]

    # Se não há componentes, retorna a linha original
    if not skus_componentes:
        return [linha_base]

    # Helper: parse total (aceita 12,34 / 12.34 / 1.234,56)
    def _to_dec(v):
        if v is None:
            return Decimal("0.00")
        if isinstance(v, int | float):
            return Decimal(str(v)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        s = str(v).strip()
        # normaliza "1.234,56" -> "1234.56"
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
                (nome for nome, info in skus_info.items() if info.get("sku") == sku), sku
            )
            nova = linha_base.copy()
            nova["Produto"] = nome_item
            nova["SKU"] = sku
            nova["Valor Unitário"] = "0,00"
            nova["Valor Total"] = "0,00"
            nova["Combo"] = nome_combo  # remova se não quiser essa coluna
            nova["indisponivel"] = "S" if eh_indisponivel(nome_item) else ""
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
        linhas.append(nova)

    return linhas


def processar_planilha(transacoes, dados, atualizar_etapa, skus_info, cancelador, estado):
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

    linhas_planilha = []
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
    def _append_linha(linha, transaction_id):
        linhas_planilha.append(linha)
        estado["mapa_transaction_id_por_linha"][offset + len(linhas_planilha) - 1] = transaction_id

    # helper: flag de indisponível
    def _flag_indisp(nome):
        try:
            return "S" if eh_indisponivel(nome) else ""
        except Exception:
            return ""

    # helper: janela segura (não explode se faltar ano/mês/ini/end)
    def _aplica_janela(dados_local, dt):
        try:
            return dentro_periodo_selecionado(dados_local, dt)
        except Exception as e:
            print(f"[DEBUG janela-skip] Ignorando janela por falta de contexto: {e}")
            # Sem contexto de período → NÃO aplica regras
            return False

    # helper: normaliza para timestamp
    def _to_ts(val):
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

    # flatten defensivo
    transacoes_corrigidas = []

    for idx, t in enumerate(transacoes):
        if isinstance(t, dict):
            transacoes_corrigidas.append(t)
        elif isinstance(t, list):
            print(f"[⚠️ processar_planilha] Corrigindo lista aninhada em transacoes[{idx}]")
            for sub in t:
                if isinstance(sub, dict):
                    transacoes_corrigidas.append(sub)
                else:
                    print(
                        f"[⚠️ Ignorado] Item inesperado do tipo {type(sub)} dentro de transacoes[{idx}]"
                    )
        else:
            print(f"[⚠️ Ignorado] transacoes[{idx}] é do tipo {type(t)} e será ignorado")

    transacoes = transacoes_corrigidas
    total_transacoes = len(transacoes)

    ids_planos_validos = dados.get("ids_planos_todos", [])
    modo = (dados.get("modo", "assinaturas") or "").strip().lower()
    ofertas_embutidas = dados.get("ofertas_embutidas", {}) or {}
    modo_periodo_sel = (dados.get("modo_periodo") or "").strip().upper()
    print(
        f"[DEBUG processar_planilha] Iniciando processamento: total_transacoes={len(transacoes)} modo={modo} modo_periodo={modo_periodo_sel}"
    )

    def is_transacao_principal(trans, ids_validos):
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
                valores = calcular_valores_pedido(
                    transacao, dados, skus_info, usar_valor_fixo=False
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
                        "indisponivel": _flag_indisp(nome_produto),
                    }
                )

                print(
                    f"[DEBUG produtos:combo] i={i} composto_de={bool(info_combo.get('composto_de'))}"
                )

                if info_combo.get("composto_de"):
                    for linha_item in desmembrar_produto_combo(valores, linha_base, skus_info):
                        linha_item["indisponivel"] = _flag_indisp(linha_item.get("Produto", ""))
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
        transacoes_por_assinatura = defaultdict(list)
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

            def safe_parse_date(t):
                try:
                    return parse_date(t.get("ordered_at") or t.get("created_at") or "1900-01-01")
                except Exception:
                    return datetime(1900, 1, 1)

            print(
                f"[DEBUG assinatura] subscription_id={subscription_id} qtd_transacoes={len(grupo_transacoes)}"
            )
            grupo_ordenado = sorted(grupo_transacoes, key=safe_parse_date)
            transacao_base = grupo_ordenado[-1]
            tipo_plano = transacao_base.get("tipo_assinatura", "bimestrais")
            print(
                f"[DEBUG assinatura] subscription_id={subscription_id} primeira={grupo_ordenado[0].get('ordered_at') or grupo_ordenado[0].get('created_at')} ultima={grupo_ordenado[-1].get('ordered_at') or grupo_ordenado[-1].get('created_at')}"
            )
            transacoes_principais = [
                t for t in grupo_ordenado if is_transacao_principal(t, ids_planos_validos)
            ]
            produtos_distintos = {
                t.get("product", {}).get("internal_id") for t in transacoes_principais
            }

            usar_valor_fixo = (
                len(produtos_distintos) > 1
                or transacao_base.get("invoice", {}).get("type") == "upgrade"
            )

            if not transacoes_principais:
                print(
                    f"[⚠️ AVISO] Nenhuma transação principal encontrada para assinatura {subscription_id}"
                )

            if usar_valor_fixo:
                valor_total_principal = 0.0
            elif transacoes_principais:
                valor_total_principal = sum(
                    float(t.get("payment", {}).get("total", 0)) for t in transacoes_principais
                )
            else:
                valor_total_principal = float(transacao_base.get("payment", {}).get("total", 0))

            # monta transação "sintética"
            transacao = transacao_base.copy()
            transacao.setdefault("payment", {})
            transacao["payment"]["total"] = valor_total_principal
            transacao["tipo_assinatura"] = tipo_plano
            transacao["subscription"] = {"id": subscription_id}

            # 👇 garante o dict e só copia offer se existir no base
            product_base = transacao_base.get("product") or {}
            transacao.setdefault("product", {})
            if "offer" not in transacao["product"] and product_base.get("offer"):
                transacao["product"]["offer"] = product_base["offer"]

            try:
                print(
                    f"[DEBUG calcular_valores_pedido] subscription_id={subscription_id} transacao_id={transacao.get('id')} ordered_at={transacao.get('ordered_at')} created_at={transacao.get('created_at')}"
                )
                valores = calcular_valores_pedido(
                    transacao, dados, skus_info, usar_valor_fixo=usar_valor_fixo
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
                linha = gerar_linha_base(
                    contact,
                    valores,
                    transacao,
                    tipo_plano=tipo_plano,
                    subscription_id=subscription_id,
                    cupom_valido=cupom_usado,
                )

                nome_produto_principal = (dados.get("box_nome") or "").strip() or valores[
                    "produto_principal"
                ]
                if eh_indisponivel(nome_produto_principal):
                    estado["boxes_indisp_set"].add(nome_produto_principal)

                linha["Produto"] = nome_produto_principal
                linha["SKU"] = skus_info.get(nome_produto_principal, {}).get("sku", "")
                linha["Valor Unitário"] = formatar_valor(valores["valor_unitario"])
                linha["Valor Total"] = formatar_valor(valores["valor_total"])
                linha["periodicidade"] = periodicidade_atual
                linha["indisponivel"] = _flag_indisp(nome_produto_principal)

                # período
                def calcular_periodo(periodicidade, data_ref):
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
                    mes_ref = (
                        data_fim_periodo if isinstance(data_fim_periodo, datetime) else data_pedido
                    )
                    linha["periodo"] = calcular_periodo(periodicidade_atual, mes_ref)

                _append_linha(linha, valores["transaction_id"])

                # ✅ NUNCA aplicar brindes fora da janela
                if not _aplica_janela(dados, data_pedido):
                    valores["brindes_extras"] = []

                # 🎁 brindes extras (somente dentro da janela)
                for brinde_nome in valores.get("brindes_extras") or []:
                    sku_b = skus_info.get(brinde_nome, {}).get("sku", "")
                    linha_b = linha.copy()
                    linha_b.update(
                        {
                            "Produto": brinde_nome,
                            "SKU": sku_b,
                            "Valor Unitário": "0,00",
                            "Valor Total": "0,00",
                            "indisponivel": _flag_indisp(brinde_nome),
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
                nome_embutido_oferta = ofertas_normalizadas.get(oferta_id_clean)

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
                            "indisponivel": _flag_indisp(nome_embutido_oferta),
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
    df_novas = padronizar_planilha_importada(df_novas)

    # normaliza "indisponivel"
    if "indisponivel" in df_novas.columns:
        df_novas["indisponivel"] = df_novas["indisponivel"].map(
            lambda x: "S" if str(x).strip().lower() in {"s", "sim", "true", "1"} else ""
        )
    else:
        df_novas["indisponivel"] = [""] * len(df_novas)

    # sanity opcional: garantir subscription_id em todas as novas linhas
    if (
        "subscription_id" in df_novas.columns
        and df_novas["subscription_id"].astype(str).str.strip().eq("").any()
    ):
        faltantes = df_novas[df_novas["subscription_id"].astype(str).str.strip().eq("")]
        print(
            f"[⚠️ SANIDADE] {len(faltantes)} linha(s) sem subscription_id; verifique geração de linhas derivadas."
        )
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
            msgs.append(
                f"Brindes indisponíveis: {lst_brindes} (serão ignorados na etapa de lotes)."
            )
        if estado.get("embutidos_indisp_set"):
            lst_embutidos = ", ".join(sorted(estado["embutidos_indisp_set"]))
            msgs.append(
                f"Embutidos indisponíveis: {lst_embutidos} (serão ignorados na etapa de lotes)."
            )
        if msgs and comunicador_global is not None:
            comunicador_global.mostrar_mensagem.emit(
                "aviso", "Itens indisponíveis", "\n".join(msgs)
            )
    except Exception:
        pass

    return linhas_planilha, contagem


def _norm(s: str) -> str:
    return unidecode((s or "").strip().lower())


def aplicar_regras_transaction(transacao: dict, dados: dict, base_produto_principal: str):
    """
    Lê config_ofertas.json e aplica:
      - override da box (action.type == 'alterar_box')
      - brindes extras (action.type == 'adicionar_brindes')
    Compatível com rótulos do JSON como:
      "Assinatura 2 anos (bimestral)", "Assinatura Anual (mensal)", "Assinatura Bimestral (bimestral)" etc.
    Sem mudar o JSON.
    """
    regras = obter_regras_config() or []
    res_override = None
    res_override_score = -1
    brindes = []

    # --- contexto da transação ---
    payment = transacao.get("payment") or {}
    coupon = payment.get("coupon") or {}
    coupon_code_norm = _norm(coupon.get("coupon_code") or "")

    tipo_ass = (
        (transacao.get("tipo_assinatura") or "").strip().lower()
    )  # anuais, bianuais, trianuais, bimestrais, mensais
    periodicidade = (
        (dados.get("periodicidade_selecionada") or dados.get("periodicidade") or "").strip().lower()
    )

    # Mapeia tipo_ass + periodicidade -> rótulos usados no JSON
    def _labels_assinatura(tipo_ass: str, periodicidade: str) -> set[str]:
        # exemplos no JSON:
        # "Assinatura 2 anos (bimestral)", "Assinatura 3 anos (mensal)",
        # "Assinatura Anual (bimestral)", "Assinatura Bimestral (bimestral)"
        base = []
        if tipo_ass == "bianuais":
            base.append("Assinatura 2 anos")
        elif tipo_ass == "trianuais":
            base.append("Assinatura 3 anos")
        elif tipo_ass == "anuais":
            base.append("Assinatura Anual")
        elif tipo_ass == "bimestrais":
            base.append("Assinatura Bimestral")
        elif tipo_ass == "mensais":
            base.append("Assinatura Mensal")
        # anexa a periodicidade entre parênteses se existir
        out = set()
        for b in base or ["Assinatura"]:
            if periodicidade:
                out.add(f"{b} ({periodicidade})")
            else:
                out.add(b)
        return {_norm(x) for x in out}

    labels_alvo = _labels_assinatura(tipo_ass, periodicidade)
    base_prod_norm = _norm(base_produto_principal)

    def _assinatura_match(lista: list[str] | None) -> tuple[bool, int]:
        """
        Retorna (casou?, score). Score maior = mais específico.
        Regras:
          - lista vazia => aplica (score 0)
          - se qualquer item da lista bate exatamente com um dos rótulos conhecidos -> score 3
          - se item corresponde ao nome do box atual -> score 2
          - se item contém tokens genéricos (anual / 2 anos / 3 anos / mensal / bimestral) presentes no rótulo -> score 1
        """
        if not lista:
            return True, 0

        tokens_genericos = {"anual", "2 anos", "3 anos", "mensal", "bimestral"}
        best = -1
        casou = False
        alvo_concat = " ".join(sorted(labels_alvo))  # string para buscas simples

        for it in lista:
            itn = _norm(it or "")
            if not itn:
                # trata string vazia como "todas"
                casou, best = True, max(best, 0)
                continue
            # Match mais específico: rótulo completo
            if itn in labels_alvo:
                casou, best = True, max(best, 3)
                continue
            # Nome do box
            if itn == base_prod_norm:
                casou, best = True, max(best, 2)
                continue
            # Token genérico presente no rótulo atual
            if itn in tokens_genericos and itn in alvo_concat:
                casou, best = True, max(best, 1)

        return casou, (best if best >= 0 else -1)

    for r in regras:
        if (r.get("applies_to") or "").strip().lower() != "cupom":
            continue

        cupom_cfg = r.get("cupom") or {}
        alvo_cupom = _norm(cupom_cfg.get("nome") or "")
        if not alvo_cupom or alvo_cupom != coupon_code_norm:
            continue

        assinaturas_lista = r.get("assinaturas") or []
        ok, score = _assinatura_match(assinaturas_lista)
        if not ok:
            continue

        action = r.get("action") or {}
        atype = (action.get("type") or "").strip().lower()

        if atype == "adicionar_brindes":
            brindes.extend(action.get("brindes") or [])

        elif atype == "alterar_box":
            # escolhe a mais específica (maior score)
            box = (action.get("box") or "").strip()
            if box:
                if score > res_override_score:
                    res_override = box
                    res_override_score = score

    # Normalização final: remove duplicatas de brindes e ignora iguais ao box
    override_norm = _norm(res_override or base_produto_principal)
    uniq = []
    seen = set()
    for b in brindes:
        nb = (b or "").strip()
        if not nb:
            continue
        nbn = _norm(nb)
        if nbn in (base_prod_norm, override_norm):
            continue
        if nbn not in seen:
            uniq.append(nb)
            seen.add(nbn)

    return {"override_box": res_override, "brindes_extra": uniq}


def calcular_valores_pedido(transacao, dados, skus_info, usar_valor_fixo=False):

    def _to_ts(val):
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

    modo = (dados.get("modo") or "").strip().lower()

    transaction_id = transacao.get("id", "")
    product = transacao.get("product") or {}
    internal_id = str(product.get("internal_id") or "").strip()
    offer = product.get("offer") or {}
    id_oferta = offer.get("id", "")

    print(
        f"[DEBUG calcular_valores_pedido] id={transaction_id} internal_id={internal_id} modo={modo}"
    )

    invoice = transacao.get("invoice") or {}
    is_upgrade = invoice.get("type") == "upgrade"

    # 🔐 data_pedido robusta (timestamp seg/ms ou ISO; normaliza para naive)
    ts = (transacao.get("dates") or {}).get("ordered_at")
    if ts is not None:
        try:
            val = float(ts)
            if val > 1e12:  # ms → s
                val = val / 1000.0
            data_pedido = datetime.fromtimestamp(val)
        except Exception:
            s = transacao.get("ordered_at") or transacao.get("created_at") or "1970-01-01"
            dt = parse_date(s)
            data_pedido = dt.replace(tzinfo=None) if getattr(dt, "tzinfo", None) else dt
    else:
        s = transacao.get("ordered_at") or transacao.get("created_at") or "1970-01-01"
        dt = parse_date(s)
        data_pedido = dt.replace(tzinfo=None) if getattr(dt, "tzinfo", None) else dt

    payment = transacao.get("payment") or {}
    try:
        valor_total_pago = float(payment.get("total") or 0)
    except Exception:
        valor_total_pago = 0.0

    coupon_info_raw = payment.get("coupon", {})
    coupon_info = coupon_info_raw if isinstance(coupon_info_raw, dict) else {}
    cupom = (coupon_info.get("coupon_code") or "").strip().lower()
    incidence_type = str(coupon_info.get("incidence_type") or "").strip().lower()

    # 🔎 produto principal (via internal_id → skus_info) com fallbacks
    produto_principal = None
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
            print(
                f"[⚠️ calcular_valores_pedido] skus_info vazio; retornando estrutura mínima para '{transaction_id}'."
            )
            return {
                "transaction_id": transaction_id,
                "id_oferta": id_oferta,
                "produto_principal": "",
                "sku_principal": "",
                "peso_principal": 0,
                "valor_unitario": round(valor_total_pago, 2),
                "valor_total": round(valor_total_pago, 2),
                "total_pedido": round(valor_total_pago, 2),
                "valor_embutido": 0.0,
                "incluir_embutido": False,
                "embutido": "",
                "brindes_extras": [],
                "data_pedido": data_pedido,
                "forma_pagamento": payment.get("method", "") or "",
                "usou_cupom": bool(cupom),
                "tipo_plano": "",
                "periodicidade": "",
                "divisor": 1,
            }

    info_produto = skus_info.get(produto_principal, {}) or {}
    sku_principal = info_produto.get("sku", "")
    peso_principal = info_produto.get("peso", 0)

    # 🚫 Sem regras para 'produtos' OU quando não tiver assinatura
    if modo == "produtos" or not transacao.get("subscription"):
        return {
            "transaction_id": transaction_id,
            "id_oferta": id_oferta,
            "produto_principal": produto_principal,
            "sku_principal": sku_principal,
            "peso_principal": peso_principal,
            "valor_unitario": round(valor_total_pago, 2),
            "valor_total": round(valor_total_pago, 2),
            "total_pedido": round(valor_total_pago, 2),
            "valor_embutido": 0.0,
            "incluir_embutido": False,
            "embutido": "",
            "brindes_extras": [],
            "data_pedido": data_pedido,
            "forma_pagamento": payment.get("method", "") or "",
            "usou_cupom": bool(cupom),
            "tipo_plano": "",
            "periodicidade": "",
            "divisor": 1,
        }

    # =========================
    # ASSINATURAS
    # =========================
    # ✅ janela/regras protegidas
    try:
        print(f"[DEBUG janela-check] id={transaction_id} data_pedido={data_pedido}")
        aplica_regras_neste_periodo = dentro_periodo_selecionado(dados, data_pedido)
    except Exception as e:
        print(f"[DEBUG janela-skip] Erro em dentro_periodo_selecionado: {e}")
        aplica_regras_neste_periodo = False

    # Regras/cupom/override só se dentro do período
    if aplica_regras_neste_periodo:
        try:
            regras_aplicadas = (
                aplicar_regras_transaction(transacao, dados, skus_info, produto_principal) or {}
            )
        except Exception as e:
            print(f"[⚠️ regras] Erro em aplicar_regras_transaction: {e}")
            regras_aplicadas = {}
    else:
        regras_aplicadas = {}

    override_box = regras_aplicadas.get("override_box")
    brindes_extra_por_regra = regras_aplicadas.get("brindes_extra", []) or []

    if override_box:
        produto_principal = override_box
        info_produto = skus_info.get(produto_principal, {}) or {}
        sku_principal = info_produto.get("sku", "")
        peso_principal = info_produto.get("peso", 0)

    tipo_assinatura = transacao.get("tipo_assinatura", "") or ""

    # Cupons personalizados só se dentro do período
    if aplica_regras_neste_periodo:
        if tipo_assinatura == "anuais":
            prod_custom = (dados.get("cupons_personalizados_anual") or {}).get(cupom)
        elif tipo_assinatura == "bimestrais":
            prod_custom = (dados.get("cupons_personalizados_bimestral") or {}).get(cupom)
        else:
            prod_custom = None
        if prod_custom and prod_custom in skus_info:
            produto_principal = prod_custom
            info_produto = skus_info.get(produto_principal, {}) or {}
            sku_principal = info_produto.get("sku", "")
            peso_principal = info_produto.get("peso", 0)

    # periodicidade: override manual → produto → inferência
    periodicidade = (
        dados.get("periodicidade_selecionada")
        or dados.get("periodicidade")
        or info_produto.get("periodicidade")
        or ("mensal" if tipo_assinatura == "mensais" else "bimestral")
    )
    periodicidade = str(periodicidade or "").strip().lower()

    # embutido via oferta (respeita timestamps E a janela)
    nome_embutido = (dados.get("ofertas_embutidas") or {}).get(str(id_oferta).strip(), "") or ""
    ini_ts = _to_ts(dados.get("embutido_ini_ts"))
    end_ts = _to_ts(dados.get("embutido_end_ts"))
    dp_ts = _to_ts(data_pedido)

    incluir_embutido = bool(
        nome_embutido
        and dp_ts is not None
        and ini_ts is not None
        and end_ts is not None
        and ini_ts <= dp_ts <= end_ts
        and aplica_regras_neste_periodo
    )
    valor_embutido = 0.0

    # 💰 tabela para assinaturas multi-ano
    tabela_valores = {
        ("anuais", "mensal"): 960,
        ("anuais", "bimestral"): 480,
        ("bianuais", "mensal"): 1920,
        ("bianuais", "bimestral"): 960,
        ("trianuais", "mensal"): 2880,
        ("trianuais", "bimestral"): 1440,
    }

    # Cálculo do valor da assinatura
    if is_upgrade or usar_valor_fixo:
        valor_assinatura = float(
            tabela_valores.get((tipo_assinatura, periodicidade), valor_total_pago)
        )
        if incidence_type == "percent":
            try:
                desconto = float(coupon_info.get("incidence_value") or 0)
            except Exception:
                desconto = 0.0
            valor_assinatura = round(valor_assinatura * (1 - desconto / 100), 2)
        incluir_embutido = False
        valor_embutido = 0.0

    elif tipo_assinatura in ("anuais", "bianuais", "trianuais"):
        valor_assinatura = float(
            tabela_valores.get((tipo_assinatura, periodicidade), valor_total_pago)
        )
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
    valor_unitario = round(valor_assinatura / divisor, 2)
    valor_total = valor_unitario
    total_pedido = round(valor_unitario + (valor_embutido if incluir_embutido else 0.0), 2)

    return {
        "transaction_id": transaction_id,
        "id_oferta": id_oferta,
        "produto_principal": produto_principal,
        "sku_principal": sku_principal,
        "peso_principal": peso_principal,
        "valor_unitario": valor_unitario,
        "valor_total": valor_total,
        "total_pedido": total_pedido,
        "valor_embutido": valor_embutido,
        "incluir_embutido": incluir_embutido,
        "embutido": nome_embutido,
        "brindes_extras": brindes_extra_por_regra,
        "data_pedido": data_pedido,
        "forma_pagamento": payment.get("method", "") or "",
        "usou_cupom": bool(cupom),
        "tipo_plano": tipo_assinatura,
        "periodicidade": periodicidade,  # ✅ ponto único de verdade
        "divisor": divisor,
    }


# Exibe resumo DMG


def exibir_resumo_final(linhas, contagem, estado, modo="assinaturas"):
    """
    - modo="produtos": mostra total e lista de produtos adicionados (nome -> qtd).
    - modo≠"produtos": além do bloco de assinaturas, mostra:
        • Itens extras (brindes/embutidos): nome -> qtd
        • Trocas de box: detalhes (se disponíveis) ou totais por período.
    """

    def _is_zero(v):
        s = str(v or "").strip()
        if not s:
            return False
        try:
            # lida com "0,00", "0.00", "0", etc.
            s_norm = s.replace(".", "").replace(",", ".")
            return abs(float(s_norm)) < 1e-9
        except Exception:
            return False

    def _pega_bloco(cont, chaves):
        for k in chaves:
            v = (cont or {}).get(k)
            if v is not None:
                return v or {}
        return {}

    def _normaliza_swaps(raw):
        """
        Aceita:
          - dict {("De","Para"): qtd}  OU  {"De → Para": qtd}
          - dict {"De": {"Para": qtd, ...}, ...}
          - Counter com chaves como acima
        Retorna lista [(de, para, qtd), ...]
        """
        out = []
        if not raw:
            return out

        if isinstance(raw, Counter):
            raw = dict(raw)

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

        # formato plano: chaves tuple ou string "De → Para"
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
                ks = str(k).split("->")
                if len(ks) == 2:
                    de, para = ks[0].strip(), ks[1].strip()
                else:
                    ks = str(k).split("→")
                    if len(ks) == 2:
                        de, para = ks[0].strip(), ks[1].strip()
                    else:
                        # se não der para separar, trata como destino desconhecido
                        de, para = str(k), "?"
            out.append((str(de), str(para), q))
        return out

    try:
        modo = (modo or "").strip().lower()
        linhas = linhas or []
        total_linhas = len(linhas)

        # ---- Contagem geral de produtos por nome (todas as linhas)
        produtos_ctr = Counter()
        for lin in linhas:
            if isinstance(lin, dict):
                nome = lin.get("Produto") or lin.get("produto") or lin.get("nome_produto") or ""
                nome = str(nome).strip()
                if nome:
                    produtos_ctr[nome] += 1

        # ---------- MODO PRODUTOS ----------
        if modo == "produtos":

            msg = [f"📦 Linhas adicionadas: {total_linhas}"]
            if produtos_ctr:
                msg.append("\n🧾 Produtos adicionados:")
                for nome, qtd in produtos_ctr.most_common():
                    msg.append(f"  - {nome}: {qtd}")
            else:
                msg.append("\n🧾 Produtos adicionados: 0")

            comunicador_global.mostrar_mensagem.emit(
                "info", "Resumo da Exportação (Produtos)", "\n".join(msg)
            )
            return

        # ---------- MODO ASSINATURAS ----------
        resumo = f"📦 Linhas adicionadas: {total_linhas}\n\n📘 Assinaturas:\n"

        TIPOS = [
            ("mensais", ["mensais", "mensal"]),
            ("bimestrais", ["bimestrais", "bimestral"]),
            ("anuais", ["anuais", "anual"]),
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
        extras_ctr = Counter()
        for lin in linhas:
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
        # 1) tenta detalhes
        swaps_raw = (estado or {}).get("alteracoes_box_detalhes") or (contagem or {}).get(
            "alteracoes_box_detalhes"
        )
        swaps_list = _normaliza_swaps(swaps_raw)

        if swaps_list:
            resumo += "\n🔁 Trocas de box (detalhes):\n"
            for de, para, qtd in sorted(swaps_list, key=lambda x: (-x[2], x[0], x[1])):
                resumo += f"  - {de} → {para}: {qtd}\n"
        else:
            # 2) senão, mostra totais por período se houver
            tem_trocas = any(
                int(_pega_bloco(contagem, ch).get("alteracoes_box", 0) or 0) > 0 for _, ch in TIPOS
            )
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


# Importação de planilha DMG


def importar_envios_realizados_planilha():
    caminho_arquivo, _ = QFileDialog.getOpenFileName(
        None, "Selecionar planilha de envios já realizados", "", "Planilhas (*.xlsx *.xls *.csv)"
    )
    if not caminho_arquivo:
        return

    try:
        df = (
            pd.read_excel(caminho_arquivo)
            if caminho_arquivo.endswith((".xls", ".xlsx"))
            else pd.read_csv(caminho_arquivo)
        )
        df.columns = [str(c).strip().lower() for c in df.columns]

        if "id transação" not in df.columns and "assinatura código" not in df.columns:
            comunicador_global.mostrar_mensagem.emit(
                "erro",
                "Erro",
                "A planilha deve conter a coluna 'id transação' e/ou 'assinatura código'.",
            )
            return

        df["transaction_id"] = (
            (df.get("id transação") or "").astype(str).str.strip()
            if "id transação" in df.columns
            else ""
        )
        df["subscription_id"] = (
            (df.get("assinatura código") or "").astype(str).str.strip()
            if "assinatura código" in df.columns
            else ""
        )

        # pergunta ano/mês
        ano_atual = datetime.today().year
        mes_padrao = datetime.today().month
        ano, ok1 = QInputDialog.getInt(
            None, "Selecionar Ano", "Ano do envio:", value=ano_atual, min=2020, max=2035
        )
        if not ok1:
            return
        mes, ok2 = QInputDialog.getInt(
            None, "Selecionar Mês", "Mês (1 a 12):", value=mes_padrao, min=1, max=12
        )
        if not ok2:
            return
        bimestre = 1 + (mes - 1) // 2

        # pergunta periodicidade
        periodicidades = ["mensal", "bimestral"]
        periodicidade, okp = QInputDialog.getItem(
            None, "periodicidade", "Periodicidade dos registros:", periodicidades, editable=False
        )
        if not okp:
            return

        registros_assinaturas = []
        registros_produtos = []
        registro_em = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        for _, r in df.iterrows():
            sid = str(r.get("subscription_id", "")).strip()
            tid = str(r.get("transaction_id", "")).strip()

            if sid:
                periodo = mes if periodicidade == "mensal" else bimestre
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
                registros_produtos.append({"transaction_id": tid, "registro_em": registro_em})

        if not registros_assinaturas and not registros_produtos:
            comunicador_global.mostrar_mensagem.emit(
                "aviso", "Aviso", "Nenhum registro válido encontrado para salvar."
            )
            return

        caminho_excel = os.path.join(os.path.dirname(__file__), "Envios", "envios_log.xlsx")
        os.makedirs(os.path.dirname(caminho_excel), exist_ok=True)

        if registros_assinaturas:
            salvar_em_excel_sem_duplicados(
                caminho_excel, registros_assinaturas, sheet_name="assinaturas"
            )
        if registros_produtos:
            salvar_em_excel_sem_duplicados(caminho_excel, registros_produtos, sheet_name="produtos")

        total = len(registros_assinaturas) + len(registros_produtos)
        comunicador_global.mostrar_mensagem.emit(
            "info",
            "Importação concluída",
            f"{total} registro(s) foram adicionados ao log de envios.",
        )

    except Exception as e:
        comunicador_global.mostrar_mensagem.emit(
            "erro", "Erro", f"Erro ao importar a planilha:\n{e}"
        )


def padronizar_planilha_importada(df: pd.DataFrame, preservar_extras: bool = True) -> pd.DataFrame:
    colunas_padrao = [
        "Número pedido",
        "Nome Comprador",
        "Data",
        "Data Pedido",
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
        # 👇 importantes p/ pipeline
        "indisponivel",  # mantemos a marcação feita na coleta
        "ID Lote",  # será preenchido no aplicar_lotes
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


def importar_planilha_pedidos_guru():
    caminho, _ = QFileDialog.getOpenFileName(
        None, "Selecione a planilha de pedidos", "", "Arquivos CSV (*.csv);;Arquivos Excel (*.xlsx)"
    )
    if not caminho:
        return

    try:
        if caminho.endswith(".csv"):
            df = pd.read_csv(caminho, sep=";", encoding="utf-8", quotechar='"', dtype=str)
        else:
            df = pd.read_excel(caminho)
    except Exception as e:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro", f"Erro ao carregar planilha: {e}")
        return

    # 🔽 Selecionar produto a partir do skus.json
    nomes_produtos = sorted(skus_info.keys())
    produto_nome, ok = QInputDialog.getItem(
        None,
        "Selecionar Produto",
        "Escolha o nome do produto para todas as linhas:",
        nomes_produtos,
        editable=False,
    )
    if not ok or not produto_nome:
        return

    info_produto = skus_info.get(produto_nome)
    if not info_produto:
        comunicador_global.mostrar_mensagem.emit(
            "erro", "Produto não encontrado", f"'{produto_nome}' não está no skus.json"
        )
        return

    sku = info_produto.get("sku", "")

    # ===== Helpers =====
    def parse_money(val):
        if pd.isna(val) or str(val).strip() == "":
            return 0.0
        s = str(val).strip().replace(".", "").replace(",", ".")
        try:
            return round(float(s), 2)
        except Exception:
            return 0.0

    def limpar(valor):
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
        if "bimestral" in s:
            return "bimestrais"
        if "mensal" in s:
            return "mensais"
        # fallback se for assinatura e não deu match
        return "anuais"

    # 🧮 Tabela multi-ano (mesma usada no outro fluxo)
    TABELA_VALORES = {
        ("anuais", "mensal"): 960,
        ("anuais", "bimestral"): 480,
        ("bianuais", "mensal"): 1920,
        ("bianuais", "bimestral"): 960,
        ("trianuais", "mensal"): 2880,
        ("trianuais", "bimestral"): 1440,
    }

    def divisor_para(tipo_assinatura: str, periodicidade: str) -> int:
        ta = (tipo_assinatura or "").lower().strip()
        per = (periodicidade or "").lower().strip()
        if ta == "trianuais":
            return 36 if per == "mensal" else 18
        if ta == "bianuais":
            return 24 if per == "mensal" else 12
        if ta == "anuais":
            return 12 if per == "mensal" else 6
        if ta == "bimestrais":
            return 2 if per == "mensal" else 1
        if ta == "mensais":
            return 1
        return 1

    registros = []
    for _, linha in df.iterrows():
        if pd.isna(linha.get("email contato")) and pd.isna(linha.get("nome contato")):
            continue

        try:
            # campos base da planilha Guru
            valor_venda = parse_money(
                linha.get("valor venda", "")
            )  # valor final pago (sempre vira Total Pedido)
            nome_prod = linha.get("nome produto", "")
            id_prod = linha.get("id produto", "")
            assinatura_codigo = (
                linha.get("assinatura código") or linha.get("assinatura codigo") or ""
            ).strip()

            is_assin = eh_assinatura(nome_prod)
            periodicidade = inferir_periodicidade(id_prod) if is_assin else ""
            tipo_ass = inferir_tipo_assinatura(nome_prod) if is_assin else ""

            # Regra de fallback de preços: só quando É assinatura e NÃO tem "assinatura código"
            usar_fallback = bool(is_assin and assinatura_codigo == "")

            # Base para aplicar divisor
            if is_assin:
                if usar_fallback and tipo_ass in {"anuais", "bianuais", "trianuais"}:
                    base = float(TABELA_VALORES.get((tipo_ass, periodicidade), valor_venda))
                else:
                    base = float(valor_venda)
                div = divisor_para(tipo_ass, periodicidade)
                valor_unitario = round(base / max(div, 1), 2)
                valor_total_item = valor_unitario  # qtd = 1
            else:
                # não assinatura → sem divisor
                valor_unitario = valor_venda
                valor_total_item = valor_venda

            total_pedido = valor_venda  # sempre o valor efetivamente pago

            cpf = limpar(linha.get("doc contato")).zfill(11)
            cep = limpar(linha.get("cep contato")).zfill(8)[:8]
            telefone = limpar(linha.get("telefone contato"))

            data_pedido_raw = linha.get("data pedido", "")
            try:
                data_pedido = pd.to_datetime(data_pedido_raw, dayfirst=True).strftime("%d/%m/%Y")
            except Exception:
                data_pedido = datetime.today().strftime("%d/%m/%Y")

            registros.append(
                {
                    "Número pedido": "",
                    "Nome Comprador": limpar(linha.get("nome contato")),
                    "Data Pedido": data_pedido,
                    "Data": datetime.today().strftime("%d/%m/%Y"),
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
                    "Valor Unitário": f"{valor_unitario:.2f}".replace(".", ","),
                    "Valor Total": f"{valor_total_item:.2f}".replace(".", ","),
                    "Total Pedido": f"{total_pedido:.2f}".replace(".", ","),
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
                    "indisponivel": "S" if eh_indisponivel(produto_nome) else "",
                    # opcional: registrar metadados detectados (úteis para auditoria)
                    "periodicidade": periodicidade,
                    "Plano Assinatura": tipo_ass if is_assin else "",
                    "assinatura_codigo": assinatura_codigo,
                }
            )
        except Exception as e:
            print(f"❌ Erro ao processar linha: {e}")

    if not registros:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhum registro foi importado.")
        return

    df_importado = pd.DataFrame(registros)
    df_importado = padronizar_planilha_importada(df_importado)

    if "df_planilha_parcial" not in estado:
        estado["df_planilha_parcial"] = pd.DataFrame()

    estado["df_planilha_parcial"] = pd.concat(
        [estado["df_planilha_parcial"], df_importado], ignore_index=True
    )
    estado["transacoes_obtidas"] = True

    comunicador_global.mostrar_mensagem.emit(
        "info",
        "Importado com sucesso",
        f"{len(df_importado)} registros adicionados à planilha parcial.",
    )


def selecionar_planilha_comercial(skus_info):
    caminho, _ = QFileDialog.getOpenFileName(
        None, "Selecionar planilha do comercial", "", "Planilhas Excel (*.xlsx *.xls)"
    )
    if caminho:
        adicionar_brindes_e_substituir_box(caminho, skus_info)


SKU_RE = re.compile(r"\(([A-Za-z0-9._\-]+)\)")  # captura CÓDIGO dentro de parênteses, p.ex. (L002A)


def _build_sku_index(skus_info: dict) -> dict:
    """
    Constrói um índice SKU (UPPER) -> nome_padrao a partir do skus_info.
    Espera-se skus_info no formato: {nome_padrao: {"sku": "...", ...}, ...}
    """
    idx = {}
    for nome_padrao, info in (skus_info or {}).items():
        sku = str((info or {}).get("sku", "")).strip()
        if sku:
            idx[sku.upper()] = nome_padrao
    return idx


def _extract_first_sku(texto: str) -> str:
    """
    Extrai o PRIMEIRO SKU encontrado no texto no padrão 'Nome (SKU)'.
    Retorna string (pode ser "").
    """
    if not texto:
        return ""
    m = SKU_RE.search(str(texto))
    return (m.group(1) if m else "").strip()


def _extract_all_skus(texto: str) -> list:
    """
    Extrai TODOS os SKUs de uma string possivelmente com múltiplos nomes, ex.:
    'Heráclito (B003A), David Hume (B004A), Leviatã (L002A)' -> ['B003A','B004A','L002A']
    """
    if not texto:
        return []
    return [m.strip() for m in SKU_RE.findall(str(texto)) if m and str(m).strip()]


def adicionar_brindes_e_substituir_box(caminho_planilha_comercial, skus_info):
    try:
        df_comercial = pd.read_excel(caminho_planilha_comercial)
    except Exception as e:
        comunicador_global.mostrar_mensagem.emit(
            "erro", "Erro", f"Erro ao ler a planilha do comercial: {e}"
        )
        return

    # normalização básica
    df_comercial.columns = df_comercial.columns.str.strip().str.lower()
    df_comercial = df_comercial.dropna(subset=["subscription_id"])

    # df parcial (destino)
    df_saida = estado.get("df_planilha_parcial")
    if df_saida is None or df_saida.empty:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro", "Planilha parcial não carregada.")
        return

    # índice SKU -> nome_padrao
    sku_index = _build_sku_index(skus_info)
    if not sku_index:
        comunicador_global.mostrar_mensagem.emit(
            "erro", "Erro", "Índice de SKUs vazio no skus_info."
        )
        return

    # ---------- escolha do BOX ORIGINAL (apenas por SKU) ----------
    lista_skus = sorted(sku_index.keys(), key=str.casefold)
    opcao_escolhida, ok = QInputDialog.getItem(
        None,
        "Box original (SKU)",
        "Selecione o SKU do BOX ORIGINAL (produto a ser substituído):",
        lista_skus,
        0,
        False,
    )
    if not ok or not str(opcao_escolhida).strip():
        comunicador_global.mostrar_mensagem.emit(
            "aviso", "Cancelado", "Operação cancelada pelo usuário."
        )
        return

    sku_box_original = str(opcao_escolhida).strip()

    novas_linhas = []

    # ---------- processa cada linha da planilha comercial ----------
    for _, row in df_comercial.iterrows():
        subscription_id = str(row["subscription_id"]).strip()

        # 1) SUBSTITUIÇÃO do box principal (NÃO cria linha)
        #    extrai o SKU do "box_principal" informado (ex.: "Santo Agostinho (B005A)" -> "B005A")
        sku_box_novo = _extract_first_sku(str(row.get("box_principal", "")).strip())
        if sku_box_novo:
            # nome_padrao a partir do SKU; se não existir, usa o próprio texto do comercial como fallback
            nome_padrao_box_novo = sku_index.get(sku_box_novo.upper(), None)
            mask_sub = df_saida["subscription_id"].astype(str).str.strip() == subscription_id
            mask_box_original = (
                df_saida["SKU"].astype(str).str.strip().str.upper() == sku_box_original.upper()
            )
            idx_alvo = df_saida[mask_sub & mask_box_original].index

            for idx in idx_alvo:
                df_saida.at[idx, "Produto"] = nome_padrao_box_novo or df_saida.at[idx, "Produto"]
                df_saida.at[idx, "SKU"] = sku_box_novo  # substitui pelo novo SKU
                # mantém quantidade/valores como estão

        # 2) BRINDES: cria NOVA LINHA por SKU (dedup por subscription_id + SKU)
        brindes_str = str(row.get("brindes", "")).strip()
        if not brindes_str:
            continue

        skus_brindes = _extract_all_skus(brindes_str)  # pode retornar múltiplos
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
                mask_sub
                & (df_saida["SKU"].astype(str).str.strip().str.upper() == sku_brinde_norm.upper())
            ].empty
            if ja_existe:
                continue

            # cria a NOVA linha do brinde
            if not linhas_base.empty:
                base = linhas_base.iloc[0].copy()
                # nome do produto a partir do índice SKU -> nome_padrao
                nome_padrao_brinde = sku_index.get(sku_brinde_norm.upper(), None)
                base["Produto"] = nome_padrao_brinde or base.get("Produto", "")
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
        df_final = pd.concat([df_saida, pd.DataFrame(novas_linhas)], ignore_index=True)
        estado["df_planilha_parcial"] = df_final
        comunicador_global.mostrar_mensagem.emit(
            "info", "Sucesso", f"{len(novas_linhas)} brinde(s) adicionados."
        )
    else:
        estado["df_planilha_parcial"] = df_saida
        comunicador_global.mostrar_mensagem.emit(
            "info", "Sucesso", "Substituições realizadas (nenhum brinde novo)."
        )


# Geração e controle de logs de envios DMG


def filtrar_linhas_ja_enviadas():
    df_orig = estado.get("df_planilha_parcial")
    if df_orig is None or df_orig.empty:
        comunicador_global.mostrar_mensagem.emit(
            "aviso", "Aviso", "Nenhuma planilha carregada para filtrar."
        )
        return

    # -- cópia de trabalho com nomes normalizados (não toca df_orig) --
    df = df_orig.copy()
    df.columns = df.columns.str.strip()
    df.columns = df.columns.str.lower()

    # aliases só na cópia de trabalho
    if "assinatura código" in df.columns and "subscription_id" not in df.columns:
        df["subscription_id"] = df["assinatura código"]
    if "id transação" in df.columns and "transaction_id" not in df.columns:
        df["transaction_id"] = df["id transação"]

    # normalizações só na cópia de trabalho
    df["subscription_id"] = df.get("subscription_id", "").astype(str).fillna("").str.strip()
    df["transaction_id"] = df.get("transaction_id", "").astype(str).fillna("").str.strip()
    df["periodicidade"] = df.get("periodicidade", "").astype(str).str.lower().replace({"nan": ""})
    df["periodo"] = pd.to_numeric(df.get("periodo", ""), errors="coerce").fillna(-1).astype(int)

    # seleção do período
    ano_atual = datetime.today().year
    mes_padrao = datetime.today().month
    ano, ok1 = QInputDialog.getInt(
        None, "Selecionar Ano", "Ano do envio:", value=ano_atual, min=2020, max=2035
    )
    if not ok1:
        return
    mes, ok2 = QInputDialog.getInt(
        None, "Selecionar Mês", "Mês (1 a 12):", value=mes_padrao, min=1, max=12
    )
    if not ok2:
        return
    bimestre = 1 + (mes - 1) // 2

    # carrega log
    caminho_excel = os.path.join(os.path.dirname(__file__), "Envios", "envios_log.xlsx")
    assinaturas_existentes, produtos_existentes = set(), set()
    if os.path.exists(caminho_excel):
        try:
            assinaturas_df = pd.read_excel(caminho_excel, sheet_name="assinaturas")
            produtos_df = pd.read_excel(caminho_excel, sheet_name="produtos")

            assinaturas_df["subscription_id"] = (
                assinaturas_df["subscription_id"].astype(str).str.strip()
            )
            assinaturas_df["periodicidade"] = (
                assinaturas_df["periodicidade"].astype(str).str.lower().str.strip()
            )
            assinaturas_df["periodo"] = (
                pd.to_numeric(assinaturas_df["periodo"], errors="coerce").fillna(-1).astype(int)
            )

            assinaturas_existentes = {
                (row["subscription_id"], int(row["ano"]), row["periodicidade"], int(row["periodo"]))
                for _, row in assinaturas_df.iterrows()
                if pd.notna(row.get("subscription_id"))
                and str(row.get("subscription_id")).strip() != ""
            }
            produtos_existentes = set(produtos_df["transaction_id"].astype(str).str.strip())

        except Exception as e:
            print(f"[⚠️] Erro ao ler Excel: {e}")

    linhas_antes = len(df)

    def deve_remover(row):
        id_sub = str(row.get("subscription_id", "")).strip()
        id_trans = str(row.get("transaction_id", "")).strip()

        if id_sub:
            per = str(row.get("periodicidade", "")).strip().lower()
            if per == "mensal":
                per_num = mes
            elif per == "bimestral":
                per_num = bimestre
            else:
                return False
            return (id_sub, ano, per, int(per_num)) in assinaturas_existentes

        if id_trans:
            return id_trans in produtos_existentes

        return False

    mask_remover = df.apply(deve_remover, axis=1)

    # -- aplica a máscara no DataFrame ORIGINAL, preservando schema/casos/acentos --
    df_filtrado = df_orig.loc[~mask_remover.values].copy()

    removidas = linhas_antes - len(df_filtrado)
    estado["df_planilha_parcial"] = df_filtrado

    comunicador_global.mostrar_mensagem.emit(
        "info",
        "Filtragem concluída",
        f"{removidas} linha(s) removida(s) com base nos registros anteriores.",
    )


def registrar_envios_por_mes_ano():
    df = estado.get("df_planilha_parcial")
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhuma planilha carregada.")
        return

    ano_atual = datetime.today().year
    mes_padrao = datetime.today().month

    ano, ok1 = QInputDialog.getInt(
        None, "Selecionar Ano", "Ano do envio:", value=ano_atual, min=2020, max=2035
    )
    if not ok1:
        return
    mes, ok2 = QInputDialog.getInt(
        None, "Selecionar Mês", "Mês (1 a 12):", value=mes_padrao, min=1, max=12
    )
    if not ok2:
        return

    bimestre = 1 + (mes - 1) // 2

    dff = df.copy()

    # ✅ Garantias básicas
    for col in ("indisponivel", "periodicidade", "subscription_id", "origem"):
        if col not in dff.columns:
            dff[col] = ""
    dff["indisponivel"] = dff["indisponivel"].astype(str)
    dff["periodicidade"] = dff["periodicidade"].astype(str).str.lower().replace({"nan": ""})
    dff["subscription_id"] = dff["subscription_id"].astype(str).str.strip()
    dff["origem"] = dff["origem"].astype(str).str.lower().str.strip()

    # 🚫 Remover indisponíveis
    mask_validos = ~dff["indisponivel"].str.upper().eq("S")
    dff = dff[mask_validos].copy()
    if dff.empty:
        comunicador_global.mostrar_mensagem.emit(
            "aviso", "Aviso", "Nenhum registro válido após remover indisponíveis."
        )
        return

    # 🔹 Assinaturas
    df_mensal = dff[dff["periodicidade"].eq("mensal")].copy()
    df_bimestral = dff[dff["periodicidade"].eq("bimestral")].copy()

    # 🔹 Produtos (sem subscription_id ou marcados como origem produtos)
    mask_prod = dff["subscription_id"].eq("") | dff["origem"].eq("produtos")
    df_produtos = dff[mask_prod].copy()

    if not df_mensal.empty:
        gerar_log_envios(df_mensal, ano, "mensal", mes)
    if not df_bimestral.empty:
        gerar_log_envios(df_bimestral, ano, "bimestral", bimestre)
    if not df_produtos.empty:
        gerar_log_envios(df_produtos, ano, "produtos", 0)

    estado["ultimo_log"] = {"ano": ano, "mes": mes, "bimestre": bimestre}

    comunicador_global.mostrar_mensagem.emit(
        "info",
        "Registro concluído",
        f"Registros salvos para {mes:02d}/{ano} (mensal), bimestre {bimestre}/{ano}"
        f"{' e produtos' if not df_produtos.empty else ''}.",
    )


def gerar_log_envios(df, ano, periodicidade, periodo):
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Não há dados para registrar.")
        return

    df = df.copy()

    # ✅ Garantias
    if "indisponivel" not in df.columns:
        df["indisponivel"] = ""
    if "subscription_id" not in df.columns:
        df["subscription_id"] = ""
    if "origem" not in df.columns:
        df["origem"] = ""

    df["indisponivel"] = df["indisponivel"].astype(str)
    df["subscription_id"] = df["subscription_id"].astype(str).str.strip()
    df["origem"] = df["origem"].astype(str).str.lower().str.strip()

    # Remove indisponíveis
    df = df[~df["indisponivel"].str.upper().eq("S")].copy()
    if df.empty:
        comunicador_global.mostrar_mensagem.emit(
            "aviso", "Aviso", "Nenhum registro válido após remover indisponíveis."
        )
        return

    registros_assinaturas = []
    registros_produtos = []
    registro_em = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    tem_id_lote = "ID Lote" in df.columns

    ignorados_sem_trans = 0

    for _, r in df.iterrows():
        id_sub = str(r.get("subscription_id", "")).strip()
        id_trans = (
            str(r.get("transaction_id", "")).strip() if "transaction_id" in df.columns else ""
        )

        if id_sub:
            registros_assinaturas.append(
                {
                    "subscription_id": id_sub,
                    "ano": int(ano),
                    "periodicidade": str(periodicidade),
                    "periodo": int(periodo),
                    "registro_em": registro_em,
                }
            )
        elif id_trans:
            rec = {"transaction_id": id_trans, "registro_em": registro_em}
            if tem_id_lote:
                rec["id_lote"] = str(r.get("ID Lote", "")).strip()
            registros_produtos.append(rec)
        else:
            ignorados_sem_trans += 1

    if not registros_assinaturas and not registros_produtos:
        comunicador_global.mostrar_mensagem.emit(
            "aviso", "Aviso", "Nenhum registro válido encontrado para salvar."
        )
        return

    caminho_excel = os.path.join(os.path.dirname(__file__), "Envios", "envios_log.xlsx")
    os.makedirs(os.path.dirname(caminho_excel), exist_ok=True)

    if registros_assinaturas:
        salvar_em_excel_sem_duplicados(
            caminho_excel, registros_assinaturas, sheet_name="assinaturas"
        )

    if registros_produtos:
        salvar_em_excel_sem_duplicados(caminho_excel, registros_produtos, sheet_name="produtos")

    total = len(registros_assinaturas) + len(registros_produtos)
    msg = f"{total} registro(s) foram adicionados ao log."
    if registros_assinaturas:
        msg += f"\n  • Assinaturas: {len(registros_assinaturas)}"
    if registros_produtos:
        msg += f"\n  • Produtos: {len(registros_produtos)}"
    if ignorados_sem_trans:
        msg += f"\n  • Ignorados (produtos sem transaction_id): {ignorados_sem_trans}"
    comunicador_global.mostrar_mensagem.emit("info", "Registro concluído", msg)


def salvar_em_excel_sem_duplicados(caminho, novos, sheet_name):
    novos_df = pd.DataFrame(novos)

    if sheet_name == "produtos":
        chave_unica = ["transaction_id"]
    elif sheet_name == "assinaturas":
        chave_unica = ["subscription_id", "ano", "periodicidade", "periodo"]
    else:
        raise ValueError(f"Aba desconhecida: {sheet_name}")

    escritor_existente = os.path.exists(caminho)
    todas_abas = {}

    if escritor_existente:
        try:
            todas_abas = pd.read_excel(caminho, sheet_name=None)
            existentes = todas_abas.get(sheet_name, pd.DataFrame())
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

    try:
        with pd.ExcelWriter(caminho, engine="openpyxl", mode="w") as writer:
            for aba, dfw in todas_abas.items():
                dfw.to_excel(writer, sheet_name=aba, index=False)
        adicionados = tamanho_depois - tamanho_antes
        print(f"[💾] {adicionados} novo(s) registro(s) adicionado(s) em '{sheet_name}'")
    except Exception as e:
        print(f"[❌] Erro ao salvar Excel: {e}")


# Integração com a API da Shopify


def normalizar_transaction_id(valor):
    if isinstance(valor, str):
        valor = valor.strip()
        if "gid://" in valor and "/" in valor:
            return valor.split("/")[-1]  # ✅ extrai apenas o número
        return valor
    elif isinstance(valor, int):
        return str(valor)
    return str(valor).strip()


# Classes de Sinalização (Signals)


class ShopifySignals(QObject):
    resultado = pyqtSignal(dict)
    erro = pyqtSignal(str)


class SinaisObterCpf(QObject):
    resultado = pyqtSignal(str, str)  # pedido_id, cpf
    erro = pyqtSignal(str, str)  # pedido_id, erro


class SinaisFulfill(QObject):
    concluido = pyqtSignal(str, int)  # order_id, qtd_itens
    erro = pyqtSignal(str, str)  # order_id, msg


class FinalizacaoProgressoSignal(QObject):
    finalizado = pyqtSignal()


class SinaisBuscarPedidos(QObject):
    resultado = pyqtSignal(list)  # Lista de pedidos
    erro = pyqtSignal(str)


# Classes de Runnable (Executando operações em threads)


class ObterCpfShopifyRunnable(QRunnable):
    def __init__(self, order_id, estado, sinal_finalizacao=None):
        super().__init__()
        self.order_id = normalizar_transaction_id(order_id)
        self.estado = estado
        self.signals = SinaisObterCpf()
        self.sinal_finalizacao = sinal_finalizacao
        self._parent_correlation_id = get_correlation_id()

    @pyqtSlot()
    def run(self):
        set_correlation_id(self._parent_correlation_id)
        logger.info("cpf_lookup_start", extra={"order_id": self.order_id})
        cpf = ""
        try:
            if self.estado["cancelador_global"].is_set():
                logger.warning("cpf_lookup_cancelled_early", extra={"order_id": self.order_id})
                return

            order_gid = f"gid://shopify/Order/{self.order_id}"
            query = {
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

            headers = {
                "Content-Type": "application/json",
                "X-Shopify-Access-Token": settings.SHOPIFY_TOKEN,
            }

            with controle_shopify["lock"]:
                delta = time.time() - controle_shopify["ultimo_acesso"]
                if delta < MIN_INTERVALO_GRAPHQL:
                    time.sleep(MIN_INTERVALO_GRAPHQL - delta)
                controle_shopify["ultimo_acesso"] = time.time()

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
                data = resp.json()
                edges = (
                    data.get("data", {})
                    .get("order", {})
                    .get("localizationExtensions", {})
                    .get("edges", [])
                )
                for edge in edges:
                    node = edge.get("node", {})
                    if node.get("purpose") == "TAX" and "cpf" in node.get("title", "").lower():
                        cpf = re.sub(r"\D", "", node.get("value", ""))[:11]
                        break
            else:
                logger.warning(
                    "cpf_lookup_http_error",
                    extra={"order_id": self.order_id, "status": resp.status_code},
                )

            self.signals.resultado.emit(self.order_id, cpf)

        except Exception as e:
            logger.exception(
                "cpf_lookup_exception", extra={"order_id": self.order_id, "err": str(e)}
            )
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
                    self.sinal_finalizacao.finalizado.emit()
                    logger.debug("cpf_lookup_final_signal", extra={"order_id": self.order_id})
                except Exception as e:
                    logger.exception(
                        "cpf_lookup_final_signal_error",
                        extra={"order_id": self.order_id, "err": str(e)},
                    )


class FulfillPedidoRunnable(QRunnable):
    def __init__(self, order_id, itens_line_ids):
        super().__init__()
        self.order_id = normalizar_transaction_id(order_id)
        self.itens_line_ids = set(map(normalizar_transaction_id, itens_line_ids))  # normaliza aqui
        self.signals = SinaisFulfill()

    @pyqtSlot()
    def run(self):
        try:
            order_gid = f"gid://shopify/Order/{self.order_id}"
            query_fo = """
            query($orderId: ID!) {
              order(id: $orderId) {
                fulfillmentOrders(first: 10) {
                  edges {
                    node {
                      id
                      status
                      lineItems(first: 50) {
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
              }
            }
            """

            headers = {
                "Content-Type": "application/json",
                "X-Shopify-Access-Token": settings.SHOPIFY_TOKEN,
            }

            with controle_shopify["lock"]:
                delta = time.time() - controle_shopify["ultimo_acesso"]
                if delta < MIN_INTERVALO_GRAPHQL:
                    time.sleep(MIN_INTERVALO_GRAPHQL - delta)
                controle_shopify["ultimo_acesso"] = time.time()

            with requests.Session() as sess:
                sess.headers.update(headers)
                r1 = sess.post(
                    GRAPHQL_URL,
                    json={"query": query_fo, "variables": {"orderId": order_gid}},
                    timeout=10,
                    verify=False,
                )

            if r1.status_code != 200:
                raise Exception(f"Erro HTTP {r1.status_code} na consulta")

            dados = r1.json()
            orders = dados["data"]["order"]["fulfillmentOrders"]["edges"]

            fulfillment_payloads = []

            for edge in orders:
                node = edge["node"]
                if node["status"] != "OPEN":
                    continue
                items = []
                for li in node["lineItems"]["edges"]:
                    li_node = li["node"]
                    line_item_gid = li_node["lineItem"]["id"]
                    line_item_id = normalizar_transaction_id(line_item_gid)

                    if line_item_id in self.itens_line_ids and li_node["remainingQuantity"] > 0:
                        items.append(
                            {
                                "id": li_node["id"],  # fulfillment line item ID
                                "quantity": li_node["remainingQuantity"],
                            }
                        )
                    else:
                        print(
                            f"[🔍] Ignorado: lineItem.id = {line_item_id}, restante = {li_node['remainingQuantity']}"
                        )

                if items:
                    fulfillment_payloads.append(
                        {"fulfillmentOrderId": node["id"], "fulfillmentOrderLineItems": items}
                    )

            if not fulfillment_payloads:
                self.signals.erro.emit(self.order_id, "Nada a enviar")
                return

            mutation = """
            mutation fulfillmentCreate($fulfillment: FulfillmentV2Input!) {
              fulfillmentCreateV2(fulfillment: $fulfillment) {
                fulfillment { id status }
                userErrors { field message }
              }
            }
            """

            with requests.Session() as sess:
                sess.headers.update(headers)
                r2 = sess.post(
                    GRAPHQL_URL,
                    json={
                        "query": mutation,
                        "variables": {
                            "fulfillment": {
                                "notifyCustomer": False,
                                "lineItemsByFulfillmentOrder": fulfillment_payloads,
                            }
                        },
                    },
                    timeout=10,
                    verify=False,
                )

            if r2.status_code != 200:
                raise Exception(f"Erro HTTP {r2.status_code} na mutation")

            resp = r2.json()
            user_errors = resp["data"]["fulfillmentCreateV2"]["userErrors"]
            if user_errors:
                erros_msg = "; ".join(f"{e['field']} → {e['message']}" for e in user_errors)
                self.signals.erro.emit(self.order_id, erros_msg)
                return

            qtd_total = sum(
                item["quantity"]
                for fo in fulfillment_payloads
                for item in fo["fulfillmentOrderLineItems"]
            )
            self.signals.concluido.emit(self.order_id, qtd_total)

        except Exception as e:
            self.signals.erro.emit(self.order_id, str(e))


class NormalizarEnderecoRunnable(QRunnable):
    def __init__(
        self, order_id, endereco_raw, complemento_raw, callback, sinal_finalizacao, estado
    ):
        super().__init__()
        self.order_id = normalizar_transaction_id(order_id)
        self.endereco_raw = endereco_raw or ""
        self.complemento_raw = complemento_raw or ""
        self.callback = callback
        self.sinal_finalizacao = sinal_finalizacao
        self.estado = estado

    @pyqtSlot()
    def run(self):
        pedido_id = self.order_id  # já normalizado

        try:
            logger.info("addr_norm_thread_started", extra={"order_id": pedido_id})

            if self.estado.get("finalizou_endereco"):
                logger.debug("addr_norm_skipped_already_finished", extra={"order_id": pedido_id})
                return

            if self.estado.get("cancelador_global", threading.Event()).is_set():
                logger.info("addr_norm_cancelled_early", extra={"order_id": pedido_id})
                return

            cep = self.estado.get("cep_por_pedido", {}).get(pedido_id, "").replace("-", "").strip()
            if not cep:
                logger.warning("addr_norm_missing_cep", extra={"order_id": pedido_id})
                logradouro_cep = ""
                bairro_cep = ""
            else:
                cep_info_cache = self.estado.get("cep_info_por_pedido", {}).get(pedido_id)
                if cep_info_cache:
                    logradouro_cep = cep_info_cache.get("street", "")
                    bairro_cep = cep_info_cache.get("district", "")
                    logger.debug("addr_norm_cep_cache_hit", extra={"order_id": pedido_id})
                else:
                    try:
                        cep_info = buscar_cep_com_timeout(cep)
                        logradouro_cep = cep_info.get("street", "")
                        bairro_cep = cep_info.get("district", "")
                        self.estado.setdefault("cep_info_por_pedido", {})[pedido_id] = cep_info
                        logger.debug("addr_norm_cep_fetched", extra={"order_id": pedido_id})
                    except Exception as e:
                        logger.error(
                            "addr_norm_cep_error", extra={"order_id": pedido_id, "err": str(e)}
                        )
                        logradouro_cep = ""
                        bairro_cep = ""

            if self.estado.get("cancelador_global", threading.Event()).is_set():
                logger.info("addr_norm_cancelled_mid", extra={"order_id": pedido_id})
                return

            if endereco_parece_completo(self.endereco_raw):
                partes = [p.strip() for p in self.endereco_raw.split(",", 1)]
                base = partes[0]
                numero = partes[1] if len(partes) > 1 else "s/n"
                complemento = self.complemento_raw.strip()
                precisa = False
                logger.debug(
                    "addr_norm_direct_ok",
                    extra={"order_id": pedido_id, "base": base, "numero": numero},
                )
            else:
                resposta = usar_gpt_callback(
                    address1=self.endereco_raw,
                    address2=self.complemento_raw,
                    logradouro_cep=logradouro_cep,
                    bairro_cep=bairro_cep,
                )

                if self.estado.get("cancelador_global", threading.Event()).is_set():
                    return

                base = resposta.get("base", "").strip()
                numero = resposta.get("numero", "").strip()
                if not re.match(r"^\d+[A-Za-z]?$", numero):
                    numero = "s/n"
                    precisa = True
                complemento = resposta.get("complemento", "") or self.complemento_raw.strip()
                if complemento.strip() == numero.strip():
                    complemento = ""
                precisa = resposta.get("precisa_contato", True)

                # segurança adicional com logradouro do CEP
                if logradouro_cep:
                    base_normalizada = normalizar(base)
                    logradouro_normalizado = normalizar(logradouro_cep)
                    if logradouro_normalizado not in base_normalizada:
                        base = logradouro_cep.strip()

            resultado = {
                "endereco_base": base,
                "numero": numero,
                "complemento": complemento,
                "precisa_contato": "SIM" if precisa else "NÃO",
                "logradouro_oficial": logradouro_cep,
                "bairro_oficial": bairro_cep,
                "raw_address1": self.endereco_raw,
                "raw_address2": self.complemento_raw,
            }

            registrar_log_endereco(pedido_id, resultado)
            self.callback(pedido_id, resultado)

        except Exception as e:
            logger.exception("addr_norm_exception", extra={"order_id": pedido_id, "err": str(e)})
            fallback = {
                "endereco_base": self.endereco_raw,
                "numero": "s/n",
                "complemento": self.complemento_raw.strip(),
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
                pendentes = self.estado.get("endereco_pendentes", set())
                if pedido_id in pendentes:
                    pendentes.discard(pedido_id)
                    logger.debug("addr_norm_pending_removed", extra={"order_id": pedido_id})
                else:
                    logger.debug("addr_norm_pending_already_gone", extra={"order_id": pedido_id})
            except Exception as e:
                logger.exception(
                    "addr_norm_pending_remove_error", extra={"order_id": pedido_id, "err": str(e)}
                )

            try:
                self.sinal_finalizacao.finalizado.emit()
                logger.debug("addr_norm_final_signal", extra={"order_id": pedido_id})
            except Exception as e:
                logger.exception(
                    "addr_norm_final_signal_error", extra={"order_id": pedido_id, "err": str(e)}
                )


class BuscarBairroRunnable(QRunnable):
    def __init__(self, order_id, cep, df, callback, estado, sinal_finalizacao=None):
        super().__init__()
        self.order_id = normalizar_transaction_id(order_id)
        self.cep = cep
        self.df = df
        self.callback = callback
        self.estado = estado
        self.sinal_finalizacao = sinal_finalizacao
        self._parent_correlation_id = get_correlation_id()

    @pyqtSlot()
    def run(self):
        set_correlation_id(self._parent_correlation_id)
        logger.info("bairro_lookup_start", extra={"order_id": self.order_id})
        try:
            if self.estado["cancelador_global"].is_set():
                logger.warning("bairro_lookup_cancelled_early", extra={"order_id": self.order_id})
                return

            cep_limpo = re.sub(r"\D", "", self.cep)
            if len(cep_limpo) != 8:
                raise ValueError("CEP inválido")

            endereco = buscar_cep_com_timeout(cep_limpo)

            if self.estado["cancelador_global"].is_set():
                logger.warning(
                    "bairro_lookup_cancelled_after_fetch", extra={"order_id": self.order_id}
                )
                return

            bairro = endereco.get("district", "").strip()
            cidade = endereco.get("city", "").strip()
            uf = endereco.get("uf", "").strip()

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

            if self.estado["cancelador_global"].is_set():
                logger.warning(
                    "bairro_lookup_cancelled_before_callback", extra={"order_id": self.order_id}
                )
                return

            self.callback(self.order_id, bairro or "")

        except Exception:
            if self.estado["cancelador_global"].is_set():
                logger.warning(
                    "bairro_lookup_cancelled_during_exception", extra={"order_id": self.order_id}
                )
                return

            logger.exception("bairro_lookup_error", extra={"order_id": self.order_id})
            self.callback(self.order_id, "")

        finally:
            try:
                self.estado["bairro_pendentes"].discard(self.order_id)
                logger.debug("bairro_lookup_popped_from_pending", extra={"order_id": self.order_id})
            except Exception as e:
                logger.exception(
                    "bairro_lookup_pending_discard_error",
                    extra={"order_id": self.order_id, "err": str(e)},
                )

            if self.sinal_finalizacao:
                try:
                    self.sinal_finalizacao.finalizado.emit()
                    logger.debug("bairro_lookup_final_signal", extra={"order_id": self.order_id})
                except Exception as e:
                    logger.exception(
                        "bairro_lookup_final_signal_error",
                        extra={"order_id": self.order_id, "err": str(e)},
                    )


class BuscarPedidosPagosRunnable(QRunnable):
    def __init__(self, data_inicio_str, estado, fulfillment_status="any"):
        super().__init__()
        self.data_inicio_str = data_inicio_str
        self.fulfillment_status = fulfillment_status
        self.sinais = SinaisBuscarPedidos()
        self.estado = estado
        self._parent_correlation_id = get_correlation_id()

        # ✅ salva o modo selecionado para uso no tratar_resultado
        self.estado["fulfillment_status_selecionado"] = (
            (fulfillment_status or "any").strip().lower()
        )

        # memória de custos/limites para rate-limit pró-ativo
        self._ultimo_requested_cost = 150.0  # palpite inicial
        self._ultimo_throttle_status = None  # dict: maximumAvailable/currentlyAvailable/restoreRate

        # garante estruturas básicas no estado (evita KeyError)
        self.estado.setdefault("dados_temp", {})
        self.estado["dados_temp"].setdefault("cpfs", {})
        self.estado["dados_temp"].setdefault("bairros", {})
        self.estado["dados_temp"].setdefault("enderecos", {})
        self.estado["dados_temp"].setdefault("status_fulfillment", {})
        self.estado["dados_temp"].setdefault("fretes", {})
        self.estado["dados_temp"].setdefault("descontos", {})

    # ---- helper: imprime contexto e emite sinal de erro ----
    def _log_erro(
        self,
        titulo,
        detalhe=None,
        exc: Exception | None = None,
        resp: requests.Response | None = None,
        extra_ctx: dict | None = None,
    ):
        print("\n" + "═" * 80)
        print(f"[❌] {titulo}")
        if detalhe:
            print(f"[📝] Detalhe: {detalhe}")

        ctx = {
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

            try:
                print(f"[📬] Headers: {dict(resp.headers)}")
            except Exception:
                pass

            # erros GraphQL detalhados (se houver)
            try:
                payload = resp.json()
                if isinstance(payload, dict) and "errors" in payload:
                    print("[🧩] GraphQL errors:")
                    for i, err in enumerate(payload.get("errors", []), start=1):
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

    # --- helper: quanto esperar para ter 'needed' créditos disponíveis ---
    def _calc_wait_seconds(self, throttle_status: dict, needed: float) -> float:
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

    # --- helper: esperar pró-ativamente antes da requisição ---
    def _esperar_creditos_se_preciso(self):
        needed = max(50.0, float(self._ultimo_requested_cost or 100.0))
        wait_s = self._calc_wait_seconds(self._ultimo_throttle_status, needed)
        if wait_s > 0:
            print(f"⏳ Aguardando {wait_s:.2f}s para recuperar créditos (precisa ~{needed:.0f}).")
            time.sleep(wait_s)

    # --- helper: extrair infos de custo/throttle do payload e guardar ---
    def _atualizar_custos(self, payload: dict):
        cost = (payload or {}).get("extensions", {}).get("cost", {}) or {}
        req_cost = cost.get("requestedQueryCost")
        act_cost = cost.get("actualQueryCost")
        if req_cost is not None:
            self._ultimo_requested_cost = float(req_cost)
        elif act_cost is not None:
            self._ultimo_requested_cost = float(act_cost)

        throttle = cost.get("throttleStatus") or {}
        if throttle:
            self._ultimo_throttle_status = {
                "maximumAvailable": throttle.get("maximumAvailable"),
                "currentlyAvailable": throttle.get("currentlyAvailable"),
                "restoreRate": throttle.get("restoreRate"),
            }

    @pyqtSlot()
    def run(self):
        set_correlation_id(self._parent_correlation_id)
        logger.info("bairro_lookup_start", extra={"order_id": self.order_id, "cep": self.cep})
        if self.estado["cancelador_global"].is_set():
            logger.warning("shopify_fetch_cancelled_early")
            return

        # valida data início
        try:
            data_inicio = datetime.strptime(self.data_inicio_str, "%d/%m/%Y")
        except Exception as e:
            self._log_erro("Data inválida", detalhe=str(e), exc=e)
            return

        cursor = None
        pedidos = []

        # ------- Fulfillment status: só "any" ou "unfulfilled" -------
        fs = (self.fulfillment_status or "").strip().lower()

        # Monta a search query base
        filtros = ["financial_status:paid"]
        if fs == "unfulfilled":
            filtros.append("fulfillment_status:unfulfilled")

        # ✅ filtro de data somente por INÍCIO (ligado por padrão)
        if self.estado.get("usar_filtro_data", True):
            filtros.append(f'created_at:>={data_inicio.strftime("%Y-%m-%d")}')

        query_str = " ".join(filtros)
        logger.debug("shopify_query", extra={"query": query_str})

        # Query usando variável $search (evita problemas de escape)
        query_template = """
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
                customer { email firstName lastName }
                shippingAddress { name address1 address2 city zip provinceCode phone }
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

        headers = {
            "Content-Type": "application/json",
            "X-Shopify-Access-Token": settings.SHOPIFY_TOKEN,
        }

        while True:
            if self.estado["cancelador_global"].is_set():
                logger.warning("shopify_fetch_cancelled_midloop")
                break

            # ⭐ espera proativa com base no último throttleStatus
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
                self._log_erro(
                    "Timeout na requisição", exc=e, extra_ctx={"cursor": cursor, "query": query_str}
                )
                return
            except requests.exceptions.RequestException as e:
                self._log_erro(
                    "Exceção de rede/requests",
                    exc=e,
                    extra_ctx={"cursor": cursor, "query": query_str},
                )
                return

            if self.estado["cancelador_global"].is_set():
                logger.warning("shopify_fetch_cancelled_after_request")
                break

            # --- HTTP status ---
            if resp.status_code == 429:
                retry = int(resp.headers.get("Retry-After", "2"))
                logger.warning("shopify_http_429", extra={"retry_after": retry})
                time.sleep(retry)
                continue
            elif resp.status_code != 200:
                self._log_erro(
                    f"Erro HTTP {resp.status_code}",
                    detalhe=resp.text[:200],
                    resp=resp,
                    extra_ctx={"cursor": cursor, "query": query_str},
                )
                return

            # --- JSON ---
            try:
                payload = resp.json()
            except ValueError as e:
                self._log_erro(
                    "Resposta não é JSON válido",
                    detalhe=str(e),
                    resp=resp,
                    extra_ctx={"cursor": cursor, "query": query_str},
                )
                return

            # Atualiza memória de custos/throttle para as próximas iterações
            self._atualizar_custos(payload)

            # --- Erros GraphQL? ---
            if "errors" in payload:
                erro = payload["errors"][0] if payload["errors"] else {}
                code = ((erro.get("extensions") or {}).get("code") or "").upper()

                if code == "THROTTLED":
                    needed = float(self._ultimo_requested_cost or 100.0)
                    wait_s = self._calc_wait_seconds(self._ultimo_throttle_status, needed)
                    if wait_s <= 0:
                        wait_s = 1.5  # fallback conservador
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

            data = (payload.get("data") or {}).get("orders", {}) or {}
            novos = []

            for edge in data.get("edges", []):
                if self.estado["cancelador_global"].is_set():
                    logger.warning("shopify_fetch_cancelled_processing")
                    break

                pedido = edge["node"]

                # (loop de itens mantido apenas se quiser depurar algo)
                itens = (pedido.get("lineItems") or {}).get("edges", []) or []
                for item_edge in itens:
                    item = item_edge.get("node") or {}
                    _ = item.get("title", "")
                    _ = item.get("quantity", "")
                    _ = str((item.get("product") or {}).get("id", "")).split("/")[-1]

                # CPF via localizationExtensions
                cpf = ""
                try:
                    extensoes = (pedido.get("localizationExtensions") or {}).get("edges", []) or []
                    for ext in extensoes:
                        node = ext.get("node", {}) or {}
                        if (
                            node.get("purpose") == "TAX"
                            and "cpf" in (node.get("title", "") or "").lower()
                        ):
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

            if not data.get("pageInfo", {}).get("hasNextPage"):
                break

            cursor = data.get("pageInfo", {}).get("endCursor")

        if self.estado["cancelador_global"].is_set():
            logger.warning("shopify_fetch_cancelled_end")
            return

        logger.info("shopify_fetch_done", extra={"qtd_pedidos": len(pedidos)})

        # Armazenando os dados coletados temporariamente no estado
        for pedido in pedidos:
            pedido_id = normalizar_transaction_id(pedido["id"])
            self.estado["dados_temp"]["cpfs"][pedido_id] = pedido.get("cpf_extraido", "")
            self.estado["dados_temp"]["bairros"][pedido_id] = ""
            end = pedido.get("shippingAddress") or {}
            self.estado["dados_temp"]["enderecos"][pedido_id] = {
                "endereco_base": end.get("address1", ""),
                "numero": end.get("address2", ""),
                "complemento": end.get("provinceCode", ""),
            }

            # status fulfillment
            status_fulfillment = (pedido.get("displayFulfillmentStatus") or "").strip().upper()
            self.estado["dados_temp"]["status_fulfillment"][pedido_id] = status_fulfillment

            # frete (robusto a None)
            valor_frete = (
                ((pedido.get("shippingLine") or {}).get("discountedPriceSet") or {}).get(
                    "shopMoney", {}
                )
            ).get("amount")
            try:
                valor_frete = float(valor_frete) if valor_frete is not None else 0.0
            except Exception:
                valor_frete = 0.0
            self.estado["dados_temp"]["fretes"][pedido_id] = valor_frete

            # desconto (robusto a None)
            valor_desconto = (
                (pedido.get("currentTotalDiscountsSet") or {}).get("shopMoney") or {}
            ).get("amount")
            try:
                valor_desconto = float(valor_desconto) if valor_desconto is not None else 0.0
            except Exception:
                valor_desconto = 0.0
            self.estado["dados_temp"]["descontos"][pedido_id] = valor_desconto

        self.sinais.resultado.emit(pedidos)


class VerificadorDeEtapa(QObject):
    def __init__(
        self,
        estado,
        chave,
        total_esperado,
        get_pendentes,
        callback_final=None,
        intervalo_ms=300,
        timeout=60,
        max_intervalo_ms=5000,
        log_cada_n_checks=10,
    ):
        super().__init__()
        self.estado = estado
        self.chave = chave
        self.total_esperado = total_esperado
        self.get_pendentes = get_pendentes
        self.callback_final = callback_final

        # controle de temporização
        self.intervalo_inicial_ms = max(50, int(intervalo_ms))
        self.intervalo_atual_ms = self.intervalo_inicial_ms
        self.max_intervalo_ms = max_intervalo_ms
        self.timeout = timeout

        # book-keeping
        self.contador = 0
        self._encerrado = False
        self._ultimo_len = None
        self._ultimo_tick_com_progresso = time.monotonic()
        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.timeout.connect(self._verificar)

        # logging
        self._log_cada_n = max(1, int(log_cada_n_checks))
        self._parent_correlation_id = get_correlation_id()

    def iniciar(self):
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

    def _reagendar(self):
        if self._encerrado:
            return
        self._timer.start(self.intervalo_atual_ms)

    def _verificar(self):
        if self._encerrado:
            return

        self.contador += 1
        pendentes = self.get_pendentes() or set()
        lp = len(pendentes)
        cancelado = self.estado["cancelador_global"].is_set()

        # timeout real em segundos (não em número de checks)
        if (time.monotonic() - self._ultimo_tick_com_progresso) > self.timeout and cancelado:
            logger.warning("monitor_timeout_cancelled", extra={"chave": self.chave})
            self._encerrar()
            return

        # log só quando muda ou a cada N checks
        if (
            self._ultimo_len is None
            or lp != self._ultimo_len
            or (self.contador % self._log_cada_n == 0)
        ):
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
                    logger.exception(
                        "monitor_callback_final_error", extra={"chave": self.chave, "err": str(e)}
                    )
            return

        # se já foi marcada como finalizada por outro caminho, encerra
        if self.estado.get(f"finalizou_{self.chave}", False):
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

    def _encerrar(self):
        if self._encerrado:
            return
        self._encerrado = True
        try:
            self._timer.stop()
        except Exception:
            pass
        logger.info("monitor_closed", extra={"chave": self.chave})


# Funções auxiliares shopify


def limpar_telefone(tel):
    return re.sub(r"\D", "", tel or "").removeprefix("55")


busca_cep_lock = threading.Lock()


def buscar_cep_com_timeout(cep, timeout=5):
    try:
        # sem lock global, sem sleep serializador
        return get_address_from_cep(cep, timeout=timeout)
    except exceptions.CEPNotFound:
        print(f"⚠️ CEP {cep} não encontrado.")
    except Exception as e:
        print(f"❌ Erro ao consultar o CEP {cep}: {e}")
    return {}


# Funções de Fluxo


def iniciar_busca_cpfs(estado, gerenciador, depois=None):
    df_temp = estado.get("df_temp")
    gerenciador.atualizar("🔍 Coletando CPF dos pedidos...", 0, 0)

    if df_temp is None or df_temp.empty:
        logger.warning("[⚠️] Não há dados de pedidos coletados.")
        return

    estado.setdefault("etapas_finalizadas", {})
    if estado.get("cancelador_global") and estado["cancelador_global"].is_set():
        logger.info("[🛑] Cancelamento detectado antes de iniciar busca de CPFs.")
        if gerenciador:
            gerenciador.fechar()
        return

    # 🔍 Quais pedidos ainda sem CPF
    serie_cpf = df_temp["CPF/CNPJ Comprador"].fillna("").astype(str)
    faltando_cpf = serie_cpf.str.strip() == ""
    pedidos_faltantes = (
        df_temp.loc[faltando_cpf, "transaction_id"].dropna().astype(str).str.strip().tolist()
    )

    if not pedidos_faltantes:
        logger.info("[✅] Todos os CPFs já foram coletados.")
        if callable(depois) and not estado["cancelador_global"].is_set():
            depois()
        return

    # ✅ Normaliza e remove duplicados UMA vez só
    pendentes_set = {normalizar_transaction_id(pid) for pid in pedidos_faltantes}
    estado["cpf_pendentes"] = pendentes_set
    estado["cpf_total_esperado"] = len(pendentes_set)

    # 🔁 Inicia threads de coleta (evita duplicados)
    pool = QThreadPool.globalInstance()

    def continuar_para_bairros():
        if estado["cancelador_global"].is_set():
            if gerenciador:
                gerenciador.fechar()
            return
        iniciar_busca_bairros(estado, gerenciador, depois=depois)

    for pedido_id in pendentes_set:
        if estado["cancelador_global"].is_set():
            break
        runnable = ObterCpfShopifyRunnable(pedido_id, estado)
        runnable.signals.resultado.connect(
            partial(
                slot_cpf_ok, estado=estado, gerenciador=gerenciador, depois=continuar_para_bairros
            )
        )
        pool.start(runnable)

    # ✅ Verificador com intervalo inicial maior (use com backoff na classe)
    estado["verificador_cpf"] = VerificadorDeEtapa(
        estado=estado,
        chave="cpf",
        total_esperado=estado["cpf_total_esperado"],
        get_pendentes=lambda: estado.get("cpf_pendentes", set()),
        callback_final=continuar_para_bairros,
        intervalo_ms=1000,  # inicial mais calmo
        # se sua classe aceitar, passe também:
        # max_intervalo_ms=8000,
        # log_cada_n_checks=20,
    )
    estado["verificador_cpf"].iniciar()


def iniciar_busca_bairros(estado, gerenciador, depois=None):
    df = estado.get("df_temp")
    if df is None or df.empty:
        logger.warning("[⚠️] Nenhuma planilha temporária encontrada.")
        return

    gerenciador.atualizar("📍 Buscando bairros dos pedidos...", 0, 0)

    estado.setdefault("etapas_finalizadas", {})
    if estado["cancelador_global"].is_set():
        logger.info("[🛑] Cancelamento detectado antes da busca de bairros.")
        if gerenciador:
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
        .dropna(
            subset=["transaction_id"]
        )  # mantém linhas com CEP NaN se quiser tentar outra estratégia
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
    pendentes_set = {
        normalizar_transaction_id(pid) for pid in pendentes_df["transaction_id"].astype(str)
    }
    estado["bairro_total_esperado"] = len(pendentes_set)
    estado["bairro_pendentes"] = set(pendentes_set)  # cópia defensiva

    pool = QThreadPool.globalInstance()

    # Dispara runnables
    for _, linha in pendentes_df.iterrows():
        if estado["cancelador_global"].is_set():
            logger.info("[🛑] Cancelamento detectado durante o disparo de tarefas de bairro.")
            break

        pedido_id = normalizar_transaction_id(str(linha["transaction_id"]))
        cep = "" if pd.isna(linha["CEP Comprador"]) else str(linha["CEP Comprador"]).strip()

        runnable = BuscarBairroRunnable(
            pedido_id,
            cep,
            df,
            # callback de cada item
            lambda pid, bairro: slot_bairro_ok(
                pedido_id=pid, bairro=bairro, estado=estado, gerenciador=gerenciador, depois=depois
            ),
            estado,
        )
        pool.start(runnable)

    # Verificador persistente (use intervalo maior; se sua classe tiver backoff, melhor ainda)
    estado["verificador_bairro"] = VerificadorDeEtapa(
        estado=estado,
        chave="bairro",
        total_esperado=estado["bairro_total_esperado"],
        get_pendentes=lambda: estado.get("bairro_pendentes", set()),
        callback_final=lambda: iniciar_normalizacao_enderecos(estado, gerenciador, depois),
        intervalo_ms=800,  # menos agressivo que 300ms
        # Se disponível na sua classe:
        # max_intervalo_ms=5000,
        # log_cada_n_checks=30,
    )
    estado["verificador_bairro"].iniciar()


def iniciar_normalizacao_enderecos(estado, gerenciador, depois=None):
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

    df = estado.get("df_temp")
    gerenciador.atualizar("📦 Normalizando endereços...", 0, 0)
    if df is None or df.empty:
        logger.warning("[⚠️] Nenhuma planilha temporária encontrada.")
        return
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
            finalizar_endereco_normalizado(estado, gerenciador)
        except Exception:
            logger.exception("[❌] Erro ao finalizar no caminho zero-pendentes")
        if callable(depois):
            try:
                depois()
            except Exception:
                logger.exception("[❌] Erro no 'depois()' após zero-pendentes")
        return

    logger.info(f"[📦] Normalizando {total} endereços.")

    pendentes_set = {
        normalizar_transaction_id(str(pid)) for pid in pendentes_df["transaction_id"].astype(str)
    }
    estado["endereco_total_esperado"] = len(pendentes_set)
    estado["endereco_pendentes"] = set(pendentes_set)

    logger.info(f"[🧪] Iniciando {len(pendentes_set)} NormalizarEnderecoRunnable(s)...")

    pool = QThreadPool.globalInstance()
    for _, linha in pendentes_df.iterrows():
        if estado["cancelador_global"].is_set():
            logger.info(
                "[🛑] Cancelamento detectado durante o disparo de normalizações de endereço."
            )
            break
        pedido_id = normalizar_transaction_id(str(linha["transaction_id"]))
        endereco_raw = "" if pd.isna(linha["Endereço Entrega"]) else str(linha["Endereço Entrega"])
        complemento_raw = (
            ""
            if pd.isna(linha.get("Complemento Entrega"))
            else str(linha.get("Complemento Entrega"))
        )
        runnable = NormalizarEnderecoRunnable(
            pedido_id,
            endereco_raw,
            complemento_raw,
            lambda pid, dados: ao_finalizar_endereco(pid, dados, estado, gerenciador, depois),
            sinal_finalizacao=FinalizacaoProgressoSignal(),
            estado=estado,
        )
        pool.start(runnable)

    estado["verificador_endereco"] = VerificadorDeEtapa(
        estado=estado,
        chave="endereco",
        total_esperado=estado["endereco_total_esperado"],
        get_pendentes=lambda: estado.get("endereco_pendentes", set()),
        callback_final=lambda: finalizar_endereco_normalizado(estado, gerenciador),
        intervalo_ms=800,
    )
    estado["verificador_endereco"].iniciar()


def ao_finalizar_endereco(pedido_id, endereco_dict, estado, gerenciador, depois_callback):
    # Proteção contra chamadas após finalização
    if estado.get("finalizou_endereco"):
        logger.debug(
            f"[🛑] Ignorando ao_finalizar_endereco para {pedido_id} - etapa já foi finalizada."
        )
        return

    pedido_id = normalizar_transaction_id(pedido_id)
    logger.info(
        f"[🧪] ao_finalizar_endereco chamado para {pedido_id} - gerenciador={id(gerenciador)}"
    )

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
    estado["enderecos_normalizados"][pedido_id] = endereco_dict
    estado["endereco_pendentes"].remove(pedido_id)

    total = estado.get("endereco_total_esperado", 0)
    atual = total - len(estado["endereco_pendentes"])
    logger.info(f"[📦] Endereços normalizados: {atual}/{total}")

    # Se todos foram normalizados, finaliza a etapa
    if not estado["endereco_pendentes"]:
        if not estado.get("finalizou_endereco", False):
            logger.info("[✅] Todos os endereços finalizados.")
            estado["etapas_finalizadas"]["endereco"] = True
            estado["finalizou_endereco"] = True

            atualizar_planilha_shopify(estado, gerenciador)

            if callable(depois_callback):
                logger.info("[📞] Chamando `depois()` após normalização.")
                try:
                    depois_callback()
                except Exception as e:
                    logger.exception(f"[❌] Erro ao executar `depois()` após normalização: {e}")
        else:
            logger.debug("[🟡] ao_finalizar_endereco ignorado - etapa já finalizada.")


def endereco_parece_completo(address1: str) -> bool:
    if not address1 or "," not in address1:
        return False

    partes = [p.strip() for p in address1.split(",")]
    if len(partes) < 2:
        return False

    # Verifica se a segunda parte tem ao menos um número
    return any(char.isdigit() for char in partes[1])


def executar_fluxo_loja(estado):
    gerenciador = GerenciadorProgresso(
        titulo="🔎 Buscando pedidos na Shopify",
        com_percentual=False,
        estado_global=estado,
        logger_obj=logger,
    )
    estado["gerenciador_progresso"] = gerenciador
    gerenciador.atualizar("🔄 Buscando pedidos pagos na Shopify...", 0, 0)

    data_inicio = estado["entrada_data_inicio"].date().toString("dd/MM/yyyy")
    fulfillment_status = estado["combo_status"].currentText()
    produto_alvo = (
        estado["combo_produto"].currentText() if estado["check_produto"].isChecked() else None
    )
    skus_info = estado["skus_info"]

    iniciar_todas_as_buscas(
        estado=estado,
        gerenciador=gerenciador,
        data_inicio_str=data_inicio,
        produto_alvo=produto_alvo,
        skus_info=skus_info,
        fulfillment_status=fulfillment_status,
        depois=lambda: iniciar_normalizacao_enderecos(estado, gerenciador),
    )


def iniciar_todas_as_buscas(
    estado,
    gerenciador,
    data_inicio_str,
    produto_alvo=None,
    skus_info=None,
    fulfillment_status="any",
    depois=None,
):
    print("[🧪] iniciar_todas_as_buscas recebeu depois =", depois)
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
    runnable = BuscarPedidosPagosRunnable(data_inicio_str, estado, fulfillment_status)
    runnable.sinais.resultado.connect(
        lambda pedidos: tratar_resultado(
            pedidos, produto_alvo, skus_info, estado, gerenciador, depois
        )
    )
    runnable.sinais.erro.connect(lambda msg: tratar_erro(msg, estado, gerenciador))

    QThreadPool.globalInstance().start(runnable)


def registrar_log_endereco(pedido_id, dados):
    try:
        log_path = os.path.abspath("log_enderecos.txt")
        with open(log_path, "a", encoding="utf-8") as f:
            f.write(f"Pedido {pedido_id}:\n")
            f.write(f"  📥 address1 (usuário): {dados.get('raw_address1', '')}\n")
            f.write(f"  📥 address2 (usuário): {dados.get('raw_address2', '')}\n")
            f.write(f"  ✅ Endereço base: {dados.get('endereco_base')}\n")
            f.write(f"  🏷️ Número: {dados.get('numero')}\n")
            f.write(f"  🧩 Complemento: {dados.get('complemento')}\n")
            f.write(f"  📍 Precisa contato: {dados.get('precisa_contato')}\n")
            f.write(f"  🧾 Logradouro oficial (CEP): {dados.get('logradouro_oficial')}\n")
            f.write(f"  🏘️ Bairro oficial (CEP): {dados.get('bairro_oficial')}\n")
            f.write("-" * 50 + "\n")
    except Exception as e:
        print(f"[⚠️] Erro ao registrar log do pedido {pedido_id}: {e}")


class GPTRateLimiter:
    def __init__(self, max_concorrentes=4, intervalo_minimo=0.3):
        self._semaforo = threading.BoundedSemaphore(value=max_concorrentes)
        self._lock = threading.Lock()
        self._ultima_chamada = 0
        self._intervalo_minimo = intervalo_minimo  # em segundos

    def chamar(self, prompt, client, model="gpt-4o"):
        with self._semaforo:
            with self._lock:
                agora = time.time()
                tempo_decorrido = agora - self._ultima_chamada
                if tempo_decorrido < self._intervalo_minimo:
                    time.sleep(self._intervalo_minimo - tempo_decorrido)
                self._ultima_chamada = time.time()

            for tentativa in range(3):
                try:
                    response = client.chat.completions.create(
                        model=model,
                        messages=[{"role": "user", "content": prompt}],
                        temperature=0,
                        timeout=10,
                    )
                    conteudo = response.choices[0].message.content.strip()
                    json_inicio = conteudo.find("{")
                    json_fim = conteudo.rfind("}") + 1
                    if json_inicio >= 0 and json_fim > json_inicio:
                        return json.loads(conteudo[json_inicio:json_fim])
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
        return {"base": prompt, "numero": "s/n", "complemento": "", "precisa_contato": True}


gpt_limiter = GPTRateLimiter(max_concorrentes=3, intervalo_minimo=0.6)


def usar_gpt_callback(address1, address2, logradouro_cep, bairro_cep):
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

    return gpt_limiter.chamar(prompt, client)


def finalizar_endereco_normalizado(estado, gerenciador=None):
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
    aguardar_e_resetar_pool()
    resetar_etapas_estado(estado)


def aguardar_e_resetar_pool():
    pool = QThreadPool.globalInstance()
    pool.waitForDone(5000)  # Espera até 5s

    while pool.activeThreadCount() > 0:
        logger.warning(
            f"[⚠️] Ainda há {pool.activeThreadCount()} threads ativas no pool - aguardando..."
        )
        time.sleep(0.5)
        pool.waitForDone(500)

    pool.clear()
    pool.setMaxThreadCount(30)
    logger.info("[✅] QThreadPool limpo com sucesso.")


def resetar_etapas_estado(estado):
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


def atualizar_planilha_shopify(estado, gerenciador):
    def encerrar_se_cancelado(mensagem):
        if estado.get("cancelador_global", threading.Event()).is_set():
            logger.warning(f"[🛑] {mensagem}")
            if gerenciador:
                gerenciador.fechar()
            return True
        return False

    if encerrar_se_cancelado("Cancelamento detectado antes de atualizar a planilha."):
        return

    # garante skus_info disponível para eh_indisponivel
    estado.setdefault("skus_info", {})

    etapas = estado.get("etapas_finalizadas", {})
    if not (etapas.get("cpf") and etapas.get("bairro") and etapas.get("endereco")):
        logger.warning(f"[⚠️] Dados incompletos! Etapas: {etapas}")
        return

    df = estado.get("df_temp")
    if df is None or df.empty:
        logger.warning("[⚠️] DataFrame temporário não encontrado.")
        return

    logger.info("[✅] Todos os dados foram coletados. Atualizando a planilha...")

    # -- preenchimentos por pedido (CPF, bairro, endereço) --
    for pedido_id, cpf in estado.get("dados_temp", {}).get("cpfs", {}).items():
        if encerrar_se_cancelado("Cancelamento durante preenchimento de CPF."):
            return
        pid = normalizar_transaction_id(pedido_id)
        idx = df["transaction_id"].astype(str).str.strip() == pid
        df.loc[idx, "CPF/CNPJ Comprador"] = cpf

    for pedido_id, bairro in estado.get("dados_temp", {}).get("bairros", {}).items():
        if encerrar_se_cancelado("Cancelamento durante preenchimento de bairro."):
            return
        pid = normalizar_transaction_id(pedido_id)
        idx = df["transaction_id"].astype(str).str.strip() == pid
        df.loc[idx, "Bairro Comprador"] = bairro

    for pedido_id, endereco in estado.get("enderecos_normalizados", {}).items():
        if encerrar_se_cancelado("Cancelamento durante preenchimento de endereço."):
            return
        pid = normalizar_transaction_id(pedido_id)
        idx = df["transaction_id"].astype(str).str.strip() == pid
        df.loc[idx, "Endereço Comprador"] = endereco.get("endereco_base", "")
        df.loc[idx, "Número Comprador"] = endereco.get("numero", "")
        df.loc[idx, "Complemento Comprador"] = endereco.get("complemento", "")
        df.loc[idx, "Precisa Contato"] = endereco.get("precisa_contato", "")
        df.loc[idx, "Endereço Entrega"] = endereco.get("endereco_base", "")
        df.loc[idx, "Número Entrega"] = endereco.get("numero", "")
        df.loc[idx, "Complemento Entrega"] = endereco.get("complemento", "")
        df.loc[idx, "Bairro Entrega"] = estado["dados_temp"]["bairros"].get(pid, "")

    # telefones normalizados
    for col in ["Telefone Comprador", "Celular Comprador"]:
        if col in df.columns:
            df[col] = df[col].apply(limpar_telefone)

    # -- NOVO: coluna "indisponivel" baseada no skus.json --
    if "Produto" in df.columns:
        try:
            df["indisponivel"] = df["Produto"].apply(
                lambda n: "S" if eh_indisponivel(str(n)) else "N"
            )
        except Exception as e:
            logger.exception(f"[⚠️] Falha ao calcular 'indisponivel': {e}")

    # 🔁 restaura frete, status e desconto capturados em tratar_resultado (se existirem)
    if "fretes_shopify" in estado:
        estado.setdefault("dados_temp", {})["fretes"] = estado["fretes_shopify"]
    if "status_fulfillment_shopify" in estado:
        estado.setdefault("dados_temp", {})["status_fulfillment"] = estado[
            "status_fulfillment_shopify"
        ]
    if "descontos_shopify" in estado:
        estado.setdefault("dados_temp", {})["descontos"] = estado["descontos_shopify"]

    estado["df_planilha_parcial"] = df
    logger.info(f"[✅] Planilha atualizada com {len(df)} linhas.")


def exibir_alerta_revisao(enderecos_normalizados):
    """
    Mostra um alerta simples com a quantidade de endereços que exigem contato.
    """
    total = sum(
        1
        for dados in enderecos_normalizados.values()
        if dados.get("precisa_contato", "").strip().upper() == "SIM"
    )

    if total > 0:
        QMessageBox.information(
            None,
            "Revisão necessária",
            f"{total} pedido(s) precisam ser revisados.\n\nEdite a planilha antes de exportar.",
        )


def tratar_resultado(pedidos, produto_alvo, skus_info, estado, gerenciador, depois):
    print("[🧪] tratar_resultado recebeu depois =", depois)
    estado["df_temp"] = pd.DataFrame()
    df_temp = estado.get("df_temp", pd.DataFrame())

    # modo de coleta: "any" (tudo) ou "unfulfilled" (somente pendentes)
    modo_fs = (estado.get("fulfillment_status_selecionado") or "any").strip().lower()

    # Filtro por produto específico (se marcado)
    ids_filtrados = set()
    if produto_alvo and skus_info:
        produto_alvo = produto_alvo.strip().lower()
        for nome_produto, dados in skus_info.items():
            if produto_alvo in nome_produto.lower():
                ids_filtrados.update(map(str, dados.get("shopify_ids", [])))

    linhas_geradas = []
    for pedido in pedidos:
        # --- dados básicos do pedido (robustos a None) ---
        cust = pedido.get("customer") or {}
        first = (cust.get("firstName") or "").strip()
        last = (cust.get("lastName") or "").strip()
        nome_cliente = f"{first} {last}".strip()
        email = cust.get("email") or ""
        endereco = pedido.get("shippingAddress") or {}  # pode vir None
        telefone = endereco.get("phone", "") or ""
        transaction_id = str(pedido.get("id") or "").split("/")[-1]

        # --- frete / status / desconto ---
        valor_frete = (
            ((pedido.get("shippingLine") or {}).get("discountedPriceSet") or {}).get(
                "shopMoney", {}
            )
        ).get("amount")
        try:
            valor_frete = float(valor_frete) if valor_frete is not None else 0.0
        except Exception:
            valor_frete = 0.0

        status_fulfillment = (pedido.get("displayFulfillmentStatus") or "").strip().upper()

        valor_desconto = (
            (pedido.get("currentTotalDiscountsSet") or {}).get("shopMoney") or {}
        ).get("amount")
        try:
            valor_desconto = float(valor_desconto) if valor_desconto is not None else 0.0
        except Exception:
            valor_desconto = 0.0

        estado.setdefault("dados_temp", {}).setdefault("fretes", {})[transaction_id] = valor_frete
        estado.setdefault("dados_temp", {}).setdefault("status_fulfillment", {})[
            transaction_id
        ] = status_fulfillment
        estado.setdefault("dados_temp", {}).setdefault("descontos", {})[
            transaction_id
        ] = valor_desconto

        print(
            f"[🧾] Pedido {transaction_id} → Status: {status_fulfillment} | Frete: {valor_frete} | Desconto: {valor_desconto}"
        )

        # --- mapa remainingQuantity por lineItem.id (a partir de fulfillmentOrders) ---
        remaining_por_line = {}
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
                        # se aparecer repetido em múltiplos FOs (raro), guarde o maior
                        remaining_por_line[lid] = max(remaining_por_line.get(lid, 0), rq)
        except Exception:
            remaining_por_line = {}

        # também guardamos o total restante do pedido (útil para “último lote” depois)
        total_remaining_pedido = sum(remaining_por_line.values())
        estado.setdefault("dados_temp", {}).setdefault("remaining_totais", {})[transaction_id] = (
            int(total_remaining_pedido)
        )

        # --- CEP por pedido (já fazia) ---
        estado.setdefault("cep_por_pedido", {})[transaction_id] = (
            (endereco.get("zip", "") or "").replace("-", "").strip()
        )

        # --- processar line items ---
        for item_edge in (pedido.get("lineItems") or {}).get("edges", []):
            item = item_edge.get("node") or {}
            product_id_raw = (item.get("product") or {}).get("id", "")
            if not product_id_raw:
                continue

            product_id = str(product_id_raw).split("/")[-1]
            if ids_filtrados and product_id not in ids_filtrados:
                continue

            # Descobre nome do produto e SKU a partir do mapeamento do skus.json
            nome_produto = ""
            sku_item = ""
            for nome_local, dados in skus_info.items():
                if product_id in map(str, dados.get("shopify_ids", [])):
                    nome_produto = nome_local
                    sku_item = dados.get("sku", "")
                    break

            base_qtd = int(item.get("quantity") or 0)
            valor_total_linha = float(
                ((item.get("discountedTotalSet") or {}).get("shopMoney") or {}).get("amount") or 0
            )
            valor_unitario = round(valor_total_linha / base_qtd, 2) if base_qtd else 0.0
            id_line_item = str(item.get("id", "")).split("/")[-1]

            # Quantidade a gerar conforme o modo selecionado
            if modo_fs == "unfulfilled":
                remaining = int(remaining_por_line.get(id_line_item, 0))
                if remaining <= 0:
                    continue
                qtd_a_gerar = remaining
            else:
                # "any" → gera todas as unidades (mesmo já processadas)
                qtd_a_gerar = base_qtd if base_qtd > 0 else 0

            # Flag de disponibilidade (usa regra local)
            indisponivel_flag = "S" if eh_indisponivel(nome_produto) else "N"

            for _ in range(qtd_a_gerar):
                linha = {
                    "Número pedido": pedido.get("name", ""),
                    "Nome Comprador": nome_cliente,
                    "Data Pedido": (pedido.get("createdAt") or "")[:10],
                    "Data": datetime.today().strftime("%d/%m/%Y"),
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
                    "Valor Unitário": f"{valor_unitario:.2f}".replace(".", ","),
                    "Valor Total": f"{valor_unitario:.2f}".replace(".", ","),
                    "Total Pedido": "",
                    # estes campos serão sobrescritos/ajustados em aplicar_lotes
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
    estado["status_fulfillment_shopify"] = (
        estado.get("dados_temp", {}).get("status_fulfillment", {}).copy()
    )
    estado["descontos_shopify"] = estado.get("dados_temp", {}).get("descontos", {}).copy()

    logger.info("[🚀] Iniciando fluxo de coleta de CPFs após tratar_resultado.")
    gerenciador.atualizar("📦 Processando transações recebidas...", 0, 0)
    iniciar_busca_cpfs(estado, estado.get("gerenciador_progresso"), depois)


def slot_cpf_ok(pedido_id, cpf, estado, gerenciador=None):
    pedido_id = normalizar_transaction_id(pedido_id)
    estado.setdefault("cpf_pendentes", set())
    estado.setdefault("dados_temp", {}).setdefault("cpfs", {})

    if estado.get("cancelador_global", threading.Event()).is_set():
        logger.warning(f"[🛑] Cancelamento detectado durante slot_cpf_ok → pedido {pedido_id}")
        if gerenciador:
            gerenciador.fechar()
        return

    if pedido_id not in estado["cpf_pendentes"]:
        logger.debug(
            f"[🟡] Pedido {pedido_id} já removido de cpf_pendentes ou não pertence ao conjunto. Ignorando."
        )
        return

    estado["cpf_pendentes"].discard(pedido_id)
    estado["dados_temp"]["cpfs"][pedido_id] = cpf

    total = estado.get("cpf_total_esperado", 0)
    atual = total - len(estado["cpf_pendentes"])
    logger.info(f"[📌] CPF {atual}/{total} coletado para pedido {pedido_id}")


def slot_bairro_ok(pedido_id, bairro, estado, gerenciador=None, depois=None):
    pedido_id = normalizar_transaction_id(pedido_id)
    estado.setdefault("bairro_pendentes", set())
    estado.setdefault("dados_temp", {}).setdefault("bairros", {})

    if pedido_id in estado["bairro_pendentes"]:
        estado["bairro_pendentes"].discard(pedido_id)
        estado["dados_temp"]["bairros"][pedido_id] = bairro

        total = estado.get("bairro_total_esperado", 0)
        atual = total - len(estado["bairro_pendentes"])
        logger.info(f"[📍] Bairros: {atual}/{total}")

    else:
        logger.debug(f"[🟡] Pedido {pedido_id} já processado ou inexistente em pendentes.")

    if not estado["bairro_pendentes"]:
        if not estado["etapas_finalizadas"].get("bairro") and not estado.get(
            "finalizou_bairro", False
        ):
            estado["etapas_finalizadas"]["bairro"] = True
            estado["finalizou_bairro"] = True
            logger.info("[✅] Todos os bairros coletados.")

            if estado.get("cancelador_global", threading.Event()).is_set():
                logger.warning("[🛑] Cancelamento detectado após bairros.")
                if gerenciador:
                    gerenciador.fechar()
                return

            if callable(depois):
                logger.info("[📞] Chamando função `depois()` após bairros.")
                try:
                    depois()
                except Exception as e:
                    logger.exception(f"[❌] Erro no callback `depois()` de bairro: {e}")


def tratar_erro(gerenciador):
    thread_ui = QCoreApplication.instance().thread()
    if QThread.currentThread() == thread_ui:
        gerenciador.fechar()
    else:
        QTimer.singleShot(0, gerenciador.fechar)


# Funções de mapeamento dos produtos da Loja


def abrir_dialogo_mapeamento_skus(skus_info, produtos_shopify, skus_path):
    class DialogoMapeamento(QDialog):
        def __init__(self):
            super().__init__()
            self.setWindowTitle("Mapear SKUs com Produtos da Shopify")
            self.setMinimumSize(800, 500)

            layout = QVBoxLayout(self)

            self.label_sku_atual = QLabel("Produto local: (nenhum)")
            layout.addWidget(self.label_sku_atual)

            # Filtro
            busca_row = QHBoxLayout()
            busca_row.addWidget(QLabel("Filtro:"))
            self.input_busca = QLineEdit()
            self.input_busca.setPlaceholderText("Digite para filtrar produtos da Shopify…")
            busca_row.addWidget(self.input_busca)
            layout.addLayout(busca_row)

            self.lista = QListWidget()
            self.lista.setSelectionMode(QAbstractItemView.MultiSelection)
            layout.addWidget(self.lista)

            # Botões
            botoes = QHBoxLayout()
            self.btn_pular = QPushButton("Pular")
            self.btn_salvar = QPushButton("Salvar e Próximo")
            self.btn_concluir = QPushButton("Concluir")
            botoes.addWidget(self.btn_pular)
            botoes.addStretch(1)
            botoes.addWidget(self.btn_salvar)
            botoes.addWidget(self.btn_concluir)
            layout.addLayout(botoes)

            # Estado
            self.skus = list(skus_info.keys())
            self.idx_atual = 0
            self.produtos = produtos_shopify or []

            # Sinais
            self.btn_pular.clicked.connect(self.pular)
            self.btn_salvar.clicked.connect(self.salvar_selecao)
            self.btn_concluir.clicked.connect(self.accept)
            self.input_busca.textChanged.connect(self._popular_lista)

            # atalhos práticos
            QShortcut(QKeySequence("Ctrl+Right"), self, activated=self.pular)
            QShortcut(QKeySequence("Ctrl+S"), self, activated=self.salvar_selecao)

            # inicia
            self._iniciar_proximo()

        def _iniciar_proximo(self):
            if self.idx_atual >= len(self.skus):
                with open(skus_path, "w", encoding="utf-8") as f:
                    json.dump(skus_info, f, indent=4, ensure_ascii=False)
                QMessageBox.information(self, "Concluído", "Mapeamento finalizado com sucesso.")
                self.accept()
                return

            self.lista.clear()
            self.input_busca.clear()
            self.nome_local = self.skus[self.idx_atual]
            self.label_sku_atual.setText(f"Produto local: {self.nome_local}")
            self._popular_lista()

        def _popular_lista(self):
            termo = unidecode(self.input_busca.text().strip().lower())
            self.lista.clear()

            nome_norm = unidecode(str(self.nome_local).lower())
            for p in self.produtos:
                titulo = p.get("name") or p.get("title") or ""
                pid = str(p.get("id") or p.get("product_id") or "").strip()
                if not pid:
                    continue
                titulo_norm = unidecode(titulo.lower())
                passa_nome = (nome_norm in titulo_norm) or (titulo_norm in nome_norm)
                passa_termo = (not termo) or (termo in titulo_norm) or (termo in pid)
                if passa_nome and passa_termo:
                    it = QListWidgetItem(f"{titulo}  [{pid}]")
                    it.setData(Qt.UserRole, pid)
                    it.setToolTip(f"product_id: {pid}")
                    self.lista.addItem(it)

        def pular(self):
            # não salva nada para este produto local; apenas avança
            self.idx_atual += 1
            self._iniciar_proximo()

        def salvar_selecao(self):
            itens = self.lista.selectedItems()
            if not itens:
                # permitir salvar “vazio” também? você decide.
                # aqui vou só avisar:
                if (
                    QMessageBox.question(
                        self,
                        "Sem seleção",
                        "Nenhum produto selecionado. Deseja pular este item?",
                        QMessageBox.Yes | QMessageBox.No,
                    )
                    == QMessageBox.Yes
                ):
                    self.pular()
                return

            novos_ids = [
                str(it.data(Qt.UserRole) or "").strip()
                for it in itens
                if str(it.data(Qt.UserRole) or "").strip()
            ]

            entrada = skus_info.setdefault(self.nome_local, {})
            entrada.setdefault("tipo", entrada.get("tipo") or "produto")
            entrada.setdefault("sku", entrada.get("sku", ""))
            entrada.setdefault("peso", entrada.get("peso", 0.0))
            entrada.setdefault("shopify_ids", [])

            ja = set(map(str, entrada["shopify_ids"]))
            for pid in novos_ids:
                if pid not in ja:
                    entrada["shopify_ids"].append(pid)
                    ja.add(pid)

            try:
                with open(skus_path, "w", encoding="utf-8") as f:
                    json.dump(skus_info, f, indent=4, ensure_ascii=False)
            except Exception as e:
                QMessageBox.warning(self, "Aviso", f"Não foi possível salvar no disco agora: {e}")

            # feedback rápido e avança
            self.idx_atual += 1
            self._iniciar_proximo()

    dlg = DialogoMapeamento()
    dlg.exec_()


def mapear_skus_com_produtos_shopify(skus_info):
    produtos = buscar_todos_produtos_shopify()
    if not produtos:
        QMessageBox.warning(None, "Erro", "Nenhum produto retornado da Shopify.")
        return
    abrir_dialogo_mapeamento_skus(skus_info, produtos, skus_path)


def buscar_todos_produtos_shopify():
    api_version = obter_api_shopify_version()
    url = f"https://{settings.SHOP_URL}/admin/api/{api_version}/products.json?limit=250"
    headers = {"X-Shopify-Access-Token": settings.SHOPIFY_TOKEN, "Content-Type": "application/json"}

    todos = []
    pagina_atual = 1

    while url:
        resp = http_get(url, headers=headers, verify=False)
        if resp.status_code != 200:
            print(f"❌ Erro Shopify {resp.status_code}: {resp.text}")
            break

        produtos = resp.json().get("products", [])
        print(f"📄 Página {pagina_atual}: {len(produtos)} produtos retornados")

        for produto in produtos:
            id_produto = produto.get("id")
            titulo_produto = produto.get("title", "").strip()
            variants = produto.get("variants", [])

            for variante in variants:
                todos.append(
                    {
                        "product_id": id_produto,
                        "variant_id": variante.get("id"),
                        "title": titulo_produto,
                        "sku": variante.get("sku", "").strip(),
                    }
                )

        pagina_atual += 1

        link = resp.headers.get("Link", "")
        if 'rel="next"' in link:
            partes = link.split(",")
            next_url = [p.split(";")[0].strip().strip("<>") for p in partes if 'rel="next"' in p]
            url = next_url[0] if next_url else None
        else:
            break

    return todos


# Função para marcar itens como processados


def marcar_itens_como_fulfilled_na_shopify(df):
    if df is None or df.empty:
        print("⚠️ Nenhuma planilha carregada.")
        return

    total_fulfilled = {"count": 0}
    erros = []

    pool = QThreadPool.globalInstance()

    for order_id, grupo in df.groupby("transaction_id"):
        planilha_line_ids = {
            f"gid://shopify/LineItem/{int(rec.get('id_line_item'))}"
            for rec in grupo.to_dict("records")
            if rec.get("id_line_item")
        }

        runnable = FulfillPedidoRunnable(order_id, planilha_line_ids)

        def sucesso(oid, qtd):
            total_fulfilled["count"] += qtd
            print(f"✅ Pedido {oid} → {qtd} item(ns) enviados.")

        def falha(oid, msg):
            erros.append((oid, msg))
            print(f"❌ Erro no pedido {oid}: {msg}")

        runnable.signals.concluido.connect(sucesso)
        runnable.signals.erro.connect(falha)

        pool.start(runnable)

    print("🚚 Fulfillments iniciados. Acompanhe no console.")


# Cotação de fretes


def aplicar_lotes(
    df: pd.DataFrame, estado: dict | None = None, lote_inicial: int = 1
) -> pd.DataFrame:
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
    cpfs = (
        df_resultado["CPF/CNPJ Comprador"].fillna("").astype(str).str.replace(r"\D", "", regex=True)
    )
    ceps = df_resultado["CEP Entrega"].fillna("").astype(str).str.replace(r"\D", "", regex=True)

    df_resultado["chave_lote"] = emails + "_" + cpfs + "_" + ceps

    # Fallbacks da chave
    mask_vazia = emails.eq("") & cpfs.eq("") & ceps.eq("")
    if mask_vazia.any():
        df_resultado.loc[mask_vazia, "chave_lote"] = (
            df_resultado.loc[mask_vazia, "transaction_id"].astype(str).str.strip()
        )
        mask_ainda_vazia = df_resultado["chave_lote"].eq("")
        if mask_ainda_vazia.any():
            df_resultado.loc[mask_ainda_vazia, "chave_lote"] = df_resultado.loc[
                mask_ainda_vazia
            ].index.astype(str)

    if df_resultado.empty:
        print("\n[✅] Nenhum item válido para lote/cotação após remoção dos indisponíveis.\n")
        return df_resultado.drop(columns=["chave_lote"], errors="ignore")

    agrupado = df_resultado.groupby("chave_lote", dropna=False)

    # Dados auxiliares (se existirem)
    fretes = estado.get("dados_temp", {}).get("fretes", {}) if estado else {}
    status = estado.get("dados_temp", {}).get("status_fulfillment", {}) if estado else {}
    descontos = estado.get("dados_temp", {}).get("descontos", {}) if estado else {}

    aplicar_frete = bool(fretes) and bool(status)
    aplicar_desconto = bool(descontos) and bool(status)

    # Garante colunas de saída
    if aplicar_frete and "Valor Frete Pedido" not in df_resultado.columns:
        df_resultado["Valor Frete Pedido"] = ""
    if aplicar_desconto and "Valor Desconto Pedido" not in df_resultado.columns:
        df_resultado["Valor Desconto Pedido"] = ""
    # (opcional) totais do lote
    if "Valor Frete Lote" not in df_resultado.columns:
        df_resultado["Valor Frete Lote"] = ""
    if "Valor Desconto Lote" not in df_resultado.columns:
        df_resultado["Valor Desconto Lote"] = ""

    lote_atual = lote_inicial
    for grupo in agrupado:
        indices = grupo.index.tolist()
        id_lote_str = f"L{lote_atual:04d}"
        df_resultado.loc[indices, "ID Lote"] = id_lote_str

        if "transaction_id" in grupo.columns:
            pedidos_do_lote = grupo["transaction_id"].astype(str).unique()
            frete_total = 0.0
            desconto_total = 0.0

            for pid in pedidos_do_lote:
                pid_norm = normalizar_transaction_id(pid)
                status_atual = (status.get(pid_norm, "") or "").upper()
                is_partial = status_atual == "PARTIALLY_FULFILLED"

                # valor por pedido: partial vira 0
                frete_val = 0.0 if is_partial else float(fretes.get(pid_norm, 0.0) or 0.0)
                desc_val = 0.0 if is_partial else float(descontos.get(pid_norm, 0.0) or 0.0)

                # acumula total do lote (partial entra como 0, como você quer)
                frete_total += frete_val
                desconto_total += desc_val

                # grava por LINHA desse pedido no lote
                idx_pid = grupo.index[grupo["transaction_id"].astype(str) == pid]
                if aplicar_frete:
                    df_resultado.loc[idx_pid, "Valor Frete Pedido"] = (
                        "0,00" if is_partial else f"{frete_val:.2f}".replace(".", ",")
                    )
                if aplicar_desconto:
                    df_resultado.loc[idx_pid, "Valor Desconto Pedido"] = (
                        "0,00" if is_partial else f"{desc_val:.2f}".replace(".", ",")
                    )

                print(
                    f"[🧾] Pedido {pid_norm} | Status: {status_atual} | Frete usado: {frete_val} | Desconto usado: {desc_val}"
                )

            # (opcional) replica o total do lote em todas as linhas do lote
            df_resultado.loc[indices, "Valor Frete Lote"] = f"{frete_total:.2f}".replace(".", ",")
            df_resultado.loc[indices, "Valor Desconto Lote"] = f"{desconto_total:.2f}".replace(
                ".", ","
            )

            print(
                f"🔸 {id_lote_str} → {len(indices)} item(ns) | Frete total LOTE: R$ {frete_total:.2f} | Desconto total LOTE: R$ {desconto_total:.2f}"
            )
        else:
            print(f"🔸 {id_lote_str} → {len(indices)} item(ns)")

        lote_atual += 1

    # limpeza
    df_resultado.drop(columns=["chave_lote"], inplace=True, errors="ignore")
    print("\n[✅] Todos os lotes atribuídos com base em email + cpf + cep.\n")
    return df_resultado


def padronizar_transportadora_servico(row):
    nome_original = str(row.get("Transportadora", "")).strip().upper()

    mapeamento = {
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

    return row.get("Transportadora", ""), row.get("Serviço", "")


def gerar_payload_fretebarato(cep, total_pedido, peso_total):
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


def adicionar_checkboxes_transportadoras(layout, transportadoras_lista, transportadoras_var):
    for nome in transportadoras_lista:
        if nome not in transportadoras_var:
            checkbox = QCheckBox(nome)
            checkbox.setChecked(True)
            transportadoras_var[nome] = checkbox
            layout.addWidget(checkbox)


def cotar_para_lote(trans_id, linhas, selecionadas):
    """
    Faz a cotação de frete para um LOTE (agrupado por e-mail + CPF + CEP).
    'trans_id' aqui é o identificador do LOTE (ex.: 'L0001'), não de transação.

    Retorna: (lote_id, nome_transportadora, servico, valor) ou None.
    """
    try:
        lote_id = str(trans_id).strip()

        # 0) normaliza transportadoras selecionadas
        nomes_aceitos = {str(s).strip().upper() for s in (selecionadas or []) if str(s).strip()}
        if not nomes_aceitos:
            msg = f"Nenhuma transportadora selecionada para o lote {lote_id}."
            print(f"[⚠️] {msg}")
            try:
                comunicador_global.mostrar_mensagem.emit("aviso", "Cotação de Frete", msg)
            except Exception:
                pass
            return None

        # 1) garantir que há exatamente um ID Lote válido nas linhas
        lotes_presentes = {(str(row.get("ID Lote") or "").strip()) for row in linhas}
        lotes_presentes.discard("")  # remove vazios
        if len(lotes_presentes) != 1:
            vistos = sorted(lotes_presentes) or ["nenhum"]
            msg = f"Lote inconsistente: esperava 1 ID Lote, mas encontrei {vistos}."
            print(f"[⚠️] {msg} (grupo solicitado: {lote_id})")
            try:
                comunicador_global.mostrar_mensagem.emit(
                    "aviso", "Cotação de Frete", f"{msg}\nGrupo solicitado: {lote_id}"
                )
            except Exception:
                pass
            return None

        # filtra só as linhas do lote selecionado
        linhas_validas = [
            row for row in linhas if (str(row.get("ID Lote") or "").strip()) == lote_id
        ]
        if not linhas_validas:
            print(f"[⚠️] Lote {lote_id} ignorado: nenhuma linha válida.")
            return None

        # 2) CEP (usa a primeira linha do lote)
        cep = (linhas_validas[0].get("CEP Entrega") or "").strip()
        if not cep:
            msg = f"Lote {lote_id} ignorado: CEP não encontrado."
            print(f"[⚠️] {msg}")
            try:
                comunicador_global.mostrar_mensagem.emit("aviso", "Cotação de Frete", msg)
            except Exception:
                pass
            return None

        # 3) total do lote (somando itens com valor > 0; fallback por preco_fallback do SKU)
        total = 0.0
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
        peso = 0.0
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

        itens = len(linhas_validas)
        print(
            f"[🔎] Lote {lote_id} - CEP: {cep} | Itens: {itens} | Peso: {peso:.3f} kg | Total: R$ {total:.2f}"
        )

        if total <= 0 or peso <= 0:
            msg = f"Lote {lote_id} ignorado: total ou peso inválido."
            print(f"[❌] {msg}")
            try:
                comunicador_global.mostrar_mensagem.emit("aviso", "Cotação de Frete", msg)
            except Exception:
                pass
            return None

        # 5) cotação (API/formatos já corretos segundo seu ambiente)
        payload = gerar_payload_fretebarato(cep, total, peso)

        # 💡 Substituição: http_post com retries/backoff e respeito a 429/5xx
        try:
            r = http_post(
                settings.FRETEBARATO_URL,
                headers={"Content-Type": "application/json"},
                json=payload,
                timeout=(5, 30),  # mesmo padrão do DEFAULT_TIMEOUT
            )
        except ExternalError as e:
            print(
                f"[❌] Lote {lote_id}: falha ao chamar FreteBarato ({e.code}) - retryable={e.retryable}"
            )
            return None

        data = r.json()
        quotes = data.get("quotes", []) or []
        print(f"[📦] Lote {lote_id} - {len(quotes)} cotações recebidas")

        # filtra por transportadoras selecionadas
        opcoes = [q for q in quotes if str(q.get("name", "")).strip().upper() in nomes_aceitos]
        print(
            f"[🔎] Lote {lote_id} - {len(opcoes)} compatíveis com selecionadas: {sorted(nomes_aceitos)}"
        )

        if not opcoes:
            print(f"[⚠️] Lote {lote_id} - Nenhum frete aceito pelas transportadoras selecionadas.")
            return None

        melhor = sorted(opcoes, key=lambda x: float(x.get("price", 0) or 0))[0]
        print(
            f"[✅] Lote {lote_id} - Frete: {melhor['name']} ({melhor.get('service','')}) - R$ {float(melhor['price']):.2f}"
        )
        return lote_id, melhor["name"], melhor.get("service", ""), float(melhor["price"])

    except Exception as e:
        print(f"[❌] Erro ao cotar frete para lote {trans_id}: {e}")
        return None


def cotar_fretes_planilha(estado, transportadoras_var, barra_progresso_frete):
    print("[🧪 estado id dentro da cotação]:", id(estado))

    df = estado.get("df_planilha_parcial")
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit(
            "aviso", "Aviso", "Nenhuma planilha carregada para cotação de frete."
        )
        return

    # 🔎 Transportadoras selecionadas
    selecionadas = [k for k, var in transportadoras_var.items() if var.isChecked()]
    if not selecionadas:
        comunicador_global.mostrar_mensagem.emit(
            "aviso", "Aviso", "Nenhuma transportadora selecionada."
        )
        return

    print("[🧪 FRETES]", estado.get("dados_temp", {}).get("fretes", {}))
    print("[🧪 STATUS]", estado.get("dados_temp", {}).get("status_fulfillment", {}))
    if "transaction_id" in df.columns:
        print("[🧪 ID transações planilha]", df["transaction_id"].unique())

    # 🔁 (Re)atribui ID Lote antes de cotar
    df = aplicar_lotes(df, estado)
    estado["df_planilha_parcial"] = df
    print("[⚙️] ID Lote atribuído antes da cotação.")

    # Agrupa por lote (apenas lotes válidos, não vazios)
    pedidos_por_lote = {}
    for _, linha in df.iterrows():
        lote = (linha.get("ID Lote") or "").strip()
        if lote:
            pedidos_por_lote.setdefault(lote, []).append(linha.to_dict())

    ids_lotes = list(pedidos_por_lote.items())
    total = len(ids_lotes)
    fretes_aplicados = []

    print(f"[📦] Iniciando cotação de {total} lotes.")
    barra_progresso_frete.setVisible(True)
    barra_progresso_frete.setMaximum(total)
    barra_progresso_frete.setValue(0)

    def processar_proxima(index=0):
        if index >= total:
            barra_progresso_frete.setVisible(False)
            estado["df_planilha_parcial"] = df

            if fretes_aplicados:
                resumo = "📦 Médias de frete por transportadora/serviço:\n\n"
                agrupados = {}
                total_fretes = 0.0

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

        resultado = cotar_para_lote(lote_id, linhas, selecionadas)
        if resultado:
            nome_transportadora, nome_servico, valor_frete = resultado[1:]
            fretes_aplicados.append((nome_transportadora, nome_servico, valor_frete))

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


class VisualizadorPlanilhaDialog(QDialog):
    def __init__(self, df, estado=None, caminho_log=None):
        super().__init__()
        self.setWindowTitle("📋 Visualizador de Planilha")
        self.setMinimumSize(1000, 600)
        self.df = df.copy()
        if "Cupom" not in self.df.columns:
            self.df["Cupom"] = ""
        self.estado = estado  # ✅ suporte ao estado
        self.caminho_log = caminho_log

        layout = QVBoxLayout(self)

        # 🔍 Campo de busca
        linha_busca = QHBoxLayout()
        linha_busca.addWidget(QLabel("🔎 Buscar:"))
        self.campo_busca = QLineEdit()
        linha_busca.addWidget(self.campo_busca)
        layout.addLayout(linha_busca)
        self.campo_busca.textChanged.connect(self.filtrar_tabela)

        # 📋 Tabela
        self.tabela = QTableWidget()
        self.tabela.setColumnCount(len(self.df.columns))
        self.tabela.setRowCount(len(self.df))
        self.tabela.setHorizontalHeaderLabels(self.df.columns.tolist())
        self.tabela.setEditTriggers(QAbstractItemView.DoubleClicked)
        self.tabela.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.tabela.setAlternatingRowColors(True)
        self.tabela.setSortingEnabled(True)

        for i in range(len(self.df)):
            for j, col in enumerate(self.df.columns):
                valor = str(self.df.iloc[i, j])
                item = QTableWidgetItem(valor)
                if col in ["Data", "Data Pedido"]:
                    try:
                        dt = datetime.strptime(valor, "%d/%m/%Y")
                        item.setData(Qt.UserRole, dt)
                    except Exception:
                        pass
                self.tabela.setItem(i, j, item)

        self.tabela.resizeColumnsToContents()
        layout.addWidget(self.tabela)

        # ⌨️ Atalho DELETE para remover linhas com confirmação
        atalho_delete = QShortcut(QKeySequence(Qt.Key_Delete), self.tabela)
        atalho_delete.activated.connect(self.remover_linhas_selecionadas)

        # 🔘 Botões
        linha_botoes = QHBoxLayout()

        btn_remover = QPushButton("🗑️ Remover linha selecionada")
        btn_remover.clicked.connect(self.remover_linhas_selecionadas)
        linha_botoes.addWidget(btn_remover)

        btn_salvar = QPushButton("💾 Salvar alterações")
        btn_salvar.clicked.connect(self.salvar_edicoes)
        linha_botoes.addWidget(btn_salvar)

        layout.addLayout(linha_botoes)

        self.showMaximized()

    def filtrar_tabela(self):
        termo = self.campo_busca.text().lower().strip()
        for row in range(self.tabela.rowCount()):
            mostrar = False
            for col in range(self.tabela.columnCount()):
                item = self.tabela.item(row, col)
                if item and termo in item.text().lower():
                    mostrar = True
                    break
            self.tabela.setRowHidden(row, not mostrar)

    def remover_linhas_selecionadas(self):
        linhas = sorted({index.row() for index in self.tabela.selectedIndexes()}, reverse=True)
        if not linhas:
            return

        resposta = QMessageBox.question(
            self,
            "Confirmar remoção",
            f"Deseja realmente remover {len(linhas)} linha(s) selecionada(s)?",
            QMessageBox.Yes | QMessageBox.No,
        )

        if resposta == QMessageBox.Yes:
            for linha in linhas:
                self.tabela.removeRow(linha)

    def salvar_edicoes(self):
        nova_df = []
        for i in range(self.tabela.rowCount()):
            linha = []
            for j in range(self.tabela.columnCount()):
                item = self.tabela.item(i, j)
                linha.append(item.text() if item else "")
            nova_df.append(linha)

        self.df = pd.DataFrame(nova_df, columns=self.df.columns)

        if self.caminho_log:
            try:
                with open(self.caminho_log, "w", encoding="utf-8") as f:
                    json.dump(self.df.to_dict(orient="records"), f, ensure_ascii=False, indent=2)
                comunicador_global.mostrar_mensagem.emit(
                    "info", "Sucesso", "Alterações salvas no log."
                )
            except Exception as e:
                comunicador_global.mostrar_mensagem.emit(
                    "erro", "Erro", f"Falha ao salvar alterações:\n{e!s}"
                )
        else:
            comunicador_global.mostrar_mensagem.emit(
                "info", "Alterações salvas", "Alterações salvas na planilha em memória."
            )

        if self.estado is not None:
            self.estado["df_planilha_parcial"] = self.df.copy()

        self.accept()


def visualizar_planilha_parcial(estado):
    df = estado.get("df_planilha_parcial")
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit("info", "Aviso", "Nenhuma planilha carregada.")
        return

    dialog = VisualizadorPlanilhaDialog(df)
    if dialog.exec_():
        estado["df_planilha_parcial"] = dialog.df.copy()


def exibir_planilha_parcial(df):
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit("aviso", "Aviso", "Nenhuma planilha carregada.")
        return
    VisualizadorPlanilhaDialog(df).exec_()


def visualizar_logs_existentes():
    """
    Lista todos os arquivos JSON de log no diretório Envios/ e,
    ao selecionar um, carrega o JSON e chama exibir_planilha_parcial.
    """
    pasta_base = os.path.join(os.path.dirname(__file__), "Envios")
    if not os.path.exists(pasta_base):
        comunicador_global.mostrar_mensagem.emit(
            "info", "Sem registros", "Nenhuma pasta de log encontrada."
        )
        return

    logs = []
    for ano in os.listdir(pasta_base):
        pasta_ano = os.path.join(pasta_base, ano)
        if not os.path.isdir(pasta_ano):
            continue
        for arquivo in os.listdir(pasta_ano):
            if arquivo.endswith(".json"):
                logs.append((ano, arquivo))

    if not logs:
        comunicador_global.mostrar_mensagem.emit(
            "info", "Sem registros", "Nenhum arquivo de log encontrado."
        )
        return

    dialog = QDialog()
    dialog.setWindowTitle("Visualizar Registros Existentes")
    dialog.setMinimumSize(900, 500)

    layout = QVBoxLayout(dialog)
    lista = QListWidget()
    layout.addWidget(lista)

    for ano, arq in logs:
        lista.addItem(f"{ano} - {arq}")

    def abrir_log():
        selected_items = lista.selectedItems()
        if not selected_items:
            return
        selecionado = selected_items[0].text()
        ano_sel, nome_arq = selecionado.split(" - ", 1)
        caminho = os.path.join(pasta_base, ano_sel, nome_arq)
        if not caminho or not os.path.exists(caminho):
            return
        with open(caminho, encoding="utf-8") as f:
            dados = json.load(f)
        df = pd.DataFrame(dados)
        VisualizadorPlanilhaDialog(df, caminho_log=caminho).exec_()

    btn = QPushButton("👁 Ver Log Selecionado")
    btn.clicked.connect(abrir_log)
    layout.addWidget(btn)

    dialog.exec_()


# Processamento e exportação da planilha para o Bling


def obter_e_salvar_planilha():
    df = estado.get("df_planilha_parcial")
    if df is None or df.empty:
        comunicador_global.mostrar_mensagem.emit(
            "erro", "Erro", "Nenhuma planilha parcial carregada."
        )
        return

    caminho, _ = QFileDialog.getSaveFileName(
        None, "Salvar Planilha", "", "Planilhas Excel (*.xlsx)"
    )
    if caminho:
        salvar_planilha_final(df, caminho)


def limpar_planilha():
    resposta = QMessageBox.question(
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
            estado["tabela_widget"].setRowCount(0)

        comunicador_global.mostrar_mensagem.emit("info", "Limpo", "Planilha foi limpa.")


def gerar_pdf_resumo_logistica(df, data_envio, bimestre, ano, caminho_planilha):
    # 🔁 Agrupa os produtos por Número pedido (pedido final)
    agrupado = {}
    for grupo in df.groupby("Número pedido"):
        produtos = grupo["Produto"].dropna().tolist()
        produtos = [p.strip() for p in produtos if p.strip()]
        if not produtos:
            continue
        chave = " + ".join(sorted(produtos))
        agrupado.setdefault(chave, 0)
        agrupado[chave] += 1

    # 📊 Contagem total por produto individual
    produtos_totais = Counter()
    for conjunto, qtd in agrupado.items():
        for produto in conjunto.split(" + "):
            produtos_totais[produto] += qtd

    # 🧾 Caminho do PDF
    nome_arquivo = f"{data_envio.strftime('%d%m%Y')}_logos_resumo_logistica_{bimestre}_{ano}.pdf"
    pasta_destino = os.path.dirname(caminho_planilha)
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
        f"Resumo de Produção - {data_envio.strftime('%d/%m/%Y')} - {bimestre}/{ano}",
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
    os.startfile(caminho_pdf)


def salvar_planilha_final(df: pd.DataFrame, output_path: str) -> None:
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
        df_final.sort_values(
            by=["Transportadora", "Conjunto Produtos", "Nome Comprador"], inplace=True
        )
    else:
        df_final.sort_values(by=["Transportadora", "Conjunto Produtos"], inplace=True)

    # Numeração por lote (se houver)
    if "ID Lote" in df_final.columns:
        numero_inicial, ok = QInputDialog.getInt(
            None, "Número Inicial", "Informe o número inicial do pedido:", value=8000, min=1
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
        mapa_lotes = {row["ID Lote"]: numero_inicial + i for i, row in lotes_ordenados.iterrows()}
        df_final["Número pedido"] = df_final["ID Lote"].map(mapa_lotes)
    else:
        df_final["Número pedido"] = ""

    # Converte valores e calcula Total Pedido
    df_final["Valor Total"] = df_final["Valor Total"].astype(str).str.replace(",", ".", regex=False)
    df_final["Valor Total"] = pd.to_numeric(df_final["Valor Total"], errors="coerce")

    if df_final["Número pedido"].notna().any():
        total_por_pedido = (
            df_final.groupby("Número pedido", as_index=False)["Valor Total"]
            .sum()
            .rename(columns={"Valor Total": "Total Pedido"})
        )
        if "Total Pedido" in df_final.columns:
            df_final.drop(columns=["Total Pedido"], inplace=True)
        df_final = pd.merge(df_final, total_por_pedido, on="Número pedido", how="left")
    else:
        df_final["Total Pedido"] = ""

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

    # Formata valores
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
        data_envio = datetime.strptime(data_envio_str, "%d/%m/%Y")

        info = estado.get("ultimo_log", {}) if isinstance(estado, dict) else {}
        periodo = info.get("periodo", info.get("bimestre", 1))
        ano_pdf = info.get("ano", data_envio.year)
        gerar_pdf_resumo_logistica(df_para_pdf, data_envio, periodo, ano_pdf, output_path)
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
    colunas_remover = ["Data Pedido", "Conjunto Produtos", "ID Lote", "indisponivel"]
    df_para_exportar = df_final.drop(columns=colunas_remover, errors="ignore")

    try:
        df_para_exportar.to_excel(output_path, index=False)
        comunicador_global.mostrar_mensagem.emit(
            "info", "Sucesso", f"Planilha exportada para:\n{output_path}"
        )
    except Exception as e:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro ao salvar", f"{e}")


# Interface para edição de SKUs.


def chave_assinatura(nome: str, periodicidade: str) -> str:
    p = (periodicidade or "").strip().lower()
    if p not in ("mensal", "bimestral"):
        p = "bimestral"  # fallback
    return f"{nome.strip()} - {p}"


def abrir_editor_skus(box_nome_input=None):

    estado.setdefault("skus_info", {})
    dialog = QDialog()
    dialog.setWindowTitle("Editor de SKUs")
    dialog.setGeometry(100, 100, 1000, 600)
    layout = QVBoxLayout(dialog)

    tabs = QTabWidget()
    tab_produtos = QWidget()
    tab_assinaturas = QWidget()
    tab_combos = QWidget()

    # 📦 Produtos
    tabela_prod = QTableWidget()
    tabela_prod.setColumnCount(7)
    tabela_prod.setHorizontalHeaderLabels(
        ["Nome", "SKU", "Peso", "Guru IDs", "Shopify IDs", "Preço Fallback", "Indisp."]
    )

    # 📬 Assinaturas
    tabela_assin = QTableWidget()
    tabela_assin.setColumnCount(6)
    tabela_assin.setHorizontalHeaderLabels(
        ["Nome", "Duração", "Periodicidade", "Guru IDs", "Preço Fallback", "Indisp."]
    )

    # 📚 Combos
    tabela_combo = QTableWidget()
    tabela_combo.setColumnCount(6)
    tabela_combo.setHorizontalHeaderLabels(
        ["Nome", "Composto de", "Guru IDs", "Shopify IDs", "Preço Fallback", "Indisp."]
    )

    for tabela in [tabela_prod, tabela_assin, tabela_combo]:
        tabela.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)

    layout_prod = QVBoxLayout(tab_produtos)
    layout_prod.addWidget(tabela_prod)
    layout_assin = QVBoxLayout(tab_assinaturas)
    layout_assin.addWidget(tabela_assin)
    layout_combo = QVBoxLayout(tab_combos)
    layout_combo.addWidget(tabela_combo)

    def _mk_checkbox(checked=False):
        cb = QCheckBox()
        cb.setChecked(bool(checked))
        cb.setStyleSheet("margin-left: 8px;")  # só pra ficar bonitinho
        return cb

    def _get_checkbox(table: QTableWidget, row: int, col: int) -> bool:
        w = table.cellWidget(row, col)
        return bool(w.isChecked()) if isinstance(w, QCheckBox) else False

    # Funções para adicionar nova linha
    def adicionar_produto():
        row = tabela_prod.rowCount()
        tabela_prod.insertRow(row)
        for col in range(6):
            tabela_prod.setItem(row, col, QTableWidgetItem(""))
        # coluna 6 = Indisp. (checkbox)
        tabela_prod.setCellWidget(row, 6, _mk_checkbox(False))

    def adicionar_assinatura():
        row = tabela_assin.rowCount()
        tabela_assin.insertRow(row)
        for col in range(5):  # até Preço Fallback
            tabela_assin.setItem(row, col, QTableWidgetItem(""))
        tabela_assin.setCellWidget(row, 5, _mk_checkbox(False))  # Indisp.

    def adicionar_combo():
        row = tabela_combo.rowCount()
        tabela_combo.insertRow(row)
        for col in range(5):
            tabela_combo.setItem(row, col, QTableWidgetItem(""))
        tabela_combo.setCellWidget(row, 5, _mk_checkbox(False))  # Indisp.

    # 🧹 Funções para remover linha selecionada
    def remover_produto():
        row = tabela_prod.currentRow()
        if row >= 0:
            tabela_prod.removeRow(row)

    def remover_assinatura():
        row = tabela_assin.currentRow()
        if row >= 0:
            tabela_assin.removeRow(row)

    def remover_combo():
        row = tabela_combo.currentRow()
        if row >= 0:
            tabela_combo.removeRow(row)

    # 📦 Botões Produtos
    layout_botoes_prod = QHBoxLayout()
    btn_novo_prod = QPushButton("+ Novo Produto")
    btn_novo_prod.clicked.connect(adicionar_produto)
    btn_remover_prod = QPushButton("🗑️ Remover Selecionado")
    btn_remover_prod.clicked.connect(remover_produto)
    layout_botoes_prod.addWidget(btn_novo_prod)
    layout_botoes_prod.addWidget(btn_remover_prod)
    layout_prod.addLayout(layout_botoes_prod)

    # 📬 Botões Assinaturas
    layout_botoes_assin = QHBoxLayout()
    btn_nova_assin = QPushButton("+ Nova Assinatura")
    btn_nova_assin.clicked.connect(adicionar_assinatura)
    btn_remover_assin = QPushButton("🗑️ Remover Selecionado")
    btn_remover_assin.clicked.connect(remover_assinatura)
    layout_botoes_assin.addWidget(btn_nova_assin)
    layout_botoes_assin.addWidget(btn_remover_assin)
    layout_assin.addLayout(layout_botoes_assin)

    # 📚 Botões Combos
    layout_botoes_combo = QHBoxLayout()
    btn_novo_combo = QPushButton("+ Novo Combo")
    btn_novo_combo.clicked.connect(adicionar_combo)
    btn_remover_combo = QPushButton("🗑️ Remover Selecionado")
    btn_remover_combo.clicked.connect(remover_combo)
    layout_botoes_combo.addWidget(btn_novo_combo)
    layout_botoes_combo.addWidget(btn_remover_combo)
    layout_combo.addLayout(layout_botoes_combo)

    tabs.addTab(tab_produtos, "📦 Produtos")
    tabs.addTab(tab_assinaturas, "📬 Assinaturas")
    tabs.addTab(tab_combos, "📚 Combos")
    layout.addWidget(tabs)

    def carregar_skus():
        if os.path.exists(skus_path):
            with open(skus_path, encoding="utf-8") as f:
                return json.load(f)
        return {}

    def preencher_tabelas(skus_dict):
        tabela_prod.setRowCount(0)
        tabela_assin.setRowCount(0)
        tabela_combo.setRowCount(0)

        for nome, info in skus_dict.items():
            # ASSINATURAS
            if info.get("tipo") == "assinatura":
                row = tabela_assin.rowCount()
                tabela_assin.insertRow(row)

                nome_base = nome.split(" - ")[0]
                periodicidade = info.get("periodicidade") or (
                    nome.split(" - ")[1] if " - " in nome else ""
                )

                tabela_assin.setItem(row, 0, QTableWidgetItem(nome_base))
                tabela_assin.setItem(
                    row,
                    1,
                    QTableWidgetItem(info.get("recorrencia", "") or info.get("recorrencia", "")),
                )
                tabela_assin.setItem(row, 2, QTableWidgetItem(periodicidade))
                tabela_assin.setItem(row, 3, QTableWidgetItem(", ".join(info.get("guru_ids", []))))
                tabela_assin.setItem(row, 4, QTableWidgetItem(str(info.get("preco_fallback", ""))))
                # indisponivel
                tabela_assin.setCellWidget(
                    row, 5, _mk_checkbox(bool(info.get("indisponivel", False)))
                )
            # COMBOS
            elif info.get("composto_de", []):
                row = tabela_combo.rowCount()
                tabela_combo.insertRow(row)
                tabela_combo.setItem(row, 0, QTableWidgetItem(nome))
                tabela_combo.setItem(
                    row, 1, QTableWidgetItem(", ".join(info.get("composto_de", [])))
                )
                tabela_combo.setItem(row, 2, QTableWidgetItem(", ".join(info.get("guru_ids", []))))
                tabela_combo.setItem(
                    row, 3, QTableWidgetItem(", ".join(str(i) for i in info.get("shopify_ids", [])))
                )
                tabela_combo.setItem(row, 4, QTableWidgetItem(str(info.get("preco_fallback", ""))))
                tabela_combo.setCellWidget(
                    row, 5, _mk_checkbox(bool(info.get("indisponivel", False)))
                )
            # PRODUTOS
            else:
                row = tabela_prod.rowCount()
                tabela_prod.insertRow(row)
                tabela_prod.setItem(row, 0, QTableWidgetItem(nome))
                tabela_prod.setItem(row, 1, QTableWidgetItem(info.get("sku", "")))
                tabela_prod.setItem(row, 2, QTableWidgetItem(str(info.get("peso", 0.0))))
                tabela_prod.setItem(row, 3, QTableWidgetItem(", ".join(info.get("guru_ids", []))))
                tabela_prod.setItem(
                    row, 4, QTableWidgetItem(", ".join(str(i) for i in info.get("shopify_ids", [])))
                )
                tabela_prod.setItem(row, 5, QTableWidgetItem(str(info.get("preco_fallback", ""))))
                tabela_prod.setCellWidget(
                    row, 6, _mk_checkbox(bool(info.get("indisponivel", False)))
                )

    def salvar_tabelas():
        skus = {}

        for row in range(tabela_prod.rowCount()):

            def get(col, _row=row):
                item = tabela_prod.item(_row, col)
                return item.text().strip() if item else ""

            nome, sku, peso, guru, shopify, preco = map(get, range(6))

            if not nome:
                continue
            try:
                peso = float(peso)
            except (ValueError, TypeError):
                peso = 0.0
            try:
                preco = float(preco) if preco else None
            except (ValueError, TypeError):
                preco = None
            skus[nome] = {
                "sku": sku,
                "peso": peso,
                "guru_ids": [x.strip() for x in guru.split(",") if x.strip()],
                "shopify_ids": [int(x.strip()) for x in shopify.split(",") if x.strip().isdigit()],
                "tipo": "produto",
                "composto_de": [],
                "indisponivel": _get_checkbox(tabela_prod, row, 6),  # << AQUI
            }
            if preco is not None:
                skus[nome]["preco_fallback"] = preco

        for row in range(tabela_assin.rowCount()):

            def get(col, _row=row):
                item = tabela_assin.item(_row, col)
                return item.text().strip() if item else ""

            nome_base, recorrencia, periodicidade, guru, preco = map(get, range(5))

            if not nome_base:
                continue

            key = chave_assinatura(nome_base, periodicidade)  # como você já faz

            try:
                preco = float(preco) if preco else None
            except (ValueError, TypeError):
                preco = None

            guru_ids = [x.strip() for x in guru.split(",") if x.strip()]

            skus[key] = {
                "tipo": "assinatura",
                "recorrencia": recorrencia,
                "periodicidade": periodicidade,
                "guru_ids": guru_ids,
                "shopify_ids": [],
                "composto_de": [],
                "sku": "",
                "peso": 0.0,
                "indisponivel": _get_checkbox(tabela_assin, row, 5),  # << AQUI
            }
            if preco is not None:
                skus[key]["preco_fallback"] = preco

        for row in range(tabela_combo.rowCount()):

            def get(col, _row=row):
                item = tabela_combo.item(_row, col)
                return item.text().strip() if item else ""

            nome, composto, guru, shopify, preco = map(get, range(5))
            if not nome:
                continue
            try:
                preco = float(preco) if preco else None
            except (ValueError, TypeError):
                preco = None
            skus[nome] = {
                "sku": "",
                "peso": 0.0,
                "tipo": "produto",  # você usa "produto" pra combos, mantive
                "composto_de": [x.strip() for x in composto.split(",") if x.strip()],
                "guru_ids": [x.strip() for x in guru.split(",") if x.strip()],
                "shopify_ids": [int(x.strip()) for x in shopify.split(",") if x.strip().isdigit()],
                "indisponivel": _get_checkbox(tabela_combo, row, 5),  # << AQUI
            }
            if preco is not None:
                skus[nome]["preco_fallback"] = preco

        with open(skus_path, "w", encoding="utf-8") as f:
            json.dump(skus, f, indent=4, ensure_ascii=False)

        estado["skus_info"].clear()
        estado["skus_info"].update(skus)

        if box_nome_input:
            box_nome_input.clear()
            box_nome_input.addItems(sorted(skus.keys()))

        QMessageBox.information(dialog, "Sucesso", "SKUs salvos com sucesso!")

    # Botão salvar
    botoes = QHBoxLayout()
    btn_salvar = QPushButton("💾 Salvar SKUs")
    btn_salvar.clicked.connect(salvar_tabelas)
    botoes.addWidget(btn_salvar)
    layout.addLayout(botoes)

    skus_dict = carregar_skus()
    print(f"[DEBUG] carregando {len(skus_dict)} produtos no editor")
    preencher_tabelas(skus_dict)
    dialog.exec_()


# Montar PDF de auxílio com XMLs


def extrair_nfs_do_zip(caminho_zip, pasta_destino="/tmp/xmls_extraidos"):
    # Limpa a pasta antes de extrair
    if os.path.exists(pasta_destino):
        shutil.rmtree(pasta_destino)
    os.makedirs(pasta_destino)

    with zipfile.ZipFile(caminho_zip, "r") as zip_ref:
        nomes_extraidos = [
            zip_ref.extract(nome, path=pasta_destino)
            for nome in zip_ref.namelist()
            if nome.endswith(".xml")
        ]
    return nomes_extraidos


def ler_dados_nf(caminho_xml):
    try:
        tree = ET.parse(caminho_xml)
        root = tree.getroot()
        ns = {"nfe": "http://www.portalfiscal.inf.br/nfe"}
        infNFe = root.find(".//nfe:infNFe", ns)

        nNF = infNFe.findtext("nfe:ide/nfe:nNF", namespaces=ns)
        xNome = infNFe.findtext("nfe:dest/nfe:xNome", namespaces=ns)
        xNomeTransportadora = (
            infNFe.findtext("nfe:transp/nfe:transporta/nfe:xNome", namespaces=ns)
            or "Sem Transportadora"
        )

        produtos = []
        for det in infNFe.findall("nfe:det", ns):
            xProd = det.findtext("nfe:prod/nfe:xProd", namespaces=ns)
            if xProd:
                produtos.append(xProd.strip())

        return nNF, xNome, xNomeTransportadora, produtos

    except Exception as e:
        print(f"Erro ao processar {caminho_xml}: {e}")
        return None, None, None, []


def agrupar_por_transportadora(lista_xml):
    # Estrutura: {Transportadora: {nNF: {"xNome": ..., "produtos": [...]}}}
    agrupado = defaultdict(lambda: defaultdict(lambda: {"xNome": "", "produtos": []}))

    for caminho in lista_xml:
        nNF, xNome, transportadora, produtos = ler_dados_nf(caminho)
        if not nNF:
            continue

        agrupado[transportadora][nNF]["xNome"] = xNome
        agrupado[transportadora][nNF]["produtos"].extend(produtos)

    return agrupado


def agrupar_por_nf(lista_xml):
    agrupado = defaultdict(lambda: {"xNome": "", "produtos": []})
    for caminho in lista_xml:
        # ANTES: nNF, xNome, produtos = ler_dados_nf(caminho_xml)
        nNF, xNome, _transportadora, produtos = ler_dados_nf(caminho)  # <- corrige aqui
        if not nNF:
            continue
        agrupado[nNF]["xNome"] = xNome
        agrupado[nNF]["produtos"].extend(produtos)
    return agrupado


def gerar_pdfs_por_transportadora(
    dados_por_transportadora, pasta_destino="/tmp/pdfs_por_transportadora"
):
    os.makedirs(pasta_destino, exist_ok=True)
    caminhos = []

    for transportadora, notas in dados_por_transportadora.items():
        # Sanitizar nome para nome de arquivo
        nome_arquivo = f"{transportadora.replace(' ', '_').replace('/', '-')}.pdf"
        caminho_pdf = os.path.join(pasta_destino, nome_arquivo)

        c = canvas.Canvas(caminho_pdf, pagesize=A4)
        altura = A4
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

    return caminhos  # lista com caminhos dos PDFs gerados


def gerar_pdf_resumo_nf(dados_agrupados, caminho_pdf="/tmp/resumo_nfes.pdf"):

    c = canvas.Canvas(caminho_pdf, pagesize=A4)
    altura = A4

    margem_sup = 10 * mm
    margem_inf = 10 * mm
    y = altura - margem_sup

    for nNF, dados in sorted(dados_agrupados.items()):
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

        y -= 5 * mm  # espaço reduzido entre blocos de NF

    c.save()
    return caminho_pdf


def processar_xmls_nfe(estado):
    try:
        caminho_zip, _ = QFileDialog.getOpenFileName(
            None, "Selecionar Arquivo ZIP", "", "ZIP Files (*.zip)"
        )
        if not caminho_zip:
            return

        lista_xmls = extrair_nfs_do_zip(caminho_zip)
        dados_agrupados = agrupar_por_transportadora(lista_xmls)
        estado["dados_agrupados_nfe"] = dados_agrupados

        pasta_pdf = QFileDialog.getExistingDirectory(None, "Selecionar pasta para salvar os PDFs")
        if not pasta_pdf:
            return

        pdfs_gerados = gerar_pdfs_por_transportadora(dados_agrupados, pasta_pdf)

        if not pdfs_gerados:
            QMessageBox.information(None, "Aviso", "Nenhum PDF foi gerado.")
            return

        # Tenta abrir a pasta de destino
        try:
            if platform.system() == "Darwin":
                subprocess.run(["open", pasta_pdf], check=False)
            elif platform.system() == "Windows":
                os.startfile(pasta_pdf)
            else:
                subprocess.run(["xdg-open", pasta_pdf], check=False)
        except Exception as e:
            QMessageBox.warning(
                None, "Aviso", f"PDFs gerados, mas não foi possível abrir a pasta.\nErro: {e}"
            )

    except Exception as e:
        QMessageBox.critical(None, "Erro ao processar XMLs", str(e))


# Design da interface


def estilizar_grupo(grupo: QGroupBox, cor_fundo="#f9f9f9", cor_borda="#ccc"):
    grupo.setStyleSheet(
        f"""
        QGroupBox {{
            background-color: {cor_fundo};
            border: 1px solid {cor_borda};
            border-radius: 6px;
            margin-top: 10px;
            padding: 10px;
        }}
        QGroupBox::title {{
            subcontrol-origin: margin;
            subcontrol-position: top left;
            padding: 0 10px;
            font-weight: bold;
            background-color: transparent;
        }}
    """
    )


def criar_grupo_guru(estado, skus_info, transportadoras_var):

    group = QGroupBox("Digital Manager Guru")
    group.setObjectName("grupo_guru")
    group.setAttribute(Qt.WA_StyledBackground, True)

    outer_layout = QVBoxLayout(group)
    inner_widget = QWidget()
    layout = QVBoxLayout(inner_widget)
    layout.setContentsMargins(0, 0, 0, 0)

    # 🗓️ Filtros
    linha_filtros = QHBoxLayout()
    ano_spin = QSpinBox()
    ano_spin.setRange(2020, 2035)
    ano_spin.setValue(datetime.today().year)
    linha_filtros.addWidget(QLabel("Ano:"))
    linha_filtros.addWidget(ano_spin)

    combo_mes = QComboBox()
    combo_mes.addItems([str(i) for i in range(1, 13)])
    combo_mes.setCurrentIndex(datetime.today().month - 1)
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

    btn_importar.clicked.connect(importar_planilha_pedidos_guru)

    # 🔁 Ações de visualização que permanecem aqui
    linha_acoes_guru = QHBoxLayout()
    layout.addLayout(linha_acoes_guru)

    # ⚙️ Regras & mapeamentos (mantém aqui)
    linha_config = QHBoxLayout()

    btn_rules = QPushButton("⚙️ Gerenciar Regras")
    btn_rules.clicked.connect(lambda: abrir_mapeador_regras(estado, skus_info))
    linha_config.addWidget(btn_rules)

    def recarregar_regras():
        try:
            config_path = os.path.join(os.path.dirname(__file__), "config_ofertas.json")
            regras = []
            if os.path.exists(config_path):
                with open(config_path, encoding="utf-8") as f:
                    cfg = json.load(f)
                    regras = cfg.get("rules") or cfg.get("regras") or []
            if isinstance(regras, list):
                estado["rules"] = regras
                comunicador_global.mostrar_mensagem.emit("info", "Regras", "Regras recarregadas.")
            else:
                comunicador_global.mostrar_mensagem.emit(
                    "aviso", "Regras", "Arquivo sem lista de regras."
                )
        except Exception as e:
            comunicador_global.mostrar_mensagem.emit("erro", "Regras", f"Falha ao recarregar: {e}")

    btn_reload_rules = QPushButton("↺ Recarregar Regras")
    btn_reload_rules.clicked.connect(recarregar_regras)
    linha_config.addWidget(btn_reload_rules)

    btn_editar = QPushButton("✏️ Editar SKUs")
    btn_editar.clicked.connect(lambda: abrir_editor_skus(None))
    linha_config.addWidget(btn_editar)

    # 🔗 Mapear produtos do Guru (fica aqui mesmo)
    btn_mapear_guru = QPushButton("🔗 Mapear produtos do Guru")
    btn_mapear_guru.clicked.connect(
        lambda: (
            abrir_dialogo_mapeamento_guru(
                skus_info, buscar_todos_produtos_guru(), skus_path  # se já existir no seu escopo
            )
        )
    )
    linha_config.addWidget(btn_mapear_guru)

    layout.addLayout(linha_config)

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

    btn_buscar_produtos.clicked.connect(
        lambda: iniciar_busca_produtos(box_nome_input, transportadoras_var, skus_info, estado)
    )

    outer_layout.addWidget(inner_widget)
    return group


def criar_grupo_shopify(estado, skus_info):
    group = QGroupBox("🛒 Shopify")
    group.setObjectName("grupo_shopify")
    group.setAttribute(Qt.WA_StyledBackground, True)

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
    combo_produto.addItems(
        sorted([n for n, i in skus_info.items() if not i.get("indisponivel", False)])
    )
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
    btn_mapear_shopify.clicked.connect(lambda: mapear_skus_com_produtos_shopify(skus_info))
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
    btn_buscar.clicked.connect(lambda: executar_fluxo_loja(estado))
    btn_fulfill.clicked.connect(
        lambda: (
            marcar_itens_como_fulfilled_na_shopify(estado.get("df_planilha_exportada"))
            if estado.get("df_planilha_exportada") is not None
            and not estado["df_planilha_exportada"].empty
            else comunicador_global.mostrar_mensagem.emit(
                "erro", "Erro", "Você deve exportar a planilha antes."
            )
        )
    )

    outer_layout.addWidget(inner_widget)
    return group


def criar_grupo_fretes(estado, transportadoras_var):
    group = QGroupBox("🚚 Cotação de Fretes")
    group.setObjectName("grupo_fretes")
    group.setAttribute(Qt.WA_StyledBackground, True)

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
    btn_cotar.clicked.connect(
        lambda: cotar_fretes_planilha(estado, transportadoras_var, barra_progresso)
    )
    layout.addWidget(btn_cotar)

    outer_layout.addWidget(inner_widget)
    return group


def criar_grupo_exportacao(estado):
    group = QGroupBox("📋 Controle e Registro")
    group.setObjectName("grupo_exportacao")
    group.setAttribute(Qt.WA_StyledBackground, True)

    outer_layout = QVBoxLayout(group)

    inner_widget = QWidget()
    layout = QVBoxLayout(inner_widget)
    layout.setContentsMargins(0, 0, 0, 0)

    # - Visualização -
    linha_visualizacao = QHBoxLayout()

    btn_ver_planilha = QPushButton("✏️ Editar Planilha Parcial")
    btn_ver_planilha.clicked.connect(lambda: visualizar_planilha_parcial(estado))
    linha_visualizacao.addWidget(btn_ver_planilha)

    btn_filtrar_enviados = QPushButton("🧲 Filtrar enviados")
    btn_filtrar_enviados.clicked.connect(filtrar_linhas_ja_enviadas)
    linha_visualizacao.addWidget(btn_filtrar_enviados)

    layout.addLayout(linha_visualizacao)

    # - Registro e complementos -
    linha_registros = QHBoxLayout()

    btn_registrar = QPushButton("📝 Registrar Envios")
    btn_registrar.clicked.connect(
        lambda: (
            registrar_envios_por_mes_ano()
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
    btn_importar_envios.clicked.connect(importar_envios_realizados_planilha)
    linha_registros.addWidget(btn_importar_envios)

    btn_adicionar_brindes = QPushButton("📄 Adicionar Brindes do Comercial")
    btn_adicionar_brindes.clicked.connect(
        lambda: selecionar_planilha_comercial(estado.get("skus_info", {}))
    )
    linha_registros.addWidget(btn_adicionar_brindes)

    layout.addLayout(linha_registros)

    # - Exportação e limpeza -
    linha_export = QHBoxLayout()

    btn_obter_planilha = QPushButton("💾 Exportar Planilha")
    btn_obter_planilha.clicked.connect(lambda: obter_e_salvar_planilha())
    linha_export.addWidget(btn_obter_planilha)

    btn_zip = QPushButton("📁 Selecionar ZIP de NF-es")
    btn_zip.clicked.connect(lambda: processar_xmls_nfe(estado))
    linha_export.addWidget(btn_zip)

    btn_limpar_planilha = QPushButton("🗑️ Limpar Planilha")
    btn_limpar_planilha.clicked.connect(limpar_planilha)
    linha_export.addWidget(btn_limpar_planilha)

    layout.addLayout(linha_export)

    outer_layout.addWidget(inner_widget)
    return group


def criar_tab_config(estado, skus_info):
    tab = QWidget()
    layout = QVBoxLayout(tab)

    grupo = QGroupBox("⚙️ Configurações")
    layout_config = QVBoxLayout(grupo)

    # 🔗 Botões de mapeamento
    linha_mapeamento = QHBoxLayout()

    btn_editar = QPushButton("✏️ Editar SKUs")
    btn_editar.clicked.connect(lambda: abrir_editor_skus(None))
    linha_mapeamento.addWidget(btn_editar)

    btn_mapear_shopify = QPushButton("🔗 Mapear produtos da loja")
    btn_mapear_shopify.clicked.connect(lambda: mapear_skus_com_produtos_shopify(skus_info))
    linha_mapeamento.addWidget(btn_mapear_shopify)

    btn_mapear_guru = QPushButton("🔗 Mapear produtos do Guru")
    btn_mapear_guru.clicked.connect(
        lambda: (abrir_dialogo_mapeamento_guru(skus_info, buscar_todos_produtos_guru(), skus_path))
    )
    linha_mapeamento.addWidget(btn_mapear_guru)

    layout_config.addLayout(linha_mapeamento)

    btn_regras = QPushButton("⚖️ Gerenciar Regras de Ofertas")
    btn_regras.clicked.connect(lambda: abrir_mapeador_regras(estado, skus_info))
    layout_config.addWidget(btn_regras)

    # As regras agora vivem no config_ofertas.json e são editadas/salvas pelo próprio diálogo de regras.

    layout.addWidget(grupo)
    return tab


def abrir_interface(estado, skus_info):

    for info in skus_info.values():
        info.setdefault("indisponivel", False)
    estado["skus_info"] = skus_info

    app = QApplication.instance()
    if app is None:
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
    janela.setWindowTitle("Editora Logos: Guru -> Planilha Bling")
    largura = 800
    altura = 700
    tela = QDesktopWidget().availableGeometry().center()
    janela.setGeometry(0, 0, largura, altura)
    janela.move(tela.x() - largura // 2, tela.y() - altura // 2)
    estado["janela_principal"] = janela

    transportadoras_var = {}
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
    layout_principal.addWidget(criar_grupo_exportacao(estado))

    janela.show()
    app.exec_()


if __name__ == "__main__":
    # importante: agora passamos SEMPRE pelo safe_cli
    raise SystemExit(main())

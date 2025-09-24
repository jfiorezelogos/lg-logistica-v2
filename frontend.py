# frontend.py
# --- Iniciar busca de assinaturas (frontend/UI) ---
from __future__ import annotations

import json
import logging
import os
import re
import threading
import traceback
import uuid
from collections import Counter, OrderedDict
from collections.abc import Iterable, Mapping, MutableMapping, Sequence
from contextlib import suppress
from logging import Logger
from threading import Event
from typing import Any, Literal, Protocol, cast

import pandas as pd
from PyQt5.QtCore import QCoreApplication, QDate, QEvent, QObject, Qt, QThread, QTimer, pyqtSignal, pyqtSlot
from PyQt5.QtGui import QGuiApplication
from PyQt5.QtWidgets import (
    QAbstractItemView,
    QApplication,
    QButtonGroup,
    QCheckBox,
    QComboBox,
    QDateEdit,
    QDialog,
    QDialogButtonBox,
    QGroupBox,
    QHBoxLayout,
    QHeaderView,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QMessageBox,
    QProgressBar,
    QPushButton,
    QRadioButton,
    QTableWidget,
    QTableWidgetItem,
    QTabWidget,
    QVBoxLayout,
    QWidget,
)
from unidecode import unidecode

# Consome utilitários/serviços do backend
# Consome serviços/utilitários do backend
# Consome serviços/utilitários do backend
# usa funções do backend
# Importa do backend os dados/paths e a função de busca
from backend import (  # eh_indisponivel deve estar no backend
    _carregar_regras,
    bounds_do_periodo,
    buscar_ofertas_do_produto,
    buscar_todos_produtos_guru,
    buscar_transacoes_assinaturas,
    buscar_transacoes_produtos,
    carregar_regras,
    eh_indisponivel,
    gerar_uuid,
    logger,  # logger já configurado no backend
    salvar_regras,
    skus_path,
)
from common.logging_setup import get_correlation_id, set_correlation_id, setup_logging

from . import (
    WorkerController,  # mesma observação
    comunicador_global,  # se estiver no mesmo arquivo, pode remover este import
)


# Sinais/slots (UI)
class Comunicador(QObject):
    mostrar_mensagem = pyqtSignal(str, str, str)
    atualizar_progresso = pyqtSignal(str, int, int)


comunicador_global = Comunicador()


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


# conecta o sinal global ao slot padrão de UI
comunicador_global.mostrar_mensagem.connect(slot_mostrar_mensagem)


def run_gui() -> int:
    # ativa JSON no console e também loga no arquivo existente
    # OBS: espera-se que caminho_base(), estado e skus_info existam no escopo do main/backend
    from backend import caminho_base, estado, skus_info  # import local para evitar ciclos

    setup_logging(
        level=logging.INFO,
        json_console=True,
        file_path=os.path.join(caminho_base(), "sistema.log"),
    )
    set_correlation_id()  # gera um id para essa execução

    # função de UI original
    # abrir_interface vem do seu main atual; quando separar a UI toda, importe-a aqui
    from main import abrir_interface  # manter enquanto a UI ainda está no main

    abrir_interface(estado, skus_info)
    return 0


# Variáveis de UI declaradas no trecho (mantidas no front)
janela_progresso = None
texto_label = None
barra_progresso = None


def mapear_skus_com_produtos_guru(skus_info: MutableMapping[str, Any]) -> None:
    produtos_guru = buscar_todos_produtos_guru()
    if not produtos_guru:
        QMessageBox.warning(None, "Erro", "Nenhum produto retornado do Guru.")
        return
    abrir_dialogo_mapeamento_guru(skus_info, produtos_guru, skus_path)


def abrir_dialogo_mapeamento_guru(
    skus_info: Mapping[str, MutableMapping[str, Any]],  # ← antes era MutableMapping[…]
    produtos_guru: Sequence[Mapping[str, Any]] | None,
    skus_path: str,
) -> None:
    class DialogoMapeamento(QDialog):
        def __init__(self) -> None:
            super().__init__()
            self.setWindowTitle("Mapear Produtos do Guru para Produtos Internos")
            self.setMinimumSize(800, 500)
            self.main_layout = QVBoxLayout(self)

            # mantém referências
            self.skus_info: MutableMapping[str, Any] = cast(MutableMapping[str, Any], skus_info)
            self.produtos: list[dict[str, Any]] = [dict(p) for p in (produtos_guru or [])]
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

            # Tipo: assinatura ou produto
            linha_tipo: QHBoxLayout = QHBoxLayout()
            self.radio_produto = QRadioButton("Produto")
            self.radio_assinatura = QRadioButton("Assinatura")
            self.radio_produto.setChecked(True)
            self.grupo_tipo = QButtonGroup()
            self.grupo_tipo.addButton(self.radio_produto)
            self.grupo_tipo.addButton(self.radio_assinatura)
            linha_tipo.addWidget(QLabel("Tipo:"))
            linha_tipo.addWidget(self.radio_produto)
            linha_tipo.addWidget(self.radio_assinatura)
            self.main_layout.addLayout(linha_tipo)

            # Assinatura: duração + periodicidade
            self.widget_assinatura = QWidget()
            linha_assin: QHBoxLayout = QHBoxLayout(self.widget_assinatura)
            self.combo_duracao = QComboBox()
            self.combo_duracao.addItems(["mensal", "bimestral", "anual", "bianual", "trianual"])
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

        # ----- helpers -----
        def _on_tipo_changed(self) -> None:
            self.widget_assinatura.setVisible(self.radio_assinatura.isChecked())
            self._recarregar_combo_interno()

        def _nomes_internos_para_tipo(self) -> list[str]:
            if self.radio_assinatura.isChecked():
                return sorted(
                    [
                        n
                        for n, info in self.skus_info.items()
                        if cast(Mapping[str, Any], info).get("tipo") == "assinatura"
                    ]
                )
            return sorted(
                [n for n, info in self.skus_info.items() if cast(Mapping[str, Any], info).get("tipo") != "assinatura"]
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
            for p in self.produtos:
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
                item.setData(Qt.UserRole, product_id)  # ID técnico salvo
                item.setData(Qt.UserRole + 1, market_id)  # informativo
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

            novos_ids: list[str] = [str(it.data(Qt.UserRole) or "").strip() for it in itens]
            novos_ids = [gid for gid in novos_ids if gid]

            is_assinatura = self.radio_assinatura.isChecked()
            if is_assinatura:
                duracao = self.combo_duracao.currentText().strip().lower()
                periodicidade = self.combo_periodicidade.currentText().strip().lower()
                if not periodicidade:
                    QMessageBox.warning(self, "Aviso", "Selecione a periodicidade da assinatura.")
                    return
                nome_base = re.sub(r"\s*\((mensal|bimestral)\)\s*$", "", nome_base_raw, flags=re.IGNORECASE).strip()
                dest_key = f"{nome_base} ({periodicidade})"
            else:
                duracao = None
                periodicidade = None
                dest_key = nome_base_raw

            # migração legado (sem sufixo -> com sufixo) somente se assinatura
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
                entrada["recorrencia"] = duracao
                entrada["periodicidade"] = periodicidade
                entrada.setdefault("sku", "")
                entrada.setdefault("peso", 0.0)
                entrada.setdefault("composto_de", [])
            else:
                entrada["tipo"] = "produto"
                entrada.pop("recorrencia", None)
                entrada.pop("periodicidade", None)

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

        # adicionar_brindes → múltiplos brindes (qualquer item não-assinatura)
        self.widget_brindes = QWidget()
        layout_br: QVBoxLayout = QVBoxLayout(self.widget_brindes)
        layout_br.setContentsMargins(0, 0, 0, 0)
        self.lista_brindes = QListWidget()
        self.lista_brindes.setSelectionMode(QAbstractItemView.MultiSelection)
        brindes = [n for n, info in self.skus_info.items() if cast(Mapping[str, Any], info).get("tipo") != "assinatura"]
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
                    self.combo_oferta.setItemData(idx_of, nome_existente or "", Qt.UserRole + 1)

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

        ofertas = buscar_ofertas_do_produto(prod_id) or []
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

        # ===== Construção do objeto da regra =====
        rid = self.regra.get("id")
        if not rid:
            try:
                rid = gerar_uuid()
            except NameError:

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

    # ---------- UI refresh ----------
    def _refresh_tables(self) -> None:
        # reconstruir índices caso o estado tenha sido atualizado externamente
        self._build_indices()

        # zera as tabelas e mapas
        self.tbl_cupons.setRowCount(0)
        self.tbl_ofertas.setRowCount(0)
        self._map_cupons = []
        self._map_ofertas = []

        for i, r in enumerate(self.estado["rules"]):
            a = r.get("action") or {}
            if r.get("applies_to") == "cupom":
                # colunas: Cupom | Tipo de ação | Box/Brindes | Plano
                cupom = ((r.get("cupom") or {}).get("nome") or "").strip() or "—"
                tipo = self._tipo_acao(a) or "—"
                box = self._pegar_box(a)
                if tipo == "adicionar_brindes":
                    brindes = self._coletar_brindes(a)
                    box_ou_brindes = " | ".join(f"{b['qtd']}x {b['nome']}" for b in brindes) or "—"
                else:
                    box_ou_brindes = box or "—"
                plano = self._format_assinaturas(r) or "—"

                row = self.tbl_cupons.rowCount()
                self.tbl_cupons.insertRow(row)
                self.tbl_cupons.setItem(row, 0, QTableWidgetItem(cupom))
                self.tbl_cupons.setItem(row, 1, QTableWidgetItem(tipo))
                self.tbl_cupons.setItem(row, 2, QTableWidgetItem(box_ou_brindes))
                self.tbl_cupons.setItem(row, 3, QTableWidgetItem(plano))
                self._map_cupons.append(i)

            else:  # oferta
                # colunas: Nome da oferta | Brinde
                of = r.get("oferta") or {}
                nome = (of.get("nome") or self._label_oferta(of.get("oferta_id")) or "—").strip()
                brinde = ""
                if self._tipo_acao(a) == "adicionar_brindes":
                    brindes = self._coletar_brindes(a)
                    brinde = " | ".join(f"{b['qtd']}x {b['nome']}" for b in brindes)
                brinde = brinde or "—"

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
            self.estado["rules"].append(dlg.get_regra())
            self._refresh_tables()

    def _edit(self) -> None:
        idx = self._selected_index()
        if idx is None:
            return
        regra = self.estado["rules"][idx]
        dlg = RuleEditorDialog(self, self.skus_info, regra=regra, produtos_guru=self.estado.get("produtos_guru"))
        if dlg.exec_() == QDialog.Accepted:
            self.estado["rules"][idx] = dlg.get_regra()
            self._refresh_tables()
            self._reselect(idx)

    def _dup(self) -> None:
        idx = self._selected_index()
        if idx is None:
            return
        r = json.loads(json.dumps(self.estado["rules"][idx]))  # deep copy
        r["id"] = gerar_uuid()
        self.estado["rules"].insert(idx + 1, r)
        self._refresh_tables()
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
            self._refresh_tables()

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
            salvar_regras(self.config_path, self.estado["rules"])
            QMessageBox.information(self, "Salvo", "Regras salvas em config_ofertas.json.")
        except Exception as e:
            QMessageBox.critical(self, "Erro", f"Falha ao salvar: {e}")

    # ---------- movimento preservando o agrupamento ----------
    def _move_relative_in_group(self, idx_global: int, delta: int) -> None:
        """Move a regra idx_global para cima/baixo, mas apenas trocando com vizinhos do MESMO grupo
        (applies_to)."""
        if not -1 <= delta <= 1 or delta == 0:
            return
        rules = self.estado["rules"]
        if not 0 <= idx_global < len(rules):
            return
        group = rules[idx_global].get("applies_to") or "oferta"
        j = idx_global + delta
        while 0 <= j < len(rules) and (rules[j].get("applies_to") or "oferta") != group:
            j += delta
        if 0 <= j < len(rules):
            rules[idx_global], rules[j] = rules[j], rules[idx_global]
            self._refresh_tables()
            self._reselect(j)

    def _reselect(self, idx_global: int) -> None:
        """Após refresh, reposiciona a seleção na aba/tabela correspondente a idx_global."""
        r = self.estado["rules"][idx_global]
        if r.get("applies_to") == "cupom":
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


class GerenciadorProgresso(QDialog):
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
            self.setWindowTitle(titulo)
            self.setFixedSize(500, 160)
            self.setAttribute(Qt.WA_DeleteOnClose, True)

            layout: QVBoxLayout = QVBoxLayout(self)

            self.label_status: QLabel = QLabel("Iniciando...")
            self.label_status.setAlignment(Qt.AlignCenter)
            layout.addWidget(self.label_status)

            self.barra: QProgressBar = QProgressBar()
            if not self.com_percentual:
                self.barra.setRange(0, 0)
            layout.addWidget(self.barra)

            self.botao_cancelar: QPushButton = QPushButton("Cancelar")
            self.botao_cancelar.clicked.connect(self.cancelar)
            layout.addWidget(self.botao_cancelar)

            self.atualizar_signal.connect(self._atualizar_seguro)

            self.show()
            self.raise_()
            self.activateWindow()
            self.showNormal()

            screen = QGuiApplication.primaryScreen().availableGeometry()
            x = screen.center().x() - self.width() // 2
            y = screen.center().y() - self.height() // 2
            self.move(x, y)

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
                if self.isVisible():
                    self._log_info("[🧼] Ocultando janela de progresso...")
                    self.hide()
                self._log_info("[✅] Fechando janela de progresso...")
                self.close()
            except Exception as e:
                self._log_exception(f"[❌] Erro ao fechar janela: {e}")

        app = cast(QCoreApplication, QCoreApplication.instance())
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


def iniciar_progresso(
    titulo: str = "Progresso",
    com_percentual: bool = True,
    estado_global: MutableMapping[str, Any] | None = None,
    logger_obj: Logger | None = None,
) -> GerenciadorProgresso:
    if QApplication.instance() is None:
        raise RuntimeError("QApplication ainda não foi iniciado.")

    gerenciador = GerenciadorProgresso(
        titulo=titulo,
        com_percentual=com_percentual,
        estado_global=estado_global,
        logger_obj=logger_obj or logger,
    )
    QApplication.processEvents()
    return gerenciador


class HasIsSet(Protocol):
    def is_set(self) -> bool: ...


class CanceladorLike(Protocol):
    def set(self) -> Any: ...


class _CancelamentoFilter(QObject):
    def __init__(self, cancelador: CanceladorLike, parent: QObject) -> None:
        super().__init__(parent)
        self._cancelador = cancelador

    def eventFilter(self, _obj: QObject, event: QEvent) -> bool:
        if event.type() == QEvent.Close:
            if hasattr(self._cancelador, "set"):
                self._cancelador.set()
            return False  # não bloqueia o fechamento
        return False


def configurar_cancelamento_em_janela(janela: QObject, cancelador: CanceladorLike) -> None:
    filtro = _CancelamentoFilter(cancelador, janela)
    janela.installEventFilter(filtro)


def exibir_resumo_final(
    linhas: Sequence[Mapping[str, Any]] | None,
    contagem: Mapping[str, Any] | None,
    estado: Mapping[str, Any] | None,
    modo: str = "assinaturas",
) -> None:
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
        from collections import Counter as _Ctr  # evitar conflito de nome

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

    try:
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
            msg: list[str] = [f"📦 Linhas adicionadas: {total_linhas}"]
            if produtos_ctr:
                msg.append("\n🧾 Produtos adicionados:")
                for nome, qtd in produtos_ctr.most_common():
                    msg.append(f"  - {nome}: {qtd}")
            else:
                msg.append("\n🧾 Produtos adicionados: 0")
            comunicador_global.mostrar_mensagem.emit("info", "Resumo da Exportação (Produtos)", "\n".join(msg))
            return

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

        comunicador_global.mostrar_mensagem.emit("info", "Resumo da Exportação", resumo)

    except Exception as e:
        comunicador_global.mostrar_mensagem.emit("erro", "Erro ao exibir resumo", str(e))


class WorkerController(QObject):
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

        # ✅ atributo para mypy e runtime
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

            configurar_cancelamento_em_janela(gerenciador, self.estado["cancelador_global"])
            print("[✅ iniciar_worker] Cancelamento configurado.")

            self.estado["worker_thread"] = WorkerThread(self.dados, self.estado, self.skus_info, gerenciador)
            worker: WorkerThread = cast(WorkerThread, self.estado["worker_thread"])

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

            # (opcional) failsafe para fechar a UI após X ms
            if self._timer is None:
                self._timer = QTimer(self)
                self._timer.setSingleShot(True)
                self._timer.timeout.connect(lambda: with_suppress_close(gerenciador))
                # self._timer.start(30_000)  # habilite se quiser time-out

            def ao_finalizar_worker(linhas: list[Any], contagem: dict[str, Any]) -> None:
                try:
                    exibir_resumo_final(
                        linhas,
                        contagem,
                        self.estado,
                        modo=(cast(str, self.dados.get("modo") or "")).lower(),
                    )
                finally:
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


# helper opcional para usar no timeout
def with_suppress_close(gerenciador: GerenciadorProgresso) -> None:
    with suppress(Exception):
        gerenciador.fechar()


class WorkerThread(QThread):
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

        # Mantém Qt.QueuedConnection
        self.progresso.connect(self.gerenciador.atualizar, type=Qt.QueuedConnection)  # type: ignore[call-arg]
        self.fechar_ui.connect(self.gerenciador.fechar, type=Qt.QueuedConnection)  # type: ignore[call-arg]

        self._parent_correlation_id = get_correlation_id()

    def run(self) -> None:
        set_correlation_id(self._parent_correlation_id)

        novas_linhas: list[Any] = []
        contagem: dict[str, Any] = {}

        try:
            logger.info("worker_started", extra={"modo": self.dados.get("modo")})

            cancelador: Event | None = cast(Event | None, self.estado.get("cancelador_global"))
            if hasattr(cancelador, "is_set") and cancelador.is_set():
                logger.warning("worker_cancelled_early")
                return

            modo = (cast(str, self.dados.get("modo") or "assinaturas")).strip().lower()

            # buscas (backend)
            if modo == "assinaturas":
                self.progresso.emit("🔄 Buscando transações de assinaturas...", 0, 0)
                transacoes, _, dados_final_map = buscar_transacoes_assinaturas(
                    cast(dict[str, Any], self.dados),
                    atualizar=self.progresso.emit,
                    cancelador=cast(Event, self.estado["cancelador_global"]),
                    estado=cast(dict[str, Any], self.estado),
                )
            elif modo == "produtos":
                self.progresso.emit("🔄 Buscando transações de produtos...", 0, 0)
                transacoes, _, dados_final_map = buscar_transacoes_produtos(
                    cast(dict[str, Any], self.dados),
                    atualizar=self.progresso.emit,
                    cancelador=cast(Event, self.estado["cancelador_global"]),
                    estado=cast(dict[str, Any], self.estado),
                )
            else:
                raise ValueError(f"Modo de busca desconhecido: {modo}")

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

            novas_linhas, contagem_map = processar_planilha(  # type: ignore[name-defined]
                transacoes=transacoes,
                dados=dados_final,
                atualizar_etapa=self.progresso.emit,
                skus_info=self.skus_info,
                cancelador=cast(Event, self.estado["cancelador_global"]),
                estado=cast(dict[str, Any], self.estado),
            )

            if not isinstance(contagem_map, Mapping):
                raise ValueError("Retorno inválido de processar_planilha (esperado Mapping).")
            contagem = dict(contagem_map)

            if cast(Event, self.estado["cancelador_global"]).is_set():
                logger.warning("worker_cancelled_after_process")
                return

            self.progresso.emit("✅ Finalizando...", 100, 100)

            if not isinstance(novas_linhas, list) or not isinstance(contagem, dict):
                raise ValueError("Retorno inválido de processar_planilha.")

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


def iniciar_busca_produtos(
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

        # Converte para string ISO "YYYY-MM-DD"
        data_ini_s = data_ini_py.isoformat()
        data_fim_s = data_fim_py.isoformat()

        executar_busca_produtos(
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


def executar_busca_produtos(
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

    print("[🚀 executar_busca_produtos] Enviando para WorkerController...")

    try:
        controller = WorkerController(dados, estado, skus_info)  # tipos permanecem aceitos
        estado["worker_controller"] = controller
        controller.iniciar_worker_signal.emit()
    except Exception as e:
        print("[❌ ERRO EM iniciar_worker via sinal]:", e)
        print(traceback.format_exc())
        comunicador_global.mostrar_mensagem.emit("erro", "Erro", f"Ocorreu um erro ao iniciar a exportação:\n{e!s}")


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
    dt_ini, dt_end, periodo = bounds_do_periodo(int(ano), int(mes), periodicidade)
    box_nome: str = (box_nome_input.currentText() or "").strip()

    # bloqueia box indisponivel
    if box_nome and eh_indisponivel(box_nome):
        comunicador_global.mostrar_mensagem.emit(
            "erro",
            "Box indisponivel",
            f"O box selecionado (“{box_nome}”) está marcado como indisponivel no SKUs.",
        )
        return

    # carrega regras ativas
    regras: list[dict[str, Any]] = _carregar_regras(estado)

    # monta o payload de execução (o WorkerThread usa isso direto)
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

    # guarda contexto p/ outras partes da UI
    estado["contexto_busca_assinaturas"] = dados
    estado["skus_info"] = cast(Mapping[str, Mapping[str, Any]], skus_info)

    # ---- dispara em QThread via WorkerController ----
    if not isinstance(estado.get("cancelador_global"), threading.Event):
        estado["cancelador_global"] = threading.Event()
    estado["cancelador_global"].clear()

    wt = estado.get("worker_thread")
    if wt is not None and wt.isRunning():
        comunicador_global.mostrar_mensagem.emit("aviso", "Em andamento", "Já existe uma exportação em andamento.")
        return

    controller = WorkerController(dados, estado, skus_info)
    estado["worker_controller"] = controller
    controller.iniciar_worker()  # ou: controller.iniciar_worker_signal.emit()

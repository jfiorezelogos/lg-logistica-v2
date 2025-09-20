# common/logging_setup.py
from __future__ import annotations

import logging
import os
import sys
import uuid
from contextvars import ContextVar

from pythonjsonlogger import jsonlogger

# contexto (propaga por thread; você seta uma vez no começo da execução/request)
correlation_id_ctx: ContextVar[str] = ContextVar("correlation_id", default="-")
app_env_ctx: ContextVar[str] = ContextVar("app_env", default=os.getenv("APP_ENV", "dev"))


class ContextFilter(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        # campos sempre presentes nos logs
        record.correlation_id = correlation_id_ctx.get("-")
        record.env = app_env_ctx.get("dev")
        return True


def _build_json_formatter() -> logging.Formatter:
    # campos em ordem útil; ajuste/adicione conforme seu gosto
    fmt = (
        "%(asctime)s %(levelname)s %(name)s %(message)s "
        "%(correlation_id)s %(env)s %(filename)s:%(lineno)d"
    )
    f = jsonlogger.JsonFormatter(
        fmt,
        timestamp=True,
        json_ensure_ascii=False,
        json_indent=None,
        rename_fields={"asctime": "ts", "levelname": "level"},
    )
    return f


def setup_logging(
    *,
    level: int = logging.INFO,
    json_console: bool = True,
    file_path: str | None = None,
) -> None:
    """
    Configura logging global:
    - console em JSON (ou texto, se json_console=False)
    - arquivo opcional (se file_path)
    """
    root = logging.getLogger()
    root.setLevel(level)

    # limpar handlers antigos (evita logs duplicados ao reconfigurar)
    for h in list(root.handlers):
        root.removeHandler(h)

    ctx_filter = ContextFilter()

    # Console handler
    ch = logging.StreamHandler(stream=sys.stdout)
    ch.setLevel(level)
    if json_console:
        ch.setFormatter(_build_json_formatter())
    else:
        ch.setFormatter(logging.Formatter("[%(asctime)s] %(levelname)s %(name)s: %(message)s"))
    ch.addFilter(ctx_filter)
    root.addHandler(ch)

    if file_path:
        fh = logging.FileHandler(file_path, encoding="utf-8")
        fh.setLevel(level)
        fh.setFormatter(_build_json_formatter())
        fh.addFilter(ctx_filter)
        root.addHandler(fh)


def set_correlation_id(value: str | None = None) -> str:
    """
    Define (ou gera) o correlation_id para o contexto atual.
    Retorna o valor definido.
    """
    cid = value or str(uuid.uuid4())
    correlation_id_ctx.set(cid)
    return cid

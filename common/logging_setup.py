# common/logging_setup.py
from __future__ import annotations

import logging
import os
import re
import sys
import uuid
from collections.abc import Iterable
from contextvars import ContextVar
from typing import Any

from pythonjsonlogger import jsonlogger

# ---------------------------
# Contexto propagado por execução
# ---------------------------
correlation_id_ctx: ContextVar[str] = ContextVar("correlation_id", default="-")
app_env_ctx: ContextVar[str] = ContextVar("app_env", default="dev")


def get_correlation_id() -> str:
    """Retorna o correlation_id atual do contexto."""
    return correlation_id_ctx.get("-")


# ---------------------------
# Filtro de contexto + máscara opcional
# ---------------------------
class ContextFilter(logging.Filter):
    def __init__(self, *, service: str, version: str, mask_secrets: bool = False) -> None:
        super().__init__()
        self.service = service
        self.version = version
        self.mask_secrets = mask_secrets
        # padrões simples para mascarar chaves (amplie conforme necessário)
        self._patterns: list[re.Pattern[str]] = []
        if mask_secrets:
            self._patterns = [
                re.compile(r"(api[_-]?key\s*=\s*)([A-Za-z0-9_\-]{6,})", re.IGNORECASE),
                re.compile(r"(token\s*=\s*)([A-Za-z0-9_\-]{6,})", re.IGNORECASE),
                re.compile(r"(authorization:\s*bearer\s+)([A-Za-z0-9\._\-]{6,})", re.IGNORECASE),
            ]

    def _mask(self, msg: str) -> str:
        if not self.mask_secrets or not msg:
            return msg
        masked = msg
        for p in self._patterns:
            masked = p.sub(r"\1***", masked)
        return masked

    def filter(self, record: logging.LogRecord) -> bool:
        # Campos padronizados
        record.correlation_id = correlation_id_ctx.get("-")
        record.env = app_env_ctx.get()
        record.service = self.service
        record.version = self.version
        record.pid = os.getpid()
        # preservar record.thread como id; expor nome separado
        record.thread_name = getattr(record, "threadName", "")

        # Se a msg for string, podemos mascarar segredos
        if isinstance(record.msg, str):
            record.msg = self._mask(record.msg)
        return True


# ---------------------------
# Formatter JSON (UTC, ISO-8601)
# ---------------------------
class UtcJsonFormatter(jsonlogger.JsonFormatter):
    def __init__(self, *args: Any, **kwargs: Any) -> None:
        kwargs.setdefault("timestamp", True)
        kwargs.setdefault("json_ensure_ascii", False)
        kwargs.setdefault("json_indent", None)
        kwargs.setdefault("rename_fields", {"asctime": "ts", "levelname": "level", "message": "msg"})
        # se o stub reclamar dos kwargs, habilite a linha abaixo:
        # super().__init__(*args, **kwargs)  # type: ignore[call-arg]
        super().__init__(*args, **kwargs)

    def add_fields(
        self,
        log_record: dict[str, Any],
        record: logging.LogRecord,
        message_dict: dict[str, Any],
    ) -> None:
        super().add_fields(log_record, record, message_dict)
        if "ts" in log_record and isinstance(log_record["ts"], str) and not log_record["ts"].endswith("Z"):
            log_record["ts"] += "Z"


# ---------------------------
# Builders de formatter
# ---------------------------
def _build_json_formatter() -> logging.Formatter:
    fmt = (
        "%(asctime)s %(levelname)s %(name)s %(message)s "
        "%(correlation_id)s %(env)s %(service)s %(version)s %(pid)s %(thread_name)s %(filename)s:%(lineno)d"
    )
    return UtcJsonFormatter(fmt)


def _build_text_formatter() -> logging.Formatter:
    return logging.Formatter(
        "[%(asctime)s] %(levelname)s %(name)s %(env)s %(service)s:%(version)s "
        "(cid=%(correlation_id)s pid=%(pid)s thread=%(thread_name)s) %(message)s"
    )


# ---------------------------
# Setup principal
# ---------------------------
def setup_logging(
    *,
    level: int | str | None = None,
    json_console: bool | None = None,
    file_path: str | None = None,
    quiet_loggers: Iterable[str] = ("urllib3", "botocore", "boto3"),
) -> None:
    """
    Configura logging global:
      - Console JSON por padrão (defina LOG_JSON=0 p/ texto)
      - Nível por LOG_LEVEL (DEBUG/INFO/WARN/ERROR), padrão INFO
      - Arquivo opcional (LOG_FILE ou parâmetro file_path)
      - Campos padrão: service, version, env, correlation_id, pid, thread_name
      - Máscara opcional de segredos: LOG_MASK_SECRETS=1
    """
    service = os.getenv("APP_NAME", "lg-logistica")
    version = os.getenv("APP_VERSION", "0.0.0")
    env = os.getenv("APP_ENV", "dev")
    app_env_ctx.set(env)

    # Deriva parâmetros dos envs se não informados
    if level is None:
        level = os.getenv("LOG_LEVEL", "INFO").upper()
    if isinstance(level, str):
        level = getattr(logging, level, logging.INFO)

    if json_console is None:
        json_console = os.getenv("LOG_JSON", "1") not in ("0", "false", "False")

    file_path = file_path or os.getenv("LOG_FILE")
    mask_secrets = os.getenv("LOG_MASK_SECRETS", "0") in ("1", "true", "True")

    root = logging.getLogger()
    root.setLevel(level)

    # Evita duplicações
    for h in list(root.handlers):
        root.removeHandler(h)

    ctx_filter = ContextFilter(service=service, version=version, mask_secrets=mask_secrets)

    # Console
    ch = logging.StreamHandler(stream=sys.stdout)
    ch.setLevel(level)
    ch.setFormatter(_build_json_formatter() if json_console else _build_text_formatter())
    ch.addFilter(ctx_filter)
    root.addHandler(ch)

    # Arquivo opcional
    if file_path:
        fh = logging.FileHandler(file_path, encoding="utf-8")
        fh.setLevel(level)
        fh.setFormatter(_build_json_formatter())
        fh.addFilter(ctx_filter)
        root.addHandler(fh)

    # Reduz ruído de libs conhecidas (sempre WARNING)
    for name in quiet_loggers or ():
        logging.getLogger(name).setLevel(logging.WARNING)


# ---------------------------
# Helpers
# ---------------------------
def set_correlation_id(value: str | None = None) -> str:
    """Define (ou gera) o correlation_id para o contexto atual.

    Retorna o valor definido.
    """
    cid = value or str(uuid.uuid4())
    correlation_id_ctx.set(cid)
    return cid


def bind_context(*, app_env: str | None = None, correlation_id: str | None = None) -> None:
    """Permite setar env e correlation_id num ponto único (ex.: início do main)."""
    if app_env:
        app_env_ctx.set(app_env)
    if correlation_id:
        set_correlation_id(correlation_id)


def get_logger(name: str | None = None) -> logging.Logger:
    """Sugar para obter logger tipado."""
    return logging.getLogger(name or "lglog")

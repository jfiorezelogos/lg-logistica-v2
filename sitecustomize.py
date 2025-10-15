# sitecustomize.py — inicializa logging e correlation id automaticamente
from __future__ import annotations

import io
import logging
import os
import sys
from logging.handlers import RotatingFileHandler
from typing import Literal, TextIO, cast

from common.logging_setup import set_correlation_id, setup_logging

# tenta usar platformdirs; se não estiver instalado, cai para um fallback seguro
try:
    from platformdirs import user_log_dir
except Exception:  # pragma: no cover
    # Assinatura idêntica à de platformdirs.user_log_dir
    def user_log_dir(
        appname: str | None = None,
        appauthor: str | Literal[False] | None = None,
        version: str | None = None,
        opinion: bool = True,
        ensure_exists: bool = False,
    ) -> str:
        """
        Fallback minimalista de user_log_dir (caso platformdirs não esteja disponível).
        Retorna um diretório de logs em LOCALAPPDATA ou no home do usuário.
        """
        # Os parâmetros version/opinion não são usados — prefixo com "_" para evitar warnings
        _ = (version, opinion)
        base = os.getenv("LOCALAPPDATA") or os.path.expanduser("~")
        parts: list[str] = [base]
        if isinstance(appauthor, str) and appauthor:
            parts.append(appauthor)
        if appname:
            parts.append(appname)
        parts.append("Logs")
        path = os.path.join(*parts)
        if ensure_exists:
            os.makedirs(path, exist_ok=True)
        return path


APP_NAME = "lg-logistica"
APP_AUTHOR = "Logos Editora"

# ---------------------------------------------------------------------
# 1) Resolve diretório/arquivo de log (Windows-friendly)
#    - Ex.: C:\Users\<user>\AppData\Local\Logos Editora\lg-logistica\Logs\sistema.log
# ---------------------------------------------------------------------
log_dir = user_log_dir(APP_NAME, APP_AUTHOR, ensure_exists=True)
os.makedirs(log_dir, exist_ok=True)
log_file = os.path.join(log_dir, "sistema.log")

# nível via ENV (DEBUG=1) ou INFO por padrão
level = logging.DEBUG if os.getenv("DEBUG") == "1" else logging.INFO

# Configura console JSON + arquivo
# (setup_logging já respeita LOG_LEVEL, LOG_JSON, LOG_FILE se definidos)
setup_logging(level=level, json_console=True, file_path=log_file)

# Roda arquivo para evitar crescimento infinito (5 MB x 5)
root = logging.getLogger()
root.addHandler(RotatingFileHandler(log_file, maxBytes=5_000_000, backupCount=5, encoding="utf-8"))

# 2) Gera um correlation_id único por execução
set_correlation_id()

bootstrap_log = logging.getLogger("bootstrap")
bootstrap_log.info(
    "logging inicializado via sitecustomize.py",
    extra={"log_file": log_file},
)


# ---------------------------------------------------------------------
# 3) (opcional) Capturar print()/stderr e mandar para o logger
#    - Desabilitar com LOG_CAPTURE_STDOUT=0
# ---------------------------------------------------------------------
class _StreamToLogger(io.TextIOBase):
    """Redireciona stdout/stderr para o logger."""

    def __init__(self, logger: logging.Logger, level: int) -> None:
        super().__init__()
        self.logger = logger
        self.level = level
        self._buf = ""

    def write(self, buf: str) -> int:
        if not isinstance(buf, str):
            buf = str(buf)
        self._buf += buf
        written = len(buf)
        while "\n" in self._buf:
            line, self._buf = self._buf.split("\n", 1)
            line = line.strip()
            if line:
                self.logger.log(self.level, line)
        return written

    def flush(self) -> None:
        if self._buf.strip():
            self.logger.log(self.level, self._buf.strip())
            self._buf = ""

    def isatty(self) -> bool:  # pragma: no cover
        return False


if os.getenv("LOG_CAPTURE_STDOUT", "1").lower() not in ("0", "false"):
    sys.stdout = cast(TextIO, _StreamToLogger(logging.getLogger("stdout"), logging.INFO))
    sys.stderr = cast(TextIO, _StreamToLogger(logging.getLogger("stderr"), logging.ERROR))

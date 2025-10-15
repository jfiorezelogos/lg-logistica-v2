# sitecustomize.py — inicializa logging e correlation id automaticamente
from __future__ import annotations

import io
import logging
import os
import sys
import tempfile
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Literal, TextIO, cast

from common.logging_setup import set_correlation_id, setup_logging

# tenta usar platformdirs; se não estiver instalado, cai para um fallback seguro
try:  # pragma: no cover
    from platformdirs import user_log_dir
except Exception:  # pragma: no cover
    # Assinatura compatível com platformdirs.user_log_dir
    def user_log_dir(
        appname: str | None = None,
        appauthor: str | Literal[False] | None = None,
        version: str | None = None,
        opinion: bool = True,
        ensure_exists: bool = False,
    ) -> str:
        """
        Fallback minimalista de user_log_dir (caso platformdirs não esteja disponível).
        Retorna um diretório de logs em LOCALAPPDATA (Windows) ou HOME (POSIX).
        """
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
# 1) Resolve diretório/arquivo de log (Windows/macOS/Linux friendly)
#    - Ex. Win: C:\Users\<user>\AppData\Local\Logos Editora\lg-logistica\Logs\sistema.log
#    - Ex. macOS: ~/Library/Logs/Logos Editora/lg-logistica/sistema.log (via platformdirs)
#    - Ex. Linux: ~/.cache/... ou ~/.local/state/... (dependendo da versão do platformdirs)
# ---------------------------------------------------------------------
def _resolve_log_path() -> Path:
    try:
        log_dir_str = user_log_dir(APP_NAME, APP_AUTHOR, ensure_exists=True)
        log_dir = Path(log_dir_str)
        # Em POSIX, tentamos reforçar perms de diretório do usuário (melhor esforço)
        if os.name == "posix":
            try:
                log_dir.mkdir(parents=True, exist_ok=True)
                os.chmod(log_dir, 0o700)
            except Exception:
                pass
        else:
            log_dir.mkdir(parents=True, exist_ok=True)
        return log_dir / "sistema.log"
    except Exception:
        # Fallback final: subpasta em temp
        tmp = Path(tempfile.gettempdir()) / "lg-logistica" / "Logs"
        tmp.mkdir(parents=True, exist_ok=True)
        return tmp / "sistema.log"


log_file_path = _resolve_log_path()

# nível via ENV (DEBUG=1) ou INFO por padrão
level = logging.DEBUG if os.getenv("DEBUG", "").strip() == "1" else logging.INFO

# ---------------------------------------------------------------------
# 2) Configura logging:
#    - Preferimos evitar duplicação de handlers de arquivo:
#      chamamos setup_logging apenas para console JSON
#      e nós próprios adicionamos um RotatingFileHandler.
# ---------------------------------------------------------------------
setup_logging(level=level, json_console=True)

# Remove quaisquer FileHandlers previamente criados para evitar duplicação
root = logging.getLogger()
for h in list(root.handlers):
    if isinstance(h, logging.FileHandler):
        root.removeHandler(h)

# Adiciona RotatingFileHandler (5 MB x 5 backups)
try:
    rotating = RotatingFileHandler(
        log_file_path,
        maxBytes=5_000_000,
        backupCount=5,
        encoding="utf-8",
        delay=True,  # abre o arquivo sob demanda
    )
    rotating.setLevel(level)
    # Formato simples; se seu setup_logging já usa JSON no console, manter arquivo legível ajuda suporte
    rotating.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(name)s %(message)s"))
    root.addHandler(rotating)
except Exception:
    # Último fallback: se não conseguir abrir o arquivo, não falha o app — mantém só console
    pass

# 3) Correlation ID por execução
set_correlation_id()

bootstrap_log = logging.getLogger("bootstrap")
bootstrap_log.info(
    "logging inicializado via sitecustomize.py",
    extra={"log_file": str(log_file_path)},
)


# ---------------------------------------------------------------------
# 4) (opcional) Capturar print()/stderr e mandar para o logger
#    - Desabilitar com LOG_CAPTURE_STDOUT=0  (stderr acompanha stdout)
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


if os.getenv("LOG_CAPTURE_STDOUT", "1").strip().lower() not in ("0", "false", "no"):
    sys.stdout = cast(TextIO, _StreamToLogger(logging.getLogger("stdout"), logging.INFO))
    sys.stderr = cast(TextIO, _StreamToLogger(logging.getLogger("stderr"), logging.ERROR))

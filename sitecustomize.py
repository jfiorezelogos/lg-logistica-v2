# sitecustomize.py — inicializa logging e correlation id automaticamente
from __future__ import annotations

import io
import logging
import os
import sys
from typing import TextIO, cast  # ⬅️ importa TextIO e cast

from common.logging_setup import set_correlation_id, setup_logging

# 1) configura logging global (respeita LOG_LEVEL, LOG_JSON, LOG_FILE)
level = logging.DEBUG if os.getenv("DEBUG") == "1" else logging.INFO
log_file = os.path.join(os.getcwd(), "sistema.log")
setup_logging(level=level, json_console=True, file_path=log_file)

# 2) gera um id único por execução (aparece como correlation_id nos logs)
set_correlation_id()

bootstrap_log = logging.getLogger("bootstrap")
bootstrap_log.info("logging inicializado via sitecustomize.py")


# 3) (opcional) capturar print()/stderr e mandar para o logger
class _StreamToLogger(io.TextIOBase):
    def __init__(self, logger: logging.Logger, level: int) -> None:
        super().__init__()
        self.logger = logger
        self.level = level
        self._buf = ""

    def write(self, buf: str) -> int:  # compatível com TextIO
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

    def flush(self) -> None:  # compatível com TextIO
        if self._buf.strip():
            self.logger.log(self.level, self._buf.strip())
            self._buf = ""

    # (opcional) ajuda ferramentas que consultam terminalidade
    def isatty(self) -> bool:
        return False


if os.getenv("LOG_CAPTURE_STDOUT", "1") not in ("0", "false", "False"):
    sys.stdout = cast(TextIO, _StreamToLogger(logging.getLogger("stdout"), logging.INFO))
    sys.stderr = cast(TextIO, _StreamToLogger(logging.getLogger("stderr"), logging.ERROR))

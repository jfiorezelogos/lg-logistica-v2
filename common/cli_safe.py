from __future__ import annotations

import functools
import os
import sys
import traceback
from collections.abc import Callable
from contextlib import suppress
from typing import Any

from .errors import AppError, to_user_message


def _is_debug_enabled() -> bool:
    val = os.getenv("DEBUG")
    if val is None:
        return "--debug" in sys.argv
    return str(val).strip().lower() in {"1", "true", "on", "yes"}


def safe_cli(main_func: Callable[..., int | None]) -> Callable[..., int]:
    """Decorator para pontos de entrada de CLI.

    Convencões:
      - Sucesso: 0
      - AppError (erro previsto/negócio): 2
      - Erro inesperado: 1
      - Ctrl+C (KeyboardInterrupt): 130

    Em DEBUG (DEBUG=1/true/on/yes ou --debug), imprime traceback completo.
    """

    @functools.wraps(main_func)
    def wrapper(*args: Any, **kwargs: Any) -> int:
        status: int = 1  # fallback padrão
        try:
            result = main_func(*args, **kwargs)
            status = int(result) if result is not None else 0
        except KeyboardInterrupt:
            status = 130
        except BrokenPipeError:
            with suppress(Exception):
                sys.stdout.flush()
            status = 0
        except SystemExit as e:
            code = e.code
            if code is None:
                status = 0
            elif isinstance(code, int):
                status = code
            else:
                status = 1
        except Exception as exc:
            debug = _is_debug_enabled()
            if debug:
                traceback.print_exc()
            msg = to_user_message(exc, debug=debug)
            print(msg, file=sys.stderr)
            status = 2 if isinstance(exc, AppError) else 1

        return status

    return wrapper

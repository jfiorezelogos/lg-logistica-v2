# common/cli_safe.py
from __future__ import annotations

import functools
import os
import sys
import traceback
from collections.abc import Callable  # <- aqui
from typing import Any

from .errors import AppError, to_user_message


def _is_debug_enabled() -> bool:
    val = os.getenv("DEBUG")
    if val is None:
        return "--debug" in sys.argv
    return val not in ("0", "false", "False", "")


def safe_cli(main_func: Callable[..., int | None]) -> Callable[..., int]:
    """
    Decorator para pontos de entrada de CLI.
    - Sucesso: 0
    - AppError (prevista/negócio): 2
    - Erro inesperado: 1
    - Ctrl+C: 130
    Em DEBUG (DEBUG=1/true ou --debug), imprime traceback completo.
    """

    @functools.wraps(main_func)
    def wrapper(*args: Any, **kwargs: Any) -> int:
        try:
            result = main_func(*args, **kwargs)
            if result is None:
                return 0
            return int(result)
        except KeyboardInterrupt:
            return 130
        except BrokenPipeError:
            try:
                sys.stdout.flush()
            except Exception:
                pass
            return 0
        except SystemExit as e:
            try:
                return int(e.code) if e.code is not None else 1
            except Exception:
                return 1
        except Exception as exc:
            debug = _is_debug_enabled()
            if debug:
                traceback.print_exc()
            msg = to_user_message(exc, debug=debug)
            print(msg, file=sys.stderr)
            return 2 if isinstance(exc, AppError) else 1

        return 1  # fallback

    return wrapper

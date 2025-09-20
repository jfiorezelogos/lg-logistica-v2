# common/cli_safe.py
from __future__ import annotations

import os
import sys
import traceback
from collections.abc import Callable
from typing import ParamSpec

from .errors import AppError, to_user_message

P = ParamSpec("P")


def safe_cli(main_func: Callable[P, int | None]) -> Callable[P, int]:
    """
    Decorator para pontos de entrada de CLI.
    - Retorna 0 em sucesso
    - Retorna 2 quando a exceção é conhecida (AppError)
    - Retorna 1 quando é erro inesperado
    Em DEBUG=1 ou com --debug nos args, imprime traceback.
    """

    def wrapper(*args: P.args, **kwargs: P.kwargs) -> int:
        try:
            result = main_func(*args, **kwargs)
            return int(result or 0)
        except SystemExit as e:
            # permite main() usar raise SystemExit(0/1/2) se desejar
            return int(e.code or 1)
        except Exception as exc:
            debug = ("--debug" in sys.argv) or bool(os.getenv("DEBUG"))
            if debug:
                traceback.print_exc()
            msg = to_user_message(exc, debug=debug)
            print(msg, file=sys.stderr)
            return 2 if isinstance(exc, AppError) else 1

    return wrapper

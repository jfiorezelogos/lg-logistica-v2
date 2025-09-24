from __future__ import annotations

from pathlib import Path
from typing import Any, cast

from pydantic import BaseModel, Field, ValidationError, field_validator

from .errors import UserError


class JobConfig(BaseModel):
    """Exemplo de config de tarefa — adapte aos campos do seu domínio."""

    input_path: str = Field(min_length=1)
    output_dir: str = Field(min_length=1)
    max_rows: int = Field(default=100_000, ge=1, le=5_000_000)
    dry_run: bool = False

    @field_validator("input_path")
    @classmethod
    def validate_input_ext(cls, v: str) -> str:
        allowed: tuple[str, str] = (".csv", ".xlsx")
        if not v.lower().endswith(allowed):
            raise ValueError(f"input_path deve terminar com {allowed}")
        return v


def validate_config(payload: dict[str, Any]) -> JobConfig:
    """Converte o dicionário em JobConfig e converte ValidationError em UserError."""
    try:
        # mypy às vezes não infere corretamente o tipo retornado
        return cast(JobConfig, JobConfig.model_validate(payload))
    except ValidationError as e:
        # e.errors() traz uma lista estruturada com campo, msg, tipo etc.
        raise UserError(
            "Configuração inválida",
            code="BAD_INPUT",
            data={"errors": e.errors()},
        ) from e


def ensure_paths(cfg: JobConfig) -> None:
    """Checagens de existência/permissão de caminhos antes de processar.

    Não altera estado além de criar a pasta de saída se necessário.
    """
    in_path = Path(cfg.input_path)
    if not in_path.exists():
        raise UserError(
            "Arquivo de entrada não existe",
            code="INPUT_NOT_FOUND",
            data={"path": str(in_path)},
        )

    out_dir = Path(cfg.output_dir)
    try:
        out_dir.mkdir(parents=True, exist_ok=True)
    except OSError as e:
        raise UserError(
            "Sem permissão para criar/escrever na pasta de saída",
            code="OUTPUT_DIR_ERROR",
            data={"path": str(out_dir)},
        ) from e

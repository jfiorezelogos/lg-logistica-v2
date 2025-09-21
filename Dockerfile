# build
FROM python:3.13-slim AS build
WORKDIR /app
ENV PIP_NO_CACHE_DIR=1 PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1
RUN apt-get update && apt-get install -y --no-install-recommends build-essential && rm -rf /var/lib/apt/lists/*
COPY requirements.txt .
RUN pip install --prefix=/install -r requirements.txt

# runtime
FROM python:3.13-slim
RUN useradd -m appuser
WORKDIR /app
COPY --from=build /install /usr/local
COPY . .
ENV PYTHONUNBUFFERED=1
USER appuser
CMD ["python","main.py"]

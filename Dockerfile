
FROM python:3.11-slim
RUN apt-get update && apt-get install -y poppler-utils libgomp1 curl && rm -rf /var/lib/apt/lists/*

RUN useradd -m -u 1000 user
USER user
ENV HOME=/home/user \
    PATH=/home/user/.local/bin:$PATH

WORKDIR $HOME/app

COPY --chown=user requirements.txt .
RUN pip install --user --no-cache-dir --upgrade pip && pip install --user --no-cache-dir -r requirements.txt huggingface_hub

COPY --chown=user . .

EXPOSE 7860
HEALTHCHECK --interval=30s --timeout=10s --start-period=30s --retries=3 CMD curl -f http://localhost:7860/_stcore/health || exit 1

CMD ["python", "start.py"]

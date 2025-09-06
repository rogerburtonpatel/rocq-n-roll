import subprocess
import json
import threading
import sys
import os

def make_message(payload: dict) -> bytes:
    """Encode JSON RPC message with Content-Length header"""
    data = json.dumps(payload)
    return f"Content-Length: {len(data)}\r\n\r\n{data}".encode("utf-8")

def reader(proc):
    """Continuously read responses from coq-lsp"""
    while True:
        # Read header
        header_bytes = b""
        while not header_bytes.endswith(b"\r\n\r\n"):
            chunk = proc.stdout.read(1)
            if not chunk:
                return
            header_bytes += chunk

        header_text = header_bytes.decode()
        length = None
        for line in header_text.split("\r\n"):
            if line.lower().startswith("content-length:"):
                length = int(line.split(":")[1].strip())
        if length is None:
            print("!!! No Content-Length found in header:", header_text)
            continue

        # Read body
        body = proc.stdout.read(length).decode()
        try:
            msg = json.loads(body)
            print("<<<", json.dumps(msg, indent=2))
        except Exception as e:
            print("!!! Failed to parse body:", body, e)

def main():
    if len(sys.argv) < 2:
        print("Usage: python coq_lsp_test.py path/to/file.v")
        sys.exit(1)

    coq_file = os.path.abspath(sys.argv[1])

    # Start coq-lsp
    proc = subprocess.Popen(
        ["coq-lsp"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        bufsize=0,
    )

    # Background reader thread
    threading.Thread(target=reader, args=(proc,), daemon=True).start()

    def send(obj):
        msg = make_message(obj)
        print(">>>", json.dumps(obj))
        proc.stdin.write(msg)
        proc.stdin.flush()

    # 1. initialize
    send({
        "jsonrpc": "2.0",
        "id": 1,
        "method": "initialize",
        "params": {
            "processId": None,
            "clientInfo": {"name": "py-test"},
            "rootUri": None,
            "capabilities": {}
        }
    })

    # 2. initialized
    send({
        "jsonrpc": "2.0",
        "method": "initialized",
        "params": {}
    })

    # 3. didOpen
    with open(coq_file) as f:
        text = f.read()
    send({
        "jsonrpc": "2.0",
        "method": "textDocument/didOpen",
        "params": {
            "textDocument": {
                "uri": f"file://{coq_file}",
                "languageId": "coq",
                "version": 1,
                "text": text
            }
        }
    })

    # 4. Try sentenceNext
    for i, method in enumerate(["coq-lsp/sentenceNext", "coq-lsp.sentenceNext"], start=10):
        send({
            "jsonrpc": "2.0",
            "id": i,
            "method": method,
            "params": {
                "textDocument": {
                    "uri": f"file://{coq_file}",
                    "version": 1
                },
                "position": {
                    "line": 0,
                    "character": 0
                }
            }
        })

    # Also print stderr logs
    def stderr_reader():
        for line in proc.stderr:
            print("STDERR:", line.decode().strip())
    threading.Thread(target=stderr_reader, daemon=True).start()

    input("Press Enter to exit...\n")
    proc.kill()

if __name__ == "__main__":
    main()

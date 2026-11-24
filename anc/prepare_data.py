"""Restore large JSON inputs compressed when building the arXiv submission."""
import gzip
import hashlib
import json
from pathlib import Path
import tempfile


def main():
    root = Path(__file__).resolve().parent
    manifest = root / 'compressed_inputs.json'
    if not manifest.exists():
        print('Repository inputs are already available; no submission manifest present.')
        return
    records = json.loads(manifest.read_text())
    for name, expected in records.items():
        target = (root / name).resolve()
        if not target.is_relative_to(root):
            raise ValueError(f'Input path leaves anc/: {name}')
        if target.exists():
            with target.open('rb') as stream:
                actual = hashlib.file_digest(stream, 'sha256').hexdigest()
            if actual != expected:
                raise ValueError(f'Existing JSON differs from the packaged input: {name}')
            continue
        temporary = None
        try:
            digest = hashlib.sha256()
            with gzip.open(str(target)+'.gz', 'rb') as source:
                with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as output:
                    temporary = Path(output.name)
                    while chunk := source.read(1024 * 1024):
                        digest.update(chunk)
                        output.write(chunk)
            if digest.hexdigest() != expected:
                raise ValueError(f'Input checksum mismatch: {name}')
            temporary.replace(target)
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
    print(f'Checked/restored {len(records)} JSON inputs; all SHA-256 hashes match.')


if __name__ == '__main__':
    main()

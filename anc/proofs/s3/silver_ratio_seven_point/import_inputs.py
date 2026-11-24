"""Copy the original seven-point JSON inputs as deterministic gzip files.

Only the destination is written. Original workspace files are never modified.
The verifier consumes these compressed copies directly.
"""
import argparse
import gzip
import hashlib
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
INPUTS = ('cert7_full_k.json', 'farkas_k_excluded.json')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path, help='original sqrt2/r7 directory')
    args = parser.parse_args()
    hashes = []
    for name in INPUTS:
        source = args.source/name
        target = HERE/(name+'.gz')
        with source.open('rb') as inp, target.open('wb') as out:
            with gzip.GzipFile(filename='', mode='wb', fileobj=out, mtime=0) as compressed:
                shutil.copyfileobj(inp, compressed)
        with source.open('rb') as inp:
            original_hash = hashlib.file_digest(inp, 'sha256').hexdigest()
        with gzip.open(target, 'rb') as inp:
            copied_hash = hashlib.file_digest(inp, 'sha256').hexdigest()
        if original_hash != copied_hash:
            raise RuntimeError(f'Copy verification failed: {name}')
        hashes.append(f'{original_hash}  {name}')
        print(f'{name}: {source.stat().st_size} -> {target.stat().st_size} bytes; identical decompressed input')
    (HERE/'INPUT_SHA256SUMS').write_text('\n'.join(hashes)+'\n')
    compressed_hashes = []
    for name in INPUTS:
        target = HERE/(name+'.gz')
        with target.open('rb') as inp:
            compressed_hashes.append(f'{hashlib.file_digest(inp, "sha256").hexdigest()}  {target.name}')
    (HERE/'SHA256SUMS').write_text('\n'.join(compressed_hashes)+'\n')


if __name__ == '__main__':
    main()

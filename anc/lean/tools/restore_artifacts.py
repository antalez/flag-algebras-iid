#!/usr/bin/env python3
"""Restore or check ignored proof artifacts from the pinned upstream ZIP."""
import argparse
import hashlib
from pathlib import Path, PurePosixPath
import sys
import zipfile

ARCHIVE_SHA256 = '465728d4b8e3368e59f522f99b10a87a4d0577d1f35a70c6e7f1fb7e1650d4d6'
PREFIX = 'formal/proof/'
ROOT = Path(__file__).resolve().parents[1]
EXACT = {
    'Fast/Cert8Data.lean', 'BeatAvg/Six/Data.lean',
    'BeatAvg/K8/Tables.lean', 'BeatAvg/K8/TablesQ.lean',
    'BeatAvg/K8/TablesF.lean', 'BeatAvg/K8/L56.lean',
    'BeatAvg/K8/L7G.lean', 'BeatAvg/K8/L7X.lean',
}


def is_artifact(name):
    p = PurePosixPath(name)
    return (name in EXACT or name.startswith(('BeatAvg/K8/F/', 'BeatAvg/K8/P8/'))
            or (p.parent == PurePosixPath('data') and p.suffix == '.txt'))


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archive', type=Path, help='beat_the_average_kernel.zip')
    parser.add_argument('--check', action='store_true', help='compare artifacts without writing')
    args = parser.parse_args()
    if digest(args.archive) != ARCHIVE_SHA256:
        parser.error('Archive SHA-256 does not match the pinned release; no files were written.')
    count = total = bad = 0
    with zipfile.ZipFile(args.archive) as archive:
        for info in archive.infolist():
            if info.is_dir() or not info.filename.startswith(PREFIX):
                continue
            name = info.filename[len(PREFIX):]
            if not is_artifact(name):
                continue
            relative = PurePosixPath(name)
            if relative.is_absolute() or '..' in relative.parts:
                parser.error('Unsafe archive path')
            target = ROOT.joinpath(*relative.parts)
            if not target.resolve().is_relative_to(ROOT):
                parser.error('Artifact path escapes the project through a symlink')
            content = archive.read(info)
            if args.check:
                if not target.is_file() or target.read_bytes() != content:
                    if bad < 10:
                        print(f'Missing or changed: {name}', file=sys.stderr)
                    bad += 1
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(content)
            count += 1
            total += len(content)
    print(f'{"Checked" if args.check else "Restored"} {count:,} artifacts ({total / 2**20:.1f} MiB).')
    if bad:
        print(f'{bad:,} missing or changed artifacts.', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())

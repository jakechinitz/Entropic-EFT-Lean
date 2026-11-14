"""Preserve primary scientific data and acquisition provenance; no deletion."""
from pathlib import Path
import urllib.request, hashlib, json, datetime, tarfile, sys

ROOT = Path(__file__).resolve().parent

def get(url, relative):
    dest = ROOT / relative
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists():
        raise FileExistsError(dest)
    with urllib.request.urlopen(url, timeout=90) as response, dest.open('xb') as out:
        final_url = response.url
        while block := response.read(1024 * 1024):
            out.write(block)
    record = dict(url=url, resolved_url=final_url, path=relative,
                  bytes=dest.stat().st_size,
                  sha256=hashlib.file_digest(dest.open('rb'), 'sha256').hexdigest(),
                  retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    with (ROOT / 'source_records' / (dest.name + '.json')).open('x', encoding='utf-8') as out:
        json.dump(record, out, indent=2)
    print(json.dumps(record), flush=True)
    return dest

if __name__ == '__main__':
    if sys.argv[1] == 'xcop':
        archive = get('https://drive.switch.ch/index.php/s/j3WUOYXWgv9Jbnz/download',
                      'source_data/xcop_allfiles.tar.gz')
        inventory=[]
        with tarfile.open(archive) as tar:
            for member in tar.getmembers():
                inventory.append(dict(name=member.name, bytes=member.size))
                # Preserve only table products expanded; original complete archive remains.
                if member.isfile() and member.name.endswith('.fits') and member.size < 2000000:
                    dest = (ROOT / 'source_data/xcop' / member.name).resolve()
                    if not dest.is_relative_to((ROOT / 'source_data/xcop').resolve()):
                        raise ValueError(member.name)
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    with dest.open('xb') as f:
                        f.write(tar.extractfile(member).read())
        (ROOT / 'source_records/xcop_archive_inventory.json').write_text(json.dumps(inventory,indent=2))
        print('Archive entries',len(inventory),flush=True)
    else:
        get(sys.argv[1],sys.argv[2])

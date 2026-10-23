#!/usr/bin/env python3
"""Check byte-model fixtures against a local copy of the pinned NIST ACVP corpus.

Pass the corpus's gen-val/json-files directory as the only argument. This check
uses no network and verifies each source hash before comparing projected fields.
"""

import hashlib
import json
from pathlib import Path
import sys


def check(source_dir: Path) -> None:
    fixture_dir = Path(__file__).resolve().parents[1] / "HashSigTest/SLHDSA/ByteModelVectors"
    for fixture in ("vectors.json", "vectors-192f.json", "vectors-256f.json"):
        root = json.loads((fixture_dir / fixture).read_text())
        if root["source"]["commit"] != "975de31eb83d87039ec88934fdc47d8c312b892d":
            raise ValueError(f"{fixture}: unexpected NIST revision")
        sources = {}
        for relative, expected_hash in root["source"]["files"].items():
            path = source_dir / relative.removeprefix("gen-val/json-files/")
            raw = path.read_bytes()
            if hashlib.sha256(raw).hexdigest() != expected_hash:
                raise ValueError(f"{fixture}: source hash mismatch: {relative}")
            sources[relative] = json.loads(raw)
        for mode in ("keyGen", "sigGen", "sigVer"):
            prefix = f"gen-val/json-files/SLH-DSA-{mode}-FIPS205/"
            expected = sources[prefix + "expectedResults.json"]
            prompt = sources[prefix + "prompt.json"]
            results = {
                (group["tgId"], test["tcId"]): test
                for group in expected["testGroups"] for test in group["tests"]
            }
            groups = {group["tgId"]: group for group in prompt["testGroups"]} if prompt else {}
            for record in root[mode]:
                group_id, case_id = record["tgId"], record["tcId"]
                projected = {"vsId": expected["vsId"], "tgId": group_id}
                if prompt:
                    group = groups[group_id]
                    if group["parameterSet"] != root["parameterSet"]:
                        raise ValueError(f"{fixture}: parameter mismatch")
                    if mode != "keyGen" and group["signatureInterface"] != "internal":
                        raise ValueError(f"{fixture}: interface mismatch")
                    projected.update(next(t for t in group["tests"] if t["tcId"] == case_id))
                    if mode == "sigGen":
                        projected["deterministic"] = group["deterministic"]
                projected.update(results[group_id, case_id])
                for key, value in record.items():
                    if key in projected and projected[key] != value:
                        raise ValueError(f"{fixture}: {mode} {case_id}: {key} differs")
                    if prompt and key not in projected:
                        raise ValueError(f"{fixture}: unaccounted field {key}")
                if any(record[key] != value for key, value in results[group_id, case_id].items()):
                    raise ValueError(f"{fixture}: incomplete result projection")
        print(f"{fixture}: pinned source hashes and record projections PASS")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: check-slh-dsa-byte-vectors.py CORPUS_JSON_DIRECTORY")
    check(Path(sys.argv[1]))

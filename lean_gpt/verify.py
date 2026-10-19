#!/usr/bin/env python3
"""Check all project modules and their transitive axiom dependencies.

Writes verification.json and verification.log only after a complete run.
The manuscript hash makes the checked source version explicit.
"""

from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

for stream in (sys.stdout, sys.stderr):
    if hasattr(stream, "reconfigure"):
        stream.reconfigure(encoding="utf-8")

project = Path(__file__).resolve().parent
manuscript_relative = "../submission-Oct2026/LaestadiusCsirik_HK.tex"
manuscript_path = project / manuscript_relative
manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
mathlib_revision = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
mathlib_path = project / manifest["packagesDir"] / "mathlib"
mathlib_head = subprocess.check_output(
    ["git", "-C", str(mathlib_path), "rev-parse", "HEAD"], text=True, encoding="utf-8").strip()
if mathlib_head != mathlib_revision:
    raise RuntimeError("Installed mathlib checkout does not match the pinned revision")
installed_revisions = {}
installed_tracked_changes = {}
git_environment = dict(os.environ)
git_environment["GIT_OPTIONAL_LOCKS"] = "0"
for package in manifest["packages"]:
    head = subprocess.check_output(
        ["git", "-C", str(project / manifest["packagesDir"] / package["name"]),
         "rev-parse", "HEAD"], text=True, encoding="utf-8").strip()
    if head != package["rev"]:
        raise RuntimeError(f"Installed dependency {package['name']} does not match its pin")
    installed_revisions[package["name"]] = head
    changes = subprocess.check_output(
        ["git", "-C", str(project / manifest["packagesDir"] / package["name"]),
         "status", "--porcelain", "--untracked-files=no"], text=True, encoding="utf-8",
        env=git_environment).splitlines()
    installed_tracked_changes[package["name"]] = changes
    if any(line[3:].endswith(".lean") or Path(line[3:]).name in
           {"lean-toolchain", "lakefile.toml", "lake-manifest.json"} for line in changes):
        raise RuntimeError(f"Installed dependency {package['name']} has modified Lean sources or build pins")
compiler_version = subprocess.check_output(
    [sys.executable, str(project / "lean_local.py"), "--version"],
    text=True, encoding="utf-8").strip()
compiler_inputs = {
    name: hashlib.sha256((project / name).read_bytes()).hexdigest()
    for name in ("lean_local.py", "lean-toolchain", "lake-manifest.json", "verify.py")
}
def discover_sources():
    found = set()
    for directory, children, files in os.walk(project, followlinks=False):
        children[:] = [name for name in children if name not in {".lake", ".git", "__pycache__"}]
        for name in files:
            if name.endswith(".lean"):
                found.add((Path(directory) / name).relative_to(project).as_posix())
    return found


sources = discover_sources()
source_bytes = {source: (project / source).read_bytes() for source in sources}
modules = []
visiting = set()
visited = set()
dependencies = {}


def lean_imports(contents):
    """Read ordinary import lines, ignoring strings and nested Lean comments.

    Unsupported import syntax is rejected instead of silently omitting an edge.
    The final Lean environment audit independently checks the imported modules.
    """
    cleaned = []
    i = depth = 0
    quoted = False
    while i < len(contents):
        pair = contents[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                cleaned.append("\n" if contents[i] == "\n" else " ")
                i += 1
        elif quoted:
            if contents[i] == "\\":
                i += 2
            elif contents[i] == '"':
                quoted = False
                i += 1
            else:
                cleaned.append("\n" if contents[i] == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            cleaned.append(" ")
            i += 2
        elif pair == "--":
            end = contents.find("\n", i)
            i = len(contents) if end == -1 else end
        elif contents[i] == '"':
            quoted = True
            cleaned.append(" ")
            i += 1
        else:
            cleaned.append(contents[i])
            i += 1
    for line in "".join(cleaned).splitlines():
        if re.match(r"\s*(?:(?:public|meta)\s+)*import\b", line):
            match = re.fullmatch(r"\s*(?:(?:public|meta)\s+)*import\s+([A-Za-z0-9_. ]+)\s*", line)
            if not match:
                raise RuntimeError(f"Unsupported import syntax in dependency scanner: {line}")
            yield from match.group(1).split()


def visit(source):
    if source in visited:
        return
    if source in visiting:
        raise RuntimeError(f"Cyclic project import at {source}")
    visiting.add(source)
    dependencies[source] = set()
    for name in lean_imports(source_bytes[source].decode()):
        dependency = name.replace(".", "/") + ".lean"
        if dependency in sources:
            dependencies[source].add(dependency)
            visit(dependency)
    visiting.remove(source)
    visited.add(source)
    modules.append(source)


visit("Audit.lean")
missing = sources - visited
if missing:
    raise RuntimeError("Project sources omitted from the umbrella import and audit: "
                       + ", ".join(sorted(missing)))
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--jobs", type=int, default=4, help="Independent Lean processes, default 4")
parser.add_argument("--reuse-checked", action="store_true",
                    help="Reuse unchanged, previously checked modules and rebuild their dependents")
args = parser.parse_args()
if args.jobs < 1:
    parser.error("--jobs must be positive")
results_by_source = {}
outputs = {}
input_hashes = {source: hashlib.sha256(source_bytes[source]).hexdigest()
                for source in modules}
manuscript_hash = hashlib.sha256(manuscript_path.read_bytes()).hexdigest()
coverage_path = project / "coverage-review.json"
coverage_bytes = coverage_path.read_bytes() if coverage_path.exists() else b""
coverage = json.loads(coverage_bytes) if coverage_bytes else {}
coverage_reviewed = (
    coverage.get("mathematical_coverage_complete") is True
    and coverage.get("manuscript") == manuscript_relative
    and coverage.get("manuscript_sha256") == manuscript_hash
    and coverage.get("source_sha256") == input_hashes
)
previous = {}
report_path = project / "verification.json"
if args.reuse_checked and report_path.exists():
    candidate = json.loads(report_path.read_text(encoding="utf-8"))
    if (candidate.get("compiler_version") == compiler_version
            and candidate.get("compiler_inputs") == compiler_inputs
            and candidate.get("installed_dependency_revisions") == installed_revisions
            and candidate.get("installed_dependency_tracked_changes") == installed_tracked_changes):
        previous = candidate
previous_results = {r["file"]: r for r in previous.get("modules", [])}
reusable = set()
for source in modules:
    target = project / ".lake/build/lib/lean" / Path(source).with_suffix(".olean")
    old = previous_results.get(source, {})
    if (source not in {"MagHK.lean", "Audit.lean"}
            and source not in previous.get("sources_changed_during_run", [])
            and old.get("exit_code") == 0
            and previous.get("source_sha256", {}).get(source) == input_hashes[source]
            and dependencies[source] <= reusable
            and target.exists()
            and target.stat().st_mtime_ns >= (project / source).stat().st_mtime_ns):
        digest = hashlib.sha256(target.read_bytes()).hexdigest()
        if old.get("olean_sha256") == digest:
            reusable.add(source)


def check_module(source):
    target = project / ".lake/build/lib/lean" / Path(source).with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    if source in reusable:
        digest = hashlib.sha256(target.read_bytes()).hexdigest()
        if digest != previous_results[source]["olean_sha256"]:
            return {"file": source, "exit_code": 1, "seconds": 0}, "Reusable artifact changed.\n"
        return {"file": source, "exit_code": 0, "seconds": 0,
                "reused_from": previous["timestamp_utc"],
                "olean_sha256": digest}, ""
    command = [sys.executable, str(project / "lean_local.py"), "-o", str(target), source]
    start = time.monotonic()
    run = subprocess.run(command, cwd=project, text=True, encoding="utf-8", stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT)
    duration = round(time.monotonic() - start, 3)
    result = {"file": source, "exit_code": run.returncode, "seconds": duration}
    if run.returncode == 0:
        result["olean_sha256"] = hashlib.sha256(target.read_bytes()).hexdigest()
    return result, run.stdout


pending = set(modules)
completed = set()
running = {}
failed = False
with ThreadPoolExecutor(max_workers=args.jobs) as executor:
    while pending or running:
        if not failed:
            for source in modules:
                if len(running) >= args.jobs:
                    break
                if source in pending and dependencies[source] <= completed:
                    print(f"{'Reusing checked' if source in reusable else 'Checking'} {source}", flush=True)
                    pending.remove(source)
                    running[executor.submit(check_module, source)] = source
        if not running:
            break
        finished, _ = wait(running, return_when=FIRST_COMPLETED)
        for future in finished:
            source = running.pop(future)
            result, output = future.result()
            results_by_source[source] = result
            outputs[source] = output
            print(f"Finished {source}, exit {result['exit_code']}", flush=True)
            if output:
                print(output, end="", flush=True)
            if result["exit_code"]:
                failed = True
            else:
                completed.add(source)

results = [results_by_source[source] for source in modules if source in results_by_source]
log = [f"Checking {r['file']}\n{outputs[r['file']]}\nExit code {r['exit_code']}\n"
       for r in results]

passed = len(results) == len(modules) and all(r["exit_code"] == 0 for r in results)
expected_audit_modules = {Path(source).with_suffix("").as_posix().replace("/", ".")
                          for source in sources if source != "Audit.lean"}
audit_match = re.search(r"AUDIT_MODULES ([A-Za-z0-9_.,]+)", outputs.get("Audit.lean", ""))
actual_audit_modules = set(audit_match.group(1).split(",")) if audit_match else set()
if actual_audit_modules != expected_audit_modules:
    passed = False
    log.append("Imported module audit does not match the project source set.\n"
               + "Missing modules " + ", ".join(sorted(expected_audit_modules - actual_audit_modules))
               + "\nUnexpected modules " + ", ".join(sorted(actual_audit_modules - expected_audit_modules)))
changed = [source for source in input_hashes
           if not (project / source).exists()
           or hashlib.sha256((project / source).read_bytes()).hexdigest() != input_hashes[source]]
final_sources = discover_sources()
if final_sources != sources:
    changed.extend(sorted(final_sources.symmetric_difference(sources)))
if not manuscript_path.exists() or hashlib.sha256(manuscript_path.read_bytes()).hexdigest() != manuscript_hash:
    changed.append(manuscript_relative)
if changed:
    passed = False
    log.append("Source changed during verification. Run again after edits finish.\n" + "\n".join(changed))
for package in manifest["packages"]:
    dependency_path = project / manifest["packagesDir"] / package["name"]
    head = subprocess.check_output(
        ["git", "-C", str(dependency_path), "rev-parse", "HEAD"],
        text=True, encoding="utf-8").strip()
    changes_now = subprocess.check_output(
        ["git", "-C", str(dependency_path), "status", "--porcelain", "--untracked-files=no"],
        text=True, encoding="utf-8", env=git_environment).splitlines()
    if (head != installed_revisions[package["name"]]
            or changes_now != installed_tracked_changes[package["name"]]):
        passed = False
        log.append(f"Dependency checkout changed during verification. {package['name']}\n")
for name, digest in compiler_inputs.items():
    if not (project / name).exists() or hashlib.sha256((project / name).read_bytes()).hexdigest() != digest:
        passed = False
        log.append(f"Compiler input changed during verification. {name}\n")
for result in results:
    target = project / ".lake/build/lib/lean" / Path(result["file"]).with_suffix(".olean")
    if result["exit_code"] == 0 and (not target.exists()
            or hashlib.sha256(target.read_bytes()).hexdigest() != result["olean_sha256"]):
        passed = False
        log.append(f"Compiled artifact changed during verification. {result['file']}\n")
if (coverage_path.read_bytes() if coverage_path.exists() else b"") != coverage_bytes:
    coverage_reviewed = False
    log.append("Coverage review changed during verification.\n")
audit_counts = re.search(r"AUDIT PASSED\. (\d+) theorems and (\d+) definitions\.",
                         outputs.get("Audit.lean", ""))
report = {
    "timestamp_utc": datetime.now(timezone.utc).isoformat(),
    "manuscript": manuscript_relative,
    "manuscript_sha256": manuscript_hash,
    "toolchain": (project / "lean-toolchain").read_text(encoding="utf-8").strip(),
    "compiler_version": compiler_version,
    "compiler_inputs": compiler_inputs,
    "parallel_jobs": args.jobs,
    "mathlib_revision": mathlib_revision,
    "installed_mathlib_revision": mathlib_head,
    "installed_dependency_revisions": installed_revisions,
    "installed_dependency_tracked_changes": installed_tracked_changes,
    "lean_checks_passed": passed,
    "full_manuscript_verification": passed and coverage_reviewed,
    "coverage_review_matches_sources": coverage_reviewed,
    "coverage_review_sha256": hashlib.sha256(coverage_bytes).hexdigest() if coverage_bytes else None,
    "coverage_scope": coverage.get("scope"),
    "coverage_explanation": (
        "Mathematical coverage is a separate reviewed claim, relative to the explicit "
        "background inputs in ASSUMPTIONS.txt. The axiom audit does not discharge "
        "those hypotheses or establish manuscript correspondence. See COVERAGE.txt."
    ),
    "audited_theorems": int(audit_counts.group(1)) if audit_counts else None,
    "audited_definitions": int(audit_counts.group(2)) if audit_counts else None,
    "modules": results,
    "audited_imported_modules": sorted(actual_audit_modules),
    "source_sha256": input_hashes,
    "sources_changed_during_run": changed,
}
(project / "verification.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
(project / "verification.log").write_text("\n".join(log), encoding="utf-8")
print("All Lean checks and the axiom audit passed." if passed else "Verification failed.")
sys.exit(0 if passed else 1)

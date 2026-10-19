"""Exercise verifier plumbing with synthetic modules, without Lean or network access.

Run with ``python -m unittest discover -s JSP-draft/lean_gpt -p test_verifier.py``.
Fixtures stay under .lake and never overwrite the project's verification reports.
These tests do not check mathematical proofs.
"""

import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import unittest
from unittest.mock import patch
from uuid import uuid4


PROJECT = Path(__file__).resolve().parent
REVISION = "1" * 40
DIAGNOSTIC = "Unicode diagnostic ∀ ψ ∈ ℂ, ψ†ψ ∈ ℝ"
COMPILER_STUB = '''\
from pathlib import Path
import sys

target, source, mode = sys.argv[1:]
sys.stdout.buffer.write(("Unicode diagnostic ∀ ψ ∈ ℂ, ψ†ψ ∈ ℝ\\n").encode("utf-8"))
if mode == "failure" and source == "MagHK/Example.lean":
    sys.exit(7)
Path(target).write_bytes(("synthetic artifact " + source).encode("utf-8"))
if source == "Audit.lean":
    modules = "MagHK" if mode == "omitted" else "MagHK,MagHK.Example"
    sys.stdout.buffer.write(("AUDIT_MODULES " + modules + "\\n").encode("utf-8"))
    sys.stdout.buffer.write(b"AUDIT PASSED. 1 theorems and 0 definitions.\\n")
'''


class VerifierTests(unittest.TestCase):
    def setUp(self):
        self.fixture_parent = (PROJECT / ".lake").resolve()
        if self.fixture_parent.parent != PROJECT:
            raise RuntimeError("Fixture directory must remain within the project")
        self.fixture_parent.mkdir(exist_ok=True)
        self.fixture = self.fixture_parent / ("test-verifier-" + uuid4().hex[:12])
        self.fixture.mkdir()
        self.addCleanup(self.remove_fixture)
        self.project = self.fixture / "project with spaces"
        self.project.mkdir()
        for name in ("verify.py", "lean_local.py"):
            shutil.copyfile(PROJECT / name, self.project / name)
        self.write("lake-manifest.json", json.dumps({
            "packagesDir": ".lake/packages",
            "packages": [{"name": "mathlib", "rev": REVISION}],
        }))
        self.write("lean-toolchain", "leanprover/lean4:v4.test\n")
        self.write("MagHK/Example.lean", "theorem sample : True := by trivial\n")
        self.write("MagHK.lean", "import MagHK.Example\n")
        self.write("Audit.lean", "import MagHK\n")
        self.manuscript = self.fixture / "submission-Oct2026/LaestadiusCsirik_HK.tex"
        self.manuscript.parent.mkdir()
        self.manuscript.write_text("Synthetic manuscript fixture\n", encoding="utf-8")
        self.write("coverage-review.json", json.dumps({
            "mathematical_coverage_complete": True,
            "manuscript": "../submission-Oct2026/LaestadiusCsirik_HK.tex",
            "manuscript_sha256": hashlib.sha256(self.manuscript.read_bytes()).hexdigest(),
            "source_sha256": {
                name: hashlib.sha256((self.project / name).read_bytes()).hexdigest()
                for name in ("Audit.lean", "MagHK.lean", "MagHK/Example.lean")
            },
            "scope": "Synthetic fixture, not mathematical evidence",
        }))
        self.compiler = self.fixture / "compiler stub.py"
        self.compiler.write_text(COMPILER_STUB, encoding="utf-8")
        self.compiled = []

    def write(self, relative, text):
        path = self.project / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8", newline="\n")

    def remove_fixture(self):
        # Resolve and check the exact recursive deletion target immediately before use.
        target = self.fixture.resolve()
        parent = self.fixture_parent.resolve()
        if (parent.parent != PROJECT or target.parent != parent
                or not target.name.startswith("test-verifier-")):
            raise RuntimeError("Refusing cleanup outside the project's fixture directory")
        shutil.rmtree(target)

    def run_verifier(self, mode="success"):
        real_run = subprocess.run

        def check_output(command, **kwargs):
            if command[0] == "git":
                if command[-2:] == ["rev-parse", "HEAD"]:
                    return REVISION + "\n"
                if "status" in command:
                    return ""
            elif command[-1] == "--version":
                return "Lean synthetic compiler\n"
            self.fail(f"Unexpected subprocess {command!r}")

        def compile_module(command, **kwargs):
            self.assertEqual(command[:2], [sys.executable, str(self.project / "lean_local.py")])
            self.assertEqual(command[2], "-o")
            self.compiled.append(command[-1])
            return real_run([sys.executable, str(self.compiler), *command[3:], mode], **kwargs)

        output_bytes = io.BytesIO()
        error_bytes = io.BytesIO()
        with (io.TextIOWrapper(output_bytes, encoding="cp1252") as output,
              io.TextIOWrapper(error_bytes, encoding="cp1252") as errors,
              contextlib.redirect_stdout(output), contextlib.redirect_stderr(errors),
              patch.object(sys, "argv", [str(self.project / "verify.py"), "--jobs", "1"]),
              patch("subprocess.check_output", side_effect=check_output),
              patch("subprocess.run", side_effect=compile_module)):
            with self.assertRaises(SystemExit) as stopped:
                runpy.run_path(str(self.project / "verify.py"), run_name="__main__")
            output.flush()
            console = output_bytes.getvalue().decode("utf-8")
        report = json.loads((self.project / "verification.json").read_text(encoding="utf-8"))
        log = (self.project / "verification.log").read_bytes().decode("utf-8")
        return stopped.exception.code, report, log, console

    def test_nested_modules_and_unicode_survive_complete_run(self):
        status, report, log, console = self.run_verifier()
        self.assertEqual(status, 0)
        self.assertTrue(report["lean_checks_passed"])
        self.assertTrue(report["full_manuscript_verification"])
        self.assertEqual(self.compiled, ["MagHK/Example.lean", "MagHK.lean", "Audit.lean"])
        self.assertEqual(set(report["source_sha256"]), set(self.compiled))
        self.assertEqual(report["audited_imported_modules"], ["MagHK", "MagHK.Example"])
        self.assertIn(DIAGNOSTIC, log)
        self.assertIn(DIAGNOSTIC, console)

    def test_successful_compilation_cannot_hide_an_omitted_audit_module(self):
        status, report, log, _ = self.run_verifier("omitted")
        self.assertEqual(status, 1)
        self.assertFalse(report["lean_checks_passed"])
        self.assertFalse(report["full_manuscript_verification"])
        self.assertTrue(all(module["exit_code"] == 0 for module in report["modules"]))
        self.assertIn("Missing modules MagHK.Example", log)

    def test_compiler_failure_blocks_dependents_and_preserves_diagnostics(self):
        status, report, log, _ = self.run_verifier("failure")
        self.assertEqual(status, 1)
        self.assertFalse(report["lean_checks_passed"])
        self.assertFalse(report["full_manuscript_verification"])
        self.assertEqual(self.compiled, ["MagHK/Example.lean"])
        self.assertEqual(report["modules"][0]["exit_code"], 7)
        self.assertIn(DIAGNOSTIC, log)

    def test_wrapper_preserves_arguments_environment_and_compiler_exit_status(self):
        dependency = self.project / ".lake/packages/mathlib/.lake/build/lib/lean"
        dependency.mkdir(parents=True)
        executable = str(self.fixture / "toolchain with spaces/lean.exe")
        arguments = ["-o", str(self.fixture / "output with spaces.olean"), "MagHK/Example.lean"]
        previous_directory = Path.cwd()
        try:
            for status in (0, 7):
                with (self.subTest(status=status),
                      patch.object(sys, "argv", [str(self.project / "lean_local.py"), *arguments]),
                      patch("subprocess.check_output", return_value=executable + "\n"),
                      patch("subprocess.run", return_value=subprocess.CompletedProcess([], status)) as run,
                      patch("os.execve", side_effect=AssertionError("Use subprocess.run on Windows"))):
                    with self.assertRaises(SystemExit) as stopped:
                        runpy.run_path(str(self.project / "lean_local.py"), run_name="__main__")
                    self.assertEqual(stopped.exception.code, status)
                    command = run.call_args.args[0]
                    self.assertEqual(command, [executable, "-DautoImplicit=false",
                                               "-DrelaxedAutoImplicit=false", *arguments])
                    environment = run.call_args.kwargs["env"]
                    self.assertEqual(environment["ELAN_TOOLCHAIN"], "leanprover/lean4:v4.test")
                    self.assertEqual(environment["LEAN_PATH"].split(os.pathsep), [
                        str(self.project / ".lake/build/lib/lean"),
                        str(self.project), str(dependency.resolve()),
                    ])
        finally:
            os.chdir(previous_directory)


if __name__ == "__main__":
    unittest.main()

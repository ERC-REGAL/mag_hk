Lean verification of LaestadiusCsirik_HK.tex

This project formalizes the manuscript's mathematical results and proof
calculations relative to explicit standard background results. Read
COVERAGE.txt for the manuscript correspondence and ASSUMPTIONS.txt for the
precise trust boundary and necessary domain interpretations. LAST_RUN.txt
and verification.json record the actual build and source-consistency
result. NEXT_STEPS.txt records any unfinished checks.

The library and namespace are MagHK. The target manuscript is
../submission-Oct2026/LaestadiusCsirik_HK.tex. The October submission update
preserves the existing standard background assumptions. The latest review
covers the final editorial changes and embedded figures, with the original
Lean proofs unchanged.
See SOURCE_REVIEW.txt for the comparison with the previously checked draft.

The project does not modify the manuscript. Verification reports identify
the exact checked version by its path and SHA-256 hash.

Reproduce the checks

    cd lean_gpt
    python3 verify.py

On Windows, use python instead of python3 in these commands. The scripts
use portable module paths and UTF-8 for compiler output and reports.

To test the Python wrappers without compiling the Lean proofs, run
python -m unittest test_verifier.py from this folder. These tests use
temporary synthetic projects and preserve the existing verification reports.

The script checks every project module using the pinned Lean compiler,
with independent modules checked in parallel. It then audits transitive axiom dependencies. It writes verification.log and
verification.json, including the manuscript and Lean-source SHA-256 hashes.
A separate coverage-review.json records the manuscript correspondence review
and its exact Lean source snapshot. The full-verification flag requires both
a completed coverage review matching the manuscript path, manuscript hash
and Lean source hashes, together with a passing consistent Lean run.
It exits unsuccessfully if any module or the audit fails.

For a later run after a small edit, previously checked modules can be
reused when their source, dependencies, compiler and compiled artifacts
are unchanged.

    python3 verify.py --reuse-checked

The umbrella import and axiom audit are always rerun. The report marks
each reused module and records its artifact hash. The default command
above rebuilds every module.
Reports without artifact hashes cannot supply reusable results. Changes
to the compiler invocation, verification script, dependency pins or an
imported project module also prevent reuse. Keep the Lean sources and
dependency cache unchanged during a run.

On a fresh machine, install Python 3, Git and elan and make their commands
available on PATH. Keep the supplied lean-toolchain, lakefile.toml and
lake-manifest.json together. From this folder in Windows PowerShell, install
the recorded Lean version and fetch the pinned dependency cache.

    $pinnedToolchain = (Get-Content -LiteralPath lean-toolchain -Raw).Trim()
    elan toolchain install $pinnedToolchain
    elan run $pinnedToolchain lake exe cache get
    python lean_local.py --version

The recorded toolchain is leanprover/lean4:v4.34.0-rc2. Lake is included
with that toolchain. The cache command obtains missing dependency checkouts
at the revisions recorded in lake-manifest.json and downloads their compiled
artifacts. It may first build the cache executable. A separate lake build
is unnecessary before verify.py, which compiles the project modules itself.

Do not run lake update or add --update when reproducing this snapshot.
Those commands resolve dependency versions again and can rewrite the
manifest. The verifier checks every installed dependency against its recorded
revision. The pinned Lake documentation describes manifest reuse here.
https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/lake/README.md#adding-dependencies

The .lake/packages directory contains dependency sources and their compiled
cache and is ignored by Git. lean_local.py reads the installed cache without
changing it and avoids Lake's metadata writes in a shared cache. No absolute
cache path is stored in the tracked project configuration.

The current Windows setup uses a directory junction at .lake/packages to a
local cache outside Proton Drive. That cache was initialized from copies of
the three pinned configuration files. The normal project commands above
can use it through the junction.

The release contains sibling lean_gpt and submission-Oct2026 directories.
Keep their relative layout so the verifier can locate the checked manuscript.
In the development repository these directories are under JSP-draft.

Git attributes preserve LF line endings for the manuscript and Lean sources.
The recorded SHA-256 hashes refer to exact file bytes. The historical review
and report remain in history/2026-10-19T053931Z. Their manuscript hash describes
the earlier snapshot, not the current manuscript.

Trust and interpretation

Audit.lean inspects every declaration originating in imported project
modules, including private declarations and other namespaces. It allows only
Lean's usual propext, Classical.choice, and Quot.sound axioms. It rejects
sorryAx and any additional axioms. An explicit theorem hypothesis is not
an axiom dependency. The verifier also checks that the audit environment
actually imported every discovered source module. Passing this audit
does not prove such hypotheses, and it does not establish that every
manuscript assertion is represented.

No floating-point calculation is used as proof of an inequality.
The monopole gap uses rational bounds and exact square-root identities.
The printed Gaussian parameter is enclosed by polynomial integral bounds
and exact rational arithmetic.

The verification targets the exact manuscript identified by the hash in
verification.json. Changes to the manuscript require a new coverage review.

Audit regression check

An unused private axiom was deliberately placed in a temporary module.
The audit rejected it. The temporary sources and artifacts were then
removed. This historical regression check predates the module rename.
Its log is not included in this release. The current run executes the
complete audit again, as recorded in verification.log.

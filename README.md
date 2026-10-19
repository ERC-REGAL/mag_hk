# Counterexamples to the total-current Hohenberg--Kohn conjecture

Lean 4 formalization accompanying the paper by A. Laestadius and M. A. Csirik (2026).

The version cited in the paper is the Git tag [`v1`](https://github.com/ERC-REGAL/mag_hk/tree/v1).
The exact manuscript source is [LaestadiusCsirik_HK.tex](submission-Oct2026/LaestadiusCsirik_HK.tex), including both figure definitions and the bibliography.

The recorded fresh run completed on 2026-10-19 and compiled all 141 source files. Its axiom audit passed for 2,043 theorems and 966 definitions. [LAST_RUN.txt](lean_gpt/LAST_RUN.txt) and [verification.json](lean_gpt/verification.json) identify the exact manuscript and checked source bytes.

## Scope

The main results and supporting mathematical arguments are represented in the Lean library [MagHK](lean_gpt/MagHK). They hold relative to explicit standard background results from operator theory, elliptic regularity, unique continuation and geometry. These enter as theorem hypotheses, including structures named `Standard...Library`. They have not all been derived from first principles in Lean.

[ASSUMPTIONS.txt](lean_gpt/ASSUMPTIONS.txt) states this boundary and the required domain interpretations. [COVERAGE.txt](lean_gpt/COVERAGE.txt) maps manuscript claims to the formalization. [SOURCE_REVIEW.txt](lean_gpt/SOURCE_REVIEW.txt) records the separate correspondence review. Schematic figures, bibliography, historical and editorial assertions are outside formal coverage.

| Paper | LaTeX label | Lean module or declaration |
|---|---|---|
| Proposition 2.1 | `prop:one-particle` | `MagHK/OneParticleTheorem.lean` |
| Lemma 2.2 | `lem:time-reversal` | `MagHK/ManyBodyTimeReversal.lean` |
| Theorem 3.1 | `thm:noninteracting` | `MagHK.NoninteractingTheorem.bounded_counterexample` and `gaussian_counterexample` |
| Eq. (23) | `eq:margin` | `MagHK/Noninteracting.lean` |
| Remark 3.3 | `rem:spin` | `MagHK/PassiveSpinCounterexample.lean` |
| Theorem 4.1 | `thm:monopole` | `MagHK.MonopoleCounterexample.exists_pair` and `MagHK.MonopoleSubmission.exists_pair` |
| Eq. (31) | `eq:angular-determinant` | `MagHK.MonopoleSubmission.angular_determinant_display` |
| Lemma A.1 | `lem:ordering` | `MagHK.OrderingTheorem.lowest_two_planar_levels` |
| Lemma B.1 | `lem:monopole-domains` | `MagHK/MonopoleEndpointDomains.lean` |

All module paths in the table are relative to `lean_gpt`.

## Reproduce the verification

Install Git, Python 3 and Lean through [elan](https://lean-lang.org/install/). Keep several GB of disk space available for the dependency cache.

```
git clone --branch v1 https://github.com/ERC-REGAL/mag_hk.git
cd mag_hk/lean_gpt
lake exe cache get
python verify.py --jobs 1
```

Use `python3` if that is the Python 3 command on your system. The single-worker setting limits simultaneous compiler memory use. `--jobs 4` can speed up the run when sufficient memory is available.

Lean is pinned to `v4.34.0-rc2` and Mathlib to `85e3a25e006c35636f0e53b0e9296caca2685bc0`. Do not run `lake update`, which can replace the pinned dependency revisions.

The verifier compiles all project sources and runs [Audit.lean](lean_gpt/Audit.lean). The audit rejects project declarations that depend on axioms beyond `propext`, `Classical.choice` and `Quot.sound`, including proofs containing `sorry`. It does not discharge explicit theorem hypotheses or establish manuscript correspondence.

The verifier compares the manuscript path and hash and the Lean source hashes with the separate coverage review. It independently checks dependency revisions and records compiler inputs and compiled artifact hashes, checking that these remain unchanged during the run. It records the result in [verification.json](lean_gpt/verification.json) and [verification.log](lean_gpt/verification.log). [LAST_RUN.txt](lean_gpt/LAST_RUN.txt) describes the recorded run. The `full_manuscript_verification` flag means the compiler checks passed and the reviewed snapshot matches, within the scope and interpretations stated above.

Alternatively, `lake build` from `lean_gpt` compiles the library and runs the axiom audit, without generating the manuscript-associated verification report. Open `lean_gpt` in VS Code with the Lean 4 extension to browse the proofs. [README.txt](lean_gpt/README.txt) gives further setup details.

The reports include SHA-256 checksums of exact source bytes. Git attributes preserve the verified source line endings. The earlier review and report are retained in [history](lean_gpt/history/2026-10-19T053931Z) and describe an older manuscript snapshot.

## License

The formalization, scripts and documentation in `lean_gpt` are released under [CC0 1.0 Universal](lean_gpt/LICENSE). This dedication does not include the manuscript in `submission-Oct2026`. See the root [license scope notice](LICENSE).

## Funding

This formalization is part of the ERC project [REGAL](https://github.com/ERC-REGAL/REGAL). Funded by the European Union (ERC, REGAL, 101041487). Views and opinions expressed are however those of the author(s) only and do not necessarily reflect those of the European Union or the European Research Council Executive Agency. Neither the European Union nor the granting authority can be held responsible for them.

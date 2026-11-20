# Verification record

The recorded November 18–19, 2026 dependency-aware verification covered 643 source modules and 647 axiom checks, including 33 manuscript correspondence checks. It reused 573 hash-checked unchanged modules and compiled 70 new or invalidated modules. This was an authenticated incremental build, not a clean rebuild.

After the reader-order revision, `ACS12/Paper.lean` was re-elaborated successfully against the verified dependency artifacts: 33 axiom checks passed; the other 642 proof modules were unchanged. The subsequent terminology revision changed the manuscript, not the mathematical proof code.

The recorded axiom audits reported only `propext`, `Classical.choice`, and `Quot.sound`. Publication packaging did not rerun the full Lean build. `MANIFEST.sha256` identifies the published source and paper files; the build commands in README allow an independent rebuild.

# Asterism formalizations

Lean developments accompanying mathematical papers by Chih-Yao Wu. Each project is an independent, version-pinned Lean package with its own paper, build instructions, and verification scope.

| Project | Formalized result | Start here |
| --- | --- | --- |
| ACS12 | Equal-mass regular-polygon classification for centered cocircular configurations, all `α ≥ 0` and `n ≥ 2` | [Project and paper](projects/acs12) |
| Five-body finiteness | Finiteness of planar Newtonian central configurations for each fixed set of five positive masses | [Project and paper](projects/five-body-finiteness) |

Build from the individual project directory, not the repository root. The projects need not use the same Lean or Mathlib version. To cite a verified snapshot, link to a commit or project-specific tag rather than the moving `main` branch.

AI agents produced these developments under the author's coordination. The project documentation states what was checked, how the formal theorem relates to the manuscript, and the current human-review status. A successful Lean check establishes the formal statement relative to its definitions and axioms.

The existing [five-body repository](https://github.com/andersonwu2000/five-body-finiteness) remains available. This repository contains publication material, not the private research workspace.

## Versions and licensing

Initial collection: November 20, 2026. See each project's verification record and `MANIFEST.sha256`. Licenses are project-specific: the five-body software retains Apache-2.0; the papers are CC BY 4.0. There is no blanket software license for the whole collection.

Contact: Chih-Yao Wu — andersonwu2000@gmail.com.

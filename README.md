<div align="center">

# Transient Structure at Solar Rigidity Interfaces and the Exceptional Point of the Dynamo Wave: An Operator-First Study of the Sun — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/suns-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/suns-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-15-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.21895551-blue)](https://doi.org/10.5281/zenodo.21895551)

Jeromie Beasley

</div>

---

## The idea in one line

The paper's results are graded computations. This repository proves the exact mathematics
those computations measure: the square-root law at an exceptional point, the pair exchange
that a loop around it records, the single-valued ledger, and the gap between modal decay and
transient growth in one damped operator.

## What is proved

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Sec. 4, EP birth | `J(δ) = [[0,1],[δ,0]]` has right eigenvectors `(1, ±√δ)` and left eigenvectors `(±√δ, 1)` | `J_right_eigen`, `J_left_eigen` |
| Square-root law | `κ(δ) = (1+δ)/(2√δ)`, so `κ√δ → 1/2` and `κ → ∞` as `δ → 0⁺` | `kappa_eq`, `sqrt_law`, `kappa_diverges` |
| Integer record | The branch `√r e^{iθ/2}` squares to `r e^{iθ}`, is exchanged after one loop (`z(2π) = −z(0)`) and restored after two (`z(4π) = z(0)`) | `branch_sq`, `exchange_one_loop`, `restore_two_loops` |
| Ledger through the EP | `(a+s)(a−s) = a² − δ` for either branch `±s`: the trace-log is single-valued | `ledger_branch_free` |
| Hair-rate ladder | `A = [[−ε,γ],[0,−ε]]` has the single eigenvalue `−ε` but numerical abscissa `−ε + |γ|/2` (bound and attainment); energy grows initially when `|γ| > 2ε` | `hair_modal`, `hair_abscissa_le`, `hair_abscissa_attained`, `hair_ladder` |
| Mode ratio | `λ/d = 2π/0.450 ∈ (13.96, 13.97)` | `mode_ratio` |
| Lane width | At `λ = 65` km, `2d > 9` km and `4d < 19` km | `lane_width` |

The file is [`Suns/Basic.lean`](Suns/Basic.lean). What is not proved is in
[`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and three deliberately false statements that must fail.

## The paper

*Transient Structure at Solar Rigidity Interfaces and the Exceptional Point of the Dynamo Wave: An Operator-First Study of the Sun*, Jeromie Beasley. DOI
[10.5281/zenodo.21895551](https://doi.org/10.5281/zenodo.21895551) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).

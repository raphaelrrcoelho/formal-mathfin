/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Single-asset market making — closed-form (Riccati) approximation

The multi-asset Avellaneda–Stoikov market-making problem of Bergault, Evangelista, Guéant
and Vieira (*Closed-form approximations in multi-asset market making*, arXiv:1810.04383)
reduces, via a quadratic (LQ) approximation of the trade-intensity Hamiltonians, to a
Riccati system whose solution is a closed-form proxy for the value function `θ(t, q)`.

Specialised here to a **single asset** (`d = 1`), we verify, in three layers:

* **Riccati coefficient** — `a(t) = Â · tanh (Â · (T − t))` solves `a' = a² − Â²`, `a(T) = 0`,
  and `a(0) → Â` as `T → ∞` (the ergodic regime).
* **Value function** — the quadratic ansatz `θ̌(t, q) = −A(t) q² − B(t) q − C(t)` solves the
  approximate Hamilton–Jacobi equation (the paper's Eq. 9) whenever `(A, B, C)` solve the
  Riccati/linear ODE system, with `A` the Riccati coefficient.
* **Quotes** — with the known exponential-intensity quote map `δ̃_ξ(p) = p + c`, the greedy
  bid/ask give a **constant** half-spread and an **inventory-linear** skew, for both the CARA
  (Model A) and risk-adjusted (Model B) objectives.

## Scope (mirroring `AlmgrenChriss.lean`)

We verify the closed-form solution of the **approximate** (quadratic-Hamiltonian) HJ equation.
Out of scope: the stochastic optimal-control substrate (existence/uniqueness of the true value
function solving the exact HJ equation, and the verification theorem linking `θ` to optimal
quotes — controlled marked-point-process control beyond the current pin); that the approximate
value function approximates the true one (justified numerically in the paper); the multi-asset
matrix-Riccati case; and deriving `δ̃_ξ` from the intensity sup (it is defined by its known
closed form from Guéant [18] / Guéant–Lehalle–Fernandez-Tapia [20]).
-/

@[expose] public section

namespace MathFin

open Real Filter Topology

end MathFin

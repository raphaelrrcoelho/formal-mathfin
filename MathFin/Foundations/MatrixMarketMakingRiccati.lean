/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.MarketMakingRiccati

/-!
# Multi-asset market making — the matrix Riccati closed form

The multi-asset Avellaneda–Stoikov market-making problem of Bergault, Evangelista, Guéant and
Vieira (*Closed-form approximations in multi-asset market making*, arXiv:1810.04383) reduces, via
a quadratic (LQ) approximation of the trade-intensity Hamiltonians, to a **matrix** Riccati
system (their Proposition 2). Its closed-form solution is the matrix analogue of the scalar
`a(t) = Â · tanh (Â (T − t))` verified in `MathFin.Foundations.MarketMakingRiccati`.

Mathlib carries neither a matrix `tanh` nor matrix-valued differentiation at this pin. We sidestep
both by **spectral reduction**: for a real symmetric (Hermitian) matrix `Â` with eigendecomposition
`Â = U · diag(λ) · Uᴴ` (`U = hÂ.eigenvectorUnitary`, `λ = hÂ.eigenvalues`), we *define* the matrix
Riccati coefficient in already-diagonalised form using the scalar `riccatiCoeff`:

`matrixRiccatiCoeff hÂ T t = U · diag (fun i ↦ riccatiCoeff (λ i) T t) · Uᴴ`.

This equals `Â · tanh (Â (T − t))` spectrally without ever constructing a matrix `tanh`, and the
matrix Riccati ODE `a' = a·a − Â·Â` reduces, on each eigenvalue, to the scalar identity
`hasDerivAt_riccatiCoeff` already proven.

## Where this sits (the Riccati is one, approximate, view)

The Riccati is the **LQ-approximation** view of optimal market making, not the fundamental structure.
For exponential order-arrival intensities the single-asset Avellaneda–Stoikov HJB equation is
*exactly* linearisable — a Hopf–Cole change of variables turns it into a **linear** ODE system
(Guéant–Lehalle–Fernandez-Tapia), i.e. a matrix-exponential object with no approximation. The exact
*multi-asset* problem has no closed form, which is precisely why BEGV quadratically approximate the
Hamiltonians to recover a solvable Riccati. So this module formalises the tractable approximate closed
form (the spectral route below); the **exact linearisation is the deeper, more faithful target**
(gated on matrix-exponential calculus, absent at this pin). Read the result as "this closed form solves
this approximate Riccati", not as "optimal market making, mechanised".

We verify, in two layers:

* **§1 Abstract matrix Riccati** — `matrixRiccatiCoeff` solves `a'(t) = a(t)·a(t) − Â·Â` with
  `a(T) = 0` (matrix-valued `HasDerivAt`, taken under the `L∞` operator norm — MathFin's committed
  instance; since `n` is finite the space is finite-dimensional, all norms are equivalent, and the
  derivative statement is norm-independent), for every Hermitian `Â`. This is the genuine multi-asset
  matrix `tanh`-Riccati closed form (an identification with `Â·tanh(Â(T−t))` made in prose under the
  Hermitian functional calculus — no matrix `tanh` object is built in Lean, the pin carrying none).
* **§2 Market-making instantiation** — with a positive diagonal `D₊` and a symmetric `Σ`, and `Â`
  the Hermitian square root scale `Â·Â = γ • (D₊^{½} Σ D₊^{½})`, the coefficient
  `A(t) = ½ • (D₊^{-½} · matrixRiccatiCoeff hÂ T t · D₊^{-½})` solves the market-making matrix
  Riccati `A'(t) = 2 • (A(t) D₊ A(t)) − (γ/2) • Σ` with `A(T) = 0` (the paper's Eq. 11 in matrix
  form).

## Scope (mirroring `MarketMakingRiccati.lean`)

We verify the closed-form solution of the **approximate** (quadratic-Hamiltonian) matrix Riccati
system. Out of scope: the stochastic optimal-control substrate (existence/uniqueness of the true
value function and the verification theorem linking it to optimal quotes); the `B(t)`/`C(t)`
closed forms (matrix variation-of-parameters / integrals) and the general-`d` value-function
verification; that the approximate value function approximates the true one; and the construction
of `Â` as a matrix square root (in §2 `Â` enters by its defining relation `Â·Â = γ • (D₊^{½}ΣD₊^{½})`,
so the content is the change of variables, not matrix-square-root existence).
-/

@[expose] public section

namespace MathFin

open Real Matrix
open scoped Matrix.Norms.Operator

/- MathFin commits to the `L∞` operator norm as *the* norm on square matrices (the only matrix norm
the library uses), so downstream consumers — and the benchmark snippets that re-export the results
below — get `NormedAddCommGroup`/`NormedSpace (Matrix n n ℝ)` without re-opening the scope. Mathlib
keeps these `scoped` only because three matrix norms compete upstream; MathFin has no such conflict,
so promoting them to global instances introduces no diamond. -/
attribute [instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## §1  Abstract matrix Riccati closed form (spectral reduction) -/

/-- **Matrix Riccati coefficient** `a(t) = U · diag (riccatiCoeff (λᵢ) T t) · Uᴴ`, the spectral
closed form of the normalised matrix Riccati equation `a' = a·a − Â·Â` with terminal value
`a(T) = 0`. Here `U = hÂ.eigenvectorUnitary` and `λ = hÂ.eigenvalues` diagonalise the Hermitian
`Â`, and `riccatiCoeff` is the scalar `Âᵢ · tanh (Âᵢ (T − t))`. -/
noncomputable def matrixRiccatiCoeff {Â : Matrix n n ℝ} (hÂ : Â.IsHermitian) (T t : ℝ) :
    Matrix n n ℝ :=
  (hÂ.eigenvectorUnitary : Matrix n n ℝ) *
    diagonal (fun i => riccatiCoeff (hÂ.eigenvalues i) T t) *
    star (hÂ.eigenvectorUnitary : Matrix n n ℝ)

/-- **Terminal condition**: `a(T) = 0`. -/
theorem matrixRiccatiCoeff_terminal {Â : Matrix n n ℝ} (hÂ : Â.IsHermitian) (T : ℝ) :
    matrixRiccatiCoeff hÂ T T = 0 := by
  unfold matrixRiccatiCoeff
  simp [riccatiCoeff_terminal]

/-- **Spectral form of `Â²`**: `Â · Â = U · diag (λᵢ²) · Uᴴ`. The conjugation `M ↦ U · M · Uᴴ` is a
`⋆`-algebra homomorphism, so `Â · Â = (U · diag λ · Uᴴ)² = U · diag λ² · Uᴴ` by `map_mul`. -/
theorem matrixRiccatiCoeff_spectral_sq {Â : Matrix n n ℝ} (hÂ : Â.IsHermitian) :
    Â * Â = (hÂ.eigenvectorUnitary : Matrix n n ℝ) *
      diagonal (fun i => (hÂ.eigenvalues i) ^ 2) *
      star (hÂ.eigenvectorUnitary : Matrix n n ℝ) := by
  conv_lhs => rw [hÂ.spectral_theorem]
  rw [← map_mul, diagonal_mul_diagonal, Unitary.conjStarAlgAut_apply]
  congr 2
  funext i
  simp [Function.comp, sq]

/-- **Symmetry**: the matrix Riccati coefficient is Hermitian (its diagonal core is real, and
conjugation by a unitary preserves Hermitian-ness) — the value function's Hessian is symmetric. -/
theorem matrixRiccatiCoeff_isHermitian {Â : Matrix n n ℝ} (hÂ : Â.IsHermitian) (T t : ℝ) :
    (matrixRiccatiCoeff hÂ T t).IsHermitian := by
  unfold matrixRiccatiCoeff
  rw [star_eq_conjTranspose]
  exact isHermitian_mul_mul_conjTranspose _ (isHermitian_diagonal _)

/-- **Matrix Riccati ODE**: `a'(t) = a(t)·a(t) − Â·Â` (matrix-valued derivative under the `L∞`
operator norm). The `t`-dependence lives entirely in the diagonal core; its derivative is
`diag (riccatiCoeff (λᵢ)² − λᵢ²)` by the scalar `hasDerivAt_riccatiCoeff`, and conjugating by the
constant `U`, `Uᴴ` and re-collapsing (`star U · U = 1`, `map_mul`) turns `U · diag(riccatiCoeff² − λ²) · Uᴴ`
into `a·a − Â·Â`. -/
theorem hasDerivAt_matrixRiccatiCoeff {Â : Matrix n n ℝ} (hÂ : Â.IsHermitian) (T t : ℝ) :
    HasDerivAt (matrixRiccatiCoeff hÂ T)
      (matrixRiccatiCoeff hÂ T t * matrixRiccatiCoeff hÂ T t - Â * Â) t := by
  set U : Matrix n n ℝ := (hÂ.eigenvectorUnitary : Matrix n n ℝ) with hU
  -- derivative of the diagonal core (Pi-derivative lifted through `diagonalLinearMap`)
  have hD : HasDerivAt (fun s => diagonal (fun i => riccatiCoeff (hÂ.eigenvalues i) T s))
      (diagonal (fun i => riccatiCoeff (hÂ.eigenvalues i) T t ^ 2 - (hÂ.eigenvalues i) ^ 2)) t := by
    have hpi : HasDerivAt (fun s => (fun i => riccatiCoeff (hÂ.eigenvalues i) T s : n → ℝ))
        (fun i => riccatiCoeff (hÂ.eigenvalues i) T t ^ 2 - (hÂ.eigenvalues i) ^ 2) t :=
      hasDerivAt_pi.2 (fun i => hasDerivAt_riccatiCoeff (hÂ.eigenvalues i) T t)
    have hL := (Matrix.diagonalLinearMap (R := ℝ) (n := n) (α := ℝ)).toContinuousLinearMap.hasFDerivAt
      (x := (fun i => riccatiCoeff (hÂ.eigenvalues i) T t : n → ℝ))
    -- `exact` (not `simpa`) bridges the operator-norm `AddCommGroup`, defeq to the default instance
    have h2 := hL.comp_hasDerivAt t hpi
    simp only [Function.comp_def] at h2
    exact h2
  -- conjugate by the constant unitary; derivative is `U · diag(riccatiCoeff² − λ²) · Uᴴ`
  have hderiv : HasDerivAt (matrixRiccatiCoeff hÂ T)
      (U * diagonal (fun i => riccatiCoeff (hÂ.eigenvalues i) T t ^ 2 - (hÂ.eigenvalues i) ^ 2)
        * star U) t :=
    (hD.const_mul U).mul_const (star U)
  -- rewrite the target derivative into that spectral form
  have hsq : matrixRiccatiCoeff hÂ T t * matrixRiccatiCoeff hÂ T t
      = U * diagonal (fun i => riccatiCoeff (hÂ.eigenvalues i) T t ^ 2) * star U := by
    have e1 : matrixRiccatiCoeff hÂ T t
        = Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hÂ.eigenvectorUnitary
            (diagonal (fun i => riccatiCoeff (hÂ.eigenvalues i) T t)) := rfl
    have hfg : (fun i => riccatiCoeff (hÂ.eigenvalues i) T t * riccatiCoeff (hÂ.eigenvalues i) T t)
        = fun i => riccatiCoeff (hÂ.eigenvalues i) T t ^ 2 :=
      funext fun i => (pow_two (riccatiCoeff (hÂ.eigenvalues i) T t)).symm
    rw [e1, ← map_mul, diagonal_mul_diagonal, Unitary.conjStarAlgAut_apply, hfg]
  rw [show matrixRiccatiCoeff hÂ T t * matrixRiccatiCoeff hÂ T t - Â * Â
      = U * diagonal (fun i => riccatiCoeff (hÂ.eigenvalues i) T t ^ 2 - (hÂ.eigenvalues i) ^ 2)
          * star U from ?_]
  · exact hderiv
  · rw [hsq, matrixRiccatiCoeff_spectral_sq hÂ, ← hU, ← sub_mul, ← mul_sub, ← diagonal_sub]

/-! ## §2  Market-making instantiation (the paper's matrix Riccati, Eq. 11) -/

/-- **Market-making matrix value coefficient** `A(t) = ½ • (D₊^{-½} · a(t) · D₊^{-½})`, the change
of variables that turns the normalised matrix Riccati `a` (`matrixRiccatiCoeff`) into the solution
of the market-making matrix Riccati `A' = 2 A D₊ A − (γ/2) Σ`. Here `D₊ = diagonal d` is the
positive diagonal `(α₂ᵢᵇ + α₂ᵢᵃ)zⁱ` and `D₊^{-½} = diagonal (√dᵢ)⁻¹`. -/
noncomputable def mmMatrixValueCoeff (d : n → ℝ) {Â : Matrix n n ℝ} (hÂ : Â.IsHermitian)
    (T t : ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (diagonal (fun i => (Real.sqrt (d i))⁻¹) * matrixRiccatiCoeff hÂ T t
    * diagonal (fun i => (Real.sqrt (d i))⁻¹))

/-- **Terminal condition**: `A(T) = 0`. -/
theorem mmMatrixValueCoeff_terminal (d : n → ℝ) {Â : Matrix n n ℝ} (hÂ : Â.IsHermitian) (T : ℝ) :
    mmMatrixValueCoeff d hÂ T T = 0 := by
  unfold mmMatrixValueCoeff
  rw [matrixRiccatiCoeff_terminal]
  simp

/-- **Market-making matrix Riccati ODE**: `A'(t) = 2 • (A(t) D₊ A(t)) − (γ/2) • Σ`, with `D₊ =
diagonal d` positive and `Â` the Hermitian generator scale `Â·Â = γ • (D₊^{½} Σ D₊^{½})` (the
paper's `Â = √γ (D₊^{½}ΣD₊^{½})^{½}`). The change of variables collapses because
`D₊^{-½} D₊ D₊^{-½} = 1` and `D₊^{-½} Â² D₊^{-½} = γ Σ`, reducing everything to the abstract matrix
Riccati ODE `hasDerivAt_matrixRiccatiCoeff`. -/
theorem hasDerivAt_mmMatrixValueCoeff
    (d : n → ℝ) (hd : ∀ i, 0 < d i) (cov : Matrix n n ℝ) (γ : ℝ)
    {Â : Matrix n n ℝ} (hÂ : Â.IsHermitian)
    (hÂsq : Â * Â = γ • (diagonal (fun i => Real.sqrt (d i)) * cov
                          * diagonal (fun i => Real.sqrt (d i)))) (T t : ℝ) :
    HasDerivAt (mmMatrixValueCoeff d hÂ T)
      ((2 : ℝ) • (mmMatrixValueCoeff d hÂ T t * diagonal d * mmMatrixValueCoeff d hÂ T t)
        - (γ / 2) • cov) t := by
  set S : Matrix n n ℝ := diagonal (fun i => Real.sqrt (d i)) with hS
  set Dm : Matrix n n ℝ := diagonal (fun i => (Real.sqrt (d i))⁻¹) with hDm
  have hpos : ∀ i, Real.sqrt (d i) ≠ 0 := fun i => Real.sqrt_ne_zero'.2 (hd i)
  have hDmS : Dm * S = 1 := by
    rw [hDm, hS, diagonal_mul_diagonal,
      show (fun i => (Real.sqrt (d i))⁻¹ * Real.sqrt (d i)) = (fun _ => (1 : ℝ)) from
        funext fun i => inv_mul_cancel₀ (hpos i), diagonal_one]
  have hSDm : S * Dm = 1 := by
    rw [hDm, hS, diagonal_mul_diagonal,
      show (fun i => Real.sqrt (d i) * (Real.sqrt (d i))⁻¹) = (fun _ => (1 : ℝ)) from
        funext fun i => mul_inv_cancel₀ (hpos i), diagonal_one]
  have hDmDDm : Dm * diagonal d * Dm = 1 := by
    rw [hDm, diagonal_mul_diagonal, diagonal_mul_diagonal,
      show (fun i => (Real.sqrt (d i))⁻¹ * d i * (Real.sqrt (d i))⁻¹) = (fun _ => (1 : ℝ)) from ?_,
      diagonal_one]
    funext i
    have h := hpos i
    field_simp
    rw [Real.sq_sqrt (hd i).le]
  have hconjCov : Dm * (S * cov * S) * Dm = cov := by
    rw [Matrix.mul_assoc S cov S, ← Matrix.mul_assoc Dm S (cov * S), hDmS, Matrix.one_mul,
      Matrix.mul_assoc cov S Dm, hSDm, Matrix.mul_one]
  -- derivative from M1, conjugated by the constant `Dm` and scaled by ½
  have hderiv : HasDerivAt (mmMatrixValueCoeff d hÂ T)
      ((1 / 2 : ℝ) • (Dm *
        (matrixRiccatiCoeff hÂ T t * matrixRiccatiCoeff hÂ T t - Â * Â) * Dm)) t :=
    (((hasDerivAt_matrixRiccatiCoeff hÂ T t).const_mul Dm).mul_const Dm).const_smul (1 / 2 : ℝ)
  convert hderiv using 1
  -- derivative equality; unfold `A t`, then collapse both sides to `½•(Dm (a·a) Dm) − (γ/2)•cov`
  have hA : mmMatrixValueCoeff d hÂ T t
      = (1 / 2 : ℝ) • (Dm * matrixRiccatiCoeff hÂ T t * Dm) := by
    rw [mmMatrixValueCoeff, ← hDm]
  set a : Matrix n n ℝ := matrixRiccatiCoeff hÂ T t
  rw [hA, hÂsq]
  -- RHS collapse
  have hRHS : (1 / 2 : ℝ) • (Dm * (a * a - γ • (S * cov * S)) * Dm)
      = (1 / 2 : ℝ) • (Dm * (a * a) * Dm) - (γ / 2) • cov := by
    rw [mul_sub, sub_mul, smul_sub, mul_smul_comm, smul_mul_assoc, hconjCov, smul_smul]
    congr 2
    ring
  -- LHS collapse: first the matrix core, then the scalars
  have hmat : (Dm * a * Dm) * diagonal d * (Dm * a * Dm) = Dm * (a * a) * Dm := by
    rw [show (Dm * a * Dm) * diagonal d * (Dm * a * Dm)
          = Dm * a * (Dm * diagonal d * Dm) * a * Dm from by simp only [Matrix.mul_assoc],
      hDmDDm, Matrix.mul_one,
      show Dm * a * a * Dm = Dm * (a * a) * Dm from by simp only [Matrix.mul_assoc]]
  have hLHS : (2 : ℝ) • ((1 / 2 : ℝ) • (Dm * a * Dm) * diagonal d * ((1 / 2 : ℝ) • (Dm * a * Dm)))
      = (1 / 2 : ℝ) • (Dm * (a * a) * Dm) := by
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, hmat, smul_smul, smul_smul]
    norm_num
  rw [hLHS, hRHS]

end MathFin

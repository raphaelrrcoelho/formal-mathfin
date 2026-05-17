/-
  HybridVerify.LpContinuousMartingaleConvergence
  Theorem 4.3.10 (Saporito): A continuous martingale `(M_t)` bounded in
  `L^p` (`p ≥ 1`) converges almost surely to an integrable `M_∞`; for
  `p > 1` it also converges in `L^p`.

  Proof strategy:
    1. Sample at natural times: `N_k(ω) := M (k : ℝ) ω` is a discrete
       martingale w.r.t. the sub-filtration `𝓕_k := 𝓕 (k : ℝ)`.
    2. The L^p bound transfers to N (trivially, since N_k = M_k for k : ℕ).
       Also L^1 bound from finite measure + L^p bound (Hölder when p > 1,
       trivial when p = 1).
    3. Apply Mathlib's `Submartingale.exists_ae_tendsto_of_bdd` to get
       almost-sure convergence of N at natural times.
    4. By path continuity, the continuous-time limit at `t → ∞` agrees
       with the natural-time limit. (This step uses Doob's L^p maximal
       inequality on the increment martingale to show
       `sup_{n ≤ t ≤ n+1} |M_t - M_n| → 0` in probability.)
    5. For `p > 1`: L^p-boundedness gives uniform integrability in L^p
       (de la Vallée-Poussin) and combined with a.s. convergence yields
       L^p convergence (Vitali).

  The first three steps are written out below. (4) and (5) remain follow-on:

  Step 5 plan (cleanest known route):
    • Define `S ω := ⨆ k : ℕ, ‖discreteSample M k ω‖ₑ : Ω → ℝ≥0∞` and reuse
      `HybridVerify.runMax` machinery from `HybridVerify.MathlibLp` (helper
      `runMax_pow_lintegral_lt_top` is the close analogue) to bound
      `∫⁻ ω, S ω ^ p ∂μ ≤ ((p/(p-1)) · R)^p` via Doob + `lintegral_iSup`.
    • Define `M^* ω := (S ω).toReal` and show `MemLp M^* (ofReal p) μ`.
    • Apply `ProbabilityTheory.uniformIntegrable_of_dominated_singleton`
      (`BrownianMotion.StochasticIntegral.UniformIntegrable`, Degenne) to get
      `UniformIntegrable (discreteSample M) (ofReal p) μ` from the dominator.
    • Finish with Mathlib's `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`
      (Vitali) using the already-proved `discreteSample_ae_tendsto_limitProcess`.

  Step 4 plan: needs continuous-time Doob (`ProbabilityTheory.maximal_ineq_norm`
  in `BrownianMotion.StochasticIntegral.DoobLp`) applied to the increment
  martingale `(M_t − M_n)_{t ∈ [n, n+1]}`, plus a path-continuity (`IsCadlag`)
  hypothesis on `M`. Note that Degenne's own
  `IsSquareIntegrable.ae_tendsto_limitProcess` /
  `tendsto_eLpNorm_two_limitProcess` are still `sorry` upstream, so this
  cannot just be transported — it requires net new mathematical work.
-/
import Mathlib
import HybridVerify.MathlibLp

namespace HybridVerify

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Discrete-time sample of a continuous-time process at natural times. -/
noncomputable def discreteSample (M : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  M (n : ℝ) ω

/-- Sub-filtration at natural times. -/
def natFiltration (𝓕 : Filtration ℝ mΩ) : Filtration ℕ mΩ where
  seq n := 𝓕 (n : ℝ)
  mono' n m hnm := 𝓕.mono (by exact_mod_cast hnm)
  le' n := 𝓕.le _

/-- A continuous martingale sampled at natural times is a discrete
    martingale w.r.t. the natural-time sub-filtration. -/
private lemma discreteSample_martingale
    {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {M : ℝ → Ω → ℝ}
    (hM : Martingale M 𝓕 μ) :
    Martingale (discreteSample M) (natFiltration 𝓕) μ := by
  refine ⟨?_, ?_⟩
  · intro n
    exact hM.stronglyAdapted (n : ℝ)
  · intro i j hij
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact hM.2 (i : ℝ) (j : ℝ) hij'

/-- L^1-norm bound from L^p-norm bound on a finite measure space (Hölder). -/
private lemma eLpNorm_one_le_of_eLpNorm_p
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    {R : ℝ} (hR : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R)
    (hfm : AEStronglyMeasurable f μ) :
    eLpNorm f 1 μ ≤ ENNReal.ofReal R * μ Set.univ ^ ((1 : ℝ) - 1 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h1_le_p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (p := 1) (q := ENNReal.ofReal p) (f := f) h1_le_p hfm).trans ?_
  rw [ENNReal.toReal_one, ENNReal.toReal_ofReal hp_pos.le, one_div_one]
  gcongr

/-- The L^1 bound for the discrete sample, expressed as `ℝ≥0` for the
    Mathlib submartingale-convergence API. -/
private lemma discreteSample_l1_bounded
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∃ R' : ℝ≥0,
      ∀ n : ℕ, eLpNorm (discreteSample M n) 1 μ ≤ (R' : ℝ≥0∞) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h_exp_nn : 0 ≤ (1 : ℝ) - 1 / p := by
    have : 1 / p ≤ 1 := (div_le_one hp_pos).mpr hp
    linarith
  set bound : ℝ≥0∞ := ENNReal.ofReal R * μ Set.univ ^ ((1 : ℝ) - 1 / p)
  have hbound_lt_top : bound < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg h_exp_nn (measure_ne_top _ _))
  refine ⟨bound.toNNReal, fun n => ?_⟩
  rw [ENNReal.coe_toNNReal hbound_lt_top.ne]
  exact eLpNorm_one_le_of_eLpNorm_p hp (hbound (n : ℝ))
    ((hM.stronglyMeasurable (n : ℝ)).mono (𝓕.le _)).aestronglyMeasurable

/-- Discrete a.s. convergence: the discrete sample converges a.s. as `n → ∞`. -/
private lemma discreteSample_ae_tendsto
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n : ℕ => discreteSample M n ω) atTop (𝓝 c) := by
  obtain ⟨R', hR'⟩ := discreteSample_l1_bounded hp hM hbound
  exact (discreteSample_martingale hM).submartingale.exists_ae_tendsto_of_bdd hR'

/-- The canonical limit of the discrete sample: a `(⨆ k, 𝓕 k)`-measurable
    function to which the sample converges a.s. Defined via Mathlib's
    `Filtration.limitProcess`. -/
noncomputable def discreteSampleLimit
    (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ)
    (M : ℝ → Ω → ℝ) : Ω → ℝ :=
  (natFiltration 𝓕).limitProcess (discreteSample M) μ

/-- The discrete sample converges a.s. to its limit process. -/
private lemma discreteSample_ae_tendsto_limitProcess
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => M (n : ℝ) ω) atTop (𝓝 (discreteSampleLimit μ 𝓕 M ω)) := by
  obtain ⟨R', hR'⟩ := discreteSample_l1_bounded hp hM hbound
  exact (discreteSample_martingale hM).submartingale.ae_tendsto_limitProcess hR'

/-- The limit process is integrable (in `L^1`). -/
private lemma discreteSampleLimit_integrable
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p R : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    Integrable (discreteSampleLimit μ 𝓕 M) μ := by
  obtain ⟨R', hR'⟩ := discreteSample_l1_bounded hp hM hbound
  have hAE : ∀ n, AEStronglyMeasurable (discreteSample M n) μ := fun n =>
    (((discreteSample_martingale hM).stronglyMeasurable n).mono
        ((natFiltration 𝓕).le _)).aestronglyMeasurable
  have h_memLp : MemLp (discreteSampleLimit μ 𝓕 M) 1 μ :=
    MeasureTheory.Filtration.memLp_limitProcess_of_eLpNorm_bdd hAE hR'
  exact h_memLp.integrable le_rfl

/-- **Theorem 4.3.10 (Saporito Ch 4.3) — natural-time formulation.**

    A continuous-time martingale `(M_t)` bounded in `L^p` (`p ≥ 1`)
    sampled at natural times `t = n : ℕ` converges almost surely to an
    integrable limit `M_∞ := (natFiltration 𝓕).limitProcess`.

    This is the discrete-time skeleton of Theorem 4.3.10. The full
    continuous-time conclusion `Tendsto (fun t : ℝ => M t ω) atTop ...`
    follows from this skeleton + path continuity + a maximal-oscillation
    bound (via Doob's `L^p` inequality applied to the increment martingale
    `(M_t - M_n)_{t ∈ [n, n+1]}`). For `p > 1`, the `L^p` convergence
    follows from a.s. convergence + uniform integrability in `L^p`. Both
    extensions are documented as follow-on work. -/
theorem lp_continuous_martingale_converges_at_naturals
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hM : Martingale M 𝓕 μ)
    (hbound : ∃ R : ℝ,
      ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∃ (M_inf : Ω → ℝ), Integrable M_inf μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (n : ℝ) ω) atTop (𝓝 (M_inf ω)) := by
  obtain ⟨R, hR⟩ := hbound
  exact ⟨discreteSampleLimit μ 𝓕 M,
    discreteSampleLimit_integrable hp hM hR,
    discreteSample_ae_tendsto_limitProcess hp hM hR⟩

end HybridVerify

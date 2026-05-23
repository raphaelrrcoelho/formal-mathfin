# zulip msg — wojciech mct coordination

**stream:** `#Brownian motion`
**topic:** `Martingale Convergence Theorem` (existing, keep the thread)

---

@Wojciech Czernous @Rémy Degenne, i have a lean proof of the continuous-time L^p martingale convergence theorem sitting locally from an unrelated saporito-style benchmark project, and want to flag overlap before duplicating work.

local statement:

```
theorem lp_continuous_martingale_full
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} {p : ℝ} (hp : 1 < p)
    (hM : Martingale M 𝓕 μ)
    (hM_cont : ∀ ω, Function.IsRightContinuous (fun t : ℝ => M t ω))
    (hbound : ∃ R : ℝ, ∀ t, eLpNorm (M t) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal R) :
    ∃ (M_inf : Ω → ℝ), Integrable M_inf μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (n : ℝ) ω) atTop (𝓝 (M_inf ω))) ∧
      TendstoInMeasure μ M atTop M_inf
```

~700 lines, axioms-clean. doesnt go through upcrossings or bernstein–lévy. instead reduces to natural times via mathlib's discrete L^p convergence, then for real-time builds a shifted-increment martingale and applies aaron's `Submartingale.rightCont_iSup_ofReal_ne_top`.

looks complementary to your upcrossing route, not a duplicate. upcrossing gives a.s. limits for L^1-bounded submartingales without continuity, this gives `TendstoInMeasure` under right-continuity + L^p-boundedness for `p > 1`. same overall area.

a few questions before opening an issue:

1. in scope for the bm project, or too downstream (project boundary = tools needed for the stochastic integral)?
2. better as a mathlib pr (built on aaron's `rightCont_iSup_ofReal_ne_top` once that lands upstream)?
3. wojciech, overlap with your plans beyond the upcrossing pr, or sits cleanly alongside? happy to coordinate however.

thanks!

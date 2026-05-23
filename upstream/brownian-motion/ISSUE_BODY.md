# degenne bm issue — draft body

**title:** `Add square and Wald exponential martingale properties for IsFilteredPreBrownian`

---

two martingale identities for `IsFilteredPreBrownian X 𝓕 P` that arent in the project yet:

- `t ↦ (X t)² − t` is a martingale w.r.t. `𝓕`
- `t ↦ exp(α X_t − α² t / 2)` is a martingale w.r.t. `𝓕`, for every `α : ℝ`

natural next-step companions to `IsPreBrownian.isMartingale`. proof sketch:

- **square**: decompose `(X_t)² = (X_s)² + 2 X_s (X_t − X_s) + (X_t − X_s)²`. first summand is `𝓕_s`-measurable; cross term has zero conditional expectation via pull-out + centered increment + `IsFilteredPreBrownian.indep`; squared increment has conditional expectation `t − s` via `IsPreBrownian.hasLaw_sub` + `variance_id_gaussianReal`. combine with `linear_combination`.
- **wald**: factor `exp(α X_t − α² t / 2) = M_s · D_{s,t}` where `M_s := exp(α X_s − α² s / 2)` is `𝓕_s`-measurable and `D_{s,t} := exp(α(X_t − X_s) − α²(t−s)/2)` is a function of the increment (independent of `𝓕_s`). then `E[D_{s,t}] = 1` by the gaussian mgf (`mgf_id_gaussianReal`) and pull-out closes it.

scope:

- new file `BrownianMotion/Gaussian/Martingale.lean`, ~365 lines
- 3 private helpers (NNReal coercion of the increment-variance `max`, MGF at mean zero, second moment of a centered gaussian) + 1 private "increment is independent of the past" convenience lemma
- 2 public theorems: `IsFilteredPreBrownian.squareSubTime_isMartingale` and `IsFilteredPreBrownian.waldExponential_isMartingale`
- builds clean against current master (commit `16d15eb4`), lean v4.30.0-rc1, no new external deps

naming: working names are `squareSubTime_isMartingale` / `waldExponential_isMartingale` (matching the `IsPreBrownian.isMartingale` precedent). happy to rename to fit your conventions (`sq_sub_id_isMartingale` / `expMartingale` or whatever). let me know before i open the pr.

proof is sitting locally and pr-ready. once this is in unclaimed ill comment `claim` and open the pr.

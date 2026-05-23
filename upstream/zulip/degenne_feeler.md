# zulip msg — degenne tasks-and-claims feeler

**stream:** `#Brownian motion`
**topic:** `Tasks and claims` (existing)

---

hi @Rémy Degenne @Etienne Marion, i have a lean proof ready for two martingale identities of `IsFilteredPreBrownian`:

- $t \mapsto X_t^2 - t$ is a martingale w.r.t. $\mathcal{F}$
- $t \mapsto \exp(\alpha X_t - \alpha^2 t / 2)$ is a martingale w.r.t. $\mathcal{F}$, for every $\alpha \in \mathbb{R}$

natural next step after `IsPreBrownian.isMartingale`. ~365 lines, single new file `BrownianMotion/Gaussian/Martingale.lean`. builds clean against current master, no new external deps. uses existing mathlib `gaussianReal` api (`mgf_id_gaussianReal`, `variance_id_gaussianReal`, `memLp_id_gaussianReal`, etc.) + the project's `IsFilteredPreBrownian.indep` / `hasLaw_sub` / `hasLaw_eval`.

no existing issue. want me to open one (or two) so i can `claim` and pr? happy to discuss naming first if you have preferences (working names `squareSubTime_isMartingale` / `waldExponential_isMartingale`).

thanks!

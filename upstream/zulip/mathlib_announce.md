# zulip msg — mathlib announce

**stream:** `#mathlib4`
**topic:** `PR #<N>: Gaussian tail and shifted-tail integrals` (fill `<N>` after `gh pr create` returns the url)

---

opened #<PR_NUMBER>: adds tail and shifted-tail integrals of the standard normal in a new file `Mathlib/Probability/Distributions/Gaussian/RealTail.lean` (138 lines). headline lemma `integral_exp_mul_gaussianPDFReal_zero_one_Ioi` is the standard computational primitive used in black-scholes derivations; the other three are supporting identities (symmetry around zero, right-tail, completing-the-square).

@Rémy Degenne @Etienne Marion, flagging since this is in your area. happy to generalize the symmetry lemma from the standard normal to `gaussianReal μ v` in this pr or a follow-up, let me know.

thanks!

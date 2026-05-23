# mathlib pr — draft body

**title:** `feat(Probability/Distributions/Gaussian): tail and shifted-tail integrals of the standard normal`

**branch:** `gaussian-real-tail`

---

adds 4 lemmas about the standard normal `gaussianReal 0 1`:

- `gaussianReal_zero_one_Iic_neg`, symmetry: `P(Z ≤ -x) = 1 − P(Z ≤ x)`
- `gaussianReal_zero_one_Ioi_toReal`, right tail: `P(Z > a) = 1 − P(Z ≤ a)`
- `exp_mul_gaussianPDFReal_zero_one`, completing-the-square: `exp(c · z) · pdf(0, 1, z) = exp(c² / 2) · pdf(c, 1, z)`
- `integral_exp_mul_gaussianPDFReal_zero_one_Ioi`, shifted-tail integral: `∫ z in Ioi a, exp(c · z) · pdf(0, 1, z) dz = exp(c² / 2) · P(Z ≤ c − a)`

new file `Mathlib/Probability/Distributions/Gaussian/RealTail.lean`, 138 lines. depends only on `Mathlib/Probability/Distributions/Gaussian/Real.lean`.

the last one is the standard computational primitive in black-scholes derivations. the other three are supporting identities i hit while building a black-scholes derivation downstream, only mathlib gaps i ran into.

all four specialize to `(μ = 0, v = 1)`. the symmetry lemma generalizes obviously to `gaussianReal μ v` via `gaussianReal_map_neg` + `gaussianReal_map_add_const`. happy to do it in this pr or a follow-up, let me know preference.

ai use: claude code (opus 4.7) helped extract and restate these from a downstream file. i read every line in the final form.

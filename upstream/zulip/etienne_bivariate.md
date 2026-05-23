# zulip msg — etienne bivariate gaussian (optional)

**stream:** `#Brownian motion`
**topic:** `Bivariate Gaussian conditional expectation` (new)

---

@Etienne Marion, quick coordination question. i have a lean proof of the classical bivariate-gaussian conditional expectation formula sitting locally:

```
theorem conditional_expectation_formula
    (h : BivariateGaussianHyp P X Y μ_X μ_Y σ_X σ_Y ρ) :
    (P[X | MeasurableSpace.comap Y inferInstance])
      =ᵐ[P] fun ω ↦ μ_X + (ρ * σ_X / σ_Y) * (Y ω - μ_Y)
```

(saporito B.1.3 (2), via linear-shift independence.)

two questions:

1. on your queue for `Gaussian/MultivariateGaussian.lean` or somewhere else in the gaussian stack? didnt see it on the open issues list but the multivariate file is small enough it could just be pending.
2. if not, want me to open an issue and pr? happy to refactor the hypothesis bundle to match your `HasLaw` / `IsGaussianProcess` conventions.

dont want to step on in-flight `Gaussian/*` work. let me know either way.

thanks!

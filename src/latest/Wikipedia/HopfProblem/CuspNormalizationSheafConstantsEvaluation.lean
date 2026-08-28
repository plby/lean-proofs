import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationSurjective
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationCompatibility
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsEvaluationNaturality

/-!
# Actual constant-sheaf evaluations and their naturality

Evaluation is independently constructed from the genuine pushforward
stalk, the actual constant-stalk identification with `ℂ`, and Mathlib's
skyscraper adjunction.  It agrees with holomorphic evaluation under the
proved constants inclusion, and is natural for actual continuous
pullback over a base.  Single-point evaluation is surjective on every
section group.  These maps supply the actual endpoint evaluations of
the constant cusp normalization sequence.
-/

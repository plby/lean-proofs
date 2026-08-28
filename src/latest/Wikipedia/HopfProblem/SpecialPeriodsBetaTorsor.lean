import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorClassification
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorUniqueness

/-!
# The actual beta torsor and its complete affine family

Given the actual normalized sphere uniformization and holomorphic tau and mu
with their generator equations, `BetaTorsor.Data.exists_normalized_beta_affine_family`
constructs beta, its analytic distinguished-cusp extension, and the entire
family of solutions beta plus a constant.  Local sections, their full-word
equivariance, their holomorphic overlap functions, and the Cousin correction
are all constructed and proved.  Classification uses only the original
boundedness condition at the distinguished cusp.
-/

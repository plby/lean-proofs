import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeH1
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeExact

/-!
# Source Lemma 9.12(iii), with original singular and holomorphic cohomology

The original inclusion of constants induces a genuine complex-linear
isomorphism `H¹(W; ℂ) ≃ₗ[ℂ] H¹(W, O_W)`. Its full degree-two map is
surjective, and its restriction to the literal kernel of the original
singular normalization pullback is a genuine complex-linear
isomorphism onto `H²(W, O_W)`.

All forward maps, the actual kernel inclusion, and the original scalar
actions are retained. The proofs compose the already established
native constant-to-holomorphic edge comparison with the canonical
constant-sheaf/singular comparison and its actual normalization square.
Only the original construction's geometric hypotheses occur.

The cup-product assertion in source Lemma 9.12(iv) is separate and is
neither assumed nor asserted by this package.
-/

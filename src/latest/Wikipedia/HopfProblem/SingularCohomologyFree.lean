import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular

/-!
# Actual integral singular cohomology with projective homology

The singular cochain complex is the literal integral dual of Mathlib's
singular chain complex, with the alternating singular-face differential
and pullback by actual continuous maps.  Its actual categorical homology
defines integral singular cohomology.

The canonical evaluation pairing is constructed from actual cycles and
boundaries, with no freeness assumption, and proved natural.  When all
integral singular homology groups are projective, genuine chain formality
and contravariant cochain homotopy transport prove that evaluation is a
linear equivalence.  Singular-chain projectivity is supplied by the
proved simplex basis.  No universal-coefficient or map-duality theorem
is postulated.
-/

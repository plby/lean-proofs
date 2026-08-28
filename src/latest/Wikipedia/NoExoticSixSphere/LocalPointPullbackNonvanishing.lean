import Wikipedia.NoExoticSixSphere.FinitePointPullback
import Wikipedia.NoExoticSixSphere.SupportedCohomologyPairPullback
import Wikipedia.NoExoticSixSphere.PointSupportedNormalClass

/-!
# Nonzero original point pullbacks from one local inverse

An original point-supported class stays nonzero when pulled back through
a map having a local inverse at a point of the fiber. Restriction to that
inverse neighborhood detects nonvanishing. Naming the exact inverse-image
support separately does not change this conclusion: its extension is
injective. The genuine normal point class is nonzero by its original
relative cohomology marking.
-/

noncomputable section

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- One actual local inverse detects a nonzero original point pullback. -/
theorem pullback_point_ne_zero_of_localHomeomorph (f : C(X, Y)) (x : X)
    (hf : IsLocalHomeomorphOn f ({x} : Set X)) (p : ℕ)
    (a : Cohomology ({f x} : Set Y) p) (ha : a ≠ 0) :
    pullback f ({f x} : Set Y) p a ≠ 0 := by
  obtain ⟨U, _, _, _, hn⟩ := exists_point_pullback_ne_zero_neighborhood f x hf p a ha
  intro he
  apply hn
  rw [he, map_zero]

/-- The same nonvanishing holds with the exact inverse-image support named separately. -/
theorem pullbackTo_ne_zero_of_local_point (f : C(X, Y)) (x : X)
    (hf : IsLocalHomeomorphOn f ({x} : Set X)) (p : ℕ) (K : Set Y) (hK : K = {f x})
    (L : Set X) (hL : f ⁻¹' K = L) (a : Cohomology K p) (ha : a ≠ 0) :
    pullbackTo f K L hL.subset p a ≠ 0 := by
  subst K
  intro he
  apply pullback_point_ne_zero_of_localHomeomorph f x hf p a ha
  apply extend_injective_of_reverse_subset hL.subset hL.symm.subset p
  exact ((pullbackTo_eq_extend f {f x} L hL.subset p a).symm.trans he).trans
    (map_zero _).symm

end NoExoticSixSphere.SupportedModTwoCohomology

namespace NoExoticSixSphere.ProductNormalCohomologyClass

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- The original normal point class is nonzero in its genuine relative cohomology group. -/
theorem pointClass_ne_zero : pointClass E n ≠ 0 :=
  ClosedBallLocalHomology.topCohomologyClass_ne_zero E n 0 le_rfl

end NoExoticSixSphere.ProductNormalCohomologyClass

import ErdosProblems.Erdos556.CubeMatchingGeometry

/-! Profile geometry describing which edges can be retained. -/

namespace Erdos556

theorem profileOppositeAt_disjoint : ∀ (p q : CubeProfile) (i : Fin 3),
    profileOppositeAt p q i → Disjoint (profileVertices p) (profileVertices q) := by decide

theorem singleton_profile_intersection_no_common_free : ∀ (p q : CubeProfile) (i : Fin 3),
    (profileVertices p ∩ profileVertices q).card = 1 → ¬ (p i = none ∧ q i = none) := by decide

theorem profileDimension_zero_iff_no_free : ∀ p : CubeProfile,
    profileDimension p = 0 ↔ ∀ i, p i ≠ none := by decide

theorem profileDimension_one_unique_free : ∀ p : CubeProfile, profileDimension p = 1 →
    ∃ i, p i = none ∧ ∀ j, p j = none → j = i := by decide

#print axioms singleton_profile_intersection_no_common_free

end Erdos556

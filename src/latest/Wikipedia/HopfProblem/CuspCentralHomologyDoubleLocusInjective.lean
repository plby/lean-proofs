import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusMap
import Wikipedia.HopfProblem.CuspCentralHomologyEdgeQuotient

/-!
# Exact fibres and injectivity of the actual double-locus suspension map

The three open edge cylinders have no additional quotient identifications.
Their points do not become toric corners, and the two endpoint poles are
distinct. Thus the exact fibre relation of the actual cylinder map is the
original suspension relation, and the descended map is injective.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

/-- The chosen edge, its oriented interval coordinate, and its circle phase. -/
private def cylinderEdgeData (t : unitInterval) (a : ThreeCircles) :
    Fin 6 × (unitInterval × Circle) :=
  match a with
  | Sum.inl a => (0, t, a)
  | Sum.inr (Sum.inl a) => (1, unitInterval.symm t, a)
  | Sum.inr (Sum.inr a) => (2, t, a)

private theorem cylinderEdgeData_index_lt (t : unitInterval) (a : ThreeCircles) :
    (cylinderEdgeData t a).1.val < 3 := by
  rcases a with a | a | a <;> norm_num [cylinderEdgeData]

private theorem cylinderEdgeData_time_ne_zero (t : unitInterval) (a : ThreeCircles)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : (cylinderEdgeData t a).2.1 ≠ 0 := by
  rcases a with a | a | a
  · exact ht0
  · exact fun h => ht1 (unitInterval.symm_eq_zero.mp h)
  · exact ht0

private theorem cylinderEdgeData_time_ne_one (t : unitInterval) (a : ThreeCircles)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : (cylinderEdgeData t a).2.1 ≠ 1 := by
  rcases a with a | a | a
  · exact ht1
  · exact fun h => ht0 (unitInterval.symm_eq_one.mp h)
  · exact ht1

private theorem cylinderEdgeData_eq_iff (s t : unitInterval) (a b : ThreeCircles) :
    ((cylinderEdgeData s a).1 = (cylinderEdgeData t b).1 ∧
      (cylinderEdgeData s a).2.1 = (cylinderEdgeData t b).2.1 ∧
      (cylinderEdgeData s a).2.2 = (cylinderEdgeData t b).2.2) ↔ s = t ∧ a = b := by
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    simp [cylinderEdgeData, unitInterval.symm_inj]

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

private theorem doubleCylinder_eq_projected (t : unitInterval) (a : ThreeCircles) :
    doubleCylinder C ε hε (t, a) =
      projectedEdgeCylinder C ε hε (cylinderEdgeData t a).1 (cylinderEdgeData t a).2 := by
  rcases a with a | a | a <;> rfl

theorem doubleCylinder_eq_iff_of_interior (s t : unitInterval)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (a b : ThreeCircles) :
    doubleCylinder C ε hε (s, a) = doubleCylinder C ε hε (t, b) ↔ s = t ∧ a = b := by
  simp only [doubleCylinder_eq_projected]
  exact (projectedEdgeCylinder_eq_iff_of_interior C ε hε _ _
    (cylinderEdgeData_index_lt s a) (cylinderEdgeData_index_lt t b) _ _
    (cylinderEdgeData_time_ne_zero s a hs0 hs1) (cylinderEdgeData_time_ne_one s a hs0 hs1)
    (cylinderEdgeData_time_ne_zero t b ht0 ht1) (cylinderEdgeData_time_ne_one t b ht0 ht1)
    _ _).trans (cylinderEdgeData_eq_iff s t a b)

theorem doubleCylinder_interior_ne_corner (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a : ThreeCircles) (j : Fin 6) :
    doubleCylinder C ε hε (t, a) ≠ cornerPoint C ε hε j := by
  rw [doubleCylinder_eq_projected]
  exact projectedEdgeCylinder_interior_ne_corner C ε hε _ _
    (cylinderEdgeData_time_ne_zero t a ht0 ht1)
    (cylinderEdgeData_time_ne_one t a ht0 ht1) _ j

theorem doubleCylinder_eq_oddPole_iff (t : unitInterval) (a : ThreeCircles) :
    doubleCylinder C ε hε (t, a) = oddPole C ε hε ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht0
    by_cases ht1 : t = 1
    · subst t
      exact pole_ne C ε hε (by simpa only [doubleCylinder_one] using h)
    · exact doubleCylinder_interior_ne_corner C ε hε t ht0 ht1 a 1 h
  · rintro rfl
    exact doubleCylinder_zero C ε hε a

theorem doubleCylinder_eq_evenPole_iff (t : unitInterval) (a : ThreeCircles) :
    doubleCylinder C ε hε (t, a) = evenPole C ε hε ↔ t = 1 := by
  constructor
  · intro h
    by_contra ht1
    by_cases ht0 : t = 0
    · subst t
      apply pole_ne C ε hε
      simpa only [doubleCylinder_zero] using h.symm
    · exact doubleCylinder_interior_ne_corner C ε hε t ht0 ht1 a 0 h
  · rintro rfl
    exact doubleCylinder_one C ε hε a

/-- The actual central quotient map has exactly the original suspension fibre relation. -/
theorem doubleCylinder_eq_iff (p q : unitInterval × ThreeCircles) :
    doubleCylinder C ε hε p = doubleCylinder C ε hε q ↔
      (suspensionSetoid ThreeCircles).r p q := by
  rcases p with ⟨s, a⟩
  rcases q with ⟨t, b⟩
  constructor
  · intro h
    change s = t ∧ (s = 0 ∨ s = 1 ∨ a = b)
    by_cases hs0 : s = 0
    · subst s
      have ht0 : t = 0 := (doubleCylinder_eq_oddPole_iff C ε hε t b).mp
        (h.symm.trans (doubleCylinder_zero C ε hε a))
      exact ⟨ht0.symm, Or.inl rfl⟩
    by_cases hs1 : s = 1
    · subst s
      have ht1 : t = 1 := (doubleCylinder_eq_evenPole_iff C ε hε t b).mp
        (h.symm.trans (doubleCylinder_one C ε hε a))
      exact ⟨ht1.symm, Or.inr (Or.inl rfl)⟩
    have ht0 : t ≠ 0 := by
      intro ht0
      subst t
      exact doubleCylinder_interior_ne_corner C ε hε s hs0 hs1 a 1
        (h.trans (doubleCylinder_zero C ε hε b))
    have ht1 : t ≠ 1 := by
      intro ht1
      subst t
      exact doubleCylinder_interior_ne_corner C ε hε s hs0 hs1 a 0
        (h.trans (doubleCylinder_one C ε hε b))
    obtain ⟨hst, hab⟩ :=
      (doubleCylinder_eq_iff_of_interior C ε hε s t hs0 hs1 ht0 ht1 a b).mp h
    exact ⟨hst, Or.inr (Or.inr hab)⟩
  · exact doubleCylinder_respects C ε hε _ _

theorem doubleSuspensionMap_injective : Function.Injective (doubleSuspensionMap C ε hε) := by
  intro x y h
  obtain ⟨⟨s, a⟩, rfl⟩ := Suspension.mk_surjective x
  obtain ⟨⟨t, b⟩, rfl⟩ := Suspension.mk_surjective y
  exact Quotient.sound ((doubleCylinder_eq_iff C ε hε (s, a) (t, b)).mp h)

end Wikipedia.HopfProblem.CuspCentralHomology

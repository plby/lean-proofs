import ErdosProblems.Erdos633.CharacterBoundary

/-!
# Intrinsic side normalization and boundary equations

Normalized sides divide by the actual side opposite the third angle. The
sine scale gives a uniform geometric side formula. Integer boundary equations
are homogeneous and therefore survive this normalization.
-/

namespace Erdos633

open scoped BigOperators

noncomputable def Triangle.normalizedSide (P : Triangle) (k : Fin 3) : ℝ :=
  P.sideLength k / P.sideLength 2

noncomputable def Triangle.sineScale (P : Triangle) : ℝ :=
  P.sideLength 2 / Real.sin P.angleC

def Triangle.CommensurableSides (P : Triangle) : Prop :=
  ∀ k : Fin 3, P.normalizedSide k ∈ rationalReals

theorem Triangle.normalizedSide_pos (P : Triangle) (k : Fin 3) : 0 < P.normalizedSide k :=
  div_pos (P.sideLength_pos k) (P.sideLength_pos 2)

@[simp] theorem Triangle.normalizedSide_two (P : Triangle) : P.normalizedSide 2 = 1 :=
  div_self (ne_of_gt (P.sideLength_pos 2))

theorem Triangle.sineScale_pos (P : Triangle) : 0 < P.sineScale :=
  div_pos (P.sideLength_pos 2) P.sin_angleC_pos

theorem Triangle.sideLength_eq_sineScale (P : Triangle) (k : Fin 3) :
    P.sideLength k = P.sineScale * Real.sin (P.cornerAngle k) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · change dist P.b P.c = (dist P.a P.b / Real.sin P.angleC) * Real.sin P.angleA
    rw [P.sideA_over_C]
    ring
  · change dist P.c P.a = (dist P.a P.b / Real.sin P.angleC) * Real.sin P.angleB
    rw [dist_comm P.c P.a, P.sideB_over_C]
    ring
  · change dist P.a P.b = (dist P.a P.b / Real.sin P.angleC) * Real.sin P.angleC
    rw [div_mul_cancel₀ _ (ne_of_gt P.sin_angleC_pos)]

theorem Triangle.normalizedSide_eq_sin_ratio (P : Triangle) (k : Fin 3) :
    P.normalizedSide k = Real.sin (P.cornerAngle k) / Real.sin P.angleC := by
  rw [Triangle.normalizedSide, P.sideLength_eq_sineScale k, P.sideLength_eq_sineScale 2]
  change P.sineScale * Real.sin (P.cornerAngle k) /
    (P.sineScale * Real.sin P.angleC) = _
  exact mul_div_mul_left _ _ (ne_of_gt P.sineScale_pos)

theorem Triangle.sin_cornerAngle_eq_normalizedSide (P : Triangle) (k : Fin 3) :
    Real.sin (P.cornerAngle k) = Real.sin P.angleC * P.normalizedSide k := by
  rw [P.normalizedSide_eq_sin_ratio, mul_div_cancel₀ _ (ne_of_gt P.sin_angleC_pos)]

theorem Triangle.normalized_outer_sides_of_sines (P R : Triangle)
    (S x y z : ℝ) (hS : 0 < S)
    (hA : Real.sin P.angleA = S * x) (hB : Real.sin P.angleB = S * y)
    (hC : Real.sin P.angleC = S * z) :
    ∃ L : ℝ, 0 < L ∧ P.sideLength 0 / R.sideLength 2 = L * x ∧
      P.sideLength 1 / R.sideLength 2 = L * y ∧
      P.sideLength 2 / R.sideLength 2 = L * z := by
  let L := P.sineScale * S / R.sideLength 2
  refine ⟨L, div_pos (mul_pos P.sineScale_pos hS) (R.sideLength_pos 2), ?_, ?_, ?_⟩
  · rw [P.sideLength_eq_sineScale 0]
    change P.sineScale * Real.sin P.angleA / R.sideLength 2 = _
    rw [hA]
    dsimp [L]
    ring
  · rw [P.sideLength_eq_sineScale 1]
    change P.sineScale * Real.sin P.angleB / R.sideLength 2 = _
    rw [hB]
    dsimp [L]
    ring
  · rw [P.sideLength_eq_sineScale 2]
    change P.sineScale * Real.sin P.angleC / R.sideLength 2 = _
    rw [hC]
    dsimp [L]
    ring

theorem Triangle.commensurableSides_of_first_two (P : Triangle)
    (h0 : P.normalizedSide 0 ∈ rationalReals) (h1 : P.normalizedSide 1 ∈ rationalReals) :
    P.CommensurableSides := by
  intro k
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · exact h0
  · exact h1
  · rw [P.normalizedSide_two]
    exact rationalReals.one_mem

theorem IntegerBoundarySigns.div {a b c X Y Z t : ℝ} {πc B C : ℤ × ℤ}
    (h : IntegerBoundarySigns a b c X Y Z πc B C) :
    IntegerBoundarySigns (a / t) (b / t) (c / t) (X / t) (Y / t) (Z / t) πc B C := by
  intro u v hπ
  obtain ⟨m, hm⟩ := h u v hπ
  refine ⟨m, ?_⟩
  have heq := congrArg (fun x : ℝ => x / t) hm
  unfold signedTriangleBoundary at heq ⊢
  convert heq using 1 <;> ring

theorem CongruentTiling.normalized_integerBoundarySigns
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hind : IntegerIndependentAngles R.angleA R.angleB) (πc B C : ℤ × ℤ)
    (hπ : Real.pi = angleFromCoordinates R.angleA R.angleB πc)
    (hB : P.angleB = angleFromCoordinates R.angleA R.angleB B)
    (hC : P.angleC = angleFromCoordinates R.angleA R.angleB C) :
    IntegerBoundarySigns (R.normalizedSide 0) (R.normalizedSide 1) 1
      (P.sideLength 0 / R.sideLength 2) (P.sideLength 1 / R.sideLength 2)
      (P.sideLength 2 / R.sideLength 2) πc B C := by
  have h := (T.integerBoundarySigns hind πc B C hπ hB hC).div (t := R.sideLength 2)
  simpa only [Triangle.normalizedSide, div_self (ne_of_gt (R.sideLength_pos 2))] using h

theorem CongruentTiling.side_div_reference_eq_sum
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (k : Fin 3) :
    P.sideLength k / R.sideLength 2 =
      ∑ j : Fin 3, (T.boundarySideCount k j : ℝ) * R.normalizedSide j := by
  rw [T.boundary_side_count_equation, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_div_assoc _ _ _

theorem CongruentTiling.commensurableSides_of_reference
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (hR : R.CommensurableSides) :
    P.CommensurableSides := by
  have hr (k : Fin 3) : P.sideLength k / R.sideLength 2 ∈ rationalReals := by
    rw [T.side_div_reference_eq_sum]
    exact rationalReals.sum_mem (fun j _ =>
      rationalReals.mul_mem (rationalReals_nat _) (hR j))
  intro k
  have h := rationalReals.div_mem (hr k) (hr 2)
  have heq : (P.sideLength k / R.sideLength 2) / (P.sideLength 2 / R.sideLength 2) =
      P.normalizedSide k := by
    unfold Triangle.normalizedSide
    field_simp [ne_of_gt (R.sideLength_pos 2), ne_of_gt (P.sideLength_pos 2)]
  rwa [heq] at h

theorem CongruentTiling.side_div_reference_eq_three
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (k : Fin 3) :
    P.sideLength k / R.sideLength 2 =
      (T.boundarySideCount k 0 : ℝ) * R.normalizedSide 0 +
      (T.boundarySideCount k 1 : ℝ) * R.normalizedSide 1 + T.boundarySideCount k 2 := by
  have h := T.side_div_reference_eq_sum k
  simpa [Fin.sum_univ_succ, ← add_assoc] using h

theorem CongruentTiling.side_div_reference_rational
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : R.CommensurableSides) (k : Fin 3) :
    P.sideLength k / R.sideLength 2 ∈ rationalReals := by
  rw [T.side_div_reference_eq_sum]
  exact rationalReals.sum_mem (fun j _ =>
    rationalReals.mul_mem (rationalReals_nat _) (hR j))

end Erdos633

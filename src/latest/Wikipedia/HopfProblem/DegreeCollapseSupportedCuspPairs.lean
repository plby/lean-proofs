import Wikipedia.HopfProblem.DegreeCollapseSupportedCuspModel

/-!
# The supported cusp endpoint has exactly one double point

The first five unchanged coordinates force every nontrivial coincidence
onto the last coordinate axis. The cutoff bounds force that pair into the
radius-one ball, where the cutoff equals one. Thus the only ordered pairs
are the two orderings of the axis points with coordinates plus and minus one.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization WhitneyCusp

theorem axis_of_distinct_map_eq (β : Vector 3 → ℝ) (t : ℝ) (x y : Vector 3)
    (h : map β t x = map β t y) (hne : x ≠ y) :
    ∃ z : ℝ, z ≠ 0 ∧ x = axis z ∧ y = axis (-z) := by
  have h₀ : x 0 = y 0 := congrArg (fun w : Vector 6 ↦ w 0) h
  have h₁ : x 1 = y 1 := congrArg (fun w : Vector 6 ↦ w 1) h
  have h₂ : x 2 ^ 2 = y 2 ^ 2 := congrArg (fun w : Vector 6 ↦ w 2) h
  have h₃ : x 0 * x 2 = y 0 * y 2 := congrArg (fun w : Vector 6 ↦ w 3) h
  have h₄ : x 1 * x 2 = y 1 * y 2 := congrArg (fun w : Vector 6 ↦ w 4) h
  have hy₂ : y 2 = -x 2 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h₂ with hz | hz
    · exact (hne (by
        ext i
        fin_cases i
        · exact h₀
        · exact h₁
        · exact hz)).elim
    · linarith
  have hz : x 2 ≠ 0 := by
    intro hx₂
    apply hne
    ext i
    fin_cases i
    · exact h₀
    · exact h₁
    · change x 2 = y 2
      rw [hy₂, hx₂, neg_zero]
  have hx₀ : x 0 = 0 := by
    rw [← h₀, hy₂] at h₃
    have hp : x 0 * x 2 = 0 := by nlinarith
    exact (mul_eq_zero.mp hp).resolve_right hz
  have hx₁ : x 1 = 0 := by
    rw [← h₁, hy₂] at h₄
    have hp : x 1 * x 2 = 0 := by nlinarith
    exact (mul_eq_zero.mp hp).resolve_right hz
  refine ⟨x 2, hz, ?_, ?_⟩
  · ext i
    fin_cases i
    · exact hx₀
    · exact hx₁
    · rfl
  · ext i
    fin_cases i
    · exact h₀.symm.trans hx₀
    · exact h₁.symm.trans hx₁
    · exact hy₂

theorem axis_crossing (β : Cutoff) : map β.value 1 (axis 1) = map β.value 1 (axis (-1)) := by
  have h₁ := β.one (axis 1) (by rw [norm_axis]; norm_num)
  have h₂ := β.one (axis (-1)) (by rw [norm_axis]; norm_num)
  rw [map_eq_cusp_of_one 1 h₁, map_eq_cusp_of_one 1 h₂]
  exact (WhitneyCusp.map_eq_iff 1 _ _).mpr
    (Or.inr ⟨1, one_ne_zero, by norm_num, rfl, rfl⟩)

theorem endpoint_map_eq_iff (β : Cutoff) (x y : Vector 3) :
    map β.value 1 x = map β.value 1 y ↔ x = y ∨
      (x = axis 1 ∧ y = axis (-1)) ∨ (x = axis (-1) ∧ y = axis 1) := by
  constructor
  · intro h
    by_cases hxy : x = y
    · exact Or.inl hxy
    obtain ⟨z, hz, rfl, rfl⟩ := axis_of_distinct_map_eq β.value 1 x y h hxy
    have hlast : z ^ 3 + z - (1 + 1) * β.value (axis z) * z =
        (-z) ^ 3 + (-z) - (1 + 1) * β.value (axis (-z)) * (-z) :=
      congrArg (fun w : Vector 6 ↦ w 5) h
    have hprod : z * (z ^ 2 + 1 - β.value (axis z) - β.value (axis (-z))) = 0 := by
      nlinarith
    have hroot : z ^ 2 + 1 = β.value (axis z) + β.value (axis (-z)) := by
      have hh := (mul_eq_zero.mp hprod).resolve_left hz
      linarith
    have hbound : z ^ 2 ≤ 1 := by
      have h₁ := (β.bounds (axis z)).2
      have h₂ := (β.bounds (axis (-z))).2
      linarith
    have habs : |z| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    have hβ₁ : β.value (axis z) = 1 := β.one _ (by rw [norm_axis]; linarith)
    have hβ₂ : β.value (axis (-z)) = 1 := β.one _ (by rw [norm_axis, abs_neg]; linarith)
    rw [hβ₁, hβ₂] at hroot
    have hsq : z ^ 2 = (1 : ℝ) ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hz₁ | hz₂
    · right
      left
      rw [hz₁]
      exact ⟨rfl, rfl⟩
    · right
      right
      rw [hz₂, neg_neg]
      exact ⟨rfl, rfl⟩
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact axis_crossing β
    · exact (axis_crossing β).symm

theorem endpoint_pairs (β : Cutoff) :
    {p : Vector 3 × Vector 3 | p.1 ≠ p.2 ∧ map β.value 1 p.1 = map β.value 1 p.2} =
      {(axis 1, axis (-1)), (axis (-1), axis 1)} := by
  have hne : axis (1 : ℝ) ≠ axis (-1) := axis_ne_neg (by norm_num)
  ext p
  rcases p with ⟨x, y⟩
  simp only [mem_setOf_eq, endpoint_map_eq_iff, mem_insert_iff, mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hne', h | h | h⟩
    · exact (hne' h).elim
    · exact Or.inl h
    · exact Or.inr h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hne, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨hne.symm, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

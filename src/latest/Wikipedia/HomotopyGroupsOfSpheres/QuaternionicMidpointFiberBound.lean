import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointCoefficients
import Mathlib.Data.Fintype.Card

/-!
# At most four sphere preimages of each midpoint matrix

The first two rotated coordinates each have at most two choices. Their
values determine the third coordinate by the off-diagonal equations.
This proves finiteness and an upper bound, not existence or a degree.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

theorem diagonal_third_coordinate (z : UnitSphere) (d : Fin 3 → ℂ)
    (hd : (symmetricMap z).val.val = Matrix.diagonal d) :
    (d 0 - d 1) * z.val 2 =
      (d 0 + d 1) * star (z.val 0) * star (z.val 1) - 2 * z.val 0 * z.val 1 := by
  have h01 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A 0 1)
    (matrix_eq_symmetric_mul_conjugate z)
  have h10 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A 1 0)
    (matrix_eq_symmetric_mul_conjugate z)
  rw [hd, Matrix.diagonal_mul] at h01 h10
  change matrix z.val 0 1 = d 0 * star (matrix z.val 0 1) at h01
  change matrix z.val 1 0 = d 1 * star (matrix z.val 1 0) at h10
  simp [matrix, outer, crossMatrix] at h01 h10
  simp only [Complex.star_def]
  linear_combination h01 + h10

theorem diagonal_first_two_injective (z w : UnitSphere) (d : Fin 3 → ℂ)
    (hz : (symmetricMap z).val.val = Matrix.diagonal d)
    (hw : (symmetricMap w).val.val = Matrix.diagonal d) (hne : d 0 ≠ d 1)
    (h0 : z.val 0 = w.val 0) (h1 : z.val 1 = w.val 1) : z = w := by
  have h2 : z.val 2 = w.val 2 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
    rw [diagonal_third_coordinate z d hz, diagonal_third_coordinate w d hw, h0, h1]
  apply Subtype.ext
  ext r
  fin_cases r
  · exact h0
  · exact h1
  · exact h2

theorem targetEigenvalues_zero_ne_one : targetEigenvalues 0 ≠ targetEigenvalues 1 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [targetEigenvalues, targetAlpha, targetBeta] at hi

theorem unitary_complex_ne_zero (u : unitary ℂ) : u.val ≠ 0 := by
  intro h
  have hn := unitary_complex_norm u
  rw [h, norm_zero] at hn
  norm_num at hn

private theorem eq_of_square_and_decide (a b c : ℂ) (ha : a ^ 2 = c ^ 2)
    (hb : b ^ 2 = c ^ 2) (h : decide (a = c) = decide (b = c)) : a = b := by
  classical
  by_cases hac : a = c
  · have hbc : b = c := by simpa [hac] using h.symm
    exact hac.trans hbc.symm
  · have hbc : b ≠ c := by simpa [hac] using h.symm
    exact ((sq_eq_sq_iff_eq_or_eq_neg.mp ha).resolve_left hac).trans
      ((sq_eq_sq_iff_eq_or_eq_neg.mp hb).resolve_left hbc).symm

def midpointFiber (u : unitary ℂ) :=
  {z : UnitSphere // (symmetricMap z).val.val = u.val • targetMatrix targetAlpha targetBeta}

theorem midpointFiber_finite_card_le_four (u : unitary ℂ) (hu : u.val ^ 3 = -1) :
    Finite (midpointFiber u) ∧ Nat.card (midpointFiber u) ≤ 4 := by
  classical
  by_cases hF : Nonempty (midpointFiber u)
  · let z : midpointFiber u := Classical.choice hF
    let f : midpointFiber u → Fin 2 → Bool := fun w r ↦
      decide ((rotationSphere w.val).val r.castSucc = (rotationSphere z.val).val r.castSucc)
    have hf : Function.Injective f := by
      intro a b hab
      have hc (r : Fin 2) :
          (rotationSphere a.val).val r.castSucc = (rotationSphere b.val).val r.castSucc :=
        eq_of_square_and_decide _ _ _
          (midpoint_same_first_two_squares a.val z.val u hu a.property z.property r)
          (midpoint_same_first_two_squares b.val z.val u hu b.property z.property r)
          (congrFun hab r)
      apply Subtype.ext
      apply rotationSphere_involutive.injective
      apply diagonal_first_two_injective (rotationSphere a.val) (rotationSphere b.val)
        (fun r ↦ u.val * targetEigenvalues r) (midpoint_diagonalized a.val u.val a.property)
        (midpoint_diagonalized b.val u.val b.property)
      · exact fun h ↦ targetEigenvalues_zero_ne_one (mul_left_cancel₀ (unitary_complex_ne_zero u) h)
      · exact hc 0
      · exact hc 1
    let : Finite (midpointFiber u) := Finite.of_injective f hf
    let : Fintype (midpointFiber u) := Fintype.ofFinite _
    refine ⟨inferInstance, ?_⟩
    calc
      Nat.card (midpointFiber u) = Fintype.card (midpointFiber u) := Nat.card_eq_fintype_card
      _ ≤ Fintype.card (Fin 2 → Bool) := Fintype.card_le_of_injective f hf
      _ = 4 := by simp
  · let : IsEmpty (midpointFiber u) := not_nonempty_iff.mp hF
    exact ⟨inferInstance, by simp⟩

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

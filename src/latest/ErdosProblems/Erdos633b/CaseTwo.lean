import ErdosProblems.Erdos633b.RightGeometry
import ErdosProblems.Erdos633b.PatchAssembly
import ErdosProblems.Erdos633b.CaseSeven

/-! Sufficiency of the rational-leg right-triangle case, with the exact biquadratic count. -/

namespace Erdos633b

theorem Triangle.angle_dilate (T : Triangle) (r : ℝ) (hr : r ≠ 0) (i : Fin 3) :
    (T.dilate r hr).angle i = T.angle i := by
  simp only [Triangle.angle, Triangle.dilate_points, EuclideanGeometry.angle, vsub_eq_sub,
    ← smul_sub, InnerProductGeometry.angle_smul_smul hr]

theorem Triangle.side_reindex (T : Triangle) (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    Triangle.side (T.reindex e) i = T.side (e.symm i) := by
  have hab : e.symm (i + 1) ≠ e.symm i := e.symm.injective.ne (by fin_cases i <;> decide)
  have hbc : e.symm i ≠ e.symm (i + 2) := e.symm.injective.ne (by fin_cases i <;> decide)
  have hac : e.symm (i + 1) ≠ e.symm (i + 2) := e.symm.injective.ne (by fin_cases i <;> decide)
  change dist (T.points (e.symm (i + 1))) (T.points (e.symm (i + 2))) =
    dist (T.points (e.symm i + 1)) (T.points (e.symm i + 2))
  obtain ⟨ha, hc⟩ | ⟨ha, hc⟩ := fin_three_other_indices _ _ _ hab hbc hac
  · rw [ha, hc]
  · rw [ha, hc, dist_comm]

/-- The biquadratic tiling for an actual right triangle with integral legs. -/
noncomputable def integer_right_tiling (T : Triangle) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hangle : T.angle 2 = Real.pi / 2) (hav : T.side 0 = a) (hbv : T.side 1 = b) :
    Tiling T (a ^ 2 + b ^ 2) := by
  let c := T.side 2
  have hc : 0 < c := T.side_pos 2
  let U := T.dilate c hc.ne'
  have hUright : U.angle 2 = Real.pi / 2 := (T.angle_dilate c hc.ne' 2).trans hangle
  have hUside (i : Fin 3) : U.side i = c * T.side i := by
    rw [Triangle.side_dilate, abs_of_pos hc]
  have hU0 : U.side 0 = c * a := by rw [hUside, hav]
  have hU1 : U.side 1 = c * b := by rw [hUside, hbv]
  have hU2 : U.side 2 = c ^ 2 := by rw [hUside]; exact (pow_two c).symm
  let w := U.side 1 ^ 2 / U.side 2 ^ 2
  have hw := U.right_weight_bounds hUright
  let R := U.edgeFirst w hw.1
  let S := U.edgeSecond w hw.2
  have hR := U.right_edgeFirst_sides hUright
  have hS := U.right_edgeSecond_sides hUright
  change R.side 0 = U.side 1 ^ 2 / U.side 2 ∧
    R.side 1 = U.side 0 * U.side 1 / U.side 2 ∧ R.side 2 = U.side 1 at hR
  change S.side 0 = U.side 0 ^ 2 / U.side 2 ∧
    S.side 1 = U.side 0 * U.side 1 / U.side 2 ∧ S.side 2 = U.side 0 at hS
  rw [hU0, hU1, hU2] at hR hS
  let T' : Triangle := T.reindex (Equiv.swap 0 1)
  have ht0 : T'.side 0 = T.side 1 := by rw [Triangle.side_reindex]; rfl
  have ht1 : T'.side 1 = T.side 0 := by rw [Triangle.side_reindex]; rfl
  have ht2 : T'.side 2 = T.side 2 := by
    rw [Triangle.side_reindex]
    congr 1
  have hrside : ∀ i, R.side i = (b : ℝ) * T'.side i := by
    intro i
    fin_cases i
    · change R.side 0 = (b : ℝ) * T'.side 0
      rw [hR.1, ht0, hbv]
      field_simp [hc.ne']
    · change R.side 1 = (b : ℝ) * T'.side 1
      rw [hR.2.1, ht1, hav]
      field_simp [hc.ne']
    · change R.side 2 = (b : ℝ) * T'.side 2
      rw [hR.2.2, ht2]
      change c * b = (b : ℝ) * c
      ring
  have hsside : ∀ i, S.side i = (a : ℝ) * T.side i := by
    intro i
    fin_cases i
    · change S.side 0 = (a : ℝ) * T.side 0
      rw [hS.1, hav]
      field_simp [hc.ne']
    · change S.side 1 = (a : ℝ) * T.side 1
      rw [hS.2.1, hbv]
      field_simp [hc.ne']
    · change S.side 2 = (a : ℝ) * T.side 2
      rw [hS.2.2]
      change c * a = (a : ℝ) * c
      ring
  have first : Patch T R.support (b ^ 2) :=
    (quadratic_patch_congruent T' R b hb hrside).changeTile (T.support_reindex _)
  have second := quadratic_patch_congruent T S a ha hsside
  have enlarged := edge_patch_assemble U T w hw.1 hw.2 (b ^ 2) (a ^ 2) first second
  have result := enlarged.dilate c⁻¹ (inv_ne_zero hc.ne')
  change Tiling ((T.dilate c hc.ne').dilate c⁻¹ _) (b ^ 2 + a ^ 2) at result
  rw [T.dilate_inv, Nat.add_comm] at result
  exact result

/-- Normalize a rational leg ratio, build the dissection, and return to the original triangle. -/
noncomputable def rational_right_tiling (T : Triangle) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hangle : T.angle 2 = Real.pi / 2)
    (hratio : T.side 0 / T.side 1 = (m : ℝ) / k) : Tiling T (m ^ 2 + k ^ 2) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  let r := (k : ℝ) / T.side 1
  have hr : 0 < r := div_pos hkr (T.side_pos 1)
  let R := T.dilate r hr.ne'
  have ha : R.angle 2 = Real.pi / 2 := (T.angle_dilate r hr.ne' 2).trans hangle
  have h0 : R.side 0 = m := by
    rw [Triangle.side_dilate, abs_of_pos hr]
    change (k : ℝ) / T.side 1 * T.side 0 = m
    calc
      _ = (T.side 0 / T.side 1) * k := by ring
      _ = ((m : ℝ) / k) * k := by rw [hratio]
      _ = m := div_mul_cancel₀ _ hkr.ne'
  have h1 : R.side 1 = k := by
    rw [Triangle.side_dilate, abs_of_pos hr]
    exact div_mul_cancel₀ _ (T.side_pos 1).ne'
  have result := (integer_right_tiling R m k hm hk ha h0 h1).dilate r⁻¹ (inv_ne_zero hr.ne')
  change Tiling ((T.dilate r hr.ne').dilate r⁻¹ _) (m ^ 2 + k ^ 2) at result
  rwa [T.dilate_inv] at result

theorem case_two_sufficient (T : Triangle) (hangle : T.angle 2 = Real.pi / 2)
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hratio : T.side 0 / T.side 1 = (m : ℝ) / k) (hn : ¬ IsSquare (m ^ 2 + k ^ 2)) :
    HasNonsquareTiling T :=
  ⟨m ^ 2 + k ^ 2, hn, ⟨rational_right_tiling T m k hm hk hangle hratio⟩⟩

theorem case_two_sufficient_reindexed (T : Triangle) (e : Equiv.Perm (Fin 3))
    (hangle : T.angle (e 2) = Real.pi / 2) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hratio : T.side (e 0) / T.side (e 1) = (m : ℝ) / k)
    (hn : ¬ IsSquare (m ^ 2 + k ^ 2)) : HasNonsquareTiling T := by
  have result := case_two_sufficient (T.reindex e.symm)
    (by simpa only [Triangle.angle_reindex, Equiv.symm_symm] using hangle) m k hm hk
    (by simpa only [Triangle.side_reindex, Equiv.symm_symm] using hratio) hn
  exact hasNonsquareTiling_of_support_eq (T.support_reindex e.symm) result

end Erdos633b

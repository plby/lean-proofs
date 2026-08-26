import ErdosProblems.Erdos1148.PrimitiveLatticeVectors
import ErdosProblems.Erdos1148.FlowShortVectorIntervals

/-! # An orbit cannot leave and return to a high cusp in a short interval -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem cusp_between_of_short_time_gap (g : SL(2, ℝ)) {H a b : ℝ} (hH : 0 < H)
    (hab : a ≤ b) (hgap : Real.exp (b - a) ≤ H ^ 4)
    (ha : modularMk (g * diagonalFlow a) ∈ modularCusp H)
    (hb : modularMk (g * diagonalFlow b) ∈ modularCusp H) :
    ∀ t ∈ Set.Icc a b, modularMk (g * diagonalFlow t) ∈ modularCusp H := by
  obtain ⟨u, v, huv, hshorta⟩ := (mem_modularCusp_iff_primitive _ H).mp ha
  obtain ⟨w, z, hwz, hshortb⟩ := (mem_modularCusp_iff_primitive _ H).mp hb
  have hframe : (g * diagonalFlow b) * diagonalFlow (a - b) = g * diagonalFlow a := by
    rw [mul_assoc, ← diagonalFlow_add, add_sub_cancel]
  have hback : modularVectorLengthSq (g * diagonalFlow a) w z ≤
      Real.exp (b - a) * modularVectorLengthSq (g * diagonalFlow b) w z := by
    have h := modularVectorLengthSq_flow_le (g * diagonalFlow b) (a - b) w z
    rwa [hframe, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub] at h
  have hbackshort : modularVectorLengthSq (g * diagonalFlow a) w z <
      Real.exp (b - a) * (H ^ 2)⁻¹ :=
    hback.trans_lt (mul_lt_mul_of_pos_left hshortb (Real.exp_pos _))
  have hupper : (H ^ 2)⁻¹ * (Real.exp (b - a) * (H ^ 2)⁻¹) ≤ 1 := by
    have heq : (H ^ 2)⁻¹ * (Real.exp (b - a) * (H ^ 2)⁻¹) =
        Real.exp (b - a) / H ^ 4 := by field_simp
    rw [heq]
    exact (div_le_one (pow_pos hH 4)).mpr hgap
  have hproduct : modularVectorLengthSq (g * diagonalFlow a) u v *
      modularVectorLengthSq (g * diagonalFlow a) w z < 1 := by
    calc
      _ ≤ modularVectorLengthSq (g * diagonalFlow a) u v *
          (Real.exp (b - a) * (H ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hbackshort.le (by dsimp [modularVectorLengthSq]; positivity)
      _ < (H ^ 2)⁻¹ * (Real.exp (b - a) * (H ^ 2)⁻¹) :=
        mul_lt_mul_of_pos_right hshorta (by positivity)
      _ ≤ 1 := hupper
  have hdet := int_pair_determinant_eq_zero_of_short_product (g * diagonalFlow a) u v w z hproduct
  have hshortb' : modularVectorLengthSq (g * diagonalFlow b) u v < (H ^ 2)⁻¹ :=
    (primitive_vector_lengthSq_le _ huv hwz.ne_zero_or_ne_zero hdet).trans_lt hshortb
  intro t ht
  apply (mem_modularCusp_iff_primitive _ H).mpr
  exact ⟨u, v, huv, (convex_short_vector_times g u v ((H ^ 2)⁻¹)).ordConnected.out
    hshorta hshortb' ht⟩

theorem cusp_between_of_log_time_gap (g : SL(2, ℝ)) {H a b : ℝ} (hH : 0 < H)
    (hab : a ≤ b) (hgap : b - a ≤ 4 * Real.log H)
    (ha : modularMk (g * diagonalFlow a) ∈ modularCusp H)
    (hb : modularMk (g * diagonalFlow b) ∈ modularCusp H) :
    ∀ t ∈ Set.Icc a b, modularMk (g * diagonalFlow t) ∈ modularCusp H := by
  apply cusp_between_of_short_time_gap g hH hab ?_ ha hb
  have hexp : Real.exp (4 * Real.log H) = H ^ 4 := by
    have hlog : Real.log (H ^ 4) = 4 * Real.log H := by rw [Real.log_pow]; norm_num
    rw [← hlog, Real.exp_log (pow_pos hH 4)]
  exact (Real.exp_le_exp.mpr hgap).trans_eq hexp

theorem ordConnected_cusp_visit_window (g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    (n : ℕ) (hwindow : Real.exp (n : ℝ) ≤ H ^ 4) :
    Set.OrdConnected {i : Fin n | modularMk (g * diagonalFlow (i.val : ℝ)) ∈ modularCusp H} := by
  constructor
  intro i hi j hj t ht
  have hij : (i.val : ℝ) ≤ j.val := by exact_mod_cast ht.1.trans ht.2
  have hgap : Real.exp ((j.val : ℝ) - i.val) ≤ H ^ 4 := by
    apply (Real.exp_le_exp.mpr ?_).trans hwindow
    have hjn : (j.val : ℝ) < n := by exact_mod_cast j.isLt
    have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    linarith
  exact cusp_between_of_short_time_gap g hH hij hgap hi hj (t.val : ℝ)
    ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩

end Erdos1148.DukeArithmetic

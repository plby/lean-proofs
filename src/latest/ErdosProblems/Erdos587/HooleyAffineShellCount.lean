import ErdosProblems.Erdos587.HooleyDyadicShell

/-! # Tolerance shells with an additive counting error -/

open scoped BigOperators

namespace Erdos587

lemma delta_sum_half_pow_le_two (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j) ≤ 2 := by
  have heq (J : ℕ) : (∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j) =
      2 - (1 / 2 : ℝ) ^ J := by
    induction J with
    | zero => norm_num
    | succ J ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [heq]
  have h := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) J
  linarith

theorem delta_sum_majorant_of_dyadic_affine_count {ι : Type*} (S : Finset ι)
    (w u : ι → ℝ) (J : ℕ) {A D E : ℝ} (_hA : 0 ≤ A) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hu0 : ∀ x ∈ S, 0 ≤ u x)
    (hu : ∀ x ∈ S, u x ≤ 2 ^ J)
    (hcount : ∀ j ≤ J, ((S.filter (fun x => u x ≤ 2 ^ j)).card : ℝ) ≤ A * 2 ^ j + E)
    (hpoint : ∀ x ∈ S, w x ≤ D / (1 + u x)) :
    (∑ x ∈ S, w x) ≤ 2 * A * D * (J + 1) + 4 * D * E := by
  classical
  apply (delta_sum_le_dyadic_shells S w u J hw hu).trans
  have hlevel (j : ℕ) (hj : j ≤ J) :
      (∑ x ∈ S with DeltaDyadicShell (u x) j, w x) ≤
        2 * A * D + (2 * D * E) * (1 / 2 : ℝ) ^ j := by
    let T := S.filter (fun x => DeltaDyadicShell (u x) j)
    have hcard : (T.card : ℝ) ≤ A * 2 ^ j + E := by
      apply le_trans _ (hcount j hj)
      exact_mod_cast Finset.card_le_card (show T ⊆ S.filter (fun x => u x ≤ 2 ^ j) from by
        intro x hx
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩)
    have hbound (x : ι) (hx : x ∈ T) : w x ≤ 2 * D / 2 ^ j := by
      have hxS := (Finset.mem_filter.mp hx).1
      apply (hpoint x hxS).trans
      apply (div_le_div_iff₀ (by linarith [hu0 x hxS]) (by positivity)).mpr
      have hs := delta_shell_scale_le (hu0 x hxS) (Finset.mem_filter.mp hx).2
      nlinarith [mul_le_mul_of_nonneg_left hs hD]
    calc
      _ ≤ ∑ _x ∈ T, 2 * D / 2 ^ j := Finset.sum_le_sum hbound
      _ = (T.card : ℝ) * (2 * D / 2 ^ j) := by simp
      _ ≤ (A * 2 ^ j + E) * (2 * D / 2 ^ j) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by rw [one_div_pow]; field_simp
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1), (2 * A * D + (2 * D * E) * (1 / 2 : ℝ) ^ j) :=
      Finset.sum_le_sum (fun j hj => hlevel j (by simpa using Finset.mem_range.mp hj))
    _ = 2 * A * D * (J + 1) +
        (2 * D * E) * ∑ j ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ j := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ 2 * A * D * (J + 1) + (2 * D * E) * 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (delta_sum_half_pow_le_two J) (by positivity))
    _ = _ := by ring

end Erdos587

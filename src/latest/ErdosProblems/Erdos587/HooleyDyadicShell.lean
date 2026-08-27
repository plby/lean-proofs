import ErdosProblems.Erdos587.HooleyFiniteCover

/-! # Dyadic tolerance shells without an extra harmonic logarithm -/

open scoped BigOperators

namespace Erdos587

def DeltaDyadicShell (u : ℝ) (j : ℕ) : Prop :=
  u ≤ 2 ^ j ∧ (j = 0 ∨ 2 ^ j < 2 * u)

lemma exists_delta_dyadic_shell {u : ℝ} {J : ℕ} (hu : u ≤ 2 ^ J) :
    ∃ j ≤ J, DeltaDyadicShell u j := by
  induction J with
  | zero => exact ⟨0, le_rfl, hu, Or.inl rfl⟩
  | succ J ih =>
    by_cases h : u ≤ 2 ^ J
    · obtain ⟨j, hj, hs⟩ := ih h
      exact ⟨j, hj.trans (Nat.le_succ J), hs⟩
    · refine ⟨J + 1, le_rfl, hu, Or.inr ?_⟩
      rw [pow_succ]
      linarith

lemma delta_shell_scale_le {u : ℝ} {j : ℕ} (hu : 0 ≤ u)
    (hs : DeltaDyadicShell u j) : (2 : ℝ) ^ j ≤ 2 * (1 + u) := by
  rcases hs.2 with rfl | h
  · norm_num
    linarith
  · linarith

open Classical in
theorem delta_sum_le_dyadic_shells {ι : Type*} (S : Finset ι)
    (w u : ι → ℝ) (J : ℕ) (hw : ∀ x ∈ S, 0 ≤ w x)
    (hu : ∀ x ∈ S, u x ≤ 2 ^ J) :
    (∑ x ∈ S, w x) ≤ ∑ j ∈ Finset.range (J + 1),
      ∑ x ∈ S with DeltaDyadicShell (u x) j, w x := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨j, hj, hs⟩ := exists_delta_dyadic_shell (hu x hx)
  calc
    w x = if DeltaDyadicShell (u x) j then w x else 0 := by rw [if_pos hs]
    _ ≤ ∑ j ∈ Finset.range (J + 1), if DeltaDyadicShell (u x) j then w x else 0 := by
      apply Finset.single_le_sum (s := Finset.range (J + 1))
        (f := fun i : ℕ => if DeltaDyadicShell (u x) i then w x else 0)
      · intro i hi
        split_ifs <;> first | exact hw x hx | exact le_rfl
      · exact Finset.mem_range.mpr (by omega)

theorem delta_sum_majorant_of_dyadic_count {ι : Type*} (S : Finset ι)
    (w u : ι → ℝ) (J : ℕ) {A D : ℝ} (_hA : 0 ≤ A) (hD : 0 ≤ D)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hu0 : ∀ x ∈ S, 0 ≤ u x)
    (hu : ∀ x ∈ S, u x ≤ 2 ^ J)
    (hcount : ∀ j ≤ J, ((S.filter (fun x => u x ≤ 2 ^ j)).card : ℝ) ≤ A * 2 ^ j)
    (hpoint : ∀ x ∈ S, w x ≤ D / (1 + u x)) :
    (∑ x ∈ S, w x) ≤ 2 * A * D * (J + 1) := by
  classical
  apply (delta_sum_le_dyadic_shells S w u J hw hu).trans
  have hlevel (j : ℕ) (hj : j ≤ J) :
      (∑ x ∈ S with DeltaDyadicShell (u x) j, w x) ≤ 2 * A * D := by
    let T := S.filter (fun x => DeltaDyadicShell (u x) j)
    have hcard : (T.card : ℝ) ≤ A * 2 ^ j := by
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
      _ ≤ (A * 2 ^ j) * (2 * D / 2 ^ j) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * A * D := by field_simp
  calc
    _ ≤ ∑ _j ∈ Finset.range (J + 1), 2 * A * D :=
      Finset.sum_le_sum (fun j hj => hlevel j (by simpa using Finset.mem_range.mp hj))
    _ = _ := by simp; ring

lemma delta_sum_two_pow (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j) = 2 ^ (J + 1) - 1 := by
  induction J with
  | zero => norm_num
  | succ J ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma delta_sum_dyadic_shell_cost (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * ((J - j : ℕ) + 3)) ≤
      8 * 2 ^ J := by
  have hexact (J : ℕ) :
      (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * ((J - j : ℕ) + 3)) =
        8 * 2 ^ J - (J + 5) := by
    induction J with
    | zero => norm_num
    | succ J ih =>
      rw [Finset.sum_range_succ]
      have hshift : (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * ((J + 1 - j : ℕ) + 3)) =
          (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * ((J - j : ℕ) + 3)) +
            ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjJ : j ≤ J := by simpa using Finset.mem_range.mp hj
        have heq : J + 1 - j = (J - j) + 1 := by omega
        rw [heq, Nat.cast_add, Nat.cast_one]
        ring
      rw [hshift, ih, delta_sum_two_pow]
      simp only [Nat.sub_self, Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      ring
  rw [hexact]
  have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  linarith

end Erdos587

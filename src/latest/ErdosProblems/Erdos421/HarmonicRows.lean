import ErdosProblems.Erdos421.DirichletMeanValue
import Mathlib.Data.Nat.Dist
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Harmonic row bounds for logarithmic frequencies -/

namespace Erdos421

theorem inverse_log_nat_difference_bound {m n N : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmN : m ≤ N) (hnN : n ≤ N) (hmn : m ≠ n) :
    1 / |Real.log (m : ℝ) - Real.log (n : ℝ)| ≤ (N : ℝ) / (Nat.dist m n : ℝ) := by
  have hordered : ∀ a b : ℕ, 0 < a → a < b → b ≤ N →
      1 / |Real.log (a : ℝ) - Real.log (b : ℝ)| ≤ (N : ℝ) / (Nat.dist a b : ℝ) := by
    intro a b ha hab hbN
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    have hlog : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
      Real.log_le_log ha' hab'.le
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), neg_sub,
      Nat.dist_eq_sub_of_le hab.le, Nat.cast_sub hab.le]
    exact inverse_log_difference_bound ha' hab' (by exact_mod_cast hbN)
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact hordered m n hm hlt hnN
  · rw [abs_sub_comm, Nat.dist_comm]
    exact hordered n m hn hgt hmN

theorem sum_inverse_nat_distance_le (S : Finset ℕ) {m N : ℕ} (hmN : m ≤ N)
    (hSN : ∀ n ∈ S, n ≤ N) :
    (∑ n ∈ S.erase m, (Nat.dist m n : ℝ)⁻¹) ≤ 2 * (harmonic N : ℝ) := by
  classical
  let L := S.filter (fun n ↦ n < m)
  let U := S.filter (fun n ↦ m < n)
  have hL : (∑ n ∈ L, ((m - n : ℕ) : ℝ)⁻¹) ≤ (harmonic N : ℝ) := by
    have hinj : Set.InjOn (fun n ↦ m - n) (↑L : Set ℕ) := by
      intro a ha b hb heq
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      dsimp only at heq
      omega
    have hsub : L.image (fun n ↦ m - n) ⊆ Finset.Icc 1 N := by
      intro d hd
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
      have hn' := (Finset.mem_filter.mp hn).2
      exact Finset.mem_Icc.mpr ⟨by omega, (Nat.sub_le m n).trans hmN⟩
    calc
      _ = ∑ d ∈ L.image (fun n ↦ m - n), (d : ℝ)⁻¹ :=
        (Finset.sum_image hinj).symm
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
      _ = (harmonic N : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hU : (∑ n ∈ U, ((n - m : ℕ) : ℝ)⁻¹) ≤ (harmonic N : ℝ) := by
    have hinj : Set.InjOn (fun n ↦ n - m) (↑U : Set ℕ) := by
      intro a ha b hb heq
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      dsimp only at heq
      omega
    have hsub : U.image (fun n ↦ n - m) ⊆ Finset.Icc 1 N := by
      intro d hd
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hnS, hmn⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega, (Nat.sub_le n m).trans (hSN n hnS)⟩
    calc
      _ = ∑ d ∈ U.image (fun n ↦ n - m), (d : ℝ)⁻¹ :=
        (Finset.sum_image hinj).symm
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
      _ = (harmonic N : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have heq : S.erase m = L ∪ U := by
    ext n
    constructor
    · intro hn
      obtain ⟨hne, hnS⟩ := Finset.mem_erase.mp hn
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnS, hlt⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnS, hgt⟩)
    · intro hn
      rcases Finset.mem_union.mp hn with hn | hn
      · have h := Finset.mem_filter.mp hn
        exact Finset.mem_erase.mpr ⟨h.2.ne, h.1⟩
      · have h := Finset.mem_filter.mp hn
        exact Finset.mem_erase.mpr ⟨h.2.ne', h.1⟩
  have hdisj : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro n hnL hnU
    have := (Finset.mem_filter.mp hnL).2
    have := (Finset.mem_filter.mp hnU).2
    omega
  rw [heq, Finset.sum_union hdisj]
  have hLeq : (∑ n ∈ L, (Nat.dist m n : ℝ)⁻¹) =
      ∑ n ∈ L, ((m - n : ℕ) : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hn).2.le]
  have hUeq : (∑ n ∈ U, (Nat.dist m n : ℝ)⁻¹) =
      ∑ n ∈ U, ((n - m : ℕ) : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.dist_eq_sub_of_le (Finset.mem_filter.mp hn).2.le]
  rw [hLeq, hUeq]
  linarith

theorem sum_inverse_log_difference_le (S : Finset ℕ) {m N : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    (∑ n ∈ S.erase m, 1 / |Real.log (m : ℝ) - Real.log (n : ℝ)|) ≤
      2 * N * (1 + Real.log N) := by
  calc
    _ ≤ ∑ n ∈ S.erase m, (N : ℝ) / (Nat.dist m n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnS := Finset.mem_of_mem_erase hn
      exact inverse_log_nat_difference_bound hm (hS n hnS).1 hmN (hS n hnS).2
        (Finset.ne_of_mem_erase hn).symm
    _ = (N : ℝ) * (∑ n ∈ S.erase m, (Nat.dist m n : ℝ)⁻¹) := by
      simp only [div_eq_mul_inv, Finset.mul_sum]
    _ ≤ (N : ℝ) * (2 * (harmonic N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_inverse_nat_distance_le S hmN (fun n hn ↦ (hS n hn).2))
        (Nat.cast_nonneg N)
    _ ≤ 2 * N * (1 + Real.log N) := by
      have h := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N)
        (show (0 : ℝ) ≤ 2 * N by positivity)
      nlinarith

end Erdos421

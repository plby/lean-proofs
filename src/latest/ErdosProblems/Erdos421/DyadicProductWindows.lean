import ErdosProblems.Erdos421.ProductWindowArithmetic
import ErdosProblems.Erdos421.DyadicDirichlet

/-! # Exact dyadic decomposition of the finite cofactor support -/

namespace Erdos421

open scoped SchwartzMap

def dyadicCofactorSupport (B j : ℕ) : Finset ℕ :=
  (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (fun n ↦ n ≤ B)

theorem dyadicCofactorSupport_bounds (B j : ℕ) {n : ℕ} (hn : n ∈ dyadicCofactorSupport B j) :
    2 ^ j ≤ n ∧ n ≤ 2 * 2 ^ j ∧ n ≤ B := by
  obtain ⟨hnI, hnB⟩ := Finset.mem_filter.mp hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hnI
  rw [pow_succ] at hhi
  exact ⟨hlo, by omega, hnB⟩

theorem dyadicCofactorSupport_pos (B j : ℕ) {n : ℕ} (hn : n ∈ dyadicCofactorSupport B j) :
    0 < n :=
  (pow_pos (by decide : 0 < (2 : ℕ)) j).trans_le (dyadicCofactorSupport_bounds B j hn).1

theorem dyadicCofactorSupport_card_le (B j : ℕ) : (dyadicCofactorSupport B j).card ≤ 2 ^ j := by
  have h := Finset.card_filter_le (Finset.Ico (2 ^ j) (2 ^ (j + 1))) (fun n ↦ n ≤ B)
  rw [Nat.card_Ico, pow_succ] at h
  change (dyadicCofactorSupport B j).card ≤ _ at h
  omega

theorem sum_dyadic_Ico {R : Type*} [AddCommMonoid R] (f : ℕ → R) (K : ℕ) :
    (∑ j ∈ Finset.range K, ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n) =
      ∑ n ∈ Finset.Ico 1 (2 ^ K), f n := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      exact Finset.sum_Ico_consecutive f (one_le_pow₀ (by norm_num))
        (by rw [pow_succ]; omega)

theorem sum_dyadicCofactorSupport {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    {B K : ℕ} (hB : B < 2 ^ K) :
    (∑ n ∈ Finset.Icc 1 B, f n) =
      ∑ j ∈ Finset.range K, ∑ n ∈ dyadicCofactorSupport B j, f n := by
  have hset : (Finset.Ico 1 (2 ^ K)).filter (fun n ↦ n ≤ B) = Finset.Icc 1 B := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [← hset, Finset.sum_filter, ← sum_dyadic_Ico (fun n ↦ if n ≤ B then f n else 0) K]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dyadicCofactorSupport, Finset.sum_filter]

theorem scaledProductWindow_dyadic (T : Finset ℕ) (a b : ℕ → ℂ) (σ : ℝ)
    (φ : 𝓢(ℝ, ℂ)) {B K : ℕ} (hB : B < 2 ^ K) (δ y : ℝ) :
    scaledProductWindow (Finset.Icc 1 B) T a b σ φ δ y =
      ∑ j ∈ Finset.range K, scaledProductWindow (dyadicCofactorSupport B j) T a b σ φ δ y := by
  unfold scaledProductWindow
  exact sum_dyadicCofactorSupport _ hB

end Erdos421

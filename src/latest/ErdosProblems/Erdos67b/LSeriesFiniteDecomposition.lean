import Mathlib.NumberTheory.LSeries.Basic

/-! # Finite interval bookkeeping for the high-height L-series split -/

open scoped BigOperators

namespace Erdos67b.LSeriesFiniteDecomposition

/-- Split a finite series into low, middle, and high pieces.  The zeroth
L-series term vanishes, so it is omitted from the displayed decomposition. -/
theorem sum_range_eq_low_add_middle_add_high
    (f : ℕ → ℂ) {M K H : ℕ} (hf0 : f 0 = 0)
    (hM : 0 < M) (hMK : M ≤ K) (hKH : K < H) :
    (∑ n ∈ Finset.range H, f n) =
      (∑ n ∈ Finset.Icc 1 M, f n) +
        (∑ n ∈ Finset.Ioc M K, f n) +
          ∑ n ∈ Finset.Ioc K (H - 1), f n := by
  have h1M : 1 ≤ M + 1 := by omega
  have hMK' : M + 1 ≤ K + 1 := by omega
  have hKH' : K + 1 ≤ H := by omega
  have hzero : (∑ n ∈ Finset.Ico 0 1, f n) = 0 := by
    simp [hf0]
  have hlow : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hmiddle : Finset.Ico (M + 1) (K + 1) = Finset.Ioc M K := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have hhigh : Finset.Ico (K + 1) H = Finset.Ioc K (H - 1) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have hsplit0 := Finset.sum_Ico_consecutive f
    (m := 0) (n := 1) (k := H) (by omega) (by omega)
  have hsplit1 := Finset.sum_Ico_consecutive f
    (m := 1) (n := M + 1) (k := H) h1M (by omega)
  have hsplit2 := Finset.sum_Ico_consecutive f
    (m := M + 1) (n := K + 1) (k := H) hMK' hKH'
  have hrange : Finset.range H = Finset.Ico 0 H := by
    ext n
    simp
  rw [hrange]
  rw [← hsplit0, hzero, zero_add]
  rw [← hsplit1, ← hsplit2]
  rw [hlow, hmiddle, hhigh]
  ring

end Erdos67b.LSeriesFiniteDecomposition

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Integral over a finite time partition

Integrability on each adjacent interval suffices to sum the signed interval
integrals. No regularity at the finitely many partition points is required.
-/

namespace NoExoticSixSphere.IntervalPartition

theorem exists_mem_adjacent {m : ℕ} (τ : Fin (m + 2) → ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (τ 0) (τ (Fin.last (m + 1)))) :
    ∃ i : Fin (m + 1), t ∈ Set.Icc (τ i.castSucc) (τ i.succ) := by
  induction m with
  | zero => exact ⟨0, ht⟩
  | succ m ih =>
    by_cases h : t ≤ τ (0 : Fin (m + 2)).succ
    · exact ⟨0, ht.1, h⟩
    · obtain ⟨i, hi⟩ := ih (fun j ↦ τ j.succ) ⟨(lt_of_not_ge h).le, ht.2⟩
      exact ⟨i.succ, hi⟩

theorem integral_eq_sum_adjacent {N : ℕ} (τ : Fin (N + 1) → ℝ) (f : ℝ → ℝ)
    (hf : ∀ i : Fin N, IntervalIntegrable f MeasureTheory.volume (τ i.castSucc) (τ i.succ)) :
    (∫ t : ℝ in τ 0..τ (Fin.last N), f t) =
      ∑ i : Fin N, ∫ t : ℝ in τ i.castSucc..τ i.succ, f t := by
  have hpart (k : Fin (N + 1)) : IntervalIntegrable f MeasureTheory.volume (τ 0) (τ k) := by
    induction k using Fin.inductionOn with
    | zero => simp
    | succ i ih => exact ih.trans (hf i)
  let F : Fin (N + 1) → ℝ := fun k ↦ ∫ t : ℝ in τ 0..τ k, f t
  have he (i : Fin N) : (∫ t : ℝ in τ i.castSucc..τ i.succ, f t) =
      F i.succ - F i.castSucc := by
    have h := intervalIntegral.integral_add_adjacent_intervals (hpart i.castSucc) (hf i)
    change F i.castSucc + (∫ t : ℝ in τ i.castSucc..τ i.succ, f t) = F i.succ at h
    linarith
  have hs : (∑ i : Fin N, (F i.succ - F i.castSucc)) = F (Fin.last N) - F 0 := by
    rw [Finset.sum_sub_distrib]
    have hleft := Fin.sum_univ_succ F
    have hright := Fin.sum_univ_castSucc F
    linarith
  simp_rw [he]
  rw [hs]
  simp only [F, intervalIntegral.integral_same, sub_zero]

end NoExoticSixSphere.IntervalPartition

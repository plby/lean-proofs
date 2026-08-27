import Arxiv.Arxiv2411_18291.CriticalWindowProcess

/-!
# Entry into a critical interval with a bounded overshoot

Before an upper crossing, take the step after the last value below the
lower boundary. The starting value is at most the lower boundary plus
one increment bound, and the path stays above the lower boundary until
the crossing. This is a deterministic statement about a finite sequence.
-/

open Finset

namespace Arxiv2411_18291

theorem exists_critical_window_start {A : ℕ → ℝ} {l u b : ℝ} {j : ℕ}
    (hb : 0 ≤ b) (h0 : A 0 < l) (hgap : l + b < u) (hcross : u ≤ A j)
    (hstep : ∀ i < j, A (i + 1) - A i ≤ b) :
    ∃ s, 0 < s ∧ s < j ∧ A s ≤ l + b ∧ ∀ k, s ≤ k → k < j → l ≤ A k := by
  classical
  have hlu : l < u := by linarith only [hb, hgap]
  have hj : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    rw [hj0] at hcross
    linarith only [h0, hlu, hcross]
  let B := (range j).filter fun i => A i < l
  have hB0 : 0 ∈ B := mem_filter.mpr ⟨mem_range.mpr hj, h0⟩
  let m := B.max' ⟨0, hB0⟩
  have hm : m ∈ B := B.max'_mem ⟨0, hB0⟩
  have hmj : m < j := mem_range.mp (mem_filter.mp hm).1
  have hml : A m < l := (mem_filter.mp hm).2
  have hnext : A (m + 1) < l + b := by
    have h := hstep m hmj
    linarith only [h, hml]
  have hsj : m + 1 < j := by
    by_contra h
    have heq : m + 1 = j := by omega
    rw [heq] at hnext
    linarith only [hnext, hgap, hcross]
  refine ⟨m + 1, by omega, hsj, hnext.le, ?_⟩
  intro k hmk hkj
  by_contra h
  have hk : k ∈ B := mem_filter.mpr ⟨mem_range.mpr hkj, lt_of_not_ge h⟩
  have hkm : k ≤ m := B.le_max' k hk
  omega

end Arxiv2411_18291

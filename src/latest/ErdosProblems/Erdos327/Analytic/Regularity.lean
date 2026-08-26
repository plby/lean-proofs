import ErdosProblems.Erdos327.Analytic.PrimeRangeWeight
import ErdosProblems.Erdos327.Analytic.RoughCount
import ErdosProblems.Erdos327.Defs

/-!
# Centered cutoff regularity and the canonical source/host sets

This file defines the regularity condition used in the analytic proof
and packages the exact finite-set cardinality bookkeeping for the rough
source and the odd host.  No analytic estimate is assumed here.
-/

namespace Erdos327.Analytic

open Finset Real

/-- The centered prime-factor budget from the paper. -/
def CutoffRegular (L : ℕ) (A K : ℝ) (n : ℕ) : Prop :=
  ∀ x : ℕ, L ≤ x →
    (primeFactorCountBetween L x n : ℝ) ≤
      A * log (log x / log L) + K

noncomputable instance cutoffRegularDecidable
    (L : ℕ) (A K : ℝ) (n : ℕ) :
    Decidable (CutoffRegular L A K n) :=
  Classical.propDecidable _

theorem not_cutoffRegular_iff {L n : ℕ} {A K : ℝ} :
    ¬CutoffRegular L A K n ↔
      ∃ x : ℕ, L ≤ x ∧
        A * log (log x / log L) + K <
          (primeFactorCountBetween L x n : ℝ) := by
  unfold CutoffRegular
  push Not
  rfl

/-- Increasing the additive budget preserves regularity. -/
theorem CutoffRegular.mono_K
    {L n : ℕ} {A K K' : ℝ}
    (h : CutoffRegular L A K n) (hKK' : K ≤ K') :
    CutoffRegular L A K' n := by
  intro x hx
  exact (h x hx).trans (by linarith)

/-- The injective parametrization `k ↦ 2k+1` of the first `N` positive
odd integers. -/
def oddEmbedding : ℕ ↪ ℕ where
  toFun k := k + k + 1
  inj' := by
    intro a b h
    have hsum : a + a = b + b := Nat.add_right_cancel h
    exact Nat.mul_left_cancel (by omega : 0 < 2)
      (by simpa [two_mul] using hsum)

@[simp] theorem oddEmbedding_apply (k : ℕ) :
    oddEmbedding k = k + k + 1 := rfl

/-- Exactly the `N` positive odd integers at most `2N`. -/
def oddHost (N : ℕ) : Finset ℕ :=
  (range N).map oddEmbedding

@[simp] theorem mem_oddHost {N a : ℕ} :
    a ∈ oddHost N ↔ ∃ k < N, 2 * k + 1 = a := by
  constructor
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨k, hk, hka⟩
    refine ⟨k, mem_range.mp hk, ?_⟩
    rw [oddEmbedding_apply] at hka
    simpa [two_mul] using hka
  · rintro ⟨k, hk, rfl⟩
    apply Finset.mem_map.mpr
    refine ⟨k, mem_range.mpr hk, ?_⟩
    rw [oddEmbedding_apply]
    simp [two_mul]

@[simp] theorem card_oddHost (N : ℕ) :
    (oddHost N).card = N := by
  simp [oddHost]

theorem oddHost_subset_upto (N : ℕ) :
    oddHost N ⊆ Erdos327.upto (2 * N) := by
  intro a ha
  rcases mem_oddHost.mp ha with ⟨k, hk, rfl⟩
  apply Erdos327.mem_upto.mpr
  omega

theorem odd_of_mem_oddHost {N a : ℕ} (ha : a ∈ oddHost N) :
    Odd a := by
  rcases mem_oddHost.mp ha with ⟨k, _hk, rfl⟩
  exact ⟨k, by omega⟩

/-- The rough, centered-regular source in `[N/2,N]`. -/
noncomputable def regularSource
    (L : ℕ) (A K : ℝ) (N : ℕ) : Finset ℕ :=
  (roughSourceInterval L N).filter (CutoffRegular L A K)

@[simp] theorem mem_regularSource
    {L N n : ℕ} {A K : ℝ} :
    n ∈ regularSource L A K N ↔
      N / 2 ≤ n ∧ n ≤ N ∧ Rough L n ∧
        CutoffRegular L A K n := by
  simp only [regularSource, mem_filter, mem_roughSourceInterval]
  tauto

theorem regularSource_subset_upto
    (L : ℕ) (A K : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    regularSource L A K N ⊆ Erdos327.upto N := by
  intro n hn
  have h := mem_regularSource.mp hn
  exact Erdos327.mem_upto.mpr ⟨by omega, h.2.1⟩

/-- Rough source vertices excluded by the regularity budget. -/
noncomputable def irregularRoughSource
    (L : ℕ) (A K : ℝ) (N : ℕ) : Finset ℕ :=
  (roughSourceInterval L N).filter
    (fun n ↦ ¬CutoffRegular L A K n)

theorem regularSource_eq_sdiff_irregular
    (L : ℕ) (A K : ℝ) (N : ℕ) :
    regularSource L A K N =
      roughSourceInterval L N \ irregularRoughSource L A K N := by
  classical
  ext n
  simp only [regularSource, irregularRoughSource, mem_filter,
    Finset.mem_sdiff]
  tauto

theorem irregularRoughSource_subset
    (L : ℕ) (A K : ℝ) (N : ℕ) :
    irregularRoughSource L A K N ⊆ roughSourceInterval L N := by
  intro n hn
  exact (mem_filter.mp hn).1

theorem card_regularSource_add_irregular
    (L : ℕ) (A K : ℝ) (N : ℕ) :
    (regularSource L A K N).card +
        (irregularRoughSource L A K N).card =
      (roughSourceInterval L N).card := by
  rw [regularSource_eq_sdiff_irregular,
    card_sdiff_of_subset (irregularRoughSource_subset L A K N)]
  exact Nat.sub_add_cancel
    (card_le_card (irregularRoughSource_subset L A K N))

/-- The centered-regular part of the canonical odd host. -/
noncomputable def regularOddHost
    (L : ℕ) (A K : ℝ) (N : ℕ) : Finset ℕ :=
  (oddHost N).filter (CutoffRegular L A K)

@[simp] theorem mem_regularOddHost
    {L N a : ℕ} {A K : ℝ} :
    a ∈ regularOddHost L A K N ↔
      a ∈ oddHost N ∧ CutoffRegular L A K a := by
  simp [regularOddHost]

theorem regularOddHost_subset_upto
    (L : ℕ) (A K : ℝ) (N : ℕ) :
    regularOddHost L A K N ⊆ Erdos327.upto (2 * N) :=
  (filter_subset _ _).trans (oddHost_subset_upto N)

theorem odd_of_mem_regularOddHost
    {L N a : ℕ} {A K : ℝ}
    (ha : a ∈ regularOddHost L A K N) :
    Odd a :=
  odd_of_mem_oddHost (mem_regularOddHost.mp ha).1

/-- Odd host vertices excluded by the regularity budget. -/
noncomputable def irregularOddHost
    (L : ℕ) (A K : ℝ) (N : ℕ) : Finset ℕ :=
  (oddHost N).filter (fun a ↦ ¬CutoffRegular L A K a)

theorem regularOddHost_eq_sdiff_irregular
    (L : ℕ) (A K : ℝ) (N : ℕ) :
    regularOddHost L A K N =
      oddHost N \ irregularOddHost L A K N := by
  classical
  ext n
  simp only [regularOddHost, irregularOddHost, mem_filter,
    Finset.mem_sdiff]
  tauto

theorem irregularOddHost_subset
    (L : ℕ) (A K : ℝ) (N : ℕ) :
    irregularOddHost L A K N ⊆ oddHost N := by
  intro n hn
  exact (mem_filter.mp hn).1

theorem card_regularOddHost_add_irregular
    (L : ℕ) (A K : ℝ) (N : ℕ) :
    (regularOddHost L A K N).card +
        (irregularOddHost L A K N).card = N := by
  rw [regularOddHost_eq_sdiff_irregular,
    card_sdiff_of_subset (irregularOddHost_subset L A K N),
    card_oddHost]
  exact Nat.sub_add_cancel
    (by
      simpa [card_oddHost] using
        card_le_card (irregularOddHost_subset L A K N))

end Erdos327.Analytic

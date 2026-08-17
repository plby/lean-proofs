/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
# Erdős Problem 54: core definitions

This file gives the exact public vocabulary needed to state the resolution of
Erdős Problem 54.  A finite set of elements of the subtype `↑A` is a set of
*distinct* elements of `A`, so `FiniteDistinctSubsetSum` and
`MonochromaticSum` do not permit repetitions.
-/

import Mathlib

namespace Erdos54

open scoped BigOperators

open Filter

/-! ## Positive sets and finite subset sums -/

/-- A set of natural numbers all of whose elements are positive. -/
def PositiveNatSet (A : Set ℕ) : Prop :=
  ∀ a : ↑A, 0 < (a : ℕ)

@[simp] theorem positiveNatSet_iff_zero_not_mem {A : Set ℕ} :
    PositiveNatSet A ↔ 0 ∉ A := by
  constructor
  · intro h h0
    exact (Nat.lt_irrefl 0) (h ⟨0, h0⟩)
  · intro h a
    exact Nat.pos_of_ne_zero fun ha ↦ h (ha ▸ a.property)

@[simp] theorem positiveNatSet_empty : PositiveNatSet (∅ : Set ℕ) := by
  simp

theorem PositiveNatSet.mono {A B : Set ℕ} (hB : PositiveNatSet B)
    (hAB : A ⊆ B) : PositiveNatSet A := by
  rw [positiveNatSet_iff_zero_not_mem] at hB ⊢
  exact fun h0 ↦ hB (hAB h0)

/-- `n` is a sum of a finite set of distinct elements of `A`.

The empty finset is allowed, and hence represents `0`. -/
def FiniteDistinctSubsetSum (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ s : Finset ↑A, ∑ a ∈ s, (a : ℕ) = n

@[simp] theorem finiteDistinctSubsetSum_zero (A : Set ℕ) :
    FiniteDistinctSubsetSum A 0 := by
  exact ⟨∅, by simp⟩

theorem finiteDistinctSubsetSum_singleton {A : Set ℕ} {a : ℕ} (ha : a ∈ A) :
    FiniteDistinctSubsetSum A a := by
  refine ⟨{⟨a, ha⟩}, ?_⟩
  simp

theorem FiniteDistinctSubsetSum.mono {A B : Set ℕ} (hAB : A ⊆ B) {n : ℕ}
    (hn : FiniteDistinctSubsetSum A n) : FiniteDistinctSubsetSum B n := by
  obtain ⟨s, rfl⟩ := hn
  let inclusion : ↑A ↪ ↑B :=
    ⟨fun a ↦ ⟨a, hAB a.property⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun z : ↑B ↦ (z : ℕ)) h)⟩
  refine ⟨s.map inclusion, ?_⟩
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a ha
  rfl

/-! ## Colorings and Ramsey completeness -/

/-- An `r`-coloring of `A`.  The coloring is defined on `A` itself, rather
than on an ambient set, exactly as in the mathematical definition. -/
abbrev Coloring (A : Set ℕ) (r : ℕ) := ↑A → Fin r

/-- A two-coloring of `A`. -/
abbrev TwoColoring (A : Set ℕ) := Coloring A 2

/-- `n` is the sum of a finite set of distinct, identically colored elements
of `A` under `color`. -/
def MonochromaticSum (A : Set ℕ) (r : ℕ) (color : Coloring A r) (n : ℕ) : Prop :=
  ∃ s : Finset ↑A,
    (∃ c : Fin r, ∀ a ∈ s, color a = c) ∧
      ∑ a ∈ s, (a : ℕ) = n

/-- The two-color specialization of `MonochromaticSum`. -/
abbrev MonochromaticTwoSum (A : Set ℕ) (color : TwoColoring A) (n : ℕ) : Prop :=
  MonochromaticSum A 2 color n

theorem MonochromaticSum.toFiniteDistinctSubsetSum {A : Set ℕ} {r n : ℕ}
    {color : Coloring A r} (h : MonochromaticSum A r color n) :
    FiniteDistinctSubsetSum A n := by
  obtain ⟨s, -, hs⟩ := h
  exact ⟨s, hs⟩

theorem monochromaticSum_singleton {A : Set ℕ} {r a : ℕ}
    (color : Coloring A r) (ha : a ∈ A) : MonochromaticSum A r color a := by
  let x : ↑A := ⟨a, ha⟩
  refine ⟨{x}, ?_, ?_⟩
  · refine ⟨color x, ?_⟩
    intro b hb
    simp only [Finset.mem_singleton] at hb
    subst b
    rfl
  · simp [x]

/-- `A` is Ramsey `r`-complete: for every coloring of `A`, the threshold may
depend on that coloring, and every integer beyond it is a monochromatic sum
of finitely many distinct elements of `A`. -/
def RamseyComplete (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ color : Coloring A r, ∃ threshold : ℕ, ∀ n ≥ threshold,
    MonochromaticSum A r color n

/-- The two-color specialization appearing in Erdős Problem 54. -/
abbrev RamseyTwoComplete (A : Set ℕ) : Prop := RamseyComplete 2 A

theorem RamseyComplete.mono {r : ℕ} {A B : Set ℕ} (hAB : A ⊆ B)
    (hA : RamseyComplete r A) : RamseyComplete r B := by
  intro colorB
  let inclusion : ↑A ↪ ↑B :=
    ⟨fun a ↦ ⟨a, hAB a.property⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun z : ↑B ↦ (z : ℕ)) h)⟩
  let colorA : Coloring A r := fun a ↦ colorB (inclusion a)
  obtain ⟨threshold, hthreshold⟩ := hA colorA
  refine ⟨threshold, fun n hn ↦ ?_⟩
  obtain ⟨s, ⟨c, hc⟩, hsum⟩ := hthreshold n hn
  refine ⟨s.map inclusion, ?_, ?_⟩
  · refine ⟨c, ?_⟩
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    exact hc a ha
  · rw [Finset.sum_map]
    exact hsum

theorem RamseyComplete.distinctSubsetSumEventually {r : ℕ} {A : Set ℕ}
    (hA : RamseyComplete r A) (color : Coloring A r) :
    ∃ threshold : ℕ, ∀ n ≥ threshold, FiniteDistinctSubsetSum A n := by
  obtain ⟨threshold, hthreshold⟩ := hA color
  exact ⟨threshold, fun n hn ↦ (hthreshold n hn).toFiniteDistinctSubsetSum⟩

/-! ## The counting function and the Conlon--Fox--Pham bound -/

/-- The number of elements of `A` in the integer interval `{1, …, N}`. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter fun a ↦ a ∈ A).card

@[simp] theorem countUpTo_empty (N : ℕ) : countUpTo ∅ N = 0 := by
  simp [countUpTo]

@[simp] theorem countUpTo_zero (A : Set ℕ) : countUpTo A 0 = 0 := by
  simp [countUpTo]

theorem countUpTo_mono_set {A B : Set ℕ} (hAB : A ⊆ B) (N : ℕ) :
    countUpTo A N ≤ countUpTo B N := by
  classical
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, hAB ha.2⟩

theorem countUpTo_mono (A : Set ℕ) : Monotone (countUpTo A) := by
  intro M N hMN
  classical
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
  exact ⟨⟨ha.1.1, ha.1.2.trans hMN⟩, ha.2⟩

theorem countUpTo_le (A : Set ℕ) (N : ℕ) : countUpTo A N ≤ N := by
  classical
  calc
    countUpTo A N ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
    _ ≤ N := by simp

/-- The `O((log N)^2)` counting bound, with the usual "for all sufficiently
large `N`" interpretation. -/
def HasLogSquaredCountingBound (A : Set ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    (countUpTo A N : ℝ) ≤ C * (Real.log (N : ℝ)) ^ 2

theorem HasLogSquaredCountingBound.mono {A B : Set ℕ} (hAB : A ⊆ B)
    (hB : HasLogSquaredCountingBound B) : HasLogSquaredCountingBound A := by
  obtain ⟨C, hC, hbound⟩ := hB
  refine ⟨C, hC, hbound.mono fun N hN ↦ ?_⟩
  have hAB' : (countUpTo A N : ℝ) ≤ countUpTo B N := by
    exact_mod_cast countUpTo_mono_set hAB N
  exact hAB'.trans hN

/-- The exact existential upper-bound assertion established by Conlon, Fox,
and Pham: there is a positive Ramsey `2`-complete set with counting function
`O((log N)^2)`. -/
def ConlonFoxPhamUpperBoundTwo : Prop :=
  ∃ A : Set ℕ,
    PositiveNatSet A ∧ RamseyTwoComplete A ∧ HasLogSquaredCountingBound A

end Erdos54

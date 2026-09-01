/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import Mathlib

/-!
# Erdős Problem 55: core definitions

This file fixes the public vocabulary used in the formalization of the
Conlon--Fox--Pham resolution of Erdős Problem 55.  A subset sum always uses a
finite set of *distinct* members of `A`.  In the definition of
`RamseyComplete`, the monochromatic color may depend on the integer being
represented, as it does in the source.
-/

namespace Erdos55

open scoped BigOperators

/-- A set of natural numbers all of whose members are positive. -/
def IsPositiveNatSet (A : Set ℕ) : Prop :=
  ∀ ⦃a : ℕ⦄, a ∈ A → 0 < a

/-- The type of sets of positive natural numbers. -/
def PositiveNatSet := {A : Set ℕ // IsPositiveNatSet A}

namespace PositiveNatSet

instance : SetLike PositiveNatSet ℕ where
  coe A := A.1
  coe_injective _ _ h := Subtype.ext h

/-- Package a set and a proof that all its members are positive. -/
@[coe]
def ofSet (A : Set ℕ) (hA : IsPositiveNatSet A) : PositiveNatSet :=
  ⟨A, hA⟩

@[simp]
theorem mem_ofSet {A : Set ℕ} {hA : IsPositiveNatSet A} {a : ℕ} :
    a ∈ ofSet A hA ↔ a ∈ A :=
  Iff.rfl

theorem pos (A : PositiveNatSet) {a : ℕ} (ha : a ∈ A) : 0 < a :=
  A.2 ha

theorem one_le (A : PositiveNatSet) {a : ℕ} (ha : a ∈ A) : 1 ≤ a :=
  A.pos ha

@[simp]
theorem zero_not_mem (A : PositiveNatSet) : 0 ∉ A := fun h ↦
  (A.pos h).ne' rfl

end PositiveNatSet

theorem isPositiveNatSet_iff_zero_not_mem {A : Set ℕ} :
    IsPositiveNatSet A ↔ 0 ∉ A := by
  constructor
  · exact fun h h0 ↦ (h h0).ne' rfl
  · intro h a ha
    exact Nat.pos_of_ne_zero fun ha0 ↦ h (ha0 ▸ ha)

theorem IsPositiveNatSet.mono {A B : Set ℕ} (hB : IsPositiveNatSet B) (hAB : A ⊆ B) :
    IsPositiveNatSet A :=
  fun _ ha ↦ hB (hAB ha)

/-- The set of sums of finite sets of distinct members of `A`.

The empty finset is allowed, so `0` is always a finite subset sum. -/
def finiteSubsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ s : Finset A, (∑ a ∈ s, (a : ℕ)) = n}

/-- Predicate form of membership in `finiteSubsetSums`. -/
def IsFiniteSubsetSum (A : Set ℕ) (n : ℕ) : Prop :=
  n ∈ finiteSubsetSums A

@[simp]
theorem mem_finiteSubsetSums {A : Set ℕ} {n : ℕ} :
    n ∈ finiteSubsetSums A ↔ ∃ s : Finset A, (∑ a ∈ s, (a : ℕ)) = n :=
  Iff.rfl

@[simp]
theorem isFiniteSubsetSum_iff {A : Set ℕ} {n : ℕ} :
    IsFiniteSubsetSum A n ↔ ∃ s : Finset A, (∑ a ∈ s, (a : ℕ)) = n :=
  Iff.rfl

@[simp]
theorem zero_mem_finiteSubsetSums (A : Set ℕ) : 0 ∈ finiteSubsetSums A := by
  exact ⟨∅, by simp⟩

theorem mem_finiteSubsetSums_of_mem {A : Set ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∈ finiteSubsetSums A := by
  refine ⟨{⟨a, ha⟩}, ?_⟩
  simp

theorem finiteSubsetSums_mono {A B : Set ℕ} (hAB : A ⊆ B) :
    finiteSubsetSums A ⊆ finiteSubsetSums B := by
  intro n hn
  rcases hn with ⟨s, rfl⟩
  let e : A ↪ B :=
    ⟨fun a ↦ ⟨a, hAB a.2⟩, by
      intro a b h
      apply Subtype.ext
      simpa using congrArg Subtype.val h⟩
  refine ⟨s.map e, ?_⟩
  rw [Finset.sum_map]
  rfl

theorem IsFiniteSubsetSum.mono {A B : Set ℕ} (hAB : A ⊆ B) {n : ℕ}
    (hn : IsFiniteSubsetSum A n) : IsFiniteSubsetSum B n :=
  finiteSubsetSums_mono hAB hn

theorem finite_finiteSubsetSums {A : Set ℕ} (hA : A.Finite) :
    (finiteSubsetSums A).Finite := by
  classical
  let := hA.fintype
  apply (Set.finite_range (fun s : Finset A ↦ ∑ a ∈ s, (a : ℕ))).subset
  rintro n ⟨s, rfl⟩
  exact ⟨s, rfl⟩

/-- The set of finite subset sums whose summands all have one color. -/
def monochromaticSums {r : ℕ} (A : Set ℕ) (color : A → Fin r) : Set ℕ :=
  {n | ∃ i : Fin r, ∃ s : Finset A,
    (∀ a ∈ s, color a = i) ∧ (∑ a ∈ s, (a : ℕ)) = n}

/-- Predicate form of membership in `monochromaticSums`. -/
def IsMonochromaticSum {r : ℕ} (A : Set ℕ) (color : A → Fin r) (n : ℕ) : Prop :=
  n ∈ monochromaticSums A color

@[simp]
theorem mem_monochromaticSums {r : ℕ} {A : Set ℕ} {color : A → Fin r} {n : ℕ} :
    n ∈ monochromaticSums A color ↔
      ∃ i : Fin r, ∃ s : Finset A,
        (∀ a ∈ s, color a = i) ∧ (∑ a ∈ s, (a : ℕ)) = n :=
  Iff.rfl

@[simp]
theorem isMonochromaticSum_iff {r : ℕ} {A : Set ℕ} {color : A → Fin r} {n : ℕ} :
    IsMonochromaticSum A color n ↔
      ∃ i : Fin r, ∃ s : Finset A,
        (∀ a ∈ s, color a = i) ∧ (∑ a ∈ s, (a : ℕ)) = n :=
  Iff.rfl

theorem monochromaticSums_subset_finiteSubsetSums {r : ℕ} (A : Set ℕ)
    (color : A → Fin r) : monochromaticSums A color ⊆ finiteSubsetSums A := by
  rintro n ⟨i, s, hs, rfl⟩
  exact ⟨s, rfl⟩

theorem IsMonochromaticSum.isFiniteSubsetSum {r : ℕ} {A : Set ℕ}
    {color : A → Fin r} {n : ℕ} (hn : IsMonochromaticSum A color n) :
    IsFiniteSubsetSum A n :=
  monochromaticSums_subset_finiteSubsetSums A color hn

theorem isMonochromaticSum_of_constant {r : ℕ} {A : Set ℕ} {color : A → Fin r}
    {i : Fin r} (hcolor : ∀ a, color a = i) {n : ℕ} (hn : IsFiniteSubsetSum A n) :
    IsMonochromaticSum A color n := by
  rcases hn with ⟨s, rfl⟩
  exact ⟨i, s, fun a _ ↦ hcolor a, rfl⟩

theorem IsMonochromaticSum.mono_set {r : ℕ} {A B : Set ℕ} (hAB : A ⊆ B)
    {colorB : B → Fin r} {n : ℕ}
    (hn : IsMonochromaticSum A (fun a ↦ colorB ⟨a, hAB a.2⟩) n) :
    IsMonochromaticSum B colorB n := by
  rcases hn with ⟨i, s, hs, hsum⟩
  let e : A ↪ B :=
    ⟨fun a ↦ ⟨a, hAB a.2⟩, by
      intro a b h
      apply Subtype.ext
      simpa using congrArg Subtype.val h⟩
  refine ⟨i, s.map e, ?_, ?_⟩
  · intro b hb
    rw [Finset.mem_map] at hb
    rcases hb with ⟨a, ha, rfl⟩
    exact hs a ha
  · rw [Finset.sum_map]
    exact hsum

/-- `A` is Ramsey `r`-complete if every `r`-coloring eventually represents
every integer as a finite distinct subset sum in a single color.

The witness color is intentionally inside the quantifier over represented
integers: different integers may use different colors. -/
def RamseyComplete (r : ℕ) (A : Set ℕ) : Prop :=
  ∀ color : A → Fin r, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    IsMonochromaticSum A color n

theorem ramseyComplete_iff {r : ℕ} {A : Set ℕ} :
    RamseyComplete r A ↔
      ∀ color : A → Fin r, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∃ i : Fin r, ∃ s : Finset A,
          (∀ a ∈ s, color a = i) ∧ (∑ a ∈ s, (a : ℕ)) = n :=
  Iff.rfl

theorem RamseyComplete.mono_set {r : ℕ} {A B : Set ℕ} (hA : RamseyComplete r A)
    (hAB : A ⊆ B) : RamseyComplete r B := by
  intro colorB
  rcases hA (fun a ↦ colorB ⟨a, hAB a.2⟩) with ⟨N₀, hN₀⟩
  exact ⟨N₀, fun n hn ↦ (hN₀ n hn).mono_set hAB⟩

theorem RamseyComplete.mono_colors {r s : ℕ} {A : Set ℕ} (hA : RamseyComplete r A)
    (hsr : s ≤ r) : RamseyComplete s A := by
  intro color
  let e : Fin s ↪ Fin r := Fin.castLEEmb hsr
  rcases hA (fun a ↦ e (color a)) with ⟨N₀, hN₀⟩
  refine ⟨N₀ + 1, fun n hn ↦ ?_⟩
  rcases hN₀ n (by omega) with ⟨i, t, ht, hsum⟩
  obtain ⟨a, ha⟩ := t.nonempty_of_ne_empty (by
    intro hempty
    subst t
    simp only [Finset.sum_empty] at hsum
    omega)
  refine ⟨color a, t, ?_, hsum⟩
  intro b hb
  apply e.injective
  exact (ht b hb).trans (ht a ha).symm

/-- The number of members of `A` in the positive interval `[1, N]`. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 N).filter (fun a ↦ a ∈ A)).card

@[simp]
theorem countUpTo_empty (N : ℕ) : countUpTo ∅ N = 0 := by
  simp [countUpTo]

@[simp]
theorem countUpTo_zero (A : Set ℕ) : countUpTo A 0 = 0 := by
  simp [countUpTo]

theorem countUpTo_mono_set {A B : Set ℕ} (hAB : A ⊆ B) (N : ℕ) :
    countUpTo A N ≤ countUpTo B N := by
  classical
  simp only [countUpTo]
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
  exact ⟨ha.1, hAB ha.2⟩

theorem countUpTo_mono_right (A : Set ℕ) : Monotone (countUpTo A) := by
  intro M N hMN
  classical
  simp only [countUpTo]
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
  exact ⟨⟨ha.1.1, ha.1.2.trans hMN⟩, ha.2⟩

theorem countUpTo_le (A : Set ℕ) (N : ℕ) : countUpTo A N ≤ N := by
  classical
  calc
    countUpTo A N ≤ (Finset.Icc 1 N).card := by
      simp only [countUpTo]
      exact Finset.card_filter_le _ _
    _ ≤ N := by simp

theorem countUpTo_eq_ncard_inter (A : Set ℕ) (N : ℕ) :
    countUpTo A N = (A ∩ Set.Icc 1 N).ncard := by
  classical
  rw [countUpTo, Set.ncard_eq_toFinset_card']
  congr
  ext a
  simp [and_comm]

/-- The exact proposition expressing the upper-bound half of the
Conlon--Fox--Pham theorem, with an absolute constant uniform in `r`. -/
def CFPUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
    ∃ A : PositiveNatSet, RamseyComplete r A ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (countUpTo A N : ℝ) ≤ C * (r : ℝ) * Real.log (N : ℝ) ^ 2

/-- The exact proposition expressing the lower-bound half of the
Conlon--Fox--Pham theorem, with an absolute constant uniform in `r`. -/
def CFPLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 2 ≤ r → ∀ A : PositiveNatSet,
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (countUpTo A N : ℝ) ≤ c * (r : ℝ) * Real.log (N : ℝ) ^ 2) →
    ¬ RamseyComplete r A

/-- The full sharp-order resolution of Erdős Problem 55. -/
def ConlonFoxPhamResolution : Prop :=
  CFPUpperBound ∧ CFPLowerBound

end Erdos55

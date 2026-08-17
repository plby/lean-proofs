/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the negative solution to Erdős Problem 8.
https://www.erdosproblems.com/8

The mathematical proof and its source audit are in `tex/8.tex`.
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import ErdosProblems.Erdos2

namespace Erdos8

attribute [local instance] Classical.propDecidable

/-- A finite family of congruence classes with distinct nontrivial moduli.

The moduli form a `Finset`, so distinctness is built into the representation.
The function `a` chooses the single residue attached to each modulus. -/
def IsDistinctCoveringSystem (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ d ∈ D, 2 ≤ d) ∧
    ∀ z : ℤ, ∃ d ∈ D, Int.ModEq d z (a d)

/-- All moduli of `D` receive one common colour. -/
def Monochromatic {κ : Type*} (colour : ℤ → κ) (D : Finset ℕ) : Prop :=
  ∃ k : κ, ∀ d ∈ D, colour (d : ℤ) = k

/-- The literal universal question in Problem 8, with a nonempty finite palette
represented by `Fin r`. -/
def EveryFiniteColoringHasMonochromaticCover : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ colour : ℤ → Fin r,
    ∃ D : Finset ℕ, ∃ a : ℕ → ℤ,
      IsDistinctCoveringSystem D a ∧ Monochromatic colour D

/-- `B` meets the minimum-modulus conclusion if every distinct covering
system contains a modulus at most `B`. -/
def IsMinimumModulusBound (B : ℕ) : Prop :=
  ∀ (D : Finset ℕ) (a : ℕ → ℤ), IsDistinctCoveringSystem D a →
    ∃ d ∈ D, d ≤ B

/-- The cutoff colouring: integers of absolute value at most `B` receive
their absolute value, and every other integer has colour zero.  In particular,
the positive moduli `d ≤ B` all receive distinct nonzero colours. -/
def cutoffColour (B : ℕ) (z : ℤ) : Fin (B + 1) :=
  if h : z.natAbs ≤ B then
    ⟨z.natAbs, by omega⟩
  else
    0

@[simp]
lemma cutoffColour_ofNat_of_le (B d : ℕ) (hd : d ≤ B) :
    cutoffColour B (d : ℤ) = ⟨d, by omega⟩ := by
  simp [cutoffColour, hd]

@[simp]
lemma cutoffColour_ofNat_of_lt (B d : ℕ) (hd : B < d) :
    cutoffColour B (d : ℤ) = 0 := by
  simp [cutoffColour, Nat.not_le.mpr hd]

/-- A small nontrivial modulus has a colour used by no other modulus. -/
lemma cutoffColour_eq_of_small
    {B d e : ℕ} (hd2 : 2 ≤ d) (hdB : d ≤ B)
    (hcolour : cutoffColour B (e : ℤ) = cutoffColour B (d : ℤ)) :
    e = d := by
  by_cases heB : e ≤ B
  · simpa [cutoffColour, hdB, heB] using congrArg Fin.val hcolour
  · have he : B < e := Nat.lt_of_not_ge heB
    have hzero : cutoffColour B (d : ℤ) = 0 := by
      rw [← hcolour, cutoffColour_ofNat_of_lt B e he]
    have := congrArg Fin.val hzero
    simp [cutoffColour, hdB] at this
    omega

/-- One congruence class with modulus greater than one cannot cover the
integers: it misses the successor of its residue. -/
lemma not_modEq_add_one (a : ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ¬ Int.ModEq d (a + 1) a := by
  intro h
  rw [Int.modEq_iff_dvd] at h
  have hd1 : (d : ℤ) ∣ 1 := by
    obtain ⟨k, hk⟩ := h
    refine ⟨-k, ?_⟩
    have hdiff : a - (a + 1) = -1 := by ring
    rw [hdiff] at hk
    calc
      (1 : ℤ) = -(-1) := by omega
      _ = -((d : ℤ) * k) := congrArg Neg.neg hk
      _ = (d : ℤ) * (-k) := by ring
  have : (d : ℤ) ≤ 1 := Int.le_of_dvd (by omega) hd1
  omega

/-- Hough's minimum-modulus conclusion implies the cutoff colouring is a
counterexample to Problem 8. -/
theorem cutoffColour_has_no_monochromatic_cover
    {B : ℕ} (hB : IsMinimumModulusBound B) :
    ∀ (D : Finset ℕ) (a : ℕ → ℤ),
      IsDistinctCoveringSystem D a → ¬ Monochromatic (cutoffColour B) D := by
  intro D a hcover hmono
  obtain ⟨d, hdD, hdB⟩ := hB D a hcover
  obtain ⟨k, hk⟩ := hmono
  have hd2 : 2 ≤ d := hcover.1 d hdD
  have hD : D = {d} := by
    ext e
    constructor
    · intro heD
      have hsame : cutoffColour B (e : ℤ) = cutoffColour B (d : ℤ) :=
        (hk e heD).trans (hk d hdD).symm
      exact Finset.mem_singleton.mpr (cutoffColour_eq_of_small hd2 hdB hsame)
    · intro hed
      have : e = d := by simpa only [Finset.mem_singleton] using hed
      subst e
      exact hdD
  obtain ⟨e, heD, hemod⟩ := hcover.2 (a d + 1)
  rw [hD] at heD
  have hed : e = d := by simpa using heD
  subst e
  exact not_modEq_add_one (a d) hd2 hemod

/-- The elementary reduction from the minimum-modulus theorem to the
negative answer to Erdős Problem 8. -/
theorem negative_answer_of_minimum_modulus_bound
    (hmin : ∃ B : ℕ, IsMinimumModulusBound B) :
    ¬ EveryFiniteColoringHasMonochromaticCover := by
  rintro hall
  obtain ⟨B, hB⟩ := hmin
  obtain ⟨D, a, hcover, hmono⟩ := hall (B + 1) (by omega) (cutoffColour B)
  exact cutoffColour_has_no_monochromatic_cover hB D a hcover hmono

/-- The minimum-modulus input, supplied by the fully proved formalization of
Erdős Problem 2. -/
theorem hough_minimum_modulus_bound :
    ∃ B : ℕ, IsMinimumModulusBound B := by
  obtain ⟨M, hM⟩ := Erdos2.uniformMinimumBound
  refine ⟨M, ?_⟩
  intro D a hcover
  have hcover' : Erdos2.IsDistinctCoveringSystem D a := by
    simpa [IsDistinctCoveringSystem, Erdos2.IsDistinctCoveringSystem] using hcover
  obtain ⟨d, hdD, hdM⟩ := hM D a hcover'
  exact ⟨d, hdD, hdM.le⟩

/-- **Erdős Problem 8.** The answer is no: there is a finite colouring of
the integers for which no distinct covering system has monochromatic
moduli. -/
theorem erdos_8 : ¬ EveryFiniteColoringHasMonochromaticCover :=
  negative_answer_of_minimum_modulus_bound hough_minimum_modulus_bound

#print axioms erdos_8

end Erdos8

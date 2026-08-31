/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1187.
https://www.erdosproblems.com/forum/thread/1187

Informal authors:
- Ben Green
- Terence Tao

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1187.md
-/
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.ZMod.Basic
import Wikipedia.GreenTao

/-!
# Erdős Problem 1187

For every finite coloring of the integers and every `k ≥ 3`, there is a
monochromatic `k`-term arithmetic progression consisting of primes.  In
contrast, the four-coloring by residue modulo four has no monochromatic
arithmetic progression whose positive common difference is prime.

The first half combines the repository's proof of the Green--Tao theorem
with Hales--Jewett (in its finite van der Waerden role).  The second half is
the elementary residue-class counterexample.

References:

* B. Green and T. Tao, *The primes contain arbitrarily long arithmetic
  progressions*, Annals of Mathematics 167 (2008), 481--547.
* https://www.erdosproblems.com/1187
-/

open scoped BigOperators Finset

namespace Erdos1187

/-- A positive-step arithmetic progression of natural primes, regarded as
integers by the coloring, is monochromatic. -/
def HasMonochromaticPrimeAP {κ : Type*} (color : ℤ → κ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧
    (∀ j : ℕ, j < k → Nat.Prime (a + d * j)) ∧
    ∃ gamma : κ, ∀ j : ℕ, j < k → color ((a + d * j : ℕ) : ℤ) = gamma

/-- An integer arithmetic progression with positive prime common difference
is monochromatic. -/
def HasMonochromaticAPWithPrimeStep {κ : Type*}
    (color : ℤ → κ) (k : ℕ) : Prop :=
  ∃ a : ℤ, ∃ p : ℕ, Nat.Prime p ∧
    ∃ gamma : κ, ∀ j : ℕ, j < k →
      color (a + ((p * j : ℕ) : ℤ)) = gamma

/-- The first question at one fixed requested length, literally quantified
over all finite color types and all colorings of the integers. -/
def FirstQuestionAt (k : ℕ) : Prop :=
  ∀ (κ : Type) [Finite κ], ∀ color : ℤ → κ,
    HasMonochromaticPrimeAP color k

/-- The second question at one fixed requested length. -/
def SecondQuestionAt (k : ℕ) : Prop :=
  ∀ (κ : Type) [Finite κ], ∀ color : ℤ → κ,
    HasMonochromaticAPWithPrimeStep color k

/-- The first question for every length in the range asked by Erdős. -/
def FirstQuestion : Prop :=
  ∀ k : ℕ, 3 ≤ k → FirstQuestionAt k

/-- The universal affirmative assertion for the second question.  We prove
both its negation and, more precisely, failure at every `k ≥ 3`. -/
def SecondQuestion : Prop :=
  ∀ k : ℕ, 3 ≤ k → SecondQuestionAt k

noncomputable section

open Combinatorics

attribute [local instance] Classical.decEq

/-- Encode a finite word by the sum of its natural-valued letters. -/
private def wordIndex {ι : Type*} [Fintype ι] {k : ℕ}
    (v : ι → Fin k) : ℕ :=
  ∑ i, (v i : ℕ)

/-- Every word index is below one plus `card ι * k`. -/
private theorem wordIndex_lt {ι : Type*} [Fintype ι] {k : ℕ}
    (v : ι → Fin k) :
    wordIndex v < Fintype.card ι * k + 1 := by
  calc
    wordIndex v ≤ ∑ _i : ι, k := by
      apply Finset.sum_le_sum
      intro i _hi
      exact Nat.le_of_lt (v i).isLt
    _ = Fintype.card ι * k := by simp
    _ < Fintype.card ι * k + 1 := Nat.lt_succ_self _

/-- Coordinates on which a combinatorial line actually varies. -/
private def varyingCoords {ι : Type*} [Fintype ι] {k : ℕ}
    (l : Line (Fin k) ι) : Finset ι :=
  {i | l.idxFun i = none}

/-- The set of varying coordinates of a combinatorial line is nonempty. -/
private theorem varyingCoords_nonempty {ι : Type*} [Fintype ι] {k : ℕ}
    (l : Line (Fin k) ι) :
    (varyingCoords l).Nonempty := by
  obtain ⟨i, hi⟩ := l.proper
  exact ⟨i, by simp [varyingCoords, hi]⟩

/-- Summing the letters along a combinatorial line gives an affine function
whose positive slope is the number of varying coordinates. -/
private theorem wordIndex_line {ι : Type*} [Fintype ι] {k : ℕ}
    (l : Line (Fin k) ι) (r : Fin k) :
    wordIndex (l r) =
      (varyingCoords l).card * (r : ℕ) +
        ∑ i ∈ (varyingCoords l)ᶜ,
          ((l.idxFun i).map Fin.val).getD 0 := by
  classical
  let s : Finset ι := varyingCoords l
  change (∑ i, ((l r i : Fin k) : ℕ)) =
    s.card * (r : ℕ) +
      ∑ i ∈ sᶜ, ((l.idxFun i).map Fin.val).getD 0
  rw [← Finset.sum_add_sum_compl s]
  congr 1
  · calc
      ∑ i ∈ s, ((l r i : Fin k) : ℕ) = ∑ _i ∈ s, (r : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hivar : l.idxFun i = none := by
          simpa [s, varyingCoords] using hi
        rw [l.apply_none r i hivar]
      _ = s.card * (r : ℕ) := by simp
  · apply Finset.sum_congr rfl
    intro i hi
    have hifixed : l.idxFun i ≠ none := by
      simpa [s, varyingCoords] using hi
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp hifixed
    simp [Line.coe_apply, ← hx]

/-- Green--Tao plus the finite Hales--Jewett theorem gives a monochromatic
prime progression for every finite coloring. -/
theorem monochromatic_prime_ap
    {κ : Type*} [Finite κ] (color : ℤ → κ) (k : ℕ) (_hk : 1 < k) :
    HasMonochromaticPrimeAP color k := by
  classical
  obtain ⟨ι, instι, hmono⟩ :=
    Line.exists_mono_in_high_dimension (Fin k) κ
  let _ : Fintype ι := instι
  let N : ℕ := Fintype.card ι * k + 1
  obtain ⟨A, D, hD, hprime⟩ := GreenTao.green_tao N
  let cubeColor : (ι → Fin k) → κ := fun v =>
    color ((A + D * wordIndex v : ℕ) : ℤ)
  obtain ⟨l, gamma, hline⟩ := hmono cubeColor
  let e : ℕ := (varyingCoords l).card
  let b : ℕ :=
    ∑ i ∈ (varyingCoords l)ᶜ,
      ((l.idxFun i).map Fin.val).getD 0
  have he : 0 < e := by
    exact Finset.card_pos.mpr (varyingCoords_nonempty l)
  have hDpos : 0 < D := by omega
  refine ⟨A + D * b, D * e, Nat.mul_pos hDpos he, ?_, ⟨gamma, ?_⟩⟩
  · intro j hj
    let r : Fin k := ⟨j, hj⟩
    have hidx : wordIndex (l r) = e * j + b := by
      simpa [e, b, r] using wordIndex_line l r
    have hterm :
        (A + D * b) + (D * e) * j = A + D * wordIndex (l r) := by
      rw [hidx]
      ring
    rw [hterm]
    exact hprime (wordIndex (l r)) (wordIndex_lt (l r))
  · intro j hj
    let r : Fin k := ⟨j, hj⟩
    have hidx : wordIndex (l r) = e * j + b := by
      simpa [e, b, r] using wordIndex_line l r
    have hterm :
        (A + D * b) + (D * e) * j = A + D * wordIndex (l r) := by
      rw [hidx]
      ring
    change color (((A + D * b) + (D * e) * j : ℕ) : ℤ) = gamma
    rw [hterm]
    exact hline r

/-- The answer to the first question is yes. -/
theorem first_question_yes : FirstQuestion := by
  intro k hk κ instκ color
  exact monochromatic_prime_ap color k (by omega)

/-- Coloring an integer by its residue class modulo four. -/
def residueColor4 (a : ℤ) : ZMod 4 :=
  (a : ZMod 4)

/-- A natural prime is not divisible by four. -/
private theorem prime_not_four_dvd {p : ℕ} (hp : Nat.Prime p) : ¬4 ∣ p := by
  intro hfour
  rcases (Nat.dvd_prime hp).mp hfour with h | h
  · norm_num at h
  · subst p
    exact (by decide : ¬ Nat.Prime 4) hp

/-- Adding a positive prime always changes the residue modulo four. -/
theorem residueColor4_add_prime_ne (a : ℤ) {p : ℕ} (hp : Nat.Prime p) :
    residueColor4 (a + (p : ℤ)) ≠ residueColor4 a := by
  intro hsame
  have hzero : (((p : ℕ) : ℤ) : ZMod 4) = 0 := by
    have hadd :
        (a : ZMod 4) + (((p : ℕ) : ℤ) : ZMod 4) =
          (a : ZMod 4) + 0 := by
      simpa [residueColor4] using hsame
    exact add_left_cancel hadd
  have hfourInt : (4 : ℤ) ∣ (p : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (p : ℤ) 4).mp hzero
  have hfourNat : 4 ∣ p :=
    Int.natCast_dvd_natCast.mp hfourInt
  exact prime_not_four_dvd hp hfourNat

/-- The four-residue coloring admits no monochromatic progression of length
at least two whose common difference is prime. -/
theorem residueColor4_no_prime_step
    (k : ℕ) (hk : 2 ≤ k) :
    ¬ HasMonochromaticAPWithPrimeStep residueColor4 k := by
  rintro ⟨a, p, hp, gamma, hmono⟩
  have hzero := hmono 0 (by omega)
  have hone := hmono 1 (by omega)
  have hsame : residueColor4 (a + (p : ℤ)) = residueColor4 a := by
    simpa using hone.trans hzero.symm
  exact residueColor4_add_prime_ne a hp hsame

/-- At every requested length, the answer to the second question is no. -/
theorem second_question_no (k : ℕ) (hk : 3 ≤ k) :
    ¬ SecondQuestionAt k := by
  intro h
  have hbad := h (ZMod 4) residueColor4
  exact residueColor4_no_prime_step k (by omega) hbad

/-- In particular, the single universal affirmative assertion is false. -/
theorem second_question_universal_no : ¬ SecondQuestion := by
  intro h
  exact second_question_no 3 (by omega) (h 3 (by omega))

/-- Complete resolution of Erdős Problem 1187. -/
theorem erdos_1187 :
    (∀ k : ℕ, 3 ≤ k → Erdos1187.FirstQuestionAt k) ∧ ∀ k : ℕ, 3 ≤ k → ¬ SecondQuestionAt k :=
  ⟨first_question_yes, second_question_no⟩

#print axioms erdos_1187

end

end Erdos1187

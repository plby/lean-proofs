/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterCharacterMinors

/-!
# A finite exceptional-set bound for Diophantine rotations

The rotations excluded in Hunter's argument are indexed by a positive
multiple, a finite tuple of bounded integer frequencies, and a square
minor.  This file proves the union bound abstractly for any finite frequency
alphabet.  Numerical parameter estimates are kept separate.
-/

open Set Function MeasureTheory Metric
open scoped ENNReal BigOperators

namespace Erdos984

noncomputable section

/-- Decode a tuple over a finite alphabet into integer frequencies. -/
def decodedFrequency {D R Q : Type*} (decode : Q → ℤ)
    (q : R → D → Q) : R → D → ℤ :=
  fun r j ↦ decode (q r j)

/-- One cell in the exceptional set.  Singular minors contribute the empty
set, while nonsingular minors contribute the simultaneous small-phase
event. -/
def characterMinorBadCell {D R Q : Type*} [Fintype D] [Fintype R]
    [DecidableEq R]
    (decode : Q → ℤ) (δ : ℝ)
    (p : Fin N × (R → D → Q) × (R → D)) : Set (UnitAddTorus D) :=
  let ξ := decodedFrequency decode p.2.1
  if (integerCharacterMinorRealMatrix ξ p.2.2).det = 0 then ∅
  else nsmulIntegerCharacterTuple (p.1 + 1) ξ ⁻¹'
    closedBall (0 : UnitAddTorus R) δ

/-- The union of every exceptional character-minor cell. -/
def characterMinorBadSet {D R Q : Type*} [Fintype D]
    [Fintype R] [DecidableEq R] [Fintype Q]
    [DecidableEq D] [DecidableEq Q]
    (N : ℕ) (decode : Q → ℤ) (δ : ℝ) :
    Set (UnitAddTorus D) :=
  ⋃ p : Fin N × (R → D → Q) × (R → D),
    characterMinorBadCell decode δ p

/-- Exact volume of a nonsingular exceptional cell. -/
lemma volume_characterMinorBadCell
    {D R Q : Type*} [Fintype D] [Fintype R]
    [DecidableEq R]
    (decode : Q → ℤ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδhalf : δ ≤ (1 : ℝ) / 2)
    (p : Fin N × (R → D → Q) × (R → D)) :
    volume (characterMinorBadCell decode δ p) ≤
      (ENNReal.ofReal (2 * δ)) ^ Fintype.card R := by
  let ξ := decodedFrequency decode p.2.1
  by_cases hdet : (integerCharacterMinorRealMatrix ξ p.2.2).det = 0
  · simp [characterMinorBadCell, ξ, hdet]
  · rw [show characterMinorBadCell decode δ p =
        nsmulIntegerCharacterTuple (p.1 + 1) ξ ⁻¹'
          closedBall (0 : UnitAddTorus R) δ by
      simp [characterMinorBadCell, ξ, hdet]]
    exact le_of_eq (volume_small_nsmul_character_event_of_minor
      (p.1 + 1) (by omega) ξ p.2.2 hdet hδ0 hδhalf)

/-- Abstract exceptional-volume estimate. -/
lemma volume_characterMinorBadSet_le
    {D R Q : Type*} [Fintype D] [Fintype R] [Fintype Q]
    [DecidableEq D] [DecidableEq R] [DecidableEq Q]
    (N : ℕ) (decode : Q → ℤ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδhalf : δ ≤ (1 : ℝ) / 2) :
    volume (characterMinorBadSet (D := D) (R := R) N decode δ) ≤
      (Fintype.card (Fin N × (R → D → Q) × (R → D)) : ENNReal) *
        (ENNReal.ofReal (2 * δ)) ^ Fintype.card R := by
  classical
  let I := Fin N × (R → D → Q) × (R → D)
  let q : ENNReal := (ENNReal.ofReal (2 * δ)) ^ Fintype.card R
  calc
    volume (characterMinorBadSet (D := D) (R := R) N decode δ) ≤
        ∑ p : I, volume (characterMinorBadCell decode δ p) := by
      exact MeasureTheory.measure_iUnion_fintype_le volume
        (fun p : I ↦ characterMinorBadCell decode δ p)
    _ ≤ ∑ _p : I, q := by
      gcongr with p
      exact volume_characterMinorBadCell decode hδ0 hδhalf p
    _ = (Fintype.card I : ℕ) • q := by simp
    _ = (Fintype.card I : ENNReal) * q := by rw [nsmul_eq_mul]

/-- If the finite union cost is below one, there is a rotation for which no
nonsingular frequency tuple has all phases small at any of the prescribed
positive multiples. -/
lemma exists_avoiding_character_minors
    {D R Q : Type*} [Fintype D] [Fintype R] [Fintype Q]
    [DecidableEq D] [DecidableEq R]
    (N : ℕ) (decode : Q → ℤ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδhalf : δ ≤ (1 : ℝ) / 2)
    (hsmall :
      (Fintype.card (Fin N × (R → D → Q) × (R → D)) : ENNReal) *
        (ENNReal.ofReal (2 * δ)) ^ Fintype.card R < 1) :
    ∃ θ : UnitAddTorus D,
      ∀ (n : Fin N) (q : R → D → Q) (σ : R → D),
        (integerCharacterMinorRealMatrix (decodedFrequency decode q) σ).det ≠ 0 →
        nsmulIntegerCharacterTuple (n + 1) (decodedFrequency decode q) θ ∉
          closedBall (0 : UnitAddTorus R) δ := by
  classical
  have hvol := volume_characterMinorBadSet_le
    (D := D) (R := R) N decode hδ0 hδhalf
  have hlt : volume (characterMinorBadSet (D := D) (R := R) N decode δ) < 1 :=
    hvol.trans_lt hsmall
  have hne : characterMinorBadSet (D := D) (R := R) N decode δ ≠ Set.univ := by
    intro hEq
    rw [hEq, volume_unitAddTorus_univ] at hlt
    exact (lt_self_iff_false 1).mp hlt
  obtain ⟨θ, hθ⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨θ, ?_⟩
  intro n q σ hdet hmem
  apply hθ
  apply Set.mem_iUnion_of_mem (n, q, σ)
  simp [characterMinorBadCell, hdet, hmem]

end

end Erdos984

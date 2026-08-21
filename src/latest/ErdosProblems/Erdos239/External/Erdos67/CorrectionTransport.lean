import ErdosProblems.Erdos239.External.Erdos67.CharacterTransport
import ErdosProblems.Erdos239.External.Erdos67.WeightedTransfer

/-!
# Weighted-transfer bridges for transported character laws

This file connects the canonical character/prime-coordinate transport to the
local increments and the correction assignment used by the weighted
Borwein--Choi--Coons argument.
-/

open MeasureTheory

namespace Erdos67

noncomputable section

/-- A local increment written directly on the compact character space. -/
def compactCharacterLocalIncrement
    (g : CompactCircleCharacter) (n H : ℕ) : ℂ :=
  compactCharacterBasePartialSum (n + H) g - compactCharacterBasePartialSum n g

/-- Squared norm of a local increment on the compact character space. -/
def compactCharacterLocalIncrementEnergy
    (n H : ℕ) (g : CompactCircleCharacter) : ℝ :=
  ‖compactCharacterLocalIncrement g n H‖ ^ 2

theorem continuous_compactCharacterLocalIncrementEnergy (n H : ℕ) :
    Continuous (compactCharacterLocalIncrementEnergy n H) := by
  unfold compactCharacterLocalIncrementEnergy compactCharacterLocalIncrement
  have hbase (m : ℕ) :
      Continuous fun g : CompactCircleCharacter ↦ compactCharacterBasePartialSum m g := by
    unfold compactCharacterBasePartialSum
    exact continuous_finsetSum (Finset.range m) fun k _ ↦
      continuous_compactCircleCharacter_eval_complex ⟨k + 1, by omega⟩
  exact ((hbase (n + H)).sub (hbase n)).norm.pow 2

theorem circleLocalIncrement_primeAssignmentOfCompactCircleCharacter
    (g : CompactCircleCharacter) (n H : ℕ) :
    circleLocalIncrement (primeAssignmentOfCompactCircleCharacter g) n H =
      compactCharacterLocalIncrement g n H := by
  simp only [circleLocalIncrement, compactCharacterLocalIncrement,
    circlePartialSum_primeAssignmentOfCompactCircleCharacter]

theorem circleLocalIncrementEnergy_primeAssignmentOfCompactCircleCharacter
    (g : CompactCircleCharacter) (n H : ℕ) :
    circleLocalIncrementEnergy n H
        (primeAssignmentOfCompactCircleCharacter g) =
      compactCharacterLocalIncrementEnergy n H g := by
  unfold circleLocalIncrementEnergy compactCharacterLocalIncrementEnergy
  rw [circleLocalIncrement_primeAssignmentOfCompactCircleCharacter]

/-- Mean-square local increment before transport to prime coordinates. -/
def compactMeanSquareLocalIncrement
    (mu : ProbabilityMeasure CompactCircleCharacter) (n H : ℕ) : ℝ :=
  ∫ g, compactCharacterLocalIncrementEnergy n H g
    ∂(mu : Measure CompactCircleCharacter)

/-- Transport preserves local-increment mean squares exactly. -/
theorem meanSquareLocalIncrement_primeAssignmentLaw
    (mu : ProbabilityMeasure CompactCircleCharacter) (n H : ℕ) :
    meanSquareLocalIncrement (primeAssignmentLaw mu) n H =
      compactMeanSquareLocalIncrement mu n H := by
  unfold meanSquareLocalIncrement primeAssignmentLaw compactMeanSquareLocalIncrement
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map continuous_primeAssignmentOfCompactCircleCharacter.measurable.aemeasurable
    (continuous_circleLocalIncrementEnergy n H).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with g
  exact circleLocalIncrementEnergy_primeAssignmentOfCompactCircleCharacter g n H

/-- A uniform compact-space stochastic bound becomes the exact prime-space
bound consumed by `weightedLocalMeanSquare_le`. -/
theorem primeAssignmentLaw_uniform_meanSquare_bound
    (mu : ProbabilityMeasure CompactCircleCharacter) (C : ℝ)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum mu m ≤ C) :
    ∀ m : ℕ, meanSquarePartialSum (primeAssignmentLaw mu) m ≤ C := by
  intro m
  rw [meanSquarePartialSum_primeAssignmentLaw]
  exact hbound m

/-- One-call form of the law transport followed by the weighted local
mean-square estimate.  This is the compact-space interface used by the
Section 4 assembly. -/
theorem weightedLocalMeanSquare_primeAssignmentLaw_le
    (mu : ProbabilityMeasure CompactCircleCharacter)
    (centers : Finset ℕ) (weight : ℕ → ℝ) (H : ℕ) (C : ℝ)
    (hweight : ∀ n ∈ centers, 0 ≤ weight n)
    (hbound : ∀ m : ℕ, compactMeanSquarePartialSum mu m ≤ C) :
    weightedLocalMeanSquare (primeAssignmentLaw mu) centers weight H ≤
      4 * C * ∑ n ∈ centers, weight n := by
  exact weightedLocalMeanSquare_le (primeAssignmentLaw mu) centers weight H C hweight
    (primeAssignmentLaw_uniform_meanSquare_bound mu C hbound)

/-! ## The correction assignment as an Euler-product coefficient -/

theorem primeAssignmentMonoidWithZeroHom_hasUnitNorm (z : PrimeAssignment) :
    EulerResidue.HasUnitNorm (primeAssignmentMonoidWithZeroHom z) := by
  intro n hn
  exact norm_primeAssignmentMonoidWithZeroHom_apply_of_ne_zero z hn

/-- The correction factor from the weighted transfer, now in the
zero-preserving format used by `EulerResidue`. -/
def correctionMonoidWithZeroHom
    (base model arch : PrimeAssignment) (exceptional : Finset PrimeNat) :
    ℕ →*₀ ℂ :=
  primeAssignmentMonoidWithZeroHom
    (correctionAssignment base model arch exceptional)

theorem correctionMonoidWithZeroHom_hasUnitNorm
    (base model arch : PrimeAssignment) (exceptional : Finset PrimeNat) :
    EulerResidue.HasUnitNorm
      (correctionMonoidWithZeroHom base model arch exceptional) :=
  primeAssignmentMonoidWithZeroHom_hasUnitNorm _

@[simp] theorem correctionMonoidWithZeroHom_apply_prime
    (base model arch : PrimeAssignment) (exceptional : Finset PrimeNat)
    (p : PrimeNat) :
    correctionMonoidWithZeroHom base model arch exceptional p =
      (correctionAssignment base model arch exceptional p : ℂ) := by
  exact primeAssignmentMonoidWithZeroHom_apply_prime _ p

theorem correctionMonoidWithZeroHom_apply_of_ne_zero
    (base model arch : PrimeAssignment) (exceptional : Finset PrimeNat)
    {n : ℕ} (hn : n ≠ 0) :
    correctionMonoidWithZeroHom base model arch exceptional n =
      (primeExtension (correctionAssignment base model arch exceptional) n : ℂ) := by
  exact primeAssignmentMonoidWithZeroHom_apply_of_ne_zero _ hn

@[simp] theorem correctionMonoidWithZeroHom_apply_exceptionalPrime
    (base model arch : PrimeAssignment) (exceptional : Finset PrimeNat)
    {p : PrimeNat} (hp : p ∈ exceptional) :
    correctionMonoidWithZeroHom base model arch exceptional p = 1 := by
  rw [correctionMonoidWithZeroHom_apply_prime,
    correctionAssignment_of_mem base model arch exceptional hp]
  rfl

end

end Erdos67

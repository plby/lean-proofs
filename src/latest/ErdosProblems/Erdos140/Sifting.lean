import APAP.Physics.DRC
import Mathlib

/-!
# Dependent random choice / sifting for Erdős Problem 140

This file proves the finite averaging argument used in the Kelley--Meka
sifting step.  All averages are written with their denominators visible.  In
particular, `rawPairAverage` divides by `|G|^2`, while
`pairProbability` divides by `|A₁||A₂|`.  The exact identity below therefore
contains the normalization factor `|G|^2 / (|B₁||B₂|)`.
-/

open scoped BigOperators
open Finset

namespace Erdos140
namespace Sifting

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

noncomputable section

/-- The elements of `B` lying in every translate `A + sᵢ`. -/
def siftedSet (A B : Finset G) {p : ℕ} (s : Fin p → G) : Finset G :=
  B.filter fun b ↦ ∀ i, b - s i ∈ A

theorem siftedSet_subset (A B : Finset G) {p : ℕ} (s : Fin p → G) :
    siftedSet A B s ⊆ B := by
  intro b hb
  exact (mem_filter.mp hb).1

@[simp] theorem mem_siftedSet {A B : Finset G} {p : ℕ} {s : Fin p → G} {b : G} :
    b ∈ siftedSet A B s ↔ b ∈ B ∧ ∀ i, b - s i ∈ A := by
  simp [siftedSet]

/-- The unnormalised weighted count of ordered differences from two sets. -/
def pairSum (A₁ A₂ : Finset G) (F : G → ℝ) : ℝ :=
  ∑ a₁ ∈ A₁, ∑ a₂ ∈ A₂, F (a₁ - a₂)

theorem pairSum_const_mul (A₁ A₂ : Finset G) (c : ℝ) (F : G → ℝ) :
    pairSum A₁ A₂ (fun x ↦ c * F x) = c * pairSum A₁ A₂ F := by
  unfold pairSum
  symm
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro a₁ ha₁
  rw [Finset.mul_sum]

/-- The pair count divided by `|G|^2`.  This is
`⟨¹_A₁ ∘ ¹_A₂, F⟩` with normalized ambient averages. -/
def rawPairAverage (A₁ A₂ : Finset G) (F : G → ℝ) : ℝ :=
  pairSum A₁ A₂ F / (Fintype.card G : ℝ) ^ 2

/-- The uniform probability average over ordered pairs from two nonempty sets.
It is defined as zero when a denominator vanishes. -/
def pairProbability (A₁ A₂ : Finset G) (F : G → ℝ) : ℝ :=
  pairSum A₁ A₂ F / ((A₁.card : ℝ) * A₂.card)

/-- The set of differences which can occur between `A₁` and `A₂`. -/
def differenceSet (A₁ A₂ : Finset G) : Finset G :=
  A₁.biUnion fun a₁ ↦ A₂.image fun a₂ ↦ a₁ - a₂

@[simp] theorem mem_differenceSet {A₁ A₂ : Finset G} {x : G} :
    x ∈ differenceSet A₁ A₂ ↔ ∃ a₁ ∈ A₁, ∃ a₂ ∈ A₂, a₁ - a₂ = x := by
  simp [differenceSet]

/-- Restricting a test function to the actual difference support does not
change its pair average. -/
theorem pairSum_support_restrict (A₁ A₂ : Finset G) (F : G → ℝ) :
    pairSum A₁ A₂ (fun x ↦ if x ∈ differenceSet A₁ A₂ then F x else 0) =
      pairSum A₁ A₂ F := by
  unfold pairSum
  apply sum_congr rfl
  intro a₁ ha₁
  apply sum_congr rfl
  intro a₂ ha₂
  simp [mem_differenceSet.mpr ⟨a₁, ha₁, a₂, ha₂, rfl⟩]

theorem pairProbability_support_restrict (A₁ A₂ : Finset G) (F : G → ℝ) :
    pairProbability A₁ A₂
        (fun x ↦ if x ∈ differenceSet A₁ A₂ then F x else 0) =
      pairProbability A₁ A₂ F := by
  rw [pairProbability, pairProbability, pairSum_support_restrict]

/-- The number of shifts putting both endpoints of a difference in `A`. -/
def commonShiftCount (A : Finset G) (x : G) : ℕ :=
  #(Finset.univ.filter fun t : G ↦ x - t ∈ A ∧ -t ∈ A)

/-- The normalized self-difference correlation, written as an explicit count. -/
def selfCorrelation (A : Finset G) (x : G) : ℝ :=
  (Fintype.card G : ℝ) / (A.card : ℝ) ^ 2 * commonShiftCount A x

/-- The density `|A| / |G|`. -/
def ambientDensity (A : Finset G) : ℝ :=
  (A.card : ℝ) / Fintype.card G

/-- The weighted `p`-moment of the self-correlation, where the weight is the
uniform difference distribution from `B₁ × B₂`. -/
def weightedCorrelationIntegral (A B₁ B₂ : Finset G) (p : ℕ) (F : G → ℝ) : ℝ :=
  pairProbability B₁ B₂ (fun x ↦ selfCorrelation A x ^ p * F x)

/-- The average of a real function over the finite shift space `G^p`. -/
def shiftAverage (p : ℕ) (H : (Fin p → G) → ℝ) : ℝ :=
  (∑ s, H s) / (Fintype.card G : ℝ) ^ p

private theorem sum_pair_shift_indicator (A : Finset G) (b₁ b₂ : G) :
    (∑ s : G, if b₁ - s ∈ A ∧ b₂ - s ∈ A then (1 : ℝ) else 0) =
      commonShiftCount A (b₁ - b₂) := by
  rw [commonShiftCount]
  let e : G ≃ G := Equiv.subRight b₂
  rw [show ((#(Finset.univ.filter fun t : G ↦ b₁ - b₂ - t ∈ A ∧ -t ∈ A) : ℕ) : ℝ) =
      ∑ t : G, if b₁ - b₂ - t ∈ A ∧ -t ∈ A then (1 : ℝ) else 0 by
    simpa using (Finset.sum_boole
      (fun t : G ↦ b₁ - b₂ - t ∈ A ∧ -t ∈ A) (Finset.univ : Finset G) :
        (∑ t ∈ (Finset.univ : Finset G),
          if b₁ - b₂ - t ∈ A ∧ -t ∈ A then (1 : ℝ) else 0) = _)]
  refine Fintype.sum_equiv e
    (fun s : G ↦ if b₁ - s ∈ A ∧ b₂ - s ∈ A then (1 : ℝ) else 0)
    (fun t : G ↦ if b₁ - b₂ - t ∈ A ∧ -t ∈ A then (1 : ℝ) else 0)
    (fun t ↦ ?_)
  change (if b₁ - t ∈ A ∧ b₂ - t ∈ A then (1 : ℝ) else 0) =
    if b₁ - b₂ - (t - b₂) ∈ A ∧ -(t - b₂) ∈ A then 1 else 0
  have h₁ : b₁ - b₂ - (t - b₂) = b₁ - t := by abel
  have h₂ : -(t - b₂) = b₂ - t := by abel
  rw [h₁, h₂]

private theorem sum_all_coordinate_indicators (A : Finset G) (b₁ b₂ : G) (p : ℕ) :
    (∑ s : Fin p → G,
        if ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A then (1 : ℝ) else 0) =
      (commonShiftCount A (b₁ - b₂) : ℝ) ^ p := by
  let D : Finset G := Finset.univ.filter fun t : G ↦ b₁ - t ∈ A ∧ b₂ - t ∈ A
  have hsets :
      Finset.univ.filter
          (fun s : Fin p → G ↦ ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A) =
        Fintype.piFinset (fun _ : Fin p ↦ D) := by
    ext s
    simp [D, Fintype.mem_piFinset]
  calc
    (∑ s : Fin p → G,
        if ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A then (1 : ℝ) else 0) =
        ((Finset.univ.filter
          (fun s : Fin p → G ↦ ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A)).card : ℝ) := by
      simpa using (Finset.sum_boole
        (fun s : Fin p → G ↦ ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A)
        (Finset.univ : Finset (Fin p → G)) :
          (∑ s ∈ (Finset.univ : Finset (Fin p → G)),
            if ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A then (1 : ℝ) else 0) = _)
    _ = ((Fintype.piFinset fun _ : Fin p ↦ D).card : ℝ) := by rw [hsets]
    _ = (D.card : ℝ) ^ p := by simp [Fintype.card_piFinset]
    _ = (commonShiftCount A (b₁ - b₂) : ℝ) ^ p := by
      congr 1
      have hsum := sum_pair_shift_indicator A b₁ b₂
      simpa [D] using hsum

/-- The raw dependent-random-choice expansion before dividing by any
probability normalizations. -/
theorem sum_pairSum_sifted (A B₁ B₂ : Finset G) (p : ℕ) (F : G → ℝ) :
    (∑ s : Fin p → G, pairSum (siftedSet A B₁ s) (siftedSet A B₂ s) F) =
      ∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂,
        (commonShiftCount A (b₁ - b₂) : ℝ) ^ p * F (b₁ - b₂) := by
  classical
  simp only [pairSum, siftedSet, sum_filter]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro b₁ hb₁
  have hpush : ∀ s : Fin p → G,
      (if ∀ i, b₁ - s i ∈ A then
          ∑ a ∈ B₂, if ∀ i, a - s i ∈ A then F (b₁ - a) else 0
        else 0) =
        ∑ a ∈ B₂, if ∀ i, b₁ - s i ∈ A then
          if ∀ i, a - s i ∈ A then F (b₁ - a) else 0 else 0 := by
    intro s
    by_cases h : ∀ i, b₁ - s i ∈ A <;> simp [h]
  simp_rw [hpush]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro b₂ hb₂
  calc
    (∑ s : Fin p → G,
      if ∀ i, b₁ - s i ∈ A then
        if ∀ i, b₂ - s i ∈ A then F (b₁ - b₂) else 0
      else 0) =
        (∑ s : Fin p → G,
          (if ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A then (1 : ℝ) else 0)) *
            F (b₁ - b₂) := by
              rw [Finset.sum_mul]
              apply sum_congr rfl
              intro s hs
              split_ifs <;> simp_all
    _ = (commonShiftCount A (b₁ - b₂) : ℝ) ^ p * F (b₁ - b₂) := by
      rw [sum_all_coordinate_indicators]

/-- Exact normalized sifting identity.  The displayed factor is the one that
is lost if ambient averages and uniform averages on `B₁,B₂` are conflated. -/
theorem sifting_identity (A B₁ B₂ : Finset G) (p : ℕ) (F : G → ℝ)
    (hA : A.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty) :
    weightedCorrelationIntegral A B₁ B₂ p F =
      (ambientDensity A) ⁻¹ ^ (2 * p) *
        ((Fintype.card G : ℝ) ^ 2 / ((B₁.card : ℝ) * B₂.card)) *
          shiftAverage p (fun s ↦ rawPairAverage (siftedSet A B₁ s) (siftedSet A B₂ s) F) := by
  have hAc : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  have hB₁c : (B₁.card : ℝ) ≠ 0 := by exact_mod_cast hB₁.card_ne_zero
  have hB₂c : (B₂.card : ℝ) ≠ 0 := by exact_mod_cast hB₂.card_ne_zero
  have hGc : (Fintype.card G : ℝ) ≠ 0 := by positivity
  unfold weightedCorrelationIntegral pairProbability selfCorrelation ambientDensity
    shiftAverage rawPairAverage
  have hpairscale :
      pairSum B₁ B₂
          (fun x ↦ ((Fintype.card G : ℝ) / (A.card : ℝ) ^ 2 *
            commonShiftCount A x) ^ p * F x) =
        ((Fintype.card G : ℝ) / (A.card : ℝ) ^ 2) ^ p *
          pairSum B₁ B₂ (fun x ↦ (commonShiftCount A x : ℝ) ^ p * F x) := by
    calc
      pairSum B₁ B₂
          (fun x ↦ ((Fintype.card G : ℝ) / (A.card : ℝ) ^ 2 *
            commonShiftCount A x) ^ p * F x) =
          pairSum B₁ B₂
            (fun x ↦ ((Fintype.card G : ℝ) / (A.card : ℝ) ^ 2) ^ p *
              ((commonShiftCount A x : ℝ) ^ p * F x)) := by
                apply congrArg (pairSum B₁ B₂)
                funext x
                rw [mul_pow]
                ring
      _ = _ := pairSum_const_mul B₁ B₂ _ _
  have hsumdiv :
      (∑ s : Fin p → G,
          pairSum (siftedSet A B₁ s) (siftedSet A B₂ s) F /
            (Fintype.card G : ℝ) ^ 2) =
        (∑ s : Fin p → G, pairSum (siftedSet A B₁ s) (siftedSet A B₂ s) F) /
          (Fintype.card G : ℝ) ^ 2 := by
    rw [Finset.sum_div]
  have hrawfold :
      (∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂,
        (commonShiftCount A (b₁ - b₂) : ℝ) ^ p * F (b₁ - b₂)) =
        pairSum B₁ B₂ (fun x ↦ (commonShiftCount A x : ℝ) ^ p * F x) := rfl
  rw [hpairscale, hsumdiv, sum_pairSum_sifted]
  rw [hrawfold]
  field_simp [hAc, hB₁c, hB₂c, hGc]
  ring

section PopularDifferences

open Function MeasureTheory Real
open scoped ENNReal NNReal Indicator Pointwise mu

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The localized popular-differences conclusion on two finite base sets.
This is the direct finite DRC output: it records the subset relations, the
`1-δ` mass conclusion, and the exact `1/4` density constant. -/
theorem popularDifferences {A : Finset G} {p : ℕ} {ε δ : ℝ}
    (B₁ B₂ : Finset G) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ)
    (hp : Even p) (hp₂ : 2 ≤ p) (hpε : ε⁻¹ * Real.log (2 / δ) ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty)
    (hf : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧ x ∉ s p ε B₁ B₂ A) :
    ∃ A₁, A₁ ⊆ B₁ ∧ ∃ A₂, A₂ ⊆ B₂ ∧
      1 - δ ≤ ∑ x ∈ s p ε B₁ B₂ A, (μ A₁ ○ᵈ μ A₂) x ∧
      (4 : ℝ)⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p) ≤
        #A₁ / #B₁ ∧
      (4 : ℝ)⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p) ≤
        #A₂ / #B₂ := by
  exact _root_.sifting B₁ B₂ hε hε₁ hδ hp hp₂ hpε hB hA hf

/-- Unconditional popular-differences sifting in the ambient finite group.

The exponent is a natural even number, the tail loss is exactly `δ`, and the
two output densities are each at least `1/4 * dens(A)^(2p)`.  This is the
finite form used when the local weight is uniform on the whole group. -/
theorem popularDifferences_univ {A : Finset G} {p : ℕ} {ε δ : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hp : Even p) (hp₀ : p ≠ 0)
    (hpε : ε⁻¹ * Real.log (2 / δ) ≤ p) (hA : A.Nonempty) :
    ∃ A₁ A₂ : Finset G,
      1 - δ ≤ ∑ x ∈ s p ε Finset.univ Finset.univ A, (μ A₁ ○ᵈ μ A₂) x ∧
      (4 : ℝ)⁻¹ * A.dens ^ (2 * p) ≤ A₁.dens ∧
      (4 : ℝ)⁻¹ * A.dens ^ (2 * p) ≤ A₂.dens := by
  exact sifting_cor hε hε₁ hδ hp hp₀ hpε hA

end PopularDifferences

#print axioms sifting_identity
#print axioms popularDifferences
#print axioms popularDifferences_univ

end

end Sifting
end Erdos140

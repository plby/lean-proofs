/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.BlockCRTClose
import ErdosProblems.Erdos144.OccupancyTransfer
import ErdosProblems.Erdos144.PrimeBlockModel

/-!
# The prime-block CRT transfer for Erdős Problem 144

This file specializes the abstract occupancy law to logarithmic prime blocks.
It produces a periodic set of integers, proves that every member has two
close divisors, and compares its exact density with the corresponding
harmonic Bernoulli good-event mass.
-/

open scoped BigOperators

namespace Erdos144.PrimeTransfer

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos144.PrimeBlocks

/-- The good-event mass on a finite set of block labels, with harmonic
inclusion probability `1/i`. -/
def harmonicSubtypeGoodMass (I : Finset ℕ) (L : ℕ) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset (Finset ↥I)).filter
      (Erdos144.BlockCRTClose.BlockGood Subtype.val L),
    Erdos697.Bernoulli.weight (Finset.univ : Finset ↥I)
      (fun i => 1 / (i.1 : ℝ)) T

/-- The exact periodic CRT set supplied by logarithmic prime blocks. -/
def primeCRTSet (K : ℕ) (I : Finset ℕ) (L : ℕ) (hK : 0 < K) : Set ℕ :=
  {n | Erdos144.BlockCRTClose.BlockGood Subtype.val L
    (Erdos144.OccupancyTransfer.occupiedLabels
      (Erdos144.PrimeBlockModel.κ K I)
      (Erdos697.CRTModel.zeroSet
        (@Erdos144.PrimeBlockModel.primeValue K I)
        (ZMod.prodEquivPi (@Erdos144.PrimeBlockModel.primeValue K I)
          (Erdos144.PrimeBlockModel.primeValue_pairwise_coprime (I := I)
            (K := K) hK)
          (n : ZMod (∏ z, Erdos144.PrimeBlockModel.primeValue z)))))}

/-- The abstract occupancy parameter of one fiber is the prime-block
occupancy defined in `PrimeBlocks`. -/
theorem occupancyParam_eq_logBlockOccupancy
    (K : ℕ) (I : Finset ℕ) (i : ↥I) :
    Erdos144.OccupancyTransfer.occupancyParam
        (Erdos144.PrimeBlockModel.κ K I)
        (fun i p => 1 / (Erdos144.PrimeBlockModel.primeValue
          (Sigma.mk i p) : ℝ)) i =
      logBlockOccupancy K i.1 := by
  unfold Erdos144.OccupancyTransfer.occupancyParam logBlockOccupancy occupancy
  change 1 - (∏ p : {p : ℕ // p ∈ logBlock K i.1},
      (1 - 1 / (p.1 : ℝ))) =
    1 - ∏ p ∈ logBlock K i.1, (1 - (p : ℝ)⁻¹)
  congr 1
  symm
  simpa only [one_div] using
    (Finset.prod_subtype (logBlock K i.1) (fun _ => Iff.rfl)
      (fun p : ℕ => 1 - 1 / (p : ℝ)))

theorem occupancyParam_nonneg (K : ℕ) (I : Finset ℕ) (i : ↥I) :
    0 ≤ Erdos144.OccupancyTransfer.occupancyParam
      (Erdos144.PrimeBlockModel.κ K I)
      (fun i p => 1 / (Erdos144.PrimeBlockModel.primeValue
        (Sigma.mk i p) : ℝ)) i := by
  rw [occupancyParam_eq_logBlockOccupancy]
  exact (occupancy_bounds _ _).1

theorem occupancyParam_le_one (K : ℕ) (I : Finset ℕ) (i : ↥I) :
    Erdos144.OccupancyTransfer.occupancyParam
      (Erdos144.PrimeBlockModel.κ K I)
      (fun i p => 1 / (Erdos144.PrimeBlockModel.primeValue
        (Sigma.mk i p) : ℝ)) i ≤ 1 := by
  rw [occupancyParam_eq_logBlockOccupancy]
  exact (occupancy_bounds _ _).2.1

/-- Occupancy parameter of a logarithmic prime block, in the exact form
used by the generic transfer theorem. -/
def primeOccupancy (K : ℕ) (I : Finset ℕ) (i : ↥I) : ℝ :=
  Erdos144.OccupancyTransfer.occupancyParam
    (Erdos144.PrimeBlockModel.κ K I)
    (fun i p => 1 / (Erdos144.PrimeBlockModel.primeValue
      (Sigma.mk i p) : ℝ)) i

@[simp] theorem primeOccupancy_eq (K : ℕ) (I : Finset ℕ) (i : ↥I) :
    primeOccupancy K I i = logBlockOccupancy K i.1 :=
  occupancyParam_eq_logBlockOccupancy K I i

/-- Exact density supplied by the finite prime-block CRT model. -/
def primeDensity (K : ℕ) (I : Finset ℕ) (L : ℕ) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset (Finset ↥I)).filter
      (Erdos144.BlockCRTClose.BlockGood Subtype.val L),
    Erdos697.Bernoulli.weight (Finset.univ : Finset ↥I)
      (primeOccupancy K I) T

/-- The occupied-label formulation of the good event is exactly the flat
coordinate formulation consumed by `BlockCRTClose`. -/
theorem blockGood_occupiedLabels_iff
    {K : ℕ} {I : Finset ℕ} {L : ℕ}
    (Z : Finset (Erdos144.PrimeBlockModel.PrimeIndex K I)) :
    Erdos144.BlockCRTClose.BlockGood Subtype.val L
        (Erdos144.OccupancyTransfer.occupiedLabels
          (Erdos144.PrimeBlockModel.κ K I) Z) ↔
      Erdos144.BlockCRTClose.BlockGood
        (fun z : Erdos144.PrimeBlockModel.PrimeIndex K I => z.1.val) L Z := by
  have hlabels :
      Erdos144.BlockCRTClose.occupiedLabels
          (fun z : Erdos144.PrimeBlockModel.PrimeIndex K I => z.1.val) Z =
        Erdos144.BlockCRTClose.occupiedLabels Subtype.val
          (Erdos144.OccupancyTransfer.occupiedLabels
            (Erdos144.PrimeBlockModel.κ K I) Z) := by
    rw [Erdos144.OccupancyTransfer.occupiedLabels_eq_image_fst]
    unfold Erdos144.BlockCRTClose.occupiedLabels
    rw [Finset.image_image]
    apply Finset.image_congr
    intro z _hz
    rfl
  unfold Erdos144.BlockCRTClose.BlockGood
  rw [hlabels]

/-- Every integer in the logarithmic prime-block CRT good set has two
divisors with ratio strictly less than two. -/
theorem primeCRTSet_subset_hasCloseDivisors
    {K : ℕ} {I : Finset ℕ} {L : ℕ}
    (hK : 0 < K)
    (hresolution : 2 * (L : ℝ) / (K : ℝ) < Real.log 2) :
    primeCRTSet K I L hK ⊆ {n : ℕ | Erdos144.CRTClose.HasCloseDivisors n} := by
  intro n hn
  have hgoodFlat : Erdos144.BlockCRTClose.BlockGood
      (fun z : Erdos144.PrimeBlockModel.PrimeIndex K I => z.1.val) L
      (Erdos697.CRTModel.zeroSet
        (@Erdos144.PrimeBlockModel.primeValue K I)
        (ZMod.prodEquivPi (@Erdos144.PrimeBlockModel.primeValue K I)
          (Erdos144.PrimeBlockModel.primeValue_pairwise_coprime hK)
          (n : ZMod (∏ z, Erdos144.PrimeBlockModel.primeValue z)))) :=
    (blockGood_occupiedLabels_iff _).mp hn
  apply Erdos144.BlockCRTClose.hasCloseDivisors_of_crtBlockGood
    (p := @Erdos144.PrimeBlockModel.primeValue K I)
    (label := fun z : Erdos144.PrimeBlockModel.PrimeIndex K I => z.1.val)
    (K := (K : ℝ)) (L := L) (n := n)
    Erdos144.PrimeBlockModel.primeValue_prime
    (Erdos144.PrimeBlockModel.primeValue_injective hK)
  · exact_mod_cast hK
  · intro z
    rcases z with ⟨i, p⟩
    have h := logBlock_log_error_bounds hK p.2
    change |Real.log (p.1 : ℝ) - (i.1 : ℝ) / (K : ℝ)| ≤ 1 / (K : ℝ)
    rw [abs_of_nonneg h.1]
    simpa [one_div] using h.2
  · exact hresolution
  · exact hgoodFlat

/-- The logarithmic prime-block CRT set has its exact finite product
density. -/
theorem primeCRTSet_hasDensity
    (K : ℕ) (I : Finset ℕ) (L : ℕ) (hK : 0 < K) :
    (primeCRTSet K I L hK).HasDensity (primeDensity K I L) := by
  let prime : Erdos144.PrimeBlockModel.PrimeIndex K I → ℕ :=
    @Erdos144.PrimeBlockModel.primeValue K I
  let : NeZero (∏ z, prime z) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun z _hz =>
      Erdos144.PrimeBlockModel.primeValue_ne_zero z)⟩
  have h := Erdos144.OccupancyTransfer.crt_occupiedLabels_good_hasDensity
    (κ := Erdos144.PrimeBlockModel.κ K I)
    prime (Erdos144.PrimeBlockModel.primeValue_pairwise_coprime hK)
    (Erdos144.BlockCRTClose.BlockGood Subtype.val L)
  change (primeCRTSet K I L hK).HasDensity (primeDensity K I L) at h
  exact h

/-- Comparison of the exact prime-block density with the harmonic product
law on the same finite set of labels. -/
theorem harmonicSubtypeGoodMass_sub_error_le_primeDensity
    (K : ℕ) (I : Finset ℕ) (L : ℕ)
    (hIpos : ∀ i ∈ I, 1 ≤ i) :
    harmonicSubtypeGoodMass I L -
        2 * ∑ i : ↥I,
          |logBlockOccupancy K i.1 - 1 / (i.1 : ℝ)| ≤
      primeDensity K I L := by
  let Good : Finset ↥I → Prop :=
    Erdos144.BlockCRTClose.BlockGood Subtype.val L
  let r : ↥I → ℝ := fun i => 1 / (i.1 : ℝ)
  have hr0 : ∀ i : ↥I, 0 ≤ r i := by
    intro i
    simp [r]
  have hr1 : ∀ i : ↥I, r i ≤ 1 := by
    intro i
    have hi : (1 : ℝ) ≤ i.1 := by exact_mod_cast hIpos i.1 i.2
    exact (div_le_one₀ (by positivity : (0 : ℝ) < i.1)).2 hi
  have hdist := Erdos144.OccupancyTransfer.bernoulli_good_mass_sub_le
    (primeOccupancy K I) r Good
    (fun i => occupancyParam_nonneg K I i)
    (fun i => occupancyParam_le_one K I i) hr0 hr1
  have hraw : harmonicSubtypeGoodMass I L -
      2 * ∑ i : ↥I, |primeOccupancy K I i - r i| ≤
        primeDensity K I L := by
    have hneg : harmonicSubtypeGoodMass I L - primeDensity K I L ≤
        |primeDensity K I L - harmonicSubtypeGoodMass I L| := by
      simpa only [neg_sub] using neg_le_abs
        (primeDensity K I L - harmonicSubtypeGoodMass I L)
    have hdist' : |primeDensity K I L - harmonicSubtypeGoodMass I L| ≤
        2 * ∑ i : ↥I, |primeOccupancy K I i - r i| := by
      simpa only [primeDensity, harmonicSubtypeGoodMass, Good, r] using hdist
    linarith
  simpa only [r, primeOccupancy_eq] using hraw

/-- The complete finite transfer statement.  It returns an exact periodic
density, the close-divisor inclusion, and the comparison with the harmonic
good-event mass. -/
theorem exists_primeCRT_subset_density
    (K : ℕ) (I : Finset ℕ) (L : ℕ)
    (hK : 0 < K) (hIpos : ∀ i ∈ I, 1 ≤ i)
    (hresolution : 2 * (L : ℝ) / (K : ℝ) < Real.log 2) :
    ∃ A : Set ℕ, ∃ d : ℝ,
      A ⊆ {n : ℕ | Erdos144.CRTClose.HasCloseDivisors n} ∧
      A.HasDensity d ∧
      harmonicSubtypeGoodMass I L -
          2 * ∑ i : ↥I,
            |logBlockOccupancy K i.1 - 1 / (i.1 : ℝ)| ≤ d := by
  exact ⟨primeCRTSet K I L hK, primeDensity K I L,
    primeCRTSet_subset_hasCloseDivisors hK hresolution,
    primeCRTSet_hasDensity K I L hK,
    harmonicSubtypeGoodMass_sub_error_le_primeDensity K I L hIpos⟩

/-- Interval-indexed form used by the final scale selection. -/
theorem exists_logInterval_primeCRT_subset_density
    (K C N L : ℕ) (hK : 0 < K) (hC : 0 < C)
    (hresolution : 2 * (L : ℝ) / (K : ℝ) < Real.log 2) :
    ∃ A : Set ℕ, ∃ d : ℝ,
      A ⊆ {n : ℕ | Erdos144.CRTClose.HasCloseDivisors n} ∧
      A.HasDensity d ∧
      harmonicSubtypeGoodMass (Finset.Ioc C N) L -
          2 * ∑ i : ↥(Finset.Ioc C N),
            |logBlockOccupancy K i.1 - 1 / (i.1 : ℝ)| ≤ d := by
  apply exists_primeCRT_subset_density K (Finset.Ioc C N) L hK
  · intro i hi
    have hiC := (Finset.mem_Ioc.mp hi).1
    omega
  · exact hresolution

end

end Erdos144.PrimeTransfer

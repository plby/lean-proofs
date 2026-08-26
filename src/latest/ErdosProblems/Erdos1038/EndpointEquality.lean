import ErdosProblems.Erdos1038.EmpiricalMeasure
import ErdosProblems.Erdos1038.SupremumExamples

/-!
# Equality bridge for the sharp upper theorem

The equality case of Tao's probability-measure theorem is the symmetric
two-point measure on `{-1,1}`.  This file proves that an empirical root
measure can equal that measure only when the monic polynomial is
`(X^2 - 1)^m` for a positive integer `m`.
-/

open scoped ENNReal Real BigOperators
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

def endpointRootMultiset : Multiset ℝ := {(-1 : ℝ), 1}

theorem endpointRootMultiset_ne_zero : endpointRootMultiset ≠ 0 := by
  simp [endpointRootMultiset]

def endpointRootPMF : PMF ℝ :=
  PMF.ofMultiset endpointRootMultiset endpointRootMultiset_ne_zero

def endpointRootProbability : ProbabilityMeasure ℝ :=
  ⟨endpointRootPMF.toMeasure, inferInstance⟩

theorem support_endpointRootPMF :
    endpointRootPMF.support = ({-1, 1} : Set ℝ) := by
  simp [endpointRootPMF, endpointRootMultiset, PMF.support_ofMultiset]

theorem empiricalRootProbability_eq_endpoint_imp_rootSet
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hP : empiricalRootProbability f hf = endpointRootProbability) :
    rootSet f = ({-1, 1} : Set ℝ) := by
  have hm : (empiricalRootPMF f hf).toMeasure = endpointRootPMF.toMeasure :=
    congrArg (fun P : ProbabilityMeasure ℝ ↦ (P : Measure ℝ)) hP
  have hp : empiricalRootPMF f hf = endpointRootPMF :=
    PMF.toMeasure_injective hm
  rw [← empiricalRootPMF_support f hf, hp, support_endpointRootPMF]

theorem empiricalRootProbability_eq_endpoint_counts
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hP : empiricalRootProbability f hf = endpointRootProbability) :
    2 * f.roots.count (-1) = f.roots.card ∧
      2 * f.roots.count 1 = f.roots.card := by
  have hm : (empiricalRootPMF f hf).toMeasure = endpointRootPMF.toMeasure :=
    congrArg (fun P : ProbabilityMeasure ℝ ↦ (P : Measure ℝ)) hP
  have hp : empiricalRootPMF f hf = endpointRootPMF :=
    PMF.toMeasure_injective hm
  have hneg := congrArg (fun p : PMF ℝ ↦ p (-1)) hp
  have hpos := congrArg (fun p : PMF ℝ ↦ p 1) hp
  change (f.roots.count (-1) : ℝ≥0∞) / f.roots.card =
    (endpointRootMultiset.count (-1) : ℝ≥0∞) / endpointRootMultiset.card at hneg
  change (f.roots.count 1 : ℝ≥0∞) / f.roots.card =
    (endpointRootMultiset.count 1 : ℝ≥0∞) / endpointRootMultiset.card at hpos
  norm_num [endpointRootMultiset] at hneg hpos
  have hcardposN : 0 < f.roots.card := Multiset.card_pos.mpr (roots_ne_zero hf)
  have hcardposR : 0 < (f.roots.card : ℝ) := by exact_mod_cast hcardposN
  have hnegR := congrArg ENNReal.toReal hneg
  have hposR := congrArg ENNReal.toReal hpos
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hnegR hposR
  norm_num at hnegR hposR
  field_simp [ne_of_gt hcardposR] at hnegR hposR
  constructor
  · rw [Polynomial.count_roots, mul_comm]
    exact_mod_cast hnegR
  · rw [Polynomial.count_roots]
    exact_mod_cast hposR

theorem roots_eq_replicate_endpoints_of_rootSet
    {f : Polynomial ℝ} (hroot : rootSet f = ({-1, 1} : Set ℝ)) :
    f.roots = Multiset.replicate (f.roots.count (-1)) (-1) +
      Multiset.replicate (f.roots.count 1) 1 := by
  classical
  rw [Multiset.ext]
  intro r
  by_cases hrn : r = -1
  · subst r
    simp only [Multiset.count_add, Multiset.count_replicate]
    norm_num
  by_cases hrp : r = 1
  · subst r
    simp only [Multiset.count_add, Multiset.count_replicate]
    norm_num
  have hrnot : r ∉ f.roots := by
    intro hr
    have : r ∈ ({-1, 1} : Set ℝ) := by
      rw [← hroot, mem_rootSet_iff]
      exact hr
    simp only [mem_insert_iff, mem_singleton_iff] at this
    exact this.elim hrn hrp
  rw [Multiset.count_eq_zero.mpr hrnot, Multiset.count_add,
    Multiset.count_replicate, Multiset.count_replicate]
  simp [Ne.symm hrn, Ne.symm hrp]

theorem empiricalRootProbability_eq_endpoint_imp_extremal
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hP : empiricalRootProbability f hf = endpointRootProbability) :
    ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m := by
  let m := f.roots.count (-1)
  have hcounts := empiricalRootProbability_eq_endpoint_counts hf hP
  have hrootset := empiricalRootProbability_eq_endpoint_imp_rootSet hf hP
  have hmpos : 0 < m := by
    have hmem : (-1 : ℝ) ∈ f.roots := by
      rw [← mem_rootSet_iff, hrootset]
      simp
    exact Multiset.count_pos.mpr hmem
  have hcountEq : f.roots.count 1 = m := by
    dsimp [m]
    omega
  have hroots := roots_eq_replicate_endpoints_of_rootSet hrootset
  rw [hcountEq] at hroots
  refine ⟨m, hmpos, ?_⟩
  rw [hf.splits.eq_prod_roots_of_monic hf.monic, hroots]
  simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
    Multiset.prod_replicate]
  change (X - C (-1 : ℝ)) ^ m * (X - C (1 : ℝ)) ^ m =
    (X ^ 2 - 1) ^ m
  rw [← mul_pow]
  congr 1
  simp only [map_neg, map_one]
  ring

end

end Erdos1038

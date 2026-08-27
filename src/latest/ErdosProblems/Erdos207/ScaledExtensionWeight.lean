/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairTwoAwayAbsorberBound
import ErdosProblems.Erdos207.PairAggregateTwoAwayAbsorberBound
import ErdosProblems.Erdos207.PairAggregateTwoAwayThreatWeight
import ErdosProblems.Erdos207.RelativeExtensionMonotonicity

/-!
# Scaling finite extension weights

The long initial process has one-step hazard `fuel / D`, rather than exactly
the ambient inverse scale used to state the absorber extension bounds.  A
pointwise loss by a factor `c` costs at most `c ^ q` on configurations of
cardinality at most `q`.  This module records that elementary comparison and
specializes it to the three two-away witness systems used by the stopped
process.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

lemma setWeight_le_pow_mul_setWeight
    {W : Type*} [DecidableEq W] {pi rho : W → ℝ≥0}
    {c : ℝ≥0} {q : ℕ}
    (hc : 1 ≤ c) (hpi : ∀ x, pi x ≤ c * rho x)
    (S : Finset W) (hS : S.card ≤ q) :
    setWeight pi S ≤ c ^ q * setWeight rho S := by
  calc
    setWeight pi S ≤ setWeight (fun x ↦ c * rho x) S :=
      setWeight_mono_pointwise hpi S
    _ = c ^ S.card * setWeight rho S := by
      simp [setWeight, Finset.prod_mul_distrib]
    _ ≤ c ^ q * setWeight rho S := by
      gcongr

lemma extensionWeight_le_pow_mul_extensionWeight
    {W I : Type*} [DecidableEq W] [Fintype I]
    (F : I → Finset W) {pi rho : W → ℝ≥0}
    {c : ℝ≥0} {q : ℕ}
    (hc : 1 ≤ c) (hpi : ∀ x, pi x ≤ c * rho x)
    (hcard : ∀ i, (F i).card ≤ q) (A : Finset W) :
    extensionWeight F pi A ≤ c ^ q * extensionWeight F rho A := by
  classical
  unfold extensionWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  by_cases hA : A ⊆ F i
  · simp only [if_pos hA]
    exact setWeight_le_pow_mul_setWeight hc hpi _
      ((card_le_card sdiff_subset).trans (hcard i))
  · simp [hA]

theorem HasExtensionBound.scale_pointwise
    {W I : Type*} [DecidableEq W] [Fintype I]
    {F : I → Finset W} {pi rho : W → ℝ≥0}
    {c kappa : ℝ≥0} {q : ℕ}
    (hF : HasExtensionBound F rho kappa)
    (hc : 1 ≤ c) (hpi : ∀ x, pi x ≤ c * rho x)
    (hcard : ∀ i, (F i).card ≤ q) :
    HasExtensionBound F pi (c ^ q * kappa) := by
  intro A
  exact (extensionWeight_le_pow_mul_extensionWeight F hc hpi hcard A).trans
    (mul_le_mul_of_nonneg_left (hF A) zero_le)

theorem absorberPairTwoAwayThreatRemainder_hasExtensionBound_scaled
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {U : TripleOn V} {P : PairOn V}
    (rate scale : ℝ≥0) (hscale : 1 ≤ scale)
    (hrate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    HasExtensionBound
      (fun z : PairTwoAwayThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) U P ↦
        pairTwoAwayThreatRemainder z)
      (constantTripleWeight rate)
      (scale ^ q * (pairTwoAwayThreatExtensionCoefficient q B : ℕ)) := by
  apply absorberPairTwoAwayThreatRemainder_hasExtensionBound.scale_pointwise
    hscale
  · intro T
    simpa [constantTripleWeight] using hrate
  · intro z
    exact (card_pairTwoAwayThreatRemainder_le
      (fun C hC ↦ card_le_cutoff_of_mem_absorberErdosForbidden hC) z).trans
      (Nat.sub_le q 2)

theorem absorberTwoAwayThreatRemainder_hasExtensionBound_scaled
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {U : TripleOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (rate scale : ℝ≥0) (hscale : 1 ≤ scale)
    (hrate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    HasExtensionBound
      (fun z : TwoAwayThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) U ↦
        twoAwayThreatRemainder z)
      (constantTripleWeight rate)
      (scale ^ q * (twoAwayThreatExtensionCoefficient q M H X B : ℕ)) := by
  apply (absorberTwoAwayThreatRemainder_hasExtensionBound hA2).scale_pointwise
    hscale
  · intro T
    simpa [constantTripleWeight] using hrate
  · intro z
    exact (card_twoAwayThreatRemainder_le
      (fun C hC ↦ card_le_cutoff_of_mem_absorberErdosForbidden hC) z).trans
      (Nat.sub_le q 2)

theorem absorberAggregatePairTwoAwayThreatRemainder_hasExtensionBound_scaled
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {B : TripleSystemOn V} {P : PairOn V}
    (rate scale : ℝ≥0) (hscale : 1 ≤ scale)
    (hrate : rate ≤ scale * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    HasExtensionBound
      (fun z : AggregatePairTwoAwayThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) P ↦
        aggregatePairTwoAwayThreatRemainder z)
      (constantTripleWeight rate)
      (scale ^ q *
        ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
          (Fintype.card V + 1 : ℝ≥0) ^ 2)) := by
  apply absorberAggregatePairTwoAwayThreatRemainder_hasExtensionBound.scale_pointwise
    hscale
  · intro T
    simpa [constantTripleWeight] using hrate
  · intro z
    exact (card_aggregatePairTwoAwayThreatRemainder_le
      (fun C hC ↦ card_le_cutoff_of_mem_absorberErdosForbidden hC) z).trans
      (Nat.sub_le q 2)

end

end Erdos207

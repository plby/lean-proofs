/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos88.StructuredConditioning
import ErdosProblems.Erdos88.SliceMixture
import ErdosProblems.Erdos88.StructuredTypical

/-!
# Exact finite mixtures for the structured branch

This module combines the remainder/covered disintegration with the exact
bucket-count disintegration.  It is the finite law-of-total-probability
bookkeeping used when Claims 12.1 and 12.2 are averaged in Section 12.
-/

open scoped BigOperators

namespace Erdos88.RLCD.BucketDecomposition

attribute [local instance] Classical.propDecidable

open Erdos88.BooleanSlices
open Erdos88.GaussianQuadratic

lemma eventProbability_half_eq_uniformProbability
    {A : Type*} [Fintype A] [DecidableEq A]
    (E : Finset A → Prop) :
    Probability.eventProbability (1 / 2 : ℝ) E =
      Concentration.uniformProbability E := by
  classical
  unfold Probability.eventProbability
  rw [← uniformExpectation_finset_eq_probability_half_finite]
  rw [Concentration.uniformExpectation, Concentration.uniformProbability,
    Finset.card_filter]
  push_cast
  rfl

lemma uniformProbability_equiv
    {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B]
    (e : A ≃ B) (E : B → Prop) :
    Concentration.uniformProbability (fun a ↦ E (e a)) =
      Concentration.uniformProbability E := by
  classical
  unfold Concentration.uniformProbability
  rw [show
      (Finset.univ.filter fun a : A ↦ E (e a)).card =
        (Finset.univ.filter E).card by
    rw [Finset.card_filter, Finset.card_filter]
    exact e.sum_comp (fun b ↦ if E b then (1 : ℕ) else 0),
    Fintype.card_congr e]

/-- A subset of the remainder and a Boolean assignment on the complement of
the covered coordinates are canonically equivalent. -/
noncomputable def remainderSubsetEquivOutsideAssignment
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho) :
    Finset (D.remainder : Set (Fin n)) ≃
      ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) :=
  (Equiv.finsetCongr D.outsideEquivRemainder.symm).trans
    (boolFunEquivFinset :
      ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) ≃
        Finset {v : Fin n // v ∉ D.blocks.biUnion id}).symm

lemma outsideAssignmentSet_remainderSubsetEquiv
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (R : Finset (D.remainder : Set (Fin n))) :
    LinearLCDCancellation.outsideAssignmentSet (D.blocks.biUnion id)
        (D.remainderSubsetEquivOutsideAssignment R) =
      BoundedWindow.subtypeSubsetImage D.remainder R := by
  classical
  let T : Finset {v : Fin n // v ∉ D.blocks.biUnion id} :=
    Equiv.finsetCongr D.outsideEquivRemainder.symm R
  have hdecode :
      (boolFunEquivFinset :
        ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) ≃
          Finset {v : Fin n // v ∉ D.blocks.biUnion id})
          (D.remainderSubsetEquivOutsideAssignment R) = T := by
    exact Equiv.apply_symm_apply _ T
  change
    ((boolFunEquivFinset :
        ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) ≃
          Finset {v : Fin n // v ∉ D.blocks.biUnion id})
      (D.remainderSubsetEquivOutsideAssignment R)).image Subtype.val =
        R.image Subtype.val
  rw [hdecode]
  ext v
  simp [T, outsideEquivRemainder]
  constructor
  · rintro ⟨hnot, hvR⟩
    have hvnotCovered : v ∉ D.blocks.biUnion id := by
      intro hv
      rw [Finset.mem_biUnion] at hv
      obtain ⟨I, hI, hvI⟩ := hv
      exact hnot I hI hvI
    have hvRem : v ∈ D.remainder := by
      rw [D.remainder_eq]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvnotCovered⟩
    refine ⟨hvRem, ?_⟩
    convert hvR using 1
  · rintro ⟨hvRem, hvR⟩
    have hvnotCovered : v ∉ D.blocks.biUnion id := by
      have := hvRem
      rw [D.remainder_eq, Finset.mem_sdiff] at this
      exact this.2
    refine ⟨?_, ?_⟩
    · intro I hI hvI
      exact hvnotCovered (Finset.mem_biUnion.mpr ⟨I, hI, hvI⟩)
    · convert hvR using 1

/-- The exceptional remainder assignments from the simultaneous degree
estimate occupy at most an `n⁻³ᵐ²` fraction of the outer probability
space, in the exact remainder-subset model used by the structured mixture. -/
theorem eventually_uniformProbability_remainder_atypical_le
    (gamma : ℝ) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ {k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
        (D : BucketDecomposition d k rho) (G : SimpleGraph (Fin n)),
        (D.remainder.card : ℝ) ≤ BooleanSlices.scale n (1 - gamma) →
        Concentration.uniformProbability
            (fun R : Finset (D.remainder : Set (Fin n)) ↦
              D.remainderSubsetEquivOutsideAssignment R ∈
                D.badRemainderConditionings G (Real.sqrt n)) ≤
          BooleanSlices.scale n (-3 / 2) := by
  have hbadEvent :=
    eventually_card_badRemainderConditionings_sqrt_le gamma hgamma
  filter_upwards [hbadEvent] with n hbadN
  intro k d rho D G hrem
  rw [uniformProbability_equiv
    D.remainderSubsetEquivOutsideAssignment
    (fun z ↦ z ∈ D.badRemainderConditionings G (Real.sqrt n))]
  rw [show Concentration.uniformProbability
      (fun z : {v : Fin n // v ∉ D.blocks.biUnion id} → Bool ↦
        z ∈ D.badRemainderConditionings G (Real.sqrt n)) =
      ((D.badRemainderConditionings G (Real.sqrt n)).card : ℝ) /
        Fintype.card ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) by
    simp [Concentration.uniformProbability]]
  have hcardPos :
      (0 : ℝ) < Fintype.card
        ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool) := by
    exact_mod_cast (Fintype.card_pos :
      0 < Fintype.card ({v : Fin n // v ∉ D.blocks.biUnion id} → Bool))
  apply (div_le_iff₀ hcardPos).2
  exact hbadN D G hrem

/-- The total probability of non-near-balanced bucket counts is eventually
at most `n⁻³ᵐ²`, uniformly over every KSSS equal-bucket partition. -/
theorem eventually_countVectorMass_not_nearBalanced_le :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (m : ℕ) (P : BucketPartition (Fin n) (Fin m)) (delta : ℝ),
        IsKSSSPartition delta P →
        countVectorMass P (fun ell ↦
            ¬ IsNearBalanced delta P (fun j ↦ (ell j).val)) ≤
          scale n (-3 / 2) := by
  have hpref := eventually_one_add_two_natCast_le_exp_log_sq
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 12)
  filter_upwards [hpref, hlog, Filter.eventually_ge_atTop 1] with
      n hprefN hlogN hn
  intro m P delta hpart
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hmargin : 0 ≤ ksssSliceMargin n delta := by
    rw [ksssSliceMargin]
    exact mul_nonneg (scale_nonneg n _)
      (Real.log_nonneg (by exact_mod_cast hn))
  have hprob := uniformProbability_not_isNearBalanced_le delta P hmargin
  have hcount := ksss_countTail_sum_le hnpos P hpart
  rw [countVectorMass_eq_uniformProbability]
  calc
    Concentration.uniformProbability (fun S : Finset (Fin n) ↦
        ¬ IsNearBalanced delta P
          (fun j ↦ (bucketCounts P S j).val)) ≤
        ∑ j : Fin m, 2 * Real.exp
          (-2 * ksssSliceMargin n delta ^ 2 /
            (P.fiber j).card) := hprob
    _ ≤ 2 * (n : ℝ) * Real.exp (-(Real.log n) ^ 2) := hcount
    _ ≤ (1 + 2 * (n : ℝ)) *
        Real.exp (-(Real.log n) ^ 2) := by
      gcongr
      linarith
    _ ≤ Real.exp ((7 / 8 : ℝ) * Real.log n ^ 2) *
        Real.exp (-(Real.log n) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hprefN (Real.exp_nonneg _)
    _ = Real.exp (-(Real.log n) ^ 2 / 8) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ scale n (-3 / 2) := by
      unfold scale
      change Real.exp (-(Real.log n) ^ 2 / 8) ≤
        (n : ℝ) ^ (-3 / 2 : ℝ)
      rw [Real.rpow_def_of_pos hnR (-3 / 2)]
      apply Real.exp_le_exp.mpr
      dsimp only [Function.comp_apply] at hlogN
      have hlogNonneg : 0 ≤ Real.log (n : ℝ) := by linarith
      nlinarith

/-- Exact structured law of total probability.  First choose the subset of
the RLCD remainder, then choose the bucket-count vector of the covered
subset, and finally choose uniformly inside its product slice. -/
theorem eventProbability_half_eq_structured_countVector_mixture
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho) (E : Finset (Fin n) → Prop) :
    Probability.eventProbability (1 / 2 : ℝ) E =
      Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (D.remainder : Set (Fin n)) ↦
          ∑ ell : BucketCountVector D.finCoveredPartition,
            (Fintype.card
                (ProductSlicePoint D.finCoveredPartition
                  (fun j ↦ (ell j).val)) : ℝ) /
                Fintype.card
                  (Finset (Fin (Fintype.card D.Covered))) *
              Concentration.uniformProbability
                (fun S : ProductSlicePoint D.finCoveredPartition
                    (fun j ↦ (ell j).val) ↦
                  E (BoundedWindow.subtypeSubsetImage D.remainder R ∪
                    D.finCoveredSubsetImage S.1))) := by
  classical
  rw [← D.eventProbability_half_remainder_covered_fubini E]
  congr 1
  funext R
  rw [eventProbability_half_eq_uniformProbability]
  exact uniformProbability_eq_sum_countVector D.finCoveredPartition
    (fun S ↦ E (BoundedWindow.subtypeSubsetImage D.remainder R ∪
      D.finCoveredSubsetImage S))

/-- A Claim 12.1 upper estimate for the centered product-slice polynomial
transfers pointwise to the original ambient polynomial after a fixed
remainder conditioning.  The deterministic conditional shift is absorbed
by translating the center of the window. -/
lemma conditionedProductSlice_window_upper_of_claim121
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (ell : Fin (Fintype.card D.BlockIndex) → ℕ)
    [Nonempty (ProductSlicePoint D.finCoveredPartition ell)]
    {B K : ℝ}
    (hupper :
      let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
        hbucket.choose (D.finCoveredGraph G)
      let f := Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O))
        (productSliceDelta D.finCoveredPartition hbucket.choose ell)
      ∀ y : ℝ,
        Esseen.smallBall
            (Esseen.finiteUniformLaw
              (ProductSlicePoint D.finCoveredPartition ell)
              (productSliceQuadratic D.finCoveredPartition ell
                (-trace F) f F)) B y ≤ K)
    (x : ℝ) :
    Concentration.uniformProbability
        (fun S : ProductSlicePoint D.finCoveredPartition ell ↦
          |Probability.perturbedEdgePolynomial G e0 c
              (O ∪ D.finCoveredSubsetImage S.1) - x| ≤ B) ≤ K := by
  classical
  let Gc := D.finCoveredGraph G
  let cc := D.conditionedCoveredCoefficient G c O
  let E := GraphQuadratic.graphSliceConstant Gc
    (Probability.perturbedEdgePolynomial G e0 c O) cc
  let y := GraphQuadratic.graphEffectiveLinear Gc cc
  let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
    hbucket.choose Gc
  let f := Structured.wStar
    (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix Gc) y
    (productSliceDelta D.finCoveredPartition hbucket.choose ell)
  let shift := Structured.conditionalShift E
    (RobustRank.graphAdjacencyMatrix Gc) y
    (productSliceDelta D.finCoveredPartition hbucket.choose ell) + trace F
  have hpoly (S : ProductSlicePoint D.finCoveredPartition ell) :
      Probability.perturbedEdgePolynomial G e0 c
          (O ∪ D.finCoveredSubsetImage S.1) =
        shift + productSliceQuadratic D.finCoveredPartition ell
          (-trace F) f F S := by
    have hconditioned :=
      (D.sliceQuadratic_conditionedCovered_eq G e0 c hO S.1).symm
    have hslice :=
      sliceQuadratic_graph_eq_shift_add_productSlice_counts
        D.finCoveredPartition hbucket ell Gc
          (Probability.perturbedEdgePolynomial G e0 c O) cc S
    exact hconditioned.trans (by
      simpa only [Gc, cc, E, y, F, f, shift, add_assoc] using hslice)
  have hevent :
      (fun S : ProductSlicePoint D.finCoveredPartition ell ↦
        |Probability.perturbedEdgePolynomial G e0 c
            (O ∪ D.finCoveredSubsetImage S.1) - x| ≤ B) =
      (fun S ↦
        |productSliceQuadratic D.finCoveredPartition ell
            (-trace F) f F S - (x - shift)| ≤ B) := by
    funext S
    rw [hpoly S]
    congr 2 <;> ring
  rw [hevent]
  change Fourier.finProbability
      (ProductSlicePoint D.finCoveredPartition ell)
        (fun S ↦
          |productSliceQuadratic D.finCoveredPartition ell
              (-trace F) f F S - (x - shift)| ≤ B) ≤ K
  rw [← Esseen.smallBall_finiteUniformLaw]
  simpa only [Gc, cc, y, F, f] using hupper (x - shift)

end Erdos88.RLCD.BucketDecomposition

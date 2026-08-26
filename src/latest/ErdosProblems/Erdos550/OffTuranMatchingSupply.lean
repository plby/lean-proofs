import Mathlib
import ErdosProblems.Erdos550.OffTuranMatchingWeights
import ErdosProblems.Erdos550.OffTuranReducedDegreeData
import ErdosProblems.Erdos550.OffTuranThresholding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Genuine matching supply at a cleaned heavy head

The cleaned normalized degree is first restricted to the endpoint union of the
maximum matching.  On each endpoint its cleaned contribution is at most the
actual density-times-target-size weight.  Injectivity of the matching endpoints
then identifies the endpoint-union sum with the sum of whole-edge weights.
-/

open Finset SimpleGraph Finpartition

namespace Erdos550

open Classical

/-- Summing over the disjoint endpoint images of an indexed matching is the
same as summing the two endpoint contributions edge by edge. -/
lemma sum_matching_endpoint_union
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (cL cR : κ → ι) (f : ι → ℝ)
    (hinj : Function.Injective (Sum.elim cL cR)) :
    (∑ i ∈ (Finset.univ.image cL ∪ Finset.univ.image cR), f i) =
      ∑ k, (f (cL k) + f (cR k)) := by
  have hL : Function.Injective cL := by
    intro k j h
    exact Sum.inl.inj (hinj h)
  have hR : Function.Injective cR := by
    intro k j h
    exact Sum.inr.inj (hinj h)
  have hdisj :
      Disjoint (Finset.univ.image cL) (Finset.univ.image cR) := by
    rw [Finset.disjoint_left]
    intro i hiL hiR
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hiL
    obtain ⟨j, _hj, hcross⟩ := Finset.mem_image.mp hiR
    have himpossible : (Sum.inl k : Sum κ κ) = Sum.inr j :=
      hinj hcross.symm
    cases himpossible
  rw [Finset.sum_union hdisj]
  rw [Finset.sum_image (by
    intro k _ j _ h
    exact hL h)]
  rw [Finset.sum_image (by
    intro k _ j _ h
    exact hR h)]
  simp only [Finset.sum_add_distrib]

/-- The cleaned contribution into all matching endpoints is bounded by the
sum of the genuine whole-edge weights at the head. -/
lemma cleaned_endpoint_union_le_matchingWeight
    {V κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (ε d : ℝ) (scale : ℕ) (hscale : 0 < scale)
    (hsize : ∀ i : {C // C ∈ P.parts}, i.1.card ≤ scale)
    (head : {C // C ∈ P.parts})
    (cL cR : κ → {C // C ∈ P.parts})
    (hinj : Function.Injective (Sum.elim cL cR)) :
    (∑ i ∈ (Finset.univ.image cL ∪ Finset.univ.image cR),
        clusterContribution (G.regularityReduced P ε d) P scale head i) ≤
      ∑ k, hpHeadMatchingWeight G (offTuranReducedGraph G P ε d)
        (fun i : {C // C ∈ P.parts} => i.1) head cL cR k := by
  calc
    _ ≤ ∑ i ∈ (Finset.univ.image cL ∪ Finset.univ.image cR),
          hpHeadEndpointWeight G (offTuranReducedGraph G P ε d)
            (fun i : {C // C ∈ P.parts} => i.1) head i := by
      apply Finset.sum_le_sum
      intro i hi
      exact clusterContribution_reduced_le_headEndpointWeight
        G P ε d scale hscale hsize head i
    _ = ∑ k, hpHeadMatchingWeight G (offTuranReducedGraph G P ε d)
          (fun i : {C // C ∈ P.parts} => i.1) head cL cR k := by
      rw [sum_matching_endpoint_union cL cR
        (fun i => hpHeadEndpointWeight G
          (offTuranReducedGraph G P ε d)
          (fun i : {C // C ∈ P.parts} => i.1) head i) hinj]
      rfl

/-- A cleaned heavy head retains `base + 78 η N` of genuine matching weight
when the uncovered-cluster loss is at most `2 η N`. -/
theorem heavy_head_matchingWeight_lower
    {V κ : Type*} [Fintype V] [DecidableEq V]
    [Fintype κ] [DecidableEq κ]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {ε d base η : ℝ} {m₀ B : ℕ}
    (D : OffTuranReducedDegreeData G ε d base η m₀)
    (X Y : {C // C ∈ D.P.parts})
    (cL cR : κ → {C // C ∈ D.P.parts})
    (U : Finset {C // C ∈ D.P.parts})
    (hX : X ∈ heavyClusterFamily Finset.univ
      (clusterNormalizedDegree
        (G.regularityReduced D.P ε d) D.P D.scale)
      base η (Fintype.card V))
    (hinj : Function.Injective (Sum.elim cL cR))
    (hsmall : U.card < B)
    (hU : ∀ a, a ∈ U ↔ a ≠ X ∧ a ≠ Y ∧
      a ∉ Finset.univ.image cL ∧ a ∉ Finset.univ.image cR)
    (hloss :
      ((B + 2 : ℕ) : ℝ) * (D.scale : ℝ) ≤
        2 * η * Fintype.card V) :
    base + 78 * η * Fintype.card V ≤
      ∑ k, hpHeadMatchingWeight G
        (offTuranReducedGraph G D.P ε d)
        (fun i : {C // C ∈ D.P.parts} => i.1) X cL cR k := by
  let Clean := G.regularityReduced D.P ε d
  let f : {C // C ∈ D.P.parts} → ℝ :=
    fun i => clusterContribution Clean D.P D.scale X i
  have hheavy :
      base + 80 * η * Fintype.card V ≤
        clusterNormalizedDegree Clean D.P D.scale X :=
    (mem_heavyClusterFamily_iff Finset.univ
      (clusterNormalizedDegree Clean D.P D.scale)
      base η (Fintype.card V) X).mp hX |>.2
  have hmatched :
      clusterNormalizedDegree Clean D.P D.scale X -
          ((B + 2 : ℕ) : ℝ) * (D.scale : ℝ) ≤
        ∑ i ∈ (Finset.univ.image cL ∪ Finset.univ.image cR),
          clusterContribution Clean D.P D.scale X i := by
    have h := matched_clusterContribution_lower
      (V := V) f (D.scale : ℝ)
      (fun i => clusterContribution_le_scale
        Clean D.P D.scale D.scale_pos D.part_size_upper X i)
      (by positivity) X Y cL cR U hU B hsmall
    simpa [f, Clean, clusterNormalizedDegree] using! h
  have htoWeight :=
    cleaned_endpoint_union_le_matchingWeight
      G D.P ε d D.scale D.scale_pos D.part_size_upper X cL cR hinj
  linarith

end Erdos550

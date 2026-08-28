import Wikipedia.HopfProblem.DegreeCollapseSelectiveSupport
import Wikipedia.SmoothSixDPoincare.TwoSheetTubularBigon

/-!
# Branch isolation around the entire embedded bigon

The interior avoids the entire original immersed image. Its boundary lies
in the old branch-isolating neighborhood. Therefore the full bigon image
has no source preimage outside the selected patches. Compactness of the
original source supplies an open neighborhood of the whole bigon with
that property, including the interior used by the Whitney motion.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare WhitneyPairModel

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
  (tube : TubularBigon (E := E) S T a b k l h)

theorem preimage_bigon_image_subset {F : N → M} {W : Set N} {O : Set M}
    (havoid : ∀ p ∈ interior (bigon h), tube.map p ∉ range F)
    (ha : MapsTo a (Icc (0 : ℝ) 1) O) (hb : MapsTo b (Icc (0 : ℝ) 1) O)
    (hpre : F ⁻¹' O ⊆ W) : F ⁻¹' (tube.map '' bigon h) ⊆ W := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  by_cases hpi : p ∈ interior (bigon h)
  · exact (havoid p hpi ⟨x, hpx.symm⟩).elim
  · have hfront : p ∈ frontier (bigon h) := by
      rw [frontier, (isClosed_bigon h).closure_eq]
      exact ⟨hp, hpi⟩
    have hpO : tube.map p ∈ O := by
      obtain ⟨t, ht, he | he⟩ := (mem_frontier_bigon_iff_exists_time tube.height_pos p).mp hfront
      · rw [he, tube.lower t ht]
        exact ha ht
      · rw [he, tube.upper t ht]
        exact hb ht
    apply hpre
    change F x ∈ O
    rwa [← hpx]

theorem exists_whole_bigon_branch_neighborhood [TopologicalSpace N] [CompactSpace N] [T2Space M]
    {F : N → M} (hF : Continuous F) {U V : Set N} (hU : IsOpen U) (hV : IsOpen V)
    {O : Set M} (ha : MapsTo a (Icc (0 : ℝ) 1) O) (hb : MapsTo b (Icc (0 : ℝ) 1) O)
    (hpre : F ⁻¹' O ⊆ U ∪ V)
    (havoid : ∀ p ∈ interior (bigon h), tube.map p ∉ range F) :
    ∃ W : Set M, IsOpen W ∧ tube.map '' bigon h ⊆ W ∧ F ⁻¹' W ⊆ U ∪ V :=
  SelectiveSheet.exists_target_neighborhood_of_preimage_subset hF (hU.union hV)
    (preimage_bigon_image_subset tube havoid ha hb hpre)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

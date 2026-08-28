import Wikipedia.SmoothSixDPoincare.SmoothCleanBigonBoundary

/-!
# A fixed bigon boundary neighborhood avoiding the whole immersed image

An open target neighborhood isolates the two selected branch images.
Shrink the compact fixed boundary neighborhood into its preimage. The
previous two-branch cleanliness then excludes every point of the entire
obstacle image on the inward part of this smaller neighborhood.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare WhitneyPairModel

variable {E M Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Target branch isolation turns two-branch cleanliness into whole-image cleanliness. -/
theorem exists_whole_image_clean_boundary_neighborhood
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : SmoothCleanBigonBoundary (E := E) S T a b k l h)
    {g : Y → M} {O : Set M} (hO : IsOpen O)
    (haO : MapsTo a (Icc (0 : ℝ) 1) O) (hbO : MapsTo b (Icc (0 : ℝ) 1) O)
    (hcover : range g ∩ O ⊆ S ∪ T) :
    ∃ C : Set (ℝ × ℝ), IsCompact C ∧ IsClosed C ∧
      frontier (bigon h) ⊆ interior C ∧ C ⊆ d.neighborhood ∧ MapsTo d.map C O ∧
      ∀ p ∈ bigon h ∩ C, p ∉ frontier (bigon h) → d.map p ∉ range g := by
  let W : Set (ℝ × ℝ) := interior d.neighborhood ∩ d.map ⁻¹' O
  have hW : IsOpen W := isOpen_interior.inter (hO.preimage d.map.continuous)
  have hfrontW : frontier (bigon h) ⊆ W := by
    intro p hp
    refine ⟨d.boundary_covered hp, ?_⟩
    change d.map p ∈ O
    obtain ⟨t, ht, hp | hp⟩ := (mem_frontier_bigon_iff_exists_time d.height_pos p).mp hp
    · rw [hp, d.lower t ht]
      exact haO ht
    · rw [hp, d.upper t ht]
      exact hbO ht
  have hfrontCompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon d.height_pos).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, hC, hCc, hfrontC, hCW⟩ :=
    exists_compact_closed_between hfrontCompact hW hfrontW
  have hCD : C ⊆ d.neighborhood := fun p hp => interior_subset (hCW hp).1
  have hCO : MapsTo d.map C O := fun p hp => (hCW hp).2
  refine ⟨C, hC, hCc, hfrontC, hCD, hCO, ?_⟩
  intro p hp hnot himage
  exact d.clean p ⟨hp.1, hCD hp.2⟩ hnot (hcover ⟨himage, hCO hp.2⟩)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

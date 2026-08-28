import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspCompactification

/-!
# The actual cusp escapes every compact subset

The explicit orbit-height bound is continuous on the upper half-plane.
Images of its strict sublevel sets form an open cover of the full triangle
quotient.  Compactness reduces this cover to one height bound.  Thus the
actual high-cusp neighborhoods form a full neighborhood basis at the
added point, and the original quotient is genuinely noncompact.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

def boundedOrbitImage (R : ℝ) : TopologicalSpace.Opens TriangleOrbitSpace :=
  ⟨triangleOrbitProjection '' {z : ℍ | orbitHeightBound z < R},
    triangleOrbitProjection_isOpenMap _
      (isOpen_lt orbitHeightBound_continuous continuous_const)⟩

theorem boundedOrbitImage_mono :
    Monotone (fun R : ℝ => (boundedOrbitImage R : Set TriangleOrbitSpace)) := by
  intro R S hRS q hq
  obtain ⟨z, hz, rfl⟩ := hq
  exact ⟨z, hz.trans_le hRS, rfl⟩

theorem boundedOrbitImage_subset_cuspImage_compl (R : ℝ) :
    (boundedOrbitImage R : Set TriangleOrbitSpace) ⊆ (cuspImage R : Set TriangleOrbitSpace)ᶜ := by
  rintro q ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
  obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff w z).mp he
  have hb := triangle_im_le_orbitHeightBound g z
  rw [hg] at hb
  exact (not_lt_of_ge (le_trans hb hz.le)) hw

theorem boundedOrbitImage_cover :
    (⋃ R : ℝ, (boundedOrbitImage R : Set TriangleOrbitSpace)) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨z, rfl⟩ := triangleOrbitProjection_surjective q
  refine mem_iUnion.mpr ⟨orbitHeightBound z + 1, z, ?_, rfl⟩
  change orbitHeightBound z < orbitHeightBound z + 1
  linarith

/-- Every actual compact set is omitted by all sufficiently high cusp
images; the displayed threshold is already in the precisely invariant range. -/
theorem compact_subset_cuspImage_compl {K : Set TriangleOrbitSpace} (hK : IsCompact K) :
    ∃ Y : ℝ, width ≤ Y ∧ K ⊆ (cuspImage Y : Set TriangleOrbitSpace)ᶜ := by
  obtain ⟨R, hR⟩ := hK.elim_directed_cover
    (fun R : ℝ => (boundedOrbitImage R : Set TriangleOrbitSpace))
    (fun R => (boundedOrbitImage R).isOpen)
    (by rw [boundedOrbitImage_cover]; exact subset_univ K)
    (fun R S => ⟨max R S,
      boundedOrbitImage_mono (le_max_left R S), boundedOrbitImage_mono (le_max_right R S)⟩)
  refine ⟨max R width, le_max_right _ _, ?_⟩
  exact hR.trans ((boundedOrbitImage_mono (le_max_left R width)).trans
    (boundedOrbitImage_subset_cuspImage_compl (max R width)))

/-- The constructed high-cusp neighborhoods are a complete neighborhood
basis at the actual added point, not merely a list of open sets. -/
theorem cuspNeighborhood_basis :
    (𝓝 triangleCuspPoint).HasBasis (fun Y : ℝ => width ≤ Y)
      (fun Y => (cuspNeighborhood Y : Set TriangleCompactifiedOrbitSpace)) := by
  rw [Filter.hasBasis_iff]
  intro U
  constructor
  · intro hU
    obtain ⟨K, ⟨hKclosed, hKcompact⟩, hKU⟩ :=
      OnePoint.hasBasis_nhds_infty.mem_iff.mp hU
    obtain ⟨Y, hY, hKY⟩ := compact_subset_cuspImage_compl hKcompact
    refine ⟨Y, hY, ?_⟩
    intro x hx
    induction x using OnePoint.rec
    · exact hKU (Or.inr rfl)
    · rename_i q
      have hq : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hx
      exact hKU (Or.inl ⟨q, fun hqK => hKY hqK hq, rfl⟩)
  · rintro ⟨Y, _, hYU⟩
    exact mem_of_superset (cuspNeighborhood_mem_nhds Y) hYU

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

namespace Wikipedia.HopfProblem.SpecialPeriods

instance triangleOrbitSpace_noncompact : NoncompactSpace TriangleOrbitSpace where
  noncompact_univ := by
    intro hK
    obtain ⟨Y, _, hY⟩ := Triangle.compact_subset_cuspImage_compl hK
    obtain ⟨z, hz⟩ := Triangle.horodisc_nonempty Y
    exact hY (mem_univ (triangleOrbitProjection z)) ⟨z, hz, rfl⟩

theorem triangleOpenInclusion_isDenseEmbedding : IsDenseEmbedding triangleOpenInclusion :=
  OnePoint.isDenseEmbedding_coe

theorem triangleCompactifiedOrbitSpace_connected : ConnectedSpace TriangleCompactifiedOrbitSpace :=
  inferInstance

end Wikipedia.HopfProblem.SpecialPeriods

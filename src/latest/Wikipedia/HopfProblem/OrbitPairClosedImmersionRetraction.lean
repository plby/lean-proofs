import Wikipedia.HopfProblem.OrbitPairLocalImmersionRetraction

/-!
# Local source recovery for a closed embedded immersion

A local immersion left inverse initially recovers only one source
neighborhood. Closedness of the whole embedding permits shrinking the
target away from the image of the complementary source set. The resulting
smooth recovery map is correct for every source point whose image lies in
the smaller target neighborhood. This is the local input for extending a
field prescribed along the entire embedded track.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeImmersion

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem exists_recovery_of_closed_immersion {f : X → N}
    (hf : ContMDiff I J ∞ f) (hemb : Topology.IsClosedEmbedding f) (x : X)
    (hi : Injective (mfderiv I J f x)) :
    ∃ O : Set N, IsOpen O ∧ f x ∈ O ∧ ∃ r : N → X,
      ContMDiffOn J I ∞ r O ∧ ∀ y : X, f y ∈ O → r (f y) = y := by
  obtain ⟨U, O₀, hU, hxU, -, hO₀, hfxO₀, -, r, hr, -, hleft⟩ :=
    exists_native_source_leftInverse isOpen_univ hf.contMDiffOn (mem_univ x) hi
  let O : Set N := O₀ ∩ (f '' Uᶜ)ᶜ
  have hO : IsOpen O :=
    hO₀.inter (hemb.isClosedMap _ hU.isClosed_compl).isOpen_compl
  have hfx : f x ∈ O := by
    refine ⟨hfxO₀, ?_⟩
    rintro ⟨y, hy, heq⟩
    exact hy (hemb.injective heq ▸ hxU)
  refine ⟨O, hO, hfx, r, hr.mono inter_subset_left, ?_⟩
  intro y hy
  apply hleft y
  by_contra hnot
  exact hy.2 ⟨y, hnot, rfl⟩

end Wikipedia.HopfProblem.OrbitPair.NativeImmersion

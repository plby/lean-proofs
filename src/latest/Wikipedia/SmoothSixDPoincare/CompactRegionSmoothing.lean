import Wikipedia.SmoothSixDPoincare.GlobalMapSmoothing

/-!
# Relative smoothing when the nonsmooth region is compact

The source need not be compact. Cover only the compact region where smoothness
is missing, and use the already proved finite smoothing induction to preserve
smoothness elsewhere and every value on the prescribed closed set.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldSmoothing

variable {E G H H' X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [SigmaCompactSpace X]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- A continuous map smooth off a compact region admits a global smooth relative representative. -/
theorem exists_smooth_map_homotopicRel_of_smooth_off_compact_within_target (f : C(X, N))
    {K C U : Set X} (hK : IsCompact K) (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (hfK : ContMDiffOn I J ∞ f Kᶜ)
    {D : Set X} {O : Set N} (hO : IsOpen O) (hKO : MapsTo f K O) (hmaps : MapsTo f D O) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ HomotopicRelWithin f f' C D O := by
  classical
  have hp (x : K) :=
    exists_smoothing_patch_at_in_open (I := I) (J := J) f (x : X) hO (hKO x.property)
  choose p hcompatible hplateau hsource using hp
  have hcover : K ⊆ ⋃ x : K, (p x).plateau := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hplateau ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => (p x).plateau)
    (fun _ => isOpen_interior) hcover
  obtain ⟨f', _, hhom, hsm⟩ := exists_finite_patch_smoothing_within_target
    (fun i : s => p i.1) f (fun i => hcompatible i.1) hC hU hCU hfU
      (fun i => hsource i.1) hmaps Finset.univ
  refine ⟨f', ?_, hhom⟩
  intro x
  apply hsm x
  by_cases hx : x ∈ K
  · obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact Or.inr ⟨⟨i, his⟩, Finset.mem_univ _, hxi⟩
  · exact Or.inl ((hfK x hx).contMDiffAt (hK.isClosed.isOpen_compl.mem_nhds hx))

/-- Relative smoothing without an additional target containment condition. -/
theorem exists_smooth_map_homotopicRel_of_smooth_off_compact (f : C(X, N))
    {K C U : Set X} (hK : IsCompact K) (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (hfK : ContMDiffOn I J ∞ f Kᶜ) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  obtain ⟨f', hf', hrel⟩ :=
    exists_smooth_map_homotopicRel_of_smooth_off_compact_within_target f hK hC hU hCU
      hfU hfK isOpen_univ (mapsTo_univ f K) (mapsTo_univ f univ)
  exact ⟨f', hf', hrel.homotopicRel⟩

end Wikipedia.SmoothSixDPoincare.ManifoldSmoothing

import Wikipedia.SmoothSixDPoincare.AmbientTransversePatches

/-!
# One ambient transverse step preserving all previous compact work

Compact native transversality stability preserves the old core. Joint
continuity preserves every future chart plateau. A small good parameter
then makes the new core transverse, through an actual ambient diffeomorphism.
-/

noncomputable section

open Set Function Filter Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.NativeTransversality

variable {D Z G H H' K X Y N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
  [LindelofSpace (X × Y)]

/-- Treat one new compact core, preserve the old core and all future plateau conditions,
and retain the actual compactly supported ambient diffeomorphism. -/
theorem exists_patch_step {ι : Type*} [Finite ι]
    (p : ι → Patch J X (N := N)) (i : ι) {f : X → N} {g : Y → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ G)
    {C : Set X} (hC : IsCompact C)
    (htrans : ∀ x ∈ C, ∀ y, At I I' J f g x y) :
    ∃ e : Diffeomorph J J N N ∞,
      (∀ j, (p j).Compatible (e ∘ f)) ∧
      (∀ x ∈ C ∪ (p i).core, ∀ y, At I I' J (e ∘ f) g x y) ∧
      (∀ y ∉ (p i).chart.symm '' tsupport (p i).cutoff, e y = y) ∧
      SupportedDiffeomorph.IsotopicToIdentity e := by
  let A : G × X → N := fun q =>
    SupportedDiffeomorph.bumpFamily (p i).chart.symm (p i).cutoff (q.1, f q.2)
  have hkeep : ∀ᶠ a in 𝓝 (0 : G), ∀ j, (p j).Compatible (fun x => A (a, x)) := by
    apply eventually_all.mpr
    intro j
    exact SupportedDiffeomorph.eventually_bumpFamily_maps_compact_into_open (p i).chart.symm
      (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hf.continuous
      (p j).core_compact (p j).plateau_open (hcompatible j)
  obtain ⟨δ, hδ, -, hsmooth, -⟩ := SupportedDiffeomorph.exists_radius_ambient_bumpFamily
    (p i).chart.symm (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support
  have hA : ContMDiffOn (𝓘(ℝ, G).prod I) J ∞ A (ball (0 : G) δ ×ˢ univ) := by
    intro q hq
    have hsmall : ‖q.1‖ < δ := by simpa only [mem_ball, dist_zero_right] using hq.1
    have hpair : ContMDiffAt (𝓘(ℝ, G).prod I) (𝓘(ℝ, G).prod J) ∞
        (fun r : G × X => (r.1, f r.2)) q :=
      contMDiffAt_fst.prodMk (hf.comp contMDiff_snd).contMDiffAt
    exact ((hsmooth (q.1, f q.2) hsmall).comp q hpair).contMDiffWithinAt
  have hzero : (fun x => A (0, x)) = f := by
    funext x
    exact SupportedDiffeomorph.bumpFamily_zero _ _ _
  have hregular : ∀ᶠ a in 𝓝 (0 : G),
      ∀ z ∈ C ×ˢ (univ : Set Y), At I I' J (fun x => A (a, x)) g z.1 z.2 := by
    apply eventually_on_compact isOpen_ball hA hg hdim (hC.prod isCompact_univ)
      (mem_ball_self hδ)
    intro z hz
    rw [hzero]
    exact htrans z.1 hz.1 z.2
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp (hkeep.and hregular)
  obtain ⟨a, ha, e, he, hfixed, hisotopy, hnew⟩ :=
    ChartMapPerturbation.exists_ambient_transverse_plateau
    (p i).chart hf hg (p i).cutoff_smooth (p i).cutoff_compact (p i).cutoff_support hdim hε
  have hgood := hsmall (show a ∈ ball (0 : G) ε by simpa only [mem_ball, dist_zero_right] using ha)
  have heq : (fun x => A (a, x)) = e ∘ f := funext (fun x => (he (f x)).symm)
  refine ⟨e, ?_, ?_, hfixed, hisotopy⟩
  · intro j
    exact heq ▸ hgood.1 j
  · intro x hx y
    rcases hx with hx | hx
    · exact heq ▸ hgood.2 (x, y) ⟨hx, mem_univ y⟩
    · intro hxy
      have hplateau := hcompatible i hx
      exact hnew x ((p i).plateau_source hplateau) ((p i).plateau_one _ hplateau) y hxy

end Wikipedia.SmoothSixDPoincare.NativeTransversality

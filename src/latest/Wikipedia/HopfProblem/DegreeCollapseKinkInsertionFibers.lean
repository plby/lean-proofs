import Wikipedia.HopfProblem.DegreeCollapseNativeKinkInsertion

/-!
# Original unique fibers and the two actual new crossing sources

The constructed patch contains no original double source. The two crossing
sources of the inserted model lie in its actual compact inner support.
The complete original fiber recognition will exclude intersections with
unchanged source points outside this patch.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

namespace SupportedCusp

theorem injective_plane : Injective plane := by
  intro x y h
  have he := congrArg (fun v : Vector 6 ↦ (planeSplit v).1) h
  simpa only [planeSplit_plane] using he

theorem scaled_axis_mem_support (β : Cutoff) (ε z : ℝ) (hz : |z| ≤ 2) :
    ε • sourceDiffeomorph (WhitneyCusp.axis z) ∈ scaledSupport β ε := by
  refine ⟨sourceDiffeomorph (WhitneyCusp.axis z), ⟨WhitneyCusp.axis z, ?_, rfl⟩, rfl⟩
  apply subset_tsupport
  change β.value (WhitneyCusp.axis z) ≠ 0
  rw [β.one _ (by rwa [norm_axis])]
  exact one_ne_zero

end SupportedCusp

namespace ImmersedSource.KinkPatchData

open SupportedCusp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {F : Sphere 3 → M} (P : KinkPatchData F)

def crossingPoint (z : ℝ) : Sphere 3 :=
  shiftedSourceChart P.center (P.scale • sourceDiffeomorph (WhitneyCusp.axis z))

theorem crossingPoint_mem_support (z : ℝ) (hz : |z| ≤ 2) :
    P.crossingPoint z ∈ P.sourceSupport :=
  ⟨_, scaled_axis_mem_support P.cutoff P.scale z hz, rfl⟩

theorem crossingPoint_ne : P.crossingPoint 1 ≠ P.crossingPoint (-1) := by
  intro h
  have he := injective_shiftedSourceChart P.center h
  have he' := congrArg (fun x : Vector 3 ↦ P.scale⁻¹ • x) he
  simp only [inv_smul_smul₀ P.scale_pos.ne'] at he'
  have ha := sourceDiffeomorph.injective he'
  have hc := congrArg (fun x : Vector 3 ↦ x 2) ha
  change (1 : ℝ) = -1 at hc
  norm_num at hc

theorem original_unique_fiber {x : Sphere 3} (hx : x ∈ P.sourcePatch)
    {y : Sphere 3} (he : F y = F x) : y = x := by
  obtain ⟨u, hu, rfl⟩ := hx
  have huΦ := P.plane_source u (ball_subset_closedBall hu)
  obtain ⟨v, huv, hyv⟩ := (P.full_fibers (plane u) huΦ y).mp
    (he.trans (P.plane_formula u huΦ).symm)
  have huv' := injective_plane huv
  exact hyv.trans (congrArg (shiftedSourceChart P.center) huv'.symm)

theorem original_pair_off_patch {x y : Sphere 3} (hne : x ≠ y) (he : F x = F y) :
    x ∉ P.sourcePatch ∧ y ∉ P.sourcePatch := by
  exact ⟨fun hx ↦ hne (P.original_unique_fiber hx he.symm).symm,
    fun hy ↦ hne (P.original_unique_fiber hy he)⟩

theorem insertedMap_source {u : Vector 3} (hu : u ∈ ball (0 : Vector 3) P.radius) :
    P.insertedMap (shiftedSourceChart P.center u) =
      P.chart (scaledMap P.cutoff P.scale 1 u) := by
  rw [P.insertedMap_on (show shiftedSourceChart P.center u ∈ P.sourcePatch from ⟨u, hu, rfl⟩)]
  exact P.localFamily_source 1 u

theorem insertedMap_source_global {u : Vector 3} (hu : plane u ∈ P.chart.source) :
    P.insertedMap (shiftedSourceChart P.center u) =
      P.chart (scaledMap P.cutoff P.scale 1 u) := by
  by_cases hx : shiftedSourceChart P.center u ∈ P.sourcePatch
  · exact (P.insertedMap_on hx).trans (P.localFamily_source 1 u)
  · have hxK : shiftedSourceChart P.center u ∉ P.sourceSupport :=
      fun h ↦ hx (P.sourceSupport_subset h)
    have huK : u ∉ scaledSupport P.cutoff P.scale := fun h ↦ hxK ⟨u, h, rfl⟩
    rw [P.insertedMap_fixed hxK,
      scaledMap_eq_plane_off_support P.cutoff P.scale_pos.ne' 1 huK]
    exact (P.plane_formula u hu).symm

theorem inserted_crossing : P.insertedMap (P.crossingPoint 1) =
    P.insertedMap (P.crossingPoint (-1)) := by
  have hp := P.support_subset (scaled_axis_mem_support P.cutoff P.scale 1 (by norm_num))
  have hm := P.support_subset (scaled_axis_mem_support P.cutoff P.scale (-1) (by norm_num))
  change P.insertedMap (shiftedSourceChart P.center _) =
    P.insertedMap (shiftedSourceChart P.center _)
  rw [P.insertedMap_source hp, P.insertedMap_source hm]
  apply congrArg P.chart
  exact (scaledMap_endpoint_eq_iff P.cutoff P.scale_pos.ne' _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))

end ImmersedSource.KinkPatchData
end Wikipedia.HopfProblem.DegreeCollapse

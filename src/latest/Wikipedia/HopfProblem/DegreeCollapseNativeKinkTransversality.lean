import Wikipedia.HopfProblem.DegreeCollapseKinkInsertionPairs

/-!
# Native self-transversality of the actual inserted immersion

The endpoint has the original full germs at every old pair. At its new
pair, the genuine source-chart derivatives parameterize the two tangent
images, and one common invertible target-chart derivative carries the
explicit model tangent sum to the original native tangent space.
-/

noncomputable section

open Set Function Metric Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource.KinkPatchData

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization SupportedCusp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {F : Sphere 3 → M} (P : KinkPatchData F)

theorem contMDiff_insertedMap (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ F) :
    ContMDiff (𝓡 3) (𝓡 6) ∞ P.insertedMap := by
  intro x
  have h := SourcePatch.contMDiffAt_family P.isOpen_sourcePatch
    P.isCompact_sourceSupport.isClosed P.sourceSupport_subset hf
    (fun _ ht _ hx ↦ P.contMDiffAt_localFamily ht hx) P.localFamily_fixed
    (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) x
  exact h.comp x (contMDiffAt_const.prodMk contMDiffAt_id)

theorem mfderiv_insertedMap_source (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    {u : Vector 3} (hu : u ∈ ball (0 : Vector 3) P.radius) :
    (mfderiv (𝓡 3) (𝓡 6) P.insertedMap (shiftedSourceChart P.center u)).comp
      (mfderiv (𝓡 3) (𝓡 3) (shiftedSourceChart P.center) u) =
    (mfderiv (𝓡 6) (𝓡 6) P.chart (scaledMap P.cutoff P.scale 1 u)).comp
      (fderiv ℝ (scaledMap P.cutoff P.scale 1) u) := by
  let χ := shiftedSourceChart P.center
  let k := scaledMap P.cutoff P.scale (1 : ℝ)
  have he : (P.insertedMap ∘ χ) =ᶠ[𝓝 u] (P.chart ∘ k) := by
    filter_upwards [isOpen_ball.mem_nhds hu] with v hv
    exact P.insertedMap_source hv
  have hg : MDifferentiableAt (𝓡 3) (𝓡 6) P.insertedMap (χ u) :=
    (P.contMDiff_insertedMap hf).mdifferentiableAt (by simp)
  have hχ : MDifferentiableAt (𝓡 3) (𝓡 3) χ u :=
    (contMDiff_shiftedSourceChart P.center).mdifferentiableAt (by simp)
  have hk : MDifferentiableAt (𝓡 3) (𝓡 6) k u :=
    (contDiff_scaledMap_slice P.cutoff P.scale 1).contMDiff.mdifferentiableAt (by simp)
  have hΦ : MDifferentiableAt (𝓡 6) (𝓡 6) P.chart (k u) :=
    P.chart.mdifferentiableAt (by simp)
      (P.map_source (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hu)
  have hd := he.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 6)
  rw [mfderiv_comp u hg hχ, mfderiv_comp u hΦ hk, mfderiv_eq_fderiv] at hd
  exact hd

theorem surjective_inserted_tangent_sum_source (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    {u v : Vector 3} (hu : u ∈ ball (0 : Vector 3) P.radius)
    (hv : v ∈ ball (0 : Vector 3) P.radius) (hne : u ≠ v)
    (he : scaledMap P.cutoff P.scale 1 u = scaledMap P.cutoff P.scale 1 v) :
    Surjective ((mfderiv (𝓡 3) (𝓡 6) P.insertedMap (shiftedSourceChart P.center u)).coprod
      (mfderiv (𝓡 3) (𝓡 6) P.insertedMap (shiftedSourceChart P.center v))) := by
  let χ := shiftedSourceChart P.center
  let k := scaledMap P.cutoff P.scale (1 : ℝ)
  let C : Vector 6 →L[ℝ] Vector 6 := mfderiv (𝓡 6) (𝓡 6) P.chart (k u)
  let L : Vector 3 →L[ℝ] Vector 6 := mfderiv (𝓡 3) (𝓡 6) P.insertedMap (χ u)
  let R : Vector 3 →L[ℝ] Vector 6 := mfderiv (𝓡 3) (𝓡 6) P.insertedMap (χ v)
  let A : Vector 3 →L[ℝ] Vector 3 := mfderiv (𝓡 3) (𝓡 3) χ u
  let B : Vector 3 →L[ℝ] Vector 3 := mfderiv (𝓡 3) (𝓡 3) χ v
  have hdu := P.mfderiv_insertedMap_source hf hu
  have hdv := P.mfderiv_insertedMap_source hf hv
  change L.comp A = C.comp (fderiv ℝ k u) at hdu
  change R.comp B =
      (mfderiv (𝓡 6) (𝓡 6) P.chart (k v) : Vector 6 →L[ℝ] Vector 6).comp
        (fderiv ℝ k v) at hdv
  have he' : k v = k u := he.symm
  rw [he'] at hdv
  have hΦ := P.chart.isLocalDiffeomorphAt (𝓡 6) (𝓡 6) ∞
    (P.map_source (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hu)
  have hCs : Surjective C := (hΦ.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hks := surjective_scaledMap_endpoint_tangent_sum P.cutoff P.scale_pos.ne' u v hne he
  intro w
  obtain ⟨z, hz⟩ := hCs w
  obtain ⟨⟨a, b⟩, hab⟩ := hks z
  refine ⟨(A a, B b), ?_⟩
  have ha := congrArg (fun D : Vector 3 →L[ℝ] Vector 6 ↦ D a) hdu
  have hb := congrArg (fun D : Vector 3 →L[ℝ] Vector 6 ↦ D b) hdv
  change L (A a) = C (fderiv ℝ k u a) at ha
  change R (B b) = C (fderiv ℝ k v b) at hb
  change L (A a) + R (B b) = w
  rw [ha, hb, ← C.map_add]
  exact (congrArg C hab).trans hz

theorem selfTransverse_insertedMap (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (ht : ∀ x y, x ≠ y → F x = F y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) F x).coprod (mfderiv (𝓡 3) (𝓡 6) F y))) :
    ∀ x y, x ≠ y → P.insertedMap x = P.insertedMap y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) P.insertedMap x).coprod
        (mfderiv (𝓡 3) (𝓡 6) P.insertedMap y)) := by
  have hgerm (x : Sphere 3) (hx : x ∉ P.sourceSupport) : P.insertedMap =ᶠ[𝓝 x] F := by
    filter_upwards [P.isCompact_sourceSupport.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact P.insertedMap_fixed hy
  have hnew (u v : Vector 3) (hu : u ∈ scaledSupport P.cutoff P.scale)
      (hv : v ∈ scaledSupport P.cutoff P.scale)
      (hne : shiftedSourceChart P.center u ≠ shiftedSourceChart P.center v)
      (he : P.insertedMap (shiftedSourceChart P.center u) =
        P.insertedMap (shiftedSourceChart P.center v)) := by
    have hu' := P.support_subset hu
    have hv' := P.support_subset hv
    have he' := he
    rw [P.insertedMap_source hu', P.insertedMap_source hv'] at he'
    have hku := P.map_source (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hu'
    have hkv := P.map_source (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hv'
    exact P.surjective_inserted_tangent_sum_source hf hu' hv'
      (fun h ↦ hne (congrArg (shiftedSourceChart P.center) h)) (P.chart.injOn hku hkv he')
  intro x y hne he
  rcases (P.inserted_pair_iff hne).mp he with hold | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hx, hy⟩ := P.original_pair_off_patch hne hold
    have hxK : x ∉ P.sourceSupport := fun h ↦ hx (P.sourceSupport_subset h)
    have hyK : y ∉ P.sourceSupport := fun h ↦ hy (P.sourceSupport_subset h)
    rw [(hgerm x hxK).mfderiv_eq, (hgerm y hyK).mfderiv_eq]
    exact ht x y hne hold
  · exact hnew _ _ (scaled_axis_mem_support P.cutoff P.scale 1 (by norm_num))
      (scaled_axis_mem_support P.cutoff P.scale (-1) (by norm_num)) hne he
  · exact hnew _ _ (scaled_axis_mem_support P.cutoff P.scale (-1) (by norm_num))
      (scaled_axis_mem_support P.cutoff P.scale 1 (by norm_num)) hne he

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource.KinkPatchData

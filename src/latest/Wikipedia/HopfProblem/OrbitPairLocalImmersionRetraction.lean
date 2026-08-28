import Wikipedia.HopfProblem.OrbitPairNativeLocalInjectivity

/-!
# Constructed local smooth left inverses of native immersions

Retain the inverse-function-theorem inverse used to prove local
injectivity. A linear left inverse of the differential, followed by this
actual smooth local inverse, retracts a target neighborhood into the
chosen source neighborhood. The original map is a right inverse there.

This gives exact source coordinates on each individual immersed branch.
It does not identify the left inverses of two branches at their crossing.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeImmersion

open Wikipedia.SmoothSixDPoincare

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem exists_euclidean_source_leftInverse
    {f : E → N} {W : Set E} (hW : IsOpen W)
    (hf : ContMDiffOn 𝓘(ℝ, E) J ∞ f W) {x : E} (hx : x ∈ W)
    (hinj : Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ U : Set E, ∃ O : Set N, IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
      IsOpen O ∧ f x ∈ O ∧ MapsTo f U O ∧ ∃ r : N → E,
      ContMDiffOn J 𝓘(ℝ, E) ∞ r O ∧ MapsTo r O U ∧ ∀ y ∈ U, r (f y) = y := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)
  have hxc : f x ∈ c.source := mem_extChartAt_source (f x)
  let W' : Set E := W ∩ f ⁻¹' c.source
  have hW' : IsOpen W' := hf.continuousOn.isOpen_inter_preimage hW c.open_source
  have hxW' : x ∈ W' := ⟨hx, hxc⟩
  have hc : ContDiffOn ℝ ∞ (c ∘ f) W' :=
    (c.contMDiffOn_toFun.comp (hf.mono inter_subset_left) (fun _ h => h.2)).contDiffOn
  have hdf := (hc.contDiffAt (hW'.mem_nhds hxW')).differentiableAt (by simp)
  have hic : Injective (fderiv ℝ (c ∘ f) x) :=
    (ManifoldImmersion.injective_fderiv_chart_iff c
      ((hf.contMDiffAt (hW.mem_nhds hx)).mdifferentiableAt (by simp)) hxc).mpr hinj
  obtain ⟨L, hL⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hic
  have hderiv : HasFDerivAt (L ∘ (c ∘ f)) (ContinuousLinearMap.id ℝ E) x := by
    convert L.hasFDerivAt.comp x hdf.hasFDerivAt using 1
    ext v
    exact (hL v).symm
  have hcomp : ContDiffOn ℝ ∞ (L ∘ (c ∘ f)) W' := L.contDiff.comp_contDiffOn hc
  have hinv : (fderiv ℝ (L ∘ (c ∘ f)) x).IsInvertible := by
    rw [hderiv.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  obtain ⟨φ, hxφ, hφW', hφeq⟩ :=
    NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn hW' hxW' hcomp hinv
  let O : Set N := c.source ∩ (L ∘ c) ⁻¹' φ.target
  have hLc : ContMDiffOn J 𝓘(ℝ, E) ∞ (L ∘ c) c.source :=
    L.contDiff.contMDiff.comp_contMDiffOn c.contMDiffOn_toFun
  have hO : IsOpen O := hLc.continuousOn.isOpen_inter_preimage c.open_source φ.open_target
  have hmap : MapsTo f φ.source O := by
    intro y hy
    refine ⟨(hφW' hy).2, ?_⟩
    change (L ∘ (c ∘ f)) y ∈ φ.target
    rw [← hφeq]
    exact φ.map_source' hy
  let r : N → E := φ.symm ∘ (L ∘ c)
  have hr : ContMDiffOn J 𝓘(ℝ, E) ∞ r O :=
    φ.contMDiffOn_invFun.comp (hLc.mono inter_subset_left) (fun _ h => h.2)
  refine ⟨φ.source, O, φ.open_source, hxφ, hφW'.trans inter_subset_left,
    hO, hmap hxφ, hmap, r, hr, (fun _ h => φ.map_target' h.2), ?_⟩
  intro y hy
  change φ.symm ((L ∘ (c ∘ f)) y) = y
  rw [← hφeq]
  exact φ.left_inv' hy

theorem exists_native_source_leftInverse
    {f : X → N} {W : Set X} (hW : IsOpen W)
    (hf : ContMDiffOn I J ∞ f W) {x : X} (hx : x ∈ W)
    (hinj : Injective (mfderiv I J f x)) :
    ∃ U : Set X, ∃ O : Set N, IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
      IsOpen O ∧ f x ∈ O ∧ MapsTo f U O ∧ ∃ r : N → X,
      ContMDiffOn J I ∞ r O ∧ MapsTo r O U ∧ ∀ y ∈ U, r (f y) = y := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := I) x
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c x ∈ c.target := c.map_source' hxc
  have hleft : c.symm (c x) = x := c.left_inv' hxc
  let W' : Set E := c.target ∩ c.symm ⁻¹' W
  have hW' : IsOpen W' := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hW
  have hxW' : c x ∈ W' := by
    refine ⟨hcx, ?_⟩
    change c.symm (c x) ∈ W
    rw [hleft]
    exact hx
  have hcW' : ContMDiffOn 𝓘(ℝ, E) J ∞ (f ∘ c.symm) W' :=
    hf.comp (c.contMDiffOn_invFun.mono inter_subset_left) (fun _ h => h.2)
  have hfs : MDifferentiableAt I J f (c.symm (c x)) :=
    (hf.contMDiffAt (hW.mem_nhds hxW'.2)).mdifferentiableAt (by simp)
  have hi : Injective (mfderiv 𝓘(ℝ, E) J (f ∘ c.symm) (c x)) := by
    apply (injective_sourceChart_iff c hcx hfs).mpr
    rw [hleft]
    exact hinj
  obtain ⟨V, O, hV, hxV, hVW', hO, hfxO, hmap, r, hr, hrmap, hright⟩ :=
    exists_euclidean_source_leftInverse hW' hcW' hxW' hi
  let U : Set X := c.symm '' V
  have hU : IsOpen U := c.toOpenPartialHomeomorph.isOpen_image_symm_of_subset_target
    hV (hVW'.trans inter_subset_left)
  have hxU : x ∈ U := ⟨c x, hxV, hleft⟩
  have hUW : U ⊆ W := by
    rintro y ⟨v, hv, rfl⟩
    exact (hVW' hv).2
  have hfrO : f x ∈ O := by
    simpa only [Function.comp_apply, hleft] using hfxO
  refine ⟨U, O, hU, hxU, hUW, hO, hfrO, ?_, c.symm ∘ r, ?_, ?_, ?_⟩
  · rintro y ⟨v, hv, rfl⟩
    exact hmap hv
  · exact c.contMDiffOn_invFun.comp hr (fun z hz => (hVW' (hrmap hz)).1)
  · intro z hz
    exact ⟨r z, hrmap hz, rfl⟩
  · rintro y ⟨v, hv, rfl⟩
    exact congrArg c.symm (hright v hv)

end Wikipedia.HopfProblem.OrbitPair.NativeImmersion

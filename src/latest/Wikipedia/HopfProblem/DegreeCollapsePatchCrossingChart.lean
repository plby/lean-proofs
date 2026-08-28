import Wikipedia.HopfProblem.DegreeCollapseEmbeddedPatchCoordinates
import Wikipedia.SmoothSixDPoincare.CornerStripData
import Wikipedia.SmoothSixDPoincare.TransverseCornerPatch

/-!
# Native crossing charts for two embedded branches of one immersion

Each original map need only be embedded on its specified source patch.
The constructed target chart detects membership in both entire patch
images and retains the actual prescribed source parametrizations. Its
planar restriction gives the shared native corner map.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare

variable {E M D Z N P A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace N] [ChartedSpace D N]
  [TopologicalSpace P] [ChartedSpace Z P]

theorem exists_patch_crossingChart_of_parametrizations {F : N → M} {G : P → M}
    {K : Set N} {L : Set P}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding (fun x : K => F x)) (hembG : IsEmbedding (fun y : L => G y))
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hcK : c.target ⊆ K) (hdL : d.target ⊆ L)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source)
    (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ a : ℝ, 0 < a ∧ ∃ Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, E) (A × B) M ∞,
      closedBall (0 : A) a ×ˢ closedBall (0 : B) a ⊆ Φ.source ∧
      Φ.source ⊆ c.source ×ˢ d.source ∧ Φ.target ⊆ O ∧ Φ (0, 0) = F (c 0) ∧
      (∀ u, (u, 0) ∈ Φ.source → Φ (u, 0) = F (c u)) ∧
      (∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (d v)) ∧
      (∀ q ∈ Φ.source, (Φ q ∈ F '' K ↔ q.2 = 0) ∧ (Φ q ∈ G '' L ↔ q.1 = 0)) := by
  have hf : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ (F ∘ c) c.source :=
    hF.comp_contMDiffOn c.contMDiffOn_toFun
  have hg : ContMDiffOn 𝓘(ℝ, B) 𝓘(ℝ, E) ∞ (G ∘ d) d.source :=
    hG.comp_contMDiffOn d.contMDiffOn_toFun
  have hembf := isEmbedding_patch_coordinates hembF c hcK
  have hembg := isEmbedding_patch_coordinates hembG d hdL
  have hdf := mfderiv_comp (I := 𝓘(ℝ, A)) (I' := 𝓘(ℝ, D)) (I'' := 𝓘(ℝ, E)) 0
    (hF.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) hc0)
  have hdg := mfderiv_comp (I := 𝓘(ℝ, B)) (I' := 𝓘(ℝ, Z)) (I'' := 𝓘(ℝ, E)) 0
    (hG.mdifferentiableAt (by simp)) (d.mdifferentiableAt (by simp) hd0)
  have ht' : Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (F ∘ c) 0).coprod
      (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) (G ∘ d) 0)) := by
    rw [hdf, hdg]
    intro w
    obtain ⟨⟨u, v⟩, huv⟩ := ht w
    obtain ⟨a, ha⟩ := (PartialChart.bijective_mfderiv c hc0).2 u
    obtain ⟨b, hb⟩ := (PartialChart.bijective_mfderiv d hd0).2 v
    refine ⟨(a, b), ?_⟩
    let DF : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)
    let DG : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0)
    let C : A →L[ℝ] D := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, D) c 0
    let Q : B →L[ℝ] Z := mfderiv 𝓘(ℝ, B) 𝓘(ℝ, Z) d 0
    change DF (C a) + DG (Q b) = w
    change C a = u at ha
    change Q b = v at hb
    rw [ha, hb]
    exact huv
  obtain ⟨U, hU, hFU, hwindowF⟩ := exists_patch_coordinate_window hembF c hcK
  obtain ⟨V, hV, hGV, hwindowG⟩ := exists_patch_coordinate_window hembG d hdL
  have hxV : F (c 0) ∈ V := by rw [← hxy]; exact hGV hd0
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hleft, hright, himages⟩ :=
    exists_clean_simultaneous_sheetChart c.open_source d.open_source hc0 hd0 hf hg
      hxy hembf hembg hdim ht' (hO.inter (hU.inter hV)) ⟨hxO, hFU hc0, hxV⟩
  refine ⟨a, ha, Φ, hprod, hsource, fun _ hy => (htarget hy).1,
    hleft 0 (hprod ⟨mem_closedBall_self ha.le, mem_closedBall_self ha.le⟩),
    hleft, hright, ?_⟩
  intro q hq
  have hqUV := (htarget (Φ.map_source' hq)).2
  exact ⟨(hwindowF (Φ q) hqUV.1).trans (himages q hq).1,
    (hwindowG (Φ q) hqUV.2).trans (himages q hq).2⟩

theorem exists_clean_corner_of_patch_parametrizations {F : N → M} {G : P → M}
    {K : Set N} {L : Set P}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding (fun x : K => F x)) (hembG : IsEmbedding (fun y : L => G y))
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hcK : c.target ⊆ K) (hdL : d.target ⊆ L)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source)
    (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {u : A} {v : B} (hu : u ≠ 0) (hv : v ≠ 0)
    {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ k : CleanCornerPatch (E := E) (F '' K) (G '' L)
      (fun t => F (c (t • u))) (fun t => G (d (t • v))),
      MapsTo k.map k.domain O := by
  obtain ⟨a, ha, Φ, hprod, _, htarget, _, hleft, hright, himages⟩ :=
    exists_patch_crossingChart_of_parametrizations hF hG hembF hembG c d hcK hdL
      hc0 hd0 hxy hdim ht hO hxO
  let L₀ := TransverseCoordinates.cornerLinear u v
  let W := L₀ ⁻¹' Φ.source
  let k := TransverseCoordinates.cornerMap Φ u v
  have h0W : (0 : ℝ × ℝ) ∈ W := by
    change L₀ 0 ∈ Φ.source
    rw [map_zero]
    exact hprod ⟨mem_closedBall_self ha.le, mem_closedBall_self ha.le⟩
  refine ⟨{
    domain := W
    open_domain := Φ.open_source.preimage L₀.continuous
    contains_zero := h0W
    map := k
    smooth := TransverseCoordinates.contMDiffOn_cornerMap Φ u v
    injective := TransverseCoordinates.injOn_cornerMap Φ hu hv
    derivative_injective := fun _ hp => TransverseCoordinates.injective_mfderiv_cornerMap Φ hu hv hp
    sheets := ?_
    axis_first := ?_
    axis_second := ?_ }, ?_⟩
  · intro p hp
    simpa only [L₀, k, TransverseCoordinates.cornerMap, comp_apply,
      TransverseCoordinates.cornerLinear_apply, smul_eq_zero, hu, hv, or_false] using
        himages (L₀ p) hp
  · intro s hs
    have haxis : (s • u, 0) ∈ Φ.source := by
      change L₀ (s, 0) ∈ Φ.source at hs
      simpa only [L₀, TransverseCoordinates.cornerLinear_apply, zero_smul] using hs
    simpa only [k, TransverseCoordinates.cornerMap, comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hleft (s • u) haxis
  · intro t ht
    have haxis : (0, t • v) ∈ Φ.source := by
      change L₀ (0, t) ∈ Φ.source at ht
      simpa only [L₀, TransverseCoordinates.cornerLinear_apply, zero_smul] using ht
    simpa only [k, TransverseCoordinates.cornerMap, comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hright (t • v) haxis
  · intro p hp
    exact htarget (Φ.map_source' hp)

variable [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
  [IsManifold 𝓘(ℝ, D) ∞ N] [IsManifold 𝓘(ℝ, Z) ∞ P]

theorem exists_clean_corner_of_source_patches {F : N → M} {G : P → M}
    {K U : Set N} {L V : Set P}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding (fun x : K => F x)) (hembG : IsEmbedding (fun y : L => G y))
    (hU : IsOpen U) (hV : IsOpen V) (hUK : U ⊆ K) (hVL : V ⊆ L)
    {x : N} {y : P} (hx : x ∈ U) (hy : y ∈ V) (hxy : G y = F x)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {u : D} {v : Z} (hu : u ≠ 0) (hv : v ≠ 0)
    {O : Set M} (hO : IsOpen O) (hxO : F x ∈ O) :
    ∃ k : CleanCornerPatch (E := E) (F '' K) (G '' L)
      (fun t => F (NativeParametrization.centered (D := D) x (t • u)))
      (fun t => G (NativeParametrization.centered (D := Z) y (t • v))),
      MapsTo k.map k.domain O := by
  let c := PartialChart.restrictTarget (NativeParametrization.centered (D := D) x) hU
  let d := PartialChart.restrictTarget (NativeParametrization.centered (D := Z) y) hV
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hdy : d 0 = y := NativeParametrization.centered_zero y
  have hc0 : (0 : D) ∈ c.source :=
    ⟨NativeParametrization.zero_mem_centered_source x, by change c 0 ∈ U; rwa [hcx]⟩
  have hd0 : (0 : Z) ∈ d.source :=
    ⟨NativeParametrization.zero_mem_centered_source y, by change d 0 ∈ V; rwa [hdy]⟩
  apply exists_clean_corner_of_patch_parametrizations hF hG hembF hembG c d
    (fun _ hz => hUK hz.2) (fun _ hz => hVL hz.2) hc0 hd0
      (by rw [hcx, hdy]; exact hxy) hdim
      (by rw [hcx, hdy]; exact ht) hu hv hO (by rwa [hcx])

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

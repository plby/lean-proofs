import Wikipedia.HopfProblem.DegreeCollapseSheetCoordinateDifferentials

/-!
# Transversality of the original native sheets during tube passage

The full-image recognition equations force the two coordinate differentials
onto complementary planes. Immersion makes their plane coordinates
surjective. The positive time derivative supplies the missing longitudinal
direction. All derivatives below concern the original source manifolds.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {U V E HU HV H M X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace HU] [TopologicalSpace HV] [TopologicalSpace H]
  {I : ModelWithCorners ℝ U HU} {I' : ModelWithCorners ℝ V HV}
  {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace X] [ChartedSpace HU X]
  [TopologicalSpace Y] [ChartedSpace HV Y]
  {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) J (ℝ × (U × V)) M ∞}

theorem LongitudinalTubeMotion.whole_sheet_transverse
    (A : LongitudinalTubeMotion Φ) {f : X → M} {g : Y → M} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hfi : Injective (mfderiv I J f x)) (hgi : Injective (mfderiv I' J g y))
    (hrecf : ∀ z ∈ Φ.source, Φ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrecg : ∀ z ∈ Φ.source, Φ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0)
    (hx : Φ 0 = f x) (hy : Φ (1, 0) = g y)
    (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) :
    NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' J
      (fun p : ℝ × X => A.family (p.1, f p.2)) g (A.time, x) y := by
  let W := ℝ × (U × V)
  let a : X → W := Φ.symm ∘ f
  let b : Y → W := Φ.symm ∘ g
  let P : W →L[ℝ] U := (ContinuousLinearMap.fst ℝ U V).comp
    (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let Q : U →L[ℝ] W := (0 : U →L[ℝ] ℝ).prod
    ((ContinuousLinearMap.id ℝ U).prod (0 : U →L[ℝ] V))
  let R : W →L[ℝ] V := (ContinuousLinearMap.snd ℝ U V).comp
    (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let S : V →L[ℝ] W := (0 : V →L[ℝ] ℝ).prod
    ((0 : V →L[ℝ] U).prod (ContinuousLinearMap.id ℝ V))
  have h1 : ((1 : ℝ), (0 : U × V)) ∈ Φ.source := by
    have hh := A.model_source A.time ((0 : ℝ), (0 : U × V)) h0
    rw [A.model_axis, A.time_value] at hh
    exact hh
  have hfx : f x ∈ Φ.target := hx ▸ Φ.map_source h0
  have hgy : g y ∈ Φ.target := hy ▸ Φ.map_source h1
  have ha : MDifferentiableAt I 𝓘(ℝ, W) a x :=
    (Φ.symm.mdifferentiableAt (by simp) hfx).comp x hf
  have hb : MDifferentiableAt I' 𝓘(ℝ, W) b y :=
    (Φ.symm.mdifferentiableAt (by simp) hgy).comp y hg
  have hai : Injective (mfderiv I 𝓘(ℝ, W) a x) := by
    rw [mfderiv_comp x (Φ.symm.mdifferentiableAt (by simp) hfx) hf]
    exact (PartialChart.bijective_mfderiv Φ.symm hfx).injective.comp hfi
  have hbi : Injective (mfderiv I' 𝓘(ℝ, W) b y) := by
    rw [mfderiv_comp y (Φ.symm.mdifferentiableAt (by simp) hgy) hg]
    exact (PartialChart.bijective_mfderiv Φ.symm hgy).injective.comp hgi
  have ha0 : a x = 0 := (congrArg Φ.symm hx).symm.trans (Φ.left_inv h0)
  have hb1 : b y = (1, 0) := (congrArg Φ.symm hy).symm.trans (Φ.left_inv h1)
  have hfn : ∀ᶠ q in 𝓝 x, f q ∈ Φ.target :=
    hf.continuousAt.eventually (Φ.open_target.mem_nhds hfx)
  have hgn : ∀ᶠ q in 𝓝 y, g q ∈ Φ.target :=
    hg.continuousAt.eventually (Φ.open_target.mem_nhds hgy)
  have hca : ∀ᶠ q in 𝓝 x, (a q).1 = 0 ∧ (a q).2.2 = 0 := by
    filter_upwards [hfn] with q hq
    exact (hrecf (a q) (Φ.map_target hq)).mp ⟨q, (Φ.right_inv hq).symm⟩
  have hcb : ∀ᶠ q in 𝓝 y, (b q).1 = 1 ∧ (b q).2.1 = 0 := by
    filter_upwards [hgn] with q hq
    exact (hrecg (b q) (Φ.map_target hq)).mp ⟨q, (Φ.right_inv hq).symm⟩
  have hagerm : a =ᶠ[𝓝 x] fun q => Q (P (a q)) + (0 : W) := by
    filter_upwards [hca] with q hq
    change a q = (0, ((a q).2.1, 0)) + (0 : W)
    rw [add_zero]
    exact Prod.ext hq.1 (Prod.ext rfl hq.2)
  have hbgerm : b =ᶠ[𝓝 y] fun q => S (R (b q)) + ((1 : ℝ), (0 : U × V)) := by
    filter_upwards [hcb] with q hq
    change b q = (0, (0, (b q).2.2)) + ((1 : ℝ), (0 : U × V))
    apply Prod.ext
    · change (b q).1 = 0 + 1
      simpa only [zero_add] using hq.1
    · apply Prod.ext
      · change (b q).2.1 = 0 + 0
        simpa only [zero_add] using hq.2
      · change (b q).2.2 = (b q).2.2 + 0
        exact (add_zero _).symm
  let α : X → U := P ∘ a
  let β : Y → V := R ∘ b
  have hα : MDifferentiableAt I 𝓘(ℝ, U) α x :=
    P.differentiableAt.mdifferentiableAt.comp x ha
  have hβ : MDifferentiableAt I' 𝓘(ℝ, V) β y :=
    R.differentiableAt.mdifferentiableAt.comp y hb
  have hαs := surjective_sheet_coordinate_mfderiv P Q 0 ha hai hagerm
  have hβs := surjective_sheet_coordinate_mfderiv R S (1, 0) hb hbi hbgerm
  let η : ℝ → ℝ := fun t => Real.smoothTransition t * A.destination
  have hη : HasDerivAt η (deriv Real.smoothTransition A.time * A.destination) A.time :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable
      (by simp) A.time).hasDerivAt.mul_const _
  let T : ℝ × X → W := fun p => (η p.1, (α p.2, 0))
  let B : Y → W := fun q => (1, (0, β q))
  have hT : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, W) T (A.time, x) :=
    (hη.differentiableAt.mdifferentiableAt.comp (A.time, x) mdifferentiableAt_fst).prodMk_space
      ((hα.comp (A.time, x) mdifferentiableAt_snd).prodMk_space mdifferentiableAt_const)
  have hB : MDifferentiableAt I' 𝓘(ℝ, W) B y :=
    mdifferentiableAt_const.prodMk_space (mdifferentiableAt_const.prodMk_space hβ)
  have hT0 : T (A.time, x) = (1, 0) := by
    change (η A.time, (P (a x), (0 : V))) = (1, 0)
    rw [ha0, map_zero]
    exact Prod.ext A.time_value rfl
  have hB0 : B y = (1, 0) := by
    change ((1 : ℝ), ((0 : U), R (b y))) = (1, 0)
    rw [hb1]
    rfl
  have hmodel : NativeTransversality.At (𝓘(ℝ, ℝ).prod I) I' 𝓘(ℝ, W)
      T B (A.time, x) y :=
    native_coordinate_plane_trace_transverse hα hβ hαs hβs hη A.time_rate.ne'
  have hnative := (TransverseGerms.native_transversality_partial_diffeomorph_iff Φ
    hT hB (hB0.trans hT0.symm) (hT0 ▸ h1)).mp hmodel
  have hq : Tendsto (fun p : ℝ × X => (p.1, a p.2))
      (𝓝 (A.time, x)) (𝓝 (A.time, (0 : W))) := by
    have hcont : ContinuousAt (fun p : ℝ × X => (p.1, a p.2)) (A.time, x) :=
      continuousAt_fst.prodMk
        (ContinuousAt.comp (g := a) (f := fun p : ℝ × X => p.2)
          ha.continuousAt continuousAt_snd)
    simpa only [ha0] using
      hcont.tendsto
  have hFgerm : (fun p : ℝ × X => A.family (p.1, f p.2)) =ᶠ[𝓝 (A.time, x)]
      (Φ ∘ T) := by
    filter_upwards [hq.eventually (A.native_germ h0 A.time),
      continuous_snd.continuousAt.eventually hfn,
      continuous_snd.continuousAt.eventually hca] with p hmove hp hplane
    have hpoint : Φ (a p.2) = f p.2 := Φ.right_inv hp
    calc
      A.family (p.1, f p.2) = A.family (p.1, Φ (a p.2)) :=
        congrArg (fun z => A.family (p.1, z)) hpoint.symm
      _ = Φ ((a p.2).1 + η p.1, (a p.2).2) := hmove
      _ = (Φ ∘ T) p := by
        apply congrArg Φ
        change ((a p.2).1 + η p.1, (a p.2).2) = (η p.1, ((a p.2).2.1, 0))
        rw [hplane.1, zero_add]
        exact Prod.ext rfl (Prod.ext rfl hplane.2)
  have hGgerm : g =ᶠ[𝓝 y] (Φ ∘ B) := by
    filter_upwards [hgn, hcb] with q hq hplane
    calc
      g q = Φ (b q) := (Φ.right_inv hq).symm
      _ = (Φ ∘ B) q := congrArg Φ (Prod.ext hplane.1 (Prod.ext hplane.2 rfl))
  intro _
  rw [hFgerm.mfderiv_eq, hGgerm.mfderiv_eq]
  exact hnative (congrArg Φ (hB0.trans hT0.symm))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

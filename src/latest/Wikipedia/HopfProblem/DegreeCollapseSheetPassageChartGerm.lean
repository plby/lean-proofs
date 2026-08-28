import Wikipedia.HopfProblem.DegreeCollapseSheetPassageNormalChoice

/-!
# The actual sheet trace in the two retained endpoint charts

The first chart determines the original sheet parameter. The second
chart sees precisely the chosen normal automorphism; the auxiliary
orientation correction acts on the zero belt-tangent coordinate and
therefore disappears from this actual joint germ.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {U V E M X : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace X]

theorem LongitudinalTubeMotion.sheet_trace_germ_of_endpoint_germs
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞}
    (A : LongitudinalTubeMotion Φ)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞)
    (C : U ≃L[ℝ] U) (R : V ≃L[ℝ] V)
    {f : X → M} {x : X} (hf : ContinuousAt f x)
    (h0 : (0 : ℝ × (U × V)) ∈ Φ.source)
    (hΦ₀ : (0 : ℝ × (U × V)) ∈ Φ₀.source) (hx : Φ₀ 0 = f x)
    (hrec : ∀ z ∈ Φ₀.source, Φ₀ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hleft : (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 (0 : ℝ × (U × V))] Φ₀)
    (hright : (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 ((1 : ℝ), (0 : U × V))]
      linearTransverseChart (C.prodCongr R) Φ₁) :
    (fun p : ℝ × X => A.family (p.1, f p.2)) =ᶠ[𝓝 (A.time, x)]
      fun p => Φ₁ (Real.smoothTransition p.1 * A.destination,
        (C (Φ₀.symm (f p.2)).2.1, 0)) := by
  let W := ℝ × (U × V)
  let a : X → W := Φ₀.symm ∘ f
  have hfx : f x ∈ Φ₀.target := hx ▸ Φ₀.map_source hΦ₀
  have ha : ContinuousAt a x :=
    (Φ₀.symm.contMDiffOn_toFun.continuousOn.continuousAt
      (Φ₀.open_target.mem_nhds hfx)).comp hf
  have ha0 : a x = 0 := (congrArg Φ₀.symm hx).symm.trans (Φ₀.left_inv hΦ₀)
  have hat : Tendsto a (𝓝 x) (𝓝 (0 : W)) := by simpa only [ha0] using ha.tendsto
  have hfn : ∀ᶠ q in 𝓝 x, f q ∈ Φ₀.target :=
    hf.eventually (Φ₀.open_target.mem_nhds hfx)
  have hplane : ∀ᶠ q in 𝓝 x, (a q).1 = 0 ∧ (a q).2.2 = 0 := by
    filter_upwards [hfn] with q hq
    exact (hrec (a q) (Φ₀.map_target hq)).mp ⟨q, (Φ₀.right_inv hq).symm⟩
  have hat' : Tendsto (fun p : ℝ × X => a p.2)
      (𝓝 (A.time, x)) (𝓝 (0 : W)) := hat.comp continuous_snd.continuousAt
  have hpair : Tendsto (fun p : ℝ × X => (p.1, a p.2))
      (𝓝 (A.time, x)) (𝓝 (A.time, (0 : W))) :=
    continuous_fst.continuousAt.prodMk_nhds hat'
  let z : ℝ × X → W := fun p =>
    (Real.smoothTransition p.1 * A.destination, ((a p.2).2.1, 0))
  have hap : ContinuousAt (fun p : ℝ × X => a p.2) (A.time, x) :=
    ContinuousAt.comp (g := a) (f := fun p : ℝ × X => p.2) ha continuousAt_snd
  have hz : ContinuousAt z (A.time, x) :=
    ((Real.smoothTransition.continuous.continuousAt.comp continuousAt_fst).mul
      continuousAt_const).prodMk
      (hap.snd.fst.prodMk continuousAt_const)
  have hz0 : z (A.time, x) = (1, 0) := by
    simp only [z, A.time_value, ha0, Prod.fst_zero, Prod.snd_zero]
    rfl
  have hzt : Tendsto z (𝓝 (A.time, x)) (𝓝 ((1 : ℝ), (0 : U × V))) := by
    simpa only [hz0] using hz.tendsto
  filter_upwards [hpair.eventually (A.native_germ h0 A.time),
    hat'.eventually hleft, continuous_snd.continuousAt.eventually hfn,
    continuous_snd.continuousAt.eventually hplane, hzt.eventually hright]
    with p hm hl hf' hp hr
  have hpoint : Φ (a p.2) = f p.2 := hl.trans (Φ₀.right_inv hf')
  calc
    A.family (p.1, f p.2) = A.family (p.1, Φ (a p.2)) :=
      congrArg (fun y => A.family (p.1, y)) hpoint.symm
    _ = Φ ((a p.2).1 + Real.smoothTransition p.1 * A.destination, (a p.2).2) := hm
    _ = Φ (z p) := by
      apply congrArg Φ
      rw [hp.1, zero_add]
      exact Prod.ext rfl (Prod.ext rfl hp.2)
    _ = Φ₁ (Real.smoothTransition p.1 * A.destination,
        (C (Φ₀.symm (f p.2)).2.1, 0)) := by
      change Φ (z p) = Φ₁ (Real.smoothTransition p.1 * A.destination, (C (a p.2).2.1, 0))
      rw [hr]
      change Φ₁ (Real.smoothTransition p.1 * A.destination,
        (C (a p.2).2.1, R 0)) = _
      rw [map_zero]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

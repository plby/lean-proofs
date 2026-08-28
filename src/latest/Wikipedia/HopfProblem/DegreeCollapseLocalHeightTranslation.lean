import Wikipedia.HopfProblem.DegreeCollapsePositiveBandNormalization
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Exact height translation from a local unit-speed identity

The field outside the regular band may have arbitrary descending speed.
Only the derivative on an open neighborhood of the band is used. Local
constancy and connectedness extend the affine identity through both closed
endpoints without assuming that a trajectory stays in the band.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

/-- An affine height germ follows solely from the unit-speed identity near its current value. -/
theorem local_affine_height_germ {γ : ℝ → ℝ} (hγ : Continuous γ)
    {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ t, γ t ∈ U → HasDerivAt γ (-1) t) {t : ℝ} (ht : γ t ∈ U) :
    ∀ᶠ s in 𝓝 t, γ s + s = γ t + t := by
  obtain ⟨l, u, htu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp ((hU.preimage hγ).mem_nhds ht)
  have hder (s : ℝ) (hs : s ∈ Ioo l u) : HasDerivAt (fun r => γ r + r) 0 s := by
    convert! (hd s (hsub hs)).add (hasDerivAt_id s) using 1
    norm_num
  filter_upwards [Ioo_mem_nhds htu.1 htu.2] with s hs
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun r hr => (hder r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hder r hr).deriv) hs htu

/-- Local descending unit speed implies exact translation throughout any
closed band contained in that open unit-speed region. -/
theorem scalar_local_height_translation {γ : ℝ → ℝ} (hγ : Continuous γ)
    {U : Set ℝ} (hU : IsOpen U) {a b c t : ℝ} (hIU : Icc a b ⊆ U)
    (hd : ∀ s, γ s ∈ U → HasDerivAt γ (-1) s) (hzero : γ 0 = c)
    (hc : c ∈ Icc a b) (ht : c - t ∈ Icc a b) : γ t = c - t := by
  let J := Icc (c - b) (c - a)
  let _ : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let P : J → Prop := fun s => γ s = c - s
  have hloc : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro s
    by_cases hs : P s
    · have hsU : γ s ∈ U := by
        rw [show γ s = c - s from hs]
        exact hIU ⟨by linarith [s.property.2], by linarith [s.property.1]⟩
      have heq := local_affine_height_germ hγ hU hd hsU
      filter_upwards [continuous_subtype_val.continuousAt heq] with r hr
      apply propext
      constructor
      · intro _
        exact hs
      · intro _
        change γ r = c - r
        change γ s = c - s at hs
        change γ r + r = γ s + s at hr
        linarith
    · have hn : (s : ℝ) ∈ {r : ℝ | γ r = c - r}ᶜ := hs
      have hopen : IsOpen {r : ℝ | γ r = c - r}ᶜ :=
        (isClosed_eq hγ ((continuous_const (y := c)).sub continuous_id)).isOpen_compl
      filter_upwards [continuous_subtype_val.continuousAt (hopen.mem_nhds hn)] with r hr
      exact propext ⟨fun h => (hr h).elim, fun h => (hs h).elim⟩
  let s₀ : J := ⟨0, ⟨by linarith [hc.2], by linarith [hc.1]⟩⟩
  let s₁ : J := ⟨t, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩
  have hinit : P s₀ := by simpa only [P, s₀, sub_zero] using hzero
  have heq : P s₀ = P s₁ := hloc.apply_eq_of_preconnectedSpace s₀ s₁
  have hfinish : P s₁ := heq ▸ hinit
  exact hfinish

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The actual complete native flow has exact affine height wherever both
endpoint heights lie in the normalized band. No prior stay-in-band assumption is used. -/
theorem native_local_height_translation {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {U : Set ℝ} (hU : IsOpen U) {a b : ℝ} (hIU : Icc a b ⊆ U)
    (hspeed : ∀ x, f x ∈ U → mvfderiv 𝓘(ℝ, E) f x (V x) = -1)
    (x : M) (t : ℝ) (hx : f x ∈ Icc a b) (ht : f x - t ∈ Icc a b) :
    f (F t x) = f x - t := by
  apply scalar_local_height_translation
    (hf.continuous.comp (F.continuous continuous_id continuous_const)) hU hIU
    (γ := fun s => f (F s x)) ?_ (by rw [F.map_zero_apply]) hx ht
  intro s hs
  have hd := FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) s
  rw [hspeed (F s x) hs] at hd
  exact hd

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

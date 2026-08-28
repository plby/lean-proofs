import Wikipedia.HopfProblem.DegreeCollapsePositiveClock
import Wikipedia.HopfProblem.DegreeCollapsePerturbedNoReturn
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Positive rescaling preserves actual native flow orbits

For a positive continuous rescaling on a compact manifold, the explicit
integral clock is complete. Its inverse reparametrizes every original
integral curve into a curve of the rescaled field. Native uniqueness
identifies it with the actual new flow, preserving whole orbits and both
infinite-time endpoint limits.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

omit [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] in
/-- The native chain rule gives the exact field after an arbitrary differentiable clock change. -/
theorem native_curve_positive_reparametrization {ρ : M → ℝ} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ V) {c : ℝ → ℝ}
    (hc : ∀ t, HasDerivAt c (ρ (γ (c t))) t) :
    IsMIntegralCurve (γ ∘ c) (fun x => ρ x • V x) := by
  intro t
  have hh := (hγ (c t)).comp t (hc t).hasFDerivAt.hasMFDerivAt
  have he : (1 : ℝ →L[ℝ] ℝ).smulRight (ρ (γ (c t)) • V (γ (c t))) =
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ (c t)))).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (ρ (γ (c t)))) := by
    ext
    simp [smul_smul, mul_comm]
  change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ ∘ c) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (γ (c t)) • V (γ (c t))))
  rw [he]
  exact hh

variable [CompactSpace M]

/-- The original complete flow and the positively rescaled complete flow
are related by an actual increasing clock on the whole real line. -/
theorem exists_native_flow_time_change {ρ : M → ℝ} (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) (fun y => ρ y • V y)) (x : M) :
    ∃ c : ℝ ≃o ℝ, c 0 = 0 ∧
      (∀ t, c t = ∫ s in (0 : ℝ)..t, (ρ (F s x))⁻¹) ∧
      (∀ t, HasDerivAt c.symm (ρ (F (c.symm t) x)) t) ∧
      ∀ t, G t x = F (c.symm t) x := by
  obtain ⟨R, hR⟩ := (isCompact_univ.image hρ).bddAbove
  have hbound (y : M) : ρ y ≤ R := hR ⟨y, mem_univ _, rfl⟩
  have hRpos : 0 < R := (hρpos x).trans_le (hbound x)
  have ha : Continuous (fun t => (ρ (F t x))⁻¹) :=
    (hρ.comp (F.continuous continuous_id continuous_const)).inv₀ (fun t => (hρpos _).ne')
  have hlower (t : ℝ) : R⁻¹ ≤ (ρ (F t x))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (hρpos (F t x)) (hbound (F t x))
  obtain ⟨c, hc0, hcint, -, hcinv⟩ :=
    exists_positive_integral_clock ha (inv_pos.mpr hRpos) hlower
  have hcinv' (t : ℝ) : HasDerivAt c.symm (ρ (F (c.symm t) x)) t := by
    simpa only [inv_inv] using hcinv t
  have hcurve := native_curve_positive_reparametrization (hF x) hcinv'
  have hc0' : c.symm 0 = 0 := by
    apply c.injective
    rw [c.apply_symm_apply]
    exact hc0.symm
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hW (hG x) hcurve
    (t₀ := 0) (by simp only [comp_apply, hc0', F.map_zero_apply, G.map_zero_apply])
  exact ⟨c, hc0, hcint, hcinv', fun t => congrFun heq t⟩

/-- Increasing complete time changes preserve the entire orbit and its two endpoint limits. -/
theorem native_flow_time_change_orbits {ρ : M → ℝ} (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F G : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hG : ∀ x, IsMIntegralCurve (fun t => G t x) (fun y => ρ y • V y)) (x : M) :
    range (fun t => G t x) = range (fun t => F t x) ∧
      (∀ p, Tendsto (fun t => G t x) atTop (𝓝 p) ↔ Tendsto (fun t => F t x) atTop (𝓝 p)) ∧
      ∀ p, Tendsto (fun t => G t x) atBot (𝓝 p) ↔ Tendsto (fun t => F t x) atBot (𝓝 p) := by
  obtain ⟨c, -, -, -, heq⟩ := exists_native_flow_time_change hρ hρpos hW F G hF hG x
  have heq' (t : ℝ) : F t x = G (c t) x := by rw [heq, c.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨c.symm t, (heq t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨c t, (heq' t).symm⟩
  · intro p
    constructor
    · intro h
      exact (h.comp c.tendsto_atTop).congr (fun t => (heq' t).symm)
    · intro h
      exact (h.comp c.symm.tendsto_atTop).congr (fun t => (heq t).symm)
  · intro p
    constructor
    · intro h
      exact (h.comp c.tendsto_atBot).congr (fun t => (heq' t).symm)
    · intro h
      exact (h.comp c.symm.tendsto_atBot).congr (fun t => (heq t).symm)

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

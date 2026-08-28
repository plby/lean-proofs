import Wikipedia.HopfProblem.DegreeCollapseCubicFieldResidence
import Wikipedia.SmoothSixDPoincare.PartialChartIntegralCurve

/-!
# Compact residence in the original native chart

The ordinary coordinate equation is derived from the actual manifold
integral-curve equation, allowing the two model spaces to differ. The compact
Lyapunov bound therefore applies to native trajectories without a global
coordinate flow or any extension of the inverse chart across its boundary.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {D E M : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The native pullback equation becomes the ordinary field equation in coordinates. -/
theorem hasDerivAt_partialChart_integralCurve
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, D) M D ∞) (W : D → D)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ V) {t : ℝ} (ht : γ t ∈ e.source)
    (hV : V (γ t) = FlowConstruction.partialChartField e W (γ t)) :
    HasDerivAt (e ∘ γ) (W (e (γ t))) t := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, D) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp),
      e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hinv := he.comp_symm_deriv (e'.map_source ht)
  rw [e'.left_inv ht] at hinv
  have hd := (he.mdifferentiableAt ht).hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D) e (γ t)
    ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
    (NormedSpace.fromTangentSpace t r) •
      (NormedSpace.fromTangentSpace (e (γ t))).symm (W (e (γ t)))
  rw [map_smul, hV, FlowConstruction.partialChartField_eq_mfderiv_symm e W ht]
  have hv := congrArg (fun A : D →L[ℝ] D => A (W (e (γ t)))) hinv
  exact congrArg (fun v => (NormedSpace.fromTangentSpace t r) • v) hv

/-- A compact coordinate Lyapunov function bounds residence of native integral curves. -/
theorem exists_native_compact_lyapunov_residence
    (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    {L : D → ℝ} {W : D → D} (hL : ContDiff ℝ ∞ L) (hW : Continuous W)
    {C : Set D} (hC : IsCompact C) (hsource : C ⊆ Φ.source)
    (hneg : ∀ x ∈ C, fderiv ℝ L x (W x) < 0)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ∀ x ∈ Φ '' C, V x = FlowConstruction.partialChartField Φ.symm W x) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ Φ '' C := by
  obtain ⟨T, hT, hTbound⟩ := exists_compact_lyapunov_residence hL hW hC hneg
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hcoords (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : Φ.symm (γ t) ∈ C := by
    obtain ⟨z, hz, he⟩ := hstay t ht
    have hh : Φ.symm (Φ z) = z := Φ.left_inv' (hsource hz)
    rw [← he, hh]
    exact hz
  obtain ⟨t, ht, hout⟩ := hTbound (Φ.symm ∘ γ) (fun t ht _ =>
    hasDerivAt_partialChart_integralCurve Φ.symm W hγ
      (by obtain ⟨z, hz, he⟩ := hstay t ht
          exact he ▸ Φ.map_source' (hsource hz)) (hV (γ t) (hstay t ht)))
  exact hout (hcoords t ht)

/-- The local cancellation model has uniformly bounded residence in each native compact region. -/
theorem exists_native_cancelledDescent_residence_bound {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφnonneg : ∀ p, 0 ≤ φ p)
    (hone : ∀ s ∈ Icc (-a) a, φ (s, 0) = 1)
    {C : Set (Model m)} (hC : IsCompact C) (hsource : C ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ∀ x ∈ Φ '' C,
      V x = FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ) x) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ Φ '' C := by
  obtain ⟨k, -, hL, hneg⟩ := exists_compact_fieldLyapunov σ hσ ha hφ hφnonneg hone hC
  exact exists_native_compact_lyapunov_residence Φ hL
    (contDiff_cancelledDescent σ a hφ).continuous hC hsource hneg hV

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

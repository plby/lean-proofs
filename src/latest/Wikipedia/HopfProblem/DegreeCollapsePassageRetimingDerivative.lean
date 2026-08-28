import Wikipedia.HopfProblem.DegreeCollapsePassageNormalDerivative

/-!
# Unit-rate retiming preserves the actual native trace derivative

The centered clock has derivative one, so the tangent map of the trace is
unchanged. A shared native parameter chart then supplies a single source
frame for comparing the two constructed passages.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {U H X N : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
  {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

theorem mfderiv_retime_unit_rate
    {F : ℝ × X → N} {x : X} {σ τ : ℝ}
    (hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x))
    {D : ℝ → ℝ} (hD : HasDerivAt D 1 σ) (hpoint : D σ = τ) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N)
      (fun p : ℝ × X => F (D p.1, p.2)) (σ, x) : (ℝ × U) →L[ℝ] N) =
      mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x) := by
  subst τ
  have hDmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) D σ (ContinuousLinearMap.id ℝ ℝ) := by
    have hid : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) = ContinuousLinearMap.id ℝ ℝ := by
      ext z
      simp
    have h := hD.hasFDerivAt
    change HasFDerivAt D (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) σ at h
    rw [hid] at h
    exact h.hasMFDerivAt
  have ht := hDmf.comp (σ, x) (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (σ, x))
  have hp : HasMFDerivAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I)
      (fun p : ℝ × X => (D p.1, p.2)) (σ, x) (ContinuousLinearMap.id ℝ (ℝ × U)) := by
    convert! ht.prodMk (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (σ, x)) using 1
  have hF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) := hF
  have hc := (hF'.hasMFDerivAt.comp (σ, x) hp).mfderiv
  change (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N)
    (fun p : ℝ × X => F (D p.1, p.2)) (σ, x) : (ℝ × U) →L[ℝ] N) =
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) : (ℝ × U) →L[ℝ] N).comp
        (ContinuousLinearMap.id ℝ (ℝ × U)) at hc
  apply ContinuousLinearMap.ext
  intro z
  exact congrArg (fun L : (ℝ × U) →L[ℝ] N => L z) hc

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem fderiv_retimed_trace_parameter
    {F : ℝ × X → N} {x : X} {σ τ : ℝ}
    (hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x))
    {D : ℝ → ℝ} (hD : HasDerivAt D 1 σ) (hpoint : D σ = τ)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, A) (𝓘(ℝ, ℝ).prod I) A (ℝ × X) ∞)
    (hΨ : (0 : A) ∈ Ψ.source) (hcenter : Ψ 0 = (σ, x)) :
    fderiv ℝ (fun z : A => F (D (Ψ z).1, (Ψ z).2)) 0 =
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x) : (ℝ × U) →L[ℝ] N).comp
        (mfderiv 𝓘(ℝ, A) (𝓘(ℝ, ℝ).prod I) Ψ 0) := by
  let G : ℝ × X → N := fun p => F (D p.1, p.2)
  have hF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) := by
    rw [hpoint]
    exact hF
  have hG : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (σ, x) :=
    hF'.comp (σ, x) ((hD.differentiableAt.mdifferentiableAt.comp
      (σ, x) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd)
  have hG' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (Ψ 0) := by
    rw [hcenter]
    exact hG
  change fderiv ℝ (G ∘ Ψ) 0 = _
  rw [← mfderiv_eq_fderiv, mfderiv_comp 0 hG' (Ψ.mdifferentiableAt (by simp) hΨ), hcenter]
  rw [show (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (σ, x) : (ℝ × U) →L[ℝ] N) =
    mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x) from mfderiv_retime_unit_rate hF hD hpoint]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

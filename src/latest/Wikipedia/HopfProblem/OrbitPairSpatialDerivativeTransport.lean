import Wikipedia.HopfProblem.OrbitPairSupportedSpatialVelocity

/-!
# Projected tangent images and time velocities under spatial source motions

Precomposition by the native time-preserving source diffeomorphism retains
the whole projected tangent image. At a fixed time slice, the prescribed
spatial velocity changes the vertical derivative to the old derivative
applied to `(1,a)`.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization

open Wikipedia.SmoothSixDPoincare

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N]
  (D : ℝ → Diffeomorph I I M M ∞)
  (hD : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => D p.1 p.2))

include hD

theorem changedFamily_derivative_range {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F) (q : ℝ × M) :
    LinearMap.range (mfderiv (𝓘(ℝ, ℝ).prod I) J
      (changedFamily F (fun t => (D t).toEquiv)) q).toLinearMap =
    LinearMap.range (mfderiv (𝓘(ℝ, ℝ).prod I) J
      F (sourceEquiv (fun t => (D t).toEquiv) q)).toLinearMap := by
  obtain ⟨Ψ, hΨ⟩ := NativeFamily.exists_spatial_source_diffeomorph hD
    (fun t => ⟨D t, fun _ => rfl⟩)
  let e := fun t => (D t).toEquiv
  have heq : (sourceEquiv e : ℝ × M → ℝ × M) = Ψ := funext (fun p => (hΨ p).symm)
  have hf : changedFamily F e = F ∘ Ψ := congrArg (fun f => F ∘ f) heq
  let A : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (Ψ q)
  let B : ℝ × E →L[ℝ] ℝ × E :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) Ψ q
  let C : ℝ × E →L[ℝ] G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) J (changedFamily F e) q
  have hC : C = A.comp B := by
    change (mfderiv (𝓘(ℝ, ℝ).prod I) J (changedFamily F e) q : ℝ × E →L[ℝ] G) = _
    rw [hf]
    exact mfderiv_comp q (hF.mdifferentiableAt (by simp))
      (Ψ.contMDiff.mdifferentiableAt (by simp))
  have hB : Surjective B :=
    (PartialChart.bijective_mfderiv Ψ.toPartialDiffeomorph (mem_univ q)).surjective
  change LinearMap.range C.toLinearMap =
    LinearMap.range (mfderiv (𝓘(ℝ, ℝ).prod I) J F (sourceEquiv e q)).toLinearMap
  rw [heq]
  change LinearMap.range C.toLinearMap = LinearMap.range A.toLinearMap
  ext w
  constructor
  · rintro ⟨v, hv⟩
    change C v = w at hv
    refine ⟨B v, ?_⟩
    change A (B v) = w
    simpa only [hC, ContinuousLinearMap.comp_apply] using hv
  · rintro ⟨v, hv⟩
    obtain ⟨u, hu⟩ := hB v
    refine ⟨u, ?_⟩
    change C u = w
    rw [hC, ContinuousLinearMap.comp_apply, hu]
    exact hv

theorem changedFamily_time_derivative {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F) {t : ℝ} {x : M} {a : E}
    (hfixed : D t x = x)
    (hvelocity : (mfderiv (𝓘(ℝ, ℝ).prod I) I
      (fun p : ℝ × M => D p.1 p.2) (t, x) : ℝ × E →L[ℝ] E) =
      ContinuousLinearMap.snd ℝ ℝ E + (ContinuousLinearMap.fst ℝ ℝ E).smulRight a) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) J
      (changedFamily F (fun s => (D s).toEquiv)) (t, x) : ℝ × E →L[ℝ] G) (1, 0) =
    (mfderiv (𝓘(ℝ, ℝ).prod I) J F (t, x) : ℝ × E →L[ℝ] G) (1, a) := by
  let e := fun s => (D s).toEquiv
  let Ψ : ℝ × M → ℝ × M := sourceEquiv e
  have hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ Ψ :=
    contMDiff_fst.prodMk hD
  have hpoint : Ψ (t, x) = (t, x) := Prod.ext rfl hfixed
  let A : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (t, x)
  let B : ℝ × E →L[ℝ] ℝ × E :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) Ψ (t, x)
  let C : ℝ × E →L[ℝ] G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) J (changedFamily F e) (t, x)
  have hB : B = (ContinuousLinearMap.fst ℝ ℝ E).prod
      (ContinuousLinearMap.snd ℝ ℝ E + (ContinuousLinearMap.fst ℝ ℝ E).smulRight a) := by
    have hh := mfderiv_prodMk (x := (t, x)) mdifferentiableAt_fst
      (hD.mdifferentiableAt (by simp))
    rw [mfderiv_fst, hvelocity] at hh
    exact hh
  have hC : C = A.comp B := by
    have hh := mfderiv_comp (t, x) (hF.mdifferentiableAt (x := Ψ (t, x)) (by simp))
      (hΨ.mdifferentiableAt (by simp))
    rw [hpoint] at hh
    exact hh
  change C (1, 0) = A (1, a)
  rw [hC, ContinuousLinearMap.comp_apply, hB]
  congr 1
  simp

end Wikipedia.HopfProblem.OrbitPair.SpatialReparametrization

import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorOverlaps
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorGluing
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCuspCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorUniquenessCusp

/-!
# Constructing the global affine mu period

The actual regular, elliptic, and cusp seeds supply the local affine
sections. Their actual descended differences supply the additive cocycle
on the finite coordinate of a supplied normalized sphere identification.
The proved negative-one Cousin theorem corrects these sections to one
global holomorphic function satisfying every triangle-group affine law.

The simple source-cusp pole of the homogeneous generator cancels the
negative-one correction factor. The resulting cusp germ is analytic in
the original exponential cusp coordinate, not merely in the target
sphere coordinate. No local section or overlap cocycle is an input.
-/

noncomputable section

open Filter Metric Set UpperHalfPlane
open scoped Topology ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

open HolomorphicCousin

attribute [local instance] triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  {τ : ℍ → ℍ} (hτ : TauCovariant τ)
  (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)

include hπ

/-- The actual zero cusp seed and the simple homogeneous pole make every
negative-one correction regular in the original source cusp parameter. -/
theorem correctedGlue_cuspRegular {F : ℍ → ℂ}
    {h : Cover.Index → Cover.Index → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hRU : (ball (0 : ℂ) R)ᶜ ⊆ Cover.finitePatch π Cover.cuspIndex)
    (s : NegativeOneCocycleSolution (fun i => (Cover.finitePatch π i : Set ℂ))
      h Cover.cuspIndex R)
    (hdiff : ∀ i j z,
      BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i →
      BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π j →
      localSection hτ hτa i z - localSection hτ hτa j z =
        F z * h i j (BetaTorsor.finiteProjection π z))
    (hFpole : ∃ v : ℂ → ℂ, AnalyticAt ℂ v 0 ∧ v 0 ≠ 0 ∧
      ∀ᶠ z in atImInfty, F z = (Triangle.cuspQ z)⁻¹ * v (Triangle.cuspQ z)) :
    CuspRegular (Gluing.correctedGlue (BetaTorsor.finiteProjection π)
      (fun i => (Cover.finitePatch π i : Set ℂ)) (Cover.exists_finitePatch π)
      (localSection hτ hτa) F s) := by
  obtain ⟨v, hv, _hv0, hFv⟩ := hFpole
  have hS : AnalyticAt ℂ s.infinityPart 0 :=
    s.infinity_analytic 0 (mem_ball_self (inv_pos.mpr hR))
  refine ⟨fun q => -v q * CuspCoordinates.tDivQ π q *
    s.infinityPart (CuspCoordinates.t π q),
    CuspCoordinates.analyticAt_correction π hπ hv hS, ?_⟩
  filter_upwards [hFv, CuspCoordinates.eventually_mem_horodisc Triangle.width,
    CuspCoordinates.eventually_lt_norm_finiteProjection π hπ R,
    CuspCoordinates.t_cuspQ_eq_inv_finiteProjection π hπ] with z hFz hz hlarge ht
  rw [Gluing.correctedGlue_cusp s hdiff hRU
    (fun z hz => localSection_cusp hτ hτa z hz) hz hlarge, hFz, ← ht]
  have hc : -((Triangle.cuspQ z)⁻¹ * v (Triangle.cuspQ z)) *
      CuspCoordinates.t π (Triangle.cuspQ z) =
      -v (Triangle.cuspQ z) * CuspCoordinates.tDivQ π (Triangle.cuspQ z) := by
    rw [CuspCoordinates.t_eq_mul_tDivQ π hπ]
    field_simp [Triangle.cuspQ_ne_zero z]
  rw [hc]

/-- Global affine mu existence from the genuine cover, the genuine
homogeneous generator, and its simple cusp pole. All local sections and
overlap cocycles are constructed in the proof. -/
theorem exists_holomorphic_affine_cuspRegular (F : ℍ → ℂ)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hFc : MuGenerator.Homogeneous τ F)
    (hFzero : ∀ z, F z = 0 ↔
      triangleOrbitProjection z = triangleOrbitCenterOne ∨
        triangleOrbitProjection z = triangleOrbitCenterTwo)
    (hFpole : ∃ v : ℂ → ℂ, AnalyticAt ℂ v 0 ∧ v 0 ≠ 0 ∧
      ∀ᶠ z in atImInfty, F z = (Triangle.cuspQ z)⁻¹ * v (Triangle.cuspQ z)) :
    ∃ μ : ℍ → ℂ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ ∧
      (∀ g z, μ (triangleGeometricRepresentation g z) =
        (cocycle hτ hτa).fibreMap g z (μ z)) ∧
      (∀ z, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ)) ∧
      (∀ z, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) ∧
      CuspRegular μ := by
  let U : Cover.Index → Set ℂ := fun i => Cover.finitePatch π i
  let h := descendedOverlap hτ hτa F π hπ
  have hlocal : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localSection hτ hτa i)
      (BetaTorsor.finiteProjection π ⁻¹' U i) := by
    intro i
    change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localSection hτ hτa i)
      (BetaTorsor.finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ))
    rw [finiteProjection_preimage_patch π hπ]
    exact localSection_holomorphic hτ hτa i
  have hq : ∀ i j z, BetaTorsor.finiteProjection π z ∈ U i →
      BetaTorsor.finiteProjection π z ∈ U j →
      h i j (BetaTorsor.finiteProjection π z) =
        (localSection hτ hτa i z - localSection hτ hτa j z) / F z :=
    descendedOverlap_projection hτ hτa F π hπ hFc
  have hz : ∀ i j z, BetaTorsor.finiteProjection π z ∈ U i →
      BetaTorsor.finiteProjection π z ∈ U j → F z = 0 →
      localSection hτ hτa i z = localSection hτ hτa j z := by
    intro i j z hi hj hzero
    exact localSection_eq_at_generator_zero hτ hτa F hFzero i j z
      ((finiteProjection_mem_patch π hπ i z).mp hi)
      ((finiteProjection_mem_patch π hπ j z).mp hj) hzero
  have hd := Gluing.difference_eq_mul_quotient hq hz
  obtain ⟨R, hR, hRU⟩ := Cover.finitePatch_cusp_contains_exterior π hπ
  obtain ⟨s, hs, _⟩ := Gluing.exists_corrected_gluing
    (BetaTorsor.finiteProjection_holomorphic π hπ)
    (BetaTorsor.finiteProjection_surjective π hπ)
    (fun i => (Cover.finitePatch π i).isOpen) (Cover.exists_finitePatch π) hlocal hF
    (descendedOverlap_analytic hτ hτa F hFzero π hπ hF hFc) hq hz
    Cover.cuspIndex hR hRU
  let μ := Gluing.correctedGlue (BetaTorsor.finiteProjection π) U
    (Cover.exists_finitePatch π) (localSection hτ hτa) F s
  have hlocalLaw : ∀ i, (cocycle hτ hτa).EquivariantOn (localSection hτ hτa i)
      (BetaTorsor.finiteProjection π ⁻¹' U i) := by
    intro i
    change (cocycle hτ hτa).EquivariantOn (localSection hτ hτa i)
      (BetaTorsor.finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ))
    rw [finiteProjection_preimage_patch π hπ]
    exact localSection_equivariant hτ hτa i
  have hμ : ∀ g z, μ (triangleGeometricRepresentation g z) =
      (cocycle hτ hτa).fibreMap g z (μ z) :=
    Gluing.correctedGlue_affine_law s hd (cocycle hτ hτa)
      (BetaTorsor.finiteProjection_invariant π) hlocalLaw
      (homogeneous_scale_law hτ hτa hFc)
  refine ⟨μ, hs, hμ, ?_, ?_, ?_⟩
  · intro z
    simpa only [triangleGeometricRepresentation_generator₁_apply,
      cocycle_fibreMap_generator₁] using hμ triangleGenerator₁ z
  · intro z
    simpa only [triangleGeometricRepresentation_generator₂_apply,
      cocycle_fibreMap_generator₂] using hμ triangleGenerator₂ z
  · exact correctedGlue_cuspRegular π hπ hτ hτa hR hRU s hd hFpole

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

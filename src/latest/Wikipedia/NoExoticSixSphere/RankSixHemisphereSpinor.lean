import Wikipedia.NoExoticSixSphere.RankSixLineSpinor
import Wikipedia.NoExoticSixSphere.HemisphereFrames

/-!
# Continuous unit spinor sections on closed hemispheres

The existing real projection transport suffices for a complex-line family:
it transports a nonzero vector, which can then be normalized. No complex
linearity of the transport is assumed.
-/

namespace NoExoticSixSphere.RankSixComplexProjection

noncomputable def realProjection (J : OrthogonalComplexStructures.Space 6) :
    Spinor →L[ℝ] Spinor := (projection J).restrictScalars ℝ

theorem realProjection_idempotent (J : OrthogonalComplexStructures.Space 6) :
    IsIdempotentElem (realProjection J) := by
  apply ContinuousLinearMap.ext
  intro q
  exact DFunLike.congr_fun (projection_idempotent J) q

theorem continuous_realProjection : Continuous realProjection :=
  (ContinuousLinearMap.continuous_restrictScalars ℝ).comp continuous_projection

theorem exists_nonzero_fixed (J : OrthogonalComplexStructures.Space 6) :
    ∃ q : Spinor, q ≠ 0 ∧ projection J q = q := by
  let : Nontrivial (LinearMap.range (projection J).toLinearMap) :=
    Module.nontrivial_of_finrank_eq_succ (projection_finrank J)
  obtain ⟨q, hq⟩ := exists_ne (0 : LinearMap.range (projection J).toLinearMap)
  refine ⟨q, fun h ↦ hq (Subtype.ext h), ?_⟩
  obtain ⟨w, hw⟩ := q.2
  rw [← hw]
  exact DFunLike.congr_fun (projection_idempotent J) w

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  (J : C(UnitSphere E, OrthogonalComplexStructures.Space 6)) (v : UnitSphere E)

noncomputable def lineTransport :
    ContinuousRangeTransport (fun _ : ClosedHemisphere v ↦ realProjection (J v))
      (fun x : ClosedHemisphere v ↦ realProjection (J x.1)) :=
  hemisphereTransport (fun x ↦ realProjection (J x))
    (fun x ↦ realProjection_idempotent (J x))
    (continuous_realProjection.comp J.continuous) v

noncomputable def hemisphereVector (q : Spinor) (x : ClosedHemisphere v) : Spinor :=
  (lineTransport J v).toFun x q

theorem continuous_hemisphereVector (q : Spinor) : Continuous (hemisphereVector J v q) :=
  (lineTransport J v).continuous.clm_apply continuous_const

theorem hemisphereVector_ne_zero {q : Spinor} (hq : q ≠ 0) (x : ClosedHemisphere v) :
    hemisphereVector J v q x ≠ 0 := by
  intro h
  apply hq
  apply ((lineTransport J v).invertible x).injective
  rw [map_zero]
  change hemisphereVector J v q x = 0
  exact h

theorem hemisphereVector_fixed {q : Spinor} (hq : projection (J v) q = q)
    (x : ClosedHemisphere v) :
    projection (J x.1) (hemisphereVector J v q x) = hemisphereVector J v q x := by
  have h := congrArg (fun T : Spinor →L[ℝ] Spinor ↦ T q)
    ((lineTransport J v).intertwines x)
  change projection (J x.1) (hemisphereVector J v q x) =
    (lineTransport J v).toFun x (projection (J v) q) at h
  rwa [hq] at h

noncomputable def hemisphereSection (q : Spinor) (hq : q ≠ 0) :
    C(ClosedHemisphere v, UnitSpinor) where
  toFun x := ⟨NormedSpace.normalize (hemisphereVector J v q x), by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize (hemisphereVector_ne_zero J v hq x)⟩
  continuous_toFun := by
    have hc := continuous_hemisphereVector J v q
    exact ((hc.norm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr
      (hemisphereVector_ne_zero J v hq x))).smul hc).subtype_mk _

theorem hemisphereSection_fixed (q : Spinor) (hne : q ≠ 0)
    (hq : projection (J v) q = q) (x : ClosedHemisphere v) :
    projection (J x.1) (hemisphereSection J v q hne x) =
      (hemisphereSection J v q hne x : Spinor) := by
  change realProjection (J x.1)
    (‖hemisphereVector J v q x‖⁻¹ • hemisphereVector J v q x) =
      ‖hemisphereVector J v q x‖⁻¹ • hemisphereVector J v q x
  rw [map_smul]
  exact congrArg (fun w : Spinor ↦ ‖hemisphereVector J v q x‖⁻¹ • w)
    (hemisphereVector_fixed J v hq x)

theorem exists_hemisphere_unitSection :
    ∃ q : C(ClosedHemisphere v, UnitSpinor),
      ∀ x, projection (J x.1) (q x) = (q x : Spinor) := by
  obtain ⟨q, hne, hq⟩ := exists_nonzero_fixed (J v)
  exact ⟨hemisphereSection J v q hne, hemisphereSection_fixed J v q hne hq⟩

end NoExoticSixSphere.RankSixComplexProjection

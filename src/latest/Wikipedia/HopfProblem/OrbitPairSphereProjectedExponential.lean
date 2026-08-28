import Wikipedia.HopfProblem.OrbitPairSphereShortGeodesic

/-!
# A genuine local inverse for the sphere tangent exponential

Project the exponential endpoint to the actual tangent hyperplane. Its
derivative at zero is the identity. The analytic inverse-function theorem
then gives a smooth partial inverse on arbitrarily small tangent vectors,
with all exponential endpoints in the positive hemisphere. Orthogonal
projection is injective on that unit hemisphere, so this inverse recovers
the original sphere endpoint rather than just its projection.
-/

noncomputable section

open scoped ContDiff Manifold
open Set

namespace Wikipedia.HopfProblem.OrbitPair.SphereTangentExponential

open NoExoticSixSphere GLOrthonormalization

variable {n : ℕ}

def projection (x : Vector n) : Vector n →L[ℝ] Tangent x :=
  ((ℝ ∙ x)ᗮ).orthogonalProjectionOnto

theorem projection_base (x : Vector n) : projection x x = 0 :=
  Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero x

theorem projection_tangent (x : Vector n) (v : Tangent x) : projection x v = v :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v

theorem projection_formula {x : Vector n} (hx : ‖x‖ = 1) (z : Vector n) :
    (projection x z : Vector n) = z - inner ℝ x z • x := by
  change ((ℝ ∙ x)ᗮ).starProjection z = _
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_unit_singleton ℝ hx]

theorem projection_norm_sq {x z : Vector n} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) :
    ‖projection x z‖ ^ 2 = 1 - (inner ℝ x z) ^ 2 := by
  change ‖(projection x z : Vector n)‖ ^ 2 = _
  rw [projection_formula hx, norm_sub_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, hx, hz, one_pow, mul_one]
  have hzx : inner ℝ z x = inner ℝ x z := real_inner_comm _ _
  rw [hzx, sq_abs]
  ring

theorem projection_injective_positive {x z z' : Vector n} (hx : ‖x‖ = 1)
    (hz : ‖z‖ = 1) (hz' : ‖z'‖ = 1)
    (hpos : 0 ≤ inner ℝ x z) (hpos' : 0 ≤ inner ℝ x z')
    (he : projection x z = projection x z') : z = z' := by
  have hs := congrArg (fun v : Tangent x => ‖v‖ ^ 2) he
  rw [projection_norm_sq hx hz, projection_norm_sq hx hz'] at hs
  have hi : inner ℝ x z = inner ℝ x z' := by nlinarith
  have hv := congrArg (fun v : Tangent x => (v : Vector n)) he
  rw [projection_formula hx, projection_formula hx, hi] at hv
  have h := congrArg (fun q : Vector n => q + inner ℝ x z' • x) hv
  simpa only [sub_add_cancel] using h

def projectedEndpoint (x : Vector n) (v : Tangent x) : Tangent x :=
  projection x (curve x v 1)

theorem contDiff_endpoint (x : Vector n) : ContDiff ℝ ∞ (fun v : Tangent x => curve x v 1) :=
  (contDiff_family x).comp (contDiff_const.prodMk contDiff_id)

theorem contDiff_projectedEndpoint (x : Vector n) : ContDiff ℝ ∞ (projectedEndpoint x) :=
  (projection x).contDiff.comp (contDiff_endpoint x)

theorem projectedEndpoint_zero (x : Vector n) : projectedEndpoint x 0 = 0 := by
  rw [projectedEndpoint, curve_zero_velocity, projection_base]

theorem hasFDerivAt_projectedEndpoint_zero {x : Vector n} (hx : ‖x‖ = 1) :
    HasFDerivAt (projectedEndpoint x) (1 : Tangent x →L[ℝ] Tangent x) 0 := by
  have hd := (projection x).hasFDerivAt.comp 0 (hasFDerivAt_endpoint_zero hx)
  have he : (projection x).comp ((ℝ ∙ x)ᗮ).subtypeL = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    exact projection_tangent x v
  simpa only [he, projectedEndpoint, Function.comp_def] using! hd

structure LocalLogData (x : Vector n) (ε : ℝ) where
  chart : PartialDiffeomorph 𝓘(ℝ, Tangent x) 𝓘(ℝ, Tangent x) (Tangent x) (Tangent x) ∞
  zero_source : 0 ∈ chart.source
  source_small : ∀ v ∈ chart.source, ‖v‖ < ε
  source_positive : ∀ v ∈ chart.source, 0 < inner ℝ x (curve x v 1)
  formula : (chart : Tangent x → Tangent x) = projectedEndpoint x

theorem nonempty_localLogData {x : Vector n} (hx : ‖x‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (LocalLogData x ε) := by
  let U : Set (Tangent x) := {v | ‖v‖ < ε ∧ 0 < inner ℝ x (curve x v 1)}
  have hheight : Continuous (fun v : Tangent x => inner ℝ x (curve x v 1)) :=
    continuous_const.inner (contDiff_endpoint x).continuous
  have ho : IsOpen U :=
    (isOpen_lt continuous_norm (continuous_const (y := ε))).inter
      (isOpen_lt (continuous_const (y := (0 : ℝ))) hheight)
  have hz : (0 : Tangent x) ∈ U := by
    change ‖(0 : Tangent x)‖ < ε ∧ 0 < inner ℝ x (curve x 0 1)
    simp only [norm_zero, curve_zero_velocity, real_inner_self_eq_norm_sq, hx, one_pow]
    exact ⟨hε, zero_lt_one⟩
  have hd : (fderiv ℝ (projectedEndpoint x) 0).IsInvertible := by
    rw [(hasFDerivAt_projectedEndpoint_zero hx).fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ (Tangent x), rfl⟩
  obtain ⟨d, hd₀, hdU, hdf⟩ := exists_partialDiffeomorph_of_contDiffOn ho hz
    (contDiff_projectedEndpoint x).contDiffOn hd
  exact ⟨⟨d, hd₀, fun v hv => (hdU hv).1, fun v hv => (hdU hv).2, hdf⟩⟩

end Wikipedia.HopfProblem.OrbitPair.SphereTangentExponential

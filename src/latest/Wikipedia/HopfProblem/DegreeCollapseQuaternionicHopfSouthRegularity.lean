import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfSouthFiber

/-!
# The south Hopf fiber has its original regular atlas and transverse derivative

Along the second quaternionic axis, the actual polynomial differential is
w ↦ (0, 2 w conjugate(b)). The explicit right inverse proves regularity
in the original sphere atlas. The actual regular fiber is diffeomorphic
to the standard S3, with its original inclusion retained.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSouthRegularity

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfSouthFiber
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

def transverseAxis : ℍ →L[ℝ] V 8 :=
  QuaternionicHopf.axis.toContinuousLinearMap.comp
    Quaternion.linearIsometryEquivTuple.toContinuousLinearMap

theorem first_transverseAxis (w : ℍ) : first (transverseAxis w) = w := by
  change first (QuaternionicHopf.axis (Quaternion.linearIsometryEquivTuple w)) = w
  rw [QuaternionicHopf.first_axis, LinearIsometryEquiv.symm_apply_apply]

theorem second_transverseAxis (w : ℍ) : second (transverseAxis w) = 0 :=
  QuaternionicHopf.second_axis _

theorem polynomial_fderiv_first (x : V 8) (hx : first x = 0) (w : ℍ) :
    fderiv ℝ polynomial x (transverseAxis w) =
      SphereCylinder.join 3 (0,
        Quaternion.linearIsometryEquivTuple ((2 : ℝ) • (w * star (second x)))) := by
  have h₁ := (hasStrictFDerivAt_norm_sq (first x)).hasFDerivAt.comp x first.hasFDerivAt
  have h₂ := (hasStrictFDerivAt_norm_sq (second x)).hasFDerivAt.comp x second.hasFDerivAt
  have hmul := first.hasFDerivAt.mul' (conjugation.hasFDerivAt.comp x second.hasFDerivAt)
  have htail := Quaternion.linearIsometryEquivTuple.hasFDerivAt.comp x
    ((hasFDerivAt_const (2 : ℝ) x).smul hmul)
  have h := (SphereCylinder.join 3).hasFDerivAt.comp x ((h₁.sub h₂).prodMk htail)
  simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply, norm_sq_eq_normSq] at h
  change HasFDerivAt (𝕜 := ℝ) polynomial _ x at h
  rw [h.fderiv]
  simp [first_transverseAxis, second_transverseAxis, hx, conjugation]

theorem inner_transverseAxis (x : V 8) (hx : first x = 0) (w : ℍ) :
    inner ℝ x (transverseAxis w) = 0 := by
  have he : x = planeCoordinates (WithLp.toLp 2 ((0 : ℍ), second x)) := by
    rw [← hx]
    exact (planeCoordinates.apply_symm_apply x).symm
  have ht : transverseAxis w = planeCoordinates (WithLp.toLp 2 (w, (0 : ℍ))) := by
    change planeCoordinates (WithLp.toLp 2
      (Quaternion.linearIsometryEquivTuple.symm (Quaternion.linearIsometryEquivTuple w),
        (0 : ℍ))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [he, ht, planeCoordinates.inner_map_map]
  simp

theorem second_mul_star (x : Sphere 7) (hx : first x.val = 0) :
    second x.val * star (second x.val) = 1 := by
  have hs := normSq_sum x.val
  rw [hx, map_zero, zero_add, mem_sphere_zero_iff_norm.mp x.property, one_pow] at hs
  rw [Quaternion.self_mul_star, hs]
  rfl

theorem transverse_right_inverse (b w : ℍ) (hb : b * star b = 1) :
    (2 : ℝ) • (((1 / 2 : ℝ) • (w * b)) * star b) = w := by
  rw [smul_mul_assoc, mul_assoc, hb, mul_one, smul_smul]
  norm_num

theorem point_inner_head (z : V 5) : inner ℝ point.val z = -(z 0) := by
  change inner ℝ (-(spherePole 4).val) z = _
  rw [inner_neg_left, QuaternionicHopf.pole_inner_head]

theorem polynomial_tangent_surjective (x : Sphere 7) (hx : first x.val = 0)
    (z : V 5) (hz : z 0 = 0) :
    ∃ v : V 8, inner ℝ x.val v = 0 ∧ fderiv ℝ polynomial x.val v = z := by
  let w := Quaternion.linearIsometryEquivTuple.symm (SphereCylinder.tail 3 z)
  let v := (1 / 2 : ℝ) • (w * second x.val)
  refine ⟨transverseAxis v, inner_transverseAxis x.val hx v, ?_⟩
  rw [polynomial_fderiv_first x.val hx]
  have ht := transverse_right_inverse (second x.val) w (second_mul_star x hx)
  change (2 : ℝ) • (v * star (second x.val)) = w at ht
  rw [ht]
  change SphereCylinder.join 3 (0, Quaternion.linearIsometryEquivTuple
    (Quaternion.linearIsometryEquivTuple.symm (SphereCylinder.tail 3 z))) = z
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact QuaternionicHopf.join_zero_tail z hz

theorem south_regular (x : Sphere 7) (hx : sphereMap x = point) :
    Function.Surjective (mfderiv (𝓡 7) (𝓡 4) sphereMap x) := by
  apply sphereMap_mfderiv_surjective_of_ambient polynomial sphereMap contDiff_polynomial
    contMDiff_sphereMap sphereMap_val x
  intro z hz
  rw [hx, point_inner_head] at hz
  exact polynomial_tangent_surjective x ((sphereMap_eq_point_iff x).mp hx) z
    (neg_eq_zero.mp hz)

theorem fiberPoint_injective : Function.Injective QuaternionicHopfSouthFiber.fiberPoint := by
  intro p q hpq
  apply Subtype.ext
  have h := congrArg (fun x : Sphere 7 ↦ Quaternion.linearIsometryEquivTuple (second x.val)) hpq
  simpa only [QuaternionicHopfSouthFiber.second_fiberPoint,
    LinearIsometryEquiv.apply_symm_apply] using h

theorem fiberPoint_mfderiv_injective (q : Sphere 3) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 7) QuaternionicHopfSouthFiber.fiberPoint q) := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  let : Fact (Module.finrank ℝ (V 8) = 7 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hsource : ContMDiff (𝓡 3) 𝓘(ℝ, V 4) ∞ (Subtype.val : Sphere 3 → V 4) :=
    contMDiff_coe_sphere
  have htarget : ContMDiff (𝓡 7) 𝓘(ℝ, V 8) ∞ (Subtype.val : Sphere 7 → V 8) :=
    contMDiff_coe_sphere
  have he : (Subtype.val : Sphere 7 → V 8) ∘ QuaternionicHopfSouthFiber.fiberPoint =
      QuaternionicHopfSouthFiber.axis.toContinuousLinearMap ∘
        (Subtype.val : Sphere 3 → V 4) := rfl
  have hd := congrArg (sphereAmbientDerivative q) he
  unfold sphereAmbientDerivative at hd
  rw [mfderiv_comp q (htarget.mdifferentiableAt (by simp))
      (QuaternionicHopfSouthFiber.contMDiff_fiberPoint.mdifferentiableAt (by simp)),
    mfderiv_comp q
      QuaternionicHopfSouthFiber.axis.toContinuousLinearMap.differentiableAt.mdifferentiableAt
      (hsource.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hd
  intro v w hvw
  have hι : Function.Injective
      (mfderiv (𝓡 3) 𝓘(ℝ, V 4) (Subtype.val : Sphere 3 → V 4) q) := by
    convert! injective_mvfderiv_subtypeVal_sphere (n := 3) q
  apply hι
  apply QuaternionicHopfSouthFiber.axis.injective
  have hv := congrArg (fun L : V 3 →L[ℝ] V 8 ↦ L v) hd
  have hw := congrArg (fun L : V 3 →L[ℝ] V 8 ↦ L w) hd
  exact hv.symm.trans ((congrArg
    (mfderiv (𝓡 7) 𝓘(ℝ, V 8) (Subtype.val : Sphere 7 → V 8)
      (QuaternionicHopfSouthFiber.fiberPoint q)) hvw).trans hw)

theorem sphereMap_fiber_range (x : Sphere 7) :
    sphereMap x = point ↔ ∃ q : Sphere 3, QuaternionicHopfSouthFiber.fiberPoint q = x := by
  constructor
  · intro hx
    exact ⟨QuaternionicHopfSouthFiber.fiberInverse ⟨x, hx⟩,
      QuaternionicHopfSouthFiber.fiberPoint_fiberInverse ⟨x, hx⟩⟩
  · rintro ⟨q, rfl⟩
    exact QuaternionicHopfSouthFiber.sphereMap_fiberPoint q

def fiberDiffeomorph :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap point south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    Sphere 3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ {x : Sphere 7 // sphereMap x = point} :=
  diffeomorphToRegularFiber sphereMap contMDiff_sphereMap point south_regular 3
    (by simp only [finrank_euclideanSpace_fin]) QuaternionicHopfSouthFiber.fiberPoint
    QuaternionicHopfSouthFiber.contMDiff_fiberPoint fiberPoint_injective
    fiberPoint_mfderiv_injective sphereMap_fiber_range

theorem fiberDiffeomorph_val (q : Sphere 3) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap point south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    (fiberDiffeomorph q).val = QuaternionicHopfSouthFiber.fiberPoint q := rfl

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSouthRegularity

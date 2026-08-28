import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfSouthNormal
import Wikipedia.NoExoticSixSphere.NormalFrameOfEquations

/-!
# The explicit canonical normal frame of the original Hopf polynomial

At the south fiber, the four quaternionic transverse directions and the
radial direction together invert the full ambient polynomial derivative.
The formula retains its actual signs and factors of two. Its image is
orthogonal to the actual kernel, so it is exactly the canonical orthogonal
right inverse and varies smoothly along the whole south fiber.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSouthPolynomialFrame

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfSouthNormal
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

def inclusion (q : Sphere 3) : V 8 := (QuaternionicHopfSouthFiber.fiberPoint q).val

theorem polynomial_fderiv_south (q : Sphere 3) (v : V 8) :
    fderiv ℝ polynomial (inclusion q) v =
      SphereCylinder.join 3
        (-2 * inner ℝ (Quaternion.linearIsometryEquivTuple.symm q.val) (second v),
          Quaternion.linearIsometryEquivTuple
            ((2 : ℝ) • (first v * star (Quaternion.linearIsometryEquivTuple.symm q.val)))) := by
  let x := inclusion q
  have h₁ := (hasStrictFDerivAt_norm_sq (first x)).hasFDerivAt.comp x first.hasFDerivAt
  have h₂ := (hasStrictFDerivAt_norm_sq (second x)).hasFDerivAt.comp x second.hasFDerivAt
  have hmul := first.hasFDerivAt.mul' (conjugation.hasFDerivAt.comp x second.hasFDerivAt)
  have htail := Quaternion.linearIsometryEquivTuple.hasFDerivAt.comp x
    (hmul.const_smul (2 : ℝ))
  have h := (SphereCylinder.join 3).hasFDerivAt.comp x ((h₁.sub h₂).prodMk htail)
  simp only [Function.comp_apply, Pi.sub_apply, norm_sq_eq_normSq] at h
  change HasFDerivAt (𝕜 := ℝ) polynomial _ x at h
  rw [h.fderiv]
  have hfirst : first x = 0 := QuaternionicHopfSouthFiber.first_fiberPoint q
  have hsecond : second x = Quaternion.linearIsometryEquivTuple.symm q.val :=
    QuaternionicHopfSouthFiber.second_fiberPoint q
  have hb :
      innerSL ℝ (Quaternion.linearIsometryEquivTuple.symm q.val) (second v) =
        inner ℝ (Quaternion.linearIsometryEquivTuple.symm q.val) (second v) ∧
      (first v * conjugation (Quaternion.linearIsometryEquivTuple.symm q.val)).re =
        (first v * star (Quaternion.linearIsometryEquivTuple.symm q.val)).re ∧
      (first v * conjugation (Quaternion.linearIsometryEquivTuple.symm q.val)).imI =
        (first v * star (Quaternion.linearIsometryEquivTuple.symm q.val)).imI ∧
      (first v * conjugation (Quaternion.linearIsometryEquivTuple.symm q.val)).imJ =
        (first v * star (Quaternion.linearIsometryEquivTuple.symm q.val)).imJ ∧
      (first v * conjugation (Quaternion.linearIsometryEquivTuple.symm q.val)).imK =
        (first v * star (Quaternion.linearIsometryEquivTuple.symm q.val)).imK :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  simpa [hfirst, hsecond, neg_mul] using hb

theorem polynomial_derivative_radial (q : Sphere 3) :
    fderiv ℝ polynomial (inclusion q) (inclusion q) = SphereCylinder.join 3 (-2, (0 : V 4)) := by
  have hb : ‖Quaternion.linearIsometryEquivTuple.symm q.val‖ ^ 2 = 1 := by
    rw [Quaternion.linearIsometryEquivTuple.symm.norm_map,
      mem_sphere_zero_iff_norm.mp q.property, one_pow]
  rw [polynomial_fderiv_south]
  simp only [inclusion, QuaternionicHopfSouthFiber.first_fiberPoint,
    QuaternionicHopfSouthFiber.second_fiberPoint, zero_mul, smul_zero, map_zero,
    real_inner_self_eq_norm_sq, hb, mul_one]

def rawRightInverse (q : Sphere 3) : (ℝ × V 4) →L[ℝ] V 8 :=
  (-1 / 2 : ℝ) • (ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ (V 4))
    (inclusion q)) +
  (1 / 2 : ℝ) • ((frame q).comp (ContinuousLinearMap.snd ℝ ℝ (V 4)))

theorem rawRightInverse_apply (q : Sphere 3) (z : ℝ × V 4) :
    rawRightInverse q z = (-1 / 2 : ℝ) • (z.1 • inclusion q) +
      (1 / 2 : ℝ) • frame q z.2 := rfl

theorem polynomial_rawRightInverse (q : Sphere 3) (z : ℝ × V 4) :
    fderiv ℝ polynomial (inclusion q) (rawRightInverse q z) = SphereCylinder.join 3 z := by
  have hf : fderiv ℝ polynomial (inclusion q) (frame q z.2) =
      SphereCylinder.join 3 (0, (2 : ℝ) • z.2) := polynomial_derivative_frame q z.2
  rw [rawRightInverse_apply, map_add, map_smul, map_smul, polynomial_derivative_radial,
    map_smul, hf]
  rw [← map_smul, ← map_smul, ← map_smul, ← map_add]
  apply congrArg (SphereCylinder.join 3)
  apply Prod.ext
  · change (-1 / 2 : ℝ) * (z.1 * (-2)) + (1 / 2) * 0 = z.1
    ring
  · change (-1 / 2 : ℝ) • (z.1 • (0 : V 4)) + (1 / 2 : ℝ) • ((2 : ℝ) • z.2) = z.2
    norm_num [smul_smul]

def rightInverse (q : Sphere 3) : V 5 →L[ℝ] V 8 :=
  (rawRightInverse q).comp (SphereCylinder.join 3).symm.toContinuousLinearMap

theorem polynomial_rightInverse (q : Sphere 3) (z : V 5) :
    fderiv ℝ polynomial (inclusion q) (rightInverse q z) = z :=
  (polynomial_rawRightInverse q ((SphereCylinder.join 3).symm z)).trans
    ((SphereCylinder.join 3).apply_symm_apply z)

theorem polynomial_fderiv_surjective (q : Sphere 3) :
    Function.Surjective (fderiv ℝ polynomial (inclusion q)) :=
  fun z ↦ ⟨rightInverse q z, polynomial_rightInverse q z⟩


theorem polynomial_kernel_iff (q : Sphere 3) (v : V 8) :
    fderiv ℝ polynomial (inclusion q) v = 0 ↔
      first v = 0 ∧ inner ℝ (Quaternion.linearIsometryEquivTuple.symm q.val) (second v) = 0 := by
  constructor
  · intro hv
    rw [polynomial_fderiv_south] at hv
    have hh := (SphereCylinder.join 3).injective (hv.trans (map_zero (SphereCylinder.join 3)).symm)
    have hh₁ : -2 * inner ℝ (Quaternion.linearIsometryEquivTuple.symm q.val) (second v) = 0 :=
      congrArg Prod.fst hh
    have hh₂ : Quaternion.linearIsometryEquivTuple
        ((2 : ℝ) • (first v * star (Quaternion.linearIsometryEquivTuple.symm q.val))) = 0 :=
      congrArg Prod.snd hh
    have ht : (2 : ℝ) • (first v * star (Quaternion.linearIsometryEquivTuple.symm q.val)) = 0 :=
      Quaternion.linearIsometryEquivTuple.injective
        (hh₂.trans (map_zero Quaternion.linearIsometryEquivTuple).symm)
    have hp : first v * star (Quaternion.linearIsometryEquivTuple.symm q.val) = 0 :=
      (smul_eq_zero.mp ht).resolve_left (by norm_num)
    have hb : star (Quaternion.linearIsometryEquivTuple.symm q.val) ≠ 0 := by
      intro hz
      have hz' : Quaternion.linearIsometryEquivTuple.symm q.val = 0 := star_eq_zero.mp hz
      have hn := Quaternion.linearIsometryEquivTuple.symm.norm_map q.val
      rw [hz', norm_zero, mem_sphere_zero_iff_norm.mp q.property] at hn
      norm_num at hn
    exact ⟨(mul_eq_zero.mp hp).resolve_right hb, (mul_eq_zero.mp hh₁).resolve_left (by norm_num)⟩
  · rintro ⟨hf, hi⟩
    rw [polynomial_fderiv_south, hf, hi]
    simp

theorem inner_inclusion_of_first_zero (q : Sphere 3) (v : V 8) (hv : first v = 0) :
    inner ℝ v (inclusion q) =
      inner ℝ (second v) (Quaternion.linearIsometryEquivTuple.symm q.val) := by
  have he := QuaternionicHopfSouthFiber.axis_second_of_first_eq_zero v hv
  calc
    inner ℝ v (inclusion q) =
        inner ℝ (QuaternionicHopfSouthFiber.axis
          (Quaternion.linearIsometryEquivTuple (second v)))
          (QuaternionicHopfSouthFiber.axis q.val) :=
      congrArg (fun z : V 8 ↦ inner ℝ z (inclusion q)) he.symm
    _ = inner ℝ (Quaternion.linearIsometryEquivTuple (second v)) q.val :=
      QuaternionicHopfSouthFiber.axis.inner_map_map _ _
    _ = inner ℝ (second v) (Quaternion.linearIsometryEquivTuple.symm q.val) := by
      have h := Quaternion.linearIsometryEquivTuple.inner_map_map
        (second v) (Quaternion.linearIsometryEquivTuple.symm q.val)
      rwa [LinearIsometryEquiv.apply_symm_apply] at h

theorem rawRightInverse_mem_orthogonal (q : Sphere 3) (z : ℝ × V 4) :
    rawRightInverse q z ∈ (fderiv ℝ polynomial (inclusion q)).kerᗮ := by
  intro v hv
  change fderiv ℝ polynomial (inclusion q) v = 0 at hv
  obtain ⟨hf, hi⟩ := (polynomial_kernel_iff q v).mp hv
  have hx : inner ℝ v (inclusion q) = 0 :=
    (inner_inclusion_of_first_zero q v hf).trans ((real_inner_comm _ _).trans hi)
  have hw : inner ℝ v (frame q z.2) = 0 := by
    rw [frame_apply]
    exact QuaternionicHopfSouthRegularity.inner_transverseAxis v hf _
  simp only [rawRightInverse_apply, inner_add_right, inner_smul_right, hx, hw,
    mul_zero, add_zero]

theorem rightInverse_range_orthogonal (q : Sphere 3) :
    (rightInverse q).range ≤ (fderiv ℝ polynomial (inclusion q)).kerᗮ := by
  rintro _ ⟨z, rfl⟩
  exact rawRightInverse_mem_orthogonal q ((SphereCylinder.join 3).symm z)

theorem canonical_rightInverse (q : Sphere 3) :
    orthogonalRightInverse (fderiv ℝ polynomial (inclusion q)) = rightInverse q :=
  orthogonalRightInverse_eq_of_rightInverse _ (polynomial_fderiv_surjective q)
    (rightInverse q) (polynomial_rightInverse q) (rightInverse_range_orthogonal q)

theorem contMDiff_inclusion : ContMDiff (𝓡 3) 𝓘(ℝ, V 8) ∞ inclusion := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact QuaternionicHopfSouthFiber.axis.contDiff.contMDiff.comp
    (contMDiff_coe_sphere (n := 3) (m := ∞))

theorem contMDiff_rightInverse :
    ContMDiff (𝓡 3) 𝓘(ℝ, V 5 →L[ℝ] V 8) ∞ rightInverse := by
  have hD : ContMDiff (𝓡 3) 𝓘(ℝ, V 8 →L[ℝ] V 5) ∞
      (fun q ↦ fderiv ℝ polynomial (inclusion q)) :=
    (contDiff_polynomial.fderiv_right (by simp)).contMDiff.comp contMDiff_inclusion
  have he : rightInverse = fun q ↦ orthogonalRightInverse (fderiv ℝ polynomial (inclusion q)) :=
    funext (fun q ↦ (canonical_rightInverse q).symm)
  rw [he]
  intro q
  exact contMDiffAt_orthogonalRightInverse (hD q) (polynomial_fderiv_surjective q)

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSouthPolynomialFrame

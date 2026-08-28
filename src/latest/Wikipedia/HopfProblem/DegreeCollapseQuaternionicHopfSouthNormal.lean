import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfSouthRegularity

/-!
# The actual south-fiber normal directions and their polynomial derivative

Right multiplication by the unit second coordinate gives four orthonormal
directions in the first quaternionic axis. They are tangent to the ambient
S7 and orthogonal to the actual fiber derivative. The original polynomial
takes these directions to twice the fixed target tangent coordinates.
Thus the normal directions and the positive derivative scale are explicit;
no geometric Arf value is assigned by definition.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSouthNormal

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfSouthRegularity

def frame (q : Sphere 3) : V 4 →L[ℝ] V 8 :=
  transverseAxis.comp
    (((ContinuousLinearMap.mul ℝ ℍ).flip
      (Quaternion.linearIsometryEquivTuple.symm q.val)).comp
        Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearMap)

theorem frame_apply (q : Sphere 3) (w : V 4) :
    frame q w = transverseAxis (Quaternion.linearIsometryEquivTuple.symm w *
      Quaternion.linearIsometryEquivTuple.symm q.val) := rfl

theorem frame_norm (q : Sphere 3) (w : V 4) : ‖frame q w‖ = ‖w‖ := by
  change ‖QuaternionicHopf.axis (Quaternion.linearIsometryEquivTuple
    (Quaternion.linearIsometryEquivTuple.symm w *
      Quaternion.linearIsometryEquivTuple.symm q.val))‖ = ‖w‖
  rw [QuaternionicHopf.axis.norm_map, Quaternion.linearIsometryEquivTuple.norm_map,
    norm_mul, Quaternion.linearIsometryEquivTuple.symm.norm_map,
    Quaternion.linearIsometryEquivTuple.symm.norm_map,
    mem_sphere_zero_iff_norm.mp q.property, mul_one]

def normalIsometry (q : Sphere 3) : V 4 →ₗᵢ[ℝ] V 8 where
  toLinearMap := (frame q).toLinearMap
  norm_map' := frame_norm q

theorem first_frame (q : Sphere 3) (w : V 4) :
    first (frame q w) = Quaternion.linearIsometryEquivTuple.symm w *
      Quaternion.linearIsometryEquivTuple.symm q.val := first_transverseAxis _

theorem second_frame (q : Sphere 3) (w : V 4) : second (frame q w) = 0 :=
  second_transverseAxis _

theorem contMDiff_frame :
    ContMDiff ((𝓡 3).prod 𝓘(ℝ, V 4)) 𝓘(ℝ, V 8) ∞
      (fun p : Sphere 3 × V 4 ↦ frame p.1 p.2) := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hb : ContMDiff ((𝓡 3).prod 𝓘(ℝ, V 4)) 𝓘(ℝ, ℍ) ∞
      (fun p : Sphere 3 × V 4 ↦ Quaternion.linearIsometryEquivTuple.symm p.1.val) :=
    Quaternion.linearIsometryEquivTuple.symm.contDiff.contMDiff.comp
      (contMDiff_coe_sphere.comp contMDiff_fst)
  have hw : ContMDiff ((𝓡 3).prod 𝓘(ℝ, V 4)) 𝓘(ℝ, ℍ) ∞
      (fun p : Sphere 3 × V 4 ↦ Quaternion.linearIsometryEquivTuple.symm p.2) :=
    Quaternion.linearIsometryEquivTuple.symm.contDiff.contMDiff.comp contMDiff_snd
  have hm : ContMDiff 𝓘(ℝ, ℍ × ℍ) 𝓘(ℝ, ℍ) ∞
      (fun p : ℍ × ℍ ↦ p.1 * p.2) := contDiff_mul.contMDiff
  exact transverseAxis.contDiff.contMDiff.comp (hm.comp (hw.prodMk_space hb))

theorem inner_frame_axis (q : Sphere 3) (w v : V 4) :
    inner ℝ (QuaternionicHopfSouthFiber.axis v) (frame q w) = 0 :=
  inner_transverseAxis _ (QuaternionicHopfSouthFiber.first_axis v) _

theorem frame_tangent_sphere (q : Sphere 3) (w : V 4) :
    inner ℝ (QuaternionicHopfSouthFiber.fiberPoint q).val (frame q w) = 0 :=
  inner_frame_axis q w q.val

theorem fiberPoint_ambient_mfderiv (q : Sphere 3) (v : V 3) :
    mfderiv (𝓡 3) 𝓘(ℝ, V 8)
      (fun x : Sphere 3 ↦ (QuaternionicHopfSouthFiber.fiberPoint x).val) q v =
        QuaternionicHopfSouthFiber.axis
          (mfderiv (𝓡 3) 𝓘(ℝ, V 4) (Subtype.val : Sphere 3 → V 4) q v) := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) 𝓘(ℝ, V 4) ∞ (Subtype.val : Sphere 3 → V 4) :=
    contMDiff_coe_sphere
  change mfderiv (𝓡 3) 𝓘(ℝ, V 8)
    (QuaternionicHopfSouthFiber.axis.toContinuousLinearMap ∘
      (Subtype.val : Sphere 3 → V 4)) q v = _
  rw [mfderiv_comp q
    QuaternionicHopfSouthFiber.axis.toContinuousLinearMap.differentiableAt.mdifferentiableAt
    (hs.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

theorem frame_orthogonal_fiber_derivative (q : Sphere 3) (w : V 4) (v : V 3) :
    inner ℝ (frame q w)
      (mfderiv (𝓡 3) 𝓘(ℝ, V 8)
        (fun x : Sphere 3 ↦ (QuaternionicHopfSouthFiber.fiberPoint x).val) q v : V 8)
      = 0 := by
  have he := congrArg (fun z : V 8 ↦ inner ℝ (frame q w) z)
    (fiberPoint_ambient_mfderiv q v)
  exact he.trans ((real_inner_comm _ _).trans (inner_frame_axis q w _))

theorem polynomial_derivative_frame (q : Sphere 3) (w : V 4) :
    fderiv ℝ polynomial (QuaternionicHopfSouthFiber.fiberPoint q).val (frame q w) =
      SphereCylinder.join 3 (0, (2 : ℝ) • w) := by
  rw [frame_apply, polynomial_fderiv_first _
    (QuaternionicHopfSouthFiber.first_fiberPoint q),
    QuaternionicHopfSouthFiber.second_fiberPoint]
  have hb := second_mul_star (QuaternionicHopfSouthFiber.fiberPoint q)
    (QuaternionicHopfSouthFiber.first_fiberPoint q)
  rw [QuaternionicHopfSouthFiber.second_fiberPoint] at hb
  rw [mul_assoc, hb, mul_one, map_smul, LinearIsometryEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSouthNormal

import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfCorrection
import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameAction
import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameConnecting

/-! # An actual Stiefel-frame lift for the corrected Clifford latitude cube -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open BalancedRealInvolutions

def hopfFrameFamily (A : Stiefel.Space 12 6) : C(EquatorSphere × ℝ, Stiefel.Space 12 6) :=
  ⟨fun p ↦ Stiefel.action (matrixOrthogonal (correctedRawHopfRotation p.1 p.2)) A,
    Stiefel.continuous_action _ _
      (continuous_matrixOrthogonal.comp continuous_correctedRawHopfRotation) continuous_const⟩

theorem hopfFrameFamily_zero (A : Stiefel.Space 12 6) (q : EquatorSphere) :
    hopfFrameFamily A (q, 0) = A := by
  change Stiefel.action (matrixOrthogonal (correctedRawHopfRotation q 0)) A = A
  rw [correctedRawHopfRotation_zero, map_one]
  exact Stiefel.action_identity A

theorem hopfFrameFamily_reference (A : Stiefel.Space 12 6) (θ : ℝ) :
    hopfFrameFamily A (equatorPole, θ) = A := by
  change Stiefel.action (matrixOrthogonal (correctedRawHopfRotation equatorPole θ)) A = A
  rw [correctedRawHopfRotation_reference, map_one]
  exact Stiefel.action_identity A

theorem hopfFrameFamily_project (A : Stiefel.Space 12 6)
    (hA : FrameProjection.toBalanced A = rawBalanced pole)
    (q : EquatorSphere) (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    FrameProjection.toBalanced (hopfFrameFamily A (q, θ)) =
      hopfCorrectedSphereMap (fourLatitudePoint θ q) := by
  change FrameProjection.toBalanced
    (Stiefel.action (matrixOrthogonal (correctedRawHopfRotation q θ)) A) = _
  rw [FrameProjection.toBalanced_action, hA]
  exact (hopfCorrectedSphereMap_latitude θ q h0 hπ).symm

def hopfLatitudeCube (p : GenLoop (Fin 3) EquatorSphere equatorPole) :
    GenLoop (Fin 4) (Space 6) (rawBalanced pole) where
  val := hopfCorrectedSphereMap.comp ⟨fun t ↦
    fourLatitudePoint ((t 0 : ℝ) * Real.pi) (p (Fin.tail t)),
    continuous_fourLatitudePoint.comp
      (((continuous_subtype_val.comp (continuous_apply 0)).mul_const Real.pi).prodMk
        (p.val.continuous.comp (continuous_pi (fun i ↦ continuous_apply i.succ))))⟩
  property t ht := by
    rcases (CubeFirstCoordinate.boundary_split_iff 3 t).mp ht with h0 | h1 | hp
    · change t 0 = 0 at h0
      change hopfCorrectedSphereMap (fourLatitudePoint ((t 0 : ℝ) * Real.pi) (p (Fin.tail t))) = _
      rw [h0]
      change hopfCorrectedSphereMap (fourLatitudePoint ((0 : ℝ) * Real.pi) (p (Fin.tail t))) = _
      rw [zero_mul, fourLatitudePoint_zero, hopfCorrectedSphereMap_pole]
    · change t 0 = 1 at h1
      change hopfCorrectedSphereMap (fourLatitudePoint ((t 0 : ℝ) * Real.pi) (p (Fin.tail t))) = _
      rw [h1]
      change hopfCorrectedSphereMap (fourLatitudePoint ((1 : ℝ) * Real.pi) (p (Fin.tail t))) = _
      rw [one_mul, hopfCorrectedSphereMap_pi]
    · change Fin.tail t ∈ Cube.boundary (Fin 3) at hp
      change hopfCorrectedSphereMap (fourLatitudePoint ((t 0 : ℝ) * Real.pi) (p (Fin.tail t))) = _
      have hpoint : p (Fin.tail t) = equatorPole := p.property _ hp
      rw [hpoint]
      exact hopfCorrectedSphereMap_reference _
        (mul_nonneg (t 0).property.1 Real.pi_pos.le) (by nlinarith [(t 0).property.2, Real.pi_pos])

def hopfLatitudeCubeAt (A : Stiefel.Space 12 6)
    (hA : FrameProjection.toBalanced A = rawBalanced pole)
    (p : GenLoop (Fin 3) EquatorSphere equatorPole) :
    GenLoop (Fin 4) (Space 6) (FrameProjection.toBalanced A) :=
  ⟨(hopfLatitudeCube p).val, fun t ht ↦ ((hopfLatitudeCube p).property t ht).trans hA.symm⟩

def hopfFrameLift (A : Stiefel.Space 12 6)
    (hA : FrameProjection.toBalanced A = rawBalanced pole)
    (p : GenLoop (Fin 3) EquatorSphere equatorPole) :
    FrameProjection.CubeLift A (hopfLatitudeCubeAt A hA p) where
  map := (hopfFrameFamily A).comp ⟨fun z : I × (Fin 3 → I) ↦ (p z.2, (z.1 : ℝ) * Real.pi),
    (p.val.continuous.comp continuous_snd).prodMk
      ((continuous_subtype_val.comp continuous_fst).mul_const Real.pi)⟩
  initial u := by
    change hopfFrameFamily A (p u, (0 : ℝ) * Real.pi) = A
    rw [zero_mul, hopfFrameFamily_zero]
  project t u := by
    change FrameProjection.toBalanced (hopfFrameFamily A (p u, (t : ℝ) * Real.pi)) =
      hopfCorrectedSphereMap (fourLatitudePoint ((t : ℝ) * Real.pi) (p u))
    exact hopfFrameFamily_project A hA (p u) _
      (mul_nonneg t.property.1 Real.pi_pos.le) (by nlinarith [t.property.2, Real.pi_pos])
  boundary t u hu := by
    change hopfFrameFamily A (p u, (t : ℝ) * Real.pi) = A
    have hpoint : p u = equatorPole := p.property u hu
    rw [hpoint, hopfFrameFamily_reference]

theorem hopfFrameLift_endpoint_operator (A : Stiefel.Space 12 6)
    (hA : FrameProjection.toBalanced A = rawBalanced pole)
    (p : GenLoop (Fin 3) EquatorSphere equatorPole) (u : Fin 3 → I) :
    ((hopfFrameLift A hA p).endpoint u).val.val =
      A.val.adjoint.comp
        ((matrixOrthogonal (correctedRawHopfRotation (p u) Real.pi)).val.val.comp A.val) := by
  refine (FrameProjection.coordinate_operator A ((hopfFrameLift A hA p).map (1, u))
    ((hopfFrameLift A hA p).endpoint_project u).symm).trans ?_
  change A.val.adjoint.comp
    ((matrixOrthogonal (correctedRawHopfRotation (p u) ((1 : ℝ) * Real.pi))).val.val.comp A.val) = _
  rw [one_mul]

theorem hopfLatitude_connecting (A : Stiefel.Space 12 6)
    (hA : FrameProjection.toBalanced A = rawBalanced pole)
    (p : GenLoop (Fin 3) EquatorSphere equatorPole) :
    FrameProjection.connecting A 3
      (⟦hopfLatitudeCubeAt A hA p⟧ : π_ 4 (Space 6) (FrameProjection.toBalanced A)) =
        (⟦(hopfFrameLift A hA p).endpoint⟧ : π_ 3 (OrthogonalOperators 6) 1) :=
  FrameProjection.connecting_eq_endpoint A (hopfLatitudeCubeAt A hA p) (hopfFrameLift A hA p)

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

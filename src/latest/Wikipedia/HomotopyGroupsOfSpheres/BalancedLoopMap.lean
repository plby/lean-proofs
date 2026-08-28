import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumPathFamily
import Wikipedia.HomotopyGroupsOfSpheres.BalancedReferenceCongruence

/-!
# The based loop map from balanced real involutions

Congruence by half of the diagonal reference path identifies antipodal
paths with based loops in the actual symmetric special-unitary space.
The balanced standard involution is sent to the constant loop.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open QuaternionicSymmetricMatrices

def halfAngle (t : I) : ℝ := (t : ℝ) * Real.pi / 2

theorem continuous_halfAngle : Continuous halfAngle :=
  (continuous_subtype_val.mul_const Real.pi).div_const 2

private def referenceActionMap (n : ℕ) :
    C(ℝ × SpecialSpace (Index n), SpecialSpace (Index n)) :=
  ⟨fun z ↦ referenceAction n z.1 z.2, continuous_referenceAction n⟩

private def actionFamily {X : Type*} [TopologicalSpace X] (n : ℕ)
    (θ : C(X, ℝ)) (B : C(X, SpecialSpace (Index n))) : C(X, SpecialSpace (Index n)) :=
  (referenceActionMap n).comp
    ⟨fun x ↦ (θ x, B x), θ.continuous.prodMk B.continuous⟩

def toLoop (n : ℕ) (p : Path specialIdentity (antipode n)) :
    Path (specialIdentity : SpecialSpace (Index n)) specialIdentity where
  toContinuousMap :=
    actionFamily n ⟨fun t ↦ -halfAngle t, continuous_halfAngle.neg⟩ p.toContinuousMap
  source' := by
    change referenceAction n (-halfAngle 0) (p 0) = specialIdentity
    rw [Path.source]
    change referenceAction n (-((0 : ℝ) * Real.pi / 2)) specialIdentity = specialIdentity
    simp only [zero_mul, zero_div, neg_zero, referenceAction_zero]
  target' := by
    change referenceAction n (-halfAngle 1) (p 1) = specialIdentity
    rw [Path.target]
    change referenceAction n (-((1 : ℝ) * Real.pi / 2)) (diagonalSpecial n Real.pi) = _
    rw [one_mul, referenceAction_diagonal,
      show 2 * -(Real.pi / 2) + Real.pi = 0 by ring, diagonalSpecial_zero]

def fromLoop (n : ℕ) (p : Path (specialIdentity : SpecialSpace (Index n)) specialIdentity) :
    Path specialIdentity (antipode n) where
  toContinuousMap := actionFamily n ⟨halfAngle, continuous_halfAngle⟩ p.toContinuousMap
  source' := by
    change referenceAction n (halfAngle 0) (p 0) = specialIdentity
    rw [Path.source]
    change referenceAction n ((0 : ℝ) * Real.pi / 2) specialIdentity = specialIdentity
    simp only [zero_mul, zero_div, referenceAction_zero]
  target' := by
    change referenceAction n (halfAngle 1) (p 1) = antipode n
    rw [Path.target, ← diagonalSpecial_zero n, referenceAction_diagonal]
    change diagonalSpecial n (2 * ((1 : ℝ) * Real.pi / 2) + 0) = diagonalSpecial n Real.pi
    congr 1
    ring

theorem continuous_toLoop (n : ℕ) : Continuous (toLoop n) := by
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : Path specialIdentity (antipode n) × I ↦
    referenceAction n (-halfAngle z.2) (z.1 z.2))
  let θ : C(Path specialIdentity (antipode n) × I, ℝ) :=
    ⟨fun z ↦ -halfAngle z.2, (continuous_halfAngle.comp continuous_snd).neg⟩
  let B : C(Path specialIdentity (antipode n) × I, SpecialSpace (Index n)) :=
    ⟨fun z ↦ z.1 z.2, continuous_eval⟩
  exact (actionFamily n θ B).continuous

theorem continuous_fromLoop (n : ℕ) : Continuous (fromLoop n) := by
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : Path (specialIdentity : SpecialSpace (Index n)) specialIdentity × I ↦
    referenceAction n (halfAngle z.2) (z.1 z.2))
  let θ : C(Path (specialIdentity : SpecialSpace (Index n)) specialIdentity × I, ℝ) :=
    ⟨fun z ↦ halfAngle z.2, continuous_halfAngle.comp continuous_snd⟩
  let B : C(Path (specialIdentity : SpecialSpace (Index n)) specialIdentity × I,
      SpecialSpace (Index n)) := ⟨fun z ↦ z.1 z.2, continuous_eval⟩
  exact (actionFamily n θ B).continuous

theorem fromLoop_toLoop (n : ℕ) (p : Path specialIdentity (antipode n)) :
    fromLoop n (toLoop n p) = p := by
  apply Path.ext
  funext t
  change referenceAction n (halfAngle t) (referenceAction n (-halfAngle t) (p t)) = p t
  rw [referenceAction_add, add_neg_cancel, referenceAction_zero]

theorem toLoop_fromLoop (n : ℕ)
    (p : Path (specialIdentity : SpecialSpace (Index n)) specialIdentity) :
    toLoop n (fromLoop n p) = p := by
  apply Path.ext
  funext t
  exact referenceAction_cancel n (halfAngle t) (p t)

def loopHomeomorph (n : ℕ) :
    Path specialIdentity (antipode n) ≃ₜ
      Path (specialIdentity : SpecialSpace (Index n)) specialIdentity where
  toFun := toLoop n
  invFun := fromLoop n
  left_inv := fromLoop_toLoop n
  right_inv := toLoop_fromLoop n
  continuous_toFun := continuous_toLoop n
  continuous_invFun := continuous_fromLoop n

theorem toLoop_reference (n : ℕ) :
    toLoop n (pathMap n (standard n)) = Path.refl specialIdentity := by
  apply Path.ext
  funext t
  change referenceAction n (-halfAngle t) (rotation (standard n) ((t : ℝ) * Real.pi)) =
    specialIdentity
  simpa only [halfAngle, neg_div] using referenceAction_reference n ((t : ℝ) * Real.pi)

def loopMap (n : ℕ) :
    C(Space n, Path (specialIdentity : SpecialSpace (Index n)) specialIdentity) :=
  (toContinuousMap (loopHomeomorph n)).comp (pathMap n)

theorem loopMap_reference (n : ℕ) : loopMap n (standard n) = Path.refl specialIdentity :=
  toLoop_reference n

theorem loopMap_injective (n : ℕ) : Function.Injective (loopMap n) :=
  (loopHomeomorph n).injective.comp (pathMap_injective n)

theorem loopMap_isClosedEmbedding (n : ℕ) : Topology.IsClosedEmbedding (loopMap n) :=
  (loopMap n).continuous.isClosedEmbedding (loopMap_injective n)

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

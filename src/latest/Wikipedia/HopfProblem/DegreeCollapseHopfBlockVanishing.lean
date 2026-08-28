import Wikipedia.HopfProblem.DegreeCollapseHopfBlockCoordinates
import Wikipedia.HopfProblem.DegreeCollapseOrthogonalHopfFourVanishing

/-!
# Nullity after adding twelve actual radial suspension coordinates

For an arbitrary S4-to-O(4) family, adjoin the identity on R12 and
use explicit orthonormal coordinates to obtain an S4-to-O(16) family.
Its Hopf map is already known to be null. The exact coordinate square
and the normalized block homotopy give nullity of the twelve-coordinate
radial suspension formula. Comparison with the original iterated
cubical product suspensions remains a separate proof obligation.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.HopfBlockVanishing

open OrthogonalHopfMap HopfBlockGeometry HopfBlockCoordinates

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] {n q : ℕ}

def parameterize (f : C(UnitSphere E, OrthogonalOperators n)) :
    C(Unit × UnitSphere E, OrthogonalOperators n) := f.comp ⟨Prod.snd, continuous_snd⟩

def blockSphereMap (f : C(UnitSphere E, OrthogonalOperators n)) :
    C(UnitSphere (Triple E (Vector n) G), UnitSphere (Triple ℝ (Vector n) G)) :=
  (blockMap (parameterize f)).comp ⟨fun x ↦ ((), x), continuous_const.prodMk continuous_id⟩

def suspendedSphereMap (f : C(UnitSphere E, OrthogonalOperators n)) :
    C(UnitSphere (Triple E (Vector n) G), UnitSphere (Triple ℝ (Vector n) G)) :=
  (suspendedMap (parameterize f)).comp ⟨fun x ↦ ((), x), continuous_const.prodMk continuous_id⟩

def blockSphereHomotopy (f : C(UnitSphere E, OrthogonalOperators n)) :
    (blockSphereMap (G := G) f).Homotopy (suspendedSphereMap (G := G) f) :=
  (HopfBlockHomotopy.blockHomotopy (parameterize f)).compContinuousMap
    ⟨fun x ↦ ((), x), continuous_const.prodMk continuous_id⟩

theorem sphereMap_coordinates (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q)
    (f : C(UnitSphere E, OrthogonalOperators n)) (x : UnitSphere (Triple E (Vector n) G)) :
    sphereMap ((blockOperatorMap e).comp f) (unitSphereCoordinates (coordinates e) x) =
      unitSphereCoordinates (coordinates (E := ℝ) e) (blockSphereMap f x) :=
  Subtype.ext (vector_coordinates e (parameterize f) () x.val)

theorem block_nullhomotopic_of_enlarged (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q)
    (f : C(UnitSphere E, OrthogonalOperators n))
    (h : (sphereMap ((blockOperatorMap e).comp f)).Nullhomotopic) :
    (blockSphereMap (G := G) f).Nullhomotopic := by
  obtain ⟨c, ⟨H⟩⟩ := h
  let φ := unitSphereCoordinates (coordinates (E := E) e)
  let ψ := unitSphereCoordinates (coordinates (E := ℝ) e)
  refine ⟨ψ.symm c, ⟨{
    toFun := fun z ↦ ψ.symm (H (z.1, φ z.2))
    continuous_toFun := ψ.symm.continuous.comp
      (H.continuous.comp (continuous_fst.prodMk (φ.continuous.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro x
    rw [H.apply_zero]
    change ψ.symm (sphereMap ((blockOperatorMap e).comp f)
      (unitSphereCoordinates (coordinates e) x)) = blockSphereMap f x
    rw [sphereMap_coordinates]
    exact ψ.symm_apply_apply (blockSphereMap f x)
  · intro x
    change ψ.symm (H (1, φ x)) = ψ.symm c
    rw [H.apply_one]
    rfl

theorem suspended_nullhomotopic_of_enlarged
    (e : WithLp 2 (Vector n × G) ≃ₗᵢ[ℝ] Vector q)
    (f : C(UnitSphere E, OrthogonalOperators n))
    (h : (sphereMap ((blockOperatorMap e).comp f)).Nullhomotopic) :
    (suspendedSphereMap (G := G) f).Nullhomotopic := by
  obtain ⟨c, ⟨H⟩⟩ := block_nullhomotopic_of_enlarged e f h
  exact ⟨c, ⟨(blockSphereHomotopy f).symm.trans H⟩⟩

def fourTwelveCoordinates : WithLp 2 (Vector 4 × Vector 12) ≃ₗᵢ[ℝ] Vector 16 :=
  ((EuclideanSpace.basisFun (Fin 4) ℝ).prod (EuclideanSpace.basisFun (Fin 12) ℝ)).equiv
    (EuclideanSpace.basisFun (Fin 16) ℝ) finSumFinEquiv

theorem four_twelve_radial_suspension_nullhomotopic (f : C(Sphere 4, OrthogonalOperators 4)) :
    (suspendedSphereMap (G := Vector 12) f).Nullhomotopic :=
  suspended_nullhomotopic_of_enlarged fourTwelveCoordinates f
    ⟨pole 16, four_hopf_nullhomotopic ((blockOperatorMap fourTwelveCoordinates).comp f)⟩

end Wikipedia.HopfProblem.DegreeCollapse.HopfBlockVanishing

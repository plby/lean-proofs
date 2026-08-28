import Wikipedia.NoExoticSixSphere.RelativeFiberMap
import Wikipedia.NoExoticSixSphere.HomotopyFiberConnectivity

/-!
# The actual pair in the contractible ending-path space

The source-evaluation preimage of the original subspace is homeomorphic
to the original inclusion fiber. Shortening paths gives a section into
the new inclusion fiber. Evaluating this section recovers each original
fiber point and each original path exactly.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.EndingPathPair

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def subspace : Set (EndingPath.Space a.val) := {p | EndingPath.source a.val p ∈ U}

def basepoint : subspace U a := ⟨EndingPath.constant a.val, a.property⟩

def homeomorph : Fiber U a ≃ₜ subspace U a where
  toFun p := ⟨⟨p.val.2, p.property.2⟩, by
    change p.val.2 0 ∈ U
    rw [p.property.1]
    exact p.val.1.property⟩
  invFun p := ⟨(⟨p.val.val 0, p.property⟩, p.val.val), rfl, p.val.property⟩
  left_inv p := Subtype.ext (Prod.ext (Subtype.ext p.property.1) rfl)
  right_inv p := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_snd.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (((EndingPath.source a.val).continuous.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_subtype_val.comp continuous_subtype_val)

theorem homeomorph_basepoint :
    homeomorph U a (HomotopyFiber.basepoint (subtypeInclusion U) a) = basepoint U a := rfl

def evaluation : C(EndingPath.Space a.val, X) := EndingPath.source a.val

theorem evaluation_mapsTo : Set.MapsTo (evaluation U a) (subspace U a) U := fun _ hp ↦ hp

theorem evaluation_basepoint : evaluation U a (basepoint U a).val = a.val := rfl

def fiberEvaluation : C(Fiber (subspace U a) (basepoint U a), Fiber U a) :=
  RelativeFiberMap.map (evaluation U a) (evaluation_mapsTo U a) (basepoint U a) a rfl

def sectionHomotopy :
    ((subtypeInclusion (subspace U a)).comp ⟨homeomorph U a, (homeomorph U a).continuous⟩).Homotopy
      (ContinuousMap.const (Fiber U a) (basepoint U a).val) :=
  (EndingPath.contraction (y₀ := a.val)).compContinuousMap
    ((subtypeInclusion (subspace U a)).comp ⟨homeomorph U a, (homeomorph U a).continuous⟩)

def liftSection : C(Fiber U a, Fiber (subspace U a) (basepoint U a)) :=
  HomotopyFiber.lift (subtypeInclusion (subspace U a)) (basepoint U a).val
    ⟨homeomorph U a, (homeomorph U a).continuous⟩ (sectionHomotopy U a)

theorem projection_liftSection :
    (HomotopyFiber.projection (subtypeInclusion (subspace U a)) (basepoint U a).val).comp
        (liftSection U a) = ⟨homeomorph U a, (homeomorph U a).continuous⟩ := rfl

theorem evaluation_liftSection :
    (fiberEvaluation U a).comp (liftSection U a) = ContinuousMap.id (Fiber U a) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext p.property.1
  · ext t
    change p.val.2 (EndingPath.remainingTime t 0) = p.val.2 t
    apply congrArg p.val.2
    apply Subtype.ext
    simp [EndingPath.remainingTime]

theorem subspace_simplyConnected [SimplyConnectedSpace (Fiber U a)] :
    SimplyConnectedSpace (subspace U a) :=
  (homeomorph U a).symm.toHomotopyEquiv.simplyConnectedSpace

end NoExoticSixSphere.EndingPathPair

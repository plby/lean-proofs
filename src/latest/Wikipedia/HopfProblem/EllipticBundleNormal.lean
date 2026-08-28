import Wikipedia.HopfProblem.EllipticBundleNormalTransitions
import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedCore

/-!
# The actual central normal line bundle and its character cocycle

Local coordinates are constructed on the actual normal tangent quotients,
using the inverse derivative of the filling covering. Their changes of
coordinates define the transition units below. The geometric derivative
calculation identifies those units with the transverse cyclic character.

The resulting `VectorBundleCore` is analytic and its fibres are explicitly
identified with the quotient of the ambient tangent space by the actual
inclusion differential. Every local bundle trivialization agrees with the
corresponding normal tangent coordinate. Thus this is a geometric normal
bundle identification, not merely a new name for a character bundle.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.NormalBundle

open HolomorphicCharacterBundle

variable (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)

/-- An actual local lift of the central surface covering. -/
def lift (i : Surface j (centralPeriod j) v hv) :
    OpenPartialHomeomorph (Surface j (centralPeriod j) v hv) (centralPeriod j).val.Torus := by
  letI := affineAction j (centralPeriod j) v hv.1
  exact AssociatedCore.lift (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv) i

def baseSet (i : Surface j (centralPeriod j) v hv) : Set (Surface j (centralPeriod j) v hv) :=
  (lift j v hv i).source

theorem isOpen_baseSet (i : Surface j (centralPeriod j) v hv) : IsOpen (baseSet j v hv i) :=
  (lift j v hv i).open_source

theorem mem_baseSet (i : Surface j (centralPeriod j) v hv) : i ∈ baseSet j v hv i := by
  let := affineAction j (centralPeriod j) v hv.1
  exact AssociatedCore.mem_baseSet (surfaceProjection_isQuotientCoveringMap
    j (centralPeriod j) v hv) i

theorem lift_project (i : Surface j (centralPeriod j) v hv)
    {x : Surface j (centralPeriod j) v hv} (hx : x ∈ baseSet j v hv i) :
    surfaceProjection j (centralPeriod j) v hv (lift j v hv i x) = x := by
  let := affineAction j (centralPeriod j) v hv.1
  exact AssociatedCore.lift_project (surfaceProjection_isQuotientCoveringMap
    j (centralPeriod j) v hv) i hx

/-- The scalar coordinate on the genuine normal quotient supplied by a
local covering lift and the actual inverse covering differential. -/
def localCoordinate (i x : Surface j (centralPeriod j) v hv) (hx : x ∈ baseSet j v hv i) :
    CentralNormalFibre j v hv x ≃ₗ[ℂ] ℂ :=
  normalCoordinateAtLift j v hv (lift j v hv i x) x (lift_project j v hv i hx)

@[simp] theorem localCoordinate_mk (i x : Surface j (centralPeriod j) v hv)
    (hx : x ∈ baseSet j v hv i) (w : FamilyModel) :
    localCoordinate j v hv i x hx (Submodule.Quotient.mk w) =
      ((fillingDerivativeEquiv j v hv (centralInclusion j (lift j v hv i x))).symm w).1 :=
  normalCoordinateAtLift_mk j v hv _ _ _ _

theorem coordinateChange_one_ne_zero (i k x : Surface j (centralPeriod j) v hv)
    (hx : x ∈ baseSet j v hv i ∩ baseSet j v hv k) :
    localCoordinate j v hv k x hx.2 ((localCoordinate j v hv i x hx.1).symm 1) ≠ 0 := by
  intro h
  have hz : (localCoordinate j v hv i x hx.1).symm 1 = 0 :=
    (localCoordinate j v hv k x hx.2).injective
      (h.trans (localCoordinate j v hv k x hx.2).map_zero.symm)
  have he := congrArg (localCoordinate j v hv i x hx.1) hz
  exact one_ne_zero (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using he)

/-- The unit transition is defined by the actual change of normal tangent
coordinates, evaluated at one. The extension off an overlap is irrelevant. -/
def transition (i k x : Surface j (centralPeriod j) v hv) : ℂˣ := by
  classical
  exact if hx : x ∈ baseSet j v hv i ∩ baseSet j v hv k then
    Units.mk0
      (localCoordinate j v hv k x hx.2 ((localCoordinate j v hv i x hx.1).symm 1))
      (coordinateChange_one_ne_zero j v hv i k x hx)
    else 1

theorem transition_val_of_mem (i k x : Surface j (centralPeriod j) v hv)
    (hx : x ∈ baseSet j v hv i ∩ baseSet j v hv k) :
    (transition j v hv i k x : ℂ) =
      localCoordinate j v hv k x hx.2 ((localCoordinate j v hv i x hx.1).symm 1) := by
  classical
  unfold transition
  rw [dif_pos hx]
  rfl

theorem transition_of_not_mem (i k x : Surface j (centralPeriod j) v hv)
    (hx : x ∉ baseSet j v hv i ∩ baseSet j v hv k) : transition j v hv i k x = 1 := by
  classical
  unfold transition
  rw [dif_neg hx]

/-- The differential calculation identifies the independently defined
normal transition with the actual covering's character cocycle. -/
theorem transition_eq_character (i k x : Surface j (centralPeriod j) v hv) :
    letI := affineAction j (centralPeriod j) v hv.1
    transition j v hv i k x = normalCharacter j
      (AssociatedCore.deck (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
        i k x) := by
  let := affineAction j (centralPeriod j) v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv
  by_cases hx : x ∈ baseSet j v hv i ∩ baseSet j v hv k
  · apply Units.ext
    rw [transition_val_of_mem j v hv i k x hx]
    have h := normalCoordinateAtLift_change j v hv (lift j v hv i x) (lift j v hv k x)
      x (lift_project j v hv i hx.1) (lift_project j v hv k hx.2)
      (AssociatedCore.deck hq i k x) (AssociatedCore.deck_spec hq i k hx)
      ((localCoordinate j v hv i x hx.1).symm 1)
    simpa only [localCoordinate, LinearEquiv.apply_symm_apply, mul_one] using h
  · rw [transition_of_not_mem j v hv i k x hx]
    change x ∉ AssociatedCore.baseSet hq i ∩ AssociatedCore.baseSet hq k at hx
    rw [AssociatedCore.deck, dif_neg hx, map_one]

/-- The normal tangent coordinates transform by these actual transitions. -/
theorem localCoordinate_change (i k x : Surface j (centralPeriod j) v hv)
    (hx : x ∈ baseSet j v hv i ∩ baseSet j v hv k) (n : CentralNormalFibre j v hv x) :
    localCoordinate j v hv k x hx.2 n = (transition j v hv i k x : ℂ) *
      localCoordinate j v hv i x hx.1 n := by
  let := affineAction j (centralPeriod j) v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv
  rw [transition_eq_character]
  exact normalCoordinateAtLift_change j v hv (lift j v hv i x) (lift j v hv k x)
    x (lift_project j v hv i hx.1) (lift_project j v hv k hx.2)
    (AssociatedCore.deck hq i k x) (AssociatedCore.deck_spec hq i k hx) n

/-- The normal line bundle's actual transition data, constructed from its
normal tangent coordinates. -/
def data :
    TransitionData (Surface j (centralPeriod j) v hv) (Surface j (centralPeriod j) v hv) := by
  letI := affineAction j (centralPeriod j) v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv
  exact
    { baseSet := baseSet j v hv
      isOpen_baseSet := isOpen_baseSet j v hv
      indexAt := id
      mem_baseSet_at := mem_baseSet j v hv
      transition := transition j v hv
      transition_self := fun i x hx => by
        rw [transition_eq_character, AssociatedCore.deck_self hq i hx, map_one]
      transition_comp := fun i k l x hx => by
        rw [transition_eq_character, transition_eq_character, transition_eq_character,
          ← map_mul, AssociatedCore.deck_comp hq i k l hx]
      continuousOn_transition := fun i k => by
        apply ((AssociatedCore.data hq (normalCharacter j)).continuousOn_transition i k).congr
        intro x hx
        exact congrArg Units.val (transition_eq_character j v hv i k x) }

private theorem transitionData_ext {M ι : Type*} [TopologicalSpace M]
    (A B : TransitionData M ι) (hbase : A.baseSet = B.baseSet)
    (hindex : A.indexAt = B.indexAt) (htransition : A.transition = B.transition) : A = B := by
  cases A
  cases B
  cases hbase
  cases hindex
  cases htransition
  rfl

/-- Identification with the character bundle is a theorem about the
independently computed normal-coordinate transition data. -/
theorem data_eq_associated :
    letI := affineAction j (centralPeriod j) v hv.1
    data j v hv = AssociatedCore.data
      (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv) (normalCharacter j) := by
  let := affineAction j (centralPeriod j) v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv
  have ht : transition j v hv =
      fun i k x => normalCharacter j (AssociatedCore.deck hq i k x) := by
    funext i k x
    exact transition_eq_character j v hv i k x
  exact transitionData_ext _ _ rfl rfl ht

instance data_isHolomorphic :
    (data j v hv).IsHolomorphic (modelWithCornersSelf ℂ ComplexPlane₂) := by
  let := affineAction j (centralPeriod j) v hv.1
  rw [data_eq_associated]
  infer_instance

/-- The analytic line bundle made from the actual normal tangent coordinates. -/
abbrev core := (data j v hv).core

theorem holomorphicVectorBundle :
    ContMDiffVectorBundle ω ℂ (core j v hv).Fiber (modelWithCornersSelf ℂ ComplexPlane₂) :=
  inferInstance

/-- Every fibre of the constructed bundle is identified with the literal
normal quotient by the actual inclusion's tangent image. -/
def fibreIdentification (x : Surface j (centralPeriod j) v hv) :
    (core j v hv).Fiber x ≃ₗ[ℂ] CentralNormalFibre j v hv x := by
  change ℂ ≃ₗ[ℂ] CentralNormalFibre j v hv x
  exact (localCoordinate j v hv x x (mem_baseSet j v hv x)).symm

/-- Every bundle chart agrees with the corresponding geometric normal
coordinate, not only the preferred chart used to represent its fibre. -/
theorem localCoordinate_fibreIdentification (i x : Surface j (centralPeriod j) v hv)
    (hx : x ∈ baseSet j v hv i) (z : (core j v hv).Fiber x) :
    localCoordinate j v hv i x hx (fibreIdentification j v hv x z) =
      ((core j v hv).localTriv i ⟨x, z⟩).2 := by
  change localCoordinate j v hv i x hx
      ((localCoordinate j v hv x x (mem_baseSet j v hv x)).symm z) =
    (transition j v hv x i x : ℂ) * id (α := ℂ) z
  have h := localCoordinate_change j v hv x i x ⟨mem_baseSet j v hv x, hx⟩
    ((localCoordinate j v hv x x (mem_baseSet j v hv x)).symm z)
  exact h.trans (congrArg (fun a : ℂ => (transition j v hv x i x : ℂ) * a)
    ((localCoordinate j v hv x x (mem_baseSet j v hv x)).apply_symm_apply
      (id (α := ℂ) z)))

end Wikipedia.HopfProblem.Elliptic.NormalBundle

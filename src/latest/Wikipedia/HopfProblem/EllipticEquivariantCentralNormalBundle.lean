import Wikipedia.HopfProblem.EllipticEquivariantCentralNormalTransitions
import Wikipedia.HopfProblem.EllipticBundleCoreCriterion
import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedCoreTensor

/-!
# The genuine central normal line of any equivariant period family

Local coordinates are constructed on the actual normal tangent quotients,
using the inverse derivative of the filling covering. Their changes of
coordinates define the transition units below. The geometric derivative
calculation for the supplied varying-period atlas identifies those units with
the transverse cyclic character.

The actual central surface retains its native fixed-period quotient atlas.
The resulting `VectorBundleCore` is analytic and its fibres are explicitly
identified with the quotient of the ambient tangent space by the actual
inclusion differential. Every local bundle trivialization agrees with the
corresponding normal tangent coordinate. Thus this is a geometric normal
bundle identification, not merely a new name for a character bundle.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.NormalBundle

open HolomorphicCharacterBundle

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IB" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ℂ)
local notation "IA" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

variable {j : Kind} (D : Equivariant.Data j) (v : Lattice) (hv : AdmissibleTwist j v)

/-- An actual local lift of the central surface covering. -/
def lift (i : Surface j D.centralPeriod v hv) :
    OpenPartialHomeomorph (Surface j D.centralPeriod v hv) D.centralPeriod.val.Torus := by
  letI := affineAction j D.centralPeriod v hv.1
  exact AssociatedCore.lift (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv) i

def baseSet (i : Surface j D.centralPeriod v hv) : Set (Surface j D.centralPeriod v hv) :=
  (lift D v hv i).source

theorem isOpen_baseSet (i : Surface j D.centralPeriod v hv) : IsOpen (baseSet D v hv i) :=
  (lift D v hv i).open_source

theorem mem_baseSet (i : Surface j D.centralPeriod v hv) : i ∈ baseSet D v hv i := by
  let := affineAction j D.centralPeriod v hv.1
  exact AssociatedCore.mem_baseSet (surfaceProjection_isQuotientCoveringMap
    j D.centralPeriod v hv) i

theorem lift_project (i : Surface j D.centralPeriod v hv)
    {x : Surface j D.centralPeriod v hv} (hx : x ∈ baseSet D v hv i) :
    surfaceProjection j D.centralPeriod v hv (lift D v hv i x) = x := by
  let := affineAction j D.centralPeriod v hv.1
  exact AssociatedCore.lift_project (surfaceProjection_isQuotientCoveringMap
    j D.centralPeriod v hv) i hx

/-- The scalar coordinate on the genuine normal quotient supplied by a
local covering lift and the actual inverse covering differential. -/
def localCoordinate (i x : Surface j D.centralPeriod v hv) (hx : x ∈ baseSet D v hv i) :
    CentralNormalFibre D v hv x ≃ₗ[ℂ] ℂ :=
  normalCoordinateAtLift D v hv (lift D v hv i x) x (lift_project D v hv i hx)

@[simp] theorem localCoordinate_mk (i x : Surface j D.centralPeriod v hv)
    (hx : x ∈ baseSet D v hv i) (w : FamilyModel) :
    localCoordinate D v hv i x hx (Submodule.Quotient.mk w) =
      ((fillingDerivativeEquiv D v hv (centralInclusion D (lift D v hv i x))).symm w).1 :=
  normalCoordinateAtLift_mk D v hv _ _ _ _

theorem coordinateChange_one_ne_zero (i k x : Surface j D.centralPeriod v hv)
    (hx : x ∈ baseSet D v hv i ∩ baseSet D v hv k) :
    localCoordinate D v hv k x hx.2 ((localCoordinate D v hv i x hx.1).symm 1) ≠ 0 := by
  intro h
  have hz : (localCoordinate D v hv i x hx.1).symm 1 = 0 :=
    (localCoordinate D v hv k x hx.2).injective
      (h.trans (localCoordinate D v hv k x hx.2).map_zero.symm)
  have he := congrArg (localCoordinate D v hv i x hx.1) hz
  exact one_ne_zero (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using he)

/-- The unit transition is defined by the actual change of normal tangent
coordinates, evaluated at one. The extension off an overlap is irrelevant. -/
def transition (i k x : Surface j D.centralPeriod v hv) : ℂˣ := by
  classical
  exact if hx : x ∈ baseSet D v hv i ∩ baseSet D v hv k then
    Units.mk0
      (localCoordinate D v hv k x hx.2 ((localCoordinate D v hv i x hx.1).symm 1))
      (coordinateChange_one_ne_zero D v hv i k x hx)
    else 1

theorem transition_val_of_mem (i k x : Surface j D.centralPeriod v hv)
    (hx : x ∈ baseSet D v hv i ∩ baseSet D v hv k) :
    (transition D v hv i k x : ℂ) =
      localCoordinate D v hv k x hx.2 ((localCoordinate D v hv i x hx.1).symm 1) := by
  classical
  unfold transition
  rw [dif_pos hx]
  rfl

theorem transition_of_not_mem (i k x : Surface j D.centralPeriod v hv)
    (hx : x ∉ baseSet D v hv i ∩ baseSet D v hv k) : transition D v hv i k x = 1 := by
  classical
  unfold transition
  rw [dif_neg hx]

/-- The differential calculation identifies the independently defined
normal transition with the actual covering's character cocycle. -/
theorem transition_eq_character (i k x : Surface j D.centralPeriod v hv) :
    letI := affineAction j D.centralPeriod v hv.1
    transition D v hv i k x = normalCharacter j
      (AssociatedCore.deck (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv)
        i k x) := by
  let := affineAction j D.centralPeriod v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv
  by_cases hx : x ∈ baseSet D v hv i ∩ baseSet D v hv k
  · apply Units.ext
    rw [transition_val_of_mem D v hv i k x hx]
    have h := normalCoordinateAtLift_change D v hv (lift D v hv i x) (lift D v hv k x)
      x (lift_project D v hv i hx.1) (lift_project D v hv k hx.2)
      (AssociatedCore.deck hq i k x) (AssociatedCore.deck_spec hq i k hx)
      ((localCoordinate D v hv i x hx.1).symm 1)
    simpa only [localCoordinate, LinearEquiv.apply_symm_apply, mul_one] using h
  · rw [transition_of_not_mem D v hv i k x hx]
    change x ∉ AssociatedCore.baseSet hq i ∩ AssociatedCore.baseSet hq k at hx
    rw [AssociatedCore.deck, dif_neg hx, map_one]

/-- The normal tangent coordinates transform by these actual transitions. -/
theorem localCoordinate_change (i k x : Surface j D.centralPeriod v hv)
    (hx : x ∈ baseSet D v hv i ∩ baseSet D v hv k) (n : CentralNormalFibre D v hv x) :
    localCoordinate D v hv k x hx.2 n = (transition D v hv i k x : ℂ) *
      localCoordinate D v hv i x hx.1 n := by
  let := affineAction j D.centralPeriod v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv
  rw [transition_eq_character]
  exact normalCoordinateAtLift_change D v hv (lift D v hv i x) (lift D v hv k x)
    x (lift_project D v hv i hx.1) (lift_project D v hv k hx.2)
    (AssociatedCore.deck hq i k x) (AssociatedCore.deck_spec hq i k hx) n

/-- The normal line bundle's actual transition data, constructed from its
normal tangent coordinates. -/
def data :
    TransitionData (Surface j D.centralPeriod v hv) (Surface j D.centralPeriod v hv) := by
  letI := affineAction j D.centralPeriod v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv
  exact
    { baseSet := baseSet D v hv
      isOpen_baseSet := isOpen_baseSet D v hv
      indexAt := id
      mem_baseSet_at := mem_baseSet D v hv
      transition := transition D v hv
      transition_self := fun i x hx => by
        rw [transition_eq_character, AssociatedCore.deck_self hq i hx, map_one]
      transition_comp := fun i k l x hx => by
        rw [transition_eq_character, transition_eq_character, transition_eq_character,
          ← map_mul, AssociatedCore.deck_comp hq i k l hx]
      continuousOn_transition := fun i k => by
        apply ((AssociatedCore.data hq (normalCharacter j)).continuousOn_transition i k).congr
        intro x hx
        exact congrArg Units.val (transition_eq_character D v hv i k x) }

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
    letI := affineAction j D.centralPeriod v hv.1
    data D v hv = AssociatedCore.data
      (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv) (normalCharacter j) := by
  let := affineAction j D.centralPeriod v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv
  have ht : transition D v hv =
      fun i k x => normalCharacter j (AssociatedCore.deck hq i k x) := by
    funext i k x
    exact transition_eq_character D v hv i k x
  exact transitionData_ext _ _ rfl rfl ht

instance data_isHolomorphic :
    (data D v hv).IsHolomorphic (modelWithCornersSelf ℂ ComplexPlane₂) := by
  let := affineAction j D.centralPeriod v hv.1
  rw [data_eq_associated]
  infer_instance

/-- The analytic line bundle made from the actual normal tangent coordinates. -/
abbrev core := (data D v hv).core

theorem holomorphicVectorBundle :
    ContMDiffVectorBundle ω ℂ (core D v hv).Fiber (modelWithCornersSelf ℂ ComplexPlane₂) :=
  inferInstance

/-- Every fibre of the constructed bundle is identified with the literal
normal quotient by the actual inclusion's tangent image. -/
def fibreIdentification (x : Surface j D.centralPeriod v hv) :
    (core D v hv).Fiber x ≃ₗ[ℂ] CentralNormalFibre D v hv x := by
  change ℂ ≃ₗ[ℂ] CentralNormalFibre D v hv x
  exact (localCoordinate D v hv x x (mem_baseSet D v hv x)).symm

/-- Every bundle chart agrees with the corresponding geometric normal
coordinate, not only the preferred chart used to represent its fibre. -/
theorem localCoordinate_fibreIdentification (i x : Surface j D.centralPeriod v hv)
    (hx : x ∈ baseSet D v hv i) (z : (core D v hv).Fiber x) :
    localCoordinate D v hv i x hx (fibreIdentification D v hv x z) =
      ((core D v hv).localTriv i ⟨x, z⟩).2 := by
  change localCoordinate D v hv i x hx
      ((localCoordinate D v hv x x (mem_baseSet D v hv x)).symm z) =
    (transition D v hv x i x : ℂ) * id (α := ℂ) z
  have h := localCoordinate_change D v hv x i x ⟨mem_baseSet D v hv x, hx⟩
    ((localCoordinate D v hv x x (mem_baseSet D v hv x)).symm z)
  exact h.trans (congrArg (fun a : ℂ => (transition D v hv x i x : ℂ) * a)
    ((localCoordinate D v hv x x (mem_baseSet D v hv x)).apply_symm_apply
      (id (α := ℂ) z)))

theorem fibre_rank_one (x : Surface j D.centralPeriod v hv) :
    Module.finrank ℂ ((core D v hv).Fiber x) = 1 := by
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

theorem normalFibre_rank_one (x : Surface j D.centralPeriod v hv) :
    Module.finrank ℂ (D.CentralNormalFibre v hv x) = 1 :=
  (localCoordinate D v hv x x (mem_baseSet D v hv x)).finrank_eq.trans
    (Module.finrank_self ℂ)

theorem totalSpace_isManifold : IsManifold IB ω (core D v hv).TotalSpace :=
  inferInstance

/-- The independently constructed normal bundle is analytically identified
with the actual orbit quotient of the transverse character. The identification
uses the same scalar coordinates as the actual normal tangent quotient. -/
def associatedIdentification :
    letI := affineAction j D.centralPeriod v hv.1
    letI := associatedChartedSpace (E := ComplexPlane₂)
      (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv) (normalCharacter j)
    Diffeomorph IB IA (core D v hv).TotalSpace
      (AssociatedSpace (A := D.centralPeriod.val.Torus) (normalCharacter j)) ω := by
  letI := affineAction j D.centralPeriod v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv
  letI := associatedChartedSpace (E := ComplexPlane₂) hq (normalCharacter j)
  let e := AssociatedCore.identification hq (normalCharacter j)
    (affineAction_holomorphic j D.centralPeriod v hv.1)
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      contMDiff_toFun := by
        unfold core
        rw [data_eq_associated]
        exact e.contMDiff
      contMDiff_invFun := by
        unfold core
        rw [data_eq_associated]
        exact e.symm.contMDiff }

@[simp] theorem associatedIdentification_preserves_base (p : (core D v hv).TotalSpace) :
    letI := affineAction j D.centralPeriod v hv.1
    HolomorphicCharacterBundle.projection
      (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv)
      (normalCharacter j) (associatedIdentification D v hv p) = p.proj := by
  let := affineAction j D.centralPeriod v hv.1
  exact AssociatedCore.projection_toAssociated
    (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv) (normalCharacter j) p

/-- Every geometric normal coordinate agrees with the associated orbit
coordinate after the analytic bundle identification. -/
theorem associatedIdentification_localTriv (i : Surface j D.centralPeriod v hv)
    (p : (core D v hv).TotalSpace) (hp : p.proj ∈ baseSet D v hv i) :
    letI := affineAction j D.centralPeriod v hv.1
    associatedIdentification D v hv p = associatedMap (normalCharacter j)
      (lift D v hv i p.proj, ((core D v hv).localTriv i p).2) := by
  let := affineAction j D.centralPeriod v hv.1
  have he := AssociatedCore.toAssociated_localTriv
    (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv)
    (normalCharacter j) i p hp
  change _ = associatedMap (normalCharacter j)
    (lift D v hv i p.proj,
      ((AssociatedCore.data (surfaceProjection_isQuotientCoveringMap
        j D.centralPeriod v hv) (normalCharacter j)).core.localTriv i p).2) at he
  rw [← data_eq_associated] at he
  exact he

/-- The associated orbit of any actual normal vector is represented in
every covering lift by that vector's genuine geometric scalar coordinate. -/
theorem associatedIdentification_normalCoordinate
    (i x : Surface j D.centralPeriod v hv) (hx : x ∈ baseSet D v hv i)
    (n : D.CentralNormalFibre v hv x) :
    letI := affineAction j D.centralPeriod v hv.1
    associatedIdentification D v hv ⟨x, (fibreIdentification D v hv x).symm n⟩ =
      associatedMap (normalCharacter j)
        (lift D v hv i x, localCoordinate D v hv i x hx n) := by
  let := affineAction j D.centralPeriod v hv.1
  rw [associatedIdentification_localTriv D v hv i _ hx]
  congr 1
  apply Prod.ext
  · rfl
  · have he := localCoordinate_fibreIdentification D v hv i x hx
      ((fibreIdentification D v hv x).symm n)
    rw [LinearEquiv.apply_symm_apply] at he
    exact he.symm

/-- Tensor-power transition data for the genuinely constructed normal line. -/
def powerData (n : ℕ) :
    TransitionData (Surface j D.centralPeriod v hv) (Surface j D.centralPeriod v hv) := by
  letI := affineAction j D.centralPeriod v hv.1
  exact AssociatedCore.data
    (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv) (normalCharacter j ^ n)

instance powerData_isHolomorphic (n : ℕ) :
    (powerData D v hv n).IsHolomorphic IS := by
  let := affineAction j D.centralPeriod v hv.1
  change (AssociatedCore.data
    (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv)
      (normalCharacter j ^ n)).IsHolomorphic IS
  infer_instance

@[simp] theorem powerData_one : powerData D v hv 1 = data D v hv := by
  let := affineAction j D.centralPeriod v hv.1
  exact (congrArg
    (AssociatedCore.data (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv))
    (pow_one (normalCharacter j))).trans (data_eq_associated D v hv).symm

@[simp] theorem powerData_transition (n : ℕ) (i k x : Surface j D.centralPeriod v hv) :
    (powerData D v hv n).transition i k x = ((data D v hv).transition i k x) ^ n := by
  let := affineAction j D.centralPeriod v hv.1
  rw [data_eq_associated D v hv]
  exact AssociatedCore.data_pow_transition
    (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv)
      (normalCharacter j) n i k x

/-- Triviality is an actual base-preserving fibre-linear analytic product
identification of the tensor-power bundle, for the native surface atlas. -/
theorem power_analyticTrivialization_iff (n : ℕ) :
    Nonempty ((powerData D v hv n).AnalyticTrivialization IS) ↔ j.order ∣ n := by
  let := affineAction j D.centralPeriod v hv.1
  have h := BundleCore.characterCore_power_analyticTrivialization_iff
    (surfaceProjection_isQuotientCoveringMap j D.centralPeriod v hv)
      (normalCharacter j) (affineAction_holomorphic j D.centralPeriod v hv.1) n
  exact h.trans (by rw [normalCharacter_orderOf])

theorem order_isLeast :
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty ((powerData D v hv n).AnalyticTrivialization IS)} j.order := by
  refine ⟨⟨j.order_pos, (power_analyticTrivialization_iff D v hv j.order).mpr (dvd_refl _)⟩, ?_⟩
  intro n hn
  exact Nat.le_of_dvd hn.1 ((power_analyticTrivialization_iff D v hv n).mp hn.2)

theorem order_power_trivial :
    Nonempty ((powerData D v hv j.order).AnalyticTrivialization IS) :=
  (power_analyticTrivialization_iff D v hv j.order).mpr (dvd_refl _)

theorem not_analytically_trivial : ¬ Nonempty ((data D v hv).AnalyticTrivialization IS) := by
  intro h
  have h1 : Nonempty ((powerData D v hv 1).AnalyticTrivialization IS) := by
    simpa only [powerData_one] using h
  have hd := (power_analyticTrivialization_iff D v hv 1).mp h1
  cases j <;> norm_num [Kind.order] at hd

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.NormalBundle

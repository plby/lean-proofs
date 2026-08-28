import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticNormalQuotient

/-!
# The geometric elliptic normal lines in the global threefold

The local normal coordinates below are coordinates on the literal quotient
of the global ambient tangent space by the actual central inclusion's
differential. They use the inverse of the normal transport induced by the
genuine full-filling parametrization. Their transition units are defined by
evaluating these actual changes of normal coordinates at one.

The cancellation of the parametrization differential identifies those
independently constructed transitions with the local filling transitions.
This gives an analytic line bundle, continuous identifications of its fibres
with the natural global normal quotients, and the exact tensor orders three
and four. Every local bundle chart agrees with its geometric normal coordinate.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry.GlobalNormalBundle

open Elliptic EllipticFilling HolomorphicCharacterBundle

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IB" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ℂ)
local notation "IA" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

variable (j : Elliptic.Kind)

/-- The open covering inherited from actual lifts of the central surface. -/
abbrev baseSet (i : SpecialCentralSurface j) : Set (SpecialCentralSurface j) :=
  Equivariant.Data.NormalBundle.baseSet
    (specialLocalData j) j.twist (mainTwist_admissible j) i

theorem isOpen_baseSet (i : SpecialCentralSurface j) : IsOpen (baseSet j i) :=
  Equivariant.Data.NormalBundle.isOpen_baseSet
    (specialLocalData j) j.twist (mainTwist_admissible j) i

theorem mem_baseSet (i : SpecialCentralSurface j) : i ∈ baseSet j i :=
  Equivariant.Data.NormalBundle.mem_baseSet
    (specialLocalData j) j.twist (mainTwist_admissible j) i

/-- A local scalar coordinate on the genuine global differential quotient. -/
def localCoordinate (i x : SpecialCentralSurface j) (hx : x ∈ baseSet j i) :
    GlobalCentralNormalFibre j x ≃ₗ[ℂ] ℂ :=
  (normalTransportLinearEquiv j x).symm.trans
    (Equivariant.Data.NormalBundle.localCoordinate
      (specialLocalData j) j.twist (mainTwist_admissible j) i x hx)

/-- On an ambient tangent representative, the coordinate first applies
the inverse global parametrization differential and then the actual inverse
filling-covering differential. -/
@[simp] theorem localCoordinate_mk (i x : SpecialCentralSurface j)
    (hx : x ∈ baseSet j i) (w : Elliptic.FamilyModel) :
    localCoordinate j i x hx (Submodule.Quotient.mk w) =
      ((Equivariant.Data.fillingDerivativeEquiv
        (specialLocalData j) j.twist (mainTwist_admissible j)
        ((specialLocalData j).centralInclusion
          (Equivariant.Data.NormalBundle.lift
            (specialLocalData j) j.twist (mainTwist_admissible j) i x))).symm
        ((fullParametrizationDerivative j x).symm w)).1 := by
  change Equivariant.Data.NormalBundle.localCoordinate
    (specialLocalData j) j.twist (mainTwist_admissible j) i x hx
      ((normalTransportLinearEquiv j x).symm (Submodule.Quotient.mk w)) = _
  rw [normalTransportLinearEquiv_symm_mk]
  exact Equivariant.Data.NormalBundle.localCoordinate_mk
    (specialLocalData j) j.twist (mainTwist_admissible j) i x hx
      ((fullParametrizationDerivative j x).symm w)

/-- The global coordinate agrees with the local normal coordinate after
the actual parametrization differential, not an arbitrary identification. -/
@[simp] theorem localCoordinate_normalTransport (i x : SpecialCentralSurface j)
    (hx : x ∈ baseSet j i) (n : SpecialCentralNormalFibre j x) :
    localCoordinate j i x hx (normalTransportLinearEquiv j x n) =
      Equivariant.Data.NormalBundle.localCoordinate
        (specialLocalData j) j.twist (mainTwist_admissible j) i x hx n := by
  exact congrArg
    (Equivariant.Data.NormalBundle.localCoordinate
      (specialLocalData j) j.twist (mainTwist_admissible j) i x hx)
    ((normalTransportLinearEquiv j x).symm_apply_apply n)

/-- These coordinates preserve the pre-existing natural quotient topologies. -/
def localCoordinateContinuous (i x : SpecialCentralSurface j)
    (hx : x ∈ baseSet j i) : GlobalCentralNormalFibre j x ≃L[ℂ] ℂ :=
  (normalTransport j x).symm.trans
    (Equivariant.Data.NormalBundle.localCoordinateContinuous
      (specialLocalData j) j.twist (mainTwist_admissible j) i x hx)

@[simp] theorem localCoordinateContinuous_toLinearEquiv
    (i x : SpecialCentralSurface j) (hx : x ∈ baseSet j i) :
    (localCoordinateContinuous j i x hx).toLinearEquiv = localCoordinate j i x hx := rfl

theorem coordinateChange_eq_local (i k x : SpecialCentralSurface j)
    (hx : x ∈ baseSet j i ∩ baseSet j k) (z : ℂ) :
    localCoordinate j k x hx.2 ((localCoordinate j i x hx.1).symm z) =
      Equivariant.Data.NormalBundle.localCoordinate
        (specialLocalData j) j.twist (mainTwist_admissible j) k x hx.2
        ((Equivariant.Data.NormalBundle.localCoordinate
          (specialLocalData j) j.twist (mainTwist_admissible j) i x hx.1).symm z) := by
  exact localCoordinate_normalTransport j k x hx.2 _

theorem coordinateChange_one_ne_zero (i k x : SpecialCentralSurface j)
    (hx : x ∈ baseSet j i ∩ baseSet j k) :
    localCoordinate j k x hx.2 ((localCoordinate j i x hx.1).symm 1) ≠ 0 := by
  rw [coordinateChange_eq_local j i k x hx 1]
  exact Equivariant.Data.NormalBundle.coordinateChange_one_ne_zero
    (specialLocalData j) j.twist (mainTwist_admissible j) i k x hx

/-- The transition unit is computed from the actual global normal quotient
coordinates. Its value outside an overlap is immaterial. -/
def transition (i k x : SpecialCentralSurface j) : ℂˣ := by
  classical
  exact if hx : x ∈ baseSet j i ∩ baseSet j k then
    Units.mk0
      (localCoordinate j k x hx.2 ((localCoordinate j i x hx.1).symm 1))
      (coordinateChange_one_ne_zero j i k x hx)
    else 1

theorem transition_val_of_mem (i k x : SpecialCentralSurface j)
    (hx : x ∈ baseSet j i ∩ baseSet j k) :
    (transition j i k x : ℂ) =
      localCoordinate j k x hx.2 ((localCoordinate j i x hx.1).symm 1) := by
  classical
  unfold transition
  rw [dif_pos hx]
  rfl

theorem transition_of_not_mem (i k x : SpecialCentralSurface j)
    (hx : x ∉ baseSet j i ∩ baseSet j k) : transition j i k x = 1 := by
  classical
  unfold transition
  rw [dif_neg hx]

/-- The differential of the actual parametrization cancels from each
change of coordinates; the two geometric transition units are equal. -/
theorem transition_eq_local (i k x : SpecialCentralSurface j) :
    transition j i k x = Equivariant.Data.NormalBundle.transition
      (specialLocalData j) j.twist (mainTwist_admissible j) i k x := by
  by_cases hx : x ∈ baseSet j i ∩ baseSet j k
  · apply Units.ext
    rw [transition_val_of_mem j i k x hx,
      Equivariant.Data.NormalBundle.transition_val_of_mem
        (specialLocalData j) j.twist (mainTwist_admissible j) i k x hx]
    exact coordinateChange_eq_local j i k x hx 1
  · rw [transition_of_not_mem j i k x hx,
      Equivariant.Data.NormalBundle.transition_of_not_mem
        (specialLocalData j) j.twist (mainTwist_admissible j) i k x hx]

/-- The actual global normal cocycle is the transverse character cocycle. -/
theorem transition_eq_character (i k x : SpecialCentralSurface j) :
    letI := affineAction j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j).1
    transition j i k x = normalCharacter j
      (AssociatedCore.deck
        (surfaceProjection_isQuotientCoveringMap j (specialLocalData j).centralPeriod
          j.twist (mainTwist_admissible j)) i k x) := by
  rw [transition_eq_local]
  exact Equivariant.Data.NormalBundle.transition_eq_character
    (specialLocalData j) j.twist (mainTwist_admissible j) i k x

theorem localCoordinate_change (i k x : SpecialCentralSurface j)
    (hx : x ∈ baseSet j i ∩ baseSet j k) (n : GlobalCentralNormalFibre j x) :
    localCoordinate j k x hx.2 n = (transition j i k x : ℂ) *
      localCoordinate j i x hx.1 n := by
  rw [transition_eq_local]
  exact Equivariant.Data.NormalBundle.localCoordinate_change
    (specialLocalData j) j.twist (mainTwist_admissible j) i k x hx
    ((normalTransportLinearEquiv j x).symm n)

/-- Transition data assembled from the genuine global normal coordinates. -/
def data : TransitionData (SpecialCentralSurface j) (SpecialCentralSurface j) where
  baseSet := baseSet j
  isOpen_baseSet := isOpen_baseSet j
  indexAt := id
  mem_baseSet_at := mem_baseSet j
  transition := transition j
  transition_self := fun i x hx => by
    rw [transition_eq_local]
    exact (Equivariant.Data.NormalBundle.data
      (specialLocalData j) j.twist (mainTwist_admissible j)).transition_self i x hx
  transition_comp := fun i k l x hx => by
    rw [transition_eq_local, transition_eq_local, transition_eq_local]
    exact (Equivariant.Data.NormalBundle.data
      (specialLocalData j) j.twist (mainTwist_admissible j)).transition_comp i k l x hx
  continuousOn_transition := fun i k => by
    apply ((Equivariant.Data.NormalBundle.data
      (specialLocalData j) j.twist (mainTwist_admissible j)).continuousOn_transition i k).congr
    intro x hx
    exact congrArg Units.val (transition_eq_local j i k x)

private theorem transitionData_ext {M ι : Type*} [TopologicalSpace M]
    (A B : TransitionData M ι) (hbase : A.baseSet = B.baseSet)
    (hindex : A.indexAt = B.indexAt) (htransition : A.transition = B.transition) : A = B := by
  cases A
  cases B
  cases hbase
  cases hindex
  cases htransition
  rfl

/-- Equality of independently constructed geometric transition data. -/
theorem data_eq_local :
    data j = Equivariant.Data.NormalBundle.data
      (specialLocalData j) j.twist (mainTwist_admissible j) := by
  refine transitionData_ext (data j) (Equivariant.Data.NormalBundle.data
    (specialLocalData j) j.twist (mainTwist_admissible j)) rfl rfl ?_
  funext i k x
  exact transition_eq_local j i k x

theorem data_eq_associated :
    letI := affineAction j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j).1
    data j = AssociatedCore.data
      (surfaceProjection_isQuotientCoveringMap j (specialLocalData j).centralPeriod
        j.twist (mainTwist_admissible j)) (normalCharacter j) := by
  rw [data_eq_local]
  exact Equivariant.Data.NormalBundle.data_eq_associated
    (specialLocalData j) j.twist (mainTwist_admissible j)

instance data_isHolomorphic : (data j).IsHolomorphic IS := by
  rw [data_eq_local]
  infer_instance

/-- The analytic normal line of the actual global central inclusion. -/
abbrev core := (data j).core

theorem core_eq_local : core j = specialCentralNormalBundle j :=
  congrArg TransitionData.core (data_eq_local j)

theorem holomorphicVectorBundle : ContMDiffVectorBundle ω ℂ (core j).Fiber IS :=
  inferInstance

theorem totalSpace_isManifold : IsManifold IB ω (core j).TotalSpace := inferInstance

/-- Fibre identification with the literal global normal tangent quotient. -/
def fibreIdentification (x : SpecialCentralSurface j) :
    (core j).Fiber x ≃ₗ[ℂ] GlobalCentralNormalFibre j x := by
  change ℂ ≃ₗ[ℂ] GlobalCentralNormalFibre j x
  exact (localCoordinate j x x (mem_baseSet j x)).symm

/-- Both maps are continuous for the existing global quotient topology. -/
def fibreIdentificationContinuous (x : SpecialCentralSurface j) :
    (core j).Fiber x ≃L[ℂ] GlobalCentralNormalFibre j x := by
  change ℂ ≃L[ℂ] GlobalCentralNormalFibre j x
  exact (localCoordinateContinuous j x x (mem_baseSet j x)).symm

@[simp] theorem fibreIdentificationContinuous_toLinearEquiv
    (x : SpecialCentralSurface j) :
    (fibreIdentificationContinuous j x).toLinearEquiv = fibreIdentification j x := rfl

/-- This is precisely the actual global differential transport of the
local filling's normal bundle identification. -/
theorem fibreIdentificationContinuous_eq_specialNormalFibreToGlobal
    (x : SpecialCentralSurface j) :
    fibreIdentificationContinuous j x = specialNormalFibreToGlobal j x := by
  ext z
  rfl

/-- Every local analytic bundle chart, not just the preferred one,
is the corresponding actual global normal quotient coordinate. -/
theorem localCoordinate_fibreIdentification
    (i x : SpecialCentralSurface j) (hx : x ∈ baseSet j i) (z : (core j).Fiber x) :
    localCoordinate j i x hx (fibreIdentification j x z) =
      ((core j).localTriv i ⟨x, z⟩).2 := by
  change localCoordinate j i x hx
      ((localCoordinate j x x (mem_baseSet j x)).symm z) =
    (transition j x i x : ℂ) * id (α := ℂ) z
  have h := localCoordinate_change j x i x ⟨mem_baseSet j x, hx⟩
    ((localCoordinate j x x (mem_baseSet j x)).symm z)
  exact h.trans (congrArg (fun a : ℂ => (transition j x i x : ℂ) * a)
    ((localCoordinate j x x (mem_baseSet j x)).apply_symm_apply (id (α := ℂ) z)))

theorem localCoordinateContinuous_fibreIdentificationContinuous
    (i x : SpecialCentralSurface j) (hx : x ∈ baseSet j i) (z : (core j).Fiber x) :
    localCoordinateContinuous j i x hx (fibreIdentificationContinuous j x z) =
      ((core j).localTriv i ⟨x, z⟩).2 :=
  localCoordinate_fibreIdentification j i x hx z

theorem fibre_rank_one (x : SpecialCentralSurface j) :
    Module.finrank ℂ ((core j).Fiber x) = 1 := by
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

theorem globalNormalFibre_rank_one (x : SpecialCentralSurface j) :
    Module.finrank ℂ (GlobalCentralNormalFibre j x) = 1 :=
  (localCoordinate j x x (mem_baseSet j x)).finrank_eq.trans (Module.finrank_self ℂ)

/-- Analytic identification with the associated orbit quotient, deduced
from the equality of the genuine global normal transition data. -/
def associatedIdentification :
    letI := affineAction j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j).1
    letI := associatedChartedSpace (E := ComplexPlane₂)
      (surfaceProjection_isQuotientCoveringMap j (specialLocalData j).centralPeriod
        j.twist (mainTwist_admissible j)) (normalCharacter j)
    Diffeomorph IB IA (core j).TotalSpace
      (AssociatedSpace (A := (specialLocalData j).centralPeriod.val.Torus)
        (normalCharacter j)) ω := by
  letI := affineAction j (specialLocalData j).centralPeriod j.twist
    (mainTwist_admissible j).1
  let hq := surfaceProjection_isQuotientCoveringMap j (specialLocalData j).centralPeriod
    j.twist (mainTwist_admissible j)
  letI := associatedChartedSpace (E := ComplexPlane₂) hq (normalCharacter j)
  let e := AssociatedCore.identification hq (normalCharacter j)
    (affineAction_holomorphic j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j).1)
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

@[simp] theorem associatedIdentification_preserves_base (p : (core j).TotalSpace) :
    letI := affineAction j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j).1
    HolomorphicCharacterBundle.projection
      (surfaceProjection_isQuotientCoveringMap j (specialLocalData j).centralPeriod
        j.twist (mainTwist_admissible j)) (normalCharacter j)
      (associatedIdentification j p) = p.proj := by
  let := affineAction j (specialLocalData j).centralPeriod j.twist
    (mainTwist_admissible j).1
  exact AssociatedCore.projection_toAssociated
    (surfaceProjection_isQuotientCoveringMap j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j)) (normalCharacter j) p

/-- The associated orbit coordinates agree with every actual global
normal-bundle chart. -/
theorem associatedIdentification_localTriv (i : SpecialCentralSurface j)
    (p : (core j).TotalSpace) (hp : p.proj ∈ baseSet j i) :
    letI := affineAction j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j).1
    associatedIdentification j p = associatedMap (normalCharacter j)
      (Equivariant.Data.NormalBundle.lift
        (specialLocalData j) j.twist (mainTwist_admissible j) i p.proj,
        ((core j).localTriv i p).2) := by
  let := affineAction j (specialLocalData j).centralPeriod j.twist
    (mainTwist_admissible j).1
  have he := AssociatedCore.toAssociated_localTriv
    (surfaceProjection_isQuotientCoveringMap j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j)) (normalCharacter j) i p hp
  change _ = associatedMap (normalCharacter j)
    (Equivariant.Data.NormalBundle.lift
      (specialLocalData j) j.twist (mainTwist_admissible j) i p.proj,
      ((AssociatedCore.data
        (surfaceProjection_isQuotientCoveringMap j (specialLocalData j).centralPeriod
          j.twist (mainTwist_admissible j)) (normalCharacter j)).core.localTriv i p).2) at he
  rw [← data_eq_associated] at he
  exact he

/-- A genuine global normal tangent vector has the indicated associated
orbit representative in every actual central-covering lift. -/
theorem associatedIdentification_normalCoordinate
    (i x : SpecialCentralSurface j) (hx : x ∈ baseSet j i)
    (n : GlobalCentralNormalFibre j x) :
    letI := affineAction j (specialLocalData j).centralPeriod j.twist
      (mainTwist_admissible j).1
    associatedIdentification j ⟨x, (fibreIdentification j x).symm n⟩ =
      associatedMap (normalCharacter j)
        (Equivariant.Data.NormalBundle.lift
          (specialLocalData j) j.twist (mainTwist_admissible j) i x,
          localCoordinate j i x hx n) := by
  let := affineAction j (specialLocalData j).centralPeriod j.twist
    (mainTwist_admissible j).1
  rw [associatedIdentification_localTriv j i _ hx]
  congr 1
  apply Prod.ext
  · rfl
  · have he := localCoordinate_fibreIdentification j i x hx
      ((fibreIdentification j x).symm n)
    rw [LinearEquiv.apply_symm_apply] at he
    exact he.symm

/-- Tensor transitions are powers of the transitions computed from the
actual global normal quotient coordinates. -/
def powerData (n : ℕ) : TransitionData (SpecialCentralSurface j) (SpecialCentralSurface j) where
  baseSet := (data j).baseSet
  isOpen_baseSet := (data j).isOpen_baseSet
  indexAt := (data j).indexAt
  mem_baseSet_at := (data j).mem_baseSet_at
  transition i k x := ((data j).transition i k x) ^ n
  transition_self i x hx := by rw [(data j).transition_self i x hx, one_pow]
  transition_comp i k l x hx := by rw [← mul_pow, (data j).transition_comp i k l x hx]
  continuousOn_transition i k := by
    change ContinuousOn (fun x => ((data j).transition i k x : ℂ) ^ n)
      ((data j).baseSet i ∩ (data j).baseSet k)
    exact ((data j).continuousOn_transition i k).pow n

@[simp] theorem powerData_transition (n : ℕ) (i k x : SpecialCentralSurface j) :
    (powerData j n).transition i k x = ((data j).transition i k x) ^ n := rfl

theorem powerData_eq_local (n : ℕ) :
    powerData j n = Equivariant.Data.NormalBundle.powerData
      (specialLocalData j) j.twist (mainTwist_admissible j) n := by
  refine transitionData_ext (powerData j n) (Equivariant.Data.NormalBundle.powerData
    (specialLocalData j) j.twist (mainTwist_admissible j) n) rfl rfl ?_
  funext i k x
  rw [powerData_transition, Equivariant.Data.NormalBundle.powerData_transition]
  exact congrArg (fun u : ℂˣ => u ^ n) (transition_eq_local j i k x)

instance powerData_isHolomorphic (n : ℕ) : (powerData j n).IsHolomorphic IS := by
  rw [powerData_eq_local]
  infer_instance

@[simp] theorem powerData_one : powerData j 1 = data j := by
  rw [powerData_eq_local, Equivariant.Data.NormalBundle.powerData_one, data_eq_local]

/-- An actual analytic, base-preserving fibre-linear product trivialization
of the global normal tensor power exists exactly for these exponents. -/
theorem power_analyticTrivialization_iff (n : ℕ) :
    Nonempty ((powerData j n).AnalyticTrivialization IS) ↔ j.order ∣ n := by
  rw [powerData_eq_local]
  exact specialCentralNormal_power_trivial_iff j n

theorem order_isLeast :
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty ((powerData j n).AnalyticTrivialization IS)} j.order := by
  refine ⟨⟨j.order_pos, (power_analyticTrivialization_iff j j.order).mpr (dvd_refl _)⟩, ?_⟩
  intro n hn
  exact Nat.le_of_dvd hn.1 ((power_analyticTrivialization_iff j n).mp hn.2)

theorem order_power_trivial :
    Nonempty ((powerData j j.order).AnalyticTrivialization IS) :=
  (power_analyticTrivialization_iff j j.order).mpr (dvd_refl _)

theorem not_analytically_trivial : ¬ Nonempty ((data j).AnalyticTrivialization IS) := by
  rw [data_eq_local]
  exact (specialCentralBundles_nontrivial j).2

theorem power_three_analyticTrivialization_iff (n : ℕ) :
    Nonempty ((powerData .three n).AnalyticTrivialization IS) ↔ 3 ∣ n :=
  power_analyticTrivialization_iff .three n

theorem power_four_analyticTrivialization_iff (n : ℕ) :
    Nonempty ((powerData .four n).AnalyticTrivialization IS) ↔ 4 ∣ n :=
  power_analyticTrivialization_iff .four n

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry.GlobalNormalBundle

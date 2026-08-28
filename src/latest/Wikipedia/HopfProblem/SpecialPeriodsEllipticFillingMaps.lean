import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingData
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingBase
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingTorus
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingRestriction

/-!
# The actual local elliptic family inside the regular period family

The map is the inverse Cayley chart on the base and the identity on real
torus coordinates.  Its analytic local inverses follow from equality of
the actual period functions and the covering atlases.  The zero-twist
cyclic action is exactly the restriction of the actual triangle action.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.LogGauge TrianglePeriodFamily

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

variable (P : HolomorphicPeriodMap ℂ ℍ) (j : Kind)

/-- The literal local punctured family map, with unchanged flat torus
coordinate and the actual inverse normalized Cayley base chart. -/
def localTotalMap : FamilyStar (localPeriods P j) → (regularPeriods P).TotalSpace :=
  fun x => (localBase j ⟨x.1.1, x.2⟩, x.1.2)

@[simp] theorem localTotalMap_fst (x : FamilyStar (localPeriods P j)) :
    (localTotalMap P j x).1 = localBase j ⟨x.1.1, x.2⟩ := rfl

@[simp] theorem localTotalMap_snd (x : FamilyStar (localPeriods P j)) :
    (localTotalMap P j x).2 = x.1.2 := rfl

theorem localTotalMap_injective : Function.Injective (localTotalMap P j) := by
  intro x y h
  have hb := localBase_injective j (congrArg Prod.fst h)
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val hb)
    (congrArg (fun z : (regularPeriods P).TotalSpace => z.2) h)

/-- The inherited punctured-family atlas agrees with the covering atlas
of its restricted periods, and the actual base chart is locally biholomorphic. -/
theorem localTotalMap_isLocalDiffeomorph :
    letI := (localPeriods P j).totalChartedSpace
    letI := (regularPeriods P).totalChartedSpace
    IsLocalDiffeomorph IF IF ω (localTotalMap P j) := by
  let Q := restrictPeriods (localPeriods P j) baseOpen
  let := (localPeriods P j).totalChartedSpace
  let := (regularPeriods P).totalChartedSpace
  let := Q.totalChartedSpace
  let e := restrictFamilyBiholomorph (localPeriods P j) baseOpen
  have hm := periodFamilyMap_isLocalDiffeomorph Q (regularPeriods P) (localBase j)
    (fun _ => rfl) (localBase_isLocalDiffeomorph j)
  intro x
  have h := (e.symm.isLocalDiffeomorph x).comp (K := IF)
    (P := (regularPeriods P).TotalSpace) (hm (e.symm x))
  apply isLocalDiffeomorphAt_congr_of_eventuallyEq h
  apply Filter.Eventually.of_forall
  intro y
  change localTotalMap P j y = periodFamilyMap Q (regularPeriods P) (localBase j)
    ((restrictFamilyBiholomorph (localPeriods P j) baseOpen).symm y)
  rw [restrictFamilyBiholomorph_symm_apply]
  rfl

theorem localTotalMap_holomorphic :
    letI := (localPeriods P j).totalChartedSpace
    letI := (regularPeriods P).totalChartedSpace
    ContMDiff IF IF ω (localTotalMap P j) := by
  let := (localPeriods P j).totalChartedSpace
  let := (regularPeriods P).totalChartedSpace
  exact (localTotalMap_isLocalDiffeomorph P j).contMDiff

theorem localTotalMap_continuous : Continuous (localTotalMap P j) := by
  let := (localPeriods P j).totalChartedSpace
  let := (regularPeriods P).totalChartedSpace
  exact (localTotalMap_holomorphic P j).continuous

/-- This includes every torus point over every regular point of the
chosen actual elliptic neighborhood. -/
theorem localTotalMap_range :
    range (localTotalMap P j) =
      {x : (regularPeriods P).TotalSpace | (x.1 : ℍ) ∈ Triangle.ellipticNeighborhood j} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact localBase_mem_neighborhood j _
  · intro hx
    have hb : x.1 ∈ range (localBase j) := by
      rw [localBase_range]
      exact hx
    obtain ⟨z, hz⟩ := hb
    exact ⟨⟨(z.val, x.2), z.property⟩, Prod.ext hz rfl⟩

theorem puncturedRotation_iterate_coe (n : ℕ) (z : BaseStar) :
    ((puncturedRotation j)^[n] z).val = (familyRotation j)^[n] z.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', puncturedRotation_val, ih,
      Function.iterate_succ_apply']

variable
  (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
  (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The actual local-to-global map intertwines the entire untwisted
cyclic action with powers of the actual triangle generator. -/
theorem localTotalMap_smul (g : CyclicGroup j) (x : FamilyStar (localPeriods P j)) :
    letI := starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    letI := (regularData P h₁ h₂).totalAction
    localTotalMap P j (g • x) =
      Triangle.ellipticGenerator j ^ g.toAdd.val • localTotalMap P j x := by
  let L := localData P h₁ h₂ j
  let D := regularData P h₁ h₂
  let := starAction L 0 (Matrix.mulVec_zero j.matrix)
  let := D.totalAction
  have hb : (⟨(g • x : FamilyStar L.periods).1.1,
      (g • x : FamilyStar L.periods).2⟩ : BaseStar) =
      (puncturedRotation j)^[g.toAdd.val] ⟨x.1.1, x.2⟩ := by
    apply Subtype.ext
    exact (zeroStarAction_fst L g x).trans
      (puncturedRotation_iterate_coe j g.toAdd.val ⟨x.1.1, x.2⟩).symm
  apply Prod.ext
  · change localBase j ⟨(g • x : FamilyStar L.periods).1.1,
        (g • x : FamilyStar L.periods).2⟩ =
      Triangle.ellipticGenerator j ^ g.toAdd.val • localBase j ⟨x.1.1, x.2⟩
    rw [hb, localBase_rotation_iterate]
  · exact zeroStarAction_snd L g x

/-- The actual quotient map to the whole regular family. -/
def regularMap : FamilyStar (localPeriods P j) → (regularData P h₁ h₂).Space :=
  (regularData P h₁ h₂).quotient ∘ localTotalMap P j

@[simp] theorem regularMap_base (x : FamilyStar (localPeriods P j)) :
    (regularData P h₁ h₂).projection (regularMap P j h₁ h₂ x) =
      baseQuotient j ⟨x.1.1, x.2⟩ := rfl

theorem regularMap_smul (g : CyclicGroup j) (x : FamilyStar (localPeriods P j)) :
    letI := starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    regularMap P j h₁ h₂ (g • x) = regularMap P j h₁ h₂ x := by
  let := starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
  let := (regularData P h₁ h₂).totalAction
  change (regularData P h₁ h₂).quotient (localTotalMap P j (g • x)) =
    (regularData P h₁ h₂).quotient (localTotalMap P j x)
  rw [localTotalMap_smul, TrianglePeriodFamily.Data.quotient_smul]

theorem regularMap_isLocalDiffeomorph :
    letI := (localPeriods P j).totalChartedSpace
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    IsLocalDiffeomorph IF IF ω (regularMap P j h₁ h₂) := by
  let := (localPeriods P j).totalChartedSpace
  let := (regularPeriods P).totalChartedSpace
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  intro x
  exact (localTotalMap_isLocalDiffeomorph P j x).comp (K := IF)
    (P := (regularData P h₁ h₂).Space)
    ((regularData P h₁ h₂).quotient_isLocalDiffeomorph (regularCovering P h₁ h₂)
      (localTotalMap P j x))

theorem regularMap_holomorphic :
    letI := (localPeriods P j).totalChartedSpace
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    ContMDiff IF IF ω (regularMap P j h₁ h₂) := by
  let := (localPeriods P j).totalChartedSpace
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  exact (regularMap_isLocalDiffeomorph P j h₁ h₂).contMDiff

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

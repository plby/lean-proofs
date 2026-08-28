import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultKernel
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrameCalculusOperations

/-!
# The native Dolbeault operators are actual sheaf derivations

The product rule is proved on the literal covering-space lifts. The
holomorphic-to-smooth inclusion is the genuine ring map retaining the
same values in the unchanged quotient charts.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

open PeriodTorusHolomorphicCohomology PeriodTorusHolomorphicCohomology.Dolbeault
open PeriodTorusLineBundleClassification
open PeriodTorusLineBundleClassificationHolomorphicFrame
open HolomorphicSheafCohomology

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IR₂" => modelWithCornersSelf ℝ ComplexPlane₂

abbrev smoothRingSheaf (p : PeriodDomain) := SmoothFunctions.sheaf IR₂ p.Torus
abbrev holomorphicRingSheaf (p : PeriodDomain) := HolomorphicFunctionSheaf.sheaf I₂ p.Torus

theorem smoothExtend_mul (p : PeriodDomain) (U : Opens p.Torus)
    (s t : SmoothSection p U) :
    smoothExtend p U (s * t) = fun x => smoothExtend p U s x * smoothExtend p U t x := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp only [smoothExtend, dif_pos hx]
    rfl
  · simp only [smoothExtend, dif_neg hx, mul_zero]

theorem liftSection_mul (p : PeriodDomain) (U : Opens p.Torus)
    (s t : SmoothSection p U) :
    liftSection p U (s * t) = fun z => liftSection p U s z * liftSection p U t z := by
  rw [liftSection, smoothExtend_mul]
  rfl

/-- Leibniz for the original native antiholomorphic coordinate derivative. -/
theorem derivativeSection_mul (p : PeriodDomain) (i : Fin 2) (U : Opens p.Torus)
    (s t : SmoothSection p U) :
    derivativeSection p i U (s * t) =
      derivativeSection p i U s * t + s * derivativeSection p i U t := by
  apply ContMDiffMap.ext
  intro x
  let z := DiscreteQuotient.representative p.lattice (x : p.Torus)
  have hz : p.lattice.mkQ z ∈ U := by
    simpa only [z, DiscreteQuotient.mkQ_representative] using x.property
  have hs : liftSection p U s z = s x := by
    change smoothExtend p U s (p.lattice.mkQ z) = s x
    rw [show p.lattice.mkQ z = (x : p.Torus) from
      DiscreteQuotient.mkQ_representative p.lattice x]
    exact smoothExtend_apply p U s x x.property
  have ht : liftSection p U t z = t x := by
    change smoothExtend p U t (p.lattice.mkQ z) = t x
    rw [show p.lattice.mkQ z = (x : p.Torus) from
      DiscreteQuotient.mkQ_representative p.lattice x]
    exact smoothExtend_apply p U t x x.property
  change dbarCoordinate (liftSection p U (s * t)) i z =
    dbarCoordinate (liftSection p U s) i z * t x + s x * dbarCoordinate (liftSection p U t) i z
  rw [liftSection_mul, dbarCoordinate_mul
    ((liftSection_contDiffAt p U s z hz).differentiableAt (by simp))
    ((liftSection_contDiffAt p U t z hz).differentiableAt (by simp)), hs, ht]
  ring

/-- The original pointwise inclusion, now retaining its genuine ring structure. -/
def inclusionRingSection (p : PeriodDomain) (U : Opens p.Torus) :
    HolomorphicSection p U →+* SmoothSection p U where
  toFun := inclusionSection p U
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual holomorphic-to-smooth ring-sheaf map in the native charts. -/
def inclusionRing (p : PeriodDomain) : holomorphicRingSheaf p ⟶ smoothRingSheaf p where
  hom :=
    { app U := CommRingCat.ofHom (inclusionRingSection p U.unop)
      naturality _ _ _ := rfl }

theorem inclusionRing_forget (p : PeriodDomain) :
    (SheafCupProduct.GodementRing.forgetSheaf (TopCat.of p.Torus)).map (inclusionRing p) =
      Dolbeault.inclusion p := rfl

/-- The original derivative, as an actual additive sheaf endomorphism. -/
def derivativeMap (p : PeriodDomain) (i : Fin 2) : End (smoothSheaf p) where
  hom :=
    { app U := AddCommGrpCat.ofHom (derivativeSection p i U.unop).toAddMonoidHom
      naturality _ _ h := by
        apply AddCommGrpCat.hom_ext
        exact AddMonoidHom.ext (derivativeSection_restrict p i (leOfHom h.unop)) }

@[simp] theorem derivativeMap_apply (p : PeriodDomain) (i : Fin 2) (U : Opens p.Torus)
    (s : SmoothSection p U) :
    (derivativeMap p i).hom.app (op U) s = derivativeSection p i U s := rfl

/-- The actual native derivative, bundled with its proved sectionwise Leibniz rule. -/
def nativeDerivation (p : PeriodDomain) (i : Fin 2) : SheafDerivation (smoothRingSheaf p) where
  map := derivativeMap p i
  leibniz := derivativeSection_mul p i

/-- The two original additive sheaf endomorphisms commute. -/
theorem derivativeMap_commute (p : PeriodDomain) :
    derivativeMap p 0 ≫ derivativeMap p 1 = derivativeMap p 1 ≫ derivativeMap p 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext fun s => (derivativeSection_commute p U.unop s).symm

/-- Every original holomorphic section is killed by either actual derivative. -/
theorem inclusion_derivativeMap (p : PeriodDomain) (i : Fin 2) :
    Dolbeault.inclusion p ≫ derivativeMap p i = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (derivativeSection_inclusion p i U.unop)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

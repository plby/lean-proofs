import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroSections
import Mathlib.Topology.Sheaves.Functors

/-!
# The genuine holomorphic-function pushforward of every period family

The actual all-open pullback algebra isomorphisms commute with the
original restriction maps. They therefore identify the original base
holomorphic-function sheaf with the genuine sheaf pushforward from
the unchanged varying-period quotient atlas.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.Zero

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IB" => modelWithCornersSelf ℂ V
local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The original holomorphic-function sheaf on the given complex base. -/
abbrev baseHolomorphicSheaf (_P : HolomorphicPeriodMap V B) :=
  HolomorphicFunctionSheaf.sheaf IB B

/-- The genuine holomorphic-function sheaf in the original family quotient atlas. -/
def totalHolomorphicSheaf (P : HolomorphicPeriodMap V B) :
    TopCat.Sheaf CommRingCat (TopCat.of P.TotalSpace) := by
  letI := P.totalChartedSpace
  exact HolomorphicFunctionSheaf.sheaf IT P.TotalSpace

/-- The genuine ring-sheaf pushforward along the actual family projection. -/
def holomorphicDirectImage (P : HolomorphicPeriodMap V B) :
    TopCat.Sheaf CommRingCat (TopCat.of B) :=
  (TopCat.Sheaf.pushforward CommRingCat (projectionMap P)).obj (totalHolomorphicSheaf P)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The isomorphism on each open is literal pullback, with its proved
literal restriction naturality. -/
def holomorphicDirectImagePresheafIso (P : HolomorphicPeriodMap V B) :
    (baseHolomorphicSheaf P).presheaf ≅ (holomorphicDirectImage P).presheaf :=
  NatIso.ofComponents
    (fun U => (pullbackSectionEquiv P U.unop).toRingEquiv.toCommRingCatIso)
    (by
      intro U W h
      ext f
      rfl)

/-- The genuine identity `O_B ≅ f_* O_Total` for the original period
family, with actual holomorphic pullback as forward map. -/
def holomorphicDirectImageIso (P : HolomorphicPeriodMap V B) :
    baseHolomorphicSheaf P ≅ holomorphicDirectImage P :=
  ObjectProperty.isoMk _ (holomorphicDirectImagePresheafIso P)

@[simp] theorem holomorphicDirectImageIso_hom_app (P : HolomorphicPeriodMap V B)
    (U : Opens B) (f : BaseSection P U) :
    (holomorphicDirectImageIso P).hom.hom.app (op U) f = pullbackSection P U f := rfl

/-- The inverse is the literal holomorphic evaluation along the original zero section. -/
@[simp] theorem holomorphicDirectImageIso_inv_app (P : HolomorphicPeriodMap V B)
    (U : Opens B) (s : PreimageSection P U) :
    (holomorphicDirectImageIso P).inv.hom.app (op U) s = descendedSection P U s := rfl

/-- The actual family direct-image assertion, without a fibre-dimension
or holomorphic-descent premise. -/
theorem directImage_holomorphic_functions (P : HolomorphicPeriodMap V B) :
    Nonempty (holomorphicDirectImage P ≅ baseHolomorphicSheaf P) :=
  ⟨(holomorphicDirectImageIso P).symm⟩

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.Zero

import Wikipedia.HopfProblem.EllipticEquivariantFillings
import Wikipedia.HopfProblem.EllipticEquivariantCentralNormalAction
import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedCore
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreSections

/-!
# The reduced central divisor in a genuine elliptic filling

Local inverses of the unramified cyclic covering retain the transverse
coordinate. Its changes are the actual normal character, so these local
coordinates define a holomorphic line-bundle section. Their prescribed
power is the original filling parameter, including on the central fibre.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix Manifold

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.RootSection

open HolomorphicCharacterBundle

variable {j : Kind} (D : Equivariant.Data j) (v : Lattice)
  (hv : AdmissibleTwist j v)

local notation "IF" => modelWithCornersSelf ℂ FamilyModel

/-- The character cocycle on the unchanged full filling. -/
def data : TransitionData (D.Space v hv) (D.Space v hv) := by
  letI := D.action v hv.1
  exact AssociatedCore.data (D.quotientCoveringMap v hv) (normalCharacter j)

local instance rootFamilyCharts : ChartedSpace FamilyModel D.TotalSpace :=
  D.periods.totalChartedSpace

local instance rootFillingCharts : ChartedSpace FamilyModel (D.Space v hv) :=
  D.chartedSpace v hv

instance data_isHolomorphic : (data D v hv).IsHolomorphic IF := by
  let := D.action v hv.1
  exact AssociatedCore.data_isHolomorphic (D.quotientCoveringMap v hv) (normalCharacter j) IF

/-- The actual transverse coordinate in each covering section. -/
def coefficient (i x : D.Space v hv) : ℂ := by
  letI := D.action v hv.1
  exact (AssociatedCore.lift (D.quotientCoveringMap v hv) i x).1.val

theorem coefficient_compatible : (data D v hv).IsCompatible (coefficient D v hv) := by
  let := D.action v hv.1
  intro i k x hx
  change (normalCharacter j (AssociatedCore.deck (D.quotientCoveringMap v hv) i k x) : ℂ) *
    (AssociatedCore.lift (D.quotientCoveringMap v hv) i x).1.val =
      (AssociatedCore.lift (D.quotientCoveringMap v hv) k x).1.val
  exact (D.familyAction_projection_coe v hv.1
    (AssociatedCore.deck (D.quotientCoveringMap v hv) i k x)
    (AssociatedCore.lift (D.quotientCoveringMap v hv) i x)).symm.trans
      (congrArg (fun a : D.TotalSpace => (a.1 : ℂ))
        (AssociatedCore.deck_spec (D.quotientCoveringMap v hv) i k hx))

theorem coefficient_holomorphic (i : D.Space v hv) :
    ContMDiffOn IF 𝓘(ℂ) ω (coefficient D v hv i) ((data D v hv).baseSet i) := by
  let := D.action v hv.1
  let := D.periods.totalSpace_isManifold
  exact (contMDiff_subtype_val.comp D.periods.projection_holomorphic).comp_contMDiffOn
    (AssociatedCore.lift_holomorphic (D.quotientCoveringMap v hv)
      (D.action_holomorphic v hv.1) i)

theorem coefficient_pow (i : D.Space v hv) {x : D.Space v hv}
    (hx : x ∈ (data D v hv).baseSet i) :
    coefficient D v hv i x ^ j.order = (D.projection v hv x : ℂ) := by
  let := D.action v hv.1
  have h := congrArg (fun y : D.Space v hv => (D.projection v hv y : ℂ))
    (AssociatedCore.lift_project (D.quotientCoveringMap v hv) i hx)
  exact h

theorem coefficient_eq_zero_iff (i : D.Space v hv) {x : D.Space v hv}
    (hx : x ∈ (data D v hv).baseSet i) :
    coefficient D v hv i x = 0 ↔ (D.projection v hv x : ℂ) = 0 := by
  rw [← coefficient_pow D v hv i hx, pow_eq_zero_iff j.order_pos.ne']

/-- The section lies in the bundle built from the actual covering cocycle. -/
def rootSection (x : D.Space v hv) : (data D v hv).core.Fiber x :=
  (data D v hv).sectionFromLocal (coefficient D v hv) x

theorem section_holomorphic :
    ContMDiff IF ((IF).prod 𝓘(ℂ)) ω
      (fun x => (⟨x, rootSection D v hv x⟩ : (data D v hv).core.TotalSpace)) :=
  (data D v hv).sectionFromLocal_holomorphic IF (coefficient D v hv)
    (coefficient_compatible D v hv) (coefficient_holomorphic D v hv)

theorem section_eq_zero_iff (x : D.Space v hv) :
    rootSection D v hv x = 0 ↔ (D.projection v hv x : ℂ) = 0 :=
  coefficient_eq_zero_iff D v hv ((data D v hv).indexAt x) ((data D v hv).mem_baseSet_at x)

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.RootSection

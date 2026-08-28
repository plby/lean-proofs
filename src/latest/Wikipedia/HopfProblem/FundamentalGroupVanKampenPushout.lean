import Wikipedia.HopfProblem.FundamentalGroupVanKampenUniversal
import Mathlib.GroupTheory.PushoutI

/-!
# The actual fundamental group as a group pushout

For a path-connected two-open-set cover with path-connected intersection,
the fundamental group of the union is isomorphic to the native indexed
group pushout.  Both homomorphisms are constructed: the forward map is
the algebraic pushout lift of the actual inclusions, and the inverse uses
the topological van Kampen lift proved by path and square subdivision.

No injectivity of either overlap homomorphism is required.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen.TwoOpenCover

variable {X : Type*} [TopologicalSpace X] (D : TwoOpenCover X)

/-- The two native chart fundamental groups, indexed by `Bool`. -/
abbrev ChartGroup (i : Bool) := FundamentalGroup (D.chart i) (D.baseChart i)

/-- The actual overlap homomorphisms as one indexed family. -/
def overlapHom : (i : Bool) → D.OverlapGroup →* D.ChartGroup i
  | false => D.overlapHomU
  | true => D.overlapHomV

/-- The two actual inclusions into the ambient fundamental group. -/
def inclusionHom : (i : Bool) → D.ChartGroup i →* FundamentalGroup X D.base
  | false => D.inclusionHomU
  | true => D.inclusionHomV

theorem inclusionHom_comp_overlapHom (i : Bool) :
    (D.inclusionHom i).comp (D.overlapHom i) =
      D.inclusionHomU.comp D.overlapHomU := by
  cases i
  · rfl
  · exact D.inclusionHom_compatible.symm

/-- The native group pushout, with no injectivity restriction on the diagram. -/
abbrev Pushout := Monoid.PushoutI D.overlapHom

/-- The canonical map from the first chart group into the pushout. -/
def pushoutOfU : D.UGroup →* D.Pushout := Monoid.PushoutI.of (φ := D.overlapHom) false

/-- The canonical map from the second chart group into the pushout. -/
def pushoutOfV : D.VGroup →* D.Pushout := Monoid.PushoutI.of (φ := D.overlapHom) true

/-- The canonical map from the overlap group into the pushout. -/
def pushoutBase : D.OverlapGroup →* D.Pushout := Monoid.PushoutI.base D.overlapHom

theorem pushoutOfU_comp_overlapHomU : D.pushoutOfU.comp D.overlapHomU = D.pushoutBase :=
  Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) false

theorem pushoutOfV_comp_overlapHomV : D.pushoutOfV.comp D.overlapHomV = D.pushoutBase :=
  Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) true

theorem pushoutOf_compatible : D.Compatible D.pushoutOfU D.pushoutOfV :=
  D.pushoutOfU_comp_overlapHomU.trans D.pushoutOfV_comp_overlapHomV.symm

/-- The algebraic pushout lift of the two geometric inclusions. -/
def pushoutToFundamentalGroup : D.Pushout →* FundamentalGroup X D.base :=
  Monoid.PushoutI.lift D.inclusionHom (D.inclusionHomU.comp D.overlapHomU)
    D.inclusionHom_comp_overlapHom

@[simp] theorem pushoutToFundamentalGroup_of (i : Bool) (g : D.ChartGroup i) :
    D.pushoutToFundamentalGroup (Monoid.PushoutI.of i g) = D.inclusionHom i g :=
  Monoid.PushoutI.lift_of _ _ _ g

theorem pushoutToFundamentalGroup_comp_of (i : Bool) :
    D.pushoutToFundamentalGroup.comp (Monoid.PushoutI.of i) = D.inclusionHom i := by
  ext g
  exact D.pushoutToFundamentalGroup_of i g

theorem pushoutToFundamentalGroup_comp_ofU :
    D.pushoutToFundamentalGroup.comp D.pushoutOfU = D.inclusionHomU :=
  D.pushoutToFundamentalGroup_comp_of false

theorem pushoutToFundamentalGroup_comp_ofV :
    D.pushoutToFundamentalGroup.comp D.pushoutOfV = D.inclusionHomV :=
  D.pushoutToFundamentalGroup_comp_of true

/-- The topological van Kampen lift of the canonical pushout homomorphisms. -/
def fundamentalGroupToPushout : FundamentalGroup X D.base →* D.Pushout :=
  D.lift D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

theorem fundamentalGroupToPushout_comp_inclusionU :
    D.fundamentalGroupToPushout.comp D.inclusionHomU = D.pushoutOfU :=
  D.lift_comp_inclusionU D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

theorem fundamentalGroupToPushout_comp_inclusionV :
    D.fundamentalGroupToPushout.comp D.inclusionHomV = D.pushoutOfV :=
  D.lift_comp_inclusionV D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

/-- The canonical maps generate the pushout, so this composite is the identity. -/
theorem fundamentalGroupToPushout_comp_pushoutToFundamentalGroup :
    D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup =
      MonoidHom.id D.Pushout := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i
  · change (D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup).comp
        D.pushoutOfU = (MonoidHom.id D.Pushout).comp D.pushoutOfU
    rw [MonoidHom.comp_assoc, D.pushoutToFundamentalGroup_comp_ofU,
      D.fundamentalGroupToPushout_comp_inclusionU, MonoidHom.id_comp]
  · change (D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup).comp
        D.pushoutOfV = (MonoidHom.id D.Pushout).comp D.pushoutOfV
    rw [MonoidHom.comp_assoc, D.pushoutToFundamentalGroup_comp_ofV,
      D.fundamentalGroupToPushout_comp_inclusionV, MonoidHom.id_comp]

/-- The geometric inclusion maps determine ambient homomorphisms, so the
composite in the other direction is also the identity. -/
theorem pushoutToFundamentalGroup_comp_fundamentalGroupToPushout :
    D.pushoutToFundamentalGroup.comp D.fundamentalGroupToPushout =
      MonoidHom.id (FundamentalGroup X D.base) := by
  apply D.hom_ext
  · rw [MonoidHom.comp_assoc, D.fundamentalGroupToPushout_comp_inclusionU,
      D.pushoutToFundamentalGroup_comp_ofU, MonoidHom.id_comp]
  · rw [MonoidHom.comp_assoc, D.fundamentalGroupToPushout_comp_inclusionV,
      D.pushoutToFundamentalGroup_comp_ofV, MonoidHom.id_comp]

/-- The Seifert--van Kampen isomorphism for the actual native fundamental
groups.  Its construction assumes no pushout or presentation of the union. -/
def pushoutEquiv : D.Pushout ≃* FundamentalGroup X D.base where
  toFun := D.pushoutToFundamentalGroup
  invFun := D.fundamentalGroupToPushout
  left_inv g := DFunLike.congr_fun D.fundamentalGroupToPushout_comp_pushoutToFundamentalGroup g
  right_inv g := DFunLike.congr_fun D.pushoutToFundamentalGroup_comp_fundamentalGroupToPushout g
  map_mul' := D.pushoutToFundamentalGroup.map_mul

@[simp] theorem pushoutEquiv_toMonoidHom :
    D.pushoutEquiv.toMonoidHom = D.pushoutToFundamentalGroup := rfl

@[simp] theorem pushoutEquiv_symm_toMonoidHom :
    D.pushoutEquiv.symm.toMonoidHom = D.fundamentalGroupToPushout := rfl

/-- Each canonical pushout map becomes exactly the corresponding actual inclusion. -/
theorem pushoutEquiv_comp_of (i : Bool) :
    D.pushoutEquiv.toMonoidHom.comp (Monoid.PushoutI.of i) = D.inclusionHom i :=
  D.pushoutToFundamentalGroup_comp_of i

theorem pushoutEquiv_comp_ofU :
    D.pushoutEquiv.toMonoidHom.comp D.pushoutOfU = D.inclusionHomU :=
  D.pushoutToFundamentalGroup_comp_ofU

theorem pushoutEquiv_comp_ofV :
    D.pushoutEquiv.toMonoidHom.comp D.pushoutOfV = D.inclusionHomV :=
  D.pushoutToFundamentalGroup_comp_ofV

@[simp] theorem pushoutEquiv_of (i : Bool) (g : D.ChartGroup i) :
    D.pushoutEquiv (Monoid.PushoutI.of i g) = D.inclusionHom i g :=
  D.pushoutToFundamentalGroup_of i g

theorem pushoutEquiv_symm_comp_inclusionU :
    D.pushoutEquiv.symm.toMonoidHom.comp D.inclusionHomU = D.pushoutOfU :=
  D.fundamentalGroupToPushout_comp_inclusionU

theorem pushoutEquiv_symm_comp_inclusionV :
    D.pushoutEquiv.symm.toMonoidHom.comp D.inclusionHomV = D.pushoutOfV :=
  D.fundamentalGroupToPushout_comp_inclusionV

end Wikipedia.HopfProblem.FundamentalGroupVanKampen.TwoOpenCover

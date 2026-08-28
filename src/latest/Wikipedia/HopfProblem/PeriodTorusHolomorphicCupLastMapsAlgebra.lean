import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastMapsBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastAlgebra

/-!
# The actual native coefficient algebra and original last-row unit

The coefficient ring is the original global smooth-function ring. Its
two derivatives are the native torus derivatives, and its ring map is
the genuine section-to-germs inclusion. All compatibility fields are
proved from the corresponding actual sheaf squares.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps

open SheafCupProduct PeriodTorusHolomorphicCohomology

variable (p : PeriodDomain)

/-- The literal global smooth row and its actual ring-valued column unit. -/
def lastAlgebra : LastAlgebra.Data (Dolbeault.SmoothSection p ⊤) (totalData p) where
  unit := ((GodementRing.inclusion (Derivation.smoothRingSheaf p)).hom.app (op ⊤)).hom
  baseDeriv i := (Dolbeault.derivativeSection p i ⊤).toAddMonoidHom
  commute := Dolbeault.derivativeSection_commute p ⊤
  unit_vertical s := congrArg
    (fun f : Dolbeault.smoothSheaf p ⟶ GodementExact.I1 (Derivation.smoothRingSheaf p) =>
      (f.hom.app (op ⊤)).hom s)
    (GodementExact.augmentation_d0 (Derivation.smoothRingSheaf p))
  unit_derivative i s := congrArg
    (fun f : Dolbeault.smoothSheaf p ⟶ GodementExact.I0 (Derivation.smoothRingSheaf p) =>
      (f.hom.app (op ⊤)).hom s)
    ((totalOperators p).unit_derivative i)

/-- The actual algebraic unit is exactly the original additive column unit on global sections. -/
theorem lastAlgebra_unit (s : Dolbeault.SmoothSection p ⊤) :
    (lastAlgebra p).unit s = (Total.columnUnit0 p).hom.app (op ⊤) s := rfl

/-- Its gradient is the unchanged native first Dolbeault differential. -/
theorem lastAlgebra_rowD0 (s : Dolbeault.SmoothSection p ⊤) :
    (lastAlgebra p).rowD0 s = Dolbeault.differentialSection p ⊤ s := rfl

/-- Its curl is the unchanged native top Dolbeault differential, in the original order. -/
theorem lastAlgebra_rowD1 (s : Dolbeault.PairSection p ⊤) :
    (lastAlgebra p).rowD1 s = Dolbeault.topSection p ⊤ s := rfl

/-- The actual native pair unit acts by that same ring map on both original coefficients. -/
theorem columnUnit1_apply (s : Dolbeault.PairSection p ⊤) :
    (Total.columnUnit1 p).hom.app (op ⊤) s =
      ((lastAlgebra p).unit s.1, (lastAlgebra p).unit s.2) := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastMaps

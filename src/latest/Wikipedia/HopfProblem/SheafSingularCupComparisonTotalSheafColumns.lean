import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafColumnsBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalExactTwo

/-!
# Exact original Godement columns on actual stalks

Every exactness assertion here follows from the proved Godement stalk
contractions. Each augmentation is the original germ map and is
injective by its actual evaluation retraction.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf

open SheafCupProduct

variable (X : TopCat.{0})

/-- Apply the actual additive stalk functor to the original diagram. -/
abbrev stalkData (x : X) := (categoryData X).mapData (GodementExact.additiveStalk x)

/-- The original singular-cochain stalk in the augmented horizontal row. -/
abbrev rowStalk (n : ℕ) (x : X) :=
  (GodementExact.additiveStalk x).obj
    ((GodementRing.forgetSheaf X).obj (RingCochains.sheaf X n))

private theorem stalk_exact (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (h : S.Exact) (x : X) : Function.Exact
      ((GodementExact.additiveStalk x).map S.f).hom
      ((GodementExact.additiveStalk x).map S.g).hom :=
  (S.map (GodementExact.additiveStalk x)).ab_exact_iff_function_exact.mp
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp h x)

/-- The original column unit is injective on each actual stalk. -/
theorem columnUnit_stalk_injective (n : ℕ) (x : X) :
    Function.Injective ((GodementExact.additiveStalk x).map (columnUnit X n)).hom := by
  intro a b hab
  exact (ConcreteCategory.congr_hom
      (GodementExact.augmentation_stalkRetraction (RingCochains.sheaf X n) x) a).symm.trans
    ((congrArg (GodementExact.stalkRetraction (RingCochains.sheaf X n) x) hab).trans
      (ConcreteCategory.congr_hom
        (GodementExact.augmentation_stalkRetraction (RingCochains.sheaf X n) x) b))

/-- The actual augmented stalk columns satisfy all hypotheses of the
proved low-degree diagram chase. -/
def stalkColumns (x : X) : TotalComplex.AugmentedColumns (stalkData X x)
    (rowStalk X 0 x) (rowStalk X 1 x) (rowStalk X 2 x) (rowStalk X 3 x) where
  i0 := ((GodementExact.additiveStalk x).map (columnUnit X 0)).hom
  i1 := ((GodementExact.additiveStalk x).map (columnUnit X 1)).hom
  i2 := ((GodementExact.additiveStalk x).map (columnUnit X 2)).hom
  i3 := ((GodementExact.additiveStalk x).map (columnUnit X 3)).hom
  d0 := ((GodementExact.additiveStalk x).map (RingCochains.d0 X)).hom
  d1 := ((GodementExact.additiveStalk x).map (RingCochains.d1 X)).hom
  d2 := ((GodementExact.additiveStalk x).map (RingCochains.d2 X)).hom
  comm0 := by
    change ((GodementExact.additiveStalk x).map (columnUnit X 0) ≫
      (GodementExact.additiveStalk x).map (categoryData X).h00).hom =
        ((GodementExact.additiveStalk x).map (RingCochains.d0 X) ≫
          (GodementExact.additiveStalk x).map (columnUnit X 1)).hom
    exact congrArg (fun f => f.hom)
      (((GodementExact.additiveStalk x).map_comp (columnUnit X 0)
        (categoryData X).h00).symm.trans
          ((congrArg (GodementExact.additiveStalk x).map (columnUnit_d0 X)).trans
            ((GodementExact.additiveStalk x).map_comp (RingCochains.d0 X)
              (columnUnit X 1))))
  comm1 := by
    change ((GodementExact.additiveStalk x).map (columnUnit X 1) ≫
      (GodementExact.additiveStalk x).map (categoryData X).h01).hom =
        ((GodementExact.additiveStalk x).map (RingCochains.d1 X) ≫
          (GodementExact.additiveStalk x).map (columnUnit X 2)).hom
    exact congrArg (fun f => f.hom)
      (((GodementExact.additiveStalk x).map_comp (columnUnit X 1)
        (categoryData X).h01).symm.trans
          ((congrArg (GodementExact.additiveStalk x).map (columnUnit_d1 X)).trans
            ((GodementExact.additiveStalk x).map_comp (RingCochains.d1 X)
              (columnUnit X 2))))
  comm2 := by
    change ((GodementExact.additiveStalk x).map (columnUnit X 2) ≫
      (GodementExact.additiveStalk x).map (categoryData X).h02).hom =
        ((GodementExact.additiveStalk x).map (RingCochains.d2 X) ≫
          (GodementExact.additiveStalk x).map (columnUnit X 3)).hom
    exact congrArg (fun f => f.hom)
      (((GodementExact.additiveStalk x).map_comp (columnUnit X 2)
        (categoryData X).h02).symm.trans
          ((congrArg (GodementExact.additiveStalk x).map (columnUnit_d2 X)).trans
            ((GodementExact.additiveStalk x).map_comp (RingCochains.d2 X)
              (columnUnit X 3))))
  column00 := stalk_exact X _ (GodementExact.exact0 (RingCochains.sheaf X 0)) x
  column01 := stalk_exact X _ (GodementExact.exact0 (RingCochains.sheaf X 1)) x
  column02 := stalk_exact X _ (GodementExact.exact0 (RingCochains.sheaf X 2)) x
  column10 := stalk_exact X _ (GodementExact.exact1 (RingCochains.sheaf X 0)) x
  column20 := stalk_exact X _ (GodementExact.exact2 (RingCochains.sheaf X 0)) x
  column11 := stalk_exact X _ (GodementExact.exact1 (RingCochains.sheaf X 1)) x
  injective0 := columnUnit_stalk_injective X 0 x
  injective1 := columnUnit_stalk_injective X 1 x
  injective2 := columnUnit_stalk_injective X 2 x
  injective3 := columnUnit_stalk_injective X 3 x

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf

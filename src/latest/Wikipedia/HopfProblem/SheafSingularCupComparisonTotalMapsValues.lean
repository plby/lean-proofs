import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsBasic

/-!
# Actual ring maps on the first and last global components

The first-column ring maps are the actual Godement images of the
original constant augmentation. The last-row ring maps are the actual
germ inclusions. Their coface compatibility is proved from the original
Godement naturality, before any passage to cohomology.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

open SheafCupProduct CuspNormalization

variable (X : TopCat.{0})

/-- The original global Godement cofaces of the original constant ring sheaf. -/
abbrev constantData := GodementRing.sectionData (SheafConstants.complexSheaf X) ⊤

/-- The actual ring-coface map into the first global column. -/
def firstValues : (constantData X).Morphism (TotalSheaf.globalData X).vertical :=
  GodementRing.cofaceMap (RingCochains.augmentation X) (GodementRing.sections ⊤)

/-- The actual ring-coface map into the last global row. -/
def lastValues : (RingCochains.globalData X).Morphism
    (TotalSheaf.globalData X).horizontal where
  f0 := ((GodementRing.inclusion (RingCochains.sheaf X 0)).hom.app (op ⊤)).hom
  f1 := ((GodementRing.inclusion (RingCochains.sheaf X 1)).hom.app (op ⊤)).hom
  f2 := ((GodementRing.inclusion (RingCochains.sheaf X 2)).hom.app (op ⊤)).hom
  f3 := ((GodementRing.inclusion (RingCochains.sheaf X 3)).hom.app (op ⊤)).hom
  comm0 i := congrArg (fun f => (f.hom.app (op ⊤)).hom)
    (GodementRing.inclusion_naturality (RingCochains.coface X 0 i)).symm
  comm1 i := congrArg (fun f => (f.hom.app (op ⊤)).hom)
    (GodementRing.inclusion_naturality (RingCochains.coface X 1 i)).symm
  comm2 i := congrArg (fun f => (f.hom.app (op ⊤)).hom)
    (GodementRing.inclusion_naturality (RingCochains.coface X 2 i)).symm

/-- The degree-one first component is the original additive Godement map on sections. -/
@[simp] theorem firstValues_f1 (a :
    (GodementRing.term1 (SheafConstants.complexSheaf X)).obj.obj (op ⊤)) :
    (firstValues X).f1 a =
      (GodementExact.I1Map (RingCochains.augmentation X)).hom.app (op ⊤) a := rfl

/-- The degree-two first component is the original additive Godement map on sections. -/
@[simp] theorem firstValues_f2 (a :
    (GodementRing.term2 (SheafConstants.complexSheaf X)).obj.obj (op ⊤)) :
    (firstValues X).f2 a =
      (GodementExact.I2Map (RingCochains.augmentation X)).hom.app (op ⊤) a := rfl

/-- The degree-one last component is the original column-unit map on sections. -/
@[simp] theorem lastValues_f1 (a : (RingCochains.sheaf X 1).obj.obj (op ⊤)) :
    (lastValues X).f1 a = (TotalSheaf.columnUnit X 1).hom.app (op ⊤) a := rfl

/-- The degree-two last component is the original column-unit map on sections. -/
@[simp] theorem lastValues_f2 (a : (RingCochains.sheaf X 2).obj.obj (op ⊤)) :
    (lastValues X).f2 a = (TotalSheaf.columnUnit X 2).hom.app (op ⊤) a := rfl

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

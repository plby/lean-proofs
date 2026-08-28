import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationGodementBasic
import Wikipedia.HopfProblem.SheafCupProductGodementCofaceNaturality
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Literal evaluation and Leibniz on the original multiplicative Godement sheaf

The actual product projections and the original skyscraper evaluation
are ring homomorphisms. They jointly determine each section. The actual
prolonged derivative therefore satisfies Leibniz on the original section
rings, not on a replacement product ring.
-/

noncomputable section

open TopCat CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

open SheafCupProduct CuspNormalization.SheafForgetStalk

attribute [local instance] Classical.propDecidable

variable {X : TopCat.{0}} {F G : GodementRing.RingSheaf X}

instance ringSections_preservesLimits (U : Opens X) :
    PreservesLimitsOfSize.{0, 0} (GodementRing.sections U) := by
  let : PreservesLimitsOfSize.{0, 0} (TopCat.Sheaf.forget CommRingCat.{0} X) :=
    (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
      CommRingCat.{0}).rightAdjoint_preservesLimits
  let : PreservesLimitsOfSize.{0, 0}
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ CommRingCat.{0}).obj (op U)) := by
    constructor
    intro J _
    infer_instance
  exact comp_preservesLimits (TopCat.Sheaf.forget CommRingCat.{0} X)
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ CommRingCat.{0}).obj (op U))

/-- The original ring section product is a genuine categorical product. -/
def sectionProductIsLimit (F : GodementRing.RingSheaf X) (U : Opens X) :
    IsLimit (Fan.mk ((GodementRing.sheaf F).obj.obj (op U))
      (fun x => (Pi.π (GodementRing.pointTerm F) x).hom.app (op U))) :=
  isLimitOfHasProductOfPreservesLimit (GodementRing.sections U) (GodementRing.pointTerm F)

/-- Literal ring evaluation of an actual Godement section at a point of its open domain. -/
def evaluation (F : GodementRing.RingSheaf X) (U : Opens X) (x : X) (hx : x ∈ U) :
    (GodementRing.sheaf F).obj.obj (op U) →+* F.presheaf.stalk x :=
  (skyscraperAtIso x (F.presheaf.stalk x) U hx).hom.hom.comp
    ((Pi.π (GodementRing.pointTerm F) x).hom.app (op U)).hom

/-- These actual ring evaluations determine an original Godement section. -/
theorem godementSection_ext (F : GodementRing.RingSheaf X) (U : Opens X)
    (a b : (GodementRing.sheaf F).obj.obj (op U))
    (h : ∀ (x : X) (hx : x ∈ U), evaluation F U x hx a = evaluation F U x hx b) : a = b := by
  apply Concrete.isLimit_ext _ (sectionProductIsLimit F U) a b
  rintro ⟨x⟩
  by_cases hx : x ∈ U
  · exact (skyscraperAtIso x (F.presheaf.stalk x) U hx).commRingCatIsoToRingEquiv.injective
      (h x hx)
  · have ht : IsTerminal ((GodementRing.pointTerm F x).obj.obj (op U)) := by
      change IsTerminal (if x ∈ U then F.presheaf.stalk x else terminal CommRingCat)
      rw [if_neg hx]
      exact terminalIsTerminal
    exact (CommRingCat.subsingleton_of_isTerminal ht).elim _ _

private theorem postcomp_square {C : Type*} [Category C] {A B D E K L : C}
    (f : A ⟶ B) (p : B ⟶ D) (q : A ⟶ E) (g : E ⟶ D)
    (r : D ⟶ K) (s : E ⟶ L) (h : L ⟶ K)
    (hp : f ≫ p = q ≫ g) (hg : g ≫ r = s ≫ h) :
    f ≫ p ≫ r = q ≫ s ≫ h := by
  rw [← Category.assoc, hp, Category.assoc, hg]

/-- The original product prolongation acts by the actual original stalk map. -/
theorem evaluation_lift
    (f : (GodementRing.forgetSheaf X).obj F ⟶ (GodementRing.forgetSheaf X).obj G)
    (U : Opens X) (x : X) (hx : x ∈ U)
    (a : (GodementRing.sheaf F).obj.obj (op U)) :
    evaluation G U x hx (sectionMap (liftMap f) U a) = stalkMap f x (evaluation F U x hx a) := by
  let E := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op U)
  have hc := (E.map_comp _ _).symm.trans
    ((congrArg E.map (liftMap_component f x)).trans (E.map_comp _ _))
  have h := postcomp_square
    (E.map (liftMap f))
    (E.map ((GodementRing.forgetSheaf X).map (Pi.π (GodementRing.pointTerm G) x)))
    (E.map ((GodementRing.forgetSheaf X).map (Pi.π (GodementRing.pointTerm F) x)))
    (E.map (pointLift f x))
    (forgetToAdd.map (skyscraperAtIso x (G.presheaf.stalk x) U hx).hom)
    (forgetToAdd.map (skyscraperAtIso x (F.presheaf.stalk x) U hx).hom)
    (AddCommGrpCat.ofHom (stalkMap f x)) hc (skyscraperLift_eval x (stalkMap f x) U hx)
  exact ConcreteCategory.congr_hom h a

/-- The actual germ inclusion evaluates to the original germ of the original section. -/
theorem evaluation_inclusion (F : GodementRing.RingSheaf X) (U : Opens X)
    (x : X) (hx : x ∈ U) (a : F.obj.obj (op U)) :
    evaluation F U x hx ((GodementRing.inclusion F).hom.app (op U) a) =
      F.presheaf.germ U x hx a := by
  have hc := congrArg (fun k => k.hom.app (op U)) (GodementRing.inclusion_component F x)
  have h := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (skyscraperAtIso x (F.presheaf.stalk x) U hx).hom) hc).trans
      (skyscraperAtIso_unit x F U hx))
  exact ConcreteCategory.congr_hom h a

/-- The genuine derivation on the original multiplicative Godement term. -/
def liftedDerivation (D : SheafDerivation F) : SheafDerivation (GodementRing.sheaf F) where
  map := liftMap D.map
  leibniz U a b := by
    apply godementSection_ext F U
    intro x hx
    rw [evaluation_lift, map_mul, stalkMap_mul, map_add, map_mul, map_mul,
      evaluation_lift, evaluation_lift]

@[simp] theorem liftedDerivation_map (D : SheafDerivation F) :
    (liftedDerivation D).map = liftMap D.map := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

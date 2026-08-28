import Wikipedia.HopfProblem.SheafCupProductGodementExact
import Wikipedia.HopfProblem.SheafCupProductGodementInjective
import Wikipedia.HopfProblem.SheafCupProductResolution

/-!
# Native sheaf cohomology and the actual multiplicative Godement cochains

The original ring sheaf is resolved by the actual iterated product of
its stalks.  The actual stalk contractions prove exactness, and its
complex scalar action proves injectivity of the first two terms.  The
native Ext-defined H¹ and H² therefore identify canonically with the
actual kernel/range quotients of the literal germ-insertion cofaces.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProduct

open GodementRing

variable {X : TopCat.{0}}

/-- The original native sheaf cohomology of the underlying additive sheaf. -/
abbrev H (F : RingSheaf X) (n : ℕ) :=
  CategoryTheory.Sheaf.H.{0} ((forgetSheaf X).obj F) n

/-- The actual four global Godement rings and their actual cofaces. -/
abbrev globalData (F : RingSheaf X) := sectionData F ⊤

/-- The first global complex is literally the alternating germ-insertion complex. -/
theorem globalOneComplex_eq (F : RingSheaf X) :
    (GodementExact.partialResolution F).globalOneComplex =
      SheafCupProductResolution.Coface.oneComplex (globalData F) := rfl

/-- The second global complex has the same literal coface differentials. -/
theorem globalTwoComplex_eq (F : RingSheaf X) :
    (GodementExact.partialResolution F).globalTwoComplex =
      SheafCupProductResolution.Coface.twoComplex (globalData F) := rfl

/-- Native H¹ is canonically the actual first Godement coface quotient. -/
def h1CofaceIso (F : RingSheaf X) (ρ : ℂ →+* End ((forgetSheaf X).obj F)) :
    AddCommGrpCat.of (H F 1) ≅ AddCommGrpCat.of (globalData F).CohomologyOne := by
  let : Injective (GodementExact.partialResolution F).I₀ :=
    godement_injective_of_scalarEnd F ρ
  exact (GodementExact.partialResolution F).h1Iso ≪≫
    SheafCupProductResolution.Coface.oneHomologyIso (globalData F)

/-- Native H² is canonically the actual second Godement coface quotient. -/
def h2CofaceIso (F : RingSheaf X) (ρ : ℂ →+* End ((forgetSheaf X).obj F)) :
    AddCommGrpCat.of (H F 2) ≅ AddCommGrpCat.of (globalData F).CohomologyTwo := by
  let : Injective (GodementExact.partialResolution F).I₀ :=
    godement_injective_of_scalarEnd F ρ
  let : Injective (GodementExact.partialResolution F).I₁ :=
    doubleGodement_injective_of_scalarEnd F ρ
  exact (GodementExact.partialResolution F).h2Iso ≪≫
    SheafCupProductResolution.Coface.twoHomologyIso (globalData F)

/-- The same canonical comparison as an additive equivalence. -/
def h1CofaceEquiv (F : RingSheaf X) (ρ : ℂ →+* End ((forgetSheaf X).obj F)) :
    H F 1 ≃+ (globalData F).CohomologyOne :=
  (h1CofaceIso F ρ).addCommGroupIsoToAddEquiv

/-- The genuine degree-two additive comparison. -/
def h2CofaceEquiv (F : RingSheaf X) (ρ : ℂ →+* End ((forgetSheaf X).obj F)) :
    H F 2 ≃+ (globalData F).CohomologyTwo :=
  (h2CofaceIso F ρ).addCommGroupIsoToAddEquiv

end Wikipedia.HopfProblem.SheafCupProduct

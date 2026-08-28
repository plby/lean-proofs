import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCohomologyAbstractQuotient

/-!
# Native naturality of the degree-one quotient comparison

Morphisms of actual short exact sequences act through their original sheaf
morphisms on global sections and through the original `Sheaf.H.map` on
cohomology.  Both the connecting class and the descended quotient comparison
commute with these maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.CohomologyAbstract

open CuspNormalization.SheafCohomologyResolution

variable {X : TopCat.{0}}
variable {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}

/-- The original short-complex commuting square, evaluated on the top open. -/
theorem sectionMap_comm₂₃ (φ : S ⟶ T) (a : Sections S.X₂) :
    sectionMap φ.τ₃ (sectionMap S.g a) = sectionMap T.g (sectionMap φ.τ₂ a) := by
  calc
    sectionMap φ.τ₃ (sectionMap S.g a) = sectionMap (S.g ≫ φ.τ₃) a := rfl
    _ = sectionMap (φ.τ₂ ≫ T.g) a := congrArg (fun f => sectionMap f a) φ.comm₂₃.symm
    _ = sectionMap T.g (sectionMap φ.τ₂ a) := rfl

/-- Naturality of the genuine positive connecting class, with the original
coefficient map on degree-one sheaf cohomology. -/
theorem classMap_naturality (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (s : Sections S.X₃) :
    classMap hT (sectionMap φ.τ₃ s) =
      CategoryTheory.Sheaf.H.map φ.τ₁ 1 (classMap hS s) := by
  change connecting (unitSheaf X) hT 0
      ((zeroEquiv T.X₃).symm (sectionMap φ.τ₃ s)) = _
  rw [← zeroEquiv_symm_naturality]
  exact connecting_naturality (unitSheaf X) hS hT φ 0 ((zeroEquiv S.X₃).symm s)

/-- The literal third-component section map descends to the original range
quotients by the commuting square of the short-complex morphism. -/
def quotientMap (φ : S ⟶ T) : SectionQuotient S →+ SectionQuotient T :=
  QuotientAddGroup.map (sectionMap S.g).range (sectionMap T.g).range
    (sectionMap φ.τ₃) (by
      rintro s ⟨a, rfl⟩
      exact ⟨sectionMap φ.τ₂ a, (sectionMap_comm₂₃ φ a).symm⟩)

@[simp] theorem quotientMap_mk (φ : S ⟶ T) (s : Sections S.X₃) :
    quotientMap φ (QuotientAddGroup.mk s) =
      QuotientAddGroup.mk (sectionMap φ.τ₃ s) := rfl

/-- Naturality of the descended connecting morphism needs no acyclicity. -/
theorem quotientClassMap_naturality (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (q : SectionQuotient S) :
    quotientClassMap hT (quotientMap φ q) =
      CategoryTheory.Sheaf.H.map φ.τ₁ 1 (quotientClassMap hS q) := by
  refine Quotient.inductionOn' q ?_
  intro s
  exact classMap_naturality hS hT φ s

/-- Under actual middle-sheaf `H¹`-vanishing, the genuine additive
equivalences commute with the original coefficient maps. -/
theorem quotientEquiv_naturality (hS : S.ShortExact) (hT : T.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} T.X₂ 1)]
    (φ : S ⟶ T) (q : SectionQuotient S) :
    quotientEquiv hT (quotientMap φ q) =
      CategoryTheory.Sheaf.H.map φ.τ₁ 1 (quotientEquiv hS q) :=
  quotientClassMap_naturality hS hT φ q

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.CohomologyAbstract

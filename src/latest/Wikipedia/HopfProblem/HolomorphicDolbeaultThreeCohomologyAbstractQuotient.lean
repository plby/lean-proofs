import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCohomologyAbstractBasic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The actual global-section quotient and genuine degree-one cohomology

The quotient is by the literal range of the original sheaf morphism on the
top open set.  Its comparison with `Sheaf.H` is the quotient lift of the
positive Ext connecting morphism, with its exact formula on representatives.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.CohomologyAbstract

variable {X : TopCat.{0}}
variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}

/-- Actual top-open sections modulo the actual global image of the middle
sheaf.  This definition does not change the meaning of `Sheaf.H`. -/
abbrev SectionQuotient (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)) : Type :=
  Sections S.X₃ ⧸ (sectionMap S.g).range

/-- The genuine connecting map, descended to the literal global-section
quotient.  Its definition needs no acyclicity assumption. -/
def quotientClassMap (hS : S.ShortExact) :
    SectionQuotient S →+ CategoryTheory.Sheaf.H.{0} S.X₁ 1 :=
  QuotientAddGroup.lift (sectionMap S.g).range (classMap hS) (classMap_ker hS).symm.le

@[simp] theorem quotientClassMap_mk (hS : S.ShortExact) (s : Sections S.X₃) :
    quotientClassMap hS (QuotientAddGroup.mk s) = classMap hS s := rfl

theorem quotientClassMap_injective (hS : S.ShortExact) :
    Function.Injective (quotientClassMap hS) :=
  (QuotientAddGroup.injective_lift_iff (sectionMap S.g).range
    (classMap hS) (classMap_ker hS).symm.le).mpr (classMap_ker hS).symm

theorem quotientClassMap_surjective (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)] :
    Function.Surjective (quotientClassMap hS) :=
  QuotientAddGroup.lift_surjective_of_surjective (sectionMap S.g).range
    (classMap hS) (classMap_surjective hS) (classMap_ker hS).symm.le

/-- Genuine `H¹` is the actual section quotient whenever the actual middle
sheaf has vanishing `H¹`.  The forward map remains the native connecting map. -/
def quotientEquiv (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)] :
    SectionQuotient S ≃+ CategoryTheory.Sheaf.H.{0} S.X₁ 1 :=
  AddEquiv.ofBijective (quotientClassMap hS)
    ⟨quotientClassMap_injective hS, quotientClassMap_surjective hS⟩

@[simp] theorem quotientEquiv_apply (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)] (q : SectionQuotient S) :
    quotientEquiv hS q = quotientClassMap hS q := rfl

@[simp] theorem quotientEquiv_mk (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)] (s : Sections S.X₃) :
    quotientEquiv hS (QuotientAddGroup.mk s) = classMap hS s := rfl

/-- The comparison on a representative has exactly the original native
degree-zero comparison followed by the original extension class. -/
theorem quotientEquiv_mk_ext (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)] (s : Sections S.X₃) :
    quotientEquiv hS (QuotientAddGroup.mk s) =
      ((CategoryTheory.Sheaf.H.equiv₀ S.X₃
        (show IsTerminal (⊤ : Opens X) from isTerminalTop)).symm s).comp
          hS.extClass rfl :=
  classMap_apply hS s

theorem quotientEquiv_symm_classMap (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)] (s : Sections S.X₃) :
    (quotientEquiv hS).symm (classMap hS s) = QuotientAddGroup.mk s := by
  apply (quotientEquiv hS).injective
  rw [AddEquiv.apply_symm_apply, quotientEquiv_mk]

/-- Two actual global representatives determine the same genuine class
exactly when their difference is a global image through the middle sheaf. -/
theorem classMap_eq_iff (hS : S.ShortExact) (s t : Sections S.X₃) :
    classMap hS s = classMap hS t ↔
      ∃ a : Sections S.X₂, sectionMap S.g a = s - t := by
  calc
    classMap hS s = classMap hS t ↔ classMap hS (s - t) = 0 := by
      rw [map_sub, sub_eq_zero]
    _ ↔ ∃ a : Sections S.X₂, sectionMap S.g a = s - t :=
      classMap_eq_zero_iff hS (s - t)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.CohomologyAbstract

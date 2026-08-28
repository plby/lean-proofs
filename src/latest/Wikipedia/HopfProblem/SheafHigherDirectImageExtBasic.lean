import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Native Hom complexes for Ext and evaluated injective resolutions

The Hom complex out of an object concentrated in degree zero is
isomorphic to the literal complex obtained by evaluating the
preadditive coyoneda functor.  We also record ordinary cycle classes
in actual categorical homology, so the comparison can be computed on
the original Ext cocycle representatives.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge

universe u

variable {C : Type u} [Category.{0} C] [Preadditive C] [HasZeroObject C]

/-- A genuine complex isomorphism, not only an equivalence of its terms. -/
def singleHomComplexIso (A : C) (K : CochainComplex C ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj A) K ≅
      ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj K := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (Cochain.fromSingleEquiv (X := A) (K := K) (zero_add n)).toAddCommGrpIso) ?_
  intro i j _
  apply AddCommGrpCat.ext
  intro z
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z i (zero_add i)
  change (Cochain.fromSingleEquiv (zero_add i) (Cochain.fromSingleMk f (zero_add i))) ≫
      K.d i j = Cochain.fromSingleEquiv (zero_add j)
        (δ i j (Cochain.fromSingleMk f (zero_add i)))
  rw [Cochain.fromSingleEquiv_fromSingleMk, Cochain.δ_fromSingleMk f (zero_add i)
    j j (zero_add j), Cochain.fromSingleEquiv_fromSingleMk]

@[simp] theorem singleHomComplexIso_hom_f (A : C) (K : CochainComplex C ℤ)
    (n : ℤ) (z : Cochain ((CochainComplex.singleFunctor C 0).obj A) K n) :
    (singleHomComplexIso A K).hom.f n z = Cochain.fromSingleEquiv (zero_add n) z := rfl

@[simp] theorem singleHomComplexIso_inv_f (A : C) (K : CochainComplex C ℤ)
    (n : ℤ) (f : A ⟶ K.X n) :
    (singleHomComplexIso A K).inv.f n f = Cochain.fromSingleMk f (zero_add n) := rfl

section Classes

/-- A literal cocycle class in native short-complex homology. -/
def shortCycleClass (S : ShortComplex AddCommGrpCat.{0}) (z : S.X₂)
    (hz : S.g z = 0) : S.homology :=
  S.homologyπ (S.abCyclesIso.inv ⟨z, hz⟩)

theorem shortCycleClass_surjective (S : ShortComplex AddCommGrpCat.{0}) (x : S.homology) :
    ∃ (z : S.X₂) (hz : S.g z = 0), shortCycleClass S z hz = x := by
  obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective S.homologyπ).mp inferInstance x
  let z := S.abCyclesIso.hom y
  refine ⟨z.val, z.property, ?_⟩
  exact congrArg S.homologyπ (S.abCyclesIso.addCommGroupIsoToAddEquiv.symm_apply_apply y)

/-- Homology maps of native short complexes preserve their literal representatives. -/
theorem shortHomologyMap_cycleClass {S T : ShortComplex AddCommGrpCat.{0}}
    (f : S ⟶ T) (z : S.X₂) (hz : S.g z = 0) (hfz : T.g (f.τ₂ z) = 0) :
    ShortComplex.homologyMap f (shortCycleClass S z hz) =
      shortCycleClass T (f.τ₂ z) hfz := by
  have hc : ShortComplex.cyclesMap f (S.abCyclesIso.inv ⟨z, hz⟩) =
      T.abCyclesIso.inv ⟨f.τ₂ z, hfz⟩ := by
    apply (AddCommGrpCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, ShortComplex.abCyclesIso_inv_apply_iCycles,
      ShortComplex.abCyclesIso_inv_apply_iCycles]
  unfold shortCycleClass
  rw [← ConcreteCategory.comp_apply, ShortComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, hc]

variable {ι : Type*} {c : ComplexShape ι}

/-- The class in native categorical homology of a literal cocycle. -/
def cycleClass (K : HomologicalComplex AddCommGrpCat.{0} c) (n : ι)
    (z : K.X n) (hz : (K.sc n).g z = 0) : K.homology n :=
  shortCycleClass (K.sc n) z hz

theorem cycleClass_surjective (K : HomologicalComplex AddCommGrpCat.{0} c) (n : ι)
    (x : K.homology n) : ∃ (z : K.X n) (hz : (K.sc n).g z = 0), cycleClass K n z hz = x :=
  shortCycleClass_surjective (K.sc n) x

/-- Native homology maps preserve literal cocycle representatives. -/
theorem homologyMap_cycleClass {K L : HomologicalComplex AddCommGrpCat.{0} c}
    (f : K ⟶ L) (n : ι) (z : K.X n) (hz : (K.sc n).g z = 0)
    (hfz : (L.sc n).g (f.f n z) = 0) :
    HomologicalComplex.homologyMap f n (cycleClass K n z hz) =
      cycleClass L n (f.f n z) hfz :=
  shortHomologyMap_cycleClass
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat c n).map f) z hz hfz

end Classes

end Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge

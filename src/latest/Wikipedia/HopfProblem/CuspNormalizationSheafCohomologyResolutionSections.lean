import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionHigher
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Limits.Preorder

/-!
# Genuine sheaf cohomology and the actual global-sections complex

The only degree-zero comparison used here is Mathlib's canonical
`Sheaf.H.equiv₀`, with its proved naturality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

variable (X : TopCat.{0})

/-- Literal global sections on the top open set. -/
def globalSectionsFunctor : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)

instance : (globalSectionsFunctor X).Additive where
  map_add := by intros; rfl

instance : PreservesFiniteLimits (globalSectionsFunctor X) := by
  let adj : constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⊣
      globalSectionsFunctor X :=
    constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}
      (show IsTerminal (⊤ : Opens X) from isTerminalTop)
  exact ⟨fun _ _ _ => adj.rightAdjoint_preservesLimits.preservesLimitsOfShape⟩

/-- The small actual sheaf category has the genuine small Ext groups. -/
instance actualSheafHasExt : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  IsGrothendieckAbelian.hasExt _

/-- The actual constant integer sheaf used by Mathlib to define `Sheaf.H`. -/
abbrev unitSheaf : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ULift.{0} ℤ))

variable {X}

/-- The existing additive group structure on the genuine Ext group. -/
instance actualCohomologyAddCommGroup (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} F n) := Ext.instAddCommGroup

/-- Mathlib's genuine degree-zero sheaf cohomology comparison. -/
def h0GlobalIso (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    AddCommGrpCat.of (Ext.{0} (unitSheaf X) F 0) ≅
      (globalSectionsFunctor X).obj F :=
  (CategoryTheory.Sheaf.H.equiv₀ F
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)).toAddCommGrpIso

theorem h0GlobalIso_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) :
    (extFunctorObj (unitSheaf X) 0).map f ≫ (h0GlobalIso G).hom =
      (h0GlobalIso F).hom ≫ (globalSectionsFunctor X).map f := by
  ext x
  exact (CategoryTheory.Sheaf.H.equiv₀_naturality
    (show IsTerminal (⊤ : Opens X) from isTerminalTop) f x).symm

namespace AugmentedResolution

variable (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- The actual global-sections complex of the three genuine sheaf terms. -/
abbrev globalComplex : ShortComplex AddCommGrpCat := R.complex.map (globalSectionsFunctor X)

/-- Canonical degree-zero comparisons give an isomorphism of the
actual three-term complexes. -/
def extZeroGlobalIso : R.extZeroComplex (unitSheaf X) ≅ R.globalComplex :=
  ShortComplex.isoMk (h0GlobalIso R.complex.X₁) (h0GlobalIso R.complex.X₂)
    (h0GlobalIso R.complex.X₃) (h0GlobalIso_naturality R.complex.f).symm
      (h0GlobalIso_naturality R.complex.g).symm

/-- Degree-one genuine sheaf cohomology is the actual homology of
the global-sections complex. -/
def h1Iso [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 1) ≅ R.globalComplex.homology := by
  letI : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  exact R.extOneIso (unitSheaf X) ≪≫ ShortComplex.homologyMapIso R.extZeroGlobalIso

/-- Degree-two genuine sheaf cohomology is the actual cokernel of
the last global-sections map. -/
def h2Iso [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 2) ≅ cokernel R.globalComplex.g := by
  letI : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  letI : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)›
  letI : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)›
  exact R.extTwoIso (unitSheaf X) ≪≫
    cokernel.mapIso ((R.extZeroComplex (unitSheaf X)).g) R.globalComplex.g
      (h0GlobalIso R.complex.X₂) (h0GlobalIso R.complex.X₃)
      (h0GlobalIso_naturality R.complex.g)

/-- Vanishing of genuine higher sheaf cohomology above the length of
the actual acyclic resolution. -/
theorem h_subsingleton_above_two
    (hA : ∀ n : ℕ, Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ (n + 1)))
    (hB : ∀ n : ℕ, Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ (n + 1)))
    (hD : ∀ n : ℕ, Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₃ (n + 1))) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} R.F (n + 3)) :=
  R.ext_subsingleton_above_two (unitSheaf X) hA hB hD n

end AugmentedResolution

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

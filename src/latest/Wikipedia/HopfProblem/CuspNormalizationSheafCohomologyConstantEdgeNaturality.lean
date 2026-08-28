import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyConstantEdgeGlobal

/-!
# Naturality of the actual sheaf edge comparison

The maps below are induced by the original augmentation and resolution
morphisms. In the mixed comparison the source retains its H² edge
kernel, while the target may use its genuinely proved H² acyclicity.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

open SheafCohomologyResolution

section Category

universe v u

variable {C : Type u} [Category.{v} C]

theorem isIso_of_comparison {A B V W : C} (f : A ⟶ B) (e : A ≅ V) (e' : B ≅ W)
    (g : V ⟶ W) [IsIso g] (h : f ≫ e'.hom = e.hom ≫ g) : IsIso f := by
  have : IsIso (f ≫ e'.hom) := h.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right f e'.hom

end Category

variable {X : TopCat.{0}} {R S : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (φ : R.Hom S)

/-- The actual kernel map induced by the original H² map of coefficient sheaves. -/
def h2EdgeKernelMap : h2EdgeKernel R ⟶ h2EdgeKernel S :=
  extEdgeKernelMap φ (unitSheaf X)

@[reassoc] theorem h2EdgeKernelMap_ι :
    h2EdgeKernelMap φ ≫ kernel.ι (h2EdgeMap S) =
      kernel.ι (h2EdgeMap R) ≫ (CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation :=
  extEdgeKernelMap_ι φ (unitSheaf X)

theorem h2EdgeIso_naturality
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₂ 1)] :
    h2EdgeKernelMap φ ≫ (h2EdgeIso S).hom = (h2EdgeIso R).hom ≫ φ.globalCokernelMap := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) S.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) S.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₂ 1)›
  change extEdgeKernelMap φ (unitSheaf X) ≫
      ((extEdgeIso S (unitSheaf X)).hom ≫ S.extGlobalCokernelIso.hom) =
    ((extEdgeIso R (unitSheaf X)).hom ≫ R.extGlobalCokernelIso.hom) ≫ φ.globalCokernelMap
  exact comparison_compose
    (extEdgeIso R (unitSheaf X)).hom R.extGlobalCokernelIso.hom
    (extEdgeIso S (unitSheaf X)).hom S.extGlobalCokernelIso.hom
    (extEdgeKernelMap φ (unitSheaf X)) (φ.extCokernelMap (unitSheaf X)) φ.globalCokernelMap
    (extEdgeIso_naturality φ (unitSheaf X)) φ.extGlobalCokernelIso_naturality

/-- The original H² coefficient map restricted to the source's literal edge kernel. -/
def h2EdgeToCohomology : h2EdgeKernel R ⟶ AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} S.F 2) :=
  kernel.ι (h2EdgeMap R) ≫ (CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation

/-- The source edge kernel maps to the target H² with the actual
global-cokernel comparison. Only the target's first term requires H² vanishing. -/
theorem h2EdgeToCohomology_naturality
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₂ 1)] :
    h2EdgeToCohomology φ ≫ S.h2Iso.hom = (h2EdgeIso R).hom ≫ φ.globalCokernelMap := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) S.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) S.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 2)›
  let : Subsingleton (Ext.{0} (unitSheaf X) S.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₂ 1)›
  change extEdgeToCohomology φ (unitSheaf X) ≫
      ((S.extTwoIso (unitSheaf X)).hom ≫ S.extGlobalCokernelIso.hom) =
    ((extEdgeIso R (unitSheaf X)).hom ≫ R.extGlobalCokernelIso.hom) ≫ φ.globalCokernelMap
  exact comparison_compose
    (extEdgeIso R (unitSheaf X)).hom R.extGlobalCokernelIso.hom
    (S.extTwoIso (unitSheaf X)).hom S.extGlobalCokernelIso.hom
    (extEdgeToCohomology φ (unitSheaf X)) (φ.extCokernelMap (unitSheaf X)) φ.globalCokernelMap
    (extEdgeToCohomology_naturality φ (unitSheaf X)) φ.extGlobalCokernelIso_naturality

/-- If the actual global-cokernel comparison is an isomorphism, so is
the original H² coefficient map restricted to the source edge kernel. -/
theorem h2EdgeToCohomology_isIso
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₂ 1)]
    [IsIso φ.globalCokernelMap] : IsIso (h2EdgeToCohomology φ) :=
  isIso_of_comparison (h2EdgeToCohomology φ) (h2EdgeIso R) S.h2Iso φ.globalCokernelMap
    (h2EdgeToCohomology_naturality φ)

/-- The genuine coefficient map on H¹ is an isomorphism when the
actual global complexes are isomorphic and their first terms have vanishing H¹. -/
theorem h1Map_isIso_of_globalMap
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.complex.X₁ 1)]
    [IsIso φ.globalMap] :
    IsIso ((CategoryTheory.Sheaf.functorH _ 1).map φ.augmentation) :=
  isIso_of_comparison ((CategoryTheory.Sheaf.functorH _ 1).map φ.augmentation)
    R.h1Iso S.h1Iso (ShortComplex.homologyMap φ.globalMap) φ.h1Iso_naturality

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

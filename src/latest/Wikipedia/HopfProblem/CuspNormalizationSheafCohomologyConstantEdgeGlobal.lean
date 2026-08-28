import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyConstantEdgeExtNaturality
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionNaturality

/-!
# Literal global sections and the actual degree-two sheaf edge kernel

The canonical degree-zero Ext/section comparison gives an isomorphism
from the literal kernel of `H²(F) → H²(A)` to the actual cokernel of
`Γ(B) → Γ(D)`. Only the two degree-one term vanishings are used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

open SheafCohomologyResolution

section Category

universe v u

variable {C : Type u} [Category.{v} C]

theorem iso_inv_comp_comparison {A B K Q Q' : C} (e : A ≅ B)
    (c : A ⟶ K) (i : K ⟶ Q) (j : Q ⟶ Q') (q : A ⟶ Q) (p : B ⟶ Q')
    (hc : c ≫ i = q) (hq : q ≫ j = e.hom ≫ p) :
    (e.inv ≫ c) ≫ (i ≫ j) = p := by
  calc
    (e.inv ≫ c) ≫ (i ≫ j) = e.inv ≫ (c ≫ i) ≫ j := by simp only [Category.assoc]
    _ = e.inv ≫ q ≫ j := by rw [hc]
    _ = e.inv ≫ e.hom ≫ p := by rw [hq]
    _ = p := e.inv_hom_id_assoc _

theorem comparison_compose {A B D A' B' D' : C}
    (a : A ⟶ B) (b : B ⟶ D) (a' : A' ⟶ B') (b' : B' ⟶ D')
    (x : A ⟶ A') (y : B ⟶ B') (z : D ⟶ D')
    (ha : x ≫ a' = a ≫ y) (hb : y ≫ b' = b ≫ z) :
    x ≫ (a' ≫ b') = (a ≫ b) ≫ z := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

end Category

variable {X : TopCat.{0}} (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- The original H² map induced by the actual augmentation into the first term. -/
def h2EdgeMap : AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 2) ⟶
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2) :=
  (CategoryTheory.Sheaf.functorH _ 2).map R.ι

/-- The literal categorical kernel of the actual H² augmentation map. -/
abbrev h2EdgeKernel := kernel (h2EdgeMap R)

/-- Actual global sections of the last term represent classes in the literal edge kernel. -/
def globalEdgeConnecting : (globalSectionsFunctor X).obj R.complex.X₃ ⟶ h2EdgeKernel R :=
  (h0GlobalIso R.complex.X₃).inv ≫ extEdgeConnecting R (unitSheaf X)

@[reassoc] theorem globalEdgeConnecting_ι :
    globalEdgeConnecting R ≫ kernel.ι (h2EdgeMap R) = R.globalConnectingTwo :=
  Eq.trans (Category.assoc _ _ _)
    (congrArg (fun f => (h0GlobalIso R.complex.X₃).inv ≫ f)
      (extEdgeConnecting_ι R (unitSheaf X)))

theorem globalEdgeConnecting_surjective
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)] :
    Function.Surjective (globalEdgeConnecting R) := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)›
  exact surjective_iso_inv_comp (h0GlobalIso R.complex.X₃)
    (extEdgeConnecting R (unitSheaf X)) (extEdgeConnecting_surjective R (unitSheaf X))

theorem globalEdgeConnecting_epi
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)] :
    Epi (globalEdgeConnecting R) :=
  (AddCommGrpCat.epi_iff_surjective _).mpr (globalEdgeConnecting_surjective R)

/-- The genuine edge kernel is the actual last global-section cokernel.
The first term's H² is not assumed to vanish. -/
def h2EdgeIso
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)] :
    h2EdgeKernel R ≅ cokernel R.globalComplex.g := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)›
  exact (extEdgeIso R (unitSheaf X)) ≪≫ R.extGlobalCokernelIso

/-- The edge comparison carries actual double-connecting representatives
to their ordinary classes in the literal global cokernel. -/
theorem h2EdgeIso_connecting
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)] :
    globalEdgeConnecting R ≫ (h2EdgeIso R).hom = cokernel.π R.globalComplex.g := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)›
  exact iso_inv_comp_comparison (h0GlobalIso R.complex.X₃)
    (extEdgeConnecting R (unitSheaf X)) (extEdgeIso R (unitSheaf X)).hom
    R.extGlobalCokernelIso.hom (cokernel.π (R.extZeroComplex (unitSheaf X)).g)
    (cokernel.π R.globalComplex.g) (extEdgeIso_connecting R (unitSheaf X))
    R.extGlobalCokernelIso_π

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

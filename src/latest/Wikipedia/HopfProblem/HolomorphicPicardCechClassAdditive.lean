import Wikipedia.HopfProblem.HolomorphicPicardCechBiproduct
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassNaturality
import Wikipedia.HopfProblem.HolomorphicPicardCechCoboundaryClass
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1ExtGlobal

/-!
# Additivity of the genuine Čech-to-sheaf-cohomology map

Naturality for the original sheaf biproduct, its two projections, and
their sum proves additivity in native derived cohomology. Consequently
the actual extension class factors as an additive map through cover
cohomology. No Čech comparison or additivity premise is introduced.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} {U : ι → Opens X}

/-- The original `Ext` group structure, exposed for the native topological
sheaf synonym as well. No new cohomology group is defined. -/
instance nativeHAddCommGroup (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} F n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

theorem classOf_add (c d : CechOneCocycle F U) (hU : ∀ x : X, ∃ i, x ∈ U i) :
    classOf (c + d) hU = classOf c hU + classOf d hU := by
  let p₁ : F ⊞ F ⟶ F := biprod.fst
  let p₂ : F ⊞ F ⟶ F := biprod.snd
  let q := Cech.pairCocycle c d
  have hsum := (classOf_naturality (p₁ + p₂) q hU).trans
    (congrArg (fun t : CechOneCocycle F U => classOf t hU)
      (Cech.mapCocycle_sum_pair c d))
  have h₁ := (classOf_naturality p₁ q hU).trans
    (congrArg (fun t : CechOneCocycle F U => classOf t hU)
      (Cech.mapCocycle_fst_pair c d))
  have h₂ := (classOf_naturality p₂ q hU).trans
    (congrArg (fun t : CechOneCocycle F U => classOf t hU)
      (Cech.mapCocycle_snd_pair c d))
  exact hsum.symm.trans ((CategoryTheory.Sheaf.H.map_add_apply p₁ p₂ (classOf q hU)).trans
    (congrArg₂ (· + ·) h₁ h₂))

@[simp] theorem classOf_zero (hU : ∀ x : X, ∃ i, x ∈ U i) :
    classOf (0 : CechOneCocycle F U) hU = 0 := by
  have h := classOf_add (0 : CechOneCocycle F U) 0 hU
  simp only [zero_add] at h
  exact (add_eq_left).mp h.symm

/-- The genuine derived extension class, now as a proved additive map. -/
def classHom (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) :
    CechOneCocycle F U →+ CategoryTheory.Sheaf.H.{0} F 1 where
  toFun c := classOf c hU
  map_zero' := classOf_zero hU
  map_add' c d := classOf_add c d hU

@[simp] theorem classHom_apply (hU : ∀ x : X, ∃ i, x ∈ U i) (c : CechOneCocycle F U) :
    classHom F hU c = classOf c hU := rfl

theorem classOf_neg (c : CechOneCocycle F U) (hU : ∀ x : X, ∃ i, x ∈ U i) :
    classOf (-c) hU = -classOf c hU := map_neg (classHom F hU) c

theorem classOf_sub (c d : CechOneCocycle F U) (hU : ∀ x : X, ∃ i, x ∈ U i) :
    classOf (c - d) hU = classOf c hU - classOf d hU := map_sub (classHom F hU) c d

/-- The comparison from actual cover cohomology to actual native sheaf
cohomology. This is constructed from the proved extension class. -/
def coverCohomologyClassHom (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) :
    Cech.CoverCohomology F U →+ CategoryTheory.Sheaf.H.{0} F 1 :=
  QuotientAddGroup.lift (Cech.coboundary F U).range (classHom F hU) (by
    rintro c ⟨b, rfl⟩
    change classOf (Cech.coboundary F U b) hU = 0
    exact (classOf_eq_of_coboundary (Cech.coboundary F U b) 0 hU b
      (sub_zero _)).trans (classOf_zero hU))

@[simp] theorem coverCohomologyClassHom_classOf
    (hU : ∀ x : X, ∃ i, x ∈ U i) (c : CechOneCocycle F U) :
    coverCohomologyClassHom F hU (Cech.classOf F U c) = classOf c hU := rfl

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

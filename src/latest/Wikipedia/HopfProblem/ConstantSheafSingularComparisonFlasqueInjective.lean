import Wikipedia.HopfProblem.SheafHigherDirectImageSectionsBasic
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Injective abelian sheaves are flasque

The actual free abelian sheaf of an open set represents its sections.
An inclusion of opens induces a monomorphism of these representing
sheaves: Yoneda, the free abelian group functor, and sheafification each
preserve monomorphisms. Injectivity then extends every section, with
the resulting equality checked against the original restriction map.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.Flasque

open HolomorphicSheafCohomology.OpenRestriction
open SheafHigherDirectImage.Sections

variable {X : TopCat.{0}}

/-- An actual inclusion of opens induces a monomorphism between the
free abelian sheaves representing sections on those opens. -/
theorem freeOpen_map_mono {U V : Opens X} (i : U ⟶ V) :
    Mono ((freeOpenFunctor X).map i) := by
  have : ∀ W, Mono ((yoneda.map i).app W) := by
    intro W
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro f g _
    change (f : W.unop ⟶ U) = g
    exact Subsingleton.elim (α := W.unop ⟶ U) f g
  have : Mono (yoneda.map i) := NatTrans.mono_of_mono_app _
  change Mono ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
    (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free))
  infer_instance

/-- Every injective abelian sheaf on the small open-set site is flasque. -/
theorem injective_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{0} X) [Injective F] :
    TopCat.Sheaf.IsFlasque F where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    have := freeOpen_map_mono i.unop
    obtain ⟨h, hh⟩ := Injective.factors ((freeHomEquiv V.unop F).symm s)
      ((freeOpenFunctor X).map i.unop)
    refine ⟨freeHomEquiv U.unop F h, ?_⟩
    calc
      F.obj.map i (freeHomEquiv U.unop F h) =
          freeHomEquiv V.unop F ((freeOpenFunctor X).map i.unop ≫ h) := by
        simpa using (freeHomEquiv_naturality_open i.unop F h).symm
      _ = s := by
        rw [hh]
        exact (freeHomEquiv V.unop F).apply_symm_apply s

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.Flasque

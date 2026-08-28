import Wikipedia.HopfProblem.HolomorphicExponentialSheafIntegersBasic
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Sheafification of exact presheaf extensions

The actual sheafification functor preserves finite limits and colimits,
so it preserves exactness and monomorphisms. A locally surjective
presheaf map becomes an epimorphism of actual sheaves. Consequently a
presheaf complex that is exact, injective on the left, and locally
surjective on the right sheafifies to a genuine short exact sequence.

Componentwise exactness of additive presheaves is also detected using
the actual homology comparison under evaluation.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

variable {X : TopCat.{0}}

/-- The short complex obtained by applying the actual sheafification
functor to all three presheaves and their maps. -/
def sheafifiedComplex (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{0} X)) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) := by
  change ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) at S
  change ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
  exact S.map (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})

/-- Exactness at every open set implies exactness in the actual
category of additive presheaves. -/
theorem presheafExact_of_app_exact
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{0} X))
    (h : ∀ V, Function.Exact (S.f.app V) (S.g.app V)) : S.Exact := by
  change ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) at S
  apply S.exact_iff_isZero_homology.mpr
  apply Functor.isZero
  intro V
  let ev := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj V
  have hV : (S.map ev).Exact :=
    (S.map ev).ab_exact_iff_function_exact.mpr (h V)
  exact ((S.map ev).exact_iff_isZero_homology.mp hV).of_iso (S.mapHomologyIso ev).symm

/-- Sheafification preserves exactness by its genuine finite-limit and
finite-colimit preservation, without an additional exactness hypothesis. -/
theorem sheafifiedComplex_exact
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{0} X)) (hS : S.Exact) :
    (sheafifiedComplex S).Exact := by
  change ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) at S
  have hs : (S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0})).Exact := hS
  have hm : (S.map (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})).Exact :=
    hs.map (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
  exact hm

/-- A locally surjective additive presheaf morphism sheafifies to a
genuine epimorphism, even if it is not surjective on global sections. -/
theorem sheafification_epi_of_locallySurjective
    {P Q : TopCat.Presheaf AddCommGrpCat.{0} X} (f : P ⟶ Q)
    (hf : TopCat.Presheaf.IsLocallySurjective f) :
    Epi ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map f) := by
  have hloc : CategoryTheory.Sheaf.IsLocallySurjective
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map f) :=
    (CategoryTheory.Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      (Opens.grothendieckTopology X) f).mpr hf
  exact CategoryTheory.Sheaf.epi_of_isLocallySurjective _

/-- Exactness, a monic first arrow, and local surjectivity of the second
arrow give a genuine short exact sequence after actual sheafification. -/
theorem sheafifiedComplex_shortExact
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{0} X))
    (hS : S.Exact) (hf : Mono S.f) (hg : TopCat.Presheaf.IsLocallySurjective S.g) :
    (sheafifiedComplex S).ShortExact := by
  let : Mono S.f := hf
  refine { exact := sheafifiedComplex_exact S hS, mono_f := ?_, epi_g := ?_ }
  · change Mono ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map S.f)
    infer_instance
  · exact sheafification_epi_of_locallySurjective S.g hg

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

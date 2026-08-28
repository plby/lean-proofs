import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Local representatives in the actual sheafification

All maps below are the native sheafification unit. Its actual stalk map
is an isomorphism, so equal germs of sheafified representatives already
come from equality of the original representatives on a smaller open
neighborhood. These facts retain the original presheaf elements.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.Sheafification

variable {X : TopCat.{0}}

/-- Native sheafification on the actual open-set site. -/
abbrev sheaf (P : TopCat.Presheaf AddCommGrpCat.{0} X) :
    TopCat.Sheaf AddCommGrpCat.{0} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj P

/-- Its original unit on presheaves. -/
def unit (P : TopCat.Presheaf AddCommGrpCat.{0} X) : P ⟶ (sheaf P).obj :=
  toSheafify (Opens.grothendieckTopology X) P

/-- The native unit is an isomorphism on each actual colimit stalk. -/
instance unit_stalk_isIso (P : TopCat.Presheaf AddCommGrpCat.{0} X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unit P)) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P

/-- The actual stalk map of the unit is injective. -/
theorem unit_stalk_injective (P : TopCat.Presheaf AddCommGrpCat.{0} X) (x : X) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (unit P)) :=
  ((ConcreteCategory.isIso_iff_bijective _).mp (unit_stalk_isIso P x)).injective

/-- Every sheafified section has an original representative near every point. -/
theorem exists_local_representative (P : TopCat.Presheaf AddCommGrpCat.{0} X)
    (U : Opens X) (s : (sheaf P).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (t : P.obj (op V)), x ∈ V ∧
      (unit P).app (op V) t = (sheaf P).obj.map (homOfLE hVU).op s := by
  have hloc : TopCat.Presheaf.IsLocallySurjective (unit P) := by
    change CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X) (toSheafify (Opens.grothendieckTopology X) P)
    infer_instance
  obtain ⟨V, hVU, ⟨t, ht⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (unit P)).mp hloc U s x hx
  exact ⟨V, hVU, t, hxV, ht⟩

/-- Equality of sheafified representative germs is equality of the
original presheaf germs, not merely a comparison of chosen values. -/
theorem germ_unit_eq_iff (P : TopCat.Presheaf AddCommGrpCat.{0} X)
    (U V : Opens X) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : P.obj (op U)) (t : P.obj (op V)) :
    TopCat.Presheaf.germ (sheaf P).obj U x hxU ((unit P).app (op U) s) =
      TopCat.Presheaf.germ (sheaf P).obj V x hxV ((unit P).app (op V) t) ↔
        P.germ U x hxU s = P.germ V x hxV t := by
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ← TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact (unit_stalk_injective P x).eq_iff

/-- Equal sheafified representative germs agree as original sections
after literal restriction to a common smaller neighborhood. -/
theorem exists_restriction_eq_of_germ_unit_eq
    (P : TopCat.Presheaf AddCommGrpCat.{0} X)
    (U V : Opens X) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : P.obj (op U)) (t : P.obj (op V))
    (h : TopCat.Presheaf.germ (sheaf P).obj U x hxU ((unit P).app (op U) s) =
      TopCat.Presheaf.germ (sheaf P).obj V x hxV ((unit P).app (op V) t)) :
    ∃ (W : Opens X), x ∈ W ∧ ∃ (i : W ⟶ U) (j : W ⟶ V),
      P.map i.op s = P.map j.op t := by
  obtain ⟨W, hxW, i, j, hij⟩ :=
    P.germ_eq _ _ _ _ _ ((germ_unit_eq_iff P U V x hxU hxV s t).mp h)
  exact ⟨W, hxW, i, j, hij⟩

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.Sheafification

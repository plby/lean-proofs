import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Simultaneous representatives of finitely many actual stalk elements

On a Hausdorff space, finitely many points have pairwise disjoint open
neighborhoods. Actual stalk representatives can be restricted to these
neighborhoods and glued by the sheaf condition. This includes the empty
finite set: its empty family glues over the empty open set.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafFiniteStalk

variable {X : TopCat.{0}} [T2Space X]

/-- Any family of actual stalk elements at finitely many distinct points
has one actual section representative on a neighborhood of those points. -/
theorem exists_section_germ_eq_of_finite
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) {s : Set X} (hs : s.Finite)
    (t : ∀ x : s, F.presheaf.stalk x.val) :
    ∃ (U : Opens X) (hU : s ⊆ U) (u : F.presheaf.obj (op U)),
      ∀ x : s, F.presheaf.germ U x.val (hU x.property) u = t x := by
  classical
  obtain ⟨V, hV, hdisj⟩ := hs.t2_separation
  let W : s → Opens X := fun x => ⟨V x.val, (hV x.val).2⟩
  choose U hUW hU u hu using fun x : s =>
    F.presheaf.exists_le_germ_eq (t x) (V := W x) (hV x.val).1
  have hcompatible : TopCat.Presheaf.IsCompatible F.presheaf U u := by
    intro x y
    by_cases hxy : x = y
    · subst y
      rfl
    · apply TopCat.Presheaf.section_ext F (U x ⊓ U y) _ _
      intro z hz
      exfalso
      have hne : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
      exact Set.disjoint_left.mp (hdisj x.property y.property hne)
        (hUW x hz.1) (hUW y hz.2)
  obtain ⟨v, hv, _⟩ := F.existsUnique_gluing U u hcompatible
  have hsubset : s ⊆ (iSup U : Opens X) := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hU ⟨x, hx⟩⟩
  refine ⟨iSup U, hsubset, v, ?_⟩
  intro x
  calc
    F.presheaf.germ (iSup U) x.val (hsubset x.property) v =
        F.presheaf.germ (U x) x.val (hU x)
          (F.presheaf.map (Opens.leSupr U x).op v) :=
      (F.presheaf.germ_res_apply (Opens.leSupr U x) x.val (hU x) v).symm
    _ = F.presheaf.germ (U x) x.val (hU x) (u x) := by rw [hv x]
    _ = t x := hu x

end Wikipedia.HopfProblem.CuspNormalization.SheafFiniteStalk

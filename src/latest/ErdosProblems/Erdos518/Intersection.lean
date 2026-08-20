/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Configuration
import ErdosProblems.Erdos518.Induction

/-!
# Opposite-colour intersections in a normalized counterexample

This file specializes the generic deletion-and-induction argument to `Configuration`.  It records
both orientations of the fact that paths of opposite colours share at most `r` vertices, and the
frequently used formulation excluding `r + 1` vertices from the support of the opposite path.
-/

open scoped SimpleGraph

namespace Erdos518
namespace Configuration

universe u

variable {V : Type u} [Fintype V] (C : Configuration V)

noncomputable local instance intersectionDecidableEq : DecidableEq V := Classical.decEq V

/-- The counterexample field says separately that neither colour has a cover by `C.c` paths. -/
lemma cover_failures :
    (¬ HasPathCoverAtMost C.G C.c) ∧ (¬ HasPathCoverAtMost C.Gᶜ C.c) := by
  have hcounter :
      ¬ (HasPathCoverAtMost C.G C.c ∨ HasPathCoverAtMost C.Gᶜ C.c) := by
    simpa [Erdos518ForType, c, n] using C.isCounterexample
  exact ⟨fun h ↦ hcounter (Or.inl h), fun h ↦ hcounter (Or.inr h)⟩

/-- Any path in the `G` colour and any path in the complementary colour share at most `C.r`
vertices.  This is the configuration-level form of the opposite-colour intersection lemma. -/
lemma oppositeColour_path_intersection_card_le
    {Pr Pb : List V} (hPr : IsPath C.G Pr) (hPb : IsPath C.Gᶜ Pb) :
    (pathSupport Pr ∩ pathSupport Pb).card ≤ C.r := by
  have hcard : Fintype.card V = C.c ^ 2 + C.r := by
    simpa [n] using C.n_eq_c_sq_add_r
  exact Erdos518.oppositeColour_path_intersection_card_le_local
    C.G C.c C.r hcard C.induced_minimality
    C.cover_failures.1 C.cover_failures.2 hPr hPb

/-- The same intersection estimate with the complementary-colour path written first. -/
lemma compl_path_inter_path_card_le
    {Pb Pr : List V} (hPb : IsPath C.Gᶜ Pb) (hPr : IsPath C.G Pr) :
    (pathSupport Pb ∩ pathSupport Pr).card ≤ C.r := by
  simpa [Finset.inter_comm] using C.oppositeColour_path_intersection_card_le hPr hPb

/-- A `G`-path cannot contain `r + 1` vertices from the support of a complementary-colour
path. -/
lemma not_r_add_one_le_path_inter_compl_path
    {Pr Pb : List V} (hPr : IsPath C.G Pr) (hPb : IsPath C.Gᶜ Pb) :
    ¬ C.r + 1 ≤ (pathSupport Pr ∩ pathSupport Pb).card := by
  have hle := C.oppositeColour_path_intersection_card_le hPr hPb
  omega

/-- A complementary-colour path cannot contain `r + 1` vertices from the support of a
`G`-path. -/
lemma not_r_add_one_le_compl_path_inter_path
    {Pb Pr : List V} (hPb : IsPath C.Gᶜ Pb) (hPr : IsPath C.G Pr) :
    ¬ C.r + 1 ≤ (pathSupport Pb ∩ pathSupport Pr).card := by
  have hle := C.compl_path_inter_path_card_le hPb hPr
  omega

/-- Every `G`-path meets the distinguished complementary-colour path `Q` in at most `r`
vertices. -/
lemma path_inter_Q_card_le {P : List V} (hP : IsPath C.G P) :
    (pathSupport P ∩ pathSupport C.Q).card ≤ C.r :=
  C.oppositeColour_path_intersection_card_le hP C.q_isPath

/-- No `G`-path contains `r + 1` vertices from the support of the distinguished path `Q`. -/
lemma not_r_add_one_le_path_inter_Q {P : List V} (hP : IsPath C.G P) :
    ¬ C.r + 1 ≤ (pathSupport P ∩ pathSupport C.Q).card :=
  C.not_r_add_one_le_path_inter_compl_path hP C.q_isPath

end Configuration
end Erdos518

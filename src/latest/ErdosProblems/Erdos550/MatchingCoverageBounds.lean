import Mathlib
import ErdosProblems.Erdos550.MaximalMatchingPackage
import ErdosProblems.Erdos550.OffTuranParams

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Coverage bounds for the off-Turán maximal matching

The matching outside `X,Y` covers every cluster except the two heads and the
small independent unmatched set.  These elementary cardinality consequences are
the exact input to the paper's head-degree estimate.
-/

open Finset

namespace Erdos550

/-- If `U` is exactly the set of non-head vertices outside the two endpoint
images, then the number of vertices outside those images is at most `|U|+2`. -/
lemma card_compl_matching_endpoints_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (X Y : ι) (cL cR : κ → ι) (U : Finset ι)
    (hU : ∀ a, a ∈ U ↔ a ≠ X ∧ a ≠ Y ∧
      a ∉ Finset.univ.image cL ∧ a ∉ Finset.univ.image cR) :
    (Finset.univ \ (Finset.univ.image cL ∪ Finset.univ.image cR)).card
      ≤ U.card + 2 := by
  let A := Finset.univ \ (Finset.univ.image cL ∪ Finset.univ.image cR)
  have hsub : A ⊆ U ∪ {X, Y} := by
    intro a ha
    have ha' := Finset.mem_sdiff.mp ha
    have haL : a ∉ Finset.univ.image cL := fun h => ha'.2 (Finset.mem_union_left _ h)
    have haR : a ∉ Finset.univ.image cR := fun h => ha'.2 (Finset.mem_union_right _ h)
    by_cases haX : a = X
    · subst haX
      simp
    by_cases haY : a = Y
    · subst haY
      simp
    have haU : a ∈ U := (hU a).mpr ⟨haX, haY, haL, haR⟩
    simp [haU]
  calc
    A.card ≤ (U ∪ {X, Y}).card := Finset.card_le_card hsub
    _ ≤ U.card + ({X, Y} : Finset ι).card := Finset.card_union_le U {X, Y}
    _ ≤ U.card + 2 := Nat.add_le_add_left (Finset.card_insert_le X {Y}) U.card

/-- The paper's `ηℓ+2` conclusion in integral form. -/
lemma card_compl_matching_endpoints_lt_add_two
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (X Y : ι) (cL cR : κ → ι) (U : Finset ι) (B : ℕ)
    (hU : ∀ a, a ∈ U ↔ a ≠ X ∧ a ≠ Y ∧
      a ∉ Finset.univ.image cL ∧ a ∉ Finset.univ.image cR)
    (hsmall : U.card < B) :
    (Finset.univ \ (Finset.univ.image cL ∪ Finset.univ.image cR)).card
      < B + 2 := by
  exact lt_of_le_of_lt (card_compl_matching_endpoints_le X Y cL cR U hU) (by omega)

/-- Combining maximal-matching coverage with the existing scalar estimate gives
the loss bound used to pass from a heavy head degree to degree into the matched
cluster union. -/
lemma matched_outside_mass_le
    (η ell s N m0 outside : ℝ)
    (hell : ell * s ≤ N) (hm0 : m0 * s ≤ N)
    (hηm0 : 2 ≤ η * m0) (hη : 0 ≤ η) (hs : 0 ≤ s)
    (hout : outside ≤ (η * ell + 2) * s) :
    outside ≤ 2 * η * N := by
  exact hout.trans (matched_cluster_excess η ell s N m0 hell hm0 hηm0 hη hs)

end Erdos550

import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: BigonRerouteCrossingCountBound]
lemma BigonRerouteCrossingCountBound
    (oldCross newCross deletedCross createdCross chargeCross :
      Finset (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ oldCross →
      x ∉ deletedCross →
        deletedCross ⊆ oldCross →
          createdCross.card ≤ chargeCross.card →
            newCross ⊆ (oldCross.erase x \ deletedCross) ∪ createdCross →
              newCross.card + deletedCross.card + 1 ≤
                oldCross.card + chargeCross.card := by
-- BODY
  intro hxold hxdel hdel_sub hcreated hnew_sub
  have hnew_card :
      newCross.card ≤ ((oldCross.erase x \ deletedCross) ∪ createdCross).card :=
    Finset.card_le_card hnew_sub
  have hunion_card :
      ((oldCross.erase x \ deletedCross) ∪ createdCross).card ≤
        (oldCross.erase x \ deletedCross).card + createdCross.card := by
    exact Finset.card_union_le (oldCross.erase x \ deletedCross) createdCross
  have hnew_bound :
      newCross.card ≤ (oldCross.erase x \ deletedCross).card + createdCross.card :=
    le_trans hnew_card hunion_card
  have hdel_sub_erase : deletedCross ⊆ oldCross.erase x := by
    intro a ha
    simp only [Finset.mem_erase]
    exact ⟨by intro hax; subst hax; exact hxdel ha, hdel_sub ha⟩
  have hcard_sdiff :
      (oldCross.erase x \ deletedCross).card + deletedCross.card =
        (oldCross.erase x).card :=
    Finset.card_sdiff_add_card_eq_card hdel_sub_erase
  have herase : (oldCross.erase x).card + 1 = oldCross.card :=
    Finset.card_erase_add_one hxold
  omega

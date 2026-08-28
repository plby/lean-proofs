import ErdosProblems.Erdos577.FullLeafHeavyAdjacentExcluded

/-! Exact row consequences when a five-set sends at least sixteen contacts to a block. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma degree_le_two_add_first_of_no_low_pair (q : Quadrilateral G) (u : V)
    (hno : ¬(G.Adj u (q 1) ∧ G.Adj u (q 3))) :
    degreeIn G u q.support ≤ 2 + (if G.Adj u (q 0) then 1 else 0) := by
  have hlow := (JointFinal.degree_pair_le_one_iff u (q 1) (q 3)
    (q.injective.ne (by decide))).mpr hno
  rw [JointFinal.opposite_degree_split q u, JointFinal.degree_pair_eq u (q 0) (q 2)
    (q.injective.ne (by decide))]
  split_ifs <;> omega

lemma full_of_other_rows_three (q : Quadrilateral G) (t : Finset V) (ht : t.card = 5)
    (hsixteen : 16 ≤ contacts G t q.support) {v : V} (hv : v ∈ t)
    (hrows : ∀ u ∈ t, u ≠ v → degreeIn G u q.support ≤ 3) :
    degreeIn G v q.support = 4 := by
  have he := sum_erase_add (s := t) (fun u ↦ degreeIn G u q.support) hv
  have hrest : (∑ u ∈ t.erase v, degreeIn G u q.support) ≤ 12 := by
    calc
      (∑ u ∈ t.erase v, degreeIn G u q.support) ≤ ∑ _ ∈ t.erase v, (3 : ℕ) :=
        sum_le_sum fun u hu ↦ hrows u (mem_erase.mp hu).2 (mem_erase.mp hu).1
      _ = 12 := by rw [sum_const, smul_eq_mul, card_erase_of_mem hv, ht]
  have hb := degreeIn_le_card G v q.support
  rw [q.card_support] at hb
  change 16 ≤ ∑ u ∈ t, degreeIn G u q.support at hsixteen
  omega

lemma row_ge_three_of_other_rows_three (q : Quadrilateral G) (t : Finset V) (ht : t.card = 5)
    (hsixteen : 16 ≤ contacts G t q.support) {v : V} (hv : v ∈ t)
    (hrows : ∀ u ∈ t, u ≠ v → degreeIn G u q.support ≤ 3)
    {u : V} (hu : u ∈ t) (huv : u ≠ v) : 3 ≤ degreeIn G u q.support := by
  have hu' : u ∈ t.erase v := mem_erase.mpr ⟨huv, hu⟩
  have he := sum_erase_add (s := t) (fun w ↦ degreeIn G w q.support) hv
  have he' := sum_erase_add (s := t.erase v) (fun w ↦ degreeIn G w q.support) hu'
  have hrest : (∑ w ∈ (t.erase v).erase u, degreeIn G w q.support) ≤ 9 := by
    calc
      (∑ w ∈ (t.erase v).erase u, degreeIn G w q.support) ≤
          ∑ _ ∈ (t.erase v).erase u, (3 : ℕ) :=
        sum_le_sum fun w hw ↦ hrows w (mem_erase.mp (mem_erase.mp hw).2).2
          (mem_erase.mp (mem_erase.mp hw).2).1
      _ = 9 := by
        rw [sum_const, smul_eq_mul, card_erase_of_mem hu', card_erase_of_mem hv, ht]
  have hb := degreeIn_le_card G v q.support
  rw [q.card_support] at hb
  change 16 ≤ ∑ w ∈ t, degreeIn G w q.support at hsixteen
  omega

end Erdos577.FullLeafHeavy

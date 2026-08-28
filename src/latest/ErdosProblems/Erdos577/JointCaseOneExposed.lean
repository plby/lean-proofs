import ErdosProblems.Erdos577.JointCaseOneLabels

/-! Exposing the last first-block vertex swaps the center and second triangle row. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem case_one_exposed_degrees (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hcl : G.IsNClique 4 q.support) (hc : CaseOne p q) :
    degreeIn G (q 3) (insert p.leaf (q.support.erase (q 3))) = 4 ∧
    0 < degreeIn G (p.vertices 2) (insert p.leaf (q.support.erase (q 3))) ∧
    2 ≤ degreeIn G p.center (insert p.leaf (q.support.erase (q 3))) := by
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hxQ : p.leaf ∉ q.support := fun hh ↦ disjoint_left.mp hd hxF hh
  have hm (i : Fin 4) : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have hnew : (insert p.leaf (q.support.erase (q 3))).card = 4 := by
    rw [card_insert_of_notMem (fun hh ↦ hxQ (mem_erase.mp hh).2),
      card_erase_of_mem (hm 3), q.card_support]
  have hrow := (degreeIn_eq_card_iff p.leaf q.support).mp (hc.1.trans q.card_support.symm)
  have hfull : degreeIn G (q 3) (insert p.leaf (q.support.erase (q 3))) = 4 := by
    refine Eq.trans ?_ hnew
    apply (degreeIn_eq_card_iff _ _).mpr
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact (hrow (q 3) (hm 3)).symm
    · exact hcl.isClique (hm 3) (mem_erase.mp hu).2 (mem_erase.mp hu).1.symm
  have hpos : 0 < degreeIn G (p.vertices 2) (insert p.leaf (q.support.erase (q 3))) :=
    card_pos.mpr ⟨q 2, mem_filter.mpr
      ⟨mem_insert_of_mem (mem_erase.mpr ⟨q.injective.ne (by decide : (2 : Fin 4) ≠ 3), hm 2⟩),
        hc.2.2.1⟩⟩
  have hpair : ({p.leaf, q 1} : Finset V) ⊆
      (insert p.leaf (q.support.erase (q 3))).filter (G.Adj p.center) :=
    insert_subset (mem_filter.mpr ⟨mem_insert_self _ _, p.pendant.symm⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr
        ⟨mem_insert_of_mem (mem_erase.mpr ⟨q.injective.ne (by decide : (1 : Fin 4) ≠ 3), hm 1⟩),
          hc.2.1⟩))
  have hxv : p.leaf ≠ q 1 := fun he ↦ hxQ (he.symm ▸ hm 1)
  have htwo := card_le_card hpair
  rw [card_pair_eq_two_iff.mpr hxv] at htwo
  exact ⟨hfull, hpos, htwo⟩

end Erdos577.JointClaims

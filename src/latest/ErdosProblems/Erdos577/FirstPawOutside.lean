import ErdosProblems.Erdos577.FirstPawOutsideWitnesses
import ErdosProblems.Erdos577.OutsideLabeling
import ErdosProblems.Erdos577.FirstPawPatterns

/-! The outside-vertex two-cycle factors in source patterns (3) and (8). -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Quadrilateral.exists_two_neighbor_indices (q : Quadrilateral G) (z : V)
    (h : 2 ≤ degreeIn G z q.support) :
    ∃ i j : Fin 4, i ≠ j ∧ G.Adj z (q i) ∧ G.Adj z (q j) := by
  have htwo : 1 < (q.support.filter (G.Adj z)).card := by change 1 < degreeIn G z q.support; omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp htwo
  obtain ⟨haq, hza⟩ := mem_filter.mp ha
  obtain ⟨hbq, hzb⟩ := mem_filter.mp hb
  obtain ⟨i, rfl⟩ := (q.mem_support a).mp haq
  obtain ⟨j, rfl⟩ := (q.mem_support b).mp hbq
  exact ⟨i, j, fun he ↦ hab (congrArg q he), hza, hzb⟩

namespace FirstPawOutside

def modelCopy (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) (patternEight : Bool) (i j : Fin 4) (hne : i ≠ j)
    (hdiag : G.Adj (q 0) (q 2))
    (hrows : ∀ r : Fin 4, r ≠ 0 → ∀ s : Fin 4,
      G.Adj (p.vertices r) (q s) ↔ (rows patternEight r).testBit s.val = true)
    (hzi : G.Adj z (q i)) (hzj : G.Adj z (q j)) : (graph patternEight i j).Copy G where
  toHom := {
    toFun := OutsideLabeling.labeling p q hd z hz
    map_rel' := by
      have h0 := OutsideLabeling.labeling_zero p q hd z hz
      have h1 := OutsideLabeling.labeling_nonzero p q hd z hz (i := 1) (by decide)
      have h2 := OutsideLabeling.labeling_nonzero p q hd z hz (i := 2) (by decide)
      have h3 := OutsideLabeling.labeling_nonzero p q hd z hz (i := 3) (by decide)
      have h4 := OutsideLabeling.labeling_right p q hd z hz 0
      have h5 := OutsideLabeling.labeling_right p q hd z hz 1
      have h6 := OutsideLabeling.labeling_right p q hd z hz 2
      have h7 := OutsideLabeling.labeling_right p q hd z hz 3
      change OutsideLabeling.labeling p q hd z hz 1 = p.vertices 1 at h1
      change OutsideLabeling.labeling p q hd z hz 2 = p.vertices 2 at h2
      change OutsideLabeling.labeling p q hd z hz 3 = p.vertices 3 at h3
      change OutsideLabeling.labeling p q hd z hz 4 = q 0 at h4
      change OutsideLabeling.labeling p q hd z hz 5 = q 1 at h5
      change OutsideLabeling.labeling p q hd z hz 6 = q 2 at h6
      change OutsideLabeling.labeling p q hd z hz 7 = q 3 at h7
      have hbase : Unattached.basePairs 1 =
          {(1, 2), (1, 3), (2, 3), (4, 5), (5, 6), (6, 7), (4, 7), (4, 6)} := by
        decide +kernel
      have hr {a b : Fin 8} (h : Unattached.relation 1 (mask patternEight i j) a b) :
          G.Adj (OutsideLabeling.labeling p q hd z hz a)
            (OutsideLabeling.labeling p q hd z hz b) := by
        rcases h with h | ⟨ha, hb, hbit⟩
        · rw [hbase] at h
          simp only [mem_insert, mem_singleton] at h
          rcases h with h | h | h | h | h | h | h | h <;>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          · rw [h1, h2]
            exact p.edge12
          · rw [h1, h3]
            exact p.edge13
          · rw [h2, h3]
            exact p.edge23
          · rw [h4, h5]
            exact q.adjacent 0
          · rw [h5, h6]
            exact q.adjacent 1
          · rw [h6, h7]
            exact q.adjacent 2
          · rw [h4, h7]
            exact (q.adjacent 3).symm
          · rw [h4, h6]
            exact hdiag
        · let r : Fin 4 := ⟨a.val, ha⟩
          let s : Fin 4 := ⟨b.val - 4, by omega⟩
          have hea : Fin.castAdd 4 r = a := Fin.ext rfl
          have heb : Fin.natAdd 4 s = b := Fin.ext (by dsimp [s]; omega)
          have hindex : 4 * a.val + b.val - 4 = 4 * r.val + s.val := by dsimp [r, s]; omega
          rw [hindex] at hbit
          have hrow := (cross_bit patternEight i j r s hne).mp hbit
          rw [← hea, ← heb, OutsideLabeling.labeling_right]
          by_cases hr0 : r = 0
          · rw [hr0]
            change G.Adj (OutsideLabeling.labeling p q hd z hz 0) (q s)
            rw [h0]
            rw [if_pos hr0] at hrow
            rcases hrow with hsi | hsj
            · rw [hsi]
              exact hzi
            · rw [hsj]
              exact hzj
          · rw [OutsideLabeling.labeling_nonzero p q hd z hz hr0]
            rw [if_neg hr0] at hrow
            exact (hrows r hr0 s).mpr hrow
      intro a b hab
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, hab | hba⟩
      · exact hr hab
      · exact (hr hba).symm }
  injective' := (OutsideLabeling.labeling p q hd z hz).injective

theorem factor (patternEight : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (z : V) (hz : z ∉ p.support ∪ q.support)
    (hdiag : G.Adj (q 0) (q 2))
    (hrows : ∀ r : Fin 4, r ≠ 0 → ∀ s : Fin 4,
      G.Adj (p.vertices r) (q s) ↔ (rows patternEight r).testBit s.val = true)
    (hdegree : 2 ≤ degreeIn G z q.support) :
    LocalFactor G (insert z (p.triangle ∪ q.support)) := by
  obtain ⟨i, j, hne, hzi, hzj⟩ := q.exists_two_neighbor_indices z hdegree
  have hf := (finite_factor patternEight i j hne).image
    (modelCopy p q hd z hz patternEight i j hne hdiag hrows hzi hzj)
  change LocalFactor G (univ.image (OutsideLabeling.labeling p q hd z hz)) at hf
  rw [OutsideLabeling.labeling_image] at hf
  exact hf

end FirstPawOutside

lemma PawBlock.Pattern3.outside_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern3 p q)
    (z : V) (hz : z ∉ p.support ∪ q.support) (hdegree : 2 ≤ degreeIn G z q.support) :
    LocalFactor G (insert z (p.triangle ∪ q.support)) := by
  apply FirstPawOutside.factor false p q hd z hz h.1.1 ?_ hdegree
  intro r hr s
  fin_cases r
  · exact False.elim (hr rfl)
  · exact h.2 1 s
  · exact h.2 2 s
  · exact h.2 3 s

lemma PawBlock.Pattern8.outside_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    (z : V) (hz : z ∉ p.support ∪ q.support) (hdegree : 2 ≤ degreeIn G z q.support) :
    LocalFactor G (insert z (p.triangle ∪ q.support)) := by
  apply FirstPawOutside.factor true p q hd z hz h.1 ?_ hdegree
  intro r hr s
  fin_cases r
  · exact False.elim (hr rfl)
  · exact h.2 1 s
  · exact h.2 2 s
  · exact h.2 3 s

end Erdos577

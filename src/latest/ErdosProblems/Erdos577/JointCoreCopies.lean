import ErdosProblems.Erdos577.JointCorePatternTransport
import ErdosProblems.Erdos577.JointCoreLabels
import ErdosProblems.Erdos577.JointCoreFactors

/-! Copies of the positive core models and all outside-neighbor factors. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def modelCopy (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.triangle q.support) (u : V) (hu : u ∉ p.triangle ∪ q.support)
    (h : SourcePattern tag p q) : (graph tag).Copy G where
  toHom := {
    toFun := labeling p q hd u hu
    map_rel' := by
      have h1 := labeling_nonzero p q hd u hu 1 (by decide)
      have h2 := labeling_nonzero p q hd u hu 2 (by decide)
      have h3 := labeling_nonzero p q hd u hu 3 (by decide)
      have h4 := labeling_right p q hd u hu 0
      have h5 := labeling_right p q hd u hu 1
      have h6 := labeling_right p q hd u hu 2
      have h7 := labeling_right p q hd u hu 3
      change labeling p q hd u hu 1 = p.vertices 1 at h1
      change labeling p q hd u hu 2 = p.vertices 2 at h2
      change labeling p q hd u hu 3 = p.vertices 3 at h3
      change labeling p q hd u hu 4 = q 0 at h4
      change labeling p q hd u hu 5 = q 1 at h5
      change labeling p q hd u hu 6 = q 2 at h6
      change labeling p q hd u hu 7 = q 3 at h7
      have hr {a b : Fin 8} (hab : Unattached.relation (diagonal tag) (mask tag) a b) :
          G.Adj (labeling p q hd u hu a) (labeling p q hd u hu b) := by
        rcases hab with hab | ⟨ha, hb, hbit⟩
        · rw [Unattached.basePairs] at hab
          rcases mem_union.mp hab with hab | hb1
          · rcases mem_union.mp hab with hab | hb0
            · simp only [mem_insert, mem_singleton] at hab
              rcases hab with hab | hab | hab | hab | hab | hab | hab <;>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
              · rw [h1, h2]; exact p.edge12
              · rw [h1, h3]; exact p.edge13
              · rw [h2, h3]; exact p.edge23
              · rw [h4, h5]; exact q.adjacent 0
              · rw [h5, h6]; exact q.adjacent 1
              · rw [h6, h7]; exact q.adjacent 2
              · rw [h4, h7]; exact (q.adjacent 3).symm
            · split_ifs at hb0 with he
              · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton.mp hb0)
                rw [h4, h6]
                exact h.1.mpr he
              · simp at hb0
          · split_ifs at hb1 with he
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (mem_singleton.mp hb1)
              rw [h5, h7]
              exact h.2.1.mpr he
            · simp at hb1
        · let i : Fin 4 := ⟨a.val, ha⟩
          let j : Fin 4 := ⟨b.val - 4, by omega⟩
          have hea : Fin.castAdd 4 i = a := Fin.ext rfl
          have heb : Fin.natAdd 4 j = b := Fin.ext (by dsimp [j]; omega)
          have hi : 4 * a.val + b.val - 4 = 4 * i.val + j.val := by dsimp [i, j]; omega
          rw [hi, mask_bit] at hbit
          have hn : i ≠ 0 := by
            intro he
            rw [he] at hbit
            simp [lowerRows] at hbit
          rw [← hea, ← heb, labeling_nonzero p q hd u hu i hn, labeling_right]
          exact (h.2.2 i j hn).1 hbit
      intro a b hab
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨_, hab | hba⟩
      · exact hr hab
      · exact (hr hba).symm }
  injective' := (labeling p q hd u hu).injective

def outsideCopy (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.triangle q.support) (u : V) (hu : u ∉ p.triangle ∪ q.support)
    (h : SourcePattern tag p q) (i j : Fin 7)
    (hi : G.Adj u (labeling p q hd u hu i.succ))
    (hj : G.Adj u (labeling p q hd u hu j.succ)) : (outsideGraph tag i j).Copy G where
  toHom := {
    toFun := labeling p q hd u hu
    map_rel' := by
      have he {a b v : Fin 8} (hv : G.Adj u (labeling p q hd u hu v))
          (hab : (SimpleGraph.edge 0 v).Adj a b) :
          G.Adj (labeling p q hd u hu a) (labeling p q hd u hu b) := by
        rcases ((SimpleGraph.edge_adj _ _ _ _).mp hab).1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [labeling_zero]; exact hv
        · rw [labeling_zero]; exact hv.symm
      intro a b hab
      rcases (SimpleGraph.sup_adj _ _ _ _).mp hab with hab | hab
      · rcases (SimpleGraph.sup_adj _ _ _ _).mp hab with hab | hab
        · exact (modelCopy tag p q hd u hu h).toHom.map_rel' hab
        · exact he hi hab
      · exact he hj hab }
  injective' := (labeling p q hd u hu).injective

theorem SourcePattern.outside_factor (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.triangle q.support) (h : SourcePattern tag p q)
    (u : V) (hu : u ∉ p.triangle ∪ q.support)
    (hdegree : 2 ≤ degreeIn G u (p.triangle ∪ q.support)) :
    LocalFactor G (insert u (p.triangle ∪ q.support)) := by
  have ht : 1 < ((p.triangle ∪ q.support).filter (G.Adj u)).card := by
    change 1 < degreeIn G u (p.triangle ∪ q.support)
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp ht
  obtain ⟨haK, hua⟩ := mem_filter.mp ha
  obtain ⟨hbK, hub⟩ := mem_filter.mp hb
  obtain ⟨i, hi⟩ := exists_core_index p q hd u hu haK
  obtain ⟨j, hj⟩ := exists_core_index p q hd u hu hbK
  have hij : i ≠ j := by
    intro he
    apply hab
    rw [← hi, ← hj, he]
  have hf := (Erdos577.JointCore.outside_factor tag i j hij).image
    (outsideCopy tag p q hd u hu h i j (by rwa [hi]) (by rwa [hj]))
  change LocalFactor G (univ.image (labeling p q hd u hu)) at hf
  rwa [labeling_image] at hf

end Erdos577.JointCore

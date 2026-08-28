import ErdosProblems.Erdos577.JointClaimFourMissing

/-! Only source configurations27/28 remain.
Their reversal does not require the optional normalization. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma early_source_reverse (tag : Fin 8) (p : Paw G) (d : Quadrilateral G)
    (htag : tag = 0 ∨ tag = 1) (h : JointCore.SourcePattern tag p d) :
    JointCore.RefinedSourcePattern tag p d.reverse := by
  have hbits : ∀ tag : Fin 8, tag = 0 ∨ tag = 1 → ∀ i j : Fin 4,
      (JointCore.lowerRows tag i).testBit (-j).val = (JointCore.lowerRows tag i).testBit j.val ∧
      (JointCore.upperRows tag i).testBit (-j).val = (JointCore.upperRows tag i).testBit j.val := by
    decide +kernel
  have hsrc : JointCore.SourcePattern tag p d.reverse := by
    refine ⟨h.1, ?_, ?_⟩
    · change G.Adj (d 3) (d 1) ↔ (JointCore.diagonal tag).val.testBit 1 = true
      exact (G.adj_comm (d 3) (d 1)).trans h.2.1
    · intro i j hi
      change ((JointCore.lowerRows tag i).testBit j.val = true →
        G.Adj (p.vertices i) (d (-j))) ∧
        (G.Adj (p.vertices i) (d (-j)) → (JointCore.upperRows tag i).testBit j.val = true)
      rw [← (hbits tag htag i j).1, ← (hbits tag htag i j).2]
      exact h.2.2 i (-j) hi
  refine ⟨hsrc, ?_, ?_, ?_, ?_⟩
  all_goals rcases htag with rfl | rfl <;> simp

omit [DecidableRel G.Adj] in
lemma early_source_triangle_clique (tag : Fin 8) (p : Paw G) (d : Quadrilateral G)
    (htag : tag = 0 ∨ tag = 1) (h : JointCore.SourcePattern tag p d) :
    G.IsNClique 4 (insert (d 0) p.triangle) := by
  have hbits : ∀ i : Fin 4, i ≠ 0 → (JointCore.lowerRows tag i).testBit 0 = true := by
    rcases htag with rfl | rfl <;> decide +kernel
  apply p.triangle_clique.insert
  intro u hu
  simp only [Paw.triangle, mem_insert, mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact ((h.2.2 1 0 (by decide)).1 (hbits 1 (by decide))).symm
  · exact ((h.2.2 2 0 (by decide)).1 (hbits 2 (by decide))).symm
  · exact ((h.2.2 3 0 (by decide)).1 (hbits 3 (by decide))).symm

variable [Fintype V]

theorem Core.missing_pair_source {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G}
    {a : Finset V} (h : Core c p q d a)
    (hmiss : ¬G.Adj (p.vertices 2) (d 2) ∧ ¬G.Adj (p.vertices 2) (d 3)) :
    contacts G p.triangle a ≤ 10 ∧
      ∃ tag : Fin 8, (tag = 0 ∨ tag = 1) ∧ JointCore.RefinedSourcePattern tag p d := by
  have hbsub : d.support.filter (G.Adj (p.vertices 2)) ⊆ {d 0, d 1} := by
    intro u hu
    obtain ⟨hm, hadj⟩ := mem_filter.mp hu
    obtain ⟨i, rfl⟩ := (d.mem_support u).mp hm
    fin_cases i
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_singleton_self _)
    · exact False.elim (hmiss.1 hadj)
    · exact False.elim (hmiss.2 hadj)
  have hb := card_le_card hbsub
  have htwo : ({d 0, d 1} : Finset V).card = 2 :=
    card_pair_eq_two_iff.mpr (d.injective.ne (by decide : (0 : Fin 4) ≠ 1))
  rw [htwo] at hb
  change degreeIn G (p.vertices 2) d.support ≤ 2 at hb
  rw [h.labels] at hb
  have hr := degreeIn_le_card G p.center a
  have hc := degreeIn_le_card G (p.vertices 3) a
  have ha := (c.property.blocks_quad a h.config.2.2.1).card
  rw [ha] at hr hc
  have hsum := p.contacts_triangle a
  change contacts G p.triangle a =
    degreeIn G p.center a + (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at hsum
  have hlow : contacts G p.triangle a ≤ 10 := by omega
  obtain ⟨tag, hpat⟩ := h.low hlow
  refine ⟨hlow, tag, ?_, hpat⟩
  fin_cases tag
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim (hpat.2.1 rfl)
  · exact False.elim (hpat.2.2.1 rfl)
  · exact False.elim (hmiss.2 ((hpat.1.2.2 2 3 (by decide)).1 (by decide)))
  · exact False.elim (hmiss.2 ((hpat.1.2.2 2 3 (by decide)).1 (by decide)))
  · exact False.elim (hmiss.1 ((hpat.1.2.2 2 2 (by decide)).1 (by decide)))
  · exact False.elim (hmiss.2 ((hpat.1.2.2 2 3 (by decide)).1 (by decide)))

end Erdos577.JointFinal

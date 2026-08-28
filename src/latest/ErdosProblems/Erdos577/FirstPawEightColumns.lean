import ErdosProblems.Erdos577.FirstPawEightLabels

/-! The two low columns meet at most one of the three remaining distinguished rows. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma Quadrilateral.low_replace_of_highs (d : Quadrilateral G) (z : V) (hz : z ∉ d.support)
    (h0 : G.Adj z (d 0)) (h2 : G.Adj z (d 2))
    (i : Fin 4) (hi : i = 1 ∨ i = 3) : QuadOn G (insert z (d.support.erase (d i))) := by
  apply d.quad_replaceAt i z hz
  intro j hij
  have he : ∀ i j : Fin 4, (i = 1 ∨ i = 3) →
      (SimpleGraph.cycleGraph 4).Adj i j → j = 0 ∨ j = 2 := by decide +kernel
  rcases he i j hi hij with rfl | rfl
  · exact h0
  · exact h2

namespace FirstPawEight

def otherRows (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    Finset V := (weightSet.erase 5).image (PawEncoding.labeling p q hd)

variable [DecidableRel G.Adj]

lemma other_contacts_add (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (a : Finset V) :
    contacts G (otherRows p q hd) a + degreeIn G (q 1) a = contacts G (rows p q hd) a :=
  contacts_image_erase_add (PawEncoding.labeling p q hd) weightSet 5 (by decide +kernel) a

lemma other_column (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (z : V) :
    degreeIn G z (otherRows p q hd) = (if G.Adj p.leaf z then 1 else 0) +
      (if G.Adj (p.vertices 3) z then 1 else 0) + (if G.Adj (q 3) z then 1 else 0) := by
  rw [otherRows, degreeIn_image G z _ _ (PawEncoding.labeling p q hd).injective]
  have hs : weightSet.erase 5 = {0, 3, 7} := by decide +kernel
  simp only [hs, sum_insert, mem_insert, mem_singleton, Fin.reduceEq,
    not_false_eq_true, or_self, sum_singleton]
  change (if G.Adj z p.leaf then 1 else 0) +
    ((if G.Adj z (p.vertices 3) then 1 else 0) + (if G.Adj z (q 3) then 1 else 0)) = _
  simp only [G.adj_comm z, Nat.add_assoc]

lemma other_columns_sum (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (d : Quadrilateral G) :
    contacts G (otherRows p q hd) d.support =
      degreeIn G (d 0) (otherRows p q hd) + degreeIn G (d 1) (otherRows p q hd) +
      degreeIn G (d 2) (otherRows p q hd) + degreeIn G (d 3) (otherRows p q hd) := by
  rw [contacts_comm, Quadrilateral.support, contacts_image_left G _ d d.injective]
  simp only [Fin.sum_univ_four]

variable [Fintype V]

theorem low_column_bound {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (d : Quadrilateral G) (hdA : d.support = a)
    (h0 : G.Adj (q 1) (d 0)) (h2 : G.Adj (q 1) (d 2))
    (i : Fin 4) (hi : i = 1 ∨ i = 3) : degreeIn G (d i) (otherRows p q hd) ≤ 1 := by
  have hout : q 1 ∉ d.support := by
    rw [hdA]
    exact fun hh ↦ disjoint_left.mp (c.property.blocks_disjoint hb ha hab.symm)
      (hq ▸ (q.mem_support _).mpr ⟨1, rfl⟩) hh
  have hr := d.low_replace_of_highs (q 1) hout h0 h2 i hi
  rw [hdA] at hr
  by_contra! hh
  obtain ⟨v, hv, w, hw, hvw⟩ := one_lt_card.mp hh
  obtain ⟨hvR, hvi⟩ := mem_filter.mp hv
  obtain ⟨hwR, hwi⟩ := mem_filter.mp hw
  obtain ⟨vi, hviIndex, rfl⟩ := mem_image.mp hvR
  obtain ⟨wi, hwiIndex, rfl⟩ := mem_image.mp hwR
  exact no_common_pair hcard hn p hp hb q hq hd h ha hab 5 vi wi (by decide +kernel)
    hviIndex hwiIndex (fun he ↦ hvw (congrArg (PawEncoding.labeling p q hd) he))
    ⟨d i, hdA ▸ (d.mem_support _).mpr ⟨i, rfl⟩, hvi.symm, hwi.symm, hr⟩

theorem other_contacts_ge_six {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hheavy : 9 ≤ contacts G (rows p q hd) a) : 6 ≤ contacts G (otherRows p q hd) a := by
  have hbnd : degreeIn G (q 1) a ≤ 3 :=
    row_bound hcard hn p hp hb q hq hd h ha hab hheavy 5 (by decide +kernel)
  have hid := other_contacts_add p q hd a
  omega

end FirstPawEight

end Erdos577

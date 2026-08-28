import ErdosProblems.Erdos577.JointEightRows

/-! Eight weighted slots have inside budget31 and force an outside weight of at least17. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def eightWeight (p : Paw G) (q : Quadrilateral G) (a : Finset V) : ℕ :=
  sixWeight p q a + degreeIn G p.center a + degreeIn G (q 3) a

lemma eightWeight_eq_rows (p : Paw G) (q : Quadrilateral G) (a : Finset V) :
    eightWeight p q a = degreeIn G p.leaf a + 2 * degreeIn G (q 3) a +
      2 * degreeIn G p.center a + degreeIn G (p.vertices 2) a +
      2 * degreeIn G (p.vertices 3) a := by
  rw [eightWeight, sixWeight_eq_rows]
  omega

variable [Fintype V]

theorem eight_inside_upper {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hcase : CaseTwo p q) : eightWeight p q (p.support ∪ q.support) ≤ 31 := by
  have hsix := inside_upper hc hcard hn p hp hs q hq (Or.inr hcase)
  have hr := case_two_center_inside hc hcard hdeg hn p hp hs q hq hcase
  have hlast := last_inside_le_five hc hcard hn p hp hs q hq (Or.inr hcase)
  rw [eightWeight]
  omega

theorem exists_eight_heavy_of_inside {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hinside : eightWeight p q (p.support ∪ q.support) ≤ 31) :
    ∃ a ∈ c.blocks, a ≠ s ∧ 17 ≤ eightWeight p q a := by
  have htotalF := minimum_degree_sum G p.support (2 * k) (fun u _ ↦ hdeg u)
  rw [p.card_support] at htotalF
  have htotalC := hdeg (p.vertices 3)
  have htotalQ := hdeg (q 3)
  have htotalR := hdeg p.center
  have hidF := c.contacts_core_add_outside hs p.support
  have hidC := c.contacts_core_add_outside hs {p.vertices 3}
  have hidQ := c.contacts_core_add_outside hs {q 3}
  have hidR := c.contacts_core_add_outside hs {p.center}
  simp only [contacts_singleton_left, degreeIn_univ] at hidC hidQ hidR
  have hcore : c.remainder ∪ s = p.support ∪ q.support := by rw [hp, hq]
  rw [hcore] at hidF hidC hidQ hidR
  have hblocks := c.card_vertices
  have herase := card_erase_of_mem hs
  have hpos : 0 < c.blocks.card := card_pos.mpr ⟨s, hs⟩
  by_contra! hn
  have hbound : (∑ a ∈ c.blocks.erase s, eightWeight p q a) ≤ (c.blocks.erase s).card * 16 := by
    calc
      _ ≤ ∑ _ ∈ c.blocks.erase s, 16 := sum_le_sum fun a ha ↦ by
        have hh := hn a (mem_erase.mp ha).2 (mem_erase.mp ha).1
        omega
      _ = _ := by simp
  simp only [eightWeight, sixWeight, sum_add_distrib] at hbound
  unfold eightWeight sixWeight at hinside
  omega

theorem exists_eight_heavy_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hcase : CaseTwo p q) : ∃ a ∈ c.blocks, a ≠ s ∧ 17 ≤ eightWeight p q a :=
  exists_eight_heavy_of_inside hcard hdeg p hp hs q hq
    (eight_inside_upper hc hcard hdeg hn p hp hs q hq hcase)

end Erdos577.JointClaims

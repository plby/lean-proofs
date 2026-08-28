import ErdosProblems.Erdos577.WeightedFourteenModel
import ErdosProblems.Erdos577.PawTerminalExchange
import ErdosProblems.Erdos577.LocalChainSupport
import ErdosProblems.Erdos577.WeightedRows

/-! The three feasible terminals retain the original triangle and every outside block. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def terminalIndex : Fin 3 → Fin 8 := ![0, 5, 7]

def terminal (p : Paw G) (q : Quadrilateral G) : Fin 3 → V := ![p.leaf, q 1, q 3]

lemma leaf_replace (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q) (i : Fin 4) (hi : i = 1 ∨ i = 3) :
    QuadOn G (insert p.leaf (q.support.erase (q i))) := by
  have hout : p.leaf ∉ q.support := fun hh ↦
    disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩) hh
  apply q.quad_replaceAt i p.leaf hout
  intro j hij
  apply (h.2.1 j).mpr
  have hf : ∀ i j : Fin 4, (i = 1 ∨ i = 3) →
      (SimpleGraph.cycleGraph 4).Adj i j → (5 : ℕ).testBit j.val = true := by decide +kernel
  exact hf i j hi hij

variable [DecidableRel G.Adj]

lemma leaf_replace_score (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern14 p q) (i : Fin 4) (hi : i = 1 ∨ i = 3) :
    edgeCount G (insert p.leaf (q.support.erase (q i))) = edgeCount G q.support := by
  have hout : p.leaf ∉ q.support := fun hh ↦
    disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩) hh
  have hlow : degreeIn G (q i) q.support = 2 := by
    rcases hi with rfl | rfl
    · rw [q.degreeIn_eq]
      change 2 + (if G.Adj (q 1) (q 3) then 1 else 0) = 2
      rw [if_neg h.1]
    · rw [q.degreeIn_eq]
      change 2 + (if G.Adj (q 3) (q 1) then 1 else 0) = 2
      rw [if_neg (fun he ↦ h.1 he.symm)]
  have hrow : degreeIn G p.leaf q.support = 2 := by
    change degreeIn G (p.vertices 0) q.support = 2
    rw [(h.2.1).degree p q 0 5]
    decide +kernel
  have hnon : ¬G.Adj p.leaf (q i) := by
    intro he
    have hh := (h.2.1 i).mp he
    rcases hi with rfl | rfl <;> contradiction
  have herase := degreeIn_erase_add G p.leaf (q i) ((q.mem_support _).mpr ⟨i, rfl⟩)
  rw [if_neg hnon] at herase
  have hid := edgeCount_replace G (q i) p.leaf ((q.mem_support _).mpr ⟨i, rfl⟩) hout
  omega

variable [Fintype V]

lemma exists_odd_terminal_chain {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = q i ∧ d.triangle = p.triangle ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  let d₀ := p.replaceLeafLocalChain q hd (q i) ((q.mem_support _).mpr ⟨i, rfl⟩)
    (leaf_replace p q hd h i hi)
  let l := d₀.withSupport (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  let d := c.replaceBlock b hb l
  have hdF : d.Feasible := hc.replaceBlock_feasible hb l (by
    change edgeCount G (insert p.leaf (q.support.erase (q i))) = edgeCount G b
    rw [leaf_replace_score p q hd h i hi, hq])
  exact ⟨d, hdF, rfl, rfl, fun a ha hab ↦ mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)⟩

theorem exists_terminal_chain {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) (tag : Fin 3) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = terminal p q tag ∧ d.triangle = p.triangle ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  fin_cases tag
  · exact ⟨c.presentPaw p hp, hc.presentPaw_feasible p hp, rfl, rfl, fun _ ha _ ↦ ha⟩
  · exact exists_odd_terminal_chain hc p hp hb q hq hd h 1 (Or.inl rfl)
  · exact exists_odd_terminal_chain hc p hp hb q hq hd h 3 (Or.inr rfl)

theorem terminal_universal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) (tag : Fin 3)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (h3 : 3 ≤ degreeIn G (terminal p q tag) a) (u : V) (hu : u ∈ a) :
    QuadOn G (insert (terminal p q tag) (a.erase u)) := by
  obtain ⟨d, hdF, hdx, _, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h tag
  rw [← hdx] at h3 ⊢
  exact hdF.terminal_universal_replace (hkeep a ha hab) h3 hu

theorem clique_of_full_terminal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) (tag : Fin 3)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (h4 : degreeIn G (terminal p q tag) a = 4) : G.IsNClique 4 a := by
  obtain ⟨d, hdF, hdx, _, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h tag
  rw [← hdx] at h4
  exact hdF.clique_of_terminal_degree_four (hkeep a ha hab) h4

theorem triangle_column_le_one {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) (tag : Fin 3)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (h3 : 3 ≤ degreeIn G (terminal p q tag) a) (u : V) (hu : u ∈ a) :
    degreeIn G u p.triangle ≤ 1 := by
  obtain ⟨d, hdF, hdx, hdt, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h tag
  have ha' := hkeep a ha hab
  have hrep := hdF.terminal_universal_replace ha' (by rw [hdx]; exact h3) hu
  have hl := (d.replaceBlock a ha' (d.swapTerminal ha' hu hrep)).terminal_degree_le_one hcard hn
  change degreeIn G u d.triangle ≤ 1 at hl
  rwa [hdt] at hl

theorem triangle_contacts_le_four {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) (tag : Fin 3)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (h3 : 3 ≤ degreeIn G (terminal p q tag) a) : contacts G p.triangle a ≤ 4 := by
  rw [contacts_comm]
  calc
    _ ≤ ∑ _ ∈ a, 1 := sum_le_sum fun u hu ↦
      triangle_column_le_one hc hcard hn p hp hb q hq hd h tag ha hab h3 u hu
    _ = 4 := by simp [(c.property.blocks_quad a ha).card]

end Erdos577.WeightedFourteen

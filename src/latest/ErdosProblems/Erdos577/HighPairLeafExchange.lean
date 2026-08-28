import ErdosProblems.Erdos577.PawTerminalExchange
import ErdosProblems.Erdos577.LocalChainSupport
import ErdosProblems.Erdos577.WeightedRows
import ErdosProblems.Erdos577.PathRowCounts

/-! A high-pair leaf replaces either low cycle vertex without changing the block score. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma Quadrilateral.high_pair_replace (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (hrow : ∀ j : Fin 4, G.Adj z (q j) ↔ (5 : ℕ).testBit j.val = true)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) : QuadOn G (insert z (q.support.erase (q i))) := by
  apply q.quad_replaceAt i z hz
  intro j hij
  have hbits : ∀ i j : Fin 4, (i = 1 ∨ i = 3) →
      (SimpleGraph.cycleGraph 4).Adj i j → (5 : ℕ).testBit j.val = true := by decide +kernel
  exact (hrow j).mpr (hbits i j hi hij)

variable [DecidableRel G.Adj]

lemma Quadrilateral.degree_eq_mask (q : Quadrilateral G) (z : V) (mask : ℕ)
    (hrow : ∀ j : Fin 4, G.Adj z (q j) ↔ mask.testBit j.val = true) :
    degreeIn G z q.support = ∑ j : Fin 4, (mask.testBit j.val).toNat :=
  le_antisymm (q.degree_le_mask z mask (fun j ↦ (hrow j).mp))
    (q.degree_ge_mask z mask (fun j ↦ (hrow j).mpr))

lemma Quadrilateral.high_pair_replace_score (q : Quadrilateral G) (z : V)
    (hz : z ∉ q.support) (hn : ¬G.Adj (q 1) (q 3))
    (hrow : ∀ j : Fin 4, G.Adj z (q j) ↔ (5 : ℕ).testBit j.val = true)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) :
    edgeCount G (insert z (q.support.erase (q i))) = edgeCount G q.support := by
  have hlow : degreeIn G (q i) q.support = 2 := by
    rcases hi with rfl | rfl
    · rw [q.degreeIn_eq]
      change 2 + (if G.Adj (q 1) (q 3) then 1 else 0) = 2
      rw [if_neg hn]
    · rw [q.degreeIn_eq]
      change 2 + (if G.Adj (q 3) (q 1) then 1 else 0) = 2
      rw [if_neg (fun he ↦ hn he.symm)]
  have htwo : degreeIn G z q.support = 2 := by
    rw [q.degree_eq_mask z 5 hrow]
    decide +kernel
  have hnon : ¬G.Adj z (q i) := by
    intro he
    have hb := (hrow i).mp he
    rcases hi with rfl | rfl <;> contradiction
  have herase := degreeIn_erase_add G z (q i) ((q.mem_support _).mpr ⟨i, rfl⟩)
  rw [if_neg hnon] at herase
  have hcount := edgeCount_replace G (q i) z ((q.mem_support _).mpr ⟨i, rfl⟩) hz
  omega

variable [Fintype V]

theorem TriangleChain.Feasible.exists_high_pair_leaf_terminal {c : TriangleChain G}
    (hc : c.Feasible) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hn : ¬G.Adj (q 1) (q 3))
    (hrow : ∀ j : Fin 4, G.Adj p.leaf (q j) ↔ (5 : ℕ).testBit j.val = true)
    (i : Fin 4) (hi : i = 1 ∨ i = 3) :
    ∃ d : TriangleChain G, d.Feasible ∧ d.terminal = q i ∧ d.triangle = p.triangle ∧
      ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  have hx : p.leaf ∉ q.support := fun hh ↦
    disjoint_left.mp hd (p.support_eq ▸ mem_insert_self _ _) hh
  let d₀ := p.replaceLeafLocalChain q hd (q i) ((q.mem_support _).mpr ⟨i, rfl⟩)
    (q.high_pair_replace p.leaf hx hrow i hi)
  let l := d₀.withSupport (show p.support ∪ q.support = c.remainder ∪ b by rw [hp, hq])
  let d := c.replaceBlock b hb l
  have hdF : d.Feasible := hc.replaceBlock_feasible hb l (by
    change edgeCount G (insert p.leaf (q.support.erase (q i))) = edgeCount G b
    rw [q.high_pair_replace_score p.leaf hx hn hrow i hi, hq])
  exact ⟨d, hdF, rfl, rfl, fun a ha hab ↦ mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)⟩

end Erdos577

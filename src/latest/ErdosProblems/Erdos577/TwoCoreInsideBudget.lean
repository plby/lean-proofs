import ErdosProblems.Erdos577.TwoCoreInsideRows

/-! The common inside estimate for the six-contact and five-contact core variants. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem inside_upper_of_budgets {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hd : Disjoint p.support q.support)
    (hdiag : PawBlock.OnlyFirst q)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ (9 : ℕ).testBit i.val = true)
    (h3 : G.Adj p.leaf (q 3)) (hBzero : degreeIn G p.leaf b = 0)
    {rowBudget coreBudget : ℕ} (hbudget : rowBudget + coreBudget ≤ 11)
    (hrows : contacts G {p.center, p.vertices 2} b ≤ rowBudget)
    (z₁ : V) (hz₁ : z₁ ∈ b)
    (hunique : ∀ u ∈ p.triangle ∪ b, G.Adj (q 1) u ↔ u = z₁)
    (hr0 : ¬G.Adj p.center (q 0)) (hr3 : ¬G.Adj p.center (q 3))
    (hb3 : ¬G.Adj (p.vertices 2) (q 3))
    (hcouple : degreeIn G (p.vertices 2) {q 0, q 2} +
      degreeIn G (q 3) (p.triangle ∪ b) ≤ coreBudget) :
    contacts G (exposedPath p q hd h3).support (p.support ∪ (b ∪ q.support)) ≤ 23 := by
  have hpB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hBQ : Disjoint b q.support := by
    rw [hq]
    exact c.property.blocks_disjoint hb hs hbs
  have hdis : Disjoint p.support (b ∪ q.support) := disjoint_union_right.mpr ⟨hpB, hd⟩
  have htri : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hmissing (u : V) (hu : u ∈ p.triangle) : ¬G.Adj u (q 1) := by
    intro hh
    have he := (hunique u (mem_union_left _ hu)).mp hh.symm
    exact disjoint_left.mp hpB (htri hu) (he.symm ▸ hz₁)
  have hr1 := hmissing p.center p.center_mem_triangle
  have hb1 := hmissing (p.vertices 2) (by simp [Paw.triangle])
  have hfirst := first_block_pair_bound p q hr0 hr1 hr3 hb1 hb3
  have hinternal := pair_internal_degree p (by rw [hp]; exact c.no_quad_remainder hcard hn)
  have hpair : contacts G {p.center, p.vertices 2} b =
      degreeIn G p.center b + degreeIn G (p.vertices 2) b :=
    sum_pair (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  rw [hpair] at hrows
  have hpairAll : degreeIn G p.center (p.support ∪ (b ∪ q.support)) +
      degreeIn G (p.vertices 2) (p.support ∪ (b ∪ q.support)) ≤
        6 + rowBudget + degreeIn G (p.vertices 2) {q 0, q 2} := by
    rw [degreeIn_union G p.center hdis, degreeIn_union G (p.vertices 2) hdis,
      degreeIn_union G p.center hBQ, degreeIn_union G (p.vertices 2) hBQ]
    omega
  have hleaf := leaf_inside_degree hcard hn p hp hb hs hbs q hq hBzero hrow
  have hlowQ : degreeIn G (q 3) q.support = 2 := by
    have hnot : ¬G.Adj (q 3) (q 1) := fun hh ↦ hdiag.2 hh.symm
    rw [q.degreeIn_eq]
    change 2 + (if G.Adj (q 3) (q 1) then 1 else 0) = 2
    rw [if_neg hnot, add_zero]
  have hxout : p.leaf ∉ (p.triangle ∪ b) ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · exact p.leaf_not_mem_triangle hh
      · exact (c.presentPaw p hp).terminal_not_mem_block hb hh
    · exact (c.presentPaw p hp).terminal_not_mem_block hs (hq ▸ hh)
  have hcover : p.support ∪ (b ∪ q.support) =
      insert p.leaf ((p.triangle ∪ b) ∪ q.support) := by
    rw [p.support_eq, insert_union, union_assoc]
  have hlowAll : degreeIn G (q 3) (p.support ∪ (b ∪ q.support)) =
      1 + (degreeIn G (q 3) (p.triangle ∪ b) + 2) := by
    rw [hcover, degreeIn_insert G (q 3) p.leaf hxout, if_pos h3.symm,
      degreeIn_union G (q 3) (disjoint_union_left.mpr ⟨hd.mono_left htri, hBQ⟩), hlowQ]
  have hsum := (exposedPath p q hd h3).contacts_support (p.support ∪ (b ∪ q.support))
  change contacts G (exposedPath p q hd h3).support (p.support ∪ (b ∪ q.support)) =
    degreeIn G (q 3) (p.support ∪ (b ∪ q.support)) +
      degreeIn G p.leaf (p.support ∪ (b ∪ q.support)) +
      degreeIn G p.center (p.support ∪ (b ∪ q.support)) +
      degreeIn G (p.vertices 2) (p.support ∪ (b ∪ q.support)) at hsum
  omega

end Erdos577.TwoCore

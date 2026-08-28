import ErdosProblems.Erdos577.JointCaseTwoLabels

/-! The full-leaf exchange retains the triangle and interchanges its first two labels. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def secondPaw (p : Paw G) (u : V) (hu : u ∉ p.support)
    (hbu : G.Adj (p.vertices 2) u) : Paw G :=
  Paw.ofVertices u (p.vertices 2) p.center (p.vertices 3)
    (fun he ↦ hu (he.symm ▸ (mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩))
    (fun he ↦ hu (he.symm ▸ (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩))
    (fun he ↦ hu (he.symm ▸ (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩))
    (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1))
    (p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 3))
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 3))
    hbu.symm p.edge12.symm p.edge23 p.edge13

lemma secondPaw_triangle (p : Paw G) (u : V) (hu : u ∉ p.support)
    (hbu : G.Adj (p.vertices 2) u) : (secondPaw p u hu hbu).triangle = p.triangle := by
  change ({p.vertices 2, p.center, p.vertices 3} : Finset V) = p.triangle
  exact insert_comm (p.vertices 2) p.center {p.vertices 3}

lemma secondPaw_support (p : Paw G) (u : V) (hu : u ∉ p.support)
    (hbu : G.Adj (p.vertices 2) u) :
    (secondPaw p u hu hbu).support = insert u p.triangle := by
  rw [Paw.support_eq, secondPaw_triangle]
  rfl

variable [Fintype V] [DecidableRel G.Adj]

theorem single_neighbor_new_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (hfull : degreeIn G p.leaf b = 4)
    (hcenter : degreeIn G p.center b = 3) (u : V) (hu : u ∈ b)
    (hbu : G.Adj (p.vertices 2) u) :
    degreeIn G u (insert p.leaf (b.erase u)) = 4 ∧
      degreeIn G p.center (insert p.leaf (b.erase u)) = 4 := by
  have hcl := FullRow.full_leaf_clique hc p hp hb hfull
  have hxout : p.leaf ∉ b := (c.presentPaw p hp).terminal_not_mem_block hb
  have hxe : p.leaf ∉ b.erase u := fun hh ↦ hxout (mem_erase.mp hh).2
  have hxu := (degreeIn_eq_card_iff p.leaf b).mp (hfull.trans hcl.card_eq.symm) u hu
  have hinside := degreeIn_clique G hcl.isClique hu
  rw [hcl.card_eq] at hinside
  have hrc := triangle_rows_disjoint hc hcard hn p hp hb (by omega) p.center (p.vertices 2)
    p.center_mem_triangle (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 2))
  have hrnot : ¬G.Adj p.center u := fun hh ↦
    disjoint_left.mp hrc (mem_filter.mpr ⟨hu, hh⟩) (mem_filter.mpr ⟨hu, hbu⟩)
  have hr := degreeIn_erase_add G p.center u hu
  rw [if_neg hrnot, hcenter] at hr
  have hrx : G.Adj p.center p.leaf := p.pendant.symm
  constructor
  · rw [degreeIn_insert G u p.leaf hxe, if_pos hxu.symm, degreeIn_erase_self G u hu, hinside]
  · rw [degreeIn_insert G p.center p.leaf hxe, if_pos hrx]
    omega

theorem exists_single_neighbor_exchange {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (hfull : degreeIn G p.leaf b = 4)
    (hcenter : degreeIn G p.center b = 3) (hsecond : degreeIn G (p.vertices 2) b = 1) :
    ∃ (d : TriangleChain G) (p' : Paw G) (s' : Finset V),
      d.Strong ∧ p'.support = d.remainder ∧ p'.center = p.vertices 2 ∧
      p'.vertices 3 = p.vertices 3 ∧ p'.triangle = p.triangle ∧
      s' ∈ d.blocks ∧ p.leaf ∈ s' ∧ degreeIn G p'.leaf s' = 4 ∧
      degreeIn G (p'.vertices 2) s' = 4 ∧ d.edgeScore = c.edgeScore ∧
      d.completeScore = c.completeScore ∧ ∀ a ∈ c.blocks, a ≠ b → a ∈ d.blocks := by
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (b.filter (G.Adj (p.vertices 2))).card by
    change 0 < degreeIn G (p.vertices 2) b
    omega)
  obtain ⟨hub, hbu⟩ := mem_filter.mp hu
  have hdis : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have huout : u ∉ p.support := by
    intro hh
    exact disjoint_left.mp hdis hh hub
  let p' := secondPaw p u huout hbu
  obtain ⟨d, hd, ht, hT, he, hcomp, hblocks⟩ :=
    FullRow.exists_full_leaf_swap hc p hp hb hfull u hub
  have hp' : p'.support = d.remainder := by
    rw [secondPaw_support]
    change insert u p.triangle = insert d.terminal d.triangle
    rw [ht, hT]
  have hbound := d.terminal_degree_le_one hcard hn
  rw [ht, hT] at hbound
  have hpos : 0 < degreeIn G u p.triangle := card_pos.mpr
    ⟨p.vertices 2, mem_filter.mpr ⟨by simp [Paw.triangle], hbu.symm⟩⟩
  have hstrong : d.Strong := by
    refine ⟨hd, ?_⟩
    change degreeIn G d.terminal d.triangle = 1
    rw [ht, hT]
    omega
  have hrows := single_neighbor_new_rows hc hcard hn p hp hb hfull hcenter u hub hbu
  refine ⟨d, p', insert p.leaf (b.erase u), hstrong, hp', rfl, rfl,
    secondPaw_triangle p u huout hbu, ?_, mem_insert_self _ _, hrows.1, hrows.2, he, hcomp, ?_⟩
  · rw [hblocks]
    exact mem_union_right _ (mem_singleton_self _)
  · intro a ha hab
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨hab, ha⟩)

end Erdos577.JointClaims

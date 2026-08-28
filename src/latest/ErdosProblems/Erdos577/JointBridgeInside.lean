import ErdosProblems.Erdos577.JointBridgeCommon

/-! The four bridge arms have exactly four vertices and inside contact budget thirty. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def arms (p : Paw G) (u z1 z2 : V) : Finset V := {p.leaf, u, z1, z2}

lemma arms_card (p : Paw G) (u z1 z2 : V) {a b : Finset V}
    (hFA : Disjoint p.support a) (hFB : Disjoint p.support b) (hAB : Disjoint a b)
    (hu : u ∈ b) (h1 : z1 ∈ a) (h2 : z2 ∈ a) (hne : z1 ≠ z2) :
    (arms p u z1 z2).card = 4 := by
  have hx : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  exact card_eq_four.mpr ⟨p.leaf, u, z1, z2,
    (fun he ↦ disjoint_left.mp hFB hx (he.symm ▸ hu)),
    (fun he ↦ disjoint_left.mp hFA hx (he.symm ▸ h1)),
    (fun he ↦ disjoint_left.mp hFA hx (he.symm ▸ h2)),
    (fun he ↦ disjoint_left.mp hAB h1 (he ▸ hu)),
    (fun he ↦ disjoint_left.mp hAB h2 (he ▸ hu)), hne, rfl⟩

lemma arms_center (p : Paw G) (u z1 z2 : V) (hu : G.Adj p.center u)
    (h1 : G.Adj p.center z1) (h2 : G.Adj p.center z2) :
    ∀ w ∈ arms p u z1 z2, G.Adj p.center w := by
  intro w hw
  simp only [arms, mem_insert, mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact p.pendant.symm
  · exact hu
  · exact h1
  · exact h2

variable [Fintype V] [DecidableRel G.Adj]

theorem bridge_column_inside {c : TriangleChain G}
    (p : Paw G) (hp : p.support = c.remainder)
    {s a b : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hb : b ∈ c.blocks)
    (has : a ≠ s) (hab : a ≠ b) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (u : V) (hu : u ∈ b)
    (hcol : degreeIn G u (p.triangle ∪ a) ≤ 1) :
    degreeIn G u (p.support ∪ q.support ∪ a ∪ b) ≤ 9 := by
  have hF (t : Finset V) (ht : t ∈ c.blocks) : Disjoint p.support t := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ht)
  obtain ⟨v, hv⟩ := c.property.blocks_quad b hb
  have hFB : Disjoint p.support v.support := by rw [hv]; exact hF b hb
  have hAB : Disjoint a v.support := by rw [hv]; exact c.property.blocks_disjoint ha hb hab
  have hsmall := JointFirst.inside_of_first_column p v hFB (hF a ha) hAB u (hv.symm ▸ hu) hcol
  rw [hv] at hsmall
  have hQ := degreeIn_le_card G u q.support
  rw [q.card_support] at hQ
  have hdis : Disjoint (p.support ∪ b ∪ a) q.support := by
    rw [hq]
    exact disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨hF s hs, c.property.blocks_disjoint hb hs hbs⟩, c.property.blocks_disjoint ha hs has⟩
  have he : p.support ∪ q.support ∪ a ∪ b = (p.support ∪ b ∪ a) ∪ q.support := by ac_rfl
  rw [he, degreeIn_union G u hdis]
  omega

theorem arms_inside_of_bounds {c : TriangleChain G}
    (p : Paw G) (hp : p.support = c.remainder)
    {s a b : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hb : b ∈ c.blocks)
    (has : a ≠ s) (hab : a ≠ b) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (u z1 z2 : V) (hu : u ∈ b)
    (hcol : degreeIn G u (p.triangle ∪ a) ≤ 1)
    (h17 : contacts G {p.leaf, z1, z2} (p.support ∪ q.support ∪ a) ≤ 17)
    (h4 : contacts G {p.leaf, z1, z2} b ≤ 4) :
    contacts G (arms p u z1 z2) (p.support ∪ q.support ∪ a ∪ b) ≤ 30 := by
  have hFB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hQB : Disjoint q.support b := by rw [hq]; exact c.property.blocks_disjoint hs hb hbs.symm
  have hdis : Disjoint (p.support ∪ q.support ∪ a) b := disjoint_union_left.mpr
    ⟨disjoint_union_left.mpr ⟨hFB, hQB⟩, c.property.blocks_disjoint ha hb hab⟩
  have htriple : contacts G {p.leaf, z1, z2} (p.support ∪ q.support ∪ a ∪ b) ≤ 21 := by
    rw [contacts_union_right G _ hdis]
    omega
  have hu9 := bridge_column_inside p hp hs ha hb has hab hbs q hq u hu hcol
  have hsum := JointCore.contacts_insert_upper (G := G) u {p.leaf, z1, z2}
    (p.support ∪ q.support ∪ a ∪ b)
  have he : insert u ({p.leaf, z1, z2} : Finset V) = arms p u z1 z2 := by
    rw [insert_comm]
    rfl
  rw [he] at hsum
  omega

end Erdos577.JointBridge

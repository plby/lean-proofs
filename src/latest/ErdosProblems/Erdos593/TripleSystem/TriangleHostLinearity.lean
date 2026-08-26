import ErdosProblems.Erdos593.TripleSystem.Basic
import Mathlib.Data.Set.PowersetCard

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The finite triangle host and its linearity

For a type `κ`, this module constructs the triple system whose vertices are
the two-element finite subsets of `κ`, whose edges are the three-element
finite subsets of `κ`, and where incidence is inclusion.  It establishes only
the finite combinatorial layer: 3-uniformity, simplicity, and linearity.

The Ramsey/Erdős–Rado statement that makes this host uncountably chromatic is
intentionally not assumed or proved here.
-/

namespace Erdos593

universe u

namespace TripleSystem
namespace TriangleHost

/-- The pair-vertices of the triangle host. -/
abbrev Pair (κ : Type u) := Set.powersetCard κ 2

/-- The triangle-edges of the triangle host. -/
abbrev Triangle (κ : Type u) := Set.powersetCard κ 3

/-- The three pair-faces of a triangle. -/
private def faces {κ : Type u} [DecidableEq κ] (t : Triangle κ) : Finset (Pair κ) :=
  (t.1.powersetCard 2).attach.map
    { toFun := fun s =>
        ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        simpa using! congrArg (fun p : Pair κ => p.1) hab }

private theorem mem_faces_iff {κ : Type u} [DecidableEq κ]
    (t : Triangle κ) (p : Pair κ) :
    p ∈ faces t ↔ p.1 ⊆ t.1 := by
  constructor
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨s, hs, hsp⟩
    rw [← hsp]
    exact (Finset.mem_powersetCard.mp s.2).1
  · intro hp
    let s : {s : Finset κ // s ∈ t.1.powersetCard 2} :=
      ⟨p.1, Finset.mem_powersetCard.mpr ⟨hp, p.2⟩⟩
    have hs : s ∈ (t.1.powersetCard 2).attach := Finset.mem_attach _ _
    apply Finset.mem_map.mpr
    refine ⟨s, hs, ?_⟩
    apply Subtype.ext
    rfl

private theorem card_faces {κ : Type u} [DecidableEq κ]
    (t : Triangle κ) : (faces t).card = 3 := by
  simp [faces, Finset.card_powersetCard]

private theorem pair_containing_of_mem {κ : Type u} [DecidableEq κ]
    (t : Triangle κ) {v : κ} (hv : v ∈ t.1) :
    ∃ p : Pair κ, v ∈ p.1 ∧ p.1 ⊆ t.1 := by
  rcases Finset.card_eq_three.mp t.2 with ⟨a, b, c, hab, hac, hbc, ht⟩
  rw [ht] at hv ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · refine ⟨⟨{v, b}, by simp [hab]⟩, ?_, ?_⟩ <;> simp
  · refine ⟨⟨{a, v}, by simp [hab]⟩, ?_, ?_⟩ <;> simp
  · refine ⟨⟨{a, v}, by simp [hac]⟩, ?_, ?_⟩ <;> simp

/-- The 3-uniform hypergraph of triangles in `κ`, with pair-vertices. -/
def system (κ : Type u) [DecidableEq κ] : TripleSystem (Pair κ) (Triangle κ) where
  Inc p t := p.1 ⊆ t.1
  edge_ncard := by
    intro t
    change Set.ncard {p : Pair κ | p.1 ⊆ t.1} = 3
    rw [show {p : Pair κ | p.1 ⊆ t.1} = (faces t : Set (Pair κ)) by
      ext p
      exact (mem_faces_iff t p).symm]
    simpa using! card_faces t
  simple := by
    intro t u htu
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨p, hvp, hpt⟩ := pair_containing_of_mem t hv
      have hpu : p.1 ⊆ u.1 := (Set.ext_iff.mp htu p).mp hpt
      exact hpu hvp
    · have ht : t.1.card = 3 := t.2
      have hu : u.1.card = 3 := u.2
      omega

/-- Distinct triangle edges share at most one pair-vertex. -/
theorem linear (κ : Type u) [DecidableEq κ] : (system κ).Linear := by
  intro e f x y hef hxe hxf hye hyf
  change x.1 ⊆ e.1 at hxe
  change x.1 ⊆ f.1 at hxf
  change y.1 ⊆ e.1 at hye
  change y.1 ⊆ f.1 at hyf
  by_contra hxy
  apply hef
  apply Subtype.ext
  let z := x.1 ∪ y.1
  have hze : z ⊆ e.1 := Finset.union_subset hxe hye
  have hzf : z ⊆ f.1 := Finset.union_subset hxf hyf
  have hx : x.1.card = 2 := x.2
  have hy : y.1.card = 2 := y.2
  have he : e.1.card = 3 := e.2
  have hf : f.1.card = 3 := f.2
  have hzle : z.card ≤ 3 := by
    calc
      z.card ≤ e.1.card := Finset.card_le_card hze
      _ = 3 := he
  have hxle : 2 ≤ z.card := by
    calc
      2 = x.1.card := hx.symm
      _ ≤ z.card := Finset.card_le_card Finset.subset_union_left
  have hz : z.card = 3 := by
    by_contra hne
    have hzle_two : z.card ≤ 2 := by omega
    have hzx : z.card ≤ x.1.card := by omega
    have hzy : z.card ≤ y.1.card := by omega
    have hxz : x.1 = z := Finset.eq_of_subset_of_card_le Finset.subset_union_left hzx
    have hyz : y.1 = z := Finset.eq_of_subset_of_card_le Finset.subset_union_right hzy
    apply hxy
    apply Subtype.ext
    exact hxz.trans hyz.symm
  have hzeq : z = e.1 := by
    apply Finset.eq_of_subset_of_card_le hze
    omega
  have hzfq : z = f.1 := by
    apply Finset.eq_of_subset_of_card_le hzf
    omega
  exact hzeq.symm.trans hzfq

end TriangleHost
end TripleSystem
end Erdos593

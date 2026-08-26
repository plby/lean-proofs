import Mathlib
import ErdosProblems.Erdos550.DynamicSequentialEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sequential embedding by dependency blocks

The specialized Hladký--Piguet procedure alternates between one-vertex head
blocks and whole shrub blocks.  A shrub is embedded after its upper head
vertex; its lower head vertex is deliberately left for a later step.  This
module isolates that finite gluing argument.

Blocks partition the source.  At a downward-closed union of blocks, a ready
vertex determines a fresh block.  The `hpredecessor` hypothesis says that every
parent of a vertex in that block is either internal to the block or already
processed.  The analytic caller only has to supply an embedding of that one
block away from the old image.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

/-- A set is a union of complete blocks. -/
def IsBlockClosed
    {A : Type*} [Fintype A] [DecidableEq A]
    (block : A → Finset A) (S : Finset A) : Prop :=
  ∀ a ∈ S, block a ⊆ S

/-- Block-by-block extension of a rooted finite graph embedding. -/
theorem sequential_block_embedding
    {A V : Type*} [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (block : A → Finset A)
    (hself : ∀ a, a ∈ block a)
    (hblock : ∀ a b, b ∈ block a → block b = block a)
    (hpredecessor : ∀ (S : Finset A),
      IsBlockClosed block S →
      (∀ x ∈ S, ∀ y, parent x = some y → y ∈ S) →
      ∀ a ∉ S, (∀ y, parent a = some y → y ∈ S) →
      ∀ x ∈ block a, ∀ y, parent x = some y →
        y ∈ block a ∨ y ∈ S)
    (cand anchors : A → Finset V)
    (hext : ∀ (S : Finset A) (f : A → V),
      IsBlockClosed block S →
      (∀ x ∈ S, ∀ y, parent x = some y → y ∈ S) →
      Set.InjOn f S →
      (∀ x ∈ S, f x ∈ cand x) →
      (∀ x ∈ S, ∀ y, parent x = some y → G.Adj (f x) (f y)) →
      (∀ x ∈ S, ∀ z ∈ anchors x, G.Adj z (f x)) →
      ∀ a ∉ S, (∀ y, parent a = some y → y ∈ S) →
        ∃ g : A → V,
          Set.InjOn g (block a) ∧
          Disjoint ((block a).image g) (S.image f) ∧
          (∀ x ∈ block a, g x ∈ cand x) ∧
          (∀ x ∈ block a, ∀ y, parent x = some y →
            if y ∈ block a then G.Adj (g x) (g y)
            else G.Adj (g x) (f y)) ∧
          (∀ x ∈ block a, ∀ z ∈ anchors x, G.Adj z (g x))) :
    ∃ f : A → V, Function.Injective f ∧
      (∀ a, f a ∈ cand a) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) ∧
      (∀ a z, z ∈ anchors a → G.Adj z (f a)) := by
  let Good : Finset A → (A → V) → Prop := fun S f =>
    IsBlockClosed block S ∧
    (∀ x ∈ S, ∀ y, parent x = some y → y ∈ S) ∧
    Set.InjOn f S ∧
    (∀ x ∈ S, f x ∈ cand x) ∧
    (∀ x ∈ S, ∀ y, parent x = some y → G.Adj (f x) (f y)) ∧
    (∀ x ∈ S, ∀ z ∈ anchors x, G.Adj z (f x))
  let P : Finset (Finset A) :=
    Finset.univ.filter fun S => ∃ f, Good S f
  have hPnonempty : P.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [P, Good, IsBlockClosed, Set.InjOn]
  obtain ⟨S, hSP, hmax⟩ := P.exists_max_image Finset.card hPnonempty
  obtain ⟨f, hSblock, hSdown, hfinj, hfmem, hfparent, hfanchor⟩ :
      ∃ f, Good S f := by
    simpa [P] using! (Finset.mem_filter.mp hSP).2
  have hSuniv : S = Finset.univ := by
    by_contra hne
    obtain ⟨a, haS, hready⟩ :=
      exists_ready_vertex parent rank hrank S hne
    obtain ⟨g, hginj, hgdisj, hgmem, hgparent, hganchor⟩ :=
      hext S f hSblock hSdown hfinj hfmem hfparent hfanchor
        a haS hready
    let B := block a
    let S' := S ∪ B
    let f' : A → V := fun x => if x ∈ B then g x else f x
    have hBS : Disjoint B S := by
      rw [Finset.disjoint_left]
      intro x hxB hxS
      have hBx : block x = B := hblock a x hxB
      have hxsub : block x ⊆ S := hSblock x hxS
      exact haS (hxsub (by simpa [hBx, B] using! hself a))
    have hGood' : Good S' f' := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx y hy
        rcases Finset.mem_union.mp hx with hxS | hxB
        · exact Finset.mem_union_left _ (hSblock x hxS hy)
        · have hxy : block y = block x := hblock x y hy
          have hxa : block x = B := hblock a x hxB
          exact Finset.mem_union_right S (by simpa [hxy, hxa, B] using! hself y)
      · intro x hx y hxy
        rcases Finset.mem_union.mp hx with hxS | hxB
        · exact Finset.mem_union_left _ (hSdown x hxS y hxy)
        · rcases hpredecessor S hSblock hSdown a haS hready
              x hxB y hxy with hyB | hyS
          · exact Finset.mem_union_right _ hyB
          · exact Finset.mem_union_left _ hyS
      · intro x hx y hy hxy
        rcases Finset.mem_union.mp hx with hxS | hxB <;>
          rcases Finset.mem_union.mp hy with hyS | hyB
        · have hxnot : x ∉ B :=
            fun hxB => Finset.disjoint_left.mp hBS hxB hxS
          have hynot : y ∉ B :=
            fun hyB => Finset.disjoint_left.mp hBS hyB hyS
          simp only [f', hxnot, hynot, if_false] at hxy
          exact hfinj hxS hyS hxy
        · have hxnot : x ∉ B :=
            fun hxB => Finset.disjoint_left.mp hBS hxB hxS
          simp only [f', hxnot, hyB, if_false, if_true] at hxy
          have hfx : f x ∈ S.image f :=
            Finset.mem_image.mpr ⟨x, hxS, rfl⟩
          have hgy : g y ∈ B.image g :=
            Finset.mem_image.mpr ⟨y, hyB, rfl⟩
          rw [hxy] at hfx
          exact False.elim
            (Finset.disjoint_left.mp hgdisj hgy hfx)
        · have hynot : y ∉ B :=
            fun hyB => Finset.disjoint_left.mp hBS hyB hyS
          simp only [f', hxB, hynot, if_true, if_false] at hxy
          have hgx : g x ∈ B.image g :=
            Finset.mem_image.mpr ⟨x, hxB, rfl⟩
          have hfy : f y ∈ S.image f :=
            Finset.mem_image.mpr ⟨y, hyS, rfl⟩
          rw [← hxy] at hfy
          exact False.elim
            (Finset.disjoint_left.mp hgdisj hgx hfy)
        · simp only [f', hxB, hyB, if_true] at hxy
          exact hginj hxB hyB hxy
      · intro x hx
        rcases Finset.mem_union.mp hx with hxS | hxB
        · have hxnot : x ∉ B :=
            fun hxB => Finset.disjoint_left.mp hBS hxB hxS
          simpa [f', hxnot] using! hfmem x hxS
        · simpa [f', hxB] using! hgmem x hxB
      · intro x hx y hxy
        rcases Finset.mem_union.mp hx with hxS | hxB
        · have hyS := hSdown x hxS y hxy
          have hxnot : x ∉ B :=
            fun hxB => Finset.disjoint_left.mp hBS hxB hxS
          have hynot : y ∉ B :=
            fun hyB => Finset.disjoint_left.mp hBS hyB hyS
          simpa [f', hxnot, hynot] using! hfparent x hxS y hxy
        · have hpred :=
            hpredecessor S hSblock hSdown a haS hready x hxB y hxy
          rcases hpred with hyB | hyS
          · have hg : G.Adj (g x) (g y) := by
              simpa [B, hyB] using! hgparent x hxB y hxy
            have hyB' : y ∈ B := by simpa [B] using! hyB
            simpa [f', hxB, hyB'] using! hg
          · have hynot : y ∉ B :=
              fun hyB => Finset.disjoint_left.mp hBS hyB hyS
            have hg : G.Adj (g x) (f y) := by
              simpa [B, hynot] using! hgparent x hxB y hxy
            simpa [f', hxB, hynot] using! hg
      · intro x hx z hz
        rcases Finset.mem_union.mp hx with hxS | hxB
        · have hxnot : x ∉ B :=
            fun hxB => Finset.disjoint_left.mp hBS hxB hxS
          simpa [f', hxnot] using! hfanchor x hxS z hz
        · simpa [f', hxB] using! hganchor x hxB z hz
    have hS'P : S' ∈ P := by
      simp [P]
      exact ⟨f', hGood'⟩
    have hcardlt : S.card < S'.card := by
      have haB : a ∈ B := hself a
      have haS' : a ∈ S' := Finset.mem_union_right S haB
      exact Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.subset_union_left, fun h => haS (h ▸ haS')⟩)
    exact (not_lt_of_ge (hmax S' hS'P)) hcardlt
  subst S
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact hfinj (by simp) (by simp) hab
  · intro a
    exact hfmem a (by simp)
  · intro a b hab
    exact hfparent a (by simp) b hab
  · intro a z hz
    exact hfanchor a (by simp) z hz

end Erdos550

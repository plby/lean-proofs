import Mathlib
import ErdosProblems.Erdos550.DynamicSequentialEmbedding
import ErdosProblems.Erdos550.SequentialBlockEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Stateful induction over dependency blocks

The stateful embedding carries numerical load and packedness invariants that
are properties of the entire partial embedding.  This maximal-extension
principle keeps an arbitrary predicate `Good S f`, while exposing a ready
source vertex whose predecessor has already been processed.
-/

open Finset

namespace Erdos550

open Classical

/-- If every proper good partial state can be extended by the full block of a
ready vertex, then there is a good state on every source vertex. -/
theorem stateful_block_induction
    {A State : Type*} [Fintype A] [DecidableEq A]
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (block : A → Finset A)
    (hself : ∀ a, a ∈ block a)
    (Good : Finset A → State → Prop)
    (hzero : ∃ z, Good ∅ z)
    (hext : ∀ (S : Finset A) (z : State), Good S z →
      ∀ a ∉ S, (∀ b, parent a = some b → b ∈ S) →
        ∃ z', Good (S ∪ block a) z') :
    ∃ z, Good Finset.univ z := by
  let P : Finset (Finset A) :=
    Finset.univ.filter fun S => ∃ z, Good S z
  have hP : P.Nonempty := by
    obtain ⟨z, hz⟩ := hzero
    exact ⟨∅, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨z, hz⟩⟩⟩
  obtain ⟨S, hSP, hmax⟩ :=
    P.exists_max_image Finset.card hP
  obtain ⟨z, hz⟩ : ∃ z, Good S z := by
    simpa [P] using! (Finset.mem_filter.mp hSP).2
  have hSuniv : S = Finset.univ := by
    by_contra hne
    obtain ⟨a, haS, hready⟩ :=
      exists_ready_vertex parent rank hrank S hne
    obtain ⟨z', hz'⟩ := hext S z hz a haS hready
    have hnewP : S ∪ block a ∈ P := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨z', hz'⟩⟩
    have hlt : S.card < (S ∪ block a).card := by
      apply Finset.card_lt_card
      exact Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_union_left, fun heq =>
          haS (heq ▸ Finset.mem_union_right S (hself a))⟩
    exact (not_lt_of_ge (hmax (S ∪ block a) hnewP)) hlt
  subst S
  exact ⟨z, hz⟩

/-- Graph-embedding form of `stateful_block_induction`.  The caller supplies a
local fresh embedding of the next block and proves the arbitrary global
invariant `Inv` for the glued map.  Injectivity, downward closure, block closure,
and parent-edge adjacency are maintained here once and for all. -/
theorem stateful_sequential_block_embedding
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
    (Inv : Finset A → (A → V) → Prop)
    (hzero : Inv ∅ (fun _ => Classical.arbitrary V))
    (hext : ∀ (S : Finset A) (f : A → V),
      IsBlockClosed block S →
      (∀ x ∈ S, ∀ y, parent x = some y → y ∈ S) →
      Set.InjOn f S →
      (∀ x ∈ S, ∀ y, parent x = some y → G.Adj (f x) (f y)) →
      Inv S f →
      ∀ a ∉ S, (∀ y, parent a = some y → y ∈ S) →
        ∃ g : A → V,
          Set.InjOn g (block a) ∧
          Disjoint ((block a).image g) (S.image f) ∧
          (∀ x ∈ block a, ∀ y, parent x = some y →
            if y ∈ block a then G.Adj (g x) (g y)
            else G.Adj (g x) (f y)) ∧
          Inv (S ∪ block a) (fun x =>
            if x ∈ block a then g x else f x)) :
    ∃ f : A → V, Function.Injective f ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) ∧
      Inv Finset.univ f := by
  let Good : Finset A → (A → V) → Prop := fun S f =>
    IsBlockClosed block S ∧
    (∀ x ∈ S, ∀ y, parent x = some y → y ∈ S) ∧
    Set.InjOn f S ∧
    (∀ x ∈ S, ∀ y, parent x = some y → G.Adj (f x) (f y)) ∧
    Inv S f
  have hGoodZero : Good ∅ (fun _ => Classical.arbitrary V) := by
    refine ⟨?_, ?_, ?_, ?_, hzero⟩ <;>
      simp [IsBlockClosed, Set.InjOn]
  have hGoodExt : ∀ (S : Finset A) (f : A → V), Good S f →
      ∀ a ∉ S, (∀ b, parent a = some b → b ∈ S) →
        ∃ f', Good (S ∪ block a) f' := by
    intro S f hGood a haS hready
    obtain ⟨hSblock, hSdown, hfinj, hfparent, hInv⟩ := hGood
    obtain ⟨g, hginj, hgdisj, hgparent, hgInv⟩ :=
      hext S f hSblock hSdown hfinj hfparent hInv a haS hready
    let B := block a
    let f' : A → V := fun x => if x ∈ B then g x else f x
    have hBS : Disjoint B S := by
      rw [Finset.disjoint_left]
      intro x hxB hxS
      have hBx : block x = B := hblock a x hxB
      have hxsub : block x ⊆ S := hSblock x hxS
      exact haS (hxsub (by simpa [hBx, B] using! hself a))
    refine ⟨f', ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      rcases Finset.mem_union.mp hx with hxS | hxB
      · exact Finset.mem_union_left _ (hSblock x hxS hy)
      · have hxy : block y = block x := hblock x y hy
        have hxa : block x = B := hblock a x hxB
        exact Finset.mem_union_right S
          (by simpa [hxy, hxa, B] using! hself y)
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
        apply hfinj hxS hyS
        simpa [f', hxnot, hynot] using! hxy
      · have hxnot : x ∉ B :=
          fun hxB => Finset.disjoint_left.mp hBS hxB hxS
        have hyB' : y ∈ B := by simpa [B] using! hyB
        have hfx : f x ∈ S.image f :=
          Finset.mem_image.mpr ⟨x, hxS, rfl⟩
        have hgy : g y ∈ B.image g :=
          Finset.mem_image.mpr ⟨y, hyB', rfl⟩
        have heq : f x = g y := by
          simpa [f', hxnot, hyB'] using! hxy
        rw [heq] at hfx
        exact False.elim
          (Finset.disjoint_left.mp hgdisj hgy hfx)
      · have hynot : y ∉ B :=
          fun hyB => Finset.disjoint_left.mp hBS hyB hyS
        have hxB' : x ∈ B := by simpa [B] using! hxB
        have hgx : g x ∈ B.image g :=
          Finset.mem_image.mpr ⟨x, hxB', rfl⟩
        have hfy : f y ∈ S.image f :=
          Finset.mem_image.mpr ⟨y, hyS, rfl⟩
        have heq : g x = f y := by
          simpa [f', hxB', hynot] using! hxy
        rw [← heq] at hfy
        exact False.elim
          (Finset.disjoint_left.mp hgdisj hgx hfy)
      · apply hginj hxB hyB
        have hxB' : x ∈ B := by simpa [B] using! hxB
        have hyB' : y ∈ B := by simpa [B] using! hyB
        simpa [f', hxB', hyB'] using! hxy
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
        have hxB' : x ∈ B := by simpa [B] using! hxB
        rcases hpred with hyB | hyS
        · have hyB' : y ∈ B := by simpa [B] using! hyB
          have hg : G.Adj (g x) (g y) := by
            simpa [B, hyB] using! hgparent x hxB y hxy
          simpa [f', hxB', hyB'] using! hg
        · have hynot : y ∉ B :=
            fun hyB => Finset.disjoint_left.mp hBS hyB hyS
          have hg : G.Adj (g x) (f y) := by
            simpa [B, hynot] using! hgparent x hxB y hxy
          simpa [f', hxB', hynot] using! hg
    · simpa [B, f'] using! hgInv
  obtain ⟨f, hf⟩ :=
    stateful_block_induction parent rank hrank block hself
      Good ⟨_, hGoodZero⟩ hGoodExt
  obtain ⟨_, _, hfinj, hadj, hInv⟩ := hf
  refine ⟨f, ?_, ?_, hInv⟩
  · intro x y hxy
    exact hfinj (by simp) (by simp) hxy
  · intro a b hab
    exact hadj a (by simp) b hab

end Erdos550

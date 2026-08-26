import Mathlib
import ErdosProblems.Erdos550.StatefulSequentialBlockEmbedding
import ErdosProblems.Erdos550.TauFineBlockOrder

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Stateful embedding over seed singletons and component blocks

This is the global induction skeleton of the parity-refined off--Turán route.
It exposes exactly two extension obligations: one for a ready seed singleton
and one for a ready deleted component.  All closure, freshness, injectivity and
edge gluing are handled here.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

/-- The common conclusion required of either kind of local block extension. -/
def IsFreshBlockExtension
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (G : SimpleGraph V) (parent : A → Option A)
    (block P : Finset A) (f : A → V)
    (Inv : Finset A → (A → V) → Prop) : Prop :=
  ∃ g : A → V,
    Set.InjOn g block ∧
    Disjoint (block.image g) (P.image f) ∧
    (∀ x ∈ block, ∀ y, parent x = some y →
      if y ∈ block then G.Adj (g x) (g y)
      else G.Adj (g x) (f y)) ∧
    Inv (P ∪ block) (fun x => if x ∈ block then g x else f x)

/-- If both ready seed blocks and ready component blocks admit fresh
extensions preserving an arbitrary state invariant, the whole rooted tree is
embedded and the invariant holds at the final state. -/
theorem stateful_tauFine_embedding
    {A : Type} {V : Type*} [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (T : SimpleGraph A)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Sseed : Finset A)
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (D : RootedSeedComponentData T Sseed parent)
    (Inv : Finset A → (A → V) → Prop)
    (hzero : Inv ∅ (fun _ => Classical.arbitrary V))
    (hseedExt : ∀ (P : Finset A) (f : A → V),
      IsBlockClosed (tauFineBlock T Sseed) P →
      (∀ x ∈ P, ∀ y, parent x = some y → y ∈ P) →
      Set.InjOn f P →
      (∀ x ∈ P, ∀ y, parent x = some y → G.Adj (f x) (f y)) →
      Inv P f →
      ∀ a ∉ P, (∀ y, parent a = some y → y ∈ P) →
      a ∈ Sseed →
      IsFreshBlockExtension G parent (tauFineBlock T Sseed a)
        P f Inv)
    (hcomponentExt : ∀ (P : Finset A) (f : A → V),
      IsBlockClosed (tauFineBlock T Sseed) P →
      (∀ x ∈ P, ∀ y, parent x = some y → y ∈ P) →
      Set.InjOn f P →
      (∀ x ∈ P, ∀ y, parent x = some y → G.Adj (f x) (f y)) →
      Inv P f →
      ∀ a ∉ P, (∀ y, parent a = some y → y ∈ P) →
      a ∉ Sseed →
      IsFreshBlockExtension G parent (tauFineBlock T Sseed a)
        P f Inv) :
    ∃ f : A → V, Function.Injective f ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) ∧
      Inv Finset.univ f := by
  apply stateful_sequential_block_embedding G parent rank hrank
    (tauFineBlock T Sseed)
    (mem_tauFineBlock_self T Sseed)
    (fun a b hb => tauFineBlock_eq_of_mem T Sseed hb)
    (tauFineBlock_predecessor T Sseed parent D)
    Inv hzero
  intro P f hPblock hPdown hfinj hfadj hInv a haP hready
  by_cases haS : a ∈ Sseed
  · exact hseedExt P f hPblock hPdown hfinj hfadj hInv
      a haP hready haS
  · exact hcomponentExt P f hPblock hPdown hfinj hfadj hInv
      a haP hready haS

/-- Graph-containment packaging of the stateful τ-fine induction. -/
theorem stateful_tauFine_graph_embedding
    {A : Type} {V : Type*} [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Sseed : Finset A)
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (D : RootedSeedComponentData T Sseed parent)
    (Inv : Finset A → (A → V) → Prop)
    (hzero : Inv ∅ (fun _ => Classical.arbitrary V))
    (hseedExt : ∀ (P : Finset A) (f : A → V),
      IsBlockClosed (tauFineBlock T Sseed) P →
      (∀ x ∈ P, ∀ y, parent x = some y → y ∈ P) →
      Set.InjOn f P →
      (∀ x ∈ P, ∀ y, parent x = some y → G.Adj (f x) (f y)) →
      Inv P f →
      ∀ a ∉ P, (∀ y, parent a = some y → y ∈ P) →
      a ∈ Sseed →
      IsFreshBlockExtension G parent (tauFineBlock T Sseed a)
        P f Inv)
    (hcomponentExt : ∀ (P : Finset A) (f : A → V),
      IsBlockClosed (tauFineBlock T Sseed) P →
      (∀ x ∈ P, ∀ y, parent x = some y → y ∈ P) →
      Set.InjOn f P →
      (∀ x ∈ P, ∀ y, parent x = some y → G.Adj (f x) (f y)) →
      Inv P f →
      ∀ a ∉ P, (∀ y, parent a = some y → y ∈ P) →
      a ∉ Sseed →
      IsFreshBlockExtension G parent (tauFineBlock T Sseed a)
        P f Inv) :
    T ⊑ G := by
  obtain ⟨f, hfinj, hparent, _⟩ :=
    stateful_tauFine_embedding T G Sseed parent rank hrank D Inv hzero
      hseedExt hcomponentExt
  refine ⟨SimpleGraph.Copy.mk (RelHom.mk f ?_) hfinj⟩
  intro a b hab
  rcases hedge a b hab with h | h
  · exact hparent a b h
  · exact (hparent b a h).symm

end Erdos550

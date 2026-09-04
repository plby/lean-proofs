import ErdosProblems.Erdos593.Graph.CompleteBipartite
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fintype.EquivFin

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Copies of balanced complete bipartite graphs

An explicit non-induced `K_{n,n}` copy is assembled from two disjoint finite
families with all cross adjacencies. The common-neighbour formulation is the
one used by the closure-chain proof of manuscript Lemma 2.1.
-/

namespace Erdos593

universe u

namespace SimpleGraph

variable {V : Type u} (G : _root_.SimpleGraph V)

/-- Enumerate an `n`-element finset by the universe-compatible finite part. -/
noncomputable def finiteBipartitePartEquivFinset (s : Finset V) {n : ℕ}
    (hcard : s.card = n) : FiniteBipartitePart.{u} n ≃ s :=
  Equiv.ulift.{u, 0}.trans <|
    (finCongr hcard.symm).trans
      ((finCongr (Fintype.card_coe s).symm).trans (Fintype.equivFin s).symm)

/-- Enumerate an `n`-element finset as a universe-compatible injected side. -/
noncomputable def finiteBipartitePartEmbeddingFinset (s : Finset V) {n : ℕ}
    (hcard : s.card = n) : FiniteBipartitePart.{u} n ↪ V :=
  (finiteBipartitePartEquivFinset s hcard).toEmbedding.trans
    (Function.Embedding.subtype _)

theorem finiteBipartitePartEmbeddingFinset_mem (s : Finset V) {n : ℕ}
    (hcard : s.card = n) (i : FiniteBipartitePart.{u} n) :
    finiteBipartitePartEmbeddingFinset s hcard i ∈ s := by
  classical
  change ((finiteBipartitePartEquivFinset s hcard i : s) : V) ∈ s
  exact (finiteBipartitePartEquivFinset s hcard i).property

/-- Two disjoint injective sides with every cross edge give a non-induced
copy of `K_{n,n}`. -/
def completeBipartiteNNCopyOfEmbeddings (n : ℕ)
    (left right : FiniteBipartitePart.{u} n ↪ V)
    (hdisjoint : ∀ a b, left a ≠ right b)
    (hadj : ∀ a b, G.Adj (left a) (right b)) :
    _root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G where
  toHom :=
    { toFun := Sum.elim left right
      map_rel' := by
        intro x y hxy
        rcases x with x | x <;> rcases y with y | y
        · simp at hxy
        · exact hadj x y
        · exact (hadj y x).symm
        · simp at hxy }
  injective' := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (left.injective hxy)
    · exact (hdisjoint x y hxy).elim
    · exact (hdisjoint y x hxy.symm).elim
    · exact congrArg Sum.inr (right.injective hxy)

/-- Common neighbours of a finite left side. -/
def commonNeighborSet {n : ℕ}
    (left : FiniteBipartitePart.{u} n ↪ V) : Set V :=
  {v | ∀ i, G.Adj (left i) v}

/-- An embedding of a second side into the common-neighbour set produces a
`K_{n,n}` copy. Disjointness follows automatically from looplessness. -/
def completeBipartiteNNCopyOfCommonNeighbors {n : ℕ}
    (left : FiniteBipartitePart.{u} n ↪ V)
    (right : FiniteBipartitePart.{u} n ↪ commonNeighborSet G left) :
    _root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G := by
  let rightV : FiniteBipartitePart.{u} n ↪ V :=
    right.trans (Function.Embedding.subtype _)
  apply completeBipartiteNNCopyOfEmbeddings G n left rightV
  · intro a b hab
    have hAdj : G.Adj (left a) (rightV b) := (right b).property a
    exact G.loopless.irrefl (left a) (hab ▸ hAdj)
  · intro a b
    exact (right b).property a

/-- In a `K_{n,n}`-free graph, the common-neighbour type of every injected
left side admits no injected second side. -/
theorem no_embedding_commonNeighbors_of_no_completeBipartiteNNCopy {n : ℕ}
    (hfree : IsEmpty
      (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (left : FiniteBipartitePart.{u} n ↪ V) :
    IsEmpty (FiniteBipartitePart.{u} n ↪ commonNeighborSet G left) :=
  ⟨fun right ↦ hfree.false
    (completeBipartiteNNCopyOfCommonNeighbors G left right)⟩

/-- In a `K_{n,n}`-free graph every common-neighbour set of an injected
`n`-element side is finite. -/
theorem commonNeighborSet_finite_of_no_completeBipartiteNNCopy {n : ℕ}
    (hfree : IsEmpty
      (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (left : FiniteBipartitePart.{u} n ↪ V) :
    Set.Finite (commonNeighborSet G left) := by
  classical
  let S := commonNeighborSet G left
  have hno := no_embedding_commonNeighbors_of_no_completeBipartiteNNCopy G hfree left
  by_contra hfinite
  let : Infinite S := Set.infinite_coe_iff.mpr hfinite
  let finToNat : FiniteBipartitePart.{u} n ↪ ℕ :=
    (Equiv.ulift.{u, 0}.toEmbedding).trans Fin.valEmbedding
  let right : FiniteBipartitePart.{u} n ↪ S :=
    finToNat.trans (Infinite.natEmbedding S)
  exact hno.false right

/-- Quantitative common-neighbour bound in a `K_{n,n}`-free graph. -/
theorem commonNeighborSet_toFinset_card_lt_of_no_completeBipartiteNNCopy
    {n : ℕ}
    (hfree : IsEmpty
      (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (left : FiniteBipartitePart.{u} n ↪ V) :
    (commonNeighborSet_finite_of_no_completeBipartiteNNCopy G hfree left).toFinset.card < n := by
  classical
  let S := commonNeighborSet G left
  let hS : Set.Finite S :=
    commonNeighborSet_finite_of_no_completeBipartiteNNCopy G hfree left
  have hno := no_embedding_commonNeighbors_of_no_completeBipartiteNNCopy G hfree left
  by_contra hlt
  have hle : n ≤ hS.toFinset.card := Nat.le_of_not_gt hlt
  let finIncl : Fin n ↪ Fin hS.toFinset.card :=
    { toFun := fun i ↦ ⟨i, i.isLt.trans_le hle⟩
      inj' := fun _ _ h ↦
        Fin.ext (congrArg (fun z : Fin hS.toFinset.card ↦ z.val) h) }
  let cardEquiv : Fin hS.toFinset.card ≃ hS.toFinset :=
    (finCongr (Fintype.card_coe hS.toFinset).symm).trans
      (Fintype.equivFin hS.toFinset).symm
  let finsetToSet : hS.toFinset ↪ S :=
    { toFun := fun x ↦
        ⟨x, by simpa only [Set.Finite.mem_toFinset] using! x.property⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : S ↦ z.val) h }
  let right : FiniteBipartitePart.{u} n ↪ S :=
    (Equiv.ulift.{u, 0}.toEmbedding).trans
      (finIncl.trans (cardEquiv.toEmbedding.trans finsetToSet))
  exact hno.false right

/-- A non-induced `K_{q,q}` copy supplies injected finite left and right
sides, with all cross adjacencies and no cross-side collisions. -/
theorem exists_finEmbeddings_of_completeBipartiteNNCopy {q : Nat}
    (f : _root_.SimpleGraph.Copy (completeBipartiteNN.{u} q) G) :
    ∃ left right : Fin q ↪ V,
      (∀ i j, left i ≠ right j) ∧ ∀ i j, G.Adj (left i) (right j) := by
  let left : Fin q ↪ V :=
    { toFun := fun i => f (Sum.inl (ULift.up i))
      inj' := by
        intro i j hij
        have h := f.injective hij
        simpa using! h }
  let right : Fin q ↪ V :=
    { toFun := fun j => f (Sum.inr (ULift.up j))
      inj' := by
        intro i j hij
        have h := f.injective hij
        simpa using! h }
  refine ⟨left, right, ?_, ?_⟩
  · intro i j h
    have hsrc : (completeBipartiteNN.{u} q).Adj
        (Sum.inl (ULift.up i)) (Sum.inr (ULift.up j)) := by
      simp [completeBipartiteNN]
    have htgt : G.Adj (left i) (right j) := by
      simpa [left, right] using! f.toHom.map_adj hsrc
    exact G.loopless.irrefl (left i) (h ▸ htgt)
  · intro i j
    have hsrc : (completeBipartiteNN.{u} q).Adj
        (Sum.inl (ULift.up i)) (Sum.inr (ULift.up j)) := by
      simp [completeBipartiteNN]
    simpa [left, right] using! f.toHom.map_adj hsrc

end SimpleGraph

end Erdos593

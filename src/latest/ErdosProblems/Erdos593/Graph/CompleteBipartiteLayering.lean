import ErdosProblems.Erdos593.Graph.CompleteBipartiteCopy
import ErdosProblems.Erdos593.Graph.CountableColoring
import ErdosProblems.Erdos593.Graph.FiniteClosureLayering

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Closure layerings and complete-bipartite forcing

This file supplies the local graph-theoretic half of the positive-atom
strategy.  In a `K_{n,n}`-free graph, a rank layering closed under finite
common-neighbour sets has fewer than `n` backward neighbours at every
vertex.  Thus, once its fibres are countably colourable, the whole graph is
countably colourable.

Constructing such a layering with small fibres is deliberately separate: it
is the singular-cardinal-sensitive infinitary part of the argument.
-/

namespace Erdos593

universe u

namespace SimpleGraph

variable {V : Type u} (G : _root_.SimpleGraph V)

/-- If a set admits no injected `n`-element bipartite part, then it is finite. -/
theorem finite_of_no_finiteBipartitePart_embedding {n : Nat} (S : Set V)
    (hno : IsEmpty (FiniteBipartitePart.{u} n ↪ S)) :
    Set.Finite S := by
  classical
  by_contra hfinite
  let : Infinite S := Set.infinite_coe_iff.mpr hfinite
  let finToNat : FiniteBipartitePart.{u} n ↪ Nat :=
    (Equiv.ulift.{u, 0}.toEmbedding).trans Fin.valEmbedding
  let right : FiniteBipartitePart.{u} n ↪ S :=
    finToNat.trans (Infinite.natEmbedding S)
  exact hno.false right

/-- The finite set above has cardinality strictly smaller than `n`. -/
theorem toFinset_card_lt_of_no_finiteBipartitePart_embedding {n : Nat}
    (S : Set V) (hno : IsEmpty (FiniteBipartitePart.{u} n ↪ S)) :
    (finite_of_no_finiteBipartitePart_embedding S hno).toFinset.card < n := by
  classical
  let hS : Set.Finite S := finite_of_no_finiteBipartitePart_embedding S hno
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

/-- The finite common-neighbour closure of an `n`-set in a `K_{n,n}`-free
graph. -/
noncomputable def commonNeighborClosure {n : Nat}
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G)) :
    {s : Finset V // s.card = n} → Finset V :=
  fun s ↦
    (commonNeighborSet_finite_of_no_completeBipartiteNNCopy G hfree
      (finiteBipartitePartEmbeddingFinset s.1 s.2)).toFinset

/-- Membership in the common-neighbour closure is exactly adjacency to every
element of its input finite set. -/
theorem mem_commonNeighborClosure_iff {n : Nat}
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (s : {s : Finset V // s.card = n}) (v : V) :
    v ∈ commonNeighborClosure G hfree s ↔ ∀ x ∈ s.1, G.Adj x v := by
  classical
  constructor
  · intro hv x hx
    have hv' : v ∈ commonNeighborSet G
        (finiteBipartitePartEmbeddingFinset s.1 s.2) := by
      simpa only [commonNeighborClosure, Set.Finite.mem_toFinset] using! hv
    let i : FiniteBipartitePart.{u} n :=
      (finiteBipartitePartEquivFinset s.1 s.2).symm ⟨x, hx⟩
    have hi : finiteBipartitePartEmbeddingFinset s.1 s.2 i = x := by
      change ((finiteBipartitePartEquivFinset s.1 s.2 i : s.1) : V) = x
      exact congrArg Subtype.val
        ((finiteBipartitePartEquivFinset s.1 s.2).apply_symm_apply ⟨x, hx⟩)
    rw [← hi]
    exact hv' i
  · intro hv
    simp only [commonNeighborClosure, Set.Finite.mem_toFinset, commonNeighborSet,
      Set.mem_setOf_eq]
    intro i
    exact hv _ (finiteBipartitePartEmbeddingFinset_mem s.1 s.2 i)

/-- A common-neighbour-closed layering prohibits an injected `n`-element
family of backward neighbours at any vertex. -/
theorem no_embedding_backNeighbors_of_commonNeighborLayering
    {n : Nat} {I : Type u} [LinearOrder I]
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I) (v : V) :
    IsEmpty (FiniteBipartitePart.{u} n ↪
      {x : V | G.Adj v x ∧ L.rank x < L.rank v}) := by
  classical
  refine ⟨?_⟩
  intro e
  let eV : FiniteBipartitePart.{u} n ↪ V :=
    e.trans (Function.Embedding.subtype _)
  let s : Finset V := Finset.univ.image eV
  have hs : s.card = n := by
    dsimp [s]
    rw [Finset.card_image_iff.mpr ?_]
    · simp
    · intro a _ b _ hab
      exact eV.injective hab
  have hsmaller : ∀ x ∈ s, L.rank x < L.rank v := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, hix⟩
    subst x
    change L.rank (e i).val < L.rank v
    exact (e i).property.2
  have hv : v ∈ commonNeighborClosure G hfree ⟨s, hs⟩ := by
    apply (mem_commonNeighborClosure_iff G hfree ⟨s, hs⟩ v).2
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, hix⟩
    subst x
    change G.Adj (e i).val v
    exact (e i).property.1.symm
  exact lt_irrefl _ (L.earlier_closed v s hs hsmaller v hv)

/-- Every backward-neighbour set of a common-neighbour-closed layering is
finite. -/
theorem finite_backNeighbors_of_commonNeighborLayering
    {n : Nat} {I : Type u} [LinearOrder I]
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I) (v : V) :
    Set.Finite {x : V | G.Adj v x ∧ L.rank x < L.rank v} :=
  finite_of_no_finiteBipartitePart_embedding _
    (no_embedding_backNeighbors_of_commonNeighborLayering G hfree L v)

/-- Quantitatively, every backward-neighbour set has cardinality below `n`. -/
theorem backNeighbors_toFinset_card_lt_of_commonNeighborLayering
    {n : Nat} {I : Type u} [LinearOrder I]
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I) (v : V) :
    (finite_backNeighbors_of_commonNeighborLayering G hfree L v).toFinset.card < n :=
  toFinset_card_lt_of_no_finiteBipartitePart_embedding _
    (no_embedding_backNeighbors_of_commonNeighborLayering G hfree L v)

/-- A finite common-neighbour closure layering turns `K_{n,n}`-freeness into
countable colourability as soon as every rank fibre is countably colourable. -/
theorem countablyColorable_of_commonNeighborLayering
    {n : Nat} {I : Type u} [LinearOrder I]
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I)
    (hfiber : ∀ i : I,
      CountablyColorable (G.induce {x : V | L.rank x = i})) :
    CountablyColorable G := by
  refine countablyColorable_of_finite_back_neighbors G L.rank (n - 1) ?_ ?_ hfiber
  · intro v
    exact finite_backNeighbors_of_commonNeighborLayering G hfree L v
  · intro v
    exact Nat.le_pred_of_lt
      (backNeighbors_toFinset_card_lt_of_commonNeighborLayering G hfree L v)

end SimpleGraph

end Erdos593

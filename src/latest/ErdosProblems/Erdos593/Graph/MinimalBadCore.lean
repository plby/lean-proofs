import ErdosProblems.Erdos593.Graph.CompleteBipartiteCopy
import ErdosProblems.Erdos593.Graph.CompleteBipartiteLayering
import ErdosProblems.Erdos593.Graph.CountableColoring
import ErdosProblems.Erdos593.Graph.FiniteClosureLayeringConstruction
import Mathlib.SetTheory.Cardinal.Order

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Minimal bad cores for the complete-bipartite graph lemma

This module packages the cardinal-minimal-counterexample reduction and closes
it using the singular-cardinal-safe finite-closure layering construction.
-/

namespace Erdos593

universe u

namespace SimpleGraph

variable {V : Type u}

/-- `KNNBadCard n κ` says that some graph of vertex cardinality `κ` is not
countably colourable and contains no (non-induced) copy of `K_{n,n}`.  The
witness carrier stays in the fixed universe, so cardinal minimisation below is
universe-local. -/
def KNNBadCard (n : Nat) (kappa : Cardinal.{u}) : Prop :=
  Exists fun (W : Type u) => Exists fun (H : _root_.SimpleGraph W) =>
    Cardinal.mk W = kappa ∧
      ¬ CountablyColorable H ∧
        IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) H)

/-- Select the least vertex cardinality of a `K_{n,n}`-free graph that is not
countably colourable.  This is cardinal minimisation, not minimisation under
induced-subgraph inclusion. -/
theorem exists_minimalKNNBadCard {n : Nat}
    (h : Exists fun kappa : Cardinal.{u} => KNNBadCard n kappa) :
    Exists fun kappa : Cardinal.{u} =>
      KNNBadCard n kappa ∧
        ((kappa' : Cardinal.{u}) -> kappa' < kappa -> ¬ KNNBadCard n kappa') := by
  rcases h with ⟨kappa0, hkappa0⟩
  let B : Set Cardinal.{u} := fun kappa => KNNBadCard n kappa
  have hB : B.Nonempty := ⟨kappa0, hkappa0⟩
  let kappa := Cardinal.lt_wf.min B hB
  refine ⟨kappa, Cardinal.lt_wf.min_mem B hB, ?_⟩
  intro kappa' hkappa' hbad
  exact (Cardinal.lt_wf.not_lt_min B hbad) hkappa'

/-- `K_{n,n}`-freeness is inherited by induced subgraphs. -/
theorem kNNFree_induce {n : Nat} (G : _root_.SimpleGraph V)
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (s : Set V) :
    IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) (G.induce s)) := by
  constructor
  intro f
  exact (isEmpty_iff.mp hfree) ((_root_.SimpleGraph.Copy.induce G s).comp f)

/-- Every induced subgraph on a strictly smaller carrier is countably
colourable.  This is the precise local consequence extracted from a
cardinal-minimal bad counterexample. -/
def LocallyCountablyColorableBelow (G : _root_.SimpleGraph V) : Prop :=
  (s : Set V) -> Cardinal.mk s < Cardinal.mk V -> CountablyColorable (G.induce s)

/-- Cardinal minimality of a bad graph makes every strictly smaller induced
subgraph countably colourable. -/
theorem locallyCountablyColorableBelow_of_minimalBad
    {n : Nat} {kappa : Cardinal.{u}} (G : _root_.SimpleGraph V)
    (hcard : Cardinal.mk V = kappa)
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (hmin : (kappa' : Cardinal.{u}) -> kappa' < kappa -> ¬ KNNBadCard n kappa') :
    LocallyCountablyColorableBelow G := by
  classical
  intro s hs
  by_contra hscolor
  apply hmin (Cardinal.mk s) (by simpa [hcard] using! hs)
  exact ⟨s, G.induce s, rfl, hscolor, kNNFree_induce G hfree s⟩

/-- A graph on a countable carrier has a proper colouring by natural numbers. -/
theorem countablyColorable_of_countable (G : _root_.SimpleGraph V) [Countable V] :
    CountablyColorable G := by
  letI : Encodable V := Encodable.ofCountable V
  apply Nonempty.intro
  apply _root_.SimpleGraph.Coloring.mk Encodable.encode
  intro x y hxy heq
  exact G.ne_of_adj hxy (Encodable.encode_injective heq)

/-- A non-countably-colourable graph has an uncountable vertex carrier. -/
theorem aleph0_lt_mk_of_not_countablyColorable
    (G : _root_.SimpleGraph V) (hG : ¬ CountablyColorable G) :
    Cardinal.aleph0 < Cardinal.mk V := by
  apply lt_of_not_ge
  intro hle
  have hcount : Countable V := Cardinal.mk_le_aleph0_iff.mp hle
  exact hG (countablyColorable_of_countable G)

/-- A finite common-neighbour closure layering becomes a global countable
colouring as soon as its individual rank fibres are strictly smaller than the
ambient carrier and hence locally countably colourable. -/
theorem countablyColorable_of_commonNeighborLayering_of_localSmall
    (G : _root_.SimpleGraph V) {n : Nat} {I : Type u} [LinearOrder I]
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I)
    (hsmall : LocallyCountablyColorableBelow G) :
    CountablyColorable G := by
  apply countablyColorable_of_commonNeighborLayering G hfree L
  intro i
  exact hsmall {x : V | L.rank x = i} (L.fiber_lt i)

/-- A cardinal-minimal non-countably-colourable `K_{n,n}`-free graph admits
no finite common-neighbour closure layering with small rank fibres.  Thus the
remaining positive-atom task is exactly the singular-cardinal-safe
construction of such a layering. -/
theorem false_of_commonNeighborLayering_of_minimalBad
    {n : Nat} {kappa : Cardinal.{u}} (G : _root_.SimpleGraph V)
    (hcard : Cardinal.mk V = kappa)
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G))
    (hbad : ¬ CountablyColorable G)
    (hmin : (kappa' : Cardinal.{u}) -> kappa' < kappa -> ¬ KNNBadCard n kappa')
    {I : Type u} [LinearOrder I]
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I) : False := by
  apply hbad
  apply countablyColorable_of_commonNeighborLayering_of_localSmall G hfree L
  exact locallyCountablyColorableBelow_of_minimalBad G hcard hfree hmin

/-- Every `K_{n,n}`-free graph is countably colourable when `n` is positive.

The proof minimizes a hypothetical bad cardinal, builds the finite common
neighbour closure layering at that cardinal without a regularity assumption,
and colours each strictly smaller rank fibre by cardinal minimality. -/
theorem countablyColorable_of_no_completeBipartiteNNCopy
    {n : Nat} (G : _root_.SimpleGraph V) (hn : 0 < n)
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (completeBipartiteNN.{u} n) G)) :
    CountablyColorable G := by
  classical
  by_contra hbad
  obtain ⟨κ, hκbad, hmin⟩ :=
    exists_minimalKNNBadCard (n := n)
      ⟨Cardinal.mk V, ⟨V, G, rfl, hbad, hfree⟩⟩
  rcases hκbad with ⟨W, H, hcard, hHbad, hHfree⟩
  let L : FiniteClosureLayering n (commonNeighborClosure H hHfree)
      (Cardinal.mk W).ord.ToType :=
    (FiniteClosureLayeringConstruction.exists_finiteClosureLayering_of_uncountable
      (commonNeighborClosure H hHfree)
      (aleph0_lt_mk_of_not_countablyColorable H hHbad) hn).some
  exact false_of_commonNeighborLayering_of_minimalBad H hcard hHfree hHbad hmin L

/-- There is no bad cardinal witness for any positive balanced complete
bipartite graph. -/
theorem not_KNNBadCard_of_pos
    (n : Nat) (hn : 0 < n) (κ : Cardinal.{u}) :
    ¬ KNNBadCard n κ := by
  rintro ⟨W, H, hcard, hbad, hfree⟩
  exact hbad (countablyColorable_of_no_completeBipartiteNNCopy H hn hfree)

end SimpleGraph

end Erdos593

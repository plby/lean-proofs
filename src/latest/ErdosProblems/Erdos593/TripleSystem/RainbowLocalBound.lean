import ErdosProblems.Erdos593.Graph.RainbowBipartite
import ErdosProblems.Erdos593.TripleSystem.HighPairGraph
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Local rainbow bounds from low codegree

This module packages the finite argument used in the low-codegree crossing
graph branch.  If a color occurs at least `t` times in one row or column of a
witnessed bipartite grid, the corresponding base/apex pair has `t` distinct
third-vertex completions and is therefore a high pair.
-/

namespace Erdos593

universe u v

namespace TripleSystem

/-- A bipartite array of third-vertex witnesses is locally `t`-bounded when
no base/apex pair occurring in a row or column is high at threshold `t`.

The strict inequality in `RainbowBipartite.LocallyBounded t` matches the
usual statement that each color occurs at most `t - 1` times at a fixed
vertex. -/
theorem locallyBounded_of_not_highPair_on_cells
    {W : Type u} {D : Type v} {H : TripleSystem W D}
    {q t : Nat} (ht : 0 < t)
    (left right : Fin q ↪ W) (apex : Fin q → Fin q → W)
    (cell : ∀ i j, ThirdVertexWitness H (left i) (right j) (apex i j))
    (hleft : ∀ i j, ¬ HighPair H t (left i) (apex i j))
    (hright : ∀ i j, ¬ HighPair H t (right j) (apex i j)) :
    RainbowBipartite.LocallyBounded t apex := by
  classical
  constructor
  · intro i a
    by_contra hlt
    have hle : t ≤ Nat.card {j : Fin q // apex i j = a} :=
      Nat.le_of_not_gt hlt
    let S := {j : Fin q // apex i j = a}
    let : Fintype S := Fintype.ofFinite S
    have hle' : Fintype.card (Fin t) ≤ Fintype.card S := by
      simpa [S, Nat.card_eq_fintype_card] using! hle
    obtain ⟨select⟩ := Function.Embedding.nonempty_of_card_le hle'
    let third : Fin t ↪ W :=
      select.trans ((Function.Embedding.subtype _).trans right)
    have hcell : ∀ k, ThirdVertexWitness H (left i) a (third k) := by
      intro k
      change ThirdVertexWitness H (left i) a (right (select k).1)
      simpa [(select k).property] using! (cell i (select k).1).rotate
    let p : PairCodegreeWitness H (left i) a t :=
      PairCodegreeWitness.ofThirdVertexWitnesses third hcell
    let k0 : Fin t := ⟨0, ht⟩
    have hhigh : HighPair H t (left i) a := highPair_of_witness p ht
    exact hleft i (select k0).1 (by
      simpa [(select k0).property] using! hhigh)
  · intro j a
    by_contra hlt
    have hle : t ≤ Nat.card {i : Fin q // apex i j = a} :=
      Nat.le_of_not_gt hlt
    let S := {i : Fin q // apex i j = a}
    let : Fintype S := Fintype.ofFinite S
    have hle' : Fintype.card (Fin t) ≤ Fintype.card S := by
      simpa [S, Nat.card_eq_fintype_card] using! hle
    obtain ⟨select⟩ := Function.Embedding.nonempty_of_card_le hle'
    let third : Fin t ↪ W :=
      select.trans ((Function.Embedding.subtype _).trans left)
    have hcell : ∀ k, ThirdVertexWitness H (right j) a (third k) := by
      intro k
      change ThirdVertexWitness H (right j) a (left (select k).1)
      simpa [(select k).property] using! (cell (select k).1 j).swap.rotate
    let p : PairCodegreeWitness H (right j) a t :=
      PairCodegreeWitness.ofThirdVertexWitnesses third hcell
    let k0 : Fin t := ⟨0, ht⟩
    have hhigh : HighPair H t (right j) a := highPair_of_witness p ht
    exact hright (select k0).1 j (by
      simpa [(select k0).property] using! hhigh)

end TripleSystem

end Erdos593

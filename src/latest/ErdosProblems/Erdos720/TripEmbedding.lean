import ErdosProblems.Erdos720.PartiteCycle

namespace Erdos720

open Finset

/-- Embed the canonical tripartite type into three pairwise disjoint finite
vertex sets of the corresponding sizes. -/
def tripartiteEmbedding {V : Type*} {m : ℕ} {L M W : Finset V}
    (eL : Fin (128 * m) ≃ L) (eM : Fin (128 * m) ≃ M)
    (eW : Fin (2 * m - 1) ≃ W)
    (hLM : Disjoint L M) (hLW : Disjoint L W) (hMW : Disjoint M W) :
    TripType m ↪ V where
  toFun
    | Sum.inl (Sum.inl x) => (eL x).1
    | Sum.inl (Sum.inr y) => (eM y).1
    | Sum.inr z => (eW z).1
  inj' := by
    intro x y hxy
    rcases x with (x | x) | x <;> rcases y with (y | y) | y
    · congr 2
      apply eL.injective
      exact Subtype.ext hxy
    · exfalso
      change (eL x).1 = (eM y).1 at hxy
      exact (Finset.disjoint_left.1 hLM (eL x).2) (hxy ▸ (eM y).2)
    · exfalso
      change (eL x).1 = (eW y).1 at hxy
      exact (Finset.disjoint_left.1 hLW (eL x).2) (hxy ▸ (eW y).2)
    · exfalso
      change (eM x).1 = (eL y).1 at hxy
      exact (Finset.disjoint_left.1 hLM (eL y).2) (hxy.symm ▸ (eM x).2)
    · congr 2
      apply eM.injective
      exact Subtype.ext hxy
    · exfalso
      change (eM x).1 = (eW y).1 at hxy
      exact (Finset.disjoint_left.1 hMW (eM x).2) (hxy ▸ (eW y).2)
    · exfalso
      change (eW x).1 = (eL y).1 at hxy
      exact (Finset.disjoint_left.1 hLW (eL y).2) (hxy.symm ▸ (eW x).2)
    · exfalso
      change (eW x).1 = (eM y).1 at hxy
      exact (Finset.disjoint_left.1 hMW (eM y).2) (hxy.symm ▸ (eW x).2)
    · congr 2
      apply eW.injective
      exact Subtype.ext hxy

@[simp] lemma tripartiteEmbedding_left {V : Type*} {m : ℕ} {L M W : Finset V}
    (eL : Fin (128 * m) ≃ L) (eM : Fin (128 * m) ≃ M)
    (eW : Fin (2 * m - 1) ≃ W) (hLM : Disjoint L M)
    (hLW : Disjoint L W) (hMW : Disjoint M W) (x : Fin (128 * m)) :
    tripartiteEmbedding eL eM eW hLM hLW hMW (Sum.inl (Sum.inl x)) = (eL x).1 := rfl

@[simp] lemma tripartiteEmbedding_right {V : Type*} {m : ℕ} {L M W : Finset V}
    (eL : Fin (128 * m) ≃ L) (eM : Fin (128 * m) ≃ M)
    (eW : Fin (2 * m - 1) ≃ W) (hLM : Disjoint L M)
    (hLW : Disjoint L W) (hMW : Disjoint M W) (x : Fin (128 * m)) :
    tripartiteEmbedding eL eM eW hLM hLW hMW (Sum.inl (Sum.inr x)) = (eM x).1 := rfl

@[simp] lemma tripartiteEmbedding_external {V : Type*} {m : ℕ} {L M W : Finset V}
    (eL : Fin (128 * m) ≃ L) (eM : Fin (128 * m) ≃ M)
    (eW : Fin (2 * m - 1) ≃ W) (hLM : Disjoint L M)
    (hLW : Disjoint L W) (hMW : Disjoint M W) (x : Fin (2 * m - 1)) :
    tripartiteEmbedding eL eM eW hLM hLW hMW (Sum.inr x) = (eW x).1 := rfl

end Erdos720

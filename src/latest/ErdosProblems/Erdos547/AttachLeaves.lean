import ErdosProblems.Erdos547.DegreeExtraction

/-!
# Attaching a finite family of leaves preserves trees
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {U L : Type*}

def attachLeaves (T : SimpleGraph U) (parent : L → U) : SimpleGraph (U ⊕ L) where
  Adj x y := match x, y with
    | .inl u, .inl v => T.Adj u v
    | .inl u, .inr l => u = parent l
    | .inr l, .inl u => parent l = u
    | .inr _, .inr _ => False
  symm := by
    constructor
    intro x y h
    cases x <;> cases y
    · exact h.symm
    · exact h.symm
    · exact h.symm
    · exact h
  loopless := by
    constructor
    intro x h
    cases x
    · exact h.ne rfl
    · exact h

instance attachLeaves_decidableAdj (T : SimpleGraph U) [DecidableRel T.Adj]
    [DecidableEq U] (parent : L → U) : DecidableRel (attachLeaves T parent).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [attachLeaves] <;> infer_instance

def attachLeavesOldHom (T : SimpleGraph U) (parent : L → U) : T →g attachLeaves T parent where
  toFun := Sum.inl
  map_rel' := fun h ↦ h

def attachLeavesOldCopy (T : SimpleGraph U) (parent : L → U) : T.Copy (attachLeaves T parent) :=
  ⟨attachLeavesOldHom T parent, Sum.inl_injective⟩

theorem attachLeaves_connected (T : SimpleGraph U) (parent : L → U) (hT : T.Connected) :
    (attachLeaves T parent).Connected := by
  obtain ⟨r⟩ := hT.nonempty
  let : Nonempty (U ⊕ L) := ⟨Sum.inl r⟩
  have hreach (x : U ⊕ L) : (attachLeaves T parent).Reachable x (Sum.inl r) := by
    cases x with
    | inl u => exact (hT u r).map (attachLeavesOldHom T parent)
    | inr l =>
        have hadj : (attachLeaves T parent).Adj (Sum.inr l) (Sum.inl (parent l)) := rfl
        exact hadj.reachable.trans ((hT (parent l) r).map (attachLeavesOldHom T parent))
  exact ⟨fun x y ↦ (hreach x).trans (hreach y).symm⟩

theorem degree_eq_sum_adj_indicator {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : G.degree v = ∑ u : V, (if G.Adj v u then 1 else 0 : ℕ) := by
  rw [← degreeIn_univ]
  simp [degreeIn]

open scoped Classical in
theorem attachLeaves_degree_inl [Fintype U] [Fintype L] (T : SimpleGraph U)
    [DecidableRel T.Adj] (parent : L → U) (u : U) :
    (attachLeaves T parent).degree (Sum.inl u) = T.degree u +
      ((Finset.univ : Finset L).filter (fun l ↦ parent l = u)).card := by
  classical
  rw [degree_eq_sum_adj_indicator, Fintype.sum_sum_type]
  change (∑ v : U, if T.Adj u v then 1 else 0) +
    (∑ l : L, if u = parent l then 1 else 0) = _
  rw [← degree_eq_sum_adj_indicator]
  simp [eq_comm]

open scoped Classical in
theorem attachLeaves_degree_inr [Fintype U] [Fintype L] (T : SimpleGraph U)
    [DecidableRel T.Adj] (parent : L → U) (l : L) :
    (attachLeaves T parent).degree (Sum.inr l) = 1 := by
  classical
  rw [degree_eq_sum_adj_indicator, Fintype.sum_sum_type]
  change (∑ u : U, if parent l = u then 1 else 0) + (∑ _ : L, if False then 1 else 0) = 1
  simp

theorem attachLeaves_isTree [Fintype U] [Fintype L] (T : SimpleGraph U)
    [DecidableRel T.Adj] (parent : L → U) (hT : T.IsTree) :
    (attachLeaves T parent).IsTree := by
  classical
  let G := attachLeaves T parent
  have hfibres : (∑ u : U, ((Finset.univ : Finset L).filter (fun l ↦ parent l = u)).card) =
      Fintype.card L := by
    calc
      _ = ∑ u : U, ∑ l : L, (if parent l = u then 1 else 0 : ℕ) := by simp
      _ = ∑ l : L, ∑ u : U, (if parent l = u then 1 else 0 : ℕ) := Finset.sum_comm
      _ = _ := by simp
  have hsum : ∑ x : U ⊕ L, G.degree x = (∑ u : U, T.degree u) + 2 * Fintype.card L := by
    rw [Fintype.sum_sum_type]
    simp only [G, attachLeaves_degree_inl, attachLeaves_degree_inr,
      Finset.sum_add_distrib, hfibres, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one]
    omega
  rw [G.sum_degrees_eq_twice_card_edges, T.sum_degrees_eq_twice_card_edges] at hsum
  have he := hT.card_edgeFinset
  have hcard : G.edgeFinset.card + 1 = Fintype.card (U ⊕ L) := by
    rw [Fintype.card_sum]
    omega
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨attachLeaves_connected T parent hT.connected, ?_⟩
  rw [Nat.card_eq_fintype_card, ← G.edgeFinset_card, Nat.card_eq_fintype_card]
  exact hcard

end Erdos547

#print axioms Erdos547.attachLeaves_isTree

import Mathlib

namespace Erdos113BipartiteGraph

abbrev LiveLeft {U V : Type*} [Fintype U] [Fintype V]
    (E : Finset (U × V)) := {u : U // ∃ v, (u, v) ∈ E}

abbrev LiveRight {U V : Type*} [Fintype U] [Fintype V]
    (E : Finset (U × V)) := {v : V // ∃ u, (u, v) ∈ E}

def retainedGraph {U V : Type*} [Fintype U] [Fintype V]
    (E : Finset (U × V)) : SimpleGraph (LiveLeft E ⊕ LiveRight E) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inr v => (u.1, v.1) ∈ E
    | Sum.inr v, Sum.inl u => (u.1, v.1) ∈ E
    | _, _ => False
  symm := ⟨by
    rintro (u | v) (u' | v') h <;> simp_all⟩
  loopless := ⟨by
    rintro (u | v) h <;> simp_all⟩

instance {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V)) :
    DecidableRel (retainedGraph E).Adj := fun x y ↦ by
  rcases x with u | v <;> rcases y with u' | v' <;>
    simp only [retainedGraph] <;> infer_instance

noncomputable def leftFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] (E : Finset (U × V)) (u : U) : Finset (U × V) :=
  E.filter fun p ↦ p.1 = u

noncomputable def rightFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (E : Finset (U × V)) (v : V) : Finset (U × V) :=
  E.filter fun p ↦ p.2 = v

@[simp] lemma mem_leftFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] (E : Finset (U × V)) (u : U) (p : U × V) :
    p ∈ leftFiber E u ↔ p ∈ E ∧ p.1 = u := by
  simp [leftFiber]

@[simp] lemma mem_rightFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (E : Finset (U × V)) (v : V) (p : U × V) :
    p ∈ rightFiber E v ↔ p ∈ E ∧ p.2 = v := by
  simp [rightFiber]

/-- Counting a finite bipartite edge set by its left endpoint. -/
lemma card_eq_sum_leftFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] (E : Finset (U × V)) :
    E.card = ∑ u : U, (leftFiber E u).card := by
  classical
  simpa [leftFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := E) (t := (Finset.univ : Finset U)) (f := Prod.fst)
      (by
        intro p _hp
        exact Finset.mem_univ p.1 :
        (E : Set (U × V)).MapsTo Prod.fst
          (↑(Finset.univ : Finset U) : Set U)))

/-- Counting a finite bipartite edge set by its right endpoint. -/
lemma card_eq_sum_rightFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (E : Finset (U × V)) :
    E.card = ∑ v : V, (rightFiber E v).card := by
  classical
  simpa [rightFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := E) (t := (Finset.univ : Finset V)) (f := Prod.snd)
      (by
        intro p _hp
        exact Finset.mem_univ p.2 :
        (E : Set (U × V)).MapsTo Prod.snd
          (↑(Finset.univ : Finset V) : Set V)))

lemma card_le_card_mul_of_leftFiber_le {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] (E : Finset (U × V)) (D : ℕ)
    (h : ∀ u, (leftFiber E u).card ≤ D) :
    E.card ≤ Fintype.card U * D := by
  rw [card_eq_sum_leftFiber]
  calc
    ∑ u : U, (leftFiber E u).card ≤ ∑ _u : U, D :=
      Finset.sum_le_sum (fun u _ ↦ h u)
    _ = Fintype.card U * D := by simp

lemma card_le_card_mul_of_rightFiber_le {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq V] (E : Finset (U × V)) (D : ℕ)
    (h : ∀ v, (rightFiber E v).card ≤ D) :
    E.card ≤ Fintype.card V * D := by
  rw [card_eq_sum_rightFiber]
  calc
    ∑ v : V, (rightFiber E v).card ≤ ∑ _v : V, D :=
      Finset.sum_le_sum (fun v _ ↦ h v)
    _ = Fintype.card V * D := by simp

noncomputable def leftNeighborEquivFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V)) (u : LiveLeft E) :
    (retainedGraph E).neighborSet (Sum.inl u) ≃ ↑(leftFiber E u.1) where
  toFun y := by
    rcases y with ⟨y, hy⟩
    rcases y with u' | v
    · exact False.elim hy
    · exact ⟨(u.1, v.1), by
        rw [mem_leftFiber]
        exact ⟨hy, rfl⟩⟩
  invFun p := by
    have hp := (mem_leftFiber E u.1 p.1).mp p.2
    let v : LiveRight E := ⟨p.1.2, ⟨p.1.1, hp.1⟩⟩
    refine ⟨Sum.inr v, ?_⟩
    change (u.1, p.1.2) ∈ E
    convert hp.1 using 1
    apply Prod.ext
    · exact hp.2.symm
    · rfl
  left_inv y := by
    rcases y with ⟨y, hy⟩
    rcases y with u' | v
    · exact False.elim hy
    · apply Subtype.ext
      rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact ((mem_leftFiber E u.1 p.1).mp p.2).2.symm
    · rfl

noncomputable def rightNeighborEquivFiber {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V)) (v : LiveRight E) :
    (retainedGraph E).neighborSet (Sum.inr v) ≃ ↑(rightFiber E v.1) where
  toFun y := by
    rcases y with ⟨y, hy⟩
    rcases y with u | v'
    · exact ⟨(u.1, v.1), by
        rw [mem_rightFiber]
        exact ⟨hy, rfl⟩⟩
    · exact False.elim hy
  invFun p := by
    have hp := (mem_rightFiber E v.1 p.1).mp p.2
    let u : LiveLeft E := ⟨p.1.1, ⟨p.1.2, hp.1⟩⟩
    refine ⟨Sum.inl u, ?_⟩
    change (p.1.1, v.1) ∈ E
    convert hp.1 using 1
    apply Prod.ext
    · rfl
    · exact hp.2.symm
  left_inv y := by
    rcases y with ⟨y, hy⟩
    rcases y with u | v'
    · apply Subtype.ext
      rfl
    · exact False.elim hy
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((mem_rightFiber E v.1 p.1).mp p.2).2.symm

lemma degree_inl {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V)) (u : LiveLeft E) :
    (retainedGraph E).degree (Sum.inl u) = (leftFiber E u.1).card := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  simpa only [Fintype.card_coe] using Fintype.card_congr (leftNeighborEquivFiber E u)

lemma degree_inr {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V)) (v : LiveRight E) :
    (retainedGraph E).degree (Sum.inr v) = (rightFiber E v.1).card := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  simpa only [Fintype.card_coe] using Fintype.card_congr (rightNeighborEquivFiber E v)

lemma cross {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (E : Finset (U × V))
    {x y : LiveLeft E ⊕ LiveRight E} (h : (retainedGraph E).Adj x y) :
    Sum.elim (fun _ ↦ false) (fun _ ↦ true) y =
      !Sum.elim (fun _ ↦ false) (fun _ ↦ true) x := by
  rcases x with u | v <;> rcases y with u' | v' <;> simp_all [retainedGraph]

lemma nonempty_of_nonempty {U V : Type*} [Fintype U] [Fintype V]
    (E : Finset (U × V)) (hE : E.Nonempty) :
    Nonempty (LiveLeft E ⊕ LiveRight E) := by
  obtain ⟨⟨u, v⟩, huv⟩ := hE
  exact ⟨Sum.inl ⟨u, ⟨v, huv⟩⟩⟩

end Erdos113BipartiteGraph

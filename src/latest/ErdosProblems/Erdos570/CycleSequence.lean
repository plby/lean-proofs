/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Producing cycle copies from injective cyclic sequences
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

/-- Adjacent vertices in `cycleGraph n` are either consecutive in the linear
order on `Fin n`, or are the two wrap-around endpoints. -/
theorem cycleGraph_adj_cases {n : ℕ} {u v : Fin n}
    (huv : (SimpleGraph.cycleGraph n).Adj u v) :
    u.val + 1 = v.val ∨ v.val + 1 = u.val ∨
      (u.val = 0 ∧ v.val + 1 = n) ∨
      (v.val = 0 ∧ u.val + 1 = n) := by
  rw [SimpleGraph.cycleGraph_adj'] at huv
  rcases huv with huv | huv
  · have hsub := Fin.intCast_val_sub_eq_sub_add_ite u v
    rw [huv] at hsub
    split_ifs at hsub <;> omega
  · have hsub := Fin.intCast_val_sub_eq_sub_add_ite v u
    rw [huv] at hsub
    split_ifs at hsub <;> omega

/-- An injective cyclically adjacent sequence gives an ordinary copy of the
canonical cycle graph.  The hypotheses separate linear consecutive pairs
from the wrap-around pair, which is convenient for explicit constructions. -/
theorem cycleGraph_isContained_of_sequence {V : Type*} {G : SimpleGraph V}
    {n : ℕ} (f : Fin n → V) (hf : Function.Injective f)
    (hlinear : ∀ u v : Fin n, u.val + 1 = v.val → G.Adj (f u) (f v))
    (hwrap : ∀ u v : Fin n, u.val = 0 → v.val + 1 = n →
      G.Adj (f u) (f v)) :
    SimpleGraph.cycleGraph n ⊑ G := by
  let hom : SimpleGraph.cycleGraph n →g G :=
    { toFun := f
      map_rel' := by
        intro u v huv
        rcases cycleGraph_adj_cases huv with h | h | h | h
        · exact hlinear u v h
        · exact (hlinear v u h).symm
        · exact hwrap u v h.1 h.2
        · exact (hwrap v u h.1 h.2).symm }
  exact ⟨hom.toCopy hf⟩

/-- A common root, two connector vertices, and an injective path segment form
the cycle
`x - a - p 0 - ⋯ - p (q+1) - b - x`.

This deliberately records all distinctness hypotheses explicitly.  It is the
indexing lemma used when two different witnesses into a second neighborhood
close a long path segment to a cycle. -/
theorem cycleGraph_add_five_isContained_of_path_connectors
    {V : Type*} {G : SimpleGraph V} {q : ℕ}
    (x a b : V) (p : Fin (q + 2) → V)
    (hp : Function.Injective p)
    (hbp : b ∉ Set.range p) (hap : a ∉ Set.range p)
    (hab : a ≠ b) (hxp : x ∉ Set.range p) (hxa : x ≠ a) (hxb : x ≠ b)
    (hxa_adj : G.Adj x a) (hap_adj : G.Adj a (p 0))
    (hp_adj : ∀ i j : Fin (q + 2), i.val + 1 = j.val → G.Adj (p i) (p j))
    (hpb_adj : G.Adj (p (Fin.last (q + 1))) b) (hbx_adj : G.Adj b x) :
    SimpleGraph.cycleGraph (q + 5) ⊑ G := by
  let pb : Fin (q + 3) → V := Fin.snoc p b
  have hpb : Function.Injective pb :=
    Fin.snoc_injective_of_injective hp hbp
  have ha_pb : a ∉ Set.range pb := by
    change a ∉ Set.range (Fin.snoc p b)
    rw [Fin.range_snoc]
    simpa [hab] using hap
  let apb : Fin (q + 4) → V := Fin.cons a pb
  have hapb : Function.Injective apb :=
    Fin.cons_injective_of_injective ha_pb hpb
  have hx_apb : x ∉ Set.range apb := by
    change x ∉ Set.range (Fin.cons a (Fin.snoc p b))
    rw [Fin.range_cons, Fin.range_snoc]
    simpa [hxa, hxb] using hxp
  let f : Fin (q + 5) → V := Fin.cons x apb
  have hf : Function.Injective f :=
    Fin.cons_injective_of_injective hx_apb hapb
  have hpb_linear : ∀ i j : Fin (q + 3), i.val + 1 = j.val →
      G.Adj (pb i) (pb j) := by
    intro i j hij
    by_cases hj : j.val < q + 2
    · let i' : Fin (q + 2) := ⟨i.val, by omega⟩
      let j' : Fin (q + 2) := ⟨j.val, hj⟩
      have hi_eq : i = i'.castSucc := Fin.ext rfl
      have hj_eq : j = j'.castSucc := Fin.ext rfl
      rw [hi_eq, hj_eq]
      simpa [pb] using hp_adj i' j' (by omega)
    · have hjlast : j = Fin.last (q + 2) := Fin.ext (by simp; omega)
      have hilast : i = (Fin.last (q + 1)).castSucc := Fin.ext (by simp; omega)
      rw [hilast, hjlast]
      simpa [pb] using hpb_adj
  have hapb_linear : ∀ i j : Fin (q + 4), i.val + 1 = j.val →
      G.Adj (apb i) (apb j) := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => omega
        | succ j =>
            have hj0 : j = 0 := Fin.ext (by simp at hij ⊢; omega)
            subst j
            simpa [apb, pb] using hap_adj
    | succ i =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
            apply hpb_linear i j
            simp only [Fin.val_succ] at hij
            omega
  apply cycleGraph_isContained_of_sequence f hf
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => omega
        | succ j =>
            have hj0 : j = 0 := Fin.ext (by simp at hij ⊢; omega)
            subst j
            simpa [f, apb] using hxa_adj
    | succ i =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
            apply hapb_linear i j
            simp only [Fin.val_succ] at hij
            omega
  · intro i j hi hj
    have hi0 : i = 0 := Fin.ext hi
    have hjlast : j = Fin.last (q + 4) := Fin.ext (by simp; omega)
    subst i
    subst j
    simpa [f, apb, pb] using hbx_adj.symm

/-- An injective path whose two endpoints are adjacent to a new vertex closes
to a cycle.  Unlike a neighborhood lemma, no adjacency from the new vertex
to the internal path vertices is required. -/
theorem cycleGraph_succ_isContained_of_path_endpoints
    {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (x : V) (p : Fin (n + 1) → V) (hp : Function.Injective p)
    (hxp : x ∉ Set.range p)
    (hp_adj : ∀ i j : Fin (n + 1), i.val + 1 = j.val → G.Adj (p i) (p j))
    (hxfirst : G.Adj x (p 0))
    (hxlast : G.Adj x (p (Fin.last n))) :
    SimpleGraph.cycleGraph (n + 2) ⊑ G := by
  let f : Fin (n + 2) → V := Fin.cons x p
  have hf : Function.Injective f :=
    Fin.cons_injective_of_injective hxp hp
  apply cycleGraph_isContained_of_sequence f hf
  · intro i j hij
    induction i using Fin.cases with
    | zero =>
        induction j using Fin.cases with
        | zero => omega
        | succ j =>
            have hj0 : j = 0 := Fin.ext (by simp at hij ⊢; omega)
            subst j
            simpa [f] using hxfirst
    | succ i =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
            apply hp_adj i j
            simp only [Fin.val_succ] at hij
            omega
  · intro i j hi hj
    have hi0 : i = 0 := Fin.ext hi
    have hjlast : j = Fin.last (n + 1) := Fin.ext (by simp; omega)
    subst i
    subst j
    simpa [f] using hxlast

/-- Prepending one vertex to a nonempty linearly adjacent finite sequence
preserves adjacency of consecutive entries. -/
theorem cons_sequence_adj
    {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (x : V) (p : Fin (n + 1) → V) (hx : G.Adj x (p 0))
    (hp : ∀ i j : Fin (n + 1), i.val + 1 = j.val → G.Adj (p i) (p j)) :
    ∀ i j : Fin (n + 2), i.val + 1 = j.val →
      G.Adj ((Fin.cons x p : Fin (n + 2) → V) i)
        ((Fin.cons x p : Fin (n + 2) → V) j) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => omega
      | succ j =>
          have hj0 : j = 0 := Fin.ext (by simp at hij ⊢; omega)
          subst j
          simpa using hx
  | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
          apply hp i j
          simp only [Fin.val_succ] at hij
          omega

end Erdos570

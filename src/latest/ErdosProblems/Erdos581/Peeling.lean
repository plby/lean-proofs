import ErdosProblems.Erdos581.StableCut

/-!
# Erdős 581: the low-degree peeling dichotomy

This file packages the deterministic part of the lower-bound argument.  For
a positive integer `D`, either a graph has a nonempty induced subgraph of
minimum degree at least `D`, or the degree square-root sum is at least
`|E| / sqrt D`.  The proof is the usual vertex peeling, expressed as strong
induction on the remaining finite vertex set.
-/

open Finset
open scoped BigOperators

namespace Erdos581

universe u

/-- Degree of a vertex into a finite set. -/
def degreeIn {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (S.filter fun w ↦ G.Adj v w).card

theorem degree_induce_finset {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (x : S) :
    (G.induce (S : Set V)).degree x = degreeIn G S x := by
  classical
  unfold SimpleGraph.degree SimpleGraph.neighborFinset degreeIn
  rw [Set.toFinset_card, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact
    { toFun := fun y ↦ ⟨y.1.1, Finset.mem_filter.mpr ⟨y.1.2, y.2⟩⟩
      invFun := fun y ↦
        ⟨⟨y.1, (Finset.mem_filter.mp y.2).1⟩, (Finset.mem_filter.mp y.2).2⟩
      left_inv := fun y ↦ by ext; rfl
      right_inv := fun y ↦ by ext; rfl }

private noncomputable def eraseInduceIso {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {x : V} (hx : x ∈ S) :
    (G.induce (S : Set V)).induce ({(⟨x, hx⟩ : S)}ᶜ) ≃g
      G.induce ((S.erase x : Finset V) : Set V) where
  toEquiv :=
    { toFun := fun y ↦ ⟨y.1.1, by
        have hyS : y.1.1 ∈ S := y.1.2
        have hyx : y.1.1 ≠ x := by
          intro h
          apply y.2
          simpa [Set.mem_singleton_iff, Subtype.ext_iff] using h
        exact Finset.mem_erase.mpr ⟨hyx, hyS⟩⟩
      invFun := fun y ↦ ⟨⟨y.1, (Finset.mem_erase.mp y.2).2⟩, by
        have hyx : y.1 ≠ x := (Finset.mem_erase.mp y.2).1
        simpa [Set.mem_singleton_iff, Subtype.ext_iff] using hyx⟩
      left_inv := fun y ↦ by ext; rfl
      right_inv := fun y ↦ by ext; rfl }
  map_rel_iff' := by
    intro a b
    rfl

/-- Every nonempty induced set has a vertex of internal degree at most `d`. -/
private def IsDegenerateAtMost {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ x ∈ S, degreeIn G S x ≤ d

private theorem degreeIn_le_degree {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    degreeIn G S v ≤ G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card (by
    intro w hw
    have hw' := (Finset.mem_filter.mp hw).2
    simpa using hw')

private noncomputable def induceUnivIso {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    G.induce ((Finset.univ : Finset V) : Set V) ≃g G where
  toEquiv :=
    { toFun := fun v ↦ v.1
      invFun := fun v ↦ ⟨v, by simp⟩
      left_inv := fun v ↦ by ext; rfl
      right_inv := fun v ↦ rfl }
  map_rel_iff' := by intro a b; rfl

/-- The weighted peeling estimate on an arbitrary remaining vertex set. -/
private theorem induced_edges_div_sqrt_le_sum_sqrt_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : 0 < D)
    (hdeg : IsDegenerateAtMost G (D - 1)) (S : Finset V) :
    ((#(G.induce (S : Set V)).edgeFinset : ℕ) : ℝ) / Real.sqrt D ≤
      ∑ v ∈ S, Real.sqrt (G.degree v : ℝ) := by
  classical
  exact Finset.strongInduction
    (p := fun S : Finset V ↦
      ((#(G.induce (S : Set V)).edgeFinset : ℕ) : ℝ) / Real.sqrt D ≤
        ∑ v ∈ S, Real.sqrt (G.degree v : ℝ))
    (fun S ih ↦ by
      by_cases hS : S.Nonempty
      · obtain ⟨x, hxS, hxdeg⟩ := hdeg S hS
        let K := G.induce (S : Set V)
        let xs : S := ⟨x, hxS⟩
        have hdegree : K.degree xs ≤ D - 1 := by
          change (G.induce (S : Set V)).degree xs ≤ D - 1
          rw [degree_induce_finset]
          exact hxdeg
        have hdegree_lt : K.degree xs < D := by omega
        have hdel :
            #(K.induce ({xs}ᶜ : Set S)).edgeFinset =
              #K.edgeFinset - K.degree xs := by
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet]
        have hiso :
            #(K.induce ({xs}ᶜ : Set S)).edgeFinset =
              #(G.induce ((S.erase x : Finset V) : Set V)).edgeFinset := by
          exact (eraseInduceIso G S hxS).card_edgeFinset_eq
        have hrest := ih (S.erase x) (Finset.erase_ssubset hxS)
        have hdegree_edges : K.degree xs ≤ #K.edgeFinset :=
          K.degree_le_card_edgeFinset xs
        have hsplit :
            #K.edgeFinset =
              #(G.induce ((S.erase x : Finset V) : Set V)).edgeFinset + K.degree xs := by
          rw [← hiso, hdel, Nat.sub_add_cancel hdegree_edges]
        have hsqrtD : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hD)
        have hlocal :
            (K.degree xs : ℝ) / Real.sqrt D ≤
              Real.sqrt (G.degree x : ℝ) := by
          have hKD : (K.degree xs : ℝ) ≤ D := by exact_mod_cast hdegree_lt.le
          have hsqrtKD : Real.sqrt (K.degree xs : ℝ) ≤ Real.sqrt (D : ℝ) :=
            Real.sqrt_le_sqrt hKD
          have hsqK : Real.sqrt (K.degree xs : ℝ) ^ 2 = K.degree xs :=
            Real.sq_sqrt (by positivity)
          have hmul : (K.degree xs : ℝ) ≤
              Real.sqrt (K.degree xs : ℝ) * Real.sqrt (D : ℝ) := by
            nlinarith [Real.sqrt_nonneg (K.degree xs : ℝ)]
          have hdiv : (K.degree xs : ℝ) / Real.sqrt D ≤
              Real.sqrt (K.degree xs : ℝ) :=
            (div_le_iff₀ hsqrtD).2 (by simpa [mul_comm] using hmul)
          have hdegreeG : K.degree xs ≤ G.degree x := by
            rw [degree_induce_finset]
            exact degreeIn_le_degree G S x
          exact hdiv.trans (Real.sqrt_le_sqrt (by exact_mod_cast hdegreeG))
        have hrest' :
            ((#(G.induce ((S.erase x : Finset V) : Set V)).edgeFinset : ℕ) : ℝ) /
                Real.sqrt D ≤
              ∑ v ∈ S.erase x, Real.sqrt (G.degree v : ℝ) := hrest
        change ((#K.edgeFinset : ℕ) : ℝ) / Real.sqrt D ≤
          ∑ v ∈ S, Real.sqrt (G.degree v : ℝ)
        rw [hsplit, Nat.cast_add, add_div]
        rw [← Finset.sum_erase_add _ _ hxS]
        exact add_le_add hrest' hlocal
      · simp only [Finset.not_nonempty_iff_eq_empty] at hS
        subst S
        have hempty :
            (G.induce (((∅ : Finset V) : Set V))).edgeFinset = ∅ := by
          ext e
          induction e using Sym2.ind with
          | _ a b => simp
        rw [hempty]
        simp) S

/-- For a positive threshold `D`, either there is a nonempty induced
minimum-degree-`D` core, or the degree square-root sum pays for all edges at
rate `1 / sqrt D`. -/
theorem core_or_sum_sqrt_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : 0 < D) :
    (∃ S : Finset V, S.Nonempty ∧
      ∀ v ∈ S, D ≤ degreeIn G S v) ∨
    ((#G.edgeFinset : ℕ) : ℝ) / Real.sqrt D ≤
      ∑ v, Real.sqrt (G.degree v : ℝ) := by
  classical
  by_cases hcore : ∃ S : Finset V, S.Nonempty ∧
      ∀ v ∈ S, D ≤ degreeIn G S v
  · exact Or.inl hcore
  · right
    have hdeg : IsDegenerateAtMost G (D - 1) := by
      intro S hS
      push_neg at hcore
      obtain ⟨v, hvS, hv⟩ := hcore S hS
      exact ⟨v, hvS, by omega⟩
    have h := induced_edges_div_sqrt_le_sum_sqrt_degree G D hD hdeg Finset.univ
    rw [(induceUnivIso G).card_edgeFinset_eq] at h
    simpa using h

end Erdos581

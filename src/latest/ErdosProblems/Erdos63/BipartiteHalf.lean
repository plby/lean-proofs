/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# A bipartite subgraph containing at least half the edges

This file proves the finite simple-graph form of the elementary maximum-cut
lemma used as Proposition 2.4 in Liu--Montgomery.  The proof exposes a finite
graph as its finset of directed edges and adapts the Boolean-cut induction from
`ErdosProblems/Erdos846.lean`.
-/

namespace Erdos63

universe u

attribute [local instance] Classical.propDecidable

/-- A loopless finset of ordered pairs whose coordinates are below `n` has a
Boolean cut containing at least half of its pairs. -/
private lemma nat_bool_cut_half_ind (n : ℕ) (S : Finset (ℕ × ℕ))
    (h_ne : ∀ e ∈ S, e.1 ≠ e.2) (hV : ∀ e ∈ S, e.1 < n ∧ e.2 < n) :
    ∃ f : ℕ → Bool, S.card ≤ 2 * (S.filter fun e ↦ f e.1 ≠ f e.2).card := by
  induction n generalizing S with
  | zero =>
      refine ⟨fun _ ↦ true, ?_⟩
      have hS : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        exact Nat.not_lt_zero e.1 (hV e he).1
      simp [hS]
  | succ n ih =>
      let S' := S.filter fun e ↦ e.1 < n ∧ e.2 < n
      have hV' : ∀ e ∈ S', e.1 < n ∧ e.2 < n := by
        intro e he
        exact (Finset.mem_filter.mp he).2
      have h_ne' : ∀ e ∈ S', e.1 ≠ e.2 := by
        intro e he
        exact h_ne e (Finset.mem_filter.mp he).1
      obtain ⟨f', hf'⟩ := ih S' h_ne' hV'
      let S_n := S.filter fun e ↦ ¬(e.1 < n ∧ e.2 < n)
      have h_card : S.card = S'.card + S_n.card := by
        have h := Finset.card_filter_add_card_filter_not
          (s := S) (p := fun e : ℕ × ℕ ↦ e.1 < n ∧ e.2 < n)
        simpa [S', S_n] using h.symm
      have h_count_split (f : ℕ → Bool) :
          (S.filter fun e ↦ f e.1 ≠ f e.2).card =
            (S'.filter fun e ↦ f e.1 ≠ f e.2).card +
              (S_n.filter fun e ↦ f e.1 ≠ f e.2).card := by
        let p : ℕ × ℕ → Prop := fun e ↦ e.1 < n ∧ e.2 < n
        let q : ℕ × ℕ → Prop := fun e ↦ f e.1 ≠ f e.2
        have h := Finset.card_filter_add_card_filter_not (s := S.filter q) (p := p)
        have hA : (S.filter q).filter p = S'.filter q := by
          ext e
          simp [S', p, q, and_left_comm, and_assoc, and_comm]
        have hB : (S.filter q).filter (fun e ↦ ¬p e) = S_n.filter q := by
          ext e
          simp [S_n, p, q, and_assoc, and_comm]
        rw [← h, hA, hB]
      let f1 := fun x ↦ if x = n then true else f' x
      let f2 := fun x ↦ if x = n then false else f' x
      have h_f1_S' :
          (S'.filter fun e ↦ f1 e.1 ≠ f1 e.2).card =
            (S'.filter fun e ↦ f' e.1 ≠ f' e.2).card := by
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro e he
        simp [f1, Nat.ne_of_lt (hV' e he).1, Nat.ne_of_lt (hV' e he).2]
      have h_f2_S' :
          (S'.filter fun e ↦ f2 e.1 ≠ f2 e.2).card =
            (S'.filter fun e ↦ f' e.1 ≠ f' e.2).card := by
        apply congrArg Finset.card
        apply Finset.filter_congr
        intro e he
        simp [f2, Nat.ne_of_lt (hV' e he).1, Nat.ne_of_lt (hV' e he).2]
      have h_sum_Sn :
          (S_n.filter fun e ↦ f1 e.1 ≠ f1 e.2).card +
              (S_n.filter fun e ↦ f2 e.1 ≠ f2 e.2).card = S_n.card := by
        have hcomp :
            S_n.filter (fun e ↦ f2 e.1 ≠ f2 e.2) =
              S_n.filter (fun e ↦ ¬f1 e.1 ≠ f1 e.2) := by
          apply Finset.filter_congr
          intro e he
          have heS : e ∈ S := (Finset.mem_filter.mp he).1
          have hnot : ¬(e.1 < n ∧ e.2 < n) := (Finset.mem_filter.mp he).2
          have hv := hV e heS
          have hne := h_ne e heS
          have hcases : (e.1 = n ∧ e.2 < n) ∨ (e.1 < n ∧ e.2 = n) := by
            omega
          cases hcases with
          | inl h =>
              cases f' e.2 <;> simp [f1, f2, h.1, Nat.ne_of_lt h.2]
          | inr h =>
              cases f' e.1 <;> simp [f1, f2, Nat.ne_of_lt h.1, h.2]
        rw [hcomp]
        exact Finset.card_filter_add_card_filter_not
          (s := S_n) (p := fun e ↦ f1 e.1 ≠ f1 e.2)
      have h_max :
          S_n.card ≤ 2 * (S_n.filter fun e ↦ f1 e.1 ≠ f1 e.2).card ∨
            S_n.card ≤ 2 * (S_n.filter fun e ↦ f2 e.1 ≠ f2 e.2).card := by
        omega
      cases h_max with
      | inl h1 =>
          refine ⟨f1, ?_⟩
          have h_old :
              S'.card ≤ 2 * (S'.filter fun e ↦ f1 e.1 ≠ f1 e.2).card := by
            rwa [h_f1_S']
          rw [h_count_split f1, h_card]
          omega
      | inr h2 =>
          refine ⟨f2, ?_⟩
          have h_old :
              S'.card ≤ 2 * (S'.filter fun e ↦ f2 e.1 ≠ f2 e.2).card := by
            rwa [h_f2_S']
          rw [h_count_split f2, h_card]
          omega

/-- A finite loopless finset of ordered pairs has a Boolean cut containing
at least half of its pairs. -/
private lemma nat_bool_cut_half (S : Finset (ℕ × ℕ))
    (h_ne : ∀ e ∈ S, e.1 ≠ e.2) :
    ∃ f : ℕ → Bool, S.card ≤ 2 * (S.filter fun e ↦ f e.1 ≠ f e.2).card := by
  have h_bound : ∃ n, ∀ e ∈ S, e.1 < n ∧ e.2 < n := by
    refine ⟨S.sup (fun e ↦ max e.1 e.2) + 1, ?_⟩
    intro e he
    have hle : max e.1 e.2 ≤ S.sup (fun e ↦ max e.1 e.2) :=
      Finset.le_sup (f := fun e ↦ max e.1 e.2) he
    omega
  obtain ⟨n, hn⟩ := h_bound
  exact nat_bool_cut_half_ind n S h_ne hn

/-- Every finite simple graph has a spanning bipartite subgraph containing at
least half of its edges. -/
theorem exists_bipartite_subgraph_half {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ H : SimpleGraph V,
      H ≤ G ∧ H.IsBipartite ∧ G.edgeFinset.card ≤ 2 * H.edgeFinset.card := by
  classical
  let enc : V → ℕ := fun v ↦ (Fintype.equivFin V v : ℕ)
  have enc_injective : Function.Injective enc := by
    intro v w hvw
    apply (Fintype.equivFin V).injective
    exact Fin.ext hvw
  let pairEnc : V × V → ℕ × ℕ := fun e ↦ (enc e.1, enc e.2)
  have pairEnc_injective : Function.Injective pairEnc := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ h
    simp only [pairEnc, Prod.mk.injEq] at h ⊢
    exact ⟨enc_injective h.1, enc_injective h.2⟩
  let D : Finset (V × V) := Finset.univ.filter fun e ↦ G.Adj e.1 e.2
  let S : Finset (ℕ × ℕ) := D.image pairEnc
  have hS_ne : ∀ e ∈ S, e.1 ≠ e.2 := by
    intro e he
    obtain ⟨d, hdD, rfl⟩ := Finset.mem_image.mp he
    have hadj : G.Adj d.1 d.2 := (Finset.mem_filter.mp hdD).2
    intro h
    have hv : d.1 = d.2 := enc_injective h
    rw [hv] at hadj
    exact G.loopless.irrefl d.2 hadj
  obtain ⟨f, hf⟩ := nat_bool_cut_half S hS_ne
  let g : V → Bool := fun v ↦ f (enc v)
  let A : Set V := {v | g v = true}
  let H : SimpleGraph V := G.between A Aᶜ
  -- Keep `edgeFinset` independent of the specialized decidability instance for
  -- `between`: the theorem statement was elaborated with this classical one.
  let : DecidableRel H.Adj := fun _ _ ↦ Classical.propDecidable _
  refine ⟨H, SimpleGraph.between_le, SimpleGraph.between_isBipartite disjoint_compl_right, ?_⟩
  have hS_card : S.card = D.card := Finset.card_image_of_injective D pairEnc_injective
  have hcut_image :
      S.filter (fun e ↦ f e.1 ≠ f e.2) =
        (D.filter fun e ↦ g e.1 ≠ g e.2).image pairEnc := by
    ext e
    simp only [S, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨d, hdD, rfl⟩, hcut⟩
      exact ⟨d, ⟨hdD, hcut⟩, rfl⟩
    · rintro ⟨d, ⟨hdD, hcut⟩, rfl⟩
      exact ⟨⟨d, hdD, rfl⟩, hcut⟩
  have hcut_card :
      (S.filter fun e ↦ f e.1 ≠ f e.2).card =
        (D.filter fun e ↦ g e.1 ≠ g e.2).card := by
    rw [hcut_image, Finset.card_image_of_injective _ pairEnc_injective]
  have hD_card : D.card = 2 * G.edgeFinset.card := by
    simpa [D] using G.two_mul_card_edgeFinset.symm
  have hH_directed :
      D.filter (fun e ↦ g e.1 ≠ g e.2) =
        Finset.univ.filter fun e : V × V ↦ H.Adj e.1 e.2 := by
    ext e
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, H,
      SimpleGraph.between_adj, A, Set.mem_setOf_eq, Set.mem_compl_iff]
    cases h₁ : g e.1 <;> cases h₂ : g e.2 <;> simp [h₁, h₂]
  have hH_card :
      (D.filter fun e ↦ g e.1 ≠ g e.2).card = 2 * H.edgeFinset.card := by
    rw [hH_directed, ← H.two_mul_card_edgeFinset]
  rw [hS_card, hD_card, hcut_card, hH_card] at hf
  exact Nat.le_of_mul_le_mul_left hf Nat.two_pos

end Erdos63

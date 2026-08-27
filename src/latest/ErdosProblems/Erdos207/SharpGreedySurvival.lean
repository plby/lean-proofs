/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpGreedyCoveringChoiceCount

/-!
# Sharp one-step survival for the greedy kernel

The Bonferroni estimate for pair stars is converted here into a probability
estimate for one uniform greedy transition.  The event can be arbitrary: it
is enough that every choice producing the event avoids all prescribed graph
edges.  This formulation will be applied simultaneously to edges of pending
prescribed triangles and to graph edges required to remain uncovered.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The sharp pair-star estimate gives an explicit lower bound for the
number of choices covering at least one prescribed edge. -/
lemma card_mul_sub_choose_two_le_greedyCoveringChoices
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (B : Finset (Sym2 V)) (d : ℕ)
    (hoffdiag : ∀ e ∈ B, ¬ e.IsDiag)
    (hsupply : ∀ e ∈ B, d ≤ (greedyChoicesCoveringEdge S e).card) :
    B.card * d - B.card.choose 2 ≤
      (greedyCoveringChoices S B).card := by
  have hsharp := card_mul_le_greedyCoveringChoices_add_choose_two
    S B d hoffdiag hsupply
  omega

/-- If every transition producing `P` uses a triangle disjoint from `B`,
then any lower bound on the number of choices meeting `B` is an upper bound
on the probability of `P`. -/
theorem greedyKernel_probability_le_of_covering
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (B : Finset (Sym2 V)) (P : GreedyStateOn V → Prop)
    (hA : S.available.Nonempty)
    (hsafe : ∀ T : S.available,
      P (greedyStep F S T.1) → Disjoint B (tripleEdgeFinset T.1))
    (loss : ℕ) (hloss : loss ≤ (greedyCoveringChoices S B).card)
    (theta : ℝ≥0)
    (hscalar : ((S.available.card - loss : ℕ) : ℝ≥0) *
        (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card) :
    (greedyKernel F S).probability P ≤ theta ^ B.card := by
  classical
  let hne : Nonempty S.available :=
    ⟨⟨hA.choose, hA.choose_spec⟩⟩
  let next : S.available → GreedyStateOn V :=
    fun T ↦ greedyStep F S T.1
  have hfilter :
      (Finset.univ.filter fun T : S.available ↦ P (next T)).card ≤
        (Finset.univ.filter fun T : S.available ↦
          Disjoint B (tripleEdgeFinset T.1)).card := by
    apply card_le_card
    intro T hT
    rw [mem_filter] at hT ⊢
    exact ⟨mem_univ T, hsafe T hT.2⟩
  have hpartition :
      (Finset.univ.filter fun T : S.available ↦
          Disjoint B (tripleEdgeFinset T.1)).card +
        (greedyCoveringChoices S B).card = S.available.card := by
    change (Finset.univ.filter fun T : S.available ↦
        Disjoint B (tripleEdgeFinset T.1)).card +
      (Finset.univ.filter fun T : S.available ↦
        ¬ Disjoint B (tripleEdgeFinset T.1)).card = _
    rw [Finset.card_filter_add_card_filter_not]
    exact Fintype.card_coe S.available
  have hsafeCard :
      (Finset.univ.filter fun T : S.available ↦
        Disjoint B (tripleEdgeFinset T.1)).card ≤
          S.available.card - loss := by
    omega
  have hcard :
      (Finset.univ.filter fun T : S.available ↦ P (next T)).card ≤
        S.available.card - loss := hfilter.trans hsafeCard
  have hcast :
      ((Finset.univ.filter fun T : S.available ↦
          P (next T)).card : ℝ≥0) ≤
        (S.available.card - loss : ℕ) := by
    exact_mod_cast hcard
  have hratio :
      ((Finset.univ.filter fun T : S.available ↦
          P (next T)).card : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤
        ((S.available.card - loss : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ := by
    gcongr
  unfold greedyKernel
  rw [dif_pos hA]
  change (FiniteLaw.map next
    (@FiniteLaw.uniform S.available _ hne)).probability P ≤ _
  rw [FiniteLaw.probability_map,
    FiniteLaw.uniform_probability_eq_card_filter]
  simpa only [Fintype.card_coe] using hratio.trans hscalar

/-- Uniform pair-star supply and the sharp overlap correction imply a
one-step survival estimate for every event whose successful choices avoid
the prescribed edges. -/
theorem greedyKernel_probability_le_of_sharp_supply
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (B : Finset (Sym2 V)) (P : GreedyStateOn V → Prop)
    (hA : S.available.Nonempty)
    (hsafe : ∀ T : S.available,
      P (greedyStep F S T.1) → Disjoint B (tripleEdgeFinset T.1))
    (d : ℕ) (hoffdiag : ∀ e ∈ B, ¬ e.IsDiag)
    (hsupply : ∀ e ∈ B, d ≤ (greedyChoicesCoveringEdge S e).card)
    (theta : ℝ≥0)
    (hscalar :
      ((S.available.card - (B.card * d - B.card.choose 2) : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card) :
    (greedyKernel F S).probability P ≤ theta ^ B.card := by
  apply greedyKernel_probability_le_of_covering F S B P hA hsafe
    (B.card * d - B.card.choose 2)
  · exact card_mul_sub_choose_two_le_greedyCoveringChoices
      S B d hoffdiag hsupply
  · exact hscalar

end

end Erdos207

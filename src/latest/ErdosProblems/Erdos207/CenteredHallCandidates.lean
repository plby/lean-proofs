/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredRelationDiscrepancy

/-! # Linear Hall candidate counts from centered full-relation discrepancy -/

namespace Erdos207

open Finset

theorem uncentered_uniformHall_scalar_impossible
    (N d D C density s : ℕ) (hcodegree : d^2 ≤ N*C) :
    ¬ N*(D+C*s) < s*(d-density)^2 := by
  have hpow : (d-density)^2 ≤ d^2 := Nat.pow_le_pow_left (Nat.sub_le d density) 2
  have hbound : s*(d-density)^2 ≤ N*(D+C*s) := by
    calc
      _ ≤ s*d^2 := Nat.mul_le_mul_left s hpow
      _ ≤ s*(N*C) := Nat.mul_le_mul_left s hcodegree
      _ ≤ _ := by nlinarith
  exact not_lt_of_ge hbound

theorem card_relationPairsBetween_embedding
    {A B V : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (r : A → B → Prop) [DecidableRel r] (R : V → V → Prop) [DecidableRel R]
    (f : A ↪ V) (g : B ↪ V) (hrel : ∀ a b, r a b ↔ R (f a) (g b))
    (S : Finset A) (T : Finset B) :
    (relationPairsBetween r S T).card = (relationPairsBetween R (S.image f) (T.image g)).card := by
  let fg := fun ab : A × B ↦ (f ab.1, g ab.2)
  have hinj : Function.Injective fg := by
    intro a b h
    exact Prod.ext (f.injective (congrArg Prod.fst h)) (g.injective (congrArg Prod.snd h))
  have heq : (relationPairsBetween r S T).image fg = relationPairsBetween R (S.image f) (T.image g) := by
    ext ab
    rcases ab with ⟨v, w⟩
    constructor
    · intro h
      obtain ⟨⟨a, b⟩, hab, he⟩ := mem_image.mp h
      have hh := (mem_relationPairsBetween_iff r).mp hab
      cases he
      exact (mem_relationPairsBetween_iff R).mpr
        ⟨mem_image.mpr ⟨a, hh.1, rfl⟩, mem_image.mpr ⟨b, hh.2.1, rfl⟩, (hrel a b).mp hh.2.2⟩
    · intro h
      have hh := (mem_relationPairsBetween_iff R).mp h
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hh.1
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hh.2.1
      exact mem_image.mpr ⟨(a,b), (mem_relationPairsBetween_iff r).mpr
        ⟨ha, hb, (hrel a b).mpr hh.2.2⟩, rfl⟩
  rw [← heq, card_image_of_injective _ hinj]

theorem smallHall_linear_candidates_of_rectangle_upper
    {A B V : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (r : A → B → Prop) [DecidableRel r] (R : V → V → Prop) [DecidableRel R]
    (f : A ↪ V) (g : B ↪ V) (hrel : ∀ a b, r a b ↔ R (f a) (g b))
    (rho error : ℝ) (hrho : 0 ≤ rho) (d c : ℕ)
    (hdegree : ∀ a, d ≤ (relationNeighborsIn r univ a).card)
    (hrectangle : ∀ S T : Finset V, T.card ≤ S.card →
      ((relationPairsBetween R S T).card : ℝ) ≤ (rho*T.card+error)*S.card)
    (hscalar : (c : ℝ)+rho*((Fintype.card A+1)/2 : ℕ)+error ≤ d)
    (S : Finset A) (T : Finset B) (hTS : T.card < S.card) (hS : 2*S.card ≤ Fintype.card A+1) :
    c*S.card ≤ (relationPairsLeaving r S T).card := by
  have hcards : (S.image f).card = S.card := card_image_of_injective _ f.injective
  have hcardt : (T.image g).card = T.card := card_image_of_injective _ g.injective
  have hupper := hrectangle (S.image f) (T.image g) (by simpa only [hcards, hcardt] using hTS.le)
  rw [← card_relationPairsBetween_embedding r R f g hrel S T, hcards, hcardt] at hupper
  have hT : T.card ≤ (Fintype.card A+1)/2 := by omega
  have hsmall : (rho*T.card+error)*(S.card : ℝ) ≤
      (rho*((Fintype.card A+1)/2 : ℕ)+error)*S.card := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast hT) hrho) le_rfl
  have htotal := sum_relationPreneighbors_ge_real r d (fun a ↦ by exact_mod_cast hdegree a) S
  have htotalEq : (∑ b : B, ((relationPreneighborsIn r S b).card : ℝ)) =
      ((relationPairsBetween r S univ).card : ℝ) := by
    exact_mod_cast (card_relationPairsBetween_eq_sum_right r S univ).symm
  rw [htotalEq] at htotal
  have hpartition : ((relationPairsBetween r S univ).card : ℝ) =
      (relationPairsBetween r S T).card+(relationPairsLeaving r S T).card := by
    rw [relationPairsLeaving_eq_between_sdiff]
    exact_mod_cast card_relationPairsBetween_univ_eq_add_complement r S T
  have hscaled := mul_le_mul_of_nonneg_right hscalar (by positivity : 0 ≤ (S.card : ℝ))
  have hresult : (c : ℝ)*S.card ≤ (relationPairsLeaving r S T).card := by
    nlinarith only [hupper, hsmall, htotal, hpartition, hscaled]
  exact_mod_cast hresult

theorem orientedSmallHall_linear_candidates_of_centered
    {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (r : A → B → Prop) [DecidableRel r] (R : V → V → Prop) [DecidableRel R]
    (f : A ↪ V) (g : B ↪ V) (hrel : ∀ a b, r a b ↔ R (f a) (g b))
    (hsymm : ∀ v w, R v w ↔ R w v) (hcard : Fintype.card A = Fintype.card B)
    (rho xi error : ℝ) (hrho : 0 ≤ rho) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (herror : 0 ≤ error)
    (hfullDegree : ∀ v, (1-xi)*rho*Fintype.card V ≤ ((relationNeighborsIn R univ v).card : ℝ) ∧
      ((relationNeighborsIn R univ v).card : ℝ) ≤ (1+xi)*rho*Fintype.card V)
    (hfullCodegree : ∀ v w, v ≠ w → ((relationCommonNeighbors R v w).card : ℝ) ≤ (1+xi)*rho^2*Fintype.card V)
    (hbudget : 2*rho*Fintype.card V+3*xi*rho^2*(Fintype.card V : ℝ)^2 ≤ error^2)
    (d c : ℕ) (hleftDegree : ∀ a, d ≤ (relationNeighborsIn r univ a).card)
    (hrightDegree : ∀ b, d ≤ (relationNeighborsIn (transposeRelation r) univ b).card)
    (hscalar : (c : ℝ)+rho*((Fintype.card A+1)/2 : ℕ)+error ≤ d) :
    ∀ o : OrientedSmallHallObstruction A B,
      c*orientedSmallHallSize o ≤ (orientedSmallHallCandidates r o).card := by
  have hrect := typical_relation_rectangle_upper R rho xi error hrho hxi hxi1 herror hfullDegree hfullCodegree hbudget
  intro o
  rcases o with o | o
  · rw [card_orientedSmallHallCandidates_left]
    exact smallHall_linear_candidates_of_rectangle_upper r R f g hrel rho error hrho d c hleftDegree hrect
      hscalar o.1.1.1 o.1.1.2 o.1.2 o.2
  · rw [card_orientedSmallHallCandidates_right]
    apply smallHall_linear_candidates_of_rectangle_upper (transposeRelation r) R g f
      (fun b a ↦ (hrel a b).trans (hsymm (f a) (g b))) rho error hrho d c hrightDegree hrect
    · simpa only [hcard] using hscalar
    · exact o.1.2
    · exact o.2

end Erdos207

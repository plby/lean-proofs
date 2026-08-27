/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SampledLinkGoodCover

/-! # Simultaneous collision failure over actual candidate link degrees -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem independentBits_not_sampledLinkCollisionGood_le
    {O V : Type*} [Fintype O] [DecidableEq O] [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop) [∀ o, DecidableRel (r o)]
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (D M cap s : ℕ)
    (hleft : ∀ o (a : ↥(K o).left), (univ.filter (r o a)).card ≤ D)
    (hright : ∀ o (b : ↥(K o).right), (univ.filter (fun a ↦ r o a b)).card ≤ D)
    (hM : ∀ x : SimultaneousLinkPair O V K, (otherLinkCoordinates K r x).card ≤ M)
    (hs : 2 * s ≤ cap + 1) :
    (FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)).probability
      (fun omega ↦ ¬ IsSampledLinkCollisionGood K r cap omega) ≤
      ∑ o, ((K o).left.card + (K o).right.card : ℝ≥0) *
        (2 * (D : ℝ≥0) * M * sigma ^ 2 / (cap + 1)) ^ s := by
  let L := FiniteLaw.independentBits (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  let B : ℝ≥0 := (2 * (D : ℝ≥0) * M * sigma ^ 2 / (cap + 1)) ^ s
  let leftBad := fun o (a : ↥(K o).left) omega ↦
    cap + 1 ≤ (sampledLinkCollisions K r (fun b ↦ ⟨o,(a,b)⟩) (univ.filter (r o a)) omega).card
  let rightBad := fun o (b : ↥(K o).right) omega ↦
    cap + 1 ≤ (sampledLinkCollisions K r (fun a ↦ ⟨o,(a,b)⟩) (univ.filter (fun a ↦ r o a b)) omega).card
  have hl (o : O) (a : ↥(K o).left) : L.probability (leftBad o a) ≤ B := by
    have ht := independentBits_sampledLinkCollisions_tail K r (fun b ↦ ⟨o,(a,b)⟩)
      (univ.filter (r o a)) (simultaneousLinkInnerEdge_left_injective K o a) sigma hsigma M
      (fun b _ ↦ hM ⟨o,(a,b)⟩) s (cap+1) (by omega) hs
    apply ht.trans
    dsimp only [B]
    simp only [Nat.cast_add, Nat.cast_one]
    gcongr
    exact_mod_cast hleft o a
  have hr (o : O) (b : ↥(K o).right) : L.probability (rightBad o b) ≤ B := by
    have ht := independentBits_sampledLinkCollisions_tail K r (fun a ↦ ⟨o,(a,b)⟩)
      (univ.filter (fun a ↦ r o a b)) (simultaneousLinkInnerEdge_right_injective K o b) sigma hsigma M
      (fun a _ ↦ hM ⟨o,(a,b)⟩) s (cap+1) (by omega) hs
    apply ht.trans
    dsimp only [B]
    simp only [Nat.cast_add, Nat.cast_one]
    gcongr
    exact_mod_cast hright o b
  calc
    _ ≤ L.probability (fun omega ↦ ∃ o : O, (∃ a, leftBad o a omega) ∨ ∃ b, rightBad o b omega) := by
      apply L.probability_mono
      intro omega hbad
      unfold IsSampledLinkCollisionGood at hbad
      push Not at hbad
      obtain ⟨o, ho⟩ := hbad
      by_cases ha : ∀ a : ↥(K o).left,
          (sampledLinkCollisions K r (fun b ↦ ⟨o,(a,b)⟩) (univ.filter (r o a)) omega).card ≤ cap
      · obtain ⟨b, hb⟩ := ho ha
        exact ⟨o, Or.inr ⟨b, Nat.succ_le_of_lt hb⟩⟩
      · push Not at ha
        obtain ⟨a, ha⟩ := ha
        exact ⟨o, Or.inl ⟨a, Nat.succ_le_of_lt ha⟩⟩
    _ ≤ ∑ o, L.probability (fun omega ↦ (∃ a, leftBad o a omega) ∨ ∃ b, rightBad o b omega) := by
      simpa only [mem_univ, true_and] using L.probability_exists_le (univ : Finset O)
        (fun o omega ↦ (∃ a, leftBad o a omega) ∨ ∃ b, rightBad o b omega)
    _ ≤ ∑ o, ((K o).left.card + (K o).right.card : ℝ≥0) * B := by
      apply sum_le_sum
      intro o _
      apply (L.probability_or_le _ _).trans
      have hlUnion : L.probability (fun omega ↦ ∃ a, leftBad o a omega) ≤ (K o).left.card * B := by
        calc
          _ ≤ ∑ a : ↥(K o).left, L.probability (leftBad o a) := by
            simpa only [mem_univ, true_and] using L.probability_exists_le univ (leftBad o)
          _ ≤ ∑ _a : ↥(K o).left, B := sum_le_sum (fun a _ ↦ hl o a)
          _ = _ := by simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      have hrUnion : L.probability (fun omega ↦ ∃ b, rightBad o b omega) ≤ (K o).right.card * B := by
        calc
          _ ≤ ∑ b : ↥(K o).right, L.probability (rightBad o b) := by
            simpa only [mem_univ, true_and] using L.probability_exists_le univ (rightBad o)
          _ ≤ ∑ _b : ↥(K o).right, B := sum_le_sum (fun b _ ↦ hr o b)
          _ = _ := by simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      exact (add_le_add hlUnion hrUnion).trans_eq (by ring)

end

end Erdos207

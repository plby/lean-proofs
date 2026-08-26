import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Averaging threshold count

This module contains the elementary averaging lemma used in the direct
off--Turán proof.
-/

open Finset

namespace Erdos550

lemma theta_counting {ι : Type*} [DecidableEq ι]
    (S 𝒜 : Finset ι) (D : ι → ℝ)
    (hsub : 𝒜 ⊆ S) (Nn base η : ℝ) (hNn : 0 < Nn)
    (hbase : 0 ≤ base + 80 * η * Nn)
    (hup : ∀ i ∈ S, D i ≤ Nn)
    (hlo : ∀ i ∈ S, i ∉ 𝒜 → D i ≤ base + 80 * η * Nn)
    (havg :
      (base + 100 * η * Nn) * (S.card : ℝ) ≤
        ∑ i ∈ S, D i) :
    (20 * η) * (S.card : ℝ) ≤ (𝒜.card : ℝ) := by
  have hsum :
      (∑ i ∈ S, D i) ≤
        (𝒜.card : ℝ) * Nn +
          ((S \ 𝒜).card : ℝ) * (base + 80 * η * Nn) := by
    rw [← Finset.sum_sdiff hsub, add_comm]
    refine add_le_add ?_ ?_
    · calc
        (∑ i ∈ 𝒜, D i) ≤ ∑ _i ∈ 𝒜, Nn :=
          Finset.sum_le_sum fun i hi => hup i (hsub hi)
        _ = (𝒜.card : ℝ) * Nn := by
          rw [Finset.sum_const, nsmul_eq_mul]
    · calc
        (∑ i ∈ S \ 𝒜, D i) ≤
            ∑ _i ∈ S \ 𝒜, (base + 80 * η * Nn) :=
          Finset.sum_le_sum fun i hi =>
            hlo i (Finset.mem_sdiff.mp hi).1
              (Finset.mem_sdiff.mp hi).2
        _ = ((S \ 𝒜).card : ℝ) * (base + 80 * η * Nn) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc :
      ((S \ 𝒜).card : ℝ) + (𝒜.card : ℝ) = (S.card : ℝ) := by
    rw [← Nat.cast_add, Finset.card_sdiff_add_card_eq_card hsub]
  nlinarith [hNn, Nat.cast_nonneg (α := ℝ) 𝒜.card,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) 𝒜.card) hNn.le]

end Erdos550

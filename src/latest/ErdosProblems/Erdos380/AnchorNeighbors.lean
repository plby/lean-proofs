import ErdosProblems.Erdos380.EligibleAnchors
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Counting covered points by their distance from an anchor

For a fixed positive distance, each anchor gives at most one point in
each direction. Summing the `1 / H` anchor bounds therefore costs only a
harmonic sum, with no separate covering lemma or dyadic decomposition.
-/

open scoped BigOperators Classical

namespace Erdos380

noncomputable def goodAnchorNeighbors (N Q T Hmax D : ℕ) (L : ℝ) : Finset ℕ :=
  (Finset.Icc 1 Hmax).biUnion fun H =>
    (goodEligibleAnchors N Q T H D (1 : ℤˣ) L).image (fun a => a + H) ∪
      (goodEligibleAnchors N Q T H D (-1 : ℤˣ) L).image (fun a => a - H)

lemma goodAnchorNeighbors_card_le_sum (N Q T Hmax D : ℕ) (L : ℝ) :
    (goodAnchorNeighbors N Q T Hmax D L).card ≤
      ∑ H ∈ Finset.Icc 1 Hmax,
        ((goodEligibleAnchors N Q T H D (1 : ℤˣ) L).card +
          (goodEligibleAnchors N Q T H D (-1 : ℤˣ) L).card) := by
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro H _
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

lemma goodAnchorNeighbors_card_le_harmonic (N Q T Hmax D : ℕ) (L F : ℝ) (hF : 0 ≤ F)
    (h : ∀ H ∈ Finset.Icc 1 Hmax, ∀ ε : ℤˣ,
      ((goodEligibleAnchors N Q T H D ε L).card : ℝ) ≤ F / H) :
    ((goodAnchorNeighbors N Q T Hmax D L).card : ℝ) ≤ 2 * F * (1 + Real.log Hmax) := by
  have hsum : (∑ H ∈ Finset.Icc 1 Hmax, (H : ℝ)⁻¹) ≤ 1 + Real.log Hmax := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_le_one_add_log Hmax
  calc
    ((goodAnchorNeighbors N Q T Hmax D L).card : ℝ) ≤
        ∑ H ∈ Finset.Icc 1 Hmax,
          (((goodEligibleAnchors N Q T H D (1 : ℤˣ) L).card : ℝ) +
            (goodEligibleAnchors N Q T H D (-1 : ℤˣ) L).card) := by
      exact_mod_cast goodAnchorNeighbors_card_le_sum N Q T Hmax D L
    _ ≤ ∑ H ∈ Finset.Icc 1 Hmax, (2 * F) * (H : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro H hH
      have h₁ := h H hH (1 : ℤˣ)
      have h₂ := h H hH (-1 : ℤˣ)
      simpa only [div_eq_mul_inv, two_mul, add_mul] using add_le_add h₁ h₂
    _ = (2 * F) * ∑ H ∈ Finset.Icc 1 Hmax, (H : ℝ)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

theorem exists_uniform_goodAnchorNeighbors_bound :
    ∃ C K U₀ : ℝ, 0 < C ∧ 0 < K ∧ 0 < U₀ ∧ ∃ T₀ d₀ P₀ : ℕ,
      ∀ T ≥ T₀, ∀ N R Q : ℕ, 1 ≤ N → 1 < R → 2 ≤ Q → 2 ^ d₀ < Q →
      2 * T ^ 90 ≤ Q → max P₀ (128 * primeBoxEnlargement 10 * R) ≤ Q →
      ∀ Hmax : ℕ, 0 < Hmax → Hmax ≤ T →
      (Hmax : ℝ) * (C * (Real.log T ^ 5 / (T : ℝ))) ≤ 1 →
      ∀ D : ℕ, 0 < D → ∀ U L : ℝ, U₀ ≤ U → (Hmax : ℝ) ≤ U ^ 48 →
      2 * Real.log D + Real.log Hmax + 111 * U * Real.log T ≤ L →
      ((goodAnchorNeighbors N Q T Hmax D L).card : ℝ) ≤
        K * (1 + Real.log Hmax) * (Real.log (N : ℝ) / Real.log (R : ℝ)) *
          (singletonBadUpTo N).card / U ^ 2 := by
  obtain ⟨C, K, U₀, hC, hK, hU₀, T₁, d₀, P₀, hbound⟩ := exists_uniform_goodEligibleAnchors_bound
  refine ⟨C, 2 * K, U₀, hC, by positivity, hU₀, max 2 T₁, d₀, P₀, ?_⟩
  intro T hT N R Q hN hR hQ hdQ hTQ hPQ Hmax hHmax hHT hmix D hD U L hU hHU hL
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT₁ : T₁ ≤ T := (le_max_right _ _).trans hT
  have hUpos : 0 < U := hU₀.trans_le hU
  let F := K * (Real.log (N : ℝ) / Real.log (R : ℝ)) * (singletonBadUpTo N).card / U ^ 2
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hsmall (H : ℕ) (hH : H ∈ Finset.Icc 1 Hmax) (ε : ℤˣ) :
      ((goodEligibleAnchors N Q T H D ε L).card : ℝ) ≤ F / H := by
    obtain ⟨hH1, hHHmax⟩ := Finset.mem_Icc.mp hH
    have hH0 : 0 < H := by omega
    have hmixfactor : 0 ≤ C * (Real.log T ^ 5 / (T : ℝ)) := by
      have hlogT : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
      positivity
    have hmixH : (H : ℝ) * (C * (Real.log T ^ 5 / (T : ℝ))) ≤ 1 :=
      (mul_le_mul_of_nonneg_right (show (H : ℝ) ≤ Hmax by exact_mod_cast hHHmax) hmixfactor).trans hmix
    have hlogH : Real.log (H : ℝ) ≤ Real.log Hmax :=
      Real.log_le_log (by exact_mod_cast hH0) (by exact_mod_cast hHHmax)
    have h := hbound T hT₁ N R Q hR hQ hdQ hTQ hPQ H hH0 (hHHmax.trans hHT)
      hmixH D hD ε U L hU ((show (H : ℝ) ≤ Hmax by exact_mod_cast hHHmax).trans hHU) (by linarith)
    exact h.trans_eq (by dsimp [F]; ring)
  have h := goodAnchorNeighbors_card_le_harmonic N Q T Hmax D L F hF hsmall
  exact h.trans_eq (by dsimp [F]; ring)

end Erdos380

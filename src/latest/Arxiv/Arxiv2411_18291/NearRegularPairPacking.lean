import Arxiv.Arxiv2411_18291.BalancedDegreeBounds
import Arxiv.Arxiv2411_18291.BipartitePairMatching
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # A finite matching criterion for nearly equal pair degrees -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_nearRegular_pair_packing {V : Type*} [DecidableEq V]
    (S : Finset V) (H : Finset (Block V 2)) (hHS : ∀ Q ∈ H, Q.val ⊆ S)
    {D c : ℝ} (hD : 0 < D) (hc : 0 ≤ c) (hcsmall : c ≤ 1 / 4)
    (hS : D / 2 ≤ (S.card : ℝ))
    (hdegree : ∀ v ∈ S, |((pairNeighbors H v).card : ℝ) - D| ≤ c * D)
    (hsmall : (S.card + 1 : ℝ) *
      (2 * Real.exp (-((D / 2) * c ^ 2 / (4 * (1 + 2 * c))))) < 1) :
    ∃ C : Finset (Block V 2), C ⊆ H ∧ IsVertexPacking C ∧
      ((S \ vertexSupport C).card : ℝ) ≤ 9 * c * S.card + 2 := by
  have hc1 : c ≤ 1 := by linarith only [hcsmall]
  have hdegrees : ∀ v ∈ S, D / 2 ≤ ((H.filter fun Q => v ∈ Q.val).card : ℝ) := by
    intro v hv
    have hlo := (abs_le.mp (hdegree v hv)).1
    have hcD := mul_le_mul_of_nonneg_right hcsmall hD.le
    rw [← card_pairNeighbors]
    linarith only [hlo, hcD, hD]
  obtain ⟨A, hAS, hbalance, hcounts⟩ :=
    exists_balanced_pair_partition S H hHS hc hS hdegrees hsmall
  let δ := (1 - c) ^ 2 * D / 2
  let Δ := (1 + c) ^ 2 * D / 2
  let d := ⌈4 * c * (S.card : ℝ)⌉₊
  have hΔ : 0 < Δ := by dsimp only [Δ]; positivity
  have hdiff : Δ - δ = 2 * c * D := by dsimp only [Δ, δ]; ring
  have hδΔ : δ ≤ Δ := by
    have hnonneg : 0 ≤ 2 * c * D := by positivity
    linarith only [hdiff, hnonneg]
  have hΔlow : D / 2 ≤ Δ := by
    have hp : (1 : ℝ) ≤ (1 + c) ^ 2 := by nlinarith only [hc, sq_nonneg c]
    have hh := mul_le_mul_of_nonneg_right hp hD.le
    dsimp only [Δ]
    linarith only [hh]
  have hmin : ∀ a ∈ A, δ ≤ ((pairNeighbors H a ∩ (S \ A)).card : ℝ) := by
    intro a ha
    have haS := hAS ha
    have hNS : pairNeighbors H a ⊆ S := by
      intro b hb
      obtain ⟨Q, hQ, hQval⟩ := (mem_pairNeighbors H a b).mp hb
      exact hHS Q hQ (by simp [hQval])
    have hsplit : ((pairNeighbors H a ∩ (S \ A)).card : ℝ) +
        ((pairNeighbors H a ∩ A).card : ℝ) = ((pairNeighbors H a).card : ℝ) := by
      exact_mod_cast card_inter_complement_of_subset (A := A) hNS
    have hlo := (balanced_half_count_bounds hc hc1 (hdegree a haS)
      (balanced_complement_error (hcounts a haS))).1
    change δ ≤ ((pairNeighbors H a).card : ℝ) - ((pairNeighbors H a ∩ A).card : ℝ) at hlo
    linarith only [hlo, hsplit]
  have hmax : ∀ b ∈ S \ A, ((pairNeighbors H b ∩ A).card : ℝ) ≤ Δ := by
    intro b hb
    exact (balanced_half_count_bounds hc hc1 (hdegree b (mem_sdiff.mp hb).1)
      (hcounts b (mem_sdiff.mp hb).1)).2
  have hround : 4 * c * (S.card : ℝ) ≤ d := Nat.le_ceil _
  have hroundUpper : (d : ℝ) < 4 * c * S.card + 1 := Nat.ceil_lt_add_one (by positivity)
  have hAcard : (A.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hAS
  have hdefect : (Δ - δ) * A.card ≤ Δ * d := by
    calc
      _ = (D / 2) * (4 * c * A.card) := by rw [hdiff]; ring
      _ ≤ (D / 2) * (4 * c * S.card) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hAcard (by positivity)) (by positivity)
      _ ≤ (D / 2) * d := mul_le_mul_of_nonneg_left hround (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hΔlow (Nat.cast_nonneg d)
  obtain ⟨C, hCH, hC, hleave⟩ := exists_bipartite_pair_packing S A H hHS hΔ hδΔ hmin hmax d hdefect
  refine ⟨C, hCH, hC, ?_⟩
  have hAlo := (abs_le.mp hbalance).1
  linarith only [hleave, hAlo, hroundUpper]

end Arxiv2411_18291

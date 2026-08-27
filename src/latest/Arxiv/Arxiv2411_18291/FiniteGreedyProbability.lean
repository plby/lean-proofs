import Arxiv.Arxiv2411_18291.ExplicitAbsorberGreedyTail
import Arxiv.Arxiv2411_18291.FiniteUniformGreedy
import Arxiv.Arxiv2411_18291.UnstoppedPrescribedGreedyProcess

/-!
# Finite high-probability bounds for the actual greedy algorithms

The ordinary processes have no degree stop. Under the verified finite
smallness conditions, their bounded-success events have failure below
exp(-n^(2/5)) at n0. Prescribed candidates may depend on the full history.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Finset W} {q r n : ℕ}

theorem unstopped_greedy_probability_paper_threshold
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (H : Hypergraph W (r + 1)) (hH : H.card ≤ n)
    (hw : 4 * (Fintype.card W) ^ 2 ≤ n) (hadm : IsAdmissible H F)
    {θ : ℝ} (hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ)
    (hsmall : H.card * (θ + H.card * (4 * (r + 1).factorial * θ)) ≤ 1 / 4)
    (t : ℕ) (Φ : ℕ → F ↪ Fin n) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B θ)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedGreedyProbability Φ H B).real
        (greedyFamilyEvent Φ H B (4 * (r + 1).factorial * θ) t) := by
  have hnpos : 0 < n := Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo
  have hs := unstopped_greedy_family_success_probability Φ H B hB hθ
    (by simpa only [Fintype.card_fin] using hw)
    (by simpa only [Fintype.card_fin] using hnpos) hsmall t hadm hroots
  simp only [Block, Fintype.card_finset_len, Fintype.card_fin] at hs
  exact (sub_lt_sub_left (absorber_greedy_failure_lt_stretched_exp hqr hn hH hlo) 1).trans_le hs

theorem unstopped_prescribed_probability_paper_threshold
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (H : Hypergraph W (r + 1)) (hH : H.card ≤ n) (hadm : IsAdmissible H F)
    {θ θB η : ℝ} (hθB : 0 ≤ θB) (hη : 0 < η)
    (hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ / η)
    (hsmall : H.card * (θB + H.card * (4 * (r + 1).factorial * θ / η)) ≤ η / 2)
    (t : ℕ) (Φ : ℕ → F ↪ Fin n) (A : CandidateFamilies Φ)
    (B : Hypergraph (Fin n) (r + 1)) (hB : IsGraphBounded B θB)
    (hA : HasCandidateLowerBound Φ A H (4 * (r + 1).factorial * θ / η) η t)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedPrescribedGreedyProbability Φ A H B).real
        (prescribedGreedyFamilyEvent Φ A H B (4 * (r + 1).factorial * θ / η) t) := by
  have hnpos : 0 < n := Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hθ : 0 ≤ θ := by
    have hh := (le_div_iff₀ hη).mp ((Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo)
    simpa only [zero_mul] using hh
  have hs := unstopped_prescribed_greedy_family_success_probability Φ A H B hB hθ hθB hη
    (by simpa only [Fintype.card_fin] using hnpos) hsmall t hA hadm hroots
  simp only [Block, Fintype.card_finset_len, Fintype.card_fin] at hs
  have heq : (2 * (r + 1).factorial * θ * (n : ℝ) / η) / 3 =
      2 * (r + 1).factorial * (θ / η) * n / 3 := by ring
  rw [heq] at hs
  exact (sub_lt_sub_left (absorber_greedy_failure_lt_stretched_exp hqr hn hH hlo) 1).trans_le hs

theorem small_pattern_uniform_greedy_probability_paper_threshold
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (H : Hypergraph W (r + 1)) (hH : H.card ≤ (4 * q) ^ (2 * q))
    (hadm : IsAdmissible H F) {θ : ℝ}
    (hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ)
    (hhi : θ ≤ (4 * q : ℝ) ^ (24 * q) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))
    (t : ℕ) (Φ : ℕ → F ↪ Fin n) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B θ)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedGreedyProbability Φ H B).real
        (greedyFamilyEvent Φ H B (4 * (r + 1).factorial * θ) t) := by
  obtain ⟨_, hsize, hsmall, _⟩ :=
    small_pattern_uniform_greedy_numerics hqr hn hw hH hlo hhi
  have hMsize : H.card ≤ n := hH.trans
    ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans
      ((boost_threshold_le_paper_threshold hqr).trans hn))
  exact unstopped_greedy_probability_paper_threshold hqr hn H hMsize hsize hadm
    hlo hsmall t Φ B hB hroots

theorem small_pattern_uniform_greedy_paper_probability
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (H : Hypergraph W (r + 1)) (hH : H.card ≤ (4 * q) ^ (2 * q))
    (hadm : IsAdmissible H F) {θ : ℝ}
    (hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ)
    (hhi : θ ≤ (4 * q : ℝ) ^ (24 * q) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))
    (t : ℕ) (Φ : ℕ → F ↪ Fin n) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B θ)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedGreedyProbability Φ H B).real
        (allEdgesGreedyFamilyEvent Φ H B
          ((2 : ℝ) ^ (r + 2) * (r + 1).factorial * θ) t) := by
  have hb := small_pattern_uniform_greedy_probability_paper_threshold hqr hn hw H hH
    hadm hlo hhi t Φ B hB hroots
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo
  obtain ⟨hθL, hL⟩ := greedy_paper_output_bound r hθ
  rw [allEdgesGreedyFamilyEvent_eq Φ H B t (hθL.trans hL) hroots]
  exact hb.trans_le (measureReal_mono (greedyFamilyEvent_mono Φ H B t hL))

end Arxiv2411_18291

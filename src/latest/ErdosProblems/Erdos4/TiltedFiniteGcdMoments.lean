import ErdosProblems.Erdos4.TiltedGcdMoment
import ErdosProblems.Erdos4.TiltedGcdDivisorBounds
import ErdosProblems.Erdos4.TiltedBlockArithmetic

/-! Averaged gcd estimates for the actual fiber partitions and root-color companions. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

noncomputable def gcdTiltError (W R N : ℕ) (τ D a : ℝ) : ℝ :=
  D * (Real.exp (2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ))) - 1) +
    (N : ℝ) ^ τ * (D * (a / R + (R : ℝ) ^ (-(1 / 2 : ℝ)) *
      Real.exp (2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ)))))

theorem partition_gcd_tilt_moment {C : Finset ℕ} (P : Finpartition C)
    (σ : FiniteLaw P.parts) (S : Finset ℕ) {x p Y U W R X K : ℕ}
    (hp : 0 < p) (hY : 1 ≤ Y) (hW : 0 < W) (hR : 1 ≤ R) (hRX : R * R ≤ X)
    (hS : ∀ s ∈ S, s.Prime ∧ W < s ∧ s ≤ X)
    (hC : ∀ n ∈ C, x < n ∧ n ≤ Y) (hYU : Y < p * U)
    (hfiber : ∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod p) = (m : ZMod p))
    (hcard : ∀ E ∈ P.parts, E.card ≤ K)
    (hsq : ∀ E ∈ P.parts, Squarefree (∏ n ∈ E, n))
    (hfactors : ∀ n ∈ C, n.primeFactors ⊆ S)
    {b τ : ℝ} (hb : 0 ≤ b) (hσ : ∀ E, σ.weight E ≤ b)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) :
    (pairLaw σ σ).mean (fun EF => (blockGcd EF.1.val EF.2.val : ℝ) ^ τ) ≤
      1 + gcdTiltError W R (Y ^ K) τ
        ((b * (((x + p : ℕ) : ℝ) + X)) ^ 2) ((U : ℝ) ^ 2) := by
  have hpos : ∀ (E : P.parts), ∀ n ∈ E.val, 0 < n := by
    intro E n hn
    exact Nat.lt_of_le_of_lt (Nat.zero_le x) (hC n (P.subset E.property hn)).1
  have hh := squarefree_tilt_moment (pairLaw σ σ)
    (fun EF => blockGcd EF.1.val EF.2.val) S hW hR hRX hS
    (fun EF => blockGcd_squarefree _ _ (hsq EF.1.val EF.1.property))
    (fun EF => blockGcd_factors_subset _ _ S (hpos EF.1)
      (fun n hn => hfactors n (P.subset EF.1.property hn)))
    (fun EF => blockGcd_le_pow _ _ hY (hpos EF.1)
      (fun n hn => (hC n (P.subset EF.1.property hn)).2) (hcard EF.1.val EF.1.property))
    hτ0 hτ (sq_nonneg _) (sq_nonneg _)
    (fun d hd hd1 hdX _ => partition_label_divisor_bound P σ x p Y U X d hp hd hd1 hdX
      hC hYU hfiber hb hσ)
  simpa only [gcdTiltError, add_assoc] using hh

theorem rooted_gcd_tilt_moment (colors : Finset ℕ) (companion : ℕ → Finset ℕ)
    (σ : FiniteLaw colors) (S : Finset ℕ) {v Y U M W R X K : ℕ}
    (hY : 1 ≤ Y) (hW : 0 < W) (hR : 1 ≤ R) (hRX : R * R ≤ X)
    (hS : ∀ s ∈ S, s.Prime ∧ W < s ∧ s ≤ X) (hU : ∀ s ∈ S, U ≤ s)
    (hcolors : ∀ p ∈ colors, 1 ≤ p ∧ p ≤ M)
    (hvY : v ≤ Y) (hYU : ∀ p ∈ colors, Y < p * U)
    (hcomp : ∀ p ∈ colors, ∀ n ∈ companion p,
      n ≤ Y ∧ n ≠ v ∧ (n : ZMod p) = (v : ZMod p))
    (hpos : ∀ p ∈ colors, ∀ n ∈ companion p, 0 < n)
    (hcard : ∀ p ∈ colors, (companion p).card ≤ K)
    (hsq : ∀ p ∈ colors, Squarefree (∏ n ∈ companion p, n))
    (hfactors : ∀ p ∈ colors, ∀ n ∈ companion p, n.primeFactors ⊆ S)
    {b τ : ℝ} (hb : 0 ≤ b) (hσ : ∀ p, σ.weight p ≤ b)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) :
    (pairLaw σ σ).mean (fun pq => (blockGcd (companion pq.1.val) (companion pq.2.val) : ℝ) ^ τ) ≤
      1 + gcdTiltError W R (Y ^ K) τ ((b * ((M : ℝ) + X)) ^ 2) ((2 * (U : ℝ)) ^ 2) := by
  have hh := squarefree_tilt_moment (pairLaw σ σ)
    (fun pq => blockGcd (companion pq.1.val) (companion pq.2.val)) S hW hR hRX hS
    (fun pq => blockGcd_squarefree _ _ (hsq pq.1.val pq.1.property))
    (fun pq => blockGcd_factors_subset _ _ S (hpos pq.1.val pq.1.property)
      (hfactors pq.1.val pq.1.property))
    (fun pq => blockGcd_le_pow _ _ hY (hpos pq.1.val pq.1.property)
      (fun n hn => (hcomp pq.1.val pq.1.property n hn).1) (hcard pq.1.val pq.1.property))
    hτ0 hτ (sq_nonneg _) (sq_nonneg _)
    (fun d hd _ hdX hdS => rooted_label_divisor_bound colors companion σ v Y U M X d hd hdX
      hcolors hvY hYU hcomp (fun s hs => hU s (hdS hs)) hb hσ)
  simpa only [gcdTiltError, add_assoc] using hh

end Erdos4.Tilted

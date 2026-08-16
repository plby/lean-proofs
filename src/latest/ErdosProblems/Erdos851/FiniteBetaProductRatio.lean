/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.BetaProductRatioDepth
import ErdosProblems.Erdos851.FiniteRecursiveBridge

/-!
# Finite beta-sieve main terms from prefix product ratios

This is the final reversal adapter: the concrete prefix Euler-product
hypotheses proved in `BetaProductRatioDepth` are transported to the increasing
list convention of `FiniteCombinatorialSieve`.
-/

namespace Erdos851

open List
open FiniteCombinatorialSieve
open BetaSieveFundamental
open FiniteRecursiveBridge

/-- Genuine prefix product-ratio estimates on the reversed prime list imply
the multiplicative lower and upper bounds for the finite combinatorial main
terms.  The statement contains no `HasDepthProductRatio` assumption. -/
theorem finiteMainTerms_bounds_of_prefixProductRatio
    (Astop : List ℕ → Prop) [DecidablePred Astop]
    (g : ℕ → ℝ) (P : List ℕ)
    (upperCutoff lowerCutoff : ℕ → List ℕ) {A κ : ℝ} {start : ℕ}
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p ∈ P, g p < 1)
    (hPnodup : P.Nodup)
    (hupperPrefix : ∀ r ≤ P.length, upperCutoff r <+: P.reverse)
    (hlowerPrefix : ∀ r ≤ P.length, lowerCutoff r <+: P.reverse)
    (hupperChain : ∀ r ≤ P.length,
      ∀ t ∈ upperFailureTerms (fun s => decide (Astop s.reverse))
          P.length [] P.reverse,
        t.1.length = r → t.1 <+ upperCutoff r)
    (hlowerChain : ∀ r ≤ P.length,
      ∀ t ∈ lowerFailureTerms (fun s => decide (Astop s.reverse))
          P.length [] P.reverse,
        t.1.length = r → t.1 <+ lowerCutoff r)
    (hupperStart : ∀ t ∈
        upperFailureTerms (fun s => decide (Astop s.reverse))
          P.length [] P.reverse,
      start ≤ t.1.length)
    (hlowerStart : ∀ t ∈
        lowerFailureTerms (fun s => decide (Astop s.reverse))
          P.length [] P.reverse,
      start ≤ t.1.length)
    (hA : 1 ≤ A) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (hupperProduct : ∀ r ≤ P.length, start ≤ r →
      (buchstabProduct g (upperCutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r))
    (hlowerProduct : ∀ r ≤ P.length, start ≤ r →
      (buchstabProduct g (lowerCutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r))
    (hlogA : ∀ r, start ≤ r → r ≤ P.length →
      Real.log A ≤ 2 * κ * r / 99) :
    let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ start
    (1 - eta) * finiteEulerProduct g P ≤ lowerMainTerm Astop g P ∧
      upperMainTerm Astop g P ≤
        (1 + eta) * finiteEulerProduct g P := by
  have h := rosserMainTerms_bounds_of_prefixProductRatio
    (fun s => decide (Astop s.reverse)) g P.length []
    upperCutoff lowerCutoff hg0
    (fun p hp => hg1 p (by simpa using hp))
    (by simpa using hPnodup : P.reverse.Nodup) (by simp)
    hupperPrefix hlowerPrefix hupperChain hlowerChain
    hupperStart hlowerStart hA hκ0 hκ2
    hupperProduct hlowerProduct hlogA
  rw [← lowerMainTerm_eq_rosserLowerEval Astop g P,
    ← upperMainTerm_eq_rosserUpperEval Astop g P] at h
  simpa [finiteEulerProduct, buchstabProduct, List.map_reverse] using h

end Erdos851

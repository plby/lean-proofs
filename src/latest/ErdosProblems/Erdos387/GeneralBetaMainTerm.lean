/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.GeneralBetaCutoff
import ErdosProblems.Erdos851.FiniteBetaProductRatio

/-!
# Arbitrary-beta finite Rosser main terms

This module joins the variable-beta stopping geometry to the already
formalized finite beta-sieve fundamental lemma.  Choosing `beta` proportional
to the actual sieve dimension makes the cutoff ratio so close to one that
its product-ratio estimate can be expressed with the existing effective
dimension `kappa = 2`.
-/

namespace Erdos387.GeneralBetaMainTerm

open Erdos851
open Erdos851.FiniteCombinatorialSieve
open Erdos851.BetaSieveFundamental
open Erdos387.GeneralBetaCutoff

/-- Variable-beta finite fundamental lemma.  All Rosser chain and minimum
depth hypotheses are discharged.  The remaining analytic hypothesis is an
ordinary inverse Euler-product estimate on the explicit cutoff prefix. -/
theorem finiteMainTerms_bounds_of_generalBetaCutoffs
    (g : ℕ → ℝ) (beta z y S : ℕ) {A : ℝ}
    (hbeta : 2 ≤ beta) (hS : beta + 1 ≤ S) (hy : 1 < y)
    (hg0 : ∀ p, 0 ≤ g p)
    (hg1 : ∀ p ∈ descendingSievePrimes z y, g p < 1)
    (hA : 1 ≤ A)
    (hproduct : ∀ r ≤ (descendingSievePrimes z y).length,
      S - beta ≤ r →
      (buchstabProduct g (betaCutoffPrefix beta z y r))⁻¹ ≤
        A * Real.rpow betaRatio (2 * r))
    (hlogA : ∀ r, S - beta ≤ r →
      r ≤ (descendingSievePrimes z y).length →
      Real.log A ≤ 4 * r / 99) :
    let P := (descendingSievePrimes z y).reverse
    let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - beta)
    (1 - eta) * finiteEulerProduct g P ≤
        lowerMainTerm (rosserStoppingPredicate beta (y ^ S)) g P ∧
      upperMainTerm (rosserStoppingPredicate beta (y ^ S)) g P ≤
        (1 + eta) * finiteEulerProduct g P := by
  classical
  dsimp only
  let P := (descendingSievePrimes z y).reverse
  let stop : List ℕ → Prop := rosserStoppingPredicate beta (y ^ S)
  letI : DecidablePred stop := Classical.decPred stop
  have hstop : (fun s : List ℕ => decide (stop s.reverse)) =
      descendingRosserStop beta (y ^ S) := by
    funext s
    unfold descendingRosserStop descendingRosserStoppingPredicate
    exact decide_eq_decide.mpr Iff.rfl
  apply Erdos851.finiteMainTerms_bounds_of_prefixProductRatio
    stop g P
    (fun r => betaCutoffPrefix beta z y r)
    (fun r => betaCutoffPrefix beta z y r)
    (A := A) (κ := 2) (start := S - beta)
  · exact hg0
  · intro p hp
    exact hg1 p (by simpa [P] using hp)
  · simp [P, descendingSievePrimes_nodup]
  · intro r hr
    simpa [P] using betaCutoffPrefix_isPrefix beta z y r (by omega)
  · intro r hr
    simpa [P] using betaCutoffPrefix_isPrefix beta z y r (by omega)
  · intro r hr t ht hlen
    rw [hstop] at ht
    have ht' : t ∈ upperFailureTerms (descendingRosserStop beta (y ^ S))
        P.length [] (descendingSievePrimes z y) := by
      simpa [P] using ht
    simpa [P] using
      upperFailureTerm_chain_sublist_betaCutoffPrefix ht' hbeta hS hlen
  · intro r hr t ht hlen
    rw [hstop] at ht
    have ht' : t ∈ lowerFailureTerms (descendingRosserStop beta (y ^ S))
        P.length [] (descendingSievePrimes z y) := by
      simpa [P] using ht
    simpa [P] using
      lowerFailureTerm_chain_sublist_betaCutoffPrefix ht' hbeta hS hlen
  · intro t ht
    rw [hstop] at ht
    have ht' : t ∈ upperFailureTerms (descendingRosserStop beta (y ^ S))
        P.length [] (descendingSievePrimes z y) := by
      simpa [P] using ht
    exact upperFailureTerm_start_depth hy ht'
  · intro t ht
    rw [hstop] at ht
    have ht' : t ∈ lowerFailureTerms (descendingRosserStop beta (y ^ S))
        P.length [] (descendingSievePrimes z y) := by
      simpa [P] using ht
    exact lowerFailureTerm_start_depth hy ht'
  · exact hA
  · norm_num
  · norm_num
  · intro r hr hstart
    simpa [P] using hproduct r (by simpa [P] using hr) hstart
  · intro r hr hstart
    simpa [P] using hproduct r (by simpa [P] using hr) hstart
  · intro r hstart hr
    convert hlogA r hstart (by simpa [P] using hr) using 1 <;> ring

end Erdos387.GeneralBetaMainTerm

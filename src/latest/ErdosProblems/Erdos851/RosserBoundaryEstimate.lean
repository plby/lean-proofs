/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.FiniteCombinatorialSieve
import ErdosProblems.Erdos851.GeometricBetaTail
import ErdosProblems.Erdos851.LocalEulerProducts
import ErdosProblems.Erdos851.BetaSieveFundamental

/-!
# From Rosser boundary errors to beta-sieve main terms

This file records the last algebraic step of the finite fundamental lemma.
The combinatorial sieve gives exact identities

`lowerMainTerm = V - lowerBoundaryError` and
`upperMainTerm = V + upperBoundaryError`.

Consequently a bound for either boundary error after division by the positive
Euler product `V` immediately gives the usual multiplicative main-term
estimate.  We also package the application of the numerical beta-100 tail,
and record the elementary fact that a failed stopping chain at level
`D = y^S` has length greater than `S - beta`.
-/

namespace Erdos851.RosserBoundaryEstimate

open scoped BigOperators
open Erdos851.FiniteCombinatorialSieve

/-- A failed Rosser stopping test at level `y^S` cannot occur before depth
`S - beta`.  The exponent in the stopping predicate is `beta + 1`, while a
chain of length `r` has `r - 1` factors in its tail, giving the exponent
`r + beta` on the right. -/
theorem stopping_failure_forces_depth
    {beta D y S : ℕ} {t : List ℕ}
    (hy : 1 < y) (hD : D = y ^ S)
    (ht : ∀ q ∈ t, q ≤ y)
    (hfail : ¬ rosserStoppingPredicate beta D t) :
    S < t.length + beta := by
  cases t with
  | nil =>
      simp [rosserStoppingPredicate] at hfail
  | cons p ps =>
      have hp : p ≤ y := ht p (by simp)
      have hps : ps.prod ≤ y ^ ps.length := by
        calc
          ps.prod ≤ (ps.map fun _ => y).prod := by
            simpa using (List.prod_le_prod' (l := ps)
              (f := id) (g := fun _ => y) (fun q hq => ht q (by simp [hq])))
          _ = y ^ ps.length := by simp
      have hpow : p ^ (beta + 1) ≤ y ^ (beta + 1) :=
        Nat.pow_le_pow_left hp _
      have hprod : ps.prod * p ^ (beta + 1) ≤
          y ^ (ps.length + (beta + 1)) := by
        calc
          ps.prod * p ^ (beta + 1) ≤
              y ^ ps.length * y ^ (beta + 1) :=
            Nat.mul_le_mul hps hpow
          _ = y ^ (ps.length + (beta + 1)) := by
            simp [pow_add, mul_assoc]
      have hlt : y ^ S < ps.prod * p ^ (beta + 1) := by
        rw [hD] at hfail
        simpa [rosserStoppingPredicate] using hfail
      have hexp : S < ps.length + (beta + 1) :=
        (Nat.pow_lt_pow_iff_right hy).mp (hlt.trans_le hprod)
      simp only [List.length_cons]
      omega

/-- The lower exact identity converted to a multiplicative estimate. -/
theorem lowerMainTerm_ge_of_normalizedBoundary_le
    {A : List ℕ → Prop} {g : ℕ → ℝ} {P : List ℕ} {η : ℝ}
    (hV : 0 < finiteEulerProduct g P)
    (herror : lowerBoundaryError A g P /
        finiteEulerProduct g P ≤ η) :
    (1 - η) * finiteEulerProduct g P ≤ lowerMainTerm A g P := by
  rw [lowerMainTerm_eq_euler_sub_boundary]
  have hmul := (div_le_iff₀ hV).mp herror
  linarith

/-- The upper exact identity converted to a multiplicative estimate. -/
theorem upperMainTerm_le_of_normalizedBoundary_le
    {A : List ℕ → Prop} {g : ℕ → ℝ} {P : List ℕ} {η : ℝ}
    (hV : 0 < finiteEulerProduct g P)
    (herror : upperBoundaryError A g P /
        finiteEulerProduct g P ≤ η) :
    upperMainTerm A g P ≤
      (1 + η) * finiteEulerProduct g P := by
  rw [upperMainTerm_eq_euler_add_boundary]
  have hmul := (div_le_iff₀ hV).mp herror
  linarith

/-- A finite beta-depth-series majorant for the two normalized errors gives
both fundamental-lemma main-term inequalities.  This theorem is independent
of how the chain majorants were obtained; in the application they come from
the dimension-one or dimension-two product-ratio estimate. -/
theorem mainTerm_bounds_of_depthSeries
    {Astop : List ℕ → Prop} {g : ℕ → ℝ} {P : List ℕ}
    {A η : ℝ} {κ R m : ℕ}
    (hV : 0 < finiteEulerProduct g P)
    (hlower : lowerBoundaryError Astop g P /
        finiteEulerProduct g P ≤
          ∑ i ∈ Finset.range m, GeometricBetaTail.term A κ (R + i))
    (hupper : upperBoundaryError Astop g P /
        finiteEulerProduct g P ≤
          ∑ i ∈ Finset.range m, GeometricBetaTail.term A κ (R + i))
    (htail : (∑ i ∈ Finset.range m,
        GeometricBetaTail.term A κ (R + i)) ≤ η) :
    (1 - η) * finiteEulerProduct g P ≤ lowerMainTerm Astop g P ∧
      upperMainTerm Astop g P ≤
        (1 + η) * finiteEulerProduct g P := by
  constructor
  · exact lowerMainTerm_ge_of_normalizedBoundary_le hV (hlower.trans htail)
  · exact upperMainTerm_le_of_normalizedBoundary_le hV (hupper.trans htail)

/-- The corrected depth-dependent beta majorants, once supplied for both
finite boundary errors, give concrete multiplicative lower and upper main
term bounds.  This is the finite-main-term endpoint matching
`BetaSieveFundamental.sum_betaDepthMajorant_le`; it avoids the older fixed-C
factorial tail and does not mention `HasDepthProductRatio`. -/
theorem mainTerm_bounds_of_betaDepthMajorantSeries
    {Astop : List ℕ → Prop} {g : ℕ → ℝ} {P : List ℕ}
    {A κ : ℝ} {start m : ℕ}
    (hV : 0 < finiteEulerProduct g P)
    (hA : 1 ≤ A) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (hlogA : ∀ i < m,
      Real.log A ≤ 2 * κ * (start + i : ℕ) / 99)
    (hlower : lowerBoundaryError Astop g P /
        finiteEulerProduct g P ≤
          ∑ i ∈ Finset.range m,
            BetaSieveFundamental.betaDepthMajorant A κ (start + i))
    (hupper : upperBoundaryError Astop g P /
        finiteEulerProduct g P ≤
          ∑ i ∈ Finset.range m,
            BetaSieveFundamental.betaDepthMajorant A κ (start + i)) :
    (1 - (4 * A / 3) * (1 / 4 : ℝ) ^ start) *
          finiteEulerProduct g P ≤ lowerMainTerm Astop g P ∧
      upperMainTerm Astop g P ≤
        (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ start) *
          finiteEulerProduct g P := by
  have htail := BetaSieveFundamental.sum_betaDepthMajorant_le
    start m hA hκ0 hκ2 hlogA
  constructor
  · exact lowerMainTerm_ge_of_normalizedBoundary_le hV
      (hlower.trans htail)
  · exact upperMainTerm_le_of_normalizedBoundary_le hV
      (hupper.trans htail)

/-- The numerical beta-100 theorem supplies one depth which works
simultaneously for every finite prime list and both Rosser errors, once their
normalized depth layers satisfy the advertised product-ratio majorant. -/
theorem exists_depth_mainTerm_bounds
    {A η : ℝ} (hA : 1 ≤ A) (hη : 0 < η) {κ : ℕ} (hκ : κ ≤ 2) :
    ∃ R : ℕ, ∀ (Astop : List ℕ → Prop) (g : ℕ → ℝ)
      (P : List ℕ) (m : ℕ),
      0 < finiteEulerProduct g P →
      lowerBoundaryError Astop g P / finiteEulerProduct g P ≤
          ∑ i ∈ Finset.range m, GeometricBetaTail.term A κ (R + i) →
      upperBoundaryError Astop g P / finiteEulerProduct g P ≤
          ∑ i ∈ Finset.range m, GeometricBetaTail.term A κ (R + i) →
      (1 - η) * finiteEulerProduct g P ≤ lowerMainTerm Astop g P ∧
        upperMainTerm Astop g P ≤
          (1 + η) * finiteEulerProduct g P := by
  obtain ⟨R, _hgeom, hfinite, _hinfinite⟩ :=
    GeometricBetaTail.exists_tails_lt hA hη hκ
  refine ⟨R, ?_⟩
  intro Astop g P m hV hlower hupper
  exact mainTerm_bounds_of_depthSeries hV hlower hupper
    (hfinite m).le

end Erdos851.RosserBoundaryEstimate

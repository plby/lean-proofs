/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.BetaSieveFundamental
import ErdosProblems.Erdos851.BetaSieveFailureCombinatorics
import ErdosProblems.Erdos851.FiniteCombinatorialSieve
import ErdosProblems.Erdos851.LocalEulerProducts

/-!
# Arithmetic geometry of Rosser first-failure chains

`RosserCore` builds selected prime chains in decreasing order.  In contrast,
`FiniteCombinatorialSieve.rosserStoppingPredicate` is stated on an increasing
chain, with its head (the smallest selected prime) receiving exponent
`beta + 1`.  This file supplies the reversal adapter and records the elementary
arithmetic consequences needed by the quantitative beta-sieve bridge.
-/

namespace Erdos851.BetaSieveFundamental

open Erdos851.FiniteCombinatorialSieve
open scoped BigOperators

/-- The finite-sieve stopping predicate transported to the decreasing chains
used by `RosserCore`. -/
def descendingRosserStoppingPredicate (beta D : ℕ) (chain : List ℕ) : Prop :=
  rosserStoppingPredicate beta D chain.reverse

/-- Boolean form of `descendingRosserStoppingPredicate`, suitable for the
recursive Rosser evaluators. -/
noncomputable def descendingRosserStop (beta D : ℕ) (chain : List ℕ) : Bool := by
  classical
  exact decide (descendingRosserStoppingPredicate beta D chain)

@[simp] theorem descendingRosserStop_eq_true {beta D : ℕ} {chain : List ℕ} :
    descendingRosserStop beta D chain = true ↔
      descendingRosserStoppingPredicate beta D chain := by
  simp [descendingRosserStop]

@[simp] theorem descendingRosserStop_eq_false {beta D : ℕ} {chain : List ℕ} :
    descendingRosserStop beta D chain = false ↔
      ¬ descendingRosserStoppingPredicate beta D chain := by
  simp [descendingRosserStop]

/-- On a nonempty decreasing chain, the transported predicate puts the large
power on the final (and hence smallest) selected prime. -/
theorem descendingRosserStoppingPredicate_append_singleton
    (beta D q : ℕ) (head : List ℕ) :
    descendingRosserStoppingPredicate beta D (head ++ [q]) ↔
      head.prod * q ^ (beta + 1) ≤ D := by
  simp [descendingRosserStoppingPredicate, rosserStoppingPredicate]

/-- Every explicit first-failure term really ends at a prefix on which the
Boolean stopping test is false.  The statement is simultaneous for the upper
and lower recursions because those recursions alternate. -/
theorem failureTerms_final_failure {alpha : Type*} (stop : List alpha → Bool) :
    ∀ (fuel : ℕ) (selected remaining : List alpha),
      (∀ t ∈ upperFailureTerms stop fuel selected remaining,
          stop (selected ++ t.1) = false) ∧
        (∀ t ∈ lowerFailureTerms stop fuel selected remaining,
          stop (selected ++ t.1) = false) := by
  intro fuel
  induction fuel with
  | zero =>
      intro selected remaining
      simp [upperFailureTerms, lowerFailureTerms]
  | succ fuel ih =>
      intro selected remaining
      constructor
      · intro t ht
        simp only [upperFailureTerms, List.mem_flatMap] at ht
        obtain ⟨q, _hq, ht⟩ := ht
        cases hstop : stop (selected ++ [q.1])
        · simp only [hstop, Bool.false_eq_true, ↓reduceIte,
              List.mem_singleton] at ht
          subst t
          simpa using hstop
        · simp only [hstop, ↓reduceIte, List.mem_map] at ht
          obtain ⟨u, hu, rfl⟩ := ht
          have hfinal := (ih (selected ++ [q.1]) q.2).2 u hu
          simpa [List.append_assoc] using hfinal
      · intro t ht
        simp only [lowerFailureTerms, List.mem_flatMap] at ht
        obtain ⟨q, _hq, ht⟩ := ht
        simp only [List.mem_map] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        have hfinal := (ih (selected ++ [q.1]) q.2).1 u hu
        simpa [List.append_assoc] using hfinal

/-- Root upper first-failure terms fail the transported arithmetic stopping
predicate on their selected chain. -/
theorem upperFailureTerms_not_descendingRosserStoppingPredicate
    {beta D fuel : ℕ} {remaining : List ℕ}
    {t : List ℕ × List ℕ}
    (ht : t ∈ upperFailureTerms (descendingRosserStop beta D)
      fuel [] remaining) :
    ¬ descendingRosserStoppingPredicate beta D t.1 := by
  have hfalse :=
    (failureTerms_final_failure (descendingRosserStop beta D)
      fuel [] remaining).1 t ht
  simpa using hfalse

/-- Root lower first-failure terms fail the transported arithmetic stopping
predicate on their selected chain. -/
theorem lowerFailureTerms_not_descendingRosserStoppingPredicate
    {beta D fuel : ℕ} {remaining : List ℕ}
    {t : List ℕ × List ℕ}
    (ht : t ∈ lowerFailureTerms (descendingRosserStop beta D)
      fuel [] remaining) :
    ¬ descendingRosserStoppingPredicate beta D t.1 := by
  have hfalse :=
    (failureTerms_final_failure (descendingRosserStop beta D)
      fuel [] remaining).2 t ht
  simpa using hfalse

/-! ## Smallest-prime and two-step geometry -/

/-- Failure at a chain ending in `q`, with every earlier selected prime at
most `y`, forces the displayed lower bound involving the smallest selected
prime `q`. -/
theorem pow_lt_pow_mul_smallest_of_stopping_failure
    {beta D y S q : ℕ} {head : List ℕ}
    (hD : D = y ^ S) (hhead : ∀ p ∈ head, p ≤ y)
    (hfail : ¬ descendingRosserStoppingPredicate beta D (head ++ [q])) :
    y ^ S < y ^ head.length * q ^ (beta + 1) := by
  have hfailure : D < head.prod * q ^ (beta + 1) := by
    have : ¬ head.prod * q ^ (beta + 1) ≤ D := by
      simpa [descendingRosserStoppingPredicate_append_singleton] using hfail
    omega
  have hprod : head.prod ≤ y ^ head.length := by
    calc
      head.prod ≤ (head.map fun _ ↦ y).prod := by
        simpa using (List.prod_le_prod' (l := head)
          (f := id) (g := fun _ ↦ y) (fun p hp ↦ hhead p (by simpa using hp)))
      _ = y ^ head.length := by simp
  rw [hD] at hfailure
  exact hfailure.trans_le (Nat.mul_le_mul_right _ hprod)

/-- Logarithmic cutoff extracted from the smallest-prime power inequality.
The denominator is the unused exponent budget `S - n`. -/
theorem log_div_log_smallest_lt_of_pow_lt
    {beta y S q n : ℕ} (hy : 1 < y) (hq : 1 < q) (hn : n < S)
    (hpow : y ^ S < y ^ n * q ^ (beta + 1)) :
    Real.log (y : ℝ) / Real.log (q : ℝ) <
      ((beta + 1 : ℕ) : ℝ) / ((S - n : ℕ) : ℝ) := by
  have hyR : (0 : ℝ) < y := by positivity
  have hqR : (0 : ℝ) < q := by positivity
  have hcast : ((y ^ S : ℕ) : ℝ) <
      ((y ^ n * q ^ (beta + 1) : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_lt_log
    (by positivity : (0 : ℝ) < ((y ^ S : ℕ) : ℝ)) hcast
  simp only [Nat.cast_pow, Nat.cast_mul, Real.log_pow,
    Real.log_mul (pow_ne_zero _ hyR.ne') (pow_ne_zero _ hqR.ne')] at hlog
  have hbudget : (0 : ℝ) < ((S - n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hn)
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq)
  have hmain : ((S - n : ℕ) : ℝ) * Real.log (y : ℝ) <
      ((beta + 1 : ℕ) : ℝ) * Real.log (q : ℝ) := by
    rw [Nat.cast_sub hn.le]
    linarith
  rw [div_lt_div_iff₀ hlogq hbudget]
  simpa [mul_comm] using hmain

/-- Direct smallest-selected-prime cutoff for a failed decreasing Rosser
chain at level `D = y^S`. -/
theorem log_div_log_smallest_lt_of_stopping_failure
    {beta D y S q : ℕ} {head : List ℕ}
    (hy : 1 < y) (hq : 1 < q) (hD : D = y ^ S)
    (hhead : ∀ p ∈ head, p ≤ y) (hlen : head.length < S)
    (hfail : ¬ descendingRosserStoppingPredicate beta D (head ++ [q])) :
    Real.log (y : ℝ) / Real.log (q : ℝ) <
      ((beta + 1 : ℕ) : ℝ) /
        ((S - head.length : ℕ) : ℝ) := by
  exact log_div_log_smallest_lt_of_pow_lt hy hq hlen
    (pow_lt_pow_mul_smallest_of_stopping_failure hD hhead hfail)

/-- In a failure term drawn from a strictly decreasing ambient prime list,
the final selected prime is strictly smaller than every earlier selection. -/
theorem failureTerm_last_is_smallest
    {remaining : List ℕ} {t : List ℕ × List ℕ}
    (hstructure : FailureTermStructure remaining t)
    (hdesc : remaining.Pairwise (fun p q ↦ q < p)) :
    ∃ (head : List ℕ) (q : ℕ), t.1 = head ++ [q] ∧
      ∀ p ∈ head, q < p := by
  obtain ⟨hsub, head, q, _before, hchain, _hsuffix⟩ := hstructure
  refine ⟨head, q, hchain, ?_⟩
  have hselected : t.1.Pairwise (fun p q ↦ q < p) :=
    (hdesc.sublist hsub).sublist (List.sublist_append_left t.1 t.2)
  rw [hchain, List.pairwise_append] at hselected
  intro p hp
  exact hselected.2.2 p hp q (by simp)

/-- Structural first-failure terms have a final selected prime, and the
global stopping failure gives the corresponding logarithmic cutoff.  The
ambient bound hypotheses are inherited by the selected sublist. -/
theorem failureTerm_exists_smallest_log_cutoff
    {beta D y S : ℕ} {remaining : List ℕ}
    {t : List ℕ × List ℕ}
    (hstructure : FailureTermStructure remaining t)
    (hy : 1 < y) (hlarge : ∀ p ∈ remaining, 1 < p)
    (hupper : ∀ p ∈ remaining, p ≤ y)
    (hD : D = y ^ S) (hlen : t.1.length ≤ S)
    (hfail : ¬ descendingRosserStoppingPredicate beta D t.1) :
    ∃ (head : List ℕ) (q : ℕ), t.1 = head ++ [q] ∧
      Real.log (y : ℝ) / Real.log (q : ℝ) <
        ((beta + 1 : ℕ) : ℝ) /
          ((S - head.length : ℕ) : ℝ) := by
  obtain ⟨hsub, head, q, _before, hchain, _hsuffix⟩ := hstructure
  refine ⟨head, q, hchain, ?_⟩
  have hqmem : q ∈ remaining := by
    apply hsub.subset
    simp [hchain]
  have hheadUpper : ∀ p ∈ head, p ≤ y := by
    intro p hp
    apply hupper p
    apply hsub.subset
    simp [hchain, hp]
  have hheadLength : head.length < S := by
    rw [hchain] at hlen
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  rw [hchain] at hfail
  exact log_div_log_smallest_lt_of_stopping_failure hy (hlarge q hqmem)
    hD hheadUpper hheadLength hfail

/-- Smallest-prime/log cutoff for a root upper first-failure term. -/
theorem upperFailureTerm_exists_smallest_log_cutoff
    {beta D y S fuel : ℕ} {remaining : List ℕ}
    {t : List ℕ × List ℕ}
    (ht : t ∈ upperFailureTerms (descendingRosserStop beta D)
      fuel [] remaining)
    (hy : 1 < y) (hlarge : ∀ p ∈ remaining, 1 < p)
    (hupper : ∀ p ∈ remaining, p ≤ y)
    (hD : D = y ^ S) (hlen : t.1.length ≤ S) :
    ∃ (head : List ℕ) (q : ℕ), t.1 = head ++ [q] ∧
      Real.log (y : ℝ) / Real.log (q : ℝ) <
        ((beta + 1 : ℕ) : ℝ) /
          ((S - head.length : ℕ) : ℝ) := by
  exact failureTerm_exists_smallest_log_cutoff
    ((failureTerms_structure (descendingRosserStop beta D)
      fuel [] remaining).1 t ht)
    hy hlarge hupper hD hlen
    (upperFailureTerms_not_descendingRosserStoppingPredicate ht)

/-- Smallest-prime/log cutoff for a root lower first-failure term. -/
theorem lowerFailureTerm_exists_smallest_log_cutoff
    {beta D y S fuel : ℕ} {remaining : List ℕ}
    {t : List ℕ × List ℕ}
    (ht : t ∈ lowerFailureTerms (descendingRosserStop beta D)
      fuel [] remaining)
    (hy : 1 < y) (hlarge : ∀ p ∈ remaining, 1 < p)
    (hupper : ∀ p ∈ remaining, p ≤ y)
    (hD : D = y ^ S) (hlen : t.1.length ≤ S) :
    ∃ (head : List ℕ) (q : ℕ), t.1 = head ++ [q] ∧
      Real.log (y : ℝ) / Real.log (q : ℝ) <
        ((beta + 1 : ℕ) : ℝ) /
          ((S - head.length : ℕ) : ℝ) := by
  exact failureTerm_exists_smallest_log_cutoff
    ((failureTerms_structure (descendingRosserStop beta D)
      fuel [] remaining).2 t ht)
    hy hlarge hupper hD hlen
    (lowerFailureTerms_not_descendingRosserStoppingPredicate ht)

/-- Comparison of two consecutive tested (same-parity) Rosser prefixes.
If the prefix ending in `p` passes, the extension ending two selections later
in `q` fails, and the intervening selected prime is at most `p`, then the
usual `(beta+1)/(beta-1)` loss follows already at the level of natural powers. -/
theorem pow_beta_sub_one_lt_pow_beta_add_one_of_two_step
    {beta D a p middle q : ℕ} (hbeta : 1 < beta)
    (ha : 0 < a) (hp : 0 < p) (hmiddle : middle ≤ p)
    (hpass : a * p ^ (beta + 1) ≤ D)
    (hfail : D < a * p * middle * q ^ (beta + 1)) :
    p ^ (beta - 1) < q ^ (beta + 1) := by
  have hcombined : a * p ^ (beta + 1) <
      a * (p * middle * q ^ (beta + 1)) := by
    calc
      a * p ^ (beta + 1) ≤ D := hpass
      _ < a * p * middle * q ^ (beta + 1) := hfail
      _ = a * (p * middle * q ^ (beta + 1)) := by ring
  have hcancelA : p ^ (beta + 1) <
      p * middle * q ^ (beta + 1) :=
    (Nat.mul_lt_mul_left ha).mp hcombined
  obtain ⟨beta', rfl⟩ : ∃ beta', beta = beta' + 2 := by
    exact ⟨beta - 2, by omega⟩
  have hmiddle' : middle * q ^ (beta' + 2 + 1) ≤
      p * q ^ (beta' + 2 + 1) :=
    Nat.mul_le_mul_right _ hmiddle
  have hcancelP : p ^ (beta' + 2) <
      middle * q ^ (beta' + 2 + 1) := by
    apply (Nat.mul_lt_mul_left hp).mp
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hcancelA
  have hpBound : p ^ (beta' + 2) <
      p * q ^ (beta' + 2 + 1) := hcancelP.trans_le hmiddle'
  apply (Nat.mul_lt_mul_right hp).mp
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hpBound

/-- Logarithmic form of the two-step Rosser loss. -/
theorem log_div_log_lt_beta_loss_of_pow
    {beta p q : ℕ} (hbeta : 1 < beta) (hp : 1 < p) (hq : 1 < q)
    (hpow : p ^ (beta - 1) < q ^ (beta + 1)) :
    Real.log (p : ℝ) / Real.log (q : ℝ) <
      ((beta + 1 : ℕ) : ℝ) / ((beta - 1 : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < p := by positivity
  have hqR : (0 : ℝ) < q := by positivity
  have hcast : ((p ^ (beta - 1) : ℕ) : ℝ) <
      ((q ^ (beta + 1) : ℕ) : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_lt_log (by positivity :
      (0 : ℝ) < ((p ^ (beta - 1) : ℕ) : ℝ)) hcast
  simp only [Nat.cast_pow, Real.log_pow] at hlog
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq)
  have hbetaR : (0 : ℝ) < ((beta - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < beta - 1 by omega)
  rw [div_lt_div_iff₀ hlogq hbetaR]
  simpa [mul_comm] using hlog

/-- At `beta = 100`, the preceding logarithmic loss is exactly
`betaRatio = 101/99`. -/
theorem log_div_log_lt_betaRatio_of_pow
    {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hpow : p ^ 99 < q ^ 101) :
    Real.log (p : ℝ) / Real.log (q : ℝ) < betaRatio := by
  simpa [betaRatio] using
    (log_div_log_lt_beta_loss_of_pow (beta := 100) (p := p) (q := q)
      (by norm_num) hp hq (by simpa using hpow))

/-! ## Euler-product bounds at a logarithmic cutoff -/

/-- The dimension-one Mertens estimate with its constant enlarged to be at
least one, as required by `betaDepthMajorant`. -/
theorem exists_oneShift_dimension_bound_one_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z y : ℕ, 2 ≤ z → z ≤ y →
      inverseLocalEulerProduct oneShiftDensity z y ≤
        A * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
  obtain ⟨C, hC, hdimension⟩ := exists_oneShift_dimension_bound
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro z y hz hzy
  have hratio : 0 ≤ Real.log (y : ℝ) / Real.log (z : ℝ) := by
    have hlogz : 0 < Real.log (z : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < z by omega))
    have hlogy : 0 ≤ Real.log (y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
    exact div_nonneg hlogy hlogz.le
  exact (hdimension z y hz hzy).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 C) hratio)

/-- The dimension-two estimate with its constant enlarged to be at least
one. -/
theorem exists_pairShift_dimension_bound_one_le :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ h z y : ℕ, 2 ≤ z → z ≤ y →
      inverseLocalEulerProduct (pairShiftDensity h) z y ≤
        A * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 2 := by
  obtain ⟨C, hC, hdimension⟩ := exists_pairShift_dimension_bound
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro h z y hz hzy
  have hratioSq : 0 ≤ (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 2 :=
    sq_nonneg _
  exact (hdimension h z y hz hzy).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 C) hratioSq)

/-- A cutoff `log y / log z ≤ betaRatio^r` converts the dimension-one
hypothesis into the exact power-ratio factor used at depth `r`. -/
theorem oneShift_inverseLocalEulerProduct_le_betaRatio_pow
    {A : ℝ} {z y r : ℕ}
    (hdimension : inverseLocalEulerProduct oneShiftDensity z y ≤
      A * (Real.log (y : ℝ) / Real.log (z : ℝ)))
    (hA : 0 ≤ A)
    (hcutoff : Real.log (y : ℝ) / Real.log (z : ℝ) ≤ betaRatio ^ r) :
    inverseLocalEulerProduct oneShiftDensity z y ≤ A * betaRatio ^ r := by
  exact hdimension.trans (mul_le_mul_of_nonneg_left hcutoff hA)

/-- The analogous dimension-two conversion. -/
theorem pairShift_inverseLocalEulerProduct_le_betaRatio_pow
    {A : ℝ} {h z y r : ℕ}
    (hdimension : inverseLocalEulerProduct (pairShiftDensity h) z y ≤
      A * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 2)
    (hA : 0 ≤ A)
    (hratio : 0 ≤ Real.log (y : ℝ) / Real.log (z : ℝ))
    (hcutoff : Real.log (y : ℝ) / Real.log (z : ℝ) ≤ betaRatio ^ r) :
    inverseLocalEulerProduct (pairShiftDensity h) z y ≤
      A * betaRatio ^ (2 * r) := by
  calc
    inverseLocalEulerProduct (pairShiftDensity h) z y ≤
        A * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 2 := hdimension
    _ ≤ A * (betaRatio ^ r) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hratio hcutoff 2) hA
    _ = A * betaRatio ^ (2 * r) := by rw [← pow_mul]; congr 2; omega

/-- Dimension-one cutoff bound written with the real power appearing in
`betaDepthMajorant`. -/
theorem oneShift_inverseLocalEulerProduct_le_betaRatio_rpow
    {A : ℝ} {z y r : ℕ}
    (hdimension : inverseLocalEulerProduct oneShiftDensity z y ≤
      A * (Real.log (y : ℝ) / Real.log (z : ℝ)))
    (hA : 0 ≤ A)
    (hcutoff : Real.log (y : ℝ) / Real.log (z : ℝ) ≤ betaRatio ^ r) :
    inverseLocalEulerProduct oneShiftDensity z y ≤
      A * Real.rpow betaRatio ((1 : ℝ) * r) := by
  simpa [Real.rpow_natCast] using
    (oneShift_inverseLocalEulerProduct_le_betaRatio_pow hdimension hA hcutoff)

/-- Dimension-two cutoff bound in the real-power form consumed by the
depth majorant. -/
theorem pairShift_inverseLocalEulerProduct_le_betaRatio_rpow
    {A : ℝ} {h z y r : ℕ}
    (hdimension : inverseLocalEulerProduct (pairShiftDensity h) z y ≤
      A * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 2)
    (hA : 0 ≤ A)
    (hratio : 0 ≤ Real.log (y : ℝ) / Real.log (z : ℝ))
    (hcutoff : Real.log (y : ℝ) / Real.log (z : ℝ) ≤ betaRatio ^ r) :
    inverseLocalEulerProduct (pairShiftDensity h) z y ≤
      A * Real.rpow betaRatio ((2 : ℝ) * r) := by
  calc
    inverseLocalEulerProduct (pairShiftDensity h) z y ≤
        A * betaRatio ^ (2 * r) :=
      pairShift_inverseLocalEulerProduct_le_betaRatio_pow
        hdimension hA hratio hcutoff
    _ = A * Real.rpow betaRatio ((2 : ℝ) * r) := by
      congr 1
      rw [show (2 : ℝ) * (r : ℝ) = ((2 * r : ℕ) : ℝ) by norm_num]
      exact (Real.rpow_natCast _ _).symm

/-- Uniform one-shift product-ratio bound at every cutoff satisfying the
beta-chain logarithmic budget. -/
theorem exists_oneShift_betaRatio_product_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z y r : ℕ, 2 ≤ z → z ≤ y →
      Real.log (y : ℝ) / Real.log (z : ℝ) ≤ betaRatio ^ r →
      inverseLocalEulerProduct oneShiftDensity z y ≤
        A * Real.rpow betaRatio ((1 : ℝ) * r) := by
  obtain ⟨A, hA, hdimension⟩ := exists_oneShift_dimension_bound_one_le
  refine ⟨A, hA, ?_⟩
  intro z y r hz hzy hcutoff
  exact oneShift_inverseLocalEulerProduct_le_betaRatio_rpow
    (hdimension z y hz hzy) (zero_le_one.trans hA) hcutoff

/-- Uniform pair-shift product-ratio bound in sieve dimension two. -/
theorem exists_pairShift_betaRatio_product_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ h z y r : ℕ, 2 ≤ z → z ≤ y →
      Real.log (y : ℝ) / Real.log (z : ℝ) ≤ betaRatio ^ r →
      inverseLocalEulerProduct (pairShiftDensity h) z y ≤
        A * Real.rpow betaRatio ((2 : ℝ) * r) := by
  obtain ⟨A, hA, hdimension⟩ := exists_pairShift_dimension_bound_one_le
  refine ⟨A, hA, ?_⟩
  intro h z y r hz hzy hcutoff
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  exact pairShift_inverseLocalEulerProduct_le_betaRatio_rpow
    (hdimension h z y hz hzy) (zero_le_one.trans hA)
      (div_nonneg hlogy hlogz.le) hcutoff

/-! ## Concrete product-ratio depth estimates -/

/-- The dimension-one interval estimate and the logarithmic density bound
combine to give exactly the factorial depth term used by the beta-100 tail.
Unlike `HasDepthProductRatio`, all hypotheses are endpoint Euler-product
statements furnished by `LocalEulerProducts`. -/
theorem oneShift_productRatio_factorialDepth_le
    {A : ℝ} {z y r : ℕ} (hA : 1 ≤ A)
    (hdimension : inverseLocalEulerProduct oneShiftDensity z y ≤
      A * (Real.log (y : ℝ) / Real.log (z : ℝ)))
    (hcutoff : Real.log (y : ℝ) / Real.log (z : ℝ) ≤ betaRatio ^ r) :
    inverseLocalEulerProduct oneShiftDensity z y *
          (∑ p ∈ sievePrimes z y, oneShiftDensity p) ^ r /
          (r.factorial : ℝ) ≤
        betaDepthMajorant A 1 r := by
  have hIpos : 0 < inverseLocalEulerProduct oneShiftDensity z y := by
    unfold inverseLocalEulerProduct
    apply Finset.prod_pos
    intro p hp
    exact inv_pos.mpr
      (oneShift_localFactor_pos (mem_sievePrimes.mp hp).2.2)
  have hL0 : 0 ≤ ∑ p ∈ sievePrimes z y, oneShiftDensity p := by
    apply Finset.sum_nonneg
    intro p hp
    exact (oneShiftDensity_pos (mem_sievePrimes.mp hp).2.2).le
  have hsum : (∑ p ∈ sievePrimes z y, oneShiftDensity p) ≤
      Real.log (inverseLocalEulerProduct oneShiftDensity z y) := by
    apply sum_density_le_log_inverseLocalEulerProduct
    intro p hp
    exact oneShiftDensity_lt_one (mem_sievePrimes.mp hp).2.2
  exact productRatio_factorialTerm_le_betaDepthMajorant r hA hIpos hL0
    (oneShift_inverseLocalEulerProduct_le_betaRatio_rpow
      hdimension (zero_le_one.trans hA) hcutoff) hsum

/-- Concrete dimension-two version of
`oneShift_productRatio_factorialDepth_le`, uniform in the difference `h`.
The lower endpoint `z ≥ 2` removes the sole exceptional local factor at
the prime two. -/
theorem pairShift_productRatio_factorialDepth_le
    {A : ℝ} {h z y r : ℕ} (hA : 1 ≤ A) (hz : 2 ≤ z)
    (hdimension : inverseLocalEulerProduct (pairShiftDensity h) z y ≤
      A * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 2)
    (hratio : 0 ≤ Real.log (y : ℝ) / Real.log (z : ℝ))
    (hcutoff : Real.log (y : ℝ) / Real.log (z : ℝ) ≤ betaRatio ^ r) :
    inverseLocalEulerProduct (pairShiftDensity h) z y *
          (∑ p ∈ sievePrimes z y, pairShiftDensity h p) ^ r /
          (r.factorial : ℝ) ≤
        betaDepthMajorant A 2 r := by
  have hIpos : 0 < inverseLocalEulerProduct (pairShiftDensity h) z y := by
    unfold inverseLocalEulerProduct
    apply Finset.prod_pos
    intro p hp
    have hp' := mem_sievePrimes.mp hp
    exact inv_pos.mpr (pairShift_localFactor_pos hp'.2.2 (by omega))
  have hL0 : 0 ≤ ∑ p ∈ sievePrimes z y, pairShiftDensity h p := by
    apply Finset.sum_nonneg
    intro p hp
    exact (pairShiftDensity_pos (mem_sievePrimes.mp hp).2.2).le
  have hsum : (∑ p ∈ sievePrimes z y, pairShiftDensity h p) ≤
      Real.log (inverseLocalEulerProduct (pairShiftDensity h) z y) := by
    apply sum_density_le_log_inverseLocalEulerProduct
    intro p hp
    have hp' := mem_sievePrimes.mp hp
    exact pairShiftDensity_lt_one hp'.2.2 (by omega)
  exact productRatio_factorialTerm_le_betaDepthMajorant r hA hIpos hL0
    (pairShift_inverseLocalEulerProduct_le_betaRatio_rpow
      hdimension (zero_le_one.trans hA) hratio hcutoff) hsum

/-- Uniform, assumption-free dimension-one product-ratio/depth constant.
Only the explicit endpoint and beta-chain cutoff conditions remain at use
sites; the Mertens product-ratio estimate is discharged here. -/
theorem exists_oneShift_productRatio_factorialDepth_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z y r : ℕ, 2 ≤ z → z ≤ y →
      Real.log (y : ℝ) / Real.log (z : ℝ) ≤ betaRatio ^ r →
      inverseLocalEulerProduct oneShiftDensity z y *
            (∑ p ∈ sievePrimes z y, oneShiftDensity p) ^ r /
            (r.factorial : ℝ) ≤
          betaDepthMajorant A 1 r := by
  obtain ⟨A, hA, hdimension⟩ := exists_oneShift_dimension_bound_one_le
  refine ⟨A, hA, ?_⟩
  intro z y r hz hzy hcutoff
  exact oneShift_productRatio_factorialDepth_le hA
    (hdimension z y hz hzy) hcutoff

/-- Uniform dimension-two product-ratio/depth constant, independent of the
pair difference `h`. -/
theorem exists_pairShift_productRatio_factorialDepth_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ h z y r : ℕ, 2 ≤ z → z ≤ y →
      Real.log (y : ℝ) / Real.log (z : ℝ) ≤ betaRatio ^ r →
      inverseLocalEulerProduct (pairShiftDensity h) z y *
            (∑ p ∈ sievePrimes z y, pairShiftDensity h p) ^ r /
            (r.factorial : ℝ) ≤
          betaDepthMajorant A 2 r := by
  obtain ⟨A, hA, hdimension⟩ := exists_pairShift_dimension_bound_one_le
  refine ⟨A, hA, ?_⟩
  intro h z y r hz hzy hcutoff
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  exact pairShift_productRatio_factorialDepth_le hA hz
    (hdimension h z y hz hzy) (div_nonneg hlogy hlogz.le) hcutoff

end Erdos851.BetaSieveFundamental

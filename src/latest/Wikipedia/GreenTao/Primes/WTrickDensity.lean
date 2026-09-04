import Wikipedia.SzemeredisTheorem.Finite.Mean
import Wikipedia.GreenTao.Parameters
import Wikipedia.GreenTao.Primes.Chebyshev
import Wikipedia.GreenTao.Primes.ReducedResidues
import Wikipedia.GreenTao.Primes.WTrick

/-!
# From primes in a quarter interval to a dense W-tricked prime weight

This file supplies the finite arithmetic bridge in the `W`-trick.  We take
`X = W * (N / 8)`, choose one reduced class among the primes in `(X / 4, X]`,
and send a prime `p` in that class to `(p - b) / W`.  The generous constants
in `greenTaoInterval` make this quotient lie in `[N / 64, N / 4]`.
-/

namespace Wikipedia.SzemeredisTheorem

open Finset Real Filter
open scoped BigOperators

/-- The scale at which primes are sampled before applying the `W`-trick. -/
def wTrickPrimeScale (W N : ℕ) : ℕ :=
  W * (N / 8)

/-- The primes in `(X / 4, X]`, where `X = W * (N / 8)`, which lie in the
standard residue class `b` modulo `W`. -/
def quarterIntervalResidueClass (W N b : ℕ) : Finset ℕ :=
  residueFiber (primesInQuarterInterval (wTrickPrimeScale W N)) W b

@[simp]
theorem mem_quarterIntervalResidueClass {W N b p : ℕ} :
    p ∈ quarterIntervalResidueClass W N b ↔
      p.Prime ∧
        wTrickPrimeScale W N / 4 < p ∧
        p ≤ wTrickPrimeScale W N ∧
        p % W = b := by
  simp only [quarterIntervalResidueClass, mem_residueFiber,
    mem_primesInQuarterInterval]
  tauto

/-- The natural parameter underlying a prime in residue class `b`. -/
def untrickPrime (W b p : ℕ) : ℕ :=
  (p - b) / W

/-- The same parameter, regarded as an element of the cyclic group. -/
def untrickPrimeZMod (N W b p : ℕ) : ZMod N :=
  (untrickPrime W b p : ℕ)

/-- On an actual residue class, subtracting the residue before division gives
the ordinary quotient. -/
theorem untrickPrime_eq_div {W b p : ℕ} (hW : 0 < W)
    (hmod : p % W = b) :
    untrickPrime W b p = p / W := by
  have hb : b ≤ p := by
    rw [← hmod]
    exact Nat.mod_le p W
  have hdecomp : W * (p / W) + b = p := by
    simpa [hmod] using Nat.div_add_mod p W
  have hsub : p - b = W * (p / W) := by
    omega
  rw [untrickPrime, hsub, Nat.mul_div_cancel_left _ hW]

/-- Reapplying the affine `W`-trick recovers the original natural number. -/
theorem w_mul_untrickPrime_add {W b p : ℕ} (hW : 0 < W)
    (hmod : p % W = b) :
    W * untrickPrime W b p + b = p := by
  rw [untrickPrime_eq_div hW hmod]
  simpa [hmod] using Nat.div_add_mod p W

/-- The lower endpoint `W * (N / 32)` lies below the quarter-scale cutoff. -/
theorem w_mul_div_thirtyTwo_le_scale_div_four (W N : ℕ) :
    W * (N / 32) ≤ wTrickPrimeScale W N / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < (4 : ℕ))]
  have hdiv : 4 * (N / 32) ≤ N / 8 := by
    omega
  calc
    W * (N / 32) * 4 = W * (4 * (N / 32)) := by ring
    _ ≤ W * (N / 8) := Nat.mul_le_mul_left W hdiv
    _ = wTrickPrimeScale W N := rfl

/-- A prime in the selected quarter-interval class maps into the fixed
Green--Tao interval. -/
theorem untrickPrime_mem_greenTaoInterval {W N b p : ℕ}
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    untrickPrime W b p ∈ greenTaoInterval N := by
  have hdata := mem_quarterIntervalResidueClass.mp hp
  have hquot : untrickPrime W b p = p / W :=
    untrickPrime_eq_div hW hdata.2.2.2
  rw [mem_greenTaoInterval, hquot]
  constructor
  · rw [Nat.le_div_iff_mul_le hW]
    calc
      N / 64 * W ≤ W * (N / 32) := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left W (by omega)
      _ ≤ wTrickPrimeScale W N / 4 :=
        w_mul_div_thirtyTwo_le_scale_div_four W N
      _ ≤ p := hdata.2.1.le
  · have hpdiv : p / W ≤ N / 8 := by
      apply Nat.div_le_of_le_mul
      simpa [wTrickPrimeScale, Nat.mul_comm] using hdata.2.2.1
    exact hpdiv.trans (by omega)

/-- The untricked parameter is a standard representative modulo `N`. -/
theorem untrickPrime_lt {W N b p : ℕ} [NeZero N]
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    untrickPrime W b p < N := by
  have hmem := mem_greenTaoInterval.mp
    (untrickPrime_mem_greenTaoInterval hW hp)
  exact hmem.2.trans_lt
    (Nat.div_lt_self (NeZero.pos N) (by norm_num))

/-- Casting an untricked parameter into `ZMod N` does not change its
standard representative. -/
@[simp]
theorem val_untrickPrimeZMod {W N b p : ℕ} [NeZero N]
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    (untrickPrimeZMod N W b p).val = untrickPrime W b p := by
  exact ZMod.val_natCast_of_lt (untrickPrime_lt hW hp)

/-- The cyclic-group affine value of the untricked parameter is the original
prime. -/
@[simp]
theorem wTrickedValue_untrickPrimeZMod {W N b p : ℕ} [NeZero N]
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    wTrickedValue W b (untrickPrimeZMod N W b p) = p := by
  rw [wTrickedValue, val_untrickPrimeZMod hW hp]
  exact w_mul_untrickPrime_add hW
    (mem_quarterIntervalResidueClass.mp hp).2.2.2

/-- Distinct primes in the chosen residue class give distinct elements of
`ZMod N`. -/
theorem untrickPrimeZMod_injOn {W N b : ℕ} [NeZero N]
    (hW : 0 < W) :
    Set.InjOn (untrickPrimeZMod N W b)
      (quarterIntervalResidueClass W N b) := by
  intro p hp q hq hpq
  calc
    p = wTrickedValue W b (untrickPrimeZMod N W b p) :=
      (wTrickedValue_untrickPrimeZMod hW hp).symm
    _ = wTrickedValue W b (untrickPrimeZMod N W b q) := by rw [hpq]
    _ = q := wTrickedValue_untrickPrimeZMod hW hq

/-- The image of the selected primes inside the cyclic group. -/
def untrickedPrimeResidues (N W b : ℕ) : Finset (ZMod N) :=
  (quarterIntervalResidueClass W N b).image
    (untrickPrimeZMod N W b)

/-- No primes are lost when the selected class is embedded into `ZMod N`. -/
@[simp]
theorem card_untrickedPrimeResidues {W N b : ℕ} [NeZero N]
    (hW : 0 < W) :
    #(untrickedPrimeResidues N W b) =
      #(quarterIntervalResidueClass W N b) := by
  exact Finset.card_image_of_injOn (untrickPrimeZMod_injOn hW)

/-- Exact value of the localized prime weight on an untricked prime. -/
@[simp]
theorem wTrickedPrimeWeight_untrickPrimeZMod
    {W N b p : ℕ} [NeZero N] (α : ℝ)
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    wTrickedPrimeWeight α W b (untrickPrimeZMod N W b p) =
      α * ((W.totient : ℝ) / W) * log p := by
  have hmem :
      (untrickPrimeZMod N W b p).val ∈ greenTaoInterval N := by
    simpa [val_untrickPrimeZMod hW hp] using
      untrickPrime_mem_greenTaoInterval hW hp
  have hprime :
      Nat.Prime
        (wTrickedValue W b (untrickPrimeZMod N W b p)) := by
    simpa [wTrickedValue_untrickPrimeZMod hW hp] using
      (mem_quarterIntervalResidueClass.mp hp).1
  rw [wTrickedPrimeWeight_eq α W b _ hmem hprime,
    wTrickedValue_untrickPrimeZMod hW hp]

/-- Exact logarithmic mass carried by the embedded prime class. -/
theorem sum_untrickedPrimeResidues_weight
    {W N b : ℕ} [NeZero N] (α : ℝ) (hW : 0 < W) :
    ∑ n ∈ untrickedPrimeResidues N W b,
        wTrickedPrimeWeight α W b n =
      α * ((W.totient : ℝ) / W) *
        ∑ p ∈ quarterIntervalResidueClass W N b, log p := by
  rw [untrickedPrimeResidues,
    Finset.sum_image (untrickPrimeZMod_injOn hW)]
  calc
    ∑ p ∈ quarterIntervalResidueClass W N b,
          wTrickedPrimeWeight α W b (untrickPrimeZMod N W b p) =
        ∑ p ∈ quarterIntervalResidueClass W N b,
          α * ((W.totient : ℝ) / W) * log p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact wTrickedPrimeWeight_untrickPrimeZMod α hW hp
    _ = α * ((W.totient : ℝ) / W) *
          ∑ p ∈ quarterIntervalResidueClass W N b, log p := by
      rw [Finset.mul_sum]

/-- The full cyclic sum dominates the exact logarithmic mass of the selected
prime class. -/
theorem selected_log_mass_le_sum_wTrickedPrimeWeight
    {W N b : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α) (hW : 0 < W) :
    α * ((W.totient : ℝ) / W) *
          ∑ p ∈ quarterIntervalResidueClass W N b, log p ≤
      ∑ n : ZMod N, wTrickedPrimeWeight α W b n := by
  rw [← sum_untrickedPrimeResidues_weight α hW]
  exact Finset.sum_le_univ_sum_of_nonneg
    (wTrickedPrimeWeight_nonneg hα W b)

/-- Mean form of the exact finite logarithmic-mass lower bound. -/
theorem selected_log_mass_div_card_le_mean
    {W N b : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α) (hW : 0 < W) :
    (α * ((W.totient : ℝ) / W) *
          ∑ p ∈ quarterIntervalResidueClass W N b, log p) / N ≤
      mean (wTrickedPrimeWeight α W b : ZMod N → ℝ) := by
  rw [mean, Fintype.expect_eq_sum_div_card, ZMod.card]
  exact div_le_div_of_nonneg_right
    (selected_log_mass_le_sum_wTrickedPrimeWeight hα hW)
    (Nat.cast_nonneg N)

/-- Every prime in the selected class contributes at least the logarithm of
the first integer strictly above the quarter-scale cutoff. -/
theorem card_mul_log_cutoff_le_selected_log_mass
    {W N b : ℕ} :
    (#(quarterIntervalResidueClass W N b) : ℝ) *
        log (wTrickPrimeScale W N / 4 + 1 : ℕ) ≤
      ∑ p ∈ quarterIntervalResidueClass W N b, log p := by
  calc
    (#(quarterIntervalResidueClass W N b) : ℝ) *
          log (wTrickPrimeScale W N / 4 + 1 : ℕ) =
        ∑ _p ∈ quarterIntervalResidueClass W N b,
          log (wTrickPrimeScale W N / 4 + 1 : ℕ) := by simp
    _ ≤ ∑ p ∈ quarterIntervalResidueClass W N b, log p := by
      apply Finset.sum_le_sum
      intro p hp
      apply Real.log_le_log
      · positivity
      · exact_mod_cast Nat.succ_le_iff.mpr
          (mem_quarterIntervalResidueClass.mp hp).2.1

/-- A cardinality lower bound for one prime class gives a fully explicit
lower bound for the mean W-tricked prime weight. -/
theorem card_class_mean_lower_bound
    {W N b : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α) (hW : 0 < W) :
    (α * ((W.totient : ℝ) / W) *
        ((#(quarterIntervalResidueClass W N b) : ℝ) *
          log (wTrickPrimeScale W N / 4 + 1 : ℕ))) / N ≤
      mean (wTrickedPrimeWeight α W b : ZMod N → ℝ) := by
  calc
    _ ≤
        (α * ((W.totient : ℝ) / W) *
          ∑ p ∈ quarterIntervalResidueClass W N b, log p) / N := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left
          card_mul_log_cutoff_le_selected_log_mass
          (mul_nonneg hα
            (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      · exact Nat.cast_nonneg N
    _ ≤ mean (wTrickedPrimeWeight α W b : ZMod N → ℝ) :=
      selected_log_mass_div_card_le_mean hα hW

/-- Pigeonhole the quarter-interval primes into reduced residue classes.
The sole size hypothesis says that every sampled prime is larger than `w`. -/
theorem exists_reducedResidue_quarterInterval_card_bound
    {w N : ℕ}
    (hw : w ≤ wTrickPrimeScale (primorial w) N / 4) :
    ∃ b ∈ reducedResidues (primorial w),
      #(primesInQuarterInterval
          (wTrickPrimeScale (primorial w) N)) ≤
        (primorial w).totient *
          #(quarterIntervalResidueClass (primorial w) N b) := by
  simpa [quarterIntervalResidueClass] using
    exists_reducedResidue_for_primes_above
      (primesInQuarterInterval
        (wTrickPrimeScale (primorial w) N))
      (fun p hp ↦ (mem_primesInQuarterInterval.mp hp).1)
      (fun p hp ↦ hw.trans_lt
        (mem_primesInQuarterInterval.mp hp).2.1)

/-- Exact Chebyshev-to-mean bridge before inserting the analytic prime-count
bound.  The totient introduced by pigeonholing cancels the totient in the
normalization, leaving only `W` in the denominator. -/
theorem exists_reducedResidue_mean_lower_bound
    {w N : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α)
    (hw : w ≤ wTrickPrimeScale (primorial w) N / 4) :
    ∃ b ∈ reducedResidues (primorial w),
      (((α / (primorial w : ℝ)) *
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) ≤
        mean
          (wTrickedPrimeWeight α (primorial w) b :
            ZMod N → ℝ) := by
  obtain ⟨b, hb, hcard⟩ :=
    exists_reducedResidue_quarterInterval_card_bound hw
  refine ⟨b, hb, ?_⟩
  have hcardReal :
      (#(primesInQuarterInterval
          (wTrickPrimeScale (primorial w) N)) : ℝ) ≤
        ((primorial w).totient : ℝ) *
          (#(quarterIntervalResidueClass (primorial w) N b) : ℝ) := by
    exact_mod_cast hcard
  let L : ℝ :=
    log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by
      exact_mod_cast
        (show 1 ≤ wTrickPrimeScale (primorial w) N / 4 + 1 by omega))
  have hscale : 0 ≤ (α / (primorial w : ℝ)) * L :=
    mul_nonneg
      (div_nonneg hα (Nat.cast_nonneg _)) hL
  have hscaled :=
    mul_le_mul_of_nonneg_left hcardReal hscale
  calc
    ((α / (primorial w : ℝ)) *
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N =
        (((α / (primorial w : ℝ)) * L) *
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ)) / N := by
      dsimp [L]
      ring
    _ ≤
        (((α / (primorial w : ℝ)) * L) *
          (((primorial w).totient : ℝ) *
            (#(quarterIntervalResidueClass
              (primorial w) N b) : ℝ))) / N := by
      exact div_le_div_of_nonneg_right hscaled (Nat.cast_nonneg N)
    _ =
        (α * (((primorial w).totient : ℝ) / primorial w) *
          ((#(quarterIntervalResidueClass
              (primorial w) N b) : ℝ) *
            log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ))) / N := by
      dsimp [L]
      ring
    _ ≤ mean
          (wTrickedPrimeWeight α (primorial w) b :
            ZMod N → ℝ) :=
      card_class_mean_lower_bound hα (primorial_pos w)

/-- Insert the quantitative Chebyshev estimate at
`X = primorial w * (N / 8)` into the exact finite bridge. -/
theorem exists_reducedResidue_chebyshev_mean_lower_bound
    {w N : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α)
    (hw : w ≤ wTrickPrimeScale (primorial w) N / 4)
    (hchebyshev :
      log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
          log (wTrickPrimeScale (primorial w) N) ≤
        (#(primesInQuarterInterval
          (wTrickPrimeScale (primorial w) N)) : ℝ)) :
    ∃ b ∈ reducedResidues (primorial w),
      (((α / (primorial w : ℝ)) *
          (log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N)) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) ≤
        mean
          (wTrickedPrimeWeight α (primorial w) b :
            ZMod N → ℝ) := by
  obtain ⟨b, hb, hmean⟩ :=
    exists_reducedResidue_mean_lower_bound hα hw
  refine ⟨b, hb, ?_⟩
  let L : ℝ :=
    log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by
      exact_mod_cast
        (show 1 ≤ wTrickPrimeScale (primorial w) N / 4 + 1 by omega))
  have hscale : 0 ≤ (α / (primorial w : ℝ)) * L :=
    mul_nonneg
      (div_nonneg hα (Nat.cast_nonneg _)) hL
  have hscaled :=
    mul_le_mul_of_nonneg_left hchebyshev hscale
  calc
    (((α / (primorial w : ℝ)) *
          (log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N)) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) =
        (((α / (primorial w : ℝ)) * L) *
          (log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N))) / N := by
      dsimp [L]
      ring
    _ ≤
        (((α / (primorial w : ℝ)) * L) *
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ)) / N := by
      exact div_le_div_of_nonneg_right hscaled (Nat.cast_nonneg N)
    _ =
        (((α / (primorial w : ℝ)) *
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) := by
      dsimp [L]
      ring
    _ ≤ mean
          (wTrickedPrimeWeight α (primorial w) b :
            ZMod N → ℝ) :=
      hmean

/-- Once the scale is at least four, the quantitative Chebyshev estimate
forces the mean W-tricked prime weight to be strictly positive. -/
theorem exists_reducedResidue_mean_pos_of_chebyshev
    {w N : ℕ} [NeZero N] {α : ℝ} (hα : 0 < α)
    (hw : w ≤ wTrickPrimeScale (primorial w) N / 4)
    (hscale : 4 ≤ wTrickPrimeScale (primorial w) N)
    (hchebyshev :
      log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
          log (wTrickPrimeScale (primorial w) N) ≤
        (#(primesInQuarterInterval
          (wTrickPrimeScale (primorial w) N)) : ℝ)) :
    ∃ b ∈ reducedResidues (primorial w),
      0 < mean
        (wTrickedPrimeWeight α (primorial w) b :
          ZMod N → ℝ) := by
  obtain ⟨b, hb, hmean⟩ :=
    exists_reducedResidue_chebyshev_mean_lower_bound hα.le hw hchebyshev
  refine ⟨b, hb, ?_⟩
  have hWreal : 0 < (primorial w : ℝ) := by
    exact_mod_cast primorial_pos w
  have hXreal :
      0 < (wTrickPrimeScale (primorial w) N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (4 : ℕ)) hscale)
  have hlogX :
      0 < log (wTrickPrimeScale (primorial w) N : ℝ) :=
    Real.log_pos (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (4 : ℕ)) hscale))
  have hcutoff :
      1 <
        ((wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show
      1 < wTrickPrimeScale (primorial w) N / 4 + 1 by
        rw [Nat.lt_succ_iff]
        exact (Nat.le_div_iff_mul_le (by norm_num : 0 < (4 : ℕ))).2
          (by simpa using hscale))
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast NeZero.pos N
  have hlower :
      0 <
        (((α / (primorial w : ℝ)) *
          (log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N)) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) := by
    exact div_pos
      (mul_pos
        (mul_pos
          (div_pos hα hWreal)
          (div_pos
            (mul_pos log_two_div_four_pos hXreal)
            hlogX))
        (Real.log_pos hcutoff))
      hNreal
  exact hlower.trans_le hmean

/-- For every positive `W`, the scale `W * (N / 8)` tends to infinity with
`N`.  This is the elementary reindexing fact needed to pull back the
Chebyshev estimate. -/
theorem tendsto_wTrickPrimeScale_atTop {W : ℕ} (hW : 0 < W) :
    Tendsto (wTrickPrimeScale W) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  filter_upwards [eventually_ge_atTop (8 * K)] with N hN
  have hK : K ≤ N / 8 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < (8 : ℕ))]
    simpa [Nat.mul_comm] using hN
  have hOne : 1 ≤ W := hW
  calc
    K ≤ N / 8 := hK
    _ = 1 * (N / 8) := by simp
    _ ≤ W * (N / 8) := Nat.mul_le_mul_right (N / 8) hOne
    _ = wTrickPrimeScale W N := rfl

/-- Past the first nontrivial block, the loss from flooring `N / 8` costs
at most a factor two. -/
theorem nat_le_sixteen_mul_div_eight
    {N : ℕ} (hN : 16 ≤ N) :
    N ≤ 16 * (N / 8) := by
  omega

/-- For `X ≥ 16`, the integer just above `X / 4` has square at least `X`.
This is a convenient floor-safe input to the logarithmic ratio estimate. -/
theorem le_div_four_add_one_sq
    {X : ℕ} (hX : 16 ≤ X) :
    X ≤ (X / 4 + 1) ^ 2 := by
  have hquot : 4 ≤ X / 4 := by
    omega
  have hupper : X ≤ 4 * (X / 4) + 3 := by
    omega
  nlinarith

/-- The logarithm at the quarter-scale cutoff retains at least half of
`log X` once `X ≥ 16`. -/
theorem half_le_log_quarter_cutoff_div_log
    {X : ℕ} (hX : 16 ≤ X) :
    (1 / 2 : ℝ) ≤
      log (X / 4 + 1 : ℕ) / log X := by
  have hXreal : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (16 : ℕ)) hX)
  have hlogX : 0 < log (X : ℝ) :=
    Real.log_pos hXreal
  have hsqReal :
      (X : ℝ) ≤ ((X / 4 + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast le_div_four_add_one_sq hX
  have hlog :
      log (X : ℝ) ≤
        log (((X / 4 + 1 : ℕ) : ℝ) ^ 2) :=
    Real.log_le_log (by positivity) hsqReal
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ hlogX]
  norm_num [Nat.cast_add] at hlog ⊢
  linarith

/-- The W-trick scale divided by `N` retains at least `W / 16` after the
floor in `N / 8`. -/
theorem w_div_sixteen_le_scale_div
    (W : ℕ) {N : ℕ} (hN : 16 ≤ N) :
    (W : ℝ) / 16 ≤
      (wTrickPrimeScale W N : ℝ) / N := by
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ)) hN)
  have hnat :
      W * N ≤ wTrickPrimeScale W N * 16 := by
    calc
      W * N ≤ W * (16 * (N / 8)) :=
        Nat.mul_le_mul_left W (nat_le_sixteen_mul_div_eight hN)
      _ = wTrickPrimeScale W N * 16 := by
        simp [wTrickPrimeScale]
        ring
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 16) hNreal]
  exact_mod_cast hnat

/-- Uniform lower bound for the explicit Chebyshev expression used in the
W-tricked density argument. -/
theorem chebyshev_wTrick_lower_bound
    {W N : ℕ} (hW : 0 < W)
    {α : ℝ} (hα : 0 ≤ α)
    (hN : 16 ≤ N)
    (hscale : 16 ≤ wTrickPrimeScale W N) :
    α * log 2 / 128 ≤
      (((α / (W : ℝ)) *
          (log 2 / 4 * (wTrickPrimeScale W N : ℝ) /
            log (wTrickPrimeScale W N)) *
          log (wTrickPrimeScale W N / 4 + 1 : ℕ)) / N) := by
  let X : ℕ := wTrickPrimeScale W N
  have hWreal : (0 : ℝ) < W := by
    exact_mod_cast hW
  have hratio :
      (W : ℝ) / 16 ≤ (X : ℝ) / N := by
    exact w_div_sixteen_le_scale_div W hN
  have hscaled :
      α / 16 ≤
        (α / (W : ℝ)) * ((X : ℝ) / N) := by
    calc
      α / 16 =
          (α / (W : ℝ)) * ((W : ℝ) / 16) := by
        field_simp
      _ ≤ (α / (W : ℝ)) * ((X : ℝ) / N) :=
        mul_le_mul_of_nonneg_left hratio
          (div_nonneg hα hWreal.le)
  have hlogRatio :
      (1 / 2 : ℝ) ≤
        log (X / 4 + 1 : ℕ) / log X :=
    half_le_log_quarter_cutoff_div_log hscale
  have hlogConst : 0 ≤ log 2 / 4 :=
    log_two_div_four_pos.le
  have hscaledLog :
      (α / 16) * (log 2 / 4) ≤
        ((α / (W : ℝ)) * ((X : ℝ) / N)) *
          (log 2 / 4) :=
    mul_le_mul_of_nonneg_right hscaled hlogConst
  calc
    α * log 2 / 128 =
        ((α / 16) * (log 2 / 4)) * (1 / 2) := by
      ring
    _ ≤
        (((α / (W : ℝ)) * ((X : ℝ) / N)) *
          (log 2 / 4)) *
            (log (X / 4 + 1 : ℕ) / log X) := by
      exact mul_le_mul hscaledLog hlogRatio
        (by norm_num) (mul_nonneg
          (mul_nonneg (div_nonneg hα hWreal.le)
            (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
          hlogConst)
    _ =
        (((α / (W : ℝ)) *
          (log 2 / 4 * (X : ℝ) / log X) *
          log (X / 4 + 1 : ℕ)) / N) := by
      ring

/-- Pulled-back Green--Tao density statement with a locally supplied
`NeZero N` instance.  For every sufficiently large positive natural `N`,
one reduced residue modulo `primorial w` has strictly positive W-tricked
prime mean. -/
theorem eventually_forall_pos_exists_reducedResidue_mean_pos
    {w : ℕ} {α : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop,
      ∀ hN : 0 < N,
        letI : NeZero N := ⟨hN.ne'⟩
        ∃ b ∈ reducedResidues (primorial w),
          0 < mean
            (wTrickedPrimeWeight α (primorial w) b :
              ZMod N → ℝ) := by
  have hscaleTends :
      Tendsto (wTrickPrimeScale (primorial w)) atTop atTop :=
    tendsto_wTrickPrimeScale_atTop (primorial_pos w)
  have hchebyshev :
      ∀ᶠ N : ℕ in atTop,
        log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N) ≤
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ) :=
    hscaleTends.eventually
      eventually_log_two_div_four_mul_div_log_le_card
  have hscaleFour :
      ∀ᶠ N : ℕ in atTop,
        4 ≤ wTrickPrimeScale (primorial w) N :=
    hscaleTends.eventually (eventually_ge_atTop 4)
  have hscaleFourW :
      ∀ᶠ N : ℕ in atTop,
        4 * w ≤ wTrickPrimeScale (primorial w) N :=
    hscaleTends.eventually (eventually_ge_atTop (4 * w))
  filter_upwards [hchebyshev, hscaleFour, hscaleFourW] with
    N hchebyshev hscaleFour hscaleFourW
  intro hN
  let : NeZero N := ⟨hN.ne'⟩
  apply exists_reducedResidue_mean_pos_of_chebyshev
    hα
  · exact (Nat.le_div_iff_mul_le (by norm_num : 0 < (4 : ℕ))).2
      (by simpa [Nat.mul_comm] using hscaleFourW)
  · exact hscaleFour
  · exact hchebyshev

/-- Uniform-density strengthening of
`eventually_forall_pos_exists_reducedResidue_mean_pos`: the lower bound is
independent of `N`. -/
theorem eventually_forall_pos_exists_reducedResidue_mean_ge
    {w : ℕ} {α : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop,
      ∀ hN : 0 < N,
        letI : NeZero N := ⟨hN.ne'⟩
        ∃ b ∈ reducedResidues (primorial w),
          α * log 2 / 128 ≤
            mean
              (wTrickedPrimeWeight α (primorial w) b :
                ZMod N → ℝ) := by
  have hscaleTends :
      Tendsto (wTrickPrimeScale (primorial w)) atTop atTop :=
    tendsto_wTrickPrimeScale_atTop (primorial_pos w)
  have hchebyshev :
      ∀ᶠ N : ℕ in atTop,
        log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N) ≤
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ) :=
    hscaleTends.eventually
      eventually_log_two_div_four_mul_div_log_le_card
  have hscaleSixteen :
      ∀ᶠ N : ℕ in atTop,
        16 ≤ wTrickPrimeScale (primorial w) N :=
    hscaleTends.eventually (eventually_ge_atTop 16)
  have hscaleFourW :
      ∀ᶠ N : ℕ in atTop,
        4 * w ≤ wTrickPrimeScale (primorial w) N :=
    hscaleTends.eventually (eventually_ge_atTop (4 * w))
  filter_upwards [
    hchebyshev, hscaleSixteen, hscaleFourW,
    eventually_ge_atTop 16] with
    N hchebyshev hscaleSixteen hscaleFourW hNsixteen
  intro hN
  let : NeZero N := ⟨hN.ne'⟩
  have hw :
      w ≤ wTrickPrimeScale (primorial w) N / 4 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < (4 : ℕ))).2
      (by simpa [Nat.mul_comm] using hscaleFourW)
  obtain ⟨b, hb, hmean⟩ :=
    exists_reducedResidue_chebyshev_mean_lower_bound
      hα.le hw hchebyshev
  refine ⟨b, hb, ?_⟩
  exact
    (chebyshev_wTrick_lower_bound
      (primorial_pos w) hα.le hNsixteen hscaleSixteen).trans hmean

/-- Threshold form of the uniform W-tricked density statement, ready for
the nested choices in the final assembly. -/
theorem exists_threshold_reducedResidue_mean_ge
    {w : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ hN : 0 < N,
      letI : NeZero N := ⟨hN.ne'⟩
      ∃ b ∈ reducedResidues (primorial w),
        α * log 2 / 128 ≤
          mean
            (wTrickedPrimeWeight α (primorial w) b :
              ZMod N → ℝ) := by
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.1
      (eventually_forall_pos_exists_reducedResidue_mean_ge hα)
  refine ⟨N₀, ?_⟩
  intro N hN hNpos
  let : NeZero N := ⟨hNpos.ne'⟩
  exact hN₀ N hN hNpos

/-- The uniform density theorem specialized to the globally fixed
Green--Tao parameter choices.  In particular, this statement fixes the
density before choosing the residue class and cyclic modulus. -/
theorem exists_threshold_reducedResidue_mean_ge_densityTarget
    {k w : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ hN : 0 < N,
      letI : NeZero N := ⟨hN.ne'⟩
      ∃ b ∈ reducedResidues (primorial w),
        densityTarget k cutoffNormalizer ≤
          mean
            (wTrickedPrimeWeight
              (primeScale k cutoffNormalizer)
              (primorial w) b : ZMod N → ℝ) := by
  obtain ⟨N₀, hN₀⟩ :=
    exists_threshold_reducedResidue_mean_ge
      (primeScale_pos hk hnorm) (w := w)
  refine ⟨N₀, ?_⟩
  intro N hN hNpos
  let : NeZero N := ⟨hNpos.ne'⟩
  obtain ⟨b, hb, hmean⟩ := hN₀ N hN hNpos
  exact ⟨b, hb,
    (densityTarget_le_primeScale_mul_log_div hk hnorm).trans
      hmean⟩

/-- Clean eventual existence form.  The positive witness is recorded only
to install the local `NeZero N` instance required by `ZMod N`; the
mathematical conclusion is the existence of a reduced class with positive
mean for every sufficiently large natural `N`. -/
theorem eventually_exists_reducedResidue_mean_pos
    {w : ℕ} {α : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop,
      ∃ hN : 0 < N,
        letI : NeZero N := ⟨hN.ne'⟩
        ∃ b ∈ reducedResidues (primorial w),
          0 < mean
            (wTrickedPrimeWeight α (primorial w) b :
              ZMod N → ℝ) := by
  filter_upwards [
    eventually_forall_pos_exists_reducedResidue_mean_pos hα,
    eventually_gt_atTop 0] with N hmean hN
  exact ⟨hN, hmean hN⟩

end Wikipedia.SzemeredisTheorem

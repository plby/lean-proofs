/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Defs
import ErdosProblems.Erdos896.Ford.Measure
import ErdosProblems.Erdos896.Ford.PrimeEstimates
import ErdosProblems.Erdos896.Ford.Uk
import ErdosProblems.Erdos896.Ford.Darboux

/-!
# Prime bins in Ford's upper-bound argument

This file packages the discretisation used in Section 3 of Kevin Ford's
short proof of the multiplication-table estimate.  The endpoints below are
the canonical double-exponential endpoints `exp (2^j)`.  Thus membership in
the `j`-th bin turns logarithms of primes into powers of two, while Mertens'
second theorem gives a uniform bound for the reciprocal mass of a bin.
-/

namespace Erdos896.Ford

open Filter
open scoped BigOperators

/-- The upper endpoint `⌊exp (2^j)⌋` of the `j`-th prime bin. -/
noncomputable def primeBinUpper (j : ℕ) : ℕ :=
  ⌊Real.exp ((2 : ℝ) ^ j)⌋₊

/-- The first bin contains the primes at most `⌊e⌋`; subsequent bins are the
half-open intervals between consecutive double-exponential endpoints. -/
noncomputable def primeBin : ℕ → Finset ℕ
  | 0 => Nat.primesLE (primeBinUpper 0)
  | j + 1 => Nat.primesLE (primeBinUpper (j + 1)) \ Nat.primesLE (primeBinUpper j)

/-- Reciprocal prime mass carried by one bin. -/
noncomputable def primeBinMass (j : ℕ) : ℝ :=
  ∑ p ∈ primeBin j, (1 : ℝ) / p

/-- The logarithmic index at the top of Ford's range. -/
noncomputable def fordBinIndex (y : ℕ) : ℕ :=
  ⌊Real.log (Real.log (2 * y)) / Real.log 2⌋₊

/-- Ford's `T_k(y)`, with the squarefree integer represented canonically by
its finite set of prime factors.  This is exactly the sum over squarefree
`a` all of whose prime factors are at most `2y` and with `ω(a)=k`. -/
noncomputable def Tk (y k : ℕ) : ℝ :=
  ∑ s ∈ (Nat.primesLE (2 * y)).powerset with s.card = k,
    L (s.prod (fun p : ℕ ↦ p)) (Real.log 2) /
      ((s.prod (fun p : ℕ ↦ p) : ℕ) : ℝ)

theorem primeBinUpper_mono : Monotone primeBinUpper := by
  intro i j hij
  unfold primeBinUpper
  apply Nat.floor_mono
  apply Real.exp_monotone
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij

theorem primeBinUpper_pos (j : ℕ) : 0 < primeBinUpper j := by
  rw [primeBinUpper, Nat.floor_pos]
  exact Real.one_le_exp (by positivity)

theorem two_le_primeBinUpper (j : ℕ) : 2 ≤ primeBinUpper j := by
  apply le_trans (b := primeBinUpper 0)
  · unfold primeBinUpper
    apply Nat.le_floor
    norm_num
    linarith [Real.exp_one_gt_d9]
  · exact primeBinUpper_mono (Nat.zero_le j)

theorem primeBinUpper_cast_le (j : ℕ) :
    (primeBinUpper j : ℝ) ≤ Real.exp ((2 : ℝ) ^ j) := by
  exact Nat.floor_le (Real.exp_pos _).le

theorem exp_half_lt_primeBinUpper (j : ℕ) :
    Real.exp ((2 : ℝ) ^ j) / 2 < (primeBinUpper j : ℝ) := by
  have hfloor :
      Real.exp ((2 : ℝ) ^ j) < (primeBinUpper j : ℝ) + 1 := by
    simpa [primeBinUpper] using
      (Nat.lt_floor_add_one (Real.exp ((2 : ℝ) ^ j)))
  have htwo : (2 : ℝ) < Real.exp ((2 : ℝ) ^ j) := by
    have hmono : Real.exp 1 ≤ Real.exp ((2 : ℝ) ^ j) :=
      Real.exp_monotone
        (show (1 : ℝ) ≤ 2 ^ j by
          exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    linarith [Real.exp_one_gt_d9]
  linarith

/-- The endpoint logarithms grow like `2^j`; this lower half is all that is
needed to make Mertens' error uniform in a bin. -/
theorem half_pow_le_log_primeBinUpper {j : ℕ} (hj : 1 ≤ j) :
    (2 : ℝ) ^ (j - 1) ≤ Real.log (primeBinUpper j) := by
  have hpos : (0 : ℝ) < primeBinUpper j := by
    exact_mod_cast primeBinUpper_pos j
  have hhalfpos : 0 < Real.exp ((2 : ℝ) ^ j) / 2 := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr hhalfpos) (Set.mem_Ioi.mpr hpos)
    (exp_half_lt_primeBinUpper j).le
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_exp] at hlog
  have hlogtwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [pow_succ] at hlog
  have hpow : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  linarith

theorem log_primeBinUpper_le_pow (j : ℕ) :
    Real.log (primeBinUpper j) ≤ (2 : ℝ) ^ j := by
  have hpos : (0 : ℝ) < primeBinUpper j := by
    exact_mod_cast primeBinUpper_pos j
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr (Real.exp_pos _))
    (primeBinUpper_cast_le j)
  simpa using hlog

theorem log_log_primeBinUpper_succ_sub_le (j : ℕ) (hj : 1 ≤ j) :
    Real.log (Real.log (primeBinUpper (j + 1))) -
        Real.log (Real.log (primeBinUpper j)) ≤ Real.log 4 := by
  have hlower := half_pow_le_log_primeBinUpper hj
  have hlowerPos : 0 < Real.log (primeBinUpper j) := by
    apply Real.log_pos
    exact_mod_cast (two_le_primeBinUpper j)
  have hupper := log_primeBinUpper_le_pow (j + 1)
  have hpowers : (2 : ℝ) ^ (j + 1) = 4 * (2 : ℝ) ^ (j - 1) := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    simp [pow_succ]
    ring
  have hfour :
      Real.log (primeBinUpper (j + 1)) ≤
        4 * Real.log (primeBinUpper j) := by
    rw [hpowers] at hupper
    linarith
  have hnextPos : 0 < Real.log (primeBinUpper (j + 1)) := by
    apply Real.log_pos
    exact_mod_cast (two_le_primeBinUpper (j + 1))
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr hnextPos)
    (Set.mem_Ioi.mpr (mul_pos (by norm_num) hlowerPos)) hfour
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hlowerPos.ne'] at hlog
  linarith

theorem mem_primeBin_succ {p j : ℕ} :
    p ∈ primeBin (j + 1) ↔
      p.Prime ∧ primeBinUpper j < p ∧ p ≤ primeBinUpper (j + 1) := by
  simp only [primeBin, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpUpper, hpPrime⟩, hpLower⟩
    exact ⟨hpPrime, lt_of_not_ge fun h ↦ hpLower ⟨h, hpPrime⟩, hpUpper⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    exact ⟨⟨hpUpper, hpPrime⟩, fun h ↦ (not_le_of_gt hpLower) h.1⟩

theorem primeBinMass_nonneg (j : ℕ) : 0 ≤ primeBinMass j := by
  apply Finset.sum_nonneg
  intro p hp
  positivity

/-- Membership in a noninitial bin gives the precise dyadic bounds on the
logarithm which drive Ford's discretisation. -/
theorem pow_le_log_of_mem_primeBin_succ {p j : ℕ}
    (hp : p ∈ primeBin (j + 1)) :
    (2 : ℝ) ^ j ≤ Real.log p := by
  have hmem := mem_primeBin_succ.mp hp
  have hfloor :
      Real.exp ((2 : ℝ) ^ j) < (primeBinUpper j : ℝ) + 1 := by
    simpa [primeBinUpper] using
      (Nat.lt_floor_add_one (Real.exp ((2 : ℝ) ^ j)))
  have hcast : (primeBinUpper j : ℝ) + 1 ≤ p := by
    exact_mod_cast hmem.2.1
  have hpos : (0 : ℝ) < p := by exact_mod_cast hmem.1.pos
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr (Real.exp_pos _)) (Set.mem_Ioi.mpr hpos)
    (hfloor.le.trans hcast)
  simpa using hlog

theorem log_le_pow_of_mem_primeBin_succ {p j : ℕ}
    (hp : p ∈ primeBin (j + 1)) :
    Real.log p ≤ (2 : ℝ) ^ (j + 1) := by
  have hmem := mem_primeBin_succ.mp hp
  have hcast : (p : ℝ) ≤ Real.exp ((2 : ℝ) ^ (j + 1)) :=
    (by exact_mod_cast hmem.2.2 : (p : ℝ) ≤ primeBinUpper (j + 1)).trans
      (primeBinUpper_cast_le (j + 1))
  have hpos : (0 : ℝ) < p := by exact_mod_cast hmem.1.pos
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr (Real.exp_pos _)) hcast
  simpa using hlog

theorem primeBinMass_succ_eq_sub (j : ℕ) :
    primeBinMass (j + 1) =
      primeReciprocalSum (primeBinUpper (j + 1)) -
        primeReciprocalSum (primeBinUpper j) := by
  rw [primeBinMass, primeBin, primeReciprocalSum]
  exact Finset.sum_sdiff_eq_sub
    (Nat.primesLE_mono (primeBinUpper_mono (Nat.le_succ j)))

/-- Mertens' second theorem gives a single absolute upper bound for the
reciprocal mass of every double-exponential bin. -/
theorem exists_primeBinMass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, primeBinMass j ≤ C := by
  obtain ⟨A, hA⟩ := exists_primeReciprocalSum_sub_log_log_bound
  let C := 1 + max (primeBinMass 0)
    (max (primeBinMass 1) (Real.log 4 + 2 * A))
  have hA0 : 0 ≤ A := by
    have h := hA (primeBinUpper 0) (two_le_primeBinUpper 0)
    exact (abs_nonneg _).trans h
  have hCpos : 0 < C := by
    dsimp [C]
    have hmass0 := primeBinMass_nonneg 0
    linarith [le_max_left (primeBinMass 0)
      (max (primeBinMass 1) (Real.log 4 + 2 * A))]
  refine ⟨C, hCpos, ?_⟩
  intro j
  rcases j with _ | j
  · dsimp [C]
    linarith [le_max_left (primeBinMass 0)
      (max (primeBinMass 1) (Real.log 4 + 2 * A))]
  rcases j with _ | j
  · dsimp [C]
    have hinner : primeBinMass 1 ≤
        max (primeBinMass 1) (Real.log 4 + 2 * A) := le_max_left _ _
    linarith [hinner, le_max_right (primeBinMass 0)
      (max (primeBinMass 1) (Real.log 4 + 2 * A))]
  · have hlow := hA (primeBinUpper (j + 1))
      (two_le_primeBinUpper (j + 1))
    have hupp := hA (primeBinUpper (j + 2))
      (two_le_primeBinUpper (j + 2))
    have hdiff := log_log_primeBinUpper_succ_sub_le (j + 1) (by omega)
    rw [primeBinMass_succ_eq_sub (j + 1)]
    have hlower := (abs_le.mp hlow).1
    have hupper := (abs_le.mp hupp).2
    have hmain :
        primeReciprocalSum (primeBinUpper (j + 2)) -
            primeReciprocalSum (primeBinUpper (j + 1)) ≤
          Real.log 4 + 2 * A := by
      linarith
    exact hmain.trans <| by
      dsimp [C]
      have hinner : Real.log 4 + 2 * A ≤
          max (primeBinMass 1) (Real.log 4 + 2 * A) := le_max_right _ _
      linarith [hinner, le_max_right (primeBinMass 0)
        (max (primeBinMass 1) (Real.log 4 + 2 * A))]

/-! ## Greedy Ford blocks

The source proof uses blocks whose reciprocal mass is bounded by `log 2`
with no multiplicative loss.  Starting from a cutoff `b`, take the first
endpoint where the cumulative mass would exceed `log 2`, and stop one
integer earlier.  The omitted crossing integer is necessarily prime, so
the deficit is smaller than one reciprocal prime.
-/

theorem exists_greedyPrimeCrossing (b : ℕ) :
    ∃ n : ℕ,
      Real.log 2 < primeReciprocalSum n - primeReciprocalSum b := by
  have htop := primeReciprocalSum_tendsto_atTop
  rw [tendsto_atTop_atTop] at htop
  obtain ⟨N, hN⟩ :=
    htop
      (primeReciprocalSum b + Real.log 2 + 1)
  refine ⟨max N b, ?_⟩
  have h := hN (max N b) (le_max_left N b)
  linarith

/-- First integer at which the reciprocal mass above `b` exceeds `log 2`. -/
noncomputable def greedyPrimeCrossing (b : ℕ) : ℕ :=
  Nat.find (exists_greedyPrimeCrossing b)

theorem greedyPrimeCrossing_spec (b : ℕ) :
    Real.log 2 <
      primeReciprocalSum (greedyPrimeCrossing b) - primeReciprocalSum b := by
  exact Nat.find_spec (exists_greedyPrimeCrossing b)

theorem greedyPrimeCrossing_min {b n : ℕ} (hn : n < greedyPrimeCrossing b) :
    primeReciprocalSum n - primeReciprocalSum b ≤ Real.log 2 := by
  exact le_of_not_gt (Nat.find_min (exists_greedyPrimeCrossing b) hn)

theorem lt_greedyPrimeCrossing (b : ℕ) : b < greedyPrimeCrossing b := by
  by_contra h
  have hmono := primeReciprocalSum_mono (Nat.le_of_not_gt h)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith [greedyPrimeCrossing_spec b]

theorem primeReciprocalSum_succ (n : ℕ) :
    primeReciprocalSum (n + 1) =
      if (n + 1).Prime then
        primeReciprocalSum n + (1 : ℝ) / (n + 1)
      else primeReciprocalSum n := by
  unfold primeReciprocalSum
  rw [Nat.primesLE_succ]
  split_ifs with hn
  · rw [Finset.sum_insert (Nat.notMem_primesLE n)]
    simp only [Nat.cast_add, Nat.cast_one]
    ac_rfl
  · rfl

/-- Greedy block endpoints.  Endpoint `j+1` is one below the first crossing
above endpoint `j`, so the corresponding block has mass at most `log 2`. -/
noncomputable def greedyPrimeBinUpper : ℕ → ℕ
  | 0 => 1
  | j + 1 => (greedyPrimeCrossing (greedyPrimeBinUpper j)).pred

/-- The `j`-th greedy block of primes. -/
noncomputable def greedyPrimeBin (j : ℕ) : Finset ℕ :=
  Nat.primesLE (greedyPrimeBinUpper (j + 1)) \
    Nat.primesLE (greedyPrimeBinUpper j)

/-- Reciprocal mass of a greedy block. -/
noncomputable def greedyPrimeBinMass (j : ℕ) : ℝ :=
  ∑ p ∈ greedyPrimeBin j, (1 : ℝ) / p

theorem greedyPrimeBinUpper_mono : Monotone greedyPrimeBinUpper := by
  apply monotone_nat_of_le_succ
  intro j
  rw [greedyPrimeBinUpper]
  exact Nat.le_pred_of_lt (lt_greedyPrimeCrossing (greedyPrimeBinUpper j))

theorem greedyPrimeBinMass_eq_sub (j : ℕ) :
    greedyPrimeBinMass j =
      primeReciprocalSum (greedyPrimeBinUpper (j + 1)) -
        primeReciprocalSum (greedyPrimeBinUpper j) := by
  rw [greedyPrimeBinMass, greedyPrimeBin, primeReciprocalSum]
  exact Finset.sum_sdiff_eq_sub
    (Nat.primesLE_mono (greedyPrimeBinUpper_mono (Nat.le_succ j)))

theorem greedyPrimeBinMass_nonneg (j : ℕ) : 0 ≤ greedyPrimeBinMass j := by
  unfold greedyPrimeBinMass
  positivity

/-- Exact upper-mass property of Ford's greedy blocks. -/
theorem greedyPrimeBinMass_le_log_two (j : ℕ) :
    greedyPrimeBinMass j ≤ Real.log 2 := by
  let b := greedyPrimeBinUpper j
  let m := greedyPrimeCrossing b
  have hbm : b < m := lt_greedyPrimeCrossing b
  have hpred : m.pred < m := Nat.pred_lt (by omega)
  have hmin := greedyPrimeCrossing_min (b := b) hpred
  rw [greedyPrimeBinMass_eq_sub, greedyPrimeBinUpper]
  simpa [b, m] using hmin

theorem greedyPrimeCrossing_prime (b : ℕ) :
    (greedyPrimeCrossing b).Prime := by
  let m := greedyPrimeCrossing b
  have hbm : b < m := lt_greedyPrimeCrossing b
  have hmpos : 0 < m := by omega
  have hpred : m.pred < m := Nat.pred_lt (by omega)
  have hmin := greedyPrimeCrossing_min (b := b) hpred
  have hspec := greedyPrimeCrossing_spec b
  by_contra hmPrime
  have hstep := primeReciprocalSum_succ m.pred
  have hsucc : m.pred + 1 = m := by
    simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hmpos
  rw [hsucc, if_neg hmPrime] at hstep
  dsimp [m] at hspec hmin hstep
  linarith

/-- The mass deficit of a greedy block is less than the reciprocal of the
single crossing prime omitted from that block. -/
theorem log_two_sub_inv_crossing_lt_greedyPrimeBinMass (j : ℕ) :
    Real.log 2 -
        (1 : ℝ) /
          greedyPrimeCrossing (greedyPrimeBinUpper j) <
      greedyPrimeBinMass j := by
  let b := greedyPrimeBinUpper j
  let m := greedyPrimeCrossing b
  have hbm : b < m := lt_greedyPrimeCrossing b
  have hmpos : 0 < m := by omega
  have hmPrime : m.Prime := greedyPrimeCrossing_prime b
  have hstep := primeReciprocalSum_succ m.pred
  have hsucc : m.pred + 1 = m := by
    simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hmpos
  rw [hsucc, if_pos hmPrime] at hstep
  have hcast : (m.pred : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hsucc
  rw [hcast] at hstep
  have hspec := greedyPrimeCrossing_spec b
  rw [greedyPrimeBinMass_eq_sub, greedyPrimeBinUpper]
  dsimp [b, m] at hstep hspec ⊢
  linarith

/-- A completely elementary upper bound for reciprocal prime mass on a
finite interval.  It is used only to show that the greedy endpoints grow
geometrically, hence that their one-prime mass deficits are summable. -/
theorem primeReciprocalSum_sub_le_nat_sub_div {b m : ℕ} (hbm : b ≤ m) :
    primeReciprocalSum m - primeReciprocalSum b ≤
      ((m - b : ℕ) : ℝ) / (b + 1) := by
  classical
  have hsub : Nat.primesLE b ⊆ Nat.primesLE m := Nat.primesLE_mono hbm
  rw [primeReciprocalSum, primeReciprocalSum,
    ← Finset.sum_sdiff_eq_sub hsub]
  let s := Nat.primesLE m \ Nat.primesLE b
  have hsIoc : s ⊆ Finset.Ioc b m := by
    intro p hp
    change p ∈ Nat.primesLE m \ Nat.primesLE b at hp
    obtain ⟨hpm, hpnb⟩ := Finset.mem_sdiff.mp hp
    have hpPrime := Nat.prime_of_mem_primesLE hpm
    have hpb : b < p := by
      by_contra h
      exact hpnb (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt h, hpPrime⟩)
    exact Finset.mem_Ioc.mpr ⟨hpb, Nat.le_of_mem_primesLE hpm⟩
  have hcard : s.card ≤ m - b := by
    have := Finset.card_le_card hsIoc
    simpa using this
  calc
    (∑ p ∈ Nat.primesLE m \ Nat.primesLE b, (1 : ℝ) / p) =
        ∑ p ∈ s, (1 : ℝ) / p := by rfl
    _ ≤ ∑ _p ∈ s, (1 : ℝ) / (b + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      change p ∈ Nat.primesLE m \ Nat.primesLE b at hp
      obtain ⟨hpm, hpnb⟩ := Finset.mem_sdiff.mp hp
      have hpPrime := Nat.prime_of_mem_primesLE hpm
      have hpb : b < p := by
        by_contra h
        exact hpnb (Nat.mem_primesLE.mpr ⟨Nat.le_of_not_gt h, hpPrime⟩)
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast hpb
    _ = (s.card : ℝ) / (b + 1) := by
      simp [div_eq_mul_inv]
    _ ≤ ((m - b : ℕ) : ℝ) / (b + 1) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-- Each greedy endpoint is at least a factor `3/2` larger than the
preceding endpoint (expressed without division). -/
theorem three_mul_greedyPrimeBinUpper_le_two_mul_succ (j : ℕ) :
    3 * greedyPrimeBinUpper j ≤ 2 * greedyPrimeBinUpper (j + 1) := by
  let b := greedyPrimeBinUpper j
  let m := greedyPrimeCrossing b
  have hbm : b < m := lt_greedyPrimeCrossing b
  have hmass := primeReciprocalSum_sub_le_nat_sub_div (Nat.le_of_lt hbm)
  have hcross := greedyPrimeCrossing_spec b
  have hhalf : (1 : ℝ) / 2 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hratio : (1 : ℝ) / 2 < ((m - b : ℕ) : ℝ) / (b + 1) := by
    dsimp [m]
    linarith
  have hden : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  have hmul : (b + 1 : ℝ) < 2 * ((m - b : ℕ) : ℝ) := by
    have := (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden).mp hratio
    norm_num [Nat.cast_add, Nat.cast_one] at this ⊢
    nlinarith
  have hmulNat : b + 1 < 2 * (m - b) := by exact_mod_cast hmul
  rw [greedyPrimeBinUpper]
  dsimp [b, m] at hmulNat ⊢
  omega

/-- Quantitative geometric growth of the greedy endpoints. -/
theorem greedyPrimeBinUpper_geometric (j : ℕ) :
    (3 : ℝ) ^ j ≤ (2 : ℝ) ^ j * greedyPrimeBinUpper j := by
  induction j with
  | zero => simp [greedyPrimeBinUpper]
  | succ j ih =>
      have hstep := three_mul_greedyPrimeBinUpper_le_two_mul_succ j
      have hstepR :
          (3 : ℝ) * greedyPrimeBinUpper j ≤
            2 * greedyPrimeBinUpper (j + 1) := by exact_mod_cast hstep
      rw [pow_succ, pow_succ]
      calc
        (3 : ℝ) ^ j * 3 ≤
            ((2 : ℝ) ^ j * (greedyPrimeBinUpper j : ℝ)) * 3 :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = (2 : ℝ) ^ j * (3 * (greedyPrimeBinUpper j : ℝ)) := by ring
        _ ≤ (2 : ℝ) ^ j * (2 * (greedyPrimeBinUpper (j + 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left hstepR (by positivity)
        _ = ((2 : ℝ) ^ j * (greedyPrimeBinUpper (j + 1) : ℝ)) * 2 := by ring
        _ = ((2 : ℝ) ^ j * 2) * (greedyPrimeBinUpper (j + 1) : ℝ) := by ring

theorem inv_greedyPrimeCrossing_le_two_thirds_pow (j : ℕ) :
    (1 : ℝ) / greedyPrimeCrossing (greedyPrimeBinUpper j) ≤
      ((2 : ℝ) / 3) ^ (j + 1) := by
  let m := greedyPrimeCrossing (greedyPrimeBinUpper j)
  have hmpos : 0 < m := by
    exact (lt_greedyPrimeCrossing (greedyPrimeBinUpper j)).trans_le' (Nat.zero_le _)
  have hupperlt : greedyPrimeBinUpper (j + 1) < m := by
    rw [greedyPrimeBinUpper]
    exact Nat.pred_lt (by omega)
  have hgeom := greedyPrimeBinUpper_geometric (j + 1)
  have htwoPos : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
  have hscale :
      (3 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (j + 1) ≤
        greedyPrimeBinUpper (j + 1) := by
    apply (div_le_iff₀ htwoPos).2
    simpa [mul_comm] using hgeom
  have hscaleM :
      (3 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (j + 1) ≤ m :=
    hscale.trans (by exact_mod_cast (Nat.le_of_lt hupperlt))
  have hinv := one_div_le_one_div_of_le
    (div_pos (by positivity) htwoPos) hscaleM
  dsimp [m] at hinv ⊢
  calc
    (1 : ℝ) / greedyPrimeCrossing (greedyPrimeBinUpper j) ≤
        1 / ((3 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (j + 1)) := hinv
    _ = ((2 : ℝ) / 3) ^ (j + 1) := by
      rw [div_pow]
      field_simp

theorem sum_two_thirds_pow_succ_le_two (n : ℕ) :
    (∑ j ∈ Finset.range n, ((2 : ℝ) / 3) ^ (j + 1)) ≤ 2 := by
  let r : ℝ := (2 : ℝ) / 3
  have hr0 : 0 ≤ r := by dsimp [r]; norm_num
  have hr1 : r ≤ 1 := by dsimp [r]; norm_num
  have hgeom :
      (∑ j ∈ Finset.range n, r ^ j) * (1 - r) = 1 - r ^ n :=
    geom_sum_mul_of_le_one hr1 n
  have hpnonneg : 0 ≤ r ^ n := pow_nonneg hr0 n
  calc
    (∑ j ∈ Finset.range n, ((2 : ℝ) / 3) ^ (j + 1)) =
        r * ∑ j ∈ Finset.range n, r ^ j := by
      dsimp [r]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring
    _ ≤ 2 := by
      dsimp [r] at hgeom ⊢
      norm_num at hgeom
      nlinarith

theorem sum_inv_greedyPrimeCrossing_le_two (n : ℕ) :
    (∑ j ∈ Finset.range n,
      (1 : ℝ) / greedyPrimeCrossing (greedyPrimeBinUpper j)) ≤ 2 := by
  calc
    (∑ j ∈ Finset.range n,
        (1 : ℝ) / greedyPrimeCrossing (greedyPrimeBinUpper j)) ≤
        ∑ j ∈ Finset.range n, ((2 : ℝ) / 3) ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact inv_greedyPrimeCrossing_le_two_thirds_pow j
    _ ≤ 2 := sum_two_thirds_pow_succ_le_two n

theorem sum_greedyPrimeBinMass (n : ℕ) :
    ∑ j ∈ Finset.range n, greedyPrimeBinMass j =
      primeReciprocalSum (greedyPrimeBinUpper n) := by
  induction n with
  | zero => simp [greedyPrimeBinUpper, primeReciprocalSum]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, greedyPrimeBinMass_eq_sub]
      ring

/-- Cumulative reciprocal mass of the greedy endpoint differs from
`n * log 2` by at most the absolute constant `2`. -/
theorem greedyPrimeBin_cumulative_mass_bounds (n : ℕ) :
    (n : ℝ) * Real.log 2 - 2 ≤
        primeReciprocalSum (greedyPrimeBinUpper n) ∧
      primeReciprocalSum (greedyPrimeBinUpper n) ≤
        (n : ℝ) * Real.log 2 := by
  constructor
  · have hterm : ∀ j ∈ Finset.range n,
        Real.log 2 ≤ greedyPrimeBinMass j +
          (1 : ℝ) / greedyPrimeCrossing (greedyPrimeBinUpper j) := by
      intro j hj
      linarith [log_two_sub_inv_crossing_lt_greedyPrimeBinMass j]
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, sum_greedyPrimeBinMass] at hsum
    have hinv := sum_inv_greedyPrimeCrossing_le_two n
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    linarith
  · rw [← sum_greedyPrimeBinMass]
    calc
      (∑ j ∈ Finset.range n, greedyPrimeBinMass j) ≤
          ∑ _j ∈ Finset.range n, Real.log 2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact greedyPrimeBinMass_le_log_two j
      _ = (n : ℝ) * Real.log 2 := by simp

theorem two_le_greedyPrimeBinUpper {n : ℕ} (hn : 1 ≤ n) :
    2 ≤ greedyPrimeBinUpper n := by
  have hstep := three_mul_greedyPrimeBinUpper_le_two_mul_succ 0
  have hone : 2 ≤ greedyPrimeBinUpper 1 := by
    norm_num [greedyPrimeBinUpper] at hstep ⊢
    omega
  exact hone.trans (greedyPrimeBinUpper_mono hn)

/-- Ford's greedy endpoints have dyadic logarithmic scale:
`log λ_n` lies between fixed constant multiples of `2^n`. -/
theorem exists_greedyPrimeBin_log_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (2 : ℝ) ^ n / C ≤ Real.log (greedyPrimeBinUpper n) ∧
        Real.log (greedyPrimeBinUpper n) ≤ C * (2 : ℝ) ^ n := by
  obtain ⟨A, hA⟩ := exists_primeReciprocalSum_sub_log_log_bound
  let C := Real.exp (A + 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn
  let u := greedyPrimeBinUpper n
  have hu2 : 2 ≤ u := two_le_greedyPrimeBinUpper hn
  have hlogu : 0 < Real.log u :=
    Real.log_pos (by exact_mod_cast hu2)
  have herr := hA u hu2
  have hmass := greedyPrimeBin_cumulative_mass_bounds n
  have hllower :
      (n : ℝ) * Real.log 2 - (A + 2) ≤
        Real.log (Real.log u) := by
    have herrUpper := (abs_le.mp herr).2
    linarith [hmass.1]
  have hlupper :
      Real.log (Real.log u) ≤ (n : ℝ) * Real.log 2 + A := by
    have herrLower := (abs_le.mp herr).1
    linarith [hmass.2]
  have hexpPow :
      Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hlowerExp := Real.exp_monotone hllower
  rw [Real.exp_sub, hexpPow, Real.exp_log hlogu] at hlowerExp
  have hupperExp := Real.exp_monotone hlupper
  rw [Real.exp_add, hexpPow, Real.exp_log hlogu] at hupperExp
  constructor
  · simpa [C] using hlowerExp
  · have hAC : Real.exp A ≤ C := by
      dsimp [C]
      exact Real.exp_monotone (by linarith)
    dsimp [u] at hupperExp ⊢
    calc
      Real.log (greedyPrimeBinUpper n) ≤ (2 : ℝ) ^ n * Real.exp A := hupperExp
      _ ≤ (2 : ℝ) ^ n * C :=
        mul_le_mul_of_nonneg_left hAC (by positivity)
      _ = C * (2 : ℝ) ^ n := by ring

theorem greedyPrimeBinUpper_strictMono : StrictMono greedyPrimeBinUpper := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hstep := three_mul_greedyPrimeBinUpper_le_two_mul_succ j
  have hpos : 1 ≤ greedyPrimeBinUpper j := by
    have := greedyPrimeBinUpper_mono (Nat.zero_le j)
    simpa [greedyPrimeBinUpper] using this
  omega

theorem nat_succ_le_greedyPrimeBinUpper (j : ℕ) :
    j + 1 ≤ greedyPrimeBinUpper j := by
  induction j with
  | zero => simp [greedyPrimeBinUpper]
  | succ j ih =>
      have hlt := greedyPrimeBinUpper_strictMono (Nat.lt_succ_self j)
      simp only [Nat.succ_eq_add_one] at ih hlt ⊢
      omega

theorem exists_le_greedyPrimeBinUpper_succ (p : ℕ) :
    ∃ j : ℕ, p ≤ greedyPrimeBinUpper (j + 1) := by
  refine ⟨p, ?_⟩
  have h := nat_succ_le_greedyPrimeBinUpper (p + 1)
  omega

/-- Index of the unique greedy block containing a prime `p`.  It is
defined for every natural number by taking the first endpoint above `p`. -/
noncomputable def greedyPrimeBinIndex (p : ℕ) : ℕ :=
  Nat.find (exists_le_greedyPrimeBinUpper_succ p)

theorem greedyPrimeBinIndex_spec (p : ℕ) :
    p ≤ greedyPrimeBinUpper (greedyPrimeBinIndex p + 1) := by
  exact Nat.find_spec (exists_le_greedyPrimeBinUpper_succ p)

theorem greedyPrimeBinIndex_min {p j : ℕ} (hj : j < greedyPrimeBinIndex p) :
    greedyPrimeBinUpper (j + 1) < p := by
  exact lt_of_not_ge (Nat.find_min (exists_le_greedyPrimeBinUpper_succ p) hj)

theorem greedyPrimeBinIndex_mono : Monotone greedyPrimeBinIndex := by
  intro p q hpq
  apply Nat.find_min' (exists_le_greedyPrimeBinUpper_succ p)
  exact hpq.trans (greedyPrimeBinIndex_spec q)

theorem lower_endpoint_lt_of_prime {p : ℕ} (hp : p.Prime) :
    greedyPrimeBinUpper (greedyPrimeBinIndex p) < p := by
  rcases hidx : greedyPrimeBinIndex p with _ | j
  · simpa [greedyPrimeBinUpper] using hp.one_lt
  · have h := greedyPrimeBinIndex_min (p := p) (j := j) (by omega)
    simpa [hidx] using h

theorem mem_greedyPrimeBin_iff {p j : ℕ} :
    p ∈ greedyPrimeBin j ↔
      p.Prime ∧ greedyPrimeBinUpper j < p ∧
        p ≤ greedyPrimeBinUpper (j + 1) := by
  rw [greedyPrimeBin, Finset.mem_sdiff]
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpUpper, hpPrime⟩, hpLower⟩
    exact ⟨hpPrime, lt_of_not_ge fun h ↦ hpLower ⟨h, hpPrime⟩, hpUpper⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    exact ⟨⟨hpUpper, hpPrime⟩, fun h ↦ (not_le_of_gt hpLower) h.1⟩

theorem mem_greedyPrimeBin_index {p : ℕ} (hp : p.Prime) :
    p ∈ greedyPrimeBin (greedyPrimeBinIndex p) := by
  rw [mem_greedyPrimeBin_iff]
  exact ⟨hp, lower_endpoint_lt_of_prime hp, greedyPrimeBinIndex_spec p⟩

theorem greedyPrimeBinIndex_lt_of_le_upper {p r : ℕ} (hr : 0 < r)
    (hp : p ≤ greedyPrimeBinUpper r) : greedyPrimeBinIndex p < r := by
  have hcand :
      p ≤ greedyPrimeBinUpper ((r - 1) + 1) := by
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr.ne')]
  have hle := Nat.find_min' (exists_le_greedyPrimeBinUpper_succ p) hcand
  have hle' : greedyPrimeBinIndex p ≤ r - 1 := by
    simpa [greedyPrimeBinIndex] using hle
  omega

/-! ## Monotonicity and integrability of Ford's integrand -/

theorem prefixWeight_monotone (k v g : ℕ) :
    Monotone (prefixWeight k v g) := by
  intro x y hxy
  unfold prefixWeight
  apply div_le_div_of_nonneg_right _ (by positivity)
  gcongr with i
  split_ifs
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_left (hxy i) (Nat.cast_nonneg v)
  · exact le_rfl

theorem ukIntegrandAux_monotone (k v g : ℕ) :
    Monotone (fun x ↦ ukIntegrandAux k v x g) := by
  induction g with
  | zero => simpa [ukIntegrandAux] using prefixWeight_monotone k v 0
  | succ g ih =>
      intro x y hxy
      simp only [ukIntegrandAux]
      exact min_le_min (ih hxy) (prefixWeight_monotone k v (g + 1) hxy)

theorem ukIntegrand_monotone (k v : ℕ) : Monotone (ukIntegrand k v) := by
  exact ukIntegrandAux_monotone k v k

theorem ukIntegrand_integrableOn_orderedSimplex (k v : ℕ) :
    MeasureTheory.IntegrableOn (ukIntegrand k v) (orderedSimplex k 0 1) := by
  have hbox : IsCompact
      (Set.Icc (fun _ : Fin k ↦ (0 : ℝ)) (fun _ : Fin k ↦ (1 : ℝ))) :=
    isCompact_Icc
  have hint := (continuous_ukIntegrand k v).continuousOn.integrableOn_compact
    (μ := MeasureTheory.volume) hbox
  apply hint.mono_set
  intro x hx
  constructor <;> intro i
  · exact (hx.1 i).1
  · exact (hx.1 i).2

/-! ## Prime-level Darboux cells

Using one cell per prime (rather than one cell per block) keeps cells
ordered even when several selected primes lie in the same greedy block.
Within a block the cell widths are their normalized reciprocal masses.
-/

noncomputable def greedyPrimeBinBelow (p : ℕ) : Finset ℕ :=
  (greedyPrimeBin (greedyPrimeBinIndex p)).filter (fun q ↦ q < p)

noncomputable def greedyPrimeBinMassBelow (p : ℕ) : ℝ :=
  ∑ q ∈ greedyPrimeBinBelow p, (1 : ℝ) / q

theorem greedyPrimeBinMassBelow_nonneg (p : ℕ) :
    0 ≤ greedyPrimeBinMassBelow p := by
  unfold greedyPrimeBinMassBelow
  positivity

theorem greedyPrimeBinMassBelow_add_inv_le {p : ℕ} (hp : p.Prime) :
    greedyPrimeBinMassBelow p + (1 : ℝ) / p ≤
      greedyPrimeBinMass (greedyPrimeBinIndex p) := by
  classical
  have hpbin := mem_greedyPrimeBin_index hp
  have hpnot : p ∉ greedyPrimeBinBelow p := by
    simp [greedyPrimeBinBelow]
  have hsub : insert p (greedyPrimeBinBelow p) ⊆
      greedyPrimeBin (greedyPrimeBinIndex p) := by
    intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · exact hpbin
    · exact (Finset.mem_filter.mp hq).1
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q hq hnot ↦ by positivity : ∀ q ∈ greedyPrimeBin (greedyPrimeBinIndex p),
      q ∉ insert p (greedyPrimeBinBelow p) → (0 : ℝ) ≤ 1 / q)
  rw [Finset.sum_insert hpnot] at hsum
  simpa [greedyPrimeBinMassBelow, greedyPrimeBinMass, add_comm] using hsum

/-- Lower endpoint of the reciprocal-mass cell for `p`, at scale `r`. -/
noncomputable def greedyPrimeCellLower (r p : ℕ) : ℝ :=
  ((greedyPrimeBinIndex p : ℝ) +
      greedyPrimeBinMassBelow p / Real.log 2) / r

/-- Upper endpoint of the reciprocal-mass cell for `p`, at scale `r`. -/
noncomputable def greedyPrimeCellUpper (r p : ℕ) : ℝ :=
  greedyPrimeCellLower r p +
    ((1 : ℝ) / p) / ((r : ℝ) * Real.log 2)

theorem greedyPrimeCellLower_nonneg (r p : ℕ) :
    0 ≤ greedyPrimeCellLower r p := by
  unfold greedyPrimeCellLower
  apply div_nonneg
  · exact add_nonneg (Nat.cast_nonneg _)
      (div_nonneg (greedyPrimeBinMassBelow_nonneg p)
        (Real.log_nonneg (by norm_num)))
  · exact Nat.cast_nonneg r

theorem greedyPrimeCellLower_le_upper (r p : ℕ) :
    greedyPrimeCellLower r p ≤ greedyPrimeCellUpper r p := by
  unfold greedyPrimeCellUpper
  apply le_add_of_nonneg_right
  exact div_nonneg (by positivity)
    (mul_nonneg (Nat.cast_nonneg r) (Real.log_nonneg (by norm_num)))

theorem greedyPrimeCell_mass_identity {r p : ℕ} (hr : 0 < r) :
    (1 : ℝ) / p =
      ((r : ℝ) * Real.log 2) *
        (greedyPrimeCellUpper r p - greedyPrimeCellLower r p) := by
  unfold greedyPrimeCellUpper
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp
  ring

theorem greedyPrimeCellLower_bin_lower {r p : ℕ} (hr : 0 < r) :
    (greedyPrimeBinIndex p : ℝ) / r ≤ greedyPrimeCellLower r p := by
  unfold greedyPrimeCellLower
  apply (div_le_div_iff_of_pos_right (by exact_mod_cast hr)).2
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  exact le_add_of_nonneg_right
    (div_nonneg (greedyPrimeBinMassBelow_nonneg p) hlog)

theorem greedyPrimeCellUpper_eq {r p : ℕ} (hr : 0 < r) :
    greedyPrimeCellUpper r p =
      ((greedyPrimeBinIndex p : ℝ) +
        (greedyPrimeBinMassBelow p + (1 : ℝ) / p) / Real.log 2) / r := by
  unfold greedyPrimeCellUpper greedyPrimeCellLower
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp
  ring

theorem greedyPrimeCellUpper_bin_upper {r p : ℕ} (hr : 0 < r)
    (hp : p.Prime) :
    greedyPrimeCellUpper r p ≤ (greedyPrimeBinIndex p + 1 : ℕ) / (r : ℝ) := by
  rw [greedyPrimeCellUpper_eq hr]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmass := greedyPrimeBinMassBelow_add_inv_le hp
  have hmass' := hmass.trans (greedyPrimeBinMass_le_log_two (greedyPrimeBinIndex p))
  apply (div_le_div_iff_of_pos_right (by exact_mod_cast hr)).2
  have hnorm :
      (greedyPrimeBinMassBelow p + (1 : ℝ) / p) / Real.log 2 ≤ 1 :=
    (div_le_one hlog).2 hmass'
  norm_num [Nat.cast_add, Nat.cast_one]
  simp only [one_div] at hnorm
  linarith

theorem massBelow_add_inv_le_massBelow_of_lt_same_bin {p q : ℕ}
    (hp : p.Prime) (hpq : p < q)
    (hbin : greedyPrimeBinIndex p = greedyPrimeBinIndex q) :
    greedyPrimeBinMassBelow p + (1 : ℝ) / p ≤
      greedyPrimeBinMassBelow q := by
  classical
  have hpnot : p ∉ greedyPrimeBinBelow p := by
    simp [greedyPrimeBinBelow]
  have hsub : insert p (greedyPrimeBinBelow p) ⊆ greedyPrimeBinBelow q := by
    intro t ht
    rw [Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · rw [greedyPrimeBinBelow, Finset.mem_filter]
      exact ⟨hbin ▸ mem_greedyPrimeBin_index hp, hpq⟩
    · rw [greedyPrimeBinBelow, Finset.mem_filter] at ht ⊢
      exact ⟨hbin ▸ ht.1, ht.2.trans hpq⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun t ht hnot ↦ by positivity : ∀ t ∈ greedyPrimeBinBelow q,
      t ∉ insert p (greedyPrimeBinBelow p) → (0 : ℝ) ≤ 1 / t)
  rw [Finset.sum_insert hpnot] at hsum
  simpa [greedyPrimeBinMassBelow, add_comm] using hsum

/-- Prime-level cells respect the prime ordering, including when both
primes lie in the same greedy block. -/
theorem greedyPrimeCell_separated {r p q : ℕ} (hr : 0 < r)
    (hp : p.Prime) (_hq : q.Prime) (hpq : p < q) :
    greedyPrimeCellUpper r p ≤ greedyPrimeCellLower r q := by
  have hindex := greedyPrimeBinIndex_mono hpq.le
  rcases hindex.eq_or_lt with hsame | hlt
  · rw [greedyPrimeCellUpper_eq hr]
    unfold greedyPrimeCellLower
    rw [hsame]
    apply (div_le_div_iff_of_pos_right (by exact_mod_cast hr)).2
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    simpa [add_comm] using add_le_add_left
      (div_le_div_of_nonneg_right
        (massBelow_add_inv_le_massBelow_of_lt_same_bin hp hpq hsame)
        hlog.le) (greedyPrimeBinIndex q : ℝ)
  · calc
      greedyPrimeCellUpper r p ≤
          (greedyPrimeBinIndex p + 1 : ℕ) / (r : ℝ) :=
        greedyPrimeCellUpper_bin_upper hr hp
      _ ≤ (greedyPrimeBinIndex q : ℝ) / r := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg r)
        exact_mod_cast (Nat.succ_le_of_lt hlt)
      _ ≤ greedyPrimeCellLower r q := greedyPrimeCellLower_bin_lower hr

/-- Strictly increasing prime tuples, with every prime at most `2y`. -/
noncomputable def orderedPrimeGrid (y k : ℕ) :
    Finset (Fin k → ↥(Nat.primesLE (2 * y))) :=
  Finset.univ.filter fun p ↦ StrictMono (fun i ↦ (p i : ℕ))

theorem mem_orderedPrimeGrid {y k : ℕ}
    {p : Fin k → ↥(Nat.primesLE (2 * y))} :
    p ∈ orderedPrimeGrid y k ↔ StrictMono (fun i ↦ (p i : ℕ)) := by
  simp [orderedPrimeGrid]

noncomputable def greedyPrimeTupleSample {y k : ℕ} (r : ℕ)
    (p : Fin k → ↥(Nat.primesLE (2 * y))) : Fin k → ℝ :=
  fun i ↦ greedyPrimeCellLower r (p i)

theorem greedyPrimeTupleSample_mem_orderedSimplex {y k r : ℕ}
    (hr : 0 < r) (htop : 2 * y ≤ greedyPrimeBinUpper r)
    {p : Fin k → ↥(Nat.primesLE (2 * y))} (hp : p ∈ orderedPrimeGrid y k) :
    greedyPrimeTupleSample r p ∈ orderedSimplex k 0 1 := by
  have hstrict := mem_orderedPrimeGrid.mp hp
  have hpPrime (i : Fin k) : (p i : ℕ).Prime :=
    Nat.prime_of_mem_primesLE (p i).property
  have hindex (i : Fin k) : greedyPrimeBinIndex (p i) < r :=
    greedyPrimeBinIndex_lt_of_le_upper hr
      ((Nat.le_of_mem_primesLE (p i).property).trans htop)
  constructor
  · intro i
    constructor
    · exact greedyPrimeCellLower_nonneg r (p i)
    · calc
        greedyPrimeCellLower r (p i) ≤ greedyPrimeCellUpper r (p i) :=
          greedyPrimeCellLower_le_upper r (p i)
        _ ≤ (greedyPrimeBinIndex (p i) + 1 : ℕ) / (r : ℝ) :=
          greedyPrimeCellUpper_bin_upper hr (hpPrime i)
        _ ≤ 1 := by
          apply (div_le_one (by exact_mod_cast hr)).2
          exact_mod_cast (Nat.succ_le_of_lt (hindex i))
  · intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · exact (greedyPrimeCellLower_le_upper r (p i)).trans
        (greedyPrimeCell_separated hr (hpPrime i) (hpPrime j) (hstrict hij))

theorem gridIoc_greedyPrimeCells_subset_orderedSimplex {y k r : ℕ}
    (hr : 0 < r) (htop : 2 * y ≤ greedyPrimeBinUpper r)
    {p : Fin k → ↥(Nat.primesLE (2 * y))} (hp : p ∈ orderedPrimeGrid y k) :
    gridIoc
        (fun _ (q : ↥(Nat.primesLE (2 * y))) ↦ greedyPrimeCellLower r q)
        (fun _ (q : ↥(Nat.primesLE (2 * y))) ↦ greedyPrimeCellUpper r q) p ⊆
      orderedSimplex k 0 1 := by
  intro x hx
  have hstrict := mem_orderedPrimeGrid.mp hp
  have hpPrime (i : Fin k) : (p i : ℕ).Prime :=
    Nat.prime_of_mem_primesLE (p i).property
  have hindex (i : Fin k) : greedyPrimeBinIndex (p i) < r :=
    greedyPrimeBinIndex_lt_of_le_upper hr
      ((Nat.le_of_mem_primesLE (p i).property).trans htop)
  have hxIoc (i : Fin k) :
      x i ∈ Set.Ioc (greedyPrimeCellLower r (p i))
        (greedyPrimeCellUpper r (p i)) :=
    Set.mem_pi.1 hx i (Set.mem_univ i)
  constructor
  · intro i
    constructor
    · exact (greedyPrimeCellLower_nonneg r (p i)).trans (hxIoc i).1.le
    · calc
        x i ≤ greedyPrimeCellUpper r (p i) := (hxIoc i).2
        _ ≤ (greedyPrimeBinIndex (p i) + 1 : ℕ) / (r : ℝ) :=
          greedyPrimeCellUpper_bin_upper hr (hpPrime i)
        _ ≤ 1 := by
          apply (div_le_one (by exact_mod_cast hr)).2
          exact_mod_cast (Nat.succ_le_of_lt (hindex i))
  · intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · exact le_rfl
    · calc
        x i ≤ greedyPrimeCellUpper r (p i) := (hxIoc i).2
        _ ≤ greedyPrimeCellLower r (p j) :=
          greedyPrimeCell_separated hr (hpPrime i) (hpPrime j) (hstrict hij)
        _ ≤ x j := (hxIoc j).1.le

/-- Exact Darboux estimate for the ordered prime grid.  The common density
is `r log 2`, since a prime of mass `1/p` is assigned a cell of width
`1/(p r log 2)`. -/
theorem orderedPrimeGrid_weighted_uk_le {y k r : ℕ}
    (hr : 0 < r) (htop : 2 * y ≤ greedyPrimeBinUpper r) :
    (∑ p ∈ orderedPrimeGrid y k,
      (∏ i : Fin k, (1 : ℝ) / (p i : ℕ)) *
        ukIntegrand k r (greedyPrimeTupleSample r p)) ≤
      ((r : ℝ) * Real.log 2) ^ k * uk k r := by
  let P := ↥(Nat.primesLE (2 * y))
  let lower : Fin k → P → ℝ := fun _ p ↦ greedyPrimeCellLower r p
  let upper : Fin k → P → ℝ := fun _ p ↦ greedyPrimeCellUpper r p
  let mass : Fin k → P → ℝ := fun _ p ↦ (1 : ℝ) / (p : ℕ)
  have h := weighted_orderedIoc_sum_le_integral_of_monotoneOn
    (orderedPrimeGrid y k) lower upper mass 0 1
      ((r : ℝ) * Real.log 2) (ukIntegrand k r)
      (mul_nonneg (Nat.cast_nonneg r) (Real.log_nonneg (by norm_num)))
      (by
        intro p hp i
        dsimp [mass]
        positivity)
      (by
        intro p hp i
        exact greedyPrimeCellLower_le_upper r (p i))
      (by
        intro p hp i
        dsimp [mass, lower, upper]
        exact (greedyPrimeCell_mass_identity (p := (p i : ℕ)) hr).le)
      (by
        intro i
        apply pairwiseDisjoint_Ioc_of_separated
        intro p q hpq
        exact greedyPrimeCell_separated hr
          (Nat.prime_of_mem_primesLE p.property)
          (Nat.prime_of_mem_primesLE q.property) hpq)
      (by
        intro p hp
        exact gridIoc_greedyPrimeCells_subset_orderedSimplex hr htop hp)
      (by
        intro p hp
        exact greedyPrimeTupleSample_mem_orderedSimplex hr htop hp)
      (ukIntegrand_integrableOn_orderedSimplex k r)
      (fun x hx ↦ ukIntegrand_nonneg k r x)
      (fun x hx y hy hxy ↦ ukIntegrand_monotone k r hxy)
  change (∑ p ∈ orderedPrimeGrid y k,
      (∏ i : Fin k, (1 : ℝ) / (p i : ℕ)) *
        ukIntegrand k r (fun i ↦ greedyPrimeCellLower r (p i))) ≤ _
  simpa [P, lower, upper, mass, gridWeight, uk] using h

/-! ## Canonical subsets and ordered prime tuples -/

noncomputable def orderedPrimeTupleOfFinset {y k : ℕ} (s : Finset ℕ)
    (hs : s ∈ (Nat.primesLE (2 * y)).powersetCard k) :
    Fin k → ↥(Nat.primesLE (2 * y)) :=
  fun i ↦ ⟨s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2 i,
    (Finset.mem_powersetCard.mp hs).1
      (s.orderEmbOfFin_mem (Finset.mem_powersetCard.mp hs).2 i)⟩

@[simp] theorem coe_orderedPrimeTupleOfFinset {y k : ℕ} (s : Finset ℕ)
    (hs : s ∈ (Nat.primesLE (2 * y)).powersetCard k) (i : Fin k) :
    (orderedPrimeTupleOfFinset s hs i : ℕ) =
      s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2 i := rfl

theorem orderedPrimeTupleOfFinset_mem_grid {y k : ℕ} (s : Finset ℕ)
    (hs : s ∈ (Nat.primesLE (2 * y)).powersetCard k) :
    orderedPrimeTupleOfFinset s hs ∈ orderedPrimeGrid y k := by
  rw [mem_orderedPrimeGrid]
  simpa only [coe_orderedPrimeTupleOfFinset] using
    (s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2).strictMono

noncomputable def primeFinsetOfOrderedTuple {y k : ℕ}
    (p : Fin k → ↥(Nat.primesLE (2 * y))) : Finset ℕ :=
  Finset.image (fun i ↦ (p i : ℕ)) Finset.univ

theorem primeFinsetOfOrderedTuple_mem_powersetCard {y k : ℕ}
    {p : Fin k → ↥(Nat.primesLE (2 * y))} (hp : p ∈ orderedPrimeGrid y k) :
    primeFinsetOfOrderedTuple p ∈ (Nat.primesLE (2 * y)).powersetCard k := by
  rw [Finset.mem_powersetCard]
  constructor
  · intro q hq
    rw [primeFinsetOfOrderedTuple, Finset.mem_image] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact (p i).property
  · rw [primeFinsetOfOrderedTuple, Finset.card_image_iff.mpr]
    · simp
    · intro i hi j hj hij
      exact (mem_orderedPrimeGrid.mp hp).injective hij

theorem primeFinsetOf_orderedPrimeTupleOfFinset {y k : ℕ} (s : Finset ℕ)
    (hs : s ∈ (Nat.primesLE (2 * y)).powersetCard k) :
    primeFinsetOfOrderedTuple (orderedPrimeTupleOfFinset s hs) = s := by
  unfold primeFinsetOfOrderedTuple
  simpa only [coe_orderedPrimeTupleOfFinset] using
    s.image_orderEmbOfFin_univ (Finset.mem_powersetCard.mp hs).2

theorem orderedPrimeTupleOf_primeFinsetOfOrderedTuple {y k : ℕ}
    (p : Fin k → ↥(Nat.primesLE (2 * y))) (hp : p ∈ orderedPrimeGrid y k) :
    orderedPrimeTupleOfFinset (primeFinsetOfOrderedTuple p)
      (primeFinsetOfOrderedTuple_mem_powersetCard hp) = p := by
  apply funext
  intro i
  apply Subtype.ext
  change (primeFinsetOfOrderedTuple p).orderEmbOfFin _ i = p i
  have hmem (i : Fin k) : (p i : ℕ) ∈ primeFinsetOfOrderedTuple p := by
    rw [primeFinsetOfOrderedTuple, Finset.mem_image]
    exact ⟨i, Finset.mem_univ i, rfl⟩
  have huniq := Finset.orderEmbOfFin_unique
    (Finset.mem_powersetCard.mp
      (primeFinsetOfOrderedTuple_mem_powersetCard hp)).2
    hmem (mem_orderedPrimeGrid.mp hp)
  exact (congr_fun huniq i).symm

theorem prod_orderedPrimeTupleOfFinset {y k : ℕ} (s : Finset ℕ)
    (hs : s ∈ (Nat.primesLE (2 * y)).powersetCard k) :
    (∏ i : Fin k, (orderedPrimeTupleOfFinset s hs i : ℕ)) =
      s.prod (fun p : ℕ ↦ p) := by
  let e := s.orderEmbOfFin (Finset.mem_powersetCard.mp hs).2
  change (∏ i : Fin k, e i) = s.prod (fun p : ℕ ↦ p)
  rw [← s.image_orderEmbOfFin_univ (Finset.mem_powersetCard.mp hs).2]
  rw [Finset.prod_image]
  intro i hi j hj hij
  exact e.injective hij

/-- Reindex the canonical squarefree-subset definition of `T_k` by its
unique increasing tuple of prime factors. -/
theorem Tk_eq_orderedPrimeGrid_sum (y k : ℕ) :
    Tk y k =
      ∑ p ∈ orderedPrimeGrid y k,
        L (∏ i : Fin k, (p i : ℕ)) (Real.log 2) *
          ∏ i : Fin k, (1 : ℝ) / (p i : ℕ) := by
  classical
  unfold Tk
  have hfilter :
      (Nat.primesLE (2 * y)).powerset.filter (fun s ↦ s.card = k) =
        (Nat.primesLE (2 * y)).powersetCard k := by
    ext s
    simp [and_comm]
  rw [hfilter]
  refine Finset.sum_bij'
      (fun s hs ↦ orderedPrimeTupleOfFinset s hs)
      (fun p hp ↦ primeFinsetOfOrderedTuple p) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    exact orderedPrimeTupleOfFinset_mem_grid s hs
  · intro p hp
    exact primeFinsetOfOrderedTuple_mem_powersetCard hp
  · intro s hs
    exact primeFinsetOf_orderedPrimeTupleOfFinset s hs
  · intro p hp
    exact orderedPrimeTupleOf_primeFinsetOfOrderedTuple p hp
  · intro s hs
    rw [prod_orderedPrimeTupleOfFinset s hs]
    simp only [Nat.cast_prod]
    rw [div_eq_mul_inv]
    congr 1
    have hprodR :
        (∏ i ∈ s, (i : ℝ)) =
          ∏ i : Fin k, ((orderedPrimeTupleOfFinset s hs i : ℕ) : ℝ) := by
      simpa only [Nat.cast_prod] using congrArg (fun n : ℕ ↦ (n : ℝ))
        (prod_orderedPrimeTupleOfFinset s hs).symm
    rw [hprodR, ← Finset.prod_inv_distrib]
    simp [one_div]

theorem le_mul_ukIntegrand_of_le_mul_prefixWeight {k v : ℕ}
    (x : Fin k → ℝ) {z C : ℝ} (hC : 0 ≤ C)
    (h : ∀ g : ℕ, g ≤ k → z ≤ C * prefixWeight k v g x) :
    z ≤ C * ukIntegrand k v x := by
  have haux : ∀ n : ℕ, n ≤ k → z ≤ C * ukIntegrandAux k v x n := by
    intro n hn
    induction n with
    | zero => simpa [ukIntegrandAux] using h 0 (Nat.zero_le k)
    | succ n ih =>
        rw [ukIntegrandAux, mul_min_of_nonneg _ _ hC]
        exact le_min (ih (by omega)) (h (n + 1) hn)
  exact haux k le_rfl

/-- Lemma 3.1(iii), repackaged pointwise in the exact integrand used by
`U_k`.  The hypothesis `hlog` is the only place where the prime-bin scale
enters. -/
theorem L_fin_prod_le_ukIntegrand {k v : ℕ} (p : Fin k → ℕ)
    (hprime : ∀ i, (p i).Prime) (hstrict : StrictMono p)
    (x : Fin k → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hlog : ∀ i, Real.log (p i) ≤ B * (2 : ℝ) ^ ((v : ℝ) * x i)) :
    L (∏ i : Fin k, p i) (Real.log 2) ≤
      ((B + 1) * (2 : ℝ) ^ k) * ukIntegrand k v x := by
  let ps : List ℕ := List.ofFn p
  have hpsPrime : ∀ q ∈ ps, q.Prime := by
    intro q hq
    change q ∈ List.ofFn p at hq
    rw [List.mem_ofFn'] at hq
    obtain ⟨i, rfl⟩ := hq
    exact hprime i
  have hpsStrict : ps.Pairwise (fun a b ↦ a < b) := by
    change (List.ofFn p).Pairwise (fun a b ↦ a < b)
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hstrict hij
  apply le_mul_ukIntegrand_of_le_mul_prefixWeight x
    (mul_nonneg (add_nonneg hB zero_le_one) (by positivity))
  intro g hg
  have hL := ford_lemma_three_one_iii hpsPrime hpsStrict
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) g
  have hprefix :
      Real.log (ps.take g).prod ≤
        B * ∑ i : Fin k,
          if i.val < g then (2 : ℝ) ^ ((v : ℝ) * x i) else 0 := by
    change Real.log ((List.ofFn p).take g).prod ≤ _
    rw [List.prod_take_ofFn]
    push_cast
    rw [Real.log_prod]
    · calc
        (∑ i with i.val < g, Real.log (p i)) ≤
            ∑ i with i.val < g,
              B * (2 : ℝ) ^ ((v : ℝ) * x i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hlog i
        _ = B * ∑ i : Fin k,
              if i.val < g then (2 : ℝ) ^ ((v : ℝ) * x i) else 0 := by
          rw [Finset.mul_sum]
          simp_rw [mul_ite, mul_zero]
          rw [← Finset.sum_filter]
    · intro i hi
      exact_mod_cast (hprime i).ne_zero
  have hsumNonneg :
      0 ≤ ∑ i : Fin k,
        if i.val < g then (2 : ℝ) ^ ((v : ℝ) * x i) else 0 := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have hlogtwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbracket :
      Real.log (ps.take g).prod + Real.log 2 ≤
        (B + 1) *
          ((∑ i : Fin k,
            if i.val < g then (2 : ℝ) ^ ((v : ℝ) * x i) else 0) + 1) := by
    nlinarith [mul_nonneg hB hsumNonneg]
  dsimp [ps] at hL
  simp only [List.length_ofFn, List.prod_ofFn] at hL
  calc
    L (∏ i : Fin k, p i) (Real.log 2) ≤
        (2 : ℝ) ^ (k - g) *
          (Real.log (List.ofFn p |>.take g).prod + Real.log 2) := hL
    _ ≤ (2 : ℝ) ^ (k - g) *
        ((B + 1) *
          ((∑ i : Fin k,
            if i.val < g then (2 : ℝ) ^ ((v : ℝ) * x i) else 0) + 1)) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = ((B + 1) * (2 : ℝ) ^ k) * prefixWeight k v g x := by
      unfold prefixWeight
      have hpow :
          (2 : ℝ) ^ (k - g) * (2 : ℝ) ^ g = (2 : ℝ) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hg]
      field_simp
      nlinarith

theorem L_orderedPrimeGrid_le_sample {y k r : ℕ} {A : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A)
    (hlogUpper : ∀ j : ℕ, 1 ≤ j →
      Real.log (greedyPrimeBinUpper j) ≤ A * (2 : ℝ) ^ j)
    {p : Fin k → ↥(Nat.primesLE (2 * y))} (hp : p ∈ orderedPrimeGrid y k) :
    L (∏ i : Fin k, (p i : ℕ)) (Real.log 2) ≤
      (((2 * A) + 1) * (2 : ℝ) ^ k) *
        ukIntegrand k r (greedyPrimeTupleSample r p) := by
  have hpPrime (i : Fin k) : (p i : ℕ).Prime :=
    Nat.prime_of_mem_primesLE (p i).property
  apply L_fin_prod_le_ukIntegrand (fun i ↦ (p i : ℕ)) hpPrime
    (mem_orderedPrimeGrid.mp hp) (greedyPrimeTupleSample r p)
    (mul_nonneg (by norm_num) hA)
  intro i
  let j := greedyPrimeBinIndex (p i)
  have hpUpper : (p i : ℕ) ≤ greedyPrimeBinUpper (j + 1) :=
    greedyPrimeBinIndex_spec (p i)
  have hpPos : (0 : ℝ) < (p i : ℕ) := by exact_mod_cast (hpPrime i).pos
  have huPos : (0 : ℝ) < greedyPrimeBinUpper (j + 1) := by
    exact_mod_cast (show 0 < greedyPrimeBinUpper (j + 1) by
      exact lt_of_lt_of_le (by omega : 0 < 2)
        (two_le_greedyPrimeBinUpper (by omega)))
  have hlogp : Real.log (p i : ℕ) ≤
      Real.log (greedyPrimeBinUpper (j + 1)) :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hpPos)
      (Set.mem_Ioi.mpr huPos) (by exact_mod_cast hpUpper)
  have hendpoint := hlogUpper (j + 1) (by omega)
  have hlower := greedyPrimeCellLower_bin_lower (p := (p i : ℕ)) hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hjexp : (j : ℝ) ≤ (r : ℝ) * greedyPrimeTupleSample r p i := by
    dsimp [greedyPrimeTupleSample]
    have := (div_le_iff₀ hrR).mp hlower
    nlinarith
  have hpow : (2 : ℝ) ^ j ≤
      (2 : ℝ) ^ ((r : ℝ) * greedyPrimeTupleSample r p i) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hjexp
  calc
    Real.log (p i : ℕ) ≤ Real.log (greedyPrimeBinUpper (j + 1)) := hlogp
    _ ≤ A * (2 : ℝ) ^ (j + 1) := hendpoint
    _ = (2 * A) * (2 : ℝ) ^ j := by rw [pow_succ]; ring
    _ ≤ (2 * A) *
        (2 : ℝ) ^ ((r : ℝ) * greedyPrimeTupleSample r p i) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hA)

/-- Lemma 3.5 at an arbitrary greedy top index `r`. -/
theorem Tk_le_mul_pow_uk_of_le_greedyUpper {y k r : ℕ} {A : ℝ}
    (hr : 0 < r) (htop : 2 * y ≤ greedyPrimeBinUpper r)
    (hA : 0 ≤ A)
    (hlogUpper : ∀ j : ℕ, 1 ≤ j →
      Real.log (greedyPrimeBinUpper j) ≤ A * (2 : ℝ) ^ j) :
    Tk y k ≤
      (((2 * A) + 1) * (2 : ℝ) ^ k) *
        (((r : ℝ) * Real.log 2) ^ k * uk k r) := by
  rw [Tk_eq_orderedPrimeGrid_sum]
  let C : ℝ := ((2 * A) + 1) * (2 : ℝ) ^ k
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hA) zero_le_one)
      (by positivity)
  calc
    (∑ p ∈ orderedPrimeGrid y k,
        L (∏ i : Fin k, (p i : ℕ)) (Real.log 2) *
          ∏ i : Fin k, (1 : ℝ) / (p i : ℕ)) ≤
        ∑ p ∈ orderedPrimeGrid y k,
          (C * ukIntegrand k r (greedyPrimeTupleSample r p)) *
            ∏ i : Fin k, (1 : ℝ) / (p i : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_right
        (L_orderedPrimeGrid_le_sample hr hA hlogUpper hp)
      positivity
    _ = C * (∑ p ∈ orderedPrimeGrid y k,
          (∏ i : Fin k, (1 : ℝ) / (p i : ℕ)) *
            ukIntegrand k r (greedyPrimeTupleSample r p)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ C * (((r : ℝ) * Real.log 2) ^ k * uk k r) := by
      exact mul_le_mul_of_nonneg_left
        (orderedPrimeGrid_weighted_uk_le hr htop) hC
    _ = (((2 * A) + 1) * (2 : ℝ) ^ k) *
        (((r : ℝ) * Real.log 2) ^ k * uk k r) := by rfl

/-! ## Changing the `v` parameter by a bounded additive amount -/

theorem prefixWeight_add_le_pow_mul {k v d g : ℕ}
    {x : Fin k → ℝ} (hx : x ∈ orderedSimplex k 0 1) :
    prefixWeight k (v + d) g x ≤
      (2 : ℝ) ^ d * prefixWeight k v g x := by
  unfold prefixWeight
  have hterm (i : Fin k) :
      (2 : ℝ) ^ (((v + d : ℕ) : ℝ) * x i) ≤
        (2 : ℝ) ^ d * (2 : ℝ) ^ ((v : ℝ) * x i) := by
    have hxi := (hx.1 i).2
    have hexp : (((v + d : ℕ) : ℝ) * x i) ≤ (v : ℝ) * x i + d := by
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg d) (hx.1 i).1]
    calc
      (2 : ℝ) ^ (((v + d : ℕ) : ℝ) * x i) ≤
          (2 : ℝ) ^ ((v : ℝ) * x i + d) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = (2 : ℝ) ^ d * (2 : ℝ) ^ ((v : ℝ) * x i) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
        ring
  have hsum :
      (∑ i : Fin k, if i.val < g then
          (2 : ℝ) ^ (((v + d : ℕ) : ℝ) * x i) else 0) ≤
        (2 : ℝ) ^ d *
          ∑ i : Fin k, if i.val < g then
            (2 : ℝ) ^ ((v : ℝ) * x i) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    split_ifs
    · exact hterm i
    · simp
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hnum :
      (∑ i : Fin k, if i.val < g then
          (2 : ℝ) ^ (((v + d : ℕ) : ℝ) * x i) else 0) + 1 ≤
        (2 : ℝ) ^ d *
          ((∑ i : Fin k, if i.val < g then
            (2 : ℝ) ^ ((v : ℝ) * x i) else 0) + 1) := by
    nlinarith
  calc
    ((∑ i : Fin k, if i.val < g then
        (2 : ℝ) ^ (((v + d : ℕ) : ℝ) * x i) else 0) + 1) /
          (2 : ℝ) ^ g ≤
        ((2 : ℝ) ^ d *
          ((∑ i : Fin k, if i.val < g then
            (2 : ℝ) ^ ((v : ℝ) * x i) else 0) + 1)) /
              (2 : ℝ) ^ g :=
      (div_le_div_iff_of_pos_right (by positivity : 0 < (2 : ℝ) ^ g)).2 hnum
    _ = (2 : ℝ) ^ d *
        (((∑ i : Fin k, if i.val < g then
          (2 : ℝ) ^ ((v : ℝ) * x i) else 0) + 1) /
            (2 : ℝ) ^ g) := by ring

theorem ukIntegrand_add_le_pow_mul {k v d : ℕ}
    {x : Fin k → ℝ} (hx : x ∈ orderedSimplex k 0 1) :
    ukIntegrand k (v + d) x ≤ (2 : ℝ) ^ d * ukIntegrand k v x := by
  have haux : ∀ g : ℕ,
      ukIntegrandAux k (v + d) x g ≤
        (2 : ℝ) ^ d * ukIntegrandAux k v x g := by
    intro g
    induction g with
    | zero => simpa [ukIntegrandAux] using prefixWeight_add_le_pow_mul (g := 0) hx
    | succ g ih =>
        simp only [ukIntegrandAux]
        rw [mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d)]
        exact min_le_min ih (prefixWeight_add_le_pow_mul (g := g + 1) hx)
  exact haux k

theorem uk_add_le_pow_mul (k v d : ℕ) :
    uk k (v + d) ≤ (2 : ℝ) ^ d * uk k v := by
  have hleft := ukIntegrand_integrableOn_orderedSimplex k (v + d)
  have hright := (ukIntegrand_integrableOn_orderedSimplex k v).const_mul ((2 : ℝ) ^ d)
  have hmono := MeasureTheory.setIntegral_mono_on hleft hright
    (measurableSet_orderedSimplex k 0 1)
    (fun x hx ↦ ukIntegrand_add_le_pow_mul hx)
  simpa only [uk, MeasureTheory.integral_const_mul] using hmono

theorem uk_nonneg (k v : ℕ) : 0 ≤ uk k v := by
  unfold uk
  exact MeasureTheory.setIntegral_nonneg (measurableSet_orderedSimplex k 0 1)
    (fun x hx ↦ ukIntegrand_nonneg k v x)

theorem fordBinIndex_log_log_bounds {y : ℕ}
    (hv : 1 ≤ fordBinIndex y) :
    (fordBinIndex y : ℝ) * Real.log 2 ≤
        Real.log (Real.log (2 * y)) ∧
      Real.log (Real.log (2 * y)) <
        ((fordBinIndex y : ℝ) + 1) * Real.log 2 := by
  let z := Real.log (Real.log (2 * y)) / Real.log 2
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : 1 ≤ z := by
    have hvpos : 0 < fordBinIndex y := by omega
    rw [fordBinIndex, Nat.floor_pos] at hvpos
    exact hvpos
  have hlower : (fordBinIndex y : ℝ) ≤ z := by
    simpa [fordBinIndex, z] using Nat.floor_le (show 0 ≤ z by linarith)
  have hupper : z < (fordBinIndex y : ℝ) + 1 := by
    simpa [fordBinIndex, z] using Nat.lt_floor_add_one z
  dsimp [z] at hlower hupper
  constructor
  · exact (le_div_iff₀ hlogtwo).mp hlower
  · exact (div_lt_iff₀ hlogtwo).mp hupper

theorem exists_nat_one_le_pow_two_ge (B : ℝ) :
    ∃ d : ℕ, 1 ≤ d ∧ B ≤ (2 : ℝ) ^ d := by
  have ht := tendsto_pow_atTop_atTop_of_one_lt
    (show (1 : ℝ) < 2 by norm_num)
  rw [Filter.tendsto_atTop_atTop] at ht
  obtain ⟨d, hd⟩ := ht B
  refine ⟨d + 1, by omega, hd (d + 1) (by omega)⟩

/-- The fixed additive enlargement of the Ford index reaches the top of
the prime range.  Its size depends only on the absolute endpoint-growth
constant, never on `y`. -/
theorem two_mul_le_greedyPrimeBinUpper_add {y d : ℕ} {A : ℝ}
    (hv : 1 ≤ fordBinIndex y) (hA : 0 < A)
    (hAd : 2 * A ≤ (2 : ℝ) ^ d)
    (hlower : ∀ j : ℕ, 1 ≤ j →
      (2 : ℝ) ^ j / A ≤ Real.log (greedyPrimeBinUpper j)) :
    2 * y ≤ greedyPrimeBinUpper (fordBinIndex y + d) := by
  let v := fordBinIndex y
  let r := v + d
  let t := Real.log (Real.log (2 * y))
  have hv' : 1 ≤ v := hv
  have hr : 1 ≤ r := by dsimp [r]; omega
  have htBounds := fordBinIndex_log_log_bounds hv
  have htUpper : t < ((v : ℝ) + 1) * Real.log 2 := by
    simpa [v, t] using htBounds.2
  have hy : 0 < y := by
    by_contra hy
    have hy0 : y = 0 := Nat.eq_zero_of_not_pos hy
    simp [fordBinIndex, hy0] at hv
  have htwoY : (1 : ℝ) < 2 * y := by exact_mod_cast (show 1 < 2 * y by omega)
  have hlogY : 0 < Real.log (2 * y) := Real.log_pos htwoY
  have hexpUpper := (Real.exp_lt_exp).2 htUpper
  have hlogYUpper : Real.log (2 * y) < (2 : ℝ) ^ (v + 1) := by
    calc
      Real.log (2 * y) = Real.exp t := by
        dsimp [t]
        rw [Real.exp_log hlogY]
      _ < Real.exp (((v + 1 : ℕ) : ℝ) * Real.log 2) := by
        convert hexpUpper using 1
        push_cast
        ring
      _ = (2 : ℝ) ^ (v + 1) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hpowScale : A * (2 : ℝ) ^ (v + 1) ≤ (2 : ℝ) ^ r := by
    calc
      A * (2 : ℝ) ^ (v + 1) = (2 * A) * (2 : ℝ) ^ v := by
        rw [pow_succ]
        ring
      _ ≤ (2 : ℝ) ^ d * (2 : ℝ) ^ v :=
        mul_le_mul_of_nonneg_right hAd (by positivity)
      _ = (2 : ℝ) ^ r := by
        dsimp [r]
        rw [pow_add]
        ring
  have hpowDiv : (2 : ℝ) ^ (v + 1) ≤ (2 : ℝ) ^ r / A := by
    exact (le_div_iff₀ hA).2 (by simpa [mul_comm] using hpowScale)
  have hendpoint := hlower r hr
  have hlogCompare : Real.log (2 * y : ℝ) <
      Real.log (greedyPrimeBinUpper r) :=
    hlogYUpper.trans_le (hpowDiv.trans hendpoint)
  have huPos : (0 : ℝ) < greedyPrimeBinUpper r := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (two_le_greedyPrimeBinUpper hr))
  have hcast : (2 * y : ℝ) < greedyPrimeBinUpper r :=
    (Real.strictMonoOn_log.lt_iff_lt (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr huPos)).mp hlogCompare
  exact_mod_cast hcast.le

/-- The harmless shift from `v` to `v+d` costs only an absolute factor in
the `((v+d) log 2)^k` scale when `k ≤ 10v`. -/
theorem ford_shifted_scale_pow_le {v d k : ℕ} {t : ℝ}
    (hv : 1 ≤ v) (hk : k ≤ 10 * v) (ht : (v : ℝ) * Real.log 2 ≤ t) :
    (((v + d : ℕ) : ℝ) * Real.log 2) ^ k ≤
      Real.exp (10 * (d : ℝ)) * t ^ k := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvR : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  have ht0 : 0 ≤ t := le_trans (mul_nonneg (by positivity) hlogtwo.le) ht
  have hfactor0 : 0 ≤ 1 + (d : ℝ) / v := by positivity
  have hrewrite :
      (((v + d : ℕ) : ℝ) * Real.log 2) =
        (1 + (d : ℝ) / v) * ((v : ℝ) * Real.log 2) := by
    push_cast
    field_simp
  have honeexp : 1 + (d : ℝ) / v ≤ Real.exp ((d : ℝ) / v) := by
    simpa [add_comm] using Real.add_one_le_exp ((d : ℝ) / v)
  have hbase : (((v + d : ℕ) : ℝ) * Real.log 2) ≤
      Real.exp ((d : ℝ) / v) * t := by
    rw [hrewrite]
    calc
      (1 + (d : ℝ) / v) * ((v : ℝ) * Real.log 2) ≤
          (1 + (d : ℝ) / v) * t :=
        mul_le_mul_of_nonneg_left ht hfactor0
      _ ≤ Real.exp ((d : ℝ) / v) * t :=
        mul_le_mul_of_nonneg_right honeexp ht0
  have hpow := pow_le_pow_left₀ (by positivity :
      0 ≤ (((v + d : ℕ) : ℝ) * Real.log 2)) hbase k
  have hexpExponent : (k : ℝ) * ((d : ℝ) / v) ≤ 10 * (d : ℝ) := by
    have hkR : (k : ℝ) ≤ 10 * (v : ℝ) := by exact_mod_cast hk
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hvR).2
    have hm := mul_le_mul_of_nonneg_right hkR
      (show (0 : ℝ) ≤ d by positivity)
    nlinarith
  have hexp : Real.exp ((d : ℝ) / v) ^ k ≤ Real.exp (10 * (d : ℝ)) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_monotone (by simpa [mul_comm] using hexpExponent)
  calc
    (((v + d : ℕ) : ℝ) * Real.log 2) ^ k ≤
        (Real.exp ((d : ℝ) / v) * t) ^ k := hpow
    _ = Real.exp ((d : ℝ) / v) ^ k * t ^ k := by rw [mul_pow]
    _ ≤ Real.exp (10 * (d : ℝ)) * t ^ k :=
      mul_le_mul_of_nonneg_right hexp (pow_nonneg ht0 k)

/-- **Ford, Lemma 3.5.**  For `v = ⌊log log (2y) / log 2⌋` and
`k ≤ 10v`, the squarefree prime-factor sum is bounded by the Ford simplex
integral.  The constant is absolute (in particular, independent of `y`
and `k`). -/
theorem ford_lemma_three_five :
    ∃ C : ℝ, 0 < C ∧ ∀ y k : ℕ,
      1 ≤ fordBinIndex y → k ≤ 10 * fordBinIndex y →
        Tk y k ≤ C *
          (2 * Real.log (Real.log (2 * y))) ^ k *
            uk k (fordBinIndex y) := by
  obtain ⟨A, hA, hgrowth⟩ := exists_greedyPrimeBin_log_growth
  obtain ⟨d, hd, hAd⟩ := exists_nat_one_le_pow_two_ge (2 * A)
  let C := ((2 * A) + 1) * Real.exp (10 * (d : ℝ)) * (2 : ℝ) ^ d
  have hA0 : 0 ≤ A := hA.le
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos (by linarith) (Real.exp_pos _)) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro y k hv hk
  let v := fordBinIndex y
  let t := Real.log (Real.log (2 * y))
  have hv' : 1 ≤ v := hv
  have hk' : k ≤ 10 * v := hk
  have htBounds := fordBinIndex_log_log_bounds hv
  have ht : (v : ℝ) * Real.log 2 ≤ t := by
    simpa [v, t] using htBounds.1
  have htop : 2 * y ≤ greedyPrimeBinUpper (v + d) := by
    simpa [v] using two_mul_le_greedyPrimeBinUpper_add hv hA hAd
      (fun j hj ↦ (hgrowth j hj).1)
  have hmain := Tk_le_mul_pow_uk_of_le_greedyUpper
    (y := y) (k := k) (r := v + d) (A := A)
    (by omega : 0 < v + d) htop hA0
    (fun j hj ↦ (hgrowth j hj).2)
  have hscale :
      (((v + d : ℕ) : ℝ) * Real.log 2) ^ k ≤
        Real.exp (10 * (d : ℝ)) * t ^ k :=
    ford_shifted_scale_pow_le hv' hk' ht
  have huk : uk k (v + d) ≤ (2 : ℝ) ^ d * uk k v :=
    uk_add_le_pow_mul k v d
  have hinner :
      (((v + d : ℕ) : ℝ) * Real.log 2) ^ k * uk k (v + d) ≤
        (Real.exp (10 * (d : ℝ)) * t ^ k) *
          ((2 : ℝ) ^ d * uk k v) := by
    exact mul_le_mul hscale huk (uk_nonneg k (v + d))
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg (le_trans
        (mul_nonneg (by positivity) (Real.log_pos (by norm_num)).le) ht) k))
  have hcoeff : 0 ≤ ((2 * A) + 1) * (2 : ℝ) ^ k := by positivity
  calc
    Tk y k ≤ (((2 * A) + 1) * (2 : ℝ) ^ k) *
        ((((v + d : ℕ) : ℝ) * Real.log 2) ^ k * uk k (v + d)) := hmain
    _ ≤ (((2 * A) + 1) * (2 : ℝ) ^ k) *
        ((Real.exp (10 * (d : ℝ)) * t ^ k) *
          ((2 : ℝ) ^ d * uk k v)) :=
      mul_le_mul_of_nonneg_left hinner hcoeff
    _ = C * (2 * Real.log (Real.log (2 * y))) ^ k *
        uk k (fordBinIndex y) := by
      dsimp [C, v, t]
      rw [mul_pow]
      ring

theorem Tk_nonneg (y k : ℕ) : 0 ≤ Tk y k := by
  unfold Tk
  apply Finset.sum_nonneg
  intro s hs
  exact div_nonneg (L_nonneg _ _) (by positivity)

/-- Exact decomposition of the total squarefree `L(a)/a` sum by the number
of prime factors. -/
theorem sum_Tk_eq (y : ℕ) :
    ∑ k ∈ Finset.range ((Nat.primesLE (2 * y)).card + 1), Tk y k =
      ∑ s ∈ (Nat.primesLE (2 * y)).powerset,
        L (s.prod (fun p : ℕ ↦ p)) (Real.log 2) /
          ((s.prod (fun p : ℕ ↦ p) : ℕ) : ℝ) := by
  classical
  simp only [Tk]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hcard : s.card < (Nat.primesLE (2 * y)).card + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_card (Finset.mem_powerset.mp hs))
  have hcard' : s.card < (2 * y).primeCounting + 1 := by
    simpa only [Nat.primesLE_card_eq_primeCounting] using hcard
  simp [hcard']

end Erdos896.Ford

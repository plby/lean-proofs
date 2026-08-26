import ErdosProblems.Erdos260.Completion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DeepMind Formal Conjectures compatible endpoint

The theorem `erdos_260` has exactly the right-hand-side type used by
`FormalConjectures/ErdosProblems/260.lean`: integer-valued sequence, the
original division by `n`, a supplied `HasSum`, and an `Irrational` conclusion.
This project intentionally does not depend on the Formal Conjectures package.
-/

noncomputable section

open Filter Set
open scoped BigOperators

namespace Erdos260

/-- Integer-exponent summand appearing in the DeepMind statement. -/
def integerSequenceTerm (a : ℕ → ℤ) (n : ℕ) : ℝ :=
  (a n : ℝ) / (2 : ℝ) ^ a n

/-- Positive natural tail after deleting a finite integer-valued prefix. -/
def positiveTail (a : ℕ → ℤ) (N n : ℕ) : ℕ :=
  Int.toNat (a (n + N))

theorem eventually_positive_of_tendsto_ratio (a : ℕ → ℤ)
    (hgrowth : Tendsto (fun n => (a n : ℝ) / n) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 0 < a n := by
  filter_upwards [hgrowth.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hratio hn
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  rcases (div_pos_iff.mp hratio) with hsame | hsame
  · exact_mod_cast hsame.1
  · exact (not_lt_of_ge hn_real.le hsame.2).elim

theorem positiveTail_strictMono (a : ℕ → ℤ) (N : ℕ)
    (ha : StrictMono a) (hpos : ∀ n ≥ N, 0 < a n) :
    StrictMono (positiveTail a N) := by
  intro n m hnm
  simp only [positiveTail]
  rw [Int.toNat_lt_toNat (hpos (m + N) (by omega))]
  exact ha (by omega)

theorem positiveTail_positive (a : ℕ → ℤ) (N : ℕ)
    (hpos : ∀ n ≥ N, 0 < a n) :
    ∀ n, 0 < positiveTail a N n := by
  intro n
  rw [positiveTail, Int.lt_toNat]
  exact hpos (n + N) (by omega)

theorem positiveTail_growth (a : ℕ → ℤ) (N : ℕ)
    (hgrowth : Tendsto (fun n => (a n : ℝ) / n) atTop atTop)
    (hpos : ∀ n ≥ N, 0 < a n) :
    Tendsto (fun n => (positiveTail a N n : ℝ) / (n + 1)) atTop atTop := by
  have hshift :
      Tendsto (fun n : ℕ => (a (n + N) : ℝ) / (n + N)) atTop atTop := by
    simpa [Function.comp_def] using hgrowth.comp (tendsto_add_atTop_nat N)
  have hfactor :
      Tendsto (fun n : ℕ => ((n + N : ℕ) : ℝ) / (n + 1)) atTop (nhds 1) := by
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (N : ℝ) 1 1 (d := 1) one_ne_zero)
  apply (hshift.atTop_mul_pos zero_lt_one hfactor).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnN_pos : (0 : ℝ) < ((n + N : ℕ) : ℝ) := by positivity
  have htail_cast : (positiveTail a N n : ℝ) = (a (n + N) : ℝ) := by
    have htail_int : (positiveTail a N n : ℤ) = a (n + N) := by
      exact Int.toNat_of_nonneg (hpos (n + N) (by omega)).le
    exact_mod_cast htail_int
  rw [htail_cast]
  field_simp
  simp only [Nat.cast_add]

theorem finite_integer_prefix_is_rational (a : ℕ → ℤ) (N : ℕ) :
    ∃ q : ℚ, (q : ℝ) = ∑ n ∈ Finset.range N, integerSequenceTerm a n := by
  refine ⟨∑ n ∈ Finset.range N, (a n : ℚ) / (2 : ℚ) ^ a n, ?_⟩
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, Rat.cast_zpow,
    integerSequenceTerm]

theorem irrational_add_rational_iff (x : ℝ) (q : ℚ) :
    Irrational (x + q) ↔ Irrational x := by
  exact irrational_add_ratCast_iff

/-- Exact RHS of DeepMind Formal Conjectures' Erdős Problem 260 statement. -/
def deepmindStatement : Prop :=
  ∀ a : ℕ → ℤ, ∀ s : ℝ,
    StrictMono a →
    Tendsto (fun n => (a n : ℝ) / n) atTop atTop →
    HasSum (fun n => (a n : ℝ) / 2 ^ a n) s →
    Irrational s

/-- DeepMind-compatible public endpoint. -/
theorem erdos_260 :
    ∀ a : ℕ → ℤ, ∀ s : ℝ,
      StrictMono a →
      Tendsto (fun n => (a n : ℝ) / n) atTop atTop →
      HasSum (fun n => (a n : ℝ) / 2 ^ a n) s →
      Irrational s := by
  intro a s ha hgrowth hsum
  obtain ⟨N, hpos⟩ :=
    (eventually_atTop.1 (eventually_positive_of_tendsto_ratio a hgrowth))
  let b := positiveTail a N
  have hbmono : StrictMono b := positiveTail_strictMono a N ha hpos
  have hbpos : ∀ n, 0 < b n := positiveTail_positive a N hpos
  have hbgrowth :
      Tendsto (fun n => (b n : ℝ) / (n + 1)) atTop atTop :=
    positiveTail_growth a N hgrowth hpos
  have hirrTail : Irrational (∑' n : ℕ, natSequenceTerm b n) :=
    cor_erdos260 b hbmono hbpos hbgrowth
  have hsum' : HasSum (integerSequenceTerm a) s := hsum
  let prefixSum : ℝ := ∑ n ∈ Finset.range N, integerSequenceTerm a n
  have htailRaw :
      HasSum (fun n => integerSequenceTerm a (n + N)) (s - prefixSum) := by
    simpa [prefixSum] using (hasSum_nat_add_iff' N).2 hsum'
  have hterm (n : ℕ) :
      natSequenceTerm b n = integerSequenceTerm a (n + N) := by
    have han : 0 < a (n + N) := hpos (n + N) (by omega)
    have hnat : (b n : ℤ) = a (n + N) := by
      simpa [b, positiveTail] using Int.toNat_of_nonneg han.le
    have hnum : (b n : ℝ) = (a (n + N) : ℝ) := by
      exact_mod_cast hnat
    have hpow : (2 : ℝ) ^ b n = (2 : ℝ) ^ a (n + N) := by
      rw [← hnat, zpow_natCast]
    simp only [natSequenceTerm, integerSequenceTerm, hnum, hpow]
  have htailNat :
      HasSum (fun n => natSequenceTerm b n) (s - prefixSum) :=
    htailRaw.congr_fun hterm
  obtain ⟨q, hq⟩ := finite_integer_prefix_is_rational a N
  have hs_decomp : s = (∑' n : ℕ, natSequenceTerm b n) + (q : ℝ) := by
    rw [htailNat.tsum_eq, hq]
    exact (sub_add_cancel s prefixSum).symm
  rw [hs_decomp]
  exact (irrational_add_rational_iff _ q).2 hirrTail

end Erdos260

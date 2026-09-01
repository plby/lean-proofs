/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos491.Mate
import ErdosProblems.Erdos491.Limit

/-!
# Erdős Problem 491

Wirsing's affirmative resolution of Problem 491: an arithmetically additive
real-valued function whose consecutive differences are bounded differs from
a constant multiple of `log` by a bounded function.

The detailed mathematical proof and source discussion are in `tex/491.tex`.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace Erdos491

noncomputable section

/-- Arithmetic additivity on coprime natural numbers. -/
def CoprimeAdditive (f : ℕ → ℝ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a.Coprime b → f (a * b) = f a + f b

/-- Complete additivity restricted to the positive natural numbers.  The
restriction is essential: imposing this equation at zero would force the
function to vanish. -/
def PosCompletelyAdditive (f : ℕ → ℝ) : Prop :=
  ∀ ⦃a b : ℕ⦄, 0 < a → 0 < b → f (a * b) = f a + f b

/-- The strict bounded-forward-difference hypothesis printed in Problem 491. -/
def HasBoundedForwardDifference (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, |f (n + 1) - f n| < C

/-- The literal `c * log n + O(1)` conclusion of Problem 491. -/
def HasLogarithmicMainTerm (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ,
    (fun n : ℕ ↦ f n - c * Real.log (n : ℝ)) =O[atTop]
      (fun _ : ℕ ↦ (1 : ℝ))

/-- The exact yes/no assertion posed in Problem 491. -/
def ProblemStatement : Prop :=
  ∀ f : ℕ → ℝ,
    CoprimeAdditive f →
    HasBoundedForwardDifference f →
    HasLogarithmicMainTerm f

lemma CoprimeAdditive.one_eq_zero {f : ℕ → ℝ} (hf : CoprimeAdditive f) :
    f 1 = 0 := by
  have h := hf (a := 1) (b := 1) (by simp)
  simpa using h

lemma PosCompletelyAdditive.one_eq_zero {f : ℕ → ℝ}
    (hf : PosCompletelyAdditive f) : f 1 = 0 := by
  have h := hf (a := 1) (b := 1) (by simp) (by simp)
  simpa using h

/-- A uniform adjacent-difference bound telescopes across any finite interval. -/
lemma abs_sub_le_mul_of_adjacent
    {f : ℕ → ℝ} {M : ℝ} (_hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M) (a d : ℕ) :
    |f (a + d) - f a| ≤ (d : ℝ) * M := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        |f (a + (d + 1)) - f a|
            = |(f (a + d + 1) - f (a + d)) + (f (a + d) - f a)| := by
                congr 1
                ring_nf
        _ ≤ |f (a + d + 1) - f (a + d)| + |f (a + d) - f a| :=
              abs_add_le _ _
        _ ≤ M + (d : ℝ) * M := add_le_add (hgap (a + d)) ih
        _ = ((d + 1 : ℕ) : ℝ) * M := by
              push_cast
              ring

/-- The strict hypothesis printed in the problem supplies a nonnegative weak
bound suitable for the quantitative argument. -/
lemma exists_nonneg_adjacent_bound_of_strict
    {f : ℕ → ℝ} (hgap : ∃ C : ℝ, ∀ n : ℕ, |f (n + 1) - f n| < C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, |f (n + 1) - f n| ≤ M := by
  obtain ⟨C, hC⟩ := hgap
  have hC0 : 0 ≤ C := le_of_lt (lt_of_le_of_lt (abs_nonneg _) (hC 0))
  exact ⟨C, hC0, fun n ↦ (hC n).le⟩

private lemma toMateCoprimeAdditive {f : ℕ → ℝ}
    (hf : CoprimeAdditive f) :
    Erdos491MateScratch.CoprimeAdditive f := by
  intro a b _ _ hab
  exact hf hab

/-- Máté's first estimate, exposed with the public additivity definition. -/
lemma mate_one
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) (hcop : s.Coprime (n - 1)) :
    |f (n ^ s) - (s : ℝ) * f n| ≤ 2 * (s : ℝ) * M := by
  exact Erdos491MateScratch.mate1 (toMateCoprimeAdditive hf) hM
    (fun n _ ↦ hgap n) n s hn hs hcop

/-- Máté's dyadic estimate. -/
lemma mate_two
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n k : ℕ) (hn : 1 ≤ n) :
    |f (n ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f n| ≤
      4 * ((2 ^ k : ℕ) : ℝ) * M := by
  exact Erdos491MateScratch.mate2 (toMateCoprimeAdditive hf) hM
    (fun n _ ↦ hgap n) n k hn

/-- Máté's power-gap estimate. -/
lemma mate_three
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n s t : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    |f (n ^ t) - f (n ^ s)| ≤
      4 * (Nat.dist t s : ℝ) * (n : ℝ) * M := by
  exact Erdos491MateScratch.mate3 (toMateCoprimeAdditive hf) hM
    (fun n _ ↦ hgap n) n s t hn hs ht

/-- A uniform explicit residual bound on positive integers yields the exact
`O(1)` conclusion; the value at zero is irrelevant to `atTop`. -/
lemma hasLogarithmicMainTerm_of_explicit_bound {f : ℕ → ℝ}
    (h : ∃ c B : ℝ, 0 ≤ B ∧
      ∀ n : ℕ, 0 < n → |f n - c * Real.log (n : ℝ)| ≤ B) :
    HasLogarithmicMainTerm f := by
  obtain ⟨c, B, _, hbound⟩ := h
  refine ⟨c, ?_⟩
  rw [isBigO_iff]
  refine ⟨B, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using hbound n (by omega)

lemma posCompletelyAdditive_log :
    PosCompletelyAdditive (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  intro a b ha hb
  dsimp
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]

lemma PosCompletelyAdditive.sub_const_mul_log
    {f : ℕ → ℝ} (hf : PosCompletelyAdditive f) (c : ℝ) :
    PosCompletelyAdditive
      (fun n : ℕ ↦ f n - c * Real.log (n : ℝ)) := by
  intro a b ha hb
  dsimp
  rw [hf ha hb, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
  ring

/-- Power homogeneity of a completely additive function. -/
lemma PosCompletelyAdditive.pow
    {f : ℕ → ℝ} (hf : PosCompletelyAdditive f)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    f (n ^ k) = (k : ℝ) * f n := by
  induction k with
  | zero => simp [hf.one_eq_zero]
  | succ k ih =>
      rw [pow_succ, hf (pow_pos hn k) hn, ih]
      push_cast
      ring

/-- A bounded completely additive real function is identically zero on the
positive natural numbers. -/
lemma PosCompletelyAdditive.eq_zero_of_bounded
    {f : ℕ → ℝ} (hf : PosCompletelyAdditive f) {B : ℝ}
    (hB : ∀ n : ℕ, 0 < n → |f n| ≤ B) :
    ∀ n : ℕ, 0 < n → f n = 0 := by
  intro n hn
  by_contra hne
  have habs : 0 < |f n| := abs_pos.mpr hne
  obtain ⟨k : ℕ, hk⟩ := exists_nat_gt (B / |f n|)
  have hkreal : B / |f n| < (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 ≤ (k : ℝ) := by positivity
  have hmul : B < (k : ℝ) * |f n| := by
    exact (div_lt_iff₀ habs).mp hkreal
  have hpow := hB (n ^ k) (pow_pos hn k)
  rw [hf.pow hn k, abs_mul, abs_of_nonneg hkpos] at hpow
  exact (not_lt_of_ge hpow) hmul

/-- A completely additive function that vanishes at every prime vanishes at
every positive integer. -/
lemma PosCompletelyAdditive.eq_zero_of_prime
    {f : ℕ → ℝ} (hf : PosCompletelyAdditive f)
    (hprime : ∀ p : ℕ, p.Prime → f p = 0) :
    ∀ n : ℕ, 0 < n → f n = 0 := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro _
      rw [hf.pow hp.pos k, hprime p hp, mul_zero]
  | zero => simp
  | one => simpa using hf.one_eq_zero
  | coprime a b ha hb hab hia hib =>
      intro _
      rw [hf (by omega) (by omega), hia (by omega), hib (by omega), add_zero]

/-- Binary recursion gives the elementary logarithmic growth bound used at
the start of the rigidity argument. -/
lemma PosCompletelyAdditive.abs_le_natLog_two_mul
    {f : ℕ → ℝ} (hf : PosCompletelyAdditive f) {K : ℝ} (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ K) :
    ∀ n : ℕ, 0 < n →
      |f n| ≤ (Nat.log 2 n : ℝ) * (|f 2| + K) := by
  intro n
  induction n using Nat.binaryRecFromOne with
  | zero => simp
  | one => simp [hf.one_eq_zero]
  | bit b n hn ih =>
      intro _
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hcoeff : 0 ≤ |f 2| + K := add_nonneg (abs_nonneg _) hK
      have hlog : Nat.log 2 (Nat.bit b n) = Nat.log 2 n + 1 :=
        Nat.log_two_bit hn
      cases b with
      | false =>
          simp only [Nat.bit_false_apply] at hlog ⊢
          have hadd := hf (a := 2) (b := n) (by omega) hnpos
          rw [hadd]
          calc
            |f 2 + f n| ≤ |f 2| + |f n| := abs_add_le _ _
            _ ≤ |f 2| + (Nat.log 2 n : ℝ) * (|f 2| + K) :=
              add_le_add le_rfl (ih hnpos)
            _ ≤ ((Nat.log 2 n : ℝ) + 1) * (|f 2| + K) := by
              nlinarith [abs_nonneg (f 2)]
            _ = (Nat.log 2 (2 * n) : ℝ) * (|f 2| + K) := by
              rw [hlog]
              push_cast
              rfl
      | true =>
          simp only [Nat.bit_true_apply] at hlog ⊢
          have hadd := hf (a := 2) (b := n) (by omega) hnpos
          have hstep := hgap (2 * n)
          calc
            |f (2 * n + 1)|
                = |(f (2 * n + 1) - f (2 * n)) + f (2 * n)| := by
                    congr 1
                    ring
            _ ≤ |f (2 * n + 1) - f (2 * n)| + |f (2 * n)| :=
              abs_add_le _ _
            _ ≤ K + |f (2 * n)| :=
              add_le_add hstep le_rfl
            _ = K + |f 2 + f n| := by rw [hadd]
            _ ≤ K + (|f 2| + |f n|) :=
              add_le_add le_rfl (abs_add_le _ _)
            _ ≤ K + (|f 2| + (Nat.log 2 n : ℝ) * (|f 2| + K)) := by
              gcongr
              exact ih hnpos
            _ = ((Nat.log 2 n : ℝ) + 1) * (|f 2| + K) := by ring
            _ = (Nat.log 2 (2 * n + 1) : ℝ) * (|f 2| + K) := by
              rw [hlog]
              push_cast
              rfl

/-- A quantitative one-sided Cauchy estimate gives a limit with the same
pointwise tail estimate.  This is the abstract dyadic-limit step in Máté's
construction. -/
lemma tendsto_of_geometric_tail_bound (A : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ k l : ℕ, k ≤ l → |A l - A k| ≤ C / (2 : ℝ) ^ k) :
    ∃ g : ℝ, Tendsto A atTop (𝓝 g) ∧
      ∀ k : ℕ, |A k - g| ≤ C / (2 : ℝ) ^ k := by
  have hzero : Tendsto (fun k : ℕ => C / (2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hCauchy : CauchySeq A := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases Metric.tendsto_atTop.mp hzero ε hε with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total m n with hmn | hnm
    · rw [Real.dist_eq, abs_sub_comm]
      exact (hA m n hmn).trans_lt (by
        simpa [Real.dist_eq, abs_of_nonneg hC] using hN m hm)
    · rw [Real.dist_eq]
      exact (hA n m hnm).trans_lt (by
        simpa [Real.dist_eq, abs_of_nonneg hC] using hN n hn)
  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨g, hg⟩
  refine ⟨g, hg, fun k => ?_⟩
  have hlim : Tendsto (fun l : ℕ => |A l - A k|) atTop (𝓝 |g - A k|) :=
    (hg.sub tendsto_const_nhds).abs
  rw [abs_sub_comm]
  exact le_of_tendsto hlim <|
    Filter.eventually_atTop.2 ⟨k, fun l hl => hA k l hl⟩

/-- The normalized dyadic values used in Máté's construction. -/
def dyadicValue (f : ℕ → ℝ) (n k : ℕ) : ℝ :=
  f (n ^ (2 ^ k)) / (2 : ℝ) ^ k

/-- Máté's second estimate gives the quantitative Cauchy bound for the
normalized dyadic values. -/
lemma dyadicValue_tail
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n k l : ℕ) (hn : 0 < n) (hkl : k ≤ l) :
    |dyadicValue f n l - dyadicValue f n k| ≤
      4 * M / (2 : ℝ) ^ k := by
  have hpow : (n ^ (2 ^ k)) ^ (2 ^ (l - k)) = n ^ (2 ^ l) := by
    rw [← pow_mul, ← pow_add]
    congr 2
    omega
  have hmate := mate_two hf hM hgap (n ^ (2 ^ k)) (l - k)
    (show 1 ≤ n ^ (2 ^ k) by exact (pow_pos hn _))
  rw [hpow] at hmate
  have htwo : (((2 ^ (l - k) : ℕ) : ℝ)) = (2 : ℝ) ^ (l - k) := by
    norm_num
  rw [htwo] at hmate
  simp only [dyadicValue]
  have hden : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hscale : f (n ^ (2 ^ k)) / (2 : ℝ) ^ k =
      (f (n ^ (2 ^ k)) * (2 : ℝ) ^ (l - k)) / (2 : ℝ) ^ l := by
    have hpowers : (2 : ℝ) ^ l =
        (2 : ℝ) ^ k * (2 : ℝ) ^ (l - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkl]
    field_simp
    rw [hpowers]
    ring
  rw [hscale, ← sub_div, abs_div]
  rw [abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |f (n ^ (2 ^ l)) - f (n ^ (2 ^ k)) * (2 : ℝ) ^ (l - k)|
        = |f (n ^ (2 ^ l)) - (2 : ℝ) ^ (l - k) *
            f (n ^ (2 ^ k))| := by ring_nf
    _ ≤ 4 * (2 : ℝ) ^ (l - k) * M := hmate
    _ = (4 * M / (2 : ℝ) ^ k) * (2 : ℝ) ^ l := by
      have hpowers : (2 : ℝ) ^ l =
          (2 : ℝ) ^ k * (2 : ℝ) ^ (l - k) := by
        rw [← pow_add, Nat.add_sub_of_le hkl]
      rw [hpowers]
      field_simp

/-- Every positive base has a dyadic limit, with Máté's uniform tail
estimate. -/
lemma exists_dyadic_limit
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M) (n : ℕ) (hn : 0 < n) :
    ∃ g : ℝ, Tendsto (dyadicValue f n) atTop (𝓝 g) ∧
      ∀ k : ℕ, |dyadicValue f n k - g| ≤ 4 * M / (2 : ℝ) ^ k := by
  exact tendsto_of_geometric_tail_bound (dyadicValue f n) (4 * M)
    (mul_nonneg (by norm_num) hM)
    (fun k l hkl ↦ dyadicValue_tail hf hM hgap n k l hn hkl)

/-- Normalized values at two positive exponents are close when the exponents
are a bounded distance apart.  This is the quantitative local-oscillation
estimate used to pass from Máté's sparse grids to every exponent. -/
lemma normalized_power_sub_le
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n t v : ℕ) (hn : 0 < n) (ht : 0 < t) (hv : 0 < v) :
    |f (n ^ t) / (t : ℝ) - f (n ^ v) / (v : ℝ)| ≤
      (4 * (Nat.dist t v : ℝ) * (n : ℝ) * M +
        (|f n| + 4 * (n : ℝ) * M) * (Nat.dist t v : ℝ)) / (t : ℝ) := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hd := mate_three hf hM hgap n t v hn ht hv
  have hvstep := mate_three hf hM hgap n 1 v hn (by omega) hv
  have hdistOne : (Nat.dist v 1 : ℝ) ≤ (v : ℝ) := by
    rw [Nat.dist_eq_sub_of_le_right (by omega)]
    exact_mod_cast Nat.sub_le v 1
  have hvalue : |f (n ^ v)| ≤
      (v : ℝ) * (|f n| + 4 * (n : ℝ) * M) := by
    calc
      |f (n ^ v)| = |(f (n ^ v) - f n) + f n| := by
        congr 1
        ring
      _ ≤ |f (n ^ v) - f n| + |f n| := abs_add_le _ _
      _ ≤ 4 * (Nat.dist v 1 : ℝ) * (n : ℝ) * M + |f n| :=
        add_le_add (by simpa using hvstep) le_rfl
      _ ≤ 4 * (v : ℝ) * (n : ℝ) * M + |f n| := by
        gcongr
      _ ≤ (v : ℝ) * (|f n| + 4 * (n : ℝ) * M) := by
        have hvone : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
        have habs : 0 ≤ |f n| := abs_nonneg _
        nlinarith
  have hvalueNorm : |f (n ^ v) / (v : ℝ)| ≤
      |f n| + 4 * (n : ℝ) * M := by
    rw [abs_div, abs_of_pos hvR]
    exact (div_le_iff₀ hvR).2 (by simpa [mul_comm] using hvalue)
  have hcastdist : |(v : ℝ) - (t : ℝ)| = (Nat.dist t v : ℝ) := by
    rcases le_total t v with htv | hvt
    · have hcast : (t : ℝ) ≤ (v : ℝ) := by exact_mod_cast htv
      rw [Nat.dist_eq_sub_of_le htv, abs_of_nonneg (sub_nonneg.mpr hcast),
        Nat.cast_sub htv]
    · have hcast : (v : ℝ) ≤ (t : ℝ) := by exact_mod_cast hvt
      rw [Nat.dist_eq_sub_of_le_right hvt, abs_of_nonpos (sub_nonpos.mpr hcast),
        Nat.cast_sub hvt]
      ring
  have hratio : |(v : ℝ) / (t : ℝ) - 1| =
      (Nat.dist t v : ℝ) / (t : ℝ) := by
    have heq : (v : ℝ) / (t : ℝ) - 1 =
        ((v : ℝ) - (t : ℝ)) / (t : ℝ) := by
      field_simp [htR.ne']
    rw [heq, abs_div, abs_of_pos htR, hcastdist]
  have hid : f (n ^ t) / (t : ℝ) - f (n ^ v) / (v : ℝ) =
      (f (n ^ t) - f (n ^ v)) / (t : ℝ) +
        (f (n ^ v) / (v : ℝ)) * ((v : ℝ) / (t : ℝ) - 1) := by
    field_simp
    ring
  rw [hid]
  calc
    |(f (n ^ t) - f (n ^ v)) / (t : ℝ) +
        (f (n ^ v) / (v : ℝ)) * ((v : ℝ) / (t : ℝ) - 1)|
        ≤ |(f (n ^ t) - f (n ^ v)) / (t : ℝ)| +
          |(f (n ^ v) / (v : ℝ)) * ((v : ℝ) / (t : ℝ) - 1)| :=
            abs_add_le _ _
    _ = |f (n ^ t) - f (n ^ v)| / (t : ℝ) +
          |f (n ^ v) / (v : ℝ)| *
            ((Nat.dist t v : ℝ) / (t : ℝ)) := by
      rw [abs_div, abs_of_pos htR, abs_mul, hratio]
    _ ≤ (4 * (Nat.dist t v : ℝ) * (n : ℝ) * M) / (t : ℝ) +
          (|f n| + 4 * (n : ℝ) * M) *
            ((Nat.dist t v : ℝ) / (t : ℝ)) := by
      gcongr
      simpa [abs_sub_comm, Nat.dist_comm] using hd
    _ = (4 * (Nat.dist t v : ℝ) * (n : ℝ) * M +
          (|f n| + 4 * (n : ℝ) * M) * (Nat.dist t v : ℝ)) /
            (t : ℝ) := by ring

/-- The admissible multiplier at dyadic scale `k`.  It is congruent to one
modulo `n^(2^k)-1`, hence is coprime to that modulus. -/
def gridMultiplier (n k t : ℕ) : ℕ :=
  let D := 2 ^ k
  let q := n ^ D - 1
  q * (t / (q * D)) + 1

/-- The nearby exponent on Máté's admissible grid. -/
def gridExponent (n k t : ℕ) : ℕ :=
  gridMultiplier n k t * 2 ^ k

lemma gridMultiplier_pos (n k t : ℕ) : 0 < gridMultiplier n k t := by
  simp [gridMultiplier]

lemma gridMultiplier_coprime (n k t : ℕ) :
    (gridMultiplier n k t).Coprime (n ^ (2 ^ k) - 1) := by
  unfold gridMultiplier
  simp [add_comm]

lemma gridExponent_pos (n k t : ℕ) : 0 < gridExponent n k t := by
  exact mul_pos (gridMultiplier_pos n k t) (pow_pos (by omega) k)

/-- For `n ≥ 2`, the admissible grid exponent stays within one fixed grid
spacing of the target exponent. -/
lemma gridExponent_dist_le (n k t : ℕ) (hn : 2 ≤ n) :
    Nat.dist t (gridExponent n k t) ≤
      (n ^ (2 ^ k) - 1) * 2 ^ k := by
  let D := 2 ^ k
  let q := n ^ D - 1
  let Q := q * D
  let a := t / Q
  let r := t % Q
  have hD : 0 < D := by simp [D]
  have hnD : 2 ≤ n ^ D := by
    exact (show 2 ≤ n ^ D by
      have hDone : 1 ≤ D := by omega
      exact le_trans hn (Nat.le_pow hDone))
  have hq : 0 < q := by simp only [q]; omega
  have hQ : 0 < Q := mul_pos hq hD
  have hDleQ : D ≤ Q := by
    simp only [Q]
    nlinarith
  have hr : r < Q := Nat.mod_lt t hQ
  have htRep : t = a * Q + r := by
    simpa [a, r, mul_comm] using (Nat.div_add_mod t Q).symm
  have hvRep : gridExponent n k t = a * Q + D := by
    simp only [gridExponent, gridMultiplier, D, q, Q, a]
    ring
  have hdist : Nat.dist r D ≤ Q := by
    rcases le_total r D with hrD | hDr
    · rw [Nat.dist_eq_sub_of_le hrD]
      omega
    · rw [Nat.dist_eq_sub_of_le_right hDr]
      omega
  calc
    Nat.dist t (gridExponent n k t) =
        Nat.dist (a * Q + r) (a * Q + D) := by rw [← htRep, ← hvRep]
    _ = Nat.dist r D := Nat.dist_add_add_left (a * Q) r D
    _ ≤ Q := hdist
    _ = (n ^ (2 ^ k) - 1) * 2 ^ k := rfl

/-- At every admissible grid exponent, the normalized power value is within
`6M/2^k` of the dyadic limit. -/
lemma grid_normalized_bound
    {f : ℕ → ℝ} {M g : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n k t : ℕ) (hn : 0 < n)
    (htail : ∀ j : ℕ, |dyadicValue f n j - g| ≤ 4 * M / (2 : ℝ) ^ j) :
    |f (n ^ (gridExponent n k t)) / (gridExponent n k t : ℝ) - g| ≤
      6 * M / (2 : ℝ) ^ k := by
  let D := 2 ^ k
  let s := gridMultiplier n k t
  have hD : 0 < D := by simp [D]
  have hs : 0 < s := gridMultiplier_pos n k t
  have hnD : 1 ≤ n ^ D := pow_pos hn D
  have hcop : s.Coprime (n ^ D - 1) := gridMultiplier_coprime n k t
  have hmate := mate_one hf hM hgap (n ^ D) s hnD hs hcop
  have hv : gridExponent n k t = s * D := rfl
  have hpow : (n ^ D) ^ s = n ^ (s * D) := by
    rw [← pow_mul]
    congr 1
    exact Nat.mul_comm D s
  rw [hpow] at hmate
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hnormEq :
      |f (n ^ (s * D)) / ((s * D : ℕ) : ℝ) -
          f (n ^ D) / (D : ℝ)| =
        |f (n ^ (s * D)) - (s : ℝ) * f (n ^ D)| /
          ((s : ℝ) * (D : ℝ)) := by
    push_cast
    have heq :
        f (n ^ (s * D)) / ((s : ℝ) * (D : ℝ)) - f (n ^ D) / (D : ℝ) =
          (f (n ^ (s * D)) - (s : ℝ) * f (n ^ D)) /
            ((s : ℝ) * (D : ℝ)) := by
      field_simp [hsR.ne', hDR.ne']
    rw [heq, abs_div, abs_of_pos (mul_pos hsR hDR)]
  have hnorm :
      |f (n ^ (s * D)) / ((s * D : ℕ) : ℝ) -
          f (n ^ D) / (D : ℝ)| ≤ 2 * M / (D : ℝ) := by
    rw [hnormEq]
    apply (div_le_iff₀ (mul_pos hsR hDR)).2
    calc
      |f (n ^ (s * D)) - (s : ℝ) * f (n ^ D)| ≤
          2 * (s : ℝ) * M := hmate
      _ = (2 * M / (D : ℝ)) * ((s : ℝ) * (D : ℝ)) := by
        field_simp [hDR.ne']
  have htailk := htail k
  have hdyadic : dyadicValue f n k = f (n ^ D) / (D : ℝ) := by
    simp [dyadicValue, D]
  rw [hv]
  calc
    |f (n ^ (s * D)) / ((s * D : ℕ) : ℝ) - g| ≤
        |f (n ^ (s * D)) / ((s * D : ℕ) : ℝ) - f (n ^ D) / (D : ℝ)| +
          |f (n ^ D) / (D : ℝ) - g| := abs_sub_le _ _ _
    _ ≤ 2 * M / (D : ℝ) + 4 * M / (D : ℝ) := by
      gcongr
      simpa [hdyadic, D] using htailk
    _ = 6 * M / (2 : ℝ) ^ k := by
      simp only [D]
      norm_num
      ring

/-- Replacing an exponent by its nearby admissible grid exponent changes the
normalized power value by a quantity tending to zero. -/
lemma normalized_power_grid_local_tendsto
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n k : ℕ) (hn : 2 ≤ n) :
    Tendsto
      (fun t : ℕ ↦
        |f (n ^ t) / (t : ℝ) -
          f (n ^ (gridExponent n k t)) / (gridExponent n k t : ℝ)|)
      atTop (𝓝 0) := by
  let B : ℝ := ((n ^ (2 ^ k) - 1) * 2 ^ k : ℕ)
  let A : ℝ := 4 * (n : ℝ) * M + (|f n| + 4 * (n : ℝ) * M)
  let C : ℝ := B * A
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hC : 0 ≤ C := by
    exact mul_nonneg (by positivity) hA
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun t ↦ abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have htpos : 0 < t := by omega
    have hvpos : 0 < gridExponent n k t := gridExponent_pos n k t
    have hraw := normalized_power_sub_le hf hM hgap n t (gridExponent n k t)
      (by omega) htpos hvpos
    have hdistNat := gridExponent_dist_le n k t hn
    have hdist : (Nat.dist t (gridExponent n k t) : ℝ) ≤ B := by
      dsimp [B]
      exact_mod_cast hdistNat
    have hnum :
        4 * (Nat.dist t (gridExponent n k t) : ℝ) * (n : ℝ) * M +
            (|f n| + 4 * (n : ℝ) * M) *
              (Nat.dist t (gridExponent n k t) : ℝ) ≤ C := by
      have hmul := mul_le_mul_of_nonneg_right hdist hA
      dsimp [C]
      dsimp [A] at hmul
      nlinarith
    exact hraw.trans (div_le_div_of_nonneg_right hnum (by positivity))
  · exact tendsto_const_div_atTop_nhds_zero_nat C

/-- The dyadic limit is also the limit of normalized values along all
positive exponents. -/
lemma tendsto_normalized_powers_of_dyadic_limit
    {f : ℕ → ℝ} {M g : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n : ℕ) (hn : 0 < n)
    (htail : ∀ j : ℕ, |dyadicValue f n j - g| ≤ 4 * M / (2 : ℝ) ^ j) :
    Tendsto (fun t : ℕ ↦ f (n ^ t) / (t : ℝ)) atTop (𝓝 g) := by
  by_cases hn1 : n = 1
  · subst n
    have hf1 : f 1 = 0 := hf.one_eq_zero
    have hg0 : g = 0 := by
      have hMseq : ∀ k : ℕ, |g| ≤ 4 * M / (2 : ℝ) ^ k := by
        intro k
        simpa [dyadicValue, hf1, abs_neg] using htail k
      have hlim : Tendsto (fun k : ℕ ↦ 4 * M / (2 : ℝ) ^ k) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
      have : |g| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hMseq)
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    simp [hf1, hg0]
  · have hn2 : 2 ≤ n := by omega
    let e : ℕ → ℝ := fun k ↦ 6 * M / (2 : ℝ) ^ k
    have he0 : Tendsto e atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    apply Erdos491LimitScratch.tendsto_of_approximation_grids
      (fun t : ℕ ↦ f (n ^ t) / (t : ℝ)) g (gridExponent n) e he0
    · intro k
      exact div_nonneg (mul_nonneg (by norm_num) hM) (by positivity)
    · intro k
      exact normalized_power_grid_local_tendsto hf hM hgap n k hn2
    · intro k t
      exact grid_normalized_bound hf hM hgap n k t hn htail

/-- Máté's decomposition: every additive function with uniformly bounded
adjacent differences is uniformly close to a completely additive function. -/
theorem mate_decomposition
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M) :
    ∃ g : ℕ → ℝ, PosCompletelyAdditive g ∧
      ∀ n : ℕ, 0 < n → |f n - g n| ≤ 4 * M := by
  let chosenLimit (n : ℕ) (hn : 0 < n) : ℝ :=
    Classical.choose (exists_dyadic_limit hf hM hgap n hn)
  let g : ℕ → ℝ := fun n ↦ if hn : 0 < n then chosenLimit n hn else 0
  have hg (n : ℕ) (hn : 0 < n) :
      Tendsto (dyadicValue f n) atTop (𝓝 (g n)) := by
    rw [show g n = chosenLimit n hn by simp [g, hn]]
    exact (Classical.choose_spec (exists_dyadic_limit hf hM hgap n hn)).1
  have htail (n : ℕ) (hn : 0 < n) :
      ∀ k : ℕ, |dyadicValue f n k - g n| ≤ 4 * M / (2 : ℝ) ^ k := by
    rw [show g n = chosenLimit n hn by simp [g, hn]]
    exact (Classical.choose_spec (exists_dyadic_limit hf hM hgap n hn)).2
  have hall (n : ℕ) (hn : 0 < n) :
      Tendsto (fun t : ℕ ↦ f (n ^ t) / (t : ℝ)) atTop (𝓝 (g n)) :=
    tendsto_normalized_powers_of_dyadic_limit hf hM hgap n hn (htail n hn)
  have hcop : ∀ ⦃a b : ℕ⦄, 0 < a → 0 < b → a.Coprime b →
      g (a * b) = g a + g b := by
    intro a b ha hb hab
    exact Erdos491LimitScratch.coprime_additive_of_dyadic_limits f g
      (fun _ _ hcop ↦ hf hcop) hg ha hb hab
  have hpow : ∀ n r : ℕ, 0 < n → 0 < r →
      g (n ^ r) = (r : ℝ) * g n :=
    Erdos491LimitScratch.power_homogeneous_of_all_exponent_limits f g hall
  have hcomplete : PosCompletelyAdditive g := by
    intro a b ha hb
    exact Erdos491LimitScratch.completely_additive_of_coprime_and_powers g
      (fun _ _ hab ↦ hcop (by omega) (by omega) hab) hpow ha hb
  refine ⟨g, hcomplete, fun n hn ↦ ?_⟩
  have h0 := htail n hn 0
  simpa [dyadicValue] using h0

/-- A finite, scale-uniform version of Elliott's logarithmic approximation
theorem.  The constant `B` is independent of the cutoff `X`; the approximating
slope may depend on `X`. -/
def UniformFiniteLogApprox (g : ℕ → ℝ) (B : ℝ) : Prop :=
  ∀ X : ℕ, 2 ≤ X →
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → n ≤ X →
      |g n - c * Real.log (n : ℝ)| ≤ B

/-- The genuinely needed quantitative input is weaker than a uniform
Elliott bound.  For each fixed positive `n`, it is enough to approximate the
two powers `n^r` and `2^r` by one logarithmic slope with an error `E r` such
that `E r / r → 0`. -/
def PowerSublinearLogApprox (g : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    ∃ E : ℕ → ℝ,
      (∀ r : ℕ, 0 ≤ E r) ∧
      Tendsto (fun r : ℕ ↦ E r / (r : ℝ)) atTop (𝓝 0) ∧
      ∀ r : ℕ, 0 < r →
        ∃ c : ℝ,
          |g (n ^ r) - c * Real.log ((n ^ r : ℕ) : ℝ)| ≤ E r ∧
          |g (2 ^ r) - c * Real.log ((2 ^ r : ℕ) : ℝ)| ≤ E r

/-- A power-sublinear finite logarithmic approximation already kills every
normalized completely additive function.  This is the exact endpoint needed
from the analytic part of Wirsing's argument. -/
lemma PosCompletelyAdditive.eq_zero_of_powerSublinearLogApprox
    {g : ℕ → ℝ} (hg : PosCompletelyAdditive g) (hg2 : g 2 = 0)
    (happrox : PowerSublinearLogApprox g) :
    ∀ n : ℕ, 0 < n → g n = 0 := by
  intro n hn
  obtain ⟨E, hE, hE0, happ⟩ := happrox n hn
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  let A : ℝ := 1 + Real.log (n : ℝ) / Real.log 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hbound : ∀ᶠ r : ℕ in atTop,
      |g n| ≤ A * (E r / (r : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with r hr
    have hrpos : 0 < r := by omega
    obtain ⟨c, hnr, h2r⟩ := happ r hrpos
    rw [hg.pow hn r, Nat.cast_pow, Real.log_pow] at hnr
    rw [hg.pow (by omega : 0 < (2 : ℕ)) r, hg2, mul_zero,
      Nat.cast_pow, Real.log_pow] at h2r
    simp only [zero_sub, abs_neg] at h2r
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
    have hratio : 0 ≤ Real.log (n : ℝ) / Real.log 2 :=
      div_nonneg hlogn hlog2.le
    have hid :
        (r : ℝ) * g n =
          ((r : ℝ) * g n - c * ((r : ℝ) * Real.log (n : ℝ))) +
            (Real.log (n : ℝ) / Real.log 2) *
              (c * ((r : ℝ) * Real.log 2)) := by
      field_simp [hlog2.ne']
      ring
    have hscaled : (r : ℝ) * |g n| ≤ A * E r := by
      calc
        (r : ℝ) * |g n| = |(r : ℝ) * g n| := by
          rw [abs_mul, abs_of_pos hrR]
        _ = |((r : ℝ) * g n - c * ((r : ℝ) * Real.log (n : ℝ))) +
              (Real.log (n : ℝ) / Real.log 2) *
                (c * ((r : ℝ) * Real.log 2))| := congrArg abs hid
        _ ≤ |(r : ℝ) * g n - c * ((r : ℝ) * Real.log (n : ℝ))| +
              |(Real.log (n : ℝ) / Real.log 2) *
                (c * ((r : ℝ) * Real.log 2))| := abs_add_le _ _
        _ = |(r : ℝ) * g n - c * ((r : ℝ) * Real.log (n : ℝ))| +
              (Real.log (n : ℝ) / Real.log 2) *
                |c * ((r : ℝ) * Real.log 2)| := by
          rw [abs_mul, abs_of_nonneg hratio]
        _ ≤ E r + (Real.log (n : ℝ) / Real.log 2) * E r := by
          exact add_le_add hnr (mul_le_mul_of_nonneg_left h2r hratio)
        _ = A * E r := by dsimp [A]; ring
    calc
      |g n| = ((r : ℝ) * |g n|) / (r : ℝ) := by field_simp
      _ ≤ (A * E r) / (r : ℝ) :=
        div_le_div_of_nonneg_right hscaled hrR.le
      _ = A * (E r / (r : ℝ)) := by ring
  have htend : Tendsto (fun r : ℕ ↦ A * (E r / (r : ℝ)))
      atTop (𝓝 0) := by simpa using hE0.const_mul A
  have hzero : |g n| ≤ 0 := ge_of_tendsto htend hbound
  exact abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))

/-- The elementary compactness-free payoff from Elliott's uniform finite
approximation.  Simultaneously testing `n^r` and `2^r` makes the varying
slope `O(1/r)`; complete additivity then forces a function normalized by
`g 2 = 0` to vanish. -/
lemma PosCompletelyAdditive.eq_zero_of_uniformFiniteLogApprox
    {g : ℕ → ℝ} (hg : PosCompletelyAdditive g) (hg2 : g 2 = 0)
    {B : ℝ} (hB : 0 ≤ B) (happrox : UniformFiniteLogApprox g B) :
    ∀ n : ℕ, 0 < n → g n = 0 := by
  intro n hn
  by_cases hn1 : n = 1
  · subst n
    exact hg.one_eq_zero
  have hn2 : 2 ≤ n := by omega
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := B + (Real.log (n : ℝ) / Real.log 2) * B
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpowBound : ∀ r : ℕ, 0 < r → (r : ℝ) * |g n| ≤ C := by
    intro r hr
    let X := max (n ^ r) (2 ^ r)
    have hX2 : 2 ≤ X := by
      exact le_trans (show 2 ≤ 2 ^ r by
        have : 1 ≤ r := by omega
        exact Nat.le_pow this) (Nat.le_max_right _ _)
    obtain ⟨c, hc⟩ := happrox X hX2
    have hnr : 1 ≤ n ^ r := by
      have := pow_pos hn r
      omega
    have h2r : 1 ≤ 2 ^ r := by
      have : 0 < 2 ^ r := pow_pos (by omega) r
      omega
    have hnX : n ^ r ≤ X := Nat.le_max_left _ _
    have h2X : 2 ^ r ≤ X := Nat.le_max_right _ _
    have hnApprox := hc (n ^ r) hnr hnX
    have h2Approx := hc (2 ^ r) h2r h2X
    rw [hg.pow hn r, Nat.cast_pow, Real.log_pow] at hnApprox
    rw [hg.pow (by omega : 0 < (2 : ℕ)) r, hg2, mul_zero,
      Nat.cast_pow, Real.log_pow] at h2Approx
    simp only [zero_sub, abs_neg] at h2Approx
    have hrR : 0 ≤ (r : ℝ) := by positivity
    have hratio : 0 ≤ Real.log (n : ℝ) / Real.log 2 :=
      div_nonneg hlogn hlog2.le
    have hid :
        (r : ℝ) * g n =
          ((r : ℝ) * g n - c * ((r : ℝ) * Real.log (n : ℝ))) +
            (Real.log (n : ℝ) / Real.log 2) *
              (c * ((r : ℝ) * Real.log 2)) := by
      field_simp [hlog2.ne']
      ring
    calc
      (r : ℝ) * |g n| = |(r : ℝ) * g n| := by
        rw [abs_mul, abs_of_nonneg hrR]
      _ = |((r : ℝ) * g n - c * ((r : ℝ) * Real.log (n : ℝ))) +
            (Real.log (n : ℝ) / Real.log 2) *
              (c * ((r : ℝ) * Real.log 2))| := congrArg abs hid
      _ ≤ |(r : ℝ) * g n - c * ((r : ℝ) * Real.log (n : ℝ))| +
            |(Real.log (n : ℝ) / Real.log 2) *
              (c * ((r : ℝ) * Real.log 2))| := abs_add_le _ _
      _ = |(r : ℝ) * g n - c * ((r : ℝ) * Real.log (n : ℝ))| +
            (Real.log (n : ℝ) / Real.log 2) *
              |c * ((r : ℝ) * Real.log 2)| := by
        rw [abs_mul, abs_of_nonneg hratio]
      _ ≤ B + (Real.log (n : ℝ) / Real.log 2) * B := by
        apply add_le_add hnApprox
        apply mul_le_mul_of_nonneg_left _ hratio
        simpa using h2Approx
      _ = C := rfl
  by_contra hne
  have habs : 0 < |g n| := abs_pos.mpr hne
  obtain ⟨r : ℕ, hr⟩ := exists_nat_gt (C / |g n|)
  have hrpos : 0 < r := by
    have hquot : 0 ≤ C / |g n| := div_nonneg hC habs.le
    exact_mod_cast (lt_of_le_of_lt hquot hr)
  have hrreal : C / |g n| < (r : ℝ) := by exact_mod_cast hr
  have hstrict : C < (r : ℝ) * |g n| :=
    (div_lt_iff₀ habs).mp hrreal
  exact (not_lt_of_ge (hpowBound r hrpos)) hstrict

/-- The exact completely-additive rigidity statement needed after Máté's
decomposition.  Wirsing proved the stronger result with only a one-sided
bound on the adjacent differences. -/
def CompletelyAdditiveBoundedGapRigidity : Prop :=
  ∀ (g : ℕ → ℝ) (K : ℝ),
    PosCompletelyAdditive g → 0 ≤ K →
    (∀ n : ℕ, 0 < n → |g (n + 1) - g n| ≤ K) →
    ∃ c : ℝ, ∀ n : ℕ, 0 < n → g n = c * Real.log (n : ℝ)

/-- The elementary outer reduction of Problem 491 to Wirsing's rigidity
theorem. -/
theorem problemStatement_of_completelyAdditiveBoundedGapRigidity
    (hW : CompletelyAdditiveBoundedGapRigidity) : ProblemStatement := by
  intro f hf hstrict
  obtain ⟨M, hM, hgap⟩ := exists_nonneg_adjacent_bound_of_strict hstrict
  obtain ⟨g, hgcomplete, hfg⟩ := mate_decomposition hf hM hgap
  have hgapg : ∀ n : ℕ, 0 < n → |g (n + 1) - g n| ≤ 9 * M := by
    intro n hn
    calc
      |g (n + 1) - g n| =
          |(g (n + 1) - f (n + 1)) + (f (n + 1) - f n) +
            (f n - g n)| := by
              congr 1
              ring
      _ ≤ |g (n + 1) - f (n + 1)| + |f (n + 1) - f n| +
          |f n - g n| := by
            calc
              _ ≤ |(g (n + 1) - f (n + 1)) + (f (n + 1) - f n)| +
                  |f n - g n| := abs_add_le _ _
              _ ≤ (|g (n + 1) - f (n + 1)| + |f (n + 1) - f n|) +
                  |f n - g n| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 4 * M + M + 4 * M := by
        gcongr
        · simpa [abs_sub_comm] using hfg (n + 1) (by omega)
        · exact hgap n
        · exact hfg n hn
      _ = 9 * M := by ring
  obtain ⟨c, hc⟩ :=
    hW g (9 * M) hgcomplete (mul_nonneg (by norm_num) hM) hgapg
  apply hasLogarithmicMainTerm_of_explicit_bound
  exact ⟨c, 4 * M, mul_nonneg (by norm_num) hM,
    fun n hn ↦ by simpa [hc n hn] using hfg n hn⟩

/-- Sparse approximation grids whose errors tend to zero determine the full
limit.  The local-oscillation estimate is kept as a separate interface. -/
lemma tendsto_of_approximation_grids (F : ℕ → ℝ) (g : ℝ)
    (v : ℕ → ℕ → ℕ) (e : ℕ → ℝ)
    (he0 : Tendsto e atTop (𝓝 0)) (he : ∀ k, 0 ≤ e k)
    (hlocal : ∀ k, Tendsto (fun t => |F t - F (v k t)|) atTop (𝓝 0))
    (hgrid : ∀ k t, |F (v k t) - g| ≤ e k) :
    Tendsto F atTop (𝓝 g) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases Metric.tendsto_atTop.mp he0 (ε / 2) (by positivity) with ⟨K, hK⟩
  have heK : e K < ε / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg (he K)] using hK K le_rfl
  rcases Metric.tendsto_atTop.mp (hlocal K) (ε / 2) (by positivity) with ⟨N, hN⟩
  refine ⟨N, fun t ht => ?_⟩
  rw [Real.dist_eq]
  calc
    |F t - g| ≤ |F t - F (v K t)| + |F (v K t) - g| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by
      simpa [Real.dist_eq] using hN t ht) ((hgrid K t).trans_lt heK)
    _ = ε := by ring

/-- Pointwise dyadic limits preserve coprime additivity on positive inputs. -/
lemma coprimeAdditive_of_dyadic_limits (f g : ℕ → ℝ)
    (hf : CoprimeAdditive f)
    (hg : ∀ n : ℕ, 0 < n →
      Tendsto (fun k : ℕ => f (n ^ (2 ^ k)) / (2 : ℝ) ^ k) atTop (𝓝 (g n))) :
    ∀ ⦃a b : ℕ⦄, 0 < a → 0 < b → a.Coprime b →
      g (a * b) = g a + g b := by
  intro a b ha hb hab
  have hseq : ∀ k : ℕ,
      f ((a * b) ^ (2 ^ k)) / (2 : ℝ) ^ k =
        f (a ^ (2 ^ k)) / (2 : ℝ) ^ k +
          f (b ^ (2 ^ k)) / (2 : ℝ) ^ k := by
    intro k
    rw [mul_pow, hf (hab.pow _ _)]
    ring
  have hsum : Tendsto
      (fun k : ℕ => f (a ^ (2 ^ k)) / (2 : ℝ) ^ k +
        f (b ^ (2 ^ k)) / (2 : ℝ) ^ k) atTop (𝓝 (g a + g b)) :=
    (hg a ha).add (hg b hb)
  exact tendsto_nhds_unique (hg (a * b) (mul_pos ha hb))
    (hsum.congr' (Filter.Eventually.of_forall fun k => (hseq k).symm))

/-- If normalized values along all positive exponents converge, their limit
is homogeneous under positive natural powers. -/
lemma power_homogeneous_of_all_exponent_limits (f g : ℕ → ℝ)
    (hg : ∀ n : ℕ, 0 < n →
      Tendsto (fun t : ℕ => f (n ^ t) / (t : ℝ)) atTop (𝓝 (g n))) :
    ∀ n r : ℕ, 0 < n → 0 < r → g (n ^ r) = (r : ℝ) * g n := by
  intro n r hn hr
  have hmul : Tendsto (fun t : ℕ => r * t) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun a ha => ha.trans ?_⟩
    simpa only [one_mul] using
      Nat.mul_le_mul_right a (Nat.one_le_iff_ne_zero.2 hr.ne')
  have hsub : Tendsto
      (fun t : ℕ => f (n ^ (r * t)) / ((r * t : ℕ) : ℝ)) atTop (𝓝 (g n)) := by
    change Tendsto
      ((fun s : ℕ => f (n ^ s) / (s : ℝ)) ∘ (fun t : ℕ => r * t))
      atTop (𝓝 (g n))
    exact (hg n hn).comp hmul
  have hscaled : Tendsto
      (fun t : ℕ => (r : ℝ) * (f (n ^ (r * t)) / ((r * t : ℕ) : ℝ)))
      atTop (𝓝 ((r : ℝ) * g n)) := tendsto_const_nhds.mul hsub
  have heq : ∀ᶠ t : ℕ in atTop,
      f ((n ^ r) ^ t) / (t : ℝ) =
        (r : ℝ) * (f (n ^ (r * t)) / ((r * t : ℕ) : ℝ)) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun t ht => ht⟩] with t ht
    rw [pow_mul]
    push_cast
    field_simp [Nat.ne_of_gt ht, hr.ne']
  have heq' :
      (fun t : ℕ => (r : ℝ) * (f (n ^ (r * t)) / ((r * t : ℕ) : ℝ))) =ᶠ[atTop]
        (fun t : ℕ => f ((n ^ r) ^ t) / (t : ℝ)) := by
    filter_upwards [heq] with t ht
    exact ht.symm
  exact tendsto_nhds_unique (hg (n ^ r) (pow_pos hn r))
    (hscaled.congr' heq')

/-- A bounded perturbation of a function with bounded adjacent differences
again has bounded adjacent differences. -/
lemma adjacent_bound_of_uniform_approximation
    {f g : ℕ → ℝ} {M B : ℝ}
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (happrox : ∀ n : ℕ, |f n - g n| ≤ B) (n : ℕ) :
    |g (n + 1) - g n| ≤ M + 2 * B := by
  calc
    |g (n + 1) - g n| =
        |(g (n + 1) - f (n + 1)) + (f (n + 1) - f n) +
          (f n - g n)| := by
            congr 1
            ring
    _ ≤ |(g (n + 1) - f (n + 1)) + (f (n + 1) - f n)| +
          |f n - g n| := abs_add_le _ _
    _ ≤ (|g (n + 1) - f (n + 1)| + |f (n + 1) - f n|) +
          |f n - g n| :=
            add_le_add (abs_add_le _ _) le_rfl
    _ ≤ B + M + B := by
          gcongr
          · simpa [abs_sub_comm] using happrox (n + 1)
          · exact hgap n
          · exact happrox n
    _ = M + 2 * B := by ring

/-- Transfer an exact logarithmic description across a uniform approximation. -/
lemma log_bound_of_uniform_approximation
    {f g : ℕ → ℝ} {c B : ℝ}
    (happrox : ∀ n : ℕ, 0 < n → |f n - g n| ≤ B)
    (hg : ∀ n : ℕ, 0 < n → g n = c * Real.log (n : ℝ)) :
    ∀ n : ℕ, 0 < n → |f n - c * Real.log (n : ℝ)| ≤ B := by
  intro n hn
  simpa [hg n hn] using happrox n hn

end

end Erdos491

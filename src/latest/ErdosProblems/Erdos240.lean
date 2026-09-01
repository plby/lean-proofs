/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos240.Analytic
import ErdosProblems.Erdos240.BakerSourceAssemblyIndependent
import ErdosProblems.Erdos240.BakerSourceFinalAssemblyIndependent
import ErdosProblems.Erdos822.PrimeIntervals

/-!
# Erdős Problem 240

Tijdeman proved that there is an infinite set of primes whose positive smooth
numbers have consecutive gaps tending to infinity.  The definitions below
state the question literally: positivity excludes zero, `EnumeratesSmooth`
requires an actual increasing enumeration of every smooth number, and
`HasDivergentGaps` uses the natural-number `atTop` limit.
-/

open Filter

namespace Erdos240

/-- `n` is a positive integer all of whose prime divisors belong to `P`. -/
def IsSmooth (P : Set ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ q : ℕ, q.Prime → q ∣ n → q ∈ P

/-- Every member of `P` is prime. -/
def IsPrimeSet (P : Set ℕ) : Prop :=
  ∀ ⦃p : ℕ⦄, p ∈ P → p.Prime

/-- `a` is the increasing enumeration of all positive `P`-smooth integers. -/
def EnumeratesSmooth (P : Set ℕ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ Set.range a = {n : ℕ | IsSmooth P n}

/-- The literal conclusion of Problem 240 for a fixed prime set. -/
def HasDivergentGaps (P : Set ℕ) : Prop :=
  ∃ a : ℕ → ℕ, EnumeratesSmooth P a ∧
    Tendsto (fun i : ℕ => a (i + 1) - a i) atTop atTop

/-- A stronger all-pairs formulation of divergence of the smooth gaps. -/
def PairwiseGapsDiverge (P : Set ℕ) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, ∀ ⦃a b : ℕ⦄,
    IsSmooth P a → IsSmooth P b → N ≤ a → a < b → K ≤ b - a

/-- A uniform lower bound `g a` for every gap beginning at the smooth number `a`. -/
def SeparatedBy (g : ℕ → ℕ) (P : Set ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, IsSmooth P a → IsSmooth P b → a < b → g a ≤ b - a

/-- A finite prime set together with a proof of the separation invariant. -/
structure FiniteStage (g : ℕ → ℕ) where
  carrier : Finset ℕ
  prime_mem : ∀ ⦃p : ℕ⦄, p ∈ carrier → p.Prime
  separated : SeparatedBy g (↑carrier : Set ℕ)

/-- The finite-stage extension statement used in Tijdeman's induction. -/
def ExtensionPrinciple (g : ℕ → ℕ) : Prop :=
  ∀ s : FiniteStage g, ∃ p : ℕ, p.Prime ∧ p ∉ s.carrier ∧
    SeparatedBy g (↑(insert p s.carrier) : Set ℕ)

lemma IsSmooth.mono {P Q : Set ℕ} {n : ℕ} (hPQ : P ⊆ Q)
    (hn : IsSmooth P n) : IsSmooth Q n := by
  exact ⟨hn.1, fun q hq hqn => hPQ (hn.2 q hq hqn)⟩

/-- A smooth number is reconstructed by multiplying its factorization over
any finite prime set witnessing its smoothness. -/
lemma IsSmooth.prod_factorization_eq {s : Finset ℕ} {n : ℕ}
    (hn : IsSmooth (↑s : Set ℕ) n) :
    ∏ q ∈ s, q ^ n.factorization q = n := by
  have hsupp : n.factorization.support ⊆ s := by
    intro q hq
    have hqFactors : q ∈ n.primeFactors := by simpa using hq
    have hqData := Nat.mem_primeFactors.mp hqFactors
    exact hn.2 q hqData.1 hqData.2.1
  calc
    ∏ q ∈ s, q ^ n.factorization q =
        n.factorization.prod (fun q e => q ^ e) := by
      symm
      exact Finsupp.prod_of_support_subset n.factorization hsupp
        (fun q e => q ^ e) (by simp)
    _ = n := Nat.prod_factorization_pow_eq_self (Nat.ne_of_gt hn.1)

/-- Separating the factor at a fresh prime gives the exponent-coordinate
form used in Tijdeman's counting argument. -/
lemma IsSmooth.eq_pow_mul_prod_factorization {s : Finset ℕ} {n p : ℕ}
    (hpFresh : p ∉ s) (hn : IsSmooth (↑(insert p s) : Set ℕ) n) :
    p ^ n.factorization p * (∏ q ∈ s, q ^ n.factorization q) = n := by
  simpa [Finset.prod_insert hpFresh] using hn.prod_factorization_eq

/-- Removing the full `p`-power from a number smooth over `insert p S`
leaves a number smooth over the old set `S`, provided `p` is genuinely new. -/
lemma isSmooth_ordCompl {S : Set ℕ} {n p : ℕ} (hp : p.Prime) (hpS : p ∉ S)
    (hn : IsSmooth (insert p S) n) : IsSmooth S (ordCompl[p] n) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn.1
  refine ⟨Nat.ordCompl_pos p hn0, ?_⟩
  intro q hq hqdiv
  have hqn : q ∣ n := hqdiv.trans (Nat.ordCompl_dvd n p)
  have hqmem : q = p ∨ q ∈ S := by
    simpa only [Set.mem_insert_iff] using hn.2 q hq hqn
  rcases hqmem with rfl | hqS
  · exact False.elim ((Nat.not_dvd_ordCompl hp hn0) hqdiv)
  · exact hqS

/-- Multiplication by a positive integer can only increase the integer square
root by at most that same factor.  This elementary estimate is exactly what is
needed when a common new-prime power is cancelled from a putative bad pair. -/
lemma sqrt_mul_le_mul_sqrt {c a : ℕ} (hc : 0 < c) (ha : 0 < a) :
    Nat.sqrt (c * a) ≤ c * Nat.sqrt a := by
  apply Nat.le_of_lt_succ
  rw [Nat.sqrt_lt]
  have haUpper := Nat.lt_succ_sqrt a
  have hspos : 0 < Nat.sqrt a := Nat.sqrt_pos.mpr ha
  by_cases hcOne : c = 1
  · subst c
    simpa using haUpper
  · have hcTwo : 2 ≤ c := by omega
    have hsSquare : 1 ≤ Nat.sqrt a * Nat.sqrt a := by
      exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hspos.ne' hspos.ne')
    have hfirst : c ≤ c * (Nat.sqrt a * Nat.sqrt a) := by
      simpa using Nat.mul_le_mul_left c hsSquare
    have hsecond :
        2 * (c * (Nat.sqrt a * Nat.sqrt a)) ≤
          c * (c * (Nat.sqrt a * Nat.sqrt a)) := by
      exact Nat.mul_le_mul_right (c * (Nat.sqrt a * Nat.sqrt a)) hcTwo
    have hmulUpper :
        c * a < c * ((Nat.sqrt a + 1) * (Nat.sqrt a + 1)) :=
      (Nat.mul_lt_mul_left hc).mpr haUpper
    nlinarith

/-- In a pair violating the square-root separation bound after adjoining a
fresh prime `p`, the exponents of `p` in the two numbers are different. -/
lemma factorization_ne_of_bad_pair (s : FiniteStage Nat.sqrt) {p a b : ℕ}
    (hp : p.Prime) (hpFresh : p ∉ s.carrier)
    (ha : IsSmooth (↑(insert p s.carrier) : Set ℕ) a)
    (hb : IsSmooth (↑(insert p s.carrier) : Set ℕ) b)
    (hab : a < b) (hgap : b - a < Nat.sqrt a) :
    a.factorization p ≠ b.factorization p := by
  intro hexp
  let c : ℕ := p ^ a.factorization p
  let a₀ : ℕ := ordCompl[p] a
  let b₀ : ℕ := ordCompl[p] b
  have hc : 0 < c := by
    dsimp [c]
    exact pow_pos hp.pos _
  have ha₀pos : 0 < a₀ := Nat.ordCompl_pos p (Nat.ne_of_gt ha.1)
  have ha₀smooth : IsSmooth (↑s.carrier : Set ℕ) a₀ :=
    isSmooth_ordCompl hp (by simpa using hpFresh) (by simpa using ha)
  have hb₀smooth : IsSmooth (↑s.carrier : Set ℕ) b₀ :=
    isSmooth_ordCompl hp (by simpa using hpFresh) (by simpa using hb)
  have haDecomp : c * a₀ = a := by
    exact Nat.ordProj_mul_ordCompl_eq_self a p
  have hbDecomp : c * b₀ = b := by
    dsimp [c, b₀]
    rw [hexp]
    exact Nat.ordProj_mul_ordCompl_eq_self b p
  have ha₀b₀ : a₀ < b₀ := by
    apply (Nat.mul_lt_mul_left hc).mp
    simpa only [haDecomp, hbDecomp] using hab
  have hold : Nat.sqrt a₀ ≤ b₀ - a₀ :=
    s.separated ha₀smooth hb₀smooth ha₀b₀
  have hsqrt : Nat.sqrt a ≤ c * Nat.sqrt a₀ := by
    rw [← haDecomp]
    exact sqrt_mul_le_mul_sqrt hc ha₀pos
  have hscaled : c * Nat.sqrt a₀ ≤ b - a := by
    calc
      c * Nat.sqrt a₀ ≤ c * (b₀ - a₀) := Nat.mul_le_mul_left c hold
      _ = c * b₀ - c * a₀ := Nat.mul_sub_left_distrib c b₀ a₀
      _ = b - a := by rw [haDecomp, hbDecomp]
  exact (not_lt_of_ge (hsqrt.trans hscaled)) hgap

/-- Candidate primes in the dyadic interval `(n / 2, n]`. -/
def primeHalfInterval (n : ℕ) : Finset ℕ :=
  (Finset.Ioc (n / 2) n).filter Nat.Prime

/-- The elementary data attached to a fixed exponent tuple in Tijdeman's
counting argument.  `A` and `B` are the old-prime parts, while `α` and `β`
are the exponents of the candidate prime. -/
def IsBadTuple (n A B α β p : ℕ) : Prop :=
  p ∈ primeHalfInterval n ∧ 0 < A ∧ 0 < B ∧
    p ^ α * A < p ^ β * B ∧
    p ^ β * B - p ^ α * A < Nat.sqrt (p ^ α * A)

lemma IsBadTuple.prime {n A B α β p : ℕ} (h : IsBadTuple n A B α β p) :
    p.Prime := by
  exact (Finset.mem_filter.mp h.1).2

lemma IsBadTuple.mem_Ioc {n A B α β p : ℕ} (h : IsBadTuple n A B α β p) :
    p ∈ Finset.Ioc (n / 2) n := by
  exact (Finset.mem_filter.mp h.1).1

/-- A bad tuple in the dyadic block has old left part larger than `n / 4`.
This is the lower-size estimate which turns a relative square-root window
into an `O(sqrt n)` interval of candidate primes. -/
lemma IsBadTuple.n_lt_four_mul_left {n A B α β p : ℕ}
    (h : IsBadTuple n A B α β p) (hαβ : α ≠ β) :
    n < 4 * (p ^ α * A) := by
  have hpPrime := h.prime
  have hpInterval := Finset.mem_Ioc.mp h.mem_Ioc
  have hnTwoP : n < 2 * p := by omega
  have hleftPos : 0 < p ^ α * A := mul_pos (pow_pos hpPrime.pos _) h.2.1
  have hsqrtLe : Nat.sqrt (p ^ α * A) ≤ p ^ α * A :=
    Nat.sqrt_le_self _
  have hgapNat :
      p ^ β * B - p ^ α * A < Nat.sqrt (p ^ α * A) :=
    h.2.2.2.2
  have hrightEq :
      p ^ β * B - p ^ α * A + p ^ α * A = p ^ β * B :=
    Nat.sub_add_cancel (Nat.le_of_lt h.2.2.2.1)
  have hrightLt : p ^ β * B < 2 * (p ^ α * A) := by omega
  rcases lt_or_gt_of_ne hαβ with hαβlt | hβαlt
  · have hβpos : 0 < β := by omega
    have hpPow : p ≤ p ^ β :=
      Nat.le_of_dvd (pow_pos hpPrime.pos _) (dvd_pow_self p hβpos.ne')
    have hpRight : p ≤ p ^ β * B := by
      exact hpPow.trans (Nat.le_mul_of_pos_right _ h.2.2.1)
    omega
  · have hαpos : 0 < α := by omega
    have hpPow : p ≤ p ^ α :=
      Nat.le_of_dvd (pow_pos hpPrime.pos _) (dvd_pow_self p hαpos.ne')
    have hpLeft : p ≤ p ^ α * A := by
      exact hpPow.trans (Nat.le_mul_of_pos_right _ h.2.1)
    omega

/-- The ratio represented by a bad exponent tuple lies in the short interval
`(1, 1 + 2 / sqrt n)`.  This is the analytic form of the source's estimate
`1 < b/a < 1 + a^{-1/2}`, with `a > n/4`. -/
lemma IsBadTuple.ratio_lt_one_add_two_div_sqrt {n A B α β p : ℕ}
    (h : IsBadTuple n A B α β p) (hαβ : α ≠ β) :
    ((p ^ β * B : ℕ) : ℝ) / ((p ^ α * A : ℕ) : ℝ) <
      1 + 2 / Real.sqrt (n : ℝ) := by
  let a : ℕ := p ^ α * A
  let b : ℕ := p ^ β * B
  have haPos : 0 < a := by
    dsimp [a]
    exact mul_pos (pow_pos h.prime.pos _) h.2.1
  have hab : a < b := h.2.2.2.1
  have hgap : b - a < Nat.sqrt a := h.2.2.2.2
  have hnFour : n < 4 * a := h.n_lt_four_mul_left hαβ
  have hnPos : 0 < n := by
    have hpLe : p ≤ n := (Finset.mem_Ioc.mp h.mem_Ioc).2
    exact h.prime.pos.trans_le hpLe
  have haReal : 0 < (a : ℝ) := by exact_mod_cast haPos
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPos
  have hgapReal : ((b - a : ℕ) : ℝ) < Real.sqrt (a : ℝ) := by
    have hcast : ((b - a : ℕ) : ℝ) < (Nat.sqrt a : ℝ) := by exact_mod_cast hgap
    exact hcast.trans_le Real.nat_sqrt_le_real_sqrt
  have hratioEq :
      (b : ℝ) / (a : ℝ) = 1 + ((b - a : ℕ) : ℝ) / (a : ℝ) := by
    rw [div_eq_iff haReal.ne']
    rw [add_mul, one_mul, div_mul_cancel₀ _ haReal.ne']
    exact_mod_cast (show b = a + (b - a) by omega)
  have hsqrtDiv :
      Real.sqrt (a : ℝ) / (a : ℝ) = 1 / Real.sqrt (a : ℝ) := by
    apply (div_eq_div_iff haReal.ne' (Real.sqrt_pos.2 haReal).ne').2
    simpa only [one_mul] using Real.mul_self_sqrt haReal.le
  have hroot : Real.sqrt (n : ℝ) < 2 * Real.sqrt (a : ℝ) := by
    have hnFourReal : (n : ℝ) < 4 * (a : ℝ) := by exact_mod_cast hnFour
    have hmono : Real.sqrt (n : ℝ) < Real.sqrt (4 * (a : ℝ)) :=
      Real.sqrt_lt_sqrt hnReal.le hnFourReal
    calc
      Real.sqrt (n : ℝ) < Real.sqrt (4 * (a : ℝ)) := hmono
      _ = 2 * Real.sqrt (a : ℝ) := by
        have hsqrtFour : Real.sqrt (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [Real.sqrt_mul (x := 4) (by norm_num) (a : ℝ), hsqrtFour]
  have hinv : 1 / Real.sqrt (a : ℝ) < 2 / Real.sqrt (n : ℝ) := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.2 haReal) (Real.sqrt_pos.2 hnReal)]
    simpa only [one_mul] using hroot
  have hgapRatio :
      ((b - a : ℕ) : ℝ) / (a : ℝ) < 2 / Real.sqrt (n : ℝ) := by
    calc
      ((b - a : ℕ) : ℝ) / (a : ℝ) < Real.sqrt (a : ℝ) / (a : ℝ) :=
        div_lt_div_of_pos_right hgapReal haReal
      _ = 1 / Real.sqrt (a : ℝ) := hsqrtDiv
      _ < 2 / Real.sqrt (n : ℝ) := hinv
  change (b : ℝ) / (a : ℝ) < 1 + 2 / Real.sqrt (n : ℝ)
  rw [hratioEq]
  linarith

lemma ratio_pow_sub_of_le {A B p α β : ℕ} (hA : 0 < A) (hp : 0 < p)
    (hαβ : α ≤ β) :
    ((p ^ β * B : ℕ) : ℝ) / ((p ^ α * A : ℕ) : ℝ) =
      ((B : ℝ) / A) * (p : ℝ) ^ (β - α) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hαβ
  simp only [Nat.add_sub_cancel_left, Nat.cast_mul, Nat.cast_pow]
  rw [pow_add]
  field_simp [show (A : ℝ) ≠ 0 by exact_mod_cast hA.ne',
    show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne']

lemma ratio_pow_sub_of_ge {A B p α β : ℕ} (hA : 0 < A) (hp : 0 < p)
    (hβα : β ≤ α) :
    ((p ^ β * B : ℕ) : ℝ) / ((p ^ α * A : ℕ) : ℝ) =
      ((B : ℝ) / A) / (p : ℝ) ^ (α - β) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hβα
  simp only [Nat.add_sub_cancel_left, Nat.cast_mul, Nat.cast_pow]
  rw [pow_add]
  field_simp [show (A : ℝ) ≠ 0 by exact_mod_cast hA.ne',
    show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne']

/-- Two candidates giving bad pairs with the same exponent tuple lie in a
common multiplicative interval of relative width `2 / sqrt n`. -/
lemma IsBadTuple.div_lt_one_add_two_div_sqrt {n A B α β p q : ℕ}
    (hp : IsBadTuple n A B α β p) (hq : IsBadTuple n A B α β q)
    (hαβ : α ≠ β) (hpq : p ≤ q) :
    (q : ℝ) / p < 1 + 2 / Real.sqrt (n : ℝ) := by
  have hpPos : 0 < p := hp.prime.pos
  have hqPos : 0 < q := hq.prime.pos
  have hpDenPos : 0 < ((p ^ α * A : ℕ) : ℝ) := by
    exact_mod_cast (mul_pos (pow_pos hpPos _) hp.2.1)
  have hqDenPos : 0 < ((q ^ α * A : ℕ) : ℝ) := by
    exact_mod_cast (mul_pos (pow_pos hqPos _) hq.2.1)
  have hpRatioOne :
      1 < ((p ^ β * B : ℕ) : ℝ) / ((p ^ α * A : ℕ) : ℝ) := by
    rw [one_lt_div hpDenPos]
    exact_mod_cast hp.2.2.2.1
  have hqRatioOne :
      1 < ((q ^ β * B : ℕ) : ℝ) / ((q ^ α * A : ℕ) : ℝ) := by
    rw [one_lt_div hqDenPos]
    exact_mod_cast hq.2.2.2.1
  have hpRatioUpper := hp.ratio_lt_one_add_two_div_sqrt hαβ
  have hqRatioUpper := hq.ratio_lt_one_add_two_div_sqrt hαβ
  have hbase : 1 ≤ (q : ℝ) / p := by
    rw [one_le_div (by exact_mod_cast hpPos)]
    exact_mod_cast hpq
  rcases lt_or_gt_of_ne hαβ with hαβlt | hβαlt
  · let d : ℕ := β - α
    have hd : d ≠ 0 := by omega
    have hpId := ratio_pow_sub_of_le (B := B) hp.2.1 hpPos (Nat.le_of_lt hαβlt)
    have hqId := ratio_pow_sub_of_le (B := B) hq.2.1 hqPos (Nat.le_of_lt hαβlt)
    have hpPowPos : 0 < (p : ℝ) ^ d := pow_pos (by exact_mod_cast hpPos) _
    have hqPowPos : 0 < (q : ℝ) ^ d := pow_pos (by exact_mod_cast hqPos) _
    have hInvC : 1 / (p : ℝ) ^ d < (B : ℝ) / A := by
      rw [div_lt_iff₀ hpPowPos]
      have := hpRatioOne
      rw [hpId] at this
      simpa only [one_mul] using this
    have hpow : ((q : ℝ) / p) ^ d < 1 + 2 / Real.sqrt (n : ℝ) := by
      calc
        ((q : ℝ) / p) ^ d = (q : ℝ) ^ d / (p : ℝ) ^ d := div_pow _ _ _
        _ = (1 / (p : ℝ) ^ d) * (q : ℝ) ^ d := by ring
        _ < ((B : ℝ) / A) * (q : ℝ) ^ d :=
          mul_lt_mul_of_pos_right hInvC hqPowPos
        _ = ((q ^ β * B : ℕ) : ℝ) / ((q ^ α * A : ℕ) : ℝ) := hqId.symm
        _ < 1 + 2 / Real.sqrt (n : ℝ) := hqRatioUpper
    exact (le_self_pow₀ hbase hd).trans_lt hpow
  · let d : ℕ := α - β
    have hd : d ≠ 0 := by omega
    have hpId := ratio_pow_sub_of_ge (B := B) hp.2.1 hpPos (Nat.le_of_lt hβαlt)
    have hqId := ratio_pow_sub_of_ge (B := B) hq.2.1 hqPos (Nat.le_of_lt hβαlt)
    have hpPowPos : 0 < (p : ℝ) ^ d := pow_pos (by exact_mod_cast hpPos) _
    have hqPowPos : 0 < (q : ℝ) ^ d := pow_pos (by exact_mod_cast hqPos) _
    have hqPowLtC : (q : ℝ) ^ d < (B : ℝ) / A := by
      have := hqRatioOne
      rw [hqId] at this
      exact (one_lt_div hqPowPos).mp this
    have hpow : ((q : ℝ) / p) ^ d < 1 + 2 / Real.sqrt (n : ℝ) := by
      calc
        ((q : ℝ) / p) ^ d = (q : ℝ) ^ d / (p : ℝ) ^ d := div_pow _ _ _
        _ < ((B : ℝ) / A) / (p : ℝ) ^ d :=
          div_lt_div_of_pos_right hqPowLtC hpPowPos
        _ = ((p ^ β * B : ℕ) : ℝ) / ((p ^ α * A : ℕ) : ℝ) := hpId.symm
        _ < 1 + 2 / Real.sqrt (n : ℝ) := hpRatioUpper
    exact (le_self_pow₀ hbase hd).trans_lt hpow

/-- Additive form of the fixed-tuple interval estimate. -/
lemma IsBadTuple.cast_sub_lt_two_mul_sqrt {n A B α β p q : ℕ}
    (hp : IsBadTuple n A B α β p) (hq : IsBadTuple n A B α β q)
    (hαβ : α ≠ β) (hpq : p ≤ q) :
    ((q - p : ℕ) : ℝ) < 2 * Real.sqrt (n : ℝ) := by
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.prime.pos
  have hnPosNat : 0 < n := hp.prime.pos.trans_le (Finset.mem_Ioc.mp hp.mem_Ioc).2
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hnPosNat
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnPos
  have hdiv := hp.div_lt_one_add_two_div_sqrt hq hαβ hpq
  have hqBound :
      (q : ℝ) < (1 + 2 / Real.sqrt (n : ℝ)) * p :=
    (div_lt_iff₀ hpPos).mp hdiv
  have hgapBound :
      ((q - p : ℕ) : ℝ) < 2 * (p : ℝ) / Real.sqrt (n : ℝ) := by
    rw [Nat.cast_sub hpq]
    calc
      (q : ℝ) - p < (1 + 2 / Real.sqrt (n : ℝ)) * p - p :=
        sub_lt_sub_right hqBound _
      _ = 2 * (p : ℝ) / Real.sqrt (n : ℝ) := by ring
  have hpLeN : (p : ℝ) ≤ n := by
    exact_mod_cast (Finset.mem_Ioc.mp hp.mem_Ioc).2
  have hscale :
      2 * (p : ℝ) / Real.sqrt (n : ℝ) ≤
        2 * (n : ℝ) / Real.sqrt (n : ℝ) := by
    gcongr
  have hnDiv : (n : ℝ) / Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) := by
    apply (div_eq_iff hsqrtPos.ne').2
    simpa only using (Real.mul_self_sqrt hnPos.le).symm
  calc
    ((q - p : ℕ) : ℝ) < 2 * (p : ℝ) / Real.sqrt (n : ℝ) := hgapBound
    _ ≤ 2 * (n : ℝ) / Real.sqrt (n : ℝ) := hscale
    _ = 2 * Real.sqrt (n : ℝ) := by rw [mul_div_assoc, hnDiv]

/-- Candidate primes realizing one fixed exponent tuple. -/
noncomputable def badTupleFiber (n A B α β : ℕ) : Finset ℕ := by
  classical
  exact (primeHalfInterval n).filter fun p => IsBadTuple n A B α β p

/-- A fixed exponent tuple contributes at most `2 * sqrt n + 2` candidates.
This is the finite-cardinality version of Tijdeman's short-interval step. -/
lemma card_badTupleFiber_le (n A B α β : ℕ) (hαβ : α ≠ β) :
    (badTupleFiber n A B α β).card ≤ 2 * Nat.sqrt n + 2 := by
  classical
  let F := badTupleFiber n A B α β
  by_cases hF : F.Nonempty
  · let p₀ : ℕ := F.min' hF
    have hp₀mem : p₀ ∈ F := Finset.min'_mem F hF
    have hp₀tuple : IsBadTuple n A B α β p₀ :=
      (Finset.mem_filter.mp (show p₀ ∈ badTupleFiber n A B α β by
        simpa [F] using hp₀mem)).2
    have hsub : F ⊆ Finset.Icc p₀ (p₀ + (2 * Nat.sqrt n + 1)) := by
      intro q hqmem
      have hqtuple : IsBadTuple n A B α β q :=
        (Finset.mem_filter.mp (show q ∈ badTupleFiber n A B α β by
          simpa [F] using hqmem)).2
      have hp₀q : p₀ ≤ q := Finset.min'_le F q hqmem
      have hgapReal := hp₀tuple.cast_sub_lt_two_mul_sqrt hqtuple hαβ hp₀q
      have hsqrtUpper : Real.sqrt (n : ℝ) < Nat.sqrt n + 1 :=
        Real.real_sqrt_lt_nat_sqrt_succ
      have hgapUpperReal :
          ((q - p₀ : ℕ) : ℝ) < (2 * Nat.sqrt n + 2 : ℕ) := by
        calc
          ((q - p₀ : ℕ) : ℝ) < 2 * Real.sqrt (n : ℝ) := hgapReal
          _ < 2 * ((Nat.sqrt n : ℕ) : ℝ) + 2 := by linarith
          _ = ((2 * Nat.sqrt n + 2 : ℕ) : ℝ) := by norm_num
      have hgapUpper : q - p₀ < 2 * Nat.sqrt n + 2 := by exact_mod_cast hgapUpperReal
      exact Finset.mem_Icc.mpr ⟨hp₀q, by omega⟩
    have hcard := Finset.card_le_card hsub
    change F.card ≤ 2 * Nat.sqrt n + 2
    simp only [Nat.card_Icc] at hcard
    omega
  · have hEmpty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [F, hEmpty]

/-- Old-prime parts whose factorization coordinates are at most `L`. -/
noncomputable def boundedOldParts (s : Finset ℕ) (L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.pi s fun _ => Finset.range (L + 1)).image fun f =>
    s.attach.prod fun q => q.1 ^ f q.1 q.2

lemma mem_boundedOldParts {s : Finset ℕ} {L m : ℕ}
    (hm : IsSmooth (↑s : Set ℕ) m)
    (hbound : ∀ q ∈ s, m.factorization q ≤ L) :
    m ∈ boundedOldParts s L := by
  classical
  let f : ∀ q, q ∈ s → ℕ := fun q _ => m.factorization q
  have hf : f ∈ Finset.pi s fun _ => Finset.range (L + 1) := by
    rw [Finset.mem_pi]
    intro q hq
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hbound q hq)
  rw [boundedOldParts, Finset.mem_image]
  refine ⟨f, hf, ?_⟩
  simpa [f] using hm.prod_factorization_eq

lemma card_boundedOldParts_le (s : Finset ℕ) (L : ℕ) :
    (boundedOldParts s L).card ≤ (L + 1) ^ s.card := by
  classical
  unfold boundedOldParts
  calc
    ((Finset.pi s fun _ => Finset.range (L + 1)).image fun f =>
        s.attach.prod fun q => q.1 ^ f q.1 q.2).card ≤
        (Finset.pi s fun _ => Finset.range (L + 1)).card := Finset.card_image_le
    _ = (L + 1) ^ s.card := by simp [Finset.card_pi, Finset.prod_const]

/-- The finite collection of bounded exponent tuples, with the unequal-new-
exponent condition already imposed. -/
noncomputable def boundedExponentCodes (s : Finset ℕ) (L E : ℕ) :
    Finset (((ℕ × ℕ) × ℕ) × ℕ) := by
  classical
  exact ((((boundedOldParts s L).product (boundedOldParts s L)).product
    (Finset.range (E + 1))).product (Finset.range (E + 1))).filter fun c =>
      c.1.2 ≠ c.2

lemma card_boundedExponentCodes_le (s : Finset ℕ) (L E : ℕ) :
    (boundedExponentCodes s L E).card ≤
      (L + 1) ^ (2 * s.card) * (E + 1) ^ 2 := by
  classical
  have hold := card_boundedOldParts_le s L
  calc
    (boundedExponentCodes s L E).card ≤
        ((((boundedOldParts s L).product (boundedOldParts s L)).product
          (Finset.range (E + 1))).product (Finset.range (E + 1))).card := by
      exact Finset.card_filter_le _ _
    _ = (boundedOldParts s L).card * (boundedOldParts s L).card *
          (E + 1) * (E + 1) := by simp
    _ ≤ ((L + 1) ^ s.card) * ((L + 1) ^ s.card) *
          (E + 1) * (E + 1) := by gcongr
    _ = (L + 1) ^ (2 * s.card) * (E + 1) ^ 2 := by
      rw [← pow_add]
      have hcard : s.card + s.card = 2 * s.card := by omega
      rw [hcard]
      simp [pow_two, mul_assoc]

/-- Union of all fixed-tuple fibers allowed by the coordinate bounds. -/
noncomputable def boundedBadTupleCover (s : Finset ℕ) (n L E : ℕ) : Finset ℕ := by
  classical
  exact (boundedExponentCodes s L E).biUnion fun c =>
    badTupleFiber n c.1.1.1 c.1.1.2 c.1.2 c.2

lemma card_boundedBadTupleCover_le (s : Finset ℕ) (n L E : ℕ) :
    (boundedBadTupleCover s n L E).card ≤
      ((L + 1) ^ (2 * s.card) * (E + 1) ^ 2) *
        (2 * Nat.sqrt n + 2) := by
  classical
  have hfiber : ∀ c ∈ boundedExponentCodes s L E,
      (badTupleFiber n c.1.1.1 c.1.1.2 c.1.2 c.2).card ≤
        2 * Nat.sqrt n + 2 := by
    intro c hc
    have hne : c.1.2 ≠ c.2 := (Finset.mem_filter.mp hc).2
    exact card_badTupleFiber_le _ _ _ _ _ hne
  calc
    (boundedBadTupleCover s n L E).card ≤
        (boundedExponentCodes s L E).card * (2 * Nat.sqrt n + 2) := by
      exact Finset.card_biUnion_le_card_mul _ _ _ hfiber
    _ ≤ ((L + 1) ^ (2 * s.card) * (E + 1) ^ 2) *
          (2 * Nat.sqrt n + 2) := by
      gcongr
      exact card_boundedExponentCodes_le s L E

/-- Candidate primes for which adjoining the prime destroys the invariant. -/
noncomputable def badPrimesInHalfInterval {g : ℕ → ℕ}
    (s : FiniteStage g) (n : ℕ) : Finset ℕ := by
  classical
  exact (primeHalfInterval n).filter fun p =>
    ¬SeparatedBy g (↑(insert p s.carrier) : Set ℕ)

/-- Membership in the bad-candidate set supplies an explicit violating pair. -/
lemma exists_bad_pair_of_mem_bad {g : ℕ → ℕ} {s : FiniteStage g} {n p : ℕ}
    (hp : p ∈ badPrimesInHalfInterval s n) :
    ∃ a b : ℕ,
      IsSmooth (↑(insert p s.carrier) : Set ℕ) a ∧
      IsSmooth (↑(insert p s.carrier) : Set ℕ) b ∧
      a < b ∧ b - a < g a := by
  classical
  have hnot : ¬SeparatedBy g (↑(insert p s.carrier) : Set ℕ) :=
    (Finset.mem_filter.mp hp).2
  simp only [SeparatedBy] at hnot
  push Not at hnot
  exact hnot

/-- Every genuinely new bad prime belongs to a fixed-exponent tuple fiber;
the old parts are the products of the factorization coordinates on the
finite stage. -/
lemma exists_badTuple_of_mem_bad_fresh (s : FiniteStage Nat.sqrt) {n p : ℕ}
    (hpBad : p ∈ badPrimesInHalfInterval s n) (hpFresh : p ∉ s.carrier) :
    ∃ A B α β : ℕ, α ≠ β ∧ IsBadTuple n A B α β p := by
  classical
  obtain ⟨a, b, ha, hb, hab, hgap⟩ := exists_bad_pair_of_mem_bad hpBad
  have hpCandidate : p ∈ primeHalfInterval n := (Finset.mem_filter.mp hpBad).1
  have hpPrime : p.Prime := (Finset.mem_filter.mp hpCandidate).2
  let A : ℕ := ∏ q ∈ s.carrier, q ^ a.factorization q
  let B : ℕ := ∏ q ∈ s.carrier, q ^ b.factorization q
  let α : ℕ := a.factorization p
  let β : ℕ := b.factorization p
  have hApos : 0 < A := by
    dsimp [A]
    exact Finset.prod_pos fun q hq => pow_pos (s.prime_mem hq).pos _
  have hBpos : 0 < B := by
    dsimp [B]
    exact Finset.prod_pos fun q hq => pow_pos (s.prime_mem hq).pos _
  have haDecomp : p ^ α * A = a := by
    exact ha.eq_pow_mul_prod_factorization hpFresh
  have hbDecomp : p ^ β * B = b := by
    exact hb.eq_pow_mul_prod_factorization hpFresh
  have hne : α ≠ β :=
    factorization_ne_of_bad_pair s hpPrime hpFresh ha hb hab hgap
  refine ⟨A, B, α, β, hne, hpCandidate, hApos, hBpos, ?_, ?_⟩
  · rw [haDecomp, hbDecomp]
    exact hab
  · rw [haDecomp, hbDecomp]
    exact hgap

/- A convenient intermediate form of Tijdeman's estimate: at each finite
stage, the two smooth numbers in a bad pair are bounded by a fixed power of
the newly adjoined prime. -/
def HasTijdemanPowerBounds : Prop :=
  ∀ s : FiniteStage Nat.sqrt, ∃ C : ℕ,
    ∀ᶠ n : ℕ in atTop, ∀ ⦃p : ℕ⦄,
      p ∈ badPrimesInHalfInterval s n → p ∉ s.carrier →
      ∃ a b : ℕ,
        IsSmooth (↑(insert p s.carrier) : Set ℕ) a ∧
        IsSmooth (↑(insert p s.carrier) : Set ℕ) b ∧
        a < b ∧ b - a < Nat.sqrt a ∧
        a ≤ p ^ C ∧ b ≤ p ^ C

/- A power bound converts to a logarithmic bound for every factorization
coordinate, uniformly over the old primes. -/
lemma factorization_le_two_mul_log_of_le_prime_pow {m p q n C : ℕ}
    (hp : p ≤ n) (hq : 2 ≤ q) (hn : 2 ≤ n) (hm : m ≤ p ^ C) :
    m.factorization q ≤ 2 * (C + 1) * Nat.log 2 n := by
  apply Nat.factorization_le_of_le_pow
  calc
    m ≤ p ^ C := hm
    _ ≤ n ^ C := by gcongr
    _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ C := by
      gcongr
      exact (Nat.lt_pow_succ_log_self (by omega) n).le
    _ = 2 ^ (C * (Nat.log 2 n + 1)) := by
      simp only [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ (2 * (C + 1) * Nat.log 2 n) := by
      apply Nat.pow_le_pow_right (by omega)
      have hlog : 1 ≤ Nat.log 2 n := by
        exact Nat.le_log_of_pow_le (by omega) hn
      calc
        C * (Nat.log 2 n + 1) = C * Nat.log 2 n + C := by
          simp [Nat.mul_add]
        _ ≤ C * Nat.log 2 n + C * Nat.log 2 n := by
          apply Nat.add_le_add_left
          simpa using Nat.mul_le_mul_left C hlog
        _ ≤ 2 * (C + 1) * Nat.log 2 n := by
          ring_nf
          omega
    _ ≤ q ^ (2 * (C + 1) * Nat.log 2 n) := by gcongr

/-- The precise output needed from Baker's distinguished-last-logarithm
estimate: at each finite stage, every fresh bad candidate has uniformly
bounded new-prime exponents and old-prime coordinates of size `O(log n)`.
All subsequent counting is elementary and formalized below. -/
def HasTijdemanExponentBounds : Prop :=
  ∀ s : FiniteStage Nat.sqrt, ∃ E : ℕ,
    ∀ᶠ n : ℕ in atTop, ∀ ⦃p : ℕ⦄,
      p ∈ badPrimesInHalfInterval s n → p ∉ s.carrier →
      ∃ A ∈ boundedOldParts s.carrier (E * Nat.log 2 n),
      ∃ B ∈ boundedOldParts s.carrier (E * Nat.log 2 n),
      ∃ α ≤ E, ∃ β ≤ E, α ≠ β ∧ IsBadTuple n A B α β p

/- Tijdeman's natural power bound implies the exact coordinate bounds used
by the finite tuple count. -/
theorem HasTijdemanPowerBounds.toExponentBounds
    (hpower : HasTijdemanPowerBounds) : HasTijdemanExponentBounds := by
  classical
  intro s
  obtain ⟨C, hC⟩ := hpower s
  let E : ℕ := 2 * (C + 1)
  refine ⟨E, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (2 : ℕ)] with n hnPower hn
  intro p hpBad hpFresh
  obtain ⟨a, b, ha, hb, hab, hgap, haPower, hbPower⟩ :=
    hnPower hpBad hpFresh
  have hpCandidate : p ∈ primeHalfInterval n :=
    (Finset.mem_filter.mp hpBad).1
  have hpPrime : p.Prime := (Finset.mem_filter.mp hpCandidate).2
  have hp_le_n : p ≤ n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpCandidate).1).2
  let A : ℕ := ordCompl[p] a
  let B : ℕ := ordCompl[p] b
  let α : ℕ := a.factorization p
  let β : ℕ := b.factorization p
  have hAsmooth : IsSmooth (↑s.carrier : Set ℕ) A := by
    dsimp [A]
    exact isSmooth_ordCompl hpPrime (by simpa using hpFresh) (by simpa using ha)
  have hBsmooth : IsSmooth (↑s.carrier : Set ℕ) B := by
    dsimp [B]
    exact isSmooth_ordCompl hpPrime (by simpa using hpFresh) (by simpa using hb)
  have hA_le : A ≤ p ^ C := (Nat.ordCompl_le a p).trans haPower
  have hB_le : B ≤ p ^ C := (Nat.ordCompl_le b p).trans hbPower
  have hAmem : A ∈ boundedOldParts s.carrier (E * Nat.log 2 n) := by
    apply mem_boundedOldParts hAsmooth
    intro q hq
    exact factorization_le_two_mul_log_of_le_prime_pow hp_le_n
      (s.prime_mem hq).two_le hn hA_le
  have hBmem : B ∈ boundedOldParts s.carrier (E * Nat.log 2 n) := by
    apply mem_boundedOldParts hBsmooth
    intro q hq
    exact factorization_le_two_mul_log_of_le_prime_pow hp_le_n
      (s.prime_mem hq).two_le hn hB_le
  have hCE : C ≤ E := by
    dsimp [E]
    omega
  have hαE : α ≤ E :=
    (Nat.factorization_le_of_le_pow haPower).trans hCE
  have hβE : β ≤ E :=
    (Nat.factorization_le_of_le_pow hbPower).trans hCE
  have hne : α ≠ β :=
    factorization_ne_of_bad_pair s hpPrime hpFresh ha hb hab hgap
  have haDecomp : p ^ α * A = a := by
    exact Nat.ordProj_mul_ordCompl_eq_self a p
  have hbDecomp : p ^ β * B = b := by
    exact Nat.ordProj_mul_ordCompl_eq_self b p
  refine ⟨A, hAmem, B, hBmem, α, hαE, β, hβE, hne, ?_⟩
  refine ⟨hpCandidate, hAsmooth.1, hBsmooth.1, ?_, ?_⟩
  · rw [haDecomp, hbDecomp]
    exact hab
  · rw [haDecomp, hbDecomp]
    exact hgap

lemma badPrimes_subset_carrier_union_cover (s : FiniteStage Nat.sqrt)
    {n E : ℕ}
    (hbound : ∀ ⦃p : ℕ⦄,
      p ∈ badPrimesInHalfInterval s n → p ∉ s.carrier →
      ∃ A ∈ boundedOldParts s.carrier (E * Nat.log 2 n),
      ∃ B ∈ boundedOldParts s.carrier (E * Nat.log 2 n),
      ∃ α ≤ E, ∃ β ≤ E, α ≠ β ∧ IsBadTuple n A B α β p) :
    badPrimesInHalfInterval s n ⊆
      s.carrier ∪ boundedBadTupleCover s.carrier n (E * Nat.log 2 n) E := by
  classical
  intro p hpBad
  by_cases hpOld : p ∈ s.carrier
  · exact Finset.mem_union_left _ hpOld
  · rw [Finset.mem_union]
    right
    obtain ⟨A, hA, B, hB, α, hα, β, hβ, hne, htuple⟩ := hbound hpBad hpOld
    let c : ((ℕ × ℕ) × ℕ) × ℕ := (((A, B), α), β)
    have hc : c ∈ boundedExponentCodes s.carrier (E * Nat.log 2 n) E := by
      simp [c, boundedExponentCodes, hA, hB, hne, Nat.lt_succ_of_le hα,
        Nat.lt_succ_of_le hβ]
    rw [boundedBadTupleCover, Finset.mem_biUnion]
    refine ⟨c, hc, ?_⟩
    exact Finset.mem_filter.mpr ⟨htuple.1, htuple⟩

lemma badPrimes_card_le_of_exponent_bound (s : FiniteStage Nat.sqrt)
    {n E : ℕ}
    (hbound : ∀ ⦃p : ℕ⦄,
      p ∈ badPrimesInHalfInterval s n → p ∉ s.carrier →
      ∃ A ∈ boundedOldParts s.carrier (E * Nat.log 2 n),
      ∃ B ∈ boundedOldParts s.carrier (E * Nat.log 2 n),
      ∃ α ≤ E, ∃ β ≤ E, α ≠ β ∧ IsBadTuple n A B α β p) :
    (badPrimesInHalfInterval s n).card ≤ s.carrier.card +
      (((E * Nat.log 2 n + 1) ^ (2 * s.carrier.card) * (E + 1) ^ 2) *
        (2 * Nat.sqrt n + 2)) := by
  calc
    (badPrimesInHalfInterval s n).card ≤
        (s.carrier ∪ boundedBadTupleCover s.carrier n
          (E * Nat.log 2 n) E).card :=
      Finset.card_le_card (badPrimes_subset_carrier_union_cover s hbound)
    _ ≤ s.carrier.card +
        (boundedBadTupleCover s.carrier n (E * Nat.log 2 n) E).card :=
      Finset.card_union_le _ _
    _ ≤ s.carrier.card +
        (((E * Nat.log 2 n + 1) ^ (2 * s.carrier.card) * (E + 1) ^ 2) *
          (2 * Nat.sqrt n + 2)) := by
      gcongr
      exact card_boundedBadTupleCover_le _ _ _ _

/- The same finite-cover argument with independent cutoffs for the old-prime
coordinates and the newly adjoined prime.  This form is useful with the
ordinary (symmetric) Baker--Wüstholz estimate, which gives polylogarithmic
rather than constant new-prime exponents. -/
lemma badPrimes_subset_carrier_union_cover_of_coordinate_bound
    (s : FiniteStage Nat.sqrt) {n L E : ℕ}
    (hbound : ∀ ⦃p : ℕ⦄,
      p ∈ badPrimesInHalfInterval s n → p ∉ s.carrier →
      ∃ A ∈ boundedOldParts s.carrier L,
      ∃ B ∈ boundedOldParts s.carrier L,
      ∃ α ≤ E, ∃ β ≤ E, α ≠ β ∧ IsBadTuple n A B α β p) :
    badPrimesInHalfInterval s n ⊆
      s.carrier ∪ boundedBadTupleCover s.carrier n L E := by
  classical
  intro p hpBad
  by_cases hpOld : p ∈ s.carrier
  · exact Finset.mem_union_left _ hpOld
  · rw [Finset.mem_union]
    right
    obtain ⟨A, hA, B, hB, α, hα, β, hβ, hne, htuple⟩ := hbound hpBad hpOld
    let c : ((ℕ × ℕ) × ℕ) × ℕ := (((A, B), α), β)
    have hc : c ∈ boundedExponentCodes s.carrier L E := by
      simp [c, boundedExponentCodes, hA, hB, hne, Nat.lt_succ_of_le hα,
        Nat.lt_succ_of_le hβ]
    rw [boundedBadTupleCover, Finset.mem_biUnion]
    refine ⟨c, hc, ?_⟩
    exact Finset.mem_filter.mpr ⟨htuple.1, htuple⟩

lemma badPrimes_card_le_of_coordinate_bound (s : FiniteStage Nat.sqrt)
    {n L E : ℕ}
    (hbound : ∀ ⦃p : ℕ⦄,
      p ∈ badPrimesInHalfInterval s n → p ∉ s.carrier →
      ∃ A ∈ boundedOldParts s.carrier L,
      ∃ B ∈ boundedOldParts s.carrier L,
      ∃ α ≤ E, ∃ β ≤ E, α ≠ β ∧ IsBadTuple n A B α β p) :
    (badPrimesInHalfInterval s n).card ≤ s.carrier.card +
      (((L + 1) ^ (2 * s.carrier.card) * (E + 1) ^ 2) *
        (2 * Nat.sqrt n + 2)) := by
  calc
    (badPrimesInHalfInterval s n).card ≤
        (s.carrier ∪ boundedBadTupleCover s.carrier n L E).card :=
      Finset.card_le_card
        (badPrimes_subset_carrier_union_cover_of_coordinate_bound s hbound)
    _ ≤ s.carrier.card + (boundedBadTupleCover s.carrier n L E).card :=
      Finset.card_union_le _ _
    _ ≤ s.carrier.card +
        (((L + 1) ^ (2 * s.carrier.card) * (E + 1) ^ 2) *
          (2 * Nat.sqrt n + 2)) := by
      gcongr
      exact card_boundedBadTupleCover_le _ _ _ _

/- The coordinate-bound interface naturally produced by the ordinary
Baker--Wüstholz theorem.  A square of the binary logarithm is deliberately
generous; any fixed polylogarithmic exponent cutoff would give the same final
sparse-bad-prime conclusion. -/
def HasTijdemanSquareLogBounds : Prop :=
  ∀ s : FiniteStage Nat.sqrt, ∃ E : ℕ,
    ∀ᶠ n : ℕ in atTop, ∀ ⦃p : ℕ⦄,
      p ∈ badPrimesInHalfInterval s n → p ∉ s.carrier →
      ∃ A ∈ boundedOldParts s.carrier (E * (Nat.log 2 n) ^ 2),
      ∃ B ∈ boundedOldParts s.carrier (E * (Nat.log 2 n) ^ 2),
      ∃ α ≤ E * (Nat.log 2 n) ^ 2,
      ∃ β ≤ E * (Nat.log 2 n) ^ 2,
        α ≠ β ∧ IsBadTuple n A B α β p

/-- The rational linear form in logarithms associated to a fixed finite stage
and one distinguished varying prime. -/
noncomputable def rationalLogForm (s : FiniteStage Nat.sqrt) (p : ℕ)
    (c : ℕ → ℤ) (d : ℤ) : ℝ :=
  ∑ q ∈ s.carrier, (c q : ℝ) * Real.log (q : ℝ) +
    (d : ℝ) * Real.log (p : ℝ)

/-- A symmetric Baker--Wüstholz interface specialized in its algebraic bases.
The old bases are the fixed primes of `s`; the varying prime has an arbitrary
nonzero integer coefficient, exactly as in the distinguished-last-logarithm
theorem.  This is sufficient here because `factorization_ne_of_bad_pair`
shows that the fresh-prime coefficient attached to every bad pair is nonzero.
The constant absorbs the fixed old heights and depends only on the finite
stage. -/
def HasRationalBakerWustholzBounds : Prop :=
  ∀ s : FiniteStage Nat.sqrt, ∃ K : ℝ, 0 < K ∧
    ∀ ⦃p : ℕ⦄ (c : ℕ → ℤ) (d : ℤ) (B : ℝ),
      p.Prime → p ∉ s.carrier → Real.exp 1 ≤ B →
      (∀ q ∈ s.carrier, |(c q : ℝ)| ≤ B) → |(d : ℝ)| ≤ B →
      d ≠ 0 →
      rationalLogForm s p c d ≠ 0 →
      Real.exp (-K * Real.log (p : ℝ) * Real.log B) ≤
        |rationalLogForm s p c d|

lemma factorization_le_natLog_two {m q : ℕ} (hm : m ≠ 0) (hq : q.Prime) :
    m.factorization q ≤ Nat.log 2 m := by
  have hfac : m.factorization q ≤ Nat.log q m := by
    apply Nat.le_log_of_pow_le hq.one_lt
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm)
      ((hq.pow_dvd_iff_le_factorization hm).mpr le_rfl)
  exact hfac.trans
    (Nat.log_antitone_left (n := m) (by omega : 1 < 2) hq.one_lt hq.two_le)

lemma natLog_two_cast_le_two_log {m : ℕ} (hm : 2 ≤ m) :
    ((Nat.log 2 m : ℕ) : ℝ) ≤ 2 * Real.log (m : ℝ) := by
  have hfloor := Real.natLog_le_logb m 2
  rw [Real.logb] at hfloor
  have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hquot : Real.log (m : ℝ) / Real.log (2 : ℝ) ≤
      2 * Real.log (m : ℝ) := by
    rw [div_le_iff₀ hlogTwoPos]
    nlinarith [Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact hfloor.trans hquot

lemma log_eq_sum_factorization_of_smooth {S : Finset ℕ} {m : ℕ}
    (hm : IsSmooth (↑S : Set ℕ) m) :
    Real.log (m : ℝ) =
      ∑ q ∈ S, (m.factorization q : ℝ) * Real.log (q : ℝ) := by
  have hsupp : m.primeFactors ⊆ S := by
    intro q hq
    have hqData := Nat.mem_primeFactors.mp hq
    exact hm.2 q hqData.1 hqData.2.1
  have hfull : Real.log (m : ℝ) =
      ∑ q ∈ m.primeFactors,
        (m.factorization q : ℝ) * Real.log (q : ℝ) := by
    simpa only [Finsupp.sum, Nat.support_factorization] using
      Real.log_nat_eq_sum_factorization m
  rw [hfull]
  apply Finset.sum_subset hsupp
  intro q hqS hqnot
  have hfac : m.factorization q = 0 := by
    rw [← Finsupp.notMem_support_iff]
    simpa only [Nat.support_factorization] using hqnot
  simp [hfac]

lemma rationalLogForm_factorization_eq_log_div
    (s : FiniteStage Nat.sqrt) {p a b : ℕ} (hpFresh : p ∉ s.carrier)
    (ha : IsSmooth (↑(insert p s.carrier) : Set ℕ) a)
    (hb : IsSmooth (↑(insert p s.carrier) : Set ℕ) b) :
    rationalLogForm s p
        (fun q => (b.factorization q : ℤ) - (a.factorization q : ℤ))
        ((b.factorization p : ℤ) - (a.factorization p : ℤ)) =
      Real.log ((b : ℝ) / (a : ℝ)) := by
  have haLog := log_eq_sum_factorization_of_smooth ha
  have hbLog := log_eq_sum_factorization_of_smooth hb
  rw [Finset.sum_insert hpFresh] at haLog hbLog
  have haNe : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha.1)
  have hbNe : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb.1)
  rw [Real.log_div hbNe haNe]
  dsimp [rationalLogForm]
  simp only [Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib]
  rw [haLog, hbLog]
  ring

/-- The symmetric rational Baker--Wüstholz estimate implies the square-log
coordinate bounds needed by the finite bad-prime counting argument. -/
theorem HasRationalBakerWustholzBounds.toSquareLogBounds
    (hBW : HasRationalBakerWustholzBounds) : HasTijdemanSquareLogBounds := by
  classical
  intro s
  obtain ⟨K, hK, hBWstage⟩ := hBW s
  let D : ℝ := 4 + 128 * K ^ 2
  obtain ⟨E : ℕ, hE⟩ := exists_nat_ge (4 * D)
  refine ⟨E, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
  intro p hpBad hpFresh
  obtain ⟨a, b, ha, hb, hab, hgap⟩ := exists_bad_pair_of_mem_bad hpBad
  have hpCandidate : p ∈ primeHalfInterval n := (Finset.mem_filter.mp hpBad).1
  have hpPrime : p.Prime := (Finset.mem_filter.mp hpCandidate).2
  have hp_le_n : p ≤ n :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpCandidate).1).2
  have haFour : 4 ≤ a := by
    have hgapPos : 0 < b - a := Nat.sub_pos_of_lt hab
    have hsqrtTwo : 2 ≤ Nat.sqrt a := by omega
    have hsquare : Nat.sqrt a ^ 2 ≤ a := Nat.sqrt_le' a
    nlinarith
  have hbTwoA : b ≤ 2 * a := by
    have hsqrtLe : Nat.sqrt a ≤ a := Nat.sqrt_le_self _
    omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha.1
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlogaPos : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogpPos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hlogaOne : 1 ≤ Real.log (a : ℝ) := by
    have hlogFour : 1 ≤ Real.log (4 : ℝ) := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      nlinarith [Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmono : Real.log (4 : ℝ) ≤ Real.log (a : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) haR (by exact_mod_cast haFour)
    exact hlogFour.trans hmono
  have hlogb_le : Real.log (b : ℝ) ≤ 2 * Real.log (a : ℝ) := by
    have hmono : Real.log (b : ℝ) ≤ Real.log (2 * (a : ℝ)) :=
      Real.strictMonoOn_log.monotoneOn hbR (mul_pos (by norm_num) haR)
        (by exact_mod_cast hbTwoA)
    rw [Real.log_mul (by norm_num) haR.ne'] at hmono
    have hlogTwoLe : Real.log (2 : ℝ) ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hnatLogB : ((Nat.log 2 b : ℕ) : ℝ) ≤ 4 * Real.log (a : ℝ) :=
    (natLog_two_cast_le_two_log (by omega : 2 ≤ b)).trans (by nlinarith)
  let c : ℕ → ℤ := fun q => (b.factorization q : ℤ) - (a.factorization q : ℤ)
  let d : ℤ := (b.factorization p : ℤ) - (a.factorization p : ℤ)
  let B : ℝ := 5 * Real.log (a : ℝ)
  have hBExp : Real.exp 1 ≤ B := by
    dsimp [B]
    exact Real.exp_one_lt_three.le.trans (by nlinarith)
  have hfacA (q : ℕ) (hq : q.Prime) :
      a.factorization q ≤ Nat.log 2 b :=
    (factorization_le_natLog_two (Nat.ne_of_gt ha.1) hq).trans
      (Nat.log_mono_right hab.le)
  have hfacB (q : ℕ) (hq : q.Prime) :
      b.factorization q ≤ Nat.log 2 b :=
    factorization_le_natLog_two (Nat.ne_of_gt hb.1) hq
  have hcBound : ∀ q ∈ s.carrier, |(c q : ℝ)| ≤ B := by
    intro q hq
    have haQ := hfacA q (s.prime_mem hq)
    have hbQ := hfacB q (s.prime_mem hq)
    have haQR : ((a.factorization q : ℕ) : ℝ) ≤ (Nat.log 2 b : ℕ) := by
      exact_mod_cast haQ
    have hbQR : ((b.factorization q : ℕ) : ℝ) ≤ (Nat.log 2 b : ℕ) := by
      exact_mod_cast hbQ
    dsimp [c]
    simp only [Int.cast_sub, Int.cast_natCast, abs_le]
    constructor <;> dsimp [B] <;> nlinarith
  have hdBound : |(d : ℝ)| ≤ B := by
    have haP := hfacA p hpPrime
    have hbP := hfacB p hpPrime
    have haPR : ((a.factorization p : ℕ) : ℝ) ≤ (Nat.log 2 b : ℕ) := by
      exact_mod_cast haP
    have hbPR : ((b.factorization p : ℕ) : ℝ) ≤ (Nat.log 2 b : ℕ) := by
      exact_mod_cast hbP
    dsimp [d]
    simp only [Int.cast_sub, Int.cast_natCast, abs_le]
    constructor <;> dsimp [B] <;> nlinarith
  have hfacNe : a.factorization p ≠ b.factorization p :=
    factorization_ne_of_bad_pair s hpPrime hpFresh ha hb hab hgap
  have hdNe : d ≠ 0 := by
    dsimp [d]
    omega
  have hform : rationalLogForm s p c d =
      Real.log ((b : ℝ) / (a : ℝ)) :=
    rationalLogForm_factorization_eq_log_div s hpFresh ha hb
  have hlambdaPos : 0 < Real.log ((b : ℝ) / (a : ℝ)) := by
    apply Real.log_pos
    rw [one_lt_div haR]
    exact_mod_cast hab
  have hformNe : rationalLogForm s p c d ≠ 0 := by
    rw [hform]
    exact hlambdaPos.ne'
  have hlower :=
    hBWstage c d B hpPrime hpFresh hBExp hcBound hdBound hdNe hformNe
  rw [hform, abs_of_pos hlambdaPos] at hlower
  have hupper := log_ratio_lt_exp_neg_half_log_of_bad_gap ha.1 hab hgap
  have hargs := Real.exp_lt_exp.mp (hlower.trans_lt hupper)
  have hbootstrap : Real.log (a : ℝ) / 2 <
      K * Real.log (p : ℝ) * Real.log (5 * Real.log (a : ℝ)) := by
    dsimp [B] at hargs
    nlinarith
  have hlogaBound : Real.log (a : ℝ) ≤
      64 * K ^ 2 * Real.log (p : ℝ) ^ 2 :=
    le_sixtyFour_mul_sq_of_half_lt_mul_log hlogpPos.le hlogaOne hK.le hbootstrap
  have hlogpSq : Real.log (p : ℝ) ≤ 2 * Real.log (p : ℝ) ^ 2 := by
    have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hpR (by exact_mod_cast hpPrime.two_le)
    nlinarith [Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2),
      sq_nonneg (Real.log (p : ℝ))]
  have hlogbBound : Real.log (b : ℝ) ≤ D * Real.log (p : ℝ) ^ 2 / 2 := by
    have hmono : Real.log (b : ℝ) ≤
        Real.log (2 : ℝ) + Real.log (a : ℝ) := by
      have hmono' : Real.log (b : ℝ) ≤ Real.log (2 * (a : ℝ)) :=
        Real.strictMonoOn_log.monotoneOn hbR (mul_pos (by norm_num) haR)
          (by exact_mod_cast hbTwoA)
      simpa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) haR.ne'] using hmono'
    have hlogTwoLeP : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hpR (by exact_mod_cast hpPrime.two_le)
    dsimp [D]
    nlinarith
  let L : ℕ := Nat.log 2 n
  have hlogpL : Real.log (p : ℝ) ≤ 2 * (L : ℝ) := by
    simpa [L] using real_log_le_two_natLog_two hpPrime.two_le hp_le_n
  have hlogpSqL : Real.log (p : ℝ) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by
    have hsquare := mul_self_le_mul_self hlogpPos.le hlogpL
    nlinarith only [hsquare]
  have hcoordReal : 2 * Real.log (b : ℝ) ≤ (E : ℝ) * (L : ℝ) ^ 2 := by
    have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
    have h1 : 2 * Real.log (b : ℝ) ≤ D * Real.log (p : ℝ) ^ 2 := by
      linarith
    have h2 : D * Real.log (p : ℝ) ^ 2 ≤ 4 * D * (L : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hlogpSqL hDnonneg
      nlinarith only [this]
    have h3 : 4 * D * (L : ℝ) ^ 2 ≤ (E : ℝ) * (L : ℝ) ^ 2 := by
      have hER : 4 * D ≤ (E : ℝ) := hE
      exact mul_le_mul_of_nonneg_right hER (sq_nonneg _)
    exact h1.trans (h2.trans h3)
  have haCoord (q : ℕ) (hq : q.Prime) :
      a.factorization q ≤ E * L ^ 2 := by
    have hnat := hfacA q hq
    have hcast : ((a.factorization q : ℕ) : ℝ) ≤ 2 * Real.log (b : ℝ) :=
      (by exact_mod_cast hnat : ((a.factorization q : ℕ) : ℝ) ≤
        (Nat.log 2 b : ℕ)).trans (natLog_two_cast_le_two_log (by omega))
    exact_mod_cast hcast.trans hcoordReal
  have hbCoord (q : ℕ) (hq : q.Prime) :
      b.factorization q ≤ E * L ^ 2 := by
    have hnat := hfacB q hq
    have hcast : ((b.factorization q : ℕ) : ℝ) ≤ 2 * Real.log (b : ℝ) :=
      (by exact_mod_cast hnat : ((b.factorization q : ℕ) : ℝ) ≤
        (Nat.log 2 b : ℕ)).trans (natLog_two_cast_le_two_log (by omega))
    exact_mod_cast hcast.trans hcoordReal
  let A : ℕ := ordCompl[p] a
  let B₀ : ℕ := ordCompl[p] b
  let α : ℕ := a.factorization p
  let β : ℕ := b.factorization p
  have hAsmooth : IsSmooth (↑s.carrier : Set ℕ) A := by
    exact isSmooth_ordCompl hpPrime (by simpa using hpFresh) (by simpa using ha)
  have hBsmooth : IsSmooth (↑s.carrier : Set ℕ) B₀ := by
    exact isSmooth_ordCompl hpPrime (by simpa using hpFresh) (by simpa using hb)
  have hAmem : A ∈ boundedOldParts s.carrier (E * L ^ 2) := by
    apply mem_boundedOldParts hAsmooth
    intro q hq
    have hqp : q ≠ p := fun h => hpFresh (h ▸ hq)
    simpa [A, Nat.factorization_ordCompl, hqp] using haCoord q (s.prime_mem hq)
  have hBmem : B₀ ∈ boundedOldParts s.carrier (E * L ^ 2) := by
    apply mem_boundedOldParts hBsmooth
    intro q hq
    have hqp : q ≠ p := fun h => hpFresh (h ▸ hq)
    simpa [B₀, Nat.factorization_ordCompl, hqp] using hbCoord q (s.prime_mem hq)
  have hα : α ≤ E * L ^ 2 := haCoord p hpPrime
  have hβ : β ≤ E * L ^ 2 := hbCoord p hpPrime
  have hne : α ≠ β :=
    factorization_ne_of_bad_pair s hpPrime hpFresh ha hb hab hgap
  have haDecomp : p ^ α * A = a := Nat.ordProj_mul_ordCompl_eq_self a p
  have hbDecomp : p ^ β * B₀ = b := Nat.ordProj_mul_ordCompl_eq_self b p
  refine ⟨A, ?_, B₀, ?_, α, ?_, β, ?_, hne, ?_⟩
  · simpa [L] using hAmem
  · simpa [L] using hBmem
  · simpa [L] using hα
  · simpa [L] using hβ
  · refine ⟨hpCandidate, hAsmooth.1, hBsmooth.1, ?_, ?_⟩
    · rw [haDecomp, hbDecomp]
      exact hab
    · rw [haDecomp, hbDecomp]
      exact hgap

lemma eventually_squareLog_bad_envelope_le
    (s : FiniteStage Nat.sqrt) (E : ℕ) :
    let r := 2 * s.carrier.card
    let t := r + 2
    let C : ℝ := (s.carrier.card : ℝ) +
      4 * ((4 * E + 1 : ℕ) : ℝ) ^ t
    ∀ᶠ n : ℕ in atTop,
      let K := E * (Nat.log 2 n) ^ 2
      ((s.carrier.card +
        (((K + 1) ^ r * (K + 1) ^ 2) *
          (2 * Nat.sqrt n + 2)) : ℕ) : ℝ) ≤
        C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (2 * t) := by
  dsimp only
  filter_upwards [eventually_ge_atTop 4] with n hn
  let r : ℕ := 2 * s.carrier.card
  let t : ℕ := r + 2
  let D : ℝ := ((4 * E + 1 : ℕ) : ℝ)
  let X : ℝ := Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (2 * t)
  have hnPos : 0 < (n : ℝ) := by positivity
  have hlogFour : 1 < Real.log (4 : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hlogMono : Real.log (4 : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hnPos
      (by exact_mod_cast hn)
  have hlogOne : 1 ≤ Real.log (n : ℝ) := (le_of_lt hlogFour).trans hlogMono
  have hsqrtOne : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogPowOne : 1 ≤ (Real.log (n : ℝ)) ^ (2 * t) :=
    one_le_pow₀ hlogOne
  have hXOne : 1 ≤ X := by
    dsimp [X]
    simpa only [one_mul] using
      (mul_le_mul hsqrtOne hlogPowOne (by norm_num) (by positivity))
  have hnatLog : ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hfloor := Real.natLog_le_logb n 2
    rw [Real.logb] at hfloor
    have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hquot : Real.log (n : ℝ) / Real.log (2 : ℝ) ≤
        2 * Real.log (n : ℝ) := by
      rw [div_le_iff₀ hlogTwoPos]
      have hlogNonneg : 0 ≤ Real.log (n : ℝ) := hlogOne.trans' zero_le_one
      nlinarith [Real.log_two_gt_d9]
    exact hfloor.trans hquot
  have hnatLogSq : ((Nat.log 2 n : ℕ) : ℝ) ^ 2 ≤
      (2 * Real.log (n : ℝ)) ^ 2 := by
    gcongr
  have hlogSqOne : 1 ≤ (Real.log (n : ℝ)) ^ 2 := one_le_pow₀ hlogOne
  have hbase : ((E * (Nat.log 2 n) ^ 2 + 1 : ℕ) : ℝ) ≤
      D * (Real.log (n : ℝ)) ^ 2 := by
    dsimp [D]
    push_cast
    nlinarith
  have hsqrtNat : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hgapFactor : ((2 * Nat.sqrt n + 2 : ℕ) : ℝ) ≤
      4 * Real.sqrt (n : ℝ) := by
    push_cast
    nlinarith
  have htuple :
      ((((E * (Nat.log 2 n) ^ 2 + 1) ^ r *
        (E * (Nat.log 2 n) ^ 2 + 1) ^ 2) *
        (2 * Nat.sqrt n + 2) : ℕ) : ℝ) ≤
      (4 * D ^ t) * X := by
    push_cast
    have hbase' :
        ↑E * ↑(Nat.log 2 n) ^ 2 + 1 ≤ D * Real.log (n : ℝ) ^ 2 := by
      simpa using hbase
    have hgapFactor' : 2 * ↑(Nat.sqrt n) + 2 ≤
        4 * Real.sqrt (n : ℝ) := by
      simpa using hgapFactor
    calc
      (↑E * ↑(Nat.log 2 n) ^ 2 + 1) ^ r *
          (↑E * ↑(Nat.log 2 n) ^ 2 + 1) ^ 2 *
          (2 * ↑(Nat.sqrt n) + 2) ≤
          (D * Real.log (n : ℝ) ^ 2) ^ r *
            (D * Real.log (n : ℝ) ^ 2) ^ 2 *
            (4 * Real.sqrt (n : ℝ)) := by
        gcongr
      _ = (4 * D ^ t) * X := by
        dsimp [t, X]
        rw [← pow_add, mul_pow, ← pow_mul]
        ring
  have hconstant : (s.carrier.card : ℝ) ≤ (s.carrier.card : ℝ) * X := by
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) hXOne
  calc
    ((s.carrier.card +
        ((((E * (Nat.log 2 n) ^ 2 + 1) ^ (2 * s.carrier.card)) *
          (E * (Nat.log 2 n) ^ 2 + 1) ^ 2) *
          (2 * Nat.sqrt n + 2)) : ℕ) : ℝ) =
        (s.carrier.card : ℝ) +
        (((((E * (Nat.log 2 n) ^ 2 + 1) ^ r) *
          (E * (Nat.log 2 n) ^ 2 + 1) ^ 2) *
          (2 * Nat.sqrt n + 2) : ℕ) : ℝ) := by norm_num [r]
    _ ≤ (s.carrier.card : ℝ) * X + (4 * D ^ t) * X :=
      add_le_add hconstant htuple
    _ = ((s.carrier.card : ℝ) + 4 * D ^ t) *
        Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (2 * t) := by
      dsimp [X]
      ring
    _ = ((s.carrier.card : ℝ) +
        4 * ((4 * E + 1 : ℕ) : ℝ) ^ (2 * s.carrier.card + 2)) *
        Real.sqrt (n : ℝ) *
          (Real.log (n : ℝ)) ^ (2 * (2 * s.carrier.card + 2)) := by
      rfl

lemma eventually_explicit_bad_envelope_le (s : FiniteStage Nat.sqrt) (E : ℕ) :
    let r := 2 * s.carrier.card
    let C : ℝ := (s.carrier.card : ℝ) +
      4 * ((2 * E + 1 : ℕ) : ℝ) ^ r * ((E + 1 : ℕ) : ℝ) ^ 2
    ∀ᶠ n : ℕ in atTop,
      ((s.carrier.card +
        (((E * Nat.log 2 n + 1) ^ r * (E + 1) ^ 2) *
          (2 * Nat.sqrt n + 2)) : ℕ) : ℝ) ≤
        C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ r := by
  dsimp only
  filter_upwards [eventually_ge_atTop 4] with n hn
  let r : ℕ := 2 * s.carrier.card
  let D : ℝ := ((2 * E + 1 : ℕ) : ℝ)
  let X : ℝ := Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ r
  have hnPos : 0 < (n : ℝ) := by positivity
  have hlogFour : 1 < Real.log (4 : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hlogMono : Real.log (4 : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hnPos
      (by exact_mod_cast hn)
  have hlogOne : 1 ≤ Real.log (n : ℝ) := (le_of_lt hlogFour).trans hlogMono
  have hsqrtOne : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogPowOne : 1 ≤ (Real.log (n : ℝ)) ^ r :=
    one_le_pow₀ hlogOne
  have hXOne : 1 ≤ X := by
    dsimp [X]
    simpa only [one_mul] using
      (mul_le_mul hsqrtOne hlogPowOne (by norm_num) (by positivity))
  have hnatLog : ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hfloor := Real.natLog_le_logb n 2
    rw [Real.logb] at hfloor
    have hlogTwoPos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hquot : Real.log (n : ℝ) / Real.log (2 : ℝ) ≤
        2 * Real.log (n : ℝ) := by
      rw [div_le_iff₀ hlogTwoPos]
      have hlogNonneg : 0 ≤ Real.log (n : ℝ) := hlogOne.trans' zero_le_one
      nlinarith [Real.log_two_gt_d9]
    exact hfloor.trans hquot
  have hbase : ((E * Nat.log 2 n + 1 : ℕ) : ℝ) ≤
      D * Real.log (n : ℝ) := by
    dsimp [D]
    push_cast
    nlinarith
  have hbasePow : ((E * Nat.log 2 n + 1 : ℕ) : ℝ) ^ r ≤
      (D * Real.log (n : ℝ)) ^ r := by
    gcongr
  have hsqrtNat : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hgapFactor : ((2 * Nat.sqrt n + 2 : ℕ) : ℝ) ≤
      4 * Real.sqrt (n : ℝ) := by
    push_cast
    nlinarith
  have htuple :
      ((((E * Nat.log 2 n + 1) ^ r * (E + 1) ^ 2) *
        (2 * Nat.sqrt n + 2) : ℕ) : ℝ) ≤
      (4 * D ^ r * ((E + 1 : ℕ) : ℝ) ^ 2) * X := by
    push_cast
    have hbase' : ↑E * ↑(Nat.log 2 n) + 1 ≤ D * Real.log (n : ℝ) := by
      simpa using hbase
    have hgapFactor' : 2 * ↑(Nat.sqrt n) + 2 ≤ 4 * Real.sqrt (n : ℝ) := by
      simpa using hgapFactor
    calc
      (↑E * ↑(Nat.log 2 n) + 1) ^ r * (↑E + 1) ^ 2 *
          (2 * ↑(Nat.sqrt n) + 2) ≤
          (D * Real.log (n : ℝ)) ^ r * (↑E + 1) ^ 2 *
            (4 * Real.sqrt (n : ℝ)) := by
        gcongr
      _ = (4 * D ^ r * (↑E + 1) ^ 2) * X := by
        dsimp [X]
        rw [mul_pow]
        ring
  have hconstant : (s.carrier.card : ℝ) ≤ (s.carrier.card : ℝ) * X := by
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) hXOne
  calc
    ((s.carrier.card +
        (((E * Nat.log 2 n + 1) ^ r * (E + 1) ^ 2) *
          (2 * Nat.sqrt n + 2)) : ℕ) : ℝ) =
        (s.carrier.card : ℝ) +
        ((((E * Nat.log 2 n + 1) ^ r * (E + 1) ^ 2) *
          (2 * Nat.sqrt n + 2) : ℕ) : ℝ) := by norm_num
    _ ≤
        (s.carrier.card : ℝ) * X +
          (4 * D ^ r * ((E + 1 : ℕ) : ℝ) ^ 2) * X :=
      add_le_add hconstant htuple
    _ = ((s.carrier.card : ℝ) +
          4 * D ^ r * ((E + 1 : ℕ) : ℝ) ^ 2) *
          Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ r := by
      dsimp [X]
      ring
    _ = ((s.carrier.card : ℝ) +
          4 * ((2 * E + 1 : ℕ) : ℝ) ^ (2 * s.carrier.card) *
            ((E + 1 : ℕ) : ℝ) ^ 2) *
          Real.sqrt (n : ℝ) *
            (Real.log (n : ℝ)) ^ (2 * s.carrier.card) := by
      rfl

/-- The quantitative conclusion of Tijdeman's Baker-and-counting argument.
The number of bad candidates is bounded by a square-root power times a fixed
power of the logarithm. -/
def HasSparseBadPrimes (g : ℕ → ℕ) : Prop :=
  ∀ s : FiniteStage g, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
    ∀ᶠ n : ℕ in atTop,
      ((badPrimesInHalfInterval s n).card : ℝ) ≤
        C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
          Real.rpow (Real.log (n : ℝ)) A

/- Ordinary Baker--Wüstholz bounds are enough: allowing all factorization
coordinates to be quadratic in `log n` still leaves only polylogarithmically
many tuples, while every fixed tuple contributes `O(sqrt n)` candidates. -/
theorem sparseBadPrimes_of_tijdemanSquareLogBounds
    (hBaker : HasTijdemanSquareLogBounds) : HasSparseBadPrimes Nat.sqrt := by
  intro s
  obtain ⟨E, hE⟩ := hBaker s
  let r : ℕ := 2 * s.carrier.card
  let t : ℕ := r + 2
  let C : ℝ := (s.carrier.card : ℝ) +
    4 * ((4 * E + 1 : ℕ) : ℝ) ^ t
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hA : 0 ≤ ((2 * t : ℕ) : ℝ) := by positivity
  refine ⟨C, ((2 * t : ℕ) : ℝ), hC, hA, ?_⟩
  have hEnvelope := eventually_squareLog_bad_envelope_le s E
  filter_upwards [hE, hEnvelope] with n hnBound hnEnvelope
  let K : ℕ := E * (Nat.log 2 n) ^ 2
  have hcardNat :
      (badPrimesInHalfInterval s n).card ≤ s.carrier.card +
        (((K + 1) ^ r * (K + 1) ^ 2) * (2 * Nat.sqrt n + 2)) := by
    exact badPrimes_card_le_of_coordinate_bound s hnBound
  have hcardReal :
      ((badPrimesInHalfInterval s n).card : ℝ) ≤
        ((s.carrier.card +
          (((K + 1) ^ r * (K + 1) ^ 2) *
            (2 * Nat.sqrt n + 2)) : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((badPrimesInHalfInterval s n).card : ℝ) ≤
        ((s.carrier.card +
          (((K + 1) ^ r * (K + 1) ^ 2) *
            (2 * Nat.sqrt n + 2)) : ℕ) : ℝ) := hcardReal
    _ ≤ C * Real.sqrt (n : ℝ) *
        (Real.log (n : ℝ)) ^ (2 * t) := by
      simpa only [C, r, t, K] using hnEnvelope
    _ = C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
        Real.rpow (Real.log (n : ℝ)) ((2 * t : ℕ) : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      exact (Real.rpow_natCast (Real.log (n : ℝ)) (2 * t)).symm

/-- Once Baker supplies the uniform exponent cutoff, the fully formalized
tuple count gives Tijdeman's sparse-bad-prime estimate. -/
theorem sparseBadPrimes_of_tijdemanExponentBounds
    (hBaker : HasTijdemanExponentBounds) : HasSparseBadPrimes Nat.sqrt := by
  intro s
  obtain ⟨E, hE⟩ := hBaker s
  let r : ℕ := 2 * s.carrier.card
  let C : ℝ := (s.carrier.card : ℝ) +
    4 * ((2 * E + 1 : ℕ) : ℝ) ^ r * ((E + 1 : ℕ) : ℝ) ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hr : 0 ≤ (r : ℝ) := by positivity
  refine ⟨C, (r : ℝ), hC, hr, ?_⟩
  have hEnvelope := eventually_explicit_bad_envelope_le s E
  filter_upwards [hE, hEnvelope] with n hnBound hnEnvelope
  have hcardNat := badPrimes_card_le_of_exponent_bound s hnBound
  have hcardReal :
      ((badPrimesInHalfInterval s n).card : ℝ) ≤
        ((s.carrier.card +
          (((E * Nat.log 2 n + 1) ^ r * (E + 1) ^ 2) *
            (2 * Nat.sqrt n + 2)) : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((badPrimesInHalfInterval s n).card : ℝ) ≤
        ((s.carrier.card +
          (((E * Nat.log 2 n + 1) ^ r * (E + 1) ^ 2) *
            (2 * Nat.sqrt n + 2)) : ℕ) : ℝ) := hcardReal
    _ ≤ C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ r := by
      simpa only [C, r] using hnEnvelope
    _ = C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
        Real.rpow (Real.log (n : ℝ)) (r : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      exact (Real.rpow_natCast (Real.log (n : ℝ)) r).symm

lemma eventually_sparse_envelope_lt_primeScale (C A : ℝ)
    (hC : 0 ≤ C) (_hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
          Real.rpow (Real.log (n : ℝ)) A <
        (n : ℝ) / (10 * Real.log (n : ℝ)) := by
  let D : ℝ := 20 * (C + 1)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hlittle :
      (fun n : ℕ => Real.rpow (Real.log (n : ℝ)) (A + 1)) =o[atTop]
        (fun n : ℕ => Real.rpow (n : ℝ) (1 / 2 : ℝ)) :=
    (isLittleO_log_rpow_rpow_atTop (A + 1) (by norm_num : (0 : ℝ) < 1 / 2)).natCast_atTop
  have hsmall := hlittle.bound (inv_pos.mpr hD)
  filter_upwards [hsmall, eventually_ge_atTop 3] with n hnsmall hn3
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsmall' :
      Real.rpow (Real.log (n : ℝ)) (A + 1) ≤
        D⁻¹ * Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
    calc
      Real.rpow (Real.log (n : ℝ)) (A + 1) ≤
          ‖Real.rpow (Real.log (n : ℝ)) (A + 1)‖ := Real.le_norm_self _
      _ ≤ D⁻¹ * ‖Real.rpow (n : ℝ) (1 / 2 : ℝ)‖ := hnsmall
      _ = D⁻¹ * Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
        congr 1
        exact Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le (1 / 2 : ℝ))
  have hlogadd :
      Real.rpow (Real.log (n : ℝ)) A * Real.log (n : ℝ) =
        Real.rpow (Real.log (n : ℝ)) (A + 1) := by
    calc
      Real.rpow (Real.log (n : ℝ)) A * Real.log (n : ℝ) =
          Real.rpow (Real.log (n : ℝ)) A *
            Real.rpow (Real.log (n : ℝ)) 1 := by
        exact congrArg (fun z => Real.rpow (Real.log (n : ℝ)) A * z)
          (Real.rpow_one (Real.log (n : ℝ))).symm
      _ = Real.rpow (Real.log (n : ℝ)) (A + 1) :=
        (Real.rpow_add hlogpos A 1).symm
  have hhalf :
      Real.rpow (n : ℝ) (1 / 2 : ℝ) * Real.rpow (n : ℝ) (1 / 2 : ℝ) = n := by
    calc
      Real.rpow (n : ℝ) (1 / 2 : ℝ) * Real.rpow (n : ℝ) (1 / 2 : ℝ) =
          Real.rpow (n : ℝ) ((1 / 2 : ℝ) + 1 / 2) :=
        (Real.rpow_add hnpos (1 / 2 : ℝ) (1 / 2 : ℝ)).symm
      _ = n := by norm_num
  rw [lt_div_iff₀ (mul_pos (by norm_num) hlogpos)]
  calc
    C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
          Real.rpow (Real.log (n : ℝ)) A * (10 * Real.log (n : ℝ)) =
        10 * C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
          (Real.rpow (Real.log (n : ℝ)) A * Real.log (n : ℝ)) := by ring
    _ = 10 * C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
          Real.rpow (Real.log (n : ℝ)) (A + 1) := by rw [hlogadd]
    _ ≤ 10 * C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
          (D⁻¹ * Real.rpow (n : ℝ) (1 / 2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsmall'
        (mul_nonneg (mul_nonneg (by norm_num) hC)
          (Real.rpow_nonneg hnpos.le (1 / 2 : ℝ)))
    _ = (10 * C * D⁻¹) * n := by
      calc
        10 * C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
            (D⁻¹ * Real.rpow (n : ℝ) (1 / 2 : ℝ)) =
            (10 * C * D⁻¹) *
              (Real.rpow (n : ℝ) (1 / 2 : ℝ) *
                Real.rpow (n : ℝ) (1 / 2 : ℝ)) := by ring
        _ = (10 * C * D⁻¹) * n := by rw [hhalf]
    _ < n := by
      have hcoef : 10 * C * D⁻¹ < 1 := by
        calc
          10 * C * D⁻¹ = (10 * C) / D := by rw [div_eq_mul_inv]
          _ < 1 := (div_lt_one hD).2 (by dsimp [D]; nlinarith)
      nlinarith

theorem extensionPrinciple_of_sparseBadPrimes {g : ℕ → ℕ}
    (hsparse : HasSparseBadPrimes g) : ExtensionPrinciple g := by
  classical
  intro s
  obtain ⟨C, A, hC, hA, hbad⟩ := hsparse s
  have henvelope := eventually_sparse_envelope_lt_primeScale C A hC hA
  have hprime := Erdos822.eventually_card_filter_Ioc_prime_half_interval_lower
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 * (s.carrier.sup id + 1) ≤ n :=
    eventually_ge_atTop (2 * (s.carrier.sup id + 1))
  have hall : ∀ᶠ n : ℕ in atTop,
      ((badPrimesInHalfInterval s n).card : ℝ) ≤
          C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
            Real.rpow (Real.log (n : ℝ)) A ∧
      C * Real.rpow (n : ℝ) (1 / 2 : ℝ) *
            Real.rpow (Real.log (n : ℝ)) A <
          (n : ℝ) / (10 * Real.log (n : ℝ)) ∧
      (n : ℝ) / (10 * Real.log (n : ℝ)) ≤
          ((primeHalfInterval n).card : ℝ) ∧
      2 * (s.carrier.sup id + 1) ≤ n := by
    filter_upwards [hbad, henvelope, hprime, hlarge] with n hnBad hnEnvelope hnPrime hnLarge
    exact ⟨hnBad, hnEnvelope, hnPrime, hnLarge⟩
  obtain ⟨n, hnBad, hnEnvelope, hnPrime, hnLarge⟩ := hall.exists
  have hcardReal :
      ((badPrimesInHalfInterval s n).card : ℝ) <
        ((primeHalfInterval n).card : ℝ) :=
    hnBad.trans_lt (hnEnvelope.trans_le hnPrime)
  have hcard : (badPrimesInHalfInterval s n).card < (primeHalfInterval n).card := by
    exact_mod_cast hcardReal
  have hnsubset : ¬primeHalfInterval n ⊆ badPrimesInHalfInterval s n := by
    intro hsub
    exact (not_lt_of_ge (Finset.card_le_card hsub)) hcard
  rw [Finset.not_subset] at hnsubset
  obtain ⟨p, hpCandidate, hpGood⟩ := hnsubset
  have hpData : p ∈ Finset.Ioc (n / 2) n ∧ p.Prime := by
    simpa [primeHalfInterval] using hpCandidate
  have hpSep : SeparatedBy g (↑(insert p s.carrier) : Set ℕ) := by
    by_contra hpNotSep
    apply hpGood
    exact Finset.mem_filter.mpr ⟨hpCandidate, hpNotSep⟩
  have hpFresh : p ∉ s.carrier := by
    intro hpMem
    have hpLe : p ≤ s.carrier.sup id :=
      Finset.le_sup (f := fun x : ℕ => x) hpMem
    have hsupHalf : s.carrier.sup id + 1 ≤ n / 2 := by omega
    have hpLower : n / 2 < p := (Finset.mem_Ioc.mp hpData.1).1
    omega
  exact ⟨p, hpData.2, hpFresh, hpSep⟩

namespace FiniteStage

/-- The empty set is a valid initial stage: its only positive smooth integer is `1`. -/
def empty (g : ℕ → ℕ) : FiniteStage g where
  carrier := ∅
  prime_mem := by simp
  separated := by
    intro a b ha hb hab
    have ha_one : a = 1 := Nat.eq_one_iff_not_exists_prime_dvd.mpr fun p hp hpa => by
      simpa using ha.2 p hp hpa
    have hb_one : b = 1 := Nat.eq_one_iff_not_exists_prime_dvd.mpr fun p hp hpb => by
      simpa using hb.2 p hp hpb
    omega

noncomputable def next {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s : FiniteStage g) : FiniteStage g := by
  let p := Classical.choose (hext s)
  have hp := Classical.choose_spec (hext s)
  exact
    { carrier := insert p s.carrier
      prime_mem := by
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact hp.1
        · exact s.prime_mem hq
      separated := hp.2.2 }

@[simp] lemma next_carrier {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s : FiniteStage g) :
    (next hext s).carrier = insert (Classical.choose (hext s)) s.carrier := by
  rfl

lemma choose_not_mem {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s : FiniteStage g) : Classical.choose (hext s) ∉ s.carrier :=
  (Classical.choose_spec (hext s)).2.1

noncomputable def chain {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) : ℕ → FiniteStage g
  | 0 => s₀
  | n + 1 => next hext (chain hext s₀ n)

@[simp] lemma chain_zero {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) : chain hext s₀ 0 = s₀ := by
  rfl

@[simp] lemma chain_succ {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) (n : ℕ) :
    chain hext s₀ (n + 1) = next hext (chain hext s₀ n) := by
  rfl

lemma carrier_subset_succ {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) (n : ℕ) :
    (chain hext s₀ n).carrier ⊆ (chain hext s₀ (n + 1)).carrier := by
  intro p hp
  simp only [chain_succ, next_carrier, Finset.mem_insert]
  exact Or.inr hp

lemma carrier_mono {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) :
    Monotone fun n => (chain hext s₀ n).carrier :=
  monotone_nat_of_le_succ (carrier_subset_succ hext s₀)

lemma chain_card {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) (n : ℕ) :
    (chain hext s₀ n).carrier.card = s₀.carrier.card + n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [chain_succ, next_carrier,
        Finset.card_insert_of_notMem (choose_not_mem hext (chain hext s₀ n)), ih]
      omega

/-- The union of the increasing finite stages. -/
def limitSet {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) : Set ℕ :=
  {p : ℕ | ∃ n : ℕ, p ∈ (chain hext s₀ n).carrier}

lemma stage_subset_limitSet {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) (n : ℕ) :
    (↑(chain hext s₀ n).carrier : Set ℕ) ⊆ limitSet hext s₀ := by
  intro p hp
  exact ⟨n, hp⟩

lemma limitSet_isPrimeSet {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) : IsPrimeSet (limitSet hext s₀) := by
  intro p hp
  obtain ⟨n, hn⟩ := hp
  exact (chain hext s₀ n).prime_mem hn

lemma limitSet_infinite {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) : (limitSet hext s₀).Infinite := by
  intro hfinite
  let F := hfinite.toFinset
  have hsub (n : ℕ) : (chain hext s₀ n).carrier ⊆ F := by
    intro p hp
    have hp' : p ∈ limitSet hext s₀ := stage_subset_limitSet hext s₀ n hp
    simpa [F] using hp'
  have hcard := Finset.card_le_card (hsub (F.card + 1))
  rw [chain_card] at hcard
  omega

lemma limitSet_separated {g : ℕ → ℕ} (hext : ExtensionPrinciple g)
    (s₀ : FiniteStage g) : SeparatedBy g (limitSet hext s₀) := by
  intro a b ha hb hab
  let support : Finset ℕ := a.primeFactors ∪ b.primeFactors
  have hsupport : (↑support : Set ℕ) ⊆
      ⋃ n : ℕ, (↑(chain hext s₀ n).carrier : Set ℕ) := by
    intro q hq
    change q ∈ support at hq
    rw [Finset.mem_union] at hq
    have hqP : q ∈ limitSet hext s₀ := by
      rcases hq with hqa | hqb
      · have hfac := (Nat.mem_primeFactors.mp hqa)
        exact ha.2 q hfac.1 hfac.2.1
      · have hfac := (Nat.mem_primeFactors.mp hqb)
        exact hb.2 q hfac.1 hfac.2.1
    obtain ⟨n, hn⟩ := hqP
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  obtain ⟨I, hIfinite, hI⟩ :=
    Set.finite_subset_iUnion support.finite_toSet hsupport
  obtain ⟨N, hN⟩ := hIfinite.exists_le
  have hsupportN : support ⊆ (chain hext s₀ N).carrier := by
    intro q hq
    have hq' := hI hq
    simp only [Set.mem_iUnion] at hq'
    obtain ⟨n, hnI, hqn⟩ := hq'
    exact carrier_mono hext s₀ (hN n hnI) hqn
  have haN : IsSmooth (↑(chain hext s₀ N).carrier : Set ℕ) a := by
    refine ⟨ha.1, fun q hqprime hqdiv => ?_⟩
    apply hsupportN
    rw [Finset.mem_union]
    exact Or.inl (Nat.mem_primeFactors.mpr ⟨hqprime, hqdiv, Nat.ne_of_gt ha.1⟩)
  have hbN : IsSmooth (↑(chain hext s₀ N).carrier : Set ℕ) b := by
    refine ⟨hb.1, fun q hqprime hqdiv => ?_⟩
    apply hsupportN
    rw [Finset.mem_union]
    exact Or.inr (Nat.mem_primeFactors.mpr ⟨hqprime, hqdiv, Nat.ne_of_gt hb.1⟩)
  exact (chain hext s₀ N).separated haN hbN hab

end FiniteStage

theorem exists_infinite_separated_of_extension {g : ℕ → ℕ}
    (s₀ : FiniteStage g) (hext : ExtensionPrinciple g) :
    ∃ P : Set ℕ, P.Infinite ∧ IsPrimeSet P ∧ SeparatedBy g P := by
  exact ⟨FiniteStage.limitSet hext s₀, FiniteStage.limitSet_infinite hext s₀,
    FiniteStage.limitSet_isPrimeSet hext s₀, FiniteStage.limitSet_separated hext s₀⟩

lemma pairwiseGapsDiverge_of_separatedBy {g : ℕ → ℕ} {P : Set ℕ}
    (hg : Tendsto g atTop atTop) (hsep : SeparatedBy g P) :
    PairwiseGapsDiverge P := by
  intro K
  have heventually : ∀ᶠ n in atTop, K ≤ g n := (tendsto_atTop.1 hg) K
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  refine ⟨N, ?_⟩
  intro a b ha hb hNa hab
  exact (hN a hNa).trans (hsep ha hb hab)

lemma tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop (K * K)] with n hn
  exact Nat.le_sqrt.mpr hn

lemma prime_mem_smooth {P : Set ℕ} (hP : IsPrimeSet P) {p : ℕ} (hp : p ∈ P) :
    IsSmooth P p := by
  refine ⟨(hP hp).pos, ?_⟩
  intro q hq hqp
  have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq (hP hp)).mp hqp
  simpa [hqp'] using hp

lemma smoothSet_infinite {P : Set ℕ} (hP : P.Infinite) (hprime : IsPrimeSet P) :
    Set.Infinite {n : ℕ | IsSmooth P n} := by
  exact hP.mono fun p hp => prime_mem_smooth hprime hp

/-- The canonical increasing enumeration of the positive smooth integers. -/
noncomputable def smoothEnumeration (P : Set ℕ) : ℕ → ℕ :=
  Nat.nth (IsSmooth P)

lemma smoothEnumeration_spec {P : Set ℕ} (hP : P.Infinite) (hprime : IsPrimeSet P) :
    EnumeratesSmooth P (smoothEnumeration P) := by
  have hinf : Set.Infinite {n : ℕ | IsSmooth P n} := smoothSet_infinite hP hprime
  exact ⟨Nat.nth_strictMono hinf, Nat.range_nth_of_infinite hinf⟩

lemma EnumeratesSmooth.smooth {P : Set ℕ} {a : ℕ → ℕ}
    (ha : EnumeratesSmooth P a) (i : ℕ) : IsSmooth P (a i) := by
  have hi : a i ∈ Set.range a := ⟨i, rfl⟩
  rw [ha.2] at hi
  exact hi

lemma EnumeratesSmooth.tendsto_atTop {P : Set ℕ} {a : ℕ → ℕ}
    (ha : EnumeratesSmooth P a) : Tendsto a atTop atTop :=
  ha.1.tendsto_atTop

theorem hasDivergentGaps_of_pairwise {P : Set ℕ} (hP : P.Infinite)
    (hprime : IsPrimeSet P) (hpair : PairwiseGapsDiverge P) :
    HasDivergentGaps P := by
  let a := smoothEnumeration P
  have ha : EnumeratesSmooth P a := smoothEnumeration_spec hP hprime
  refine ⟨a, ha, tendsto_atTop.2 fun K => ?_⟩
  obtain ⟨N, hN⟩ := hpair K
  filter_upwards [ha.tendsto_atTop.eventually_ge_atTop N] with i hi
  exact hN (ha.smooth i) (ha.smooth (i + 1)) hi (ha.1 (Nat.lt_succ_self i))

/-- Exact proposition asked in Erdős Problem 240. -/
def Problem240 : Prop :=
  ∃ P : Set ℕ, P.Infinite ∧ IsPrimeSet P ∧ HasDivergentGaps P

theorem problem240_of_pairwise
    (h : ∃ P : Set ℕ, P.Infinite ∧ IsPrimeSet P ∧ PairwiseGapsDiverge P) :
    Problem240 := by
  obtain ⟨P, hP, hprime, hpair⟩ := h
  exact ⟨P, hP, hprime, hasDivergentGaps_of_pairwise hP hprime hpair⟩

/-- Once the finite-stage extension theorem is available for the unbounded
lower bound `Nat.sqrt`, the exact statement of Problem 240 follows. -/
theorem problem240_of_sqrt_extension (hext : ExtensionPrinciple Nat.sqrt) :
    Problem240 := by
  obtain ⟨P, hP, hprime, hsep⟩ :=
    exists_infinite_separated_of_extension (FiniteStage.empty Nat.sqrt) hext
  exact problem240_of_pairwise
    ⟨P, hP, hprime, pairwiseGapsDiverge_of_separatedBy tendsto_natSqrt_atTop hsep⟩

/-- Tijdeman's quantitative bad-candidate estimate, together with the proved
prime number theorem, implies the exact statement of Problem 240. -/
theorem problem240_of_sparseBadPrimes
    (hsparse : HasSparseBadPrimes Nat.sqrt) : Problem240 :=
  problem240_of_sqrt_extension (extensionPrinciple_of_sparseBadPrimes hsparse)

/-- The ordinary symmetric Baker--Wüstholz estimate, through the quadratic
logarithmic coordinate interface, already implies the exact statement of
Problem 240. -/
theorem problem240_of_tijdemanSquareLogBounds
    (hBaker : HasTijdemanSquareLogBounds) : Problem240 :=
  problem240_of_sparseBadPrimes
    (sparseBadPrimes_of_tijdemanSquareLogBounds hBaker)

/-- All steps after Baker's uniform exponent estimate are now internal to this
file: tuple counting, prime supply, induction, passage to the infinite union,
and conversion to the literal consecutive-gap limit. -/
theorem problem240_of_tijdemanExponentBounds
    (hBaker : HasTijdemanExponentBounds) : Problem240 :=
  problem240_of_sparseBadPrimes
    (sparseBadPrimes_of_tijdemanExponentBounds hBaker)

/-! ## Final source-independent Baker specialization

The analytic auxiliary-function development deliberately does not import this
module.  Importing its source assembly above and performing the short
project-facing specialization here keeps the dependency graph acyclic: the
eventual unconditional source-component theorem can be applied directly by
`erdos_240` at the end of this file.
-/

/-- The source-independent uniform rational-prime theorem specializes to the
finite-stage Baker--Wüstholz interface used by the counting argument above. -/
theorem hasRationalBakerWustholzBounds_of_uniform
    (h : RationalPrimeBaker.HasUniformRationalPrimeLogBounds.{0}) :
    HasRationalBakerWustholzBounds := by
  intro s
  obtain ⟨K, hK, hbound⟩ :=
    RationalPrimeBaker.finset_bounds_of_uniform h s.carrier
      (fun _q hq ↦ s.prime_mem hq)
  refine ⟨K, hK, ?_⟩
  intro p c d B hp hpFresh hB hc hd hdne hform
  simpa only [RationalPrimeBaker.finsetRationalLogForm,
    rationalLogForm] using
      hbound c d B hp hpFresh hB hc hd hdne hform

/-- The normalized concrete source components imply the full uniform
rational-prime logarithm estimate, with no reference back to the main file. -/
theorem uniformRationalPrimeLogBounds_of_normalizedConcreteSourceComponents
    (hsource :
      BakerSourceAssemblyIndependent.HasNormalizedConcreteSourceComponents.{0}) :
    RationalPrimeBaker.HasUniformRationalPrimeLogBounds.{0} :=
  BakerSourceAssemblyIndependent.uniformBounds_of_normalizedConcreteSourceChains
    (BakerSourceAssemblyIndependent.normalizedConcreteSourceChains_of_components
      hsource)

/-- Project-facing finite-stage Baker bounds obtained from the faithful
normalized source construction. -/
theorem hasRationalBakerWustholzBounds_of_normalizedConcreteSourceComponents
    (hsource :
      BakerSourceAssemblyIndependent.HasNormalizedConcreteSourceComponents.{0}) :
    HasRationalBakerWustholzBounds :=
  hasRationalBakerWustholzBounds_of_uniform
    (uniformRationalPrimeLogBounds_of_normalizedConcreteSourceComponents hsource)

/-- The exact Erdős-240 proposition follows from the normalized concrete
source construction.  Once that construction is closed unconditionally, the
final theorem `erdos_240` is the one-line application of this result. -/
theorem problem240_of_normalizedConcreteSourceComponents
    (hsource :
      BakerSourceAssemblyIndependent.HasNormalizedConcreteSourceComponents.{0}) :
    Problem240 :=
  problem240_of_tijdemanSquareLogBounds
    (HasRationalBakerWustholzBounds.toSquareLogBounds
      (hasRationalBakerWustholzBounds_of_normalizedConcreteSourceComponents
        hsource))

/-- Erdős Problem 240: there is an infinite set of primes whose positive
smooth numbers, in increasing order, have consecutive gaps tending to
infinity. -/
theorem erdos_240 :
    ∃ P : Set ℕ,
      P.Infinite ∧ Erdos240.IsPrimeSet P ∧ Erdos240.HasDivergentGaps P :=
  problem240_of_normalizedConcreteSourceComponents
    BakerSourceFinalAssemblyIndependent.hasNormalizedConcreteSourceComponents

end Erdos240

#print axioms Erdos240.problem240_of_tijdemanExponentBounds
#print axioms Erdos240.hasRationalBakerWustholzBounds_of_uniform
#print axioms Erdos240.problem240_of_normalizedConcreteSourceComponents
#print axioms Erdos240.erdos_240

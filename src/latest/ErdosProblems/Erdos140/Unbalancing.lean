import APAP.Physics.Unbalancing
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The Kelley--Meka unbalancing lemma

This file proves the finite, power-moment form of the unbalancing step.  Keeping
the statement in power-moment form has two advantages: all exponents are
natural numbers, and no convention at exponent zero is hidden in an `L^p`
notation.  Taking the positive `p'`-th root gives the usual weighted `L^p`
form immediately.
-/

open Finset Function
open scoped BigOperators NNReal

namespace Erdos140

section Moments

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The `k`-th moment of `f` with respect to the (not necessarily normalized)
weight `ν`. -/
def weightedMoment (ν f : X → ℝ) (k : ℕ) : ℝ :=
  ∑ x : X, ν x * f x ^ k

/-- The absolute `k`-th moment. -/
def weightedAbsMoment (ν f : X → ℝ) (k : ℕ) : ℝ :=
  ∑ x : X, ν x * |f x| ^ k

theorem weightedAbsMoment_nonneg {ν f : X → ℝ} (hν : ∀ x, 0 ≤ ν x) (k : ℕ) :
    0 ≤ weightedAbsMoment ν f k := by
  exact sum_nonneg fun x _ ↦ mul_nonneg (hν x) (pow_nonneg (abs_nonneg _) _)

theorem weightedMoment_even_eq_abs {ν f : X → ℝ} {k : ℕ} (hk : Even k) :
    weightedMoment ν f k = weightedAbsMoment ν f k := by
  unfold weightedMoment weightedAbsMoment
  apply sum_congr rfl
  intro x _
  congr 1
  exact (hk.pow_abs (f x)).symm

/-- A convenient explicit multiplier.  The very generous constant `60` lets
Bernoulli's inequality replace the logarithm in the customary proof. -/
noncomputable def unbalancingMultiplier (ε : ℝ) : ℕ :=
  Nat.ceil (60 / ε ^ 2)

/-- The even exponent used in the small-moment branch of unbalancing. -/
noncomputable def unbalancingExponent (ε : ℝ) (p : ℕ) : ℕ :=
  2 * p * unbalancingMultiplier ε

theorem unbalancingMultiplier_pos {ε : ℝ} (hε : 0 < ε) :
    0 < unbalancingMultiplier ε := by
  rw [unbalancingMultiplier, Nat.ceil_pos]
  positivity

theorem unbalancingExponent_even (ε : ℝ) (p : ℕ) :
    Even (unbalancingExponent ε p) := by
  refine ⟨p * unbalancingMultiplier ε, ?_⟩
  simp [unbalancingExponent, two_mul, add_mul]

theorem unbalancingExponent_pos {ε : ℝ} {p : ℕ} (hε : 0 < ε) (hp : p ≠ 0) :
    0 < unbalancingExponent ε p := by
  simp [unbalancingExponent, unbalancingMultiplier_pos hε, Nat.pos_of_ne_zero hp]

theorem unbalancingMultiplier_spec {ε : ℝ} (hε : 0 < ε) :
    60 / ε ^ 2 ≤ unbalancingMultiplier ε := by
  simpa [unbalancingMultiplier] using Nat.le_ceil (60 / ε ^ 2)

private theorem add_pow_le_two_pow_mul_add_pow {a b : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 1 ≤ n) :
    (a + b) ^ n ≤ 2 ^ (n - 1) * (a ^ n + b ^ n) := by
  let a' : ℝ≥0 := ⟨a, ha⟩
  let b' : ℝ≥0 := ⟨b, hb⟩
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow a' b'
    (p := (n : ℝ)) (by exact_mod_cast hn)
  exact_mod_cast h

/-- **Unbalancing, power-moment form.**  If all moments of `f` against a
probability weight are nonnegative and the `p`-th absolute moment is at least
`ε^p`, then at some explicitly bounded even exponent the absolute moment of
`1 + f` is at least `(1 + ε/2)^p'`.

The hypotheses `Odd p` and `5 ≤ p` are the standard intermediate form.  An
arbitrary positive input exponent is replaced by `2 * p + 3` before applying
this lemma. -/
theorem unbalancing_of_nonnegative_moments
    {ν f : X → ℝ} {ε : ℝ} {p : ℕ}
    (hν : ∀ x, 0 ≤ ν x) (hνmass : ∑ x : X, ν x = 1)
    (hmom : ∀ k : ℕ, 0 ≤ weightedMoment ν f k)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hp : 5 ≤ p) (hpodd : Odd p)
    (hlarge : ε ^ p ≤ weightedAbsMoment ν f p) :
    ∃ p' : ℕ, 0 < p' ∧ Even p' ∧ p' ≤ unbalancingExponent ε p ∧
      (1 + ε / 2) ^ p' ≤ weightedAbsMoment ν (f + 1) p' := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
  have hpm1even : Even (p - 1) := Nat.Odd.sub_odd hpodd odd_one
  have hpositive :
      ε ^ p ≤ 2 * ∑ i : X, ν i * ((f ^ (p - 1)) i * (f i)⁺) := by
    calc
      ε ^ p ≤ weightedAbsMoment ν f p := hlarge
      _ = ∑ i : X, ν i * ((f ^ (p - 1)) i * |f i|) := by
        unfold weightedAbsMoment
        apply sum_congr rfl
        intro i _
        congr 1
        change |f i| ^ p = f i ^ (p - 1) * |f i|
        rw [← abs_of_nonneg (hpm1even.pow_nonneg (f i)), abs_pow,
          pow_sub_one_mul hp0]
      _ ≤ weightedMoment ν f p +
          ∑ i : X, ν i * ((f ^ (p - 1)) i * |f i|) :=
        le_add_of_nonneg_left (hmom p)
      _ = ∑ i : X, ν i * ((f ^ (p - 1)) i * (f i + |f i|)) := by
        simp [weightedMoment, mul_add, sum_add_distrib, pow_sub_one_mul hp0]
      _ = ∑ i : X, ν i * ((f ^ (p - 1)) i * (2 • (f i)⁺)) := by
        simp [add_abs_eq_two_nsmul_posPart]
      _ = 2 * ∑ i : X, ν i * ((f ^ (p - 1)) i * (f i)⁺) := by
        simp [mul_sum]
        ring_nf
  let P : Finset X := Finset.univ.filter fun i ↦ 0 ≤ f i
  let T : Finset X := Finset.univ.filter fun i ↦ 3 / 4 * ε ≤ f i
  have hTP : T ⊆ P := by
    intro i hi
    simp only [P, T, mem_filter, mem_univ, true_and] at hi ⊢
    exact le_trans (by positivity) hi
  have hP :
      (2 : ℝ)⁻¹ * ε ^ p ≤ ∑ i ∈ P, ν i * (f ^ p) i := by
    rw [inv_mul_le_iff₀ (by norm_num : (0 : ℝ) < 2), sum_filter]
    simpa [P, Pi.posPart_apply, posPart_eq_ite, pow_sub_one_mul hp0] using hpositive
  have hlow :
      ∑ i ∈ P \ T, ν i * (f ^ p) i ≤ (4 : ℝ)⁻¹ * ε ^ p := by
    calc
      _ ≤ ∑ i ∈ P \ T, ν i * (3 / 4 * ε) ^ p := by
        apply sum_le_sum
        intro i hi
        have hi' := hi
        simp only [mem_sdiff, P, T, mem_filter, mem_univ, true_and, not_le] at hi'
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hi'.1 hi'.2.le p) (hν i)
      _ = (3 / 4) ^ p * ε ^ p * ∑ i ∈ P \ T, ν i := by
        rw [← sum_mul]
        simp [mul_pow]
        ring
      _ ≤ (4 : ℝ)⁻¹ * ε ^ p * ∑ i : X, ν i := by
        have hpow : (3 / 4 : ℝ) ^ p ≤ (4 : ℝ)⁻¹ := by
          calc
            (3 / 4 : ℝ) ^ p ≤ (3 / 4 : ℝ) ^ 5 := by
              exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
            _ ≤ (4 : ℝ)⁻¹ := by norm_num
        calc
          (3 / 4) ^ p * ε ^ p * ∑ i ∈ P \ T, ν i ≤
              (4 : ℝ)⁻¹ * ε ^ p * ∑ i ∈ P \ T, ν i :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpow (pow_nonneg hε₀.le p))
              (sum_nonneg fun i _ ↦ hν i)
          _ ≤ (4 : ℝ)⁻¹ * ε ^ p * ∑ i : X, ν i :=
            mul_le_mul_of_nonneg_left
              (sum_le_univ_sum_of_nonneg fun i ↦ hν i)
              (mul_nonneg (by norm_num) (pow_nonneg hε₀.le p))
      _ = (4 : ℝ)⁻¹ * ε ^ p := by rw [hνmass, mul_one]
  have hTmoment :
      (4 : ℝ)⁻¹ * ε ^ p ≤ ∑ i ∈ T, ν i * (f ^ p) i := by
    calc
      (4 : ℝ)⁻¹ * ε ^ p =
          (2 : ℝ)⁻¹ * ε ^ p - (4 : ℝ)⁻¹ * ε ^ p := by ring
      _ ≤ (∑ i ∈ P, ν i * (f ^ p) i) -
          ∑ i ∈ P \ T, ν i * (f ^ p) i := sub_le_sub hP hlow
      _ = ∑ i ∈ T, ν i * (f ^ p) i := by
        rw [sum_sdiff_eq_sub hTP]
        ring
  have hTmoment_nonneg : 0 ≤ ∑ i ∈ T, ν i * (f ^ p) i :=
    (mul_nonneg (by norm_num) (pow_nonneg hε₀.le p)).trans hTmoment
  have hCS :
      (∑ i ∈ T, ν i * (f ^ p) i) ^ 2 ≤
        (∑ i ∈ T, ν i) * ∑ i ∈ T, ν i * (f ^ (2 * p)) i := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul T
    · intro i _
      exact hν i
    · intro i _
      exact mul_nonneg (hν i) ((even_two_mul p).pow_nonneg (f i))
    · intro i _
      dsimp
      rw [show 2 * p = p * 2 by omega, pow_mul, mul_pow]
      ring_nf
      exact le_rfl
  have hCSabs :
      ((4 : ℝ)⁻¹ * ε ^ p) ^ 2 ≤
        (∑ i ∈ T, ν i) * weightedAbsMoment ν f (2 * p) := by
    calc
      _ ≤ (∑ i ∈ T, ν i * (f ^ p) i) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by norm_num) (pow_nonneg hε₀.le p)) hTmoment 2
      _ ≤ (∑ i ∈ T, ν i) * ∑ i ∈ T, ν i * (f ^ (2 * p)) i := hCS
      _ ≤ (∑ i ∈ T, ν i) * weightedAbsMoment ν f (2 * p) := by
        apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun i _ ↦ hν i)
        unfold weightedAbsMoment
        have heq :
            (∑ i ∈ T, ν i * (f ^ (2 * p)) i) =
              ∑ i ∈ T, ν i * |f i| ^ (2 * p) := by
          apply sum_congr rfl
          intro i _
          simp only [Pi.pow_apply]
          rw [(even_two_mul p).pow_abs]
        rw [heq]
        apply sum_le_sum_of_subset_of_nonneg (subset_univ T)
        intro i _ _
        exact mul_nonneg (hν i) (pow_nonneg (abs_nonneg _) _)
  let q : ℕ := 2 * p
  by_cases hbig : (2 : ℝ) ^ q ≤ weightedAbsMoment ν (f + 1) q
  · refine ⟨q, by dsimp [q]; omega, even_two_mul p, ?_, ?_⟩
    · dsimp [q, unbalancingExponent]
      exact Nat.le_mul_of_pos_right _ (unbalancingMultiplier_pos hε₀)
    · exact (pow_le_pow_left₀ (by positivity) (by linarith) q).trans hbig
  · have hsmall : weightedAbsMoment ν (f + 1) q < (2 : ℝ) ^ q := lt_of_not_ge hbig
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hfq : weightedAbsMoment ν f q ≤ (2 : ℝ) ^ (2 * q) := by
      calc
        weightedAbsMoment ν f q ≤
            (2 : ℝ) ^ (q - 1) * (weightedAbsMoment ν (f + 1) q + 1) := by
          unfold weightedAbsMoment
          calc
            (∑ x : X, ν x * |f x| ^ q) ≤
                ∑ x : X, ν x *
                  ((2 : ℝ) ^ (q - 1) * (|f x + 1| ^ q + 1 ^ q)) := by
              apply sum_le_sum
              intro i _
              apply mul_le_mul_of_nonneg_left _ (hν i)
              calc
                |f i| ^ q ≤ (|f i + 1| + 1) ^ q := by
                  apply pow_le_pow_left₀ (abs_nonneg _) _ q
                  calc
                    |f i| = |(f i + 1) - 1| := by ring_nf
                    _ ≤ |f i + 1| + |(1 : ℝ)| := abs_sub _ _
                    _ = |f i + 1| + 1 := by norm_num
                _ ≤ (2 : ℝ) ^ (q - 1) * (|f i + 1| ^ q + 1 ^ q) :=
                  add_pow_le_two_pow_mul_add_pow (abs_nonneg _) (by norm_num) hq
            _ = (2 : ℝ) ^ (q - 1) *
                (∑ x : X, ν x * |(f + 1) x| ^ q + 1) := by
              simp only [Pi.add_apply, Pi.one_apply, one_pow]
              calc
                (∑ x : X, ν x * (2 ^ (q - 1) * (|f x + 1| ^ q + 1))) =
                    2 ^ (q - 1) * (∑ x : X, ν x * |f x + 1| ^ q) +
                      2 ^ (q - 1) * ∑ x : X, ν x := by
                  simp_rw [mul_add]
                  rw [sum_add_distrib]
                  congr 1
                  · rw [mul_sum]
                    apply sum_congr rfl
                    intro i _
                    ring
                  · rw [mul_sum]
                    apply sum_congr rfl
                    intro i _
                    ring
                _ = 2 ^ (q - 1) * ((∑ x : X, ν x * |f x + 1| ^ q) + 1) := by
                  rw [hνmass]
                  ring
        _ ≤ (2 : ℝ) ^ (q - 1) * ((2 : ℝ) ^ q + 1) := by
          gcongr
        _ ≤ (2 : ℝ) ^ (q - 1) * (2 : ℝ) ^ (q + 1) := by
          gcongr
          calc
            (2 : ℝ) ^ q + 1 ≤ (2 : ℝ) ^ q + (2 : ℝ) ^ q := by
              gcongr
              exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
            _ = (2 : ℝ) ^ (q + 1) := by rw [pow_succ]; ring
        _ = (2 : ℝ) ^ (2 * q) := by rw [← pow_add]; congr 1; omega
    have hmassT : (ε / 8) ^ (2 * p) ≤ ∑ i ∈ T, ν i := by
      have hfq' : weightedAbsMoment ν f (2 * p) ≤ (2 : ℝ) ^ (4 * p) := by
        convert hfq using 1 <;> simp [q] <;> omega
      have hcs' :
          ((4 : ℝ)⁻¹ * ε ^ p) ^ 2 ≤
            (∑ i ∈ T, ν i) * (2 : ℝ) ^ (4 * p) :=
        hCSabs.trans (mul_le_mul_of_nonneg_left hfq' (sum_nonneg fun i _ ↦ hν i))
      have hden : (16 : ℝ) * (2 : ℝ) ^ (4 * p) ≤ (8 : ℝ) ^ (2 * p) := by
        have h16 : (16 : ℝ) ≤ 4 ^ p := by
          calc
            (16 : ℝ) = 4 ^ 2 := by norm_num
            _ ≤ 4 ^ p := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)
        rw [show (2 : ℝ) ^ (4 * p) = 16 ^ p by rw [pow_mul]; norm_num,
          show (8 : ℝ) ^ (2 * p) = 64 ^ p by rw [pow_mul]; norm_num]
        calc
          (16 : ℝ) * 16 ^ p ≤ 4 ^ p * 16 ^ p :=
            mul_le_mul_of_nonneg_right h16 (pow_nonneg (by norm_num) p)
          _ = 64 ^ p := by rw [← mul_pow]; norm_num
      rw [div_pow]
      apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 8) (2 * p))).2
      have hscaled := mul_le_mul_of_nonneg_left hcs' (by norm_num : (0 : ℝ) ≤ 16)
      calc
        ε ^ (2 * p) = 16 * ((4 : ℝ)⁻¹ * ε ^ p) ^ 2 := by
          rw [show 2 * p = p + p by omega, pow_add, pow_two]
          ring
        _ ≤ 16 * ((∑ i ∈ T, ν i) * (2 : ℝ) ^ (4 * p)) := hscaled
        _ = (∑ i ∈ T, ν i) * (16 * (2 : ℝ) ^ (4 * p)) := by ring
        _ ≤ (∑ i ∈ T, ν i) * (8 : ℝ) ^ (2 * p) :=
          mul_le_mul_of_nonneg_left hden (sum_nonneg fun i _ ↦ hν i)
    let m : ℕ := unbalancingMultiplier ε
    have hmpos : 0 < m := unbalancingMultiplier_pos hε₀
    have hm_spec : 60 / ε ^ 2 ≤ (m : ℝ) := by
      simpa [m] using unbalancingMultiplier_spec hε₀
    have hratio :
        1 + ε / 6 ≤ (1 + 3 * ε / 4) / (1 + ε / 2) := by
      apply (le_div_iff₀ (by positivity : 0 < 1 + ε / 2)).2
      nlinarith
    have hratio_pow :
        8 / ε ≤ ((1 + 3 * ε / 4) / (1 + ε / 2)) ^ m := by
      calc
        8 / ε ≤ 1 + (m : ℝ) * (ε / 6) := by
          have := mul_le_mul_of_nonneg_right hm_spec (by positivity : 0 ≤ ε / 6)
          field_simp at this ⊢
          nlinarith [sq_pos_of_pos hε₀]
        _ ≤ (1 + ε / 6) ^ m := one_add_mul_le_pow (by linarith) m
        _ ≤ ((1 + 3 * ε / 4) / (1 + ε / 2)) ^ m :=
          pow_le_pow_left₀ (by positivity) hratio m
    have hratio_mul :
        (1 + ε / 2) ^ m ≤ (ε / 8) * (1 + 3 * ε / 4) ^ m := by
      have hdenpos : 0 < (1 + ε / 2) ^ m := pow_pos (by positivity) m
      rw [div_pow] at hratio_pow
      have hcross := (le_div_iff₀ hdenpos).1 hratio_pow
      calc
        (1 + ε / 2) ^ m =
            (ε / 8) * ((8 / ε) * (1 + ε / 2) ^ m) := by field_simp
        _ ≤ (ε / 8) * (1 + 3 * ε / 4) ^ m :=
          mul_le_mul_of_nonneg_left hcross (by positivity)
    have hpower :
        (1 + ε / 2) ^ (2 * p * m) ≤
          (ε / 8) ^ (2 * p) * (1 + 3 * ε / 4) ^ (2 * p * m) := by
      calc
        (1 + ε / 2) ^ (2 * p * m) = ((1 + ε / 2) ^ m) ^ (2 * p) := by
          rw [← pow_mul, Nat.mul_comm m (2 * p)]
        _ ≤ ((ε / 8) * (1 + 3 * ε / 4) ^ m) ^ (2 * p) :=
          pow_le_pow_left₀ (by positivity) hratio_mul (2 * p)
        _ = (ε / 8) ^ (2 * p) * (1 + 3 * ε / 4) ^ (2 * p * m) := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm m (2 * p)]
    have heven : Even (2 * p * m) := by
      simpa [Nat.mul_assoc] using even_two_mul (p * m)
    refine ⟨2 * p * m, by positivity, heven, ?_, ?_⟩
    · simp [unbalancingExponent, m]
    · calc
        (1 + ε / 2) ^ (2 * p * m) ≤
            (ε / 8) ^ (2 * p) * (1 + 3 * ε / 4) ^ (2 * p * m) := hpower
        _ ≤ (∑ i ∈ T, ν i) * (1 + 3 * ε / 4) ^ (2 * p * m) :=
          mul_le_mul_of_nonneg_right hmassT (pow_nonneg (by positivity) _)
        _ = ∑ i ∈ T, ν i * (1 + 3 * ε / 4) ^ (2 * p * m) := by
          rw [← sum_mul]
        _ ≤ ∑ i ∈ T, ν i * |(f + 1) i| ^ (2 * p * m) := by
          apply sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left _ (hν i)
          apply pow_le_pow_left₀ (by positivity) _ _
          have hi' : 3 / 4 * ε ≤ f i := by simpa [T] using hi
          have hf1 : 0 ≤ (f + 1) i := by
            simp only [Pi.add_apply, Pi.one_apply]
            nlinarith
          rw [abs_of_nonneg hf1]
          simp only [Pi.add_apply, Pi.one_apply]
          nlinarith
        _ ≤ weightedAbsMoment ν (f + 1) (2 * p * m) := by
          unfold weightedAbsMoment
          apply sum_le_sum_of_subset_of_nonneg (subset_univ T)
          intro i _ _
          exact mul_nonneg (hν i) (pow_nonneg (abs_nonneg _) _)
          

end Moments

section PhysicalUnbalancing

open Fintype MeasureTheory RCLike Real
open scoped ComplexConjugate ComplexOrder ENNReal mu

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- Physical-space positivity of every moment.  This is Bloom--Sisask Lemma 7:
autocorrelation representations of both the function and the weight turn the
moment into a finite sum of complex squared norms. -/
theorem physical_pow_inner_nonneg {ν : G → ℝ≥0} {f : G → ℝ} {g h : G → ℂ}
    (hf : g ○ᵈ g = (↑) ∘ f) (hν : h ○ᵈ h = (↑) ∘ ν) (k : ℕ) :
    (0 : ℝ) ≤ ⟪(↑) ∘ ν, f ^ k⟫_[ℝ] :=
  _root_.pow_inner_nonneg hf hν k

/-- Weighted physical unbalancing for an arbitrary probability weight having
an autocorrelation representation.  This is the form used after restricting
to a pair of Bohr sets. -/
theorem physical_weighted_unbalancing (p : ℕ) (hp : p ≠ 0) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (ν : G → ℝ≥0)
    (f : G → ℝ) (g h : G → ℂ)
    (hf : g ○ᵈ g = (↑) ∘ f) (hν : h ○ᵈ h = (↑) ∘ ν)
    (hνmass : ∑ x : G, ν x = 1) (hε : ε ≤ ‖f‖_[p, ν]) :
    ∃ p' : ℕ, 0 < p' ∧ p' ≤ 2 ^ 10 * ε⁻¹ ^ 2 * p ∧
      1 + ε / 2 ≤ ‖f + 1‖_[p', ν] := by
  obtain ⟨p', hp'bound, hp'large⟩ :=
    _root_.unbalancing' p hp ε hε₀ hε₁ ν f g h hf hν hνmass hε
  refine ⟨p', ?_, hp'bound, hp'large⟩
  rw [Nat.pos_iff_ne_zero]
  intro hp'zero
  subst p'
  simp at hp'large
  linarith

/-- The standard weighted-`L^p` form of the physical unbalancing lemma
(Bloom--Sisask Lemma 8), re-exported in the Erdős 140 namespace.  The output
exponent is a natural number and has the explicit bound
`2^10 * ε⁻² * p`. -/
theorem physical_unbalancing (p : ℕ) (hp : p ≠ 0) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (f : G → ℝ) (g h : G → ℂ)
    (hf : g ○ᵈ g = (↑) ∘ f) (hh : h ○ᵈ h = μ univ)
    (hε : ε ≤ ‖f‖_[p, μ univ]) :
    ∃ p' : ℕ, 0 < p' ∧ p' ≤ 2 ^ 10 * ε⁻¹ ^ 2 * p ∧
      1 + ε / 2 ≤ ‖f + 1‖_[p', μ univ] := by
  obtain ⟨p', hp'bound, hp'large⟩ :=
    _root_.unbalancing p hp ε hε₀ hε₁ f g h hf hh hε
  refine ⟨p', ?_, hp'bound, hp'large⟩
  rw [Nat.pos_iff_ne_zero]
  intro hp'zero
  subst p'
  simp at hp'large
  linarith

end PhysicalUnbalancing

end Erdos140

#print axioms Erdos140.unbalancing_of_nonnegative_moments
#print axioms Erdos140.physical_pow_inner_nonneg
#print axioms Erdos140.physical_weighted_unbalancing
#print axioms Erdos140.physical_unbalancing

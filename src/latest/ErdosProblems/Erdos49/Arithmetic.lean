import ErdosProblems.Erdos49.Fibre

/-!
# Arithmetic comparison lemmas for Erdős Problem 49

The primary part of Tao's argument orders integers `d * p` first by the
reduced rational number `φ(d) / d`.  The key finite fact is that two distinct
ratios coming from denominators at most `D` are separated by at least
`1 / D²`.  This file also records the exact totient formula after adjoining a
new prime factor.
-/

namespace Erdos49

open scoped BigOperators

/-- The rational totient ratio used to label primary fibres. -/
def totientRatio (d : ℕ) : ℚ := (d.totient : ℚ) / (d : ℚ)

lemma totientRatio_nonneg (d : ℕ) : 0 ≤ totientRatio d := by
  unfold totientRatio
  positivity

lemma totientRatio_pos {d : ℕ} (hd : 0 < d) : 0 < totientRatio d := by
  unfold totientRatio
  exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hd) (by exact_mod_cast hd)

lemma totientRatio_le_one (d : ℕ) : totientRatio d ≤ 1 := by
  unfold totientRatio
  by_cases hd : d = 0
  · simp [hd]
  · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hd)).2
      (by exact_mod_cast Nat.totient_le d)

/-- Two different totient ratios with positive denominators at most `D` are
separated by at least `1 / D²`.  No reduction-to-lowest-terms API is needed:
cross multiplication gives a positive integer numerator directly. -/
lemma one_div_sq_le_totientRatio_sub {D d e : ℕ}
    (hD : 0 < D) (hd : 0 < d) (he : 0 < e)
    (hdD : d ≤ D) (heD : e ≤ D)
    (hde : totientRatio d < totientRatio e) :
    (1 : ℚ) / (D : ℚ) ^ 2 ≤ totientRatio e - totientRatio d := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have heq : (0 : ℚ) < e := by exact_mod_cast he
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hcross : (d.totient : ℚ) * e < (e.totient : ℚ) * d := by
    unfold totientRatio at hde
    rw [div_lt_div_iff₀ hdq heq] at hde
    simpa [mul_comm] using hde
  have hcrossNat : d.totient * e < e.totient * d := by
    exact_mod_cast hcross
  have honeNat : 1 ≤ e.totient * d - d.totient * e :=
    Nat.sub_pos_of_lt hcrossNat
  have hone : (1 : ℚ) ≤ ((e.totient * d - d.totient * e : ℕ) : ℚ) := by
    exact_mod_cast honeNat
  have hden : (d : ℚ) * e ≤ (D : ℚ) ^ 2 := by
    norm_cast
    simpa [pow_two] using Nat.mul_le_mul hdD heD
  calc
    (1 : ℚ) / (D : ℚ) ^ 2 ≤
        (1 : ℚ) / ((d : ℚ) * e) := by
      exact one_div_le_one_div_of_le (mul_pos hdq heq) hden
    _ ≤ (((e.totient * d : ℕ) - d.totient * e : ℕ) : ℚ) /
        ((d : ℚ) * e) := by
      exact div_le_div_of_nonneg_right hone (mul_nonneg hdq.le heq.le)
    _ = totientRatio e - totientRatio d := by
      unfold totientRatio
      rw [Nat.cast_sub (Nat.le_of_lt hcrossNat)]
      push_cast
      field_simp

/-- A prime not dividing `d` is coprime to `d`. -/
lemma coprime_prime_of_not_dvd {d p : ℕ} (hp : p.Prime) (hpd : ¬p ∣ d) :
    d.Coprime p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  exact hpd

/-- Exact totient formula after adjoining a new prime factor. -/
lemma totient_mul_prime {d p : ℕ} (hp : p.Prime) (hpd : ¬p ∣ d) :
    Nat.totient (d * p) = Nat.totient d * (p - 1) := by
  rw [Nat.totient_mul (coprime_prime_of_not_dvd hp hpd), Nat.totient_prime hp]

/-- Real form of the primary identity
`φ(dp) = (φ(d)/d) * (1 - 1/p) * dp`. -/
lemma totient_mul_prime_real {d p : ℕ} (hd : 0 < d)
    (hp : p.Prime) (hpd : ¬p ∣ d) :
    (Nat.totient (d * p) : ℝ) =
      ((Nat.totient d : ℝ) / d) * (1 - 1 / (p : ℝ)) * (d * p : ℕ) := by
  rw [totient_mul_prime hp hpd]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  push_cast
  rw [Nat.cast_sub hp.one_le]
  field_simp [hd0, hp0]
  ring

/-- The rational and real versions of the totient ratio agree. -/
lemma cast_totientRatio (d : ℕ) :
    ((totientRatio d : ℚ) : ℝ) = (Nat.totient d : ℝ) / d := by
  simp [totientRatio]

/-- Quantitative ordering lemma for the primary fibres.  Two products `d*p`
and `e*q` lying in the same short interval inherit the strict order of their
distinct totient-ratio labels.  The constants are deliberately generous;
only their absoluteness matters in the asymptotic argument. -/
lemma primary_totient_lt_of_ratio_lt
    {D d e p q : ℕ} {B H : ℝ}
    (hD : 1 ≤ D) (hd : 0 < d) (he : 0 < e)
    (hdD : d ≤ D) (heD : e ≤ D)
    (hp : p.Prime) (hq : q.Prime) (hpd : ¬p ∣ d) (hqe : ¬q ∣ e)
    (hratio : totientRatio d < totientRatio e)
    (hB : 0 < B) (hH : 0 ≤ H)
    (hshort : H ≤ B / (4 * (D : ℝ) ^ 2))
    (hnlow : B ≤ (d * p : ℕ)) (hnhigh : (d * p : ℕ) ≤ B + H)
    (hmlow : B ≤ (e * q : ℕ)) (hmhigh : (e * q : ℕ) ≤ B + H)
    (hpLarge : 8 * D ^ 2 ≤ p) (hqLarge : 8 * D ^ 2 ≤ q) :
    Nat.totient (d * p) < Nat.totient (e * q) := by
  let rd : ℝ := (Nat.totient d : ℝ) / d
  let re : ℝ := (Nat.totient e : ℝ) / e
  let den : ℝ := (D : ℝ) ^ 2
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hden : 0 < den := by dsimp only [den]; positivity
  have hgapQ := one_div_sq_le_totientRatio_sub
    (D := D) (d := d) (e := e) (by omega) hd he hdD heD hratio
  have hgap : (1 : ℝ) / den ≤ re - rd := by
    simpa [den, rd, re, cast_totientRatio] using
      ((Rat.cast_le (K := ℝ)).2 hgapQ)
  have hrd0 : 0 ≤ rd := by dsimp only [rd]; positivity
  have hre0 : 0 ≤ re := by dsimp only [re]; positivity
  have hrd1 : rd ≤ 1 := by
    dsimp only [rd]
    exact (div_le_one (by exact_mod_cast hd)).2 (by exact_mod_cast Nat.totient_le d)
  have hre1 : re ≤ 1 := by
    dsimp only [re]
    exact (div_le_one (by exact_mod_cast he)).2 (by exact_mod_cast Nat.totient_le e)
  have hfourDen : 1 ≤ 4 * den := by
    dsimp only [den]
    have hDone : (1 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith [sq_nonneg ((D : ℝ) - 1)]
  have hHleB : H ≤ B :=
    hshort.trans (div_le_self hB.le hfourDen)
  have hnTwo : ((d * p : ℕ) : ℝ) ≤ 2 * B := by
    push_cast at hnhigh ⊢
    linarith
  have hmTwo : ((e * q : ℕ) : ℝ) ≤ 2 * B := by
    push_cast at hmhigh ⊢
    linarith
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpLargeR : 8 * den ≤ (p : ℝ) := by
    dsimp only [den]
    exact_mod_cast hpLarge
  have hqLargeR : 8 * den ≤ (q : ℝ) := by
    dsimp only [den]
    exact_mod_cast hqLarge
  have hmq : ((e * q : ℕ) : ℝ) / (q : ℝ) ≤ B / (4 * den) := by
    apply (div_le_div_iff₀ hqPos (mul_pos (by norm_num) hden)).2
    calc
      ((e * q : ℕ) : ℝ) * (4 * den) ≤ (2 * B) * (4 * den) :=
        mul_le_mul_of_nonneg_right hmTwo (by positivity)
      _ = B * (8 * den) := by ring
      _ ≤ B * q := mul_le_mul_of_nonneg_left hqLargeR hB.le
  have hupper :
      rd * (1 - 1 / (p : ℝ)) * ((d * p : ℕ) : ℝ) ≤
        rd * B + B / (4 * den) := by
    have hfactor : 1 - 1 / (p : ℝ) ≤ 1 :=
      sub_le_self _ (one_div_nonneg.mpr hpPos.le)
    have hfactor0 : 0 ≤ 1 - 1 / (p : ℝ) := by
      have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
      exact sub_nonneg.mpr ((one_div_le hpPos zero_lt_one).2 (by simpa using hpOne))
    calc
      rd * (1 - 1 / (p : ℝ)) * ((d * p : ℕ) : ℝ) ≤
          rd * ((d * p : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_left hfactor hrd0
        exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using this)
          (Nat.cast_nonneg _)
      _ ≤ rd * (B + H) := mul_le_mul_of_nonneg_left hnhigh hrd0
      _ = rd * B + rd * H := by ring
      _ ≤ rd * B + H := add_le_add le_rfl
        (mul_le_of_le_one_left hH hrd1)
      _ ≤ rd * B + B / (4 * den) := by
        exact add_le_add le_rfl hshort
  have hlower :
      rd * B + 3 * (B / (4 * den)) ≤
        re * (1 - 1 / (q : ℝ)) * ((e * q : ℕ) : ℝ) := by
    have hgapB : rd * B + B / den ≤ re * B := by
      have := mul_le_mul_of_nonneg_right hgap hB.le
      calc
        rd * B + B / den = rd * B + (1 / den) * B := by ring
        _ ≤ rd * B + (re - rd) * B := add_le_add le_rfl this
        _ = re * B := by ring
    have hreMq : re * (((e * q : ℕ) : ℝ) / (q : ℝ)) ≤ B / (4 * den) :=
      (mul_le_of_le_one_left
        (div_nonneg (Nat.cast_nonneg _) hqPos.le) hre1).trans hmq
    have hreB : re * B ≤ re * ((e * q : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hmlow hre0
    calc
      rd * B + 3 * (B / (4 * den)) ≤ re * B - B / (4 * den) := by
        calc
          rd * B + 3 * (B / (4 * den)) = rd * B + B / den - B / (4 * den) := by
            field_simp [hden.ne']
            ring
          _ ≤ re * B - B / (4 * den) := sub_le_sub_right hgapB _
      _ ≤ re * ((e * q : ℕ) : ℝ) -
          re * (((e * q : ℕ) : ℝ) / (q : ℝ)) :=
        sub_le_sub hreB hreMq
      _ = re * (1 - 1 / (q : ℝ)) * ((e * q : ℕ) : ℝ) := by ring
  have hstrictReal :
      rd * (1 - 1 / (p : ℝ)) * ((d * p : ℕ) : ℝ) <
        re * (1 - 1 / (q : ℝ)) * ((e * q : ℕ) : ℝ) := by
    apply hupper.trans_lt
    apply lt_of_lt_of_le (b := rd * B + 3 * (B / (4 * den)))
    · have : 0 < B / (4 * den) := by positivity
      linarith
    · exact hlower
  rw [← totient_mul_prime_real hd hp hpd,
    ← totient_mul_prime_real he hq hqe] at hstrictReal
  exact_mod_cast hstrictReal

#print axioms one_div_sq_le_totientRatio_sub
#print axioms totient_mul_prime_real
#print axioms primary_totient_lt_of_ratio_lt

end Erdos49

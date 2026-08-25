import ErdosProblems.Erdos69.HalaszMean

/-!
# A finite prime-avoidance sieve on arbitrary intervals

The one-level Selberg square in `Erdos69.HalaszMean` is stated on a prefix.
For the medium and large prime-band factors in the cheap Halasz argument we
need the same estimate on an arbitrary interval.  Subtracting the exact
divisor counts at the two endpoints gives an error of at most one for each
linear divisor condition and for each pair of divisor conditions.  Thus the
only new endpoint loss is quadratic in the cardinality of the prime packet.

The last theorem below is the directly usable `L^2` form: the square mass of
any one-bounded complex coefficient, restricted to integers avoiding the
packet, is bounded by the length divided by the reciprocal-prime mass, plus
the explicit endpoint loss.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67.MRIntervalSieve

noncomputable section

open Erdos69.HalaszMean

/-- Exact count of multiples on `(L,U]`, written as a difference of the two
prefix counts. -/
theorem sum_dvdIndicator_Ioc_interval {L U : ℕ} (hLU : L ≤ U) (d : ℕ) :
    (∑ n ∈ Finset.Ioc L U, dvdIndicator d n) =
      ((U / d : ℕ) : ℝ) - ((L / d : ℕ) : ℝ) := by
  have hdisj : Disjoint (Finset.Ioc 0 L) (Finset.Ioc L U) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hunion : Finset.Ioc 0 L ∪ Finset.Ioc L U = Finset.Ioc 0 U :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le L) hLU
  have hsum := Finset.sum_union hdisj (f := fun n ↦ dvdIndicator d n)
  rw [hunion, sum_dvdIndicator_Ioc U d, sum_dvdIndicator_Ioc L d] at hsum
  linarith

/-- A floor difference differs from the real interval length divided by the
modulus by at most one, lower-bound form. -/
theorem cast_div_interval_lower {L U : ℕ} (hLU : L ≤ U) (d : ℕ)
    (hd : 0 < d) :
    (((U - L : ℕ) : ℝ) / d) - 1 ≤
      ((U / d : ℕ) : ℝ) - ((L / d : ℕ) : ℝ) := by
  have hU := cast_div_lower U d hd
  have hL := cast_div_upper L d
  have hlen : (((U - L : ℕ) : ℝ) / d) =
      (U : ℝ) / d - (L : ℝ) / d := by
    rw [Nat.cast_sub hLU]
    ring
  rw [hlen]
  linarith

/-- A floor difference differs from the real interval length divided by the
modulus by at most one, upper-bound form. -/
theorem cast_div_interval_upper {L U : ℕ} (hLU : L ≤ U) (d : ℕ)
    (hd : 0 < d) :
    ((U / d : ℕ) : ℝ) - ((L / d : ℕ) : ℝ) ≤
      (((U - L : ℕ) : ℝ) / d) + 1 := by
  have hU := cast_div_upper U d
  have hL := cast_div_lower L d hd
  have hlen : (((U - L : ℕ) : ℝ) / d) =
      (U : ℝ) / d - (L : ℝ) / d := by
    rw [Nat.cast_sub hLU]
    ring
  rw [hlen]
  linarith

theorem sum_linear_dvdIndicator_interval
    (P : Finset ℕ) {L U : ℕ} (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ioc L U, ∑ p ∈ P, dvdIndicator p n) =
      ∑ p ∈ P, (((U / p : ℕ) : ℝ) - ((L / p : ℕ) : ℝ)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  exact sum_dvdIndicator_Ioc_interval hLU p

theorem sum_quadratic_dvdIndicator_interval
    (P : Finset ℕ) {L U : ℕ} (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ioc L U, (∑ p ∈ P, dvdIndicator p n) ^ 2) =
      ∑ p ∈ P, ∑ q ∈ P,
        (((U / Nat.lcm p q : ℕ) : ℝ) -
          ((L / Nat.lcm p q : ℕ) : ℝ)) := by
  calc
    (∑ n ∈ Finset.Ioc L U, (∑ p ∈ P, dvdIndicator p n) ^ 2) =
        ∑ n ∈ Finset.Ioc L U,
          ∑ p ∈ P, ∑ q ∈ P, dvdIndicator p n * dvdIndicator q n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
    _ = ∑ p ∈ P, ∑ q ∈ P,
        ∑ n ∈ Finset.Ioc L U, dvdIndicator p n * dvdIndicator q n := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
    _ = ∑ p ∈ P, ∑ q ∈ P,
        (((U / Nat.lcm p q : ℕ) : ℝ) -
          ((L / Nat.lcm p q : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      simp_rw [dvdIndicator_mul]
      exact sum_dvdIndicator_Ioc_interval hLU (Nat.lcm p q)

/-- The linear term in the interval Selberg square has the same endpoint
loss `#P` as on a prefix. -/
theorem linear_floor_interval_lower
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {L U : ℕ} (hLU : L ≤ U) :
    ((U - L : ℕ) : ℝ) * reciprocalMass P - P.card ≤
      ∑ p ∈ P, (((U / p : ℕ) : ℝ) - ((L / p : ℕ) : ℝ)) := by
  calc
    ((U - L : ℕ) : ℝ) * reciprocalMass P - P.card =
        ∑ p ∈ P, ((((U - L : ℕ) : ℝ) / p) - 1) := by
      rw [reciprocalMass, Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      apply congrArg₂ (· - ·)
      · apply Finset.sum_congr rfl
        intro p hp
        rw [div_eq_mul_inv]
      · simp
    _ ≤ ∑ p ∈ P,
        (((U / p : ℕ) : ℝ) - ((L / p : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact cast_div_interval_lower hLU p (hprime p hp).pos

/-- The quadratic term has one endpoint unit for every ordered pair of
primes. -/
theorem quadratic_floor_interval_upper
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    {L U : ℕ} (hLU : L ≤ U) :
    (∑ p ∈ P, ∑ q ∈ P,
        (((U / Nat.lcm p q : ℕ) : ℝ) -
          ((L / Nat.lcm p q : ℕ) : ℝ))) ≤
      ((U - L : ℕ) : ℝ) *
          (reciprocalMass P ^ 2 + diagonalMass P) + P.card ^ 2 := by
  have hlcm_pos : ∀ p ∈ P, ∀ q ∈ P, 0 < Nat.lcm p q := by
    intro p hp q hq
    exact Nat.lcm_pos (hprime p hp).pos (hprime q hq).pos
  calc
    (∑ p ∈ P, ∑ q ∈ P,
        (((U / Nat.lcm p q : ℕ) : ℝ) -
          ((L / Nat.lcm p q : ℕ) : ℝ))) ≤
        ∑ p ∈ P, ∑ q ∈ P,
          ((((U - L : ℕ) : ℝ) / Nat.lcm p q) + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact cast_div_interval_upper hLU (Nat.lcm p q) (hlcm_pos p hp q hq)
    _ = ((U - L : ℕ) : ℝ) *
          (∑ p ∈ P, ∑ q ∈ P, ((Nat.lcm p q : ℕ) : ℝ)⁻¹) +
        P.card ^ 2 := by
      simp_rw [Finset.sum_add_distrib, div_eq_mul_inv, Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      ring
    _ = ((U - L : ℕ) : ℝ) *
          (reciprocalMass P ^ 2 + diagonalMass P) + P.card ^ 2 := by
      rw [sum_inv_lcm_eq_sq_add_diagonalMass P hprime]

theorem sum_selbergLinearWeight_sq_interval
    (P : Finset ℕ) {L U : ℕ} (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ioc L U, selbergLinearWeight P n ^ 2) =
      ((U - L : ℕ) : ℝ) - 2 * selbergCoefficient P *
          (∑ p ∈ P,
            (((U / p : ℕ) : ℝ) - ((L / p : ℕ) : ℝ))) +
        selbergCoefficient P ^ 2 *
          (∑ p ∈ P, ∑ q ∈ P,
            (((U / Nat.lcm p q : ℕ) : ℝ) -
              ((L / Nat.lcm p q : ℕ) : ℝ))) := by
  let c := selbergCoefficient P
  let A : ℕ → ℝ := fun n ↦ ∑ p ∈ P, dvdIndicator p n
  calc
    (∑ n ∈ Finset.Ioc L U, selbergLinearWeight P n ^ 2) =
        ∑ n ∈ Finset.Ioc L U,
          (1 - 2 * c * A n + c ^ 2 * (A n) ^ 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [c, A, selbergLinearWeight]
      ring
    _ = (∑ n ∈ Finset.Ioc L U, (1 : ℝ)) -
          ∑ n ∈ Finset.Ioc L U, 2 * c * A n +
          ∑ n ∈ Finset.Ioc L U, c ^ 2 * (A n) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ((U - L : ℕ) : ℝ) - 2 * c *
          (∑ n ∈ Finset.Ioc L U, A n) +
        c ^ 2 * (∑ n ∈ Finset.Ioc L U, (A n) ^ 2) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      simp [hLU]
    _ = ((U - L : ℕ) : ℝ) - 2 * selbergCoefficient P *
          (∑ p ∈ P,
            (((U / p : ℕ) : ℝ) - ((L / p : ℕ) : ℝ))) +
        selbergCoefficient P ^ 2 *
          (∑ p ∈ P, ∑ q ∈ P,
            (((U / Nat.lcm p q : ℕ) : ℝ) -
              ((L / Nat.lcm p q : ℕ) : ℝ))) := by
      dsimp [c, A]
      rw [sum_linear_dvdIndicator_interval P hLU,
        sum_quadratic_dvdIndicator_interval P hLU]

/-- Arbitrary-interval Selberg bound.  Compared with the prefix theorem the
only extra loss is `#P^2`, coming from the pairwise divisor counts. -/
theorem primeAvoidance_interval_sum_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hmass : 0 < reciprocalMass P) {L U : ℕ} (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ioc L U, primeAvoidance P n) ≤
      ((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
        2 * P.card + P.card ^ 2 := by
  have hdiag : 0 ≤ diagonalMass P := diagonalMass_nonneg P hprime
  have hc0 : 0 ≤ selbergCoefficient P := selbergCoefficient_nonneg P hdiag
  have hc1 : selbergCoefficient P ≤ 1 := selbergCoefficient_le_one P hmass
  have hlinear := linear_floor_interval_lower P hprime hLU
  have hquad := quadratic_floor_interval_upper P hprime hLU
  have hbase :
      (∑ n ∈ Finset.Ioc L U, primeAvoidance P n) ≤
        ((U - L : ℕ) : ℝ) *
            (1 - 2 * selbergCoefficient P * reciprocalMass P +
              selbergCoefficient P ^ 2 *
                (reciprocalMass P ^ 2 + diagonalMass P)) +
          2 * selbergCoefficient P * P.card +
          selbergCoefficient P ^ 2 * P.card ^ 2 := by
    calc
      (∑ n ∈ Finset.Ioc L U, primeAvoidance P n) ≤
          ∑ n ∈ Finset.Ioc L U, selbergLinearWeight P n ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact primeAvoidance_le_selbergLinearWeight_sq P n
      _ = ((U - L : ℕ) : ℝ) - 2 * selbergCoefficient P *
            (∑ p ∈ P,
              (((U / p : ℕ) : ℝ) - ((L / p : ℕ) : ℝ))) +
          selbergCoefficient P ^ 2 *
            (∑ p ∈ P, ∑ q ∈ P,
              (((U / Nat.lcm p q : ℕ) : ℝ) -
                ((L / Nat.lcm p q : ℕ) : ℝ))) :=
        sum_selbergLinearWeight_sq_interval P hLU
      _ ≤ ((U - L : ℕ) : ℝ) - 2 * selbergCoefficient P *
            (((U - L : ℕ) : ℝ) * reciprocalMass P - P.card) +
          selbergCoefficient P ^ 2 *
            (((U - L : ℕ) : ℝ) *
                (reciprocalMass P ^ 2 + diagonalMass P) + P.card ^ 2) := by
        have hcoef : 0 ≤ (2 : ℝ) * selbergCoefficient P :=
          mul_nonneg (by norm_num) hc0
        have hlinmul := mul_le_mul_of_nonneg_left hlinear hcoef
        have hqmul := mul_le_mul_of_nonneg_left hquad
          (sq_nonneg (selbergCoefficient P))
        linarith
      _ = ((U - L : ℕ) : ℝ) *
            (1 - 2 * selbergCoefficient P * reciprocalMass P +
              selbergCoefficient P ^ 2 *
                (reciprocalMass P ^ 2 + diagonalMass P)) +
          2 * selbergCoefficient P * P.card +
          selbergCoefficient P ^ 2 * P.card ^ 2 := by ring
  rw [selbergQuadratic_eq_diagonal_div P hmass] at hbase
  have hdecay := diagonal_div_le_halasz_decay P hmass
  have hlength0 : (0 : ℝ) ≤ (U - L : ℕ) := Nat.cast_nonneg _
  have hmain := mul_le_mul_of_nonneg_left hdecay hlength0
  have hlinEndpoint :
      (2 : ℝ) * selbergCoefficient P * P.card ≤ 2 * P.card := by
    have htwo : (2 : ℝ) * selbergCoefficient P ≤ 2 := by linarith
    exact mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg P.card)
  have hquadEndpoint :
      selbergCoefficient P ^ 2 * (P.card : ℝ) ^ 2 ≤ (P.card : ℝ) ^ 2 := by
    have hcSq : selbergCoefficient P ^ 2 ≤ (1 : ℝ) := by
      nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
    simpa using mul_le_mul_of_nonneg_right hcSq (sq_nonneg (P.card : ℝ))
  calc
    (∑ n ∈ Finset.Ioc L U, primeAvoidance P n) ≤
        ((U - L : ℕ) : ℝ) *
            (diagonalMass P /
              (reciprocalMass P ^ 2 + diagonalMass P)) +
          2 * selbergCoefficient P * P.card +
          selbergCoefficient P ^ 2 * P.card ^ 2 := hbase
    _ ≤ ((U - L : ℕ) : ℝ) * (1 / (1 + reciprocalMass P)) +
          2 * P.card + P.card ^ 2 := by
      exact add_le_add (add_le_add hmain hlinEndpoint) hquadEndpoint
    _ = ((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
          2 * P.card + P.card ^ 2 := by
      simp only [one_mul, div_eq_mul_inv]

/-- Direct `L^2` sieve input.  The factor `primeAvoidance P n` restricts the
coefficient to integers with no prime divisor in `P`. -/
theorem sum_primeAvoidance_mul_normSq_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hmass : 0 < reciprocalMass P)
    (a : ℕ → ℂ) (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {L U : ℕ} (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ioc L U, primeAvoidance P n * Complex.normSq (a n)) ≤
      ((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
        2 * P.card + P.card ^ 2 := by
  calc
    (∑ n ∈ Finset.Ioc L U, primeAvoidance P n * Complex.normSq (a n)) ≤
        ∑ n ∈ Finset.Ioc L U, primeAvoidance P n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le L) (Finset.mem_Ioc.mp hn).1
      have hnorm := ha n hnpos
      rw [Complex.normSq_eq_norm_sq]
      by_cases hav : primeAvoidance P n = 0
      · simp [hav]
      · have hav1 : primeAvoidance P n = 1 := by
          unfold primeAvoidance at hav ⊢
          split <;> simp_all
        rw [hav1, one_mul]
        nlinarith [norm_nonneg (a n)]
    _ ≤ ((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
        2 * P.card + P.card ^ 2 :=
      primeAvoidance_interval_sum_le P hprime hmass hLU

/-- Support-form `L^2` sieve input.  It applies directly to a prime-band
coefficient once one checks that every nonzero term has no prime divisor in
the selected packet. -/
theorem sum_normSq_le_of_prime_avoiding_support
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hmass : 0 < reciprocalMass P)
    (a : ℕ → ℂ) (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {L U : ℕ} (hLU : L ≤ U)
    (hsupport : ∀ n ∈ Finset.Ioc L U, a n ≠ 0 →
      ∀ p ∈ P, ¬p ∣ n) :
    (∑ n ∈ Finset.Ioc L U, Complex.normSq (a n)) ≤
      ((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
        2 * P.card + P.card ^ 2 := by
  have heq :
      (∑ n ∈ Finset.Ioc L U, Complex.normSq (a n)) =
        ∑ n ∈ Finset.Ioc L U,
          primeAvoidance P n * Complex.normSq (a n) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases han : a n = 0
    · simp [han]
    · have hav : primeAvoidance P n = 1 :=
        primeAvoidance_eq_one_iff.mpr (hsupport n hn han)
      simp [hav]
  rw [heq]
  exact sum_primeAvoidance_mul_normSq_le P hprime hmass a ha hLU

end

end Erdos67.MRIntervalSieve

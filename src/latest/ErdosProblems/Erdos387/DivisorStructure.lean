/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CoverAlgebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The almost-prime case split in the BNPZ divisor argument

This file formalizes the elementary factorization step between Propositions
6.4 and 6.5 of Bui--Naprienko--Pratt--Zaharescu.  If an integer has no
factorization whose two factors both exceed a threshold `y`, its `y`-smooth
part is at most `y ^ 3`, and it has at most one prime factor above `y`, with
multiplicity one.  Consequently it is a small smooth factor times either
`1` or one large prime.
-/

namespace Erdos387

/-- `d` has no factorization with both factors strictly larger than `y`. -/
def NoConvenientFactorization (y d : ℕ) : Prop :=
  ∀ r s : ℕ, d = r * s → r ≤ y ∨ s ≤ y

/-- A `y`-smooth integer larger than `y` has a divisor in `(y, y²]`.

The proof is the greedy argument used implicitly in BNPZ: if the integer is
still above `y²`, divide by any prime factor (which is at most `y`) and apply
strong induction. -/
theorem exists_balanced_divisor_of_smooth {y f : ℕ} (hy : 2 ≤ y) (hyf : y < f)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ f → p ≤ y) :
    ∃ r : ℕ, r ∣ f ∧ y < r ∧ r ≤ y * y := by
  induction f using Nat.strong_induction_on with
  | h f ih =>
      by_cases hfy : f ≤ y * y
      · exact ⟨f, dvd_rfl, hyf, hfy⟩
      · have hfne : f ≠ 1 := by omega
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hfne
        have hple : p ≤ y := hsmooth p hp hpd
        have hfpos : 0 < f := by omega
        have hfdivlt : f / p < f := Nat.div_lt_self hfpos hp.one_lt
        have hmuleq : p * (f / p) = f := Nat.mul_div_cancel' hpd
        have hydiv : y < f / p := by
          by_contra hnot
          simp only [not_lt] at hnot
          nlinarith
        have hsmoothDiv : ∀ q : ℕ, q.Prime → q ∣ f / p → q ≤ y := by
          intro q hq hqd
          exact hsmooth q hq (hqd.trans (Nat.div_dvd_of_dvd hpd))
        obtain ⟨r, hrf, hyr, hry⟩ := ih (f / p) hfdivlt hydiv hsmoothDiv
        exact ⟨r, hrf.trans (Nat.div_dvd_of_dvd hpd), hyr, hry⟩

/-- Under the no-convenient-factorization hypothesis, every smooth divisor
is at most `y³`. -/
theorem smooth_divisor_le_cube {y d f : ℕ} (hy : 2 ≤ y) (hd : 0 < d)
    (hno : NoConvenientFactorization y d) (hfd : f ∣ d)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ f → p ≤ y) :
    f ≤ y ^ 3 := by
  by_contra hnot
  have hyf : y < f := by
    have hcubeLt : y ^ 3 < f := Nat.lt_of_not_ge hnot
    have hcube : y ^ 3 = y * y * y := by ring
    rw [hcube] at hcubeLt
    nlinarith
  obtain ⟨r, hrf, hyr, hry⟩ :=
    exists_balanced_divisor_of_smooth hy hyf hsmooth
  have hrd : r ∣ d := hrf.trans hfd
  have hdeq : d = r * (d / r) := (Nat.mul_div_cancel' hrd).symm
  have hys : y < d / r := by
    by_contra hnotS
    have hsle : d / r ≤ y := Nat.le_of_not_gt hnotS
    have hfle : f ≤ d := Nat.le_of_dvd hd hfd
    have hcube : y ^ 3 = y * y * y := by ring
    rw [hdeq] at hfle
    nlinarith
  rcases hno r (d / r) hdeq with hry' | hsy
  · omega
  · omega

/-- Two prime divisors above the threshold must be equal. -/
theorem large_primes_unique {y d p q : ℕ} (hd : 0 < d)
    (hno : NoConvenientFactorization y d)
    (hp : p.Prime) (hq : q.Prime) (hyp : y < p) (hyq : y < q)
    (hpd : p ∣ d) (hqd : q ∣ d) : p = q := by
  by_contra hpq
  have hcop : Nat.Coprime q p := by
    rw [hq.coprime_iff_not_dvd]
    intro hqp
    exact hpq ((hp.dvd_iff_eq hq.ne_one).mp hqp)
  have hqdiv : q ∣ d / p := by
    apply hcop.dvd_of_dvd_mul_left
    rwa [Nat.mul_div_cancel' hpd]
  have hp_le_d : p ≤ d := Nat.le_of_dvd hd hpd
  have hspos : 0 < d / p := Nat.div_pos hp_le_d hp.pos
  have hqle : q ≤ d / p := Nat.le_of_dvd hspos hqdiv
  have hdeq : d = p * (d / p) := (Nat.mul_div_cancel' hpd).symm
  rcases hno p (d / p) hdeq with hpy | hsy
  · omega
  · omega

/-- A prime divisor above the threshold occurs with multiplicity one. -/
theorem large_prime_squarefree {y d p : ℕ} (hd : 0 < d)
    (hno : NoConvenientFactorization y d)
    (hp : p.Prime) (hyp : y < p) (hpd : p ∣ d) :
    ¬p ^ 2 ∣ d := by
  intro hp2d
  have hpdiv : p ∣ d / p := by
    apply (Nat.dvd_div_iff_mul_dvd hpd).mpr
    simpa [pow_two] using hp2d
  have hp_le_d : p ≤ d := Nat.le_of_dvd hd hpd
  have hspos : 0 < d / p := Nat.div_pos hp_le_d hp.pos
  have hple : p ≤ d / p := Nat.le_of_dvd hspos hpdiv
  have hdeq : d = p * (d / p) := (Nat.mul_div_cancel' hpd).symm
  rcases hno p (d / p) hdeq with hpy | hsy
  · omega
  · omega

/-- Exact almost-prime decomposition used in the last two BNPZ error cases.
The small factor is `≤ y³`; the other factor is either one or a single prime
strictly exceeding `y`. -/
theorem exists_almostPrime_decomposition {y d : ℕ} (hy : 2 ≤ y) (hd : 0 < d)
    (hno : NoConvenientFactorization y d) :
    ∃ f q : ℕ, d = f * q ∧ f ≤ y ^ 3 ∧
      (q = 1 ∨ q.Prime ∧ y < q) := by
  by_cases hlarge : ∃ p : ℕ, p.Prime ∧ y < p ∧ p ∣ d
  · obtain ⟨p, hp, hyp, hpd⟩ := hlarge
    let f := d / p
    have hfd : f ∣ d := Nat.div_dvd_of_dvd hpd
    have hsmooth : ∀ r : ℕ, r.Prime → r ∣ f → r ≤ y := by
      intro r hr hrf
      by_contra hry
      have hyr : y < r := Nat.lt_of_not_ge hry
      have hre : r = p := large_primes_unique hd hno hr hp hyr hyp
        (hrf.trans hfd) hpd
      subst r
      have hp2d : p ^ 2 ∣ d := by
        apply (Nat.dvd_div_iff_mul_dvd hpd).mp at hrf
        simpa [pow_two] using hrf
      exact large_prime_squarefree hd hno hp hyp hpd hp2d
    refine ⟨f, p, ?_, smooth_divisor_le_cube hy hd hno hfd hsmooth,
      Or.inr ⟨hp, hyp⟩⟩
    exact (Nat.div_mul_cancel hpd).symm
  · have hsmooth : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ y := by
      intro p hp hpd
      by_contra hyp
      exact hlarge ⟨p, hp, Nat.lt_of_not_ge hyp, hpd⟩
    exact ⟨d, 1, by simp, smooth_divisor_le_cube hy hd hno dvd_rfl hsmooth,
      Or.inl rfl⟩

end Erdos387

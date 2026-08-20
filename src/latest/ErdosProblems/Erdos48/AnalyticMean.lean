/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import BoundedGaps.BombieriVinogradov.Analytic.VaughanPrimitiveMeanEquationOneOne
import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimePowerRemoval

/-!
# The primitive-character mean estimate used by Ford--Luca--Pomerance

The `BoundedGaps` library proves Vaughan's primitive-character mean-value
estimate in a slightly stronger, endpoint-maximal form.  This file records
the unweighted consequence used in FLP Lemma 2.5.  Keeping the exact
polynomial supplied by the library avoids any asymptotic or hidden-constant
interface.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

open BoundedGaps.Maynard

/-- FLP's primitive-character mass, with the maximum over endpoints up to
`x` already built in. -/
noncomputable def primitiveCharacterMass (x q : ℕ) : ℝ :=
  ∑ χ : primitiveCharacters q, primitiveRawEndpointMaximum x q χ

theorem primitiveCharacterMass_nonneg (x q : ℕ) :
    0 ≤ primitiveCharacterMass x q := by
  exact sum_primitiveRawEndpointMaximum_nonneg x q

/-- Euler's totient never exceeds its argument. -/
theorem one_le_cast_div_totient {q : ℕ} (hq : 0 < q) :
    (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := by
  have hφpos : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  rw [le_div_iff₀ hφpos]
  norm_num
  exact_mod_cast Nat.totient_le q

/-- Removing the source weight `q / φ(q)` can only decrease the positive
primitive-character mass. -/
theorem primitiveCharacterMass_le_weight (x : ℕ) {q : ℕ} (hq : 0 < q) :
    primitiveCharacterMass x q ≤
      ((q : ℝ) / (q.totient : ℝ)) * primitiveCharacterMass x q := by
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (one_le_cast_div_totient hq)
      (primitiveCharacterMass_nonneg x q)

/-- The centered primitive mass at a positive conductor is bounded by the
corresponding raw mass.  At conductor one the centered term is exactly zero;
at every larger conductor the two terms agree. -/
theorem centeredPrimitiveMass_le_raw (x : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ χ : primitiveCharacters d,
        primitiveCenteredEndpointMaximum x d χ) ≤
      primitiveCharacterMass x d := by
  by_cases hd1 : d = 1
  · subst d
    rw [sum_primitiveCenteredEndpointMaximum_one]
    exact primitiveCharacterMass_nonneg x 1
  · have hdTwo : 1 < d := by omega
    exact le_of_eq (sum_primitiveCenteredEndpointMaximum_eq_raw x hdTwo)

/-- Reindexing characters by conductor bounds the inducing-character mass
by the raw primitive masses over the divisors of the modulus. -/
theorem inducingPrimitiveMass_le_divisorMass (x : ℕ) {m : ℕ}
    (hm : 0 < m) :
    (∑ χ : DirichletCharacter ℂ m,
        inducingPrimitiveCenteredEndpointMaximum x m χ) ≤
      ∑ d ∈ m.divisors with d ≠ 1, primitiveCharacterMass x d := by
  rw [sum_inducingPrimitiveCenteredEndpointMaximum_eq_divisors_ne_one hm]
  apply Finset.sum_le_sum
  intro d hd
  have hdmem := (Finset.mem_filter.mp hd).1
  exact centeredPrimitiveMass_le_raw x (Nat.pos_of_mem_divisors hdmem)

/-- A product of two distinct primes has four divisors. -/
theorem card_divisors_prime_mul_prime {q r : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    (q * r).divisors.card = 4 := by
  have hcop : q.Coprime r := (Nat.coprime_primes hq hr).2 hqr
  calc
    (q * r).divisors.card = q.divisors.card * r.divisors.card :=
      hcop.card_divisors_mul
    _ = 2 * 2 := by
      rw [hq.divisors, hr.divisors,
        Finset.card_pair (Ne.symm hq.ne_one),
        Finset.card_pair (Ne.symm hr.ne_one)]
    _ = 4 := by norm_num

/-- If every nontrivial primitive conductor dividing `q*r` has mass at most
`x/10`, then the complete inducing-character mass costs at most `4x/10`.
This is the exact finite conductor decomposition in FLP equation (2.3). -/
theorem inducingPrimitiveMass_prime_mul_le
    {x q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hgood : ∀ d ∈ (q * r).divisors, d ≠ 1 →
      primitiveCharacterMass x d ≤ (x : ℝ) / 10) :
    (∑ χ : DirichletCharacter ℂ (q * r),
        inducingPrimitiveCenteredEndpointMaximum x (q * r) χ) ≤
      4 * ((x : ℝ) / 10) := by
  apply (inducingPrimitiveMass_le_divisorMass x
    (Nat.mul_pos hq.pos hr.pos)).trans
  calc
    (∑ d ∈ (q * r).divisors with d ≠ 1,
        primitiveCharacterMass x d) ≤
        ∑ _d ∈ (q * r).divisors with _d ≠ 1, (x : ℝ) / 10 := by
      apply Finset.sum_le_sum
      intro d hd
      have hddata := Finset.mem_filter.mp hd
      exact hgood d hddata.1 hddata.2
    _ ≤ 4 * ((x : ℝ) / 10) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · have hcard := Finset.card_filter_le
            (s := (q * r).divisors) (p := fun d ↦ d ≠ 1)
        rw [card_divisors_prime_mul_prime hq hr hqr] at hcard
        exact_mod_cast hcard
      · positivity

/-- The finite set of primes up to `x` in one natural residue class. -/
def primesInProgression (x m a : ℕ) : Finset ℕ :=
  (Nat.primesLE x).filter fun p ↦ p % m = a % m

@[simp] theorem mem_primesInProgression {x m a p : ℕ} :
    p ∈ primesInProgression x m a ↔
      p ≤ x ∧ p.Prime ∧ p % m = a % m := by
  rw [primesInProgression, Finset.mem_filter, Nat.mem_primesLE]
  tauto

/-- Every logarithmic prime weight in a progression is at most `log x`. -/
theorem thetaProgressionSum_le_card_mul_log
    {x m a : ℕ} (hx : 2 ≤ x) :
    thetaProgressionSum x m a ≤
      ((primesInProgression x m a).card : ℝ) * Real.log (x : ℝ) := by
  rw [thetaProgressionSum]
  change (∑ p ∈ primesInProgression x m a, Real.log (p : ℝ)) ≤ _
  calc
    (∑ p ∈ primesInProgression x m a, Real.log (p : ℝ)) ≤
        ∑ _p ∈ primesInProgression x m a, Real.log (x : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := mem_primesInProgression.mp hp
      apply Real.log_le_log
      · exact_mod_cast hpData.2.1.pos
      · exact_mod_cast hpData.1
    _ = ((primesInProgression x m a).card : ℝ) *
        Real.log (x : ℝ) := by
      simp [nsmul_eq_mul]

/-- A positive lower bound for the theta-weighted progression gives the
corresponding unweighted prime-count lower bound. -/
theorem div_log_le_card_primesInProgression
    {x m a : ℕ} (hx : 2 ≤ x) {L : ℝ}
    (hL : L ≤ thetaProgressionSum x m a) :
    L / Real.log (x : ℝ) ≤
      ((primesInProgression x m a).card : ℝ) := by
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  rw [div_le_iff₀ hlog]
  exact hL.trans (thetaProgressionSum_le_card_mul_log hx)

/-- FLP equation (2.3), followed by removal of higher prime powers, in the
special case of a product of two distinct primes.  All losses are displayed:
the elementary imprimitive-character correction, four primitive masses, and
the global prime-power remainder. -/
theorem centeredThetaProgressionDiscrepancy_prime_mul_le
    {x q r a : ℕ} (hx : 2 ≤ x)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (ha : a.Coprime (q * r))
    (hgood : ∀ d ∈ (q * r).divisors, d ≠ 1 →
      primitiveCharacterMass x d ≤ (x : ℝ) / 10) :
    centeredThetaProgressionDiscrepancy x (q * r) a ≤
      Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
        ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) +
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := by
  have hmOne : 1 ≤ q * r := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero hq.ne_zero hr.ne_zero)
  have hpsi := centeredProgressionEndpointMaximum_le_log_sq_add_primitive
    hx hmOne ha
  have hpoint : centeredProgressionDiscrepancy x (q * r) a ≤
      Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
        ((q * r).totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ (q * r),
            inducingPrimitiveCenteredEndpointMaximum x (q * r) χ) := by
    exact (Finset.le_sup'
      (fun y ↦ |chebyshevProgressionSum y (q * r) a -
        Chebyshev.psi (y : ℝ) / ((q * r).totient : ℝ)|)
      (Finset.mem_Icc.mpr ⟨hx, le_rfl⟩)).trans hpsi
  have hinducing := inducingPrimitiveMass_prime_mul_le hq hr hqr hgood
  have hpsi' : centeredProgressionDiscrepancy x (q * r) a ≤
      Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
        ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) := by
    exact hpoint.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hinducing (by positivity)))
  calc
    centeredThetaProgressionDiscrepancy x (q * r) a ≤
        centeredProgressionDiscrepancy x (q * r) a +
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) :=
      centeredThetaProgressionDiscrepancy_le hmOne
    _ ≤ (Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
          ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10))) +
        (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) :=
      add_le_add hpsi' le_rfl

/-- A source-shaped lower bound for the theta mass in a good product
progression.  Later parameter estimates only have to prove the displayed
right-hand side is large. -/
theorem thetaProgressionSum_prime_mul_lower
    {x q r a : ℕ} (hx : 2 ≤ x)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (ha : a.Coprime (q * r))
    (hgood : ∀ d ∈ (q * r).divisors, d ≠ 1 →
      primitiveCharacterMass x d ≤ (x : ℝ) / 10) :
    Chebyshev.theta (x : ℝ) / ((q * r).totient : ℝ) -
        (Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
          ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) +
            (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) ≤
      thetaProgressionSum x (q * r) a := by
  have hdisc := centeredThetaProgressionDiscrepancy_prime_mul_le
    hx hq hr hqr ha hgood
  rw [centeredThetaProgressionDiscrepancy,
    centeredThetaProgressionError] at hdisc
  have hlower := (abs_le.mp hdisc).1
  linarith

/-- The unweighted cumulative primitive mass is bounded by the exact
Vaughan polynomial.  This is the kernel-checked quantitative core of FLP
Lemma 2.5. -/
theorem sum_primitiveCharacterMass_le_vaughan
    {x M : ℕ} (hx : 4 ≤ x)
    (hM : (M : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Icc 1 M, primitiveCharacterMass x q) ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanEquationOneOnePolynomial x M *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  have hcumulative :=
    primitiveRawMeanValueCumulative_nat_le_equationOneOne hx hM
  apply le_trans ?_ hcumulative
  rw [primitiveRawMeanValueCumulative_nat_eq_weightedRawEndpointMaximum]
  apply Finset.sum_le_sum
  intro q hq
  have hqpos : 0 < q := by
    exact (Finset.mem_Icc.mp hq).1
  exact primitiveCharacterMass_le_weight x hqpos

/-- Finite Markov inequality for nonnegative weights, stated in the form used
to count conductors whose primitive mass exceeds a threshold. -/
theorem card_filter_mul_le_sum_of_nonneg
    {A : Type*} [DecidableEq A] (s : Finset A) (f : A → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hf : ∀ a ∈ s, 0 ≤ f a) :
    (((s.filter fun a ↦ T < f a).card : ℕ) : ℝ) * T ≤
      ∑ a ∈ s, f a := by
  calc
    (((s.filter fun a ↦ T < f a).card : ℕ) : ℝ) * T =
        ∑ _a ∈ s.filter (fun a ↦ T < f a), T := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ a ∈ s.filter (fun a ↦ T < f a), f a := by
      apply Finset.sum_le_sum
      intro a ha
      exact (Finset.mem_filter.mp ha).2.le
    _ ≤ ∑ a ∈ s, f a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro a ha _haFilter
      exact hf a ha

/-- Conductors with primitive mass larger than `x/10` satisfy the explicit
Vaughan/Markov cardinal bound. -/
theorem badPrimitiveConductors_card_mul_le_vaughan
    {x M : ℕ} (hx : 4 ≤ x)
    (hM : (M : ℝ) ≤ Real.sqrt (x : ℝ)) :
    ((((Finset.Icc 1 M).filter fun q ↦
        (x : ℝ) / 10 < primitiveCharacterMass x q).card : ℕ) : ℝ) *
          ((x : ℝ) / 10) ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanEquationOneOnePolynomial x M *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  exact (card_filter_mul_le_sum_of_nonneg (Finset.Icc 1 M)
    (primitiveCharacterMass x) (by positivity)
    (fun q _ ↦ primitiveCharacterMass_nonneg x q)).trans
      (sum_primitiveCharacterMass_le_vaughan hx hM)

/-- Multiplication by a fixed positive modulus injects a prime interval into
the conductor interval.  Consequently the total mass of the product
conductors `q*r` is controlled by the same global Vaughan mean. -/
theorem sum_prime_product_primitiveCharacterMass_le_vaughan
    {x q R : ℕ} (hx : 4 ≤ x) (hq : 0 < q)
    (hQR : (q * R : ℕ) ≤ Real.sqrt (x : ℝ)) :
    (∑ r ∈ Nat.primesLE R, primitiveCharacterMass x (q * r)) ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanEquationOneOnePolynomial x (q * R) *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  have hinj : Set.InjOn (fun r : ℕ ↦ q * r) (Nat.primesLE R) := by
    intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hq hab
  have hsubset : (Nat.primesLE R).image (fun r : ℕ ↦ q * r) ⊆
      Finset.Icc 1 (q * R) := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hd
    have hrData := Nat.mem_primesLE.mp hr
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hq.ne' hrData.2.ne_zero),
        Nat.mul_le_mul_left q hrData.1⟩
  calc
    (∑ r ∈ Nat.primesLE R, primitiveCharacterMass x (q * r)) =
        ∑ d ∈ (Nat.primesLE R).image (fun r : ℕ ↦ q * r),
          primitiveCharacterMass x d := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ d ∈ Finset.Icc 1 (q * R), primitiveCharacterMass x d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro d hd _
      exact primitiveCharacterMass_nonneg x d
    _ ≤ _ := by
      simpa only [Nat.cast_mul] using
        (sum_primitiveCharacterMass_le_vaughan hx hQR)

/-- Markov's inequality for the bad product conductors associated to one
fixed `q`. -/
theorem badPrimeProductPartners_card_mul_le_vaughan
    {x q R : ℕ} (hx : 4 ≤ x) (hq : 0 < q)
    (hQR : (q * R : ℕ) ≤ Real.sqrt (x : ℝ)) :
    ((((Nat.primesLE R).filter fun r ↦
        (x : ℝ) / 10 < primitiveCharacterMass x (q * r)).card : ℕ) : ℝ) *
          ((x : ℝ) / 10) ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanEquationOneOnePolynomial x (q * R) *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  exact (card_filter_mul_le_sum_of_nonneg (Nat.primesLE R)
    (fun r ↦ primitiveCharacterMass x (q * r)) (by positivity)
    (fun r _ ↦ primitiveCharacterMass_nonneg x (q * r))).trans
      (sum_prime_product_primitiveCharacterMass_le_vaughan hx hq hQR)

end

end Erdos48

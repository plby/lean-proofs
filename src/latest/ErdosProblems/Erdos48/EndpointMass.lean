/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.AnalyticMean

/-!
# The endpoint-exact character mass in Ford--Luca--Pomerance

Ford--Luca--Pomerance define `Psi(x,m)` at the single endpoint `x`.  The
Bombieri--Vinogradov development also supplies endpoint maxima, and those are
convenient for Vaughan's mean theorem, but the small-conductor Gallagher input
is only an endpoint statement.  This file separates the two notions and proves
all finite conductor and progression reductions for the weaker, source-exact
mass.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

open BoundedGaps.Maynard

/-- FLP's quantity `Psi(x,q)`: the sum of the norms of the primitive twists at
the single endpoint `x`. -/
noncomputable def primitiveEndpointMass (x q : ℕ) : ℝ :=
  ∑ psi : primitiveCharacters q, ‖twistedChebyshevSum x q psi.1‖

theorem primitiveEndpointMass_nonneg (x q : ℕ) :
    0 ≤ primitiveEndpointMass x q := by
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- A single endpoint is bounded by the endpoint maximum already used in the
formal Vaughan mean theorem. -/
theorem primitiveEndpointMass_le_primitiveCharacterMass
    {x q : ℕ} (hx : 2 ≤ x) :
    primitiveEndpointMass x q ≤ primitiveCharacterMass x q := by
  unfold primitiveEndpointMass primitiveCharacterMass
  apply Finset.sum_le_sum
  intro psi _
  unfold primitiveRawEndpointMaximum
  rw [dif_pos hx]
  exact Finset.le_sup' (fun y => ‖twistedChebyshevSum y q psi.1‖)
    (Finset.mem_Icc.mpr ⟨hx, le_rfl⟩)

/-- The endpoint norm of the canonical primitive character inducing `chi`. -/
noncomputable def inducingPrimitiveCenteredEndpointMass
    (x q : ℕ) (chi : DirichletCharacter ℂ q) : ℝ :=
  ‖centeredTwistedChebyshevSum x chi.conductor chi.primitiveCharacter‖

/-- Lifting a primitive character does not change its inducing endpoint mass.
-/
theorem inducingPrimitiveCenteredEndpointMass_changeLevel
    {x q d : ℕ} (hq : 0 < q) (hd : d ∣ q)
    (psi : primitiveCharacters d) :
    inducingPrimitiveCenteredEndpointMass x q
        (DirichletCharacter.changeLevel hd psi.1) =
      ‖centeredTwistedChebyshevSum x d psi.1‖ := by
  unfold inducingPrimitiveCenteredEndpointMass
  rw [centeredTwistedChebyshevSum_changeLevel_primitive hq hd psi]

/-- Partition the inducing endpoint mass by primitive conductor. -/
theorem sum_inducingPrimitiveCenteredEndpointMass_eq_divisors
    {x q : ℕ} (hq : 0 < q) :
    (∑ chi : DirichletCharacter ℂ q,
      inducingPrimitiveCenteredEndpointMass x q chi) =
      ∑ d : q.divisors,
        ∑ psi : primitiveCharacters d.1,
          ‖centeredTwistedChebyshevSum x d.1 psi.1‖ := by
  rw [sum_characters_eq_sum_divisor_primitive hq]
  apply Fintype.sum_congr
  intro d
  apply Fintype.sum_congr
  intro psi
  exact inducingPrimitiveCenteredEndpointMass_changeLevel hq
    (Nat.dvd_of_mem_divisors d.2) psi

/-- The centered primitive endpoint contribution at conductor one is zero. -/
theorem sum_norm_centeredTwistedChebyshevSum_one (x : ℕ) :
    (∑ psi : primitiveCharacters 1,
      ‖centeredTwistedChebyshevSum x 1 psi.1‖) = 0 := by
  apply Fintype.sum_eq_zero
  intro psi
  rw [show (psi.1 : DirichletCharacter ℂ 1) = 1 by
    exact DirichletCharacter.level_one psi.1]
  simp [centeredTwistedChebyshevSum_one]

/-- Remove precisely the conductor-one term from the endpoint partition. -/
theorem sum_inducingPrimitiveCenteredEndpointMass_eq_divisors_ne_one
    {x q : ℕ} (hq : 0 < q) :
    (∑ chi : DirichletCharacter ℂ q,
      inducingPrimitiveCenteredEndpointMass x q chi) =
      ∑ d ∈ q.divisors with d ≠ 1,
        ∑ psi : primitiveCharacters d,
          ‖centeredTwistedChebyshevSum x d psi.1‖ := by
  rw [sum_inducingPrimitiveCenteredEndpointMass_eq_divisors hq]
  let G : ℕ → ℝ := fun d =>
    ∑ psi : primitiveCharacters d,
      ‖centeredTwistedChebyshevSum x d psi.1‖
  have hzero : ∀ d ∈ q.divisors, d = 1 → G d = 0 := by
    intro d _ hd
    subst d
    exact sum_norm_centeredTwistedChebyshevSum_one x
  change (∑ d : q.divisors, G d.1) =
    ∑ d ∈ q.divisors with d ≠ 1, G d
  rw [← Finset.sum_subtype q.divisors (fun _ => Iff.rfl) G,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hd1 : d ≠ 1
  · simp [hd1]
  · have hEq : d = 1 := not_ne_iff.mp hd1
    subst d
    simpa using hzero 1 hd rfl

/-- Above conductor one, the centered endpoint mass is the raw FLP mass. -/
theorem sum_norm_centeredTwistedChebyshevSum_eq_endpointMass
    (x : ℕ) {d : ℕ} (hd : 1 < d) :
    (∑ psi : primitiveCharacters d,
      ‖centeredTwistedChebyshevSum x d psi.1‖) =
      primitiveEndpointMass x d := by
  unfold primitiveEndpointMass
  apply Fintype.sum_congr
  intro psi
  rw [centeredTwistedChebyshevSum_eq_twisted_of_primitive hd psi]

/-- Reindexing all characters by conductor bounds the inducing endpoint mass
by the divisor sum of the source-exact primitive masses. -/
theorem inducingPrimitiveEndpointMass_le_divisorMass
    (x : ℕ) {m : ℕ} (hm : 0 < m) :
    (∑ chi : DirichletCharacter ℂ m,
        inducingPrimitiveCenteredEndpointMass x m chi) ≤
      ∑ d ∈ m.divisors with d ≠ 1, primitiveEndpointMass x d := by
  rw [sum_inducingPrimitiveCenteredEndpointMass_eq_divisors_ne_one hm]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro d hd
  have hdData := Finset.mem_filter.mp hd
  have hdPos := Nat.pos_of_mem_divisors hdData.1
  rw [sum_norm_centeredTwistedChebyshevSum_eq_endpointMass x (by omega)]

/-- For a product of two distinct primes, four endpoint conductor bounds
control the complete character average. -/
theorem inducingPrimitiveEndpointMass_prime_mul_le
    {x q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hgood : ∀ d ∈ (q * r).divisors, d ≠ 1 →
      primitiveEndpointMass x d ≤ (x : ℝ) / 10) :
    (∑ chi : DirichletCharacter ℂ (q * r),
        inducingPrimitiveCenteredEndpointMass x (q * r) chi) ≤
      4 * ((x : ℝ) / 10) := by
  apply (inducingPrimitiveEndpointMass_le_divisorMass x
    (Nat.mul_pos hq.pos hr.pos)).trans
  calc
    (∑ d ∈ (q * r).divisors with d ≠ 1,
        primitiveEndpointMass x d) ≤
        ∑ _d ∈ (q * r).divisors with _d ≠ 1, (x : ℝ) / 10 := by
      apply Finset.sum_le_sum
      intro d hd
      exact hgood d (Finset.mem_filter.mp hd).1
        (Finset.mem_filter.mp hd).2
    _ ≤ 4 * ((x : ℝ) / 10) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · have hcard := Finset.card_filter_le
          (s := (q * r).divisors) (p := fun d => d ≠ 1)
        rw [card_divisors_prime_mul_prime hq hr hqr] at hcard
        exact_mod_cast hcard
      · positivity

/-- The pointwise progression discrepancy in terms of FLP's endpoint mass. -/
theorem centeredProgressionDiscrepancy_prime_mul_endpoint_le
    {x q r a : ℕ} (hx : 2 ≤ x)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (ha : a.Coprime (q * r))
    (hgood : ∀ d ∈ (q * r).divisors, d ≠ 1 →
      primitiveEndpointMass x d ≤ (x : ℝ) / 10) :
    centeredProgressionDiscrepancy x (q * r) a ≤
      Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
        ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) := by
  have hmOne : 1 ≤ q * r := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero hq.ne_zero hr.ne_zero)
  have hpoint :=
    abs_chebyshevProgressionSum_sub_global_le_log_sq_add_primitive_average
      hx hmOne ha
  change |chebyshevProgressionSum x (q * r) a -
      Chebyshev.psi (x : ℝ) / ((q * r).totient : ℝ)| ≤ _
  apply hpoint.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact inducingPrimitiveEndpointMass_prime_mul_le hq hr hqr hgood

/-- FLP equation (2.3) at the natural endpoint, followed by removal of higher
prime powers. -/
theorem centeredThetaProgressionDiscrepancy_prime_mul_endpoint_le
    {x q r a : ℕ} (hx : 2 ≤ x)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (ha : a.Coprime (q * r))
    (hgood : ∀ d ∈ (q * r).divisors, d ≠ 1 →
      primitiveEndpointMass x d ≤ (x : ℝ) / 10) :
    centeredThetaProgressionDiscrepancy x (q * r) a ≤
      Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
        ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) +
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := by
  calc
    centeredThetaProgressionDiscrepancy x (q * r) a ≤
        centeredProgressionDiscrepancy x (q * r) a +
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) :=
      centeredThetaProgressionDiscrepancy_le
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero hq.ne_zero hr.ne_zero))
    _ ≤ _ := add_le_add
      (centeredProgressionDiscrepancy_prime_mul_endpoint_le
        hx hq hr hqr ha hgood) le_rfl

/-- The source-shaped lower bound for a progression whose three nontrivial
primitive conductors have small endpoint mass. -/
theorem thetaProgressionSum_prime_mul_endpoint_lower
    {x q r a : ℕ} (hx : 2 ≤ x)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (ha : a.Coprime (q * r))
    (hgood : ∀ d ∈ (q * r).divisors, d ≠ 1 →
      primitiveEndpointMass x d ≤ (x : ℝ) / 10) :
    Chebyshev.theta (x : ℝ) / ((q * r).totient : ℝ) -
        (Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
          ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) +
            (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) ≤
      thetaProgressionSum x (q * r) a := by
  have hdisc := centeredThetaProgressionDiscrepancy_prime_mul_endpoint_le
    hx hq hr hqr ha hgood
  rw [centeredThetaProgressionDiscrepancy,
    centeredThetaProgressionError] at hdisc
  linarith [(abs_le.mp hdisc).1]

/-- The existing Vaughan mean for endpoint maxima immediately bounds the
source-exact endpoint masses. -/
theorem sum_primitiveEndpointMass_le_vaughan
    {x M : ℕ} (hx : 4 ≤ x)
    (hM : (M : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Icc 1 M, primitiveEndpointMass x q) ≤
      vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanEquationOneOnePolynomial x M *
          vaughanPrimitiveMeanEquationOneOneLogPower x := by
  calc
    (∑ q ∈ Finset.Icc 1 M, primitiveEndpointMass x q) ≤
        ∑ q ∈ Finset.Icc 1 M, primitiveCharacterMass x q := by
      apply Finset.sum_le_sum
      intro q _
      exact primitiveEndpointMass_le_primitiveCharacterMass (by omega)
    _ ≤ _ := sum_primitiveCharacterMass_le_vaughan hx hM

end

end Erdos48

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.BilinearMomentInequality
import ErdosProblems.Erdos387.HighMomentExpansion
import Mathlib.Algebra.Order.Chebyshev

/-!
# Hölder--Cauchy reduction for the convenient-factor case

This file connects the exact phase-preserving high-moment expansion with
the two complete-frequency moments.  It is the finite algebraic core of
BNPZ (9.2), before the dyadic summation over the original divisor
certificates.
-/

namespace Erdos387

open scoped BigOperators

namespace ConvenientMoment

/-- The chosen unimodular coefficient specialized to the scaled inverse
phase `h a / r`. -/
noncomputable def inversePhaseEta
    (q h a ell : ℕ) [NeZero q] (U : Finset ℕ)
    (beta : ℕ → ℂ) (r : ℕ) : ℂ :=
  HighMoment.reciprocalEta q ell U beta
    ((h : ZMod q) * (a : ZMod q)) (r : ZMod q)

theorem norm_inversePhaseEta
    (q h a ell : ℕ) [NeZero q] (U : Finset ℕ)
    (beta : ℕ → ℂ) (r : ℕ) :
    ‖inversePhaseEta q h a ell U beta r‖ = 1 := by
  exact HighMoment.norm_reciprocalEta q ell U beta
    ((h : ZMod q) * (a : ZMod q)) (r : ZMod q)

/-- Sum the exact high-moment expansion over the short variable and
interchange that sum with the complete additive frequency.  The
unimodular coefficient becomes the one-bounded short-variable weight in
`T₂`. -/
theorem sum_norm_reciprocalCharacter_pow_eq_bilinear
    (q h a ell : ℕ) [NeZero q]
    (U R : Finset ℕ) (beta : ℕ → ℂ) :
    (∑ r ∈ R,
        ((‖∑ s ∈ U,
            beta s * ZMod.stdAddChar
              ((h : ZMod q) * (a : ZMod q) *
                (r : ZMod q)⁻¹ * (s : ZMod q)⁻¹)‖ ^ ell : ℝ) : ℂ)) =
      ∑ u : ZMod q,
        AdditiveOrthogonality.residueFiberSum
            (ReciprocalMoment.halfTuples ell U)
            (ReciprocalMoment.halfPhase q)
            (fun t => ∏ j, beta (t j)) u *
          AdditiveOrthogonality.characterSum R
            (InversePhase.phase q h a)
            (inversePhaseEta q h a ell U beta) u := by
  classical
  let nu : ZMod q → ℂ :=
    AdditiveOrthogonality.residueFiberSum
      (ReciprocalMoment.halfTuples ell U)
      (ReciprocalMoment.halfPhase q)
      (fun t => ∏ j, beta (t j))
  calc
    (∑ r ∈ R,
        ((‖∑ s ∈ U,
            beta s * ZMod.stdAddChar
              ((h : ZMod q) * (a : ZMod q) *
                (r : ZMod q)⁻¹ * (s : ZMod q)⁻¹)‖ ^ ell : ℝ) : ℂ)) =
        ∑ r ∈ R, inversePhaseEta q h a ell U beta r *
          ∑ u : ZMod q, nu u *
            ZMod.stdAddChar
              ((h : ZMod q) * (a : ZMod q) * (r : ZMod q)⁻¹ * u) := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact HighMoment.norm_weighted_reciprocal_sum_pow_grouped_eq
        q ell U beta ((h : ZMod q) * (a : ZMod q)) (r : ZMod q)
    _ = ∑ r ∈ R, ∑ u : ZMod q,
          nu u *
            (inversePhaseEta q h a ell U beta r *
              ZMod.stdAddChar
                (u * InversePhase.phase q h a r)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      simp only [InversePhase.phase]
      have hchar :
          ZMod.stdAddChar
              ((h : ZMod q) * (a : ZMod q) * (r : ZMod q)⁻¹ * u) =
            ZMod.stdAddChar
              (u * ((h : ZMod q) * (a : ZMod q) * (r : ZMod q)⁻¹)) := by
        congr 1
        ring
      rw [hchar]
      ring
    _ = ∑ u : ZMod q, nu u *
          ∑ r ∈ R, inversePhaseEta q h a ell U beta r *
            ZMod.stdAddChar (u * InversePhase.phase q h a r) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum]
    _ = ∑ u : ZMod q, nu u *
          AdditiveOrthogonality.characterSum R
            (InversePhase.phase q h a)
            (inversePhaseEta q h a ell U beta) u := by
      rfl
    _ = _ := by rfl

/-- Jensen/Hölder in the precise finite form used to pass from the first
moment over a finite certificate family to an `ell`-th moment. -/
theorem sum_pow_le_card_pow_mul_sum_pow
    {I : Type*} [DecidableEq I]
    (S : Finset I) (f : I → ℝ) (ell : ℕ) (hell : 1 ≤ ell)
    (hf : ∀ i ∈ S, 0 ≤ f i) :
    (∑ i ∈ S, f i) ^ ell ≤
      (S.card : ℝ) ^ (ell - 1) * ∑ i ∈ S, f i ^ ell := by
  have h := pow_sum_le_card_mul_sum_pow hf (ell - 1)
  have he : ell - 1 + 1 = ell := by omega
  simpa only [he] using h

/-- Hölder followed by a supplied square bound for the high moment. -/
theorem holder_cauchy_of_moment_sq_le
    {I : Type*} [DecidableEq I]
    (S : Finset I) (f : I → ℝ) (ell : ℕ) (hell : 1 ≤ ell)
    (hf : ∀ i ∈ S, 0 ≤ f i) {B : ℝ}
    (hmoment : (∑ i ∈ S, f i ^ ell) ^ 2 ≤ B) :
    (∑ i ∈ S, f i) ^ (2 * ell) ≤
      (S.card : ℝ) ^ (2 * (ell - 1)) * B := by
  have hholder := sum_pow_le_card_pow_mul_sum_pow S f ell hell hf
  have htotal : 0 ≤ ∑ i ∈ S, f i := Finset.sum_nonneg hf
  calc
    (∑ i ∈ S, f i) ^ (2 * ell) =
        ((∑ i ∈ S, f i) ^ ell) ^ 2 := by
      rw [mul_comm, pow_mul]
    _ ≤ ((S.card : ℝ) ^ (ell - 1) *
          ∑ i ∈ S, f i ^ ell) ^ 2 :=
      pow_le_pow_left₀ (pow_nonneg htotal ell) hholder 2
    _ = (S.card : ℝ) ^ (2 * (ell - 1)) *
          (∑ i ∈ S, f i ^ ell) ^ 2 := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    _ ≤ (S.card : ℝ) ^ (2 * (ell - 1)) * B :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)

/-- Product-indexed version of the preceding theorem, matching the outer
modulus/short-variable pair in the convenient-factor argument. -/
theorem family_holder_cauchy_of_moment_sq_le
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (S : Finset I) (T : Finset J) (f : I → J → ℝ)
    (ell : ℕ) (hell : 1 ≤ ell)
    (hf : ∀ i ∈ S, ∀ j ∈ T, 0 ≤ f i j) {B : ℝ}
    (hmoment : (∑ i ∈ S, ∑ j ∈ T, (f i j) ^ ell) ^ 2 ≤ B) :
    (∑ i ∈ S, ∑ j ∈ T, f i j) ^ (2 * ell) ≤
      (S.card * T.card : ℕ) ^ (2 * (ell - 1)) * B := by
  let F : I × J → ℝ := fun ij => f ij.1 ij.2
  have hF : ∀ ij ∈ S ×ˢ T, 0 ≤ F ij := by
    intro ij hij
    exact hf ij.1 (Finset.mem_product.mp hij).1
      ij.2 (Finset.mem_product.mp hij).2
  have h := holder_cauchy_of_moment_sq_le
    (S ×ˢ T) F ell hell hF (B := B) (by
      simpa [F, Finset.sum_product] using hmoment)
  simpa [F, Finset.sum_product, Finset.card_product, Nat.cast_mul] using h

/-- The exact regrouping simultaneously over a finite family of varying
moduli. -/
theorem sum_family_norm_reciprocalCharacter_pow_eq_bilinear
    (ell : ℕ) (Q : Finset ℕ)
    (modulus frequency scale : ℕ → ℕ)
    [∀ d, NeZero (modulus d)]
    (U R : Finset ℕ) (beta : ℕ → ℕ → ℂ) :
    (((∑ d ∈ Q, ∑ r ∈ R,
        ‖∑ s ∈ U,
          beta d s * ZMod.stdAddChar
            ((frequency d : ZMod (modulus d)) *
              (scale d : ZMod (modulus d)) *
              (r : ZMod (modulus d))⁻¹ *
              (s : ZMod (modulus d))⁻¹)‖ ^ ell : ℝ)) : ℂ) =
      ∑ d ∈ Q, ∑ u : ZMod (modulus d),
        AdditiveOrthogonality.residueFiberSum
            (ReciprocalMoment.halfTuples ell U)
            (ReciprocalMoment.halfPhase (modulus d))
            (fun t => ∏ j, beta d (t j)) u *
          AdditiveOrthogonality.characterSum R
            (InversePhase.phase (modulus d) (frequency d) (scale d))
            (inversePhaseEta (modulus d) (frequency d) (scale d)
              ell U (beta d)) u := by
  classical
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Complex.ofReal_sum]
  exact sum_norm_reciprocalCharacter_pow_eq_bilinear
    (modulus d) (frequency d) (scale d) ell U R (beta d)

/-- Insert the two checked complete-frequency moment estimates after the
exact high-moment expansion.  This is the subpower-scale finite form of
BNPZ (9.2). -/
theorem subpower_sum_norm_reciprocalCharacter_pow_sq_le
    {ell N k R : ℕ} (hk : 0 < k)
    (Q : Finset ℕ) (modulus frequency scale : ℕ → ℕ)
    [∀ d, NeZero (modulus d)]
    (Sbox Rbox : Finset ℕ) (beta : ℕ → ℕ → ℂ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (SubpowerScale.z N k) d)
    (hSpos : ∀ s ∈ Sbox, 0 < s)
    (hSle : ∀ s ∈ Sbox, s ≤ SubpowerScale.medium N k)
    (hSrough : ∀ s ∈ Sbox, IsZRough (SubpowerScale.z N k) s)
    (hScop : ∀ d ∈ Q, ∀ s ∈ Sbox, s.Coprime (modulus d))
    (hbeta : ∀ d ∈ Q, ∀ s ∈ Sbox, ‖beta d s‖ ≤ 1)
    (hmodPos : ∀ d ∈ Q, 0 < modulus d)
    (hscale : ∀ d ∈ Q, (scale d).Coprime (modulus d))
    (hRcop : ∀ d ∈ Q, ∀ r ∈ Rbox, r.Coprime (modulus d))
    (hRle : ∀ r ∈ Rbox, r ≤ R)
    (hshort : ∀ d ∈ Q,
      R < modulus d / Nat.gcd (modulus d) (frequency d)) :
    (∑ d ∈ Q, ∑ r ∈ Rbox,
        ‖∑ s ∈ Sbox,
          beta d s * ZMod.stdAddChar
            ((frequency d : ZMod (modulus d)) *
              (scale d : ZMod (modulus d)) *
              (r : ZMod (modulus d))⁻¹ *
              (s : ZMod (modulus d))⁻¹)‖ ^ ell) ^ 2 ≤
      (((Q.card * SubpowerScale.medium N k ^ ell +
          Sbox.card ^ (2 * ell)) * SubpowerScale.base N k) *
        (∑ d ∈ Q, modulus d * Rbox.card) : ℕ) := by
  classical
  let moment : ℝ := ∑ d ∈ Q, ∑ r ∈ Rbox,
    ‖∑ s ∈ Sbox,
      beta d s * ZMod.stdAddChar
        ((frequency d : ZMod (modulus d)) *
          (scale d : ZMod (modulus d)) *
          (r : ZMod (modulus d))⁻¹ *
          (s : ZMod (modulus d))⁻¹)‖ ^ ell
  let bilinear : ℂ := ∑ d ∈ Q, ∑ u : ZMod (modulus d),
    AdditiveOrthogonality.residueFiberSum
        (ReciprocalMoment.halfTuples ell Sbox)
        (ReciprocalMoment.halfPhase (modulus d))
        (fun t => ∏ j, beta d (t j)) u *
      AdditiveOrthogonality.characterSum Rbox
        (InversePhase.phase (modulus d) (frequency d) (scale d))
        (inversePhaseEta (modulus d) (frequency d) (scale d)
          ell Sbox (beta d)) u
  have heq : (moment : ℂ) = bilinear := by
    simpa [moment, bilinear] using
      sum_family_norm_reciprocalCharacter_pow_eq_bilinear
        ell Q modulus frequency scale Sbox Rbox beta
  have hmomentNonneg : 0 ≤ moment := by
    dsimp [moment]
    positivity
  have hnorm : moment = ‖bilinear‖ := by
    calc
      moment = ‖(moment : ℂ)‖ := by
        simp [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hmomentNonneg]
      _ = ‖bilinear‖ := congrArg norm heq
  have hweightS : ∀ d ∈ Q,
      ∀ t ∈ ReciprocalMoment.halfTuples ell Sbox,
        ‖∏ j, beta d (t j)‖ ≤ 1 := by
    intro d hd t ht
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro j _hj
      positivity
    · intro j _hj
      exact hbeta d hd (t j) (Fintype.mem_piFinset.mp ht j)
  have hweightR : ∀ d ∈ Q, ∀ r ∈ Rbox,
      ‖inversePhaseEta (modulus d) (frequency d) (scale d)
        ell Sbox (beta d) r‖ ≤ 1 := by
    intro d _hd r _hr
    rw [norm_inversePhaseEta]
  have hbilinear := BilinearMoment.subpower_bilinear_character_cauchy
    hk Q modulus frequency scale Sbox Rbox
      (fun d t => ∏ j, beta d (t j))
      (fun d r => inversePhaseEta (modulus d) (frequency d) (scale d)
        ell Sbox (beta d) r)
      hN hDmod hQrough hSpos hSle hSrough hScop hweightS
      hmodPos hscale hweightR hRcop hRle hshort
  change moment ^ 2 ≤ _
  rw [hnorm]
  simpa [bilinear] using hbilinear

end ConvenientMoment

end Erdos387

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ReciprocalMoment
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic

/-!
# Opening a finite high moment

This file formalizes the algebra immediately before the two Cauchy factors
in BNPZ Lemma 9.2.  An `ell`-th power of a finite sum is a sum over ordered
`ell`-tuples, and the absolute value is removed by a unimodular coefficient
without discarding the phase.
-/

namespace Erdos387

open scoped BigOperators

namespace HighMoment

/-- Finite-sum form of the defining additive-character homomorphism law. -/
theorem prod_addChar_eq_addChar_sum
    {A M ι : Type*} [AddCommMonoid A] [CommMonoid M]
    (psi : AddChar A M) (S : Finset ι) (f : ι → A) :
    (∏ i ∈ S, psi (f i)) = psi (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      simp [ha, ih, AddChar.map_add_eq_mul]

/-- Ordered-tuple expansion of a power of a finite sum. -/
theorem sum_pow_eq_halfTuples_prod
    {R : Type*} [CommRing R]
    (ell : ℕ) (U : Finset ℕ) (f : ℕ → R) :
    (∑ u ∈ U, f u) ^ ell =
      ∑ s ∈ ReciprocalMoment.halfTuples ell U, ∏ j, f (s j) := by
  classical
  simpa [ReciprocalMoment.halfTuples] using Finset.sum_pow' U f ell

/-- A complex power of an absolute value can be written as the same power
with one unimodular coefficient. -/
theorem exists_unimodular_mul_pow_eq_norm_pow (ell : ℕ) (z : ℂ) :
    ∃ eta : ℂ, ‖eta‖ = 1 ∧
      ((‖z‖ ^ ell : ℝ) : ℂ) = eta * z ^ ell := by
  obtain ⟨c, hcNorm, hc⟩ := Complex.exists_norm_eq_mul_self z
  refine ⟨c ^ ell, ?_, ?_⟩
  · rw [norm_pow, hcNorm, one_pow]
  · have hp := congrArg (fun w : ℂ => w ^ ell) hc
    rw [mul_pow] at hp
    simpa using hp

/-- Exact phase-preserving expansion used after replacing
`|sum|^ell` by `eta * sum^ell`. -/
theorem exists_unimodular_norm_sum_pow_expansion
    (ell : ℕ) (U : Finset ℕ) (f : ℕ → ℂ) :
    ∃ eta : ℂ, ‖eta‖ = 1 ∧
      ((‖∑ u ∈ U, f u‖ ^ ell : ℝ) : ℂ) =
        eta *
          ∑ s ∈ ReciprocalMoment.halfTuples ell U, ∏ j, f (s j) := by
  obtain ⟨eta, heta, hpow⟩ :=
    exists_unimodular_mul_pow_eq_norm_pow ell (∑ u ∈ U, f u)
  refine ⟨eta, heta, ?_⟩
  rw [hpow, sum_pow_eq_halfTuples_prod]

/-- Products of the one-variable reciprocal characters combine into the
character of the modular reciprocal sum of the whole tuple. -/
theorem prod_stdAddChar_scaled_inv_eq_halfPhase
    (q ell : ℕ) [NeZero q] (c r : ZMod q) (s : Fin ell → ℕ) :
    (∏ j, ZMod.stdAddChar (c * r⁻¹ * (s j : ZMod q)⁻¹)) =
      ZMod.stdAddChar
        (c * r⁻¹ * ReciprocalMoment.halfPhase q s) := by
  rw [prod_addChar_eq_addChar_sum]
  congr 1
  simp only [ReciprocalMoment.halfPhase, modularReciprocalSum]
  rw [Finset.mul_sum]

/-- Tuple expansion for a weighted reciprocal-character sum, with the
character product already grouped by the tuple's modular phase. -/
theorem weighted_reciprocalCharacter_sum_pow
    (q ell : ℕ) [NeZero q] (U : Finset ℕ)
    (beta : ℕ → ℂ) (c r : ZMod q) :
    (∑ s ∈ U,
        beta s * ZMod.stdAddChar (c * r⁻¹ * (s : ZMod q)⁻¹)) ^ ell =
      ∑ t ∈ ReciprocalMoment.halfTuples ell U,
        (∏ j, beta (t j)) *
          ZMod.stdAddChar
            (c * r⁻¹ * ReciprocalMoment.halfPhase q t) := by
  rw [sum_pow_eq_halfTuples_prod]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_mul_distrib,
    prod_stdAddChar_scaled_inv_eq_halfPhase]

/-- The same expansion regrouped into modular reciprocal-sum fibres. -/
theorem weighted_reciprocalCharacter_sum_pow_grouped
    (q ell : ℕ) [NeZero q] (U : Finset ℕ)
    (beta : ℕ → ℂ) (c r : ZMod q) :
    (∑ s ∈ U,
        beta s * ZMod.stdAddChar (c * r⁻¹ * (s : ZMod q)⁻¹)) ^ ell =
      ∑ u : ZMod q,
        AdditiveOrthogonality.residueFiberSum
            (ReciprocalMoment.halfTuples ell U)
            (ReciprocalMoment.halfPhase q)
            (fun t => ∏ j, beta (t j)) u *
          ZMod.stdAddChar (c * r⁻¹ * u) := by
  rw [weighted_reciprocalCharacter_sum_pow]
  exact (AdditiveOrthogonality.sum_residueFiberSum_mul
    (ReciprocalMoment.halfTuples ell U)
    (ReciprocalMoment.halfPhase q) (fun t => ∏ j, beta (t j))
    (fun u => ZMod.stdAddChar (c * r⁻¹ * u))).symm

/-- Phase-preserving grouped form of the absolute high moment.  The
coefficient `eta` is the unimodular factor denoted by the same letter in the
proof of BNPZ Lemma 9.2. -/
theorem exists_unimodular_norm_weighted_reciprocal_sum_pow_grouped
    (q ell : ℕ) [NeZero q] (U : Finset ℕ)
    (beta : ℕ → ℂ) (c r : ZMod q) :
    ∃ eta : ℂ, ‖eta‖ = 1 ∧
      ((‖∑ s ∈ U,
          beta s * ZMod.stdAddChar (c * r⁻¹ * (s : ZMod q)⁻¹)‖ ^ ell : ℝ) : ℂ) =
        eta *
          ∑ u : ZMod q,
            AdditiveOrthogonality.residueFiberSum
                (ReciprocalMoment.halfTuples ell U)
                (ReciprocalMoment.halfPhase q)
                (fun t => ∏ j, beta (t j)) u *
              ZMod.stdAddChar (c * r⁻¹ * u) := by
  obtain ⟨eta, heta, hpow⟩ := exists_unimodular_mul_pow_eq_norm_pow ell
    (∑ s ∈ U,
      beta s * ZMod.stdAddChar (c * r⁻¹ * (s : ZMod q)⁻¹))
  refine ⟨eta, heta, ?_⟩
  rw [hpow, weighted_reciprocalCharacter_sum_pow_grouped]

/-- A canonical (classically chosen) unimodular coefficient for the
phase-preserving high-moment expansion. -/
noncomputable def reciprocalEta
    (q ell : ℕ) [NeZero q] (U : Finset ℕ)
    (beta : ℕ → ℂ) (c r : ZMod q) : ℂ :=
  Classical.choose
    (exists_unimodular_norm_weighted_reciprocal_sum_pow_grouped
      q ell U beta c r)

theorem norm_reciprocalEta
    (q ell : ℕ) [NeZero q] (U : Finset ℕ)
    (beta : ℕ → ℂ) (c r : ZMod q) :
    ‖reciprocalEta q ell U beta c r‖ = 1 :=
  (Classical.choose_spec
    (exists_unimodular_norm_weighted_reciprocal_sum_pow_grouped
      q ell U beta c r)).1

theorem norm_weighted_reciprocal_sum_pow_grouped_eq
    (q ell : ℕ) [NeZero q] (U : Finset ℕ)
    (beta : ℕ → ℂ) (c r : ZMod q) :
    ((‖∑ s ∈ U,
        beta s * ZMod.stdAddChar (c * r⁻¹ * (s : ZMod q)⁻¹)‖ ^ ell : ℝ) : ℂ) =
      reciprocalEta q ell U beta c r *
        ∑ u : ZMod q,
          AdditiveOrthogonality.residueFiberSum
              (ReciprocalMoment.halfTuples ell U)
              (ReciprocalMoment.halfPhase q)
              (fun t => ∏ j, beta (t j)) u *
            ZMod.stdAddChar (c * r⁻¹ * u) :=
  (Classical.choose_spec
    (exists_unimodular_norm_weighted_reciprocal_sum_pow_grouped
      q ell U beta c r)).2

end HighMoment

end Erdos387

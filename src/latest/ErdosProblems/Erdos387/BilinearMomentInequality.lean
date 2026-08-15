/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.InversePhaseOrthogonality
import ErdosProblems.Erdos387.SubpowerModularMoment
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The finite Cauchy step in the bilinear moment argument

The frequency group varies with the outer modulus, so the correct common
index is a sigma type.  On that literal finite index set, the Cauchy--Schwarz
step in BNPZ Lemma 9.2 is the ordinary finite inequality.
-/

namespace Erdos387

open scoped BigOperators

namespace BilinearMoment

/-- All pairs consisting of an outer parameter and a complete additive
frequency for its modulus. -/
noncomputable def phaseIndex
    {I : Type*} [DecidableEq I]
    (S : Finset I) (modulus : I → ℕ) [∀ i, NeZero (modulus i)] :
    Finset (Σ i : I, ZMod (modulus i)) := by
  classical
  exact S.sigma fun _ => Finset.univ

theorem sum_norm_mul_sq_le_moments
    {I : Type*} [DecidableEq I]
    (S : Finset I) (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (nu rho : (i : I) → ZMod (modulus i) → ℂ) :
    (∑ i ∈ S, ∑ u : ZMod (modulus i), ‖nu i u‖ * ‖rho i u‖) ^ 2 ≤
      (∑ i ∈ S, ∑ u : ZMod (modulus i), ‖nu i u‖ ^ 2) *
        (∑ i ∈ S, ∑ u : ZMod (modulus i), ‖rho i u‖ ^ 2) := by
  classical
  have h := Finset.sum_mul_sq_le_sq_mul_sq (phaseIndex S modulus)
    (fun iu => ‖nu iu.1 iu.2‖) (fun iu => ‖rho iu.1 iu.2‖)
  rw [phaseIndex, Finset.sum_sigma, Finset.sum_sigma,
    Finset.sum_sigma] at h
  simpa using h

/-- Complex form: triangle inequality followed by the sigma-indexed
Cauchy--Schwarz inequality. -/
theorem norm_sum_mul_sq_le_moments
    {I : Type*} [DecidableEq I]
    (S : Finset I) (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (nu rho : (i : I) → ZMod (modulus i) → ℂ) :
    ‖∑ i ∈ S, ∑ u : ZMod (modulus i), nu i u * rho i u‖ ^ 2 ≤
      (∑ i ∈ S, ∑ u : ZMod (modulus i), ‖nu i u‖ ^ 2) *
        (∑ i ∈ S, ∑ u : ZMod (modulus i), ‖rho i u‖ ^ 2) := by
  calc
    ‖∑ i ∈ S, ∑ u : ZMod (modulus i), nu i u * rho i u‖ ^ 2 ≤
        (∑ i ∈ S, ∑ u : ZMod (modulus i),
          ‖nu i u‖ * ‖rho i u‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        ‖∑ i ∈ S, ∑ u : ZMod (modulus i), nu i u * rho i u‖ ≤
            ∑ i ∈ S, ‖∑ u : ZMod (modulus i), nu i u * rho i u‖ :=
          norm_sum_le _ _
        _ ≤ ∑ i ∈ S, ∑ u : ZMod (modulus i),
              ‖nu i u * rho i u‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact norm_sum_le _ _
        _ = ∑ i ∈ S, ∑ u : ZMod (modulus i),
              ‖nu i u‖ * ‖rho i u‖ := by
          simp only [norm_mul]
    _ ≤ _ := sum_norm_mul_sq_le_moments S modulus nu rho

/-- Ready-to-use Cauchy form when separate numerical bounds for the two
moments have already been proved. -/
theorem norm_sum_mul_sq_le_of_moment_bounds
    {I : Type*} [DecidableEq I]
    (S : Finset I) (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (nu rho : (i : I) → ZMod (modulus i) → ℂ)
    {A B : ℝ}
    (hnu : (∑ i ∈ S, ∑ u : ZMod (modulus i), ‖nu i u‖ ^ 2) ≤ A)
    (hrho : (∑ i ∈ S, ∑ u : ZMod (modulus i), ‖rho i u‖ ^ 2) ≤ B) :
    ‖∑ i ∈ S, ∑ u : ZMod (modulus i), nu i u * rho i u‖ ^ 2 ≤
      A * B := by
  have hnuNonneg :
      0 ≤ (∑ i ∈ S, ∑ u : ZMod (modulus i), ‖nu i u‖ ^ 2) := by
    positivity
  have hrhoNonneg :
      0 ≤ (∑ i ∈ S, ∑ u : ZMod (modulus i), ‖rho i u‖ ^ 2) := by
    positivity
  have hA : 0 ≤ A := hnuNonneg.trans hnu
  exact (norm_sum_mul_sq_le_moments S modulus nu rho).trans
    (mul_le_mul hnu hrho hrhoNonneg hA)

/-- The checked finite bilinear estimate obtained by inserting the
subpower `T₁` bound and the short-box complete-character `T₂` bound into
Cauchy--Schwarz.  This is the literal finite counterpart of the product
`T₁ T₂` in BNPZ (9.2); in particular, the `T₂` factor is the exact sum of
the varying moduli times the short-box cardinality. -/
theorem subpower_bilinear_character_cauchy
    {ell N k R : ℕ} (hk : 0 < k)
    (Q : Finset ℕ) (modulus frequency phaseScale : ℕ → ℕ)
    [∀ d, NeZero (modulus d)]
    (Sbox Rbox : Finset ℕ)
    (weightS : ℕ → (Fin ell → ℕ) → ℂ)
    (weightR : ℕ → ℕ → ℂ)
    (hN : SubpowerScale.reciprocalMomentThreshold k ell ≤ N)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (SubpowerScale.z N k) d)
    (hSpos : ∀ s ∈ Sbox, 0 < s)
    (hSle : ∀ s ∈ Sbox, s ≤ SubpowerScale.medium N k)
    (hSrough : ∀ s ∈ Sbox, IsZRough (SubpowerScale.z N k) s)
    (hScop : ∀ d ∈ Q, ∀ s ∈ Sbox, s.Coprime (modulus d))
    (hweightS : ∀ d ∈ Q,
      ∀ s ∈ ReciprocalMoment.halfTuples ell Sbox, ‖weightS d s‖ ≤ 1)
    (hmodPos : ∀ d ∈ Q, 0 < modulus d)
    (hscale : ∀ d ∈ Q, (phaseScale d).Coprime (modulus d))
    (hweightR : ∀ d ∈ Q, ∀ r ∈ Rbox, ‖weightR d r‖ ≤ 1)
    (hRcop : ∀ d ∈ Q, ∀ r ∈ Rbox, r.Coprime (modulus d))
    (hRle : ∀ r ∈ Rbox, r ≤ R)
    (hshort : ∀ d ∈ Q,
      R < modulus d / Nat.gcd (modulus d) (frequency d)) :
    ‖∑ d ∈ Q, ∑ u : ZMod (modulus d),
        AdditiveOrthogonality.residueFiberSum
            (ReciprocalMoment.halfTuples ell Sbox)
            (ReciprocalMoment.halfPhase (modulus d)) (weightS d) u *
          AdditiveOrthogonality.characterSum Rbox
            (InversePhase.phase (modulus d) (frequency d) (phaseScale d))
            (weightR d) u‖ ^ 2 ≤
      (((Q.card * SubpowerScale.medium N k ^ ell +
          Sbox.card ^ (2 * ell)) * SubpowerScale.base N k) *
        (∑ d ∈ Q, modulus d * Rbox.card) : ℕ) := by
  let nu : (d : ℕ) → ZMod (modulus d) → ℂ := fun d =>
    AdditiveOrthogonality.residueFiberSum
      (ReciprocalMoment.halfTuples ell Sbox)
      (ReciprocalMoment.halfPhase (modulus d)) (weightS d)
  let rho : (d : ℕ) → ZMod (modulus d) → ℂ := fun d =>
    AdditiveOrthogonality.characterSum Rbox
      (InversePhase.phase (modulus d) (frequency d) (phaseScale d))
      (weightR d)
  let A : ℝ := ((Q.card * SubpowerScale.medium N k ^ ell +
    Sbox.card ^ (2 * ell)) * SubpowerScale.base N k : ℕ)
  let B : ℝ := (∑ d ∈ Q, modulus d * Rbox.card : ℕ)
  have hnu :
      (∑ d ∈ Q, ∑ u : ZMod (modulus d), ‖nu d u‖ ^ 2) ≤ A := by
    simpa [nu, A] using
      SubpowerScale.sum_halfPhase_fibre_secondMoment_le_medium_mul_base
        hk Q modulus Sbox weightS hN hDmod hQrough hSpos hSle hSrough
          hScop hweightS
  have hrho :
      (∑ d ∈ Q, ∑ u : ZMod (modulus d), ‖rho d u‖ ^ 2) ≤ B := by
    simpa [rho, B] using
      InversePhase.sum_norm_characterSum_sq_le_short_box_family
        Q modulus frequency phaseScale R Rbox weightR hmodPos hscale
          hweightR hRcop hRle hshort
  have h := norm_sum_mul_sq_le_of_moment_bounds Q modulus nu rho hnu hrho
  simpa [nu, rho, A, B, Nat.cast_mul] using h

end BilinearMoment

end Erdos387

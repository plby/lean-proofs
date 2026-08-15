/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.AdditiveCharacterOrthogonality
import Mathlib.Data.ZMod.Coprime

/-!
# Orthogonality for a scaled inverse phase

This is the exact elementary cancellation used for the `T₂` factor in
BNPZ Lemma 9.2.  After complete additive-character orthogonality, equality
of two inverse phases forces the two short variables to be congruent modulo
`q / gcd q h`.  If that quotient is longer than the variable box, the two
variables are equal.
-/

namespace Erdos387

open scoped BigOperators ComplexConjugate

namespace InversePhase

/-- The scaled reciprocal phase `h a / r (mod q)`. -/
noncomputable def phase (q h a r : ℕ) : ZMod q :=
  (h : ZMod q) * (a : ZMod q) * (r : ZMod q)⁻¹

/-- Complete additive-character orthogonality for two scaled inverse
phases. -/
theorem sum_stdAddChar_phase_mul_conj
    (q h a r₁ r₂ : ℕ) [NeZero q] :
    ∑ u : ZMod q,
        ZMod.stdAddChar (u * phase q h a r₁) *
          conj (ZMod.stdAddChar (u * phase q h a r₂)) =
      if phase q h a r₁ = phase q h a r₂ then (q : ℂ) else 0 := by
  exact AdditiveOrthogonality.sum_stdAddChar_mul_conj q
    (phase q h a r₁) (phase q h a r₂)

/-- Equality of scaled inverse phases implies a congruence after cancelling
the possibly non-coprime frequency `h`. -/
theorem modEq_div_gcd_of_phase_eq
    {q h a r₁ r₂ : ℕ} (hq : 0 < q)
    (ha : a.Coprime q) (hr₁ : r₁.Coprime q) (hr₂ : r₂.Coprime q)
    (hphase : phase q h a r₁ = phase q h a r₂) :
    Nat.ModEq (q / Nat.gcd q h) r₁ r₂ := by
  have hcast :
      ((h * a * r₂ : ℕ) : ZMod q) = ((h * a * r₁ : ℕ) : ZMod q) := by
    calc
      ((h * a * r₂ : ℕ) : ZMod q) =
          phase q h a r₁ * (r₁ : ZMod q) * (r₂ : ZMod q) := by
        rw [phase]
        push_cast
        have hinv : (r₁ : ZMod q)⁻¹ * (r₁ : ZMod q) = 1 := by
          simpa [mul_comm] using ZMod.coe_mul_inv_eq_one r₁ hr₁
        calc
          (h : ZMod q) * a * r₂ = (h : ZMod q) * a * 1 * r₂ := by ring
          _ = (h : ZMod q) * a * ((r₁ : ZMod q)⁻¹ * r₁) * r₂ := by
            rw [hinv]
          _ = (h : ZMod q) * a * (r₁ : ZMod q)⁻¹ * r₁ * r₂ := by
            ring
      _ = phase q h a r₂ * (r₁ : ZMod q) * (r₂ : ZMod q) := by
        rw [hphase]
      _ = ((h * a * r₁ : ℕ) : ZMod q) := by
        rw [phase]
        push_cast
        have hinv : (r₂ : ZMod q)⁻¹ * (r₂ : ZMod q) = 1 := by
          simpa [mul_comm] using ZMod.coe_mul_inv_eq_one r₂ hr₂
        calc
          (h : ZMod q) * a * (r₂ : ZMod q)⁻¹ * r₁ * r₂ =
              (h : ZMod q) * a * r₁ * ((r₂ : ZMod q)⁻¹ * r₂) := by ring
          _ = (h : ZMod q) * a * r₁ := by rw [hinv]; ring
  have hmod : Nat.ModEq q (h * (a * r₂)) (h * (a * r₁)) := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa [mul_assoc] using hcast
  have hcancelH :
      Nat.ModEq (q / Nat.gcd q h) (a * r₂) (a * r₁) :=
    hmod.cancel_left_div_gcd hq
  have hquotDvd : q / Nat.gcd q h ∣ q :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q h)
  have hcop : Nat.Coprime (q / Nat.gcd q h) a :=
    Nat.Coprime.of_dvd_left hquotDvd ha.symm
  exact (hcancelH.cancel_left_of_coprime hcop.gcd_eq_one).symm

/-- If the reduced modulus is larger than the whole short-variable box,
orthogonality has only the literal diagonal `r₁ = r₂`. -/
theorem eq_of_phase_eq_of_le_of_lt_div_gcd
    {q h a r₁ r₂ R : ℕ} (hq : 0 < q)
    (ha : a.Coprime q) (hr₁ : r₁.Coprime q) (hr₂ : r₂.Coprime q)
    (hr₁R : r₁ ≤ R) (hr₂R : r₂ ≤ R)
    (hR : R < q / Nat.gcd q h)
    (hphase : phase q h a r₁ = phase q h a r₂) :
    r₁ = r₂ := by
  have hmod := modEq_div_gcd_of_phase_eq hq ha hr₁ hr₂ hphase
  exact hmod.eq_of_lt_of_lt (hr₁R.trans_lt hR) (hr₂R.trans_lt hR)

/-- In a box shorter than the reduced modulus, the inverse phase is
injective and its equal-phase pair set has at most the diagonal size. -/
theorem equalPhasePairs_card_le_short_box
    {q h a R : ℕ} (hq : 0 < q) (ha : a.Coprime q)
    (U : Finset ℕ) (hUcop : ∀ r ∈ U, r.Coprime q)
    (hUle : ∀ r ∈ U, r ≤ R) (hR : R < q / Nat.gcd q h) :
    (AdditiveOrthogonality.equalPhasePairs U (phase q h a)).card ≤
      U.card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro rs hrs
    change rs ∈ AdditiveOrthogonality.equalPhasePairs U (phase q h a) at hrs
    rw [AdditiveOrthogonality.equalPhasePairs, Finset.mem_filter,
      Finset.mem_product] at hrs
    exact hrs.1.1
  · intro rs hrs tu htu heq
    change rs ∈ AdditiveOrthogonality.equalPhasePairs U (phase q h a) at hrs
    change tu ∈ AdditiveOrthogonality.equalPhasePairs U (phase q h a) at htu
    rw [AdditiveOrthogonality.equalPhasePairs, Finset.mem_filter,
      Finset.mem_product] at hrs htu
    have hrsDiag : rs.1 = rs.2 :=
      eq_of_phase_eq_of_le_of_lt_div_gcd hq ha
        (hUcop rs.1 hrs.1.1) (hUcop rs.2 hrs.1.2)
        (hUle rs.1 hrs.1.1) (hUle rs.2 hrs.1.2) hR hrs.2
    have htuDiag : tu.1 = tu.2 :=
      eq_of_phase_eq_of_le_of_lt_div_gcd hq ha
        (hUcop tu.1 htu.1.1) (hUcop tu.2 htu.1.2)
        (hUle tu.1 htu.1.1) (hUle tu.2 htu.1.2) hR htu.2
    apply Prod.ext heq
    calc
      rs.2 = rs.1 := hrsDiag.symm
      _ = tu.1 := heq
      _ = tu.2 := htuDiag

/-- Fibre-coefficient second moment of a short scaled-inverse phase.  The
actual complete-frequency `T₂` estimate below is obtained from this count
by Parseval and therefore carries one factor of the modulus. -/
theorem sum_norm_residueFiberSum_sq_le_short_box
    {q h a R : ℕ} [NeZero q] (hq : 0 < q) (ha : a.Coprime q)
    (U : Finset ℕ) (weight : ℕ → ℂ)
    (hweight : ∀ r ∈ U, ‖weight r‖ ≤ 1)
    (hUcop : ∀ r ∈ U, r.Coprime q)
    (hUle : ∀ r ∈ U, r ≤ R) (hR : R < q / Nat.gcd q h) :
    (∑ u : ZMod q,
        ‖AdditiveOrthogonality.residueFiberSum U
          (phase q h a) weight u‖ ^ 2) ≤ (U.card : ℝ) := by
  exact (AdditiveOrthogonality.sum_norm_residueFiberSum_sq_le
    U (phase q h a) weight hweight).trans (by
      exact_mod_cast equalPhasePairs_card_le_short_box hq ha U hUcop hUle hR)

/-- The actual complete-frequency second moment of the inverse-phase
character sum.  In the short box only diagonal pairs survive, and Parseval
contributes the indispensable factor `q`. -/
theorem sum_norm_characterSum_sq_le_short_box
    {q h a R : ℕ} [NeZero q] (hq : 0 < q) (ha : a.Coprime q)
    (U : Finset ℕ) (weight : ℕ → ℂ)
    (hweight : ∀ r ∈ U, ‖weight r‖ ≤ 1)
    (hUcop : ∀ r ∈ U, r.Coprime q)
    (hUle : ∀ r ∈ U, r ≤ R) (hR : R < q / Nat.gcd q h) :
    (∑ u : ZMod q,
        ‖AdditiveOrthogonality.characterSum U
          (phase q h a) weight u‖ ^ 2) ≤ (q * U.card : ℕ) := by
  exact (AdditiveOrthogonality.sum_norm_characterSum_sq_le
    U (phase q h a) weight hweight).trans (by
      exact_mod_cast Nat.mul_le_mul_left q
        (equalPhasePairs_card_le_short_box hq ha U hUcop hUle hR))

/-- The fibre-energy estimate summed over an arbitrary finite outer
family.  This is the coefficient-side input to the complete-frequency
estimate below. -/
theorem sum_norm_residueFiberSum_sq_le_short_box_family
    {I : Type*} [DecidableEq I]
    (S : Finset I) (modulus frequency scale : I → ℕ)
    [∀ i, NeZero (modulus i)]
    (R : ℕ) (U : Finset ℕ) (weight : I → ℕ → ℂ)
    (hmodPos : ∀ i ∈ S, 0 < modulus i)
    (hscale : ∀ i ∈ S, (scale i).Coprime (modulus i))
    (hweight : ∀ i ∈ S, ∀ r ∈ U, ‖weight i r‖ ≤ 1)
    (hUcop : ∀ i ∈ S, ∀ r ∈ U, r.Coprime (modulus i))
    (hUle : ∀ r ∈ U, r ≤ R)
    (hshort : ∀ i ∈ S,
      R < modulus i / Nat.gcd (modulus i) (frequency i)) :
    (∑ i ∈ S, ∑ u : ZMod (modulus i),
        ‖AdditiveOrthogonality.residueFiberSum U
          (phase (modulus i) (frequency i) (scale i)) (weight i) u‖ ^ 2) ≤
      (S.card * U.card : ℕ) := by
  calc
    (∑ i ∈ S, ∑ u : ZMod (modulus i),
        ‖AdditiveOrthogonality.residueFiberSum U
          (phase (modulus i) (frequency i) (scale i)) (weight i) u‖ ^ 2) ≤
        ∑ _i ∈ S, (U.card : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact sum_norm_residueFiberSum_sq_le_short_box
        (hmodPos i hi) (hscale i hi) U (weight i) (hweight i hi)
          (hUcop i hi) hUle (hshort i hi)
    _ = (S.card * U.card : ℕ) := by simp

/-- The short-box `T₂` estimate summed over an arbitrary finite outer
family whose modulus, frequency, and coprime scale factor may vary.  The
right side retains the exact sum of the varying moduli. -/
theorem sum_norm_characterSum_sq_le_short_box_family
    {I : Type*} [DecidableEq I]
    (S : Finset I) (modulus frequency scale : I → ℕ)
    [∀ i, NeZero (modulus i)]
    (R : ℕ) (U : Finset ℕ) (weight : I → ℕ → ℂ)
    (hmodPos : ∀ i ∈ S, 0 < modulus i)
    (hscale : ∀ i ∈ S, (scale i).Coprime (modulus i))
    (hweight : ∀ i ∈ S, ∀ r ∈ U, ‖weight i r‖ ≤ 1)
    (hUcop : ∀ i ∈ S, ∀ r ∈ U, r.Coprime (modulus i))
    (hUle : ∀ r ∈ U, r ≤ R)
    (hshort : ∀ i ∈ S,
      R < modulus i / Nat.gcd (modulus i) (frequency i)) :
    (∑ i ∈ S, ∑ u : ZMod (modulus i),
        ‖AdditiveOrthogonality.characterSum U
          (phase (modulus i) (frequency i) (scale i)) (weight i) u‖ ^ 2) ≤
      ((∑ i ∈ S, modulus i * U.card : ℕ) : ℝ) := by
  calc
    (∑ i ∈ S, ∑ u : ZMod (modulus i),
        ‖AdditiveOrthogonality.characterSum U
          (phase (modulus i) (frequency i) (scale i)) (weight i) u‖ ^ 2) ≤
        ∑ i ∈ S, ((modulus i * U.card : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact sum_norm_characterSum_sq_le_short_box
        (hmodPos i hi) (hscale i hi) U (weight i) (hweight i hi)
          (hUcop i hi) hUle (hshort i hi)
    _ = ((∑ i ∈ S, modulus i * U.card : ℕ) : ℝ) := by
      push_cast
      rfl

end InversePhase

end Erdos387

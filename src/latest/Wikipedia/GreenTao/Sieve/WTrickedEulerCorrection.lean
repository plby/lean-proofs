import Wikipedia.GreenTao.Sieve.WTrickedLocalFactors
import Wikipedia.GreenTao.Sieve.ComplexEulerProductComparison
import Mathlib.NumberTheory.PrimeCounting

/-!
# The finite Euler correction at W-tricked primes

For `W = primorial w`, every arithmetic local factor at a prime `p ≤ w`
is one.  Relative to the universal zeta Euler model, its arithmetic/zeta
ratio is therefore the inverse zeta factor.  This file packages the exact
finite product of those inverses and compares it with the Selberg
normalization `(φ(W) / W)^m`.

The comparison is exact: the normalized correction is a finite product of
the ratios between the unshifted local model `(1 - p⁻¹)^m` and the shifted
Fourier-zeta local model.  Thus the only remaining small-prime asymptotic is
to show that these finitely many shifted model factors approach their
unshifted values in the chosen joint `w, R` regime.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Natural primes at most `w`, represented in the prime subtype used by
unordered Euler products. -/
def smallPrimeFinset (w : ℕ) : Finset Nat.Primes :=
  (Nat.primesLE w).attach.map
    ⟨fun p =>
        (⟨p.1, Nat.prime_of_mem_primesLE p.2⟩ :
          Nat.Primes),
      by
        intro p q hpq
        apply Subtype.ext
        exact congrArg (fun r : Nat.Primes => (r : ℕ)) hpq⟩

@[simp]
theorem mem_smallPrimeFinset {w : ℕ} {p : Nat.Primes} :
    p ∈ smallPrimeFinset w ↔ (p : ℕ) ≤ w := by
  constructor
  · intro hp
    rw [smallPrimeFinset, Finset.mem_map] at hp
    obtain ⟨q, _hq, hpq⟩ := hp
    have hval : (q : ℕ) = (p : ℕ) :=
      congrArg (fun r : Nat.Primes => (r : ℕ)) hpq
    rw [← hval]
    exact Nat.le_of_mem_primesLE q.2
  · intro hp
    have hmem :
        (p : ℕ) ∈ Nat.primesLE w :=
      Nat.mem_primesLE.mpr ⟨hp, p.prop⟩
    rw [smallPrimeFinset, Finset.mem_map]
    refine ⟨⟨(p : ℕ), hmem⟩, Finset.mem_attach _ _, ?_⟩
    apply Nat.Primes.coe_nat_injective
    rfl

/-- The product over prime subtypes agrees with the usual natural-prime
finset product. -/
theorem prod_smallPrimeFinset_eq_prod_primesLE
    {M : Type*} [CommMonoid M]
    (w : ℕ) (f : ℕ → M) :
    ∏ p ∈ smallPrimeFinset w, f p =
      ∏ p ∈ Nat.primesLE w, f p := by
  unfold smallPrimeFinset
  rw [Finset.prod_map]
  exact Finset.prod_attach _ f

/-- At every small prime, the exact W-tricked arithmetic factor is one. -/
theorem pairedFourierPrimeLocalFactor_wTricked_eq_one_of_small
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {w b : ℕ} (hwb : (primorial w).Coprime b)
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) {p : Nat.Primes}
    (hp : p ∈ smallPrimeFinset w) :
    pairedFourierPrimeLocalFactor R
        (fun q =>
          wTrickedAffineForm (primorial w) b (forms q))
        t u p = 1 := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  rw [pairedFourierPrimeLocalFactor]
  exact
    pairedFourierLocalFactor_wTricked_primorial_eq_one
      p.prop (mem_smallPrimeFinset.mp hp) hwb
      R forms t u

/-- Hence the arithmetic/zeta ratio at a small W-tricked prime is exactly
the inverse universal zeta-model factor. -/
theorem primeArithmeticZetaRatio_wTricked_eq_inv_of_small
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {w b : ℕ} (hwb : (primorial w).Coprime b)
    (R : ℕ)
    (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) {p : Nat.Primes}
    (hp : p ∈ smallPrimeFinset w) :
    primePairedFourierArithmeticToZetaLocalRatio R
        (fun q =>
          wTrickedAffineForm (primorial w) b (forms q))
        t u p =
      (cutoffZetaEulerLocalFactor R t u p)⁻¹ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  rw [primePairedFourierArithmeticToZetaLocalRatio,
    pairedFourierArithmeticToZetaLocalRatio,
    pairedFourierLocalFactor_wTricked_primorial_eq_one
      p.prop (mem_smallPrimeFinset.mp hp) hwb
      R forms t u,
    one_div,
    cutoffZetaEulerLocalFactor_eq_fourierZetaSystemEulerLocalFactor]

/-- The exact finite small-prime correction supplied by the zeta model. -/
noncomputable def smallPrimeZetaCorrection
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) : ℂ :=
  ∏ p ∈ smallPrimeFinset w,
    (cutoffZetaEulerLocalFactor R t u p)⁻¹

/-- The product of the actual arithmetic/zeta ratios at the omitted
W-tricked primes is exactly `smallPrimeZetaCorrection`. -/
theorem prod_smallPrimeArithmeticZetaRatio_wTricked_eq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {w b : ℕ} (hwb : (primorial w).Coprime b)
    (R : ℕ)
    (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    ∏ p ∈ smallPrimeFinset w,
        primePairedFourierArithmeticToZetaLocalRatio R
          (fun q =>
            wTrickedAffineForm (primorial w) b (forms q))
          t u p =
      smallPrimeZetaCorrection R w t u := by
  apply Finset.prod_congr rfl
  intro p hp
  exact primeArithmeticZetaRatio_wTricked_eq_inv_of_small
    hwb R forms t u hp

/-- The product of the exact arithmetic factors themselves is one on the
omitted small-prime range. -/
theorem prod_smallPrimeLocalFactor_wTricked_eq_one
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {w b : ℕ} (hwb : (primorial w).Coprime b)
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    ∏ p ∈ smallPrimeFinset w,
        pairedFourierPrimeLocalFactor R
          (fun q =>
            wTrickedAffineForm (primorial w) b (forms q))
          t u p = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  exact pairedFourierPrimeLocalFactor_wTricked_eq_one_of_small
    hwb R forms t u hp

/-! ## The parallel first-order correction -/

/-- Prime-indexed form of the arithmetic/first-order local ratio. -/
noncomputable def primePairedFourierArithmeticToFirstOrderLocalRatio
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (p : Nat.Primes) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact pairedFourierLocalRatio R (p : ℕ) forms t u

/-- At a small W-tricked prime, the arithmetic/first-order ratio is the
inverse first-order model factor. -/
theorem primeArithmeticFirstOrderRatio_wTricked_eq_inv_of_small
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {w b : ℕ} (hwb : (primorial w).Coprime b)
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) {p : Nat.Primes}
    (hp : p ∈ smallPrimeFinset w) :
    primePairedFourierArithmeticToFirstOrderLocalRatio R
        (fun q =>
          wTrickedAffineForm (primorial w) b (forms q))
        t u p =
      (pairedFourierFirstOrderLocalModel
        R (p : ℕ) t u)⁻¹ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  rw [primePairedFourierArithmeticToFirstOrderLocalRatio,
    pairedFourierLocalRatio,
    pairedFourierLocalFactor_wTricked_primorial_eq_one
      p.prop (mem_smallPrimeFinset.mp hp) hwb
      R forms t u,
    one_div]

/-- Exact product of the omitted first-order model factors. -/
noncomputable def smallPrimeFirstOrderCorrection
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) : ℂ :=
  ∏ p ∈ smallPrimeFinset w,
    (pairedFourierFirstOrderLocalModel
      R (p : ℕ) t u)⁻¹

/-- The finite product of the W-tricked arithmetic/first-order ratios is
the inverse product of the omitted first-order factors. -/
theorem prod_smallPrimeArithmeticFirstOrderRatio_wTricked_eq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {w b : ℕ} (hwb : (primorial w).Coprime b)
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    ∏ p ∈ smallPrimeFinset w,
        primePairedFourierArithmeticToFirstOrderLocalRatio R
          (fun q =>
            wTrickedAffineForm (primorial w) b (forms q))
          t u p =
      smallPrimeFirstOrderCorrection R w t u := by
  apply Finset.prod_congr rfl
  intro p hp
  exact
    primeArithmeticFirstOrderRatio_wTricked_eq_inv_of_small
      hwb R forms t u hp

/-! ## Exact comparison with the totient normalization -/

/-- The density of reduced residues for the standard primorial W-trick,
viewed in `ℂ`. -/
noncomputable def primorialReducedResidueDensity (w : ℕ) : ℂ :=
  ((primorial w).totient : ℂ) / (primorial w : ℂ)

/-- Euler's totient product formula for a primorial, in the exact complex
form used by the Fourier-zeta factors. -/
theorem primorialReducedResidueDensity_eq_prod
    (w : ℕ) :
    primorialReducedResidueDensity w =
      ∏ p ∈ smallPrimeFinset w,
        (1 - (p : ℂ)⁻¹) := by
  have hW : primorial w ≠ 0 :=
    (primorial_pos w).ne'
  have hq :
      (((primorial w).totient : ℚ) /
          (primorial w : ℚ)) =
        ∏ p ∈ Nat.primesLE w,
          (1 - (p : ℚ)⁻¹) := by
    rw [Nat.totient_eq_mul_prod_factors (primorial w),
      primeFactors_primorial]
    have hWq : (primorial w : ℚ) ≠ 0 := by
      exact_mod_cast hW
    field_simp [hWq]
  have hprod :
      (∏ p ∈ smallPrimeFinset w,
          (1 - (p : ℂ)⁻¹)) =
        ∏ p ∈ Nat.primesLE w,
          (1 - (p : ℂ)⁻¹) := by
    rw [smallPrimeFinset, Finset.prod_map]
    exact Finset.prod_attach
      (Nat.primesLE w)
      (fun p : ℕ => 1 - (p : ℂ)⁻¹)
  rw [primorialReducedResidueDensity, hprod]
  have hc :=
    congrArg (algebraMap ℚ ℂ) hq
  simpa using hc

/-- The unshifted zeta local factor for a system of `m` paired forms. -/
noncomputable def unshiftedZetaSystemLocalFactor
    (m p : ℕ) : ℂ :=
  (1 - (p : ℂ)⁻¹) ^ m

/-- The `m`th power of the primorial reduced-residue density is exactly the
product of the unshifted system local factors. -/
theorem primorialReducedResidueDensity_pow_eq_prod
    (w m : ℕ) :
    primorialReducedResidueDensity w ^ m =
      ∏ p ∈ smallPrimeFinset w,
        unshiftedZetaSystemLocalFactor m p := by
  rw [primorialReducedResidueDensity_eq_prod]
  exact
    (Finset.prod_pow (smallPrimeFinset w) m
      (fun p : Nat.Primes =>
        1 - (p : ℂ)⁻¹)).symm

/-- The inverse reduced-residue density is the familiar `W / φ(W)`
factor. -/
theorem primorialReducedResidueDensity_inv
    (w : ℕ) :
    (primorialReducedResidueDensity w)⁻¹ =
      (primorial w : ℂ) /
        ((primorial w).totient : ℂ) := by
  rw [primorialReducedResidueDensity, inv_div]

/-- Product of the inverses of the unshifted small-prime model factors. -/
noncomputable def unshiftedSmallPrimeZetaCorrection
    (w m : ℕ) : ℂ :=
  ∏ p ∈ smallPrimeFinset w,
    (unshiftedZetaSystemLocalFactor m p)⁻¹

/-- The unshifted correction is exactly `(W / φ(W))^m`. -/
theorem unshiftedSmallPrimeZetaCorrection_eq
    (w m : ℕ) :
    unshiftedSmallPrimeZetaCorrection w m =
      ((primorial w : ℂ) /
        ((primorial w).totient : ℂ)) ^ m := by
  rw [unshiftedSmallPrimeZetaCorrection,
    Finset.prod_inv_distrib,
    ← primorialReducedResidueDensity_pow_eq_prod,
    ← inv_pow, primorialReducedResidueDensity_inv]

/-! ## The unshifted phase model -/

/-- At unit phases, one paired zeta factor is exactly `1 - p⁻¹`. -/
theorem phasePairZetaEulerLocalModel_one_one
    {p : ℕ} (hp : p.Prime) :
    phasePairZetaEulerLocalModel p 1 1 =
      1 - (p : ℂ)⁻¹ := by
  have hne :
      1 - (p : ℂ)⁻¹ ≠ 0 := by
    simpa using
      phaseZetaNumerator_ne_zero hp
        (z := (1 : ℂ)) (by simp)
  rw [phasePairZetaEulerLocalModel]
  simp only [mul_one]
  field_simp [hne]

/-- The unit-phase system factor is the unshifted model used in the
totient product. -/
theorem phaseZetaSystemEulerLocalFactor_one_one
    {κ : Type*} [Fintype κ]
    {p : ℕ} (hp : p.Prime) :
    phaseZetaSystemEulerLocalFactor p
        (fun _ : κ => 1) (fun _ : κ => 1) =
      unshiftedZetaSystemLocalFactor
        (Fintype.card κ) p := by
  rw [phaseZetaSystemEulerLocalFactor,
    unshiftedZetaSystemLocalFactor]
  simp_rw [phasePairZetaEulerLocalModel_one_one hp]
  simp

/-- The unshifted system local factor is nonzero at every prime. -/
theorem unshiftedZetaSystemLocalFactor_ne_zero
    {m p : ℕ} (hp : p.Prime) :
    unshiftedZetaSystemLocalFactor m p ≠ 0 := by
  rw [unshiftedZetaSystemLocalFactor]
  apply pow_ne_zero
  simpa using
    phaseZetaNumerator_ne_zero hp
      (z := (1 : ℂ)) (by simp)

/-- The model residual would be exactly one if all shifted phases were
replaced by their limiting value one. -/
theorem prod_unshifted_mul_inv_phaseUnit_eq_one
    {κ : Type*} [Fintype κ]
    (w : ℕ) :
    ∏ p ∈ smallPrimeFinset w,
        (unshiftedZetaSystemLocalFactor
            (Fintype.card κ) p *
          (phaseZetaSystemEulerLocalFactor (p : ℕ)
            (fun _ : κ => 1) (fun _ : κ => 1))⁻¹) =
      1 := by
  apply Finset.prod_eq_one
  intro p _hp
  rw [phaseZetaSystemEulerLocalFactor_one_one p.prop]
  exact mul_inv_cancel₀
    (unshiftedZetaSystemLocalFactor_ne_zero p.prop)

/-- At the actual cutoff shifts, the universal zeta factor is the phase
system evaluated at the divisor multiplicative phases. -/
theorem cutoffZetaEulerLocalFactor_eq_phaseSystem
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) (p : Nat.Primes) :
    cutoffZetaEulerLocalFactor R t u p =
      phaseZetaSystemEulerLocalFactor (p : ℕ)
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q))
        (fun q =>
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q)) := by
  rw [cutoffZetaEulerLocalFactor_eq_fourierZetaSystemEulerLocalFactor]
  exact fourierZetaSystemEulerLocalFactor_eq_phase
    (by omega) p.prop t u

/-- The finite correction after inserting the actual Selberg
normalization `(φ(W)/W)^m`. -/
noncomputable def normalizedSmallPrimeZetaCorrection
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) : ℂ :=
  primorialReducedResidueDensity w ^ Fintype.card κ *
    smallPrimeZetaCorrection R w t u

/-- Exact residual identity: the normalized small-prime correction is a
finite product of unshifted model factors divided by the exact shifted
zeta factors. -/
theorem normalizedSmallPrimeZetaCorrection_eq_prod_residual
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) :
    normalizedSmallPrimeZetaCorrection R w t u =
      ∏ p ∈ smallPrimeFinset w,
        (unshiftedZetaSystemLocalFactor
            (Fintype.card κ) p *
          (cutoffZetaEulerLocalFactor R t u p)⁻¹) := by
  rw [normalizedSmallPrimeZetaCorrection,
    primorialReducedResidueDensity_pow_eq_prod,
    smallPrimeZetaCorrection,
    ← Finset.prod_mul_distrib]

/-- Phase-coordinate form of the exact residual.  Together with
`prod_unshifted_mul_inv_phaseUnit_eq_one`, this isolates the remaining
asymptotic as convergence of the displayed cutoff phases to one. -/
theorem normalizedSmallPrimeZetaCorrection_eq_phaseResidual
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (w : ℕ) (t u : κ → ℝ) :
    normalizedSmallPrimeZetaCorrection R w t u =
      ∏ p ∈ smallPrimeFinset w,
        (unshiftedZetaSystemLocalFactor
            (Fintype.card κ) p *
          (phaseZetaSystemEulerLocalFactor (p : ℕ)
            (fun q =>
              SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (t q))
            (fun q =>
              SmoothSieveCutoff.divisorMultiplicativePhase
                R (p : ℕ) (u q)))⁻¹) := by
  rw [normalizedSmallPrimeZetaCorrection_eq_prod_residual]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [cutoffZetaEulerLocalFactor_eq_phaseSystem hR]

/-- The same exact residual identity stated directly for the product of
the actual W-tricked arithmetic/zeta ratios. -/
theorem density_pow_mul_prod_smallPrimeArithmeticZetaRatio_eq_residual
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {w b : ℕ} (hwb : (primorial w).Coprime b)
    (R : ℕ)
    (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    primorialReducedResidueDensity w ^ Fintype.card κ *
        ∏ p ∈ smallPrimeFinset w,
          primePairedFourierArithmeticToZetaLocalRatio R
            (fun q =>
              wTrickedAffineForm (primorial w) b (forms q))
            t u p =
      ∏ p ∈ smallPrimeFinset w,
        (unshiftedZetaSystemLocalFactor
            (Fintype.card κ) p *
          (cutoffZetaEulerLocalFactor R t u p)⁻¹) := by
  rw [prod_smallPrimeArithmeticZetaRatio_wTricked_eq
    hwb R forms t u]
  exact normalizedSmallPrimeZetaCorrection_eq_prod_residual
    R w t u

end Wikipedia.SzemeredisTheorem

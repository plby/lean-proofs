import Wikipedia.GreenTao.AsymptoticAssembly
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Green--Tao assembly along cofinal prime moduli

The transference layer uses invertibility of the nonzero progression
coefficients and therefore naturally assumes that the cyclic modulus is
coprime to `(k - 1)!`.  Choosing an arbitrarily large prime modulus larger
than `k` supplies that hypothesis.  The previous assembly-facing predicate
asked for a count lower bound at *every* sufficiently large modulus, which
was stronger than both the proof and the transference theorem require.

This file records the exact cofinal prime-modulus interface.  Cofinality is
enough for diagonal exclusion because the logarithmic diagonal estimate is
eventual: simply choose the prime modulus after its threshold.  The
Chebyshev reduced-residue argument also holds at every sufficiently large
modulus, so it restricts to the same cofinal prime family without loss.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter

/-! ## Cofinal prime count lower bounds -/

/-- The exact count output needed along arbitrarily large prime cyclic
moduli.  All W-trick parameters and the positive count lower bound are
fixed before the lower bound on the modulus is supplied. -/
def HasCofinalPrimeWTrickedPrimeProgressionCountLower : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (α : ℝ) (W : ℕ) (c : ℝ),
      0 < α ∧ 0 < W ∧ 0 < c ∧
        ∀ M₀ : ℕ,
          ∃ M : ℕ,
            M₀ ≤ M ∧ Nat.Prime (M + 1) ∧
              ∃ b : ℕ, b < W ∧
                c ≤
                  cyclicAPCount k (M + 1)
                    (wTrickedPrimeWeight α W b)

/-- The former eventual-all-moduli interface implies the cofinal prime
interface.  This is mainly a compatibility theorem; the converse is neither
needed nor mathematically expected. -/
theorem HasEventuallyWTrickedPrimeProgressionCountLower.toCofinalPrime
    (hcount : HasEventuallyWTrickedPrimeProgressionCountLower) :
    HasCofinalPrimeWTrickedPrimeProgressionCountLower := by
  intro k hk
  obtain ⟨α, W, c, hα, hW, hc, heventual⟩ :=
    hcount k hk
  rw [eventually_atTop] at heventual
  obtain ⟨Mcount, hcountFrom⟩ := heventual
  refine ⟨α, W, c, hα, hW, hc, ?_⟩
  intro M₀
  obtain ⟨p, hpLarge, hpPrime⟩ :=
    Nat.exists_infinite_primes (max M₀ Mcount + 1)
  let M := p - 1
  have hpPos : 0 < p := hpPrime.pos
  have hMsucc : M + 1 = p := by
    dsimp [M]
    omega
  have hM₀ : M₀ ≤ M := by
    dsimp [M]
    omega
  have hMcount : Mcount ≤ M := by
    dsimp [M]
    omega
  obtain ⟨b, hb, hcountLower⟩ :=
    hcountFrom M hMcount
  exact
    ⟨M, hM₀, by simpa only [hMsucc] using hpPrime,
      b, hb, hcountLower⟩

/-- Cofinal positive count lower bounds imply positive off-diagonal
progression mass.  The selected prime is taken beyond the logarithmic
height threshold and the elementary `W+b≤N` threshold. -/
theorem HasCofinalPrimeWTrickedPrimeProgressionCountLower.toMass
    (hcount :
      HasCofinalPrimeWTrickedPrimeProgressionCountLower) :
    HasPrimeProgressionMass := by
  intro k hk
  obtain ⟨α, W, c, hα, hW, hc, hcofinal⟩ :=
    hcount k hk
  have heventualHeight :=
    eventually_wTrickedPrimeWeight_height_pow_lt_linear
      α c k hc
  rw [eventually_atTop] at heventualHeight
  obtain ⟨Nheight, hheightFrom⟩ := heventualHeight
  obtain ⟨M, hMlarge, _hprime, b, hb, hcountLower⟩ :=
    hcofinal (max (2 * W) Nheight)
  have htwoW : 2 * W ≤ M :=
    (le_max_left (2 * W) Nheight).trans hMlarge
  have hNheight : Nheight ≤ M + 1 :=
    (le_max_right (2 * W) Nheight).trans
      (hMlarge.trans (Nat.le_succ M))
  have hWB : W + b ≤ M + 1 := by
    omega
  have hheight :
      (2 * α * Real.log ((M + 1 : ℕ) : ℝ)) ^ k <
        ((M + 1 : ℕ) : ℝ) * c :=
    hheightFrom (M + 1) hNheight
  refine ⟨M, α, W, b, hα, hW, ?_⟩
  exact
    wTrickedPrimeWeight_offDiagMass_pos_of_count_lower
      (by omega) hα.le hW (by omega) hWB
      hcountLower hheight

/-- Final benchmark assembly from the cofinal prime-modulus count
interface. -/
theorem containsArbitraryAPs_primes_of_cofinal_prime_count_lower
    (hcount :
      HasCofinalPrimeWTrickedPrimeProgressionCountLower) :
    SzemeredisTheorem.ContainsArbitraryAPs
      {p : ℕ | Nat.Prime p} :=
  containsArbitraryAPs_primes_of_mass hcount.toMass

/-! ## Standard cutoff and reduced-residue selection -/

/-- Uniform transference at cofinally many prime moduli.  The modulus may
depend on the requested lower bound, but the estimate is uniform over every
standard residue `b<W` meeting the density hypothesis. -/
def CofinalPrimeUniformWTrickedPrimeProgressionCount
    (k : ℕ) (α : ℝ) (W : ℕ) (δ c : ℝ) : Prop :=
  ∀ M₀ : ℕ,
    ∃ M : ℕ,
      M₀ ≤ M ∧ Nat.Prime (M + 1) ∧
        ∀ b : ℕ, b < W →
          δ ≤
            mean
              (wTrickedPrimeWeight α W b :
                ZMod (M + 1) → ℝ) →
          c ≤
            cyclicAPCount k (M + 1)
              (wTrickedPrimeWeight α W b)

/-- The sole standard-cutoff transference obligation with the correct
prime-modulus quantifier. -/
def HasCofinalPrimeStandardWTrickedPrimeProgressionCounts : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (w : ℕ) (c : ℝ), 0 < c ∧
      CofinalPrimeUniformWTrickedPrimeProgressionCount
        k
        (primeScale k
          standardSmoothSieveCutoff.normalizer)
        (primorial w)
        (densityTarget k
          standardSmoothSieveCutoff.normalizer)
        c

/-- Cofinal prime-modulus transference, combined with the already proved
Chebyshev density selection, gives the cofinal count-lower-bound interface.
-/
theorem HasCofinalPrimeStandardWTrickedPrimeProgressionCounts.toCountLower
    (htransfer :
      HasCofinalPrimeStandardWTrickedPrimeProgressionCounts) :
    HasCofinalPrimeWTrickedPrimeProgressionCountLower := by
  intro k hk
  obtain ⟨w, c, hc, htransferCofinal⟩ :=
    htransfer k hk
  refine
    ⟨primeScale k standardSmoothSieveCutoff.normalizer,
      primorial w, c,
      primeScale_pos hk
        standardSmoothSieveCutoff_normalizer_pos,
      primorial_pos w, hc, ?_⟩
  have hdensity :=
    eventually_exists_reducedResidue_mean_ge_densityTarget_succ
      (w := w) hk
  rw [eventually_atTop] at hdensity
  obtain ⟨Mdensity, hdensityFrom⟩ := hdensity
  intro M₀
  obtain ⟨M, hMlarge, hprime, htransferM⟩ :=
    htransferCofinal (max M₀ Mdensity)
  have hM₀ : M₀ ≤ M :=
    (le_max_left M₀ Mdensity).trans hMlarge
  have hMdensity : Mdensity ≤ M :=
    (le_max_right M₀ Mdensity).trans hMlarge
  obtain ⟨b, hb, hmean⟩ :=
    hdensityFrom M hMdensity
  exact
    ⟨M, hM₀, hprime, b, hb,
      htransferM b hb hmean⟩

/-- Benchmark-facing endpoint using only the cofinal prime-modulus
transference statement. -/
theorem containsArbitraryAPs_primes_of_standard_cofinal_prime_counts
    (htransfer :
      HasCofinalPrimeStandardWTrickedPrimeProgressionCounts) :
    SzemeredisTheorem.ContainsArbitraryAPs
      {p : ℕ | Nat.Prime p} :=
  containsArbitraryAPs_primes_of_cofinal_prime_count_lower
    htransfer.toCountLower

end Wikipedia.SzemeredisTheorem

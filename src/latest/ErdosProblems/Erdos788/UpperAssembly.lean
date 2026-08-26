import ErdosProblems.Erdos788.EveryNFinite
import ErdosProblems.Erdos788.ExtractorInterface
import ErdosProblems.Erdos788.TrevisanParameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite assembly of the upper-bound construction

This file composes the checked extractor, kernel-palette, carry, and
normalization interfaces.  No asymptotic parameter choices are made here.
-/

namespace Erdos788

/-- The exact two-term upper bound before removing the ceiling logarithms. -/
def trevisanFiniteUpperBound (p r D : ℕ) : ℕ :=
  2 ^ (2 * r) * p ^ (r + trevisanSeedExponent p D) +
    p ^ (r + trevisanSlackExponent p r D)

/-- Both ceiling logarithms cost at most one factor of `p`; after factoring,
all remaining losses are displayed explicitly. -/
theorem trevisanFiniteUpperBound_le {p r D : ℕ}
    (hp : 1 < p) (hr : 0 < r) :
    trevisanFiniteUpperBound p r D ≤
      p ^ r * p * 2 ^ D *
        (2 ^ (2 * r) + 40 * r * (3200 * p ^ 2 * r ^ 2 + 1)) := by
  have hd := pow_seedExponent_le (p := p) (D := D) hp
  have hs := pow_slackExponent_le (p := p) (r := r) (D := D) hp hr
  rw [trevisanFiniteUpperBound, Nat.pow_add, Nat.pow_add]
  calc
    2 ^ (2 * r) * (p ^ r * p ^ trevisanSeedExponent p D) +
        p ^ r * p ^ trevisanSlackExponent p r D ≤
      2 ^ (2 * r) * (p ^ r * (p * 2 ^ D)) +
        p ^ r * (p * trevisanSlackThreshold p r D) := by
          exact Nat.add_le_add
            (Nat.mul_le_mul_left (2 ^ (2 * r))
              (Nat.mul_le_mul_left (p ^ r) hd))
            (Nat.mul_le_mul_left (p ^ r) hs)
    _ = p ^ r * p * 2 ^ D *
        (2 ^ (2 * r) + 40 * r * (3200 * p ^ 2 * r ^ 2 + 1)) := by
          rw [trevisanSlackThreshold]
          ring

/-- A simpler multiplicative majorant, convenient for taking logarithms. -/
theorem trevisanFiniteUpperBound_le_monomial {p r D : ℕ}
    (hp : 2 < p) (hr : 0 < r) :
    trevisanFiniteUpperBound p r D ≤
      130000 * p ^ (r + 3) * 2 ^ (D + 2 * r) * r ^ 3 := by
  have hbase := trevisanFiniteUpperBound_le (p := p) (r := r) (D := D)
    (by omega) hr
  have hpr0 : 0 < p ^ 2 * r ^ 2 := by positivity
  have hpr : 1 ≤ p ^ 2 * r ^ 2 := by omega
  have hinner : 3200 * p ^ 2 * r ^ 2 + 1 ≤
      3201 * p ^ 2 * r ^ 2 := by
    nlinarith
  have hpoly : 40 * r * (3200 * p ^ 2 * r ^ 2 + 1) ≤
      128040 * p ^ 2 * r ^ 3 := by
    calc
      40 * r * (3200 * p ^ 2 * r ^ 2 + 1) ≤
          40 * r * (3201 * p ^ 2 * r ^ 2) :=
        Nat.mul_le_mul_left (40 * r) hinner
      _ = 128040 * p ^ 2 * r ^ 3 := by ring
  have hunit0 : 0 < p ^ 2 * r ^ 3 := by positivity
  have hunit : 1 ≤ p ^ 2 * r ^ 3 := by omega
  have htwo : 2 ^ (2 * r) ≤
      2 ^ (2 * r) * p ^ 2 * r ^ 3 := by
    simpa [mul_assoc] using! Nat.mul_le_mul_left (2 ^ (2 * r)) hunit
  have hbracket :
      2 ^ (2 * r) + 40 * r * (3200 * p ^ 2 * r ^ 2 + 1) ≤
        130000 * 2 ^ (2 * r) * p ^ 2 * r ^ 3 := by
    calc
      2 ^ (2 * r) + 40 * r * (3200 * p ^ 2 * r ^ 2 + 1) ≤
          2 ^ (2 * r) * p ^ 2 * r ^ 3 +
            128040 * p ^ 2 * r ^ 3 := Nat.add_le_add htwo hpoly
      _ ≤ 130000 * 2 ^ (2 * r) * p ^ 2 * r ^ 3 := by
        have hpow0 : 0 < 2 ^ (2 * r) := by positivity
        have hpow : 1 ≤ 2 ^ (2 * r) := by omega
        nlinarith
  calc
    trevisanFiniteUpperBound p r D ≤
        p ^ r * p * 2 ^ D *
          (2 ^ (2 * r) + 40 * r * (3200 * p ^ 2 * r ^ 2 + 1)) := hbase
    _ ≤ p ^ r * p * 2 ^ D *
          (130000 * 2 ^ (2 * r) * p ^ 2 * r ^ 3) :=
      Nat.mul_le_mul_left (p ^ r * p * 2 ^ D) hbracket
    _ = 130000 * p ^ (r + 3) * 2 ^ (D + 2 * r) * r ^ 3 := by
      rw [Nat.pow_add, Nat.pow_add]
      ring

/-- A linear extractor family gives an ordinary normalized palette on every
shorter initial interval, with the exact carry and kernel bounds exposed. -/
theorem exists_normalizedPalette_of_linearExtractorFamily
    {p r d s N : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hN : N ≤ p ^ (2 * r))
    (E : LinearExtractorFamily p r d s) :
    ∃ B : Finset ℕ,
      B ⊆ attainableNormalizedSums N ∧
      B.card ≤ 2 ^ (2 * r) * p ^ (r + d) ∧
      (sumGraph N B).indepNum ≤ p ^ (r + s) := by
  obtain ⟨S, hScard, hSind⟩ :=
    kernelPalette_of_linearExtractorFamily hp hr E
  obtain ⟨B, hBatt, hBcard, hBind⟩ :=
    carry_lift_restrict p (2 * r) N (by omega) hN S
  refine ⟨B, hBatt, hBcard.trans ?_, hBind.trans ?_⟩
  · exact Nat.mul_le_mul_left (2 ^ (2 * r)) hScard
  · exact Nat.le_of_lt hSind

/-- Exact finite upper bound for the original Erdős min--max function,
before choosing the asymptotic parameters. -/
theorem fNat_succ_le_of_linearExtractorFamily
    {p r d s N : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hN : N ≤ p ^ (2 * r))
    (E : LinearExtractorFamily p r d s) :
    fNat (N + 1) ≤
      2 ^ (2 * r) * p ^ (r + d) + p ^ (r + s) := by
  obtain ⟨B, hBatt, hBcard, hBind⟩ :=
    exists_normalizedPalette_of_linearExtractorFamily hp hr hN E
  have hf := fNat_le_of_normalized_palette (N + 1) B (by
    simpa using! hBatt)
  exact hf.trans (Nat.add_le_add hBcard hBind)

/-- Specialized form for the canonical integral Trevisan exponents. -/
theorem fNat_succ_le_of_trevisanFamily
    {p r D N : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r) (hN : N ≤ p ^ (2 * r))
    (E : LinearExtractorFamily p r
      (trevisanSeedExponent p D) (trevisanSlackExponent p r D)) :
    fNat (N + 1) ≤ trevisanFiniteUpperBound p r D := by
  exact fNat_succ_le_of_linearExtractorFamily hp hr hN E

end Erdos788

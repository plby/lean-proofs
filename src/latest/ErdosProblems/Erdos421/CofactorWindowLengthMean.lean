import ErdosProblems.Erdos421.CofactorWindowErrors
import ErdosProblems.Erdos421.CanonicalPrimeSieveMean
import ErdosProblems.Erdos421.RoughWindowComparison

/-! # An unconditional additive comparison for the actual large-prime cofactor window -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem additivePrimeCofactorWindow_length_mean {k : ℕ} (hk : 0 < k) (A : ℝ)
    {ε τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ X : ℕ in atTop, ∀ Q D z w : ℕ, 0 < Q → 0 < D → 2 ≤ z → 0 < w →
      Q * (z * D ^ 2) < w ^ k →
      ((Q * (z * D ^ 2) : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ w ≤ p ∧ p ≤ Q) →
      ∀ (Y u v : ℝ) (B : ℕ), (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y →
      0 ≤ u → u ≤ v → v - u ≤ X → v + Y ≤ B →
      (∫ x in u..v, |additivePrimeCofactorWindow P B z Y x -
        (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z| ^ 2) ≤
          3 * (v - u) * (ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z) ^ 2 +
            τ * X / (Real.log X) ^ A := by
  have hτ6 : 0 < τ / 6 := by positivity
  filter_upwards [eventually_ge_atTop 1, canonicalPrimeUpper_window_mean hk A hτ6,
    canonicalPrimeLower_window_mean hk A hτ6] with X hX hU hL
  intro Q D z w hQ hD hz hw hcut hMX hlevel P hP Y u v B hY hu huv hlen hB
  have hYpos : 0 < Y := (Real.rpow_pos_of_pos (by exact_mod_cast hX) _).trans_le hY
  have hsub : Q * D ^ 2 ≤ Q * (z * D ^ 2) := Nat.mul_le_mul_left Q
    (Nat.le_mul_of_pos_left (D ^ 2) (by omega : 0 < z))
  have hUX : ((Q * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) :=
    le_trans (by exact_mod_cast hsub) hMX
  have hPprime : ∀ p ∈ P, p.Prime ∧ w ≤ p := fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.1⟩
  have hPbounds : ∀ p ∈ P, 0 < p ∧ p ≤ Q := fun p hp ↦ ⟨(hP p hp).1.pos, (hP p hp).2.2⟩
  have hbU := hU Q D z w hQ hD hw (hsub.trans_lt hcut) hUX P hPprime Y u v hY huv hlen
  have hbL := hL Q D z w hQ hD (by omega) hw hcut hMX P hPprime Y u v hY huv hlen
  have hb := additivePrimeCofactorWindow_mean_square_errors P hPbounds hD hz hε hε1 hlevel
    hYpos hu huv hB
  apply hb.trans
  calc
    _ ≤ 3 * (v - u) * (ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z) ^ 2 +
        3 * (τ / 6 * X / (Real.log X) ^ A) + 3 * (τ / 6 * X / (Real.log X) ^ A) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbU (by norm_num)))
        (mul_le_mul_of_nonneg_left hbL (by norm_num))
    _ = _ := by ring

theorem additivePrimeCofactorWindow_length_comparison {k : ℕ} (hk : 0 < k) (A : ℝ)
    {ε τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ X : ℕ in atTop, ∀ Q D z w : ℕ, 0 < Q → 0 < D → 2 ≤ z → 0 < w →
      Q * (z * D ^ 2) < w ^ k →
      ((Q * (z * D ^ 2) : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ w ≤ p ∧ p ≤ Q) →
      ∀ (Y₁ Y₂ u v : ℝ) (B : ℕ), (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y₁ →
      (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y₂ →
      0 ≤ u → u ≤ v → v - u ≤ X → v + Y₁ ≤ B → v + Y₂ ≤ B →
      (∫ x in u..v, |additivePrimeCofactorWindow P B z Y₁ x -
        additivePrimeCofactorWindow P B z Y₂ x| ^ 2) ≤
          12 * (v - u) * (ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z) ^ 2 +
            τ * X / (Real.log X) ^ A := by
  filter_upwards [additivePrimeCofactorWindow_length_mean hk A hε hε1
    (by positivity : 0 < τ / 4)] with X hX
  intro Q D z w hQ hD hz hw hcut hMX hlevel P hP Y₁ Y₂ u v B hY₁ hY₂ hu huv hlen hB₁ hB₂
  have h₁ := hX Q D z w hQ hD hz hw hcut hMX hlevel P hP Y₁ u v B hY₁ hu huv hlen hB₁
  have h₂ := hX Q D z w hQ hD hz hw hcut hMX hlevel P hP Y₂ u v B hY₂ hu huv hlen hB₂
  have hb := continuous_interval_square_difference_le (additivePrimeCofactorWindow P B z Y₁)
    (additivePrimeCofactorWindow P B z Y₂) (additivePrimeCofactorWindow_continuous P B z Y₁)
    (additivePrimeCofactorWindow_continuous P B z Y₂)
    ((∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z) huv
  apply hb.trans
  calc
    _ ≤ 2 * (3 * (v - u) * (ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z) ^ 2 +
        τ / 4 * X / (Real.log X) ^ A) +
      2 * (3 * (v - u) * (ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z) ^ 2 +
        τ / 4 * X / (Real.log X) ^ A) :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ (by norm_num))
        (mul_le_mul_of_nonneg_left h₂ (by norm_num))
    _ = _ := by ring

end Erdos421

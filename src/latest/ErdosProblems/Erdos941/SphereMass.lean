import ErdosProblems.Erdos941.SphereMassTransfer
import ErdosProblems.Erdos941.PrincipalMeanLowerBound
import ErdosProblems.Erdos941.PrimitiveThreeSquares

/-!
# A uniform lower bound for integral sphere points

The bound applies to all eligible norms, with arbitrary square factors. It uses
the proved real-variable Siegel bound, elementary character convolution, and the
Hurwitz lattice count, without a class-number or ideal-counting formula.
-/

namespace Erdos941

open Analytic

theorem exists_sphereCount_lower_of_primitive {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (v : Triple), 0 < n →
      tripleNorm v = n → PrimitiveTriple v →
      c * (n : ℝ) ^ (1 / 2 - δ) ≤ (sphereCount n : ℝ) := by
  obtain ⟨Cm, hCm, hm⟩ := exists_principalMean_lower_bound (half_pos hδ)
  obtain ⟨Cl, hCl, hl⟩ := exists_negative_LValue_lower (half_pos hδ)
  let C : ℝ := Cm * (4 : ℝ) ^ (-(δ / 2)) * Cl
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C / 16, div_pos hC (by norm_num), ?_⟩
  intro n v hn hv hp
  let : NeZero n := ⟨hn.ne'⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (Cm * (4 : ℝ) ^ (-(δ / 2))) * (n : ℝ) ^ (-(δ / 2)) ≤
      principalCharacterMean (4 * n) := by
    have h := hm (4 * n) (by omega)
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hnR.le] at h
    simpa only [mul_assoc] using h
  have hl' := hl n
  have hprod := mul_le_mul hm' hl' (by positivity)
    (principalCharacterMean_nonneg (4 * n))
  have he : ((Cm * (4 : ℝ) ^ (-(δ / 2))) * (n : ℝ) ^ (-(δ / 2))) *
      (Cl * (n : ℝ) ^ (-(δ / 2))) = C * (n : ℝ) ^ (-δ) := by
    calc
      _ = C * ((n : ℝ) ^ (-(δ / 2)) * (n : ℝ) ^ (-(δ / 2))) := by dsimp [C]; ring
      _ = _ := by rw [← Real.rpow_add hnR]; congr 2 <;> ring
  rw [he] at hprod
  have hbound := hprod.trans (principalMean_mul_LValue_le_sphere hn hv hp)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hmul := (le_div_iff₀ hsqrt).mp hbound
  have hpow : (n : ℝ) ^ (1 / 2 - δ) = (n : ℝ) ^ (-δ) * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnR]
    congr 1
    ring
  rw [hpow]
  nlinarith

theorem exists_sphereCount_lower_four_free {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ¬4 ∣ n → n % 8 ≠ 7 →
      c * (n : ℝ) ^ (1 / 2 - δ) ≤ (sphereCount n : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := exists_sphereCount_lower_of_primitive hδ
  refine ⟨c, hc, ?_⟩
  intro n hn h4 h8
  obtain ⟨v, hp, hv⟩ := primitive_three_squares_four_free hn h4 h8
  exact hbound n v hn hv hp

theorem exists_sphereCount_lower_two_three_six {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, (n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 6) →
      c * (n : ℝ) ^ (1 / 2 - δ) ≤ (sphereCount n : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := exists_sphereCount_lower_four_free hδ
  exact ⟨c, hc, fun n hn => hbound n (by omega) (by omega) (by omega)⟩

end Erdos941

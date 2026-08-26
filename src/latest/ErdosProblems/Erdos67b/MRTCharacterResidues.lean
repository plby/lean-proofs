import ErdosProblems.Erdos67b.MRTCharacterDistance
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! # Exact finite expansion of a unit residue class by Dirichlet characters -/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

theorem mrtConj_character_inv {q : ℕ} [NeZero q] {b : ZMod q} (hb : IsUnit b)
    (χ : DirichletCharacter ℂ q) : conj (χ b⁻¹) = χ b := by
  have hnorm : ‖χ b‖ = 1 := by simpa only [hb.unit_spec] using χ.unit_norm_eq_one hb.unit
  have hne : χ b ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  have hprod : χ b * χ b⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit b hb, map_one]
  have hinv : χ b⁻¹ = conj (χ b) := by
    apply mul_left_cancel₀ hne
    rw [hprod, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  simp [hinv]

theorem mrtSum_character_mul_conj {q : ℕ} [NeZero q] {b : ZMod q}
    (hb : IsUnit b) (m : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, χ b * conj (χ m)) =
      if (m : ZMod q) = b then (q.totient : ℂ) else 0 := by
  have hh := congrArg conj (DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb (m : ZMod q))
  simpa only [map_sum, map_mul, mrtConj_character_inv hb, apply_ite,
    map_natCast, map_zero, eq_comm] using hh

theorem mrtResidue_sum_eq_character_sum {q : ℕ} [NeZero q] {b : ZMod q}
    (hb : IsUnit b) (S : Finset ℕ) (F : ℕ → ℂ) :
    (∑ m ∈ S.filter (fun m : ℕ ↦ (m : ZMod q) = b), F m) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ b * ∑ m ∈ S, F m * conj (χ m) := by
  classical
  have hphi : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
  symm
  calc
    _ = ∑ m ∈ S, (q.totient : ℂ)⁻¹ * F m *
        ∑ χ : DirichletCharacter ℂ q, χ b * conj (χ m) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m _
      rw [mrtSum_character_mul_conj hb]
      by_cases hm : (m : ZMod q) = b
      · simp only [if_pos hm]
        field_simp
      · simp only [if_neg hm, mul_zero]

theorem mrtNorm_residue_sum_le_character_norm_sum {q : ℕ} [NeZero q] {b : ZMod q}
    (hb : IsUnit b) (S : Finset ℕ) (F : ℕ → ℂ) :
    ‖∑ m ∈ S.filter (fun m : ℕ ↦ (m : ZMod q) = b), F m‖ ≤
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ‖∑ m ∈ S, F m * conj (χ m)‖ := by
  rw [mrtResidue_sum_eq_character_sum hb, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q,
        ‖χ b * ∑ m ∈ S, F m * conj (χ m)‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      have hnorm : ‖χ b‖ = 1 := by
        simpa only [hb.unit_spec] using χ.unit_norm_eq_one hb.unit
      rw [norm_mul, hnorm, one_mul]

theorem mrtSum_norm_residue_sum_le {ι : Type*} (I : Finset ι)
    (S : ι → Finset ℕ) (F : ι → ℕ → ℂ) {q : ℕ} [NeZero q] {b : ZMod q}
    (hb : IsUnit b) {B : ℝ}
    (hbound : ∀ χ : DirichletCharacter ℂ q,
      (∑ x ∈ I, ‖∑ m ∈ S x, F x m * conj (χ m)‖) ≤ B) :
    (∑ x ∈ I, ‖∑ m ∈ (S x).filter (fun m : ℕ ↦ (m : ZMod q) = b), F x m‖) ≤ B := by
  classical
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (NeZero.pos q)).ne'
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  calc
    _ ≤ ∑ x ∈ I, (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ‖∑ m ∈ S x, F x m * conj (χ m)‖ :=
      Finset.sum_le_sum fun x _ ↦ mrtNorm_residue_sum_le_character_norm_sum hb (S x) (F x)
    _ = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        ∑ x ∈ I, ‖∑ m ∈ S x, F x m * conj (χ m)‖ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (q.totient : ℝ)⁻¹ * ∑ _χ : DirichletCharacter ℂ q, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ ↦ hbound χ)
        (inv_nonneg.2 (Nat.cast_nonneg _))
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      field_simp

theorem mrtTypicalShort_character_eq_support_sum (blocks : Finset (ℕ × ℕ))
    (Z n h : ℕ) (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    typicalModulatedShortSum blocks Z (mrtCharacterUntwist f χ) n h 0 =
      ∑ m ∈ typicalShortSupport blocks Z n h, f m * conj (χ m) := by
  simpa only [additivePhase, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul,
    mrtCharacterUntwist] using
    typicalModulatedShortSum_eq_support_sum blocks Z (mrtCharacterUntwist f χ) n h 0

theorem mrtExists_logPower_unit_residue_short_firstMoment {rho R : ℝ}
    (hrho : 0 < rho) (hR : 1 ≤ R) :
    ∃ H₀ : ℕ, 10 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      2 ≤ mrtLogPowerWindow (Real.log (H : ℝ)) ∧
      mrtLogPowerLower (Real.log (H : ℝ)) / mrtLogPowerUpper (Real.log (H : ℝ)) ≤ rho ∧
      ∃ K A₀ Y₀ : ℕ, 0 < K ∧ 0 < A₀ ∧ H ≤ Y₀ ∧
        ∀ {A X Y : ℕ}, A₀ ≤ A → Y₀ ≤ Y → Y ≤ X →
          Real.log (X : ℝ) ≤ R * Real.log (Y : ℝ) →
        ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
          (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRTNonpretentious f A X →
        ∀ {q : ℕ}, 0 < q → q ≤ A → ∀ b : ZMod q, IsUnit b →
        ∀ {h Z : ℕ},
          (H : ℝ) / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 3 ≤ h → h ≤ H → 2 * Y ≤ Z →
          (∑ n ∈ Finset.Ioc Y (2 * Y),
            ‖∑ m ∈ (typicalShortSupport
              (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
                (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z n h).filter
                (fun m : ℕ ↦ (m : ZMod q) = b), f m‖) ≤
              (h : ℝ) * Y / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 3 := by
  classical
  obtain ⟨H₀, hH₀, hmain⟩ := mrtExists_logPower_character_short_firstMoment hrho hR
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  obtain ⟨hW, hratio, K, A₀, Y₀, hK, hA₀, hY₀, hfirst⟩ := hmain H hH
  refine ⟨hW, hratio, K, A₀, Y₀, hK, hA₀, hY₀, ?_⟩
  intro A X Y hA hY hYX hlog f hmul hbound hnonpret q hq hqA b hb h Z hlength hhH hZ
  let : NeZero q := ⟨hq.ne'⟩
  apply mrtSum_norm_residue_sum_le (Finset.Ioc Y (2 * Y))
    (fun n ↦ typicalShortSupport
      (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
        (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z n h) (fun _ ↦ f) hb
  intro χ
  have hh := hfirst hA hY hYX hlog hmul hbound hnonpret hq hqA χ hlength hhH hZ
  simpa only [mrtTypicalShort_character_eq_support_sum] using hh

end

end Erdos67b

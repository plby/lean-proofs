import ErdosProblems.Erdos67b.MRTGeneralResidues

/-! # Rational additive phases with a bound for every partial short length -/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

theorem mrtNorm_typicalModulatedShortSum_le (blocks : Finset (ℕ × ℕ)) (Z n h : ℕ)
    {f : ℕ → ℂ} (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1) (α : ℝ) :
    ‖typicalModulatedShortSum blocks Z f n h α‖ ≤ (h : ℝ) := by
  classical
  unfold typicalModulatedShortSum
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 h, ‖if n + j ∈ typicalFactorizationSet blocks Z then
        f (n + j) * additivePhase α j else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 h, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs
      · rw [norm_mul, norm_additivePhase, mul_one]
        exact hbound _ (by have := (Finset.mem_Icc.1 hj).1; omega)
      · norm_num
    _ = _ := by simp

theorem mrtTypical_rational_eq_residue_sum (blocks : Finset (ℕ × ℕ)) (Z : ℕ)
    (f : ℕ → ℂ) (n h : ℕ) {q : ℕ} [NeZero q] (a : ℤ) :
    typicalModulatedShortSum blocks Z f n h ((a : ℝ) / q) =
      conj (additivePhase ((a : ℝ) / q) n) * ∑ b : ZMod q,
        rationalPhase q a b * mrtResidueShortSum blocks Z f n h q b.val := by
  classical
  let S := typicalShortSupport blocks Z n h
  calc
    _ = conj (additivePhase ((a : ℝ) / q) n) *
        ∑ m ∈ S, rationalPhase q a (m : ZMod q) * f m := by
      rw [typicalModulatedShortSum_eq_support_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [additivePhase_natSub _ (mem_typicalShortSupport.1 hm).2.1.le]
      simp only [additivePhase_rational, mul_assoc]
    _ = _ := by
      congr 1
      calc
        _ = ∑ b : ZMod q, ∑ m ∈ S.filter (fun m : ℕ ↦ (m : ZMod q) = b),
            rationalPhase q a (m : ZMod q) * f m := by
          exact (Finset.sum_fiberwise_of_maps_to
            (s := S) (t := (Finset.univ : Finset (ZMod q)))
            (g := fun m : ℕ ↦ (m : ZMod q)) (fun _ _ ↦ Finset.mem_univ _)
            (fun m ↦ rationalPhase q a (m : ZMod q) * f m)).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro b _
          rw [mrtResidueShortSum, Finset.mul_sum]
          simp only [ZMod.natCast_zmod_val]
          apply Finset.sum_congr rfl
          intro m hm
          rw [(Finset.mem_filter.1 hm).2]

theorem mrtNorm_typical_rational_le_residue_sum (blocks : Finset (ℕ × ℕ)) (Z : ℕ)
    (f : ℕ → ℂ) (n h : ℕ) {q : ℕ} [NeZero q] (a : ℤ) :
    ‖typicalModulatedShortSum blocks Z f n h ((a : ℝ) / q)‖ ≤
      ∑ b : ZMod q, ‖mrtResidueShortSum blocks Z f n h q b.val‖ := by
  rw [mrtTypical_rational_eq_residue_sum, norm_mul, Complex.norm_conj,
    norm_additivePhase, one_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [norm_mul, norm_rationalPhase, one_mul]

theorem mrtSum_norm_typical_rational_le (blocks : Finset (ℕ × ℕ)) (Z Y h : ℕ)
    (f : ℕ → ℂ) {q : ℕ} [NeZero q] (a : ℤ) {B : ℝ}
    (hres : ∀ b : ZMod q, (∑ n ∈ Finset.Ioc Y (2 * Y),
      ‖mrtResidueShortSum blocks Z f n h q b.val‖) ≤ B) :
    (∑ n ∈ Finset.Ioc Y (2 * Y),
      ‖typicalModulatedShortSum blocks Z f n h ((a : ℝ) / q)‖) ≤ (q : ℝ) * B := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc Y (2 * Y), ∑ b : ZMod q,
        ‖mrtResidueShortSum blocks Z f n h q b.val‖ :=
      Finset.sum_le_sum fun n _ ↦ mrtNorm_typical_rational_le_residue_sum blocks Z f n h a
    _ = ∑ b : ZMod q, ∑ n ∈ Finset.Ioc Y (2 * Y),
        ‖mrtResidueShortSum blocks Z f n h q b.val‖ := Finset.sum_comm
    _ ≤ ∑ _b : ZMod q, B := Finset.sum_le_sum fun b _ ↦ hres b
    _ = _ := by simp

theorem mrtExists_logPower_rational_prefix_firstMoment {rho R : ℝ}
    (hrho : 0 < rho) (hR : 1 ≤ R) :
    ∃ H₀ : ℕ, 10 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      2 ≤ mrtLogPowerWindow (Real.log (H : ℝ)) ∧
      mrtLogPowerLower (Real.log (H : ℝ)) / mrtLogPowerUpper (Real.log (H : ℝ)) ≤ rho ∧
      ∃ K A₀ Y₀ : ℕ, 0 < K ∧ 0 < A₀ ∧ H ≤ Y₀ ∧
        ∀ {A X Y : ℕ}, A₀ ≤ A → Y₀ ≤ Y → Y ≤ X →
          Real.log (X : ℝ) ≤ R * Real.log
            ((Y / mrtLogPowerNatWindow (Real.log (H : ℝ)) : ℕ) : ℝ) →
        ∀ {f : ℕ → ℂ}, IsCompletelyMultiplicativeOnPositive f →
          (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRTNonpretentious f A X →
        ∀ {q : ℕ}, 0 < q → q ≤ mrtLogPowerNatWindow (Real.log (H : ℝ)) →
        ∀ a : ℤ, ∀ {h Z : ℕ}, h ≤ H → 2 * Y ≤ Z →
          (∑ n ∈ Finset.Ioc Y (2 * Y),
            ‖typicalModulatedShortSum
              (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
                (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z f n h ((a : ℝ) / q)‖) ≤
              2 * (H : ℝ) * Y / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 2 +
                (q : ℝ) * ((H : ℝ) * Y / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 3 +
                  2 * H + Y) := by
  obtain ⟨H₀, hH₀, hmain⟩ := mrtExists_logPower_residue_short_firstMoment hrho hR
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  obtain ⟨hW, hratio, K, A₀, Y₀, hK, hA₀, hY₀, hres⟩ := hmain H hH
  refine ⟨hW, hratio, K, A₀, Y₀, hK, hA₀, hY₀, ?_⟩
  intro A X Y hA hY hYX hlog f hmul hbound hnonpret q hq hqw a h Z hhH hZ
  let W := mrtLogPowerWindow (Real.log (H : ℝ))
  have hWpos : 0 < W := mrtLogPowerWindow_pos _
  have hhHR : (h : ℝ) ≤ H := by exact_mod_cast hhH
  let : NeZero q := ⟨hq.ne'⟩
  by_cases hshort : 2 * (H : ℝ) / W ^ 2 ≤ h
  · have hrat := mrtSum_norm_typical_rational_le
      (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
        (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z Y h f (q := q) a
      (B := (H : ℝ) * Y / W ^ 3 + 2 * H + Y) ?_
    · exact hrat.trans (le_add_of_nonneg_left (by positivity))
    intro b
    apply (hres hA hY hYX hlog hmul hbound hnonpret hq hqw b.val hshort hhH hZ).trans
    gcongr
  · have hsmall : (h : ℝ) ≤ 2 * (H : ℝ) / W ^ 2 := (lt_of_not_ge hshort).le
    calc
      _ ≤ ∑ _n ∈ Finset.Ioc Y (2 * Y), (h : ℝ) :=
        Finset.sum_le_sum fun n _ ↦ mrtNorm_typicalModulatedShortSum_le _ Z n h hbound _
      _ = (h : ℝ) * Y := by
        simp only [Finset.sum_const, nsmul_eq_mul, card_Ioc_self_two_mul]
        ring
      _ ≤ (2 * (H : ℝ) / W ^ 2) * Y :=
        mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg Y)
      _ = 2 * (H : ℝ) * Y / W ^ 2 := by ring
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

end

end Erdos67b

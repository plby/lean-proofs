import ErdosProblems.Erdos964.UniformSemiprimeBlocks
import ErdosProblems.Erdos964.SemiprimeDyadicPartition

/-!
# Semiprime distribution after summing the prime blocks

The constant and threshold are uniform in the smaller-prime support and in
the independently chosen endpoints and reduced residues of every modulus.
The modulus range `L^θ`, for `θ < 1`, has level below one half relative
to the product cap `L²`.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem exists_semiprimesAtScale_logSaving (a : ℕ) (η θ : ℝ)
    (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 16 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
        (∀ p ∈ P, Real.rpow (L : ℝ) η < p) →
      ∀ X : ℕ → ℕ,
        (∀ q, 0 < q → q ≤ modulusCutoff θ L → X q ∈ Finset.Icc 1 (L ^ 2)) →
      ∀ r : ℕ → ℕ, (∀ q, 0 < q → q ≤ modulusCutoff θ L → (r q).Coprime q) →
      (∑ q ∈ Finset.Ioc 0 (modulusCutoff θ L),
        |(finiteResidueCount (semiprimesAtScale P L (X q)) q (r q) : ℝ) -
          ((semiprimesAtScale P L (X q)).card : ℝ) / q.totient|) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  classical
  obtain ⟨C, hC, L₀, hL₀, hblock⟩ :=
    exists_uniform_dyadicSemiprimeBlock_logSaving a η θ hη hθ hθ1
  refine ⟨4 * C, by positivity, L₀, hL₀, ?_⟩
  intro L hL P hP hPL hPlower X hX r hr
  have hL16 : 16 ≤ L := hL₀.trans hL
  have hL4 : 4 ≤ L := by omega
  have hLpos : 0 < L := by omega
  have hlogpos : 0 < Real.log (L : ℝ) := by
    have := two_le_log_natCast_of_sixteen_le hL16
    linarith
  have hblockBound (α : ℕ) (hα : α ∈ dyadicExponentRange L) :
      (∑ q ∈ Finset.Ioc 0 (modulusCutoff θ L),
        |(finiteResidueCount (dyadicSemiprimesAtScale P L (X q) α) q (r q) : ℝ) -
          ((dyadicSemiprimesAtScale P L (X q) α).card : ℝ) / q.totient|) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 1) := by
    let Pα := P.filter (fun p => p ∈ dyadicBlock α)
    by_cases hnonempty : Pα.Nonempty
    · obtain ⟨p, hp⟩ := hnonempty
      have hpP := (Finset.mem_filter.mp hp).1
      have hpblock := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).2
      have hαlog : α ≤ Nat.log 2 L := by
        simpa only [dyadicExponentRange, Finset.mem_range, Nat.lt_succ_iff] using hα
      have hML : 2 ^ α ≤ L :=
        (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hαlog).trans
          (Nat.pow_log_le_self 2 hLpos.ne')
      have hMlower : Real.rpow (L : ℝ) η / 2 ≤ (2 ^ α : ℕ) := by
        have hpupper : (p : ℝ) ≤ 2 * ((2 ^ α : ℕ) : ℝ) := by
          exact_mod_cast (by simpa only [pow_succ, mul_comm] using hpblock.2 : p ≤ 2 * 2 ^ α)
        have hplower := hPlower p hpP
        linarith
      have hPα : ∀ p ∈ Pα, p.Prime := fun p hp => hP p (Finset.mem_filter.mp hp).1
      have hPαL : ∀ p ∈ Pα, p ≤ L := fun p hp => hPL p (Finset.mem_filter.mp hp).1
      have hPαinterval : Pα ⊆ Finset.Ioc (2 ^ α) (2 ^ α + 2 ^ α) := by
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).2
        simpa only [dyadicBlock, pow_succ, mul_two] using hp'
      exact hblock L hL (2 ^ α) hMlower hML X hX Pα hPα hPαL hPαinterval r hr
    · have hempty : Pα = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
      have hblockEmpty (q : ℕ) : dyadicSemiprimesAtScale P L (X q) α = ∅ := by
        change primeProductBlock Pα _ _ = ∅
        simp only [hempty, primeProductBlock, Finset.empty_product, Finset.filter_empty,
          Finset.image_empty]
      simp only [hblockEmpty, finiteResidueCount, Finset.filter_empty, Finset.card_empty,
        Nat.cast_zero, zero_div, sub_self, abs_zero, Finset.sum_const_zero]
      positivity
  have hcount : ((dyadicExponentRange L).card : ℝ) ≤ 4 * Real.log (L : ℝ) := by
    have h := (semiprime_block_log_bounds L 1 1 L hL4 (by norm_num) (by norm_num)
      hLpos le_rfl (by norm_num; nlinarith)).2.1
    simpa only [dyadicExponentRange, Finset.card_range] using h
  calc
    _ ≤ ∑ q ∈ Finset.Ioc 0 (modulusCutoff θ L), ∑ α ∈ dyadicExponentRange L,
        |(finiteResidueCount (dyadicSemiprimesAtScale P L (X q) α) q (r q) : ℝ) -
          ((dyadicSemiprimesAtScale P L (X q) α).card : ℝ) / q.totient| := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := Finset.mem_Ioc.mp hq
      rw [semiprimesAtScale_error_eq_sum_dyadic P L (X q) q (r q) hP hPL
        (Finset.mem_Icc.mp (hX q hq'.1 hq'.2)).2]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ α ∈ dyadicExponentRange L, ∑ q ∈ Finset.Ioc 0 (modulusCutoff θ L),
        |(finiteResidueCount (dyadicSemiprimesAtScale P L (X q) α) q (r q) : ℝ) -
          ((dyadicSemiprimesAtScale P L (X q) α).card : ℝ) / q.totient| := Finset.sum_comm
    _ ≤ ∑ α ∈ dyadicExponentRange L, C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 1) :=
      Finset.sum_le_sum (fun α hα => hblockBound α hα)
    _ = ((dyadicExponentRange L).card : ℝ) *
        (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 1)) := by simp
    _ ≤ (4 * Real.log (L : ℝ)) *
        (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 1)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by
      rw [pow_succ]
      field_simp
      rw [pow_succ]
      ring

end Erdos964

import ErdosProblems.Erdos67b.MRTDividedIntervals
import ErdosProblems.Erdos67b.MRTResidueShortSum

/-! # Exact residue reindexing by a common divisor -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrtGcd_residue_parameters (b : ℕ) {q : ℕ} (hq : 0 < q) :
    0 < Nat.gcd b q ∧ Nat.gcd b q ≤ q ∧ 0 < q / Nat.gcd b q ∧
      Nat.Coprime (b / Nat.gcd b q) (q / Nat.gcd b q) := by
  have hd : 0 < Nat.gcd b q := Nat.gcd_pos_of_pos_right b hq
  have hdq := Nat.gcd_dvd_right b q
  have hle := Nat.le_of_dvd hq hdq
  exact ⟨hd, hle, Nat.div_pos hle hd, Nat.coprime_div_gcd_div_gcd hd⟩

theorem mrtResidue_divisor_dvd {d q b m : ℕ} (hdq : d ∣ q) (hdb : d ∣ b)
    (hres : (m : ZMod q) = (b : ZMod q)) : d ∣ m := by
  have hh := (ZMod.natCast_eq_natCast_iff m b q).1 hres
  exact (hh.dvd_iff hdq).2 hdb

theorem mrtResidue_mul_iff {d q b : ℕ} (hd : 0 < d) (hdq : d ∣ q) (hdb : d ∣ b)
    (m : ℕ) :
    ((d * m : ℕ) : ZMod q) = (b : ZMod q) ↔
      (m : ZMod (q / d)) = ((b / d : ℕ) : ZMod (q / d)) := by
  rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff]
  have hh := Nat.ModEq.mul_left_cancel_iff' (a := m) (b := b / d) (m := q / d) hd.ne'
  simpa only [Nat.mul_div_cancel' hdq, Nat.mul_div_cancel' hdb] using hh

theorem mrtResidueShortSum_divisor_reindex {blocks : Finset (ℕ × ℕ)} {d q b : ℕ}
    (hd : 0 < d) (hdq : d ∣ q) (hdb : d ∣ b)
    (hlarge : ∀ I ∈ blocks, ∀ p ∈ primesInBlock I, d < p)
    {f : ℕ → ℂ} (hmul : IsCompletelyMultiplicativeOnPositive f) (Z n h : ℕ) :
    mrtResidueShortSum blocks Z f n h q b =
      f d * mrtResidueShortSum blocks (Z / d) f (n / d)
        (mrtDividedLength n h d) (q / d) (b / d) := by
  classical
  rw [mrtResidueShortSum, mrtResidueShortSum, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun m _ ↦ d * m)
  · intro m hm
    obtain ⟨hsupport, hres⟩ := Finset.mem_filter.1 hm
    exact Finset.mem_filter.2
      ⟨(mrtMem_typicalShortSupport_mul_iff hd hlarge Z n h m).2 hsupport,
        (mrtResidue_mul_iff hd hdq hdb m).2 hres⟩
  · intro m₁ _ m₂ _ heq
    exact Nat.eq_of_mul_eq_mul_left hd heq
  · intro m hm
    obtain ⟨hsupport, hres⟩ := Finset.mem_filter.1 hm
    have hdm := mrtResidue_divisor_dvd hdq hdb hres
    have heq : d * (m / d) = m := Nat.mul_div_cancel' hdm
    refine ⟨m / d, Finset.mem_filter.2 ⟨?_, ?_⟩, heq⟩
    · apply (mrtMem_typicalShortSupport_mul_iff hd hlarge Z n h (m / d)).1
      simpa only [heq] using hsupport
    · apply (mrtResidue_mul_iff hd hdq hdb (m / d)).1
      simpa only [heq] using hres
  · intro m hm
    have hsupport := (Finset.mem_filter.1 hm).1
    have hmpos := (mem_typicalFactorizationSet.1 (mem_typicalShortSupport.1 hsupport).1).1
    exact (hmul.2 d m hd hmpos).symm

theorem mrtNorm_residueShortSum_divisor_le {blocks : Finset (ℕ × ℕ)} {d q b : ℕ}
    (hd : 0 < d) (hdq : d ∣ q) (hdb : d ∣ b)
    (hlarge : ∀ I ∈ blocks, ∀ p ∈ primesInBlock I, d < p)
    {f : ℕ → ℂ} (hmul : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1) (Z n h : ℕ) :
    ‖mrtResidueShortSum blocks Z f n h q b‖ ≤
      ‖mrtResidueShortSum blocks (Z / d) f (n / d) (h / d) (q / d) (b / d)‖ + 1 := by
  rw [mrtResidueShortSum_divisor_reindex hd hdq hdb hlarge hmul, norm_mul]
  calc
    _ ≤ 1 * ‖mrtResidueShortSum blocks (Z / d) f (n / d)
        (mrtDividedLength n h d) (q / d) (b / d)‖ :=
      mul_le_mul_of_nonneg_right (hbound d hd) (norm_nonneg _)
    _ = _ := one_mul _
    _ ≤ _ := mrtNorm_residueShortSum_adjacent_le blocks (Z / d) (n / d) (h / d)
      (mrtDividedLength n h d) (q / d) (b / d) hbound (mrtDividedLength_eq_or n h d)

end

end Erdos67b

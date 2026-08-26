import ErdosProblems.Erdos67b.MRTShortSumPrimeSquare
import ErdosProblems.Erdos67b.MRTWindowBlockSaving

/-! # The actual common Ramaré sum becomes the dual-window prime rows -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrtRawRamarePrimeSum (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (S : Finset ℕ)
    (Z : ℕ) (f : ℕ → ℂ) (n H : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ S, ∑ m ∈ divisorCofactorImage (typicalShortSupport blocks Z n H) p,
    (f p * f m / (mrCommonDenominator (primesInBlock I) m : ℂ)) * additivePhase α (p * m)

def mrtTypicalCofactorWeight (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ)
    (f : ℕ → ℂ) (m : ℕ) : ℂ := by
  classical
  exact if HasTypicalFactorization (blocks.erase I) m then
    f m / (mrCommonDenominator (primesInBlock I) m : ℂ) else 0

theorem mrtNorm_typicalCofactorWeight_le (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ)
    {f : ℕ → ℂ} (hf : ∀ m, 0 < m → ‖f m‖ ≤ 1) {m : ℕ} (hm : 0 < m) :
    ‖mrtTypicalCofactorWeight blocks I f m‖ ≤ 1 := by
  classical
  unfold mrtTypicalCofactorWeight
  split_ifs
  · rw [norm_div, Complex.norm_natCast]
    have hden : (1 : ℝ) ≤ mrCommonDenominator (primesInBlock I) m := by
      unfold mrCommonDenominator
      exact_mod_cast (Nat.le_add_right 1 _)
    exact (div_le_one (by linarith)).2 ((hf m hm).trans hden)
  · simp

theorem mrtRawCommonShortSum_eq_primeSum (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ)
    (Z : ℕ) (f : ℕ → ℂ) (n H : ℕ) (α : ℝ) :
    mrtRawShortSum (mrTypicalCommonCoefficient blocks Z (primesInBlock I) f) n H α =
      mrtRawRamarePrimeSum blocks I (primesInBlock I) Z f n H α := by
  classical
  have hsupport :
      mrtRawShortSum (mrTypicalCommonCoefficient blocks Z (primesInBlock I) f) n H α =
      ∑ r ∈ typicalShortSupport blocks Z n H,
        mrCommonRamareCoefficient (primesInBlock I) f r * additivePhase α r := by
    have hset : (Finset.Ioc n (n + H)).filter
        (fun r ↦ r ∈ typicalFactorizationSet blocks Z) = typicalShortSupport blocks Z n H := by
      ext r
      simp only [Finset.mem_filter, mem_typicalShortSupport, Finset.mem_Ioc]
      tauto
    rw [← hset, Finset.sum_filter]
    unfold mrtRawShortSum mrTypicalCommonCoefficient
    apply Finset.sum_congr rfl
    intro r hr
    split_ifs <;> simp
  rw [hsupport]
  unfold mrCommonRamareCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold mrtRawRamarePrimeSum
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 := (mem_primesInBlock.1 hp).1.pos
  calc
    _ = ∑ r ∈ typicalShortSupport blocks Z n H, if p ∣ r then
        (f p * f (r / p) / (mrCommonDenominator (primesInBlock I) (r / p) : ℂ)) *
          additivePhase α r else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs <;> simp
    _ = _ := sum_dvd_eq_sum_divisorCofactorImage _ hp0
      (fun r m ↦ (f p * f m / (mrCommonDenominator (primesInBlock I) m : ℂ)) *
        additivePhase α r)

open scoped Classical in
theorem mrtDivisorCofactorImage_eq_window
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} {p P Z H Y n : ℕ}
    (hp : p ∈ primesInBlock I) (hP : 0 < P) (hPp : P ≤ p)
    (hHY : H ≤ Y) (hn : n ∈ Finset.Ioc Y (2 * Y))
    (hdisj : ∀ J ∈ blocks, J ≠ I → Disjoint (primesInBlock I) (primesInBlock J)) :
    divisorCofactorImage (typicalShortSupport blocks Z n H) p =
      (Finset.Icc 1 (3 * Y / P)).filter fun m ↦
        HasTypicalFactorization (blocks.erase I) m ∧ mrtProductWindow Z H n p m := by
  classical
  have hp0 := (mem_primesInBlock.1 hp).1.pos
  ext m
  rw [mem_divisorCofactorImage, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨r, hr, hpr, hquot⟩
    have heq : p * m = r := by rw [← hquot, Nat.mul_div_cancel' hpr]
    have heq' : m * p = r := by rw [Nat.mul_comm, heq]
    obtain ⟨htyp, hnr, hrn⟩ := mem_typicalShortSupport.1 hr
    obtain ⟨hr1, hrZ, hrtyp⟩ := mem_typicalFactorizationSet.1 htyp
    have hm : 0 < m := by
      rw [← hquot]
      exact Nat.div_pos (Nat.le_of_dvd hr1 hpr) hp0
    have hmp : m * P ≤ 3 * Y := by
      have hnhi := (Finset.mem_Ioc.1 hn).2
      calc
        _ ≤ m * p := Nat.mul_le_mul_left m hPp
        _ = r := heq'
        _ ≤ 3 * Y := by omega
    refine ⟨⟨hm, (Nat.le_div_iff_mul_le hP).2 hmp⟩, ?_, ?_⟩
    · apply (hasTypicalFactorization_prime_mul_iff_erase hp hdisj).1
      rwa [heq]
    · exact ⟨by rwa [heq'], by rwa [heq'], by rwa [heq']⟩
  · rintro ⟨⟨hm, _⟩, htyp, hwindow⟩
    refine ⟨p * m, ?_, dvd_mul_right p m, Nat.mul_div_cancel_left _ hp0⟩
    rw [mem_typicalShortSupport, mem_typicalFactorizationSet]
    have hpm : 1 ≤ p * m := Nat.mul_pos hp0 hm
    have htyp' := (hasTypicalFactorization_prime_mul_iff_erase hp hdisj).2 htyp
    simpa only [Nat.mul_comm p m] using
      (show (1 ≤ p * m ∧ p * m ≤ Z ∧ HasTypicalFactorization blocks (p * m)) ∧
        n < p * m ∧ p * m ≤ n + H from
        ⟨⟨hpm, by simpa [Nat.mul_comm] using hwindow.2.2, htyp'⟩,
          by simpa [Nat.mul_comm] using hwindow.1,
          by simpa [Nat.mul_comm] using hwindow.2.1⟩)

theorem mrtRawRamarePrimeSum_eq_windows
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} {S : Finset ℕ} {P Z H Y n : ℕ}
    (hS : S ⊆ primesInBlock I) (hP : 0 < P) (hPS : ∀ p ∈ S, P ≤ p)
    (hHY : H ≤ Y) (hn : n ∈ Finset.Ioc Y (2 * Y))
    (hdisj : ∀ J ∈ blocks, J ≠ I → Disjoint (primesInBlock I) (primesInBlock J))
    (f : ℕ → ℂ) (α : ℝ) :
    mrtRawRamarePrimeSum blocks I S Z f n H α =
      ∑ p ∈ S, ∑ m ∈ Finset.Icc 1 (3 * Y / P),
        if mrtProductWindow Z H n p m then
          mrtTypicalCofactorWeight blocks I f m * (f p * additivePhase α (m * p)) else 0 := by
  classical
  unfold mrtRawRamarePrimeSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [mrtDivisorCofactorImage_eq_window (hS hp) hP (hPS p hp) hHY hn hdisj,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  unfold mrtTypicalCofactorWeight
  by_cases htyp : HasTypicalFactorization (blocks.erase I) m <;>
    by_cases hw : mrtProductWindow Z H n p m <;> simp only [htyp, hw, and_self,
      false_and, and_false, ↓reduceIte, zero_mul]
  rw [Nat.mul_comm p m]
  ring

theorem mrtDual_rawRamarePrimeSum_eq_windowRow
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} {S : Finset ℕ} {P Z H Y : ℕ}
    (hS : S ⊆ primesInBlock I) (hP : 0 < P) (hPS : ∀ p ∈ S, P ≤ p) (hHY : H ≤ Y)
    (hdisj : ∀ J ∈ blocks, J ≠ I → Disjoint (primesInBlock I) (primesInBlock J))
    (f θ : ℕ → ℂ) (α : ℝ) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), θ n * mrtRawRamarePrimeSum blocks I S Z f n H α) =
      ∑ m ∈ Finset.Icc 1 (3 * Y / P),
        mrtTypicalCofactorWeight blocks I f m * mrtWindowPrimeRow S Z H Y f θ α m := by
  classical
  calc
    _ = ∑ n ∈ Finset.Ioc Y (2 * Y), θ n *
        ∑ p ∈ S, ∑ m ∈ Finset.Icc 1 (3 * Y / P),
          if mrtProductWindow Z H n p m then
            mrtTypicalCofactorWeight blocks I f m * (f p * additivePhase α (m * p))
          else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [mrtRawRamarePrimeSum_eq_windows hS hP hPS hHY hn hdisj f α]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s := Finset.Ioc Y (2 * Y))]
      rw [Finset.sum_comm]
      unfold mrtWindowPrimeRow mrtWindowWeight
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> ring

end

end Erdos67b

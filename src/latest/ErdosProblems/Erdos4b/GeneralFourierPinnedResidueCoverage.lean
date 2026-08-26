/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSourceResidueMass
import ErdosProblems.Erdos4b.GeneralFourierPinnedPhysicalWeight
import ErdosProblems.Erdos4b.GeneralFourierPinnedPositiveWeight

/-!
# Pinned squares contribute to the literal residue mass

The positive natural-base-point margin is explicit. Every shift gives
a distinct pre-sieved integer in the same residue class, so all pinned
squares can be retained at once.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem sum_weight_le_largeGapResidueRawWeight_of_injective
    {ι : Type*} [Fintype ι] (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (U w m q : ℕ) (a : Fin q)
    (f : ι → ℕ) (hinj : Function.Injective f)
    (hmem : ∀ i, f i ≤ U / m) (hmod : ∀ i, f i % q = a.val)
    (hpre : ∀ i, largeGapPreSieved w m (f i)) :
    (∑ i, doubledSelbergWeight H D E lambda m q (f i)) ≤
      largeGapResidueRawWeight H D E lambda U w m q a := by
  classical
  let A := Finset.univ.image f
  let g : ℕ → ℝ := fun n ↦ if n % q = a.val ∧ largeGapPreSieved w m n then
    doubledSelbergWeight H D E lambda m q n else 0
  have hA : A ⊆ Finset.Icc 0 (U / m) := by
    intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hmem i⟩
  calc
    _ = ∑ n ∈ A, doubledSelbergWeight H D E lambda m q n := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij ↦ hinj hij
    _ = ∑ n ∈ A, g n := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
      exact (if_pos ⟨hmod i, hpre i⟩).symm
    _ ≤ ∑ n ∈ Finset.Icc 0 (U / m), g n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hA
      intro n _ _
      dsimp only [g]
      split_ifs
      · exact doubledSelbergWeight_nonneg H D E lambda m q n
      · exact le_rfl
    _ = _ := rfl

theorem largeGapPreSieved_of_residual_prime
    {w m p₀ Y : ℕ} (hp₀ : p₀.Prime) (hwY : w ≤ Y) (hYp₀ : Y < p₀)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) :
    largeGapPreSieved w m p₀ := by
  have hpw : p₀.Coprime (primorial w) := hp₀.coprime_iff_not_dvd.mpr (by
    intro hd
    exact (not_le_of_gt (hwY.trans_lt hYp₀)) (hp₀.dvd_primorial_iff.mp hd))
  exact hpw.mul_left (hcop.of_dvd_right (primorial_dvd_primorial hwY))

theorem sum_shift_doubledSelbergWeight_le_residueRawWeight
    {K U w m q p₀ : ℕ} (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hm : 0 < m) (hq : 0 < q) (hpT : p₀ ≤ U / m)
    (hpre : largeGapPreSieved w m p₀)
    (hmargin : ∀ h : Fin K, primorial w * h.val * q < p₀) :
    (∑ h : Fin K, doubledSelbergWeight H D E lambda m q
      (p₀ - primorial w * h.val * q)) ≤
      largeGapResidueRawWeight H D E lambda U w m q
        ⟨p₀ % q, Nat.mod_lt p₀ hq⟩ := by
  apply sum_weight_le_largeGapResidueRawWeight_of_injective
  · intro h i heq
    have hmul := (tsub_right_inj (hmargin h).le (hmargin i).le).mp heq
    have hvals : h.val = i.val := by
      apply Nat.eq_of_mul_eq_mul_left (primorial_pos w)
      exact Nat.eq_of_mul_eq_mul_right hq hmul
    exact Fin.ext hvals
  · intro h
    exact (Nat.sub_le _ _).trans hpT
  · intro h
    have hshift : h.val * (primorial w * q) < p₀ := by
      simpa only [mul_assoc, mul_left_comm] using hmargin h
    simpa only [mul_assoc, mul_left_comm] using
      sub_scaledShift_mod (primorial_pos w) hq hshift.le
  · intro h
    have hshift : h.val * (primorial w * q) < p₀ := by
      simpa only [mul_assoc, mul_left_comm] using hmargin h
    simpa only [mul_assoc, mul_left_comm] using
      largeGapPreSieved_sub_scaledShift hm hq hshift hpre

theorem sum_pinnedSourceWeight_le_sourceResidueRawWeight
    {K U w m p₀ q Y : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {LD : ℝ}
    (hLD : 0 < LD) (hY : 1 < Y) (hm : 0 < m) (hq : 0 < q)
    (hp₀ : p₀.Prime) (hwY : w ≤ Y) (hYp₀ : Y < p₀) (hpT : p₀ ≤ U / m)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (hD : LD / 10 < Real.log p₀) (hcop : (m * p₀ - 1).Coprime (primorial Y))
    (hmargin : ∀ h : Fin K, primorial w * h.val * q < p₀) :
    (∑ h : Fin K, pinnedSourceRealIntegerWeight S F G h P w m p₀ q LD (Real.log Y)) ≤
      sourceResidueRawWeight S F G P LD (Real.log Y) U w m q
        ⟨p₀ % q, Nat.mod_lt p₀ hq⟩ := by
  have hpre := largeGapPreSieved_of_residual_prime hp₀ hwY hYp₀ hcop
  have hsum := sum_shift_doubledSelbergWeight_le_residueRawWeight
    (preSievedShifts K w) (cutoffDivisorTupleSupport (preSievedShifts K w) P)
    (cutoffCompanionDivisorTupleSupport (preSievedShifts K w) P m)
    (sourceAnalyticSelbergCoefficient S
      (fun j i ↦ F j ((preSievedShiftEquiv K w).symm i)) G LD (Real.log Y))
    hm hq hpT hpre hmargin
  apply le_trans (le_of_eq ?_) hsum
  apply Finset.sum_congr rfl
  intro h _
  apply Complex.ofReal_injective
  rw [ofReal_pinnedSourceRealIntegerWeight]
  exact (doubledSelbergWeight_source_eq_pinned S F G h P hP hLD hY hm
    (Nat.sub_pos_of_lt (hmargin h)) hp₀ (Nat.sub_add_cancel (hmargin h).le)
    hFsupport hGsupport hD hcop).symm

end

end Erdos4b

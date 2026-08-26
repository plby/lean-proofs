/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCompatibleSupport
import ErdosProblems.Erdos4b.GeneralFourierCoefficientSquare

/-!
# Removing the within-family filter from the affine coefficient kernel

The raw finite box contains every divisor quadruple at the prime cutoff.
For nonzero coefficients with all coordinates below the auxiliary prime,
the literal CRT compatibility forces the within-family coprimality used
in the Fourier calculation. Its denominator is the actual CRT period.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance rawCrtDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open scoped BigOperators

def rawDoubledCutoffDivisorTuples (ι : Type*) [Fintype ι] (P : Finset ℕ) :
    Finset ((ι ⊕ ι) → Bool → ℕ) :=
  Fintype.piFinset fun _ : ι ⊕ ι ↦ Fintype.piFinset fun _ : Bool ↦ (∏ p ∈ P, p).divisors

theorem mem_rawDoubledCutoffDivisorTuples {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (d : (ι ⊕ ι) → Bool → ℕ) :
    d ∈ rawDoubledCutoffDivisorTuples ι P ↔ ∀ i b, d i b ∣ ∏ p ∈ P, p := by
  simp [rawDoubledCutoffDivisorTuples, Fintype.mem_piFinset, Nat.mem_divisors,
    (primeFinsetProduct_pos P hP).ne']

def rawAffineDivisorKernel (H P : Finset ℕ) (m q : ℕ)
    (a b : ((H ⊕ H) → ℕ) → ℂ) : ℂ :=
  ∑ d ∈ rawDoubledCutoffDivisorTuples H P,
    if (∀ j : H, m.Coprime (Nat.lcm (d (.inr j) false) (d (.inr j) true))) ∧
      LargeGapCoordinateCrtCompatible H m q
        (fun i ↦ d (.inl i) false) (fun i ↦ d (.inr i) false)
        (fun i ↦ d (.inl i) true) (fun i ↦ d (.inr i) true) then
      a (fun i ↦ d i false) * b (fun i ↦ d i true) /
        (largeGapCoordinateCrtModulus H
          (fun i ↦ d (.inl i) false) (fun i ↦ d (.inr i) false)
          (fun i ↦ d (.inl i) true) (fun i ↦ d (.inr i) true) : ℂ)
    else 0

theorem cutoffSelbergBilinearSum_eq_rawAffineDivisorKernel
    (H P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m q : ℕ)
    (a b : ((H ⊕ H) → ℕ) → ℂ)
    (hwithin : ∀ d ∈ rawDoubledCutoffDivisorTuples H P,
      a (fun i ↦ d i false) * b (fun i ↦ d i true) ≠ 0 →
      (∀ j : H, m.Coprime (Nat.lcm (d (.inr j) false) (d (.inr j) true))) →
      LargeGapCoordinateCrtCompatible H m q
        (fun i ↦ d (.inl i) false) (fun i ↦ d (.inr i) false)
        (fun i ↦ d (.inl i) true) (fun i ↦ d (.inr i) true) →
      WithinFamilyDivisorCoprime d) :
    cutoffSelbergBilinearSum P (affineFourierCollisionEdges H m q)
        (affineFourierCompanionSwitch m) a b = rawAffineDivisorKernel H P m q a b := by
  unfold cutoffSelbergBilinearSum rawAffineDivisorKernel
  calc
    _ = ∑ d ∈ doubledCutoffDivisorTuples H P,
        if (∀ j : H, m.Coprime (Nat.lcm (d (.inr j) false) (d (.inr j) true))) ∧
          LargeGapCoordinateCrtCompatible H m q
            (fun i ↦ d (.inl i) false) (fun i ↦ d (.inr i) false)
            (fun i ↦ d (.inl i) true) (fun i ↦ d (.inr i) true) then
          a (fun i ↦ d i false) * b (fun i ↦ d i true) /
            (largeGapCoordinateCrtModulus H
              (fun i ↦ d (.inl i) false) (fun i ↦ d (.inr i) false)
              (fun i ↦ d (.inl i) true) (fun i ↦ d (.inr i) true) : ℂ)
        else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [doubledDivisorPrimeCompatible_iff_affineCrt H P hP m q d hd,
        largeGapCoordinateCrtModulus_eq_flat_lcm]
      split_ifs <;> rfl
    _ = _ := by
      change (∑ d ∈ (rawDoubledCutoffDivisorTuples H P).filter WithinFamilyDivisorCoprime, _) = _
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnot
      split_ifs with hc
      · have hzero : a (fun i ↦ d i false) * b (fun i ↦ d i true) = 0 := by
          by_contra hne
          exact hnot (Finset.mem_filter.mpr ⟨hd, hwithin d hd hne hc.1 hc.2⟩)
        rw [hzero, zero_div]
      · rfl

theorem primorial_coprime_rawCutoff_coordinate
    {ι : Type*} [Fintype ι] {P : Finset ℕ} {w : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hrough : ∀ p ∈ P, w < p)
    {d : (ι ⊕ ι) → Bool → ℕ} (hd : d ∈ rawDoubledCutoffDivisorTuples ι P)
    (i : ι ⊕ ι) (b : Bool) : (primorial w).Coprime (d i b) := by
  apply Nat.coprime_of_dvd
  intro p hp hpw hpdiv
  have hpP := (prime_dvd_primeFinsetProduct_iff P hP hp).mp
    (hpdiv.trans ((mem_rawDoubledCutoffDivisorTuples P hP d).mp hd i b))
  exact (not_lt_of_ge (hp.dvd_primorial_iff.mp hpw)) (hrough p hpP)

theorem cutoffSelbergBilinearSum_preSieved_eq_raw
    {K w m q : ℕ} (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hm : 0 < m) (hq : q.Prime) (hKw : K ≤ w)
    (a b : ((preSievedShifts K w ⊕ preSievedShifts K w) → ℕ) → ℂ)
    (hsmall : ∀ d ∈ rawDoubledCutoffDivisorTuples (preSievedShifts K w) P,
      a (fun i ↦ d i false) * b (fun i ↦ d i true) ≠ 0 → ∀ i b, d i b < q) :
    cutoffSelbergBilinearSum P (affineFourierCollisionEdges (preSievedShifts K w) m q)
        (affineFourierCompanionSwitch m) a b =
      rawAffineDivisorKernel (preSievedShifts K w) P m q a b := by
  apply cutoffSelbergBilinearSum_eq_rawAffineDivisorKernel _ P hP m q a b
  intro d hd hne hmE hc
  have hpos (i) (b) : 0 < d i b := Nat.pos_of_dvd_of_pos
    ((mem_rawDoubledCutoffDivisorTuples P hP d).mp hd i b) (primeFinsetProduct_pos P hP)
  exact withinFamilyDivisorCoprime_preSieved_of_compatible d hm hKw hpos
    (primorial_coprime_rawCutoff_coordinate hP hrough hd)
    (fun i b ↦ Nat.coprime_of_lt_prime (hpos i b).ne' (hsmall d hd hne i b) hq) hmE hc

end

end Erdos4b

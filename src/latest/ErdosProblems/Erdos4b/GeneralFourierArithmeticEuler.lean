/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierFiniteEuler
import ErdosProblems.Erdos4b.GeneralCollision

/-!
# The affine CRT arithmetic behind the finite Fourier Euler product

The collision edges are defined by the actual first/companion congruence.
The companion switch excludes precisely the primes dividing its slope.
-/

namespace Erdos4b

noncomputable section

noncomputable local instance arithmeticEulerDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open scoped BigOperators

theorem modEq_primeFinsetProduct_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a b : ℕ) :
    a ≡ b [MOD ∏ p ∈ P, p] ↔ ∀ p ∈ P, a ≡ b [MOD p] := by
  have hpair : P.toList.Pairwise Nat.Coprime := by
    apply List.Nodup.pairwise_of_forall_ne P.nodup_toList
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hP p (by simpa using hp))
      (hP q (by simpa using hq))).mpr hpq
  simpa using (Nat.modEq_list_map_prod_iff (s := id) (a := a) (b := b) hpair)

theorem modEq_divisor_primeFinsetProduct_iff
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {D : ℕ}
    (hD : D ∣ ∏ p ∈ P, p) (a b : ℕ) :
    a ≡ b [MOD D] ↔ ∀ p ∈ P, p ∣ D → a ≡ b [MOD p] := by
  constructor
  · exact fun h p hp hpD ↦ h.of_dvd hpD
  · intro h
    have hsq := (primeFinsetProduct_squarefree P hP).squarefree_of_dvd hD
    rw [← Nat.prod_primeFactors_of_squarefree hsq,
      modEq_primeFinsetProduct_iff _ (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)]
    intro p hp
    have hpD := Nat.dvd_of_mem_primeFactors hp
    have hpP := (prime_dvd_primeFinsetProduct_iff P hP
      (Nat.prime_of_mem_primeFactors hp)).mp (hpD.trans hD)
    exact h p hpP hpD

theorem coprime_divisor_primeFinsetProduct_iff
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {D : ℕ}
    (hD : D ∣ ∏ p ∈ P, p) (m : ℕ) :
    m.Coprime D ↔ ∀ p ∈ P, p ∣ D → ¬p ∣ m := by
  constructor
  · intro h p hp hpD
    exact ((hP p hp).coprime_iff_not_dvd).mp (h.coprime_dvd_right hpD).symm
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpm hpD
    exact h p ((prime_dvd_primeFinsetProduct_iff P hP hp).mp (hpD.trans hD)) hpD hpm

def affineFourierCollisionEdges (H : Finset ℕ) (m q p : ℕ) : Finset (H × H) :=
  Finset.univ.filter fun ij ↦ m * (ij.1.val * q) + 1 ≡ m * (ij.2.val * q) [MOD p]

def affineFourierCompanionSwitch (m p : ℕ) : Bool := decide (¬p ∣ m)

theorem affineFourierCollisionEdges_companion {H : Finset ℕ} {m q p : ℕ}
    (hp : p.Prime) (ij : H × H) (hij : ij ∈ affineFourierCollisionEdges H m q p) :
    affineFourierCompanionSwitch m p = true := by
  simp only [affineFourierCompanionSwitch, decide_eq_true_eq]
  intro hpm
  have hmod := (Finset.mem_filter.mp hij).2
  have ha : m * (ij.1.val * q) ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hpm _)
  have hb : m * (ij.2.val * q) ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hpm _)
  have h10 : 1 ≡ 0 [MOD p] := by simpa using ((ha.add_right 1).symm.trans hmod).trans hb
  exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp h10)

theorem withinFamilyDivisorCoprime_lcm {ι : Type*}
    {d : (ι ⊕ ι) → Bool → ℕ} (hcop : WithinFamilyDivisorCoprime d) :
    (∀ {i j : ι}, i ≠ j → (Nat.lcm (d (.inl i) false) (d (.inl i) true)).Coprime
      (Nat.lcm (d (.inl j) false) (d (.inl j) true))) ∧
    (∀ {i j : ι}, i ≠ j → (Nat.lcm (d (.inr i) false) (d (.inr i) true)).Coprime
      (Nat.lcm (d (.inr j) false) (d (.inr j) true))) := by
  constructor
  · intro i j hij
    exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
      (hcop.1 i j hij false false) (hcop.1 i j hij false true)
      (hcop.1 i j hij true false) (hcop.1 i j hij true true)
  · intro i j hij
    exact BoundedGaps.Maynard.coprime_lcm_lcm_of_four
      (hcop.2 i j hij false false) (hcop.2 i j hij false true)
      (hcop.2 i j hij true false) (hcop.2 i j hij true true)

theorem doubledDivisorPrimeCompatible_iff_affineCrt
    (H P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m q : ℕ)
    (d : (H ⊕ H) → Bool → ℕ) (hd : d ∈ doubledCutoffDivisorTuples H P) :
    DoubledDivisorPrimeCompatible P (affineFourierCollisionEdges H m q)
        (affineFourierCompanionSwitch m) d ↔
      (∀ j : H, m.Coprime (Nat.lcm (d (.inr j) false) (d (.inr j) true))) ∧
        LargeGapCoordinateCrtCompatible H m q
          (fun i ↦ d (.inl i) false) (fun j ↦ d (.inr j) false)
          (fun i ↦ d (.inl i) true) (fun j ↦ d (.inr j) true) := by
  obtain ⟨hdiv, hcop⟩ := (mem_doubledCutoffDivisorTuples P hP d).mp hd
  have hlcmdiv (i : H ⊕ H) : Nat.lcm (d i false) (d i true) ∣ ∏ p ∈ P, p :=
    Nat.lcm_dvd (hdiv i false) (hdiv i true)
  have hpos (i : H ⊕ H) : 0 < Nat.lcm (d i false) (d i true) := by
    have hsq (b : Bool) := (primeFinsetProduct_squarefree P hP).squarefree_of_dvd (hdiv i b)
    exact Nat.lcm_pos (hsq false).ne_zero.bot_lt (hsq true).ne_zero.bot_lt
  obtain ⟨hDD, hEE⟩ := withinFamilyDivisorCoprime_lcm hcop
  constructor
  · intro hprime
    have hmE : ∀ j : H, m.Coprime (Nat.lcm (d (.inr j) false) (d (.inr j) true)) := by
      intro j
      apply (coprime_divisor_primeFinsetProduct_iff P hP (hlcmdiv (.inr j)) m).mpr
      intro p hp hpE
      simpa only [affineFourierCompanionSwitch, decide_eq_true_eq] using (hprime ⟨p, hp⟩).1 j hpE
    refine ⟨hmE, ?_⟩
    apply (largeGapCoordinateCrtCompatible_iff_cross_affine
      (fun i ↦ hpos (.inl i)) (fun j ↦ hpos (.inr j)) hmE hDD hEE).mpr
    intro i j
    apply (modEq_divisor_primeFinsetProduct_iff P hP
      ((Nat.gcd_dvd_left _ _).trans (hlcmdiv (.inl i))) _ _).mpr
    intro p hp hpG
    have hpair := Nat.dvd_gcd_iff.mp hpG
    exact (Finset.mem_filter.mp ((hprime ⟨p, hp⟩).2 i j hpair.1 hpair.2)).2
  · rintro ⟨hmE, hcrt⟩ p
    have hcross := (largeGapCoordinateCrtCompatible_iff_cross_affine
      (fun i ↦ hpos (.inl i)) (fun j ↦ hpos (.inr j)) hmE hDD hEE).mp hcrt
    constructor
    · intro j hpE
      have hnot := (coprime_divisor_primeFinsetProduct_iff P hP (hlcmdiv (.inr j)) m).mp
        (hmE j) p p.property hpE
      simpa only [affineFourierCompanionSwitch, decide_eq_true_eq] using hnot
    · intro i j hpD hpE
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcross i j).of_dvd (Nat.dvd_gcd hpD hpE)⟩

theorem largeGapCoordinateCrtModulus_eq_flat_lcm
    (H : Finset ℕ) (d : (H ⊕ H) → Bool → ℕ) :
    largeGapCoordinateCrtModulus H
        (fun i ↦ d (.inl i) false) (fun j ↦ d (.inr j) false)
        (fun i ↦ d (.inl i) true) (fun j ↦ d (.inr j) true) =
      (Finset.univ : Finset ((H ⊕ H) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) := by
  have hmod (i : H ⊕ H) :
      largeGapCrtModulus H (fun i ↦ d (.inl i) false) (fun j ↦ d (.inr j) false)
          (fun i ↦ d (.inl i) true) (fun j ↦ d (.inr j) true) i =
        Nat.lcm (d i false) (d i true) := by cases i <;> rfl
  unfold largeGapCoordinateCrtModulus
  rw [show largeGapCrtModulus H (fun i ↦ d (.inl i) false) (fun j ↦ d (.inr j) false)
      (fun i ↦ d (.inl i) true) (fun j ↦ d (.inr j) true) =
        (fun i ↦ Nat.lcm (d i false) (d i true)) from funext hmod]
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro i hi
    exact Nat.lcm_dvd (Finset.dvd_lcm (Finset.mem_univ (i, false)))
      (Finset.dvd_lcm (Finset.mem_univ (i, true)))
  · apply Finset.lcm_dvd
    rintro ⟨i, b⟩ hib
    have h := Finset.dvd_lcm (s := (Finset.univ : Finset (H ⊕ H)))
      (f := fun i ↦ Nat.lcm (d i false) (d i true)) (Finset.mem_univ i)
    cases b
    · exact (Nat.dvd_lcm_left _ _).trans h
    · exact (Nat.dvd_lcm_right _ _).trans h

theorem sum_affineCrt_divisorFourierWeight_eq_finiteEulerProduct
    (H P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m q : ℕ)
    (s : (H ⊕ H) → Bool → ℂ) :
    (∑ d ∈ doubledCutoffDivisorTuples H P,
      if (∀ j : H, m.Coprime (Nat.lcm (d (.inr j) false) (d (.inr j) true))) ∧
        LargeGapCoordinateCrtCompatible H m q
          (fun i ↦ d (.inl i) false) (fun j ↦ d (.inr j) false)
          (fun i ↦ d (.inl i) true) (fun j ↦ d (.inr j) true) then
        doubledDivisorFourierWeight d s else 0) =
      ∏ p ∈ P, doubledFourierLocalPolynomial Finset.univ (affineFourierCollisionEdges H m q p)
        (affineFourierCompanionSwitch m p) p
        (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inl i) false))
          (primeFourierPower p (s (.inl i) true)))
        (fun i ↦ selbergPairPolynomial (primeFourierPower p (s (.inr i) false))
          (primeFourierPower p (s (.inr i) true))) := by
  rw [← sum_doubledDivisorFourierWeight_eq_finiteEulerProduct P hP
    (affineFourierCollisionEdges H m q) (affineFourierCompanionSwitch m)
    (fun p hp ij hij ↦ affineFourierCollisionEdges_companion (hP p hp) ij hij) s]
  apply Finset.sum_congr rfl
  intro d hd
  rw [doubledDivisorPrimeCompatible_iff_affineCrt H P hP m q d hd]
  split_ifs <;> rfl

end

end Erdos4b

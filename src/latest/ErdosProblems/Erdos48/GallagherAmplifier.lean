/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherImprimitiveGauss
import BoundedGaps.BombieriVinogradov.Analytic.PositiveDivisorPairReindex
import BoundedGaps.Maynard.MaynardPreSievedTotientMean

/-!
# Gallagher's finite rough-support amplifier

This file proves the exact horizontal Bombieri--Davenport--Gallagher
amplifier.  The all-character additive large sieve is reindexed by primitive
conductors, squarefree coprime multipliers are retained, and the imprimitive
Gauss norm turns their total weight into the squarefree reciprocal-totient
mean.  The final interface applies directly to prime-supported polynomials
whose support lies above the amplifier level.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

noncomputable def primitiveTwistSquareMass
    (q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ psi : primitiveCharacters q,
    ‖∑ n ∈ s, c n * psi.1 n‖ ^ 2

noncomputable def inducedGaussPrimitiveMass
    (q r : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  if hqr : q * r = 0 then 0 else
    letI : NeZero (q * r) := ⟨hqr⟩
    ∑ psi : primitiveCharacters q,
      ‖gaussSum
          (DirichletCharacter.changeLevel
            (Nat.dvd_mul_right q r) psi.1)⁻¹
          ZMod.stdAddChar *
        ∑ n ∈ s, c n * psi.1 n‖ ^ 2

theorem inducedGaussPrimitiveMass_nonneg
    (q r : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) :
    0 ≤ inducedGaussPrimitiveMass q r s c := by
  classical
  unfold inducedGaussPrimitiveMass
  split
  · exact le_rfl
  · exact Finset.sum_nonneg fun psi _hpsi ↦ sq_nonneg _

noncomputable def roughAmplifierCoefficient (q A : ℕ) : ℝ :=
  (q : ℝ) / Nat.totient q * squarefreeCoprimeInvTotientMean q A

theorem roughAmplifierCoefficient_nonneg (q A : ℕ) :
    0 ≤ roughAmplifierCoefficient q A := by
  classical
  unfold roughAmplifierCoefficient squarefreeCoprimeInvTotientMean
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro r _hr
  split <;> positivity

def rectangularSquarefreeCoprimePairs (Q A : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 Q ×ˢ Finset.Ioc 0 A).filter
    (fun p ↦ Squarefree p.2 ∧ p.1.Coprime p.2)

theorem sum_invTotient_gaussWeighted_eq_positiveFactorPairs
    (R : ℕ) (s : Finset ℕ) (c : ℕ → ℂ)
    (hcop : ∀ m ∈ Finset.Ioc 0 R, ∀ n ∈ s, n.Coprime m) :
    (∑ m ∈ Finset.Ioc 0 R,
      (Nat.totient m : ℝ)⁻¹ * gaussWeightedAllCharacterMass m s c) =
      ∑ p ∈ positiveFactorPairs R,
        ((Nat.totient (p.1 * p.2) : ℝ)⁻¹ *
          inducedGaussPrimitiveMass p.1 p.2 s c) := by
  classical
  let F : ∀ {m q : ℕ}, q ∣ m → primitiveCharacters q → ℝ :=
    fun {m q} hq psi =>
      if hm : m = 0 then 0 else
        letI : NeZero m := ⟨hm⟩
        (Nat.totient m : ℝ)⁻¹ *
          ‖gaussSum (DirichletCharacter.changeLevel hq psi.1)⁻¹
              ZMod.stdAddChar *
            ∑ n ∈ s, c n * psi.1 n‖ ^ 2
  have hlevel (m : ℕ) (hm : m ∈ Finset.Ioc 0 R) :
      (Nat.totient m : ℝ)⁻¹ * gaussWeightedAllCharacterMass m s c =
        ∑ q : m.divisors,
          ∑ psi : primitiveCharacters q.1,
            F (Nat.dvd_of_mem_divisors q.2) psi := by
    have hmpos : 0 < m := (Finset.mem_Ioc.mp hm).1
    let : NeZero m := ⟨hmpos.ne'⟩
    rw [gaussWeightedAllCharacterMass, dif_neg hmpos.ne']
    rw [sum_characters_eq_sum_divisor_primitive hmpos]
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro q
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro psi
    unfold F
    rw [dif_neg hmpos.ne']
    rw [sum_mul_changeLevel_eq_of_coprime
      (Nat.dvd_of_mem_divisors q.2) psi.1 s c
      (fun n hn => hcop m hm n hn)]
  calc
    (∑ m ∈ Finset.Ioc 0 R,
        (Nat.totient m : ℝ)⁻¹ * gaussWeightedAllCharacterMass m s c) =
        ∑ m ∈ Finset.Ioc 0 R,
          ∑ q : m.divisors,
            ∑ psi : primitiveCharacters q.1,
              F (Nat.dvd_of_mem_divisors q.2) psi := by
      apply Finset.sum_congr rfl
      exact hlevel
    _ = ∑ p ∈ positiveFactorPairs R,
          ∑ psi : primitiveCharacters p.1,
            F (Nat.dvd_mul_right p.1 p.2) psi :=
      sum_primitive_conductors_up_to_eq_sum_positiveFactorPairs F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hppos : 0 < p.1 * p.2 := by
        rcases Finset.mem_filter.mp hp with ⟨hprod, _⟩
        rcases Finset.mem_product.mp hprod with ⟨hq, hr⟩
        exact Nat.mul_pos (Finset.mem_Ioc.mp hq).1
          (Finset.mem_Ioc.mp hr).1
      unfold F inducedGaussPrimitiveMass
      rw [dif_neg hppos.ne']
      simp_rw [dif_neg hppos.ne']
      rw [Finset.mul_sum]

theorem inducedGaussPrimitiveMass_eq_mul
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hcop : q.Coprime r) (hrsq : Squarefree r)
    (s : Finset ℕ) (c : ℕ → ℂ) :
    inducedGaussPrimitiveMass q r s c =
      (q : ℝ) * primitiveTwistSquareMass q s c := by
  classical
  have hqr : q * r ≠ 0 := Nat.mul_ne_zero hq.ne' hr.ne'
  let : NeZero q := ⟨hq.ne'⟩
  let : NeZero r := ⟨hr.ne'⟩
  let : NeZero (q * r) := ⟨hqr⟩
  rw [inducedGaussPrimitiveMass, dif_neg hqr]
  unfold primitiveTwistSquareMass
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro psi
  have hpsiInv : psi.1⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive,
      DirichletCharacter.conductor_inv]
    exact psi.2
  have hchange :
      (DirichletCharacter.changeLevel
        (Nat.dvd_mul_right q r) psi.1)⁻¹ =
        DirichletCharacter.changeLevel
          (Nat.dvd_mul_right q r) psi.1⁻¹ := by
    exact (map_inv (DirichletCharacter.changeLevel
      (R := ℂ) (Nat.dvd_mul_right q r)) psi.1).symm
  rw [hchange, norm_mul, mul_pow]
  rw [norm_gaussSum_changeLevel_sq_eq hcop hrsq psi.1⁻¹ hpsiInv
    ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar (q * r))]

theorem roughAmplifierCoefficient_mul_primitiveMass_eq
    {q A : ℕ} (hq : 0 < q) (s : Finset ℕ) (c : ℕ → ℂ) :
    roughAmplifierCoefficient q A * primitiveTwistSquareMass q s c =
      ∑ r ∈ Finset.Ioc 0 A,
        if hgood : Squarefree r ∧ r.Coprime q then
          (Nat.totient (q * r) : ℝ)⁻¹ *
            inducedGaussPrimitiveMass q r s c
        else 0 := by
  classical
  have hinterval : Finset.Icc 1 A = Finset.Ioc 0 A := by
    ext r
    simp
    omega
  rw [roughAmplifierCoefficient,
    squarefreeCoprimeInvTotientMean, hinterval]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hrmem
  by_cases hgood : Squarefree r ∧ r.Coprime q
  · rw [if_pos hgood, dif_pos hgood]
    have hr : 0 < r := (Finset.mem_Ioc.mp hrmem).1
    rw [inducedGaussPrimitiveMass_eq_mul hq hr hgood.2.symm
      hgood.1 s c]
    rw [Nat.totient_mul hgood.2.symm]
    simp only [div_eq_mul_inv, Nat.cast_mul]
    ring
  · rw [if_neg hgood, dif_neg hgood]
    ring

theorem sum_roughAmplifier_eq_rectangularPairs
    (Q A : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      roughAmplifierCoefficient q A * primitiveTwistSquareMass q s c) =
      ∑ p ∈ rectangularSquarefreeCoprimePairs Q A,
        (Nat.totient (p.1 * p.2) : ℝ)⁻¹ *
          inducedGaussPrimitiveMass p.1 p.2 s c := by
  rw [rectangularSquarefreeCoprimePairs, Finset.sum_filter,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  rw [roughAmplifierCoefficient_mul_primitiveMass_eq
    (Finset.mem_Ioc.mp hq).1 s c]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hgood : Squarefree r ∧ r.Coprime q
  · simp [hgood, Nat.coprime_comm]
  · simp [hgood, Nat.coprime_comm]

theorem rectangularSquarefreeCoprimePairs_subset_positiveFactorPairs
    (Q A : ℕ) :
    rectangularSquarefreeCoprimePairs Q A ⊆
      positiveFactorPairs (Q * A) := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpbox, _hgood⟩
  rcases Finset.mem_product.mp hpbox with ⟨hq, hr⟩
  have hqBounds := Finset.mem_Ioc.mp hq
  have hrBounds := Finset.mem_Ioc.mp hr
  have hprod : p.1 * p.2 ≤ Q * A :=
    Nat.mul_le_mul hqBounds.2 hrBounds.2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hprod⟩
  · exact Finset.mem_Ioc.mpr ⟨hqBounds.1,
      (Nat.le_mul_of_pos_right p.1 hrBounds.1).trans hprod⟩
  · exact Finset.mem_Ioc.mpr ⟨hrBounds.1,
      (Nat.le_mul_of_pos_left p.2 hqBounds.1).trans hprod⟩

theorem sum_roughAmplifier_le_positiveFactorPairs
    (Q A : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      roughAmplifierCoefficient q A * primitiveTwistSquareMass q s c) ≤
      ∑ p ∈ positiveFactorPairs (Q * A),
        (Nat.totient (p.1 * p.2) : ℝ)⁻¹ *
          inducedGaussPrimitiveMass p.1 p.2 s c := by
  rw [sum_roughAmplifier_eq_rectangularPairs]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (rectangularSquarefreeCoprimePairs_subset_positiveFactorPairs Q A)
  intro p _hp _hnot
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (inducedGaussPrimitiveMass_nonneg p.1 p.2 s c)

/-- The exact horizontal Bombieri--Davenport amplifier before using a lower
bound for its arithmetic coefficient. -/
theorem sum_roughAmplifier_primitiveMass_le
    (Q A m0 N : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (c : ℕ → ℂ)
    (hcop : ∀ m ∈ Finset.Ioc 0 (Q * A), ∀ n ∈ s, n.Coprime m) :
    (∑ q ∈ Finset.Ioc 0 Q,
      roughAmplifierCoefficient q A * primitiveTwistSquareMass q s c) ≤
      ((N : ℝ) + (Q * A : ℕ) ^ 2) *
        ∑ n ∈ s, ‖c n‖ ^ 2 := by
  calc
    _ ≤ ∑ p ∈ positiveFactorPairs (Q * A),
          (Nat.totient (p.1 * p.2) : ℝ)⁻¹ *
            inducedGaussPrimitiveMass p.1 p.2 s c :=
      sum_roughAmplifier_le_positiveFactorPairs Q A s c
    _ = ∑ m ∈ Finset.Ioc 0 (Q * A),
          (Nat.totient m : ℝ)⁻¹ *
            gaussWeightedAllCharacterMass m s c :=
      (sum_invTotient_gaussWeighted_eq_positiveFactorPairs
        (Q * A) s c hcop).symm
    _ ≤ _ :=
      sum_invTotient_mul_gaussWeighted_allCharacters_subset_Ioc_le
        (Q * A) m0 N s hs c hcop

/-- Prime support above the amplifier level automatically supplies all the
coprimality hypotheses in `sum_roughAmplifier_primitiveMass_le`. -/
theorem sum_roughAmplifier_primitiveMass_primeSupport_le
    (Q A m0 N : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (c : ℕ → ℂ)
    (hprime : ∀ n ∈ s, n.Prime)
    (hrough : ∀ n ∈ s, Q * A < n) :
    (∑ q ∈ Finset.Ioc 0 Q,
      roughAmplifierCoefficient q A * primitiveTwistSquareMass q s c) ≤
      ((N : ℝ) + (Q * A : ℕ) ^ 2) *
        ∑ n ∈ s, ‖c n‖ ^ 2 := by
  apply sum_roughAmplifier_primitiveMass_le Q A m0 N s hs c
  intro m hm n hn
  have hmBounds := Finset.mem_Ioc.mp hm
  apply (hprime n hn).coprime_iff_not_dvd.mpr
  apply Nat.not_dvd_of_pos_of_lt hmBounds.1
  exact hmBounds.2.trans_lt (hrough n hn)

end Erdos48

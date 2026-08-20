/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.HybridLargeSieve
import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.CharacterLargeSieve

/-!
# Rough-support Fourier reduction for Gallagher's large sieve

The Gauss-sum transform used in the Bombieri--Davenport mean value theorem
does not require a primitive character when every active coefficient is
coprime to the modulus.  This file proves that exact transform and the
corresponding invariance under change of level.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

private theorem sum_units_invCharacter_mul_stdAddChar_eq_sum_zmod_general
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (n : ZMod q) :
    (∑ u : (ZMod q)ˣ,
      chi⁻¹ (u : ZMod q) * ZMod.stdAddChar ((u : ZMod q) * n)) =
      ∑ a : ZMod q, chi⁻¹ a * ZMod.stdAddChar (a * n) := by
  classical
  letI : Fintype (IsUnit.submonoid (ZMod q)) := Fintype.ofFinite _
  calc
    (∑ u : (ZMod q)ˣ,
        chi⁻¹ (u : ZMod q) * ZMod.stdAddChar ((u : ZMod q) * n)) =
        ∑ a : IsUnit.submonoid (ZMod q),
          chi⁻¹ (a : ZMod q) * ZMod.stdAddChar ((a : ZMod q) * n) := by
      apply Fintype.sum_equiv
        (Submonoid.unitsTypeEquivIsUnitSubmonoid (M := ZMod q)).toEquiv
      intro u
      rfl
    _ = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
        chi⁻¹ a * ZMod.stdAddChar (a * n) := by
      exact (Finset.sum_subtype
        (p := IsUnit) ((Finset.univ : Finset (ZMod q)).filter IsUnit)
        (by simp) (fun a ↦ chi⁻¹ a * ZMod.stdAddChar (a * n))).symm
    _ = ∑ a : ZMod q, chi⁻¹ a * ZMod.stdAddChar (a * n) := by
      apply Finset.sum_filter_of_ne
      intro a _ha hterm
      by_contra ha
      simp [MulChar.map_nonunit chi⁻¹ ha] at hterm

/-- Fourier expansion of an arbitrary Dirichlet character at an integer
coprime to its level. -/
theorem fourier_expansion_of_coprime
    {q n : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hn : n.Coprime q) :
    (∑ a : ZMod q, chi⁻¹ a *
        ZMod.stdAddChar (a * (n : ZMod q))) =
      chi n * gaussSum chi⁻¹ ZMod.stdAddChar := by
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime n hn
  have hshift :
      (∑ a : ZMod q, chi⁻¹ a *
          ZMod.stdAddChar (a * (n : ZMod q))) =
        gaussSum chi⁻¹ (ZMod.stdAddChar.mulShift u) := by
    unfold gaussSum
    apply Finset.sum_congr rfl
    intro a _ha
    simp only [AddChar.mulShift_apply, u, ZMod.coe_unitOfCoprime]
    ring
  rw [hshift, gaussSum_mulShift_eq]
  have hu : chi⁻¹⁻¹ (u : ZMod q) = chi n := by
    simp only [inv_inv, u, ZMod.coe_unitOfCoprime]
  rw [hu]

/-- On coprime support, the unit-group character transform is exactly a
Gauss sum times the original character twist. -/
theorem dirichletCharacterUnitTransform_additive_eq_gaussSum_mul_twist_of_coprime
    {q : ℕ} [NeZero q] (s : Finset ℕ) (c : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q)
    (hcop : ∀ n ∈ s, n.Coprime q) :
    dirichletCharacterUnitTransform
        (fun u ↦ ∑ n ∈ s,
          c n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))) chi =
      gaussSum chi⁻¹ ZMod.stdAddChar *
        ∑ n ∈ s, c n * chi n := by
  unfold dirichletCharacterUnitTransform
  calc
    (∑ u : (ZMod q)ˣ,
        chi⁻¹ (u : ZMod q) *
          ∑ n ∈ s,
            c n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))) =
        ∑ u : (ZMod q)ˣ,
          ∑ n ∈ s,
            chi⁻¹ (u : ZMod q) *
              (c n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [Finset.mul_sum]
    _ = ∑ n ∈ s,
        ∑ u : (ZMod q)ˣ,
          chi⁻¹ (u : ZMod q) *
            (c n * ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q))) := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ s, c n *
        ∑ u : (ZMod q)ˣ,
          chi⁻¹ (u : ZMod q) *
            ZMod.stdAddChar ((u : ZMod q) * (n : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      ring
    _ = ∑ n ∈ s, c n *
        (chi n * gaussSum chi⁻¹ ZMod.stdAddChar) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sum_units_invCharacter_mul_stdAddChar_eq_sum_zmod_general]
      rw [fourier_expansion_of_coprime chi (hcop n hn)]
    _ = gaussSum chi⁻¹ ZMod.stdAddChar *
        ∑ n ∈ s, c n * chi n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring

/-- Inducing a character to a larger level does not change a polynomial
whose support is coprime to the larger level. -/
theorem sum_mul_changeLevel_eq_of_coprime
    {d q : ℕ} [NeZero q] (hd : d ∣ q)
    (psi : DirichletCharacter ℂ d) (s : Finset ℕ) (c : ℕ → ℂ)
    (hcop : ∀ n ∈ s, n.Coprime q) :
    (∑ n ∈ s, c n * (DirichletCharacter.changeLevel hd psi) n) =
      ∑ n ∈ s, c n * psi n := by
  apply Finset.sum_congr rfl
  intro n hn
  have hchange := DirichletCharacter.changeLevel_eq_cast_of_dvd' psi hd
    (a := (n : ℤ)) (Nat.Coprime.isCoprime (hcop n hn))
  rw [show (DirichletCharacter.changeLevel hd psi) n = psi n by
    simpa only [Int.cast_natCast] using hchange]

private theorem Icc_one_eq_Ioc_zero (Q : ℕ) :
    Finset.Icc 1 Q = Finset.Ioc 0 Q := by
  ext q
  simp
  omega

private theorem sum_positiveModuliUpTo_eq_sum_Ioc
    (Q : ℕ) (f : ℕ → ℝ) :
    (∑ q : positiveModuliUpTo Q, f q.1) =
      ∑ q ∈ Finset.Ioc 0 Q, f q := by
  calc
    (∑ q : positiveModuliUpTo Q, f q.1) =
        ∑ q ∈ Finset.Icc 1 Q, f q :=
      (Finset.sum_subtype (p := fun q => q ∈ Finset.Icc 1 Q)
        (Finset.Icc 1 Q) (by simp) f).symm
    _ = ∑ q ∈ Finset.Ioc 0 Q, f q := by rw [Icc_one_eq_Ioc_zero]

private theorem sum_units_eq_sum_reduced
    (Q : ℕ) (f : reducedFractionIndices Q → ℝ) :
    (∑ q : positiveModuliUpTo Q, ∑ u : (ZMod q.1)ˣ, f ⟨q, u⟩) =
      ∑ z : reducedFractionIndices Q, f z := by
  rw [← Finset.sum_sigma]
  apply Finset.sum_congr
  · ext z
    simp
  · intro z _hz
    rfl

private theorem sum_zeroExtension_mul
    (s t : Finset ℕ) (hst : s ⊆ t) (c f : ℕ → ℂ) :
    (∑ n ∈ t, (if n ∈ s then c n else 0) * f n) =
      ∑ n ∈ s, c n * f n := by
  calc
    (∑ n ∈ t, (if n ∈ s then c n else 0) * f n) =
        ∑ n ∈ s, (if n ∈ s then c n else 0) * f n := by
      symm
      apply Finset.sum_subset hst
      intro n _hnt hns
      simp [hns]
    _ = ∑ n ∈ s, c n * f n := by
      apply Finset.sum_congr rfl
      intro n hns
      simp [hns]

private theorem sum_norm_sq_zeroExtension
    (s t : Finset ℕ) (hst : s ⊆ t) (c : ℕ → ℂ) :
    (∑ n ∈ t, ‖if n ∈ s then c n else 0‖ ^ 2) =
      ∑ n ∈ s, ‖c n‖ ^ 2 := by
  calc
    (∑ n ∈ t, ‖if n ∈ s then c n else 0‖ ^ 2) =
        ∑ n ∈ s, ‖if n ∈ s then c n else 0‖ ^ 2 := by
      symm
      apply Finset.sum_subset hst
      intro n _hnt hns
      simp [hns]
    _ = ∑ n ∈ s, ‖c n‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hns
      simp [hns]

/-- The Gauss-weighted square mass of all characters at one modulus,
totalized to zero at modulus zero. -/
noncomputable def gaussWeightedAllCharacterMass
    (q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ chi : DirichletCharacter ℂ q,
      ‖gaussSum chi⁻¹ ZMod.stdAddChar *
        ∑ n ∈ s, c n * chi n‖ ^ 2

/-- Exact Bombieri--Davenport additive reduction before conductor
amplification.  On support coprime to every positive modulus through `Q`,
the reciprocal-totient weighted all-character Gauss mass is bounded by the
usual reduced-fraction large-sieve coefficient. -/
theorem sum_invTotient_mul_gaussWeighted_allCharacters_subset_Ioc_le
    (Q m0 N : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (c : ℕ → ℂ)
    (hcop : ∀ q ∈ Finset.Ioc 0 Q, ∀ n ∈ s, n.Coprime q) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (Nat.totient q : ℝ)⁻¹ *
        gaussWeightedAllCharacterMass q s c) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  classical
  have hfixed :
      (∑ q : positiveModuliUpTo Q,
        (Nat.totient q.1 : ℝ)⁻¹ *
          gaussWeightedAllCharacterMass q.1 s c) =
        ∑ q : positiveModuliUpTo Q,
          ∑ u : (ZMod q.1)ˣ,
            ‖∑ n ∈ s,
              c n * ZMod.stdAddChar
                ((u : ZMod q.1) * (n : ZMod q.1))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro q _hq
    have hqne : q.1 ≠ 0 := NeZero.ne q.1
    rw [gaussWeightedAllCharacterMass, dif_neg hqne]
    let b : (ZMod q.1)ˣ → ℂ := fun u ↦
      ∑ n ∈ s, c n * ZMod.stdAddChar
        ((u : ZMod q.1) * (n : ZMod q.1))
    have htransform (chi : DirichletCharacter ℂ q.1) :
        dirichletCharacterUnitTransform b chi =
          gaussSum chi⁻¹ ZMod.stdAddChar *
            ∑ n ∈ s, c n * chi n := by
      apply dirichletCharacterUnitTransform_additive_eq_gaussSum_mul_twist_of_coprime
      intro n hn
      apply hcop q.1
      have hqmem := q.2
      simp only [Finset.mem_Icc] at hqmem
      simp only [Finset.mem_Ioc]
      omega
      exact hn
    have hparseval := sum_norm_sq_dirichletCharacterUnitTransform b
    simp_rw [htransform] at hparseval
    have hphi : (0 : ℝ) < Nat.totient q.1 := by
      exact_mod_cast Nat.totient_pos.mpr q.1.pos_of_neZero
    change (Nat.totient q.1 : ℝ)⁻¹ *
        (∑ chi : DirichletCharacter ℂ q.1,
          ‖gaussSum chi⁻¹ ZMod.stdAddChar *
            ∑ n ∈ s, c n * chi n‖ ^ 2) =
      ∑ u : (ZMod q.1)ˣ, ‖b u‖ ^ 2
    rw [hparseval]
    field_simp
  let d : ℕ → ℂ := fun n => if n ∈ s then c n else 0
  have hadditive (z : reducedFractionIndices Q) :
      (∑ n ∈ Finset.Ioc m0 (m0 + N),
          d n * ZMod.stdAddChar
            ((z.2 : ZMod z.1.1) * (n : ZMod z.1.1))) =
        ∑ n ∈ s, c n * ZMod.stdAddChar
          ((z.2 : ZMod z.1.1) * (n : ZMod z.1.1)) := by
    simpa only [d] using sum_zeroExtension_mul s
      (Finset.Ioc m0 (m0 + N)) hs c
      (fun n ↦ ZMod.stdAddChar
        ((z.2 : ZMod z.1.1) * (n : ZMod z.1.1)))
  have henergy :
      (∑ n ∈ Finset.Ioc m0 (m0 + N), ‖d n‖ ^ 2) =
        ∑ n ∈ s, ‖c n‖ ^ 2 := by
    simpa only [d] using sum_norm_sq_zeroExtension s
      (Finset.Ioc m0 (m0 + N)) hs c
  have hlarge := sum_norm_sq_reducedFraction_stdAddChar_Ioc_le Q m0 N d
  simp_rw [hadditive] at hlarge
  rw [henergy] at hlarge
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (Nat.totient q : ℝ)⁻¹ *
          gaussWeightedAllCharacterMass q s c) =
        ∑ q : positiveModuliUpTo Q,
          (Nat.totient q.1 : ℝ)⁻¹ *
            gaussWeightedAllCharacterMass q.1 s c :=
      (sum_positiveModuliUpTo_eq_sum_Ioc Q fun q =>
        (Nat.totient q : ℝ)⁻¹ *
          gaussWeightedAllCharacterMass q s c).symm
    _ = ∑ q : positiveModuliUpTo Q,
          ∑ u : (ZMod q.1)ˣ,
            ‖∑ n ∈ s, c n * ZMod.stdAddChar
              ((u : ZMod q.1) * (n : ZMod q.1))‖ ^ 2 := hfixed
    _ = ∑ z : reducedFractionIndices Q,
          ‖∑ n ∈ s, c n * ZMod.stdAddChar
            ((z.2 : ZMod z.1.1) * (n : ZMod z.1.1))‖ ^ 2 := by
      exact sum_units_eq_sum_reduced Q fun z =>
        ‖∑ n ∈ s, c n * ZMod.stdAddChar
          ((z.2 : ZMod z.1.1) * (n : ZMod z.1.1))‖ ^ 2
    _ ≤ _ := hlarge

end Erdos48

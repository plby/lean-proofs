/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.AnnularTail
import BoundedGaps.BombieriVinogradov.Analytic.DirichletLocalDivisorMass

/-!
# The finite radius-six zero multiset

This packages the ordinary divisor in the fixed disk centered at `2+it` as
a natural-valued `Finsupp`.  The package is convenient for the finite
power-sum and annular-tail arguments, while the comparison lemmas retain the
exact divisor used by the fixed-disk logarithmic-derivative theorem.
-/

namespace Erdos48

open Complex Metric Set
open BoundedGaps.Maynard

noncomputable section

noncomputable def radiusSixZeroMultiplicity
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (t : ℝ) : ℂ → ℕ := fun rho ↦
  if dist rho ((2 : ℂ) + t * I) ≤ 6 then
    analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
  else 0

theorem radiusSixZeroMultiplicity_hasFiniteSupport
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) :
    Function.HasFiniteSupport (radiusSixZeroMultiplicity chi t) := by
  apply (divisor_LFunction_closedBall_support_finite
    (character_ne_one_of_isPrimitive hq chi hchi)
    ((2 : ℂ) + t * I) 6).subset
  intro rho hrho
  rw [Function.mem_support] at hrho ⊢
  rw [divisor_LFunction_radiusSix_apply hq chi hchi t rho]
  exact_mod_cast hrho

noncomputable def radiusSixZeroFinsupp
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) : ℂ →₀ ℕ :=
  Finsupp.ofSupportFinite (radiusSixZeroMultiplicity chi t)
    (radiusSixZeroMultiplicity_hasFiniteSupport hq chi hchi t)

@[simp] theorem radiusSixZeroFinsupp_apply
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) (rho : ℂ) :
    radiusSixZeroFinsupp hq chi hchi t rho =
      radiusSixZeroMultiplicity chi t rho := rfl

theorem radiusSixZeroFinsupp_apply_eq_divisor
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) (rho : ℂ) :
    (radiusSixZeroFinsupp hq chi hchi t rho : ℤ) =
      MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
        (closedBall ((2 : ℂ) + t * I) 6) rho := by
  rw [radiusSixZeroFinsupp_apply, radiusSixZeroMultiplicity,
    divisor_LFunction_radiusSix_apply hq chi hchi t rho]

/-- The natural multiplicity sum of the radius-six `Finsupp` is the
ordinary integer divisor mass from the analytic library. -/
theorem radiusSixZeroFinsupp_sum_eq_divisor_finsum
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) :
    ((radiusSixZeroFinsupp hq chi hchi t).sum
        (fun _ m ↦ (m : ℤ))) =
      ∑ᶠ rho : ℂ,
        MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
          (closedBall ((2 : ℂ) + t * I) 6) rho := by
  let D := radiusSixZeroFinsupp hq chi hchi t
  rw [Finsupp.sum]
  symm
  calc
    (∑ᶠ rho : ℂ,
        MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
          (closedBall ((2 : ℂ) + t * I) 6) rho) =
        ∑ rho ∈ D.support,
          MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
            (closedBall ((2 : ℂ) + t * I) 6) rho := by
      apply finsum_eq_sum_of_support_subset
      intro rho hrho
      rw [Function.mem_support] at hrho
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro hzero
      apply hrho
      rw [← radiusSixZeroFinsupp_apply_eq_divisor hq chi hchi t rho,
        show radiusSixZeroFinsupp hq chi hchi t rho = D rho by rfl,
        hzero]
      norm_num
    _ = ∑ rho ∈ D.support, (D rho : ℤ) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      exact (radiusSixZeroFinsupp_apply_eq_divisor
        hq chi hchi t rho).symm

/-- Reindex a reciprocal power of the ordinary radius-six divisor by the
natural-valued zero `Finsupp`. -/
theorem radiusSixZeroFinsupp_sum_div_pow_eq_divisor_finsum
    {q j : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t : ℝ) (s : ℂ) :
    (radiusSixZeroFinsupp hq chi hchi t).sum
        (fun rho m ↦ (m : ℂ) / (s - rho) ^ j) =
      ∑ᶠ rho : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
          (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℂ) /
            (s - rho) ^ j := by
  let D := radiusSixZeroFinsupp hq chi hchi t
  rw [Finsupp.sum]
  symm
  calc
    (∑ᶠ rho : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
          (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℂ) /
            (s - rho) ^ j) =
        ∑ rho ∈ D.support,
          ((MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
            (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℂ) /
              (s - rho) ^ j := by
      apply finsum_eq_sum_of_support_subset
      intro rho hrho
      rw [Function.mem_support] at hrho
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro hzero
      apply hrho
      rw [← radiusSixZeroFinsupp_apply_eq_divisor hq chi hchi t rho,
        show radiusSixZeroFinsupp hq chi hchi t rho = D rho by rfl,
        hzero]
      norm_num
    _ = ∑ rho ∈ D.support, (D rho : ℂ) / (s - rho) ^ j := by
      apply Finset.sum_congr rfl
      intro rho hrho
      rw [← radiusSixZeroFinsupp_apply_eq_divisor hq chi hchi t rho]
      norm_cast

/-- The full finite radius-six zero multiset has the standard logarithmic
conductor-height mass bound. -/
theorem exists_radiusSixZeroFinsupp_mass_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ t : ℝ,
            (radiusSixZeroFinsupp hq chi hchi t).sum
                (fun _ m ↦ (m : ℝ)) ≤
              2 * (A : ℝ) * Real.log ((q : ℝ) * (|t| + 2)) := by
  obtain ⟨A, hA, hmass⟩ :=
    exists_nat_finsum_divisor_LFunction_radiusSix_le
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t
  have heq := radiusSixZeroFinsupp_sum_eq_divisor_finsum
    hq chi hchi t
  have hcast :
      (radiusSixZeroFinsupp hq chi hchi t).sum
          (fun _ m ↦ (m : ℝ)) =
        (((∑ᶠ rho : ℂ,
          MeromorphicOn.divisor (DirichletCharacter.LFunction chi)
            (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ)) : ℝ) := by
    rw [← heq]
    push_cast
    rfl
  rw [hcast]
  exact hmass q hq chi hchi t

end

end Erdos48

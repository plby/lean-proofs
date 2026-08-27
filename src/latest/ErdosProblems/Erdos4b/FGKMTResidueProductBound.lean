/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTResidueCollisions
import ErdosProblems.Erdos4b.FGKMTResidueLogBounds
import Mathlib.Analysis.PSeries

/-! # A uniform numerical bound for the residue-correlation product -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem finite_rough_reciprocal_square_sum {S : Finset ℕ} {w : ℕ}
    (hw : 0 < w) (hS : ∀ p ∈ S, w < p) :
    (∑ p ∈ S, 1 / (p : ℝ) ^ 2) ≤ 2 / (w : ℝ) := by
  let Q := max w (S.sup id)
  have hsub : S ⊆ Finset.Ioc w Q := by
    intro p hp
    have hsup : p ≤ S.sup id := Finset.le_sup (f := id) hp
    exact Finset.mem_Ioc.mpr ⟨hS p hp, hsup.trans (le_max_right _ _)⟩
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  calc
    _ ≤ ∑ p ∈ Finset.Ioc w Q, 1 / (p : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _p _hp _hn => by positivity)
    _ ≤ (w : ℝ)⁻¹ - (Q : ℝ)⁻¹ := by
      simpa only [one_div] using sum_Ioc_inv_sq_le_sub (α := ℝ) hw.ne' (le_max_left w (S.sup id))
    _ ≤ 2 / (w : ℝ) := by
      have hQ : 0 ≤ (Q : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg Q)
      rw [div_eq_mul_inv]
      nlinarith [inv_nonneg.mpr hwR.le]

theorem residueSieveDensity_pos {S : Finset ℕ} (hS : ∀ p ∈ S, 1 < p) :
    0 < residueSieveDensity S := by
  apply Finset.prod_pos
  intro p hp
  have hpR : (1 : ℝ) < p := by exact_mod_cast hS p hp
  exact sub_pos.mpr ((div_lt_one (by linarith : (0 : ℝ) < p)).mpr hpR)

theorem residueAvoidanceMass_pos {S : Finset ℕ} {N : Finset ℤ}
    (hS : ∀ p ∈ S, 0 < p) (hsize : ∀ p ∈ S, N.card < p) :
    0 < residueAvoidanceMass S N := by
  rw [residueAvoidanceMass_eq_prod hS]
  apply Finset.prod_pos
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hS p hp
  apply sub_pos.mpr
  apply (div_lt_one hpR).mpr
  exact_mod_cast (occupiedResidues_card_le p N).trans_lt (hsize p hp)

def residueCorrelationError (w t : ℕ) (H : ℝ) : ℝ :=
  (8 * (t : ℝ) ^ 2 + 4 * (t : ℝ) ^ 3 * Real.log (2 * H)) / w

theorem residueAvoidance_log_ratio_bound {S : Finset ℕ} {N : Finset ℤ} {w : ℕ} {H : ℝ}
    (hw : 0 < w) (hS : ∀ p ∈ S, p.Prime) (hrough : ∀ p ∈ S, w < p)
    (ht : 1 ≤ N.card) (hsize : 2 * N.card ≤ w)
    (hH : 1 ≤ H) (hN : ∀ n ∈ N, |(n : ℝ)| ≤ H) :
    |Real.log (residueAvoidanceMass S N / residueSieveDensity S ^ N.card)| ≤
      residueCorrelationError w N.card H := by
  classical
  let t : ℝ := N.card
  have htR : 1 ≤ t := by dsimp only [t]; exact_mod_cast ht
  have ht0 : 0 ≤ t := by linarith
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hprimepos : ∀ p ∈ S, 0 < p := fun p hp => (hS p hp).pos
  have hprimeone : ∀ p ∈ S, 1 < p := fun p hp => (hS p hp).one_lt
  have hsmall (p : ℕ) (hp : p ∈ S) : t / (p : ℝ) ≤ 1 / 2 := by
    have hle : 2 * N.card ≤ p := hsize.trans (hrough p hp).le
    have hleR : 2 * t ≤ (p : ℝ) := by dsimp only [t]; exact_mod_cast hle
    exact (div_le_iff₀ (by exact_mod_cast hprimepos p hp : (0 : ℝ) < p)).mpr (by linarith)
  have hlt (p : ℕ) (hp : p ∈ S) : N.card < p := by have := hrough p hp; omega
  have hApos := residueAvoidanceMass_pos hprimepos hlt
  have hspos := residueSieveDensity_pos hprimeone
  have hlogA : Real.log (residueAvoidanceMass S N) =
      ∑ p ∈ S, Real.log (1 - (occupiedResidues p N).card / (p : ℝ)) := by
    rw [residueAvoidanceMass_eq_prod hprimepos]
    apply Real.log_prod
    intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hprimepos p hp
    exact (sub_pos.mpr ((div_lt_one hpR).mpr
      (by exact_mod_cast (occupiedResidues_card_le p N).trans_lt (hlt p hp)))).ne'
  have hlogs : Real.log (residueSieveDensity S) = ∑ p ∈ S, Real.log (1 - 1 / (p : ℝ)) := by
    apply Real.log_prod
    intro p hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast hprimeone p hp
    exact (sub_pos.mpr ((div_lt_one (by linarith : (0 : ℝ) < p)).mpr hpR)).ne'
  have hlocal (p : ℕ) (hp : p ∈ S) :
      |Real.log (1 - (occupiedResidues p N).card / (p : ℝ)) - t * Real.log (1 - 1 / (p : ℝ))| ≤
        4 * t ^ 2 / (p : ℝ) ^ 2 +
          if (occupiedResidues p N).card = N.card then 0 else 2 * t / p := by
    have hh := residue_local_log_error htR (Nat.cast_nonneg (occupiedResidues p N).card)
      (by dsimp only [t]; exact_mod_cast occupiedResidues_card_le p N)
      (by exact_mod_cast hprimepos p hp) (hsmall p hp)
    simpa only [t, Nat.cast_inj] using hh
  have hbad : (∑ p ∈ S, if (occupiedResidues p N).card = N.card then 0 else 2 * t / (p : ℝ)) ≤
      (2 * t ^ 2 * Real.log (2 * H)) * (2 * t / w) := by
    have hid : (∑ p ∈ S, if (occupiedResidues p N).card = N.card then 0 else 2 * t / (p : ℝ)) =
        ∑ p ∈ residueCollisionPrimes S N, 2 * t / (p : ℝ) := by
      rw [residueCollisionPrimes, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hcard : (occupiedResidues p N).card = N.card <;> simp [hcard]
    rw [hid]
    calc
      _ ≤ ∑ _p ∈ residueCollisionPrimes S N, 2 * t / (w : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        exact div_le_div_of_nonneg_left (by positivity) hwR
          (by exact_mod_cast (hrough p hpS).le)
      _ = ((residueCollisionPrimes S N).card : ℝ) * (2 * t / w) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (residueCollisionPrimes_card_le hS hH hN) (by positivity)
  rw [Real.log_div hApos.ne' (pow_pos hspos _).ne', Real.log_pow, hlogA, hlogs,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ S, |Real.log (1 - (occupiedResidues p N).card / (p : ℝ)) -
        t * Real.log (1 - 1 / (p : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, (4 * t ^ 2 / (p : ℝ) ^ 2 +
        if (occupiedResidues p N).card = N.card then 0 else 2 * t / p) := Finset.sum_le_sum hlocal
    _ = 4 * t ^ 2 * (∑ p ∈ S, 1 / (p : ℝ) ^ 2) +
        (∑ p ∈ S, if (occupiedResidues p N).card = N.card then 0 else 2 * t / p) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ 4 * t ^ 2 * (2 / (w : ℝ)) + (2 * t ^ 2 * Real.log (2 * H)) * (2 * t / w) :=
      add_le_add (mul_le_mul_of_nonneg_left (finite_rough_reciprocal_square_sum hw hrough)
        (by positivity)) hbad
    _ = _ := by unfold residueCorrelationError; dsimp only [t]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.residueAvoidance_log_ratio_bound

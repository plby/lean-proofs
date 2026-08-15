/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.InverseWeylDifferencing
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# A finite positive-shift Weyl inequality

The result is purely algebraic: expand a squared finite sum, separate the
diagonal, and reindex the strict upper triangle by its positive gap.
-/

namespace Erdos387

open scoped BigOperators ComplexConjugate

namespace FiniteWeyl

def strictUpperCorrelation (z : ℕ → ℂ) (P : ℕ) : ℂ :=
  ∑ x ∈ Finset.range P, ∑ y ∈ Finset.range x,
    z x * conj (z y)

theorem sum_mul_conj_sum_eq_diagonal_add_strictUpper
    (z : ℕ → ℂ) (P : ℕ) :
    (∑ x ∈ Finset.range P, z x) *
        conj (∑ x ∈ Finset.range P, z x) =
      (∑ x ∈ Finset.range P, z x * conj (z x)) +
        strictUpperCorrelation z P + conj (strictUpperCorrelation z P) := by
  induction P with
  | zero => simp [strictUpperCorrelation]
  | succ P ih =>
      have hupper : strictUpperCorrelation z (P + 1) =
          strictUpperCorrelation z P +
            ∑ y ∈ Finset.range P, z P * conj (z y) := by
        simp [strictUpperCorrelation, Finset.sum_range_succ]
      rw [Finset.sum_range_succ, map_add, hupper]
      simp only [Finset.sum_range_succ, map_add, starRingEnd_apply]
      simp_rw [← Finset.mul_sum]
      simp only [← star_sum, star_mul, star_star]
      simp only [Complex.star_def] at ih ⊢
      linear_combination ih

theorem norm_sum_range_sq_le_add_two_norm_strictUpper
    (z : ℕ → ℂ) (P : ℕ)
    (hz : ∀ x < P, ‖z x‖ = 1) :
    ‖∑ x ∈ Finset.range P, z x‖ ^ 2 ≤
      P + 2 * ‖strictUpperCorrelation z P‖ := by
  have hdiag :
      (∑ x ∈ Finset.range P, z x * conj (z x)) = (P : ℂ) := by
    calc
      (∑ x ∈ Finset.range P, z x * conj (z x)) =
          ∑ _x ∈ Finset.range P, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Complex.mul_conj']
        rw [hz x (Finset.mem_range.mp hx)]
        norm_num
      _ = (P : ℂ) := by simp
  have hnormExpand :
      ‖∑ x ∈ Finset.range P, z x‖ ^ 2 =
        ‖(P : ℂ) + strictUpperCorrelation z P +
          conj (strictUpperCorrelation z P)‖ := by
    calc
      ‖∑ x ∈ Finset.range P, z x‖ ^ 2 =
          ‖(∑ x ∈ Finset.range P, z x) *
            conj (∑ x ∈ Finset.range P, z x)‖ := by
        rw [norm_mul, Complex.norm_conj, pow_two]
      _ = ‖(∑ x ∈ Finset.range P, z x * conj (z x)) +
            strictUpperCorrelation z P +
              conj (strictUpperCorrelation z P)‖ := by
        rw [sum_mul_conj_sum_eq_diagonal_add_strictUpper]
      _ = _ := by rw [hdiag]
  rw [hnormExpand]
  calc
    ‖(P : ℂ) + strictUpperCorrelation z P +
        conj (strictUpperCorrelation z P)‖ ≤
      ‖(P : ℂ)‖ + ‖strictUpperCorrelation z P‖ +
        ‖conj (strictUpperCorrelation z P)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = P + 2 * ‖strictUpperCorrelation z P‖ := by
      rw [Complex.norm_natCast, Complex.norm_conj]
      ring

theorem strictUpperCorrelation_eq_sum_positiveShift
    (z : ℕ → ℂ) (P : ℕ) :
    strictUpperCorrelation z P =
      ∑ h ∈ Finset.range P, ∑ y ∈ Finset.range (P - h - 1),
        InverseWeyl.positiveShiftCorrelation z h y := by
  rw [strictUpperCorrelation, Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij
      (fun p _ => ⟨p.1 - p.2 - 1, p.2⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    exact ⟨by omega, by omega⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_sigma, Finset.mem_range] at hx hy
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at hxy
    apply Sigma.ext
    · omega
    · exact heq_of_eq hxy.2
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    refine ⟨⟨p.2 + p.1 + 1, p.2⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      exact ⟨by omega, by omega⟩
    · apply Sigma.ext
      · change p.2 + p.1 + 1 - p.2 - 1 = p.1
        omega
      · rfl
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    have hx : p.2 + (p.1 - p.2 - 1) + 1 = p.1 := by omega
    change z p.1 * conj (z p.2) =
      InverseWeyl.positiveShiftCorrelation z (p.1 - p.2 - 1) p.2
    simp only [InverseWeyl.positiveShiftCorrelation, hx]

/-- First finite Weyl-differencing inequality in positive-shift form. -/
theorem norm_sum_range_sq_le_sum_positiveShift
    (z : ℕ → ℂ) (P : ℕ) (hz : ∀ x < P, ‖z x‖ = 1) :
    ‖∑ x ∈ Finset.range P, z x‖ ^ 2 ≤
      P + 2 * ∑ h ∈ Finset.range P,
        ‖∑ y ∈ Finset.range (P - h - 1),
          InverseWeyl.positiveShiftCorrelation z h y‖ := by
  have hbase := norm_sum_range_sq_le_add_two_norm_strictUpper z P hz
  rw [strictUpperCorrelation_eq_sum_positiveShift] at hbase
  calc
    ‖∑ x ∈ Finset.range P, z x‖ ^ 2 ≤
        P + 2 * ‖∑ h ∈ Finset.range P,
          ∑ y ∈ Finset.range (P - h - 1),
            InverseWeyl.positiveShiftCorrelation z h y‖ := hbase
    _ ≤ P + 2 * ∑ h ∈ Finset.range P,
        ‖∑ y ∈ Finset.range (P - h - 1),
          InverseWeyl.positiveShiftCorrelation z h y‖ := by
      gcongr
      exact norm_sum_le _ _

/-- The same inequality at an arbitrary stage of iterated differencing. -/
theorem norm_sum_iteratedCorrelation_sq_le
    (z : ℕ → ℂ) (hz : ∀ x, ‖z x‖ = 1)
    (hs : List ℕ) (P : ℕ) :
    ‖∑ x ∈ Finset.range P,
        InverseWeyl.iteratedPositiveShiftCorrelation z hs x‖ ^ 2 ≤
      P + 2 * ∑ h ∈ Finset.range P,
        ‖∑ y ∈ Finset.range (P - h - 1),
          InverseWeyl.iteratedPositiveShiftCorrelation z (h :: hs) y‖ := by
  have h := norm_sum_range_sq_le_sum_positiveShift
    (InverseWeyl.iteratedPositiveShiftCorrelation z hs) P
      (fun x _hx =>
        InverseWeyl.norm_iteratedPositiveShiftCorrelation_eq_one
          z hz hs x)
  simpa only [InverseWeyl.iteratedPositiveShiftCorrelation,
    InverseWeyl.positiveShiftCorrelation] using h

/-- Iterated finite Weyl differencing for the reciprocal rational phase. -/
theorem norm_sum_iteratedInversePhase_sq_le
    (q : ℕ) [NeZero q] (c a : ZMod q)
    (hs : List ℕ) (P : ℕ) :
    ‖∑ x ∈ Finset.range P,
        ZMod.stdAddChar (InverseWeyl.iteratedInversePhase q c a hs x)‖ ^ 2 ≤
      P + 2 * ∑ h ∈ Finset.range P,
        ‖∑ y ∈ Finset.range (P - h - 1),
          ZMod.stdAddChar
            (InverseWeyl.iteratedInversePhase q c a (h :: hs) y)‖ := by
  have h := norm_sum_iteratedCorrelation_sq_le
    (InverseWeyl.inversePhaseSequence q c a)
    (fun x => InverseWeyl.norm_inversePhaseSequence q c a x) hs P
  simp_rw [
    InverseWeyl.iteratedPositiveShiftCorrelation_inversePhaseSequence]
    at h
  exact h

/-- The same inequality specialized to the reciprocal phase. -/
theorem norm_sum_inversePhaseSequence_sq_le
    (q : ℕ) [NeZero q] (c a : ZMod q) (P : ℕ) :
    ‖∑ x ∈ Finset.range P,
        InverseWeyl.inversePhaseSequence q c a x‖ ^ 2 ≤
      P + 2 * ∑ h ∈ Finset.range P,
        ‖∑ y ∈ Finset.range (P - h - 1),
          ZMod.stdAddChar
            (InverseWeyl.iteratedInversePhase q c a [h] y)‖ := by
  have h := norm_sum_range_sq_le_sum_positiveShift
    (InverseWeyl.inversePhaseSequence q c a) P
      (fun x _hx => InverseWeyl.norm_inversePhaseSequence q c a x)
  have hcorr (shift y : ℕ) :
      InverseWeyl.positiveShiftCorrelation
          (InverseWeyl.inversePhaseSequence q c a) shift y =
        ZMod.stdAddChar
          (InverseWeyl.iteratedInversePhase q c a [shift] y) := by
    change InverseWeyl.iteratedPositiveShiftCorrelation
        (InverseWeyl.inversePhaseSequence q c a) [shift] y = _
    exact InverseWeyl.iteratedPositiveShiftCorrelation_inversePhaseSequence
      q c a [shift] y
  simpa only [hcorr] using h

end FiniteWeyl

end Erdos387

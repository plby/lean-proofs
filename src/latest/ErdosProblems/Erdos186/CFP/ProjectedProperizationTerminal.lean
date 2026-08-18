/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ProjectedProperizationScale
import ErdosProblems.Erdos186.CFP.Bilu.MahlerOuterContainer

/-!
# Terminal outer boxes for projected properization

These are generic-target versions of the Section 9.2 outer-injectivity
bridge.  They turn injectivity on a seminorm ball into properness of the
mapped Mahler box, including rank zero, and record the centered and
nondegenerate presentation data needed by `ProjectedProperization.Data`.
-/

namespace Erdos186.CFP.ProjectedProperization

open scoped BigOperators
open Module
open NoCarryEmbedding
open Bilu.Mahler Bilu.MahlerBox Bilu.MahlerOuterContainer
open Bilu.MinkowskiSecond Bilu.Section92OuterInjectivityBridge

noncomputable section

/-- The centered presentation of the canonical outer Mahler box. -/
theorem centered_centeredBasisGAP_outerRadius {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    (centeredBasisGAP b (outerRadius p)).Centered (outerRadius p) := by
  constructor
  · rfl
  · rfl

/-- Every canonical outer radius is positive. -/
theorem outerRadius_pos {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (i : Fin n) :
    0 < outerRadius p i := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (zero_lt_one.trans_le (one_le_outerConstant n))
    (inv_pos.mpr (successiveMinimum_pos p hp i))

/-- Hence the canonical outer box is nondegenerate. -/
theorem centeredBasisGAP_outerRadius_nondegenerate {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    (centeredBasisGAP b (outerRadius p)).Nondegenerate := by
  exact (centered_centeredBasisGAP_outerRadius p b).nondegenerate_iff.mpr
    (outerRadius_pos p hp)

/-- Unit-ball containment, with the vacuous rank-zero case included. -/
theorem unitBall_integral_subset_outerGAP_all_rank {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (hb : IsMahlerBasis p b) :
    ∀ z : IntegralPoint n, p (integralEmbed z) ≤ 1 →
      z ∈ (centeredBasisGAP b (outerRadius p)).carrier := by
  by_cases hn : n = 0
  · subst n
    intro z _hz
    have hz : z = 0 := by
      funext i
      exact Fin.elim0 i
    subst z
    exact (centered_centeredBasisGAP_outerRadius p b).zero_mem_carrier
  · exact unitBall_integral_subset_outerGAP (Nat.pos_of_ne_zero hn) p hp b hb

/-- Every point of a dilated outer Mahler box lies in the uniform seminorm
ball used by the scale schedule.  Unlike the Section 9 statement, the
target homomorphism is irrelevant and no positivity of the rank is needed. -/
theorem seminorm_le_outerDilationBound_of_mem_outerGAP
    {n k : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
    (hp : IsDefinite p) (hfull : AdmitsIndependent p n 1)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (hb : IsMahlerBasis p b)
    (z : IntegralPoint n)
    (hz : z ∈ (centeredBasisGAP b (outerRadius p) |>.dilate k).carrier) :
    p (integralEmbed z) ≤ outerDilationBound n k := by
  have hmin : ∀ i, successiveMinimum p i ≤ 1 :=
    successiveMinimum_le_one_of_admitsIndependent_full p hfull
  rw [dilate_centeredBasisGAP] at hz
  obtain ⟨c, hc, hcz⟩ :=
    exists_bounded_coefficients_of_mem_centeredBasisGAP hz
  have hembed : integralEmbed z =
      ∑ i, (c i : ℝ) • integralEmbed (b i) := by
    rw [hcz]
    funext j
    simp [integralEmbed]
  rw [hembed]
  refine (seminorm_sum_integralBasis_le p b (fun i ↦ (c i : ℝ))
    ((k : ℝ) * (n : ℝ) * (outerConstant n + 1)) ?_).trans_eq ?_
  · intro i
    let lambda : ℝ := successiveMinimum p i
    let C : ℝ := outerConstant n
    have hlambda : 0 < lambda := successiveMinimum_pos p hp i
    have hlambda_le : lambda ≤ 1 := hmin i
    have hC : 0 ≤ C := outerConstant_nonneg n
    have hceil : ((outerRadius p i : ℕ) : ℝ) ≤ C * lambda⁻¹ + 1 := by
      dsimp only [outerRadius, C, lambda]
      exact (Nat.ceil_lt_add_one
        (mul_nonneg (outerConstant_nonneg n)
          (inv_nonneg.mpr hlambda.le))).le
    have hcReal : |(c i : ℝ)| ≤
        (k : ℝ) * (outerRadius p i : ℝ) := by
      exact_mod_cast hc i
    have hbasis : p (integralEmbed (b i)) ≤
        (n : ℝ) * lambda := hb.le_rank_mul_successiveMinimum i
    have hk : 0 ≤ (k : ℝ) := by positivity
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hradius : (k : ℝ) * (outerRadius p i : ℝ) ≤
        (k : ℝ) * (C * lambda⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left hceil hk
    calc
      |(c i : ℝ)| * p (integralEmbed (b i)) ≤
          ((k : ℝ) * (outerRadius p i : ℝ)) *
            ((n : ℝ) * lambda) :=
        mul_le_mul hcReal hbasis (apply_nonneg p _)
          (mul_nonneg hk (by positivity))
      _ ≤ ((k : ℝ) * (C * lambda⁻¹ + 1)) *
            ((n : ℝ) * lambda) :=
        mul_le_mul_of_nonneg_right hradius (mul_nonneg hn hlambda.le)
      _ = (k : ℝ) * (n : ℝ) * (C + lambda) := by
        field_simp
      _ ≤ (k : ℝ) * (n : ℝ) * (C + 1) := by
        gcongr
  · simp only [outerDilationBound]
    ring

/-- Injectivity on the outer-body seminorm ball makes the mapped outer
dilation proper in an arbitrary lattice target. -/
theorem mapped_outerGAP_dilate_proper_of_injOn_ball
    {n e k : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
    (hp : IsDefinite p) (hfull : AdmitsIndependent p n 1)
    (phi : IntegralPoint n →+ LatticePoint e)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (hb : IsMahlerBasis p b)
    (hinj : Set.InjOn phi
      {z : IntegralPoint n |
        p (integralEmbed z) ≤ outerDilationBound n k}) :
    ((mapGAP phi (centeredBasisGAP b (outerRadius p))).dilate k).Proper := by
  rw [← mapGAP_dilate]
  apply mapGAP_proper_of_injOn_carrier phi _
    (dilate_centeredBasisGAP_proper b (outerRadius p) k)
  intro x hx y hy hxy
  apply hinj
  · exact seminorm_le_outerDilationBound_of_mem_outerGAP
      hp hfull b hb x hx
  · exact seminorm_le_outerDilationBound_of_mem_outerGAP
      hp hfull b hb y hy
  · exact hxy

end

end Erdos186.CFP.ProjectedProperization

#print axioms
  Erdos186.CFP.ProjectedProperization.seminorm_le_outerDilationBound_of_mem_outerGAP
#print axioms
  Erdos186.CFP.ProjectedProperization.mapped_outerGAP_dilate_proper_of_injOn_ball

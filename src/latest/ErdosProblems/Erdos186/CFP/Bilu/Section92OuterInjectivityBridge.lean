/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section91InitialPresentation
import ErdosProblems.Erdos186.CFP.Bilu.Section94SortedContainerAssembly

/-!
# From bounded-body injectivity to outer-GAP injectivity

Section 9.2 produces injectivity on a dimension-only dilation of the convex
body.  The terminal container API asks for injectivity on a dilation of the
selected outer Mahler GAP.  This file proves the required containment with
an explicit uniform seminorm radius.
-/

namespace Erdos186.CFP.Bilu.Section92OuterInjectivityBridge

open scoped BigOperators
open Module
open Mahler MahlerBox MahlerOuterContainer MinkowskiSecond
open Section9ContainerIntegration

noncomputable section

/-- A dimension-only seminorm radius containing the `k`-fold dilation of
the outer Mahler GAP. -/
noncomputable def outerDilationBound (n k : ℕ) : ℝ :=
  (k : ℝ) * (n : ℝ) ^ 2 * (outerConstant n + 1)

theorem outerDilationBound_nonneg (n k : ℕ) :
    0 ≤ outerDilationBound n k := by
  unfold outerDilationBound
  exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (by linarith [outerConstant_nonneg n])

/-- Every displayed point of the dilated outer box lies in a uniform
seminorm ball. -/
theorem seminorm_le_outerDilationBound_of_mem
    {n k : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
    {phi : Mahler.IntegralPoint n →+ ℤ}
    (D : MappedOuterContainer p phi)
    (hp : IsDefinite p)
    (hfull : AdmitsIndependent p n 1)
    (z : Mahler.IntegralPoint n)
    (hz : z ∈ (D.source.dilate k).carrier) :
    p (integralEmbed z) ≤ outerDilationBound n k := by
  have hmin : ∀ i, successiveMinimum p i ≤ 1 :=
    successiveMinimum_le_one_of_admitsIndependent_full p hfull
  rw [MappedOuterContainer.source, dilate_centeredBasisGAP] at hz
  obtain ⟨c, hc, hcz⟩ :=
    exists_bounded_coefficients_of_mem_centeredBasisGAP hz
  have hembed : integralEmbed z =
      ∑ i, (c i : ℝ) • integralEmbed (D.basis i) := by
    rw [hcz]
    funext j
    simp [integralEmbed]
  rw [hembed]
  refine (seminorm_sum_integralBasis_le p D.basis (fun i ↦ (c i : ℝ))
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
        (mul_nonneg (outerConstant_nonneg n) (inv_nonneg.mpr hlambda.le))).le
    have hcReal : |(c i : ℝ)| ≤
        (k : ℝ) * (outerRadius p i : ℝ) := by
      exact_mod_cast hc i
    have hbasis : p (integralEmbed (D.basis i)) ≤
        (n : ℝ) * lambda := by
      exact D.isMahlerBasis.le_rank_mul_successiveMinimum i
    have hk : 0 ≤ (k : ℝ) := by positivity
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hradius : (k : ℝ) * (outerRadius p i : ℝ) ≤
        (k : ℝ) * (C * lambda⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left hceil hk
    calc
      |(c i : ℝ)| * p (integralEmbed (D.basis i)) ≤
          ((k : ℝ) * (outerRadius p i : ℝ)) *
            ((n : ℝ) * lambda) :=
        mul_le_mul hcReal hbasis (apply_nonneg p _) <|
          mul_nonneg hk (by positivity)
      _ ≤ ((k : ℝ) * (C * lambda⁻¹ + 1)) *
            ((n : ℝ) * lambda) :=
        mul_le_mul_of_nonneg_right hradius (mul_nonneg hn hlambda.le)
      _ = (k : ℝ) * (n : ℝ) * (C + lambda) := by
        field_simp
      _ ≤ (k : ℝ) * (n : ℝ) * (C + 1) := by
        gcongr
  · simp only [outerDilationBound]
    ring

/-- Injectivity on the uniform seminorm ball supplied by Section 9.2
implies the exact enlarged-source injectivity required by the terminal
Mahler container. -/
theorem enlarged_injective_of_injectiveOn_seminormBall
    {n k : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
    {phi : Mahler.IntegralPoint n →+ ℤ}
    (D : MappedOuterContainer p phi)
    (hp : IsDefinite p)
    (hfull : AdmitsIndependent p n 1)
    (hinj : Set.InjOn phi
      {z : Mahler.IntegralPoint n |
        p (integralEmbed z) ≤ outerDilationBound n k}) :
    Set.InjOn (integerPointHom phi) (D.source.dilate k).carrier := by
  intro x hx y hy hxy
  apply hinj
  · exact seminorm_le_outerDilationBound_of_mem D hp hfull x hx
  · exact seminorm_le_outerDilationBound_of_mem D hp hfull y hy
  · have h0 := congrFun hxy (0 : Fin 1)
    simpa [integerPointHom, CFP.BiluFreiman.integerPoint] using h0

end

end Erdos186.CFP.Bilu.Section92OuterInjectivityBridge

#print axioms Erdos186.CFP.Bilu.Section92OuterInjectivityBridge.seminorm_le_outerDilationBound_of_mem
#print axioms Erdos186.CFP.Bilu.Section92OuterInjectivityBridge.enlarged_injective_of_injectiveOn_seminormBall

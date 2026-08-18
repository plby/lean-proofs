/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ProjectedProperization
import ErdosProblems.Erdos186.CFP.Bilu.MahlerBasis
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecond

/-!
# The coefficient body of a symmetric GAP

A nondegenerate symmetric GAP has positive integral radii.  Dividing each
real coefficient by its radius identifies its coefficient boxes with the
sublevel sets of a definite weighted sup seminorm.  This is the initial
body used in projected properization: its integral points at natural scale
`k` are exactly the centered coefficients of the displayed GAP dilation.
-/

namespace Erdos186.CFP.ProjectedProperization

open scoped BigOperators
open Bilu.Mahler
open NoCarryEmbedding

noncomputable section

/-- Divide every real coefficient by its positive integral radius. -/
def centeredBoxScaleMap {r : ℕ} (radii : Fin r → ℕ) :
    (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun := fun x i ↦ x i / (radii i : ℝ)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' a x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem centeredBoxScaleMap_apply {r : ℕ} (radii : Fin r → ℕ)
    (x : Fin r → ℝ) (i : Fin r) :
    centeredBoxScaleMap radii x i = x i / (radii i : ℝ) :=
  rfl

/-- The weighted sup seminorm whose unit ball is the real centered
coefficient box with half-widths `radii`. -/
def centeredBoxSeminorm {r : ℕ} (radii : Fin r → ℕ) :
    Seminorm ℝ (Fin r → ℝ) :=
  (normSeminorm ℝ (Fin r → ℝ)).comp (centeredBoxScaleMap radii)

@[simp]
theorem centeredBoxSeminorm_apply {r : ℕ} (radii : Fin r → ℕ)
    (x : Fin r → ℝ) :
    centeredBoxSeminorm radii x =
      ‖fun i ↦ x i / (radii i : ℝ)‖ :=
  rfl

/-- Positive radii make the weighted coefficient seminorm definite. -/
theorem centeredBoxSeminorm_definite {r : ℕ} (radii : Fin r → ℕ)
    (hradii : ∀ i, 0 < radii i) :
    IsDefinite (centeredBoxSeminorm radii) := by
  intro x hx
  have hscaled : (fun i ↦ x i / (radii i : ℝ)) = 0 := by
    exact norm_eq_zero.mp hx
  funext i
  have hi := congrFun hscaled i
  simp only [Pi.zero_apply, div_eq_zero_iff] at hi
  exact hi.resolve_right (by exact_mod_cast (Nat.ne_of_gt (hradii i)))

/-- The standard integral coordinate vectors lie in the unit ball and
give a full independent family. -/
theorem centeredBoxSeminorm_admitsIndependent
    {r : ℕ} (radii : Fin r → ℕ) (hradii : ∀ i, 0 < radii i) :
    AdmitsIndependent (centeredBoxSeminorm radii) r 1 := by
  refine ⟨Bilu.MinkowskiSecond.standardIntegralPoint,
    Bilu.MinkowskiSecond.linearIndependent_integralEmbed_standard, ?_⟩
  intro i
  rw [centeredBoxSeminorm_apply,
    Bilu.MinkowskiSecond.integralEmbed_standardIntegralPoint]
  have hscaled :
      (fun j ↦ (Pi.basisFun ℝ (Fin r) i j) /
        (radii j : ℝ)) =
        (Pi.single i ((radii i : ℝ)⁻¹) : Fin r → ℝ) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Pi.basisFun_apply, Pi.single, div_eq_mul_inv]
    · simp [Pi.basisFun_apply, Pi.single, hji, Ne.symm hji]
  rw [hscaled, Pi.norm_single, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Nat.cast_nonneg (radii i))]
  exact (inv_le_one₀ (by exact_mod_cast hradii i)).2
    (by exact_mod_cast hradii i)

/-- Exact coordinate form of a natural sublevel set on integral points. -/
theorem centeredBoxSeminorm_integral_le_iff
    {r : ℕ} (hr : 0 < r) (radii : Fin r → ℕ)
    (hradii : ∀ i, 0 < radii i) (z : IntegralPoint r) (k : ℕ) :
    centeredBoxSeminorm radii (integralEmbed z) ≤ (k : ℝ) ↔
      ∀ i, |z i| ≤ (k : ℤ) * (radii i : ℤ) := by
  letI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [centeredBoxSeminorm_apply, pi_norm_le_iff_of_nonempty]
  constructor
  · intro h i
    have hi := h i
    simp only [integralEmbed, Real.norm_eq_abs, abs_div] at hi
    have hri : (0 : ℝ) < (radii i : ℝ) := by exact_mod_cast hradii i
    rw [abs_of_pos hri] at hi
    have hmul : |(z i : ℝ)| ≤ (k : ℝ) * (radii i : ℝ) :=
      (div_le_iff₀ hri).mp hi
    exact_mod_cast hmul
  · intro h i
    have hi : |(z i : ℝ)| ≤ (k : ℝ) * (radii i : ℝ) := by
      exact_mod_cast h i
    have hri : (0 : ℝ) < (radii i : ℝ) := by exact_mod_cast hradii i
    simp only [integralEmbed, Real.norm_eq_abs, abs_div, abs_of_pos hri]
    exact (div_le_iff₀ hri).mpr hi

/-- The integer-linear evaluation map of a tuple of displayed steps. -/
def centeredStepHom {d r : ℕ} (steps : Fin r → LatticePoint d) :
    IntegralPoint r →+ LatticePoint d where
  toFun := fun z j ↦ ∑ i, z i * steps i j
  map_zero' := by
    funext j
    simp
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp]
theorem centeredStepHom_apply {d r : ℕ}
    (steps : Fin r → LatticePoint d) (z : IntegralPoint r) :
    centeredStepHom steps z = fun j ↦ ∑ i, z i * steps i j :=
  rfl

/-- Step evaluation followed by an ambient additive projection. -/
def mappedCenteredStepHom {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (steps : Fin r → LatticePoint d) :
    IntegralPoint r →+ LatticePoint e :=
  f.comp (centeredStepHom steps)

@[simp]
theorem mappedCenteredStepHom_apply {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (steps : Fin r → LatticePoint d) (z : IntegralPoint r) :
    mappedCenteredStepHom f steps z =
      f (fun j ↦ ∑ i, z i * steps i j) :=
  rfl

/-- An additive map may be pushed through the finite integral step
combination defining centered evaluation. -/
theorem mappedCenteredStepHom_eq_sum {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (steps : Fin r → LatticePoint d) (z : IntegralPoint r) :
    mappedCenteredStepHom f steps z =
      fun j ↦ ∑ i, z i * f (steps i) j := by
  change f (fun j ↦ ∑ i, z i * steps i j) = _
  have hsource :
      (fun j ↦ ∑ i, z i * steps i j) = ∑ i, z i • steps i := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsource, map_sum]
  simp only [map_zsmul]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Mapping the ambient lattice preserves a centered GAP presentation. -/
theorem mapGAP_centered_of_centered {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    {radii : Fin r → ℕ} (hP : P.Centered radii) :
    (mapGAP f P).Centered radii := by
  constructor
  · exact hP.widths_eq
  · change f P.offset =
      fun j ↦ -∑ i, (radii i : ℤ) * f (P.steps i) j
    rw [hP.offset_eq]
    have hmapped :
        f (fun j ↦ ∑ i, (-(radii i : ℤ)) * P.steps i j) =
          fun j ↦ ∑ i, (-(radii i : ℤ)) * f (P.steps i) j := by
      exact mappedCenteredStepHom_eq_sum f P.steps
        (fun i ↦ -(radii i : ℤ))
    calc
      f (fun j ↦ -∑ i, (radii i : ℤ) * P.steps i j) =
          f (fun j ↦ ∑ i, (-(radii i : ℤ)) * P.steps i j) := by
            congr 1
            funext j
            simp only [neg_mul, Finset.sum_neg_distrib]
      _ = fun j ↦ ∑ i, (-(radii i : ℤ)) * f (P.steps i) j := hmapped
      _ = fun j ↦ -∑ i, (radii i : ℤ) * f (P.steps i) j := by
        funext j
        simp only [neg_mul, Finset.sum_neg_distrib]

/-- A centered symmetric dilation is exactly the image of the corresponding
integral weighted-seminorm sublevel set under step evaluation. -/
theorem mem_dilate_carrier_iff_exists_centeredBoxSeminorm
    {d r : ℕ} (hr : 0 < r) (P : GAP d r) (radii : Fin r → ℕ)
    (hP : P.Centered radii) (hradii : ∀ i, 0 < radii i)
    (k : ℕ) (x : LatticePoint d) :
    x ∈ (P.dilate k).carrier ↔
      ∃ z : IntegralPoint r,
        centeredBoxSeminorm radii (integralEmbed z) ≤ (k : ℝ) ∧
        centeredStepHom P.steps z = x := by
  rw [GAP.mem_carrier_iff]
  constructor
  · rintro ⟨n, rfl⟩
    let z : IntegralPoint r :=
      fun i ↦ (n i : ℤ) - ((k * radii i : ℕ) : ℤ)
    refine ⟨z, ?_, ?_⟩
    · rw [centeredBoxSeminorm_integral_le_iff hr radii hradii]
      intro i
      have hn : (n i : ℕ) < 2 * (k * radii i) + 1 := by
        simpa only [(hP.dilate k).width_eq] using (n i).isLt
      simp only [z]
      rw [abs_le]
      push_cast at hn ⊢
      constructor <;> omega
    · rw [(hP.dilate k).coordPoint_eq]
      rfl
  · rintro ⟨z, hz, rfl⟩
    rw [centeredBoxSeminorm_integral_le_iff hr radii hradii] at hz
    let n : (P.dilate k).Coord := fun i ↦
      ⟨(z i + ((k * radii i : ℕ) : ℤ)).toNat, by
        have hi := hz i
        have hnonneg : 0 ≤ z i + ((k * radii i : ℕ) : ℤ) := by
          rw [abs_le] at hi
          push_cast at hi ⊢
          omega
        have hupper : z i + ((k * radii i : ℕ) : ℤ) ≤
            (2 * (k * radii i) : ℕ) := by
          rw [abs_le] at hi
          push_cast at hi ⊢
          omega
        rw [(hP.dilate k).width_eq]
        omega
      ⟩
    refine ⟨n, ?_⟩
    rw [(hP.dilate k).coordPoint_eq]
    change (fun j ↦ ∑ i,
      (((n i : ℕ) : ℤ) - ((k * radii i : ℕ) : ℤ)) * P.steps i j) =
        fun j ↦ ∑ i, z i * P.steps i j
    funext j
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    have hi := hz i
    have hnonneg : 0 ≤ z i + ((k * radii i : ℕ) : ℤ) := by
      rw [abs_le] at hi
      push_cast at hi ⊢
      omega
    simp only [n]
    rw [Int.toNat_of_nonneg hnonneg]
    ring

/-- Projected membership has the same exact integral coefficient-body
description, with step evaluation followed by the projection. -/
theorem mem_mapped_dilate_carrier_iff_exists_centeredBoxSeminorm
    {d e r : ℕ} (hr : 0 < r) (P : GAP d r)
    (radii : Fin r → ℕ) (hP : P.Centered radii)
    (hradii : ∀ i, 0 < radii i)
    (f : LatticePoint d →+ LatticePoint e)
    (k : ℕ) (x : LatticePoint e) :
    x ∈ ((mapGAP f P).dilate k).carrier ↔
      ∃ z : IntegralPoint r,
        centeredBoxSeminorm radii (integralEmbed z) ≤ (k : ℝ) ∧
        mappedCenteredStepHom f P.steps z = x := by
  rw [← mapGAP_dilate, mapGAP_carrier]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, hzy⟩ :=
      (mem_dilate_carrier_iff_exists_centeredBoxSeminorm
        hr P radii hP hradii k y).mp hy
    refine ⟨z, hz, ?_⟩
    exact congrArg f hzy
  · rintro ⟨z, hz, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨centeredStepHom P.steps z, ?_, rfl⟩
    exact (mem_dilate_carrier_iff_exists_centeredBoxSeminorm
      hr P radii hP hradii k _).mpr ⟨z, hz, rfl⟩

/-- Injectivity of projected step evaluation on the weighted integral
sublevel set is precisely enough to make the corresponding mapped GAP
dilation proper. -/
theorem mapped_dilate_proper_of_injOn_centeredBoxSeminorm
    {d e r k : ℕ} (hr : 0 < r) (P : GAP d r)
    (radii : Fin r → ℕ) (hP : P.Centered radii)
    (hradii : ∀ i, 0 < radii i)
    (f : LatticePoint d →+ LatticePoint e)
    (hinjective : Set.InjOn (mappedCenteredStepHom f P.steps)
      {z : IntegralPoint r |
        centeredBoxSeminorm radii (integralEmbed z) ≤ (k : ℝ)}) :
    ((mapGAP f P).dilate k).Proper := by
  intro n m hnm
  let z : IntegralPoint r :=
    fun i ↦ (n i : ℤ) - ((k * radii i : ℕ) : ℤ)
  let w : IntegralPoint r :=
    fun i ↦ (m i : ℤ) - ((k * radii i : ℕ) : ℤ)
  have hz : centeredBoxSeminorm radii (integralEmbed z) ≤ (k : ℝ) := by
    rw [centeredBoxSeminorm_integral_le_iff hr radii hradii]
    intro i
    have hn : (n i : ℕ) < 2 * (k * radii i) + 1 := by
      simpa only [(mapGAP_centered_of_centered f P hP).dilate k |>.width_eq]
        using (n i).isLt
    simp only [z]
    rw [abs_le]
    push_cast at hn ⊢
    constructor <;> omega
  have hw : centeredBoxSeminorm radii (integralEmbed w) ≤ (k : ℝ) := by
    rw [centeredBoxSeminorm_integral_le_iff hr radii hradii]
    intro i
    have hm : (m i : ℕ) < 2 * (k * radii i) + 1 := by
      simpa only [(mapGAP_centered_of_centered f P hP).dilate k |>.width_eq]
        using (m i).isLt
    simp only [w]
    rw [abs_le]
    push_cast at hm ⊢
    constructor <;> omega
  have hzw : z = w := by
    apply hinjective hz hw
    have hcenter := mapGAP_centered_of_centered f P hP
    have hcoordn :
        ((mapGAP f P).dilate k).coordPoint n =
          mappedCenteredStepHom f P.steps z := by
      rw [(hcenter.dilate k).coordPoint_eq,
        mappedCenteredStepHom_eq_sum]
      rfl
    have hcoordm :
        ((mapGAP f P).dilate k).coordPoint m =
          mappedCenteredStepHom f P.steps w := by
      rw [(hcenter.dilate k).coordPoint_eq,
        mappedCenteredStepHom_eq_sum]
      rfl
    exact hcoordn.symm.trans (hnm.trans hcoordm)
  funext i
  apply Fin.ext
  have hi := congrFun hzw i
  simp only [z, w] at hi
  omega

/-- The homogeneous covered translate of an enhanced witness lies in the
integral span of the centered displayed steps.  The dilation offset is
itself such a combination, so it can be moved to the other side. -/
theorem exists_centeredStepHom_eq_translatePoint
    {d s D k loss : ℕ} {H : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness H s D k loss) :
    ∃ z : IntegralPoint W.rank,
      centeredStepHom W.progression.steps z = W.translatePoint := by
  obtain ⟨a, ha⟩ := W.covered_translate_homogeneous
  let z : IntegralPoint W.rank := fun i ↦
    a i + ((k * W.symmetryRadii i : ℕ) : ℤ)
  refine ⟨z, ?_⟩
  rw [centeredStepHom_apply]
  funext j
  have haj := congrFun ha j
  rw [(W.symmetryCentered.dilate k).offset_eq] at haj
  simp only [Pi.add_apply, GAP.dilate_steps] at haj
  simp only [z, add_mul, Finset.sum_add_distrib]
  push_cast at haj ⊢
  linear_combination -haj

end

end Erdos186.CFP.ProjectedProperization

#print axioms
  Erdos186.CFP.ProjectedProperization.centeredBoxSeminorm_integral_le_iff
#print axioms
  Erdos186.CFP.ProjectedProperization.mem_dilate_carrier_iff_exists_centeredBoxSeminorm
#print axioms
  Erdos186.CFP.ProjectedProperization.exists_centeredStepHom_eq_translatePoint

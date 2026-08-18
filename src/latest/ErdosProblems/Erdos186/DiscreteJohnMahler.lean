/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.DiscreteJohnSection
import ErdosProblems.Erdos186.CFP.Bilu.MahlerTheorem
import ErdosProblems.Erdos186.CFP.Bilu.MahlerBox
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecondUpperDirect
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Extracting discrete-John boxes from Mahler bases

This file records the determinant calculation behind the outer coordinate
bound.  Replacing one column of a unimodular integral basis by a lattice
point has determinant equal, in absolute value, to the corresponding basis
coordinate.  It is the bridge from crosspolytope volume estimates to a
rectangular progression.
-/

namespace Erdos186
namespace DiscreteJohn
namespace MahlerExtraction

open scoped BigOperators
open Module CFP.Bilu.Mahler CFP.Bilu.MinkowskiSecond
open CFP.Bilu.MahlerBox

variable {d : ℕ}

/-- Replace one vector in an integral basis by a specified lattice point. -/
noncomputable def replaceBasisVector
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (z : LatticePoint d) (i : Fin d) : Fin d → LatticePoint d :=
  fun j ↦ if j = i then z else b j

theorem realColumns_replaceBasisVector
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (z : LatticePoint d) (i : Fin d) :
    (integralColumns (replaceBasisVector b z i)).map (Int.castRingHom ℝ) =
      (integralBasisMatrix b).updateCol i (integralEmbed z) := by
  classical
  ext row col
  by_cases h : col = i
  · subst col
    simp only [Matrix.map_apply, integralColumns_apply,
      Matrix.updateCol_self, replaceBasisVector, if_pos]
    rfl
  · simp [replaceBasisVector, h, integralBasisMatrix]

/-- Cramer's rule in a unimodular integral basis: a replacement-column
determinant is the corresponding integral basis coordinate. -/
theorem abs_det_replaceBasisVector
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (z : LatticePoint d) (i : Fin d) :
    |(((integralColumns (replaceBasisVector b z i)).det : ℤ) : ℝ)| =
      |(b.repr z i : ℝ)| := by
  classical
  let A := integralBasisMatrix b
  let c : Fin d → ℝ := fun j ↦ (b.repr z j : ℝ)
  have hdet : A.det ≠ 0 := by
    intro h
    have := abs_det_integralBasisMatrix b
    rw [h, abs_zero] at this
    norm_num at this
  have hc : A.mulVec c = integralEmbed z :=
    mulVec_integralBasisMatrix_repr b z
  have hcramer : A.cramer (integralEmbed z) = A.det • c := by
    apply A.mulVec_injective_of_det_ne_zero hdet
    rw [Matrix.mulVec_cramer, Matrix.mulVec_smul, hc]
  have hcol :
      (((integralColumns (replaceBasisVector b z i)).det : ℤ) : ℝ) =
        (A.updateCol i (integralEmbed z)).det := by
    calc
      (((integralColumns (replaceBasisVector b z i)).det : ℤ) : ℝ) =
          ((integralColumns (replaceBasisVector b z i)).map
            (Int.castRingHom ℝ)).det := by
        simpa using (Int.cast_det (R := ℝ)
          (integralColumns (replaceBasisVector b z i)))
      _ = (A.updateCol i (integralEmbed z)).det := by
        exact congrArg Matrix.det (realColumns_replaceBasisVector b z i)
  rw [hcol, ← Matrix.cramer_apply, hcramer]
  change |A.det * c i| = |c i|
  rw [abs_mul, abs_det_integralBasisMatrix b, one_mul]

/-- A nonzero coordinate makes the family obtained by replacing that basis
vector real-linearly independent. -/
theorem linearIndependent_replaceBasisVector
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (z : LatticePoint d) (i : Fin d) (hi : b.repr z i ≠ 0) :
    LinearIndependent ℝ
      (fun j ↦ integralEmbed (replaceBasisVector b z i j)) := by
  classical
  let A : Matrix (Fin d) (Fin d) ℝ :=
    (integralColumns (replaceBasisVector b z i)).map (Int.castRingHom ℝ)
  have hdet : A.det ≠ 0 := by
    intro hzero
    have habs := abs_det_replaceBasisVector b z i
    have hcast :
        (((integralColumns (replaceBasisVector b z i)).det : ℤ) : ℝ) =
          A.det := by
      simpa [A] using
        (Int.cast_det (R := ℝ)
          (integralColumns (replaceBasisVector b z i)))
    rw [hcast, hzero, abs_zero] at habs
    have : (b.repr z i : ℝ) ≠ 0 := by exact_mod_cast hi
    exact this (abs_eq_zero.mp habs.symm)
  have hcols : LinearIndependent ℝ A.col :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hfun : A.col =
      (fun j ↦ integralEmbed (replaceBasisVector b z i j)) := by
    funext j
    ext row
    rfl
  rwa [hfun] at hcols

/-- Exact replacement-column crosspolytope lower bound.  Unlike the usual
integral-determinant estimate, this retains the size of the selected basis
coordinate. -/
theorem replacement_coordinate_crosspolytope_le_volume
    [Nonempty (Fin d)]
    (p : Seminorm ℝ (Fin d → ℝ))
    (b : Basis (Fin d) ℤ (LatticePoint d))
    (z : LatticePoint d) (i : Fin d) (a : Fin d → ℝ)
    (ha : ∀ j,
      |a j| * p (integralEmbed (replaceBasisVector b z i j)) ≤ 1) :
    ENNReal.ofReal
        ((∏ j, |a j|) * |(b.repr z i : ℝ)|) *
        ENNReal.ofReal ((2 : ℝ) ^ d / (d.factorial : ℝ)) ≤
      MeasureTheory.volume {y | p y ≤ 1} := by
  let v := replaceBasisVector b z i
  have hsubset := image_l1UnitBall_subset_seminorm_unitBall p a v ha
  have hmeasure :
      MeasureTheory.volume
          ((Matrix.toLin' (scaledRealColumns a v)) '' l1UnitBall d) ≤
        MeasureTheory.volume {y | p y ≤ 1} :=
    MeasureTheory.measure_mono hsubset
  rw [volume_image_l1UnitBall_scaledRealColumns] at hmeasure
  have hdet :
      |(scaledRealColumns a v).det| =
        (∏ j, |a j|) * |(b.repr z i : ℝ)| := by
    rw [det_scaledRealColumns, abs_mul, Finset.abs_prod]
    exact congrArg ((∏ j, |a j|) * ·)
      (abs_det_replaceBasisVector b z i)
  rwa [hdet] at hmeasure

/-- The coarse upper half of Minkowski II and the replacement-column
crosspolytope bound give a dimension-only weighted coordinate estimate for
every lattice point of the unit ball. -/
theorem mahlerBasis_coordinate_mul_successiveMinimum_le
    (hd : 0 < d) (p : Seminorm ℝ (Fin d → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin d) ℤ (LatticePoint d)) (hb : IsMahlerBasis p b)
    (z : LatticePoint d) (hz : p (integralEmbed z) ≤ 1) (i : Fin d) :
    |(b.repr z i : ℝ)| * successiveMinimum p i ≤
      (d.factorial : ℝ) * (d : ℝ) ^ d * (8 : ℝ) ^ d := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let lambda : Fin d → ℝ := fun j ↦ successiveMinimum p j
  let R : Fin d → ℝ := fun j ↦ (d : ℝ) * lambda j
  let a : Fin d → ℝ := fun j ↦ if j = i then 1 else (R j)⁻¹
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hlambda (j : Fin d) : 0 < lambda j :=
    successiveMinimum_pos p hp j
  have hR (j : Fin d) : 0 < R j := mul_pos hdreal (hlambda j)
  have ha : ∀ j,
      |a j| * p (integralEmbed (replaceBasisVector b z i j)) ≤ 1 := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [a, replaceBasisVector] using hz
    · have hbj := hb.le_rank_mul_successiveMinimum j
      have hRinv : 0 ≤ (R j)⁻¹ := (inv_pos.mpr (hR j)).le
      have hscaled : (R j)⁻¹ * p (integralEmbed (b j)) ≤ 1 := by
        calc
          (R j)⁻¹ * p (integralEmbed (b j)) ≤ (R j)⁻¹ * R j := by
            exact mul_le_mul_of_nonneg_left (by simpa [R, lambda] using hbj) hRinv
          _ = 1 := inv_mul_cancel₀ (hR j).ne'
      simpa [a, replaceBasisVector, hji, abs_of_pos (inv_pos.mpr (hR j))]
        using hscaled
  have hcross := replacement_coordinate_crosspolytope_le_volume
    p b z i a ha
  have hball_ne_top :
      MeasureTheory.volume {y : Fin d → ℝ | p y ≤ 1} ≠ ⊤ :=
    (CFP.Bilu.MinkowskiUpper.isBounded_unitBall p hp).measure_lt_top.ne
  have hcrossReal := ENNReal.toReal_mono hball_ne_top hcross
  have hleft_nonneg :
      0 ≤ (∏ j, |a j|) * |(b.repr z i : ℝ)| :=
    mul_nonneg (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _) (abs_nonneg _)
  have hcrossReal' :
      ((∏ j, |a j|) * |(b.repr z i : ℝ)|) *
          ((2 : ℝ) ^ d / (d.factorial : ℝ)) ≤
        MeasureTheory.volume.real {y : Fin d → ℝ | p y ≤ 1} := by
    simpa [MeasureTheory.measureReal_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hleft_nonneg,
      ENNReal.toReal_ofReal (by positivity :
        (0 : ℝ) ≤ (2 : ℝ) ^ d / (d.factorial : ℝ))] using hcrossReal
  have hproda :
      (∏ j, |a j|) * (R i)⁻¹ = (∏ j, R j)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    rw [show (R i)⁻¹ =
        ∏ j : Fin d, if j = i then (R i)⁻¹ else 1 by simp]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [a]
    · simp [a, hji, abs_of_pos (inv_pos.mpr (hR j))]
  have hprodR : (∏ j, R j) = (d : ℝ) ^ d * ∏ j, lambda j := by
    simp only [R, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hupper :=
    CFP.Bilu.MinkowskiSecond.minkowskiSecond_upper_eight_pow_real p hp
  have hfactorial_pos : (0 : ℝ) < d.factorial := by positivity
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hP : 0 < ∏ j, lambda j :=
    Finset.prod_pos fun j _ ↦ hlambda j
  have hRi : 0 < R i := hR i
  have hA : 0 ≤ |(b.repr z i : ℝ)| := abs_nonneg _
  rw [hprodR] at hproda
  change (∏ j, successiveMinimum p j) *
      MeasureTheory.volume.real (CFP.Bilu.MinkowskiUpper.unitBall p) ≤
        (8 : ℝ) ^ d at hupper
  change MeasureTheory.volume.real (CFP.Bilu.MinkowskiUpper.unitBall p) ≥ _ at hcrossReal'
  dsimp only [CFP.Bilu.MinkowskiUpper.unitBall] at hcrossReal'
  have hprod_pos : 0 < (d : ℝ) ^ d * ∏ j, lambda j :=
    mul_pos (pow_pos hdreal _) hP
  have hQ : (∏ j, |a j|) =
      R i * ((d : ℝ) ^ d * ∏ j, lambda j)⁻¹ := by
    apply mul_left_cancel₀ (inv_ne_zero hRi.ne')
    calc
      (R i)⁻¹ * ∏ j, |a j| =
          (∏ j, |a j|) * (R i)⁻¹ := mul_comm _ _
      _ = ((d : ℝ) ^ d * ∏ j, lambda j)⁻¹ := hproda
      _ = (R i)⁻¹ *
          (R i * ((d : ℝ) ^ d * ∏ j, lambda j)⁻¹) := by
        rw [← mul_assoc, inv_mul_cancel₀ hRi.ne', one_mul]
  rw [hQ] at hcrossReal'
  dsimp only [R, lambda] at hcrossReal' hupper ⊢
  have hPne : (∏ j, successiveMinimum p j) ≠ 0 := by
    simpa [lambda] using hP.ne'
  field_simp [hPne, hfactorial_pos.ne'] at hcrossReal'
  have hPpos : 0 < ∏ j, successiveMinimum p j :=
    Finset.prod_pos fun j _ ↦ successiveMinimum_pos p hp j
  have hcrossMul :
      (d : ℝ) * successiveMinimum p i * |(b.repr z i : ℝ)| * (2 : ℝ) ^ d ≤
        ((d : ℝ) ^ d * (d.factorial : ℝ) *
          MeasureTheory.volume.real {x : Fin d → ℝ | p x ≤ 1}) *
            ∏ j, successiveMinimum p j :=
    (div_le_iff₀ hPpos).mp hcrossReal'
  have hconst_nonneg :
      0 ≤ (d : ℝ) ^ d * (d.factorial : ℝ) := by positivity
  have hmid :
      (d : ℝ) * successiveMinimum p i * |(b.repr z i : ℝ)| * (2 : ℝ) ^ d ≤
        (d : ℝ) ^ d * (d.factorial : ℝ) * (8 : ℝ) ^ d := by
    calc
      (d : ℝ) * successiveMinimum p i * |(b.repr z i : ℝ)| * (2 : ℝ) ^ d ≤
          ((d : ℝ) ^ d * (d.factorial : ℝ) *
            MeasureTheory.volume.real {x : Fin d → ℝ | p x ≤ 1}) *
              ∏ j, successiveMinimum p j := hcrossMul
      _ = ((d : ℝ) ^ d * (d.factorial : ℝ)) *
          ((∏ j, successiveMinimum p j) *
            MeasureTheory.volume.real
              (CFP.Bilu.MinkowskiUpper.unitBall p)) := by
        simp only [CFP.Bilu.MinkowskiUpper.unitBall]
        ring
      _ ≤ ((d : ℝ) ^ d * (d.factorial : ℝ)) * (8 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left hupper hconst_nonneg
  have hscale : (1 : ℝ) ≤ (d : ℝ) * (2 : ℝ) ^ d := by
    have hdone : (1 : ℝ) ≤ d := by exact_mod_cast hd
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (d : ℝ) * (2 : ℝ) ^ d :=
        mul_le_mul hdone htwo (by norm_num) hdreal.le
  have hcoord_nonneg :
      0 ≤ |(b.repr z i : ℝ)| * successiveMinimum p i :=
    mul_nonneg (abs_nonneg _) (successiveMinimum_nonneg p i)
  calc
    |(b.repr z i : ℝ)| * successiveMinimum p i ≤
        ((d : ℝ) * (2 : ℝ) ^ d) *
          (|(b.repr z i : ℝ)| * successiveMinimum p i) := by
      nlinarith
    _ = (d : ℝ) * successiveMinimum p i *
        |(b.repr z i : ℝ)| * (2 : ℝ) ^ d := by ring
    _ ≤ (d : ℝ) ^ d * (d.factorial : ℝ) * (8 : ℝ) ^ d := hmid
    _ = (d.factorial : ℝ) * (d : ℝ) ^ d * (8 : ℝ) ^ d := by ring

/-- The integral version of the coarse replacement-column constant. -/
def coordinateConstant (d : ℕ) : ℕ := d.factorial * d ^ d * 8 ^ d

/-- A uniform shrink factor large enough for both the outer coordinate
bound and the inner Mahler box. -/
def johnFactor (d : ℕ) : ℕ := coordinateConstant d * d * d

theorem coordinateConstant_pos (hd : 0 < d) : 0 < coordinateConstant d := by
  simp only [coordinateConstant]
  positivity

theorem johnFactor_pos (hd : 0 < d) : 0 < johnFactor d := by
  simp only [johnFactor]
  exact Nat.mul_pos (Nat.mul_pos (coordinateConstant_pos hd) hd) hd

/-- Radius whose quotient by `johnFactor` is exactly Bilu's canonical
inner radius.  The extra `factor - 1` is the rounding room used for the
outer coordinate cover. -/
noncomputable def johnRadius (p : Seminorm ℝ (Fin d → ℝ)) (i : Fin d) : ℕ :=
  johnFactor d * innerRadius p i + (johnFactor d - 1)

theorem johnRadius_div (hd : 0 < d)
    (p : Seminorm ℝ (Fin d → ℝ)) (i : Fin d) :
    johnRadius p i / johnFactor d = innerRadius p i := by
  have hfactor : 0 < johnFactor d := johnFactor_pos hd
  rw [johnRadius, Nat.add_comm,
    Nat.add_mul_div_left (johnFactor d - 1) (innerRadius p i) hfactor]
  have hlt : johnFactor d - 1 < johnFactor d := by
    omega
  rw [Nat.div_eq_of_lt hlt]
  omega

/-- The actual uniformly bounded minima data used by the finite
discrete-John certificate in positive dimension. -/
noncomputable def fullRankMinimaData
    (hd : 0 < d) (p : Seminorm ℝ (Fin d → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin d) ℤ (LatticePoint d)) (hb : IsMahlerBasis p b) :
    FullRankMinimaData p b where
  factor := johnFactor d
  radii := johnRadius p
  factor_pos := johnFactor_pos hd
  mahler := hb
  outer_coordinate_bound := by
    intro z hz i
    let lambda := successiveMinimum p i
    let weight := mahlerFactor i * lambda
    let q := innerRadius p i
    let C := coordinateConstant d
    let F := johnFactor d
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
    have hlambda : 0 < lambda := successiveMinimum_pos p hp i
    have hweight : 0 < weight := by
      exact mul_pos (zero_lt_one.trans_le (one_le_mahlerFactor i)) hlambda
    have hD : 0 < (d : ℝ) * weight := mul_pos hdreal hweight
    have hfloor : (((d : ℝ) * weight)⁻¹) < (q : ℝ) + 1 := by
      simpa only [q, innerRadius, weight, upperWeight, lambda] using
        (Nat.lt_floor_add_one (((d : ℝ) * weight)⁻¹))
    have hmf : mahlerFactor i ≤ (d : ℝ) := mahlerFactor_le_rank i
    have hscale : lambda⁻¹ < (d : ℝ) ^ 2 * ((q : ℝ) + 1) := by
      have hone : ((d : ℝ) * weight)⁻¹ * ((d : ℝ) * weight) = 1 :=
        inv_mul_cancel₀ hD.ne'
      have hupperWeight : weight ≤ (d : ℝ) * lambda :=
        mul_le_mul_of_nonneg_right hmf hlambda.le
      have hposq : 0 < (q : ℝ) + 1 := by positivity
      have hprod : 1 < ((q : ℝ) + 1) * ((d : ℝ) ^ 2 * lambda) := by
        calc
          1 = ((d : ℝ) * weight)⁻¹ * ((d : ℝ) * weight) := hone.symm
          _ < ((q : ℝ) + 1) * ((d : ℝ) * weight) := by
            exact mul_lt_mul_of_pos_right hfloor hD
          _ ≤ ((q : ℝ) + 1) * ((d : ℝ) * ((d : ℝ) * lambda)) := by
            gcongr
          _ = ((q : ℝ) + 1) * ((d : ℝ) ^ 2 * lambda) := by ring
      rw [← one_div]
      apply (div_lt_iff₀ hlambda).2
      nlinarith
    have hcoord := mahlerBasis_coordinate_mul_successiveMinimum_le
      hd p hp b hb z hz i
    have hCcast : (C : ℝ) =
        (d.factorial : ℝ) * (d : ℝ) ^ d * (8 : ℝ) ^ d := by
      simp [C, coordinateConstant]
    have hcoordDiv : |(b.repr z i : ℝ)| ≤ (C : ℝ) * lambda⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ hlambda).2
      simpa [lambda, hCcast, mul_comm] using hcoord
    have hstrict : |(b.repr z i : ℝ)| < (F : ℝ) * ((q : ℝ) + 1) := by
      have hCpos : (0 : ℝ) < C := by exact_mod_cast coordinateConstant_pos hd
      calc
        |(b.repr z i : ℝ)| ≤ (C : ℝ) * lambda⁻¹ := hcoordDiv
        _ < (C : ℝ) * ((d : ℝ) ^ 2 * ((q : ℝ) + 1)) :=
          mul_lt_mul_of_pos_left hscale hCpos
        _ = (F : ℝ) * ((q : ℝ) + 1) := by
          simp [F, johnFactor, C]
          ring
    have hcast : (((b.repr z i).natAbs : ℕ) : ℝ) =
        |(b.repr z i : ℝ)| := by simp
    have hnat : (b.repr z i).natAbs < F * (q + 1) := by
      rw [← hcast] at hstrict
      exact_mod_cast hstrict
    have hFpos : 0 < F := by
      simpa [F] using johnFactor_pos hd
    have hnatle : (b.repr z i).natAbs ≤ F * q + (F - 1) := by
      apply Nat.le_of_lt_succ
      have hsub : F - 1 + 1 = F :=
        Nat.sub_add_cancel (Nat.succ_le_iff.mp hFpos)
      rw [Nat.succ_eq_add_one, Nat.add_assoc, hsub]
      simpa [Nat.mul_add] using hnat
    change |b.repr z i| ≤ (johnRadius p i : ℤ)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hnatle
  inner_budget := by
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
    calc
      (∑ i, (((johnRadius p i / johnFactor d : ℕ) : ℝ)) *
          p (integralEmbed (b i))) =
          ∑ i, (innerRadius p i : ℝ) * p (integralEmbed (b i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [johnRadius_div hd]
      _ ≤ ∑ _i : Fin d, (d : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        exact (mul_le_mul_of_nonneg_left (hb i)
          (Nat.cast_nonneg (innerRadius p i))).trans
            (innerRadius_weight_bound hd p hp i)
      _ = (d : ℝ) * (d : ℝ)⁻¹ := by simp
      _ = 1 := mul_inv_cancel₀ hdreal.ne'

/-- The vacuous zero-dimensional minima data, with positive factor one. -/
noncomputable def zeroDimensionalMinimaData
    (p : Seminorm ℝ (Fin 0 → ℝ))
    (b : Basis (Fin 0) ℤ (LatticePoint 0)) (hb : IsMahlerBasis p b) :
    FullRankMinimaData p b where
  factor := 1
  radii := Fin.elim0
  factor_pos := by norm_num
  mahler := hb
  outer_coordinate_bound := by
    intro z hz i
    exact Fin.elim0 i
  inner_budget := by simp

/-- The formerly conditional `FullRankMinimaStatement` follows from the
coarse upper half of Minkowski II. -/
theorem fullRankMinimaStatement : FullRankMinimaStatement := by
  intro d p hp b hb
  by_cases hd : d = 0
  · subst d
    exact ⟨zeroDimensionalMinimaData p b hb⟩
  · exact ⟨fullRankMinimaData (Nat.pos_of_ne_zero hd) p hp b hb⟩

/-- Unconditional source-shaped discrete John theorem.  The explicit
factor bound is `max 1 (johnFactor d)`; no compact body or lattice section
appears in that bound. -/
theorem discreteJohnStatement : DiscreteJohnStatement := by
  intro d
  refine ⟨max 1 (johnFactor d), ?_⟩
  intro K hK points hpoints
  obtain ⟨b, hb⟩ := CFP.Bilu.Mahler.mahlerBasisStatement
    d hK.seminorm hK.seminorm_definite
  by_cases hd : d = 0
  · subst d
    let D := zeroDimensionalMinimaData hK.seminorm b hb
    refine ⟨0, 1, le_rfl, le_max_left _ _, ?_⟩
    exact ⟨certificateOfFullRankMinimaDataBody hK b D points hpoints⟩
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let D := fullRankMinimaData hdpos hK.seminorm
      hK.seminorm_definite b hb
    refine ⟨d, johnFactor d, le_rfl, le_max_right _ _, ?_⟩
    exact ⟨certificateOfFullRankMinimaDataBody hK b D points hpoints⟩

end MahlerExtraction
end DiscreteJohn
end Erdos186

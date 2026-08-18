/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MahlerBasis
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Successive-minimum infrastructure for Minkowski's second theorem

Mathlib contains Minkowski's first convex-body theorem, but (as of 4.33) it
does not contain successive minima or Minkowski's second theorem.  This file
develops the order-theoretic part of the missing theory for the standard
integer lattice.  In particular, it proves that every successive minimum is
finite, that the minima increase with the rank, and that the defining
infimum can be approximated by an actual independent integral family.

These statements are the prerequisites used in both classical proofs of
Minkowski's second theorem: one first chooses independent lattice points at
radii arbitrarily close to the successive minima, and only then applies the
volume/dissection argument.
-/

namespace Erdos186.CFP.Bilu.MinkowskiSecond

open scoped BigOperators
open Erdos186.CFP.Bilu.Mahler
open Module

/-- Restricting a linearly independent integral family to fewer indices
preserves admissibility at the same radius. -/
theorem AdmitsIndependent.antitone_rank {n k l : ℕ}
    {p : Seminorm ℝ (Fin n → ℝ)} {r : ℝ} (hkl : k ≤ l)
    (h : AdmitsIndependent p l r) : AdmitsIndependent p k r := by
  obtain ⟨v, hv, hp⟩ := h
  let e : Fin k → Fin l := Fin.castLE hkl
  refine ⟨fun i ↦ v (e i), hv.comp e (Fin.castLE_injective hkl), fun i ↦ hp (e i)⟩

/-- The standard integral coordinate vector. -/
noncomputable def standardIntegralPoint {n : ℕ} (i : Fin n) : IntegralPoint n :=
  (Pi.basisFun ℤ (Fin n)) i

@[simp]
theorem integralEmbed_standardIntegralPoint {n : ℕ} (i : Fin n) :
    integralEmbed (standardIntegralPoint i) = (Pi.basisFun ℝ (Fin n)) i := by
  classical
  ext j
  by_cases hij : i = j
  · subst j
    simp [standardIntegralPoint, integralEmbed]
  · simp [standardIntegralPoint, integralEmbed, hij]

/-- The embedded standard integral coordinate vectors are linearly
independent over the reals. -/
theorem linearIndependent_integralEmbed_standard {n : ℕ} :
    LinearIndependent ℝ (fun i : Fin n ↦ integralEmbed (standardIntegralPoint i)) := by
  simpa only [integralEmbed_standardIntegralPoint] using
    (Pi.basisFun ℝ (Fin n)).linearIndependent

/-- An explicit radius at which the standard coordinate vectors witness
full-rank admissibility. -/
noncomputable def standardRadius {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) : ℝ :=
  ∑ i : Fin n, p (integralEmbed (standardIntegralPoint i))

theorem standardRadius_nonneg {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) :
    0 ≤ standardRadius p := by
  exact Finset.sum_nonneg fun i _ ↦ apply_nonneg p _

/-- Every seminorm on the finite coordinate space is bounded by its values
on the standard basis times the ambient sup norm. -/
theorem apply_le_standardRadius_mul_norm {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (x : Fin n → ℝ) :
    p x ≤ standardRadius p * ‖x‖ := by
  have hrepr :
      ∑ i : Fin n, x i • integralEmbed (standardIntegralPoint i) = x := by
    classical
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      standardIntegralPoint, integralEmbed]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  calc
    p x = p (∑ i : Fin n, x i • integralEmbed (standardIntegralPoint i)) :=
      congrArg p hrepr.symm
    _ ≤ ∑ i : Fin n, |x i| * p (integralEmbed (standardIntegralPoint i)) :=
      Erdos186.CFP.Bilu.Mahler.seminorm_sum_le p x
        (fun i ↦ integralEmbed (standardIntegralPoint i))
    _ ≤
        ∑ i : Fin n, ‖x‖ * p (integralEmbed (standardIntegralPoint i)) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      exact mul_le_mul_of_nonneg_right
        (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i)
        (apply_nonneg p _)
    _ = standardRadius p * ‖x‖ := by
      rw [← Finset.mul_sum, mul_comm]
      rfl

/-- Seminorms on the finite real coordinate space are continuous.  This is
proved directly, rather than assumed as a finite-dimensional black box. -/
theorem continuous_seminorm {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) :
    Continuous p := by
  let C : NNReal := Real.toNNReal (standardRadius p)
  have hC : (C : ℝ) = standardRadius p := by
    exact Real.coe_toNNReal _ (standardRadius_nonneg p)
  let q : Seminorm ℝ (Fin n → ℝ) := C • normSeminorm ℝ (Fin n → ℝ)
  refine Seminorm.continuous_of_le (q := q) ?_ ?_
  · change Continuous (fun x : Fin n → ℝ ↦ (C : ℝ) * ‖x‖)
    exact continuous_const.mul continuous_norm
  · intro x
    simpa [q, NNReal.smul_def, hC] using apply_le_standardRadius_mul_norm p x

/-- The canonical embedding of the standard integral lattice is injective. -/
theorem integralEmbed_injective {n : ℕ} :
    Function.Injective (@integralEmbed n) := by
  intro x y hxy
  ext i
  have hi := congrFun hxy i
  change ((x i : ℤ) : ℝ) = ((y i : ℤ) : ℝ) at hi
  exact_mod_cast hi

/-- Every nonzero standard integral lattice point has ambient sup norm at
least one. -/
theorem one_le_norm_integralEmbed {n : ℕ} {x : IntegralPoint n}
    (hx : x ≠ 0) : 1 ≤ ‖integralEmbed x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hint : (1 : ℤ) ≤ |x i| := by
    have : (0 : ℤ) < |x i| := abs_pos.mpr hi
    omega
  have hreal : (1 : ℝ) ≤ |((x i : ℤ) : ℝ)| := by
    exact_mod_cast hint
  calc
    (1 : ℝ) ≤ ‖integralEmbed x i‖ := by
      simpa [integralEmbed, Real.norm_eq_abs] using hreal
    _ ≤ ‖integralEmbed x‖ := norm_le_pi_norm _ i

/-! ## The integral determinant input -/

/-- The integer matrix whose columns are a family of standard integral
lattice points. -/
def integralColumns {n : ℕ} (v : Fin n → IntegralPoint n) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun row col ↦ v col row

@[simp]
theorem integralColumns_apply {n : ℕ} (v : Fin n → IntegralPoint n)
    (row col : Fin n) : integralColumns v row col = v col row := rfl

/-- Casting the integral column matrix to the reals gives exactly the
matrix whose columns are the embedded lattice vectors. -/
theorem map_integralColumns {n : ℕ} (v : Fin n → IntegralPoint n) :
    (integralColumns v).map (Int.castRingHom ℝ) =
      fun row col ↦ integralEmbed (v col) row := by
  rfl

/-- A full independent family of standard integral lattice vectors has
integer determinant of absolute value at least one.  This is the lattice
covolume input in both halves of Minkowski's second theorem. -/
theorem one_le_abs_det_integralColumns {n : ℕ}
    (v : Fin n → IntegralPoint n)
    (hv : LinearIndependent ℝ (fun j ↦ integralEmbed (v j))) :
    (1 : ℝ) ≤ |(((integralColumns v).det : ℤ) : ℝ)| := by
  let A : Matrix (Fin n) (Fin n) ℝ :=
    (integralColumns v).map (Int.castRingHom ℝ)
  have hcols : LinearIndependent ℝ A.col := by
    have hcol : A.col = fun j ↦ integralEmbed (v j) := by
      ext j row
      rfl
    rw [hcol]
    exact hv
  have hAunit : IsUnit A := Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  have hAdet : A.det ≠ 0 :=
    (A.isUnit_iff_isUnit_det.mp hAunit).ne_zero
  have hcastdet : (((integralColumns v).det : ℤ) : ℝ) = A.det := by
    simpa [A] using (Int.cast_det (R := ℝ) (integralColumns v))
  have hintdet : (integralColumns v).det ≠ 0 := by
    intro hzero
    apply hAdet
    rw [← hcastdet, hzero, Int.cast_zero]
  have hint : (1 : ℤ) ≤ |(integralColumns v).det| := by
    have : (0 : ℤ) < |(integralColumns v).det| := abs_pos.mpr hintdet
    omega
  exact_mod_cast hint

/-- Scale each embedded lattice column by its own real factor. -/
def scaledRealColumns {n : ℕ} (a : Fin n → ℝ)
    (v : Fin n → IntegralPoint n) : Matrix (Fin n) (Fin n) ℝ :=
  fun row col ↦ a col * integralEmbed (v col) row

/-- Columnwise scaling multiplies the determinant by the product of the
scale factors. -/
theorem det_scaledRealColumns {n : ℕ} (a : Fin n → ℝ)
    (v : Fin n → IntegralPoint n) :
    (scaledRealColumns a v).det =
      (∏ i, a i) * (((integralColumns v).det : ℤ) : ℝ) := by
  let A : Matrix (Fin n) (Fin n) ℝ :=
    fun row col ↦ integralEmbed (v col) row
  calc
    (scaledRealColumns a v).det =
        (Matrix.of fun row col ↦ a col * A row col).det := by rfl
    _ = (∏ i, a i) * A.det := Matrix.det_mul_row a A
    _ = (∏ i, a i) * (((integralColumns v).det : ℤ) : ℝ) := by
      congr 1
      rw [Int.cast_det]
      congr

/-- After arbitrary columnwise scaling, the determinant is bounded below
by the product of the absolute scale factors. -/
theorem prod_abs_le_abs_det_scaledRealColumns {n : ℕ}
    (a : Fin n → ℝ) (v : Fin n → IntegralPoint n)
    (hv : LinearIndependent ℝ (fun j ↦ integralEmbed (v j))) :
    (∏ i, |a i|) ≤ |(scaledRealColumns a v).det| := by
  rw [det_scaledRealColumns, abs_mul, Finset.abs_prod]
  have hprod : 0 ≤ ∏ i, |a i| := Finset.prod_nonneg fun i _ ↦ abs_nonneg _
  simpa using mul_le_mul_of_nonneg_left
    (one_le_abs_det_integralColumns v hv) hprod

/-! ## Crosspolytope inclusion -/

/-- The standard closed crosspolytope, i.e. the unit ball of the l1 norm. -/
def l1UnitBall (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∑ i, |x i|) ≤ 1}

/-- The standard l1 unit ball has volume `2^n / n!`.  This is the
specialization at `p = 1` of Mathlib's general finite-dimensional Lp-ball
volume formula. -/
theorem volume_l1UnitBall {n : ℕ} [Nonempty (Fin n)] :
    MeasureTheory.volume (l1UnitBall n) =
      ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) := by
  have hGammaTwo : Real.Gamma ((1 : ℝ) + 1) = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  simpa [l1UnitBall, Real.rpow_one, Real.Gamma_nat_eq_factorial,
    hGammaTwo] using
    (MeasureTheory.volume_sum_rpow_le (Fin n) (p := (1 : ℝ)) le_rfl 1)

/-- The linear combination whose matrix is `scaledRealColumns a v`. -/
def scaledCombination {n : ℕ} (a x : Fin n → ℝ)
    (v : Fin n → IntegralPoint n) : Fin n → ℝ :=
  ∑ i, x i • (a i • integralEmbed (v i))

/-- Matrix multiplication by the scaled column matrix agrees with the
corresponding finite linear combination. -/
theorem mulVec_scaledRealColumns {n : ℕ} (a x : Fin n → ℝ)
    (v : Fin n → IntegralPoint n) :
    (scaledRealColumns a v).mulVec x = scaledCombination a x v := by
  ext row
  simp [Matrix.mulVec, dotProduct, scaledRealColumns, scaledCombination,
    mul_comm, mul_left_comm]

/-- If every scaled generator has seminorm at most one, the seminorm of
the resulting combination is bounded by the l1 norm of its coefficient
vector.  Geometrically, this is the inclusion of the associated
crosspolytope in the seminorm unit ball. -/
theorem seminorm_scaledCombination_le_l1 {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (a x : Fin n → ℝ)
    (v : Fin n → IntegralPoint n)
    (ha : ∀ i, |a i| * p (integralEmbed (v i)) ≤ 1) :
    p (scaledCombination a x v) ≤ ∑ i, |x i| := by
  refine (Erdos186.CFP.Bilu.Mahler.seminorm_sum_le p x
    (fun i ↦ a i • integralEmbed (v i))).trans ?_
  calc
    (∑ i, |x i| * p (a i • integralEmbed (v i))) =
        ∑ i, |x i| * (|a i| * p (integralEmbed (v i))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul_eq_mul, Real.norm_eq_abs]
    _ ≤ ∑ i, |x i| * 1 := by
      exact Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (ha i) (abs_nonneg _)
    _ = ∑ i, |x i| := by simp

/-- Unit-l1 coefficients map into the seminorm unit ball. -/
theorem scaledCombination_mem_unitBall {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (a x : Fin n → ℝ)
    (v : Fin n → IntegralPoint n)
    (ha : ∀ i, |a i| * p (integralEmbed (v i)) ≤ 1)
    (hx : (∑ i, |x i|) ≤ 1) :
    p (scaledCombination a x v) ≤ 1 :=
  (seminorm_scaledCombination_le_l1 p a x v ha).trans hx

/-- Exact volume of a scaled integral crosspolytope. -/
theorem volume_image_l1UnitBall_scaledRealColumns {n : ℕ}
    [Nonempty (Fin n)] (a : Fin n → ℝ)
    (v : Fin n → IntegralPoint n) :
    MeasureTheory.volume
        ((Matrix.toLin' (scaledRealColumns a v)) '' l1UnitBall n) =
      ENNReal.ofReal |(scaledRealColumns a v).det| *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) := by
  rw [MeasureTheory.Measure.addHaar_image_linearMap,
    LinearMap.det_toLin', volume_l1UnitBall]

/-- The volume of a scaled crosspolytope generated by independent integral
vectors is at least the product of the absolute scale factors times
`2^n/n!`. -/
theorem volume_image_l1UnitBall_scaledRealColumns_lower {n : ℕ}
    [Nonempty (Fin n)] (a : Fin n → ℝ)
    (v : Fin n → IntegralPoint n)
    (hv : LinearIndependent ℝ (fun j ↦ integralEmbed (v j))) :
    ENNReal.ofReal (∏ i, |a i|) *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      MeasureTheory.volume
        ((Matrix.toLin' (scaledRealColumns a v)) '' l1UnitBall n) := by
  rw [volume_image_l1UnitBall_scaledRealColumns]
  gcongr
  exact prod_abs_le_abs_det_scaledRealColumns a v hv

/-- The scaled integral crosspolytope is contained in the seminorm unit
ball whenever all its generators have seminorm at most one. -/
theorem image_l1UnitBall_subset_seminorm_unitBall {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (a : Fin n → ℝ)
    (v : Fin n → IntegralPoint n)
    (ha : ∀ i, |a i| * p (integralEmbed (v i)) ≤ 1) :
    (Matrix.toLin' (scaledRealColumns a v)) '' l1UnitBall n ⊆
      {y | p y ≤ 1} := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Matrix.toLin'_apply, mulVec_scaledRealColumns]
  exact scaledCombination_mem_unitBall p a x v ha hx

/-- Crosspolytope lower bound for the volume of a seminorm unit ball. -/
theorem crosspolytope_volume_le_seminorm_unitBall {n : ℕ}
    [Nonempty (Fin n)] (p : Seminorm ℝ (Fin n → ℝ))
    (a : Fin n → ℝ) (v : Fin n → IntegralPoint n)
    (hv : LinearIndependent ℝ (fun j ↦ integralEmbed (v j)))
    (ha : ∀ i, |a i| * p (integralEmbed (v i)) ≤ 1) :
    ENNReal.ofReal (∏ i, |a i|) *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      MeasureTheory.volume {y | p y ≤ 1} := by
  exact (volume_image_l1UnitBall_scaledRealColumns_lower a v hv).trans
    (MeasureTheory.measure_mono (image_l1UnitBall_subset_seminorm_unitBall p a v ha))

/-- A definite seminorm on a nonzero finite coordinate space dominates a
positive multiple of the ambient norm.  The proof minimizes the seminorm
on the compact unit sphere. -/
theorem exists_pos_mul_norm_le {n : ℕ} [Nonempty (Fin n)]
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ p x := by
  let S : Set (Fin n → ℝ) := Metric.sphere 0 1
  have hS_ne : S.Nonempty := by
    exact NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨y, hyS, hymin⟩ :=
    (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hS_ne
      (continuous_seminorm p).continuousOn
  have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hyS
  have hpy_pos : 0 < p y := lt_of_le_of_ne (apply_nonneg p y) fun hpy ↦ by
    have hy0 : y = 0 := hp y hpy.symm
    subst y
    norm_num at hy_norm
  refine ⟨p y, hpy_pos, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let z : Fin n → ℝ := ‖x‖⁻¹ • x
    have hzS : z ∈ S := by
      rw [show S = Metric.sphere (0 : Fin n → ℝ) 1 from rfl,
        mem_sphere_zero_iff_norm]
      simp [z, norm_smul, hxnorm.ne']
    have hmin : p y ≤ p z := hymin hzS
    have hscale : p z = p x / ‖x‖ := by
      change p (‖x‖⁻¹ • x) = p x / ‖x‖
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_norm, div_eq_inv_mul]
    rw [hscale] at hmin
    exact (le_div_iff₀ hxnorm).mp hmin

/-- The standard basis witnesses `n` independent lattice points in the
ball of radius `standardRadius p`. -/
theorem admitsIndependent_standardRadius {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) :
    AdmitsIndependent p n (standardRadius p) := by
  refine ⟨standardIntegralPoint, linearIndependent_integralEmbed_standard, ?_⟩
  intro i
  exact Finset.single_le_sum (fun j _ ↦ apply_nonneg p
    (integralEmbed (standardIntegralPoint j))) (Finset.mem_univ i)

/-- Every rank not exceeding the ambient dimension is admissible at the
same explicit standard-basis radius. -/
theorem admitsIndependent_standardRadius_of_le {n k : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hkn : k ≤ n) :
    AdmitsIndependent p k (standardRadius p) :=
  AdmitsIndependent.antitone_rank hkn (admitsIndependent_standardRadius p)

/-- The set whose infimum defines any successive minimum is nonempty. -/
theorem successiveMinimum_set_nonempty {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n) :
    {r : ℝ | AdmitsIndependent p (i.val + 1) r}.Nonempty := by
  exact ⟨standardRadius p,
    admitsIndependent_standardRadius_of_le p i.isLt⟩

/-- All successive minima have the explicit finite upper bound supplied by
the standard integral coordinate basis. -/
theorem successiveMinimum_le_standardRadius {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n) :
    successiveMinimum p i ≤ standardRadius p :=
  successiveMinimum_le_of_admits
    (admitsIndependent_standardRadius_of_le p i.isLt)

/-- For a definite seminorm every successive minimum is strictly positive.
This uses both discreteness of the standard integer lattice and compactness
of the ambient unit sphere. -/
theorem successiveMinimum_pos {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (i : Fin n) :
    0 < successiveMinimum p i := by
  let _ : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨c, hc, hc_lower⟩ := exists_pos_mul_norm_le p hp
  rw [successiveMinimum]
  refine hc.trans_le (le_csInf (successiveMinimum_set_nonempty p i) ?_)
  intro r hr
  obtain ⟨v, hv, hvr⟩ := hr
  let j : Fin (i.val + 1) := ⟨0, Nat.succ_pos i.val⟩
  have hvreal : integralEmbed (v j) ≠ 0 := hv.ne_zero j
  have hvint : v j ≠ 0 := fun hv0 ↦ by
    apply hvreal
    rw [hv0, integralEmbed_zero]
  have hone : (1 : ℝ) ≤ ‖integralEmbed (v j)‖ :=
    one_le_norm_integralEmbed hvint
  calc
    c ≤ c * ‖integralEmbed (v j)‖ := by
      nlinarith
    _ ≤ p (integralEmbed (v j)) := hc_lower _
    _ ≤ r := hvr j

/-- Successive minima are monotone in their one-based rank. -/
theorem successiveMinimum_mono {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) {i j : Fin n} (hij : i ≤ j) :
    successiveMinimum p i ≤ successiveMinimum p j := by
  rw [successiveMinimum, successiveMinimum]
  refine le_csInf (successiveMinimum_set_nonempty p j) ?_
  intro r hr
  exact csInf_le
    ⟨0, fun R hR ↦ hR.nonneg (Nat.succ_pos i.val)⟩
    (AdmitsIndependent.antitone_rank (Nat.succ_le_succ hij) hr)

/-- The defining infimum can be approached from above by a radius carrying
an actual independent integral family.  No attainment assertion is hidden
here: the arbitrarily small positive error is explicit. -/
theorem exists_admitsIndependent_lt_add {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, AdmitsIndependent p (i.val + 1) r ∧
      r < successiveMinimum p i + ε := by
  rw [successiveMinimum]
  exact exists_lt_of_csInf_lt (successiveMinimum_set_nonempty p i)
    (lt_add_of_pos_right _ hε)

/-- Unpacked approximation form: there are actual independent integral
vectors, all lying in the ball of radius `lambda_i + ε`. -/
theorem exists_independent_integral_points_le_add {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Fin (i.val + 1) → IntegralPoint n,
      LinearIndependent ℝ (fun j ↦ integralEmbed (v j)) ∧
      ∀ j, p (integralEmbed (v j)) < successiveMinimum p i + ε := by
  obtain ⟨r, ⟨v, hv, hvr⟩, hr⟩ := exists_admitsIndependent_lt_add p i hε
  exact ⟨v, hv, fun j ↦ (hvr j).trans_lt hr⟩

/-- Full-rank specialization of infimum approximation, bundled with the
integer determinant lower bound.  This is the exact algebraic input used
when the crosspolytope spanned by the chosen points is compared with the
convex body. -/
theorem exists_full_rank_approx_with_det {n : ℕ}
    (p : Seminorm ℝ (Fin (n + 1) → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Fin (n + 1) → IntegralPoint (n + 1),
      LinearIndependent ℝ (fun j ↦ integralEmbed (v j)) ∧
      (∀ j, p (integralEmbed (v j)) <
        successiveMinimum p (Fin.last n) + ε) ∧
      (1 : ℝ) ≤ |(((integralColumns v).det : ℤ) : ℝ)| := by
  obtain ⟨v, hv, hpv⟩ :=
    exists_independent_integral_points_le_add p (Fin.last n) hε
  exact ⟨v, hv, hpv, one_le_abs_det_integralColumns v hv⟩

end Erdos186.CFP.Bilu.MinkowskiSecond

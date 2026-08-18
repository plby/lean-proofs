/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MahlerBox

/-!
# The outer rectangular bound in Bilu Section 3

The missing direction in the Mahler-box construction is a bound on the
coordinates of a lattice point of the convex body.  Replacing one column
of the unimodular Mahler basis by that point exposes the corresponding
basis coordinate as a determinant.  The associated scaled crosspolytope,
together with the coarse upper half of Minkowski's second theorem, then
gives a dimension-only coordinate bound.
-/

namespace Erdos186.CFP.Bilu.MahlerOuterBox

open scoped BigOperators ENNReal
open Module
open MeasureTheory
open Erdos186.CFP.Bilu.Mahler
open Erdos186.CFP.Bilu.MahlerBox
open Erdos186.CFP.Bilu.MinkowskiSecond
open Erdos186.CFP.Bilu.MinkowskiUpper

/-- Replace the `i`th vector of an integral basis by `z`. -/
noncomputable def replaceBasisVector {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (z : IntegralPoint n) (i : Fin n) : Fin n → IntegralPoint n :=
  fun j ↦ if j = i then z else b j

theorem integralColumns_replaceBasisVector {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (z : IntegralPoint n) (i : Fin n) :
    integralColumns (replaceBasisVector b z i) =
      (integralColumns (fun j ↦ b j)).updateCol i (fun row ↦ z row) := by
  ext row col
  by_cases hcol : col = i
  · subst col
    simp [replaceBasisVector, integralColumns]
  · simp [replaceBasisVector, integralColumns, hcol]

/-- Replacing a basis column by `z` multiplies its determinant by the
corresponding basis coordinate. -/
theorem det_integralColumns_replaceBasisVector {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (z : IntegralPoint n) (i : Fin n) :
    (integralColumns (replaceBasisVector b z i)).det =
      b.repr z i * (integralColumns (fun j ↦ b j)).det := by
  rw [integralColumns_replaceBasisVector]
  let A : Matrix (Fin n) (Fin n) ℤ := integralColumns (fun j ↦ b j)
  have hz : (fun row ↦ z row) =
      fun row ↦ ∑ j, (b.repr z j) • A row j := by
    funext row
    have hrepr := congrFun (b.sum_repr z) row
    simpa only [A, integralColumns, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using hrepr.symm
  rw [hz, Matrix.det_updateCol_sum]
  rfl

/-- Absolute-value form of the preceding determinant identity, using
unimodularity of the original integral basis. -/
theorem abs_cast_det_integralColumns_replaceBasisVector {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (z : IntegralPoint n) (i : Fin n) :
    |(((integralColumns (replaceBasisVector b z i)).det : ℤ) : ℝ)| =
      |((b.repr z i : ℤ) : ℝ)| := by
  rw [det_integralColumns_replaceBasisVector, Int.cast_mul, abs_mul]
  have hbdet :
      |(((integralColumns (fun j ↦ b j)).det : ℤ) : ℝ)| = 1 := by
    have hcast :
        (((integralColumns (fun j ↦ b j)).det : ℤ) : ℝ) =
          (integralBasisMatrix b).det := by
      simpa [integralBasisMatrix, integralColumns] using
        (Int.cast_det (R := ℝ) (integralColumns (fun j ↦ b j)))
    rw [hcast]
    exact abs_det_integralBasisMatrix b
  rw [hbdet, mul_one]

/-- Scale the replacement vector by one and every unchanged basis vector
by the reciprocal of its seminorm. -/
noncomputable def replacementScale {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (i : Fin n) : Fin n → ℝ :=
  fun j ↦ if j = i then 1 else (p (integralEmbed (b j)))⁻¹

theorem replacementScale_nonneg {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (i j : Fin n) :
    0 ≤ replacementScale p b i j := by
  by_cases hji : j = i
  · simp [replacementScale, hji]
  · simp [replacementScale, hji, apply_nonneg]

theorem seminorm_integralBasis_pos {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (j : Fin n) :
    0 < p (integralEmbed (b j)) := by
  have hb0 : b j ≠ 0 := b.linearIndependent.ne_zero j
  have hembed0 : integralEmbed (b j) ≠ 0 := by
    intro hzero
    apply hb0
    apply integralEmbed_injective
    simpa only [integralEmbed_zero] using hzero
  apply lt_of_le_of_ne (apply_nonneg p _)
  intro hpzero
  exact hembed0 (hp _ hpzero.symm)

theorem prod_replacementScale {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (i : Fin n) :
    (∏ j : Fin n, replacementScale p b i j) =
      (∏ j ∈ Finset.univ.erase i, p (integralEmbed (b j)))⁻¹ := by
  classical
  rw [← Finset.prod_inv_distrib]
  simp only [replacementScale]
  rw [Finset.prod_ite]
  rw [Finset.filter_ne']
  simp

/-- Every generator of the replacement crosspolytope lies in the
seminorm unit ball. -/
theorem replacementScale_generator_bound {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (z : IntegralPoint n) (hz : p (integralEmbed z) ≤ 1)
    (i j : Fin n) :
    |replacementScale p b i j| *
        p (integralEmbed (replaceBasisVector b z i j)) ≤ 1 := by
  by_cases hji : j = i
  · subst j
    simpa [replacementScale, replaceBasisVector] using hz
  · have hpj : 0 < p (integralEmbed (b j)) :=
      seminorm_integralBasis_pos p hp b j
    simp [replacementScale, replaceBasisVector, hji, abs_of_pos hpj,
      hpj.ne']

/-- The replacement crosspolytope gives the determinant/volume inequality
which is the heart of Bilu's outer-coordinate estimate. -/
theorem replacement_coordinate_crosspolytope_volume_le {n : ℕ}
    [Nonempty (Fin n)]
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (z : IntegralPoint n) (hz : p (integralEmbed z) ≤ 1)
    (i : Fin n) :
    ENNReal.ofReal
          ((∏ j : Fin n, replacementScale p b i j) *
            |((b.repr z i : ℤ) : ℝ)|) *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      volume {y | p y ≤ 1} := by
  let a : Fin n → ℝ := replacementScale p b i
  let v : Fin n → IntegralPoint n := replaceBasisVector b z i
  have ha : ∀ j, |a j| * p (integralEmbed (v j)) ≤ 1 := by
    exact replacementScale_generator_bound p hp b z hz i
  have hmono :
      volume ((Matrix.toLin' (scaledRealColumns a v)) '' l1UnitBall n) ≤
        volume {y | p y ≤ 1} :=
    measure_mono (image_l1UnitBall_subset_seminorm_unitBall p a v ha)
  rw [volume_image_l1UnitBall_scaledRealColumns] at hmono
  have hdet : |(scaledRealColumns a v).det| =
      (∏ j : Fin n, replacementScale p b i j) *
        |((b.repr z i : ℤ) : ℝ)| := by
    rw [det_scaledRealColumns, abs_mul, Finset.abs_prod]
    rw [Finset.prod_congr rfl (fun j _ ↦
      abs_of_nonneg (replacementScale_nonneg p b i j))]
    rw [abs_cast_det_integralColumns_replaceBasisVector]
  rw [hdet] at hmono
  exact hmono

/-- Real-valued form of the replacement crosspolytope inequality. -/
theorem replacement_coordinate_crosspolytope_volume_real_le {n : ℕ}
    [Nonempty (Fin n)]
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (z : IntegralPoint n) (hz : p (integralEmbed z) ≤ 1)
    (i : Fin n) :
    ((∏ j : Fin n, replacementScale p b i j) *
          |((b.repr z i : ℤ) : ℝ)|) *
        ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      volume.real {y | p y ≤ 1} := by
  have h := replacement_coordinate_crosspolytope_volume_le p hp b z hz i
  have htop : volume {y | p y ≤ 1} ≠ ∞ :=
    (isBounded_unitBall p hp).measure_lt_top.ne
  have hreal := ENNReal.toReal_mono htop h
  have hscale : 0 ≤ ∏ j : Fin n, replacementScale p b i j :=
    Finset.prod_nonneg fun j _ ↦ replacementScale_nonneg p b i j
  have hleft : 0 ≤
      (∏ j : Fin n, replacementScale p b i j) *
        |((b.repr z i : ℤ) : ℝ)| :=
    mul_nonneg hscale (abs_nonneg _)
  have hsimplex : 0 ≤ (2 : ℝ) ^ n / (n.factorial : ℝ) := by positivity
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hleft,
    ENNReal.toReal_ofReal hsimplex, measureReal_def] using hreal

/-- Bilu's Section 3 outer-coordinate estimate.  The constant is
dimension-only; `8^n / 2^n` is the loss from the proved coarse upper
Minkowski theorem divided by the crosspolytope volume factor. -/
theorem basisCoordinate_mul_successiveMinimum_le {n : ℕ}
    (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (hb : IsMahlerBasis p b)
    (z : IntegralPoint n) (hz : p (integralEmbed z) ≤ 1)
    (i : Fin n) :
    |((b.repr z i : ℤ) : ℝ)| * successiveMinimum p i ≤
      (((8 : ℝ) ^ n * (n.factorial : ℝ)) / (2 : ℝ) ^ n) *
        (∏ j : Fin n, mahlerFactor j) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let U : Finset (Fin n) := Finset.univ.erase i
  let Q : ℝ := ∏ j ∈ U, p (integralEmbed (b j))
  let L : ℝ := ∏ j ∈ U, successiveMinimum p j
  let F : ℝ := ∏ j ∈ U, mahlerFactor j
  let c : ℝ := |((b.repr z i : ℤ) : ℝ)|
  let simplex : ℝ := (2 : ℝ) ^ n / (n.factorial : ℝ)
  let body : ℝ := volume.real {y | p y ≤ 1}
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact Finset.prod_pos fun j _ ↦ seminorm_integralBasis_pos p hp b j
  have hL : 0 < L := by
    dsimp only [L]
    exact Finset.prod_pos fun j _ ↦ successiveMinimum_pos p hp j
  have hF : 0 < F := by
    dsimp only [F]
    exact Finset.prod_pos fun j _ ↦
      zero_lt_one.trans_le (one_le_mahlerFactor j)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hsimplex : 0 < simplex := by dsimp only [simplex]; positivity
  have hQbound : Q ≤ F * L := by
    calc
      Q ≤ ∏ j ∈ U,
          mahlerFactor j * successiveMinimum p j := by
        apply Finset.prod_le_prod (fun j _ ↦ (apply_nonneg p _))
        intro j hj
        exact hb j
      _ = F * L := by
        simp only [F, L, Finset.prod_mul_distrib]
  have hinv : (F * L)⁻¹ ≤ Q⁻¹ :=
    (inv_le_inv₀ (mul_pos hF hL) hQ).2 hQbound
  have hcross0 :=
    replacement_coordinate_crosspolytope_volume_real_le p hp b z hz i
  have hcross : Q⁻¹ * c * simplex ≤ body := by
    rw [prod_replacementScale] at hcross0
    simpa only [Q, c, simplex, body, U, mul_assoc] using hcross0
  have hcrossWeak : (F * L)⁻¹ * c * simplex ≤ body := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hinv hc) hsimplex.le).trans hcross
  have hminkowski0 := minkowskiSecond_upper_eight_pow_real p hp
  have hfullProduct :
      (∏ j : Fin n, successiveMinimum p j) = L * successiveMinimum p i := by
    simpa only [L, U] using
      (Finset.prod_erase_mul Finset.univ
        (fun j : Fin n ↦ successiveMinimum p j) (Finset.mem_univ i)).symm
  have hminkowski : body * (successiveMinimum p i * L) ≤ (8 : ℝ) ^ n := by
    rw [mul_comm (successiveMinimum p i) L, ← hfullProduct]
    simpa only [body, unitBall, mul_comm] using hminkowski0
  have hcombined :
      ((F * L)⁻¹ * c * simplex) *
          (successiveMinimum p i * L) ≤ (8 : ℝ) ^ n := by
    exact (mul_le_mul_of_nonneg_right hcrossWeak
      (mul_nonneg (successiveMinimum_nonneg p i) hL.le)).trans hminkowski
  have hcancel :
      ((F * L)⁻¹ * c * simplex) *
          (successiveMinimum p i * L) =
        (c * successiveMinimum p i * simplex) / F := by
    field_simp
  rw [hcancel] at hcombined
  have hnumerator : c * successiveMinimum p i * simplex ≤
      (8 : ℝ) ^ n * F :=
    (div_le_iff₀ hF).mp hcombined
  have hcoordF : c * successiveMinimum p i ≤
      ((8 : ℝ) ^ n * F) / simplex := by
    apply (le_div_iff₀ hsimplex).2
    simpa only [mul_assoc] using hnumerator
  have hFfull : F ≤ ∏ j : Fin n, mahlerFactor j := by
    have hprod : F * mahlerFactor i = ∏ j : Fin n, mahlerFactor j := by
      simpa only [F, U] using
        Finset.prod_erase_mul Finset.univ (fun j : Fin n ↦ mahlerFactor j)
          (Finset.mem_univ i)
    rw [← hprod]
    exact le_mul_of_one_le_right hF.le (one_le_mahlerFactor i)
  have hconstant :
      ((8 : ℝ) ^ n * F) / simplex =
        (((8 : ℝ) ^ n * (n.factorial : ℝ)) / (2 : ℝ) ^ n) * F := by
    dsimp only [simplex]
    field_simp
  rw [hconstant] at hcoordF
  exact hcoordF.trans (mul_le_mul_of_nonneg_left hFfull (by positivity))

end Erdos186.CFP.Bilu.MahlerOuterBox

#print axioms Erdos186.CFP.Bilu.MahlerOuterBox.abs_cast_det_integralColumns_replaceBasisVector
#print axioms Erdos186.CFP.Bilu.MahlerOuterBox.replacement_coordinate_crosspolytope_volume_le
#print axioms Erdos186.CFP.Bilu.MahlerOuterBox.basisCoordinate_mul_successiveMinimum_le

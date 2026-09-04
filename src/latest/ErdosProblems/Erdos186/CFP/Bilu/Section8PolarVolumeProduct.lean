/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MahlerTheorem
import ErdosProblems.Erdos186.CFP.Bilu.MahlerOuterBox
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecondUpperDirect
import ErdosProblems.Erdos186.CFP.Bilu.PolarSeparation

/-!
# A coarse polar-volume product bound

For the Section 8 exceptional-set estimate it is enough to have any
dimension-only upper bound for `vol(B) vol(B⁺)`.  A Mahler basis sends the
polar of a seminorm unit ball into the coordinate box with half-widths
`p(b i)`.  The basis is unimodular, and the coarse upper half of Minkowski's
second theorem bounds the product of these half-widths times `vol(B)`.

This gives the explicit (deliberately coarse) constant `(16 n)^n`, avoiding
any appeal to the Blaschke--Santaló inequality.
-/

namespace Erdos186.CFP.Bilu.Section8PolarVolumeProduct

open scoped BigOperators ENNReal
open MeasureTheory Set Module
open Mahler MinkowskiSecond MinkowskiUpper PolarSeparation

noncomputable section

set_option autoImplicit false

/-- The absolute polar is closed, hence measurable, without any regularity
assumption on the original set. -/
theorem isClosed_euclideanPolar {n : ℕ} (B : Set (Fin n → ℝ)) :
    IsClosed (euclideanPolar B) := by
  change IsClosed {z | ∀ x, x ∈ B → |euclideanPairing x z| ≤ 1}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _hx
  apply isClosed_le
  · apply Continuous.abs
    unfold euclideanPairing
    fun_prop
  · exact continuous_const

theorem measurableSet_euclideanPolar {n : ℕ} (B : Set (Fin n → ℝ)) :
    MeasurableSet (euclideanPolar B) :=
  (isClosed_euclideanPolar B).measurableSet

/-- Pairing with the vectors of an integral basis, written as one linear
map.  Its matrix is the transpose of the integral basis matrix. -/
def dualBasisMap {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLin' (integralBasisMatrix b).transpose

@[simp] theorem dualBasisMap_apply {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (z : Fin n → ℝ) (i : Fin n) :
    dualBasisMap b z i = euclideanPairing (integralEmbed (b i)) z := by
  simp [dualBasisMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    euclideanPairing, integralBasisMatrix_apply, integralEmbed, mul_comm]

theorem abs_det_dualBasisMap {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    |LinearMap.det (dualBasisMap b)| = 1 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
  change |(LinearMap.toMatrix'
    (Matrix.toLin' (integralBasisMatrix b).transpose)).det| = 1
  simpa only [LinearMap.toMatrix'_toLin', Matrix.det_transpose] using
    abs_det_integralBasisMatrix b

/-- The rectangular box dual to the scaled basis crosspolytope. -/
def mahlerPolarBox {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) : Set (Fin n → ℝ) :=
  Icc (fun i ↦ -p (integralEmbed (b i)))
    (fun i ↦ p (integralEmbed (b i)))

/-- The transpose-basis coordinates of every point of the polar lie in the
explicit Mahler box. -/
theorem image_euclideanPolar_unitBall_subset_mahlerPolarBox
    {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    dualBasisMap b '' euclideanPolar (unitBall p) ⊆
      mahlerPolarBox p b := by
  rintro y ⟨z, hz, rfl⟩
  rw [mem_euclideanPolar_iff] at hz
  constructor <;> intro i
  · have hpi : 0 < p (integralEmbed (b i)) :=
      Erdos186.CFP.Bilu.MahlerOuterBox.seminorm_integralBasis_pos p hp b i
    let x : Fin n → ℝ :=
      (p (integralEmbed (b i)))⁻¹ • integralEmbed (b i)
    have hx : x ∈ unitBall p := by
      change p x ≤ 1
      dsimp only [x]
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpi),
        inv_mul_cancel₀ hpi.ne']
    have hpair := hz x hx
    rw [dualBasisMap_apply]
    dsimp only [x] at hpair
    have hscale : euclideanPairing
        ((p (integralEmbed (b i)))⁻¹ • integralEmbed (b i)) z =
        (p (integralEmbed (b i)))⁻¹ *
          euclideanPairing (integralEmbed (b i)) z := by
      simp [euclideanPairing, Finset.mul_sum, mul_assoc]
    rw [hscale, abs_mul, abs_of_pos (inv_pos.mpr hpi)] at hpair
    have habs : |euclideanPairing (integralEmbed (b i)) z| ≤
        p (integralEmbed (b i)) := by
      exact (inv_mul_le_one₀ hpi).mp hpair
    exact (abs_le.mp habs).1
  · have hpi : 0 < p (integralEmbed (b i)) :=
      Erdos186.CFP.Bilu.MahlerOuterBox.seminorm_integralBasis_pos p hp b i
    let x : Fin n → ℝ :=
      (p (integralEmbed (b i)))⁻¹ • integralEmbed (b i)
    have hx : x ∈ unitBall p := by
      change p x ≤ 1
      dsimp only [x]
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpi),
        inv_mul_cancel₀ hpi.ne']
    have hpair := hz x hx
    rw [dualBasisMap_apply]
    dsimp only [x] at hpair
    have hscale : euclideanPairing
        ((p (integralEmbed (b i)))⁻¹ • integralEmbed (b i)) z =
        (p (integralEmbed (b i)))⁻¹ *
          euclideanPairing (integralEmbed (b i)) z := by
      simp [euclideanPairing, Finset.mul_sum, mul_assoc]
    rw [hscale, abs_mul, abs_of_pos (inv_pos.mpr hpi)] at hpair
    have habs : |euclideanPairing (integralEmbed (b i)) z| ≤
        p (integralEmbed (b i)) := by
      exact (inv_mul_le_one₀ hpi).mp hpair
    exact (abs_le.mp habs).2

/-- Exact volume of the Mahler polar box. -/
theorem volume_mahlerPolarBox {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    volume (mahlerPolarBox p b) =
      ENNReal.ofReal ((2 : ℝ) ^ n *
        ∏ i, p (integralEmbed (b i))) := by
  rw [mahlerPolarBox, Real.volume_Icc_pi]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ ↦ apply_nonneg p (integralEmbed (b i)))]
  simp only [sub_neg_eq_add]
  have hterm (i : Fin n) :
      ENNReal.ofReal
          (p (integralEmbed (b i)) + p (integralEmbed (b i))) =
        2 * ENNReal.ofReal (p (integralEmbed (b i))) := by
    rw [show p (integralEmbed (b i)) + p (integralEmbed (b i)) =
        2 * p (integralEmbed (b i)) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp_rw [hterm, Finset.prod_mul_distrib]
  simp

/-- The polar volume is at most the explicit basis-box volume. -/
theorem volume_euclideanPolar_unitBall_le_mahlerBox
    {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    volume (euclideanPolar (unitBall p)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ n *
        ∏ i, p (integralEmbed (b i))) := by
  have hmap := Measure.addHaar_image_linearMap volume (dualBasisMap b)
    (euclideanPolar (unitBall p))
  rw [abs_det_dualBasisMap b, ENNReal.ofReal_one, one_mul] at hmap
  rw [← hmap, ← volume_mahlerPolarBox p b]
  exact measure_mono
    (image_euclideanPolar_unitBall_subset_mahlerPolarBox p hp b)

/-- Coarse dimension-only volume-product estimate used by Proposition 8.3.
The zero-dimensional case is included. -/
theorem polar_volume_mul_unitBall_volume_le
    {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    volume (euclideanPolar (unitBall p)) * volume (unitBall p) ≤
      ENNReal.ofReal (((16 : ℝ) * n) ^ n) := by
  by_cases hn : n = 0
  · subst n
    have hpolar : euclideanPolar (unitBall p) = Set.univ := by
      ext z
      simp [euclideanPolar, euclideanPairing]
    have hball : unitBall p = Set.univ := by
      ext z
      have hz : z = 0 := Subsingleton.elim _ _
      subst z
      simp only [Set.mem_univ, iff_true]
      change p 0 ≤ 1
      rw [map_zero]
      norm_num
    rw [hpolar, hball]
    have huniv : (Set.univ : Set (Fin 0 → ℝ)) =
        Set.Icc (0 : Fin 0 → ℝ) 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    rw [huniv, Real.volume_Icc_pi]
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    obtain ⟨b, hb⟩ := exists_isMahlerBasis p hp
    have hpolar := volume_euclideanPolar_unitBall_le_mahlerBox p hp b
    have hbprod : (∏ i, p (integralEmbed (b i))) ≤
        (n : ℝ) ^ n * ∏ i, successiveMinimum p i := by
      calc
        (∏ i, p (integralEmbed (b i))) ≤
            ∏ i, (n : ℝ) * successiveMinimum p i := by
          exact Finset.prod_le_prod
            (fun i _ ↦ apply_nonneg p _)
            (fun i _ ↦ hb.le_rank_mul_successiveMinimum i)
        _ = (n : ℝ) ^ n * ∏ i, successiveMinimum p i := by
          rw [Finset.prod_mul_distrib]
          simp
    have hpolar' : volume (euclideanPolar (unitBall p)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ n * (n : ℝ) ^ n) *
          ENNReal.ofReal (∏ i, successiveMinimum p i) := by
      calc
        volume (euclideanPolar (unitBall p)) ≤
            ENNReal.ofReal ((2 : ℝ) ^ n *
              ∏ i, p (integralEmbed (b i))) := hpolar
        _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n *
              ((n : ℝ) ^ n * ∏ i, successiveMinimum p i)) := by
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left hbprod (by positivity))
        _ = ENNReal.ofReal ((2 : ℝ) ^ n * (n : ℝ) ^ n) *
              ENNReal.ofReal (∏ i, successiveMinimum p i) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
    have hmink := minkowskiSecond_upper_eight_pow_ennreal p hp
    calc
      volume (euclideanPolar (unitBall p)) * volume (unitBall p) ≤
          (ENNReal.ofReal ((2 : ℝ) ^ n * (n : ℝ) ^ n) *
            ENNReal.ofReal (∏ i, successiveMinimum p i)) *
              volume (unitBall p) := by gcongr
      _ = ENNReal.ofReal ((2 : ℝ) ^ n * (n : ℝ) ^ n) *
          (ENNReal.ofReal (∏ i, successiveMinimum p i) *
            volume (unitBall p)) := by ac_rfl
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n * (n : ℝ) ^ n) *
          ENNReal.ofReal ((8 : ℝ) ^ n) := by gcongr
      _ = ENNReal.ofReal (((16 : ℝ) * n) ^ n) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          (2 : ℝ) ^ n * (n : ℝ) ^ n * 8 ^ n =
              (n : ℝ) ^ n * ((2 : ℝ) ^ n * 8 ^ n) := by ring
          _ = (n : ℝ) ^ n * ((2 : ℝ) * 8) ^ n := by rw [mul_pow]
          _ = (n : ℝ) ^ n * (16 : ℝ) ^ n := by norm_num
          _ = ((n : ℝ) * 16) ^ n := by rw [mul_pow]
          _ = ((16 : ℝ) * n) ^ n := by rw [mul_comm]

/-- The form consumed by Proposition 8.3.  Once the current unit-ball
volume is large enough, the coarse volume-product estimate supplies the
source's displayed polar-volume hypothesis. -/
theorem polar_volume_le_four_pow_div
    {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    {epsilon card : ℝ} (hepsilon : 0 < epsilon) (hcard : 0 < card)
    (hbody : 0 < volume.real (unitBall p))
    (hlarge : (((16 : ℝ) * n) ^ n) * epsilon * card ≤
      (4 : ℝ) ^ n * volume.real (unitBall p)) :
    volume (euclideanPolar (unitBall p)) ≤
      ENNReal.ofReal ((4 : ℝ) ^ n / (epsilon * card)) := by
  let polarVolume : ENNReal := volume (euclideanPolar (unitBall p))
  let bodyVolume : ENNReal := volume (unitBall p)
  let C : ℝ := ((16 : ℝ) * n) ^ n
  have hpolarBox := volume_euclideanPolar_unitBall_le_mahlerBox p hp
    (Classical.choose (exists_isMahlerBasis p hp))
  have hpolarTop : polarVolume ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpolarBox
  have hbodyTop : bodyVolume ≠ ∞ :=
    (isBounded_unitBall p hp).measure_lt_top.ne
  have hproduct := polar_volume_mul_unitBall_volume_le p hp
  have hproductReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hproduct
  have hCnonneg : 0 ≤ C := by dsimp only [C]; positivity
  have hreal : polarVolume.toReal * bodyVolume.toReal ≤ C := by
    rw [ENNReal.toReal_mul] at hproductReal
    change polarVolume.toReal * bodyVolume.toReal ≤
      (ENNReal.ofReal C).toReal at hproductReal
    rw [ENNReal.toReal_ofReal hCnonneg] at hproductReal
    exact hproductReal
  have hbodyReal : bodyVolume.toReal = volume.real (unitBall p) := rfl
  have hpole : polarVolume.toReal ≤ C / volume.real (unitBall p) := by
    apply (le_div_iff₀ hbody).2
    simpa only [hbodyReal] using hreal
  have hden : 0 < epsilon * card := mul_pos hepsilon hcard
  have hdiv : C / volume.real (unitBall p) ≤
      (4 : ℝ) ^ n / (epsilon * card) := by
    apply (div_le_div_iff₀ hbody hden).2
    simpa only [C, mul_assoc] using hlarge
  apply (ENNReal.toReal_le_toReal hpolarTop ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (div_nonneg (by positivity) hden.le)]
  exact hpole.trans hdiv

end

end Erdos186.CFP.Bilu.Section8PolarVolumeProduct

#print axioms
  Erdos186.CFP.Bilu.Section8PolarVolumeProduct.polar_volume_mul_unitBall_volume_le

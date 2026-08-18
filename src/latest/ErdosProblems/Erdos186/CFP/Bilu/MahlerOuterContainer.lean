/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MahlerOuterBox
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecondLower

/-!
# The outer Mahler progression in Bilu Section 3

This file turns the determinant estimate in `MahlerOuterBox` into an
actual proper generalized arithmetic progression containing every lattice
point of the seminorm unit ball.  The construction is still canonical in
the selected integral Mahler basis: the radius in direction `i` is the
ceiling of the dimension-only coordinate bound divided by the `i`th
successive minimum.
-/

namespace Erdos186.CFP.Bilu.MahlerOuterContainer

open scoped BigOperators
open Module
open Erdos186.CFP.Bilu.Mahler
open Erdos186.CFP.Bilu.MahlerBox
open Erdos186.CFP.Bilu.MahlerOuterBox
open Erdos186.CFP.Bilu.MinkowskiSecond

/-- The dimension-only constant in the outer-coordinate estimate. -/
noncomputable def outerConstant (n : ℕ) : ℝ :=
  (((8 : ℝ) ^ n * (n.factorial : ℝ)) / (2 : ℝ) ^ n) *
    ∏ j : Fin n, mahlerFactor j

theorem outerConstant_nonneg (n : ℕ) : 0 ≤ outerConstant n := by
  unfold outerConstant
  exact mul_nonneg
    (div_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity))
    (Finset.prod_nonneg fun j _ ↦ (one_le_mahlerFactor j).trans' (by norm_num))

theorem one_le_outerConstant (n : ℕ) : 1 ≤ outerConstant n := by
  have hpow : (2 : ℝ) ^ n ≤ (8 : ℝ) ^ n := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast n.factorial_pos
  have hratio : (1 : ℝ) ≤
      ((8 : ℝ) ^ n * (n.factorial : ℝ)) / (2 : ℝ) ^ n := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).2
    simpa only [one_mul] using
      hpow.trans (le_mul_of_one_le_right (by positivity) hfac)
  have hmahler : (1 : ℝ) ≤ ∏ j : Fin n, mahlerFactor j := by
    exact Finset.one_le_prod (fun j _ ↦ one_le_mahlerFactor j)
  unfold outerConstant
  simpa only [one_mul] using
    mul_le_mul hratio hmahler (by norm_num : (0 : ℝ) ≤ 1)
      ((zero_le_one : (0 : ℝ) ≤ 1).trans hratio)

/-- Integral radius of the outer Mahler box. -/
noncomputable def outerRadius {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n) : ℕ :=
  ⌈outerConstant n * (successiveMinimum p i)⁻¹⌉₊

/-- The outer radii are nonincreasing because the successive minima are
nondecreasing. -/
theorem outerRadius_antitone {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    {i j : Fin n} (hij : i ≤ j) :
    outerRadius p j ≤ outerRadius p i := by
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (outerConstant_nonneg n)
  exact (inv_le_inv₀ (successiveMinimum_pos p hp j)
    (successiveMinimum_pos p hp i)).2
      (MinkowskiSecond.successiveMinimum_mono p hij)

/-- Consequently the displayed widths of the outer progression are sorted
in nonincreasing order. -/
theorem outerGAP_widths_sorted {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) →
      (centeredBasisGAP b (outerRadius p)).widths j ≤
        (centeredBasisGAP b (outerRadius p)).widths i := by
  intro i j hij
  simp only [centeredBasisGAP_widths]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 2
      (outerRadius_antitone p hp (Fin.mk_le_mk.mpr hij))) 1

/-- If the unit ball already contains enough independent lattice points,
so every successive minimum is at most one, each outer width has the
expected reciprocal-minimum bound. -/
theorem outerGAP_width_real_le {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (hmin : ∀ i, successiveMinimum p i ≤ 1) (i : Fin n) :
    ((centeredBasisGAP b (outerRadius p)).widths i : ℝ) ≤
      5 * outerConstant n * (successiveMinimum p i)⁻¹ := by
  let x : ℝ := outerConstant n * (successiveMinimum p i)⁻¹
  have hminPos : 0 < successiveMinimum p i := successiveMinimum_pos p hp i
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg (outerConstant_nonneg n) (inv_nonneg.mpr hminPos.le)
  have hinvone : (1 : ℝ) ≤ (successiveMinimum p i)⁻¹ := by
    rw [one_le_inv₀ hminPos]
    exact hmin i
  have hxone : (1 : ℝ) ≤ x := by
    dsimp only [x]
    simpa only [one_mul] using
      mul_le_mul (one_le_outerConstant n) hinvone (by norm_num : (0 : ℝ) ≤ 1)
        (outerConstant_nonneg n)
  have hceil : ((⌈x⌉₊ : ℕ) : ℝ) ≤ 2 * x := by
    calc
      ((⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0).le
      _ ≤ 2 * x := by linarith
  simp only [centeredBasisGAP_widths, outerRadius]
  push_cast
  dsimp only [x] at hceil ⊢
  nlinarith

/-- Minkowski's lower inequality converts the product of the reciprocal
successive minima into the body's volume.  This is the linear-volume
estimate for the canonical outer progression, in a denominator-free form. -/
theorem outerGAP_volume_mul_simplex_le {n : ℕ} [Nonempty (Fin n)]
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n))
    (hmin : ∀ i, successiveMinimum p i ≤ 1) :
    ((centeredBasisGAP b (outerRadius p)).volume : ENNReal) *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      ENNReal.ofReal ((5 * outerConstant n) ^ n) *
        MeasureTheory.volume {y | p y ≤ 1} := by
  let P : ℝ := ∏ i : Fin n, successiveMinimum p i
  have hminNonneg : ∀ i : Fin n, 0 ≤ successiveMinimum p i :=
    fun i ↦ (successiveMinimum_pos p hp i).le
  have houter :
      ((centeredBasisGAP b (outerRadius p)).volume : ENNReal) ≤
      ∏ i : Fin n,
        ENNReal.ofReal
          (5 * outerConstant n * (successiveMinimum p i)⁻¹) := by
    simp only [GAP.volume]
    push_cast
    apply Finset.prod_le_prod (fun _ _ ↦ bot_le)
    intro i _
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (outerGAP_width_real_le p hp b hmin i)
  have hproduct :
      (∏ i : Fin n,
        ENNReal.ofReal
          (5 * outerConstant n * (successiveMinimum p i)⁻¹)) =
        ENNReal.ofReal ((5 * outerConstant n) ^ n) *
          ENNReal.ofReal P⁻¹ := by
    have hfive : 0 ≤ 5 * outerConstant n :=
      mul_nonneg (by norm_num) (outerConstant_nonneg n)
    simp_rw [ENNReal.ofReal_mul hfive]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin,
      ← ENNReal.ofReal_pow hfive]
    have hprodmin :
        (∏ i : Fin n, ENNReal.ofReal (successiveMinimum p i)⁻¹) =
          ENNReal.ofReal P⁻¹ := by
      rw [← ENNReal.ofReal_prod_of_nonneg
          (fun i _ ↦ inv_nonneg.mpr (hminNonneg i)),
        Finset.prod_inv_distrib (s := Finset.univ)
          (fun i : Fin n ↦ successiveMinimum p i)]
    rw [hprodmin]
  have hlower := minkowskiSecond_lower_volume p hp
  change ENNReal.ofReal P⁻¹ *
      ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
        MeasureTheory.volume {y | p y ≤ 1} at hlower
  rw [hproduct] at houter
  calc
    ((centeredBasisGAP b (outerRadius p)).volume : ENNReal) *
          ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
        (ENNReal.ofReal ((5 * outerConstant n) ^ n) *
          ENNReal.ofReal P⁻¹) *
            ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) := by
      gcongr
    _ = ENNReal.ofReal ((5 * outerConstant n) ^ n) *
        (ENNReal.ofReal P⁻¹ *
          ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ))) := by
      rw [mul_assoc]
    _ ≤ ENNReal.ofReal ((5 * outerConstant n) ^ n) *
        MeasureTheory.volume {y | p y ≤ 1} := by gcongr

/-- The canonical inner Mahler radius is bounded by the outer radius.  Thus
the inner and outer boxes can be chosen in the same integral Mahler basis.
This comparison is the bridge which supplies the reverse, covolume-normalized
volume estimate for the outer container. -/
theorem innerRadius_le_outerRadius {n : ℕ} (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (i : Fin n) :
    innerRadius p i ≤ outerRadius p i := by
  let lambda : ℝ := successiveMinimum p i
  let D : ℝ := (n : ℝ) * upperWeight p i
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hlambda : 0 < lambda := successiveMinimum_pos p hp i
  have hw : 0 < upperWeight p i := upperWeight_pos p hp i
  have hfloor : (innerRadius p i : ℝ) ≤ D⁻¹ := by
    dsimp only [innerRadius, D]
    exact Nat.floor_le (inv_nonneg.mpr (mul_pos hnreal hw).le)
  have hfactor : (1 : ℝ) ≤ (n : ℝ) * mahlerFactor i := by
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hfOne := one_le_mahlerFactor i
    nlinarith [mul_nonneg (sub_nonneg.mpr hnOne) (sub_nonneg.mpr hfOne)]
  have hlambdaD : lambda ≤ D := by
    dsimp only [lambda, D, upperWeight]
    calc
      successiveMinimum p i = 1 * successiveMinimum p i := by ring
      _ ≤ ((n : ℝ) * mahlerFactor i) * successiveMinimum p i :=
        mul_le_mul_of_nonneg_right hfactor hlambda.le
      _ = (n : ℝ) * (mahlerFactor i * successiveMinimum p i) := by ring
  have hD : 0 < D := mul_pos hnreal hw
  have hinv : D⁻¹ ≤ lambda⁻¹ :=
    (inv_le_inv₀ hD hlambda).2 hlambdaD
  have hscale : lambda⁻¹ ≤ outerConstant n * lambda⁻¹ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_outerConstant n) (inv_nonneg.mpr hlambda.le)
  have hceil : outerConstant n * lambda⁻¹ ≤ (outerRadius p i : ℝ) := by
    simpa only [outerRadius, lambda] using
      (Nat.le_ceil (outerConstant n * (successiveMinimum p i)⁻¹))
  exact_mod_cast hfloor.trans (hinv.trans (hscale.trans hceil))

/-- The canonical inner Mahler box is coordinatewise contained in the outer
box, hence its displayed volume is no larger. -/
theorem innerGAP_volume_le_outerGAP_volume {n : ℕ} (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    (centeredBasisGAP b (innerRadius p)).volume ≤
      (centeredBasisGAP b (outerRadius p)).volume := by
  simp only [GAP.volume, centeredBasisGAP_widths]
  apply Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
  intro i _
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (innerRadius_le_outerRadius hn p hp i)) 1

/-- Reverse volume comparison for the outer box.  The standard integral
basis has covolume one, so the same dimension-only Mahler--Minkowski factor
which controls the canonical inner box also controls the body by the outer
box's displayed lattice volume. -/
theorem unitBall_volume_le_constant_mul_outerGAP_volume {n : ℕ}
    (hn : 0 < n) (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    MeasureTheory.volume.real {y | p y ≤ 1} ≤
      (8 : ℝ) ^ n * (n : ℝ) ^ n *
        (∏ i : Fin n, mahlerFactor i) *
          ((centeredBasisGAP b (outerRadius p)).volume : ℝ) := by
  have hinner :=
    unitBall_volume_le_constant_mul_canonicalGAP_volume hn p hp b
  have hvol :
      ((centeredBasisGAP b (innerRadius p)).volume : ℝ) ≤
        ((centeredBasisGAP b (outerRadius p)).volume : ℝ) := by
    exact_mod_cast innerGAP_volume_le_outerGAP_volume hn p hp b
  have hfactor : 0 ≤ (8 : ℝ) ^ n * (n : ℝ) ^ n *
      (∏ i : Fin n, mahlerFactor i) := by
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (Finset.prod_nonneg fun i _ ↦ mahlerFactor_nonneg i)
  exact hinner.trans (mul_le_mul_of_nonneg_left hvol hfactor)

/-- Dilation simply multiplies the radii of a centered basis GAP. -/
theorem dilate_centeredBasisGAP {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (radius : Fin n → ℕ)
    (k : ℕ) :
    (centeredBasisGAP b radius).dilate k =
      centeredBasisGAP b (fun i ↦ k * radius i) := by
  rw [GAP.mk.injEq]
  refine ⟨?_, rfl, ?_⟩
  · funext x
    simp only [GAP.dilate_offset, centeredBasisGAP]
    push_cast
    rw [mul_neg]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  · funext i
    simp [GAP.dilate_widths, centeredBasisGAP_widths, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm]

/-- Every integral dilation of a centered box in a genuine lattice basis
is proper.  This is the `F_s` input required downstream. -/
theorem dilate_centeredBasisGAP_proper {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (radius : Fin n → ℕ)
    (k : ℕ) :
    ((centeredBasisGAP b radius).dilate k).Proper := by
  rw [dilate_centeredBasisGAP]
  exact centeredBasisGAP_proper b (fun i ↦ k * radius i)

/-- Converse to the coefficient extraction lemma for a centered basis GAP. -/
theorem mem_centeredBasisGAP_of_repr_abs_le {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (radius : Fin n → ℕ)
    (z : IntegralPoint n)
    (hz : ∀ i, |b.repr z i| ≤ (radius i : ℤ)) :
    z ∈ (centeredBasisGAP b radius).carrier := by
  classical
  let c : (centeredBasisGAP b radius).Coord := fun i ↦
    ⟨Int.toNat (b.repr z i + (radius i : ℤ)), by
      have hi := hz i
      rw [abs_le] at hi
      simp only [centeredBasisGAP_widths]
      omega⟩
  rw [GAP.mem_carrier_iff]
  refine ⟨c, ?_⟩
  rw [centeredBasisGAP_coordPoint]
  calc
    (∑ i, ((((c i : ℕ) : ℤ) - (radius i : ℤ))) • b i) =
        ∑ i, (b.repr z i) • b i := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      have hi := hz i
      rw [abs_le] at hi
      simp only [c]
      rw [Int.toNat_of_nonneg]
      · ring
      · omega
    _ = z := b.sum_repr z

/-- The determinant estimate bounds every integral Mahler coordinate by
the corresponding integral outer radius. -/
theorem repr_abs_le_outerRadius {n : ℕ}
    (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (hb : IsMahlerBasis p b)
    (z : IntegralPoint n) (hz : p (integralEmbed z) ≤ 1)
    (i : Fin n) :
    |b.repr z i| ≤ (outerRadius p i : ℤ) := by
  have hminPos : 0 < successiveMinimum p i := successiveMinimum_pos p hp i
  have hcoord :=
    basisCoordinate_mul_successiveMinimum_le hn p hp b hb z hz i
  have hdiv : |((b.repr z i : ℤ) : ℝ)| ≤
      outerConstant n * (successiveMinimum p i)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hminPos).2 (by
      simpa only [outerConstant] using hcoord)
  have hceil : outerConstant n * (successiveMinimum p i)⁻¹ ≤
      (outerRadius p i : ℝ) := by
    exact Nat.le_ceil _
  have hreal : |((b.repr z i : ℤ) : ℝ)| ≤
      (outerRadius p i : ℝ) := hdiv.trans hceil
  exact_mod_cast hreal

/-- Every integral point of the unit ball belongs to the canonical outer
Mahler progression. -/
theorem unitBall_integral_subset_outerGAP {n : ℕ}
    (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (hb : IsMahlerBasis p b) :
    ∀ z : IntegralPoint n, p (integralEmbed z) ≤ 1 →
      z ∈ (centeredBasisGAP b (outerRadius p)).carrier := by
  intro z hz
  apply mem_centeredBasisGAP_of_repr_abs_le
  exact repr_abs_le_outerRadius hn p hp b hb z hz

/-- A full independent family in the unit ball bounds every successive
minimum by one.  This is the form in which the thick-range hypothesis is
available in Bilu's affine-span reduction. -/
theorem successiveMinimum_le_one_of_admitsIndependent_full {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (hfull : AdmitsIndependent p n 1) :
    ∀ i : Fin n, successiveMinimum p i ≤ 1 := by
  intro i
  obtain ⟨v, hvIndependent, hv⟩ := hfull
  have hi : i.val + 1 ≤ n := Nat.succ_le_iff.mpr i.isLt
  let e : Fin (i.val + 1) ↪ Fin n := Fin.castLEEmb hi
  apply successiveMinimum_le_of_admits
  refine ⟨fun j ↦ v (e j), ?_, fun j ↦ hv (e j)⟩
  exact hvIndependent.comp e e.injective

/-- Unconditional Section 3 outer progression extracted from Mahler's
basis theorem. -/
theorem exists_proper_outerGAP_containing_unitBall_integralPoints {n : ℕ}
    (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ∃ b : Basis (Fin n) ℤ (IntegralPoint n),
      IsMahlerBasis p b ∧
      (centeredBasisGAP b (outerRadius p)).Proper ∧
      (centeredBasisGAP b (outerRadius p)).Homogeneous ∧
      (∀ k : ℕ, ((centeredBasisGAP b (outerRadius p)).dilate k).Proper) ∧
      (∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) →
        (centeredBasisGAP b (outerRadius p)).widths j ≤
          (centeredBasisGAP b (outerRadius p)).widths i) ∧
      ∀ z : IntegralPoint n, p (integralEmbed z) ≤ 1 →
        z ∈ (centeredBasisGAP b (outerRadius p)).carrier := by
  obtain ⟨b, hb⟩ := exists_isMahlerBasis p hp
  exact ⟨b, hb, centeredBasisGAP_proper b (outerRadius p),
    centeredBasisGAP_homogeneous b (outerRadius p),
    dilate_centeredBasisGAP_proper b (outerRadius p),
    outerGAP_widths_sorted p hp b,
    unitBall_integral_subset_outerGAP hn p hp b hb⟩

/-- Complete Section 3 outer-container package in the full-rank (thick)
range used downstream.  The selected basis has standard-lattice covolume
one; its canonical centered GAP contains every integral point of the unit
ball, remains proper under every coefficient dilation, has nonincreasing
widths and the reciprocal-minimum width bound, and satisfies both directions
of the dimension-only body/GAP volume comparison. -/
theorem exists_proper_outerGAP_containing_unitBall_with_two_sided_volume
    {n : ℕ} (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (hfull : AdmitsIndependent p n 1) :
    ∃ b : Basis (Fin n) ℤ (IntegralPoint n),
      IsMahlerBasis p b ∧
      |(integralBasisMatrix b).det| = 1 ∧
      (centeredBasisGAP b (outerRadius p)).Proper ∧
      (centeredBasisGAP b (outerRadius p)).Homogeneous ∧
      (∀ k : ℕ, ((centeredBasisGAP b (outerRadius p)).dilate k).Proper) ∧
      (∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) →
        (centeredBasisGAP b (outerRadius p)).widths j ≤
          (centeredBasisGAP b (outerRadius p)).widths i) ∧
      (∀ i : Fin n,
        ((centeredBasisGAP b (outerRadius p)).widths i : ℝ) ≤
          5 * outerConstant n * (successiveMinimum p i)⁻¹) ∧
      (∀ z : IntegralPoint n, p (integralEmbed z) ≤ 1 →
        z ∈ (centeredBasisGAP b (outerRadius p)).carrier) ∧
      ((centeredBasisGAP b (outerRadius p)).volume : ENNReal) *
          ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
        ENNReal.ofReal ((5 * outerConstant n) ^ n) *
          MeasureTheory.volume {y | p y ≤ 1} ∧
      MeasureTheory.volume.real {y | p y ≤ 1} ≤
        (8 : ℝ) ^ n * (n : ℝ) ^ n *
          (∏ i : Fin n, mahlerFactor i) *
            ((centeredBasisGAP b (outerRadius p)).volume : ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hmin : ∀ i : Fin n, successiveMinimum p i ≤ 1 :=
    successiveMinimum_le_one_of_admitsIndependent_full p hfull
  obtain ⟨b, hb⟩ := exists_isMahlerBasis p hp
  exact ⟨b, hb, abs_det_integralBasisMatrix b,
    centeredBasisGAP_proper b (outerRadius p),
    centeredBasisGAP_homogeneous b (outerRadius p),
    dilate_centeredBasisGAP_proper b (outerRadius p),
    outerGAP_widths_sorted p hp b,
    outerGAP_width_real_le p hp b hmin,
    unitBall_integral_subset_outerGAP hn p hp b hb,
    outerGAP_volume_mul_simplex_le p hp b hmin,
    unitBall_volume_le_constant_mul_outerGAP_volume hn p hp b⟩

end Erdos186.CFP.Bilu.MahlerOuterContainer

#print axioms Erdos186.CFP.Bilu.MahlerOuterContainer.exists_proper_outerGAP_containing_unitBall_with_two_sided_volume

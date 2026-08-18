/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MahlerTheorem
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecondLower
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecondUpperDirect
import ErdosProblems.Erdos186.GAP

/-!
# The rectangular progression extracted from a Mahler basis

This file is the elementary geometry-to-progression step in Section 3 of
Bilu's proof.  A Mahler basis turns a weighted coordinate box into a subset
of the unit ball of a definite seminorm.  Integral coordinate boxes in the
same basis are packaged as centered, proper GAPs.

The remaining volume estimate for the radii is supplied by Minkowski's
second theorem; none of the inclusion or properness results below assumes
that estimate.
-/

namespace Erdos186.CFP.Bilu.MahlerBox

open scoped BigOperators
open Module
open Erdos186.CFP.Bilu.Mahler
open Erdos186.CFP.Bilu.MinkowskiSecond

/-- The real linear combination in the embedded integral basis `b`. -/
noncomputable def basisCombination {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (a : Fin n → ℝ) :
    Fin n → ℝ :=
  ∑ i, a i • integralEmbed (b i)

/-- Bilu's Mahler upper weight
`c_i λ_i`, where `c_1=1` and `c_i=i/2` thereafter. -/
noncomputable def upperWeight {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n) : ℝ :=
  mahlerFactor i * successiveMinimum p i

/-- The real coefficient box with every weighted coordinate at most `R`. -/
noncomputable def coefficientBox {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (R : ℝ) : Set (Fin n → ℝ) :=
  {a | ∀ i, |a i| * upperWeight p i ≤ R}

@[simp]
theorem mem_coefficientBox {n : ℕ}
    {p : Seminorm ℝ (Fin n → ℝ)} {R : ℝ} {a : Fin n → ℝ} :
    a ∈ coefficientBox p R ↔ ∀ i, |a i| * upperWeight p i ≤ R :=
  Iff.rfl

/-- Equation (3.2), normalized so that the coordinate box lies in the
seminorm unit ball. -/
theorem IsMahlerBasis.basisCombination_mem_unitBall {n : ℕ}
    (hn : 0 < n) {p : Seminorm ℝ (Fin n → ℝ)}
    {b : Basis (Fin n) ℤ (IntegralPoint n)} (hb : IsMahlerBasis p b)
    {a : Fin n → ℝ}
    (ha : a ∈ coefficientBox p ((n : ℝ)⁻¹)) :
    p (basisCombination b a) ≤ 1 := by
  have hsum := hb.seminorm_sum_le a
  change p (basisCombination b a) ≤ 1
  refine hsum.trans ?_
  calc
    (∑ i, |a i| * (mahlerFactor i * successiveMinimum p i)) ≤
        ∑ _i : Fin n, ((n : ℝ)⁻¹) :=
      Finset.sum_le_sum fun i _ ↦ ha i
    _ = (n : ℝ) * (n : ℝ)⁻¹ := by simp
    _ = 1 := by
      exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hn))

/-- Unconditional Mahler-basis extraction of an inner rectangular box. -/
theorem exists_basis_coefficientBox_mapsTo_unitBall {n : ℕ}
    (hn : 0 < n) (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ∃ b : Basis (Fin n) ℤ (IntegralPoint n),
      IsMahlerBasis p b ∧
      ∀ a ∈ coefficientBox p ((n : ℝ)⁻¹),
        p (basisCombination b a) ≤ 1 := by
  obtain ⟨b, hb⟩ := exists_isMahlerBasis p hp
  exact ⟨b, hb, fun _a ha ↦
    IsMahlerBasis.basisCombination_mem_unitBall hn hb ha⟩

/-- The centered integer coefficient box in an integral Mahler basis. -/
noncomputable def centeredBasisGAP {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (radius : Fin n → ℕ) :
    GAP n n where
  offset := fun j ↦ -∑ i, (radius i : ℤ) * b i j
  steps := fun i ↦ b i
  widths := fun i ↦ 2 * radius i + 1
  width_pos := fun _ ↦ Nat.zero_lt_succ _

@[simp]
theorem centeredBasisGAP_widths {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (radius : Fin n → ℕ)
    (i : Fin n) :
    (centeredBasisGAP b radius).widths i = 2 * radius i + 1 := rfl

/-- Evaluation of the centered box is the signed basis combination with
coefficients in `[-radius i, radius i]`. -/
theorem centeredBasisGAP_coordPoint {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (radius : Fin n → ℕ)
    (c : (centeredBasisGAP b radius).Coord) :
    (centeredBasisGAP b radius).coordPoint c =
      ∑ i, (((c i : ℕ) : ℤ) - (radius i : ℤ)) • b i := by
  funext j
  simp only [GAP.coordPoint, centeredBasisGAP, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

/-- A coefficient box in a genuine integral basis is proper. -/
theorem centeredBasisGAP_proper {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (radius : Fin n → ℕ) :
    (centeredBasisGAP b radius).Proper := by
  classical
  intro c d hcd
  rw [centeredBasisGAP_coordPoint, centeredBasisGAP_coordPoint] at hcd
  funext i
  apply Fin.ext
  have hi : ((c i : ℕ) : ℤ) - (radius i : ℤ) =
      ((d i : ℕ) : ℤ) - (radius i : ℤ) := by
    calc
      ((c i : ℕ) : ℤ) - (radius i : ℤ) =
          b.repr (∑ j, (((c j : ℕ) : ℤ) - (radius j : ℤ)) • b j) i :=
        (congrFun (b.repr_sum_self
          (fun j ↦ ((c j : ℕ) : ℤ) - (radius j : ℤ))) i).symm
      _ = b.repr (∑ j, (((d j : ℕ) : ℤ) - (radius j : ℤ)) • b j) i :=
        congrArg (fun z : IntegralPoint n ↦ b.repr z i) hcd
      _ = ((d i : ℕ) : ℤ) - (radius i : ℤ) :=
        congrFun (b.repr_sum_self
          (fun j ↦ ((d j : ℕ) : ℤ) - (radius j : ℤ))) i
  omega

/-- The centered basis box is homogeneous. -/
theorem centeredBasisGAP_homogeneous {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (radius : Fin n → ℕ) :
    (centeredBasisGAP b radius).Homogeneous := by
  refine ⟨fun i ↦ -(radius i : ℤ), ?_⟩
  funext j
  simp [centeredBasisGAP]

/-- Every integral point displayed by the centered basis GAP has signed
basis coefficients bounded by its radii. -/
theorem exists_bounded_coefficients_of_mem_centeredBasisGAP {n : ℕ}
    {b : Basis (Fin n) ℤ (IntegralPoint n)} {radius : Fin n → ℕ}
    {x : IntegralPoint n} (hx : x ∈ (centeredBasisGAP b radius).carrier) :
    ∃ z : Fin n → ℤ,
      (∀ i, |z i| ≤ (radius i : ℤ)) ∧ x = ∑ i, z i • b i := by
  obtain ⟨c, rfl⟩ := GAP.mem_carrier_iff.mp hx
  let z : Fin n → ℤ :=
    fun i ↦ ((c i : ℕ) : ℤ) - (radius i : ℤ)
  refine ⟨z, ?_, centeredBasisGAP_coordPoint b radius c⟩
  intro i
  have hc := (c i).isLt
  simp only [centeredBasisGAP_widths] at hc
  dsimp only [z]
  rw [abs_le]
  constructor <;> omega

/-- If each chosen integral radius satisfies Bilu's weighted `1/n`
bound, the entire proper centered GAP lies in the seminorm unit ball. -/
theorem IsMahlerBasis.centeredBasisGAP_carrier_subset_unitBall {n : ℕ}
    (hn : 0 < n) {p : Seminorm ℝ (Fin n → ℝ)}
    {b : Basis (Fin n) ℤ (IntegralPoint n)} (hb : IsMahlerBasis p b)
    (radius : Fin n → ℕ)
    (hradius : ∀ i,
      (radius i : ℝ) * upperWeight p i ≤ (n : ℝ)⁻¹) :
    ∀ x ∈ (centeredBasisGAP b radius).carrier,
      p (integralEmbed x) ≤ 1 := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := exists_bounded_coefficients_of_mem_centeredBasisGAP hx
  have hcomb :
      integralEmbed (∑ i, z i • b i) =
        basisCombination b (fun i ↦ (z i : ℝ)) := by
    funext j
    simp [basisCombination, integralEmbed]
  rw [hcomb]
  apply IsMahlerBasis.basisCombination_mem_unitBall hn hb
  intro i
  have hzreal : |(z i : ℝ)| ≤ (radius i : ℝ) := by
    exact_mod_cast hz i
  exact (mul_le_mul_of_nonneg_right hzreal
    (mul_nonneg (mahlerFactor_nonneg i) (successiveMinimum_nonneg p i))).trans
      (hradius i)

/-- The fully packaged Section 3 inner progression: a centered proper GAP
in a Mahler basis, contained in the seminorm unit ball whenever its radii
satisfy the explicit weighted bounds. -/
theorem exists_proper_centeredGAP_subset_unitBall {n : ℕ}
    (hn : 0 < n) (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (radius : Fin n → ℕ)
    (hradius : ∀ i,
      (radius i : ℝ) * upperWeight p i ≤ (n : ℝ)⁻¹) :
    ∃ b : Basis (Fin n) ℤ (IntegralPoint n),
      IsMahlerBasis p b ∧
      (centeredBasisGAP b radius).Proper ∧
      (centeredBasisGAP b radius).Homogeneous ∧
      ∀ x ∈ (centeredBasisGAP b radius).carrier,
        p (integralEmbed x) ≤ 1 := by
  obtain ⟨b, hb⟩ := exists_isMahlerBasis p hp
  exact ⟨b, hb, centeredBasisGAP_proper b radius,
    centeredBasisGAP_homogeneous b radius,
    IsMahlerBasis.centeredBasisGAP_carrier_subset_unitBall hn hb radius hradius⟩

/-- Minkowski II turns coordinatewise width estimates into the exact
cross-multiplied volume estimate needed in Section 3.  The hypothesis
`2 r_i + 1 ≤ 3 / λ_i` is the elementary floor estimate for Bilu's
chosen radii; keeping it coordinatewise makes this theorem reusable for
any harmless rounding convention. -/
theorem centeredBasisGAP_volume_mul_minkowskiFactor_le {n : ℕ}
    (hn : 0 < n) (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (radius : Fin n → ℕ)
    (hwidth : ∀ i,
      ((2 * radius i + 1 : ℕ) : ℝ) ≤
        3 * (successiveMinimum p i)⁻¹) :
    ENNReal.ofReal ((centeredBasisGAP b radius).volume : ℝ) *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ n) *
        MeasureTheory.volume {y | p y ≤ 1} := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hprod :
      ((centeredBasisGAP b radius).volume : ℝ) ≤
        (3 : ℝ) ^ n * (∏ i, successiveMinimum p i)⁻¹ := by
    calc
      ((centeredBasisGAP b radius).volume : ℝ) =
          ∏ i : Fin n, (((2 * radius i + 1 : ℕ) : ℝ)) := by
        simp [GAP.volume]
      _ ≤ ∏ i : Fin n, 3 * (successiveMinimum p i)⁻¹ := by
        apply Finset.prod_le_prod (fun i _ ↦ by positivity)
        intro i _
        exact hwidth i
      _ = (3 : ℝ) ^ n * (∏ i, successiveMinimum p i)⁻¹ := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [Finset.prod_inv_distrib]
  have henn :
      ENNReal.ofReal ((centeredBasisGAP b radius).volume : ℝ) ≤
        ENNReal.ofReal ((3 : ℝ) ^ n) *
          ENNReal.ofReal ((∏ i, successiveMinimum p i)⁻¹) := by
    calc
      ENNReal.ofReal ((centeredBasisGAP b radius).volume : ℝ) ≤
          ENNReal.ofReal
            ((3 : ℝ) ^ n * (∏ i, successiveMinimum p i)⁻¹) :=
        ENNReal.ofReal_le_ofReal hprod
      _ = ENNReal.ofReal ((3 : ℝ) ^ n) *
          ENNReal.ofReal ((∏ i, successiveMinimum p i)⁻¹) := by
        rw [ENNReal.ofReal_mul (by positivity)]
  have hminkowski := minkowskiSecond_lower_volume p hp
  calc
    ENNReal.ofReal ((centeredBasisGAP b radius).volume : ℝ) *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
      (ENNReal.ofReal ((3 : ℝ) ^ n) *
          ENNReal.ofReal ((∏ i, successiveMinimum p i)⁻¹)) *
        ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) := by
      gcongr
    _ = ENNReal.ofReal ((3 : ℝ) ^ n) *
        (ENNReal.ofReal ((∏ i, successiveMinimum p i)⁻¹) *
          ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ))) := by
      rw [mul_assoc]
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ n) *
        MeasureTheory.volume {y | p y ≤ 1} := by
      gcongr

/-- Combined Mahler--Minkowski Section 3 extraction.  It produces the
actual proper inner progression and its volume comparison in one theorem,
with only the elementary per-coordinate rounding bounds left to the caller.
-/
theorem exists_proper_centeredGAP_subset_unitBall_with_volume {n : ℕ}
    (hn : 0 < n) (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (radius : Fin n → ℕ)
    (hradius : ∀ i,
      (radius i : ℝ) * upperWeight p i ≤ (n : ℝ)⁻¹)
    (hwidth : ∀ i,
      ((2 * radius i + 1 : ℕ) : ℝ) ≤
        3 * (successiveMinimum p i)⁻¹) :
    ∃ b : Basis (Fin n) ℤ (IntegralPoint n),
      IsMahlerBasis p b ∧
      (centeredBasisGAP b radius).Proper ∧
      (centeredBasisGAP b radius).Homogeneous ∧
      (∀ x ∈ (centeredBasisGAP b radius).carrier,
        p (integralEmbed x) ≤ 1) ∧
      ENNReal.ofReal ((centeredBasisGAP b radius).volume : ℝ) *
          ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
        ENNReal.ofReal ((3 : ℝ) ^ n) *
          MeasureTheory.volume {y | p y ≤ 1} := by
  obtain ⟨b, hb, hproper, hhomogeneous, hsubset⟩ :=
    exists_proper_centeredGAP_subset_unitBall hn p hp radius hradius
  exact ⟨b, hb, hproper, hhomogeneous, hsubset,
    centeredBasisGAP_volume_mul_minkowskiFactor_le hn p hp b radius hwidth⟩

/-! ## Bilu's canonical rounded radii -/

/-- Every Mahler factor is at least one. -/
theorem one_le_mahlerFactor {n : ℕ} (i : Fin n) :
    1 ≤ mahlerFactor i := by
  by_cases hi : i.val = 0
  · rw [mahlerFactor_zero i hi]
  · rw [mahlerFactor_of_pos i (Nat.pos_of_ne_zero hi)]
    have hi2 : (2 : ℝ) ≤ (i.val + 1 : ℕ) := by
      exact_mod_cast (show 2 ≤ i.val + 1 by omega)
    push_cast at hi2
    linarith

theorem upperWeight_pos {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ))
    (hp : IsDefinite p) (i : Fin n) : 0 < upperWeight p i := by
  dsimp only [upperWeight]
  exact mul_pos (zero_lt_one.trans_le (one_le_mahlerFactor i))
    (successiveMinimum_pos p hp i)

/-- Bilu's integral radius, rounded down from
`1 / (n · c_i λ_i)`. -/
noncomputable def innerRadius {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n) : ℕ :=
  ⌊(((n : ℝ) * upperWeight p i)⁻¹)⌋₊

theorem innerRadius_weight_bound {n : ℕ} (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (i : Fin n) :
    (innerRadius p i : ℝ) * upperWeight p i ≤ (n : ℝ)⁻¹ := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : 0 < upperWeight p i := upperWeight_pos p hp i
  have hden : 0 < (n : ℝ) * upperWeight p i := mul_pos hnreal hw
  have hfloor : (innerRadius p i : ℝ) ≤
      (((n : ℝ) * upperWeight p i)⁻¹) := by
    exact Nat.floor_le (inv_nonneg.mpr hden.le)
  calc
    (innerRadius p i : ℝ) * upperWeight p i ≤
        (((n : ℝ) * upperWeight p i)⁻¹) * upperWeight p i :=
      mul_le_mul_of_nonneg_right hfloor hw.le
    _ = (n : ℝ)⁻¹ := by
      field_simp

/-- The canonical odd width also has the lower floor bound needed to
compare the volume of the progression with the volume of the body. -/
theorem innerRadius_width_ge {n : ℕ} (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (i : Fin n) :
    (((n : ℝ) * upperWeight p i)⁻¹) ≤
      ((2 * innerRadius p i + 1 : ℕ) : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : 0 < upperWeight p i := upperWeight_pos p hp i
  have hlt : (((n : ℝ) * upperWeight p i)⁻¹) <
      (innerRadius p i : ℝ) + 1 := by
    simpa only [innerRadius] using
      (Nat.lt_floor_add_one (((n : ℝ) * upperWeight p i)⁻¹))
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  linarith [show (0 : ℝ) ≤ innerRadius p i by positivity]

/-- The upper half of Minkowski's second theorem converts the canonical
Mahler box into a progression occupying a dimension-only fraction of the
unit body's volume.  This is the reverse volume comparison complementary
to `centeredBasisGAP_volume_mul_minkowskiFactor_le`.

The displayed constant is deliberately left as the transparent product
of the `8^n` loss, the `n^n` normalization of the inner box, and Mahler's
factor product. -/
theorem unitBall_volume_le_constant_mul_canonicalGAP_volume {n : ℕ}
    (hn : 0 < n) (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    MeasureTheory.volume.real {y | p y ≤ 1} ≤
      (8 : ℝ) ^ n * (n : ℝ) ^ n * (∏ i : Fin n, mahlerFactor i) *
        ((centeredBasisGAP b (innerRadius p)).volume : ℝ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let N : ℝ := (n : ℝ) ^ n
  let F : ℝ := ∏ i : Fin n, mahlerFactor i
  let Lambda : ℝ := ∏ i : Fin n, successiveMinimum p i
  let G : ℝ := ((centeredBasisGAP b (innerRadius p)).volume : ℝ)
  have hN : 0 < N := by
    dsimp only [N]
    positivity
  have hF : 0 < F := by
    dsimp only [F]
    exact Finset.prod_pos fun i _ ↦
      zero_lt_one.trans_le (one_le_mahlerFactor i)
  have hLambda : 0 < Lambda := by
    dsimp only [Lambda]
    exact Finset.prod_pos fun i _ ↦ successiveMinimum_pos p hp i
  have hbox : (N * F * Lambda)⁻¹ ≤ G := by
    calc
      (N * F * Lambda)⁻¹ =
          ∏ i : Fin n, (((n : ℝ) * upperWeight p i)⁻¹) := by
        simp only [N, F, Lambda, upperWeight, Finset.prod_inv_distrib,
          Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        ring
      _ ≤ ∏ i : Fin n,
          (((2 * innerRadius p i + 1 : ℕ) : ℝ)) := by
        apply Finset.prod_le_prod (fun i _ ↦ inv_nonneg.mpr
          (mul_nonneg (Nat.cast_nonneg n)
            (mul_nonneg (mahlerFactor_nonneg i)
              (successiveMinimum_nonneg p i))))
        intro i _
        exact innerRadius_width_ge hn p hp i
      _ = G := by
        simp [G, GAP.volume]
  have hminkowski :
      Lambda * MeasureTheory.volume.real {y | p y ≤ 1} ≤ (8 : ℝ) ^ n := by
    simpa only [Lambda, MinkowskiUpper.unitBall] using
      minkowskiSecond_upper_eight_pow_real p hp
  have hbody : MeasureTheory.volume.real {y | p y ≤ 1} ≤
      (8 : ℝ) ^ n / Lambda := by
    apply (le_div_iff₀ hLambda).2
    simpa only [mul_comm] using hminkowski
  have hscale : 0 ≤ (8 : ℝ) ^ n * N * F := by positivity
  calc
    MeasureTheory.volume.real {y | p y ≤ 1} ≤
        (8 : ℝ) ^ n / Lambda := hbody
    _ = ((8 : ℝ) ^ n * N * F) * (N * F * Lambda)⁻¹ := by
      field_simp
    _ ≤ ((8 : ℝ) ^ n * N * F) * G :=
      mul_le_mul_of_nonneg_left hbox hscale
    _ = (8 : ℝ) ^ n * (n : ℝ) ^ n *
        (∏ i : Fin n, mahlerFactor i) *
          ((centeredBasisGAP b (innerRadius p)).volume : ℝ) := by
      rfl

/-- In the thick range `λ_i ≤ 1`, the canonical odd width has the
source's convenient upper bound `3 / λ_i`. -/
theorem innerRadius_width_le {n : ℕ} (hn : 0 < n)
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (hthick : ∀ i, successiveMinimum p i ≤ 1) (i : Fin n) :
    (((2 * innerRadius p i + 1 : ℕ) : ℝ)) ≤
      3 * (successiveMinimum p i)⁻¹ := by
  let lambda : ℝ := successiveMinimum p i
  let D : ℝ := (n : ℝ) * upperWeight p i
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hlambda : 0 < lambda := successiveMinimum_pos p hp i
  have hw : 0 < upperWeight p i := upperWeight_pos p hp i
  have hD : 0 < D := mul_pos hnreal hw
  have hfloor : (innerRadius p i : ℝ) ≤ D⁻¹ := by
    dsimp only [innerRadius, D]
    exact Nat.floor_le (inv_nonneg.mpr (mul_pos hnreal hw).le)
  have hnfactor : (1 : ℝ) ≤ (n : ℝ) * mahlerFactor i := by
    have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hf_one := one_le_mahlerFactor i
    nlinarith [mul_nonneg (sub_nonneg.mpr hn_one) (sub_nonneg.mpr hf_one)]
  have hlambdaD : lambda ≤ D := by
    dsimp only [lambda, D, upperWeight]
    calc
      successiveMinimum p i = 1 * successiveMinimum p i := by ring
      _ ≤ ((n : ℝ) * mahlerFactor i) * successiveMinimum p i :=
        mul_le_mul_of_nonneg_right hnfactor hlambda.le
      _ = (n : ℝ) * (mahlerFactor i * successiveMinimum p i) := by ring
  have hDinv : D⁻¹ ≤ lambda⁻¹ :=
    (inv_le_inv₀ hD hlambda).2 hlambdaD
  have hone_inv : (1 : ℝ) ≤ lambda⁻¹ := by
    have := (inv_le_inv₀ (by positivity : (0 : ℝ) < 1) hlambda).2 (hthick i)
    simpa only [inv_one, lambda] using this
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  nlinarith

/-- Fully unconditional Section 3 extraction in the thick range, with
the floor radii and all rounding inequalities discharged. -/
theorem exists_canonical_proper_centeredGAP_subset_unitBall_with_volume
    {n : ℕ} (hn : 0 < n) (p : Seminorm ℝ (Fin n → ℝ))
    (hp : IsDefinite p) (hthick : ∀ i, successiveMinimum p i ≤ 1) :
    ∃ b : Basis (Fin n) ℤ (IntegralPoint n),
      IsMahlerBasis p b ∧
      (centeredBasisGAP b (innerRadius p)).Proper ∧
      (centeredBasisGAP b (innerRadius p)).Homogeneous ∧
      (∀ x ∈ (centeredBasisGAP b (innerRadius p)).carrier,
        p (integralEmbed x) ≤ 1) ∧
      ENNReal.ofReal
          ((centeredBasisGAP b (innerRadius p)).volume : ℝ) *
          ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
        ENNReal.ofReal ((3 : ℝ) ^ n) *
          MeasureTheory.volume {y | p y ≤ 1} := by
  exact exists_proper_centeredGAP_subset_unitBall_with_volume hn p hp
    (innerRadius p) (innerRadius_weight_bound hn p hp)
    (innerRadius_width_le hn p hp hthick)

/-- Fully packaged two-sided volume form of the Section 3 inner
progression.  Both constants depend only on the ambient dimension. -/
theorem exists_canonical_proper_centeredGAP_subset_unitBall_with_two_sided_volume
    {n : ℕ} (hn : 0 < n) (p : Seminorm ℝ (Fin n → ℝ))
    (hp : IsDefinite p) (hthick : ∀ i, successiveMinimum p i ≤ 1) :
    ∃ b : Basis (Fin n) ℤ (IntegralPoint n),
      IsMahlerBasis p b ∧
      (centeredBasisGAP b (innerRadius p)).Proper ∧
      (centeredBasisGAP b (innerRadius p)).Homogeneous ∧
      (∀ x ∈ (centeredBasisGAP b (innerRadius p)).carrier,
        p (integralEmbed x) ≤ 1) ∧
      ENNReal.ofReal
          ((centeredBasisGAP b (innerRadius p)).volume : ℝ) *
          ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) ≤
        ENNReal.ofReal ((3 : ℝ) ^ n) *
          MeasureTheory.volume {y | p y ≤ 1} ∧
      MeasureTheory.volume.real {y | p y ≤ 1} ≤
        (8 : ℝ) ^ n * (n : ℝ) ^ n *
          (∏ i : Fin n, mahlerFactor i) *
            ((centeredBasisGAP b (innerRadius p)).volume : ℝ) := by
  obtain ⟨b, hb, hproper, hhomogeneous, hsubset, hupper⟩ :=
    exists_canonical_proper_centeredGAP_subset_unitBall_with_volume
      hn p hp hthick
  exact ⟨b, hb, hproper, hhomogeneous, hsubset, hupper,
    unitBall_volume_le_constant_mul_canonicalGAP_volume hn p hp b⟩

end Erdos186.CFP.Bilu.MahlerBox

#print axioms Erdos186.CFP.Bilu.MahlerBox.exists_basis_coefficientBox_mapsTo_unitBall
#print axioms Erdos186.CFP.Bilu.MahlerBox.exists_proper_centeredGAP_subset_unitBall
#print axioms Erdos186.CFP.Bilu.MahlerBox.exists_proper_centeredGAP_subset_unitBall_with_volume
#print axioms Erdos186.CFP.Bilu.MahlerBox.exists_canonical_proper_centeredGAP_subset_unitBall_with_volume
#print axioms Erdos186.CFP.Bilu.MahlerBox.unitBall_volume_le_constant_mul_canonicalGAP_volume
#print axioms Erdos186.CFP.Bilu.MahlerBox.exists_canonical_proper_centeredGAP_subset_unitBall_with_two_sided_volume

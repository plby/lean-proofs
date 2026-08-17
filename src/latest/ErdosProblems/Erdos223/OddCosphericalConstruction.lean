/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.LocalSphere
import ErdosProblems.Erdos223.OddCosphericalWitness

/-!
# Odd sharp configurations on a two-sphere

This file formalizes the odd-cardinality construction in the proof of
Swanepoel's spherical diameter lemma.  The construction is kept separate from
the five-dimensional Lenz construction: it is a genuinely three-dimensional
diameter-one set, all of whose points lie on one sphere.
-/

open Metric
open scoped RealInnerProductSpace SimpleGraph

namespace Erdos223
namespace OddCosphericalConstruction

noncomputable section

/-! ## Scalar data -/

private def rad (δ : ℝ) : ℝ := 1 / (2 * Real.cos (δ / 2))
private def ht (δ : ℝ) : ℝ := Real.sqrt (1 - rad δ ^ 2)
private def ctr (δ : ℝ) : ℝ := (1 - 2 * rad δ ^ 2) / (2 * ht δ)
private def sphRad (δ : ℝ) : ℝ := 1 / (2 * ht δ)

private def outer (k : ℕ) (δ : ℝ) : ℝ :=
  rad δ * Real.sin ((k : ℝ) * δ / 2)

private def inner (k : ℕ) (δ : ℝ) : ℝ :=
  rad δ * Real.sin (((k : ℝ) - 2) * δ / 2)

private def qx (δ t : ℝ) : ℝ :=
  -2 * sphRad δ * t * ctr δ / (t ^ 2 + ctr δ ^ 2)

private def qz (δ t : ℝ) : ℝ :=
  ctr δ + sphRad δ * (ctr δ ^ 2 - t ^ 2) / (t ^ 2 + ctr δ ^ 2)

private def qdistSq (k : ℕ) (δ : ℝ) : ℝ :=
  (qx δ (outer k δ) - qx δ (-inner k δ)) ^ 2 +
    (qz δ (outer k δ) - qz δ (-inner k δ)) ^ 2

private def antipodalTest (k : ℕ) (δ : ℝ) : ℝ :=
  outer k δ * inner k δ - ctr δ ^ 2

private lemma pi_pos : 0 < Real.pi := Real.pi_pos

private lemma delta0_pos {k : ℕ} : 0 < Real.pi / ((k : ℝ) + 2) := by
  positivity

private lemma delta0_le_pi_div_five {k : ℕ} (hk : 3 ≤ k) :
    Real.pi / ((k : ℝ) + 2) ≤ Real.pi / 5 := by
  apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by exact_mod_cast Nat.add_le_add_right hk 2)

private lemma cos_delta_pos {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    0 < Real.cos δ := by
  have hpi2 : δ < Real.pi / 2 := by
    have : Real.pi / 5 < Real.pi / 2 := by nlinarith [Real.pi_pos]
    exact hδ.trans_lt this
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hpi2⟩

private lemma cos_half_pos {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    0 < Real.cos (δ / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have := Real.pi_pos
    linarith
  · have : Real.pi / 5 < Real.pi := by nlinarith [Real.pi_pos]
    linarith

private lemma rad_pos {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    0 < rad δ := by
  unfold rad
  positivity [cos_half_pos hδ0 hδ]

private lemma rad_sq_lt_one {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    rad δ ^ 2 < 1 := by
  have hc := cos_half_pos hδ0 hδ
  have hδ2 : δ / 2 ≤ Real.pi / 10 := by linarith
  have hcos : Real.cos (Real.pi / 10) ≤ Real.cos (δ / 2) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · positivity
    · have : Real.pi / 10 ≤ Real.pi := by nlinarith [Real.pi_pos]
      exact this
    · exact hδ2
  have hbound : (1 / 2 : ℝ) < Real.cos (Real.pi / 10) := by
    have h10 : Real.pi / 10 ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> nlinarith [Real.pi_pos]
    have h3 : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> nlinarith [Real.pi_pos]
    have hlt : Real.pi / 10 < Real.pi / 3 := by nlinarith [Real.pi_pos]
    have hc := Real.strictAntiOn_cos h10 h3 hlt
    simpa [Real.cos_pi_div_three] using hc
  have hhalf : (1 / 2 : ℝ) < Real.cos (δ / 2) := hbound.trans_le hcos
  unfold rad
  have hden : 0 < 2 * Real.cos (δ / 2) := by positivity
  rw [one_div_pow]
  apply (div_lt_one (sq_pos_of_pos hden)).2
  nlinarith

private lemma rad_sq_lt_half {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    rad δ ^ 2 < 1 / 2 := by
  have hmem1 : δ / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · linarith
    · have := Real.pi_pos
      linarith
  have hmem2 : Real.pi / 4 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have harg : δ / 2 < Real.pi / 4 := by
    have := Real.pi_pos
    linarith
  have hcos := Real.strictAntiOn_cos hmem1 hmem2 harg
  rw [Real.cos_pi_div_four] at hcos
  have hsqrt : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : 0 < Real.cos (δ / 2) := cos_half_pos hδ0 hδ
  have hcsq : 1 / 2 < Real.cos (δ / 2) ^ 2 := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hne : Real.cos (δ / 2) ≠ 0 := hc.ne'
  unfold rad
  field_simp [hne]
  nlinarith

private lemma ht_pos {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    0 < ht δ := by
  unfold ht
  positivity [rad_sq_lt_one hδ0 hδ]

private lemma ht_sq {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    ht δ ^ 2 = 1 - rad δ ^ 2 := by
  unfold ht
  rw [Real.sq_sqrt]
  exact sub_nonneg.mpr (rad_sq_lt_one hδ0 hδ).le

private lemma rad_sq_add_ht_sq {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    rad δ ^ 2 + ht δ ^ 2 = 1 := by
  rw [ht_sq hδ0 hδ]
  ring

private lemma one_sub_two_rad_sq_pos {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ Real.pi / 5) : 0 < 1 - 2 * rad δ ^ 2 := by
  have hc := cos_delta_pos hδ0 hδ
  have hhalf := cos_half_pos hδ0 hδ
  have hdouble := Real.cos_two_mul (δ / 2)
  have hdouble' : Real.cos δ = 2 * Real.cos (δ / 2) ^ 2 - 1 := by
    convert hdouble using 1 <;> ring
  have hne : 2 * Real.cos (δ / 2) ≠ 0 := by positivity
  unfold rad
  field_simp [hne]
  nlinarith [hdouble']

private lemma ctr_pos {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    0 < ctr δ := by
  unfold ctr
  positivity [one_sub_two_rad_sq_pos hδ0 hδ, ht_pos hδ0 hδ]

private lemma sphRad_pos {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    0 < sphRad δ := by
  unfold sphRad
  positivity [ht_pos hδ0 hδ]

private lemma sphRad_sq_lt_half {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    sphRad δ ^ 2 < 1 / 2 := by
  have hh := ht_pos hδ0 hδ
  have hrh := rad_sq_add_ht_sq hδ0 hδ
  have hr := rad_sq_lt_half hδ0 hδ
  unfold sphRad
  field_simp [hh.ne']
  nlinarith

private lemma ht_sub_ctr {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    ht δ - ctr δ = sphRad δ := by
  have hh := ht_pos hδ0 hδ
  have heq := rad_sq_add_ht_sq hδ0 hδ
  unfold ctr sphRad
  field_simp [hh.ne']
  nlinarith

private lemma rad_sq_add_ctr_sq {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    rad δ ^ 2 + ctr δ ^ 2 = sphRad δ ^ 2 := by
  have hh := ht_pos hδ0 hδ
  have heq := rad_sq_add_ht_sq hδ0 hδ
  unfold ctr sphRad
  field_simp [hh.ne']
  nlinarith [sq_nonneg (1 - 2 * rad δ ^ 2)]

private lemma ctr_add_sphRad {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    ctr δ + sphRad δ = ht δ := by
  linarith [ht_sub_ctr hδ0 hδ]

private lemma ctr_eq_sphRad_mul {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    ctr δ = sphRad δ * (1 - 2 * rad δ ^ 2) := by
  have hh := ht_pos hδ0 hδ
  unfold ctr sphRad
  field_simp [hh.ne']

private lemma qden_pos {δ t : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    0 < t ^ 2 + ctr δ ^ 2 := by
  nlinarith [sq_pos_of_pos (ctr_pos hδ0 hδ), sq_nonneg t]

private lemma q_center_sq {δ t : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    qx δ t ^ 2 + (qz δ t - ctr δ) ^ 2 = sphRad δ ^ 2 := by
  have hd := (qden_pos (t := t) hδ0 hδ).ne'
  unfold qx qz
  field_simp [hd]
  ring

private lemma q_support_line {δ t : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    qx δ t * t - ctr δ * qz δ t = rad δ ^ 2 - 1 / 2 := by
  have hd := (qden_pos (t := t) hδ0 hδ).ne'
  have hs : sphRad δ = ht δ - ctr δ := by linarith [ht_sub_ctr hδ0 hδ]
  have hch : -(ctr δ * ht δ) = rad δ ^ 2 - 1 / 2 := by
    have hh := (ht_pos hδ0 hδ).ne'
    unfold ctr
    field_simp [hh]
    ring
  unfold qx qz
  rw [hs]
  field_simp [hd]
  ring_nf
  nlinarith

private lemma q_support_dist_sq {δ t X Y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5)
    (hbase : X ^ 2 + Y ^ 2 = rad δ ^ 2) :
    (qx δ t - X) ^ 2 + Y ^ 2 + qz δ t ^ 2 - 1 =
      -2 * qx δ t * (X - t) := by
  have hrs := rad_sq_add_ctr_sq hδ0 hδ
  have hq := q_center_sq (t := t) hδ0 hδ
  have hl := q_support_line (t := t) hδ0 hδ
  nlinarith

private lemma pole_q_dist_sq {δ t : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ Real.pi / 5) :
    qx δ t ^ 2 + (qz δ t - ht δ) ^ 2 =
      4 * sphRad δ ^ 2 * t ^ 2 / (t ^ 2 + ctr δ ^ 2) := by
  have hhc := ht_sub_ctr hδ0 hδ
  have hq := q_center_sq (t := t) hδ0 hδ
  have hd := (qden_pos (t := t) hδ0 hδ).ne'
  have hstep :
      qx δ t ^ 2 + (qz δ t - ht δ) ^ 2 =
        2 * sphRad δ ^ 2 - 2 * sphRad δ * (qz δ t - ctr δ) := by
    have hht : ht δ = ctr δ + sphRad δ := by linarith
    rw [hht]
    nlinarith [hq]
  rw [hstep]
  unfold qz
  field_simp [hd]
  ring

/-! ## Scalar intermediate-value argument

The right endpoint is chosen so that the two relevant regular-polygon
coordinates become `rad δ * cos δ` and `rad δ * cos (2 * δ)`.  The first
one is sent by the rational parametrization `q` to `(-rad δ, 0)`.  The
support-line identity above then gives a particularly simple strictly
positive expression for `qdistSq k δ - 1`.
-/

private lemma qdistSq_zero (k : ℕ) : qdistSq k 0 = 0 := by
  simp [qdistSq, outer, inner]

private lemma outer_at_delta0 {k : ℕ} (hk : 3 ≤ k) :
    outer k (Real.pi / ((k : ℝ) + 2)) =
      rad (Real.pi / ((k : ℝ) + 2)) *
        Real.cos (Real.pi / ((k : ℝ) + 2)) := by
  unfold outer
  congr 1
  rw [← Real.sin_pi_div_two_sub]
  congr 1
  have hk' : (k : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hk']
  ring

private lemma inner_at_delta0 {k : ℕ} (hk : 3 ≤ k) :
    inner k (Real.pi / ((k : ℝ) + 2)) =
      rad (Real.pi / ((k : ℝ) + 2)) *
        Real.cos (2 * (Real.pi / ((k : ℝ) + 2))) := by
  unfold inner
  congr 1
  rw [← Real.sin_pi_div_two_sub]
  congr 1
  have hk' : (k : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hk']
  ring

private lemma outer_eq_ht_mul_ctr_div_rad {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    rad δ * Real.cos δ = ht δ * ctr δ / rad δ := by
  have hr := (rad_pos hδ0 hδ).ne'
  have hh := (ht_pos hδ0 hδ).ne'
  have hdouble := Real.cos_two_mul (δ / 2)
  have hdouble' : Real.cos δ = 2 * Real.cos (δ / 2) ^ 2 - 1 := by
    convert hdouble using 1 <;> ring
  unfold ctr rad
  field_simp [hr, hh, cos_half_pos hδ0 hδ |>.ne']
  nlinarith [hdouble']

private lemma q_at_outer_endpoint {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) :
    qx δ (rad δ * Real.cos δ) = -rad δ ∧
      qz δ (rad δ * Real.cos δ) = 0 := by
  have hr := (rad_pos hδ0 hδ).ne'
  have hh := (ht_pos hδ0 hδ).ne'
  have hc := (ctr_pos hδ0 hδ).ne'
  have hs := (sphRad_pos hδ0 hδ).ne'
  have hout := outer_eq_ht_mul_ctr_div_rad hδ0 hδ
  have hrs := rad_sq_add_ctr_sq hδ0 hδ
  have hsc := ctr_eq_sphRad_mul hδ0 hδ
  have hhc := ht_sub_ctr hδ0 hδ
  have hrh := rad_sq_add_ht_sq hδ0 hδ
  have hRh : 2 * sphRad δ * ht δ = 1 := by
    unfold sphRad
    field_simp [hh]
  have hd := (qden_pos (t := ht δ * ctr δ / rad δ) hδ0 hδ).ne'
  have hdeneq :
      (ht δ * ctr δ / rad δ) ^ 2 + ctr δ ^ 2 = ctr δ ^ 2 / rad δ ^ 2 := by
    field_simp [hr]
    nlinarith [hrh, sq_nonneg (rad δ), sq_nonneg (ht δ), sq_nonneg (ctr δ)]
  constructor
  · rw [hout]
    unfold qx
    rw [hdeneq]
    field_simp [hr, hc]
    nlinarith
  · rw [hout]
    unfold qz
    rw [hdeneq]
    field_simp [hr, hc]
    rw [hsc]
    linear_combination -sphRad δ * hrh

private lemma two_delta0_mem {k : ℕ} (hk : 3 ≤ k) :
    2 * (Real.pi / ((k : ℝ) + 2)) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hδpos : 0 < Real.pi / ((k : ℝ) + 2) := delta0_pos
  have hδle : Real.pi / ((k : ℝ) + 2) ≤ Real.pi / 5 :=
    delta0_le_pi_div_five hk
  constructor
  · positivity
  · nlinarith [Real.pi_pos]

private lemma inner_endpoint_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < inner k (Real.pi / ((k : ℝ) + 2)) := by
  rw [inner_at_delta0 hk]
  have hδle := delta0_le_pi_div_five hk
  have hδpos : 0 < Real.pi / ((k : ℝ) + 2) := delta0_pos
  have htwo := two_delta0_mem hk
  have hcos : 0 < Real.cos (2 * (Real.pi / ((k : ℝ) + 2))) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [htwo.1, Real.pi_pos], htwo.2⟩
  positivity [rad_pos hδpos.le hδle]

private lemma inner_endpoint_lt_rad {k : ℕ} (hk : 3 ≤ k) :
    inner k (Real.pi / ((k : ℝ) + 2)) <
      rad (Real.pi / ((k : ℝ) + 2)) := by
  rw [inner_at_delta0 hk]
  have hδle := delta0_le_pi_div_five hk
  have hδpos : 0 < Real.pi / ((k : ℝ) + 2) := delta0_pos
  have htwo := two_delta0_mem hk
  have hcoslt : Real.cos (2 * (Real.pi / ((k : ℝ) + 2))) < 1 := by
    have hanti := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := 2 * (Real.pi / ((k : ℝ) + 2)))
      (by norm_num) (by linarith [htwo.2, Real.pi_pos]) htwo.1
    simpa using hanti
  nlinarith [rad_pos hδpos.le hδle]

private lemma qx_neg_inner_endpoint_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < qx (Real.pi / ((k : ℝ) + 2))
      (-inner k (Real.pi / ((k : ℝ) + 2))) := by
  have hδpos : 0 < Real.pi / ((k : ℝ) + 2) := delta0_pos
  have hδle := delta0_le_pi_div_five hk
  have hi := inner_endpoint_pos hk
  have hs := sphRad_pos hδpos.le hδle
  have hc := ctr_pos hδpos.le hδle
  have hd := qden_pos (t := -inner k (Real.pi / ((k : ℝ) + 2))) hδpos.le hδle
  unfold qx
  apply div_pos
  · ring_nf at hs hi hc ⊢
    positivity
  · exact hd

private lemma qdistSq_endpoint_sub_one {k : ℕ} (hk : 3 ≤ k) :
    qdistSq k (Real.pi / ((k : ℝ) + 2)) - 1 =
      2 * qx (Real.pi / ((k : ℝ) + 2))
          (-inner k (Real.pi / ((k : ℝ) + 2))) *
        (rad (Real.pi / ((k : ℝ) + 2)) -
          inner k (Real.pi / ((k : ℝ) + 2))) := by
  let δ : ℝ := Real.pi / ((k : ℝ) + 2)
  have hδpos : 0 < δ := delta0_pos
  have hδle : δ ≤ Real.pi / 5 := delta0_le_pi_div_five hk
  have hq := q_at_outer_endpoint hδpos.le hδle
  have hbase :
      inner k δ ^ 2 + (rad δ * Real.sin (2 * δ)) ^ 2 = rad δ ^ 2 := by
    rw [inner_at_delta0 hk]
    calc
      (rad δ * Real.cos (2 * δ)) ^ 2 +
          (rad δ * Real.sin (2 * δ)) ^ 2 =
          rad δ ^ 2 * (Real.cos (2 * δ) ^ 2 + Real.sin (2 * δ) ^ 2) := by ring
      _ = rad δ ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hsupp := q_support_dist_sq
    (δ := δ) (t := -inner k δ) (X := inner k δ)
    (Y := rad δ * Real.sin (2 * δ)) hδpos.le hδle hbase
  change qdistSq k δ - 1 = _
  unfold qdistSq
  rw [outer_at_delta0 hk, hq.1, hq.2]
  nlinarith

private lemma one_lt_qdistSq_endpoint {k : ℕ} (hk : 3 ≤ k) :
    1 < qdistSq k (Real.pi / ((k : ℝ) + 2)) := by
  rw [← sub_pos]
  rw [qdistSq_endpoint_sub_one hk]
  exact mul_pos (mul_pos (by norm_num) (qx_neg_inner_endpoint_pos hk))
    (sub_pos.mpr (inner_endpoint_lt_rad hk))

private lemma continuousOn_qdistSq (k : ℕ) :
    ContinuousOn (qdistSq k) (Set.Icc (0 : ℝ) (Real.pi / 5)) := by
  intro δ hδ
  have hcos := cos_half_pos hδ.1 hδ.2
  have hht := ht_pos hδ.1 hδ.2
  have hctr := ctr_pos hδ.1 hδ.2
  have hrad : ContinuousWithinAt rad (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by
    unfold rad
    have hden : ContinuousWithinAt (fun x : ℝ => 2 * Real.cos (x / 2))
        (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by fun_prop
    exact continuousWithinAt_const.div hden (by positivity)
  have hhtc : ContinuousWithinAt ht (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by
    unfold ht
    fun_prop
  have hctrc : ContinuousWithinAt ctr (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by
    unfold ctr
    exact (continuousWithinAt_const.sub (continuousWithinAt_const.mul (hrad.pow 2))).div
      (continuousWithinAt_const.mul hhtc) (by positivity)
  have hsph : ContinuousWithinAt sphRad (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by
    unfold sphRad
    exact continuousWithinAt_const.div (continuousWithinAt_const.mul hhtc) (by positivity)
  have hout : ContinuousWithinAt (outer k) (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by
    unfold outer
    fun_prop
  have hinn : ContinuousWithinAt (inner k) (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by
    unfold inner
    fun_prop
  have hdo := qden_pos (t := outer k δ) hδ.1 hδ.2
  have hdi := qden_pos (t := -inner k δ) hδ.1 hδ.2
  have hqxo : ContinuousWithinAt (fun x => qx x (outer k x))
      (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by
    unfold qx
    exact (((continuousWithinAt_const.mul hsph).mul hout).mul hctrc).div
      ((hout.pow 2).add (hctrc.pow 2)) hdo.ne'
  have hqxi : ContinuousWithinAt (fun x => qx x (-inner k x))
      (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by
    unfold qx
    have hneg : ContinuousWithinAt (fun x => -inner k x)
        (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := hinn.neg
    exact (((continuousWithinAt_const.mul hsph).mul hneg).mul hctrc).div
      ((hneg.pow 2).add (hctrc.pow 2)) hdi.ne'
  have hqzo : ContinuousWithinAt (fun x => qz x (outer k x))
      (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by
    unfold qz
    exact hctrc.add ((hsph.mul ((hctrc.pow 2).sub (hout.pow 2))).div
      ((hout.pow 2).add (hctrc.pow 2)) hdo.ne')
  have hqzi : ContinuousWithinAt (fun x => qz x (-inner k x))
      (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := by
    unfold qz
    have hneg : ContinuousWithinAt (fun x => -inner k x)
        (Set.Icc (0 : ℝ) (Real.pi / 5)) δ := hinn.neg
    exact hctrc.add ((hsph.mul ((hctrc.pow 2).sub (hneg.pow 2))).div
      ((hneg.pow 2).add (hctrc.pow 2)) hdi.ne')
  unfold qdistSq
  fun_prop

/-- The scalar parameter needed for the odd cospherical construction. -/
theorem exists_delta_qdistSq_eq_one (k : ℕ) (hk : 3 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / ((k : ℝ) + 2) ∧ qdistSq k δ = 1 := by
  let δ₀ : ℝ := Real.pi / ((k : ℝ) + 2)
  have hδ₀pos : 0 < δ₀ := delta0_pos
  have hδ₀le : δ₀ ≤ Real.pi / 5 := delta0_le_pi_div_five hk
  have hcont : ContinuousOn (qdistSq k) (Set.Icc (0 : ℝ) δ₀) :=
    (continuousOn_qdistSq k).mono (Set.Icc_subset_Icc_right hδ₀le)
  have hone : (1 : ℝ) ∈ Set.Icc (qdistSq k 0) (qdistSq k δ₀) := by
    constructor
    · rw [qdistSq_zero]
      norm_num
    · exact (one_lt_qdistSq_endpoint hk).le
  obtain ⟨δ, hδmem, hδeq⟩ := intermediate_value_Icc hδ₀pos.le hcont hone
  have hδne0 : δ ≠ 0 := by
    intro h
    subst δ
    rw [qdistSq_zero] at hδeq
    norm_num at hδeq
  have hδneδ₀ : δ ≠ δ₀ := by
    intro h
    subst δ
    exact (one_lt_qdistSq_endpoint hk).ne hδeq.symm
  exact ⟨δ, lt_of_le_of_ne hδmem.1 (Ne.symm hδne0),
    lt_of_le_of_ne hδmem.2 hδneδ₀, hδeq⟩

theorem exists_delta_qdistSq_eq_one_le_pi_div_five (k : ℕ) (hk : 3 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Real.pi / ((k : ℝ) + 2) ∧
      δ ≤ Real.pi / 5 ∧ qdistSq k δ = 1 := by
  obtain ⟨δ, hδpos, hδlt, hδeq⟩ := exists_delta_qdistSq_eq_one k hk
  exact ⟨δ, hδpos, hδlt, hδlt.le.trans (delta0_le_pi_div_five hk), hδeq⟩

/-! ## The alternating base chain -/

def point3 (x y z : ℝ) : Point 3 :=
  EuclideanSpace.single (0 : Fin 3) x +
    EuclideanSpace.single (1 : Fin 3) y +
      EuclideanSpace.single (2 : Fin 3) z

def rawAngle (k : ℕ) (δ : ℝ) (i : ℕ) : ℝ :=
  ((k : ℝ) - 2 * (i : ℝ)) * δ / 2

def sign (i : ℕ) : ℝ := (-1 : ℝ) ^ i

def basePoint (k : ℕ) (δ : ℝ) (i : Fin (k + 1)) : Point 3 :=
  point3
    (sign i * rad δ * Real.sin (rawAngle k δ i))
    (sign i * rad δ * Real.cos (rawAngle k δ i)) 0

lemma point3_apply_zero (x y z : ℝ) : point3 x y z 0 = x := by
  simp [point3]

lemma inner_point3 (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) :
    ⟪point3 x₁ y₁ z₁, point3 x₂ y₂ z₂⟫ =
      x₁ * x₂ + y₁ * y₂ + z₁ * z₂ := by
  simp [point3, inner_add_left, inner_add_right, EuclideanSpace.inner_single_left]

lemma dist_point3_sq (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) :
    dist (point3 x₁ y₁ z₁) (point3 x₂ y₂ z₂) ^ 2 =
      (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 + (z₁ - z₂) ^ 2 := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [inner_point3, inner_point3, inner_point3, inner_point3]
  ring

lemma sign_sq (i : ℕ) : sign i ^ 2 = 1 := by
  unfold sign
  rw [← pow_mul]
  norm_num

lemma sign_mul_eq_sign_sub {i j : ℕ} (hij : i ≤ j) :
    sign i * sign j = sign (j - i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hij
  simp only [Nat.add_sub_cancel_left]
  rw [show sign (i + m) = sign i * sign m by simp [sign, pow_add]]
  calc
    sign i * (sign i * sign m) = sign i ^ 2 * sign m := by ring
    _ = sign m := by rw [sign_sq]; ring

lemma dist_basePoint_sq (k : ℕ) (δ : ℝ) (i j : Fin (k + 1)) :
    dist (basePoint k δ i) (basePoint k δ j) ^ 2 =
      2 * rad δ ^ 2 *
        (1 - sign i * sign j * Real.cos (rawAngle k δ i - rawAngle k δ j)) := by
  rw [basePoint, basePoint, dist_point3_sq]
  rw [Real.cos_sub]
  have hi := Real.sin_sq_add_cos_sq (rawAngle k δ i)
  have hj := Real.sin_sq_add_cos_sq (rawAngle k δ j)
  have hsi := sign_sq i
  have hsj := sign_sq j
  ring_nf
  rw [hsi, hsj]
  nlinarith [hi, hj]

lemma dist_basePoint_sq_of_le (k : ℕ) (δ : ℝ) (i j : Fin (k + 1))
    (hij : (i : ℕ) ≤ j) :
    dist (basePoint k δ i) (basePoint k δ j) ^ 2 =
      2 * rad δ ^ 2 *
        (1 - sign ((j : ℕ) - i) * Real.cos ((((j : ℕ) - i : ℕ) : ℝ) * δ)) := by
  rw [dist_basePoint_sq, sign_mul_eq_sign_sub hij]
  congr 3
  congr 1
  unfold rawAngle
  have hsub : (((j.val - i.val : ℕ) : ℝ)) = (j.val : ℝ) - (i.val : ℝ) := by
    exact Nat.cast_sub hij
  rw [hsub]
  ring

lemma delta_mul_add_lt_pi {k : ℕ} {δ : ℝ}
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    δ * ((k : ℝ) + 2) < Real.pi := by
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  exact (lt_div_iff₀ hk2).mp hδ

lemma k_mul_delta_lt_pi {k : ℕ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    (k : ℝ) * δ < Real.pi := by
  have h := delta_mul_add_lt_pi hδ
  nlinarith

lemma delta_lt_pi_div_five {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) : δ < Real.pi / 5 := by
  by_cases hδnonpos : δ ≤ 0
  · nlinarith [Real.pi_pos]
  have h := delta_mul_add_lt_pi hδ
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have h5 : (5 : ℝ) ≤ (k : ℝ) + 2 := by linarith
  have hδpos : 0 < δ := lt_of_not_ge hδnonpos
  have hmul := mul_le_mul_of_nonneg_left h5 hδpos.le
  nlinarith

lemma base_cos_half_pos {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) : 0 < Real.cos (δ / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos]
  · have hd5 := delta_lt_pi_div_five hk hδ
    nlinarith [Real.pi_pos]

lemma base_rad_pos {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) : 0 < rad δ := by
  unfold rad
  positivity [base_cos_half_pos hk hδ0 hδ]

lemma diameter_identity {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    2 * rad δ ^ 2 * (1 + Real.cos δ) = 1 := by
  have hc := base_cos_half_pos hk hδ0 hδ
  have htwo := Real.cos_two_mul (δ / 2)
  have hcos : Real.cos δ = 2 * Real.cos (δ / 2) ^ 2 - 1 := by
    convert htwo using 1 <;> ring
  unfold rad
  field_simp [hc.ne']
  nlinarith

lemma rawAngle_mem {k : ℕ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) (i : Fin (k + 1)) :
    rawAngle k δ i ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hiN : (i : ℕ) ≤ k := by omega
  have hiR : (i : ℝ) ≤ k := by exact_mod_cast hiN
  have hkpi := k_mul_delta_lt_pi hδ0 hδ
  unfold rawAngle
  constructor <;> nlinarith

lemma neg_rawAngle_mem {k : ℕ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) (i : Fin (k + 1)) :
    -rawAngle k δ i ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have h := rawAngle_mem hδ0 hδ i
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

lemma outer_angle_mem {k : ℕ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    (k : ℝ) * δ / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hkpi := k_mul_delta_lt_pi hδ0 hδ
  constructor <;> nlinarith [Real.pi_pos]

lemma inner_neg_angle_mem {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    -(((k : ℝ) - 2) * δ / 2) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpi := k_mul_delta_lt_pi hδ0 hδ
  constructor <;> nlinarith [Real.pi_pos]

lemma basePoint_x_le_outer {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) (i : Fin (k + 1)) :
    basePoint k δ i 0 ≤ outer k δ := by
  have hr := (base_rad_pos hk hδ0 hδ).le
  have hiRaw := rawAngle_mem hδ0 hδ i
  have hiNeg := neg_rawAngle_mem hδ0 hδ i
  have hkAng := outer_angle_mem hδ0 hδ
  rcases Nat.even_or_odd (i : ℕ) with hi | hi
  · have hs : sign i = 1 := hi.neg_one_pow
    have hangle : rawAngle k δ i ≤ (k : ℝ) * δ / 2 := by
      have hiR : (0 : ℝ) ≤ (i : ℕ) := by positivity
      unfold rawAngle
      nlinarith
    have hsin := Real.strictMonoOn_sin.monotoneOn hiRaw hkAng hangle
    simpa [basePoint, point3, outer, hs] using mul_le_mul_of_nonneg_left hsin hr
  · have hs : sign i = -1 := hi.neg_one_pow
    have hangle : -rawAngle k δ i ≤ (k : ℝ) * δ / 2 := by
      have hiN : (i : ℕ) ≤ k := by omega
      have hiR : (i : ℝ) ≤ k := by exact_mod_cast hiN
      unfold rawAngle
      nlinarith
    have hsin := Real.strictMonoOn_sin.monotoneOn hiNeg hkAng hangle
    have hmul := mul_le_mul_of_nonneg_left hsin hr
    simpa [basePoint, point3_apply_zero, outer, hs, mul_neg] using hmul

lemma neg_inner_le_basePoint_x {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) (i : Fin (k + 1)) :
    -inner k δ ≤ basePoint k δ i 0 := by
  have hr := (base_rad_pos hk hδ0 hδ).le
  have hiRaw := rawAngle_mem hδ0 hδ i
  have hiNeg := neg_rawAngle_mem hδ0 hδ i
  have hinner := inner_neg_angle_mem hk hδ0 hδ
  rcases Nat.even_or_odd (i : ℕ) with hi | hi
  · have hs : sign i = 1 := hi.neg_one_pow
    obtain ⟨a, ha⟩ := hi
    obtain ⟨b, hb⟩ := hkodd
    have hiN : (i : ℕ) ≤ k := by omega
    have hik : (i : ℕ) < k := by omega
    have hikR : (i : ℝ) < k := by exact_mod_cast hik
    have hik1 : (i : ℕ) + 1 ≤ k := by omega
    have hik1R : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik1
    have hangle : -(((k : ℝ) - 2) * δ / 2) ≤ rawAngle k δ i := by
      have hcoef : -((k : ℝ) - 2) ≤ (k : ℝ) - 2 * (i : ℝ) := by
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right hcoef hδ0.le
      unfold rawAngle
      nlinarith
    have hsin := Real.strictMonoOn_sin.monotoneOn hinner hiRaw hangle
    have hmul := mul_le_mul_of_nonneg_left hsin hr
    simpa [basePoint, point3_apply_zero, inner, hs, mul_neg] using hmul
  · have hs : sign i = -1 := hi.neg_one_pow
    obtain ⟨a, ha⟩ := hi
    have hiN : 1 ≤ (i : ℕ) := by omega
    have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hiN
    have hangle : -(((k : ℝ) - 2) * δ / 2) ≤ -rawAngle k δ i := by
      unfold rawAngle
      nlinarith
    have hsin := Real.strictMonoOn_sin.monotoneOn hinner hiNeg hangle
    have hmul := mul_le_mul_of_nonneg_left hsin hr
    simpa [basePoint, point3_apply_zero, inner, hs, mul_neg] using hmul

lemma basePoint_coordinate_strip {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) (i : Fin (k + 1)) :
    -inner k δ ≤ basePoint k δ i 0 ∧ basePoint k δ i 0 ≤ outer k δ :=
  ⟨neg_inner_le_basePoint_x hk hkodd hδ0 hδ i,
    basePoint_x_le_outer hk hδ0 hδ i⟩

lemma signed_cos_factor_le {k m : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) (hm : m ≤ k) :
    1 - sign m * Real.cos ((m : ℝ) * δ) ≤ 1 + Real.cos δ := by
  have hkpi := k_mul_delta_lt_pi hδ0 hδ
  have hmR : (m : ℝ) ≤ k := by exact_mod_cast hm
  have hm_nonneg : 0 ≤ (m : ℝ) * δ := mul_nonneg (by positivity) hδ0.le
  have hm_lt_pi : (m : ℝ) * δ < Real.pi := by
    have hmk := mul_le_mul_of_nonneg_right hmR hδ0.le
    nlinarith
  rcases Nat.even_or_odd m with he | ho
  · have hs : sign m = 1 := he.neg_one_pow
    obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := hkodd
    have hmk : m < k := by omega
    have hmk1 : m + 1 ≤ k := by omega
    have hmk1R : (m : ℝ) + 1 ≤ k := by exact_mod_cast hmk1
    have hprod := mul_le_mul_of_nonneg_right hmk1R hδ0.le
    have hm_le : (m : ℝ) * δ ≤ Real.pi - δ := by
      nlinarith
    have hpi_sub : Real.pi - δ ≤ Real.pi := by linarith
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hm_nonneg hpi_sub hm_le
    rw [Real.cos_pi_sub] at hc
    rw [hs, one_mul]
    nlinarith
  · have hs : sign m = -1 := ho.neg_one_pow
    obtain ⟨a, ha⟩ := ho
    have hm1 : 1 ≤ m := by omega
    have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hdel_le : δ ≤ (m : ℝ) * δ := by
      have := mul_le_mul_of_nonneg_right hm1R hδ0.le
      nlinarith
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hδ0.le hm_lt_pi.le hdel_le
    rw [hs, neg_one_mul]
    nlinarith

lemma dist_basePoint_le_one_of_le {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hkodd : Odd k) (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2))
    (i j : Fin (k + 1)) (hij : (i : ℕ) ≤ j) :
    dist (basePoint k δ i) (basePoint k δ j) ≤ 1 := by
  have hm : (j : ℕ) - i ≤ k := by omega
  have hf := signed_cos_factor_le hk hkodd hδ0 hδ hm
  have hcoef : 0 ≤ 2 * rad δ ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hf hcoef
  have hsq := dist_basePoint_sq_of_le k δ i j hij
  have hid := diameter_identity hk hδ0 hδ
  rw [hid] at hmul
  have hsqle : dist (basePoint k δ i) (basePoint k δ j) ^ 2 ≤ 1 := by
    rw [hsq]
    exact hmul
  nlinarith [dist_nonneg (x := basePoint k δ i) (y := basePoint k δ j)]

lemma dist_basePoint_le_one {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2))
    (i j : Fin (k + 1)) : dist (basePoint k δ i) (basePoint k δ j) ≤ 1 := by
  rcases le_total (i : ℕ) (j : ℕ) with hij | hji
  · exact dist_basePoint_le_one_of_le hk hkodd hδ0 hδ i j hij
  · rw [dist_comm]
    exact dist_basePoint_le_one_of_le hk hkodd hδ0 hδ j i hji

lemma dist_basePoint_consecutive {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) (i : Fin k) :
    dist (basePoint k δ i.castSucc) (basePoint k δ i.succ) = 1 := by
  have hij : ((i.castSucc : Fin (k + 1)) : ℕ) ≤ (i.succ : Fin (k + 1)) := by simp
  have hsq := dist_basePoint_sq_of_le k δ i.castSucc i.succ hij
  have hsq' :
      dist (basePoint k δ i.castSucc) (basePoint k δ i.succ) ^ 2 =
        2 * rad δ ^ 2 * (1 + Real.cos δ) := by
    simpa [sign] using hsq
  rw [diameter_identity hk hδ0 hδ] at hsq'
  nlinarith [dist_nonneg
    (x := basePoint k δ i.castSucc) (y := basePoint k δ i.succ)]

lemma signed_cos_factor_pos {k m : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2))
    (hm0 : 0 < m) (hm : m ≤ k) :
    0 < 1 - sign m * Real.cos ((m : ℝ) * δ) := by
  have hkpi := k_mul_delta_lt_pi hδ0 hδ
  have hmR : (m : ℝ) ≤ k := by exact_mod_cast hm
  have hm0R : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmδ0 : 0 < (m : ℝ) * δ := mul_pos hm0R hδ0
  have hmk := mul_le_mul_of_nonneg_right hmR hδ0.le
  have hmδpi : (m : ℝ) * δ < Real.pi := by nlinarith
  rcases Nat.even_or_odd m with he | ho
  · have hs : sign m = 1 := he.neg_one_pow
    have hc := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
      (show (m : ℝ) * δ ∈ Set.Icc 0 Real.pi by exact ⟨hmδ0.le, hmδpi.le⟩)
      hmδ0
    simp only [Real.cos_zero] at hc
    rw [hs, one_mul]
    linarith
  · have hs : sign m = -1 := ho.neg_one_pow
    have hc := Real.strictAntiOn_cos
      (show (m : ℝ) * δ ∈ Set.Icc 0 Real.pi by exact ⟨hmδ0.le, hmδpi.le⟩)
      (show Real.pi ∈ Set.Icc (0 : ℝ) Real.pi by exact ⟨Real.pi_pos.le, le_rfl⟩)
      hmδpi
    rw [Real.cos_pi] at hc
    rw [hs, neg_one_mul]
    linarith

lemma basePoint_ne_of_lt {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2))
    (i j : Fin (k + 1)) (hij : (i : ℕ) < j) :
    basePoint k δ i ≠ basePoint k δ j := by
  have hle : (i : ℕ) ≤ j := hij.le
  have hm0 : 0 < (j : ℕ) - i := Nat.sub_pos_of_lt hij
  have hm : (j : ℕ) - i ≤ k := by omega
  have hf := signed_cos_factor_pos hk hkodd hδ0 hδ hm0 hm
  have hr := base_rad_pos hk hδ0 hδ
  have hsq := dist_basePoint_sq_of_le k δ i j hle
  have hdistpos : 0 < dist (basePoint k δ i) (basePoint k δ j) ^ 2 := by
    rw [hsq]
    positivity
  intro heq
  rw [heq, dist_self] at hdistpos
  norm_num at hdistpos

lemma basePoint_injective {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    Function.Injective (basePoint k δ) := by
  intro i j hij
  apply Fin.ext
  by_contra hval
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact (basePoint_ne_of_lt hk hkodd hδ0 hδ i j hlt) hij
  · exact (basePoint_ne_of_lt hk hkodd hδ0 hδ j i hgt) hij.symm

def baseConfiguration (k : ℕ) (δ : ℝ) : Finset (Point 3) :=
  Finset.univ.image (basePoint k δ)

lemma card_baseConfiguration {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    (baseConfiguration k δ).card = k + 1 := by
  rw [baseConfiguration, Finset.card_image_iff.mpr
    (basePoint_injective hk hkodd hδ0 hδ).injOn]
  simp

lemma mem_baseConfiguration (k : ℕ) (δ : ℝ) (i : Fin (k + 1)) :
    basePoint k δ i ∈ baseConfiguration k δ := by
  simp [baseConfiguration]

lemma isDiameterOne_baseConfiguration {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hkodd : Odd k) (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    IsDiameterOne (baseConfiguration k δ) := by
  rw [isDiameterOne_iff]
  constructor
  · intro x hx y hy
    simp only [baseConfiguration, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact dist_basePoint_le_one hk hkodd hδ0 hδ i j
  · let i : Fin k := ⟨0, by omega⟩
    refine ⟨basePoint k δ i.castSucc, mem_baseConfiguration k δ i.castSucc,
      basePoint k δ i.succ, mem_baseConfiguration k δ i.succ, ?_⟩
    exact dist_basePoint_consecutive hk hδ0 hδ i

lemma basePoint_first_x (k : ℕ) (δ : ℝ) :
    basePoint k δ (⟨0, by omega⟩ : Fin (k + 1)) 0 = outer k δ := by
  simp [basePoint, point3_apply_zero, sign, rawAngle, outer]

lemma basePoint_last_x {k : ℕ} (hkodd : Odd k) (δ : ℝ) :
    basePoint k δ (⟨k, by omega⟩ : Fin (k + 1)) 0 = outer k δ := by
  have hs : sign k = -1 := hkodd.neg_one_pow
  rw [basePoint, point3_apply_zero, hs]
  simp only [neg_one_mul]
  rw [show rawAngle k δ k = -((k : ℝ) * δ / 2) by
    unfold rawAngle; ring]
  rw [Real.sin_neg]
  simp [outer]

lemma basePoint_second_x {k : ℕ} (hk : 1 ≤ k) (δ : ℝ) :
    basePoint k δ (⟨1, by omega⟩ : Fin (k + 1)) 0 = -inner k δ := by
  rw [basePoint, point3_apply_zero]
  simp [sign, rawAngle, inner]

lemma basePoint_penultimate_x {k : ℕ} (hk : 3 ≤ k) (hkodd : Odd k) (δ : ℝ) :
    basePoint k δ (⟨k - 1, by omega⟩ : Fin (k + 1)) 0 = -inner k δ := by
  obtain ⟨a, ha⟩ := hkodd
  have he : Even (k - 1) := ⟨a, by omega⟩
  have hs : sign (k - 1) = 1 := he.neg_one_pow
  rw [basePoint, point3_apply_zero, hs, one_mul]
  rw [show rawAngle k δ (k - 1) = -(((k : ℝ) - 2) * δ / 2) by
    unfold rawAngle
    push_cast [show 1 ≤ k by omega]
    ring]
  rw [Real.sin_neg]
  simp [inner]

/-! ## The complete cospherical configuration -/

lemma point3_apply_one (x y z : ℝ) : point3 x y z 1 = y := by
  simp [point3]

lemma point3_apply_two (x y z : ℝ) : point3 x y z 2 = z := by
  simp [point3]

lemma basePoint_apply_two (k : ℕ) (δ : ℝ) (i : Fin (k + 1)) :
    basePoint k δ i 2 = 0 := by
  simp [basePoint, point3_apply_two]

lemma basePoint_xy_sq (k : ℕ) (δ : ℝ) (i : Fin (k + 1)) :
    (basePoint k δ i 0) ^ 2 + (basePoint k δ i 1) ^ 2 = rad δ ^ 2 := by
  rw [basePoint, point3_apply_zero, point3_apply_one]
  have hs := sign_sq (i : ℕ)
  have ht := Real.sin_sq_add_cos_sq (rawAngle k δ i)
  nlinarith [sq_nonneg (rad δ * Real.sin (rawAngle k δ i)),
    sq_nonneg (rad δ * Real.cos (rawAngle k δ i))]

def polePoint (δ : ℝ) : Point 3 := point3 0 0 (ht δ)

def supportPoint (δ t : ℝ) : Point 3 := point3 (qx δ t) 0 (qz δ t)

def sphereCenter (δ : ℝ) : Point 3 := point3 0 0 (ctr δ)

@[simp] lemma polePoint_apply_zero (δ : ℝ) : polePoint δ 0 = 0 := by
  simp [polePoint, point3_apply_zero]

@[simp] lemma polePoint_apply_two (δ : ℝ) : polePoint δ 2 = ht δ := by
  simp [polePoint, point3_apply_two]

@[simp] lemma supportPoint_apply_zero (δ t : ℝ) : supportPoint δ t 0 = qx δ t := by
  simp [supportPoint, point3_apply_zero]

@[simp] lemma supportPoint_apply_two (δ t : ℝ) : supportPoint δ t 2 = qz δ t := by
  simp [supportPoint, point3_apply_two]

lemma outer_pos {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) : 0 < outer k δ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have harg0 : 0 < (k : ℝ) * δ / 2 := by positivity
  have hargpi : (k : ℝ) * δ / 2 < Real.pi := by
    have := k_mul_delta_lt_pi hδ0 hδ
    nlinarith [Real.pi_pos]
  unfold outer
  exact mul_pos (base_rad_pos hk hδ0 hδ)
    (Real.sin_pos_of_pos_of_lt_pi harg0 hargpi)

lemma inner_pos {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) : 0 < inner k δ := by
  have hkR : (2 : ℝ) < k := by exact_mod_cast hk
  have harg0 : 0 < ((k : ℝ) - 2) * δ / 2 := by positivity
  have hargpi : ((k : ℝ) - 2) * δ / 2 < Real.pi := by
    have := k_mul_delta_lt_pi hδ0 hδ
    nlinarith [Real.pi_pos]
  unfold inner
  exact mul_pos (base_rad_pos hk hδ0 hδ)
    (Real.sin_pos_of_pos_of_lt_pi harg0 hargpi)

lemma inner_le_outer {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) : inner k δ ≤ outer k δ := by
  have hiNeg := inner_neg_angle_mem hk hδ0 hδ
  have hi : ((k : ℝ) - 2) * δ / 2 ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [hiNeg.2], by linarith [hiNeg.1]⟩
  have ho := outer_angle_mem hδ0 hδ
  have hangle : ((k : ℝ) - 2) * δ / 2 ≤ (k : ℝ) * δ / 2 := by
    nlinarith
  have hs := Real.strictMonoOn_sin.monotoneOn hi ho hangle
  exact mul_le_mul_of_nonneg_left hs (base_rad_pos hk hδ0 hδ).le

lemma outer_lt_threshold {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    outer k δ < ht δ * ctr δ / rad δ := by
  have ho := outer_angle_mem hδ0 hδ
  have htarget : Real.pi / 2 - δ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have hd5 := delta_lt_pi_div_five hk hδ
    constructor <;> nlinarith [Real.pi_pos]
  have hangle : (k : ℝ) * δ / 2 < Real.pi / 2 - δ := by
    have := delta_mul_add_lt_pi hδ
    nlinarith
  have hs := Real.strictMonoOn_sin ho htarget hangle
  rw [Real.sin_pi_div_two_sub] at hs
  have hmul := mul_lt_mul_of_pos_left hs (base_rad_pos hk hδ0 hδ)
  rw [outer_eq_ht_mul_ctr_div_rad hδ0.le
    (delta_lt_pi_div_five hk hδ).le] at hmul
  simpa [outer] using hmul

lemma qx_outer_neg {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) : qx δ (outer k δ) < 0 := by
  have hd5 := (delta_lt_pi_div_five hk hδ).le
  unfold qx
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num) (sphRad_pos hδ0.le hd5))
        (outer_pos hk hδ0 hδ))
      (ctr_pos hδ0.le hd5))
    (qden_pos (t := outer k δ) hδ0.le hd5)

lemma qx_neg_inner_pos {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) : 0 < qx δ (-inner k δ) := by
  have hd5 := (delta_lt_pi_div_five hk hδ).le
  unfold qx
  apply div_pos
  · ring_nf
    positivity [sphRad_pos hδ0.le hd5, inner_pos hk hδ0 hδ,
      ctr_pos hδ0.le hd5]
  · exact qden_pos (t := -inner k δ) hδ0.le hd5

lemma dist_support_point3_sq_sub_one {δ t X Y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5)
    (hbase : X ^ 2 + Y ^ 2 = rad δ ^ 2) :
    dist (supportPoint δ t) (point3 X Y 0) ^ 2 - 1 =
      -2 * qx δ t * (X - t) := by
  rw [supportPoint, dist_point3_sq]
  have h := q_support_dist_sq (t := t) hδ0 hδ hbase
  nlinarith

lemma dist_support_base_sq_sub_one {k : ℕ} {δ t : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) (i : Fin (k + 1)) :
    dist (supportPoint δ t) (basePoint k δ i) ^ 2 - 1 =
      -2 * qx δ t * (basePoint k δ i 0 - t) := by
  rw [basePoint]
  simp only [point3_apply_zero]
  apply dist_support_point3_sq_sub_one hδ0 hδ
  have hbase := basePoint_xy_sq k δ i
  rw [basePoint, point3_apply_zero, point3_apply_one] at hbase
  exact hbase

lemma dist_support_base_le_one {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hkodd : Odd k) (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2))
    (i : Fin (k + 1)) (which : Fin 2) :
    dist (supportPoint δ (if which = 0 then outer k δ else -inner k δ))
      (basePoint k δ i) ≤ 1 := by
  have hd5 := (delta_lt_pi_div_five hk hδ).le
  fin_cases which
  · change dist (supportPoint δ (outer k δ)) (basePoint k δ i) ≤ 1
    have hsq := dist_support_base_sq_sub_one hδ0.le hd5 (t := outer k δ) i
    have hstrip := (basePoint_coordinate_strip hk hkodd hδ0 hδ i).2
    have hqx := qx_outer_neg hk hδ0 hδ
    have hdist := dist_nonneg (x := supportPoint δ (outer k δ))
      (y := basePoint k δ i)
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hqx.le (sub_nonpos.mpr hstrip)]
  · change dist (supportPoint δ (-inner k δ)) (basePoint k δ i) ≤ 1
    have hsq := dist_support_base_sq_sub_one hδ0.le hd5 (t := -inner k δ) i
    have hstrip := (basePoint_coordinate_strip hk hkodd hδ0 hδ i).1
    have hqx := qx_neg_inner_pos hk hδ0 hδ
    have hdist := dist_nonneg (x := supportPoint δ (-inner k δ))
      (y := basePoint k δ i)
    have hdiff : 0 ≤ basePoint k δ i 0 - -inner k δ := by linarith
    nlinarith [mul_nonneg hqx.le hdiff]

lemma dist_support_base_eq_one_of_x {k : ℕ} {δ t : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5) (i : Fin (k + 1))
    (hx : basePoint k δ i 0 = t) :
    dist (supportPoint δ t) (basePoint k δ i) = 1 := by
  have hsq := dist_support_base_sq_sub_one hδ0 hδ (t := t) i
  rw [hx] at hsq
  have hd := dist_nonneg (x := supportPoint δ t) (y := basePoint k δ i)
  nlinarith

lemma dist_pole_base {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) (i : Fin (k + 1)) :
    dist (polePoint δ) (basePoint k δ i) = 1 := by
  have hd5 := (delta_lt_pi_div_five hk hδ).le
  have hsq : dist (polePoint δ) (basePoint k δ i) ^ 2 = 1 := by
    rw [polePoint, basePoint, dist_point3_sq]
    have hxy := basePoint_xy_sq k δ i
    have hrh := rad_sq_add_ht_sq hδ0.le hd5
    rw [basePoint, point3_apply_zero, point3_apply_one] at hxy
    nlinarith
  nlinarith [dist_nonneg (x := polePoint δ) (y := basePoint k δ i)]

lemma dist_pole_support_sq {δ t : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ Real.pi / 5) :
    dist (polePoint δ) (supportPoint δ t) ^ 2 =
      4 * sphRad δ ^ 2 * t ^ 2 / (t ^ 2 + ctr δ ^ 2) := by
  rw [polePoint, supportPoint, dist_point3_sq]
  have h := pole_q_dist_sq (t := t) hδ0 hδ
  nlinarith

lemma two_sphRad_mul_ht {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ Real.pi / 5) : 2 * sphRad δ * ht δ = 1 := by
  have hh := (ht_pos hδ0 hδ).ne'
  unfold sphRad
  field_simp [hh]

lemma dist_pole_support_le_one_of_sq {δ t : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ Real.pi / 5)
    (htsq : t ^ 2 * rad δ ^ 2 ≤ ht δ ^ 2 * ctr δ ^ 2) :
    dist (polePoint δ) (supportPoint δ t) ≤ 1 := by
  have hform := dist_pole_support_sq (t := t) hδ0 hδ
  have hden := qden_pos (t := t) hδ0 hδ
  have hrh := rad_sq_add_ht_sq hδ0 hδ
  have hsh := two_sphRad_mul_ht hδ0 hδ
  have hshsq : 4 * sphRad δ ^ 2 * ht δ ^ 2 = 1 := by nlinarith
  have hnum : 4 * sphRad δ ^ 2 * t ^ 2 ≤ t ^ 2 + ctr δ ^ 2 := by
    nlinarith [sq_nonneg (t * rad δ), sq_nonneg (ht δ * ctr δ),
      sq_nonneg (sphRad δ * t), sq_nonneg (sphRad δ * ht δ)]
  have hsq : dist (polePoint δ) (supportPoint δ t) ^ 2 ≤ 1 := by
    rw [hform]
    exact (div_le_one hden).2 hnum
  nlinarith [dist_nonneg (x := polePoint δ) (y := supportPoint δ t)]

lemma dist_pole_support_outer_le_one {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    dist (polePoint δ) (supportPoint δ (outer k δ)) ≤ 1 := by
  have hd5 := (delta_lt_pi_div_five hk hδ).le
  have hr := rad_pos hδ0.le hd5
  have hlt := outer_lt_threshold hk hδ0 hδ
  have hmul : outer k δ * rad δ < ht δ * ctr δ := by
    exact (lt_div_iff₀ hr).mp hlt
  apply dist_pole_support_le_one_of_sq hδ0.le hd5
  have hsquare : (outer k δ * rad δ) ^ 2 < (ht δ * ctr δ) ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg (outer_pos hk hδ0 hδ).le hr.le)
      (mul_nonneg (ht_pos hδ0.le hd5).le (ctr_pos hδ0.le hd5).le)).2 hmul
  nlinarith

lemma dist_pole_support_inner_le_one {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    dist (polePoint δ) (supportPoint δ (-inner k δ)) ≤ 1 := by
  have hd5 := (delta_lt_pi_div_five hk hδ).le
  have hr := rad_pos hδ0.le hd5
  have hpos := inner_pos hk hδ0 hδ
  have hle := inner_le_outer hk hδ0 hδ
  have hlt := outer_lt_threshold hk hδ0 hδ
  have hmul : inner k δ * rad δ < ht δ * ctr δ := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hr.le)
    exact (lt_div_iff₀ hr).mp hlt
  apply dist_pole_support_le_one_of_sq hδ0.le hd5
  have hsquare : (inner k δ * rad δ) ^ 2 < (ht δ * ctr δ) ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg hpos.le hr.le)
      (mul_nonneg (ht_pos hδ0.le hd5).le (ctr_pos hδ0.le hd5).le)).2 hmul
  nlinarith

lemma dist_base_sphereCenter {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) (i : Fin (k + 1)) :
    dist (basePoint k δ i) (sphereCenter δ) = sphRad δ := by
  have hd5 := (delta_lt_pi_div_five hk hδ).le
  have hsq : dist (basePoint k δ i) (sphereCenter δ) ^ 2 = sphRad δ ^ 2 := by
    rw [basePoint, sphereCenter, dist_point3_sq]
    have hxy := basePoint_xy_sq k δ i
    rw [basePoint, point3_apply_zero, point3_apply_one] at hxy
    have hrs := rad_sq_add_ctr_sq hδ0.le hd5
    nlinarith
  nlinarith [dist_nonneg (x := basePoint k δ i) (y := sphereCenter δ),
    sphRad_pos hδ0.le hd5]

lemma dist_pole_sphereCenter {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    dist (polePoint δ) (sphereCenter δ) = sphRad δ := by
  have hd5 := (delta_lt_pi_div_five hk hδ).le
  have hh := ht_sub_ctr hδ0.le hd5
  have hs := sphRad_pos hδ0.le hd5
  have hsq : dist (polePoint δ) (sphereCenter δ) ^ 2 = sphRad δ ^ 2 := by
    rw [polePoint, sphereCenter, dist_point3_sq]
    nlinarith
  have hd := dist_nonneg (x := polePoint δ) (y := sphereCenter δ)
  nlinarith

lemma dist_support_sphereCenter {k : ℕ} {δ t : ℝ} (hk : 3 ≤ k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    dist (supportPoint δ t) (sphereCenter δ) = sphRad δ := by
  have hd5 := (delta_lt_pi_div_five hk hδ).le
  have hsq : dist (supportPoint δ t) (sphereCenter δ) ^ 2 = sphRad δ ^ 2 := by
    rw [supportPoint, sphereCenter, dist_point3_sq]
    have hq := q_center_sq (t := t) hδ0.le hd5
    nlinarith
  nlinarith [dist_nonneg (x := supportPoint δ t) (y := sphereCenter δ),
    sphRad_pos hδ0.le hd5]

lemma dist_supports_sq (k : ℕ) (δ : ℝ) :
    dist (supportPoint δ (outer k δ)) (supportPoint δ (-inner k δ)) ^ 2 =
      qdistSq k δ := by
  rw [supportPoint, supportPoint, dist_point3_sq]
  unfold qdistSq
  ring

lemma dist_supports_eq_one {k : ℕ} {δ : ℝ} (hq : qdistSq k δ = 1) :
    dist (supportPoint δ (outer k δ)) (supportPoint δ (-inner k δ)) = 1 := by
  have hsq := dist_supports_sq k δ
  rw [hq] at hsq
  nlinarith [dist_nonneg (x := supportPoint δ (outer k δ))
    (y := supportPoint δ (-inner k δ))]

lemma basePoint_apply_one_ne_zero {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) (i : Fin (k + 1)) :
    basePoint k δ i 1 ≠ 0 := by
  have hiN : (i : ℕ) ≤ k := by omega
  have hiR : (i : ℝ) ≤ k := by exact_mod_cast hiN
  have hkpi := k_mul_delta_lt_pi hδ0 hδ
  have harg : rawAngle k δ i ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    unfold rawAngle
    constructor <;> nlinarith [Real.pi_pos]
  have hc := Real.cos_pos_of_mem_Ioo harg
  rw [basePoint, point3_apply_one]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (base_rad_pos hk hδ0 hδ).ne') hc.ne'

def exceptionalPoint (k : ℕ) (δ : ℝ) : Fin 3 → Point 3
  | 0 => polePoint δ
  | 1 => supportPoint δ (outer k δ)
  | 2 => supportPoint δ (-inner k δ)

def vertexPoint (k : ℕ) (δ : ℝ) : OddVertex k → Point 3
  | .inl i => basePoint k δ i
  | .inr j => exceptionalPoint k δ j

lemma exceptionalPoint_apply_one (k : ℕ) (δ : ℝ) (j : Fin 3) :
    exceptionalPoint k δ j 1 = 0 := by
  fin_cases j <;> simp [exceptionalPoint, polePoint, supportPoint, point3_apply_one]

lemma vertexPoint_injective {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    Function.Injective (vertexPoint k δ) := by
  intro u v huv
  cases u with
  | inl i =>
      cases v with
      | inl j =>
          exact congrArg Sum.inl ((basePoint_injective hk hkodd hδ0 hδ) huv)
      | inr j =>
          exfalso
          have hy := congrArg (fun p : Point 3 => p 1) huv
          simp only [vertexPoint, exceptionalPoint_apply_one] at hy
          exact basePoint_apply_one_ne_zero hk hδ0 hδ i hy
  | inr i =>
      cases v with
      | inl j =>
          exfalso
          have hy := congrArg (fun p : Point 3 => p 1) huv
          simp only [vertexPoint, exceptionalPoint_apply_one] at hy
          exact basePoint_apply_one_ne_zero hk hδ0 hδ j hy.symm
      | inr j =>
          apply congrArg Sum.inr
          fin_cases i <;> fin_cases j <;> (try rfl)
          all_goals
            exfalso
            have hx := congrArg (fun p : Point 3 => p 0) huv
            simp only [vertexPoint, exceptionalPoint, polePoint_apply_zero,
              supportPoint_apply_zero] at hx
          · exact (qx_outer_neg hk hδ0 hδ).ne hx.symm
          · exact (qx_neg_inner_pos hk hδ0 hδ).ne' hx.symm
          · exact (qx_outer_neg hk hδ0 hδ).ne hx
          · nlinarith [qx_outer_neg hk hδ0 hδ, qx_neg_inner_pos hk hδ0 hδ]
          · exact (qx_neg_inner_pos hk hδ0 hδ).ne' hx
          · nlinarith [qx_outer_neg hk hδ0 hδ, qx_neg_inner_pos hk hδ0 hδ]

def vertexEmbedding {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) : OddVertex k ↪ Point 3 :=
  ⟨vertexPoint k δ, vertexPoint_injective hk hkodd hδ0 hδ⟩

def configuration {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) : Finset (Point 3) :=
  Finset.univ.map (vertexEmbedding hk hkodd hδ0 hδ)

lemma card_configuration {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    (configuration hk hkodd hδ0 hδ).card = k + 4 := by
  simp [configuration, OddVertex]

lemma mem_configuration {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) (v : OddVertex k) :
    vertexPoint k δ v ∈ configuration hk hkodd hδ0 hδ := by
  exact Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩

lemma vertex_dist_le_one {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2))
    (hq : qdistSq k δ = 1) (u v : OddVertex k) :
    dist (vertexPoint k δ u) (vertexPoint k δ v) ≤ 1 := by
  cases u with
  | inl i =>
      cases v with
      | inl j => exact dist_basePoint_le_one hk hkodd hδ0 hδ i j
      | inr j =>
          fin_cases j
          · simpa [vertexPoint, exceptionalPoint, dist_comm] using (dist_pole_base hk hδ0 hδ i).le
          · simpa [vertexPoint, exceptionalPoint, dist_comm] using
              dist_support_base_le_one hk hkodd hδ0 hδ i (0 : Fin 2)
          · simpa [vertexPoint, exceptionalPoint, dist_comm] using
              dist_support_base_le_one hk hkodd hδ0 hδ i (1 : Fin 2)
  | inr i =>
      cases v with
      | inl j =>
          fin_cases i
          · simpa [vertexPoint, exceptionalPoint] using (dist_pole_base hk hδ0 hδ j).le
          · simpa [vertexPoint, exceptionalPoint] using
              dist_support_base_le_one hk hkodd hδ0 hδ j (0 : Fin 2)
          · simpa [vertexPoint, exceptionalPoint] using
              dist_support_base_le_one hk hkodd hδ0 hδ j (1 : Fin 2)
      | inr j =>
          fin_cases i <;> fin_cases j <;>
            simp only [vertexPoint, exceptionalPoint, dist_self, zero_le_one]
          · exact dist_pole_support_outer_le_one hk hδ0 hδ
          · exact dist_pole_support_inner_le_one hk hδ0 hδ
          · simpa [dist_comm] using dist_pole_support_outer_le_one hk hδ0 hδ
          · exact (dist_supports_eq_one hq).le
          · simpa [dist_comm] using dist_pole_support_inner_le_one hk hδ0 hδ
          · simpa [dist_comm] using (dist_supports_eq_one hq).le

lemma isDiameterOne_configuration {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) (hq : qdistSq k δ = 1) :
    IsDiameterOne (configuration hk hkodd hδ0 hδ) := by
  rw [isDiameterOne_iff]
  constructor
  · intro x hx y hy
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hy
    exact vertex_dist_le_one hk hkodd hδ0 hδ hq u v
  · refine ⟨supportPoint δ (outer k δ), mem_configuration hk hkodd hδ0 hδ (.inr 1),
      supportPoint δ (-inner k δ), mem_configuration hk hkodd hδ0 hδ (.inr 2), ?_⟩
    exact dist_supports_eq_one hq

lemma configuration_onSphere {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    LocalSphere.IsOnSphere (configuration hk hkodd hδ0 hδ) (sphereCenter δ) (sphRad δ) := by
  intro x hx
  obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hx
  cases v with
  | inl i => exact dist_base_sphereCenter hk hδ0 hδ i
  | inr j =>
      fin_cases j
      · exact dist_pole_sphereCenter hk hδ0 hδ
      · exact dist_support_sphereCenter hk hδ0 hδ
      · exact dist_support_sphereCenter hk hδ0 hδ

lemma dist_support_first {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    dist (supportPoint δ (outer k δ)) (basePoint k δ (firstBase k)) = 1 := by
  apply dist_support_base_eq_one_of_x hδ0.le (delta_lt_pi_div_five hk hδ).le
  exact basePoint_first_x k δ

lemma dist_support_last {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    dist (supportPoint δ (outer k δ)) (basePoint k δ (lastBase k)) = 1 := by
  apply dist_support_base_eq_one_of_x hδ0.le (delta_lt_pi_div_five hk hδ).le
  exact basePoint_last_x hkodd δ

lemma dist_support_second {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hδ0 : 0 < δ)
    (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    dist (supportPoint δ (-inner k δ)) (basePoint k δ (secondBase hk)) = 1 := by
  apply dist_support_base_eq_one_of_x hδ0.le (delta_lt_pi_div_five hk hδ).le
  exact basePoint_second_x (by omega) δ

lemma dist_support_penultimate {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    dist (supportPoint δ (-inner k δ)) (basePoint k δ (penultimateBase hk)) = 1 := by
  apply dist_support_base_eq_one_of_x hδ0.le (delta_lt_pi_div_five hk hδ).le
  exact basePoint_penultimate_x hk hkodd δ

lemma dist_eq_one_of_oddEdgeMap_eq {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) (hq : qdistSq k δ = 1)
    (e : OddEdgeIndex k) (u v : OddVertex k) (he : oddEdgeMap hk e = s(u, v)) :
    dist (vertexPoint k δ u) (vertexPoint k δ v) = 1 := by
  rcases e with i | (i | (i | (i | i)))
  · simp only [oddEdgeMap] at he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hl : pathLeft i = i.castSucc := Fin.ext rfl
      have hr : pathRight i = i.succ := Fin.ext rfl
      simpa only [vertexPoint, hl, hr] using
        dist_basePoint_consecutive hk hδ0 hδ i
    · have hl : pathLeft i = i.castSucc := Fin.ext rfl
      have hr : pathRight i = i.succ := Fin.ext rfl
      simpa only [vertexPoint, hl, hr, dist_comm] using
        dist_basePoint_consecutive hk hδ0 hδ i
  · simp only [oddEdgeMap] at he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [vertexPoint, exceptionalPoint] using dist_pole_base hk hδ0 hδ i
    · simpa [vertexPoint, exceptionalPoint, dist_comm] using dist_pole_base hk hδ0 hδ i
  · simp only [oddEdgeMap] at he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · fin_cases i
      · simpa [vertexPoint, exceptionalPoint, yBase] using dist_support_first hk hδ0 hδ
      · simpa [vertexPoint, exceptionalPoint, yBase] using dist_support_last hk hkodd hδ0 hδ
    · fin_cases i
      · simpa [vertexPoint, exceptionalPoint, yBase, dist_comm] using dist_support_first hk hδ0 hδ
      · simpa [vertexPoint, exceptionalPoint, yBase, dist_comm] using dist_support_last hk hkodd hδ0 hδ
  · simp only [oddEdgeMap] at he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · fin_cases i
      · simpa [vertexPoint, exceptionalPoint, zBase] using dist_support_second hk hδ0 hδ
      · simpa [vertexPoint, exceptionalPoint, zBase] using
          dist_support_penultimate hk hkodd hδ0 hδ
    · fin_cases i
      · simpa [vertexPoint, exceptionalPoint, zBase, dist_comm] using dist_support_second hk hδ0 hδ
      · simpa [vertexPoint, exceptionalPoint, zBase, dist_comm] using
          dist_support_penultimate hk hkodd hδ0 hδ
  · simp only [oddEdgeMap] at he
    rw [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [vertexPoint, exceptionalPoint] using dist_supports_eq_one hq
    · simpa [vertexPoint, exceptionalPoint, dist_comm] using dist_supports_eq_one hq

lemma dist_eq_one_of_oddWitnessGraph_adj {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hkodd : Odd k) (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2))
    (hq : qdistSq k δ = 1) {u v : OddVertex k} (huv : (oddWitnessGraph hk).Adj u v) :
    dist (vertexPoint k δ u) (vertexPoint k δ v) = 1 := by
  rw [oddWitnessGraph, SimpleGraph.fromEdgeSet_adj] at huv
  have hmem : s(u, v) ∈ oddWitnessEdges hk := huv.1
  rw [oddWitnessEdges, Finset.mem_image] at hmem
  obtain ⟨e, -, he⟩ := hmem
  exact dist_eq_one_of_oddEdgeMap_eq hk hkodd hδ0 hδ hq e u v he

def configurationVertexEmbedding {k : ℕ} {δ : ℝ} (hk : 3 ≤ k) (hkodd : Odd k)
    (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2)) :
    OddVertex k ↪ {x // x ∈ configuration hk hkodd hδ0 hδ} where
  toFun v := ⟨vertexPoint k δ v, mem_configuration hk hkodd hδ0 hδ v⟩
  inj' := by
    intro u v huv
    exact vertexPoint_injective hk hkodd hδ0 hδ (congrArg Subtype.val huv)

lemma oddWitnessGraph_map_le_diameterGraph {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hkodd : Odd k) (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2))
    (hq : qdistSq k δ = 1) :
    (oddWitnessGraph hk).map (configurationVertexEmbedding hk hkodd hδ0 hδ) ≤
      diameterGraph (configuration hk hkodd hδ0 hδ) := by
  intro x y hxy
  obtain ⟨u, v, huv, rfl, rfl⟩ :=
    (SimpleGraph.map_adj (configurationVertexEmbedding hk hkodd hδ0 hδ)
      (oddWitnessGraph hk) x y).mp hxy
  exact dist_eq_one_of_oddWitnessGraph_adj hk hkodd hδ0 hδ hq huv

lemma oddWitness_count_le_diameterPairCount {k : ℕ} {δ : ℝ} (hk : 3 ≤ k)
    (hkodd : Odd k) (hδ0 : 0 < δ) (hδ : δ < Real.pi / ((k : ℝ) + 2))
    (hq : qdistSq k δ = 1) :
    2 * k + 6 ≤ diameterPairCount (configuration hk hkodd hδ0 hδ) := by
  classical
  have hmono := SimpleGraph.edgeFinset_mono
    (oddWitnessGraph_map_le_diameterGraph hk hkodd hδ0 hδ hq)
  have hcard := Finset.card_le_card hmono
  rw [SimpleGraph.card_edgeFinset_map, card_oddWitnessGraph hk] at hcard
  exact hcard

/-- Every odd cardinality at least seven admits a sharp three-dimensional
cospherical diameter configuration.  The carrier sphere has squared radius
strictly below `1 / 2`, as needed in the five-dimensional Lenz construction. -/
theorem exists_odd_cospherical_configuration (m : ℕ) (hm : 7 ≤ m) (hodd : Odd m) :
    ∃ A : Finset (Point 3), ∃ c : Point 3, ∃ r : ℝ,
      A.card = m ∧ LocalSphere.IsOnSphere A c r ∧ 0 < r ∧ r ^ 2 < 1 / 2 ∧
        IsDiameterOne A ∧ 2 * m - 2 ≤ diameterPairCount A := by
  let k := m - 4
  have hk : 3 ≤ k := by omega
  have hkodd : Odd k := Nat.Odd.sub_even (by omega) hodd (by decide)
  obtain ⟨δ, hδ0, hδ, hδpi5, hq⟩ := exists_delta_qdistSq_eq_one_le_pi_div_five k hk
  refine ⟨configuration hk hkodd hδ0 hδ, sphereCenter δ, sphRad δ,
    ?_, configuration_onSphere hk hkodd hδ0 hδ, sphRad_pos hδ0.le hδpi5,
    sphRad_sq_lt_half hδ0.le hδpi5, isDiameterOne_configuration hk hkodd hδ0 hδ hq, ?_⟩
  · rw [card_configuration]
    omega
  · have hc := oddWitness_count_le_diameterPairCount hk hkodd hδ0 hδ hq
    omega

end

end OddCosphericalConstruction
end Erdos223

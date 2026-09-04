/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.LeviAffineVertices
import ErdosProblems.Erdos735.LeviSignVector

/-!
# Exterior sectors at affine arrangement vertices

This file develops the local affine geometry used in Felsner's proof of
Levi's triangle theorem.  At an affine crossing `v`, the incident dual lines
are finite and pairwise nonparallel.  Their oriented rays into a strict
supporting half-plane can therefore be linearly ordered; two consecutive
rays bound an empty exterior sector.
-/

open scoped Matrix

namespace Erdos735.LeviExteriorSector

noncomputable section

open LeviAffineChart LeviAffineVertices

abbrev Point := ProjectiveArrangement.Point

/-- A continuous linear functional on the concrete affine plane. -/
def planeFunctional (a b : ℝ) : Point →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ a * u 0 + b * u 1
      map_add' := by
        intro u v
        simp
        ring
      map_smul' := by
        intro c u
        simp
        ring }

@[simp] theorem planeFunctional_apply (a b : ℝ) (u : Point) :
    planeFunctional a b u = a * u 0 + b * u 1 := by
  rfl

/-- A finite family of nonzero planar vectors admits one linear functional
which is nonzero on every member.  The explicit parameter is chosen larger
than every forbidden root. -/
theorem exists_planeFunctional_nonzero_on (D : Finset Point)
    (hne : ∀ d ∈ D, d ≠ 0) :
    ∃ l : Point →L[ℝ] ℝ, ∀ d ∈ D, l d ≠ 0 := by
  classical
  let bad : Finset ℝ :=
    (D.filter fun d ↦ d 1 ≠ 0).image fun d ↦ -(d 0) / d 1
  let t : ℝ := ∑ z ∈ bad, |z| + 1
  refine ⟨planeFunctional 1 t, ?_⟩
  intro d hd
  by_cases hd1 : d 1 = 0
  · have hd0 : d 0 ≠ 0 := by
      intro hd0
      apply hne d hd
      apply PiLp.ext
      intro i
      fin_cases i
      · exact hd0
      · exact hd1
    simpa [planeFunctional, hd1] using hd0
  · have hroot : -(d 0) / d 1 ∈ bad := by
      exact Finset.mem_image.mpr
        ⟨d, Finset.mem_filter.mpr ⟨hd, hd1⟩, rfl⟩
    have habs_le : |-(d 0) / d 1| ≤ ∑ z ∈ bad, |z| := by
      exact Finset.single_le_sum
        (fun z hz ↦ abs_nonneg z) hroot
    have htgt : -(d 0) / d 1 < t := by
      have hle : -(d 0) / d 1 ≤ |-(d 0) / d 1| := le_abs_self _
      dsimp [t]
      linarith
    intro hzero
    have htroot : t = -(d 0) / d 1 := by
      apply (eq_div_iff hd1).2
      rw [planeFunctional_apply] at hzero
      simp only [one_mul] at hzero
      linarith
    linarith

/-- Strict support at a finite hull vertex can be chosen nonconstant in
every direction from a prescribed finite nonzero family. -/
theorem hullVertex_exists_generic_strict_support
    (A D : Finset Point) {v : Point}
    (hv : v ∈ Erdos957.hullVertices A)
    (hD : ∀ d ∈ D, d ≠ 0) :
    ∃ l : Point →L[ℝ] ℝ,
      (∀ w ∈ A, l w ≤ l v) ∧
      (∀ w ∈ A, w ≠ v → l w < l v) ∧
      (∀ d ∈ D, l d ≠ 0) := by
  classical
  obtain ⟨l₀, hl₀le, hl₀lt⟩ :=
    Erdos957.hullVertex_exists_strict_support A hv
  obtain ⟨g, hg⟩ := exists_planeFunctional_nonzero_on D hD
  let W := A.erase v
  obtain ⟨c, hc, hcW⟩ :=
    SignVector.exists_pos_forall_abs_mul_lt_finset W
      (fun w ↦ l₀ v - l₀ w) (fun w ↦ g w - g v) (by
        intro w hw
        have hw' := Finset.mem_erase.mp hw
        exact sub_pos.mpr (hl₀lt w hw'.2 hw'.1))
  let D' := D.filter fun d ↦ l₀ d ≠ 0
  obtain ⟨e, he, heD⟩ :=
    SignVector.exists_pos_forall_abs_mul_lt_finset D'
      (fun d ↦ |l₀ d|) (fun d ↦ g d) (by
        intro d hd
        have hd' : l₀ d ≠ 0 := (Finset.mem_filter.mp hd).2
        exact abs_pos.mpr hd')
  let ε : ℝ := min c e
  have hε : 0 < ε := lt_min hc he
  let l : Point →L[ℝ] ℝ := l₀ + ε • g
  have hstrict : ∀ w ∈ A, w ≠ v → l w < l v := by
    intro w hw hwv
    have hwW : w ∈ W := Finset.mem_erase.mpr ⟨hwv, hw⟩
    have hb := hcW w hwW
    have hεc : ε ≤ c := min_le_left _ _
    have habsnonneg : 0 ≤ |g w - g v| := abs_nonneg _
    have hbε : |g w - g v| * ε < l₀ v - l₀ w :=
      (mul_le_mul_of_nonneg_left hεc habsnonneg).trans_lt hb
    have hdiff : ε * (g w - g v) ≤ |g w - g v| * ε := by
      calc
        ε * (g w - g v) ≤ ε * |g w - g v| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
        _ = |g w - g v| * ε := mul_comm _ _
    dsimp [l]
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    linarith
  refine ⟨l, ?_, hstrict, ?_⟩
  · intro w hw
    by_cases hwv : w = v
    · subst w
      exact le_rfl
    · exact (hstrict w hw hwv).le
  · intro d hd
    by_cases hzero : l₀ d = 0
    · dsimp [l]
      simp only [ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, hzero, zero_add]
      exact mul_ne_zero hε.ne' (hg d hd)
    · have hdD' : d ∈ D' := Finset.mem_filter.mpr ⟨hd, hzero⟩
      have hb := heD d hdD'
      have hεe : ε ≤ e := min_le_right _ _
      have habsnonneg : 0 ≤ |g d| := abs_nonneg _
      have hbε : |g d| * ε < |l₀ d| :=
        (mul_le_mul_of_nonneg_left hεe habsnonneg).trans_lt hb
      intro hsum
      have heq : l₀ d + ε * g d = 0 := by
        simpa [l] using hsum
      have habseq : |g d| * ε = |l₀ d| := by
        have : ε * g d = -(l₀ d) := by linarith
        calc
          |g d| * ε = |ε * g d| := by rw [abs_mul, abs_of_pos hε]; ring
          _ = |l₀ d| := by rw [this, abs_neg]
      linarith

/-- A nonzero functional and its quarter turn give injective coordinates on
the affine plane. -/
theorem supportCoordinate_injective {l : Point →L[ℝ] ℝ} (hl : l ≠ 0) :
    Function.Injective
      (fun x : Point ↦ (l x, Erdos957.quarterTurnFunctional l x)) := by
  intro x y hxy
  have h₀ : l (x - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
  have h₁ : Erdos957.quarterTurnFunctional l (x - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
  have hcoeff := Erdos957.support_coefficient_sq_pos hl
  have hlcoord := Erdos957.continuousLinearMap_apply_eq_coordinates l (x - y)
  have hqcoord := Erdos957.quarterTurnFunctional_apply l (x - y)
  have heq₀ :
      l (Erdos957.planeBasisVector 0) * (x - y) 0 +
        l (Erdos957.planeBasisVector 1) * (x - y) 1 = 0 := by
    rw [← hlcoord, h₀]
  have heq₁ :
      -(l (Erdos957.planeBasisVector 1)) * (x - y) 0 +
        l (Erdos957.planeBasisVector 0) * (x - y) 1 = 0 := by
    rw [← hqcoord, h₁]
  have hprod₀ :
      (l (Erdos957.planeBasisVector 0) ^ 2 +
          l (Erdos957.planeBasisVector 1) ^ 2) * (x - y) 0 = 0 := by
    linear_combination
      l (Erdos957.planeBasisVector 0) * heq₀ -
        l (Erdos957.planeBasisVector 1) * heq₁
  have hprod₁ :
      (l (Erdos957.planeBasisVector 0) ^ 2 +
          l (Erdos957.planeBasisVector 1) ^ 2) * (x - y) 1 = 0 := by
    linear_combination
      l (Erdos957.planeBasisVector 1) * heq₀ +
        l (Erdos957.planeBasisVector 0) * heq₁
  have hcoeff_ne :
      l (Erdos957.planeBasisVector 0) ^ 2 +
          l (Erdos957.planeBasisVector 1) ^ 2 ≠ 0 :=
    ne_of_gt hcoeff
  have hz₀ : (x - y) 0 = 0 := by
    exact (mul_eq_zero.mp hprod₀).resolve_left hcoeff_ne
  have hz₁ : (x - y) 1 = 0 := by
    exact (mul_eq_zero.mp hprod₁).resolve_left hcoeff_ne
  apply PiLp.ext
  intro i
  fin_cases i
  · exact sub_eq_zero.mp (by simpa using hz₀)
  · exact sub_eq_zero.mp (by simpa using hz₁)

/-- A direction vector along the affine line with covector `q-p`. -/
def lineDirection (p q : Point) : Point :=
  WithLp.toLp 2 ![-(coeff p q 1), coeff p q 0]

@[simp] theorem lineDirection_apply_zero (p q : Point) :
    lineDirection p q 0 = -(coeff p q 1) := rfl

@[simp] theorem lineDirection_apply_one (p q : Point) :
    lineDirection p q 1 = coeff p q 0 := rfl

@[simp] theorem directionEval_lineDirection_self (p q : Point) :
    directionEval p q (lineDirection p q) = 0 := by
  simp [directionEval, lineDirection, coeff]
  ring

theorem lineDirection_ne_zero {p q : Point} (hpq : p ≠ q) :
    lineDirection p q ≠ 0 := by
  intro hzero
  have h0 := congrArg (fun z : Point ↦ z 0) hzero
  have h1 := congrArg (fun z : Point ↦ z 1) hzero
  simp [lineDirection] at h0 h1
  apply coeff_ne_zero hpq
  apply PiLp.ext
  intro i
  fin_cases i
  · simpa [coeff] using h1
  · have : q 1 - p 1 = 0 := by linarith
    simpa [coeff] using this

@[simp] theorem directionEval_lineDirection (p q r : Point) :
    directionEval p q (lineDirection p r) =
      -(det2 (coeff p q) (coeff p r)) := by
  simp [directionEval, lineDirection, det2, coeff]
  ring

theorem directionEval_eq_crossVec_lineDirection (p q : Point) (u : Point) :
    directionEval p q u = Erdos957.crossVec u (lineDirection p q) := by
  simp [directionEval, lineDirection, Erdos957.crossVec, coeff]
  ring

theorem crossVec_smul_right (u v : Point) (c : ℝ) :
    Erdos957.crossVec u (c • v) = c * Erdos957.crossVec u v := by
  simp [Erdos957.crossVec]
  ring

@[simp] theorem directionEval_neg_apply (p q u : Point) :
    directionEval p q (-u) = -directionEval p q u := by
  simp [directionEval]
  ring

/-- The ray on the affine line of `q`, oriented into the half-plane where
`l` is positive and normalized to have support coordinate one. -/
def supportRay (l : Point →L[ℝ] ℝ) (p q : Point) : Point :=
  (l (lineDirection p q))⁻¹ • lineDirection p q

theorem supportRay_support {l : Point →L[ℝ] ℝ} {p q : Point}
    (hlq : l (lineDirection p q) ≠ 0) :
    l (supportRay l p q) = 1 := by
  simp [supportRay, hlq]

theorem supportRay_rescale {l : Point →L[ℝ] ℝ} {p q : Point}
    (hlq : l (lineDirection p q) ≠ 0) :
    l (lineDirection p q) • supportRay l p q = lineDirection p q := by
  rw [supportRay, smul_smul, mul_inv_cancel₀ hlq, one_smul]

@[simp] theorem directionEval_supportRay_self
    (l : Point →L[ℝ] ℝ) (p q : Point) :
    directionEval p q (supportRay l p q) = 0 := by
  rw [supportRay, directionEval_smul, directionEval_lineDirection_self,
    mul_zero]

/-- The transverse coordinate of a normalized exterior ray. -/
def rayCoordinate (l : Point →L[ℝ] ℝ) (p q : Point) : ℝ :=
  Erdos957.quarterTurnFunctional l (supportRay l p q)

@[simp] theorem supportRay_neg (l : Point →L[ℝ] ℝ) (p q : Point) :
    supportRay (-l) p q = -supportRay l p q := by
  simp [supportRay]

@[simp] theorem rayCoordinate_neg (l : Point →L[ℝ] ℝ) (p q : Point) :
    rayCoordinate (-l) p q = rayCoordinate l p q := by
  simp [rayCoordinate, Erdos957.quarterTurnFunctional_apply]

/-- On the support-one affine line, the transverse-coordinate difference
is a positive constant times the planar determinant. -/
theorem rayCoordinate_sub_eq_supportSq_mul_cross
    {l : Point →L[ℝ] ℝ} {p q r : Point}
    (hlq : l (lineDirection p q) ≠ 0)
    (hlr : l (lineDirection p r) ≠ 0) :
    rayCoordinate l p r - rayCoordinate l p q =
      (l (Erdos957.planeBasisVector 0) ^ 2 +
        l (Erdos957.planeBasisVector 1) ^ 2) *
          Erdos957.crossVec (supportRay l p q) (supportRay l p r) := by
  have hdet := Erdos957.support_turn_coordinate_det l
    (supportRay l p q) (supportRay l p r)
  rw [supportRay_support hlq, supportRay_support hlr, one_mul, mul_one] at hdet
  simpa [rayCoordinate] using hdet

/-- Coordinate form of evaluating an incident line on another normalized
ray. -/
theorem supportSq_mul_directionEval_supportRay
    {l : Point →L[ℝ] ℝ} {p a q : Point}
    (hla : l (lineDirection p a) ≠ 0)
    (hlq : l (lineDirection p q) ≠ 0) :
    (l (Erdos957.planeBasisVector 0) ^ 2 +
      l (Erdos957.planeBasisVector 1) ^ 2) *
        directionEval p a (supportRay l p q) =
      l (lineDirection p a) *
        (rayCoordinate l p a - rayCoordinate l p q) := by
  have hcrossscale :
      Erdos957.crossVec (supportRay l p q) (lineDirection p a) =
        l (lineDirection p a) *
          Erdos957.crossVec (supportRay l p q) (supportRay l p a) := by
    calc
      Erdos957.crossVec (supportRay l p q) (lineDirection p a) =
          Erdos957.crossVec (supportRay l p q)
            (l (lineDirection p a) • supportRay l p a) := by
              rw [supportRay_rescale hla]
      _ = _ := crossVec_smul_right _ _ _
  rw [directionEval_eq_crossVec_lineDirection, hcrossscale]
  have hcoord := rayCoordinate_sub_eq_supportSq_mul_cross
    (p := p) (q := q) (r := a) hlq hla
  rw [hcoord]
  ring

theorem directionEval_supportRay_ne_zero_of_nonparallel
    {l : Point →L[ℝ] ℝ} {p a q : Point}
    (haq : Nonparallel p a q)
    (hlq : l (lineDirection p q) ≠ 0) :
    directionEval p a (supportRay l p q) ≠ 0 := by
  rw [supportRay, directionEval_smul, directionEval_lineDirection]
  exact mul_ne_zero (inv_ne_zero hlq) (neg_ne_zero.mpr haq)

/-- Strict transverse order makes the two normalized rays linearly
independent. -/
theorem det2_supportRay_ne_zero_of_rayCoordinate_lt
    {l : Point →L[ℝ] ℝ} {p q r : Point}
    (hl : l ≠ 0)
    (hlq : l (lineDirection p q) ≠ 0)
    (hlr : l (lineDirection p r) ≠ 0)
    (hqr : rayCoordinate l p q < rayCoordinate l p r) :
    det2 (supportRay l p q) (supportRay l p r) ≠ 0 := by
  have hcoord := rayCoordinate_sub_eq_supportSq_mul_cross hlq hlr
  have hK := Erdos957.support_coefficient_sq_pos hl
  have hcross : 0 < Erdos957.crossVec
      (supportRay l p q) (supportRay l p r) := by
    nlinarith
  simpa [det2, Erdos957.crossVec] using hcross.ne'

/-- In any finite linearly ordered family with at least two members and
distinct coordinates, the two smallest members are consecutive. -/
theorem exists_consecutive_of_two_le_card
    {A : Type*} [DecidableEq A] (S : Finset A) (t : A → ℝ)
    (hcard : 2 ≤ S.card) (hinj : Set.InjOn t (S : Set A)) :
    ∃ q ∈ S, ∃ r ∈ S, q ≠ r ∧ t q < t r ∧
      ∀ a ∈ S, ¬ (t q < t a ∧ t a < t r) := by
  classical
  have hS : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    rw [hzero] at hcard
    simp at hcard
  obtain ⟨q, hqS, hqmin⟩ := Finset.exists_min_image S t hS
  have herase : (S.erase q).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hcarderase : (S.erase q).card = 0 := by simp [hempty]
    rw [Finset.card_erase_of_mem hqS] at hcarderase
    omega
  obtain ⟨r, hrErase, hrmin⟩ :=
    Finset.exists_min_image (S.erase q) t herase
  have hrS : r ∈ S := (Finset.mem_erase.mp hrErase).2
  have hqr : q ≠ r := by
    exact Ne.symm (Finset.mem_erase.mp hrErase).1
  have hle : t q ≤ t r := hqmin r hrS
  have hne : t q ≠ t r := by
    intro heq
    exact hqr (hinj hqS hrS heq)
  refine ⟨q, hqS, r, hrS, hqr, lt_of_le_of_ne hle hne, ?_⟩
  intro a haS haBetween
  have haq : a ≠ q := by
    intro haq
    subst a
    exact (lt_irrefl _ haBetween.1)
  have haErase : a ∈ S.erase q := Finset.mem_erase.mpr ⟨haq, haS⟩
  have hra : t r ≤ t a := hrmin a haErase
  exact (not_lt_of_ge hra) haBetween.2

/-- Boolean sign chosen from a nonzero real number. -/
def positiveSign (r : ℝ) : Bool := if 0 < r then true else false

theorem positiveSign_neg_ne {r : ℝ} (hr : r ≠ 0) :
    positiveSign (-r) ≠ positiveSign r := by
  by_cases hpos : 0 < r
  · have hnpos : ¬ 0 < -r := by linarith
    simp [positiveSign, hpos, hnpos]
  · have hneg : r < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hr
    have hnpos : 0 < -r := by linarith
    simp [positiveSign, hpos, hnpos]

theorem signed_positiveSign_pos {r : ℝ} (hr : r ≠ 0) :
    0 < SignVector.signed (positiveSign r) r := by
  by_cases hpos : 0 < r
  · simp [positiveSign, hpos, SignVector.signed]
  · have hneg : r < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hr
    simp [positiveSign, hpos, SignVector.signed, hneg]

theorem signed_positiveSign_pos_iff_mul_pos {r s : ℝ}
    (hr : r ≠ 0) :
    0 < SignVector.signed (positiveSign r) s ↔ 0 < r * s := by
  by_cases hpos : 0 < r
  · simp only [positiveSign, hpos, ↓reduceIte, SignVector.signed]
    constructor
    · exact mul_pos hpos
    · intro hrs
      rcases (mul_pos_iff.mp hrs) with hpp | hnn
      · exact hpp.2
      · linarith
  · have hneg : r < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hr
    simp only [positiveSign, hpos, Bool.false_eq_true, ↓reduceIte,
      SignVector.signed]
    constructor
    · intro hs
      exact mul_pos_of_neg_of_neg hneg (neg_pos.mp hs)
    · intro hrs
      rcases (mul_pos_iff.mp hrs) with hpp | hnn
      · linarith
      · exact neg_pos.mpr hnn.2

theorem signed_positiveSign_nonneg_of_mul_nonneg {r s : ℝ}
    (hrne : r ≠ 0) (hrs : 0 ≤ r * s) :
    0 ≤ SignVector.signed (positiveSign r) s := by
  by_cases hpos : 0 < r
  · simp only [positiveSign, hpos, ↓reduceIte, SignVector.signed]
    by_contra hs
    have : s < 0 := lt_of_not_ge hs
    exact (not_lt_of_ge hrs) (mul_neg_of_pos_of_neg hpos this)
  · simp only [positiveSign, hpos, Bool.false_eq_true, ↓reduceIte,
      SignVector.signed]
    have hr : r ≤ 0 := le_of_not_gt hpos
    by_contra hs
    have : 0 < s := by linarith
    exact (not_lt_of_ge hrs) (mul_neg_of_neg_of_pos
      (lt_of_le_of_ne hr hrne) this)

/-- The strict sign-vector face containing a chart point away from every
arrangement line. -/
noncomputable def affineFace (B : Finset Point) (p : B) (x : Point)
    (hx : ∀ a : B, lineEval p.1 a.1 x ≠ 0) :
    SignVector.StrictFace
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) :=
  ⟨fun a ↦ positiveSign (lineEval p.1 a.1 x), ⟨chartPoint p.1 x, by
    intro a
    rw [normalVec_dot_chartPoint]
    exact signed_positiveSign_pos (hx a)⟩⟩

@[simp] theorem affineFace_sign (B : Finset Point) (p : B) (x : Point)
    (hx : ∀ a : B, lineEval p.1 a.1 x ≠ 0) (a : B) :
    (affineFace B p x hx).1 a = positiveSign (lineEval p.1 a.1 x) := rfl

/-- Equality of three homogeneous covectors can be checked on one affine
chart point and two independent chart directions. -/
theorem vec3_eq_of_dot_chartPoint_and_directions
    {p v u w : Point} {A C : SignVector.Vec3}
    (huw : det2 u w ≠ 0)
    (hv : A ⬝ᵥ chartPoint p v = C ⬝ᵥ chartPoint p v)
    (hu : A ⬝ᵥ chartDirection p u = C ⬝ᵥ chartDirection p u)
    (hw : A ⬝ᵥ chartDirection p w = C ⬝ᵥ chartDirection p w) :
    A = C := by
  let z : SignVector.Vec3 := A - C
  have hvz : z ⬝ᵥ chartPoint p v = 0 := by
    dsimp [z]
    rw [sub_dotProduct]
    linarith
  have huz : z ⬝ᵥ chartDirection p u = 0 := by
    dsimp [z]
    rw [sub_dotProduct]
    linarith
  have hwz : z ⬝ᵥ chartDirection p w = 0 := by
    dsimp [z]
    rw [sub_dotProduct]
    linarith
  have hu' :
      (z 0 - p 0 * z 2) * u 0 + (z 1 - p 1 * z 2) * u 1 = 0 := by
    rw [Matrix.vec3_dotProduct] at huz
    simp [chartDirection] at huz
    linear_combination huz
  have hw' :
      (z 0 - p 0 * z 2) * w 0 + (z 1 - p 1 * z 2) * w 1 = 0 := by
    rw [Matrix.vec3_dotProduct] at hwz
    simp [chartDirection] at hwz
    linear_combination hwz
  have hz₀ : z 0 - p 0 * z 2 = 0 := by
    have hprod : det2 u w * (z 0 - p 0 * z 2) = 0 := by
      dsimp [det2]
      linear_combination w 1 * hu' - u 1 * hw'
    exact (mul_eq_zero.mp hprod).resolve_left huw
  have hz₁ : z 1 - p 1 * z 2 = 0 := by
    have hprod : det2 u w * (z 1 - p 1 * z 2) = 0 := by
      dsimp [det2]
      linear_combination -(w 0) * hu' + u 0 * hw'
    exact (mul_eq_zero.mp hprod).resolve_left huw
  have hz₀eq : z 0 = p 0 * z 2 := sub_eq_zero.mp hz₀
  have hz₁eq : z 1 = p 1 * z 2 := sub_eq_zero.mp hz₁
  have hz₂ : z 2 = 0 := by
    rw [Matrix.vec3_dotProduct] at hvz
    simp [chartPoint] at hvz
    rw [hz₀eq, hz₁eq] at hvz
    linear_combination hvz
  have hz : z = 0 := by
    funext i
    fin_cases i
    · change z 0 = 0
      rw [hz₀eq, hz₂, mul_zero]
    · change z 1 = 0
      rw [hz₁eq, hz₂, mul_zero]
    · exact hz₂
  apply sub_eq_zero.mp
  exact hz

theorem sum_mul_left_pos_of_nonneg_mul
    {A Q R : ℝ} (hA : A ≠ 0) (hAQ : 0 ≤ A * Q) (hAR : 0 ≤ A * R) :
    0 < (A + Q + R) * (A + Q) := by
  have hAsq : 0 < A ^ 2 := sq_pos_of_ne_zero hA
  have hAx : 0 < A * (A + Q + R) := by nlinarith
  have hAy : 0 < A * (A + Q) := by nlinarith
  have hprod : 0 < (A * (A + Q + R)) * (A * (A + Q)) :=
    mul_pos hAx hAy
  have hid : (A * (A + Q + R)) * (A * (A + Q)) =
      A ^ 2 * ((A + Q + R) * (A + Q)) := by ring
  rw [hid] at hprod
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos.2
  · linarith

theorem sum_mul_right_pos_of_nonneg_mul
    {A Q R : ℝ} (hA : A ≠ 0) (hAQ : 0 ≤ A * Q) (hAR : 0 ≤ A * R) :
    0 < (A + Q + R) * (A + R) := by
  have hAsq : 0 < A ^ 2 := sq_pos_of_ne_zero hA
  have hAx : 0 < A * (A + Q + R) := by nlinarith
  have hAy : 0 < A * (A + R) := by nlinarith
  have hprod : 0 < (A * (A + Q + R)) * (A * (A + R)) :=
    mul_pos hAx hAy
  have hid : (A * (A + Q + R)) * (A * (A + R)) =
      A ^ 2 * ((A + Q + R) * (A + R)) := by ring
  rw [hid] at hprod
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos.2
  · linarith

theorem sum_mul_self_pos_of_mul_nonneg_left
    {Q R : ℝ} (hQ : Q ≠ 0) (hQR : 0 ≤ Q * R) :
    0 < (Q + R) * Q := by
  have hQsq : 0 < Q ^ 2 := sq_pos_of_ne_zero hQ
  nlinarith

theorem sum_mul_self_pos_of_mul_nonneg_right
    {Q R : ℝ} (hR : R ≠ 0) (hQR : 0 ≤ Q * R) :
    0 < (Q + R) * R := by
  have hRsq : 0 < R ^ 2 := sq_pos_of_ne_zero hR
  nlinarith

theorem mul_nonneg_of_common_nonzero_factor
    {A Q R : ℝ} (hA : A ≠ 0) (hAQ : 0 ≤ A * Q) (hAR : 0 ≤ A * R) :
    0 ≤ Q * R := by
  have hprod : 0 ≤ (A * Q) * (A * R) := mul_nonneg hAQ hAR
  have hid : (A * Q) * (A * R) = A ^ 2 * (Q * R) := by ring
  rw [hid] at hprod
  have hAsq : 0 < A ^ 2 := sq_pos_of_ne_zero hA
  by_contra hneg
  have hQR : Q * R < 0 := lt_of_not_ge hneg
  have : A ^ 2 * (Q * R) < 0 := mul_neg_of_pos_of_neg hAsq hQR
  linarith

/-- Two independent chart directions determine an affine line covector. -/
theorem coeff_eq_zero_of_directionEval_eq_zero
    {p a u w : Point} (huw : det2 u w ≠ 0)
    (hu : directionEval p a u = 0) (hw : directionEval p a w = 0) :
    coeff p a = 0 := by
  have hu' : coeff p a 0 * u 0 + coeff p a 1 * u 1 = 0 := by
    simpa [directionEval, coeff] using hu
  have hw' : coeff p a 0 * w 0 + coeff p a 1 * w 1 = 0 := by
    simpa [directionEval, coeff] using hw
  have h₀ : coeff p a 0 = 0 := by
    have hprod : det2 u w * coeff p a 0 = 0 := by
      dsimp [det2]
      linear_combination w 1 * hu' - u 1 * hw'
    exact (mul_eq_zero.mp hprod).resolve_left huw
  have h₁ : coeff p a 1 = 0 := by
    have hprod : det2 u w * coeff p a 1 = 0 := by
      dsimp [det2]
      linear_combination -(w 0) * hu' + u 0 * hw'
    exact (mul_eq_zero.mp hprod).resolve_left huw
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h₀
  · exact h₁

section FiniteConfiguration

variable (B : Finset Point)

/-- Lines through the affine arrangement vertex `v`. -/
def incidentLines (p : B) (v : Point) : Finset (OtherPoint B p) := by
  classical
  exact Finset.univ.filter fun q ↦ lineEval p.1 q.1.1 v = 0

@[simp] theorem mem_incidentLines (p : B) (v : Point)
    (q : OtherPoint B p) :
    q ∈ incidentLines B p v ↔ lineEval p.1 q.1.1 v = 0 := by
  classical
  simp [incidentLines]

/-- Two distinct affine lines through one point cannot be parallel. -/
theorem nonparallel_of_mem_incidentLines (p : B) (v : Point)
    {q r : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v) (hqr : q ≠ r) :
    Nonparallel p.1 q.1.1 r.1.1 := by
  intro hdet
  have hqv : lineEval p.1 q.1.1 v = 0 :=
    (mem_incidentLines B p v q).mp hq
  have hrv : lineEval p.1 r.1.1 v = 0 :=
    (mem_incidentLines B p v r).mp hr
  let d := coeff p.1 q.1.1
  let e := coeff p.1 r.1.1
  have hdet' : d 0 * e 1 - d 1 * e 0 = 0 := by
    simpa [Nonparallel, det2, d, e] using hdet
  have hd : d 0 * v 0 + d 1 * v 1 = -1 := by
    dsimp [d, coeff]
    simp [lineEval] at hqv
    linear_combination hqv
  have he : e 0 * v 0 + e 1 * v 1 = -1 := by
    dsimp [e, coeff]
    simp [lineEval] at hrv
    linear_combination hrv
  have hzero : d = e := by
    apply PiLp.ext
    intro i
    fin_cases i
    · change d 0 = e 0
      linear_combination d 0 * he - e 0 * hd - v 1 * hdet'
    · change d 1 = e 1
      linear_combination d 1 * he - e 1 * hd + v 0 * hdet'
  apply hqr
  apply Subtype.ext
  apply Subtype.ext
  exact coeff_injective p.1 hzero

/-- Every recorded affine crossing has at least two incident lines. -/
theorem two_le_incidentLines_card (p : B) {v : Point}
    (hv : v ∈ vertexFinset B p) :
    2 ≤ (incidentLines B p v).card := by
  obtain ⟨qr, hqrv⟩ := (mem_vertexFinset B p v).mp hv
  let q : OtherPoint B p := qr.1.1
  let r : OtherPoint B p := qr.1.2
  have hq : q ∈ incidentLines B p v := by
    rw [mem_incidentLines]
    rw [← hqrv]
    exact indexedCrossing_on_left B p qr
  have hr : r ∈ incidentLines B p v := by
    rw [mem_incidentLines]
    rw [← hqrv]
    exact indexedCrossing_on_right B p qr
  have hqr : q ≠ r := by
    intro heq
    have hnp : Nonparallel p.1 q.1.1 r.1.1 := qr.2
    apply hnp
    have hval : q.1.1 = r.1.1 :=
      congrArg (fun z : OtherPoint B p ↦ z.1.1) heq
    rw [hval]
    simp [det2]
    ring
  have hsub : ({q, r} : Finset (OtherPoint B p)) ⊆ incidentLines B p v := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hq
    · exact hr
  have hcard := Finset.card_le_card hsub
  simpa [hqr] using hcard

/-- Normalized exterior-ray coordinates distinguish the different lines
through a fixed affine crossing. -/
theorem rayCoordinate_injective_on_incidentLines
    (p : B) (v : Point) (l : Point →L[ℝ] ℝ)
    (hl : ∀ q ∈ incidentLines B p v,
      l (lineDirection p.1 q.1.1) ≠ 0) :
    Set.InjOn (fun q : OtherPoint B p ↦
      rayCoordinate l p.1 q.1.1) (incidentLines B p v : Set _) := by
  intro q hq r hr hcoord
  have hlq := hl q hq
  have hlr := hl r hr
  have hpair :
      (l (supportRay l p.1 q.1.1),
        Erdos957.quarterTurnFunctional l (supportRay l p.1 q.1.1)) =
      (l (supportRay l p.1 r.1.1),
        Erdos957.quarterTurnFunctional l (supportRay l p.1 r.1.1)) := by
    rw [supportRay_support hlq, supportRay_support hlr]
    exact Prod.ext rfl hcoord
  have hlne : l ≠ 0 := by
    intro hlzero
    have := congrArg (fun g : Point →L[ℝ] ℝ ↦
      g (lineDirection p.1 q.1.1)) hlzero
    exact hlq (by simpa using this)
  have hray : supportRay l p.1 q.1.1 =
      supportRay l p.1 r.1.1 :=
    supportCoordinate_injective hlne hpair
  by_contra hqr
  have hnp := nonparallel_of_mem_incidentLines B p v hq hr hqr
  apply hnp
  have hzero : directionEval p.1 q.1.1
      (supportRay l p.1 r.1.1) = 0 := by
    rw [← hray]
    exact directionEval_supportRay_self l p.1 q.1.1
  rw [supportRay, directionEval_smul, directionEval_lineDirection] at hzero
  have hinv : (l (lineDirection p.1 r.1.1))⁻¹ ≠ 0 := inv_ne_zero hlr
  exact neg_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hinv)

/-- At every affine crossing, a generic support functional supplies two
consecutive incident rays in its positive half-plane. -/
theorem exists_consecutive_incident_rays
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hl : ∀ q ∈ incidentLines B p v,
      l (lineDirection p.1 q.1.1) ≠ 0) :
    ∃ q ∈ incidentLines B p v, ∃ r ∈ incidentLines B p v,
      q ≠ r ∧
      rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1 ∧
      ∀ a ∈ incidentLines B p v,
        ¬ (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
          rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1) := by
  exact exists_consecutive_of_two_le_card
    (incidentLines B p v) (fun q ↦ rayCoordinate l p.1 q.1.1)
    (two_le_incidentLines_card B p hv)
    (rayCoordinate_injective_on_incidentLines B p v l hl)

/-- Any incident line has the same weak sign on two consecutive normalized
rays.  In support/transverse coordinates this is the elementary fact that
`(t_a-t_q)(t_a-t_r) ≥ 0` when `t_a` is not strictly between `t_q` and
`t_r`. -/
theorem directionEval_mul_nonneg_of_consecutive_incident_rays
    (p : B) (v : Point) (l : Point →L[ℝ] ℝ)
    {q r a : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v)
    (ha : a ∈ incidentLines B p v)
    (hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0)
    (hqr : rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1)
    (hbetween : ¬
      (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
       rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1)) :
    0 ≤ directionEval p.1 a.1.1 (supportRay l p.1 q.1.1) *
      directionEval p.1 a.1.1 (supportRay l p.1 r.1.1) := by
  have hla := hl a ha
  have hlq := hl q hq
  have hlr := hl r hr
  have hlne : l ≠ 0 := by
    intro hlzero
    have hz := congrArg (fun g : Point →L[ℝ] ℝ ↦
      g (lineDirection p.1 q.1.1)) hlzero
    exact hlq (by simpa using hz)
  let K : ℝ := l (Erdos957.planeBasisVector 0) ^ 2 +
    l (Erdos957.planeBasisVector 1) ^ 2
  let A : ℝ := directionEval p.1 a.1.1 (supportRay l p.1 q.1.1)
  let C : ℝ := directionEval p.1 a.1.1 (supportRay l p.1 r.1.1)
  let c : ℝ := l (lineDirection p.1 a.1.1)
  let ta : ℝ := rayCoordinate l p.1 a.1.1
  let tq : ℝ := rayCoordinate l p.1 q.1.1
  let tr : ℝ := rayCoordinate l p.1 r.1.1
  have hKA : K * A = c * (ta - tq) := by
    exact supportSq_mul_directionEval_supportRay hla hlq
  have hKC : K * C = c * (ta - tr) := by
    exact supportSq_mul_directionEval_supportRay hla hlr
  have hcoord : 0 ≤ (ta - tq) * (ta - tr) := by
    by_cases hatq : ta ≤ tq
    · have hatr : ta ≤ tr := hatq.trans hqr.le
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hatq)
        (sub_nonpos.mpr hatr)
    · have htqa : tq < ta := lt_of_not_ge hatq
      have hrta : tr ≤ ta := by
        by_contra hnot
        exact hbetween ⟨htqa, lt_of_not_ge hnot⟩
      exact mul_nonneg (sub_nonneg.mpr htqa.le) (sub_nonneg.mpr hrta)
  have hK : 0 < K := Erdos957.support_coefficient_sq_pos hlne
  have hidentity : K ^ 2 * (A * C) = c ^ 2 * ((ta - tq) * (ta - tr)) := by
    calc
      K ^ 2 * (A * C) = (K * A) * (K * C) := by ring
      _ = (c * (ta - tq)) * (c * (ta - tr)) := by rw [hKA, hKC]
      _ = c ^ 2 * ((ta - tq) * (ta - tr)) := by ring
  have hright : 0 ≤ c ^ 2 * ((ta - tq) * (ta - tr)) :=
    mul_nonneg (sq_nonneg c) hcoord
  have hKsq : 0 < K ^ 2 := sq_pos_of_pos hK
  dsimp [A, C] at hidentity ⊢
  nlinarith

/-- No line other than the ray's owner can meet a positive normalized ray
from a strictly supported arrangement vertex.  Otherwise that meeting would
be another arrangement vertex beyond the strict supporting line. -/
theorem lineEval_ne_zero_on_positive_incident_ray_smul
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q a : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hlq : l (lineDirection p.1 q.1.1) ≠ 0) (haq : a ≠ q)
    {t : ℝ} (ht : 0 < t) :
    lineEval p.1 a.1.1 (v + t • supportRay l p.1 q.1.1) ≠ 0 := by
  intro hazero
  let y : Point := v + t • supportRay l p.1 q.1.1
  have hqv := (mem_incidentLines B p v q).mp hq
  have hqzero : lineEval p.1 q.1.1 y = 0 := by
    dsimp [y]
    rw [lineEval_add_smul, hqv, directionEval_supportRay_self,
      mul_zero, zero_add]
  have hqy : q ∈ incidentLines B p y :=
    (mem_incidentLines B p y q).mpr hqzero
  have hay : a ∈ incidentLines B p y :=
    (mem_incidentLines B p y a).mpr (by simpa [y] using hazero)
  have hnp : Nonparallel p.1 q.1.1 a.1.1 :=
    nonparallel_of_mem_incidentLines B p y hqy hay (Ne.symm haq)
  let qa : CrossingPair B p := ⟨(q, a), hnp⟩
  have hcross : indexedCrossing B p qa = y := by
    exact crossing_eq_of_lineEval_eq_zero hnp hqzero
      (by simpa [y] using hazero)
  have hyV : y ∈ vertexFinset B p := by
    rw [← hcross]
    exact indexedCrossing_mem B p qa
  have hly : l y = l v + t := by
    dsimp [y]
    rw [map_add, map_smul, supportRay_support hlq]
    simp only [smul_eq_mul, mul_one]
  have hyv : y ≠ v := by
    intro hyv
    rw [hyv] at hly
    linarith
  have := hstrict y hyV hyv
  linarith

/-- The unit-parameter specialization of the preceding ray obstruction. -/
theorem lineEval_ne_zero_on_positive_incident_ray
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q a : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hlq : l (lineDirection p.1 q.1.1) ≠ 0) (haq : a ≠ q) :
    lineEval p.1 a.1.1 (v + supportRay l p.1 q.1.1) ≠ 0 := by
  simpa using lineEval_ne_zero_on_positive_incident_ray_smul B p hv l
    hstrict hq hlq haq (t := 1) zero_lt_one

/-- A nonincident affine line and its directional derivative along an
exterior incident ray have weakly equal signs.  Opposite signs would force a
positive-parameter zero, which the strict support obstruction excludes. -/
theorem lineEval_mul_directionEval_nonneg_of_not_incident
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q a : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hlq : l (lineDirection p.1 q.1.1) ≠ 0)
    (ha : a ∉ incidentLines B p v) :
    0 ≤ lineEval p.1 a.1.1 v *
      directionEval p.1 a.1.1 (supportRay l p.1 q.1.1) := by
  have ha0 : lineEval p.1 a.1.1 v ≠ 0 := by
    simpa [mem_incidentLines] using ha
  by_contra hneg
  have hprod : lineEval p.1 a.1.1 v *
      directionEval p.1 a.1.1 (supportRay l p.1 q.1.1) < 0 :=
    lt_of_not_ge hneg
  have hdir : directionEval p.1 a.1.1
      (supportRay l p.1 q.1.1) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hprod
    linarith
  let t : ℝ := -(lineEval p.1 a.1.1 v) /
    directionEval p.1 a.1.1 (supportRay l p.1 q.1.1)
  have ht : 0 < t := by
    dsimp [t]
    rcases (mul_neg_iff.mp hprod) with hcase | hcase
    · exact div_pos_of_neg_of_neg (neg_neg_of_pos hcase.1) hcase.2
    · exact div_pos (neg_pos.mpr hcase.1) hcase.2
  have hzero : lineEval p.1 a.1.1
      (v + t • supportRay l p.1 q.1.1) = 0 := by
    rw [lineEval_add_smul]
    dsimp [t]
    field_simp [hdir]
    ring
  have haq : a ≠ q := by
    intro haq
    subst a
    exact ha hq
  exact lineEval_ne_zero_on_positive_incident_ray_smul B p hv l
    hstrict hq hlq haq ht hzero

/-- The point obtained by moving from a strictly exposed crossing into a
sector between consecutive incident rays lies on no arrangement line. -/
theorem lineEval_ne_zero_at_consecutive_exterior_sector
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q r : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v) (hqr : q ≠ r)
    (hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0)
    (hcoord : rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1)
    (hbetween : ∀ a ∈ incidentLines B p v,
      ¬ (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
        rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1)) :
    ∀ a : B, lineEval p.1 a.1
      (v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1) ≠ 0 := by
  intro a
  by_cases hap : a = p
  · subst a
    simp [lineEval]
  let oa : OtherPoint B p := ⟨a, hap⟩
  let uq := supportRay l p.1 q.1.1
  let ur := supportRay l p.1 r.1.1
  let A := lineEval p.1 a.1 v
  let Q := directionEval p.1 a.1 uq
  let R := directionEval p.1 a.1 ur
  have heval : lineEval p.1 a.1 (v + uq + ur) = A + Q + R := by
    simp [A, Q, R, uq, ur, lineEval, directionEval]
    ring
  by_cases haInc : oa ∈ incidentLines B p v
  · have hA : A = 0 := by
      exact (mem_incidentLines B p v oa).mp haInc
    by_cases haq : oa = q
    · have haeq : a = q.1 := by
        exact congrArg (fun z : OtherPoint B p ↦ z.1) haq
      subst a
      have hQ : Q = 0 := by
        exact directionEval_supportRay_self l p.1 q.1.1
      have hnp := nonparallel_of_mem_incidentLines B p v hq hr hqr
      have hR : R ≠ 0 :=
        directionEval_supportRay_ne_zero_of_nonparallel hnp (hl r hr)
      rw [heval, hA, hQ, zero_add, zero_add]
      exact hR
    by_cases har : oa = r
    · have haeq : a = r.1 := by
        exact congrArg (fun z : OtherPoint B p ↦ z.1) har
      subst a
      have hR : R = 0 := by
        exact directionEval_supportRay_self l p.1 r.1.1
      have hnp := nonparallel_of_mem_incidentLines B p v hr hq (Ne.symm hqr)
      have hQ : Q ≠ 0 :=
        directionEval_supportRay_ne_zero_of_nonparallel hnp (hl q hq)
      rw [heval, hA, hR, zero_add, add_zero]
      exact hQ
    · have hnpQ := nonparallel_of_mem_incidentLines B p v haInc hq haq
      have hnpR := nonparallel_of_mem_incidentLines B p v haInc hr har
      have hQ : Q ≠ 0 :=
        directionEval_supportRay_ne_zero_of_nonparallel hnpQ (hl q hq)
      have hR : R ≠ 0 :=
        directionEval_supportRay_ne_zero_of_nonparallel hnpR (hl r hr)
      have hQR : 0 ≤ Q * R :=
        directionEval_mul_nonneg_of_consecutive_incident_rays B p v l
          hq hr haInc hl hcoord (hbetween oa haInc)
      rw [heval, hA, zero_add]
      intro hsum
      have hQsq : 0 < Q ^ 2 := sq_pos_of_ne_zero hQ
      have hReq : R = -Q := by linarith
      rw [hReq] at hQR
      nlinarith
  · have hA : A ≠ 0 := by
      simpa [A, mem_incidentLines] using haInc
    have hAQ : 0 ≤ A * Q := by
      exact lineEval_mul_directionEval_nonneg_of_not_incident B p hv l
        hstrict hq (hl q hq) haInc
    have hAR : 0 ≤ A * R := by
      exact lineEval_mul_directionEval_nonneg_of_not_incident B p hv l
        hstrict hr (hl r hr) haInc
    rw [heval]
    intro hsum
    have hAsq : 0 < A ^ 2 := sq_pos_of_ne_zero hA
    have htotal : A ^ 2 + A * Q + A * R = 0 := by
      linear_combination A * hsum
    nlinarith

/-- The interior line value has nonnegative product with the value at the
supporting vertex and with both exterior directional derivatives.  After
orienting by the interior sign, these are precisely the three nonnegative
coordinates used in the wall-normal cone decomposition. -/
theorem exteriorSector_oriented_coordinate_products_nonneg
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q r : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v)
    (hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0)
    (hcoord : rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1)
    (hbetween : ∀ a ∈ incidentLines B p v,
      ¬ (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
        rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1))
    (a : B) :
    let uq := supportRay l p.1 q.1.1
    let ur := supportRay l p.1 r.1.1
    let X := lineEval p.1 a.1 (v + uq + ur)
    0 ≤ X * lineEval p.1 a.1 v ∧
      0 ≤ X * directionEval p.1 a.1 uq ∧
      0 ≤ X * directionEval p.1 a.1 ur := by
  dsimp only
  by_cases hap : a = p
  · subst a
    simp [lineEval, directionEval]
  let oa : OtherPoint B p := ⟨a, hap⟩
  let uq := supportRay l p.1 q.1.1
  let ur := supportRay l p.1 r.1.1
  let A := lineEval p.1 a.1 v
  let Q := directionEval p.1 a.1 uq
  let R := directionEval p.1 a.1 ur
  let X := lineEval p.1 a.1 (v + uq + ur)
  have hX : X = A + Q + R := by
    simp [X, A, Q, R, uq, ur, lineEval, directionEval]
    ring
  change 0 ≤ X * A ∧ 0 ≤ X * Q ∧ 0 ≤ X * R
  by_cases haInc : oa ∈ incidentLines B p v
  · have hA : A = 0 := (mem_incidentLines B p v oa).mp haInc
    have hQR : 0 ≤ Q * R :=
      directionEval_mul_nonneg_of_consecutive_incident_rays B p v l
        hq hr haInc hl hcoord (hbetween oa haInc)
    rw [hX, hA]
    constructor
    · ring_nf
      exact le_rfl
    constructor <;> nlinarith [sq_nonneg Q, sq_nonneg R]
  · have hA : A ≠ 0 := by
      simpa [A, mem_incidentLines] using haInc
    have hAQ : 0 ≤ A * Q :=
      lineEval_mul_directionEval_nonneg_of_not_incident B p hv l hstrict
        hq (hl q hq) haInc
    have hAR : 0 ≤ A * R :=
      lineEval_mul_directionEval_nonneg_of_not_incident B p hv l hstrict
        hr (hl r hr) haInc
    have hQR : 0 ≤ Q * R :=
      mul_nonneg_of_common_nonzero_factor hA hAQ hAR
    rw [hX]
    constructor
    · nlinarith [sq_nonneg A]
    constructor <;> nlinarith [sq_nonneg Q, sq_nonneg R]

/-- Every line other than the first wall has the same strict sign at the
sector interior and on that wall ray. -/
theorem lineEval_mul_lineEval_qWall_pos
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q r : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v) (hqr : q ≠ r)
    (hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0)
    (hcoord : rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1)
    (hbetween : ∀ a ∈ incidentLines B p v,
      ¬ (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
        rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1))
    (a : B) (haq : a ≠ q.1) :
    0 < lineEval p.1 a.1
        (v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1) *
      lineEval p.1 a.1 (v + supportRay l p.1 q.1.1) := by
  by_cases hap : a = p
  · subst a
    norm_num [lineEval]
  let oa : OtherPoint B p := ⟨a, hap⟩
  let uq := supportRay l p.1 q.1.1
  let ur := supportRay l p.1 r.1.1
  let A := lineEval p.1 a.1 v
  let Q := directionEval p.1 a.1 uq
  let R := directionEval p.1 a.1 ur
  have hx : lineEval p.1 a.1 (v + uq + ur) = A + Q + R := by
    simp [A, Q, R, uq, ur, lineEval, directionEval]
    ring
  have hy : lineEval p.1 a.1 (v + uq) = A + Q := by
    simp [A, Q, uq, lineEval, directionEval]
    ring
  by_cases haInc : oa ∈ incidentLines B p v
  · have hA : A = 0 := (mem_incidentLines B p v oa).mp haInc
    have hoaq : oa ≠ q := by
      intro h
      apply haq
      exact congrArg (fun z : OtherPoint B p ↦ z.1) h
    have hnpQ := nonparallel_of_mem_incidentLines B p v haInc hq hoaq
    have hQ : Q ≠ 0 :=
      directionEval_supportRay_ne_zero_of_nonparallel hnpQ (hl q hq)
    have hQR : 0 ≤ Q * R :=
      directionEval_mul_nonneg_of_consecutive_incident_rays B p v l
        hq hr haInc hl hcoord (hbetween oa haInc)
    rw [hx, hy]
    simpa [hA] using sum_mul_self_pos_of_mul_nonneg_left hQ hQR
  · have hA : A ≠ 0 := by
      simpa [A, mem_incidentLines] using haInc
    have hAQ : 0 ≤ A * Q :=
      lineEval_mul_directionEval_nonneg_of_not_incident B p hv l hstrict
        hq (hl q hq) haInc
    have hAR : 0 ≤ A * R :=
      lineEval_mul_directionEval_nonneg_of_not_incident B p hv l hstrict
        hr (hl r hr) haInc
    rw [hx, hy]
    exact sum_mul_left_pos_of_nonneg_mul hA hAQ hAR

/-- Symmetric strict-sign agreement on the second wall. -/
theorem lineEval_mul_lineEval_rWall_pos
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q r : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v) (hqr : q ≠ r)
    (hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0)
    (hcoord : rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1)
    (hbetween : ∀ a ∈ incidentLines B p v,
      ¬ (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
        rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1))
    (a : B) (har : a ≠ r.1) :
    0 < lineEval p.1 a.1
        (v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1) *
      lineEval p.1 a.1 (v + supportRay l p.1 r.1.1) := by
  by_cases hap : a = p
  · subst a
    norm_num [lineEval]
  let oa : OtherPoint B p := ⟨a, hap⟩
  let uq := supportRay l p.1 q.1.1
  let ur := supportRay l p.1 r.1.1
  let A := lineEval p.1 a.1 v
  let Q := directionEval p.1 a.1 uq
  let R := directionEval p.1 a.1 ur
  have hx : lineEval p.1 a.1 (v + uq + ur) = A + Q + R := by
    simp [A, Q, R, uq, ur, lineEval, directionEval]
    ring
  have hy : lineEval p.1 a.1 (v + ur) = A + R := by
    simp [A, R, ur, lineEval, directionEval]
    ring
  by_cases haInc : oa ∈ incidentLines B p v
  · have hA : A = 0 := (mem_incidentLines B p v oa).mp haInc
    have hoar : oa ≠ r := by
      intro h
      apply har
      exact congrArg (fun z : OtherPoint B p ↦ z.1) h
    have hnpR := nonparallel_of_mem_incidentLines B p v haInc hr hoar
    have hR : R ≠ 0 :=
      directionEval_supportRay_ne_zero_of_nonparallel hnpR (hl r hr)
    have hQR : 0 ≤ Q * R :=
      directionEval_mul_nonneg_of_consecutive_incident_rays B p v l
        hq hr haInc hl hcoord (hbetween oa haInc)
    rw [hx, hy]
    simpa [hA] using sum_mul_self_pos_of_mul_nonneg_right hR hQR
  · have hA : A ≠ 0 := by
      simpa [A, mem_incidentLines] using haInc
    have hAQ : 0 ≤ A * Q :=
      lineEval_mul_directionEval_nonneg_of_not_incident B p hv l hstrict
        hq (hl q hq) haInc
    have hAR : 0 ≤ A * R :=
      lineEval_mul_directionEval_nonneg_of_not_incident B p hv l hstrict
        hr (hl r hr) haInc
    rw [hx, hy]
    exact sum_mul_right_pos_of_nonneg_mul hA hAQ hAR

/-- Every nonselected line has the same strict sign at the sector interior
and at the corresponding point at infinity.  This supplies the open edge on
the selected projective line. -/
theorem lineEval_mul_directionEval_infinity_pos
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q r : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v) (hqr : q ≠ r)
    (hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0)
    (hcoord : rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1)
    (hbetween : ∀ a ∈ incidentLines B p v,
      ¬ (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
        rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1))
    (a : B) (hap : a ≠ p) :
    0 < lineEval p.1 a.1
        (v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1) *
      directionEval p.1 a.1
        (supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1) := by
  let oa : OtherPoint B p := ⟨a, hap⟩
  let uq := supportRay l p.1 q.1.1
  let ur := supportRay l p.1 r.1.1
  let A := lineEval p.1 a.1 v
  let Q := directionEval p.1 a.1 uq
  let R := directionEval p.1 a.1 ur
  have hx : lineEval p.1 a.1 (v + uq + ur) = A + Q + R := by
    simp [A, Q, R, uq, ur, lineEval, directionEval]
    ring
  have hy : directionEval p.1 a.1 (uq + ur) = Q + R := by
    rw [directionEval_add]
  have hlne : l ≠ 0 := by
    intro hlzero
    have hz := congrArg (fun g : Point →L[ℝ] ℝ ↦
      g (lineDirection p.1 q.1.1)) hlzero
    exact (hl q hq) (by simpa using hz)
  have huray : det2 uq ur ≠ 0 := by
    exact det2_supportRay_ne_zero_of_rayCoordinate_lt hlne
      (hl q hq) (hl r hr) hcoord
  by_cases haInc : oa ∈ incidentLines B p v
  · have hA : A = 0 := (mem_incidentLines B p v oa).mp haInc
    have hInterior := lineEval_ne_zero_at_consecutive_exterior_sector
      B p hv l hstrict hq hr hqr hl hcoord hbetween a
    have hsum : Q + R ≠ 0 := by
      intro hs
      apply hInterior
      rw [hx, hA, zero_add, hs]
    rw [hx, hy, hA, zero_add]
    nlinarith [sq_pos_of_ne_zero hsum]
  · have hA : A ≠ 0 := by
      simpa [A, mem_incidentLines] using haInc
    have hAQ : 0 ≤ A * Q :=
      lineEval_mul_directionEval_nonneg_of_not_incident B p hv l hstrict
        hq (hl q hq) haInc
    have hAR : 0 ≤ A * R :=
      lineEval_mul_directionEval_nonneg_of_not_incident B p hv l hstrict
        hr (hl r hr) haInc
    have hAsq : 0 < A ^ 2 := sq_pos_of_ne_zero hA
    have hQR : 0 ≤ Q * R := by
      have hprod : 0 ≤ (A * Q) * (A * R) := mul_nonneg hAQ hAR
      have hid : (A * Q) * (A * R) = A ^ 2 * (Q * R) := by ring
      rw [hid] at hprod
      by_contra hneg
      have : Q * R < 0 := lt_of_not_ge hneg
      have : A ^ 2 * (Q * R) < 0 := mul_neg_of_pos_of_neg hAsq this
      linarith
    have hsum : Q + R ≠ 0 := by
      intro hs
      have hQzero : Q = 0 := by
        have hReq : R = -Q := by linarith
        rw [hReq] at hQR
        nlinarith [sq_nonneg Q]
      have hRzero : R = 0 := by linarith
      have hcoeffzero : coeff p.1 a.1 = 0 :=
        coeff_eq_zero_of_directionEval_eq_zero huray hQzero hRzero
      exact coeff_ne_zero (by
        intro h
        apply hap
        exact Subtype.ext h.symm) hcoeffzero
    have hAS : 0 ≤ A * (Q + R) := by nlinarith
    have hASne : A * (Q + R) ≠ 0 := mul_ne_zero hA hsum
    have hASpos : 0 < A * (Q + R) :=
      lt_of_le_of_ne hAS (Ne.symm hASne)
    rw [hx, hy]
    nlinarith [sq_pos_of_ne_zero hsum]

/-- The three walls of a consecutive exterior sector are feasible strict
edges of its sign-vector face: the selected line at infinity and the two
incident affine lines. -/
theorem exteriorSector_three_wallFeasible
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q r : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v) (hqr : q ≠ r)
    (hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0)
    (hcoord : rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1)
    (hbetween : ∀ a ∈ incidentLines B p v,
      ¬ (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
        rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1))
    (hx : ∀ a : B, lineEval p.1 a.1
      (v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1) ≠ 0) :
    let x := v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1
    let n := fun a : B ↦ ProjectiveArrangement.normalVec a.1
    let f := affineFace B p x hx
    SignVector.EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 p) ∧
      SignVector.EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 q.1) ∧
      SignVector.EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 r.1) := by
  dsimp only
  let x := v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1
  let f := affineFace B p x hx
  have hpEdge : SignVector.EdgeFeasible
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1)
      (SignVector.PolarFace.faceEdgeCode f.1 p) := by
    refine ⟨chartDirection p.1
      (supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1), ?_, ?_⟩
    · intro a
      change 0 < SignVector.signed (f.1 a.1)
        (ProjectiveArrangement.normalVec a.1.1 ⬝ᵥ
          chartDirection p.1
            (supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1))
      rw [normalVec_dot_chartDirection]
      change 0 < SignVector.signed (positiveSign
        (lineEval p.1 a.1.1 x)) _
      rw [signed_positiveSign_pos_iff_mul_pos (hx a.1)]
      exact lineEval_mul_directionEval_infinity_pos B p hv l hstrict
        hq hr hqr hl hcoord hbetween a.1 a.2
    · exact selected_dot_chartDirection p.1 _
  have hqEdge : SignVector.EdgeFeasible
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1)
      (SignVector.PolarFace.faceEdgeCode f.1 q.1) := by
    refine ⟨chartPoint p.1 (v + supportRay l p.1 q.1.1), ?_, ?_⟩
    · intro a
      change 0 < SignVector.signed (f.1 a.1)
        (ProjectiveArrangement.normalVec a.1.1 ⬝ᵥ
          chartPoint p.1 (v + supportRay l p.1 q.1.1))
      rw [normalVec_dot_chartPoint]
      change 0 < SignVector.signed (positiveSign
        (lineEval p.1 a.1.1 x)) _
      rw [signed_positiveSign_pos_iff_mul_pos (hx a.1)]
      exact lineEval_mul_lineEval_qWall_pos B p hv l hstrict
        hq hr hqr hl hcoord hbetween a.1 a.2
    · have hqv := (mem_incidentLines B p v q).mp hq
      change ProjectiveArrangement.normalVec q.1.1 ⬝ᵥ
        chartPoint p.1 (v + supportRay l p.1 q.1.1) = 0
      rw [normalVec_dot_chartPoint, lineEval_add, hqv,
        directionEval_supportRay_self, zero_add]
  have hrEdge : SignVector.EdgeFeasible
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1)
      (SignVector.PolarFace.faceEdgeCode f.1 r.1) := by
    refine ⟨chartPoint p.1 (v + supportRay l p.1 r.1.1), ?_, ?_⟩
    · intro a
      change 0 < SignVector.signed (f.1 a.1)
        (ProjectiveArrangement.normalVec a.1.1 ⬝ᵥ
          chartPoint p.1 (v + supportRay l p.1 r.1.1))
      rw [normalVec_dot_chartPoint]
      change 0 < SignVector.signed (positiveSign
        (lineEval p.1 a.1.1 x)) _
      rw [signed_positiveSign_pos_iff_mul_pos (hx a.1)]
      exact lineEval_mul_lineEval_rWall_pos B p hv l hstrict
        hq hr hqr hl hcoord hbetween a.1 a.2
    · have hrv := (mem_incidentLines B p v r).mp hr
      change ProjectiveArrangement.normalVec r.1.1 ⬝ᵥ
        chartPoint p.1 (v + supportRay l p.1 r.1.1) = 0
      rw [normalVec_dot_chartPoint, lineEval_add, hrv,
        directionEval_supportRay_self, zero_add]
  exact ⟨hpEdge, hqEdge, hrEdge⟩

/-- All face-oriented normals lie in the nonnegative cone generated by the
selected line and the two walls of a consecutive exterior sector. -/
theorem exteriorSector_orientedCone
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q r : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v)
    (hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0)
    (hcoord : rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1)
    (hbetween : ∀ a ∈ incidentLines B p v,
      ¬ (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
        rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1))
    (hx : ∀ a : B, lineEval p.1 a.1
      (v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1) ≠ 0) :
    let x := v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1
    let n := fun a : B ↦ ProjectiveArrangement.normalVec a.1
    let f := affineFace B p x hx
    ∀ a : B, ∃ α β γ : ℝ,
      0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧
      SignVector.PolarFace.orientedNormal n f.1 a =
        α • SignVector.PolarFace.orientedNormal n f.1 p +
        β • SignVector.PolarFace.orientedNormal n f.1 q.1 +
        γ • SignVector.PolarFace.orientedNormal n f.1 r.1 := by
  dsimp only
  let uq := supportRay l p.1 q.1.1
  let ur := supportRay l p.1 r.1.1
  let x := v + uq + ur
  let n := fun a : B ↦ ProjectiveArrangement.normalVec a.1
  let f := affineFace B p x hx
  let N := SignVector.PolarFace.orientedNormal n f.1
  have hlne : l ≠ 0 := by
    intro hlzero
    have hz := congrArg (fun g : Point →L[ℝ] ℝ ↦
      g (lineDirection p.1 q.1.1)) hlzero
    exact (hl q hq) (by simpa using hz)
  have huray : det2 uq ur ≠ 0 :=
    det2_supportRay_ne_zero_of_rayCoordinate_lt hlne
      (hl q hq) (hl r hr) hcoord
  have hqv := (mem_incidentLines B p v q).mp hq
  have hrv := (mem_incidentLines B p v r).mp hr
  have hNp : N p = ProjectiveArrangement.normalVec p.1 := by
    simp [N, n, f, affineFace, positiveSign, x, uq, ur, lineEval,
      SignVector.PolarFace.orientedNormal, SignVector.PolarFace.signScalar]
  have hNqv : N q.1 ⬝ᵥ chartPoint p.1 v = 0 := by
    rw [SignVector.PolarFace.orientedNormal_dot, normalVec_dot_chartPoint, hqv]
    simp [SignVector.signed]
  have hNrv : N r.1 ⬝ᵥ chartPoint p.1 v = 0 := by
    rw [SignVector.PolarFace.orientedNormal_dot, normalVec_dot_chartPoint, hrv]
    simp [SignVector.signed]
  have hNqu : N q.1 ⬝ᵥ chartDirection p.1 uq = 0 := by
    rw [SignVector.PolarFace.orientedNormal_dot, normalVec_dot_chartDirection]
    change SignVector.signed (f.1 q.1) (directionEval p.1 q.1.1 uq) = 0
    rw [directionEval_supportRay_self]
    cases f.1 q.1 <;> simp [SignVector.signed]
  have hNrw : N r.1 ⬝ᵥ chartDirection p.1 ur = 0 := by
    rw [SignVector.PolarFace.orientedNormal_dot, normalVec_dot_chartDirection]
    change SignVector.signed (f.1 r.1) (directionEval p.1 r.1.1 ur) = 0
    rw [directionEval_supportRay_self]
    cases f.1 r.1 <;> simp [SignVector.signed]
  let Dq := N q.1 ⬝ᵥ chartDirection p.1 ur
  let Dr := N r.1 ⬝ᵥ chartDirection p.1 uq
  have hDq : 0 < Dq := by
    change 0 < N q.1 ⬝ᵥ chartDirection p.1 ur
    rw [SignVector.PolarFace.orientedNormal_dot,
      normalVec_dot_chartDirection]
    change 0 < SignVector.signed (positiveSign
      (lineEval p.1 q.1.1 x)) (directionEval p.1 q.1.1 ur)
    have heq : lineEval p.1 q.1.1 x = directionEval p.1 q.1.1 ur := by
      dsimp [x]
      rw [lineEval_add, lineEval_add, hqv,
        directionEval_supportRay_self, zero_add, zero_add]
    rw [← heq]
    exact signed_positiveSign_pos (hx q.1)
  have hDr : 0 < Dr := by
    change 0 < N r.1 ⬝ᵥ chartDirection p.1 uq
    rw [SignVector.PolarFace.orientedNormal_dot,
      normalVec_dot_chartDirection]
    change 0 < SignVector.signed (positiveSign
      (lineEval p.1 r.1.1 x)) (directionEval p.1 r.1.1 uq)
    have heq : lineEval p.1 r.1.1 x = directionEval p.1 r.1.1 uq := by
      dsimp [x]
      rw [lineEval_add, lineEval_add, hrv,
        directionEval_supportRay_self, add_zero, zero_add]
    rw [← heq]
    exact signed_positiveSign_pos (hx r.1)
  intro a
  let α := N a ⬝ᵥ chartPoint p.1 v
  let β := (N a ⬝ᵥ chartDirection p.1 ur) / Dq
  let γ := (N a ⬝ᵥ chartDirection p.1 uq) / Dr
  have hproducts := exteriorSector_oriented_coordinate_products_nonneg
    B p hv l hstrict hq hr hl hcoord hbetween a
  have hα : 0 ≤ α := by
    change 0 ≤ N a ⬝ᵥ chartPoint p.1 v
    rw [SignVector.PolarFace.orientedNormal_dot, normalVec_dot_chartPoint]
    change 0 ≤ SignVector.signed (positiveSign
      (lineEval p.1 a.1 x)) (lineEval p.1 a.1 v)
    exact signed_positiveSign_nonneg_of_mul_nonneg (hx a) hproducts.1
  have hNu : 0 ≤ N a ⬝ᵥ chartDirection p.1 uq := by
    rw [SignVector.PolarFace.orientedNormal_dot, normalVec_dot_chartDirection]
    change 0 ≤ SignVector.signed (positiveSign
      (lineEval p.1 a.1 x)) (directionEval p.1 a.1 uq)
    exact signed_positiveSign_nonneg_of_mul_nonneg (hx a) hproducts.2.1
  have hNw : 0 ≤ N a ⬝ᵥ chartDirection p.1 ur := by
    rw [SignVector.PolarFace.orientedNormal_dot, normalVec_dot_chartDirection]
    change 0 ≤ SignVector.signed (positiveSign
      (lineEval p.1 a.1 x)) (directionEval p.1 a.1 ur)
    exact signed_positiveSign_nonneg_of_mul_nonneg (hx a) hproducts.2.2
  have hβ : 0 ≤ β := div_nonneg hNw hDq.le
  have hγ : 0 ≤ γ := div_nonneg hNu hDr.le
  refine ⟨α, β, γ, hα, hβ, hγ, ?_⟩
  change N a = α • N p + β • N q.1 + γ • N r.1
  apply vec3_eq_of_dot_chartPoint_and_directions
    (p := p.1) (v := v) (u := uq) (w := ur) huray
  · simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hNp, selected_dot_chartPoint, hNqv, hNrv]
    simp [α]
  · simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hNp, selected_dot_chartDirection, hNqu]
    simp only [mul_zero, zero_add]
    dsimp [γ, Dr]
    exact (div_mul_cancel₀ _ (by exact hDr.ne')).symm
  · simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hNp, selected_dot_chartDirection, hNrw]
    simp only [mul_zero, zero_add, add_zero]
    dsimp [β, Dq]
    exact (div_mul_cancel₀ _ (by exact hDq.ne')).symm

/-- A consecutive exterior sector at a strictly supported affine crossing
is a genuine triangular strict face incident with the selected projective
line. -/
theorem consecutiveExteriorSector_is_incident_triangle
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q r : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v) (hqr : q ≠ r)
    (hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0)
    (hcoord : rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1)
    (hbetween : ∀ a ∈ incidentLines B p v,
      ¬ (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
        rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1)) :
    let x := v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1
    let hx := lineEval_ne_zero_at_consecutive_exterior_sector B p hv l
      hstrict hq hr hqr hl hcoord hbetween
    let n := fun a : B ↦ ProjectiveArrangement.normalVec a.1
    let f := affineFace B p x hx
    SignVectorArrangement.LineFaceIncident n p f ∧
      SignVectorArrangement.strictFaceDegree n f = 3 := by
  dsimp only
  let x := v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1
  let hx := lineEval_ne_zero_at_consecutive_exterior_sector B p hv l
    hstrict hq hr hqr hl hcoord hbetween
  let n := fun a : B ↦ ProjectiveArrangement.normalVec a.1
  let f := affineFace B p x hx
  have hwalls := exteriorSector_three_wallFeasible B p hv l hstrict
    hq hr hqr hl hcoord hbetween hx
  have hcone := exteriorSector_orientedCone B p hv l hstrict
    hq hr hl hcoord hbetween hx
  have hpq : p ≠ q.1 := Ne.symm q.2
  have hpr : p ≠ r.1 := Ne.symm r.2
  have hqr' : q.1 ≠ r.1 := by
    intro heq
    apply hqr
    exact Subtype.ext heq
  exact SignVectorArrangement.incident_and_degree_eq_three_of_orientedCone
    f (fun a ↦ ProjectiveArrangement.normalVec_ne_zero a.1)
    hpq hpr hqr' hwalls.1 hwalls.2.1 hwalls.2.2 hcone

/-- Exact boundary-owner form of the preceding triangle construction. -/
theorem consecutiveExteriorSector_faceEdgeOwners
    (p : B) {v : Point} (hv : v ∈ vertexFinset B p)
    (l : Point →L[ℝ] ℝ)
    (hstrict : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v)
    {q r : OtherPoint B p}
    (hq : q ∈ incidentLines B p v)
    (hr : r ∈ incidentLines B p v) (hqr : q ≠ r)
    (hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0)
    (hcoord : rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 r.1.1)
    (hbetween : ∀ a ∈ incidentLines B p v,
      ¬ (rayCoordinate l p.1 q.1.1 < rayCoordinate l p.1 a.1.1 ∧
        rayCoordinate l p.1 a.1.1 < rayCoordinate l p.1 r.1.1)) :
    let x := v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1
    let hx := lineEval_ne_zero_at_consecutive_exterior_sector B p hv l
      hstrict hq hr hqr hl hcoord hbetween
    let n := fun a : B ↦ ProjectiveArrangement.normalVec a.1
    let f := affineFace B p x hx
    SignVectorArrangement.faceEdgeOwners n f = {p, q.1, r.1} := by
  dsimp only
  let x := v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1
  let hx := lineEval_ne_zero_at_consecutive_exterior_sector B p hv l
    hstrict hq hr hqr hl hcoord hbetween
  let n := fun a : B ↦ ProjectiveArrangement.normalVec a.1
  let f := affineFace B p x hx
  have hwalls := exteriorSector_three_wallFeasible B p hv l hstrict
    hq hr hqr hl hcoord hbetween hx
  have hcone := exteriorSector_orientedCone B p hv l hstrict
    hq hr hl hcoord hbetween hx
  exact SignVectorArrangement.faceEdgeOwners_eq_three_of_orientedCone
    f (fun a ↦ ProjectiveArrangement.normalVec_ne_zero a.1)
    hwalls.1 hwalls.2.1 hwalls.2.2 hcone

/-- Finite data retained from the convex-hull construction, sufficient to
recover the affine base vertex from the resulting triangular face. -/
structure VertexTriangleCertificate (p : B) (v : Point) where
  q : OtherPoint B p
  r : OtherPoint B p
  q_ne_r : q ≠ r
  q_incident : q ∈ incidentLines B p v
  r_incident : r ∈ incidentLines B p v
  face : SignVector.StrictFace
    (fun a : B ↦ ProjectiveArrangement.normalVec a.1)
  owners : SignVectorArrangement.faceEdgeOwners
    (fun a : B ↦ ProjectiveArrangement.normalVec a.1) face =
      {p, q.1, r.1}

theorem VertexTriangleCertificate.owner_incident_at
    {p : B} {v : Point} (C : VertexTriangleCertificate B p v)
    {a : B}
    (ha : a ∈ SignVectorArrangement.faceEdgeOwners
      (fun z : B ↦ ProjectiveArrangement.normalVec z.1) C.face)
    (hap : a ≠ p) :
    lineEval p.1 a.1 v = 0 := by
  rw [C.owners] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with ha | ha | ha
  · exact (hap ha).elim
  · subst a
    exact (mem_incidentLines B p v C.q).mp C.q_incident
  · subst a
    exact (mem_incidentLines B p v C.r).mp C.r_incident

theorem VertexTriangleCertificate.incident_and_degree_three
    {p : B} {v : Point} (C : VertexTriangleCertificate B p v) :
    SignVectorArrangement.LineFaceIncident
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p C.face ∧
      SignVectorArrangement.strictFaceDegree
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) C.face = 3 := by
  constructor
  · rw [← SignVectorArrangement.mem_faceEdgeOwners_iff, C.owners]
    simp
  · rw [← SignVectorArrangement.card_faceEdgeOwners, C.owners]
    have hpq : p ≠ C.q.1 := Ne.symm C.q.2
    have hpr : p ≠ C.r.1 := Ne.symm C.r.2
    have hqr : C.q.1 ≠ C.r.1 := by
      intro h
      apply C.q_ne_r
      exact Subtype.ext h
    simp [hpq, hpr, hqr]

/-- Equality of the three boundary-owner sets recovers the affine base
crossing recorded by two vertex certificates. -/
theorem VertexTriangleCertificate.base_eq_of_owners_eq
    {p : B} {v w : Point}
    (Cv : VertexTriangleCertificate B p v)
    (Cw : VertexTriangleCertificate B p w)
    (howners : SignVectorArrangement.faceEdgeOwners
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cv.face =
      SignVectorArrangement.faceEdgeOwners
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cw.face) :
    v = w := by
  have hqOwner : Cv.q.1 ∈ SignVectorArrangement.faceEdgeOwners
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cw.face := by
    rw [← howners, Cv.owners]
    simp
  have hrOwner : Cv.r.1 ∈ SignVectorArrangement.faceEdgeOwners
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cw.face := by
    rw [← howners, Cv.owners]
    simp
  have hqv := (mem_incidentLines B p v Cv.q).mp Cv.q_incident
  have hrv := (mem_incidentLines B p v Cv.r).mp Cv.r_incident
  have hqw := VertexTriangleCertificate.owner_incident_at
    (B := B) Cw hqOwner Cv.q.2
  have hrw := VertexTriangleCertificate.owner_incident_at
    (B := B) Cw hrOwner Cv.r.2
  have hnp : Nonparallel p.1 Cv.q.1.1 Cv.r.1.1 :=
    nonparallel_of_mem_incidentLines B p v Cv.q_incident Cv.r_incident Cv.q_ne_r
  exact eq_of_lineEval_eq_zero_of_nonparallel hnp hqv hrv hqw hrw

/-- Direction set of all affine lines through a recorded crossing. -/
def incidentDirections (p : B) (v : Point) : Finset Point := by
  classical
  exact (incidentLines B p v).image fun q ↦ lineDirection p.1 q.1.1

theorem incidentDirections_ne_zero (p : B) (v : Point) :
    ∀ d ∈ incidentDirections B p v, d ≠ 0 := by
  intro d hd
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
  apply lineDirection_ne_zero
  intro heq
  apply q.2
  exact Subtype.ext heq.symm

/-- Every convex-hull vertex of the affine crossing set yields a certified
triangular face based at that vertex. -/
theorem hullVertex_exists_triangleCertificate
    (p : B) {v : Point}
    (hv : v ∈ Erdos957.hullVertices (vertexFinset B p)) :
    Nonempty (VertexTriangleCertificate B p v) := by
  have hvA : v ∈ vertexFinset B p := Erdos957.hullVertices_subset _ hv
  obtain ⟨l, -, hstrict, hlD⟩ := hullVertex_exists_generic_strict_support
    (vertexFinset B p) (incidentDirections B p v) hv
    (incidentDirections_ne_zero B p v)
  have hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0 := by
    intro z hz
    apply hlD
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  obtain ⟨q, hq, r, hr, hqr, hcoord, hbetween⟩ :=
    exists_consecutive_incident_rays B p hvA l hl
  let hx := lineEval_ne_zero_at_consecutive_exterior_sector B p hvA l
    hstrict hq hr hqr hl hcoord hbetween
  let x := v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1
  let f := affineFace B p x hx
  have howners := consecutiveExteriorSector_faceEdgeOwners B p hvA l
    hstrict hq hr hqr hl hcoord hbetween
  exact ⟨⟨q, r, hqr, hq, hr, f, howners⟩⟩

/-- Choice of the certified triangular face at every affine hull vertex. -/
noncomputable def hullVertexTriangleCertificate (p : B)
    (v : {v // v ∈ Erdos957.hullVertices (vertexFinset B p)}) :
    VertexTriangleCertificate B p v.1 :=
  Classical.choice (hullVertex_exists_triangleCertificate B p v.2)

/-- Distinct affine hull vertices yield distinct certified faces. -/
theorem hullVertexTriangleFace_injective (p : B) :
    Function.Injective (fun v :
      {v // v ∈ Erdos957.hullVertices (vertexFinset B p)} ↦
        (hullVertexTriangleCertificate B p v).face) := by
  intro v w hface
  let Cv := hullVertexTriangleCertificate B p v
  let Cw := hullVertexTriangleCertificate B p w
  change Cv.face = Cw.face at hface
  have howners : SignVectorArrangement.faceEdgeOwners
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cv.face =
      SignVectorArrangement.faceEdgeOwners
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cw.face := by
    rw [hface]
  apply Subtype.ext
  exact VertexTriangleCertificate.base_eq_of_owners_eq
    (B := B) Cv Cw howners

/-- A certified face based at one hull vertex cannot be the antipode of a
certified face based at a different hull vertex. -/
theorem hullVertexTriangleFace_ne_antipodal_of_ne (p : B)
    {v w : {x // x ∈ Erdos957.hullVertices (vertexFinset B p)}}
    (hvw : v ≠ w) :
    (hullVertexTriangleCertificate B p w).face ≠
      SignVectorArrangement.antipodalStrictFace
        (hullVertexTriangleCertificate B p v).face := by
  intro hface
  let Cv := hullVertexTriangleCertificate B p v
  let Cw := hullVertexTriangleCertificate B p w
  have howners : SignVectorArrangement.faceEdgeOwners
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cv.face =
      SignVectorArrangement.faceEdgeOwners
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cw.face := by
    rw [hface, SignVectorArrangement.faceEdgeOwners_antipodalStrictFace]
  apply hvw
  apply Subtype.ext
  exact VertexTriangleCertificate.base_eq_of_owners_eq
    (B := B) Cv Cw howners

/-- A finite planar set containing two distinct points has at least two
convex-hull vertices. -/
theorem two_le_hullVertexCount_of_two_le_card (A : Finset Point)
    (hA : 2 ≤ A.card) :
    2 ≤ Erdos957.hullVertexCount A := by
  obtain ⟨x, hx, y, hy, hxy, hdist⟩ :=
    Erdos957.exists_pair_dist_eq_maxDist A hA
  have hmax : ∀ z ∈ (A : Set Point), dist z y ≤ dist x y := by
    intro z hz
    by_cases hzy : z = y
    · subst z
      simp
    · rw [hdist]
      exact Erdos957.dist_le_maxDist hA hz hy hzy
  have hxext : x ∈ (convexHull ℝ (A : Set Point)).extremePoints ℝ :=
    Erdos957.farthestPoint_mem_extremePoints_convexHull
      (A : Set Point) hx hxy hmax
  have hmax' : ∀ z ∈ (A : Set Point), dist z x ≤ dist y x := by
    intro z hz
    by_cases hzx : z = x
    · subst z
      simp
    · simpa [dist_comm, hdist] using
        Erdos957.dist_le_maxDist hA hz hx hzx
  have hyext : y ∈ (convexHull ℝ (A : Set Point)).extremePoints ℝ :=
    Erdos957.farthestPoint_mem_extremePoints_convexHull
      (A : Set Point) hy hxy.symm hmax'
  change 2 ≤ (Erdos957.hullVertices A).card
  exact Finset.one_lt_card.mpr ⟨x, Erdos957.mem_hullVertices.mpr hxext,
    y, Erdos957.mem_hullVertices.mpr hyext, hxy⟩

/-- Two distinct affine crossing vertices already give three spherical
triangular chambers: the two constructed chambers and the antipode of one. -/
theorem three_le_incident_triangles_of_two_le_vertex_card
    (p : B) (hvertices : 2 ≤ (vertexFinset B p).card) :
    3 ≤ (Finset.univ.filter fun f : SignVector.StrictFace
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) ↦
      SignVectorArrangement.LineFaceIncident
          (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p f ∧
        SignVectorArrangement.strictFaceDegree
          (fun a : B ↦ ProjectiveArrangement.normalVec a.1) f = 3).card := by
  classical
  let V := {v // v ∈ Erdos957.hullVertices (vertexFinset B p)}
  have hVcard : 1 < Fintype.card V := by
    have htwo := two_le_hullVertexCount_of_two_le_card
      (vertexFinset B p) hvertices
    change 2 ≤ (Erdos957.hullVertices (vertexFinset B p)).card at htwo
    rw [show Fintype.card V =
        (Erdos957.hullVertices (vertexFinset B p)).card by simp [V]]
    omega
  let v : V := Classical.choice (Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V))
  obtain ⟨w, hvw⟩ := Fintype.exists_ne_of_one_lt_card hVcard v
  let Cv := hullVertexTriangleCertificate B p v
  let Cw := hullVertexTriangleCertificate B p w
  let face : Fin 3 → SignVector.StrictFace
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) :=
    ![Cv.face, SignVectorArrangement.antipodalStrictFace Cv.face, Cw.face]
  have hvwface : Cv.face ≠ Cw.face := by
    intro h
    apply hvw
    exact (hullVertexTriangleFace_injective B p h).symm
  have hantiw : SignVectorArrangement.antipodalStrictFace Cv.face ≠ Cw.face := by
    exact (hullVertexTriangleFace_ne_antipodal_of_ne B p hvw.symm).symm
  let : Nonempty B := ⟨p⟩
  have hanti : Cv.face ≠
      SignVectorArrangement.antipodalStrictFace Cv.face :=
    (SignVectorArrangement.antipodalStrictFace_ne Cv.face).symm
  have hface : Function.Injective face := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      apply hanti
      exact hij
    · exfalso
      apply hvwface
      exact hij
    · exfalso
      apply hanti
      exact hij.symm
    · rfl
    · exfalso
      apply hantiw
      exact hij
    · exfalso
      apply hvwface
      exact hij.symm
    · exfalso
      apply hantiw
      exact hij.symm
    · rfl
  apply SignVectorArrangement.three_le_incident_triangles_of_injective p face hface
  · intro t
    fin_cases t
    · change SignVectorArrangement.LineFaceIncident
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p Cv.face
      exact Cv.incident_and_degree_three.1
    · change SignVectorArrangement.LineFaceIncident
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p
          (SignVectorArrangement.antipodalStrictFace Cv.face)
      rw [← SignVectorArrangement.mem_faceEdgeOwners_iff,
        SignVectorArrangement.faceEdgeOwners_antipodalStrictFace, Cv.owners]
      simp
    · change SignVectorArrangement.LineFaceIncident
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p Cw.face
      exact Cw.incident_and_degree_three.1
  · intro t
    fin_cases t
    · change SignVectorArrangement.strictFaceDegree
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cv.face = 3
      exact Cv.incident_and_degree_three.2
    · change SignVectorArrangement.strictFaceDegree
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1)
          (SignVectorArrangement.antipodalStrictFace Cv.face) = 3
      rw [← SignVectorArrangement.card_faceEdgeOwners,
        SignVectorArrangement.faceEdgeOwners_antipodalStrictFace, Cv.owners]
      have hpq : p ≠ Cv.q.1 := Ne.symm Cv.q.2
      have hpr : p ≠ Cv.r.1 := Ne.symm Cv.r.2
      have hqr : Cv.q.1 ≠ Cv.r.1 := by
        intro h
        apply Cv.q_ne_r
        exact Subtype.ext h
      simp [hpq, hpr, hqr]
    · change SignVectorArrangement.strictFaceDegree
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cw.face = 3
      exact Cw.incident_and_degree_three.2

/-- In the concurrent degeneracy, the two opposite choices of supporting
half-plane give two non-antipodal triangular chambers.  Together with the
antipode of the first chamber, these give the required three. -/
theorem three_le_incident_triangles_of_vertex_card_eq_one
    (p : B) (hvertices : (vertexFinset B p).card = 1) :
    3 ≤ (Finset.univ.filter fun f : SignVector.StrictFace
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) ↦
      SignVectorArrangement.LineFaceIncident
          (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p f ∧
        SignVectorArrangement.strictFaceDegree
          (fun a : B ↦ ProjectiveArrangement.normalVec a.1) f = 3).card := by
  classical
  obtain ⟨v, hV⟩ := Finset.card_eq_one.mp hvertices
  have hv : v ∈ vertexFinset B p := by
    rw [hV]
    simp
  have hstrict : ∀ w ∈ vertexFinset B p, w ≠ v →
      (0 : Point →L[ℝ] ℝ) w < (0 : Point →L[ℝ] ℝ) v := by
    intro w hw hwv
    rw [hV] at hw
    simp only [Finset.mem_singleton] at hw
    exact (hwv hw).elim
  obtain ⟨l, hlD⟩ := exists_planeFunctional_nonzero_on
    (incidentDirections B p v) (incidentDirections_ne_zero B p v)
  have hl : ∀ z ∈ incidentLines B p v,
      l (lineDirection p.1 z.1.1) ≠ 0 := by
    intro z hz
    apply hlD
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hstrictL : ∀ w ∈ vertexFinset B p, w ≠ v → l w < l v := by
    intro w hw hwv
    rw [hV] at hw
    simp only [Finset.mem_singleton] at hw
    exact (hwv hw).elim
  have hstrictNL : ∀ w ∈ vertexFinset B p, w ≠ v →
      (-l) w < (-l) v := by
    intro w hw hwv
    rw [hV] at hw
    simp only [Finset.mem_singleton] at hw
    exact (hwv hw).elim
  obtain ⟨q, hq, r, hr, hqr, hcoord, hbetween⟩ :=
    exists_consecutive_incident_rays B p hv l hl
  have hnl : ∀ z ∈ incidentLines B p v,
      (-l) (lineDirection p.1 z.1.1) ≠ 0 := by
    intro z hz
    simpa using neg_ne_zero.mpr (hl z hz)
  have hncoord : rayCoordinate (-l) p.1 q.1.1 <
      rayCoordinate (-l) p.1 r.1.1 := by
    simpa using hcoord
  have hnbetween : ∀ a ∈ incidentLines B p v,
      ¬ (rayCoordinate (-l) p.1 q.1.1 < rayCoordinate (-l) p.1 a.1.1 ∧
        rayCoordinate (-l) p.1 a.1.1 < rayCoordinate (-l) p.1 r.1.1) := by
    intro a ha
    simpa using hbetween a ha
  let xplus := v + supportRay l p.1 q.1.1 + supportRay l p.1 r.1.1
  let hxplus := lineEval_ne_zero_at_consecutive_exterior_sector B p hv l
    hstrictL hq hr hqr hl hcoord hbetween
  let fplus := affineFace B p xplus hxplus
  let xminus := v + supportRay (-l) p.1 q.1.1 + supportRay (-l) p.1 r.1.1
  let hxminus := lineEval_ne_zero_at_consecutive_exterior_sector B p hv (-l)
    hstrictNL hq hr hqr hnl hncoord hnbetween
  let fminus := affineFace B p xminus hxminus
  have hownersPlus : SignVectorArrangement.faceEdgeOwners
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) fplus =
        {p, q.1, r.1} := by
    exact consecutiveExteriorSector_faceEdgeOwners B p hv l hstrictL
      hq hr hqr hl hcoord hbetween
  have hownersMinus : SignVectorArrangement.faceEdgeOwners
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) fminus =
        {p, q.1, r.1} := by
    exact consecutiveExteriorSector_faceEdgeOwners B p hv (-l) hstrictNL
      hq hr hqr hnl hncoord hnbetween
  let Cplus : VertexTriangleCertificate B p v :=
    ⟨q, r, hqr, hq, hr, fplus, hownersPlus⟩
  let Cminus : VertexTriangleCertificate B p v :=
    ⟨q, r, hqr, hq, hr, fminus, hownersMinus⟩
  have hqv : lineEval p.1 q.1.1 v = 0 :=
    (mem_incidentLines B p v q).mp hq
  have hnp : Nonparallel p.1 q.1.1 r.1.1 :=
    nonparallel_of_mem_incidentLines B p v hq hr hqr
  have hD : directionEval p.1 q.1.1
      (supportRay l p.1 r.1.1) ≠ 0 :=
    directionEval_supportRay_ne_zero_of_nonparallel hnp (hl r hr)
  have hplusEval : lineEval p.1 q.1.1 xplus =
      directionEval p.1 q.1.1 (supportRay l p.1 r.1.1) := by
    dsimp [xplus]
    rw [lineEval_add, lineEval_add, hqv,
      directionEval_supportRay_self, zero_add, zero_add]
  have hminusEval : lineEval p.1 q.1.1 xminus =
      -(directionEval p.1 q.1.1 (supportRay l p.1 r.1.1)) := by
    dsimp [xminus]
    rw [supportRay_neg, supportRay_neg, lineEval_add, lineEval_add, hqv,
      directionEval_neg_apply, directionEval_neg_apply,
      directionEval_supportRay_self]
    ring
  have hplusMinus : fplus ≠ fminus := by
    intro hfaces
    have hs := congrArg
      (fun f : SignVector.StrictFace
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) ↦ f.1 q.1) hfaces
    change positiveSign (lineEval p.1 q.1.1 xplus) =
      positiveSign (lineEval p.1 q.1.1 xminus) at hs
    rw [hplusEval, hminusEval] at hs
    exact (positiveSign_neg_ne hD) hs.symm
  have hplusSelected : fplus.1 p = true := by
    simp [fplus, affineFace, positiveSign, lineEval]
  have hminusSelected : fminus.1 p = true := by
    simp [fminus, affineFace, positiveSign, lineEval]
  have hantiSelected :
      (SignVectorArrangement.antipodalStrictFace fplus).1 p = false := by
    rw [SignVectorArrangement.antipodalStrictFace_sign]
    simp [SignVector.antipodalSign, hplusSelected]
  have hminusAnti : fminus ≠
      SignVectorArrangement.antipodalStrictFace fplus := by
    intro hfaces
    have hs := congrArg
      (fun f : SignVector.StrictFace
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) ↦ f.1 p) hfaces
    rw [hminusSelected, hantiSelected] at hs
    exact Bool.noConfusion hs
  let : Nonempty B := ⟨p⟩
  have hplusAnti : fplus ≠
      SignVectorArrangement.antipodalStrictFace fplus :=
    (SignVectorArrangement.antipodalStrictFace_ne fplus).symm
  let face : Fin 3 → SignVector.StrictFace
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) :=
    ![fplus, fminus, SignVectorArrangement.antipodalStrictFace fplus]
  have hface : Function.Injective face := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      exact hplusMinus hij
    · exfalso
      exact hplusAnti hij
    · exfalso
      exact hplusMinus hij.symm
    · rfl
    · exfalso
      exact hminusAnti hij
    · exfalso
      exact hplusAnti hij.symm
    · exfalso
      exact hminusAnti hij.symm
    · rfl
  apply SignVectorArrangement.three_le_incident_triangles_of_injective p face hface
  · intro t
    fin_cases t
    · change SignVectorArrangement.LineFaceIncident
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p Cplus.face
      exact Cplus.incident_and_degree_three.1
    · change SignVectorArrangement.LineFaceIncident
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p Cminus.face
      exact Cminus.incident_and_degree_three.1
    · change SignVectorArrangement.LineFaceIncident
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p
          (SignVectorArrangement.antipodalStrictFace fplus)
      rw [← SignVectorArrangement.mem_faceEdgeOwners_iff,
        SignVectorArrangement.faceEdgeOwners_antipodalStrictFace, hownersPlus]
      simp
  · intro t
    fin_cases t
    · change SignVectorArrangement.strictFaceDegree
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cplus.face = 3
      exact Cplus.incident_and_degree_three.2
    · change SignVectorArrangement.strictFaceDegree
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) Cminus.face = 3
      exact Cminus.incident_and_degree_three.2
    · change SignVectorArrangement.strictFaceDegree
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1)
          (SignVectorArrangement.antipodalStrictFace fplus) = 3
      rw [← SignVectorArrangement.card_faceEdgeOwners,
        SignVectorArrangement.faceEdgeOwners_antipodalStrictFace, hownersPlus]
      have hpq : p ≠ q.1 := Ne.symm q.2
      have hpr : p ≠ r.1 := Ne.symm r.2
      have hqr' : q.1 ≠ r.1 := by
        intro h
        apply hqr
        exact Subtype.ext h
      simp [hpq, hpr, hqr']

/-- Concrete Levi theorem for the affine-dual normal family.  One
noncollinear triple ensures that every selected line leaves at least one
affine crossing after it is sent to infinity.  The crossing set then has
either one point (the concurrent case) or at least two points, exactly the
two cases proved above. -/
theorem hasSignVectorLeviProperty_of_noncollinear_triple
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    SignVectorArrangement.HasSignVectorLeviProperty
      (fun z : B ↦ ProjectiveArrangement.normalVec z.1) := by
  classical
  intro p
  have hverticesNonempty : (vertexFinset B p).Nonempty := by
    rcases ProjectiveArrangement.exists_noncollinear_pair_through_point
      hncol p.1 with hab | hac | hbc
    · let qa : B := ⟨a, ha⟩
      let qb : B := ⟨b, hb⟩
      have hpa : p ≠ qa := by
        intro h
        apply hab
        have hp : p.1 = a := congrArg Subtype.val h
        simp [ProjectiveDuality.Collinear3,
          ProjectiveDuality.orientationDet, hp]
      have hpb : p ≠ qb := by
        intro h
        apply hab
        have hp : p.1 = b := congrArg Subtype.val h
        simp [ProjectiveDuality.Collinear3,
          ProjectiveDuality.orientationDet, hp]
      exact vertexFinset_nonempty_of_noncollinear B p qa qb hpa hpb hab
    · let qa : B := ⟨a, ha⟩
      let qc : B := ⟨c, hc⟩
      have hpa : p ≠ qa := by
        intro h
        apply hac
        have hp : p.1 = a := congrArg Subtype.val h
        simp [ProjectiveDuality.Collinear3,
          ProjectiveDuality.orientationDet, hp]
      have hpc : p ≠ qc := by
        intro h
        apply hac
        have hp : p.1 = c := congrArg Subtype.val h
        simp [ProjectiveDuality.Collinear3,
          ProjectiveDuality.orientationDet, hp]
      exact vertexFinset_nonempty_of_noncollinear B p qa qc hpa hpc hac
    · let qb : B := ⟨b, hb⟩
      let qc : B := ⟨c, hc⟩
      have hpb : p ≠ qb := by
        intro h
        apply hbc
        have hp : p.1 = b := congrArg Subtype.val h
        simp [ProjectiveDuality.Collinear3,
          ProjectiveDuality.orientationDet, hp]
      have hpc : p ≠ qc := by
        intro h
        apply hbc
        have hp : p.1 = c := congrArg Subtype.val h
        simp [ProjectiveDuality.Collinear3,
          ProjectiveDuality.orientationDet, hp]
      exact vertexFinset_nonempty_of_noncollinear B p qb qc hpb hpc hbc
  have hpos : 0 < (vertexFinset B p).card :=
    Finset.card_pos.mpr hverticesNonempty
  by_cases htwo : 2 ≤ (vertexFinset B p).card
  · exact three_le_incident_triangles_of_two_le_vertex_card B p htwo
  · have hone : (vertexFinset B p).card = 1 := by omega
    exact three_le_incident_triangles_of_vertex_card_eq_one B p hone

/-- Levi's local three-triangle bound in the genuinely two-dimensional
affine-vertex case. -/
theorem three_le_incident_triangles_of_affineSpan_eq_top
    (p : B)
    (hspan : affineSpan ℝ (vertexFinset B p : Set Point) = ⊤) :
    3 ≤ (Finset.univ.filter fun f : SignVector.StrictFace
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) ↦
      SignVectorArrangement.LineFaceIncident
          (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p f ∧
        SignVectorArrangement.strictFaceDegree
          (fun a : B ↦ ProjectiveArrangement.normalVec a.1) f = 3).card := by
  classical
  let V := {v // v ∈ Erdos957.hullVertices (vertexFinset B p)}
  let face : V → SignVector.StrictFace
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) := fun v ↦
    (hullVertexTriangleCertificate B p v).face
  let T : Finset (SignVector.StrictFace
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1)) :=
    Finset.univ.image face
  have hTcard : T.card = Erdos957.hullVertexCount (vertexFinset B p) := by
    rw [Finset.card_image_of_injective _ (hullVertexTriangleFace_injective B p)]
    simp [V, Erdos957.hullVertexCount]
  have hsubset : T ⊆ Finset.univ.filter fun f : SignVector.StrictFace
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) ↦
      SignVectorArrangement.LineFaceIncident
          (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p f ∧
        SignVectorArrangement.strictFaceDegree
          (fun a : B ↦ ProjectiveArrangement.normalVec a.1) f = 3 := by
    intro f hf
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hullVertexTriangleCertificate B p v).incident_and_degree_three⟩
  calc
    3 ≤ Erdos957.hullVertexCount (vertexFinset B p) :=
      three_le_hullVertexCount_of_affineSpan_eq_top B p hspan
    _ = T.card := hTcard.symm
    _ ≤ _ := Finset.card_le_card hsubset

end FiniteConfiguration

end

end Erdos735.LeviExteriorSector

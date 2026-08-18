/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.WidthInradius
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# A quantitative width-to-inball theorem

We prove the elementary Minkowski--Radon bound: a compact convex set in
`d`-dimensional Euclidean space whose width in every unit direction is at
least `w` contains a closed ball of radius `w / (d + 1)`.

The proof has two independent pieces.  Helly's theorem gives a point `c`
such that `c + (d + 1)⁻¹ (P - P) ⊆ P`.  Hahn--Banach separation and the
Riesz representation theorem show that the width hypothesis implies
`closedBall 0 w ⊆ P - P`.  No John ellipsoid or Steinhagen theorem is
assumed.
-/

open Set MeasureTheory
open scoped ENNReal Pointwise Topology

namespace Erdos186.PZ.ConvexDensity

noncomputable section

private def translateConstraint {d : ℕ} (P : Set (EuclideanPoint d))
    (a : ℝ) (z : P × P) : Set (EuclideanPoint d) :=
  {x | x + a • ((z.1 : EuclideanPoint d) - (z.2 : EuclideanPoint d)) ∈ P}

private theorem convex_translateConstraint {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : Convex ℝ P) (a : ℝ) (z : P × P) :
    Convex ℝ (translateConstraint P a z) := by
  intro x hx y hy p q hp hq hpq
  change x + a • ((z.1 : EuclideanPoint d) - (z.2 : EuclideanPoint d)) ∈ P at hx
  change y + a • ((z.1 : EuclideanPoint d) - (z.2 : EuclideanPoint d)) ∈ P at hy
  have h := hP hx hy hp hq hpq
  change p • x + q • y + a • ((z.1 : EuclideanPoint d) - (z.2 : EuclideanPoint d)) ∈ P
  have hv :
      a • ((z.1 : EuclideanPoint d) - (z.2 : EuclideanPoint d)) =
        p • (a • ((z.1 : EuclideanPoint d) - (z.2 : EuclideanPoint d))) +
          q • (a • ((z.1 : EuclideanPoint d) - (z.2 : EuclideanPoint d))) := by
    rw [← add_smul, hpq, one_smul]
  rw [hv]
  convert h using 1 <;> module

private theorem compact_translateConstraint {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (a : ℝ) (z : P × P) :
    IsCompact (translateConstraint P a z) := by
  let v : EuclideanPoint d := a • ((z.1 : EuclideanPoint d) - (z.2 : EuclideanPoint d))
  have himage : translateConstraint P a z = (fun y ↦ y - v) '' P := by
    ext x
    constructor
    · intro hx
      change x + v ∈ P at hx
      exact ⟨x + v, hx, by simp [v]⟩
    · rintro ⟨y, hy, rfl⟩
      change y - v + v ∈ P
      simpa using hy
  rw [himage]
  exact hP.image (continuous_id.sub continuous_const)

/-- Minkowski--Radon asymmetry bound in the form needed here. -/
theorem exists_center_inv_succ_smul_sub_mem {d : ℕ}
    {P : Set (EuclideanPoint d)} (hPconv : Convex ℝ P)
    (hPcomp : IsCompact P) (hPne : P.Nonempty) :
    ∃ c : EuclideanPoint d, ∀ p ∈ P, ∀ q ∈ P,
      c + ((d + 1 : ℕ) : ℝ)⁻¹ • (p - q) ∈ P := by
  let a : ℝ := ((d + 1 : ℕ) : ℝ)⁻¹
  let F : P × P → Set (EuclideanPoint d) := translateConstraint P a
  have hfin : Module.finrank ℝ (EuclideanPoint d) = d :=
    finrank_euclideanSpace_fin
  have hinter : ∀ I : Finset (P × P), I.card ≤ d + 1 →
      (⋂ z ∈ I, F z).Nonempty := by
    intro I hI
    by_cases hI0 : I = ∅
    · subst I
      simpa using (Set.univ_nonempty : (Set.univ : Set (EuclideanPoint d)).Nonempty)
    obtain ⟨z0, hz0⟩ := I.nonempty_iff_ne_empty.mpr hI0
    let base : EuclideanPoint d := hPne.some
    let n : ℝ := I.card
    let mu : ℝ := 1 - n * a
    let c : EuclideanPoint d :=
      a • (∑ z ∈ I, (z.2 : EuclideanPoint d)) + mu • base
    refine ⟨c, ?_⟩
    rw [Set.mem_iInter₂]
    intro z hz
    change c ∈ F z
    let point : P × P → EuclideanPoint d := fun t ↦
      if t = z then (z.1 : EuclideanPoint d) else (t.2 : EuclideanPoint d)
    let y : EuclideanPoint d := ∑ t ∈ I, n⁻¹ • point t
    have hnpos : 0 < n := by
      simp only [n, Nat.cast_pos]
      exact I.card_pos.mpr ⟨z0, hz0⟩
    have hysum : y ∈ P := by
      apply hPconv.sum_mem
      · intro t ht
        exact inv_nonneg.mpr hnpos.le
      · simp only [n, Finset.sum_const, nsmul_eq_mul]
        exact mul_inv_cancel₀ hnpos.ne'
      · intro t ht
        simp only [point]
        split_ifs
        · exact z.1.property
        · exact t.2.property
    have ha : 0 ≤ (I.card : ℝ) * a := by
      exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (by positivity))
    have hmu : 0 ≤ mu := by
      dsimp only [mu, n, a]
      rw [sub_nonneg]
      have hcast : (I.card : ℝ) ≤ d + 1 := by exact_mod_cast hI
      calc
        (I.card : ℝ) * (↑(d + 1))⁻¹ ≤
            (d + 1 : ℝ) * (↑(d + 1))⁻¹ := by
          gcongr
        _ = (d + 1 : ℝ) * (d + 1 : ℝ)⁻¹ := by norm_num
        _ = 1 := mul_inv_cancel₀ (show (d + 1 : ℝ) ≠ 0 by positivity)
    have hcombo : ((I.card : ℝ) * a) • y + mu • base ∈ P := by
      apply hPconv hysum hPne.some_mem ha hmu
      dsimp only [mu, n]
      ring
    change c + a • ((z.1 : EuclideanPoint d) - (z.2 : EuclideanPoint d)) ∈ P
    convert hcombo using 1
    have hsum_point :
        (∑ t ∈ I, point t) =
          (∑ t ∈ I, (t.2 : EuclideanPoint d)) +
            ((z.1 : EuclideanPoint d) - (z.2 : EuclideanPoint d)) := by
      rw [← Finset.sum_erase_add I point hz,
        ← Finset.sum_erase_add I (fun t ↦ (t.2 : EuclideanPoint d)) hz]
      simp only [point, if_pos]
      have herase :
          (∑ t ∈ I.erase z, point t) =
            ∑ t ∈ I.erase z, (t.2 : EuclideanPoint d) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [point, if_neg (Finset.ne_of_mem_erase ht)]
      rw [herase]
      abel
    dsimp only [c, y]
    rw [← Finset.smul_sum, hsum_point]
    dsimp only [n]
    rw [smul_add, smul_add]
    have hcardne : (I.card : ℝ) ≠ 0 := by positivity
    have hcoef : ((I.card : ℝ) * a) * (I.card : ℝ)⁻¹ = a := by
      rw [mul_assoc, mul_comm a, ← mul_assoc, mul_inv_cancel₀ hcardne, one_mul]
    rw [smul_smul, smul_smul, hcoef]
    module
  have hhelly : (⋂ z, F z).Nonempty := by
    apply Convex.helly_theorem_compact' (𝕜 := ℝ)
    · exact fun z ↦ convex_translateConstraint hPconv a z
    · exact fun z ↦ compact_translateConstraint hPcomp a z
    · intro I hI
      apply hinter I
      simpa only [hfin] using hI
  obtain ⟨c, hc⟩ := hhelly
  refine ⟨c, fun p hp q hq ↦ ?_⟩
  let z : P × P := ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  have hcz : c ∈ F z := Set.mem_iInter.mp hc z
  simpa only [F, translateConstraint, a, Set.mem_setOf_eq] using hcz

/-- A directional width of a compact set is realized by a difference of two
points of the set. -/
theorem exists_sub_directionalValue_eq_width {d : ℕ}
    {P : Set (EuclideanPoint d)} (hPcomp : IsCompact P) (hPne : P.Nonempty)
    (u : EuclideanPoint d) :
    ∃ p ∈ P, ∃ q ∈ P,
      directionalValue u (p - q) = directionalWidth P u := by
  obtain ⟨p, hp, hpEq, _hpmax⟩ := exists_supportUpper hPcomp hPne u
  obtain ⟨q, hq, hqEq, _hqmin⟩ := exists_supportLower hPcomp hPne u
  refine ⟨p, hp, q, hq, ?_⟩
  rw [directionalWidth, hpEq, hqEq]
  simp only [directionalValue, inner_sub_right]

/-- If every unit directional width is at least `w`, the difference body
contains the radius-`w` closed ball. -/
theorem closedBall_zero_subset_sub_of_forall_width {d : ℕ}
    {P : Set (EuclideanPoint d)} (hPconv : Convex ℝ P)
    (hPcomp : IsCompact P) (hPne : P.Nonempty) {w : ℝ} (hw : 0 ≤ w)
    (hwidth : ∀ u : EuclideanPoint d, ‖u‖ = 1 →
      w ≤ directionalWidth P u) :
    Metric.closedBall (0 : EuclideanPoint d) w ⊆ P - P := by
  have hDconv : Convex ℝ (P - P) := hPconv.sub hPconv
  have hDcomp : IsCompact (P - P) := by
    rw [sub_eq_add_neg]
    exact hPcomp.add hPcomp.neg
  intro y hy
  by_contra hyD
  obtain ⟨f, t, hft, hty⟩ :=
    geometric_hahn_banach_closed_point hDconv hDcomp.isClosed hyD
  obtain ⟨p0, hp0⟩ := hPne
  have hzeroD : (0 : EuclideanPoint d) ∈ P - P := by
    rw [Set.mem_sub]
    exact ⟨p0, hp0, p0, hp0, sub_self p0⟩
  have hfne : f ≠ 0 := by
    intro hf
    have hzero := hft 0 hzeroD
    rw [hf] at hzero hty
    simp only [ContinuousLinearMap.zero_apply] at hzero hty
    linarith
  let v : EuclideanPoint d := (InnerProductSpace.toDual ℝ (EuclideanPoint d)).symm f
  have hvne : v ≠ 0 := by
    intro hv
    apply hfne
    have h := congrArg (fun x ↦ (InnerProductSpace.toDual ℝ (EuclideanPoint d)) x) hv
    simpa only [v, LinearIsometryEquiv.apply_symm_apply, map_zero] using h
  let u : EuclideanPoint d := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvne)
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    exists_sub_directionalValue_eq_width hPcomp ⟨p0, hp0⟩ u
  have hpqD : p - q ∈ P - P := by
    rw [Set.mem_sub]
    exact ⟨p, hp, q, hq, rfl⟩
  have hsep : f (p - q) < f y := (hft (p - q) hpqD).trans hty
  have hvnorm : ‖v‖ = ‖f‖ :=
    (InnerProductSpace.toDual ℝ (EuclideanPoint d)).symm.norm_map f
  have hrepr (x : EuclideanPoint d) : inner ℝ v x = f x :=
    InnerProductSpace.toDual_symm_apply
  have hfpq : f (p - q) = ‖v‖ * directionalWidth P u := by
    rw [← hrepr, ← hpq]
    simp only [directionalValue, u, inner_smul_left, conj_trivial]
    rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_mul]
  have hfy : f y ≤ ‖v‖ * w := by
    calc
      f y ≤ |f y| := le_abs_self _
      _ = ‖f y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖f‖ * ‖y‖ := f.le_opNorm y
      _ ≤ ‖f‖ * w := by
        gcongr
        simpa only [Metric.mem_closedBall, dist_zero_right] using hy
      _ = ‖v‖ * w := by rw [hvnorm]
  have hlow : ‖v‖ * w ≤ f (p - q) := by
    rw [hfpq]
    exact mul_le_mul_of_nonneg_left (hwidth u hu) (norm_nonneg v)
  linarith

/-- A set contained in the radius-`R` ball has volume at most its width in any
unit direction times `(2R)^(d-1)`.  The proof rotates the direction to a
coordinate axis, applies the coordinate-box estimate, and uses invariance of
Lebesgue measure under linear isometries. -/
theorem volume_le_directionalWidth_mul_ball {d : ℕ} (hd : 0 < d)
    {P : Set (EuclideanPoint d)} (hP : IsCompact P) (hPne : P.Nonempty)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : P ⊆ Metric.closedBall (0 : EuclideanPoint d) R)
    (u : EuclideanPoint d) (hu : ‖u‖ = 1) :
    volume P ≤ ENNReal.ofReal (2 * R) ^ (d - 1) *
      ENNReal.ofReal (directionalWidth P u) := by
  let i : Fin d := ⟨0, hd⟩
  let e : EuclideanPoint d := EuclideanSpace.single i (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  let T : EuclideanPoint d ≃ₗᵢ[ℝ] EuclideanPoint d :=
    ((ℝ ∙ (u - e))ᗮ).reflection
  have hTu : T u = e := by
    exact Submodule.reflection_sub (hu.trans he.symm)
  let Q : Set (EuclideanPoint d) := T '' P
  have hQcomp : IsCompact Q := hP.image T.continuous
  have hQne : Q.Nonempty := hPne.image T
  have hQball : Q ⊆ Metric.closedBall (0 : EuclideanPoint d) R := by
    rintro y ⟨x, hx, rfl⟩
    have hxnorm : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball hx
    simpa only [Metric.mem_closedBall, map_zero, dist_zero_right, T.norm_map] using hxnorm
  have hQcube : Q ⊆ closedAxisBox
      (fun j ↦ coordinate (0 : EuclideanPoint d) j - R)
      (fun j ↦ coordinate (0 : EuclideanPoint d) j + R) := by
    intro y hy j
    have hynorm : ‖y‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hQball hy
    have habs : |coordinate y j| ≤ R := by
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le y j).trans hynorm
    have hzero : coordinate (0 : EuclideanPoint d) j = 0 := by rfl
    simpa only [hzero, zero_sub, zero_add] using (abs_le.mp habs)
  have hcoord (x : EuclideanPoint d) :
      coordinate (T x) i = directionalValue u x := by
    change coordinate (T x) i = inner ℝ u x
    rw [← T.inner_map_map u x, hTu]
    simp only [e, EuclideanSpace.inner_single_left, map_one, one_mul]
  have himage :
      (fun y : EuclideanPoint d ↦ coordinate y i) '' Q =
        directionalValue u '' P := by
    ext r
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hcoord x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨T x, ⟨x, hx, rfl⟩, hcoord x⟩
  have hQwidth : coordinateWidth Q i = directionalWidth P u := by
    rw [coordinateWidth, coordinateUpper, coordinateLower,
      directionalWidth, supportUpper, supportLower, himage]
  have hQvol : volume Q = volume P := by
    have hpre : Q = ⇑T.symm ⁻¹' P := by
      ext y
      simp only [Q, mem_image, mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        exact ⟨T.symm y, hy, T.apply_symm_apply y⟩
    rw [hpre]
    rw [← Measure.map_apply T.symm.continuous.measurable hP.measurableSet,
      (LinearIsometryEquiv.measurePreserving T.symm).map_eq]
  have hvol := volume_le_coordinateWidth_mul_cube
    hQcomp hQne (0 : EuclideanPoint d) hR hQcube i
  rwa [hQvol, hQwidth] at hvol

/-- **Quantitative width-to-inball theorem.**  A nonempty compact convex set in
`d`-dimensional Euclidean space whose width in every unit direction is at least
`w ≥ 0` contains a closed ball of radius `w / (d + 1)`.

The constant is completely explicit and the result does not require an ambient
cube bound. -/
theorem exists_closedBall_width_div_succ_subset {d : ℕ}
    {P : Set (EuclideanPoint d)} (hPconv : Convex ℝ P)
    (hPcomp : IsCompact P) (hPne : P.Nonempty) {w : ℝ} (hw : 0 ≤ w)
    (hwidth : ∀ u : EuclideanPoint d, ‖u‖ = 1 →
      w ≤ directionalWidth P u) :
    ∃ c ∈ P, Metric.closedBall c (w / ((d + 1 : ℕ) : ℝ)) ⊆ P := by
  obtain ⟨c, hc⟩ :=
    exists_center_inv_succ_smul_sub_mem hPconv hPcomp hPne
  obtain ⟨p0, hp0⟩ := hPne
  have hcP : c ∈ P := by
    simpa using hc p0 hp0 p0 hp0
  refine ⟨c, hcP, ?_⟩
  intro x hx
  let N : ℝ := ((d + 1 : ℕ) : ℝ)
  have hN : 0 < N := by
    dsimp only [N]
    positivity
  let z : EuclideanPoint d := N • (x - c)
  have hxnorm : ‖x - c‖ ≤ w / N := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, N] using hx
  have hzball : z ∈ Metric.closedBall (0 : EuclideanPoint d) w := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simp only [z, norm_smul, Real.norm_eq_abs, abs_of_pos hN]
    calc
      N * ‖x - c‖ ≤ N * (w / N) :=
        mul_le_mul_of_nonneg_left hxnorm hN.le
      _ = w := by field_simp
  have hzD := closedBall_zero_subset_sub_of_forall_width
    hPconv hPcomp ⟨p0, hp0⟩ hw hwidth hzball
  rw [Set.mem_sub] at hzD
  obtain ⟨p, hp, q, hq, hpq⟩ := hzD
  have hmem := hc p hp q hq
  rw [hpq] at hmem
  dsimp only [z, N] at hmem
  have hcast : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [smul_smul, inv_mul_cancel₀ hcast, one_smul] at hmem
  convert hmem using 1 <;> module

/-- The quantitative inball theorem, packaged for `IsConvexBody`. -/
theorem IsConvexBody.exists_closedBall_width_div_succ_subset {d : ℕ}
    {P : Set (EuclideanPoint d)} (hP : IsConvexBody P) {w : ℝ} (hw : 0 ≤ w)
    (hwidth : ∀ u : EuclideanPoint d, ‖u‖ = 1 →
      w ≤ directionalWidth P u) :
    ∃ c ∈ P, Metric.closedBall c (w / ((d + 1 : ℕ) : ℝ)) ⊆ P :=
  Erdos186.PZ.ConvexDensity.exists_closedBall_width_div_succ_subset
    hP.convex hP.isCompact hP.nonempty hw hwidth

/-- **Volume-to-inball theorem.**  If a nonempty compact convex set in the
radius-`R` ball has volume at least `v`, it contains a closed ball of radius
`(v / (2R)^(d-1)) / (d+1)`. -/
theorem exists_closedBall_volume_div_ball_subset {d : ℕ} (hd : 0 < d)
    {P : Set (EuclideanPoint d)} (hPconv : Convex ℝ P)
    (hPcomp : IsCompact P) (hPne : P.Nonempty)
    {R v : ℝ} (hR : 0 < R) (hv : 0 ≤ v)
    (hball : P ⊆ Metric.closedBall (0 : EuclideanPoint d) R)
    (hvolume : ENNReal.ofReal v ≤ volume P) :
    ∃ c ∈ P, Metric.closedBall c
      ((v / (2 * R) ^ (d - 1)) / ((d + 1 : ℕ) : ℝ)) ⊆ P := by
  let B : ℝ := (2 * R) ^ (d - 1)
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hwidth : ∀ u : EuclideanPoint d, ‖u‖ = 1 →
      v / B ≤ directionalWidth P u := by
    intro u hu
    have hupper := volume_le_directionalWidth_mul_ball
      hd hPcomp hPne hR.le hball u hu
    have hENN : ENNReal.ofReal v ≤
        ENNReal.ofReal B * ENNReal.ofReal (directionalWidth P u) := by
      calc
        ENNReal.ofReal v ≤ volume P := hvolume
        _ ≤ ENNReal.ofReal (2 * R) ^ (d - 1) *
            ENNReal.ofReal (directionalWidth P u) := hupper
        _ = ENNReal.ofReal B * ENNReal.ofReal (directionalWidth P u) := by
          rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * R)]
    have hmul : v ≤ B * directionalWidth P u := by
      apply (ENNReal.ofReal_le_ofReal_iff ?_).mp
      · rw [ENNReal.ofReal_mul hB.le]
        exact hENN
      · exact mul_nonneg hB.le (directionalWidth_nonneg hPcomp hPne u)
    apply (div_le_iff₀ hB).mpr
    simpa only [mul_comm] using hmul
  simpa only [B] using exists_closedBall_width_div_succ_subset
    hPconv hPcomp hPne (div_nonneg hv hB.le) hwidth

/-- The volume-to-inball theorem, packaged for `IsConvexBody`. -/
theorem IsConvexBody.exists_closedBall_volume_div_ball_subset {d : ℕ}
    (hd : 0 < d) {P : Set (EuclideanPoint d)} (hP : IsConvexBody P)
    {R v : ℝ} (hR : 0 < R) (hv : 0 ≤ v)
    (hball : P ⊆ Metric.closedBall (0 : EuclideanPoint d) R)
    (hvolume : ENNReal.ofReal v ≤ volume P) :
    ∃ c ∈ P, Metric.closedBall c
      ((v / (2 * R) ^ (d - 1)) / ((d + 1 : ℕ) : ℝ)) ⊆ P :=
  Erdos186.PZ.ConvexDensity.exists_closedBall_volume_div_ball_subset
    hd hP.convex hP.isCompact hP.nonempty hR hv hball hvolume

end

end Erdos186.PZ.ConvexDensity

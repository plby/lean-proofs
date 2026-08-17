/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.CarrierFive
import ErdosProblems.Erdos223.CompleteBipartiteGeometry
import ErdosProblems.Erdos223.Lenz
import ErdosProblems.Erdos223.LenzOptimization
import ErdosProblems.Erdos223.LocalCircle
import ErdosProblems.Erdos223.SphericalThrackle

/-!
# Local diameter estimates on a two-sphere

This file packages the local spherical estimates used in the odd-dimensional
Lenz optimization for Erdős Problem 223.  The carrier sphere is represented
inside `Point 3`; an isometric identification of a three-dimensional carrier
with `Point 3` preserves all of the hypotheses below.
-/

open Metric
open scoped RealInnerProductSpace SimpleGraph

namespace Erdos223
namespace LocalSphere

noncomputable section

/-- Every point of `A` lies on the sphere with centre `c` and radius `r`. -/
def IsOnSphere {d : ℕ} (A : Finset (Point d)) (c : Point d) (r : ℝ) : Prop :=
  ∀ x ∈ A, dist x c = r

lemma IsOnSphere.radius_nonneg {d : ℕ} {A : Finset (Point d)}
    {c : Point d} {r : ℝ} (hA : A.Nonempty) (h : IsOnSphere A c r) : 0 ≤ r := by
  obtain ⟨x, hx⟩ := hA
  rw [← h x hx]
  exact dist_nonneg

/-- A finite spherical configuration contained in a rank-three linear
carrier through its center has an isometric model in `Point 3`.  Cardinality,
radius, and the number of unit pairs are all preserved. -/
theorem exists_pointThree_model_of_mem_sphere_in_finrank_three
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    (U : Submodule ℝ (Point d)) (hfin : Module.finrank ℝ U = 3)
    (hU : ∀ x ∈ A, x - c ∈ U) (hsphere : IsOnSphere A c r) :
    ∃ B : Finset (Point 3), B.card = A.card ∧ IsOnSphere B 0 r ∧
      diameterPairCount B = diameterPairCount A ∧
      (IsDiameterOne B ↔ IsDiameterOne A) := by
  classical
  let basis : OrthonormalBasis (Fin 3) ℝ U :=
    (stdOrthonormalBasis ℝ U).reindex (finCongr hfin)
  let coord : U ≃ₗᵢ[ℝ] Point 3 := basis.repr
  let emb : {x : Point d // x ∈ A} ↪ Point 3 :=
    { toFun := fun x ↦ coord ⟨x.1 - c, hU x.1 x.2⟩
      inj' := by
        intro x y hxy
        have hv : (⟨x.1 - c, hU x.1 x.2⟩ : U) =
            ⟨y.1 - c, hU y.1 y.2⟩ := coord.injective hxy
        apply Subtype.ext
        have := congrArg ((↑) : U → Point d) hv
        simpa only [Submodule.coe_mk] using sub_left_injective this }
  let B : Finset (Point 3) := Finset.univ.map emb
  have hmem (x : {x : Point d // x ∈ A}) : emb x ∈ B := by
    exact Finset.mem_map.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hcard : B.card = A.card := by simp [B]
  have hdist (x y : {x : Point d // x ∈ A}) :
      dist (emb x) (emb y) = dist x.1 y.1 := by
    rw [dist_eq_norm, dist_eq_norm]
    change ‖coord ⟨x.1 - c, hU x.1 x.2⟩ -
        coord ⟨y.1 - c, hU y.1 y.2⟩‖ = ‖x.1 - y.1‖
    rw [← coord.map_sub, coord.norm_map]
    change ‖(x.1 - c) - (y.1 - c)‖ = ‖x.1 - y.1‖
    congr 1
    abel
  have hB_sphere : IsOnSphere B 0 r := by
    intro z hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hz
    rw [dist_zero_right]
    change ‖coord ⟨x.1 - c, hU x.1 x.2⟩‖ = r
    rw [coord.norm_map]
    change ‖x.1 - c‖ = r
    simpa [dist_eq_norm] using hsphere x.1 x.2
  let e : {x : Point d // x ∈ A} ≃ {z : Point 3 // z ∈ B} :=
    Equiv.ofBijective
      (fun x ↦ (⟨emb x, hmem x⟩ : {z : Point 3 // z ∈ B}))
      ⟨fun x y h ↦ emb.injective (congrArg Subtype.val h), by
        intro z
        obtain ⟨x, -, hx⟩ := Finset.mem_map.mp z.2
        exact ⟨x, Subtype.ext hx⟩⟩
  let iso : diameterGraph A ≃g diameterGraph B :=
    ⟨e, by
      intro x y
      change dist (emb x) (emb y) = 1 ↔ dist x.1 y.1 = 1
      rw [hdist]⟩
  have hcount : diameterPairCount B = diameterPairCount A := by
    simp only [diameterPairCount]
    exact iso.card_edgeFinset_eq.symm
  have hdiam : IsDiameterOne B ↔ IsDiameterOne A := by
    rw [isDiameterOne_iff, isDiameterOne_iff]
    constructor
    · rintro ⟨hle, z, hz, w, hw, hzw⟩
      refine ⟨?_, ?_⟩
      · intro x hx y hy
        let xA : {x : Point d // x ∈ A} := ⟨x, hx⟩
        let yA : {x : Point d // x ∈ A} := ⟨y, hy⟩
        rw [← hdist xA yA]
        exact hle (emb xA) (hmem xA) (emb yA) (hmem yA)
      · obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hz
        obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hw
        exact ⟨x.1, x.2, y.1, y.2, by simpa [hdist] using hzw⟩
    · rintro ⟨hle, x, hx, y, hy, hxy⟩
      refine ⟨?_, ?_⟩
      · intro z hz w hw
        obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hz
        obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hw
        rw [hdist]
        exact hle x.1 x.2 y.1 y.2
      · let xA : {x : Point d // x ∈ A} := ⟨x, hx⟩
        let yA : {x : Point d // x ∈ A} := ⟨y, hy⟩
        exact ⟨emb xA, hmem xA, emb yA, hmem yA, by simpa [hdist] using hxy⟩
  exact ⟨B, hcard, hB_sphere, hcount, hdiam⟩

/-- An upper bound known for configurations of cardinality at least four
extends to all finite configurations.  The three small cases use only the
trivial `choose 2` bound. -/
lemma diameterPairCount_le_two_mul_card_sub_two_of_large_bound
    (hlarge : ∀ A : Finset (Point 3), 4 ≤ A.card → IsDiameterOne A →
      diameterPairCount A ≤ 2 * A.card - 2)
    (A : Finset (Point 3)) (hA : IsDiameterOne A) :
    diameterPairCount A ≤ 2 * A.card - 2 := by
  by_cases hcard : 4 ≤ A.card
  · exact hlarge A hcard hA
  · have hchoose := diameterPairCount_le_choose A
    have hc : A.card ≤ 3 := by omega
    interval_cases A.card <;> simp at hchoose ⊢ <;> omega

/-- Additive form of the preceding reduction, avoiding truncated subtraction.
This is the convenient form for the finite optimization of the sphere part. -/
lemma diameterPairCount_add_two_le_two_mul_card_of_large_bound
    (hlarge : ∀ A : Finset (Point 3), 4 ≤ A.card → IsDiameterOne A →
      diameterPairCount A ≤ 2 * A.card - 2)
    (A : Finset (Point 3)) (hcard : 2 ≤ A.card) (hA : IsDiameterOne A) :
    diameterPairCount A + 2 ≤ 2 * A.card := by
  have h := diameterPairCount_le_two_mul_card_sub_two_of_large_bound hlarge A hA
  omega

/-- The sharp large-radius local estimate: on a two-sphere of radius at
least `1 / sqrt 2`, there is at most one diameter pair per point. -/
theorem diameterPairCount_le_card_of_onSphere_of_invSqrtTwo_le_radius
    {A : Finset (Point 3)} {c : Point 3} {r : ℝ}
    (hsphere : IsOnSphere A c r) (hr : 1 / Real.sqrt 2 ≤ r)
    (hA : IsDiameterOne A) : diameterPairCount A ≤ A.card :=
  SphericalThrackle.diameterPairCount_le_card hsphere hr hA

/-- Coordinate-free rank-three form of the large-radius sphere estimate.
This is the form consumed by a three-sphere sitting inside `Point 5`. -/
theorem diameterPairCount_le_card_of_mem_sphere_in_finrank_three
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    (U : Submodule ℝ (Point d)) (hfin : Module.finrank ℝ U = 3)
    (hU : ∀ x ∈ A, x - c ∈ U) (hsphere : IsOnSphere A c r)
    (hr : 1 / Real.sqrt 2 ≤ r) (hA : IsDiameterOne A) :
    diameterPairCount A ≤ A.card := by
  obtain ⟨B, hcard, hBsphere, hcount, hdiam⟩ :=
    exists_pointThree_model_of_mem_sphere_in_finrank_three
      U hfin hU hsphere
  have hB := diameterPairCount_le_card_of_onSphere_of_invSqrtTwo_le_radius
    hBsphere hr (hdiam.mpr hA)
  omega

/-- Additive `2m - 2` form of the large-radius estimate.  The stronger
one-edge-per-point estimate above is what makes this immediate. -/
theorem diameterPairCount_add_two_le_two_mul_card_of_onSphere_of_invSqrtTwo_le_radius
    {A : Finset (Point 3)} {c : Point 3} {r : ℝ}
    (hsphere : IsOnSphere A c r) (hr : 1 / Real.sqrt 2 ≤ r)
    (hcard : 2 ≤ A.card) (hA : IsDiameterOne A) :
    diameterPairCount A + 2 ≤ 2 * A.card := by
  have h := diameterPairCount_le_card_of_onSphere_of_invSqrtTwo_le_radius
    hsphere hr hA
  omega

/-! ## The dimension-five sphere--circle dichotomy -/

/-- Orthogonal affine spans meet when their direction dimensions exhaust the
ambient finite-dimensional inner-product space.  This is the valid alignment
criterion behind the dimension-five sphere--circle carrier: dimensions
`3 + 2 = 5` rule out an axial shift.  Without the dimension equality (for
example, two circles in `ℝ⁵`) the conclusion is deliberately unavailable. -/
theorem exists_mem_affineSpans_of_direction_isOrtho_of_finrank_add
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A B : Set E}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (horth : (affineSpan ℝ A).direction ⟂ (affineSpan ℝ B).direction)
    (hfin : Module.finrank ℝ (affineSpan ℝ A).direction +
      Module.finrank ℝ (affineSpan ℝ B).direction = Module.finrank ℝ E) :
    ∃ c : E, c ∈ affineSpan ℝ A ∧ c ∈ affineSpan ℝ B := by
  classical
  let SA : AffineSubspace ℝ E := affineSpan ℝ A
  let SB : AffineSubspace ℝ E := affineSpan ℝ B
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  let _ : Nonempty SA := ⟨⟨a, mem_affineSpan ℝ ha⟩⟩
  let c : E := EuclideanGeometry.orthogonalProjection SA b
  have hcA : c ∈ SA := EuclideanGeometry.orthogonalProjection_mem _
  have hle : SB.direction ≤ SA.directionᗮ := by
    intro v hv
    exact horth.ge hv
  have horthfin := SA.direction.finrank_add_finrank_orthogonal
  have hfin' : Module.finrank ℝ SA.direction +
      Module.finrank ℝ SB.direction = Module.finrank ℝ E := by
    simpa [SA, SB] using hfin
  have hdim : Module.finrank ℝ SA.directionᗮ ≤
      Module.finrank ℝ SB.direction := by omega
  have heq : SB.direction = SA.directionᗮ :=
    Submodule.eq_of_le_of_finrank_le hle hdim
  have hbc : b -ᵥ c ∈ SA.directionᗮ := by
    simpa [c] using
      EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal SA b
  have hcb : c -ᵥ b ∈ SB.direction := by
    have : b -ᵥ c ∈ SB.direction := by simpa [heq] using hbc
    simpa only [vsub_eq_sub, neg_sub] using SB.direction.neg_mem this
  have hcB : c ∈ SB := by
    have := AffineSubspace.vadd_mem_of_mem_direction hcb (mem_affineSpan ℝ hb)
    simpa only [vsub_vadd] using this
  exact ⟨c, by simpa [SA] using hcA, by simpa [SB] using hcB⟩

/-- Once two orthogonal affine spans have a common point, a constant unit
cross-distance makes the two sets cospherical about that point, with
complementary squared radii.  Combined with the preceding theorem this is
the valid common-center conclusion in the complementary-dimension case. -/
theorem exists_complementary_radii_of_common_affine_center
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B : Set E} {c : E}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hcA : c ∈ affineSpan ℝ A) (hcB : c ∈ affineSpan ℝ B)
    (horth : (affineSpan ℝ A).direction ⟂ (affineSpan ℝ B).direction)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, dist a b = 1) :
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧
      (∀ a ∈ A, dist a c = r) ∧
      (∀ b ∈ B, dist b c = s) ∧ r ^ 2 + s ^ 2 = 1 := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  have hpythag (a : E) (ha : a ∈ A) (b : E) (hb : b ∈ B) :
      dist a b ^ 2 = dist a c ^ 2 + dist b c ^ 2 := by
    have hac : a - c ∈ (affineSpan ℝ A).direction :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ ha) hcA
    have hbc : b - c ∈ (affineSpan ℝ B).direction :=
      AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hb) hcB
    have hi0 : inner ℝ (a - c) (b - c) = 0 := horth.inner_eq hac hbc
    have hi : inner ℝ (a - c) (c - b) = 0 := by
      rw [show c - b = -(b - c) by abel, inner_neg_right, hi0, neg_zero]
    calc
      dist a b ^ 2 =
          ‖(a - c) + (c - b)‖ * ‖(a - c) + (c - b)‖ := by
            rw [dist_eq_norm, pow_two]
            congr 1 <;> abel_nf
      _ = ‖a - c‖ * ‖a - c‖ + ‖c - b‖ * ‖c - b‖ :=
        norm_add_sq_eq_norm_sq_add_norm_sq_real hi
      _ = dist a c ^ 2 + dist b c ^ 2 := by
        rw [dist_eq_norm, dist_eq_norm, pow_two, pow_two, norm_sub_rev c b]
  let r := dist a₀ c
  let s := dist b₀ c
  have hAr : ∀ a ∈ A, dist a c = r := by
    intro a ha
    have h := hpythag a ha b₀ hb₀
    have h₀ := hpythag a₀ ha₀ b₀ hb₀
    rw [hcross a ha b₀ hb₀] at h
    rw [hcross a₀ ha₀ b₀ hb₀] at h₀
    have ha0 : 0 ≤ dist a c := dist_nonneg
    have hr0 : 0 ≤ r := by dsimp [r]; exact dist_nonneg
    dsimp [r, s] at h h₀ ⊢
    nlinarith
  have hBs : ∀ b ∈ B, dist b c = s := by
    intro b hb
    have h := hpythag a₀ ha₀ b hb
    have h₀ := hpythag a₀ ha₀ b₀ hb₀
    rw [hcross a₀ ha₀ b hb] at h
    rw [hcross a₀ ha₀ b₀ hb₀] at h₀
    have hb0 : 0 ≤ dist b c := dist_nonneg
    have hs0 : 0 ≤ s := by dsimp [s]; exact dist_nonneg
    dsimp [r, s] at h h₀ ⊢
    nlinarith
  have hrs := hpythag a₀ ha₀ b₀ hb₀
  rw [hcross a₀ ha₀ b₀ hb₀] at hrs
  exact ⟨r, s, dist_nonneg, dist_nonneg, hAr, hBs,
    by simpa [r, s] using hrs.symm⟩

/-- Corrected complete-bipartite geometry in the complementary-dimensional
case.  Unlike the false unrestricted common-center formulation, this theorem
requires the two affine direction dimensions to fill the ambient space. -/
theorem completeBipartiteGeometry_of_finrank_add
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {A B : Set E}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, dist a b = 1)
    (hfin : Module.finrank ℝ (affineSpan ℝ A).direction +
      Module.finrank ℝ (affineSpan ℝ B).direction = Module.finrank ℝ E) :
    ∃ c : E, ∃ r s : ℝ,
      c ∈ affineSpan ℝ A ∧ c ∈ affineSpan ℝ B ∧
      0 ≤ r ∧ 0 ≤ s ∧
      (∀ a ∈ A, dist a c = r) ∧
      (∀ b ∈ B, dist b c = s) ∧ r ^ 2 + s ^ 2 = 1 := by
  have horth := affineSpan_direction_isOrtho_of_cross_dist_eq hA hB 1 hcross
  obtain ⟨c, hcA, hcB⟩ :=
    exists_mem_affineSpans_of_direction_isOrtho_of_finrank_add
      hA hB horth hfin
  obtain ⟨r, s, hr0, hs0, hAr, hBs, hrs⟩ :=
    exists_complementary_radii_of_common_affine_center
      hA hB hcA hcB horth hcross
  exact ⟨c, r, s, hcA, hcB, hr0, hs0, hAr, hBs, hrs⟩

/-- If nonnegative radii satisfy `r² + s² = 1`, a sphere radius below
`1 / sqrt 2` forces the complementary circle radius above `1 / sqrt 3`.
The latter is the strict threshold in the large-circle local theorem. -/
theorem invSqrtThree_lt_of_sq_add_sq_eq_one_of_lt_invSqrtTwo
    {r s : ℝ} (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hrs : r ^ 2 + s ^ 2 = 1) (hr : r < 1 / Real.sqrt 2) :
    1 / Real.sqrt 3 < s := by
  have htwo : 0 < (1 / Real.sqrt 2 : ℝ) := by positivity
  have hthree : 0 < (1 / Real.sqrt 3 : ℝ) := by positivity
  have htwo_sq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hthree_sq : (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hr_sq : r ^ 2 < 1 / 2 := by
    have hprod : 0 < (1 / Real.sqrt 2 - r) * (1 / Real.sqrt 2 + r) :=
      mul_pos (sub_pos.mpr hr) (add_pos_of_pos_of_nonneg htwo hr0)
    nlinarith [htwo_sq]
  have hs_sq : 1 / 2 < s ^ 2 := by nlinarith
  by_contra hnot
  have hsle : s ≤ 1 / Real.sqrt 3 := le_of_not_gt hnot
  have hprod :
      0 ≤ (1 / Real.sqrt 3 - s) * (1 / Real.sqrt 3 + s) :=
    mul_nonneg (sub_nonneg.mpr hsle) (add_nonneg hthree.le hs0)
  nlinarith [hthree_sq]

private theorem turanNumber_two_add_two (n : ℕ) :
    turanNumber 2 (n + 2) = turanNumber 2 n + n + 1 := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    turanNumber_two_succ, turanNumber_two_succ]
  have hceil : ceilQuot n 2 + ceilQuot (n + 1) 2 = n + 1 := by
    unfold ceilQuot
    omega
  omega

/-- The numerical estimate for the small-sphere branch in dimension five.
Here `sphereLocal + 2 ≤ 2 * sphere` is Vázsonyi's local bound, while
`circleLocal ≤ 1` is the large-circle bound.  The shifted product
`sphere * (circle + 2)` gives the sharp optimization without any balance
assumption on the two carrier classes. -/
theorem five_smallSphere_upper_of_carrier
    {sphere circle n sphereLocal circleLocal edges : ℕ}
    (hsum : sphere + circle = n)
    (hsphere : sphereLocal + 2 ≤ 2 * sphere)
    (hcircle : circleLocal ≤ 1)
    (hedges : edges ≤ sphere * circle + sphereLocal + circleLocal) :
    edges ≤ turanNumber 2 n + n := by
  have hshift : sphere + (circle + 2) = n + 2 := by omega
  have hproduct : sphere * (circle + 2) ≤ turanNumber 2 (n + 2) :=
    mul_le_turanNumber_two hshift
  have hedges_add_one : edges + 1 ≤ sphere * (circle + 2) := by
    rw [mul_add]
    omega
  rw [turanNumber_two_add_two] at hproduct
  omega

/-- Complete numerical form of the dimension-five sphere--circle local
dichotomy.  The four local hypotheses are deliberately implications: this
lets a carrier proof discharge them after separating empty or edgeless
parts, without falsely assuming that each part itself has diameter one.

If `r ≥ 1 / sqrt 2`, both local counts are bounded by their class sizes. If
`r < 1 / sqrt 2`, the complementary radius is greater than `1 / sqrt 3`, so
the circle contributes at most one edge and the shifted small-sphere
estimate applies. -/
theorem five_sphereCircle_upper_of_radius_dichotomy
    {sphere circle n sphereLocal circleLocal edges : ℕ} {r s : ℝ}
    (hsum : sphere + circle = n) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hrs : r ^ 2 + s ^ 2 = 1)
    (hsphereLarge : 1 / Real.sqrt 2 ≤ r → sphereLocal ≤ sphere)
    (hsphereSmall : r < 1 / Real.sqrt 2 → sphereLocal + 2 ≤ 2 * sphere)
    (hcircleGeneral : circleLocal ≤ circle)
    (hcircleLarge : 1 / Real.sqrt 3 < s → circleLocal ≤ 1)
    (hedges : edges ≤ sphere * circle + sphereLocal + circleLocal) :
    edges ≤ turanNumber 2 n + n := by
  by_cases hr : 1 / Real.sqrt 2 ≤ r
  · apply five_upper_of_carrier hsum
      (localEdges := sphereLocal + circleLocal) (e := edges)
    · have := hsphereLarge hr
      omega
    · simpa [add_assoc] using hedges
  · have hr' : r < 1 / Real.sqrt 2 := lt_of_not_ge hr
    exact five_smallSphere_upper_of_carrier hsum (hsphereSmall hr')
      (hcircleLarge
        (invSqrtThree_lt_of_sq_add_sq_eq_one_of_lt_invSqrtTwo
          hr0 hs0 hrs hr')) hedges

/-- A positive unit-chord count, together with the inherited diameter-at-most
one condition, upgrades a carrier part to `IsDiameterOne`.  Carrier parts in
an ambient diameter-one configuration frequently have no internal edge, so
this zero/nonzero wrapper avoids imposing a false nonemptiness hypothesis. -/
theorem isDiameterOne_of_diameterPairCount_pos_of_dist_le
    {d : ℕ} {A : Finset (Point d)}
    (hdist : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    (hpos : 0 < diameterPairCount A) : IsDiameterOne A := by
  classical
  rw [isDiameterOne_iff]
  refine ⟨hdist, ?_⟩
  have hne : (diameterGraph A).edgeFinset.Nonempty := by
    rw [← Finset.card_pos]
    simpa [diameterPairCount] using hpos
  obtain ⟨e, he⟩ := hne
  revert he
  refine Sym2.inductionOn e ?_
  intro x y hxy
  rw [SimpleGraph.mem_edgeFinset] at hxy
  exact ⟨(x : Point d), x.property, (y : Point d), y.property, hxy⟩

/-- Large-radius spherical bound for a part inherited from a larger
diameter-one configuration.  No internal diameter is required. -/
theorem diameterPairCount_le_card_of_onSphere_of_invSqrtTwo_le_radius_of_dist_le
    {A : Finset (Point 3)} {c : Point 3} {r : ℝ}
    (hsphere : IsOnSphere A c r) (hr : 1 / Real.sqrt 2 ≤ r)
    (hdist : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) :
    diameterPairCount A ≤ A.card := by
  by_cases hz : diameterPairCount A = 0
  · simp [hz]
  · exact diameterPairCount_le_card_of_onSphere_of_invSqrtTwo_le_radius
      hsphere hr
        (isDiameterOne_of_diameterPairCount_pos_of_dist_le hdist
          (Nat.pos_of_ne_zero hz))

/-- Rank-three carrier version of the preceding zero-edge-safe wrapper. -/
theorem diameterPairCount_le_card_of_mem_sphere_in_finrank_three_of_dist_le
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    (U : Submodule ℝ (Point d)) (hfin : Module.finrank ℝ U = 3)
    (hU : ∀ x ∈ A, x - c ∈ U) (hsphere : IsOnSphere A c r)
    (hr : 1 / Real.sqrt 2 ≤ r)
    (hdist : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) :
    diameterPairCount A ≤ A.card := by
  by_cases hz : diameterPairCount A = 0
  · simp [hz]
  · exact diameterPairCount_le_card_of_mem_sphere_in_finrank_three
      U hfin hU hsphere hr
        (isDiameterOne_of_diameterPairCount_pos_of_dist_le hdist
          (Nat.pos_of_ne_zero hz))

/-- Large-circle bound for a carrier part inherited from an ambient
diameter-one configuration, including the internally edgeless case. -/
theorem diameterPairCount_circle_le_one_of_radius_gt_of_dist_le
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)}
    (hcircle : LocalCircle.IsOnCircle A c r P)
    (hr : 1 / Real.sqrt 3 < r)
    (hdist : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) :
    diameterPairCount A ≤ 1 := by
  by_cases hz : diameterPairCount A = 0
  · simp [hz]
  · exact LocalCircle.diameterPairCount_le_one_of_radius_gt
      (isDiameterOne_of_diameterPairCount_pos_of_dist_le hdist
        (Nat.pos_of_ne_zero hz)) hcircle hr

/-- The shifted all-concyclic dimension-five branch is harmless for the
upper bound: no relation between the two circle centers or radii is needed.
Each circle contributes at most one unit chord per vertex. -/
theorem five_circleCircle_upper
    {d : ℕ} {A B : Finset (Point d)}
    {ca cb : Point d} {ra rb : ℝ}
    {PA PB : AffineSubspace ℝ (Point d)}
    (hA : LocalCircle.IsOnCircle A ca ra PA)
    (hB : LocalCircle.IsOnCircle B cb rb PB) :
    A.card * B.card + diameterPairCount A + diameterPairCount B ≤
      turanNumber 2 (A.card + B.card) + (A.card + B.card) := by
  apply five_upper_of_carrier
    (sphere := A.card) (circle := B.card) (n := A.card + B.card) rfl
    (localEdges := diameterPairCount A + diameterPairCount B)
    (e := A.card * B.card + diameterPairCount A + diameterPairCount B)
  · exact Nat.add_le_add
      (LocalCircle.diameterPairCount_le_card hA)
      (LocalCircle.diameterPairCount_le_card hB)
  · omega

/-- Direct strong-carrier endpoint for dimension five.  `S` is the
three-dimensional sphere part and `C` the complementary circle part.  The
only external input is the unrestricted small-sphere Vázsonyi estimate;
all radius splitting, circle bounds, and zero-internal-edge cases are
discharged here. -/
theorem five_aligned_sphereCircle_upper
    {d : ℕ} {S : Finset (Point 3)} {C : Finset (Point d)}
    {cs : Point 3} {cc : Point d} {r s : ℝ}
    {P : AffineSubspace ℝ (Point d)}
    (hsphere : IsOnSphere S cs r)
    (hcircle : LocalCircle.IsOnCircle C cc s P)
    (hr0 : 0 ≤ r) (hs0 : 0 ≤ s) (hrs : r ^ 2 + s ^ 2 = 1)
    (hdistS : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hdistC : ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ 1)
    (hsphereSmall : r < 1 / Real.sqrt 2 →
      diameterPairCount S + 2 ≤ 2 * S.card) :
    S.card * C.card + diameterPairCount S + diameterPairCount C ≤
      turanNumber 2 (S.card + C.card) + (S.card + C.card) := by
  apply five_sphereCircle_upper_of_radius_dichotomy
    (sphere := S.card) (circle := C.card)
    (sphereLocal := diameterPairCount S)
    (circleLocal := diameterPairCount C)
    (edges := S.card * C.card + diameterPairCount S + diameterPairCount C)
    (r := r) (s := s) rfl hr0 hs0 hrs
  · intro hr
    exact diameterPairCount_le_card_of_onSphere_of_invSqrtTwo_le_radius_of_dist_le
      hsphere hr hdistS
  · exact hsphereSmall
  · exact LocalCircle.diameterPairCount_le_card hcircle
  · intro hs
    exact diameterPairCount_circle_le_one_of_radius_gt_of_dist_le
      hcircle hs hdistC
  · exact le_rfl

/-! ## Two-exception joins

The tempting pointwise replacement argument for the five-dimensional
problem is false: an odd regular polygon on a latitude of a large sphere can
be saturated by just two axial exceptional points.  The following two
lemmas record why adjoining an orthogonal companion circle to that family
still cannot violate the desired extremal estimate.  A circle joined to the
whole latitude polygon has a fixed axial centre.  It cannot be at unit
distance from both exceptional points, and even the deliberately generous
edge budget which lets one exception and every companion vertex contribute
is below `turanNumber 2 n + n`.
-/

/-- A circle all of whose points are unit-distant from a nondegenerate
latitude circle cannot simultaneously be unit-distant from the origin and
from an axial point on the opposite side of the latitude plane.

Here `rho` and `a` are the horizontal radius and height of the latitude,
`r` is its spherical radius, `t` and `s` are the axial centre and radius of
the companion circle, and `d < 0` is the second exceptional point's axial
coordinate. -/
theorem no_companion_circle_unit_to_both_axis_exceptions
    {rho a r d t s : ℝ}
    (hradius : rho ^ 2 + a ^ 2 = r ^ 2)
    (ha : 0 < a) (hr : 0 < r) (hd : d < 0)
    (hcross : rho ^ 2 + (a - t) ^ 2 + s ^ 2 = 1)
    (horigin : t ^ 2 + s ^ 2 = 1)
    (hother : (t - d) ^ 2 + s ^ 2 = 1) : False := by
  have hfactor : d * (d - 2 * t) = 0 := by
    nlinarith [hother, horigin]
  have hdt : d - 2 * t = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (ne_of_lt hd)
  have hart : r ^ 2 = 2 * a * t := by
    nlinarith [hradius, hcross, horigin]
  have had : a * d < 0 := mul_neg_of_pos_of_neg ha hd
  nlinarith [sq_pos_of_pos hr]

/-- Numerical upper bound for joining the saturated odd-latitude-polygon
counterexample to a companion block.  The budget consists of all
`polygon * companion` join edges, two linear contributions on the polygon
side, and two on the companion side.  It already overcounts the actual
construction, but remains strictly within the dimension-five target. -/
theorem five_two_exception_join_upper
    {polygon companion edges : ℕ}
    (hedges :
      edges ≤ polygon * companion + 2 * polygon + 2 * companion) :
    edges ≤
      turanNumber 2 (polygon + companion + 2) +
        (polygon + companion + 2) := by
  have hsum : (polygon + 1) + (companion + 1) =
      polygon + companion + 2 := by omega
  have hproduct :
      (polygon + 1) * (companion + 1) ≤
        turanNumber 2 (polygon + companion + 2) :=
    mul_le_turanNumber_two hsum
  simp only [add_mul, mul_add, mul_one, one_mul] at hproduct
  omega

/-! ## Transfer to the faithful shifted five-dimensional carrier -/

private theorem secondPlane_orthogonal_finrank
    (K : FiveWeakCarrier.Carrier) :
    Module.finrank ℝ K.secondPlane.directionᗮ = 3 := by
  have h := K.secondPlane.direction.finrank_add_finrank_orthogonal
  rw [K.second_finrank] at h
  have hambient : Module.finrank ℝ (Point 5) = 5 := by simp
  rw [hambient] at h
  omega

private theorem firstPlane_orthogonal_finrank
    (K : FiveWeakCarrier.Carrier) :
    Module.finrank ℝ K.firstPlane.directionᗮ = 3 := by
  have h := K.firstPlane.direction.finrank_add_finrank_orthogonal
  rw [K.first_finrank] at h
  have hambient : Module.finrank ℝ (Point 5) = 5 := by simp
  rw [hambient] at h
  omega

/-- The first weak-carrier sphere is an honest rank-three sphere, so its
large-radius local count is bounded by its number of points. -/
theorem fiveWeakCarrier_firstSphere_le_card
    (K : FiveWeakCarrier.Carrier) {A : Finset (Point 5)}
    (hmem : ∀ x ∈ A, x ∈ K.firstSphere)
    (hr : 1 / Real.sqrt 2 ≤ K.firstSphereRadius)
    (hdist : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) :
    diameterPairCount A ≤ A.card := by
  apply diameterPairCount_le_card_of_mem_sphere_in_finrank_three_of_dist_le
    K.secondPlane.directionᗮ (secondPlane_orthogonal_finrank K)
  · intro x hx
    exact (K.mem_firstSphere.mp (hmem x hx)).1
  · intro x hx
    exact (K.mem_firstSphere.mp (hmem x hx)).2
  · exact hr
  · exact hdist

/-- Symmetric large-radius estimate for the second weak-carrier sphere. -/
theorem fiveWeakCarrier_secondSphere_le_card
    (K : FiveWeakCarrier.Carrier) {A : Finset (Point 5)}
    (hmem : ∀ x ∈ A, x ∈ K.secondSphere)
    (hr : 1 / Real.sqrt 2 ≤ K.secondSphereRadius)
    (hdist : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) :
    diameterPairCount A ≤ A.card := by
  apply diameterPairCount_le_card_of_mem_sphere_in_finrank_three_of_dist_le
    K.firstPlane.directionᗮ (firstPlane_orthogonal_finrank K)
  · intro x hx
    exact (K.mem_secondSphere.mp (hmem x hx)).1
  · intro x hx
    exact (K.mem_secondSphere.mp (hmem x hx)).2
  · exact hr
  · exact hdist

private theorem isOnFirstCircle (K : FiveWeakCarrier.Carrier)
    {A : Finset (Point 5)} (hmem : ∀ x ∈ A, x ∈ K.firstCircle) :
    LocalCircle.IsOnCircle A K.firstCenter K.firstRadius K.firstPlane := by
  exact ⟨K.first_finrank, K.firstCenter_mem, hmem⟩

private theorem isOnSecondCircle (K : FiveWeakCarrier.Carrier)
    {A : Finset (Point 5)} (hmem : ∀ x ∈ A, x ∈ K.secondCircle) :
    LocalCircle.IsOnCircle A K.secondCenter K.secondRadius K.secondPlane := by
  exact ⟨K.second_finrank, K.secondCenter_mem, hmem⟩

/-- The genuinely shifted circle--circle branch of the five-dimensional weak
carrier already satisfies the target upper bound; no center alignment is
needed. -/
theorem fiveWeakCarrier_circleCircle_upper
    (K : FiveWeakCarrier.Carrier) {A B : Finset (Point 5)}
    (hA : ∀ x ∈ A, x ∈ K.firstCircle)
    (hB : ∀ x ∈ B, x ∈ K.secondCircle) :
    A.card * B.card + diameterPairCount A + diameterPairCount B ≤
      turanNumber 2 (A.card + B.card) + (A.card + B.card) :=
  five_circleCircle_upper (isOnFirstCircle K hA) (isOnSecondCircle K hB)

/-- Exact endpoint for the aligned first-sphere/second-circle branch of a
faithful five-dimensional weak carrier.  The only remaining input is the
unrestricted small-sphere Vázsonyi estimate. -/
theorem fiveWeakCarrier_firstSphere_secondCircle_upper
    (K : FiveWeakCarrier.Carrier) {S C : Finset (Point 5)}
    (hS : ∀ x ∈ S, x ∈ K.firstSphere)
    (hC : ∀ x ∈ C, x ∈ K.secondCircle)
    (hdistS : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hdistC : ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ 1)
    (hsmall : K.firstSphereRadius < 1 / Real.sqrt 2 →
      diameterPairCount S + 2 ≤ 2 * S.card) :
    S.card * C.card + diameterPairCount S + diameterPairCount C ≤
      turanNumber 2 (S.card + C.card) + (S.card + C.card) := by
  apply five_sphereCircle_upper_of_radius_dichotomy
    (sphere := S.card) (circle := C.card)
    (sphereLocal := diameterPairCount S)
    (circleLocal := diameterPairCount C)
    (edges := S.card * C.card + diameterPairCount S + diameterPairCount C)
    (r := K.firstSphereRadius) (s := K.secondRadius) rfl
    K.firstSphereRadius_nonneg K.secondRadius_nonneg K.first_cross_radius_sq
  · intro hr
    exact fiveWeakCarrier_firstSphere_le_card K hS hr hdistS
  · exact hsmall
  · exact LocalCircle.diameterPairCount_le_card (isOnSecondCircle K hC)
  · intro hr
    exact diameterPairCount_circle_le_one_of_radius_gt_of_dist_le
      (isOnSecondCircle K hC) hr hdistC
  · exact le_rfl

/-- Symmetric aligned branch with the second sphere active. -/
theorem fiveWeakCarrier_firstCircle_secondSphere_upper
    (K : FiveWeakCarrier.Carrier) {C S : Finset (Point 5)}
    (hC : ∀ x ∈ C, x ∈ K.firstCircle)
    (hS : ∀ x ∈ S, x ∈ K.secondSphere)
    (hdistC : ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ 1)
    (hdistS : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hsmall : K.secondSphereRadius < 1 / Real.sqrt 2 →
      diameterPairCount S + 2 ≤ 2 * S.card) :
    C.card * S.card + diameterPairCount C + diameterPairCount S ≤
      turanNumber 2 (C.card + S.card) + (C.card + S.card) := by
  have h := five_sphereCircle_upper_of_radius_dichotomy
    (sphere := S.card) (circle := C.card)
    (sphereLocal := diameterPairCount S)
    (circleLocal := diameterPairCount C)
    (edges := S.card * C.card + diameterPairCount S + diameterPairCount C)
    (r := K.secondSphereRadius) (s := K.firstRadius) rfl
    K.secondSphereRadius_nonneg K.firstRadius_nonneg
    (by nlinarith [K.second_cross_radius_sq])
    (fun hr ↦ fiveWeakCarrier_secondSphere_le_card K hS hr hdistS)
    hsmall (LocalCircle.diameterPairCount_le_card (isOnFirstCircle K hC))
    (fun hr ↦ diameterPairCount_circle_le_one_of_radius_gt_of_dist_le
      (isOnFirstCircle K hC) hr hdistC) le_rfl
  rw [Nat.mul_comm S.card C.card, Nat.add_comm S.card C.card] at h
  omega

/-! ## Sharpness at the radius threshold -/

namespace ThresholdConstruction

/-- Equally spaced algebraic parameters in the interval `[0,1]`. -/
private def parameter {k : ℕ} (_hk : 2 ≤ k) (i : Fin k) : ℝ :=
  (i : ℝ) / ((k - 1 : ℕ) : ℝ)

private lemma parameter_nonneg {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    0 ≤ parameter hk i := by
  unfold parameter
  positivity

private lemma parameter_le_one {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    parameter hk i ≤ 1 := by
  unfold parameter
  have hkpred : 0 < k - 1 := by omega
  rw [div_le_one (by exact_mod_cast hkpred : (0 : ℝ) < (k - 1 : ℕ))]
  exact_mod_cast Nat.le_pred_of_lt i.isLt

private lemma parameter_sq_le_one {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    parameter hk i ^ 2 ≤ 1 := by
  have h0 := parameter_nonneg hk i
  have h1 := parameter_le_one hk i
  nlinarith

private lemma parameter_injective {k : ℕ} (hk : 2 ≤ k) :
    Function.Injective (parameter hk) := by
  intro i j hij
  unfold parameter at hij
  have hkpred : 0 < k - 1 := by omega
  have hden : (((k - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hkpred.ne'
  apply Fin.ext
  exact_mod_cast (div_left_inj' hden).mp hij

/-- A point of the equatorial quarter-circle of radius `1 / sqrt 2`. -/
private def equatorPoint {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : Point 3 :=
  EuclideanSpace.single (0 : Fin 3) (Lenz.firstCoordinate (parameter hk i)) +
    EuclideanSpace.single (1 : Fin 3) (Lenz.secondCoordinate (parameter hk i))

/-- The pole orthogonal to the equatorial coordinate plane. -/
private def pole : Point 3 :=
  EuclideanSpace.single (2 : Fin 3) (1 / Real.sqrt 2)

private lemma equatorPoint_apply_one {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    equatorPoint hk i (1 : Fin 3) = Lenz.secondCoordinate (parameter hk i) := by
  simp [equatorPoint]

private lemma equatorPoint_apply_two {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    equatorPoint hk i (2 : Fin 3) = 0 := by
  simp [equatorPoint]

private lemma equatorPoint_injective {k : ℕ} (hk : 2 ≤ k) :
    Function.Injective (equatorPoint hk) := by
  intro i j hij
  have hcoord := congrArg (fun z : Point 3 ↦ z (1 : Fin 3)) hij
  rw [equatorPoint_apply_one, equatorPoint_apply_one] at hcoord
  exact parameter_injective hk (Lenz.secondCoordinate_injective hcoord)

private lemma pole_apply_two : pole (2 : Fin 3) = 1 / Real.sqrt 2 := by
  simp [pole]

private lemma equatorPoint_ne_pole {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    equatorPoint hk i ≠ pole := by
  intro h
  have hcoord := congrArg (fun z : Point 3 ↦ z (2 : Fin 3)) h
  rw [equatorPoint_apply_two, pole_apply_two] at hcoord
  have : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  linarith

/-- The threshold construction: `k` equatorial points and one pole. -/
private noncomputable def points {k : ℕ} (hk : 2 ≤ k) : Finset (Point 3) := by
  classical
  exact insert pole (Finset.univ.image (equatorPoint hk))

private lemma card_points {k : ℕ} (hk : 2 ≤ k) : (points hk).card = k + 1 := by
  rw [points, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ (equatorPoint_injective hk)]
    simp
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    push Not
    intro i
    exact equatorPoint_ne_pole hk i

private lemma inv_sqrt_two_sq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num
  rw [div_pow, one_pow, hs]

private lemma inner_equatorPoint_self {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    inner ℝ (equatorPoint hk i) (equatorPoint hk i) = 1 / 2 := by
  have hcoord := Lenz.coordinates_sq_add (parameter_sq_le_one hk i)
  simp only [equatorPoint, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply,
    starRingEnd_apply, star_trivial] at ⊢
  norm_num at ⊢
  simpa [pow_two] using hcoord

private lemma inner_pole_self : inner ℝ pole pole = 1 / 2 := by
  simp only [pole, EuclideanSpace.inner_single_left, PiLp.single_apply,
    starRingEnd_apply, star_trivial]
  norm_num
  simpa [pow_two] using inv_sqrt_two_sq

private lemma inner_equatorPoint_pole {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    inner ℝ (equatorPoint hk i) pole = 0 := by
  simp only [equatorPoint, pole, inner_add_left,
    EuclideanSpace.inner_single_left, PiLp.single_apply,
    starRingEnd_apply, star_trivial]
  rw [if_neg (by decide : (0 : Fin 3) ≠ 2),
    if_neg (by decide : (1 : Fin 3) ≠ 2)]
  norm_num

private lemma inner_equatorPoint {k : ℕ} (hk : 2 ≤ k) (i j : Fin k) :
    inner ℝ (equatorPoint hk i) (equatorPoint hk j) =
      Lenz.firstCoordinate (parameter hk i) * Lenz.firstCoordinate (parameter hk j) +
        Lenz.secondCoordinate (parameter hk i) * Lenz.secondCoordinate (parameter hk j) := by
  simp only [equatorPoint, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, PiLp.single_apply,
    starRingEnd_apply, star_trivial]
  norm_num

private lemma inner_equatorPoint_nonneg {k : ℕ} (hk : 2 ≤ k) (i j : Fin k) :
    0 ≤ inner ℝ (equatorPoint hk i) (equatorPoint hk j) := by
  rw [inner_equatorPoint]
  exact add_nonneg
    (mul_nonneg (Lenz.firstCoordinate_nonneg _) (Lenz.firstCoordinate_nonneg _))
    (mul_nonneg
      (Lenz.secondCoordinate_nonneg (parameter_nonneg hk i))
      (Lenz.secondCoordinate_nonneg (parameter_nonneg hk j)))

private lemma dist_equatorPoint_sq {k : ℕ} (hk : 2 ≤ k) (i j : Fin k) :
    dist (equatorPoint hk i) (equatorPoint hk j) ^ 2 =
      1 - 2 * inner ℝ (equatorPoint hk i) (equatorPoint hk j) := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [inner_equatorPoint_self, inner_equatorPoint_self,
    real_inner_comm (equatorPoint hk j) (equatorPoint hk i)]
  ring

private lemma dist_equatorPoint_le_one {k : ℕ} (hk : 2 ≤ k) (i j : Fin k) :
    dist (equatorPoint hk i) (equatorPoint hk j) ≤ 1 := by
  have hsq := dist_equatorPoint_sq hk i j
  have hi := inner_equatorPoint_nonneg hk i j
  have hd : 0 ≤ dist (equatorPoint hk i) (equatorPoint hk j) := dist_nonneg
  nlinarith

private lemma dist_equatorPoint_pole {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    dist (equatorPoint hk i) pole = 1 := by
  have hsq : dist (equatorPoint hk i) pole ^ 2 = 1 := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [inner_equatorPoint_self, inner_pole_self, inner_equatorPoint_pole]
    have hcross : inner ℝ pole (equatorPoint hk i) = 0 := by
      rw [real_inner_comm]
      exact inner_equatorPoint_pole hk i
    rw [hcross]
    ring
  have hd : 0 ≤ dist (equatorPoint hk i) pole := dist_nonneg
  nlinarith

private lemma dist_equatorPoint_zero {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    dist (equatorPoint hk i) 0 = 1 / Real.sqrt 2 := by
  have hsq : dist (equatorPoint hk i) 0 ^ 2 = 1 / 2 := by
    rw [dist_zero_right, ← real_inner_self_eq_norm_sq,
      inner_equatorPoint_self]
  have hd : 0 ≤ dist (equatorPoint hk i) 0 := dist_nonneg
  have hr : 0 < (1 / Real.sqrt 2 : ℝ) := by positivity
  nlinarith [inv_sqrt_two_sq]

private lemma dist_pole_zero : dist pole 0 = 1 / Real.sqrt 2 := by
  have hsq : dist pole 0 ^ 2 = 1 / 2 := by
    rw [dist_zero_right, ← real_inner_self_eq_norm_sq, inner_pole_self]
  have hd : 0 ≤ dist pole 0 := dist_nonneg
  have hr : 0 < (1 / Real.sqrt 2 : ℝ) := by positivity
  nlinarith [inv_sqrt_two_sq]

private lemma points_on_sphere {k : ℕ} (hk : 2 ≤ k) :
    IsOnSphere (points hk) 0 (1 / Real.sqrt 2) := by
  intro x hx
  rw [points] at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact dist_pole_zero
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact dist_equatorPoint_zero hk i

private lemma points_pairwise_dist_le_one {k : ℕ} (hk : 2 ≤ k) :
    ∀ x ∈ points hk, ∀ y ∈ points hk, dist x y ≤ 1 := by
  intro x hx y hy
  rw [points] at hx hy
  rcases Finset.mem_insert.mp hx with rfl | hx <;>
    rcases Finset.mem_insert.mp hy with rfl | hy
  · simp
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    simpa [dist_comm] using (dist_equatorPoint_pole hk j).le
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact (dist_equatorPoint_pole hk i).le
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    exact dist_equatorPoint_le_one hk i j

private lemma points_isDiameterOne {k : ℕ} (hk : 2 ≤ k) :
    IsDiameterOne (points hk) := by
  rw [isDiameterOne_iff]
  refine ⟨points_pairwise_dist_le_one hk, ?_⟩
  let i : Fin k := ⟨0, by omega⟩
  have hi : equatorPoint hk i ∈ points hk := by
    rw [points]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hp : pole ∈ points hk := by simp [points]
  exact ⟨equatorPoint hk i, hi, pole, hp, dist_equatorPoint_pole hk i⟩

private def first {k : ℕ} (hk : 2 ≤ k) : Fin k := ⟨0, by omega⟩

private def last {k : ℕ} (hk : 2 ≤ k) : Fin k :=
  ⟨k - 1, Nat.sub_lt (by omega) (by omega)⟩

private lemma parameter_first {k : ℕ} (hk : 2 ≤ k) :
    parameter hk (first hk) = 0 := by
  simp [parameter, first]

private lemma parameter_last {k : ℕ} (hk : 2 ≤ k) :
    parameter hk (last hk) = 1 := by
  simp only [parameter, last]
  have hkpred : 0 < k - 1 := by omega
  exact div_self (by exact_mod_cast hkpred.ne' : ((k - 1 : ℕ) : ℝ) ≠ 0)

private lemma dist_equatorPoint_first_last {k : ℕ} (hk : 2 ≤ k) :
    dist (equatorPoint hk (first hk)) (equatorPoint hk (last hk)) = 1 := by
  have hinner : inner ℝ (equatorPoint hk (first hk)) (equatorPoint hk (last hk)) = 0 := by
    rw [inner_equatorPoint, parameter_first, parameter_last]
    simp [Lenz.firstCoordinate, Lenz.secondCoordinate]
  have hsq := dist_equatorPoint_sq hk (first hk) (last hk)
  rw [hinner] at hsq
  have hd : 0 ≤ dist (equatorPoint hk (first hk)) (equatorPoint hk (last hk)) :=
    dist_nonneg
  nlinarith

private def equatorVertex {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    {x // x ∈ points hk} :=
  ⟨equatorPoint hk i, by
    rw [points]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩

private def poleVertex {k : ℕ} (hk : 2 ≤ k) : {x // x ∈ points hk} :=
  ⟨pole, by simp [points]⟩

private lemma pole_adj_equatorVertex {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    (diameterGraph (points hk)).Adj (poleVertex hk) (equatorVertex hk i) := by
  rw [diameterGraph_adj]
  change dist pole (equatorPoint hk i) = 1
  rw [dist_comm]
  exact dist_equatorPoint_pole hk i

private lemma equatorVertex_injective {k : ℕ} (hk : 2 ≤ k) :
    Function.Injective (equatorVertex hk) := by
  intro i j h
  apply equatorPoint_injective hk
  exact congrArg Subtype.val h

private lemma degree_poleVertex_ge {k : ℕ} (hk : 2 ≤ k) :
    k ≤ (diameterGraph (points hk)).degree (poleVertex hk) := by
  classical
  let e : Fin k → (diameterGraph (points hk)).neighborSet (poleVertex hk) :=
    fun i ↦ ⟨equatorVertex hk i, by
      exact pole_adj_equatorVertex hk i⟩
  have he : Function.Injective e := by
    intro i j hij
    exact equatorVertex_injective hk (congrArg Subtype.val hij)
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e he

private lemma diameterPairCount_points_ge {k : ℕ} (hk : 2 ≤ k) :
    k + 1 ≤ diameterPairCount (points hk) := by
  classical
  let G := diameterGraph (points hk)
  let p := poleVertex hk
  let u := equatorVertex hk (first hk)
  let v := equatorVertex hk (last hk)
  have huv : G.Adj u v := by
    rw [diameterGraph_adj]
    exact dist_equatorPoint_first_last hk
  have hup : u ≠ p := by
    intro h
    exact equatorPoint_ne_pole hk (first hk) (congrArg Subtype.val h)
  have hvp : v ≠ p := by
    intro h
    exact equatorPoint_ne_pole hk (last hk) (congrArg Subtype.val h)
  have hdelete : (G.deleteIncidenceSet p).Adj u v :=
    SimpleGraph.deleteIncidenceSet_adj.mpr ⟨huv, hup, hvp⟩
  have hnonempty : (G.deleteIncidenceSet p).edgeFinset.Nonempty := by
    refine ⟨s(u, v), ?_⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hdelete
  have hdeleted : 1 ≤ (G.deleteIncidenceSet p).edgeFinset.card :=
    Finset.one_le_card.mpr hnonempty
  have hdeg : k ≤ G.degree p := degree_poleVertex_ge hk
  have hdeg_edges : G.degree p ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset p
  have hcard_delete := G.card_edgeFinset_deleteIncidenceSet p
  change k + 1 ≤ G.edgeFinset.card
  omega

/-- For every `m ≥ 3`, the radius-`1 / sqrt 2` two-sphere carries a
diameter-one `m`-point set with at least `m` diameter pairs.  Together with
the spherical-thrackle upper bound this is the equality construction used by
the odd-dimensional Lenz optimization. -/
theorem exists_threshold_sphere_configuration (m : ℕ) (hm : 3 ≤ m) :
    ∃ A : Finset (Point 3), A.card = m ∧
      IsOnSphere A 0 (1 / Real.sqrt 2) ∧ IsDiameterOne A ∧
        m ≤ diameterPairCount A := by
  let k := m - 1
  have hk : 2 ≤ k := by omega
  refine ⟨points hk, ?_, points_on_sphere hk, points_isDiameterOne hk, ?_⟩
  · rw [card_points]
    omega
  · have := diameterPairCount_points_ge hk
    dsimp [k] at this
    omega

/-- Exact sharpness of the one-edge-per-point estimate at radius
`1 / sqrt 2`. -/
theorem exists_threshold_sphere_configuration_eq (m : ℕ) (hm : 3 ≤ m) :
    ∃ A : Finset (Point 3), A.card = m ∧
      IsOnSphere A 0 (1 / Real.sqrt 2) ∧ IsDiameterOne A ∧
        diameterPairCount A = m := by
  obtain ⟨A, hcard, hsphere, hA, hlo⟩ :=
    exists_threshold_sphere_configuration m hm
  have hhi : diameterPairCount A ≤ A.card :=
    diameterPairCount_le_card_of_onSphere_of_invSqrtTwo_le_radius
      hsphere le_rfl hA
  exact ⟨A, hcard, hsphere, hA, by omega⟩

end ThresholdConstruction

export ThresholdConstruction
  (exists_threshold_sphere_configuration exists_threshold_sphere_configuration_eq)

end

end LocalSphere
end Erdos223

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.Basic

/-!
# Erdős Problem 957: normalization by the minimum distance

This module contains the exact similarity-normalization layer used to reduce
the problem to point sets whose least determined distance is one.  Scaling by
`r⁻¹` is bundled as an equivalence when `r > 0`; consequently it preserves the
cardinality of the point set and gives an isomorphism of every distance graph.
-/

open Metric
open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos957

/-- The similarity `x ↦ r⁻¹ • x`, with inverse `x ↦ r • x`. -/
noncomputable def scalePointEquiv (r : ℝ) (hr : 0 < r) : Point ≃ Point where
  toFun x := r⁻¹ • x
  invFun x := r • x
  left_inv x := by
    change r • (r⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  right_inv x := by
    change r⁻¹ • (r • x) = x
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

@[simp]
theorem scalePointEquiv_apply (r : ℝ) (hr : 0 < r) (x : Point) :
    scalePointEquiv r hr x = r⁻¹ • x :=
  rfl

@[simp]
theorem scalePointEquiv_symm_apply (r : ℝ) (hr : 0 < r) (x : Point) :
    (scalePointEquiv r hr).symm x = r • x :=
  rfl

/-- The point set obtained by dividing all coordinates by the positive number
`r`.  `Finset.map` records injectivity at the definition site. -/
noncomputable def normalizedSet (A : Finset Point) (r : ℝ) (hr : 0 < r) :
    Finset Point :=
  A.map (scalePointEquiv r hr).toEmbedding

@[simp]
theorem mem_normalizedSet (A : Finset Point) (r : ℝ) (hr : 0 < r)
    (x : Point) :
    scalePointEquiv r hr x ∈ normalizedSet A r hr ↔ x ∈ A := by
  exact Finset.mem_map' (scalePointEquiv r hr).toEmbedding

@[simp]
theorem normalizedSet_card (A : Finset Point) (r : ℝ) (hr : 0 < r) :
    (normalizedSet A r hr).card = A.card := by
  simp [normalizedSet]

/-- Euclidean distance is divided by `r` under the normalization map. -/
theorem dist_scalePointEquiv (r : ℝ) (hr : 0 < r) (x y : Point) :
    dist (scalePointEquiv r hr x) (scalePointEquiv r hr y) = dist x y / r := by
  rw [scalePointEquiv_apply, scalePointEquiv_apply, dist_eq_norm, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← dist_eq_norm]
  simp [div_eq_mul_inv, mul_comm]

/-- Membership in the normalized distance set is transported exactly by
division by `r`. -/
theorem div_mem_distanceSet_normalizedSet_iff (A : Finset Point)
    (r : ℝ) (hr : 0 < r) (d : ℝ) :
    d / r ∈ distanceSet (normalizedSet A r hr) ↔ d ∈ distanceSet A := by
  constructor
  · intro hd
    obtain ⟨x, hx, y, hy, hxy, hdist⟩ := mem_distanceSet.mp hd
    let e := scalePointEquiv r hr
    have hxA : e.symm x ∈ A := by
      simpa [normalizedSet, e] using hx
    have hyA : e.symm y ∈ A := by
      simpa [normalizedSet, e] using hy
    have hne : e.symm x ≠ e.symm y := by
      exact e.symm.injective.ne hxy
    refine mem_distanceSet.mpr ⟨e.symm x, hxA, e.symm y, hyA, hne, ?_⟩
    have htransport := dist_scalePointEquiv r hr (e.symm x) (e.symm y)
    rw [e.apply_symm_apply, e.apply_symm_apply, hdist] at htransport
    exact (div_left_inj' hr.ne').mp htransport.symm
  · intro hd
    obtain ⟨x, hx, y, hy, hxy, hdist⟩ := mem_distanceSet.mp hd
    refine mem_distanceSet.mpr
      ⟨scalePointEquiv r hr x, mem_normalizedSet A r hr x |>.2 hx,
        scalePointEquiv r hr y, mem_normalizedSet A r hr y |>.2 hy,
        (scalePointEquiv r hr).injective.ne hxy, ?_⟩
    rw [dist_scalePointEquiv, hdist]

/-- The complete distance set of the normalized configuration is the image of
the original distance set under division by `r`. -/
theorem distanceSet_normalizedSet (A : Finset Point) (r : ℝ) (hr : 0 < r) :
    distanceSet (normalizedSet A r hr) =
      (distanceSet A).image (fun d ↦ d / r) := by
  ext t
  constructor
  · intro ht
    obtain ⟨x, hx, y, hy, hxy, hdist⟩ := mem_distanceSet.mp ht
    let e := scalePointEquiv r hr
    have hxA : e.symm x ∈ A := by
      simpa [normalizedSet, e] using hx
    have hyA : e.symm y ∈ A := by
      simpa [normalizedSet, e] using hy
    have hne : e.symm x ≠ e.symm y := e.symm.injective.ne hxy
    have hdmem : dist (e.symm x) (e.symm y) ∈ distanceSet A :=
      dist_mem_distanceSet hxA hyA hne
    apply Finset.mem_image.mpr
    refine ⟨dist (e.symm x) (e.symm y), hdmem, ?_⟩
    have htransport := dist_scalePointEquiv r hr (e.symm x) (e.symm y)
    rw [e.apply_symm_apply, e.apply_symm_apply, hdist] at htransport
    exact htransport.symm
  · intro ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
    exact (div_mem_distanceSet_normalizedSet_iff A r hr d).2 hd

/-- The subtype of vertices of `A` is canonically equivalent to the subtype
of vertices of its normalized image. -/
noncomputable def normalizedVertexEquiv (A : Finset Point)
    (r : ℝ) (hr : 0 < r) :
    {x // x ∈ A} ≃ {x // x ∈ normalizedSet A r hr} :=
  (scalePointEquiv r hr).subtypeEquiv fun x ↦
    (mem_normalizedSet A r hr x).symm

@[simp]
theorem normalizedVertexEquiv_apply_val (A : Finset Point)
    (r : ℝ) (hr : 0 < r) (x : {x // x ∈ A}) :
    ((normalizedVertexEquiv A r hr x :
      {x // x ∈ normalizedSet A r hr}) : Point) = r⁻¹ • (x : Point) :=
  rfl

/-- Scaling gives an isomorphism from the distance-`d` graph of `A` to the
distance-`d/r` graph of the normalized configuration. -/
noncomputable def distanceGraphNormalizedIso (A : Finset Point)
    (r : ℝ) (hr : 0 < r) (d : ℝ) :
    distanceGraph A d ≃g distanceGraph (normalizedSet A r hr) (d / r) where
  toEquiv := normalizedVertexEquiv A r hr
  map_rel_iff' := by
    intro x y
    rw [distanceGraph_adj, distanceGraph_adj]
    constructor
    · rintro ⟨hxy, hdist⟩
      refine ⟨fun h ↦ hxy (congrArg (normalizedVertexEquiv A r hr) h), ?_⟩
      change dist (scalePointEquiv r hr (x : Point))
        (scalePointEquiv r hr (y : Point)) = d / r at hdist
      have hscale := dist_scalePointEquiv r hr (x : Point) (y : Point)
      rw [hdist] at hscale
      exact (div_left_inj' hr.ne').mp hscale.symm
    · rintro ⟨hxy, hdist⟩
      refine ⟨(normalizedVertexEquiv A r hr).injective.ne hxy, ?_⟩
      change dist (scalePointEquiv r hr (x : Point))
        (scalePointEquiv r hr (y : Point)) = d / r
      exact (dist_scalePointEquiv r hr (x : Point) (y : Point)).trans
        (congrArg (fun t : ℝ ↦ t / r) hdist)

/-- Every numerical distance multiplicity is preserved exactly by scaling. -/
theorem multiplicity_normalizedSet (A : Finset Point)
    (r : ℝ) (hr : 0 < r) (d : ℝ) :
    multiplicity (normalizedSet A r hr) (d / r) = multiplicity A d := by
  classical
  exact (distanceGraphNormalizedIso A r hr d).card_edgeFinset_eq.symm

/-- Minimum-distance status is invariant under positive scaling. -/
theorem isMinimumDistance_normalizedSet_iff (A : Finset Point)
    (r : ℝ) (hr : 0 < r) (d : ℝ) :
    IsMinimumDistance (normalizedSet A r hr) (d / r) ↔
      IsMinimumDistance A d := by
  constructor
  · rintro ⟨hd, hleast⟩
    refine ⟨(div_mem_distanceSet_normalizedSet_iff A r hr d).1 hd, ?_⟩
    intro s hs
    have hsdiv : s / r ∈ distanceSet (normalizedSet A r hr) :=
      (div_mem_distanceSet_normalizedSet_iff A r hr s).2 hs
    exact (div_le_div_iff_of_pos_right hr).mp (hleast (s / r) hsdiv)
  · rintro ⟨hd, hleast⟩
    refine ⟨(div_mem_distanceSet_normalizedSet_iff A r hr d).2 hd, ?_⟩
    intro t ht
    obtain ⟨s, hs, rfl⟩ := by
      rw [distanceSet_normalizedSet] at ht
      exact Finset.mem_image.mp ht
    exact (div_le_div_iff_of_pos_right hr).2 (hleast s hs)

/-- Maximum-distance status is invariant under positive scaling. -/
theorem isMaximumDistance_normalizedSet_iff (A : Finset Point)
    (r : ℝ) (hr : 0 < r) (d : ℝ) :
    IsMaximumDistance (normalizedSet A r hr) (d / r) ↔
      IsMaximumDistance A d := by
  constructor
  · rintro ⟨hd, hgreatest⟩
    refine ⟨(div_mem_distanceSet_normalizedSet_iff A r hr d).1 hd, ?_⟩
    intro s hs
    have hsdiv : s / r ∈ distanceSet (normalizedSet A r hr) :=
      (div_mem_distanceSet_normalizedSet_iff A r hr s).2 hs
    exact (div_le_div_iff_of_pos_right hr).mp (hgreatest (s / r) hsdiv)
  · rintro ⟨hd, hgreatest⟩
    refine ⟨(div_mem_distanceSet_normalizedSet_iff A r hr d).2 hd, ?_⟩
    intro t ht
    obtain ⟨s, hs, rfl⟩ := by
      rw [distanceSet_normalizedSet] at ht
      exact Finset.mem_image.mp ht
    exact (div_le_div_iff_of_pos_right hr).2 (hgreatest s hs)

/-- The minimum determined distance is divided by the scaling denominator. -/
theorem minDist_normalizedSet (A : Finset Point) (hA : 2 ≤ A.card)
    (r : ℝ) (hr : 0 < r) :
    minDist (normalizedSet A r hr) (by simpa using hA) = minDist A hA / r := by
  symm
  apply IsMinimumDistance.eq_minDist
  · exact (isMinimumDistance_normalizedSet_iff A r hr (minDist A hA)).2
      (isMinimumDistance_minDist A hA)

/-- The maximum determined distance is divided by the scaling denominator. -/
theorem maxDist_normalizedSet (A : Finset Point) (hA : 2 ≤ A.card)
    (r : ℝ) (hr : 0 < r) :
    maxDist (normalizedSet A r hr) (by simpa using hA) = maxDist A hA / r := by
  symm
  apply IsMaximumDistance.eq_maxDist
  · exact (isMaximumDistance_normalizedSet_iff A r hr (maxDist A hA)).2
      (isMaximumDistance_maxDist A hA)

/-- Normalizing by the genuine least distance makes the least distance one. -/
theorem minimumDistance_normalized_eq_one {A : Finset Point} {r : ℝ}
    (hr : IsMinimumDistance A r) :
    IsMinimumDistance (normalizedSet A r hr.pos) 1 := by
  have h := (isMinimumDistance_normalizedSet_iff A r hr.pos r).2 hr
  simpa [hr.pos.ne'] using h

/-- Distinct original points become one-separated after normalizing by the
genuine least distance. -/
theorem one_le_dist_normalized_of_isMinimum {A : Finset Point} {r : ℝ}
    (hr : IsMinimumDistance A r) {x y : Point}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    1 ≤ dist (scalePointEquiv r hr.pos x) (scalePointEquiv r hr.pos y) := by
  rw [dist_scalePointEquiv]
  have hmin : r ≤ dist x y := hr.2 _ (dist_mem_distanceSet hx hy hxy)
  exact (le_div_iff₀ hr.pos).2 (by simpa using hmin)

/-- Intrinsic form of one-separation for arbitrary vertices of the normalized
point set. -/
theorem normalizedSet_one_separated {A : Finset Point} {r : ℝ}
    (hr : IsMinimumDistance A r) {x y : Point}
    (hx : x ∈ normalizedSet A r hr.pos)
    (hy : y ∈ normalizedSet A r hr.pos) (hxy : x ≠ y) :
    1 ≤ dist x y := by
  have hminimum := minimumDistance_normalized_eq_one hr
  exact hminimum.2 _ (dist_mem_distanceSet hx hy hxy)

/-- If `R` is the greatest original distance, every pair of normalized points
has distance at most the exact ratio `R / r`. -/
theorem dist_normalized_le_ratio_of_isMaximum {A : Finset Point} {r R : ℝ}
    (hr : 0 < r) (hR : IsMaximumDistance A R) {x y : Point}
    (hx : x ∈ normalizedSet A r hr) (hy : y ∈ normalizedSet A r hr) :
    dist x y ≤ R / r := by
  by_cases hxy : x = y
  · subst y
    simpa using (div_nonneg (le_of_lt hR.pos) (le_of_lt hr))
  · have hmax : IsMaximumDistance (normalizedSet A r hr) (R / r) :=
      (isMaximumDistance_normalizedSet_iff A r hr R).2 hR
    exact hmax.2 _ (dist_mem_distanceSet hx hy hxy)

/-- The two simultaneous metric consequences of normalizing a configuration
by its genuine minimum distance. -/
theorem normalized_metric_bounds {A : Finset Point} {r R : ℝ}
    (hr : IsMinimumDistance A r) (hR : IsMaximumDistance A R) :
    (∀ x ∈ normalizedSet A r hr.pos, ∀ y ∈ normalizedSet A r hr.pos,
        x ≠ y → 1 ≤ dist x y) ∧
      (∀ x ∈ normalizedSet A r hr.pos, ∀ y ∈ normalizedSet A r hr.pos,
        dist x y ≤ R / r) := by
  refine ⟨?_, ?_⟩
  · exact fun x hx y hy hxy ↦ normalizedSet_one_separated hr hx hy hxy
  · exact fun x hx y hy ↦ dist_normalized_le_ratio_of_isMaximum hr.pos hR hx hy

end Erdos957


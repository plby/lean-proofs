/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# The short positive path: selection and polygonal bookkeeping

This file isolates the formal, non-potential-theoretic part of the Lewis--Rossi--Weitsman
short-path lemma.  Its analytic inputs are ordinary theorem parameters: a Hall set of good
directions, the two exceptional sets furnished by the Prawitz radial-maximal and logarithmic
derivative estimates, a normalized Riemann map with its boundary-limit property, and the Koebe
quarter bound.

There is a minor point which matters in a formal statement.  A boundary endpoint of an open
domain cannot be the last vertex of a *finite* polygonal arc all of whose closed segments lie in
the domain.  We record a countable boundary-approaching model, but the production theorem uses a
finite truncation: convergence of the endpoint-growth quantity lets us stop inside the domain at
any strictly smaller target.  The compact radial piece is then polygonalized without increasing
its variation.  This finite form is the one that concatenates directly in the nested-domain
construction.
-/

open Filter MeasureTheory Set

open scoped ENNReal NNReal Topology

namespace Erdos515

/-- The radial point `r exp(i theta)` in the unit disk. -/
noncomputable def shortPathRadialPoint (r theta : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (Complex.I * theta)

@[simp] lemma shortPathRadialPoint_zero (theta : ℝ) :
    shortPathRadialPoint 0 theta = 0 := by
  simp [shortPathRadialPoint]

/-- The image of a radius under a candidate normalized Riemann map. -/
noncomputable def shortPathRadialCurve (F : ℂ → ℂ) (theta : ℝ) (r : ℝ) : ℂ :=
  F (shortPathRadialPoint r theta)

/-- The exceptional directions for a radial-maximal estimate. -/
def radialMaxBadDirections (radialMax : ℝ → ℝ) (bound : ℝ) : Set ℝ :=
  {theta | bound < radialMax theta}

/-- The exceptional directions for a logarithmic-derivative area estimate. -/
def logDerivativeBadDirections (logDerivativeIntegral : ℝ → ℝ) (bound : ℝ) : Set ℝ :=
  {theta | bound < logDerivativeIntegral theta}

/-- If two exceptional sets together have less measure than the good set, some good direction
avoids both of them.  No measurability hypothesis is needed for this elementary use of outer
measure. -/
theorem exists_good_direction_avoiding_two
    {G B₁ B₂ : Set ℝ} {mu : Measure ℝ}
    (hmeasure : mu B₁ + mu B₂ < mu G) :
    ∃ theta, theta ∈ G ∧ theta ∉ B₁ ∧ theta ∉ B₂ := by
  by_contra h
  have h' : ∀ theta, theta ∈ G → theta ∉ B₁ → theta ∈ B₂ := by
    intro theta htheta htheta₁
    by_contra htheta₂
    exact h ⟨theta, htheta, htheta₁, htheta₂⟩
  have hsub : G ⊆ B₁ ∪ B₂ := by
    intro theta htheta
    by_cases h₁ : theta ∈ B₁
    · exact Or.inl h₁
    · exact Or.inr (h' theta htheta h₁)
  have hle : mu G ≤ mu B₁ + mu B₂ :=
    (measure_mono hsub).trans (measure_union_le B₁ B₂)
  exact (not_le_of_gt hmeasure) hle

/-- The customary Hall--Prawitz numerical estimates imply the strict selection budget. -/
theorem hall_prawitz_selection_budget
    {G B₁ B₂ : Set ℝ} {mu : Measure ℝ}
    (hHall : ENNReal.ofReal Real.pi ≤ mu G)
    (hPrawitz : mu B₁ < ENNReal.ofReal (Real.pi / 4))
    (hLogArea : mu B₂ < ENNReal.ofReal (Real.pi / 4)) :
    mu B₁ + mu B₂ < mu G := by
  have hquarter : 0 ≤ Real.pi / 4 := by positivity
  have hhalf : Real.pi / 4 + Real.pi / 4 < Real.pi := by
    nlinarith [Real.pi_pos]
  have hofReal : ENNReal.ofReal (Real.pi / 4) + ENNReal.ofReal (Real.pi / 4) <
      ENNReal.ofReal Real.pi := by
    rw [← ENNReal.ofReal_add hquarter hquarter,
      ENNReal.ofReal_lt_ofReal_iff Real.pi_pos]
    exact hhalf
  exact (ENNReal.add_lt_add hPrawitz hLogArea).trans (hofReal.trans_le hHall)

/-- A Hall set of angular measure at least `pi` cannot be covered by two exceptional sets of
measure less than `pi / 4`. -/
theorem exists_good_direction_of_hall_prawitz
    {G B₁ B₂ : Set ℝ} {mu : Measure ℝ}
    (hHall : ENNReal.ofReal Real.pi ≤ mu G)
    (hPrawitz : mu B₁ < ENNReal.ofReal (Real.pi / 4))
    (hLogArea : mu B₂ < ENNReal.ofReal (Real.pi / 4)) :
    ∃ theta, theta ∈ G ∧ theta ∉ B₁ ∧ theta ∉ B₂ :=
  exists_good_direction_avoiding_two
    (hall_prawitz_selection_budget hHall hPrawitz hLogArea)

/-- A countable polygonal arc which approaches a boundary point.

The endpoint is not itself a vertex.  This is necessary for an open domain: every closed segment
belongs to `D`, whereas the limiting endpoint belongs to `frontier D`.
-/
structure PolygonalArcToBoundary (D : Set ℂ) (v : ℂ → ℝ) (a b : ℂ) where
  vertex : ℕ → ℂ
  start : vertex 0 = a
  segment_mem : ∀ n t, t ∈ Icc (0 : ℝ) 1 →
    AffineMap.lineMap (vertex n) (vertex (n + 1)) t ∈ D
  segment_positive : ∀ n t, t ∈ Icc (0 : ℝ) 1 →
    0 < v (AffineMap.lineMap (vertex n) (vertex (n + 1)) t)
  tendsto_endpoint : Tendsto vertex atTop (nhds b)
  endpoint_mem_frontier : b ∈ frontier D

namespace PolygonalArcToBoundary

/-- The total polygonal length, with no possibility of cancellation. -/
noncomputable def length {D : Set ℂ} {v : ℂ → ℝ} {a b : ℂ}
    (P : PolygonalArcToBoundary D v a b) : ℝ≥0∞ :=
  ∑' n : ℕ, edist (P.vertex n) (P.vertex (n + 1))

lemma vertex_mem {D : Set ℂ} {v : ℂ → ℝ} {a b : ℂ}
    (P : PolygonalArcToBoundary D v a b) (n : ℕ) : P.vertex n ∈ D := by
  simpa using P.segment_mem n 0 (by simp)

lemma vertex_positive {D : Set ℂ} {v : ℂ → ℝ} {a b : ℂ}
    (P : PolygonalArcToBoundary D v a b) (n : ℕ) : 0 < v (P.vertex n) := by
  simpa using P.segment_positive n 0 (by simp)

end PolygonalArcToBoundary

/-- A finite polygonal arc.  The index `i < steps` denotes the segment joining vertices `i` and
`i + 1`. -/
structure FinitePositivePolygonalArc (D : Set ℂ) (v : ℂ → ℝ) (a c : ℂ) where
  steps : ℕ
  steps_pos : 0 < steps
  vertex : Fin (steps + 1) → ℂ
  start : vertex ⟨0, Nat.zero_lt_succ steps⟩ = a
  finish : vertex ⟨steps, Nat.lt_succ_self steps⟩ = c
  segment_mem : ∀ i (hi : i < steps) t, t ∈ Icc (0 : ℝ) 1 →
    AffineMap.lineMap (vertex ⟨i, Nat.lt_succ_of_lt hi⟩)
      (vertex ⟨i + 1, Nat.succ_lt_succ hi⟩) t ∈ D
  segment_positive : ∀ i (hi : i < steps) t, t ∈ Icc (0 : ℝ) 1 →
    0 < v (AffineMap.lineMap (vertex ⟨i, Nat.lt_succ_of_lt hi⟩)
      (vertex ⟨i + 1, Nat.succ_lt_succ hi⟩) t)

namespace FinitePositivePolygonalArc

/-- The exact sum of the finitely many chord lengths. -/
noncomputable def length {D : Set ℂ} {v : ℂ → ℝ} {a c : ℂ}
    (P : FinitePositivePolygonalArc D v a c) : ℝ≥0∞ :=
  ∑ i : Fin P.steps, edist (P.vertex i.castSucc) (P.vertex i.succ)

end FinitePositivePolygonalArc

/-- Uniform parameter mesh on `[0,r]`. -/
private noncomputable def uniformMesh (r : ℝ) (N i : ℕ) : ℝ :=
  r * (i : ℝ) / (N : ℝ)

private lemma uniformMesh_zero (r : ℝ) {N : ℕ} : uniformMesh r N 0 = 0 := by
  simp [uniformMesh]

private lemma uniformMesh_last (r : ℝ) {N : ℕ} (hN : 0 < N) :
    uniformMesh r N N = r := by
  simp [uniformMesh, Nat.ne_of_gt hN]

private lemma uniformMesh_mem_Icc {r : ℝ} {N i : ℕ} (hr : 0 ≤ r) (hN : 0 < N)
    (hi : i ≤ N) : uniformMesh r N i ∈ Icc (0 : ℝ) r := by
  have hNc : 0 < (N : ℝ) := by exact_mod_cast hN
  constructor
  · exact div_nonneg (mul_nonneg hr (Nat.cast_nonneg i)) hNc.le
  · unfold uniformMesh
    rw [div_le_iff₀ hNc]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hi) hr

private lemma monotone_uniformMesh (r : ℝ) {N : ℕ} (hr : 0 ≤ r) :
    Monotone (uniformMesh r N) := by
  intro i j hij
  unfold uniformMesh
  gcongr

private lemma dist_uniformMesh_succ {r : ℝ} {N i : ℕ} (hr : 0 ≤ r) (hN : 0 < N) :
    dist (uniformMesh r N i) (uniformMesh r N (i + 1)) = r / N := by
  have hNc : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [Real.dist_eq]
  have heq : uniformMesh r N i - uniformMesh r N (i + 1) = -(r / N) := by
    unfold uniformMesh
    push_cast
    field_simp
    ring
  rw [heq, abs_neg, abs_of_nonneg]
  positivity

/-- A compact piece of a continuous curve in an open positive region admits a finite polygonal
approximation sampled in parameter order.  Its chord sum is bounded by the variation of the
original curve, because variation is the supremum over all monotone finite samples. -/
theorem exists_finite_positive_polygonal_approximation
    {D : Set ℂ} {v : ℂ → ℝ} {a : ℂ} {gamma : ℝ → ℂ} {r : ℝ}
    (hD : IsOpen D) (hv : Continuous v)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hgamma : ContinuousOn gamma (Icc (0 : ℝ) r))
    (hgamma_zero : gamma 0 = a)
    (hpositive : ∀ s ∈ Icc (0 : ℝ) r, gamma s ∈ D ∧ 0 < v (gamma s)) :
    ∃ P : FinitePositivePolygonalArc D v a (gamma r),
      P.length ≤ eVariationOn gamma (Ico (0 : ℝ) 1) := by
  let U : Set ℂ := D ∩ v ⁻¹' Ioi 0
  have hU : IsOpen U := hD.inter (isOpen_Ioi.preimage hv)
  have hcompact : IsCompact (gamma '' Icc (0 : ℝ) r) :=
    isCompact_Icc.image_of_continuousOn hgamma
  have hsubset : gamma '' Icc (0 : ℝ) r ⊆ U := by
    rintro z ⟨s, hs, rfl⟩
    exact hpositive s hs
  obtain ⟨eps, heps, hepsU⟩ := hcompact.exists_thickening_subset_open hU hsubset
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hgamma
  obtain ⟨delta, hdelta, hdeltaMap⟩ :=
    (Metric.uniformContinuousOn_iff.1 huc) eps heps
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (r / delta)
  have hN : 0 < N := by
    have : 0 ≤ r / delta := div_nonneg hr0.le hdelta.le
    exact_mod_cast (this.trans_lt hNlarge)
  have hNc : 0 < (N : ℝ) := by exact_mod_cast hN
  have hstep : r / N < delta := by
    rw [div_lt_iff₀ hNc]
    have := (div_lt_iff₀ hdelta).1 hNlarge
    nlinarith
  let vert : Fin (N + 1) → ℂ := fun i ↦ gamma (uniformMesh r N i)
  have hsafe : ∀ i (hi : i < N) t, t ∈ Icc (0 : ℝ) 1 →
      AffineMap.lineMap (vert ⟨i, Nat.lt_succ_of_lt hi⟩)
        (vert ⟨i + 1, Nat.succ_lt_succ hi⟩) t ∈ U := by
    intro i hi t ht
    have hiN : i ≤ N := hi.le
    have hisN : i + 1 ≤ N := hi
    have hmi := uniformMesh_mem_Icc hr0.le hN hiN
    have hmis := uniformMesh_mem_Icc hr0.le hN hisN
    have hdistParam : dist (uniformMesh r N i) (uniformMesh r N (i + 1)) < delta := by
      rw [dist_uniformMesh_succ hr0.le hN]
      exact hstep
    have hdistImage : dist (gamma (uniformMesh r N i))
        (gamma (uniformMesh r N (i + 1))) < eps :=
      hdeltaMap _ hmi _ hmis hdistParam
    apply hepsU
    rw [Metric.mem_thickening_iff]
    refine ⟨gamma (uniformMesh r N i), ⟨uniformMesh r N i, hmi, rfl⟩, ?_⟩
    rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (dist_nonneg) ht.2).trans_lt hdistImage
  let P : FinitePositivePolygonalArc D v a (gamma r) :=
    { steps := N
      steps_pos := hN
      vertex := vert
      start := by simp [vert, uniformMesh_zero, hgamma_zero]
      finish := by simp [vert, uniformMesh_last r hN]
      segment_mem := fun i hi t ht ↦ (hsafe i hi t ht).1
      segment_positive := fun i hi t ht ↦ (hsafe i hi t ht).2 }
  refine ⟨P, ?_⟩
  have hsum := eVariationOn.sum_le_of_monotoneOn_Iic
    (f := gamma) (s := Ico (0 : ℝ) 1) (n := N) (u := uniformMesh r N)
    ((monotone_uniformMesh (N := N) r hr0.le).monotoneOn (Iic N))
    (fun i hi ↦ ⟨(uniformMesh_mem_Icc hr0.le hN hi).1,
      (uniformMesh_mem_Icc hr0.le hN hi).2.trans_lt hr1⟩)
  rw [FinitePositivePolygonalArc.length]
  change (∑ i : Fin N, edist (gamma (uniformMesh r N i))
    (gamma (uniformMesh r N (i + 1)))) ≤ _
  rw [Fin.sum_univ_eq_sum_range (fun i ↦
    edist (gamma (uniformMesh r N i)) (gamma (uniformMesh r N (i + 1)))) N]
  simpa only [edist_comm] using hsum

/-- Data certifying that a radius has been polygonalized inside the positive region.

The radii need only be monotone (repeated vertices are harmless).  The variation bound below
shows that the sum of all chord lengths is no larger than the variation of the original radial
curve.
-/
structure RadialPolygonalApproximation
    (F : ℂ → ℂ) (theta : ℝ) (D : Set ℂ) (v : ℂ → ℝ) where
  radius : ℕ → ℝ
  radius_zero : radius 0 = 0
  radius_mono : Monotone radius
  radius_mem : ∀ n, radius n ∈ Ico (0 : ℝ) 1
  radius_tendsto_one : Tendsto radius atTop (nhds (1 : ℝ))
  segment_mem : ∀ n t, t ∈ Icc (0 : ℝ) 1 →
    AffineMap.lineMap (shortPathRadialCurve F theta (radius n))
      (shortPathRadialCurve F theta (radius (n + 1))) t ∈ D
  segment_positive : ∀ n t, t ∈ Icc (0 : ℝ) 1 →
    0 < v (AffineMap.lineMap (shortPathRadialCurve F theta (radius n))
      (shortPathRadialCurve F theta (radius (n + 1))) t)

/-- Chords sampled at monotone radial parameters have total length at most the variation of the
radial curve. -/
theorem radialPolygonal_length_le_variation
    {F : ℂ → ℂ} {theta : ℝ} {D : Set ℂ} {v : ℂ → ℝ}
    (P : RadialPolygonalApproximation F theta D v) :
    (∑' n : ℕ, edist (shortPathRadialCurve F theta (P.radius n))
      (shortPathRadialCurve F theta (P.radius (n + 1)))) ≤
      eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n ↦ ?_
  simpa only [edist_comm] using
    (eVariationOn.sum_le
      (f := shortPathRadialCurve F theta) (s := Ico (0 : ℝ) 1)
      (n := n) (u := P.radius) P.radius_mono P.radius_mem)

/-- The formal endpoint-and-polygonal bookkeeping lemma.

The existence of the radial limit follows from bounded variation and completeness of `ℂ`.
The `noInteriorLimit` hypothesis is the standard elementary boundary consequence of a normalized
Riemann map (apply the continuous inverse and compare with `r exp(i theta) → exp(i theta)`).
-/
theorem polygonalArcToBoundary_of_radial_data
    {D : Set ℂ} {v : ℂ → ℝ} {a : ℂ} {F : ℂ → ℂ} {theta : ℝ} {L : ℝ}
    (hD : IsOpen D)
    (hFzero : F 0 = a)
    (hradial_mem : ∀ r ∈ Ico (0 : ℝ) 1, shortPathRadialCurve F theta r ∈ D)
    (hvariation : eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1)
      ≤ ENNReal.ofReal L)
    (hnoInteriorLimit : ∀ b : ℂ,
      Tendsto (shortPathRadialCurve F theta)
        (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1 ∩ Iio 1)) (nhds b) → b ∉ D)
    (P : RadialPolygonalApproximation F theta D v) :
    ∃ b, ∃ Q : PolygonalArcToBoundary D v a b,
      Q.length ≤ ENNReal.ofReal L := by
  have hbounded : BoundedVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvariation
  obtain ⟨b, hb⟩ := hbounded.exists_tendsto_left (1 : ℝ)
  have hradius_within : Tendsto P.radius atTop
      (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1 ∩ Iio 1)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨P.radius_tendsto_one, ?_⟩
    exact Filter.Eventually.of_forall fun n ↦ ⟨P.radius_mem n, (P.radius_mem n).2⟩
  have hvertex : Tendsto
      (fun n ↦ shortPathRadialCurve F theta (P.radius n)) atTop (nhds b) :=
    hb.comp hradius_within
  have hbclosure : b ∈ closure D := by
    apply isClosed_closure.mem_of_tendsto hvertex
    exact Filter.Eventually.of_forall fun n ↦ subset_closure (hradial_mem _ (P.radius_mem n))
  have hbnot : b ∉ D := hnoInteriorLimit b hb
  have hbfrontier : b ∈ frontier D := by
    change b ∈ closure D \ interior D
    exact ⟨hbclosure, by simpa [hD.interior_eq] using hbnot⟩
  let Q : PolygonalArcToBoundary D v a b :=
    { vertex := fun n ↦ shortPathRadialCurve F theta (P.radius n)
      start := by simp [shortPathRadialCurve, P.radius_zero, hFzero]
      segment_mem := P.segment_mem
      segment_positive := P.segment_positive
      tendsto_endpoint := hvertex
      endpoint_mem_frontier := hbfrontier }
  refine ⟨b, Q, ?_⟩
  exact (radialPolygonal_length_le_variation P).trans hvariation

/-- The Hall--Prawitz--Koebe short-path implication with all hard analytic statements exposed as
ordinary parameters.

`good` is the Hall-good set and `radialBad`, `logBad` are the two exceptional sets.  Away from
both exceptional sets the Prawitz calculation gives the numerical variation bound directly;
Koebe then converts the conformal radius `scale` to boundary distance.
-/
theorem short_positive_countable_polygonal_path
    {D : Set ℂ} {v : ℂ → ℝ} {a : ℂ} {F : ℂ → ℂ}
    (good radialBad logBad : Set ℝ)
    (K J scale : ℝ)
    (hD : IsOpen D)
    (hFzero : F 0 = a)
    (hK : 0 ≤ K) (hJ : 0 ≤ J) (hscale : 0 ≤ scale)
    (hselection : volume radialBad + volume logBad < volume good)
    (hgood : ∀ theta ∈ good, ∀ r ∈ Ico (0 : ℝ) 1,
      shortPathRadialCurve F theta r ∈ D ∧ 0 < v (shortPathRadialCurve F theta r))
    (hvariation : ∀ theta ∈ good,
      theta ∉ radialBad → theta ∉ logBad →
      eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) ≤
        ENNReal.ofReal (K * scale * J))
    (hkoebe : scale ≤ 4 * Metric.infDist a (frontier D))
    (hnoInteriorLimit : ∀ theta ∈ good, ∀ b : ℂ,
      Tendsto (shortPathRadialCurve F theta)
        (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1 ∩ Iio 1)) (nhds b) → b ∉ D)
    (hpolygonal : ∀ theta ∈ good,
      theta ∉ radialBad → theta ∉ logBad →
      RadialPolygonalApproximation F theta D v) :
    ∃ b, ∃ Q : PolygonalArcToBoundary D v a b,
      Q.length ≤ ENNReal.ofReal ((4 * K * J) * Metric.infDist a (frontier D)) := by
  obtain ⟨theta, htheta, hthetaMax, hthetaLog⟩ :=
    exists_good_direction_avoiding_two hselection
  have hkoebeProduct : K * scale * J ≤
      (4 * K * J) * Metric.infDist a (frontier D) := by
    calc
      K * scale * J ≤ K * (4 * Metric.infDist a (frontier D)) * J := by
        gcongr
      _ = (4 * K * J) * Metric.infDist a (frontier D) := by ring
  have hvar : eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) ≤
      ENNReal.ofReal ((4 * K * J) * Metric.infDist a (frontier D)) := by
    refine (hvariation theta htheta hthetaMax hthetaLog).trans ?_
    exact ENNReal.ofReal_le_ofReal hkoebeProduct
  exact polygonalArcToBoundary_of_radial_data hD hFzero
    (fun r hr ↦ (hgood theta htheta r hr).1) hvar
    (hnoInteriorLimit theta htheta) (hpolygonal theta htheta hthetaMax hthetaLog)

/-- Finite form of the short-path lemma used by the nested-domain construction.

The radial curve has a boundary value for the continuous quantity `q`.  Given any strictly
smaller target `T`, convergence selects a truncation radius `r < 1` with `T < q (F(r e^{iθ}))`.
The compact radial interval `[0,r]` is then polygonalized by
`exists_finite_positive_polygonal_approximation`.  In particular, the result has finitely many
segments and can be concatenated with the later stages of the LRW construction.
-/
theorem short_positive_polygonal_path
    {D : Set ℂ} {v q : ℂ → ℝ} {a : ℂ} {F : ℂ → ℂ}
    (good radialBad logBad : Set ℝ)
    (K J scale boundaryValue T : ℝ)
    (hD : IsOpen D) (hv : Continuous v)
    (hFzero : F 0 = a)
    (hK : 0 ≤ K) (hJ : 0 ≤ J) (hscale : 0 ≤ scale)
    (hHall : ENNReal.ofReal Real.pi ≤ volume good)
    (hPrawitz : volume radialBad < ENNReal.ofReal (Real.pi / 4))
    (hLogArea : volume logBad < ENNReal.ofReal (Real.pi / 4))
    (hcontinuous : ∀ theta ∈ good,
      ContinuousOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1))
    (hgood : ∀ theta ∈ good, ∀ r ∈ Ico (0 : ℝ) 1,
      shortPathRadialCurve F theta r ∈ D ∧ 0 < v (shortPathRadialCurve F theta r))
    (hvariation : ∀ theta ∈ good,
      theta ∉ radialBad → theta ∉ logBad →
      eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) ≤
        ENNReal.ofReal (K * scale * J))
    (hkoebe : scale ≤ 4 * Metric.infDist a (frontier D))
    (htargetLimit : ∀ theta ∈ good,
      theta ∉ radialBad → theta ∉ logBad →
      Tendsto (fun r ↦ q (shortPathRadialCurve F theta r))
        (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)) (nhds boundaryValue))
    (hT : T < boundaryValue) :
    ∃ c, c ∈ D ∧ T < q c ∧
      ∃ P : FinitePositivePolygonalArc D v a c,
        P.length ≤ ENNReal.ofReal ((4 * K * J) * Metric.infDist a (frontier D)) := by
  obtain ⟨theta, htheta, hthetaMax, hthetaLog⟩ :=
    exists_good_direction_of_hall_prawitz hHall hPrawitz hLogArea
  have hkoebeProduct : K * scale * J ≤
      (4 * K * J) * Metric.infDist a (frontier D) := by
    calc
      K * scale * J ≤ K * (4 * Metric.infDist a (frontier D)) * J := by
        gcongr
      _ = (4 * K * J) * Metric.infDist a (frontier D) := by ring
  have hvar : eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) ≤
      ENNReal.ofReal ((4 * K * J) * Metric.infDist a (frontier D)) := by
    refine (hvariation theta htheta hthetaMax hthetaLog).trans ?_
    exact ENNReal.ofReal_le_ofReal hkoebeProduct
  let l : Filter ℝ := nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)
  have hclosure : (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) := by simp
  let _ : l.NeBot := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hevTarget : ∀ᶠ r in l, T < q (shortPathRadialCurve F theta r) :=
    (tendsto_order.1 (htargetLimit theta htheta hthetaMax hthetaLog)).1 T hT
  have htoOne : Tendsto id l (nhds (1 : ℝ)) := tendsto_id.mono_left inf_le_left
  have hevPos : ∀ᶠ r in l, 0 < r := htoOne (Ioi_mem_nhds zero_lt_one)
  have hevMem : ∀ᶠ r in l, r ∈ Ico (0 : ℝ) 1 := self_mem_nhdsWithin
  obtain ⟨r, hqr, hrpos, hrmem⟩ := (hevTarget.and (hevPos.and hevMem)).exists
  have hcontR : ContinuousOn (shortPathRadialCurve F theta) (Icc (0 : ℝ) r) :=
    (hcontinuous theta htheta).mono fun s hs ↦ ⟨hs.1, hs.2.trans_lt hrmem.2⟩
  have hposR : ∀ s ∈ Icc (0 : ℝ) r,
      shortPathRadialCurve F theta s ∈ D ∧ 0 < v (shortPathRadialCurve F theta s) := by
    intro s hs
    exact hgood theta htheta s ⟨hs.1, hs.2.trans_lt hrmem.2⟩
  obtain ⟨P, hPlength⟩ := exists_finite_positive_polygonal_approximation
    (D := D) (v := v) (a := a) (gamma := shortPathRadialCurve F theta) (r := r)
    hD hv hrpos hrmem.2 hcontR
    (by simp [shortPathRadialCurve, hFzero]) hposR
  exact ⟨shortPathRadialCurve F theta r, (hgood theta htheta r hrmem).1, hqr,
    P, hPlength.trans hvar⟩

end Erdos515

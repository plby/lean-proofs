/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic

/-!
# Polygonal rays and their nonnegative arclength integrals

This file supplies the path model used in the formalization of Erdős Problem 515.
A path is represented by a sequence of vertices. Its escape field controls every point of every
sufficiently late affine segment, rather than merely the vertices. The integral is an `ENNReal`
sum of the exact constant-speed affine-segment arclength integrals, so it cannot hide cancellation.
-/

open Filter MeasureTheory Set

open scoped ENNReal NNReal Topology

namespace Erdos515

/-- The point with affine parameter `t` on the segment from `a` to `b`. -/
noncomputable def segmentPoint (a b : ℂ) (t : ℝ) : ℂ :=
  AffineMap.lineMap a b t

@[simp] lemma segmentPoint_zero (a b : ℂ) : segmentPoint a b 0 = a := by
  simp [segmentPoint]

@[simp] lemma segmentPoint_one (a b : ℂ) : segmentPoint a b 1 = b := by
  simp [segmentPoint]

lemma continuous_segmentPoint (a b : ℂ) : Continuous (segmentPoint a b) := by
  exact AffineMap.lineMap_continuous

lemma lipschitzWith_segmentPoint (a b : ℂ) :
    LipschitzWith (nndist a b) (segmentPoint a b) := by
  intro x y
  simp only [segmentPoint, edist_nndist, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  rw [nndist_lineMap_lineMap, mul_comm]

/-- Every affine piece has bounded variation on its closed parameter interval. -/
lemma boundedVariationOn_segmentPoint (a b : ℂ) :
    BoundedVariationOn (segmentPoint a b) (Icc (0 : ℝ) 1) := by
  simpa only [Function.comp_id] using
    (lipschitzWith_segmentPoint a b).comp_boundedVariationOn
      (BoundedVariationOn.id_Icc (0 : ℝ) 1)

/-- The variation of the affine parametrization is exactly the Euclidean segment length. -/
lemma eVariationOn_segmentPoint (a b : ℂ) :
    eVariationOn (segmentPoint a b) (Icc (0 : ℝ) 1) = ENNReal.ofReal ‖b - a‖ := by
  apply le_antisymm
  · calc
      eVariationOn (segmentPoint a b) (Icc (0 : ℝ) 1)
          ≤ (nndist a b : ℝ≥0∞) * eVariationOn id (Icc (0 : ℝ) 1) := by
            simpa only [Function.comp_id] using
              (lipschitzWith_segmentPoint a b).lipschitzOnWith.comp_eVariationOn_le
                (mapsTo_univ id (Icc (0 : ℝ) 1))
      _ = ENNReal.ofReal ‖b - a‖ := by
        simp [edist_dist, Complex.dist_eq, norm_sub_rev]
  · simpa [edist_dist, Complex.dist_eq, norm_sub_rev] using
      (eVariationOn.edist_le (segmentPoint a b)
        (show (0 : ℝ) ∈ Icc 0 1 by simp) (show (1 : ℝ) ∈ Icc 0 1 by simp))

/--
An exact polygonal model for a locally rectifiable ray tending to infinity.

The last field is deliberately uniform over each whole segment. Thus a sequence of far-away
vertices whose joining segments return to a bounded set does not satisfy this definition.
-/
structure LocallyRectifiablePath where
  vertex : ℕ → ℂ
  tendsToInfinity : ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
    R ≤ ‖segmentPoint (vertex n) (vertex (n + 1)) t‖

namespace LocallyRectifiablePath

/-- The `n`th closed affine segment of a polygonal ray. -/
def segment (C : LocallyRectifiablePath) (n : ℕ) : Set ℂ :=
  segmentPoint (C.vertex n) (C.vertex (n + 1)) '' Icc (0 : ℝ) 1

lemma vertex_mem_segment_left (C : LocallyRectifiablePath) (n : ℕ) :
    C.vertex n ∈ C.segment n := by
  exact ⟨0, by simp, by simp⟩

lemma vertex_mem_segment_right (C : LocallyRectifiablePath) (n : ℕ) :
    C.vertex (n + 1) ∈ C.segment n := by
  exact ⟨1, by simp, by simp⟩

lemma isCompact_segment (C : LocallyRectifiablePath) (n : ℕ) : IsCompact (C.segment n) := by
  exact isCompact_Icc.image (continuous_segmentPoint _ _)

/-- The escape field rewritten without the affine parameter. -/
lemma eventually_segment_norm_ge (C : LocallyRectifiablePath) (R : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ C.segment n, R ≤ ‖z‖ := by
  obtain ⟨N, hN⟩ := C.tendsToInfinity R
  refine ⟨N, fun n hn z hz ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ := hz
  exact hN n hn t ht

/-- In particular, the vertices themselves tend to infinity in norm. -/
lemma tendsto_vertex_norm_atTop (C : LocallyRectifiablePath) :
    Tendsto (fun n ↦ ‖C.vertex n‖) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro R
  obtain ⟨N, hN⟩ := C.tendsToInfinity R
  exact ⟨N, fun n hn ↦ by simpa using hN n hn 0 (by simp)⟩

/-- Consecutive affine pieces agree at their common endpoint. -/
lemma segmentPoint_right_eq_next_left (C : LocallyRectifiablePath) (n : ℕ) :
    segmentPoint (C.vertex n) (C.vertex (n + 1)) 1 =
      segmentPoint (C.vertex (n + 1)) (C.vertex (n + 2)) 0 := by
  simp

/-- Each piece in the ray is a continuous rectifiable path with the advertised length. -/
lemma continuous_boundedVariation_segment (C : LocallyRectifiablePath) (n : ℕ) :
    Continuous (segmentPoint (C.vertex n) (C.vertex (n + 1))) ∧
      BoundedVariationOn (segmentPoint (C.vertex n) (C.vertex (n + 1))) (Icc (0 : ℝ) 1) ∧
      eVariationOn (segmentPoint (C.vertex n) (C.vertex (n + 1))) (Icc (0 : ℝ) 1) =
        ENNReal.ofReal ‖C.vertex (n + 1) - C.vertex n‖ :=
  ⟨continuous_segmentPoint _ _, boundedVariationOn_segmentPoint _ _, eVariationOn_segmentPoint _ _⟩

/-- Remove finitely many initial segments of a ray. -/
def drop (C : LocallyRectifiablePath) (k : ℕ) : LocallyRectifiablePath where
  vertex n := C.vertex (k + n)
  tendsToInfinity R := by
    obtain ⟨N, hN⟩ := C.tendsToInfinity R
    refine ⟨N, fun n hn t ht ↦ ?_⟩
    simpa [Nat.add_assoc] using hN (k + n) (hn.trans (Nat.le_add_left n k)) t ht

@[simp] lemma drop_vertex (C : LocallyRectifiablePath) (k n : ℕ) :
    (C.drop k).vertex n = C.vertex (k + n) :=
  rfl

/-- The usual unit-speed-in-parameter realization of a polygonal ray on the real half-line.
It is extended constantly to negative parameters, which makes continuity most convenient to
state. -/
noncomputable def trace (C : LocallyRectifiablePath) (x : ℝ) : ℂ :=
  if _hx : 0 ≤ x then
    let n := ⌊x⌋₊
    segmentPoint (C.vertex n) (C.vertex (n + 1)) (x - n)
  else
    C.vertex 0

@[simp] lemma trace_of_nonpos (C : LocallyRectifiablePath) {x : ℝ} (hx : x ≤ 0) :
    C.trace x = C.vertex 0 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [trace]
  · rw [trace, dif_neg (not_le_of_gt hx)]

/-- On the `n`th unit interval, `trace` is exactly the `n`th affine segment, including both
endpoints. -/
lemma trace_eq_segmentPoint_of_mem_Icc (C : LocallyRectifiablePath) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (n : ℝ) (n + 1 : ℝ)) :
    C.trace x = segmentPoint (C.vertex n) (C.vertex (n + 1)) (x - n) := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
  rw [trace, dif_pos hx0]
  by_cases hright : x < (n : ℝ) + 1
  · have hfloor : ⌊x⌋₊ = n :=
      (Nat.floor_eq_iff hx0).2 ⟨hx.1, hright⟩
    simp [hfloor]
  · have hxeq : x = (n : ℝ) + 1 := le_antisymm hx.2 (not_lt.mp hright)
    subst x
    have hfloor : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by
      rw [Nat.floor_eq_iff (by positivity)]
      norm_num
    rw [hfloor]
    simp

/-- The polygonal trace is continuous on each of its unit parameter intervals. -/
lemma continuousOn_trace_unitInterval (C : LocallyRectifiablePath) (n : ℕ) :
    ContinuousOn C.trace (Icc (n : ℝ) (n + 1 : ℝ)) := by
  let g : ℝ → ℂ := fun x ↦
    segmentPoint (C.vertex n) (C.vertex (n + 1)) (x - n)
  have hg : Continuous g :=
    (continuous_segmentPoint _ _).comp (continuous_id.sub continuous_const)
  exact hg.continuousOn.congr fun x hx ↦ C.trace_eq_segmentPoint_of_mem_Icc n hx

/-- On each unit interval the global trace has bounded variation. -/
lemma boundedVariationOn_trace_unitInterval (C : LocallyRectifiablePath) (n : ℕ) :
    BoundedVariationOn C.trace (Icc (n : ℝ) (n + 1 : ℝ)) := by
  let g : ℝ → ℂ := fun x ↦
    segmentPoint (C.vertex n) (C.vertex (n + 1)) (x - n)
  have hgLip : LipschitzWith (nndist (C.vertex n) (C.vertex (n + 1))) g := by
    intro x y
    simpa only [g, edist_sub_right] using
      lipschitzWith_segmentPoint (C.vertex n) (C.vertex (n + 1))
        (x - n) (y - n)
  have hg : BoundedVariationOn g (Icc (n : ℝ) (n + 1 : ℝ)) := by
    simpa only [Function.comp_id] using
      hgLip.comp_boundedVariationOn (BoundedVariationOn.id_Icc (n : ℝ) (n + 1 : ℝ))
  unfold BoundedVariationOn at hg ⊢
  rw [show eVariationOn C.trace (Icc (n : ℝ) (n + 1 : ℝ)) =
      eVariationOn g (Icc (n : ℝ) (n + 1 : ℝ)) by
    apply eVariationOn.eq_of_eqOn
    intro x hx
    exact C.trace_eq_segmentPoint_of_mem_Icc n hx]
  exact hg

private lemma locallyFinite_int_unitIntervals :
    LocallyFinite (fun z : ℤ ↦ Icc (z : ℝ) ((z : ℝ) + 1)) := by
  have hleft : Tendsto (fun z : ℤ ↦ (z : ℝ)) atTop atTop :=
    tendsto_intCast_atTop_atTop
  have hcastBot : Tendsto (fun z : ℤ ↦ (z : ℝ)) atBot atBot :=
    tendsto_intCast_atBot_iff.mpr tendsto_id
  have hright : Tendsto (fun z : ℤ ↦ (z : ℝ) + 1) atBot atBot :=
    tendsto_atBot_add_const_right _ _ hcastBot
  exact locallyFinite_Icc_of_tendsto hleft hright

/-- The constant negative extension and the matching affine pieces glue to a continuous path on
the whole real line. -/
lemma continuous_trace (C : LocallyRectifiablePath) : Continuous C.trace := by
  apply locallyFinite_int_unitIntervals.continuous (iUnion_Icc_intCast ℝ)
    (fun _ ↦ isClosed_Icc)
  intro z
  by_cases hz : 0 ≤ z
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    simpa using C.continuousOn_trace_unitInterval n
  · have hz' : z ≤ -1 := by omega
    have hzReal : (z : ℝ) ≤ -1 := by exact_mod_cast hz'
    have hright : (z : ℝ) + 1 ≤ 0 := by linarith
    exact continuousOn_const.congr fun x hx ↦ C.trace_of_nonpos (hx.2.trans hright)

/-- The norm of the realized trace tends to infinity along its positive parameter ray. -/
lemma tendsto_trace_norm_atTop (C : LocallyRectifiablePath) :
    Tendsto (fun x : ℝ ↦ ‖C.trace x‖) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro R
  obtain ⟨N, hN⟩ := C.tendsToInfinity R
  refine ⟨(N : ℝ), fun x hx ↦ ?_⟩
  let n := ⌊x⌋₊
  have hx0 : 0 ≤ x := (Nat.cast_nonneg N).trans hx
  have hn : N ≤ n := by
    exact Nat.le_floor hx
  have hfrac : x - n ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Nat.floor_le hx0)
    · apply sub_le_iff_le_add.mpr
      simpa only [n, add_comm] using (Nat.lt_floor_add_one x).le
  rw [trace, dif_pos hx0]
  exact hN n hn (x - n) hfrac

private lemma boundedVariationOn_trace_zero_nat
    (C : LocallyRectifiablePath) (N : ℕ) :
    BoundedVariationOn C.trace (Icc (0 : ℝ) N) := by
  have hmono : Monotone (fun n : ℕ ↦ (n : ℝ)) := fun i j h ↦ by
    change (i : ℝ) ≤ (j : ℝ)
    exact_mod_cast h
  have hsum := eVariationOn.sum' C.trace hmono (n := N)
  have hfinite :
      (∑ i ∈ Finset.range N,
        eVariationOn C.trace (Icc (i : ℝ) (i + 1 : ℝ))) ≠ ∞ := by
    exact ENNReal.sum_ne_top.mpr fun i hi ↦ C.boundedVariationOn_trace_unitInterval i
  have hsum' :
      (∑ i ∈ Finset.range N,
        eVariationOn C.trace (Icc (i : ℝ) (i + 1 : ℝ))) =
          eVariationOn C.trace (Icc (0 : ℝ) N) := by
    simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] using hsum
  unfold BoundedVariationOn
  rw [← hsum']
  exact hfinite

private lemma boundedVariationOn_trace_nonpos
    (C : LocallyRectifiablePath) {a b : ℝ} (hb : b ≤ 0) :
    BoundedVariationOn C.trace (Icc a b) := by
  unfold BoundedVariationOn
  rw [show eVariationOn C.trace (Icc a b) =
      eVariationOn (fun _ : ℝ ↦ C.vertex 0) (Icc a b) by
    apply eVariationOn.eq_of_eqOn
    intro x hx
    exact C.trace_of_nonpos (hx.2.trans hb)]
  have hzero : eVariationOn (fun _ : ℝ ↦ C.vertex 0) (Icc a b) = 0 := by
    rw [eVariationOn.eq_zero_iff]
    simp
  rw [hzero]
  exact ENNReal.zero_ne_top

/-- The realized polygonal trace is locally rectifiable in Mathlib's precise bounded-variation
sense: it has finite variation on every compact parameter interval. -/
lemma locallyBoundedVariationOn_trace (C : LocallyRectifiablePath) :
    LocallyBoundedVariationOn C.trace univ := by
  intro a b _ha _hb
  simp only [univ_inter]
  by_cases hab : a ≤ b
  · by_cases hb0 : b ≤ 0
    · exact C.boundedVariationOn_trace_nonpos hb0
    · have h0b : 0 ≤ b := le_of_not_ge hb0
      obtain ⟨N, hNb⟩ := exists_nat_ge b
      have hzeroN := C.boundedVariationOn_trace_zero_nat N
      by_cases ha0 : 0 ≤ a
      · exact hzeroN.mono fun x hx ↦ ⟨ha0.trans hx.1, hx.2.trans hNb⟩
      · have ha0' : a ≤ 0 := le_of_not_ge ha0
        have hneg : BoundedVariationOn C.trace (Icc a 0) :=
          C.boundedVariationOn_trace_nonpos le_rfl
        have hjoin := eVariationOn.Icc_add_Icc (f := C.trace) (s := univ)
          ha0' (Nat.cast_nonneg N) (mem_univ (0 : ℝ))
        simp only [univ_inter] at hjoin
        have hwhole : BoundedVariationOn C.trace (Icc a (N : ℝ)) := by
          unfold BoundedVariationOn at hneg hzeroN ⊢
          rw [← hjoin]
          exact ENNReal.add_ne_top.mpr ⟨hneg, hzeroN⟩
        exact hwhole.mono fun x hx ↦ ⟨hx.1, hx.2.trans hNb⟩
  · rw [Icc_eq_empty hab]
    simp [BoundedVariationOn]

end LocallyRectifiablePath

/-- The inverse-modulus density used on an affine segment. -/
noncomputable def inverseNormDensity (f : ℂ → ℂ) (lambda : ℝ) (a b : ℂ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖f (segmentPoint a b t)‖) ^ (-lambda)

/-- The nonnegative arclength integral along the affine segment from `a` to `b`. -/
noncomputable def segmentIntegral (f : ℂ → ℂ) (lambda : ℝ) (a b : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖b - a‖ *
    ∫⁻ t in Icc (0 : ℝ) 1, inverseNormDensity f lambda a b t

/-- The nonnegative arclength integral along all segments of the polygonal ray. -/
noncomputable def lineIntegral
    (C : LocallyRectifiablePath) (f : ℂ → ℂ) (lambda : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, segmentIntegral f lambda (C.vertex n) (C.vertex (n + 1))

lemma inverseNormDensity_nonneg (f : ℂ → ℂ) (lambda : ℝ) (a b : ℂ) (t : ℝ) :
    0 ≤ inverseNormDensity f lambda a b t :=
  bot_le

lemma segmentIntegral_nonneg (f : ℂ → ℂ) (lambda : ℝ) (a b : ℂ) :
    0 ≤ segmentIntegral f lambda a b :=
  bot_le

lemma lineIntegral_nonneg
    (C : LocallyRectifiablePath) (f : ℂ → ℂ) (lambda : ℝ) :
    0 ≤ lineIntegral C f lambda :=
  bot_le

lemma measurable_inverseNormDensity (f : ℂ → ℂ) (hf : Continuous f)
    (lambda : ℝ) (a b : ℂ) : Measurable (inverseNormDensity f lambda a b) := by
  unfold inverseNormDensity
  exact (ENNReal.continuous_rpow_const.comp
    (ENNReal.continuous_ofReal.comp ((hf.comp (continuous_segmentPoint a b)).norm))).measurable

lemma aemeasurable_inverseNormDensity (f : ℂ → ℂ) (hf : Continuous f)
    (lambda : ℝ) (a b : ℂ) : AEMeasurable (inverseNormDensity f lambda a b) :=
  (measurable_inverseNormDensity f hf lambda a b).aemeasurable

lemma ennreal_rpow_neg_anti {x y : ℝ≥0∞} {lambda : ℝ} (hxy : x ≤ y)
    (hlambda : 0 ≤ lambda) : y ^ (-lambda) ≤ x ^ (-lambda) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ENNReal.inv_le_inv]
  exact ENNReal.rpow_le_rpow hxy hlambda

/-- A positive lower bound for `|f|` gives the expected constant-density segment bound. -/
lemma segmentIntegral_le_of_norm_ge {f : ℂ → ℂ} {lambda m : ℝ} {a b : ℂ}
    (hlambda : 0 ≤ lambda)
    (hfm : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ ‖f (segmentPoint a b t)‖) :
    segmentIntegral f lambda a b ≤
      ENNReal.ofReal ‖b - a‖ * (ENNReal.ofReal m) ^ (-lambda) := by
  unfold segmentIntegral
  gcongr
  calc
    (∫⁻ t in Icc (0 : ℝ) 1, inverseNormDensity f lambda a b t)
        ≤ ∫⁻ _t in Icc (0 : ℝ) 1, (ENNReal.ofReal m) ^ (-lambda) := by
          refine setLIntegral_mono measurable_const fun t ht ↦ ?_
          apply ennreal_rpow_neg_anti _ hlambda
          exact ENNReal.ofReal_le_ofReal (hfm t ht)
    _ = (ENNReal.ofReal m) ^ (-lambda) := by
      simp [Real.volume_Icc]

/-- The preceding lower-bound hypothesis also rules out an infinite one-segment integral. -/
lemma segmentIntegral_ne_top_of_norm_ge {f : ℂ → ℂ} {lambda m : ℝ} {a b : ℂ}
    (hlambda : 0 ≤ lambda) (hm : 0 < m)
    (hfm : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ ‖f (segmentPoint a b t)‖) :
    segmentIntegral f lambda a b ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (segmentIntegral_le_of_norm_ge hlambda hfm)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hm) ENNReal.ofReal_ne_top)

/-- Exponential form of `segmentIntegral_le_of_norm_ge`. -/
lemma segmentIntegral_le_of_norm_ge_exp {f : ℂ → ℂ} {lambda A : ℝ} {a b : ℂ}
    (hlambda : 0 ≤ lambda)
    (hfA : ∀ t ∈ Icc (0 : ℝ) 1, Real.exp A ≤ ‖f (segmentPoint a b t)‖) :
    segmentIntegral f lambda a b ≤
      ENNReal.ofReal ‖b - a‖ * ENNReal.ofReal (Real.exp (-lambda * A)) := by
  refine (segmentIntegral_le_of_norm_ge hlambda hfA).trans_eq ?_
  congr 1
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos A), ← Real.exp_mul]
  congr 2
  ring

@[simp] lemma segmentIntegral_self (f : ℂ → ℂ) (lambda : ℝ) (a : ℂ) :
    segmentIntegral f lambda a a = 0 := by
  simp [segmentIntegral]

lemma lineIntegral_le_tsum {C : LocallyRectifiablePath} {f : ℂ → ℂ}
    {lambda : ℝ} {bound : ℕ → ℝ≥0∞}
    (hbound : ∀ n, segmentIntegral f lambda (C.vertex n) (C.vertex (n + 1)) ≤ bound n) :
    lineIntegral C f lambda ≤ ∑' n, bound n := by
  exact ENNReal.tsum_le_tsum hbound

/-- A summable segmentwise majorant proves finiteness of the whole ray integral. -/
lemma lineIntegral_ne_top_of_bound {C : LocallyRectifiablePath} {f : ℂ → ℂ}
    {lambda : ℝ} {bound : ℕ → ℝ≥0∞} (hboundTop : ∑' n, bound n ≠ ∞)
    (hbound : ∀ n, segmentIntegral f lambda (C.vertex n) (C.vertex (n + 1)) ≤ bound n) :
    lineIntegral C f lambda ≠ ∞ := by
  exact ne_top_of_le_ne_top hboundTop (lineIntegral_le_tsum hbound)

/-- Discarding a finite initial part cannot increase a nonnegative ray integral. -/
lemma lineIntegral_drop_le (C : LocallyRectifiablePath) (f : ℂ → ℂ)
    (lambda : ℝ) (k : ℕ) : lineIntegral (C.drop k) f lambda ≤ lineIntegral C f lambda := by
  let g : ℕ → ℝ≥0∞ := fun n ↦
    segmentIntegral f lambda (C.vertex n) (C.vertex (n + 1))
  have hinj : Function.Injective (fun n : ℕ ↦ k + n) := by
    intro m n hmn
    exact Nat.add_left_cancel hmn
  simpa [lineIntegral, g, Nat.add_assoc] using
    ENNReal.tsum_comp_le_tsum_of_injective hinj g

/-- Finiteness of all inverse-modulus integrals is preserved after deleting an initial part. -/
lemma lineIntegral_drop_ne_top {C : LocallyRectifiablePath} {f : ℂ → ℂ}
    {lambda : ℝ} (hfinite : lineIntegral C f lambda ≠ ∞) (k : ℕ) :
    lineIntegral (C.drop k) f lambda ≠ ∞ :=
  ne_top_of_le_ne_top hfinite (lineIntegral_drop_le C f lambda k)

/-! ### Flattening countably many finite polygonal blocks -/

/-- A sequence of nonempty finite polygonal arcs with matching consecutive endpoints.

`point k` contains `segCount k + 1` vertices and therefore `segCount k` affine segments.  The
matching condition makes it possible to concatenate all blocks without adding artificial joining
segments. -/
structure FiniteArcBlocks where
  segCount : ℕ → ℕ
  segCount_pos : ∀ k, 0 < segCount k
  point : (k : ℕ) → Fin (segCount k + 1) → ℂ
  endpoint_eq_next : ∀ k,
    point k ⟨segCount k, Nat.lt_succ_self _⟩ = point (k + 1) ⟨0, Nat.zero_lt_succ _⟩

namespace FiniteArcBlocks

/-- The global segment index at which block `k` starts. -/
def blockStart (B : FiniteArcBlocks) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, B.segCount i

@[simp] lemma blockStart_zero (B : FiniteArcBlocks) : B.blockStart 0 = 0 := by
  simp [blockStart]

lemma blockStart_succ (B : FiniteArcBlocks) (k : ℕ) :
    B.blockStart (k + 1) = B.blockStart k + B.segCount k := by
  simp [blockStart, Finset.sum_range_succ]

lemma strictMono_blockStart (B : FiniteArcBlocks) : StrictMono B.blockStart := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [B.blockStart_succ]
  exact Nat.lt_add_of_pos_right (B.segCount_pos k)

/-- State of the elementary counter which walks through every finite block in order.  Its first
component is the block number and its second component is the segment number in that block. -/
def scan (B : FiniteArcBlocks) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      let p := B.scan n
      if p.2 + 1 < B.segCount p.1 then (p.1, p.2 + 1) else (p.1 + 1, 0)

@[simp] lemma scan_zero (B : FiniteArcBlocks) : B.scan 0 = (0, 0) := rfl

lemma scan_succ (B : FiniteArcBlocks) (n : ℕ) :
    B.scan (n + 1) =
      if (B.scan n).2 + 1 < B.segCount (B.scan n).1 then
        ((B.scan n).1, (B.scan n).2 + 1)
      else ((B.scan n).1 + 1, 0) := by
  rw [scan]

lemma scan_second_lt (B : FiniteArcBlocks) (n : ℕ) :
    (B.scan n).2 < B.segCount (B.scan n).1 := by
  induction n with
  | zero => simpa using B.segCount_pos 0
  | succ n ih =>
      rw [B.scan_succ]
      split_ifs with h
      · exact h
      · simpa using B.segCount_pos ((B.scan n).1 + 1)

private lemma scan_blockStart_add_of_scan_blockStart (B : FiniteArcBlocks) (k : ℕ)
    (hstart : B.scan (B.blockStart k) = (k, 0)) :
    ∀ j, j < B.segCount k → B.scan (B.blockStart k + j) = (k, j) := by
  intro j hj
  induction j with
  | zero => simpa using hstart
  | succ j ih =>
      have hj' : j < B.segCount k := Nat.lt_trans (Nat.lt_succ_self j) hj
      rw [show B.blockStart k + (j + 1) = (B.blockStart k + j) + 1 by omega,
        B.scan_succ, ih hj']
      simp [hj]

lemma scan_blockStart (B : FiniteArcBlocks) (k : ℕ) :
    B.scan (B.blockStart k) = (k, 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hpos := B.segCount_pos k
      have hlast := B.scan_blockStart_add_of_scan_blockStart k ih
        (B.segCount k - 1) (by omega)
      rw [B.blockStart_succ]
      rw [show B.blockStart k + B.segCount k =
          (B.blockStart k + (B.segCount k - 1)) + 1 by omega,
        B.scan_succ, hlast]
      simp only [Prod.fst, Prod.snd]
      rw [if_neg (by omega)]

lemma scan_blockStart_add (B : FiniteArcBlocks) (k : ℕ) (j : ℕ)
    (hj : j < B.segCount k) :
    B.scan (B.blockStart k + j) = (k, j) :=
  B.scan_blockStart_add_of_scan_blockStart k (B.scan_blockStart k) j hj

/-- Every counter state records the original global index as `blockStart + localIndex`. -/
lemma blockStart_add_scan (B : FiniteArcBlocks) (n : ℕ) :
    B.blockStart (B.scan n).1 + (B.scan n).2 = n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [B.scan_succ]
      split_ifs with h
      · simp only [Prod.fst, Prod.snd]
        omega
      · have hlt := B.scan_second_lt n
        rw [B.blockStart_succ]
        simp only [Prod.fst, Prod.snd]
        omega

/-- The natural order-preserving enumeration of all segments in all blocks. -/
def segmentEquiv (B : FiniteArcBlocks) : (Σ k, Fin (B.segCount k)) ≃ ℕ where
  toFun p := B.blockStart p.1 + p.2
  invFun n := ⟨(B.scan n).1, ⟨(B.scan n).2, B.scan_second_lt n⟩⟩
  left_inv p := by
    obtain ⟨k, j⟩ := p
    have hscan := B.scan_blockStart_add k j j.isLt
    have hfst := congrArg Prod.fst hscan
    have hsnd := congrArg Prod.snd hscan
    exact Sigma.ext hfst ((Fin.heq_ext_iff (congrArg B.segCount hfst)).mpr hsnd)
  right_inv n := B.blockStart_add_scan n

/-- A block vertex viewed in the common type `Fin (segCount k + 1)`. -/
def blockVertex (B : FiniteArcBlocks) (k : ℕ) (j : Fin (B.segCount k)) : ℂ :=
  B.point k ⟨j, j.isLt.trans (Nat.lt_succ_self _)⟩

/-- The endpoint immediately after a block segment. -/
def blockVertexSucc (B : FiniteArcBlocks) (k : ℕ) (j : Fin (B.segCount k)) : ℂ :=
  B.point k ⟨j + 1, Nat.succ_lt_succ j.isLt⟩

/-- The block and local segment containing a global segment index. -/
def position (B : FiniteArcBlocks) (n : ℕ) : Σ k, Fin (B.segCount k) :=
  B.segmentEquiv.symm n

/-- The flattened sequence of vertices.  The recursive counter underlying `segmentEquiv` is what
guarantees that no finite block is lost. -/
def vertex (B : FiniteArcBlocks) (n : ℕ) : ℂ :=
  let p := B.position n
  B.blockVertex p.1 p.2

lemma vertex_segmentEquiv (B : FiniteArcBlocks) (p : Σ k, Fin (B.segCount k)) :
    B.vertex (B.segmentEquiv p) = B.blockVertex p.1 p.2 := by
  unfold vertex position
  rw [B.segmentEquiv.symm_apply_apply p]

lemma vertex_segmentEquiv_succ (B : FiniteArcBlocks) (p : Σ k, Fin (B.segCount k)) :
    B.vertex (B.segmentEquiv p + 1) = B.blockVertexSucc p.1 p.2 := by
  obtain ⟨k, j⟩ := p
  by_cases hnext : j.val + 1 < B.segCount k
  · let j' : Fin (B.segCount k) := ⟨j + 1, hnext⟩
    have hindex : B.segmentEquiv ⟨k, j'⟩ = B.segmentEquiv ⟨k, j⟩ + 1 := by
      simp [segmentEquiv, j']
      omega
    rw [← hindex, B.vertex_segmentEquiv]
    rfl
  · let j' : Fin (B.segCount (k + 1)) := ⟨0, B.segCount_pos (k + 1)⟩
    have hjlast : j.val + 1 = B.segCount k := by omega
    have hindex : B.segmentEquiv ⟨k + 1, j'⟩ = B.segmentEquiv ⟨k, j⟩ + 1 := by
      simp [segmentEquiv, j', B.blockStart_succ]
      omega
    rw [← hindex, B.vertex_segmentEquiv]
    change B.point (k + 1) ⟨0, _⟩ = B.point k ⟨j + 1, _⟩
    rw [← B.endpoint_eq_next k]
    congr 1
    apply Fin.ext
    exact hjlast.symm

/-- A whole-block escape estimate transfers to the naturally flattened global segment sequence. -/
lemma eventually_flattened_segment_norm_ge (B : FiniteArcBlocks)
    (hescape : ∀ R : ℝ, ∃ K : ℕ, ∀ k ≥ K, ∀ j : Fin (B.segCount k),
      ∀ t ∈ Icc (0 : ℝ) 1,
        R ≤ ‖segmentPoint (B.blockVertex k j) (B.blockVertexSucc k j) t‖)
    (R : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
      R ≤ ‖segmentPoint (B.vertex n) (B.vertex (n + 1)) t‖ := by
  obtain ⟨K, hK⟩ := hescape R
  refine ⟨B.blockStart K, fun n hn t ht ↦ ?_⟩
  let p : Σ k, Fin (B.segCount k) := B.segmentEquiv.symm n
  have hpencode : B.segmentEquiv p = n := B.segmentEquiv.apply_symm_apply n
  have hpblock : K ≤ p.1 := by
    by_contra hnot
    have hpk : p.1 < K := Nat.lt_of_not_ge hnot
    have hlocal : B.segmentEquiv p < B.blockStart (p.1 + 1) := by
      simp only [segmentEquiv, Equiv.coe_fn_mk]
      rw [B.blockStart_succ]
      omega
    have hstart : B.blockStart (p.1 + 1) ≤ B.blockStart K :=
      B.strictMono_blockStart.monotone (Nat.succ_le_iff.mpr hpk)
    omega
  rw [← hpencode, B.vertex_segmentEquiv p, B.vertex_segmentEquiv_succ p]
  exact hK p.1 hpblock p.2 t ht

/-- Flatten finite matching arcs into a single polygonal ray, given uniform escape on all late
blocks. -/
def toLocallyRectifiablePath (B : FiniteArcBlocks)
    (hescape : ∀ R : ℝ, ∃ K : ℕ, ∀ k ≥ K, ∀ j : Fin (B.segCount k),
      ∀ t ∈ Icc (0 : ℝ) 1,
        R ≤ ‖segmentPoint (B.blockVertex k j) (B.blockVertexSucc k j) t‖) :
    LocallyRectifiablePath where
  vertex := B.vertex
  tendsToInfinity := B.eventually_flattened_segment_norm_ge hescape

@[simp] lemma toLocallyRectifiablePath_vertex (B : FiniteArcBlocks) (hescape) (n : ℕ) :
    (B.toLocallyRectifiablePath hescape).vertex n = B.vertex n := rfl

/-- Cost of one finite block, defined as the finite sum of the exact affine arclength integrals. -/
noncomputable def blockCost (B : FiniteArcBlocks) (f : ℂ → ℂ) (lambda : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∑ j : Fin (B.segCount k),
    segmentIntegral f lambda (B.blockVertex k j) (B.blockVertexSucc k j)

/-- Regrouping the flattened ray by its finite blocks is an exact identity, not merely an
inequality. -/
lemma lineIntegral_toLocallyRectifiablePath (B : FiniteArcBlocks)
    (hescape : ∀ R : ℝ, ∃ K : ℕ, ∀ k ≥ K, ∀ j : Fin (B.segCount k),
      ∀ t ∈ Icc (0 : ℝ) 1,
        R ≤ ‖segmentPoint (B.blockVertex k j) (B.blockVertexSucc k j) t‖)
    (f : ℂ → ℂ) (lambda : ℝ) :
    lineIntegral (B.toLocallyRectifiablePath hescape) f lambda =
      ∑' k, B.blockCost f lambda k := by
  unfold lineIntegral blockCost
  simp only [toLocallyRectifiablePath_vertex]
  rw [← B.segmentEquiv.tsum_eq (fun n ↦
    segmentIntegral f lambda (B.vertex n) (B.vertex (n + 1)))]
  simp_rw [B.vertex_segmentEquiv, B.vertex_segmentEquiv_succ]
  calc
    (∑' p : Σ k, Fin (B.segCount k),
        segmentIntegral f lambda (B.blockVertex p.1 p.2) (B.blockVertexSucc p.1 p.2)) =
        ∑' k, ∑' j : Fin (B.segCount k),
          segmentIntegral f lambda (B.blockVertex k j) (B.blockVertexSucc k j) :=
      ENNReal.tsum_sigma (α := ℕ) (β := fun k ↦ Fin (B.segCount k))
        (fun k j ↦
          segmentIntegral f lambda (B.blockVertex k j) (B.blockVertexSucc k j))
    _ = ∑' k, ∑ j : Fin (B.segCount k),
          segmentIntegral f lambda (B.blockVertex k j) (B.blockVertexSucc k j) := by
      congr 1
      funext k
      exact tsum_fintype _

end FiniteArcBlocks

end Erdos515

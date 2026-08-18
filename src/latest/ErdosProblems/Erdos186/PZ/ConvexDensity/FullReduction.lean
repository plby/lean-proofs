/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.DimensionOne
import ErdosProblems.Erdos186.PZ.ConvexDensity.Numerics
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Reductions for the full Pham--Zakharov convex-density lemma

The difficult geometric argument in Lemma 1 is only needed in dimensions at
least two and for the small-error range `epsilon <= 1 / (d + 1)`.  This file
proves that exact reduction, including the bookkeeping needed to enlarge the
error exponent.  In particular, a proof of `PZLemmaOneSmallEpsilon` gives the
literal public statement `PZLemmaOneStatement`; the already proved median
argument discharges dimension one.

No geometric assertion is postulated here.  `PZLemmaOneSmallEpsilon` is a
definition of the remaining theorem-shaped proof obligation.
-/

open Set MeasureTheory MeasureTheory.Measure

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-- A convex-density witness for a smaller error exponent is also a witness
for a larger one, provided `delta <= 1` and `tau > 0`. -/
theorem ConvexDensityOutput.mono_epsilon {d : ℕ}
    {epsilon epsilon' tau delta : ℝ}
    {Omega : Set (EuclideanPoint d)} {X : Finset (EuclideanPoint d)}
    (h : ConvexDensityOutput epsilon tau delta Omega X)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) (htau : 0 < tau)
    (hepsilon : epsilon ≤ epsilon') :
    ConvexDensityOutput epsilon' tau delta Omega X := by
  obtain ⟨eta, heta, Omega', hconvex, hsubset, hvolume, hpoints⟩ := h
  have hetaPos : 0 < eta := hdelta.trans_le heta.1
  have hdeltaTauOne : delta ^ tau ≤ (1 : ℝ) := by
    exact Real.rpow_le_one (le_of_lt hdelta) hdeltaOne (le_of_lt htau)
  have hetaOne : eta ≤ 1 := heta.2.trans hdeltaTauOne
  have hexponent :
      densityExponent d epsilon ≤ densityExponent d epsilon' := by
    unfold densityExponent
    linarith
  have hrpow :
      eta ^ densityExponent d epsilon' ≤
        eta ^ densityExponent d epsilon := by
    exact Real.rpow_le_rpow_of_exponent_ge hetaPos hetaOne hexponent
  refine ⟨eta, heta, Omega', hconvex, hsubset, hvolume, ?_⟩
  exact (mul_le_mul_of_nonneg_right hrpow (Nat.cast_nonneg X.card)).trans hpoints

/-- If the point set does not affinely span the ambient Euclidean space, the
conclusion is immediate: its convex hull contains every point and has zero
ambient volume.  This removes all lower-dimensional degeneracies from the
geometric core of Lemma 1. -/
theorem convexDensityOutput_of_affineSpan_ne_top {d : ℕ}
    {epsilon tau delta : ℝ}
    {Omega : Set (EuclideanPoint d)} {X : Finset (EuclideanPoint d)}
    (hd : 1 ≤ d) (hepsilon : 0 < epsilon)
    (htau : 0 < tau) (htauOne : tau < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint d)) ⊆ Omega)
    (hspan : affineSpan ℝ (X : Set (EuclideanPoint d)) ≠ ⊤) :
    ConvexDensityOutput epsilon tau delta Omega X := by
  let S : Set (EuclideanPoint d) := convexHull ℝ (X : Set (EuclideanPoint d))
  have hXS : (X : Set (EuclideanPoint d)) ⊆ S := by
    exact subset_convexHull ℝ (X : Set (EuclideanPoint d))
  have hSOmega : S ⊆ Omega := by
    exact convexHull_min hXOmega hOmega.convex
  have hmeasureSpan :
      (volume : Measure (EuclideanPoint d))
          (affineSpan ℝ (X : Set (EuclideanPoint d)) : Set (EuclideanPoint d)) = 0 := by
    exact Measure.addHaar_affineSubspace volume _ hspan
  have hmeasureS : (volume : Measure (EuclideanPoint d)) S = 0 := by
    exact measure_mono_null (convexHull_subset_affineSpan (X : Set (EuclideanPoint d)))
      hmeasureSpan
  have hdeltaTau : delta ≤ delta ^ tau := by
    exact delta_le_rpow_of_exponent_mem_Ioc hdelta hdeltaOne ⟨htau, htauOne.le⟩
  have hexponent : 0 ≤ densityExponent d epsilon := by
    rw [show densityExponent d epsilon = alpha d + epsilon by rfl]
    exact add_nonneg (alpha_nonneg hd) hepsilon.le
  have hrpow : delta ^ densityExponent d epsilon ≤ 1 := by
    exact Real.rpow_le_one hdelta.le hdeltaOne hexponent
  refine ⟨delta, ⟨le_rfl, hdeltaTau⟩, S, convex_convexHull ℝ _, hSOmega, ?_, ?_⟩
  · simp [relativeVolume, hmeasureS]
  · rw [pointsIn_eq_self_of_subset hXS]
    exact mul_le_of_le_one_left (Nat.cast_nonneg X.card) hrpow

/-- The small-convex-hull branch of the paper is formal independently of
the width estimate used to enter it.  If the convex hull already has relative
volume at most `delta ^ tau`, take that hull itself and retain every point. -/
theorem convexDensityOutput_of_small_convexHull {d : ℕ}
    {epsilon tau delta : ℝ}
    {Omega : Set (EuclideanPoint d)} {X : Finset (EuclideanPoint d)}
    (hd : 1 ≤ d) (hepsilon : 0 < epsilon)
    (htau : 0 < tau) (htauOne : tau < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint d)) ⊆ Omega)
    (hsmall : relativeVolume (convexHull ℝ (X : Set (EuclideanPoint d))) Omega ≤
      ENNReal.ofReal (delta ^ tau)) :
    ConvexDensityOutput epsilon tau delta Omega X := by
  let S : Set (EuclideanPoint d) := convexHull ℝ (X : Set (EuclideanPoint d))
  have hXS : (X : Set (EuclideanPoint d)) ⊆ S := by
    exact subset_convexHull ℝ (X : Set (EuclideanPoint d))
  have hSOmega : S ⊆ Omega := by
    exact convexHull_min hXOmega hOmega.convex
  have hdeltaTau : delta ≤ delta ^ tau := by
    exact delta_le_rpow_of_exponent_mem_Ioc hdelta hdeltaOne ⟨htau, htauOne.le⟩
  have hdeltaTauOne : delta ^ tau ≤ (1 : ℝ) := by
    exact Real.rpow_le_one hdelta.le hdeltaOne htau.le
  have hexponent : 0 ≤ densityExponent d epsilon := by
    rw [show densityExponent d epsilon = alpha d + epsilon by rfl]
    exact add_nonneg (alpha_nonneg hd) hepsilon.le
  have hrpow : (delta ^ tau) ^ densityExponent d epsilon ≤ 1 := by
    exact Real.rpow_le_one (Real.rpow_nonneg hdelta.le tau) hdeltaTauOne hexponent
  refine ⟨delta ^ tau, ⟨hdeltaTau, le_rfl⟩, S, convex_convexHull ℝ _, hSOmega,
    ?_, ?_⟩
  · exact hsmall
  · rw [pointsIn_eq_self_of_subset hXS]
    exact mul_le_of_le_one_left (Nat.cast_nonneg X.card) hrpow

/-- Exact entry dichotomy for the genuinely geometric part of Lemma 1.
Every input is already solved unless the point set affinely spans and its
convex hull occupies more than `delta ^ tau` of the ambient body's volume. -/
theorem convexDensityOutput_or_fullSpan_largeHull {d : ℕ}
    {epsilon tau delta : ℝ}
    {Omega : Set (EuclideanPoint d)} {X : Finset (EuclideanPoint d)}
    (hd : 1 ≤ d) (hepsilon : 0 < epsilon)
    (htau : 0 < tau) (htauOne : tau < 1)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint d)) ⊆ Omega) :
    ConvexDensityOutput epsilon tau delta Omega X ∨
      (affineSpan ℝ (X : Set (EuclideanPoint d)) = ⊤ ∧
        ENNReal.ofReal (delta ^ tau) <
          relativeVolume (convexHull ℝ (X : Set (EuclideanPoint d))) Omega) := by
  by_cases hspan : affineSpan ℝ (X : Set (EuclideanPoint d)) = ⊤
  · by_cases hsmall :
        relativeVolume (convexHull ℝ (X : Set (EuclideanPoint d))) Omega ≤
          ENNReal.ofReal (delta ^ tau)
    · exact Or.inl (convexDensityOutput_of_small_convexHull hd hepsilon htau htauOne
        hdelta hdeltaOne hOmega hXOmega hsmall)
    · exact Or.inr ⟨hspan, lt_of_not_ge hsmall⟩
  · exact Or.inl (convexDensityOutput_of_affineSpan_ne_top hd hepsilon htau htauOne
      hdelta hdeltaOne hOmega hXOmega hspan)

/-- The convex hull of a finite full-dimensional point set is a convex body. -/
theorem isConvexBody_convexHull_of_affineSpan_eq_top {d : ℕ}
    {X : Finset (EuclideanPoint d)}
    (hspan : affineSpan ℝ (X : Set (EuclideanPoint d)) = ⊤) :
    IsConvexBody (convexHull ℝ (X : Set (EuclideanPoint d))) := by
  let P : Set (EuclideanPoint d) := convexHull ℝ (X : Set (EuclideanPoint d))
  have hconvex : Convex ℝ P := convex_convexHull ℝ _
  refine ⟨hconvex, X.finite_toSet.isCompact_convexHull ℝ, ?_⟩
  rw [hconvex.interior_nonempty_iff_affineSpan_eq_top, affineSpan_convexHull]
  exact hspan

/-- Enlarging the ambient convex body preserves a convex-density witness.
The numerator is unchanged while the reference volume only increases. -/
theorem ConvexDensityOutput.mono_ambient {d : ℕ}
    {epsilon tau delta : ℝ}
    {P Omega : Set (EuclideanPoint d)} {X : Finset (EuclideanPoint d)}
    (h : ConvexDensityOutput epsilon tau delta P X)
    (hP : IsConvexBody P) (hOmega : IsConvexBody Omega)
    (hPOmega : P ⊆ Omega) :
    ConvexDensityOutput epsilon tau delta Omega X := by
  obtain ⟨eta, heta, Omega', hconvex, hsubset, hvolume, hpoints⟩ := h
  refine ⟨eta, heta, Omega', hconvex, hsubset.trans hPOmega, ?_, hpoints⟩
  rw [relativeVolume_le_iff hP eta] at hvolume
  rw [relativeVolume_le_iff hOmega eta]
  exact hvolume.trans (by
    gcongr)

/-- A witness proved after replacing the ambient body by `convexHull X`
immediately gives the original output. -/
theorem convexDensityOutput_of_convexHull {d : ℕ}
    {epsilon tau delta : ℝ}
    {Omega : Set (EuclideanPoint d)} {X : Finset (EuclideanPoint d)}
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint d)) ⊆ Omega)
    (hspan : affineSpan ℝ (X : Set (EuclideanPoint d)) = ⊤)
    (h : ConvexDensityOutput epsilon tau delta
      (convexHull ℝ (X : Set (EuclideanPoint d))) X) :
    ConvexDensityOutput epsilon tau delta Omega X := by
  exact h.mono_ambient
    (isConvexBody_convexHull_of_affineSpan_eq_top hspan) hOmega
    (convexHull_min hXOmega hOmega.convex)

/-- The genuinely geometric range left after the elementary reductions:
dimension at least two and `epsilon <= 1/(d+1)`. -/
def PZLemmaOneSmallEpsilon : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / ((d : ℝ) + 1) →
      ∃ tau deltaZero : ℝ,
        0 < tau ∧ tau < 1 ∧ 0 < deltaZero ∧
        ∀ delta : ℝ, 0 < delta → delta < deltaZero →
          ∃ largeEnough : ℕ,
            ∀ (Omega : Set (EuclideanPoint d)) (X : Finset (EuclideanPoint d)),
              IsConvexBody Omega →
              (X : Set (EuclideanPoint d)) ⊆ Omega →
              largeEnough ≤ X.card →
              ConvexGeometry.IsDeltaConvexPosition delta X →
              ConvexDensityOutput epsilon tau delta Omega X

/-- The fully normalized remaining core.  The ambient body has disappeared:
for a full-span finite set it is enough to work in `convexHull X`, with the
paper's fixed choice `tau = epsilon / 10`.  All hypotheses here are used by
the genuine heavy-cell/boundary-graph argument. -/
def PZFullSpanHullCore : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 / ((d : ℝ) + 1) →
      ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta < deltaZero →
          ∃ largeEnough : ℕ,
            ∀ X : Finset (EuclideanPoint d),
              largeEnough ≤ X.card →
              affineSpan ℝ (X : Set (EuclideanPoint d)) = ⊤ →
              ConvexGeometry.IsDeltaConvexPosition delta X →
              ConvexDensityOutput epsilon (tau epsilon) delta
                (convexHull ℝ (X : Set (EuclideanPoint d))) X

/-- The normalized full-span convex-hull core implies the exact small-error
statement with an arbitrary ambient convex body. -/
theorem pzLemmaOneSmallEpsilon_of_fullSpanHullCore
    (hcore : PZFullSpanHullCore) : PZLemmaOneSmallEpsilon := by
  intro d hd epsilon hepsilon hepsilonLe
  obtain ⟨deltaZero, hdeltaZero, hdeltaZeroOne, hcoreDelta⟩ :=
    hcore d hd epsilon hepsilon hepsilonLe
  have htau := tau_mem_Ioo_of_epsilon_le_inv_dimension hepsilon hepsilonLe
  refine ⟨tau epsilon, deltaZero, htau.1, htau.2, hdeltaZero, ?_⟩
  intro delta hdelta hdeltaSmall
  obtain ⟨largeEnough, hlarge⟩ := hcoreDelta delta hdelta hdeltaSmall
  refine ⟨largeEnough, ?_⟩
  intro Omega X hOmega hXOmega hcard hconvex
  have hdeltaOne : delta ≤ 1 := (hdeltaSmall.trans_le hdeltaZeroOne).le
  by_cases hspan : affineSpan ℝ (X : Set (EuclideanPoint d)) = ⊤
  · exact convexDensityOutput_of_convexHull hOmega hXOmega hspan
      (hlarge X hcard hspan hconvex)
  · exact convexDensityOutput_of_affineSpan_ne_top (by omega) hepsilon
      htau.1 htau.2 hdelta hdeltaOne hOmega hXOmega hspan

/-- It suffices to prove the Pham--Zakharov geometric argument for positive
errors at most `1/(d+1)` and dimensions at least two. -/
theorem pzLemmaOneStatement_of_smallEpsilon
    (hsmall : PZLemmaOneSmallEpsilon) : PZLemmaOneStatement := by
  intro d hd epsilon hepsilon
  by_cases hdOne : d = 1
  · subst d
    exact pzLemmaOneStatement_dimension_one epsilon hepsilon
  · have hdTwo : 2 ≤ d := by omega
    let epsilonSmall : ℝ := min epsilon (1 / ((d : ℝ) + 1))
    have hdenom : 0 < (d : ℝ) + 1 := by positivity
    have hepsilonSmall : 0 < epsilonSmall := by
      dsimp [epsilonSmall]
      exact lt_min hepsilon (one_div_pos.mpr hdenom)
    have hepsilonSmallLe : epsilonSmall ≤ 1 / ((d : ℝ) + 1) := by
      exact min_le_right _ _
    obtain ⟨tau, deltaZero, htau, htauOne, hdeltaZero, hcore⟩ :=
      hsmall d hdTwo epsilonSmall hepsilonSmall hepsilonSmallLe
    refine ⟨tau, min deltaZero 1, htau, htauOne, ?_, ?_⟩
    · exact lt_min hdeltaZero zero_lt_one
    · intro delta hdelta hdeltaSmall
      have hdeltaCore : delta < deltaZero :=
        hdeltaSmall.trans_le (min_le_left _ _)
      have hdeltaOne : delta ≤ 1 :=
        (hdeltaSmall.trans_le (min_le_right _ _)).le
      obtain ⟨largeEnough, hlarge⟩ := hcore delta hdelta hdeltaCore
      refine ⟨largeEnough, ?_⟩
      intro Omega X hOmega hsubset hcard hconvex
      exact (hlarge Omega X hOmega hsubset hcard hconvex).mono_epsilon
        hdelta hdeltaOne htau (min_le_left _ _)

end

end Erdos186.PZ.ConvexDensity

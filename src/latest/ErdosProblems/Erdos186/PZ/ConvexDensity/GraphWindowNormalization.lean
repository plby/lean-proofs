/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.CenteredBoundary
import ErdosProblems.Erdos186.PZ.ConvexDensity.IndexedGraphDensity

/-!
# Normalizing a physical upper-boundary window to the unit graph grid

The cap argument produces upper-boundary points whose base coordinates lie
in `[-q,q]^n`.  The analytic graph lemmas use the unit grid and require a
concave function on `[-1/2,3/2]^n` with values in `[0,1]`.  The affine
change `x ↦ 2q*x-q` and vertical scaling by an outer radius provide exactly
that interface.
-/

open Set

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false

noncomputable section

open Subgradient

/-- Physical base point corresponding to a normalized base coordinate. -/
def graphPhysicalBase {n : ℕ} (q : ℝ) (x : Fin n → ℝ) : EuclideanPoint n :=
  WithLp.toLp 2 (fun i ↦ 2 * q * x i - q)

@[simp]
theorem coordinate_graphPhysicalBase {n : ℕ} (q : ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    coordinate (graphPhysicalBase q x) i = 2 * q * x i - q := by
  rfl

/-- The normalized upper roof.  The upper roof is already nonnegative on
the inner-ball base, so only division by the outer radius is needed. -/
def normalizedUpperRoof {n : ℕ} (P : Set (EuclideanPoint (n + 1)))
    (hP : IsCompact P) (q outer : ℝ) (x : Fin n → ℝ) : ℝ :=
  upperBoundaryValue P hP (graphPhysicalBase q x) / outer

/-- Normalize an ambient graph point to unit base and unit height. -/
def normalizeGraphPoint {n : ℕ} (q outer : ℝ)
    (z : EuclideanPoint (n + 1)) : EuclideanPoint (n + 1) :=
  appendCoordinate
    (WithLp.toLp 2 (fun i ↦ (coordinate (baseCoordinates z) i + q) / (2 * q)))
    (lastCoordinate z / outer)

@[simp]
theorem baseCoordinates_normalizeGraphPoint {n : ℕ} (q outer : ℝ)
    (z : EuclideanPoint (n + 1)) :
    baseCoordinates (normalizeGraphPoint q outer z) =
      WithLp.toLp 2
        (fun i ↦ (coordinate (baseCoordinates z) i + q) / (2 * q)) := by
  simp [normalizeGraphPoint]

@[simp]
theorem lastCoordinate_normalizeGraphPoint {n : ℕ} (q outer : ℝ)
    (z : EuclideanPoint (n + 1)) :
    lastCoordinate (normalizeGraphPoint q outer z) =
      lastCoordinate z / outer := by
  simp [normalizeGraphPoint]

/-- The two base changes are inverse when the window radius is positive. -/
theorem graphPhysicalBase_of_normalized_base {n : ℕ} {q : ℝ} (hq : 0 < q)
    (outer : ℝ) (z : EuclideanPoint (n + 1)) :
    graphPhysicalBase q
        (WithLp.ofLp (baseCoordinates (normalizeGraphPoint q outer z))) =
      baseCoordinates z := by
  ext i
  simp [graphPhysicalBase, normalizeGraphPoint]
  field_simp
  ring

/-- The expanded unit box maps into the physical box of coordinate radius
`2q`. -/
theorem graphPhysicalBase_mem_symmetricAxisBox {n : ℕ} {q : ℝ}
    (hq : 0 ≤ q) {x : Fin n → ℝ}
    (hx : x ∈ pzExpandedBox n (1 / 2)) :
    graphPhysicalBase q x ∈ symmetricAxisBox n (2 * q) := by
  intro i
  have hi : -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ 1 + 1 / 2 :=
    ⟨hx.1 i, hx.2 i⟩
  change -(2 * q) ≤ 2 * q * x i - q ∧
    2 * q * x i - q ≤ 2 * q
  constructor <;> nlinarith

/-- The physical radius-`2q` coordinate box lies in the standard inscribed
base box under the displayed quantitative window condition. -/
theorem symmetricAxisBox_two_mul_subset_inscribed {n : ℕ}
    {q inner : ℝ}
    (hwindow : 2 * q ≤ inner / Real.sqrt (n : ℝ)) :
    symmetricAxisBox n (2 * q) ⊆
      symmetricAxisBox n (inner / Real.sqrt (n : ℝ)) := by
  intro x hx i
  exact ⟨(neg_le_neg hwindow).trans (hx i).1,
    (hx i).2.trans hwindow⟩

/-- The physical base map preserves affine combinations. -/
theorem graphPhysicalBase_combo {n : ℕ} (q : ℝ)
    (x y : Fin n → ℝ) (a b : ℝ) (hab : a + b = 1) :
    graphPhysicalBase q (a • x + b • y) =
      a • graphPhysicalBase q x + b • graphPhysicalBase q y := by
  ext i
  simp [graphPhysicalBase, smul_eq_mul]
  linear_combination q * hab

/-- The normalized roof has precisely the concavity and range hypotheses of
the indexed graph-density lemmas. -/
theorem normalizedUpperRoof_concave_range {n : ℕ} (hn : 0 < n)
    {P : Set (EuclideanPoint (n + 1))}
    (hPcompact : IsCompact P) (hPconvex : Convex ℝ P)
    {q inner outer : ℝ} (hq : 0 ≤ q) (hinner : 0 ≤ inner)
    (houterPos : 0 < outer)
    (hwindow : 2 * q ≤ inner / Real.sqrt (n : ℝ))
    (hinnerBall : Metric.closedBall 0 inner ⊆ P)
    (houterBall : P ⊆ Metric.closedBall 0 outer) :
    ConcaveOn ℝ (pzExpandedBox n (1 / 2))
        (normalizedUpperRoof P hPcompact q outer) ∧
      ∀ x ∈ pzExpandedBox n (1 / 2),
        normalizedUpperRoof P hPcompact q outer x ∈ Set.Icc (0 : ℝ) 1 := by
  let B := symmetricAxisBox n (inner / Real.sqrt (n : ℝ))
  have hbase : ∀ x ∈ pzExpandedBox n (1 / 2), graphPhysicalBase q x ∈ B := by
    intro x hx
    exact symmetricAxisBox_two_mul_subset_inscribed hwindow
      (graphPhysicalBase_mem_symmetricAxisBox hq hx)
  have hroof := concaveOn_upperBoundaryValue_on_inscribedAxisBox
    hn hPcompact hPconvex hinner hinnerBall
  constructor
  · refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hg := hroof.2 (hbase x hx) (hbase y hy) ha hb hab
    rw [← graphPhysicalBase_combo q x y a b hab] at hg
    change a * (upperBoundaryValue P hPcompact (graphPhysicalBase q x) / outer) +
        b * (upperBoundaryValue P hPcompact (graphPhysicalBase q y) / outer) ≤
      upperBoundaryValue P hPcompact
        (graphPhysicalBase q (a • x + b • y)) / outer
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    calc
      a * (upperBoundaryValue P hPcompact (graphPhysicalBase q x) * outer⁻¹) +
          b * (upperBoundaryValue P hPcompact (graphPhysicalBase q y) * outer⁻¹) =
        (a * upperBoundaryValue P hPcompact (graphPhysicalBase q x) +
          b * upperBoundaryValue P hPcompact (graphPhysicalBase q y)) * outer⁻¹ := by
            ring
      _ ≤ upperBoundaryValue P hPcompact
          (graphPhysicalBase q (a • x + b • y)) * outer⁻¹ :=
        mul_le_mul_of_nonneg_right hg (inv_nonneg.mpr houterPos.le)
  · intro x hx
    have hb := upperBoundaryValue_bounds_on_inscribedAxisBox
      hn hPcompact hinner hinnerBall houterBall (hbase x hx)
    exact ⟨div_nonneg hb.1 houterPos.le,
      (div_le_one houterPos).2 hb.2⟩

/-- A physical upper-boundary point becomes a point on the normalized roof. -/
theorem normalizeGraphPoint_on_normalizedUpperRoof {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hPcompact : IsCompact P)
    {q outer : ℝ} (hq : 0 < q) (houter : 0 < outer)
    {z : EuclideanPoint (n + 1)}
    (hz : z = upperBoundaryPoint P hPcompact (baseCoordinates z)) :
    lastCoordinate (normalizeGraphPoint q outer z) =
      normalizedUpperRoof P hPcompact q outer
        (WithLp.ofLp (baseCoordinates (normalizeGraphPoint q outer z))) := by
  rw [lastCoordinate_normalizeGraphPoint, normalizedUpperRoof,
    graphPhysicalBase_of_normalized_base hq]
  have hzlast : lastCoordinate z =
      upperBoundaryValue P hPcompact (baseCoordinates z) := by
    exact (congrArg lastCoordinate hz).trans (by rfl)
  exact congrArg (fun t : ℝ ↦ t / outer) hzlast

end

end Erdos186.PZ.ConvexDensity

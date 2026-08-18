/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.LemmaSeven
import ErdosProblems.Erdos186.PZ.ConvexDensity.AffineSlab

/-!
# Narrow functional slabs inside integer boxes

This is the geometric estimate used in the separation proof of
Pham--Zakharov Lemma 14.  A nonzero functional is split along a coordinate
on which its coefficient has maximal absolute value.  The remaining
coordinates form the base of an affine graph slab; since a full-dimensional
integer box has side lengths at least one, the resulting relative volume is
at most `2 * d * t`.
-/

namespace Erdos186.PZ.Intersection

open Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

abbrev EuclideanPoint (d : ℕ) := ConvexDensity.EuclideanPoint d

/-- Sum of the absolute standard-coordinate coefficients of a functional. -/
def coefficientMass {d : ℕ} (f : (Fin d → ℝ) →L[ℝ] ℝ) : ℝ :=
  ∑ i, |f (Pi.single i 1)|

/-- The portion of an integer box lying in the centered open functional
slab of normalized half-width `t`. -/
def functionalSlabInBox {d : ℕ} (B : IntegerBox d)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ) : Set (EuclideanPoint d) :=
  {x | x ∈ OneStepAssembly.boxRealization B ∧
    |f x.ofLp| < t * coefficientMass f}

@[simp]
theorem mem_functionalSlabInBox_iff {d : ℕ}
    {B : IntegerBox d}
    {f : (Fin d → ℝ) →L[ℝ] ℝ} {t : ℝ} {x : EuclideanPoint d} :
    x ∈ functionalSlabInBox B f t ↔
      x ∈ OneStepAssembly.boxRealization B ∧
        |f x.ofLp| < t * coefficientMass f := by
  rfl

theorem functionalSlabInBox_subset {d : ℕ}
    (B : IntegerBox d)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    functionalSlabInBox B f t ⊆ OneStepAssembly.boxRealization B := by
  intro x hx
  exact hx.1

/-- Functional slabs clipped to a box are convex. -/
theorem convex_functionalSlabInBox {d : ℕ}
    (B : IntegerBox d)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    Convex ℝ (functionalSlabInBox B f t) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxbox, hxslab⟩
  rcases hy with ⟨hybox, hyslab⟩
  constructor
  · exact (ConvexDensity.convex_closedAxisBox
      (fun i ↦ (B.lower i : ℝ)) (fun i ↦ (B.upper i : ℝ)))
      hxbox hybox ha hb hab
  · rw [abs_lt] at hxslab hyslab ⊢
    have hmap : f ((a • x + b • y).ofLp) =
        a * f x.ofLp + b * f y.ofLp := by
      change f (a • x.ofLp + b • y.ofLp) = _
      rw [map_add, map_smul, map_smul]
      simp
    rw [hmap]
    rcases ha.eq_or_lt with rfl | haPos
    · have hbOne : b = 1 := by linarith
      simpa [hbOne] using hyslab
    rcases hb.eq_or_lt with rfl | hbPos
    · have haOne : a = 1 := by linarith
      simpa [haOne] using hxslab
    constructor
    · nlinarith [mul_lt_mul_of_pos_left hxslab.1 haPos,
        mul_lt_mul_of_pos_left hyslab.1 hbPos]
    · nlinarith [mul_lt_mul_of_pos_left hxslab.2 haPos,
        mul_lt_mul_of_pos_left hyslab.2 hbPos]

/-- A nonzero functional has a largest nonzero standard-coordinate
coefficient, and its coefficient mass is at most the dimension times that
coefficient. -/
theorem exists_maximal_coefficient {n : ℕ}
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ i : Fin (n + 1),
      f (Pi.single i 1) ≠ 0 ∧
        coefficientMass f ≤ (n + 1 : ℝ) * |f (Pi.single i 1)| := by
  obtain ⟨i, _hi, himax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin (n + 1) ↦ |f (Pi.single j 1)|) Finset.univ_nonempty
  have hmass : coefficientMass f ≤
      (n + 1 : ℝ) * |f (Pi.single i 1)| := by
    change (∑ j : Fin (n + 1), |f (Pi.single j 1)|) ≤ _
    simpa [nsmul_eq_mul, mul_comm] using
      (Finset.univ.sum_le_card_nsmul
        (fun j : Fin (n + 1) ↦ |f (Pi.single j 1)|)
        |f (Pi.single i 1)| (fun j _hj ↦ himax j (Finset.mem_univ j)))
  refine ⟨i, ?_, hmass⟩
  intro hi
  apply hf
  ext x
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin (n + 1) → ℝ) := by
    funext k
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp
    · intro j _hj hjk
      simp [hjk]
    · simp
  rw [hx, map_sum]
  have hall : ∀ j : Fin (n + 1), f (Pi.single j 1) = 0 := by
    intro j
    have hj := himax j (Finset.mem_univ j)
    rw [hi, abs_zero] at hj
    exact abs_eq_zero.mp (le_antisymm hj (abs_nonneg _))
  simp [hall]

/-- Expansion of a functional in the standard basis. -/
theorem apply_eq_sum_standard {d : ℕ}
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (x : Fin d → ℝ) :
    f x = ∑ i, x i * f (Pi.single i 1) := by
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin d → ℝ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _hi hij
      simp [hij]
    · simp
  calc
    f x = f (∑ i, x i • (Pi.single i 1 : Fin d → ℝ)) := congrArg f hx
    _ = ∑ i, x i * f (Pi.single i 1) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]

/-- Lower endpoints of the base obtained by deleting coordinate `i`. -/
def erasedLower {n : ℕ} (B : IntegerBox (n + 1)) (i : Fin (n + 1)) :
    EuclideanPoint n :=
  WithLp.toLp 2 (fun j ↦ (B.lower (i.succAbove j) : ℝ))

/-- Upper endpoints of the base obtained by deleting coordinate `i`. -/
def erasedUpper {n : ℕ} (B : IntegerBox (n + 1)) (i : Fin (n + 1)) :
    EuclideanPoint n :=
  WithLp.toLp 2 (fun j ↦ (B.upper (i.succAbove j) : ℝ))

/-- The contribution of all coordinates except `i` to `f`. -/
def residualFunctional {n : ℕ}
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (i : Fin (n + 1)) :
    EuclideanPoint n →L[ℝ] ℝ :=
  ∑ j : Fin n, f (Pi.single (i.succAbove j) 1) •
    (PiLp.proj (p := (2 : ℝ≥0∞)) (fun _ : Fin n ↦ ℝ) j)

@[simp]
theorem residualFunctional_apply {n : ℕ}
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (i : Fin (n + 1))
    (y : EuclideanPoint n) :
    residualFunctional f i y =
      ∑ j : Fin n, y.ofLp j * f (Pi.single (i.succAbove j) 1) := by
  simp [residualFunctional, mul_comm]

/-- The graph whose vertical deviation is the functional value divided by
the selected nonzero coefficient. -/
def functionalGraph {n : ℕ}
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (i : Fin (n + 1)) :
    EuclideanPoint n →L[ℝ] ℝ :=
  (-(f (Pi.single i 1))⁻¹) • residualFunctional f i

@[simp]
theorem functionalGraph_apply {n : ℕ}
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (i : Fin (n + 1))
    (y : EuclideanPoint n) :
    functionalGraph f i y =
      -(f (Pi.single i 1))⁻¹ *
        (∑ j : Fin n, y.ofLp j * f (Pi.single (i.succAbove j) 1)) := by
  simp [functionalGraph]

/-- The exact total vertical thickness after solving the functional
inequality for coordinate `i`. -/
def functionalThickness {n : ℕ}
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (t : ℝ) (i : Fin (n + 1)) : ℝ :=
  2 * t * coefficientMass f / |f (Pi.single i 1)|

/-- The clipped functional slab lies in the graph slab obtained by solving
for any coordinate with nonzero coefficient. -/
theorem functionalSlabInBox_subset_affineSlab {n : ℕ}
    (B : IntegerBox (n + 1))
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (t : ℝ) (i : Fin (n + 1))
    (hi : f (Pi.single i 1) ≠ 0) :
    functionalSlabInBox B f t ⊆
      ConvexDensity.AffineSlab.affineSlab
        (erasedLower B i) (erasedUpper B i) i
        (functionalGraph f i) 0 (functionalThickness f t i) := by
  intro x hx
  have hxbox := hx.1
  have hxabs := hx.2
  have hbase : ConvexDensity.AffineSlab.eraseCoordinate i x ∈
      ConvexDensity.AffineSlab.axisBaseBox
        (erasedLower B i) (erasedUpper B i) := by
    intro j
    simpa [OneStepAssembly.boxRealization, OneStepAssembly.toDiscretizationBox,
      BoxDiscretization.IntegerBox.realization, ConvexDensity.closedAxisBox,
      ConvexDensity.AffineSlab.eraseCoordinate_apply, erasedLower, erasedUpper]
      using hxbox (i.succAbove j)
  refine ⟨hbase, ?_⟩
  let a : ℝ := f (Pi.single i 1)
  let r : ℝ := residualFunctional f i
    (ConvexDensity.AffineSlab.eraseCoordinate i x)
  have ha : a ≠ 0 := hi
  have haabs : 0 < |a| := abs_pos.mpr ha
  have hr : (∑ j : Fin n,
      (ConvexDensity.AffineSlab.eraseCoordinate i x).ofLp j *
        f (Pi.single (i.succAbove j) 1)) = r := by
    exact (residualFunctional_apply f i _).symm
  have hsplit : f x.ofLp = a * x.ofLp i + r := by
    rw [apply_eq_sum_standard,
      Fin.sum_univ_succAbove
        (fun j : Fin (n + 1) ↦ x.ofLp j * f (Pi.single j 1)) i]
    rw [← hr]
    simp only [a, ConvexDensity.AffineSlab.eraseCoordinate_apply]
    ring
  have hdev : |x.ofLp i - functionalGraph f i
      (ConvexDensity.AffineSlab.eraseCoordinate i x)| = |f x.ofLp| / |a| := by
    have hmul : a * (x.ofLp i - functionalGraph f i
        (ConvexDensity.AffineSlab.eraseCoordinate i x)) = f x.ofLp := by
      rw [functionalGraph_apply]
      rw [hr]
      simp only [a]
      rw [hsplit]
      field_simp
      ring
    rw [← hmul, abs_mul, mul_div_cancel_left₀ _ (abs_ne_zero.mpr ha)]
  have hdevlt : |x.ofLp i - functionalGraph f i
      (ConvexDensity.AffineSlab.eraseCoordinate i x)| <
      (t * coefficientMass f) / |a| := by
    rw [hdev]
    exact (div_lt_div_iff_of_pos_right haabs).mpr hxabs
  rw [abs_lt] at hdevlt
  simp only [ConvexDensity.AffineSlab.affineValue, add_zero]
  change functionalGraph f i
        (ConvexDensity.AffineSlab.eraseCoordinate i x) -
        functionalThickness f t i / 2 < x.ofLp i
      ∧ x.ofLp i < functionalGraph f i
        (ConvexDensity.AffineSlab.eraseCoordinate i x) +
        functionalThickness f t i / 2
  have hhalf : functionalThickness f t i / 2 =
      (t * coefficientMass f) / |a| := by
    simp only [functionalThickness, a]
    ring
  rw [hhalf]
  constructor <;> linarith

/-- Every side of an integer box whose realization is a genuine convex body
has real length at least one. -/
theorem one_le_integerBox_sideLength_of_isConvexBody {d : ℕ}
    (B : IntegerBox d)
    (hB : ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization B)) (i : Fin d) :
    (1 : ℝ) ≤ (B.upper i : ℝ) - (B.lower i : ℝ) := by
  obtain ⟨x, hx⟩ := hB.nonempty
  have horder : B.lower i ≤ B.upper i := by
    have hxi := hx i
    exact_mod_cast hxi.1.trans hxi.2
  have hstrict : B.lower i < B.upper i := by
    apply lt_of_le_of_ne horder
    intro heq
    apply hB.volume_ne_zero
    have hrealization : OneStepAssembly.boxRealization B =
        ConvexDensity.closedAxisBox
          (fun j ↦ (B.lower j : ℝ)) (fun j ↦ (B.upper j : ℝ)) := by
      ext y
      rfl
    rw [hrealization,
      ConvexDensity.volume_closedAxisBox]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [heq]
  have hcast : (B.lower i : ℝ) + 1 ≤ (B.upper i : ℝ) := by
    exact_mod_cast (show B.lower i + 1 ≤ B.upper i by omega)
  linarith

/-- Real thickness of the graph slab is bounded by `2 * d * t` when the
split coordinate has maximal absolute coefficient. -/
theorem functionalThickness_le_of_maximal {n : ℕ}
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (t : ℝ) (i : Fin (n + 1))
    (ht : 0 ≤ t) (hi : f (Pi.single i 1) ≠ 0)
    (himax : coefficientMass f ≤
      (n + 1 : ℝ) * |f (Pi.single i 1)|) :
    functionalThickness f t i ≤ 2 * (n + 1 : ℝ) * t := by
  have haabs : 0 < |f (Pi.single i 1)| := abs_pos.mpr hi
  rw [functionalThickness, div_le_iff₀ haabs]
  have hmul := mul_le_mul_of_nonneg_left himax
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2) ht)
  calc
    2 * t * coefficientMass f ≤
        2 * t * ((n + 1 : ℝ) * |f (Pi.single i 1)|) := by
      simpa [mul_assoc] using hmul
    _ = (2 * (n + 1 : ℝ) * t) * |f (Pi.single i 1)| := by ring

/-- Volume form of the narrow functional-slab estimate. -/
theorem volume_functionalSlabInBox_le {n : ℕ}
    (B : IntegerBox (n + 1))
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (t : ℝ)
    (hB : ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization B))
    (ht : 0 ≤ t) (hf : f ≠ 0) :
    (volume : Measure (EuclideanPoint (n + 1)))
        (functionalSlabInBox B f t) ≤
      ENNReal.ofReal (2 * (n + 1 : ℝ) * t) *
        (volume : Measure (EuclideanPoint (n + 1)))
          (OneStepAssembly.boxRealization B) := by
  obtain ⟨i, hi, himax⟩ := exists_maximal_coefficient f hf
  let baseVolume : ℝ≥0∞ :=
    (volume : Measure (EuclideanPoint n))
      (ConvexDensity.AffineSlab.axisBaseBox
        (erasedLower B i) (erasedUpper B i))
  have hsub := functionalSlabInBox_subset_affineSlab B f t i hi
  have hvolume :
      (volume : Measure (EuclideanPoint (n + 1)))
          (functionalSlabInBox B f t) ≤
        ENNReal.ofReal (functionalThickness f t i) * baseVolume := by
    calc
      (volume : Measure (EuclideanPoint (n + 1)))
          (functionalSlabInBox B f t) ≤
          volume (ConvexDensity.AffineSlab.affineSlab
            (erasedLower B i) (erasedUpper B i) i
            (functionalGraph f i) 0 (functionalThickness f t i)) :=
        measure_mono hsub
      _ = ENNReal.ofReal (functionalThickness f t i) * baseVolume := by
        rw [ConvexDensity.AffineSlab.volume_affineSlab]
  have hthickness : functionalThickness f t i ≤
      2 * (n + 1 : ℝ) * t :=
    functionalThickness_le_of_maximal f t i ht hi himax
  have hbase : baseVolume ≤
      (volume : Measure (EuclideanPoint (n + 1)))
        (OneStepAssembly.boxRealization B) := by
    have hrealization : OneStepAssembly.boxRealization B =
        ConvexDensity.closedAxisBox
          (fun j ↦ (B.lower j : ℝ)) (fun j ↦ (B.upper j : ℝ)) := by
      ext y
      rfl
    rw [hrealization,
      ConvexDensity.volume_closedAxisBox,
      Fin.prod_univ_succAbove
        (fun j : Fin (n + 1) ↦
          ENNReal.ofReal ((B.upper j : ℝ) - (B.lower j : ℝ))) i]
    rw [show baseVolume =
        ∏ j : Fin n, ENNReal.ofReal
          ((B.upper (i.succAbove j) : ℝ) -
            (B.lower (i.succAbove j) : ℝ)) by
      simp [baseVolume, ConvexDensity.AffineSlab.volume_axisBaseBox,
        erasedLower, erasedUpper]]
    have hside := one_le_integerBox_sideLength_of_isConvexBody B hB i
    calc
      ∏ j : Fin n, ENNReal.ofReal
          ((B.upper (i.succAbove j) : ℝ) -
            (B.lower (i.succAbove j) : ℝ)) =
          1 * ∏ j : Fin n, ENNReal.ofReal
          ((B.upper (i.succAbove j) : ℝ) -
            (B.lower (i.succAbove j) : ℝ)) := by simp
      _ ≤ ENNReal.ofReal ((B.upper i : ℝ) - (B.lower i : ℝ)) *
          ∏ j : Fin n, ENNReal.ofReal
          ((B.upper (i.succAbove j) : ℝ) -
            (B.lower (i.succAbove j) : ℝ)) := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal hside
  calc
    (volume : Measure (EuclideanPoint (n + 1)))
        (functionalSlabInBox B f t) ≤
        ENNReal.ofReal (functionalThickness f t i) * baseVolume := hvolume
    _ ≤ ENNReal.ofReal (2 * (n + 1 : ℝ) * t) * baseVolume := by
      gcongr
    _ ≤ ENNReal.ofReal (2 * (n + 1 : ℝ) * t) *
        (volume : Measure (EuclideanPoint (n + 1)))
          (OneStepAssembly.boxRealization B) := by
      gcongr

/-- Relative-volume form consumed by PZ Lemma 7. -/
theorem relativeVolume_functionalSlabInBox_le {n : ℕ}
    (B : IntegerBox (n + 1))
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (t : ℝ)
    (hB : ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization B))
    (ht : 0 ≤ t) (hf : f ≠ 0) :
    ConvexDensity.relativeVolume (functionalSlabInBox B f t)
        (OneStepAssembly.boxRealization B) ≤
      ENNReal.ofReal (2 * (n + 1 : ℝ) * t) := by
  rw [ConvexDensity.relativeVolume_le_iff hB]
  exact volume_functionalSlabInBox_le B f t hB ht hf

/-- Dimension-indexed spelling of the relative-volume estimate. -/
theorem relativeVolume_functionalSlabInBox_le_dimension {d : ℕ}
    (hd : 0 < d) (B : IntegerBox d)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ)
    (hB : ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization B))
    (ht : 0 ≤ t) (hf : f ≠ 0) :
    ConvexDensity.relativeVolume (functionalSlabInBox B f t)
        (OneStepAssembly.boxRealization B) ≤
      ENNReal.ofReal (2 * (d : ℝ) * t) := by
  cases d with
  | zero => omega
  | succ n =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        relativeVolume_functionalSlabInBox_le B f t hB ht hf

end

end Erdos186.PZ.Intersection

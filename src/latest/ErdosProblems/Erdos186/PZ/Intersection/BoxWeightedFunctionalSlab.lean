/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.FunctionalSlab
import ErdosProblems.Erdos186.PZ.Intersection.SlabJohnBound

/-!
# Functional slabs normalized by the side lengths of a box

The isotropic coefficient mass loses the source GAP widths.  Here the
coefficient of the `i`-th standard vector is weighted by the actual length
of the `i`-th side of the control box.  The same side length then cancels in
the Fubini estimate, so the relative-volume bound remains dimension-only.
-/

namespace Erdos186.PZ.Intersection

open Set MeasureTheory
open scoped BigOperators ENNReal
open OneStepAssembly

noncomputable section

set_option autoImplicit false

/-- Real length of one side of an integer box. -/
def integerBoxSideLength {d : ℕ} (B : IntegerBox d) (i : Fin d) : ℝ :=
  (B.upper i : ℝ) - (B.lower i : ℝ)

/-- The dual mass associated with the coordinate side lengths of `B`. -/
def boxCoefficientMass {d : ℕ} (B : IntegerBox d)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) : ℝ :=
  ∑ i, integerBoxSideLength B i * |f (Pi.single i 1)|

/-- The centered functional slab whose normalization is dual to `B`. -/
def boxWeightedFunctionalSlabInBox {d : ℕ} (B : IntegerBox d)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ) : Set (EuclideanPoint d) :=
  {x | x ∈ OneStepAssembly.boxRealization B ∧
    |f x.ofLp| < t * boxCoefficientMass B f}

@[simp] theorem mem_boxWeightedFunctionalSlabInBox_iff {d : ℕ}
    {B : IntegerBox d} {f : (Fin d → ℝ) →L[ℝ] ℝ}
    {t : ℝ} {x : EuclideanPoint d} :
    x ∈ boxWeightedFunctionalSlabInBox B f t ↔
      x ∈ OneStepAssembly.boxRealization B ∧
        |f x.ofLp| < t * boxCoefficientMass B f := by
  rfl

theorem boxWeightedFunctionalSlabInBox_subset {d : ℕ}
    (B : IntegerBox d) (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    boxWeightedFunctionalSlabInBox B f t ⊆
      OneStepAssembly.boxRealization B := by
  intro x hx
  exact hx.1

theorem convex_boxWeightedFunctionalSlabInBox {d : ℕ}
    (B : IntegerBox d) (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    Convex ℝ (boxWeightedFunctionalSlabInBox B f t) := by
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

theorem integerBoxSideLength_pos_of_isConvexBody {d : ℕ}
    (B : IntegerBox d)
    (hB : ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization B)) (i : Fin d) :
    0 < integerBoxSideLength B i := by
  unfold integerBoxSideLength
  exact lt_of_lt_of_le zero_lt_one
    (one_le_integerBox_sideLength_of_isConvexBody B hB i)

/-- A nonzero functional has a coordinate maximizing its side-weighted
coefficient. -/
theorem exists_maximal_boxCoefficient {n : ℕ}
    (B : IntegerBox (n + 1))
    (hB : ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization B))
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ i : Fin (n + 1),
      f (Pi.single i 1) ≠ 0 ∧
      boxCoefficientMass B f ≤
        (n + 1 : ℝ) *
          (integerBoxSideLength B i * |f (Pi.single i 1)|) := by
  obtain ⟨i, _hi, himax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin (n + 1) ↦
      integerBoxSideLength B j * |f (Pi.single j 1)|)
    Finset.univ_nonempty
  have hmass : boxCoefficientMass B f ≤
      (n + 1 : ℝ) *
        (integerBoxSideLength B i * |f (Pi.single i 1)|) := by
    change (∑ j : Fin (n + 1),
      integerBoxSideLength B j * |f (Pi.single j 1)|) ≤ _
    simpa [nsmul_eq_mul, mul_comm] using
      (Finset.univ.sum_le_card_nsmul
        (fun j : Fin (n + 1) ↦
          integerBoxSideLength B j * |f (Pi.single j 1)|)
        (integerBoxSideLength B i * |f (Pi.single i 1)|)
        (fun j _hj ↦ himax j (Finset.mem_univ j)))
  refine ⟨i, ?_, hmass⟩
  intro hi
  apply hf
  ext x
  have hx : x = ∑ j, x j •
      (Pi.single j 1 : Fin (n + 1) → ℝ) := by
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
    rw [hi, abs_zero, mul_zero] at hj
    have hside := integerBoxSideLength_pos_of_isConvexBody B hB j
    have hprod : integerBoxSideLength B j * |f (Pi.single j 1)| = 0 :=
      le_antisymm hj (mul_nonneg hside.le (abs_nonneg _))
    exact abs_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hside.ne')
  simp [hall]

def boxWeightedFunctionalThickness {n : ℕ}
    (B : IntegerBox (n + 1))
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (t : ℝ) (i : Fin (n + 1)) : ℝ :=
  2 * t * boxCoefficientMass B f / |f (Pi.single i 1)|

theorem boxWeightedFunctionalSlabInBox_subset_affineSlab {n : ℕ}
    (B : IntegerBox (n + 1))
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (t : ℝ) (i : Fin (n + 1))
    (hi : f (Pi.single i 1) ≠ 0) :
    boxWeightedFunctionalSlabInBox B f t ⊆
      ConvexDensity.AffineSlab.affineSlab
        (erasedLower B i) (erasedUpper B i) i
        (functionalGraph f i) 0
        (boxWeightedFunctionalThickness B f t i) := by
  intro x hx
  have hxbox := hx.1
  have hxabs := hx.2
  have hbase : ConvexDensity.AffineSlab.eraseCoordinate i x ∈
      ConvexDensity.AffineSlab.axisBaseBox
        (erasedLower B i) (erasedUpper B i) := by
    intro j
    simpa [OneStepAssembly.boxRealization,
      OneStepAssembly.toDiscretizationBox,
      BoxDiscretization.IntegerBox.realization,
      ConvexDensity.closedAxisBox,
      ConvexDensity.AffineSlab.eraseCoordinate_apply,
      erasedLower, erasedUpper] using hxbox (i.succAbove j)
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
      (ConvexDensity.AffineSlab.eraseCoordinate i x)| =
      |f x.ofLp| / |a| := by
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
      (t * boxCoefficientMass B f) / |a| := by
    rw [hdev]
    exact (div_lt_div_iff_of_pos_right haabs).mpr hxabs
  rw [abs_lt] at hdevlt
  simp only [ConvexDensity.AffineSlab.affineValue, add_zero]
  change functionalGraph f i
        (ConvexDensity.AffineSlab.eraseCoordinate i x) -
        boxWeightedFunctionalThickness B f t i / 2 < x.ofLp i
      ∧ x.ofLp i < functionalGraph f i
        (ConvexDensity.AffineSlab.eraseCoordinate i x) +
        boxWeightedFunctionalThickness B f t i / 2
  have hhalf : boxWeightedFunctionalThickness B f t i / 2 =
      (t * boxCoefficientMass B f) / |a| := by
    simp only [boxWeightedFunctionalThickness, a]
    ring
  rw [hhalf]
  constructor <;> linarith

theorem boxWeightedFunctionalThickness_le_of_maximal {n : ℕ}
    (B : IntegerBox (n + 1))
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (t : ℝ) (i : Fin (n + 1))
    (ht : 0 ≤ t) (hi : f (Pi.single i 1) ≠ 0)
    (himax : boxCoefficientMass B f ≤
      (n + 1 : ℝ) *
        (integerBoxSideLength B i * |f (Pi.single i 1)|)) :
    boxWeightedFunctionalThickness B f t i ≤
      (2 * (n + 1 : ℝ) * t) * integerBoxSideLength B i := by
  have haabs : 0 < |f (Pi.single i 1)| := abs_pos.mpr hi
  rw [boxWeightedFunctionalThickness, div_le_iff₀ haabs]
  have hmul := mul_le_mul_of_nonneg_left himax
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 2) ht)
  calc
    2 * t * boxCoefficientMass B f ≤
        2 * t * ((n + 1 : ℝ) *
          (integerBoxSideLength B i * |f (Pi.single i 1)|)) := by
      simpa [mul_assoc] using hmul
    _ = ((2 * (n + 1 : ℝ) * t) * integerBoxSideLength B i) *
        |f (Pi.single i 1)| := by ring

theorem volume_boxWeightedFunctionalSlabInBox_le {n : ℕ}
    (B : IntegerBox (n + 1))
    (f : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (t : ℝ)
    (hB : ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization B))
    (ht : 0 ≤ t) (hf : f ≠ 0) :
    (volume : Measure (EuclideanPoint (n + 1)))
        (boxWeightedFunctionalSlabInBox B f t) ≤
      ENNReal.ofReal (2 * (n + 1 : ℝ) * t) *
        (volume : Measure (EuclideanPoint (n + 1)))
          (OneStepAssembly.boxRealization B) := by
  obtain ⟨i, hi, himax⟩ := exists_maximal_boxCoefficient B hB f hf
  let baseVolume : ℝ≥0∞ :=
    (volume : Measure (EuclideanPoint n))
      (ConvexDensity.AffineSlab.axisBaseBox
        (erasedLower B i) (erasedUpper B i))
  have hsub := boxWeightedFunctionalSlabInBox_subset_affineSlab
    B f t i hi
  have hvolume :
      (volume : Measure (EuclideanPoint (n + 1)))
          (boxWeightedFunctionalSlabInBox B f t) ≤
        ENNReal.ofReal (boxWeightedFunctionalThickness B f t i) *
          baseVolume := by
    calc
      (volume : Measure (EuclideanPoint (n + 1)))
          (boxWeightedFunctionalSlabInBox B f t) ≤
          volume (ConvexDensity.AffineSlab.affineSlab
            (erasedLower B i) (erasedUpper B i) i
            (functionalGraph f i) 0
            (boxWeightedFunctionalThickness B f t i)) :=
        measure_mono hsub
      _ = ENNReal.ofReal (boxWeightedFunctionalThickness B f t i) *
          baseVolume := by
        rw [ConvexDensity.AffineSlab.volume_affineSlab]
  have hthickness : boxWeightedFunctionalThickness B f t i ≤
      (2 * (n + 1 : ℝ) * t) * integerBoxSideLength B i :=
    boxWeightedFunctionalThickness_le_of_maximal B f t i ht hi himax
  have hside : 0 ≤ integerBoxSideLength B i :=
    (integerBoxSideLength_pos_of_isConvexBody B hB i).le
  have hcoeff : 0 ≤ 2 * (n + 1 : ℝ) * t := by positivity
  have hrealization : OneStepAssembly.boxRealization B =
      ConvexDensity.closedAxisBox
        (fun j ↦ (B.lower j : ℝ)) (fun j ↦ (B.upper j : ℝ)) := by
    ext y
    rfl
  have hfull :
      (volume : Measure (EuclideanPoint (n + 1)))
          (OneStepAssembly.boxRealization B) =
        ENNReal.ofReal (integerBoxSideLength B i) * baseVolume := by
    rw [hrealization, ConvexDensity.volume_closedAxisBox,
      Fin.prod_univ_succAbove
        (fun j : Fin (n + 1) ↦
          ENNReal.ofReal ((B.upper j : ℝ) - (B.lower j : ℝ))) i]
    rw [show baseVolume =
        ∏ j : Fin n, ENNReal.ofReal
          ((B.upper (i.succAbove j) : ℝ) -
            (B.lower (i.succAbove j) : ℝ)) by
      simp [baseVolume, ConvexDensity.AffineSlab.volume_axisBaseBox,
        erasedLower, erasedUpper]]
    rfl
  calc
    (volume : Measure (EuclideanPoint (n + 1)))
        (boxWeightedFunctionalSlabInBox B f t) ≤
        ENNReal.ofReal (boxWeightedFunctionalThickness B f t i) *
          baseVolume := hvolume
    _ ≤ ENNReal.ofReal
          ((2 * (n + 1 : ℝ) * t) * integerBoxSideLength B i) *
          baseVolume := by gcongr
    _ = (ENNReal.ofReal (2 * (n + 1 : ℝ) * t) *
          ENNReal.ofReal (integerBoxSideLength B i)) * baseVolume := by
      rw [ENNReal.ofReal_mul hcoeff]
    _ = ENNReal.ofReal (2 * (n + 1 : ℝ) * t) *
        (volume : Measure (EuclideanPoint (n + 1)))
          (OneStepAssembly.boxRealization B) := by rw [hfull]; ring

theorem relativeVolume_boxWeightedFunctionalSlabInBox_le_dimension
    {d : ℕ} (hd : 0 < d) (B : IntegerBox d)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (t : ℝ)
    (hB : ConvexDensity.IsConvexBody
      (OneStepAssembly.boxRealization B))
    (ht : 0 ≤ t) (hf : f ≠ 0) :
    ConvexDensity.relativeVolume (boxWeightedFunctionalSlabInBox B f t)
        (OneStepAssembly.boxRealization B) ≤
      ENNReal.ofReal (2 * (d : ℝ) * t) := by
  cases d with
  | zero => omega
  | succ n =>
      rw [ConvexDensity.relativeVolume_le_iff hB]
      simpa only [Nat.cast_add, Nat.cast_one] using
        volume_boxWeightedFunctionalSlabInBox_le B f t hB ht hf

/-- Source-facing John contradiction for the side-length-normalized slab. -/
theorem exists_boxWeightedFunctionalSlabContradictionConstants
    (d : ℕ) (hd : 0 < d) :
    ∃ factorBound : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ {s D k loss referenceVolume boxFactor : ℕ}
        {A : Finset (LatticePoint d)}
        (W : CFP.EnhancedCFPWitness A s D k loss)
        (B : IntegerBox d)
        (f : (Fin d → ℝ) →L[ℝ] ℝ) (t gamma : ℝ),
        W.rank = d →
        ConvexDensity.IsConvexBody (OneStepAssembly.boxRealization B) →
        f ≠ 0 → 0 < t →
        (0 : LatticePoint d) ∈ B.carrier →
        W.core ⊆ B.carrier →
        (∀ x ∈ W.core,
          |f (realVector x)| < t * boxCoefficientMass B f) →
        1 ≤ (2 * (d : ℝ) * t) * (B.carrier.card : ℝ) →
        B.carrier.card ≤ boxFactor * referenceVolume →
        0 < referenceVolume → 0 < gamma →
        gamma * (referenceVolume : ℝ) ≤
          (W.progression.volume : ℝ) →
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            constant * boxFactor < (k : ℝ) * gamma →
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            constant * (2 * (d : ℝ) * t) * boxFactor < gamma →
        False := by
  obtain ⟨factorBound, constant, hconstant, hcontradiction⟩ :=
    exists_slabJohnContradictionConstants pzLemmaSeven d hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro s D k loss referenceVolume boxFactor A W B f t gamma hWrank hB hf ht
    hzeroB hcoreB hcoreSlab hscale hbox hrefPos hgamma hlower
    hlowHierarchy hfullHierarchy
  let Omega := boxWeightedFunctionalSlabInBox B f t
  have hmemWeighted {x : LatticePoint d} (hxB : x ∈ B.carrier)
      (hxslab : |f (realVector x)| < t * boxCoefficientMass B f) :
      x ∈ boxLatticePointsIn B Omega := by
    unfold boxLatticePointsIn
    rw [mem_latticeRestriction]
    refine ⟨hxB, ?_⟩
    rw [mem_boxWeightedFunctionalSlabInBox_iff]
    constructor
    · change ∀ i, (B.lower i : ℝ) ≤ (x i : ℝ) ∧
          (x i : ℝ) ≤ (B.upper i : ℝ)
      intro i
      have hxi := (IntegerBox.mem_carrier_iff.mp hxB) i
      exact ⟨by exact_mod_cast hxi.1, by exact_mod_cast hxi.2⟩
    · change |f (fun i ↦ (x i : ℝ))| < t * boxCoefficientMass B f
      exact hxslab
  have hcore : W.core ⊆ boxLatticePointsIn B Omega := by
    intro x hx
    exact hmemWeighted (hcoreB hx) (hcoreSlab x hx)
  have hmassPos : 0 < boxCoefficientMass B f := by
    have hmass := coefficientMass_pos f hf
    apply hmass.trans_le
    unfold coefficientMass boxCoefficientMass
    apply Finset.sum_le_sum
    intro i _hi
    have hside : (1 : ℝ) ≤ integerBoxSideLength B i := by
      exact one_le_integerBox_sideLength_of_isConvexBody B hB i
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hside (abs_nonneg _)
  have hzero : (0 : LatticePoint d) ∈ boxLatticePointsIn B Omega := by
    apply hmemWeighted hzeroB
    have hz : realVector (0 : LatticePoint d) = (0 : Fin d → ℝ) := by
      funext i
      simp [realVector]
    rw [hz, map_zero, abs_zero]
    exact mul_pos ht hmassPos
  have hnonempty : (boxLatticePointsIn B Omega).Nonempty := ⟨0, hzero⟩
  apply hcontradiction W hWrank B Omega (2 * (d : ℝ) * t) gamma hB
  · positivity
  · exact convex_boxWeightedFunctionalSlabInBox B f t
  · exact boxWeightedFunctionalSlabInBox_subset B f t
  · exact hnonempty
  · exact relativeVolume_boxWeightedFunctionalSlabInBox_le_dimension
      hd B f t hB ht.le hf
  · exact hscale
  · exact hcore
  · exact hzero
  · exact hbox
  · exact hrefPos
  · exact hgamma
  · exact hlower
  · exact hlowHierarchy
  · exact hfullHierarchy

end

end Erdos186.PZ.Intersection

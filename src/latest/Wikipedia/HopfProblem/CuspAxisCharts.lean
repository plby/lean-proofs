import Wikipedia.HopfProblem.CuspDoubleCurves
import Wikipedia.HopfProblem.ToricAxisCharts
import Wikipedia.HopfProblem.ToricBranchSeparation

/-!
# The affine parametrizations of the quotient double curves

The coordinate axes descend to injective holomorphic parametrizations in
the cusp quotient. Translated triangles have the same axis images, and
the lower reference axis and its adjacent upper axis cover the double
curve, with inversion as their transition on nonzero parameters.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricFan.Triangle

open ToricCharts

theorem zeroCount_axisPoint_eq_three (s : Triangle) (i : Fin 3) (z : ℂ) :
    zeroCount (axisPoint s i z) = 3 ↔ z = 0 := by
  rw [zeroCount_eq_three]
  constructor
  · intro h
    simpa only [axisPoint_apply_axisIndex, Pi.zero_apply] using congrFun h (s.axisIndex i)
  · rintro rfl
    exact axisPoint_zero s i

end Wikipedia.HopfProblem.ToricFan.Triangle

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace ToricFan Triangle

def centralAxis (s : Triangle) (i : Fin 3) (z : ℂ) : centralAffine :=
  ⟨axisPoint s i z, time_axisPoint s i z⟩

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

def axisLift (s : Triangle) (i : Fin 3) (z : ℂ) : Tube (disc ε) :=
  centralLift ε hε s (centralAxis s i z)

theorem axisLift_continuous (s : Triangle) (i : Fin 3) : Continuous (axisLift ε hε s i) :=
  ((inclusion_openEmbedding s).continuous.comp (axisPoint_holomorphic s i).continuous).subtype_mk _

theorem axisLift_holomorphic (s : Triangle) (i : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ (CoordinateSpace 3))
      ω (axisLift ε hε s i) := by
  intro z
  have he : ContMDiffAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (fun w => (axisLift ε hε s i w : Space)) z ↔
    ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ (CoordinateSpace 3))
      ω (axisLift ε hε s i) z := ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((inclusion_holomorphic s).comp (axisPoint_holomorphic s i).contMDiff z)

def axisMap (s : Triangle) (i : Fin 3) : ℂ → QuotientSpace C ε :=
  quotientMap C ε ∘ axisLift ε hε s i

theorem axisMap_eq_centralChartMap (s : Triangle) (i : Fin 3) (z : ℂ) :
    axisMap C ε hε s i z = centralChartMap C ε hε s (centralAxis s i z) := rfl

theorem axisMap_continuous (s : Triangle) (i : Fin 3) : Continuous (axisMap C ε hε s i) :=
  (quotientMap_continuous C ε).comp (axisLift_continuous ε hε s i)

@[simp] theorem axisMap_zero (s : Triangle) (i : Fin 3) :
    axisMap C ε hε s i 0 = centralChartMap C ε hε s centralOrigin := by
  rw [axisMap_eq_centralChartMap]
  exact congrArg (centralChartMap C ε hε s) (Subtype.ext (axisPoint_zero s i))

@[simp] theorem branchCount_axisMap (s : Triangle) (i : Fin 3) (z : ℂ) :
    branchCount C ε (axisMap C ε hε s i z) = zeroCount (axisPoint s i z) :=
  ToricSpace.branchCount_inclusion s (axisPoint s i z)

theorem axisMap_mem_doubleCurve (s : Triangle) (i : Fin 3) (z : ℂ) :
    axisMap C ε hε s i z ∈ doubleCurve C ε hε i :=
  (mem_doubleCurve_centralChartMap C ε hε s (centralAxis s i z) i).mpr
    (fun j hj => axisPoint_apply_of_ne s i j z hj)

theorem axisMap_injective (s : Triangle) (i : Fin 3) :
    Function.Injective (axisMap C ε hε s i) := by
  let := tubeAction C (disc ε)
  intro z w heq
  have hc := congrArg (branchCount C ε) heq
  rw [branchCount_axisMap, branchCount_axisMap] at hc
  have hziff : z = 0 ↔ w = 0 := by
    rw [← zeroCount_axisPoint_eq_three s i z, ← zeroCount_axisPoint_eq_three s i w, hc]
  by_cases hz : z = 0
  · exact hz.trans (hziff.mp hz).symm
  have hw : w ≠ 0 := fun h => hz (hziff.mpr h)
  have horb := Quotient.exact heq
  change axisLift ε hε s i z ∈ MulAction.orbit LatticeGroup (axisLift ε hε s i w) at horb
  obtain ⟨g, hg⟩ := horb
  have he : twistedTranslate C g.toAdd (inclusion s (axisPoint s i w)) =
      inclusion s (axisPoint s i z) := congrArg Subtype.val hg
  have hb : branchVertices (inclusion s (axisPoint s i w)) =
      branchVertices (inclusion s (axisPoint s i z)) := by
    rw [branchVertices_inclusion, branchVertices_inclusion]
    apply chartBranches_eq_of_zero_iff
    intro j
    by_cases hj : j = s.axisIndex i
    · subst j
      simp [hw, hz]
    · simp [axisPoint_apply_of_ne s i j _ hj]
  have hg0 := twistedTranslate_eq_of_branchVertices_eq C g.toAdd _ _ (by simp) hb he
  rw [hg0, twistedTranslate_zero] at he
  exact (axisPoint_injective s i ((inclusion_openEmbedding s).injective he)).symm

theorem axisMap_inversion (i : Fin 3) {z : ℂ} (hz : z ≠ 0) :
    axisMap C ε hε referenceTriangle i z =
      axisMap C ε hε (upperNeighbour i) i z⁻¹ := by
  apply congrArg (quotientMap C ε)
  exact Subtype.ext (axis_inclusion_inversion i hz)

theorem axisMap_shift (v : Fin 2 → ℤ) (s : Triangle) (i : Fin 3) (z : ℂ) :
    axisMap C ε hε (s.shift (cuspVector v)) i
      (factors (s.shift (cuspVector v)) (fibreMultiplier (exponentialMultiplier C v 0))
        ((s.shift (cuspVector v)).axisIndex i) * z) = axisMap C ε hε s i z := by
  have he : tubeTranslate C (disc ε) v (axisLift ε hε s i z) =
      axisLift ε hε (s.shift (cuspVector v)) i
        (factors (s.shift (cuspVector v)) (fibreMultiplier (exponentialMultiplier C v 0))
          ((s.shift (cuspVector v)).axisIndex i) * z) :=
    Subtype.ext (twistedTranslate_axisPoint C v s i z)
  exact (congrArg (quotientMap C ε) he).symm.trans
    (quotientMap_translate C ε v (axisLift ε hε s i z))

theorem axisMap_range_shift (v : Fin 2 → ℤ) (s : Triangle) (i : Fin 3) :
    range (axisMap C ε hε (s.shift (cuspVector v)) i) = range (axisMap C ε hε s i) := by
  let u := factors (s.shift (cuspVector v)) (fibreMultiplier (exponentialMultiplier C v 0))
    ((s.shift (cuspVector v)).axisIndex i)
  have hu : u ≠ 0 := factors_nonzero _ _ _
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    have hm : u * (z / u) = z := by simp [div_eq_mul_inv, hu, mul_left_comm]
    refine ⟨z / u, ?_⟩
    have h := axisMap_shift C ε hε v s i (z / u)
    change axisMap C ε hε (s.shift (cuspVector v)) i (u * (z / u)) = _ at h
    rw [hm] at h
    exact h.symm
  · rintro ⟨z, rfl⟩
    exact ⟨u * z, axisMap_shift C ε hε v s i z⟩

theorem axisMap_range_same_upper (s t : Triangle) (i : Fin 3) (hst : s.upper = t.upper) :
    range (axisMap C ε hε s i) = range (axisMap C ε hε t i) := by
  let v : Fin 2 → ℤ := ![t.a - s.a, t.b - s.b]
  have he : s.shift (cuspVector (-cuspVector v)) = t := by
    simp only [cuspVector_neg, cuspVector_cuspVector, neg_neg]
    apply Triangle.ext
    · simp [shift, v]
    · simp [shift, v]
    · exact hst
  simpa only [he] using (axisMap_range_shift C ε hε (-cuspVector v) s i).symm

theorem doubleCurve_eq_two_axis_ranges (i : Fin 3) : doubleCurve C ε hε i =
    range (axisMap C ε hε referenceTriangle i) ∪ range (axisMap C ε hε (upperNeighbour i) i) := by
  apply subset_antisymm
  · intro x hx
    have ht := doubleCurve_subset_central C ε hε i hx
    rw [central_fibre_eq_union C ε hε] at ht
    obtain ⟨s, z, rfl⟩ := Set.mem_iUnion.mp ht
    have hz := (eq_axisPoint_iff s i (z : CoordinateSpace 3)).mpr
      ((mem_doubleCurve_centralChartMap C ε hε s z i).mp hx)
    have hz' : centralAxis s i ((z : CoordinateSpace 3) (s.axisIndex i)) = z := Subtype.ext hz.symm
    have hm : centralChartMap C ε hε s z ∈ range (axisMap C ε hε s i) := by
      refine ⟨(z : CoordinateSpace 3) (s.axisIndex i), ?_⟩
      rw [axisMap_eq_centralChartMap, hz']
    cases hs : s.upper
    · left
      rwa [axisMap_range_same_upper C ε hε s referenceTriangle i hs] at hm
    · right
      rwa [axisMap_range_same_upper C ε hε s (upperNeighbour i) i
        (hs.trans (upperNeighbour_upper i).symm)] at hm
  · rintro x (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · exact axisMap_mem_doubleCurve C ε hε referenceTriangle i z
    · exact axisMap_mem_doubleCurve C ε hε (upperNeighbour i) i z

theorem axisMap_reference_zero_ne_upper (i : Fin 3) :
    axisMap C ε hε referenceTriangle i 0 ≠ axisMap C ε hε (upperNeighbour i) i 0 := by
  rw [axisMap_zero, axisMap_zero]
  intro he
  have h := (centralChartMap_origin_eq_iff C ε hε referenceTriangle (upperNeighbour i)).mp he
  simp [referenceTriangle] at h

theorem axisMap_holomorphic (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (s : Triangle) (i : Fin 3) :
    letI := chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ (CoordinateSpace 3))
      ω (axisMap C ε hε s i) := by
  let := chartedSpace C ε hε hε1 hC hR
  exact (quotientMap_holomorphic C ε hε hε1 hC hR).comp (axisLift_holomorphic ε hε s i)

end Wikipedia.HopfProblem.CuspQuotient

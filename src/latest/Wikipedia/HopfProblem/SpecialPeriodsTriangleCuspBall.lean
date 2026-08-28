import Wikipedia.HopfProblem.SpecialPeriodsTriangleCusp
import Wikipedia.HopfProblem.SpecialPeriodsTriangleHorodisc

/-!
# Exponential coordinates on horodiscs

The cusp exponential restricts to a holomorphic open map from a
horodisc to the corresponding punctured complex ball.  For nonnegative
height this map is surjective, and its fibres remain exactly the integer
powers of the actual cusp transformation.  This file does not descend
the map through the full triangle-group quotient.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The radius corresponding to the horizontal boundary at height `Y`. -/
def cuspRadius (Y : ℝ) : ℝ := Real.exp (-2 * Real.pi * Y / width)

@[simp] theorem cuspRadius_pos (Y : ℝ) : 0 < cuspRadius Y := Real.exp_pos _

@[simp] theorem cuspRadius_zero : cuspRadius 0 = 1 := by simp [cuspRadius]

theorem cuspRadius_le_one (Y : ℝ) (hY : 0 ≤ Y) : cuspRadius Y ≤ 1 := by
  rw [cuspRadius, Real.exp_le_one_iff]
  apply div_nonpos_of_nonpos_of_nonneg _ width_pos.le
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) Real.pi_pos.le) hY

theorem cuspRadius_lt_one (Y : ℝ) (hY : 0 < Y) : cuspRadius Y < 1 := by
  rw [cuspRadius, Real.exp_lt_one_iff]
  apply div_neg_of_neg_of_pos _ width_pos
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos) hY

/-- The actual punctured complex ball used by the cusp coordinate at
height `Y`, with its inherited topology and complex manifold structure. -/
def puncturedCuspBall (Y : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨{q : ℂ | q ≠ 0 ∧ ‖q‖ < cuspRadius Y},
    isOpen_compl_singleton.inter (isOpen_lt continuous_norm continuous_const)⟩

@[simp] theorem mem_puncturedCuspBall (Y : ℝ) (q : ℂ) :
    q ∈ puncturedCuspBall Y ↔ q ≠ 0 ∧ ‖q‖ < cuspRadius Y := Iff.rfl

theorem cuspQ_mem_puncturedCuspBall_iff (Y : ℝ) (z : ℍ) :
    cuspQ z ∈ puncturedCuspBall Y ↔ z ∈ horodisc Y := by
  change (cuspQ z ≠ 0 ∧ ‖cuspQ z‖ < Real.exp (-2 * Real.pi * Y / width)) ↔ Y < z.im
  constructor
  · intro h
    exact (cuspQ_norm_lt_exp_iff Y z).mp h.2
  · intro h
    exact ⟨cuspQ_ne_zero z, (cuspQ_norm_lt_exp_iff Y z).mpr h⟩

/-- The cusp exponential restricted to the actual horodisc. -/
def cuspQHorodisc (Y : ℝ) (z : horodisc Y) : puncturedCuspBall Y :=
  ⟨cuspQ z, (cuspQ_mem_puncturedCuspBall_iff Y z).mpr z.property⟩

@[simp] theorem cuspQHorodisc_coe (Y : ℝ) (z : horodisc Y) :
    (cuspQHorodisc Y z : ℂ) = cuspQ (z : ℍ) := rfl

theorem cuspQHorodisc_eq_iff (Y : ℝ) (z w : horodisc Y) :
    cuspQHorodisc Y z = cuspQHorodisc Y w ↔
      ∃ n : ℤ, triangleGeometricRepresentation (triangleCuspGenerator ^ n) (w : ℍ) =
        (z : ℍ) :=
  Subtype.ext_iff.trans (cuspQ_eq_iff z w)

theorem cuspQHorodisc_holomorphic (Y : ℝ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspQHorodisc Y) := by
  have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : horodisc Y => cuspQ (z : ℍ)) :=
    cuspQ_holomorphic.comp contMDiff_subtype_val
  intro z
  have hi : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun w : horodisc Y => (cuspQHorodisc Y w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (cuspQHorodisc Y) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact hi.mp (h z)

theorem cuspQHorodisc_continuous (Y : ℝ) : Continuous (cuspQHorodisc Y) :=
  (cuspQHorodisc_holomorphic Y).continuous

theorem cuspQHorodisc_isOpenMap (Y : ℝ) : IsOpenMap (cuspQHorodisc Y) := by
  apply (puncturedCuspBall Y).isOpen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
  exact cuspQ_isOpenMap.comp (horodisc Y).isOpen.isOpenEmbedding_subtypeVal.isOpenMap

/-- Every point of the corresponding punctured ball has a lift in the
specified horodisc when its boundary height is nonnegative. -/
theorem cuspQHorodisc_surjective (Y : ℝ) (hY : 0 ≤ Y) :
    Function.Surjective (cuspQHorodisc Y) := by
  intro q
  let q' : PuncturedDisc :=
    ⟨q, q.property.1, q.property.2.trans_le (cuspRadius_le_one Y hY)⟩
  obtain ⟨z, hz⟩ := cuspQMap_surjective q'
  have hzq : cuspQ z = (q : ℂ) := congrArg Subtype.val hz
  have hzY : z ∈ horodisc Y := by
    apply (cuspQ_mem_puncturedCuspBall_iff Y z).mp
    rw [hzq]
    exact q.property
  refine ⟨⟨z, hzY⟩, ?_⟩
  exact Subtype.ext hzq

theorem cuspQHorodisc_isOpenQuotientMap (Y : ℝ) (hY : 0 ≤ Y) :
    IsOpenQuotientMap (cuspQHorodisc Y) :=
  ⟨cuspQHorodisc_surjective Y hY, cuspQHorodisc_continuous Y,
    cuspQHorodisc_isOpenMap Y⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

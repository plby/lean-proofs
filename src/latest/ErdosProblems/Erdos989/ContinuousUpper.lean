/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos989.Core
import ErdosProblems.Erdos228.GaussianWalk
import ErdosProblems.Erdos989.GlobalSelection

/-!
# Continuous jitter model for the upper bound in Erdős problem 989

This file develops the finite-period random model used in the unconditional
fixed-radius upper construction.
-/

namespace Erdos989
namespace ContinuousUpper

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal unitInterval

noncomputable section

open GlobalSelection

/-- A uniformly distributed offset in the closed unit square.  The four
edges form a null set; later they are included among the bad events. -/
abbrev UnitSquare := I × I

instance : MeasureSpace UnitSquare := inferInstance
instance : IsProbabilityMeasure (volume : Measure UnitSquare) := inferInstance

/-- Fold the null upper endpoint of the unit interval back to zero. -/
def foldedUnit (u : I) : ℝ := if (u : ℝ) = 1 then 0 else u

theorem foldedUnit_nonneg (u : I) : 0 ≤ foldedUnit u := by
  simp only [foldedUnit]
  split_ifs
  · norm_num
  · exact u.2.1

theorem foldedUnit_lt_one (u : I) : foldedUnit u < 1 := by
  simp only [foldedUnit]
  split_ifs with h
  · norm_num
  · exact lt_of_le_of_ne u.2.2 h

theorem measurable_foldedUnit : Measurable foldedUnit := by
  unfold foldedUnit
  exact Measurable.ite (measurable_subtype_coe (measurableSet_singleton 1))
    measurable_const measurable_subtype_coe

theorem foldedUnit_ae_eq_coe :
    (fun u : I ↦ foldedUnit u) =ᵐ[volume] fun u ↦ (u : ℝ) := by
  filter_upwards [(volume : Measure I).ae_ne (1 : I)] with u hu
  simp only [foldedUnit, ite_eq_right_iff]
  intro h
  exact (hu (Subtype.ext h)).elim

/-- The measurable, half-open unit-square offset attached to a continuous
candidate. -/
def continuousOffset (q : UnitSquare) : ℝ × ℝ :=
  (foldedUnit q.1, foldedUnit q.2)

theorem continuousOffset_in_halfOpen :
    OffsetsInHalfOpenUnitSquare continuousOffset := by
  intro q
  exact ⟨foldedUnit_nonneg q.1, foldedUnit_lt_one q.1,
    foldedUnit_nonneg q.2, foldedUnit_lt_one q.2⟩

theorem measurable_continuousOffset : Measurable continuousOffset := by
  exact Measurable.prodMk (measurable_foldedUnit.comp measurable_fst)
    (measurable_foldedUnit.comp measurable_snd)

/-- Cells in one square period. -/
abbrev PeriodCell (L : ℕ) := ZMod L × ZMod L

/-- Reduction of an integer cell modulo the period. -/
def periodClass (L : ℕ) (cell : PlaneCell) : PeriodCell L :=
  ((cell.1 : ZMod L), (cell.2 : ZMod L))

/-- Extend a choice on one period to every integer unit cell. -/
def periodicSelection (L : ℕ) (ω : PeriodCell L → UnitSquare) :
    JitteredSelection UnitSquare := fun cell ↦ ω (periodClass L cell)

/-- The selected point in an integer cell. -/
def periodicPoint (L : ℕ) (ω : PeriodCell L → UnitSquare)
    (cell : PlaneCell) : Plane :=
  selectedPoint (latticeLocation continuousOffset) (periodicSelection L ω) cell

/-- Hoeffding's two-sided estimate for finitely many indicator variables in
an arbitrary finite product of probability spaces.  Unlike the finite-grid
version in `Upper.lean`, this applies to the continuous unit-square model. -/
theorem finiteProduct_indicator_hoeffding_general
    {ι Q : Type*} [Fintype ι] [MeasurableSpace Q]
    (ν : ι → Measure Q) (hν : ∀ i, IsProbabilityMeasure (ν i))
    (active : Finset ι) (hit : ι → Q → Bool)
    (hhit : ∀ i, Measurable (fun q ↦ hit i q))
    (t : ℝ) (ht : 0 ≤ t) :
    let μ : Measure (ι → Q) := Measure.pi ν
    μ.real {ω | t ≤
        |(∑ i ∈ active, if hit i (ω i) then (1 : ℝ) else 0) -
          ∑ i ∈ active,
            ∫ q, (if hit i q then (1 : ℝ) else 0) ∂ν i|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ((active.card : ℝ) / 4))) := by
  let μ : Measure (ι → Q) := Measure.pi ν
  let Y : ι → (ι → Q) → ℝ := fun i ω ↦ if hit i (ω i) then 1 else 0
  let m : ι → ℝ := fun i ↦
    ∫ q, (if hit i q then (1 : ℝ) else 0) ∂ν i
  let Z : ι → (ι → Q) → ℝ := fun i ω ↦ Y i ω - μ[Y i]
  letI (i : ι) : IsProbabilityMeasure (ν i) := hν i
  have hcoord : iIndepFun (fun i ω ↦ ω i) μ := by
    exact iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hYmeas : ∀ i,
      Measurable (fun q : Q ↦ if hit i q then (1 : ℝ) else 0) := by
    intro i
    exact (measurable_of_finite
      (fun b : Bool ↦ if b then (1 : ℝ) else 0)).comp (hhit i)
  have hindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hcoord.comp (fun i q ↦ if hit i q then (1 : ℝ) else 0) hYmeas
  have hindepZ : iIndepFun Z μ := by
    apply hindep.comp (fun i y ↦ y - μ[Y i])
    intro i
    fun_prop
  have hsub : ∀ i ∈ active,
      HasSubgaussianMGF (Z i) (1 / 4 : ℝ≥0) μ := by
    intro i hi
    have hYi : AEMeasurable (Y i) μ := by
      simpa [Y, Function.comp_def] using
        (hYmeas i).comp_aemeasurable
          (measurable_pi_apply i).aemeasurable
    have hb : ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [] with ω
      simp only [Y]
      split_ifs <;> norm_num
    have h := hasSubgaussianMGF_of_mem_Icc
      (μ := μ) (X := Y i) (a := (0 : ℝ)) (b := 1) hYi hb
    convert h using 1 <;> norm_num [Z]
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindepZ
    (c := fun _ ↦ (1 / 4 : ℝ≥0)) hsub
  have htail :=
    Erdos228.GaussianWalk.measureReal_abs_ge_le_of_hasSubgaussianMGF hsum ht
  have hmean (i : ι) : μ[Y i] = m i := by
    let g : Q → ℝ := fun q ↦ if hit i q then 1 else 0
    have heval : AEMeasurable (fun ω : ι → Q ↦ ω i) μ :=
      (measurable_pi_apply i).aemeasurable
    have hg : AEStronglyMeasurable g
        (Measure.map (fun ω : ι → Q ↦ ω i) μ) :=
      (hYmeas i).aestronglyMeasurable
    have hi := integral_map heval hg
    rw [(measurePreserving_eval ν i).map_eq] at hi
    simpa [Y, m, g, Function.comp_def] using hi.symm
  simpa [Z, Y, m, hmean, μ, Finset.sum_sub_distrib,
    div_eq_mul_inv] using htail

end

end ContinuousUpper
end Erdos989

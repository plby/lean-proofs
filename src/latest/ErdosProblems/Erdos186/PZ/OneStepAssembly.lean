/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.BoxDiscretization
import ErdosProblems.Erdos186.CFP.Main
import ErdosProblems.Erdos186.DiscreteJohnMahler
import ErdosProblems.Erdos186.PZ.ConvexDensity
import ErdosProblems.Erdos186.PZ.FinalIteration.TracePersistence
import ErdosProblems.Erdos186.PZ.Intersection
import ErdosProblems.Erdos186.PZ.Reduction

/-!
# Assembly boundary for the Pham--Zakharov one-step theorem

This file records the exact implication which remains between the four deep
source statements and the finite iteration.  It also proves the parts of the
assembly which are independent of those source theorems:

* every supercritical state contains at least two points and its box has
  cardinality strictly less than the fourth power of its population;
* population cardinality is antitone along a concrete trace;
* the excess budget bounds the length of every trace;
* a discrete-John certificate transports the restricted population through
  proper GAP coordinates without changing cardinality or nonaveraging;
* the generic axis-parallel rounding lemmas in `BoxDiscretization` remain
  available after an integral coordinate system has been supplied.

The discrete-John output below uses the checked intrinsic-rank construction
from `DiscreteJohnSection`.  The remaining geometric boundary is split into
two precise full-dimensional estimates: maximal-simplex determinant
cancellation for the finite lattice hull, and the continuous-volume estimate
for the outer GAP of a full-rank certificate.  Lower-rank transport, exact
lattice filtering, and the rank dichotomy are proved here.
-/

namespace Erdos186.PZ

open Finset
open scoped BigOperators
open scoped Pointwise
open scoped ENNReal

noncomputable section

/-- The exact end-to-end composition target.  This is a proposition, not an
assumed theorem and not an inhabitant of the final box bound. -/
def OneStepAssemblyStatement : Prop :=
  CFP.NonemptyHigherDimensionalCorollary5 →
    Reduction.IrreducibleReplacementStatement →
      ConvexDensity.PZLemmaOneStatement →
        FinalIteration.OneStepPackageStatement

namespace OneStepAssembly

open FinalIteration
open FinalIteration.Partial

/-! ## Elementary consequences of a supercritical state -/

/-- A strict supercritical density certificate forces at least two points. -/
theorem State.two_le_points_card {ζ : ℝ} (current : State ζ) :
    2 ≤ current.points.card := by
  have hboxNat : 1 ≤ current.box.carrier.card :=
    (Nat.succ_le_iff.mpr current.points_nonempty.card_pos).trans
      (Finset.card_le_card current.points_subset_box)
  have hlogBox : 0 ≤ Real.log (current.box.carrier.card : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hboxNat
  have htotalPos :
      0 < boxExponent current.dimension + ζ + current.excess := by
    have hbox := boxExponent_pos current.dimension_pos
    linarith [current.zeta_pos, current.excess_nonneg]
  have hlogPoints : 0 < Real.log (current.points.card : ℝ) := by
    exact (mul_nonneg htotalPos.le hlogBox).trans_lt
      current.density_certificate
  have hone : (1 : ℝ) < (current.points.card : ℝ) :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogPoints
  exact_mod_cast hone

/-- Consequently the containing integer box also has at least two points. -/
theorem State.two_le_box_card {ζ : ℝ} (current : State ζ) :
    2 ≤ current.box.carrier.card :=
  (State.two_le_points_card current).trans
    (Finset.card_le_card current.points_subset_box)

/-- The fixed exponent `4` is an admissible CFP box exponent at every
positive-dimensional supercritical state. -/
theorem State.box_card_lt_points_card_rpow_four {ζ : ℝ}
    (current : State ζ) :
    (current.box.carrier.card : ℝ) <
      (current.points.card : ℝ) ^ (4 : ℝ) := by
  have hboxPos : 0 < (current.box.carrier.card : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (State.two_le_box_card current))
  have hpointsPos : 0 < (current.points.card : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (State.two_le_points_card current))
  have hlogBox : 0 ≤ Real.log (current.box.carrier.card : ℝ) := by
    exact Real.log_nonneg (by
      exact_mod_cast ((by omega : 1 ≤ 2).trans
        (State.two_le_box_card current)))
  have hquarter :
      (1 / 4 : ℝ) <
        boxExponent current.dimension + ζ + current.excess := by
    have hbox := one_div_four_le_boxExponent current.dimension_pos
    linarith [current.zeta_pos, current.excess_nonneg]
  have hquarterLog :
      (1 / 4 : ℝ) * Real.log (current.box.carrier.card : ℝ) <
        Real.log (current.points.card : ℝ) := by
    calc
      (1 / 4 : ℝ) * Real.log (current.box.carrier.card : ℝ) ≤
          (boxExponent current.dimension + ζ + current.excess) *
            Real.log (current.box.carrier.card : ℝ) :=
        mul_le_mul_of_nonneg_right hquarter.le hlogBox
      _ < Real.log (current.points.card : ℝ) :=
        current.density_certificate
  apply (Real.lt_rpow_iff_log_lt hboxPos hpointsPos).2
  nlinarith

/-- Weak form used directly by the eligibility field of the bounded CFP
context. -/
theorem State.box_card_le_points_card_rpow_four {ζ : ℝ}
    (current : State ζ) :
    (current.box.carrier.card : ℝ) ≤
      (current.points.card : ℝ) ^ (4 : ℝ) :=
  (State.box_card_lt_points_card_rpow_four current).le

/-! ## Trace bookkeeping available before the analytic persistence proof -/

/-- The baseline stopping threshold `2` persists along every trace without
any multiplicative retention argument: it is already forced by the strict
density certificate carried by the last concrete state.  Larger analytic
thresholds still require the source's global persistence calculation. -/
theorem Trace.two_le_last_points_card
    {K : ℕ} {ζ changeGain sameGain rho : ℝ}
    {length : ℕ} {first last : State ζ}
    (_trace : Trace (K := K) (ζ := ζ) (changeGain := changeGain)
      (sameGain := sameGain) (rho := rho) length first last) :
    2 ≤ last.points.card :=
  State.two_le_points_card last

/-- The excess certificate gives the universal numerical length budget for
any concrete trace. -/
theorem Trace.length_mul_uniformGain_le_one_sub_excess
    {K : ℕ} {ζ changeGain sameGain rho : ℝ}
    {length : ℕ} {first last : State ζ}
    (trace : Trace (K := K) (ζ := ζ) (changeGain := changeGain)
      (sameGain := sameGain) (rho := rho) length first last) :
    (length : ℝ) *
        DensityIteration.Iteration.uniformGain changeGain sameGain ≤
      1 - first.excess := by
  have hlower := trace.excess_lower_bound
  have hupper := last.excess_le_one
  linarith

/-! ## The terminal reduction output as a concrete next-state shell -/

/-- The public iteration box viewed as the box type used by the CFP
reduction.  The two records have the same endpoint data but intentionally
live in separate namespaces. -/
def toCFPBox {d : ℕ} (B : IntegerBox d) : CFP.IntegerBox d where
  lower := B.lower
  upper := B.upper

@[simp]
theorem carrier_toCFPBox {d : ℕ} (B : IntegerBox d) :
    (toCFPBox B).carrier = B.carrier := by
  rfl

/-- Coordinate replacement and passage to the selected core never increase
the original population.  This is the `StepOutput.points_card_le` field for
the raw rank-change branches, before their density certificate is supplied. -/
theorem replacementCore_card_le_input
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context} {ell : ℕ}
    {B : CFP.IntegerBox ell} {A : Finset (LatticePoint ell)}
    {hA : selector.Eligible (Reduction.normalizeSet B A)}
    {epsilon delta gamma : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector B A hA
      epsilon delta gamma K constant) :
    (selector.chosen R.points R.eligible).identifiedCore.card ≤ A.card := by
  have hterminal : R.points.card ≤ A.card := by
    have hreach := Reduction.card_le_of_coordinateReachable R.reachable
    simpa using hreach
  calc
    (selector.chosen R.points R.eligible).identifiedCore.card =
        (selector.chosen R.points R.eligible).core.card :=
      (selector.chosen R.points R.eligible).card_identifiedCore
    _ ≤ R.points.card := Finset.card_le_card
      (selector.chosen R.points R.eligible).witness.core_subset
    _ ≤ A.card := hterminal

/-- The same core-retention inequality used by the post-CFP theorem also
guarantees that the selected core is nonempty. -/
theorem replacementCore_nonempty_of_coreRetention
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context} {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta : ℝ} (hdelta : 0 < delta)
    (hcoreRetention : delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ)) :
    (selector.chosen A hA).identifiedCore.Nonempty := by
  have hApos : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast (selector.eligible_nonempty hA).card_pos
  have hhalfPos : (0 : ℝ) <
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ) :=
    (mul_pos hdelta hApos).trans_le hcoreRetention
  have hhalfNat : 0 <
      ((selector.chosen A hA).identifiedCore.card - 2) / 2 := by
    exact_mod_cast hhalfPos
  exact Finset.card_pos.mp (by omega)

/-- Once the numerical branch argument supplies nonemptiness, positive rank,
and the improved density inequality, the terminal selected core is already
an actual `Partial.State`: its box, containment, and nonaveraging fields are
all provided by the reduction output. -/
noncomputable def replacementCoreState
    {beta eta zeta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context} {ell : ℕ}
    {B : CFP.IntegerBox ell} {A : Finset (LatticePoint ell)}
    {hA : selector.Eligible (Reduction.normalizeSet B A)}
    {epsilon delta gamma : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector B A hA
      epsilon delta gamma K constant)
    (hzeta : 0 < zeta)
    (hrank : 0 < (selector.chosen R.points R.eligible).dimension)
    (hcore : (selector.chosen R.points R.eligible).identifiedCore.Nonempty)
    (excess : ℝ) (hexcess : 0 ≤ excess)
    (hdensity :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + excess) *
          Real.log
            ((gapCoefficientBox
              (selector.chosen R.points R.eligible).progression).carrier.card : ℝ) <
        Real.log
          ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ)) :
    State zeta where
  dimension := (selector.chosen R.points R.eligible).dimension
  dimension_pos := hrank
  zeta_pos := hzeta
  box := gapCoefficientBox
    (selector.chosen R.points R.eligible).progression
  points := (selector.chosen R.points R.eligible).identifiedCore
  points_subset_box :=
    (selector.chosen R.points R.eligible).identifiedCore_subset_coefficientBox
  nonaveraging :=
    (selector.chosen R.points R.eligible).identifiedCore_nonaveraging
      R.nonaveraging
  points_nonempty := hcore
  excess := excess
  excess_nonneg := hexcess
  density_certificate := hdensity

/-- Core retention discharges the two structural hypotheses of
`replacementCoreState`.  Thus the only missing state field in a rank-change
branch is the numerical improved-density inequality itself. -/
theorem exists_replacementCoreState_of_coreRetention
    {beta eta zeta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context} {ell : ℕ}
    {B : CFP.IntegerBox ell} {A : Finset (LatticePoint ell)}
    {hA : selector.Eligible (Reduction.normalizeSet B A)}
    {epsilon delta gamma : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector B A hA
      epsilon delta gamma K constant)
    (hzeta : 0 < zeta) (hdelta : 0 < delta)
    (hcoreRetention : delta * (R.points.card : ℝ) ≤
      ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
        2 : ℕ) : ℝ))
    (excess : ℝ) (hexcess : 0 ≤ excess)
    (hdensity :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + excess) *
          Real.log
            ((gapCoefficientBox
              (selector.chosen R.points R.eligible).progression).carrier.card : ℝ) <
        Real.log
          ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ)) :
    ∃ next : State zeta,
      next.dimension = (selector.chosen R.points R.eligible).dimension ∧
      next.points.card =
        (selector.chosen R.points R.eligible).identifiedCore.card ∧
      next.points.card ≤ A.card := by
  have hrank : 0 < (selector.chosen R.points R.eligible).dimension :=
    Intersection.selectedDimension_pos_of_coreRetention selector hdelta
      hcoreRetention
  have hcore :
      (selector.chosen R.points R.eligible).identifiedCore.Nonempty :=
    replacementCore_nonempty_of_coreRetention hdelta hcoreRetention
  let next := replacementCoreState R hzeta hrank hcore excess hexcess hdensity
  refine ⟨next, rfl, rfl, ?_⟩
  exact replacementCore_card_le_input R

/-- The common logarithmic calculation for both rank-change branches.

`q` is the power of the old population appearing in the terminal GAP-volume
bound: it is zero in the downward branch and
`-(1-epsilon) * (newDimension - oldDimension)` in the upward branch.  The
two displayed numerical hypotheses are exactly the source hierarchy split
into its exponent part and the uniform absorption of the fixed constant and
the retention factor. -/
theorem replacementCore_densityCertificate_of_volumeBound
    {beta eta zeta changeGain : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {constant q slack : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA
      epsilon delta gamma K constant)
    (hconstant : 0 < constant) (hchange : 0 < changeGain)
    (hdelta : 0 < delta)
    (hcoreRetention : delta * (R.points.card : ℝ) ≤
      ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
        2 : ℕ) : ℝ))
    (hvolume :
      ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
        constant * Real.rpow (current.points.card : ℝ) q *
          (current.box.carrier.card : ℝ))
    (hexponent :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            ((boxExponent current.dimension + zeta + current.excess)⁻¹ + q) +
          slack ≤ 1 - epsilon)
    (habsorb :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) * Real.log constant -
            Real.log delta ≤
        slack * Real.log (current.points.card : ℝ)) :
    (boxExponent (selector.chosen R.points R.eligible).dimension +
        zeta + (current.excess + changeGain)) *
        Real.log
          ((gapCoefficientBox
            (selector.chosen R.points R.eligible).progression).carrier.card : ℝ) <
      Real.log
        ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) := by
  let oldExponent := boxExponent current.dimension + zeta + current.excess
  let newExponent :=
    boxExponent (selector.chosen R.points R.eligible).dimension +
      zeta + (current.excess + changeGain)
  have hrank : 0 < (selector.chosen R.points R.eligible).dimension :=
    Intersection.selectedDimension_pos_of_coreRetention selector hdelta
      hcoreRetention
  have holdExponent : 0 < oldExponent := by
    dsimp only [oldExponent]
    have hbox := boxExponent_pos current.dimension_pos
    linarith [current.zeta_pos, current.excess_nonneg]
  have hnewExponent : 0 < newExponent := by
    dsimp only [newExponent]
    have hbox := boxExponent_pos hrank
    linarith [current.zeta_pos, current.excess_nonneg]
  have hmTwo : (2 : ℝ) ≤ (current.points.card : ℝ) := by
    exact_mod_cast State.two_le_points_card current
  have hmOne : (1 : ℝ) < (current.points.card : ℝ) :=
    lt_of_lt_of_le (by norm_num) hmTwo
  have hmPos : (0 : ℝ) < (current.points.card : ℝ) :=
    zero_lt_one.trans hmOne
  have hlogm : 0 < Real.log (current.points.card : ℝ) :=
    Real.log_pos hmOne
  have hbPos : (0 : ℝ) < (current.box.carrier.card : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (State.two_le_box_card current))
  have hvPos : (0 : ℝ) <
      ((selector.chosen R.points R.eligible).progression.volume : ℝ) := by
    exact_mod_cast (show 0 <
        (selector.chosen R.points R.eligible).progression.volume by
      apply Finset.prod_pos
      intro i _hi
      exact (selector.chosen R.points R.eligible).progression.width_pos i)
  have hvolume' :
      ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
        constant * (current.points.card : ℝ) ^ q *
          (current.box.carrier.card : ℝ) := by
    simpa only [Real.rpow_eq_pow] using hvolume
  have hboundPos : 0 <
      constant * (current.points.card : ℝ) ^ q *
        (current.box.carrier.card : ℝ) :=
    mul_pos (mul_pos hconstant (Real.rpow_pos_of_pos hmPos q)) hbPos
  have hlogVolume :
      Real.log
          ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
        Real.log constant + q * Real.log (current.points.card : ℝ) +
          Real.log (current.box.carrier.card : ℝ) := by
    have hlog := Real.log_le_log hvPos hvolume'
    calc
      Real.log
            ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
          Real.log (constant * (current.points.card : ℝ) ^ q *
            (current.box.carrier.card : ℝ)) := hlog
      _ = Real.log (constant *
            (current.points.card : ℝ) ^ q) +
          Real.log (current.box.carrier.card : ℝ) :=
        Real.log_mul
          (mul_pos hconstant (Real.rpow_pos_of_pos hmPos q)).ne' hbPos.ne'
      _ = (Real.log constant +
            Real.log ((current.points.card : ℝ) ^ q)) +
          Real.log (current.box.carrier.card : ℝ) := by
        rw [Real.log_mul hconstant.ne'
          (Real.rpow_pos_of_pos hmPos q).ne']
      _ = Real.log constant + q *
            Real.log (current.points.card : ℝ) +
          Real.log (current.box.carrier.card : ℝ) := by
        rw [Real.log_rpow hmPos]
  have holdDensity :
      oldExponent * Real.log (current.box.carrier.card : ℝ) <
        Real.log (current.points.card : ℝ) := by
    simpa only [oldExponent] using current.density_certificate
  have hscaledOld :
      newExponent * Real.log (current.box.carrier.card : ℝ) <
        (newExponent * oldExponent⁻¹) *
          Real.log (current.points.card : ℝ) := by
    have hscale : 0 < newExponent * oldExponent⁻¹ :=
      mul_pos hnewExponent (inv_pos.mpr holdExponent)
    have hmul := mul_lt_mul_of_pos_left holdDensity hscale
    calc
      newExponent * Real.log (current.box.carrier.card : ℝ) =
          (newExponent * oldExponent⁻¹) *
            (oldExponent * Real.log (current.box.carrier.card : ℝ)) := by
        field_simp
      _ < (newExponent * oldExponent⁻¹) *
          Real.log (current.points.card : ℝ) := hmul
  have hcoefficient :
      newExponent * (oldExponent⁻¹ + q) ≤ 1 - epsilon - slack := by
    dsimp only [newExponent, oldExponent] at hexponent ⊢
    linarith
  have hpopulation :
      delta * (current.points.card : ℝ) ^ (1 - epsilon) <
        ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) := by
    have hterminal' :
        (current.points.card : ℝ) ^ (1 - epsilon) <
          (R.points.card : ℝ) := by
      simpa only [Real.rpow_eq_pow] using R.population_large
    have hterminal := mul_lt_mul_of_pos_left hterminal' hdelta
    have hhalf :
        ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
          2 : ℕ) : ℝ) ≤
          ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) := by
      exact_mod_cast (show
        ((selector.chosen R.points R.eligible).identifiedCore.card - 2) / 2 ≤
          (selector.chosen R.points R.eligible).identifiedCore.card by omega)
    exact hterminal.trans_le (hcoreRetention.trans hhalf)
  have hlogPopulation :
      Real.log delta + (1 - epsilon) *
          Real.log (current.points.card : ℝ) <
        Real.log
          ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) := by
    have hpositive : 0 <
        delta * (current.points.card : ℝ) ^ (1 - epsilon) :=
      mul_pos hdelta (Real.rpow_pos_of_pos hmPos _)
    have hlog := Real.log_lt_log hpositive hpopulation
    calc
      Real.log delta + (1 - epsilon) *
            Real.log (current.points.card : ℝ) =
          Real.log delta + Real.log
            ((current.points.card : ℝ) ^ (1 - epsilon)) := by
        rw [Real.log_rpow hmPos]
      _ = Real.log (delta *
          (current.points.card : ℝ) ^ (1 - epsilon)) := by
        rw [Real.log_mul hdelta.ne'
          (Real.rpow_pos_of_pos hmPos (1 - epsilon)).ne']
      _ < Real.log
          ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) :=
        hlog
  have hmain :
      newExponent *
          Real.log
            ((selector.chosen R.points R.eligible).progression.volume : ℝ) <
        Real.log delta + (1 - epsilon) *
          Real.log (current.points.card : ℝ) := by
    calc
      newExponent *
            Real.log
              ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
          newExponent *
            (Real.log constant + q * Real.log (current.points.card : ℝ) +
              Real.log (current.box.carrier.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogVolume hnewExponent.le
      _ < (newExponent * (oldExponent⁻¹ + q)) *
            Real.log (current.points.card : ℝ) +
          newExponent * Real.log constant := by
        nlinarith [hscaledOld]
      _ ≤ (1 - epsilon - slack) *
            Real.log (current.points.card : ℝ) +
          newExponent * Real.log constant := by
        gcongr
      _ ≤ Real.log delta + (1 - epsilon) *
            Real.log (current.points.card : ℝ) := by
        dsimp only [newExponent] at habsorb ⊢
        linarith
  simpa only [gapCoefficientBox_card, newExponent] using
    hmain.trans hlogPopulation

/-- The source population lower bound from irreducible replacement absorbs a
fixed core fraction into any slightly weaker power. -/
theorem rankChange_powerRetention_of_logBudget
    {beta eta zeta epsilon delta rho : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {gamma : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K constant)
    (hdelta : 0 < delta)
    (hbudget : -Real.log delta ≤
      (rho - epsilon) * Real.log (current.points.card : ℝ)) :
    (current.points.card : ℝ) ^ (1 - rho) ≤
      delta * (R.points.card : ℝ) := by
  have hcurrent : (0 : ℝ) < (current.points.card : ℝ) := by
    exact_mod_cast current.points_nonempty.card_pos
  have hterminal : (0 : ℝ) < (R.points.card : ℝ) := by
    exact_mod_cast (selector.eligible_nonempty R.eligible).card_pos
  have hpopulationLog :
      (1 - epsilon) * Real.log (current.points.card : ℝ) <
        Real.log (R.points.card : ℝ) := by
    have hlog := Real.log_lt_log
      (Real.rpow_pos_of_pos hcurrent _) R.population_large
    rwa [Real.log_rpow hcurrent] at hlog
  apply (Real.log_le_log_iff
    (Real.rpow_pos_of_pos hcurrent _)
    (mul_pos hdelta hterminal)).mp
  rw [Real.log_rpow hcurrent,
    Real.log_mul hdelta.ne' hterminal.ne']
  nlinarith

/-- A uniform population threshold supplies the logarithmic budget in
`rankChange_powerRetention_of_logBudget` for every current state. -/
theorem exists_rankChange_powerRetentionThreshold
    {epsilon delta rho : ℝ} (hdelta : 0 < delta)
    (hepsilonRho : epsilon < rho) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {zeta beta eta : ℝ}
        {context : Reduction.HigherDimensionalContext beta eta}
        {selector : Reduction.BoundedCFPSelector context}
        (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        {gamma : ℝ} {K : ℕ} {constant : ℝ}
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA epsilon delta gamma K
            constant),
        pointThreshold ≤ current.points.card →
        (current.points.card : ℝ) ^ (1 - rho) ≤
          delta * (R.points.card : ℝ) := by
  let gap : ℝ := rho - epsilon
  have hgap : 0 < gap := sub_pos.mpr hepsilonRho
  let burden : ℝ := max (-Real.log delta) 0
  obtain ⟨pointThreshold, hthreshold⟩ :=
    exists_nat_gt (max 2 (Real.exp (burden / gap)))
  refine ⟨pointThreshold, ?_, ?_⟩
  · have htwo : (2 : ℝ) < (pointThreshold : ℝ) :=
      (le_max_left 2 (Real.exp (burden / gap))).trans_lt hthreshold
    exact_mod_cast htwo.le
  intro zeta beta eta context selector current hA gamma K constant R hlarge
  apply rankChange_powerRetention_of_logBudget current R hdelta
  have hcardCast : (pointThreshold : ℝ) ≤
      (current.points.card : ℝ) := by exact_mod_cast hlarge
  have hexpLt : Real.exp (burden / gap) <
      (current.points.card : ℝ) :=
    ((le_max_right 2 (Real.exp (burden / gap))).trans_lt
      hthreshold).trans_le hcardCast
  have hcardPos : (0 : ℝ) < (current.points.card : ℝ) :=
    (Real.exp_pos _).trans hexpLt
  have hlogLarge : burden / gap <
      Real.log (current.points.card : ℝ) :=
    (Real.lt_log_iff_exp_lt hcardPos).2 hexpLt
  have hscaled : burden < gap * Real.log (current.points.card : ℝ) :=
    by simpa [mul_comm] using (div_lt_iff₀ hgap).mp hlogLarge
  have hcost : -Real.log delta ≤ burden := le_max_left _ _
  dsimp only [gap] at hscaled ⊢
  exact hcost.trans hscaled.le

/-- A terminal reduction output of genuinely different selected dimension
already gives a concrete `StepOutput` once the branchwise density inequality
has been established.  The multiplicative fields unused by rank-change
transitions are filled canonically. -/
theorem exists_rankChangeStepOutput_of_densityCertificate
    {beta eta zeta changeGain sameGain rho : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K constant)
    (hchange : 0 < changeGain) (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hpower : (current.points.card : ℝ) ^ (1 - rho) ≤
      delta * (R.points.card : ℝ))
    (hcoreRetention : delta * (R.points.card : ℝ) ≤
      ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
        2 : ℕ) : ℝ))
    (hrankne : (selector.chosen R.points R.eligible).dimension ≠
      current.dimension)
    (hdensity :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
          Real.log
            ((gapCoefficientBox
              (selector.chosen R.points R.eligible).progression).carrier.card : ℝ) <
        Real.log
          ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ)) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain) (rhoChange := rho)
      current) := by
  have hrank : 0 < (selector.chosen R.points R.eligible).dimension :=
    Intersection.selectedDimension_pos_of_coreRetention selector hdelta
      hcoreRetention
  have hcore :
      (selector.chosen R.points R.eligible).identifiedCore.Nonempty :=
    replacementCore_nonempty_of_coreRetention hdelta hcoreRetention
  let next := replacementCoreState R current.zeta_pos hrank hcore
    (current.excess + changeGain)
    (add_nonneg current.excess_nonneg hchange.le) hdensity
  let retention : ℝ := delta *
    ((R.points.card : ℝ) / (current.points.card : ℝ))
  have hcurrentCard : (0 : ℝ) < (current.points.card : ℝ) := by
    exact_mod_cast current.points_nonempty.card_pos
  have hterminalCard : (0 : ℝ) < (R.points.card : ℝ) := by
    exact_mod_cast (selector.eligible_nonempty R.eligible).card_pos
  have hterminalCardLe : (R.points.card : ℝ) ≤
      (current.points.card : ℝ) := by
    have hterminalCardLeNat :=
      Reduction.card_le_of_coordinateReachable R.reachable
    exact_mod_cast (show R.points.card ≤ current.points.card by
      simpa only [Reduction.card_normalizeSet] using hterminalCardLeNat)
  have hratioNonneg : 0 ≤
      (R.points.card : ℝ) / (current.points.card : ℝ) :=
    (div_pos hterminalCard hcurrentCard).le
  have hratioOne :
      (R.points.card : ℝ) / (current.points.card : ℝ) ≤ 1 :=
    (div_le_one hcurrentCard).2 hterminalCardLe
  let step : StepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) current := {
    next := next
    points_card_le := by
      dsimp only [next, replacementCoreState]
      exact replacementCore_card_le_input R
    kind := if current.dimension < next.dimension then
      DensityIteration.StepKind.up else DensityIteration.StepKind.down
    retention := retention
    retention_pos := by
      dsimp only [retention]
      exact mul_pos hdelta (div_pos hterminalCard hcurrentCard)
    retention_le_one := by
      dsimp only [retention]
      calc
        delta * ((R.points.card : ℝ) / (current.points.card : ℝ)) ≤
            1 * ((R.points.card : ℝ) / (current.points.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hdeltaOne hratioNonneg
        _ ≤ 1 := by simpa using hratioOne
    population_retained := by
      dsimp only [retention, next, replacementCoreState]
      calc
        (delta * ((R.points.card : ℝ) / (current.points.card : ℝ))) *
              (current.points.card : ℝ) =
            delta * (R.points.card : ℝ) := by
          rw [mul_assoc, div_mul_cancel₀ _ hcurrentCard.ne']
        _ ≤ ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
              2 : ℕ) : ℝ) := hcoreRetention
        _ ≤ ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) := by
          exact_mod_cast (show
            ((selector.chosen R.points R.eligible).identifiedCore.card - 2) / 2 ≤
              (selector.chosen R.points R.eligible).identifiedCore.card by omega)
    structuralRatio := 1
    structuralRatio_pos := zero_lt_one
    structuralRatio_le_one := le_rfl
    convexScale := 1
    convexScale_pos := zero_lt_one
    convexScale_le_one := le_rfl
    boxConstant := 1
    one_le_boxConstant := le_rfl
    transition := by
      dsimp only [next, replacementCoreState]
      by_cases hup : current.dimension <
          (selector.chosen R.points R.eligible).dimension
      · simp [hup]
      · have hrankle :
            (selector.chosen R.points R.eligible).dimension ≤
              current.dimension := Nat.le_of_not_gt hup
        have hranklt :
            (selector.chosen R.points R.eligible).dimension <
              current.dimension := lt_of_le_of_ne hrankle hrankne
        simp [hup, hranklt] }
  refine ⟨step.withBranchControl ?_ ?_⟩
  · intro _hchange
    dsimp only [step, next, replacementCoreState]
    exact hpower.trans (hcoreRetention.trans (by
      exact_mod_cast (show
        ((selector.chosen R.points R.eligible).identifiedCore.card - 2) / 2 ≤
          (selector.chosen R.points R.eligible).identifiedCore.card by omega)))
  · intro hsame
    dsimp only [step, next, replacementCoreState] at hsame
    by_cases hup : current.dimension <
        (selector.chosen R.points R.eligible).dimension
    · simp [hup] at hsame
    · simp [hup] at hsame

/-- The source hierarchy and terminal volume estimate close the rank-change
`StepOutput`; no density-certificate premise remains. -/
theorem exists_rankChangeStepOutput_of_volumeBound
    {beta eta zeta changeGain sameGain rho : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ}
    {constant q slack : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA
      epsilon delta gamma K constant)
    (hconstant : 0 < constant) (hchange : 0 < changeGain)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hpower : (current.points.card : ℝ) ^ (1 - rho) ≤
      delta * (R.points.card : ℝ))
    (hcoreRetention : delta * (R.points.card : ℝ) ≤
      ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
        2 : ℕ) : ℝ))
    (hrankne : (selector.chosen R.points R.eligible).dimension ≠
      current.dimension)
    (hvolume :
      ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
        constant * Real.rpow (current.points.card : ℝ) q *
          (current.box.carrier.card : ℝ))
    (hexponent :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            ((boxExponent current.dimension + zeta + current.excess)⁻¹ + q) +
          slack ≤ 1 - epsilon)
    (habsorb :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) * Real.log constant -
            Real.log delta ≤
        slack * Real.log (current.points.card : ℝ)) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain) (rhoChange := rho)
      current) := by
  apply exists_rankChangeStepOutput_of_densityCertificate current R
    hchange hdelta hdeltaOne hpower hcoreRetention hrankne
  exact replacementCore_densityCertificate_of_volumeBound current R
    hconstant hchange hdelta hcoreRetention hvolume hexponent habsorb

/-- Upward-rank specialization using the sharp terminal power saving. -/
theorem exists_highRankStepOutput
    {beta eta zeta changeGain sameGain rho : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ}
    {constant slack : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA
      epsilon delta gamma K constant)
    (hconstant : 0 < constant) (hchange : 0 < changeGain)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hpower : (current.points.card : ℝ) ^ (1 - rho) ≤
      delta * (R.points.card : ℝ))
    (hcoreRetention : delta * (R.points.card : ℝ) ≤
      ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
        2 : ℕ) : ℝ))
    (hrank : current.dimension <
      (selector.chosen R.points R.eligible).dimension)
    (hexponent :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            ((boxExponent current.dimension + zeta + current.excess)⁻¹ -
              (1 - epsilon) *
                (((selector.chosen R.points R.eligible).dimension : ℝ) -
                  (current.dimension : ℝ))) +
          slack ≤ 1 - epsilon)
    (habsorb :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) * Real.log constant -
            Real.log delta ≤
        slack * Real.log (current.points.card : ℝ)) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain) (rhoChange := rho)
      current) := by
  let q : ℝ := -(1 - epsilon) *
    (((selector.chosen R.points R.eligible).dimension : ℝ) -
      (current.dimension : ℝ))
  apply exists_rankChangeStepOutput_of_volumeBound
    (q := q) (slack := slack) current R hconstant hchange hdelta hdeltaOne
      hpower hcoreRetention (ne_of_gt hrank)
  · simpa only [q, carrier_toCFPBox] using R.high_rank_bound hrank
  · simpa only [q, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      neg_mul] using hexponent
  · exact habsorb

/-- Downward-rank specialization using the coarse terminal volume bound. -/
theorem exists_lowRankStepOutput
    {beta eta zeta changeGain sameGain rho : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ}
    {constant slack : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA
      epsilon delta gamma K constant)
    (hconstant : 0 < constant) (hchange : 0 < changeGain)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hpower : (current.points.card : ℝ) ^ (1 - rho) ≤
      delta * (R.points.card : ℝ))
    (hcoreRetention : delta * (R.points.card : ℝ) ≤
      ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
        2 : ℕ) : ℝ))
    (hrank : (selector.chosen R.points R.eligible).dimension <
      current.dimension)
    (hexponent :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            (boxExponent current.dimension + zeta + current.excess)⁻¹ +
          slack ≤ 1 - epsilon)
    (habsorb :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) * Real.log constant -
            Real.log delta ≤
        slack * Real.log (current.points.card : ℝ)) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain) (rhoChange := rho)
      current) := by
  apply exists_rankChangeStepOutput_of_volumeBound
    (q := 0) (slack := slack) current R hconstant hchange hdelta hdeltaOne
      hpower hcoreRetention (ne_of_lt hrank)
  · simpa using R.low_rank_bound hrank
  · simpa using hexponent
  · exact habsorb

/-- The two rank-change cases with one common choice of reduction constant,
density increment, retention parameter, and constant-absorption slack.  The
source hierarchy is exposed branchwise only because the high-rank terminal
estimate has a genuine power saving while the low-rank estimate does not. -/
theorem exists_rankChangeStepOutput
    {beta eta zeta changeGain sameGain rho : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ}
    {constant slack : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA
      epsilon delta gamma K constant)
    (hconstant : 0 < constant) (hchange : 0 < changeGain)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hpower : (current.points.card : ℝ) ^ (1 - rho) ≤
      delta * (R.points.card : ℝ))
    (hcoreRetention : delta * (R.points.card : ℝ) ≤
      ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
        2 : ℕ) : ℝ))
    (hrankne : (selector.chosen R.points R.eligible).dimension ≠
      current.dimension)
    (hhighExponent : current.dimension <
        (selector.chosen R.points R.eligible).dimension →
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            ((boxExponent current.dimension + zeta + current.excess)⁻¹ -
              (1 - epsilon) *
                (((selector.chosen R.points R.eligible).dimension : ℝ) -
                  (current.dimension : ℝ))) +
          slack ≤ 1 - epsilon)
    (hlowExponent : (selector.chosen R.points R.eligible).dimension <
        current.dimension →
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            (boxExponent current.dimension + zeta + current.excess)⁻¹ +
          slack ≤ 1 - epsilon)
    (habsorb :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) * Real.log constant -
            Real.log delta ≤
        slack * Real.log (current.points.card : ℝ)) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain) (rhoChange := rho)
      current) := by
  rcases lt_or_gt_of_ne hrankne.symm with hhigh | hlow
  · exact exists_highRankStepOutput current R hconstant hchange hdelta
      hdeltaOne hpower hcoreRetention hhigh (hhighExponent hhigh) habsorb
  · exact exists_lowRankStepOutput current R hconstant hchange hdelta
      hdeltaOne hpower hcoreRetention hlow (hlowExponent hlow) habsorb

/-- A single population threshold absorbs the fixed reduction constant and
the core-retention factor in every rank-change branch.  The threshold is
uniform in the current state and the new positive dimension; the state-level
exponent obstruction supplies the only bounds needed on the old excess and
on the new box exponent. -/
theorem exists_rankChange_constantAbsorptionThreshold
    {zeta changeGain constant delta slack : ℝ}
    (hchange : 0 < changeGain) (hslack : 0 < slack) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ (current : State zeta) (newDimension : ℕ),
        0 < newDimension → pointThreshold ≤ current.points.card →
        (boxExponent newDimension + zeta +
            (current.excess + changeGain)) * Real.log constant -
              Real.log delta ≤
          slack * Real.log (current.points.card : ℝ) := by
  let burden : ℝ :=
    max (2 + zeta + changeGain) 0 * max (Real.log constant) 0 +
      max (-Real.log delta) 0
  have hburdenNonneg : 0 ≤ burden := by
    dsimp only [burden]
    exact add_nonneg
      (mul_nonneg (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)
  obtain ⟨pointThreshold, hthreshold⟩ :=
    exists_nat_gt (max 2 (Real.exp (burden / slack)))
  refine ⟨pointThreshold, ?_, ?_⟩
  · have htwo : (2 : ℝ) < (pointThreshold : ℝ) :=
      (le_max_left 2 (Real.exp (burden / slack))).trans_lt hthreshold
    exact_mod_cast htwo.le
  intro current newDimension hnewDimension hlarge
  have hnewExponentPos :
      0 < boxExponent newDimension + zeta +
        (current.excess + changeGain) := by
    have hbox := boxExponent_pos hnewDimension
    linarith [current.zeta_pos, current.excess_nonneg]
  have hnewExponentLe :
      boxExponent newDimension + zeta +
          (current.excess + changeGain) ≤
        2 + zeta + changeGain := by
    have hbox := boxExponent_lt_one hnewDimension
    have hexcess := current.excess_le_one
    linarith
  have hlogConstant :
      Real.log constant ≤ max (Real.log constant) 0 :=
    le_max_left _ _
  have hmaxLogNonneg : 0 ≤ max (Real.log constant) 0 :=
    le_max_right _ _
  have hfixedCost :
      (boxExponent newDimension + zeta +
          (current.excess + changeGain)) * Real.log constant -
            Real.log delta ≤ burden := by
    have hmul :
        (boxExponent newDimension + zeta +
            (current.excess + changeGain)) * Real.log constant ≤
          max (2 + zeta + changeGain) 0 *
            max (Real.log constant) 0 := by
      calc
        (boxExponent newDimension + zeta +
            (current.excess + changeGain)) * Real.log constant ≤
            (boxExponent newDimension + zeta +
              (current.excess + changeGain)) *
                max (Real.log constant) 0 :=
          mul_le_mul_of_nonneg_left hlogConstant hnewExponentPos.le
        _ ≤ (2 + zeta + changeGain) *
              max (Real.log constant) 0 :=
          mul_le_mul_of_nonneg_right hnewExponentLe hmaxLogNonneg
        _ ≤ max (2 + zeta + changeGain) 0 *
              max (Real.log constant) 0 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hmaxLogNonneg
    have hdeltaCost : -Real.log delta ≤ max (-Real.log delta) 0 :=
      le_max_left _ _
    dsimp only [burden]
    linarith
  have hcardCast : (pointThreshold : ℝ) ≤
      (current.points.card : ℝ) := by
    exact_mod_cast hlarge
  have hexpLt : Real.exp (burden / slack) <
      (current.points.card : ℝ) := by
    exact ((le_max_right 2 (Real.exp (burden / slack))).trans_lt
      hthreshold).trans_le hcardCast
  have hcardPos : (0 : ℝ) < (current.points.card : ℝ) :=
    (Real.exp_pos _).trans hexpLt
  have hlogLarge : burden / slack <
      Real.log (current.points.card : ℝ) :=
    (Real.lt_log_iff_exp_lt hcardPos).2 hexpLt
  have hburdenAbsorbed : burden <
      slack * Real.log (current.points.card : ℝ) := by
    have := (div_lt_iff₀ hslack).mp hlogLarge
    nlinarith
  exact hfixedCost.trans hburdenAbsorbed.le

/-- After one uniform threshold choice, the terminal reduction and the two
branch exponent inequalities construct every rank-change step.  In
particular, constant absorption is no longer a per-state premise. -/
theorem exists_rankChangeStepOutput_threshold
    {beta eta zeta changeGain sameGain rho : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {epsilon delta gamma : ℝ} {K : ℕ}
    {constant slack : ℝ}
    (hconstant : 0 < constant) (hchange : 0 < changeGain)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hslack : 0 < slack) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA
          epsilon delta gamma K constant),
        pointThreshold ≤ current.points.card →
        (current.points.card : ℝ) ^ (1 - rho) ≤
          delta * (R.points.card : ℝ) →
        delta * (R.points.card : ℝ) ≤
          ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
            2 : ℕ) : ℝ) →
        (selector.chosen R.points R.eligible).dimension ≠
          current.dimension →
        (current.dimension <
            (selector.chosen R.points R.eligible).dimension →
          (boxExponent (selector.chosen R.points R.eligible).dimension +
              zeta + (current.excess + changeGain)) *
                ((boxExponent current.dimension + zeta + current.excess)⁻¹ -
                  (1 - epsilon) *
                    (((selector.chosen R.points R.eligible).dimension : ℝ) -
                      (current.dimension : ℝ))) +
              slack ≤ 1 - epsilon) →
        ((selector.chosen R.points R.eligible).dimension <
            current.dimension →
          (boxExponent (selector.chosen R.points R.eligible).dimension +
              zeta + (current.excess + changeGain)) *
                (boxExponent current.dimension + zeta + current.excess)⁻¹ +
              slack ≤ 1 - epsilon) →
        Nonempty (BranchControlledStepOutput (K := K)
          (changeGain := changeGain) (sameGain := sameGain) (rhoChange := rho)
          current) := by
  obtain ⟨pointThreshold, hthresholdTwo, habsorb⟩ :=
    exists_rankChange_constantAbsorptionThreshold
      (zeta := zeta) (constant := constant) (delta := delta)
      hchange hslack
  refine ⟨pointThreshold, hthresholdTwo, ?_⟩
  intro current hA R hlarge hpower hcoreRetention hrankne
    hhighExponent hlowExponent
  have hnewDimension :
      0 < (selector.chosen R.points R.eligible).dimension :=
    Intersection.selectedDimension_pos_of_coreRetention selector hdelta
      hcoreRetention
  apply exists_rankChangeStepOutput current R hconstant hchange hdelta
    hdeltaOne hpower hcoreRetention hrankne hhighExponent hlowExponent
  exact habsorb current
    (selector.chosen R.points R.eligible).dimension hnewDimension hlarge

/-- Observation 15 in the exact exponent form consumed by the upward-rank
constructor.  A single dimension ceiling and scalar budget work for every
state because the state's excess simply enlarges the perturbation parameter
from `zeta` to `zeta + excess`. -/
theorem highRank_exponent_of_uniform_budget
    {zeta epsilon changeGain slack : ℝ} {newDimension dimensionCeiling : ℕ}
    (current : State zeta)
    (hrank : current.dimension < newDimension)
    (hnewDimensionLe : newDimension ≤ dimensionCeiling)
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hepsilonSmall :
      epsilon ≤ zeta / (4 * (dimensionCeiling : ℝ)))
    (hchange : 0 ≤ changeGain)
    (hbudget : 4 * changeGain + slack + epsilon ≤ zeta / 2) :
    (boxExponent newDimension + zeta +
        (current.excess + changeGain)) *
          ((boxExponent current.dimension + zeta + current.excess)⁻¹ -
            (1 - epsilon) *
              ((newDimension : ℝ) - (current.dimension : ℝ))) +
        slack ≤ 1 - epsilon := by
  let perturbation := zeta + current.excess
  let oldExponent := boxExponent current.dimension + perturbation
  let newBase := boxExponent newDimension + perturbation
  let bracket := oldExponent⁻¹ -
    (1 - epsilon) * ((newDimension : ℝ) - (current.dimension : ℝ))
  have hperturbationLower : zeta ≤ perturbation := by
    dsimp only [perturbation]
    linarith [current.excess_nonneg]
  have hperturbationOne : perturbation ≤ 1 := by
    have htotal := current.totalExponent_lt_one
    have hbox := boxExponent_pos current.dimension_pos
    dsimp only [perturbation]
    linarith
  have hobservation : newBase * bracket ≤ 1 - zeta / 2 := by
    have h := observation15_boxExponent_uniform
      current.dimension_pos hrank hnewDimensionLe current.zeta_pos
      hperturbationLower hperturbationOne hepsilon hepsilonSmall
    dsimp only [newBase, bracket, oldExponent, perturbation]
    simpa only [one_div, Nat.cast_sub hrank.le] using h
  have holdExponentPos : 0 < oldExponent := by
    dsimp only [oldExponent, perturbation]
    have hbox := boxExponent_pos current.dimension_pos
    linarith [current.zeta_pos, current.excess_nonneg]
  have holdExponentQuarter : (1 / 4 : ℝ) ≤ oldExponent := by
    dsimp only [oldExponent, perturbation]
    have hbox := one_div_four_le_boxExponent current.dimension_pos
    linarith [current.zeta_pos, current.excess_nonneg]
  have holdInverseLe : oldExponent⁻¹ ≤ 4 := by
    have honeDiv : 1 / oldExponent ≤ 4 :=
      (div_le_iff₀ holdExponentPos).2 (by nlinarith)
    simpa only [one_div] using honeDiv
  have hdimensionGap : 0 ≤
      (newDimension : ℝ) - (current.dimension : ℝ) := by
    apply sub_nonneg.mpr
    exact_mod_cast hrank.le
  have hsavingNonneg : 0 ≤
      (1 - epsilon) *
        ((newDimension : ℝ) - (current.dimension : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hepsilonOne) hdimensionGap
  have hbracketLe : bracket ≤ 4 := by
    dsimp only [bracket]
    linarith
  have hchangeBracket : changeGain * bracket ≤ 4 * changeGain := by
    nlinarith
  calc
    (boxExponent newDimension + zeta +
          (current.excess + changeGain)) *
            ((boxExponent current.dimension + zeta + current.excess)⁻¹ -
              (1 - epsilon) *
                ((newDimension : ℝ) - (current.dimension : ℝ))) +
          slack =
        newBase * bracket + changeGain * bracket + slack := by
      dsimp only [newBase, bracket, oldExponent, perturbation]
      ring
    _ ≤ (1 - zeta / 2) + 4 * changeGain + slack := by
      linarith
    _ ≤ 1 - epsilon := by
      linarith

/-- A downward rank change gains exactly the gap between the two box
exponents.  Spending at most that gap on `changeGain + epsilon + slack`
gives the low-rank exponent inequality uniformly in the state's excess. -/
theorem lowRank_exponent_of_gap_budget
    {zeta epsilon changeGain slack : ℝ} {newDimension : ℕ}
    (current : State zeta)
    (hlossNonneg : 0 ≤ epsilon + slack)
    (hbudget : changeGain + epsilon + slack ≤
      boxExponent current.dimension - boxExponent newDimension) :
    (boxExponent newDimension + zeta +
        (current.excess + changeGain)) *
          (boxExponent current.dimension + zeta + current.excess)⁻¹ +
        slack ≤ 1 - epsilon := by
  let oldExponent :=
    boxExponent current.dimension + zeta + current.excess
  let newExponent :=
    boxExponent newDimension + zeta + (current.excess + changeGain)
  have holdExponentPos : 0 < oldExponent := by
    dsimp only [oldExponent]
    have hbox := boxExponent_pos current.dimension_pos
    linarith [current.zeta_pos, current.excess_nonneg]
  have holdExponentLe : oldExponent ≤ 1 := by
    exact current.totalExponent_lt_one.le
  have hlossScaled :
      (epsilon + slack) * oldExponent ≤ epsilon + slack := by
    nlinarith
  have hnewExponentBudget :
      newExponent ≤ (1 - epsilon - slack) * oldExponent := by
    dsimp only [newExponent, oldExponent] at ⊢
    nlinarith
  have hdiv : newExponent / oldExponent ≤
      1 - epsilon - slack :=
    (div_le_iff₀ holdExponentPos).2 hnewExponentBudget
  dsimp only [newExponent, oldExponent] at hdiv ⊢
  rw [div_eq_mul_inv] at hdiv
  linarith

/-- Below a fixed finite dimension ceiling, all strict downward changes have
a common positive box-exponent gap. -/
theorem exists_uniform_boxExponent_gap (dimensionCeiling : ℕ) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ {lower upper : ℕ}, 0 < lower → lower < upper →
        upper ≤ dimensionCeiling →
        gap ≤ boxExponent upper - boxExponent lower := by
  induction dimensionCeiling with
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro lower upper _hlower _hrank hupper
      omega
  | succ dimensionCeiling ih =>
      by_cases hceilingZero : dimensionCeiling = 0
      · subst dimensionCeiling
        refine ⟨1, zero_lt_one, ?_⟩
        intro lower upper _hlower _hrank hupper
        omega
      · have hceilingPos : 0 < dimensionCeiling :=
          Nat.pos_of_ne_zero hceilingZero
        obtain ⟨oldGap, holdGapPos, holdGap⟩ := ih
        let edgeGap :=
          boxExponent (dimensionCeiling + 1) -
            boxExponent dimensionCeiling
        have hedgeGapPos : 0 < edgeGap := by
          dsimp only [edgeGap]
          exact boxExponent_downward_gap_pos hceilingPos (by omega)
        refine ⟨min oldGap edgeGap, lt_min holdGapPos hedgeGapPos, ?_⟩
        intro lower upper hlower hrank hupper
        by_cases hupperOld : upper ≤ dimensionCeiling
        · exact (min_le_left _ _).trans
            (holdGap hlower hrank hupperOld)
        · have hupperTop : upper = dimensionCeiling + 1 := by omega
          have hlowerCeiling : lower ≤ dimensionCeiling := by omega
          have hexponentMono :
              boxExponent lower ≤ boxExponent dimensionCeiling :=
            boxExponent_mono hlower hlowerCeiling
          calc
            min oldGap edgeGap ≤ edgeGap := min_le_right _ _
            _ ≤ boxExponent upper - boxExponent lower := by
              dsimp only [edgeGap]
              rw [hupperTop]
              linarith

/-- One explicit uniform scalar hierarchy for both rank-change branches.
The same positive number is used for the reduction population loss,
rank-change gain, and absorption slack; taking the minimum of the
Observation-15 budget, one quarter of the finite downward gap, and `1/6`
meets every required strict/source inequality. -/
theorem exists_rankChange_scalarHierarchy
    {zeta : ℝ} (hzeta : 0 < zeta)
    (dimensionCeiling : ℕ) (hceiling : 0 < dimensionCeiling) :
    ∃ epsilon changeGain slack : ℝ,
      0 < epsilon ∧ epsilon < (1 / 3 : ℝ) ∧ epsilon ≤ 1 ∧
      0 < changeGain ∧ 0 < slack ∧
      epsilon ≤ zeta / (4 * (dimensionCeiling : ℝ)) ∧
      4 * changeGain + slack + epsilon ≤ zeta / 2 ∧
      ∀ {lower upper : ℕ}, 0 < lower → lower < upper →
        upper ≤ dimensionCeiling →
        changeGain + epsilon + slack ≤
          boxExponent upper - boxExponent lower := by
  obtain ⟨gap, hgap, hgapUniform⟩ :=
    exists_uniform_boxExponent_gap dimensionCeiling
  let observationBudget : ℝ :=
    zeta / (16 * (dimensionCeiling : ℝ))
  let gapBudget : ℝ := gap / 4
  let gain : ℝ := min (min observationBudget gapBudget) (1 / 6)
  have hceilingReal : (0 : ℝ) < (dimensionCeiling : ℝ) := by
    exact_mod_cast hceiling
  have hobservationBudget : 0 < observationBudget := by
    dsimp only [observationBudget]
    positivity
  have hgapBudget : 0 < gapBudget := by
    dsimp only [gapBudget]
    positivity
  have hgain : 0 < gain := by
    dsimp only [gain]
    exact lt_min (lt_min hobservationBudget hgapBudget) (by norm_num)
  refine ⟨gain, gain, gain, hgain, ?_, ?_, hgain, hgain, ?_, ?_, ?_⟩
  · have hgainSixth : gain ≤ (1 / 6 : ℝ) := by
      exact min_le_right _ _
    norm_num at hgainSixth ⊢
    linarith
  · exact (min_le_right _ _).trans (by norm_num)
  · have hgainObservation : gain ≤ observationBudget :=
      (min_le_left _ _).trans (min_le_left _ _)
    dsimp only [observationBudget] at hgainObservation
    apply hgainObservation.trans
    gcongr
    nlinarith [hceilingReal]
  · have hgainObservation : gain ≤ observationBudget :=
      (min_le_left _ _).trans (min_le_left _ _)
    dsimp only [observationBudget] at hgainObservation
    have hscaled : 6 * gain ≤
        6 * (zeta / (16 * (dimensionCeiling : ℝ))) :=
      mul_le_mul_of_nonneg_left hgainObservation (by norm_num)
    have hceilingOne : (1 : ℝ) ≤ (dimensionCeiling : ℝ) := by
      exact_mod_cast hceiling
    have hfraction :
        6 * (zeta / (16 * (dimensionCeiling : ℝ))) ≤ zeta / 2 := by
      rw [← mul_div_assoc]
      rw [div_le_iff₀ (by positivity :
        (0 : ℝ) < 16 * (dimensionCeiling : ℝ))]
      nlinarith
    norm_num at hscaled ⊢
    linarith
  · intro lower upper hlower hrank hupper
    have hgainGap : gain ≤ gapBudget :=
      (min_le_left _ _).trans (min_le_right _ _)
    have hthree : gain + gain + gain ≤ gap := by
      dsimp only [gapBudget] at hgainGap
      linarith
    exact hthree.trans (hgapUniform hlower hrank hupper)

/-! ## Coordinate realizations and finite restrictions -/

/-- View the public integer-box type in the standalone discretization
namespace.  The two structures have literally the same endpoints. -/
def toDiscretizationBox {d : ℕ} (B : IntegerBox d) :
    BoxDiscretization.IntegerBox d where
  lower := B.lower
  upper := B.upper

/-- Return a discretization box to the public integer-box type. -/
def ofDiscretizationBox {d : ℕ} (B : BoxDiscretization.IntegerBox d) :
    IntegerBox d where
  lower := B.lower
  upper := B.upper

@[simp]
theorem carrier_toDiscretizationBox {d : ℕ} (B : IntegerBox d) :
    (toDiscretizationBox B).carrier = B.carrier := by
  rfl

@[simp]
theorem carrier_ofDiscretizationBox {d : ℕ}
    (B : BoxDiscretization.IntegerBox d) :
    (ofDiscretizationBox B).carrier = B.carrier := by
  rfl

/-- The Euclidean realization of a public integer box. -/
def boxRealization {d : ℕ} (B : IntegerBox d) :
    Set (ConvexDensity.EuclideanPoint d) :=
  (toDiscretizationBox B).realization

/-- The public integer box obtained by outward rounding a real box. -/
def roundedIntegerBox {d : ℕ} (lower upper : Fin d → ℝ) :
    IntegerBox d :=
  ofDiscretizationBox (BoxDiscretization.roundedBox lower upper)

/-- Restrict a lattice population to a Euclidean region. -/
def latticeRestriction {d : ℕ} (A : Finset (BoxPoint d))
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    Finset (BoxPoint d) := by
  classical
  exact A.filter fun z ↦ BoxDiscretization.latticeEmbed z ∈ Omega

@[simp]
theorem mem_latticeRestriction {d : ℕ} {A : Finset (BoxPoint d)}
    {Omega : Set (ConvexDensity.EuclideanPoint d)} {z : BoxPoint d} :
    z ∈ latticeRestriction A Omega ↔
      z ∈ A ∧ BoxDiscretization.latticeEmbed z ∈ Omega := by
  simp [latticeRestriction]

theorem latticeRestriction_subset {d : ℕ} (A : Finset (BoxPoint d))
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    latticeRestriction A Omega ⊆ A := by
  intro z hz
  exact (mem_latticeRestriction.mp hz).1

/-- Translation is monotone on finite lattice sets. -/
theorem translate_mono {d : ℕ} {A C : Finset (BoxPoint d)}
    (v : BoxPoint d) (hAC : A ⊆ C) :
    PZ.translate v A ⊆ PZ.translate v C := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨x, hAC hx, rfl⟩

/-- Nonaveraging is inherited by a convex-region restriction. -/
theorem latticeRestriction_nonaveraging {d : ℕ}
    {A : Finset (BoxPoint d)} (hA : IsBoxNonaveraging A)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    IsBoxNonaveraging (latticeRestriction A Omega) :=
  isBoxNonaveraging_mono hA (latticeRestriction_subset A Omega)

@[simp]
theorem latticeEmbed_eq_latticeEuclidean {d : ℕ} (z : BoxPoint d) :
    BoxDiscretization.latticeEmbed z =
      Intersection.latticeEuclidean z := by
  rfl

/-- Restriction commutes with the injective lattice-to-Euclidean embedding.
This identifies the point count returned by `ConvexDensityOutput` with the
cardinality of the literal lattice subset used by the next state. -/
theorem realImage_latticeRestriction {d : ℕ}
    (A : Finset (BoxPoint d))
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    Intersection.realImage (latticeRestriction A Omega) =
      ConvexDensity.pointsIn (Intersection.realImage A) Omega := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hz' := mem_latticeRestriction.mp hz
    rw [ConvexDensity.mem_pointsIn]
    exact ⟨Intersection.mem_realImage_of_mem hz'.1, by
      simpa using hz'.2⟩
  · intro hx
    rw [ConvexDensity.mem_pointsIn] at hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx.1
    apply Finset.mem_image.mpr
    exact ⟨z, mem_latticeRestriction.mpr ⟨hz, by simpa using hx.2⟩,
      rfl⟩

@[simp]
theorem card_latticeRestriction {d : ℕ} (A : Finset (BoxPoint d))
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    (latticeRestriction A Omega).card =
      (ConvexDensity.pointsIn (Intersection.realImage A) Omega).card := by
  calc
    (latticeRestriction A Omega).card =
        (Intersection.realImage (latticeRestriction A Omega)).card := by
      symm
      exact Intersection.card_realImage _
    _ = (ConvexDensity.pointsIn (Intersection.realImage A) Omega).card := by
      rw [realImage_latticeRestriction]

/-! ## Exact rank-sensitive discrete-John boundary -/

/-- All lattice points of a convex restriction which lie in the current
finite box. -/
def boxLatticePointsIn {d : ℕ} (B : IntegerBox d)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    Finset (BoxPoint d) :=
  latticeRestriction B.carrier Omega

/-- Center all lattice points in the convex restriction at a chosen lattice
point.  PZ Lemma 7 is applied to this translated finite set. -/
def centeredBoxLatticePointsIn {d : ℕ} (B : IntegerBox d)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) (center : BoxPoint d) :
    Finset (BoxPoint d) :=
  PZ.translate (-center) (boxLatticePointsIn B Omega)

/-- Rank-sensitive discrete-John data before the continuous-volume estimate.

The existing `DiscreteJohn.Certificate` contains the independent integral
directions and the inner/outer lattice inclusions.  The rank can be smaller
than the ambient dimension; that case must be routed to a dimension-drop
transition rather than to the full-dimensional volume argument. -/
structure CenteredDiscreteJohnCertificate {d : ℕ} (B : IntegerBox d)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) where
  center : BoxPoint d
  center_mem : center ∈ boxLatticePointsIn B Omega
  /-- The symmetric-body lattice set to which discrete John is actually
  applied.  For the source proof this is supplied by a symmetrization of
  `Omega`; it need only contain the centered population. -/
  johnPoints : Finset (BoxPoint d)
  centered_subset_johnPoints :
    centeredBoxLatticePointsIn B Omega center ⊆ johnPoints
  rank : ℕ
  rank_le : rank ≤ d
  factor : ℕ
  certificate :
    DiscreteJohn.Certificate johnPoints rank factor

namespace CenteredDiscreteJohnCertificate

variable {d : ℕ} {B : IntegerBox d}
  {Omega : Set (ConvexDensity.EuclideanPoint d)}

/-- A restricted population, centered at the same lattice point, lies in the
outer GAP of the certificate. -/
theorem centeredRestriction_subset_outer
    (J : CenteredDiscreteJohnCertificate B Omega)
    {A : Finset (BoxPoint d)} (hAB : A ⊆ B.carrier) :
    PZ.translate (-J.center) (latticeRestriction A Omega) ⊆
      J.certificate.outer.carrier := by
  have hrestrict :
      latticeRestriction A Omega ⊆ boxLatticePointsIn B Omega := by
    intro z hz
    have hz' := mem_latticeRestriction.mp hz
    exact mem_latticeRestriction.mpr ⟨hAB hz'.1, hz'.2⟩
  exact ((translate_mono (-J.center) hrestrict).trans
      J.centered_subset_johnPoints).trans
    J.certificate.subset_outer_carrier

/-- The finite certificate alone gives a coarse bound by the number of
lattice points in the symmetric body.  Converting this to a bound by the
current box is the elementary cardinal part of the adapter below. -/
theorem outer_volume_le_factor_mul_johnPoints
    (J : CenteredDiscreteJohnCertificate B Omega) :
    J.certificate.outer.volume ≤
      (2 * J.factor + 1) ^ J.rank * J.johnPoints.card := by
  calc
    J.certificate.outer.volume =
        J.certificate.outer.carrier.card := by
      exact (GAP.card_carrier_eq_volume _
        J.certificate.outer_proper).symm
    _ ≤ (2 * J.factor + 1) ^ J.rank * J.johnPoints.card :=
      J.certificate.card_outer_le

/-- Proper GAP coordinates turn either rank branch into an actual standard
integer box.  Cardinality and nonaveraging are preserved exactly. -/
theorem exists_coordinateBox
    (J : CenteredDiscreteJohnCertificate B Omega)
    {A : Finset (BoxPoint d)} (hAB : A ⊆ B.carrier)
    (hNA : IsBoxNonaveraging A) :
    ∃ (B' : IntegerBox J.rank) (A' : Finset (BoxPoint J.rank)),
      A' ⊆ B'.carrier ∧
        IsBoxNonaveraging A' ∧
        A'.card = (latticeRestriction A Omega).card ∧
        B'.carrier.card = J.certificate.outer.volume := by
  let P := J.certificate.outer
  have hP : P.Proper := J.certificate.outer_proper
  let centered := PZ.translate (-J.center) (latticeRestriction A Omega)
  have hcentered : centered ⊆ P.carrier :=
    J.centeredRestriction_subset_outer hAB
  let A' : Finset (BoxPoint J.rank) :=
    Reduction.coordinateImage P hP centered hcentered
  refine ⟨gapCoefficientBox P, A', ?_, ?_, ?_, ?_⟩
  · exact Reduction.coordinateImage_subset_coefficientBox
      P hP centered hcentered
  · exact Reduction.coordinateImage_nonaveraging P hP hcentered
      (isBoxNonaveraging_translate (-J.center)
        (latticeRestriction_nonaveraging hNA Omega))
  · calc
      A'.card = centered.card :=
        Reduction.card_coordinateImage P hP centered hcentered
      _ = (latticeRestriction A Omega).card := PZ.card_translate _ _
  · exact gapCoefficientBox_card P

end CenteredDiscreteJohnCertificate

/-- The output of the centering and symmetrization step which precedes
discrete John in the source proof.  The symmetric body may contain more
lattice points than the centered restriction (as happens for a difference
body), but its lattice population is uniformly controlled by the current
box. -/
def coordinateDifferenceBody {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) : Set (Fin d → ℝ) :=
  {v | ∃ x ∈ Omega, ∃ y ∈ Omega, v = fun i ↦ x i - y i}

/-- Forget the `L²` norm wrapper on Euclidean coordinate space. -/
def coordinateSet {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) : Set (Fin d → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)) '' Omega

/-- Coordinate unwrapping is equivalently the preimage under the inverse
`PiLp` wrapper. -/
theorem coordinateSet_eq_preimage {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    coordinateSet Omega = (WithLp.toLp 2) ⁻¹' Omega := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [coordinateSet] using hy
  · intro hx
    refine ⟨WithLp.toLp 2 x, hx, ?_⟩
    rfl

/-- Forgetting the `L²` wrapper preserves Euclidean volume. -/
theorem volume_coordinateSet {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d))
    (hOmega : MeasureTheory.NullMeasurableSet Omega
      (MeasureTheory.volume : MeasureTheory.Measure
        (ConvexDensity.EuclideanPoint d))) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (coordinateSet Omega) =
      (MeasureTheory.volume : MeasureTheory.Measure
        (ConvexDensity.EuclideanPoint d)) Omega := by
  rw [coordinateSet_eq_preimage]
  exact (PiLp.volume_preserving_toLp (Fin d)).measure_preimage hOmega

/-- The explicit coordinate difference body agrees with pointwise set
subtraction after forgetting the norm wrapper. -/
theorem coordinateDifferenceBody_eq_sub {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    coordinateDifferenceBody Omega = coordinateSet Omega - coordinateSet Omega := by
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [Set.mem_sub]
    refine ⟨(WithLp.linearEquiv 2 ℝ (Fin d → ℝ)) x,
      ⟨x, hx, rfl⟩,
      (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)) y, ⟨y, hy, rfl⟩, ?_⟩
    rfl
  · rw [Set.mem_sub]
    rintro ⟨x, ⟨x', hx', rfl⟩, y, ⟨y', hy', rfl⟩, rfl⟩
    exact ⟨x', hx', y', hy', rfl⟩

/-- Euclidean-space spelling of the closed difference body. -/
def euclideanClosedDifferenceBody {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    Set (ConvexDensity.EuclideanPoint d) :=
  closure (Omega - Omega)

/-- Coordinate unwrapping commutes with taking the raw difference body. -/
theorem coordinateDifferenceBody_eq_coordinateSet_sub {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    coordinateDifferenceBody Omega = coordinateSet (Omega - Omega) := by
  rw [coordinateDifferenceBody_eq_sub]
  ext v
  constructor
  · rw [Set.mem_sub]
    rintro ⟨x, ⟨x', hx', rfl⟩, y, ⟨y', hy', rfl⟩, rfl⟩
    refine ⟨x' - y', ?_, ?_⟩
    · rw [Set.mem_sub]
      exact ⟨x', hx', y', hy', rfl⟩
    · rfl
  · rintro ⟨z, hz, rfl⟩
    rw [Set.mem_sub] at hz ⊢
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    exact ⟨(WithLp.linearEquiv 2 ℝ (Fin d → ℝ)) x, ⟨x, hx, rfl⟩,
      (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)) y, ⟨y, hy, rfl⟩, rfl⟩

/-- Linear coordinates preserve convexity. -/
theorem convex_coordinateSet {d : ℕ}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hOmega : Convex ℝ Omega) : Convex ℝ (coordinateSet Omega) :=
  hOmega.linear_image (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap

/-- The difference body of a convex set is convex. -/
theorem convex_coordinateDifferenceBody {d : ℕ}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hOmega : Convex ℝ Omega) : Convex ℝ (coordinateDifferenceBody Omega) := by
  rw [coordinateDifferenceBody_eq_sub]
  exact (convex_coordinateSet hOmega).sub (convex_coordinateSet hOmega)

/-- The difference body is centrally symmetric, hence balanced because it
is convex. -/
theorem balanced_coordinateDifferenceBody {d : ℕ}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hOmega : Convex ℝ Omega) : Balanced ℝ (coordinateDifferenceBody Omega) := by
  apply (balanced_iff_neg_mem (convex_coordinateDifferenceBody hOmega)).2
  intro v hv
  rw [coordinateDifferenceBody_eq_sub, Set.mem_sub] at hv ⊢
  obtain ⟨x, hx, y, hy, rfl⟩ := hv
  exact ⟨y, hy, x, hx, by abel⟩

/-- Closed difference body used for the relative-span John input. -/
def closedCoordinateDifferenceBody {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) : Set (Fin d → ℝ) :=
  closure (coordinateDifferenceBody Omega)

theorem differenceBody_subset_closedDifferenceBody {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    coordinateDifferenceBody Omega ⊆ closedCoordinateDifferenceBody Omega :=
  subset_closure

theorem convex_closedCoordinateDifferenceBody {d : ℕ}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hOmega : Convex ℝ Omega) :
    Convex ℝ (closedCoordinateDifferenceBody Omega) :=
  (convex_coordinateDifferenceBody hOmega).closure

theorem balanced_closedCoordinateDifferenceBody {d : ℕ}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hOmega : Convex ℝ Omega) :
    Balanced ℝ (closedCoordinateDifferenceBody Omega) :=
  (balanced_coordinateDifferenceBody hOmega).closure

theorem isClosed_closedCoordinateDifferenceBody {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    IsClosed (closedCoordinateDifferenceBody Omega) :=
  isClosed_closure

/-- Coordinate unwrapping also commutes with closure. -/
theorem closedCoordinateDifferenceBody_eq_coordinateSet {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    closedCoordinateDifferenceBody Omega =
      coordinateSet (euclideanClosedDifferenceBody Omega) := by
  rw [closedCoordinateDifferenceBody, euclideanClosedDifferenceBody,
    coordinateDifferenceBody_eq_coordinateSet_sub]
  exact ((WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toContinuousLinearEquiv.image_closure
    (Omega - Omega)).symm

/-- The coordinate and Euclidean closed difference bodies have equal
volume. -/
theorem volume_closedCoordinateDifferenceBody {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (closedCoordinateDifferenceBody Omega) =
      (MeasureTheory.volume : MeasureTheory.Measure
        (ConvexDensity.EuclideanPoint d))
          (euclideanClosedDifferenceBody Omega) := by
  rw [closedCoordinateDifferenceBody_eq_coordinateSet]
  exact volume_coordinateSet _ isClosed_closure.nullMeasurableSet

/-- Containment in a compact reference body supplies the boundedness field
needed by relative discrete John. -/
theorem bounded_coordinateDifferenceBody_of_subset {d : ℕ}
    {Omega reference : Set (ConvexDensity.EuclideanPoint d)}
    (hreference : ConvexDensity.IsConvexBody reference)
    (hsub : Omega ⊆ reference) :
    Bornology.IsVonNBounded ℝ (coordinateDifferenceBody Omega) := by
  have hOmegaBounded : Bornology.IsBounded Omega :=
    hreference.isCompact.isBounded.subset hsub
  have hcoordBounded : Bornology.IsBounded (coordinateSet Omega) := by
    simpa [coordinateSet, PiLp.coe_continuousLinearEquiv] using
      hOmegaBounded.image
        (PiLp.continuousLinearEquiv 2 ℝ
          (fun _ : Fin d ↦ ℝ)).toContinuousLinearMap
  have hcoord : Bornology.IsVonNBounded ℝ (coordinateSet Omega) :=
    (NormedSpace.isVonNBounded_iff ℝ).2 hcoordBounded
  rw [coordinateDifferenceBody_eq_sub]
  exact hcoord.sub hcoord

/-- The integer coordinate box containing differences of points in `B`. -/
def differenceBoundingBox {d : ℕ} (B : IntegerBox d) : IntegerBox d where
  lower := B.lower - B.upper
  upper := B.upper - B.lower

/-- Product formula for the public integer-box carrier. -/
theorem integerBox_card_carrier {d : ℕ} (B : IntegerBox d) :
    B.carrier.card =
      ∏ i, (B.upper i + 1 - B.lower i).toNat := by
  simp [IntegerBox.carrier, Int.card_Icc]

/-- The doubled difference box costs at most `2^d` lattice points. -/
theorem differenceBoundingBox_card_le {d : ℕ} (B : IntegerBox d)
    (hB : B.carrier.Nonempty) :
    (differenceBoundingBox B).carrier.card ≤ 2 ^ d * B.carrier.card := by
  rw [integerBox_card_carrier, integerBox_card_carrier]
  calc
    ∏ i, ((differenceBoundingBox B).upper i + 1 -
          (differenceBoundingBox B).lower i).toNat
        ≤ ∏ i, 2 * (B.upper i + 1 - B.lower i).toNat := by
      apply Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
      intro i _hi
      obtain ⟨x, hx⟩ := hB
      have hi := (IntegerBox.mem_carrier_iff.mp hx) i
      have hw : 0 ≤ B.upper i - B.lower i := by omega
      have hs : 0 ≤ (differenceBoundingBox B).upper i + 1 -
          (differenceBoundingBox B).lower i := by
        dsimp [differenceBoundingBox]
        linarith
      have ho : 0 ≤ B.upper i + 1 - B.lower i := by linarith
      dsimp [differenceBoundingBox]
      omega
    _ = 2 ^ d * ∏ i, (B.upper i + 1 - B.lower i).toNat := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Continuous coordinate version of `differenceBoundingBox`. -/
def realDifferenceCoordinateBox {d : ℕ} (B : IntegerBox d) :
    Set (Fin d → ℝ) :=
  Set.Icc (fun i ↦ (B.lower i - B.upper i : ℤ))
    (fun i ↦ (B.upper i - B.lower i : ℤ))

theorem coordinateDifferenceBody_subset_realDifferenceCoordinateBox
    {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hsub : Omega ⊆ boxRealization B) :
    coordinateDifferenceBody Omega ⊆ realDifferenceCoordinateBox B := by
  rintro v ⟨x, hx, y, hy, rfl⟩
  have hxB := hsub hx
  have hyB := hsub hy
  constructor <;> intro i
  · have hxi := (BoxDiscretization.IntegerBox.mem_realization_iff.mp hxB i)
    have hyi := (BoxDiscretization.IntegerBox.mem_realization_iff.mp hyB i)
    change (B.lower i : ℝ) ≤ x i ∧ x i ≤ (B.upper i : ℝ) at hxi
    change (B.lower i : ℝ) ≤ y i ∧ y i ≤ (B.upper i : ℝ) at hyi
    change ((B.lower i - B.upper i : ℤ) : ℝ) ≤ x i - y i
    push_cast
    linarith
  · have hxi := (BoxDiscretization.IntegerBox.mem_realization_iff.mp hxB i)
    have hyi := (BoxDiscretization.IntegerBox.mem_realization_iff.mp hyB i)
    change (B.lower i : ℝ) ≤ x i ∧ x i ≤ (B.upper i : ℝ) at hxi
    change (B.lower i : ℝ) ≤ y i ∧ y i ≤ (B.upper i : ℝ) at hyi
    change x i - y i ≤ ((B.upper i - B.lower i : ℤ) : ℝ)
    push_cast
    linarith

/-- Taking closure does not leave the closed doubled coordinate box. -/
theorem closedCoordinateDifferenceBody_subset_realDifferenceCoordinateBox
    {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hsub : Omega ⊆ boxRealization B) :
    closedCoordinateDifferenceBody Omega ⊆ realDifferenceCoordinateBox B := by
  apply (isClosed_Icc : IsClosed (realDifferenceCoordinateBox B)).closure_subset_iff.mpr
  exact coordinateDifferenceBody_subset_realDifferenceCoordinateBox hsub

/-- Every lattice point of the closed difference body lies in the finite
doubled coordinate box. -/
theorem integralEmbed_mem_differenceBoundingBox_of_mem_closedDifferenceBody
    {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hsub : Omega ⊆ boxRealization B) {z : BoxPoint d}
    (hz : CFP.Bilu.Mahler.integralEmbed z ∈
      closedCoordinateDifferenceBody Omega) :
    z ∈ (differenceBoundingBox B).carrier := by
  rw [IntegerBox.mem_carrier_iff]
  have hzbox :=
    closedCoordinateDifferenceBody_subset_realDifferenceCoordinateBox hsub hz
  intro i
  change B.lower i - B.upper i ≤ z i ∧
    z i ≤ B.upper i - B.lower i
  constructor
  · have hi := hzbox.1 i
    change ((B.lower i - B.upper i : ℤ) : ℝ) ≤ (z i : ℝ) at hi
    exact_mod_cast hi
  · have hi := hzbox.2 i
    change (z i : ℝ) ≤ ((B.upper i - B.lower i : ℤ) : ℝ) at hi
    exact_mod_cast hi

/-- The exact finite lattice section of the closed difference body. -/
def closedDifferenceLatticeSection {d : ℕ} (B : IntegerBox d)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    Finset (BoxPoint d) := by
  classical
  exact (differenceBoundingBox B).carrier.filter fun z ↦
    CFP.Bilu.Mahler.integralEmbed z ∈
      closedCoordinateDifferenceBody Omega

/-- Under containment in the reference box, filtering the doubled box loses
no lattice point of the closed difference body. -/
theorem mem_closedDifferenceLatticeSection_iff {d : ℕ}
    {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hsub : Omega ⊆ boxRealization B) {z : BoxPoint d} :
    z ∈ closedDifferenceLatticeSection B Omega ↔
      CFP.Bilu.Mahler.integralEmbed z ∈
        closedCoordinateDifferenceBody Omega := by
  simp only [closedDifferenceLatticeSection, Finset.mem_filter]
  constructor
  · exact fun hz ↦ hz.2
  · intro hz
    exact ⟨integralEmbed_mem_differenceBoundingBox_of_mem_closedDifferenceBody
      hsub hz, hz⟩

/-- The exact lattice section has a uniform dimension-only cardinal cost. -/
theorem closedDifferenceLatticeSection_card_le {d : ℕ}
    {B : IntegerBox d}
    (hB : B.carrier.Nonempty)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    (closedDifferenceLatticeSection B Omega).card ≤
      2 ^ d * B.carrier.card := by
  classical
  exact (Finset.card_filter_le _ _).trans
    (differenceBoundingBox_card_le B hB)

/-- Centering at a retained lattice point puts every restricted lattice
point in the literal coordinate difference body.  This is the fully
elementary centering part of the PZ discretization step. -/
theorem integralEmbed_centeredBoxLatticePointsIn_subset_differenceBody
    {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    {center : BoxPoint d}
    (hcenter : center ∈ boxLatticePointsIn B Omega) :
    ∀ z ∈ centeredBoxLatticePointsIn B Omega center,
      CFP.Bilu.Mahler.integralEmbed z ∈ coordinateDifferenceBody Omega := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have hxOmega : BoxDiscretization.latticeEmbed x ∈ Omega :=
    (mem_latticeRestriction.mp hx).2
  have hcenterOmega : BoxDiscretization.latticeEmbed center ∈ Omega :=
    (mem_latticeRestriction.mp hcenter).2
  refine ⟨BoxDiscretization.latticeEmbed x, hxOmega,
    BoxDiscretization.latticeEmbed center, hcenterOmega, ?_⟩
  funext i
  simp [CFP.Bilu.Mahler.integralEmbed, BoxDiscretization.latticeEmbed,
    sub_eq_add_neg]

/-- The real inner parallelepiped determined by a full-rank certificate.
Unlike the finite inner GAP, this is the continuous object whose volume is
controlled by the determinant of the integral step matrix. -/
def realInnerParallelepiped {d rank factor : ℕ}
    {points : Finset (BoxPoint d)}
    (C : DiscreteJohn.Certificate points rank factor) : Set (Fin d → ℝ) :=
  {x | ∃ a : Fin rank → ℝ,
    (∀ i, |a i| ≤ ((C.radii i / factor : ℕ) : ℝ)) ∧
      x = ∑ i, a i • CFP.Bilu.Mahler.integralEmbed (C.steps i)}

/-- Symmetric convex data in its actual affine span.  Unlike
`DiscreteJohn.SymmetricConvexBody`, this does not demand ambient nonempty
interior; that omission is essential for the dimension-drop branch. -/
structure RelativeSymmetricConvexBody {d : ℕ} (K : Set (Fin d → ℝ)) : Prop where
  balanced : Balanced ℝ K
  convex : Convex ℝ K
  bounded : Bornology.IsVonNBounded ℝ K
  isClosed : IsClosed K

/-- All algebraic/topological fields of the relative symmetric body follow
for the closed difference body once boundedness has been supplied. -/
theorem closedDifferenceBody_isRelativeSymmetricConvexBody {d : ℕ}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hOmega : Convex ℝ Omega)
    (hbounded : Bornology.IsVonNBounded ℝ
      (coordinateDifferenceBody Omega)) :
    RelativeSymmetricConvexBody (closedCoordinateDifferenceBody Omega) :=
  ⟨balanced_closedCoordinateDifferenceBody hOmega,
    convex_closedCoordinateDifferenceBody hOmega, hbounded.closure,
    isClosed_closedCoordinateDifferenceBody Omega⟩

/-! ### The finite lattice hull used by the source normalization -/

/-- Convex hull of the retained lattice section, in Euclidean space. -/
def finiteLatticeHull {d : ℕ} (B : IntegerBox d)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    Set (ConvexDensity.EuclideanPoint d) :=
  convexHull ℝ
    (Intersection.realImage (boxLatticePointsIn B Omega) :
      Set (ConvexDensity.EuclideanPoint d))

/-- The actual symmetric set needed for discrete John is the closed
difference body of the finite lattice hull, not of all of `Omega`. -/
def finiteHullDifferenceBody {d : ℕ} (B : IntegerBox d)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) : Set (Fin d → ℝ) :=
  closedCoordinateDifferenceBody (finiteLatticeHull B Omega)

theorem convex_finiteLatticeHull {d : ℕ} (B : IntegerBox d)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    Convex ℝ (finiteLatticeHull B Omega) :=
  convex_convexHull ℝ _

/-- The finite lattice hull stays inside every convex set which contains
the retained lattice section. -/
theorem finiteLatticeHull_subset {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hOmega : Convex ℝ Omega) : finiteLatticeHull B Omega ⊆ Omega := by
  apply convexHull_min _ hOmega
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  exact (mem_latticeRestriction.mp hz).2

/-- Centered retained points lie in the finite-hull difference body. -/
theorem centered_mem_finiteHullDifferenceBody {d : ℕ}
    {B : IntegerBox d} {Omega : Set (ConvexDensity.EuclideanPoint d)}
    {center : BoxPoint d} (hcenter : center ∈ boxLatticePointsIn B Omega) :
    ∀ z ∈ centeredBoxLatticePointsIn B Omega center,
      CFP.Bilu.Mahler.integralEmbed z ∈ finiteHullDifferenceBody B Omega := by
  intro z hz
  apply differenceBody_subset_closedDifferenceBody
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have hxHull : BoxDiscretization.latticeEmbed x ∈ finiteLatticeHull B Omega :=
    subset_convexHull ℝ _ (Intersection.mem_realImage_of_mem hx)
  have hcHull : BoxDiscretization.latticeEmbed center ∈
      finiteLatticeHull B Omega :=
    subset_convexHull ℝ _ (Intersection.mem_realImage_of_mem hcenter)
  exact ⟨BoxDiscretization.latticeEmbed x, hxHull,
    BoxDiscretization.latticeEmbed center, hcHull, by
      funext i
      simp [CFP.Bilu.Mahler.integralEmbed,
        BoxDiscretization.latticeEmbed, sub_eq_add_neg]⟩

/-- The finite-hull body still lies in the doubled coordinate box. -/
theorem finiteHullDifferenceBody_subset_realDifferenceCoordinateBox
    {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hOmega : Convex ℝ Omega) (hsub : Omega ⊆ boxRealization B) :
    finiteHullDifferenceBody B Omega ⊆ realDifferenceCoordinateBox B := by
  exact closedCoordinateDifferenceBody_subset_realDifferenceCoordinateBox
    ((finiteLatticeHull_subset hOmega).trans hsub)

/-- Exact lattice section of the finite-hull difference body. -/
def finiteHullJohnPoints {d : ℕ} (B : IntegerBox d)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) : Finset (BoxPoint d) := by
  classical
  exact (differenceBoundingBox B).carrier.filter fun z ↦
    CFP.Bilu.Mahler.integralEmbed z ∈ finiteHullDifferenceBody B Omega

theorem mem_finiteHullJohnPoints_iff {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (hOmega : Convex ℝ Omega) (hsub : Omega ⊆ boxRealization B)
    {z : BoxPoint d} :
    z ∈ finiteHullJohnPoints B Omega ↔
      CFP.Bilu.Mahler.integralEmbed z ∈ finiteHullDifferenceBody B Omega := by
  classical
  simp only [finiteHullJohnPoints, Finset.mem_filter]
  constructor
  · exact fun hz ↦ hz.2
  · intro hz
    refine ⟨?_, hz⟩
    apply integralEmbed_mem_differenceBoundingBox_of_mem_closedDifferenceBody
      ((finiteLatticeHull_subset hOmega).trans hsub)
    exact hz

theorem finiteHullJohnPoints_card_le {d : ℕ} {B : IntegerBox d}
    (hB : B.carrier.Nonempty)
    (Omega : Set (ConvexDensity.EuclideanPoint d)) :
    (finiteHullJohnPoints B Omega).card ≤ 2 ^ d * B.carrier.card := by
  classical
  exact (Finset.card_filter_le _ _).trans
    (differenceBoundingBox_card_le B hB)

/-- The sole continuous normalization input left by the finite-hull
construction.  This is the determinant-cancellation estimate obtained by
putting a maximal simplex of the finite hull between the normalized inner
and outer cubes.  It is strictly narrower than a Rogers--Shephard theorem:
only finite lattice hulls occurring here are quantified. -/
def FiniteHullDeterminantCancellationStatement : Prop :=
  ∀ d : ℕ, 0 < d →
    ∃ volumeFactor : ℝ, 1 ≤ volumeFactor ∧
      ∀ (B : IntegerBox d)
        (Omega : Set (ConvexDensity.EuclideanPoint d)),
        Convex ℝ Omega → Omega ⊆ boxRealization B →
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
            (finiteHullDifferenceBody B Omega) ≤
          ENNReal.ofReal volumeFactor *
            (MeasureTheory.volume : MeasureTheory.Measure
              (ConvexDensity.EuclideanPoint d)) Omega

/-- Full-span core of the determinant-cancellation estimate.  This is the
single branch where maximal-simplex normalization and Jacobian cancellation
are needed; the non-full-span branch is proved below by measure zero. -/
def FullSpanFiniteHullDeterminantCancellationStatement : Prop :=
  ∀ d : ℕ, 0 < d →
    ∃ volumeFactor : ℝ, 1 ≤ volumeFactor ∧
      ∀ (B : IntegerBox d)
        (Omega : Set (ConvexDensity.EuclideanPoint d)),
        Convex ℝ Omega → Omega ⊆ boxRealization B →
        affineSpan ℝ
          (Intersection.realImage (boxLatticePointsIn B Omega) :
            Set (ConvexDensity.EuclideanPoint d)) = ⊤ →
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
            (finiteHullDifferenceBody B Omega) ≤
          ENNReal.ofReal volumeFactor *
            (MeasureTheory.volume : MeasureTheory.Measure
              (ConvexDensity.EuclideanPoint d)) Omega

/-- A lower-dimensional finite hull has a null closed difference body.  This
discharges the degenerate branch of the maximal-simplex normalization. -/
theorem volume_euclideanClosedDifferenceBody_finiteHull_eq_zero_of_span_ne_top
    {d : ℕ} (X : Finset (ConvexDensity.EuclideanPoint d))
    (hspan : affineSpan ℝ (X : Set (ConvexDensity.EuclideanPoint d)) ≠ ⊤) :
    (MeasureTheory.volume : MeasureTheory.Measure
        (ConvexDensity.EuclideanPoint d))
      (euclideanClosedDifferenceBody
        (convexHull ℝ (X : Set (ConvexDensity.EuclideanPoint d)))) = 0 := by
  by_cases hX : X.Nonempty
  · obtain ⟨x, hx⟩ := hX
    let s : AffineSubspace ℝ (ConvexDensity.EuclideanPoint d) :=
      affineSpan ℝ (X : Set (ConvexDensity.EuclideanPoint d))
    have hsNonempty : (s : Set (ConvexDensity.EuclideanPoint d)).Nonempty :=
      ⟨x, subset_affineSpan ℝ (X : Set (ConvexDensity.EuclideanPoint d)) hx⟩
    have hdir : s.direction ≠ ⊤ := by
      intro htop
      apply hspan
      exact (AffineSubspace.direction_eq_top_iff_of_nonempty hsNonempty).mp htop
    have hraw :
        convexHull ℝ (X : Set (ConvexDensity.EuclideanPoint d)) -
            convexHull ℝ (X : Set (ConvexDensity.EuclideanPoint d)) ⊆
          (s.direction : Set (ConvexDensity.EuclideanPoint d)) := by
      rw [Set.sub_subset_iff]
      intro y hy z hz
      exact AffineSubspace.vsub_mem_direction
        (convexHull_subset_affineSpan _ hy)
        (convexHull_subset_affineSpan _ hz)
    have hclosed : IsClosed
        (s.direction : Set (ConvexDensity.EuclideanPoint d)) :=
      Submodule.closed_of_finiteDimensional s.direction
    have hbody :
        euclideanClosedDifferenceBody
            (convexHull ℝ (X : Set (ConvexDensity.EuclideanPoint d))) ⊆
          (s.direction : Set (ConvexDensity.EuclideanPoint d)) := by
      exact hclosed.closure_subset_iff.mpr hraw
    exact MeasureTheory.measure_mono_null hbody
      (MeasureTheory.Measure.addHaar_submodule
        (MeasureTheory.volume : MeasureTheory.Measure
          (ConvexDensity.EuclideanPoint d)) s.direction hdir)
  · have hEmpty : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    subst X
    simp [euclideanClosedDifferenceBody]

/-- Coordinate unwrapping transfers the lower-dimensional null estimate to
the body used by discrete John. -/
theorem volume_finiteHullDifferenceBody_eq_zero_of_span_ne_top
    {d : ℕ} (B : IntegerBox d)
    (Omega : Set (ConvexDensity.EuclideanPoint d))
    (hspan : affineSpan ℝ
      (Intersection.realImage (boxLatticePointsIn B Omega) :
        Set (ConvexDensity.EuclideanPoint d)) ≠ ⊤) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
      (finiteHullDifferenceBody B Omega) = 0 := by
  rw [finiteHullDifferenceBody,
    volume_closedCoordinateDifferenceBody]
  exact
    volume_euclideanClosedDifferenceBody_finiteHull_eq_zero_of_span_ne_top
      (Intersection.realImage (boxLatticePointsIn B Omega)) hspan

/-- The fixed doubled cube which contains the normalized difference body. -/
def normalizedDoubleCube (d : ℕ) :
    Set (ConvexDensity.EuclideanPoint d) :=
  ConvexDensity.closedAxisBox (fun _ ↦ -2) (fun _ ↦ 2)

theorem isClosed_normalizedDoubleCube (d : ℕ) :
    IsClosed (normalizedDoubleCube d) :=
  ConvexDensity.isClosed_closedAxisBox _ _

/-- If an affine normalization sends `L` into `[-1,1]^d`, its linear part
sends the closed difference body into `[-2,2]^d`. -/
theorem linear_image_closedDifferenceBody_subset_normalizedDoubleCube
    {d : ℕ} (e : ConvexDensity.EuclideanPoint d ≃ᵃ[ℝ]
      ConvexDensity.EuclideanPoint d)
    (L : Set (ConvexDensity.EuclideanPoint d))
    (houter : e '' L ⊆ ConvexDensity.normalizedOuterCube d) :
    e.linear '' euclideanClosedDifferenceBody L ⊆ normalizedDoubleCube d := by
  rw [euclideanClosedDifferenceBody]
  change (fun x ↦ e.linear.toContinuousLinearEquiv.toHomeomorph x) ''
      closure (L - L) ⊆ normalizedDoubleCube d
  rw [e.linear.toContinuousLinearEquiv.toHomeomorph.image_closure]
  apply (isClosed_normalizedDoubleCube d).closure_subset_iff.mpr
  rintro w ⟨v, hv, rfl⟩
  rw [Set.mem_sub] at hv
  obtain ⟨x, hx, y, hy, rfl⟩ := hv
  have hex := houter ⟨x, hx, rfl⟩
  have hey := houter ⟨y, hy, rfl⟩
  change e.linear (x - y) ∈ normalizedDoubleCube d
  rw [show e.linear (x - y) = e x - e y by
    exact AffineMap.linearMap_vsub e.toAffineMap x y]
  intro i
  constructor
  · have hxcoord := hex i
    have hycoord := hey i
    dsimp [ConvexDensity.normalizedOuterCube,
      ConvexDensity.closedAxisBox] at hxcoord hycoord
    dsimp [normalizedDoubleCube, ConvexDensity.closedAxisBox]
    linarith
  · have hxcoord := hex i
    have hycoord := hey i
    dsimp [ConvexDensity.normalizedOuterCube,
      ConvexDensity.closedAxisBox] at hxcoord hycoord
    dsimp [normalizedDoubleCube, ConvexDensity.closedAxisBox]
    linarith

/-- The doubled normalized cube has `2^d` times the volume of the outer
normalization cube. -/
theorem volume_normalizedDoubleCube (d : ℕ) :
    (MeasureTheory.volume : MeasureTheory.Measure
        (ConvexDensity.EuclideanPoint d)) (normalizedDoubleCube d) =
      (2 : ℝ≥0∞) ^ d *
        (MeasureTheory.volume : MeasureTheory.Measure
          (ConvexDensity.EuclideanPoint d))
            (ConvexDensity.normalizedOuterCube d) := by
  rw [normalizedDoubleCube, ConvexDensity.volume_closedAxisBox,
    ConvexDensity.volume_normalizedOuterCube]
  norm_num [← mul_pow]

/-- The full-span maximal-simplex estimate extends to every finite lattice
hull because the complementary branch has zero volume. -/
theorem finiteHullDeterminantCancellation_of_fullSpan
    (hFullSpan : FullSpanFiniteHullDeterminantCancellationStatement) :
    FiniteHullDeterminantCancellationStatement := by
  intro d hd
  obtain ⟨volumeFactor, hvolumeFactor, hfull⟩ := hFullSpan d hd
  refine ⟨volumeFactor, hvolumeFactor, ?_⟩
  intro B Omega hOmega hsub
  by_cases hspan : affineSpan ℝ
      (Intersection.realImage (boxLatticePointsIn B Omega) :
        Set (ConvexDensity.EuclideanPoint d)) = ⊤
  · exact hfull B Omega hOmega hsub hspan
  · rw [volume_finiteHullDifferenceBody_eq_zero_of_span_ne_top B Omega hspan]
    exact bot_le

structure SymmetricReductionData {d : ℕ} (B : IntegerBox d)
    (Omega : Set (ConvexDensity.EuclideanPoint d))
    (eta : ℝ) (pointFactor : ℕ) (volumeFactor : ℝ) where
  center : BoxPoint d
  center_mem : center ∈ boxLatticePointsIn B Omega
  body : Set (Fin d → ℝ)
  body_isSymmetricConvex : RelativeSymmetricConvexBody body
  /-- This is the exact containment consumed by the John-coordinate
  transport.  Requiring the whole difference body would be unnecessarily
  strong: only the centered retained lattice population is used. -/
  centered_mem_body :
    ∀ z ∈ centeredBoxLatticePointsIn B Omega center,
      CFP.Bilu.Mahler.integralEmbed z ∈ body
  johnPoints : Finset (BoxPoint d)
  johnPoints_exact :
    ∀ z, z ∈ johnPoints ↔ CFP.Bilu.Mahler.integralEmbed z ∈ body
  johnPoints_card_le : johnPoints.card ≤ pointFactor * B.carrier.card
  body_volume_le :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) body ≤
      ENNReal.ofReal (volumeFactor * eta) *
        (MeasureTheory.volume : MeasureTheory.Measure
          (ConvexDensity.EuclideanPoint d)) (boxRealization B)

namespace SymmetricReductionData

variable {d : ℕ} {B : IntegerBox d}
  {Omega : Set (ConvexDensity.EuclideanPoint d)}
  {eta volumeFactor : ℝ} {pointFactor : ℕ}

/-- Difference-body containment and exact lattice-section membership imply
the centered finite containment needed by the coordinate transport. -/
theorem centered_subset_johnPoints
    (S : SymmetricReductionData B Omega eta pointFactor volumeFactor) :
    centeredBoxLatticePointsIn B Omega S.center ⊆ S.johnPoints := by
  intro z hz
  rw [S.johnPoints_exact]
  exact S.centered_mem_body z hz

end SymmetricReductionData

/-- The first genuinely geometric bridge not supplied by
`DiscreteJohnStatement`: center and (if necessary) slightly thicken the
difference body so that it is a symmetric convex body with exactly the
displayed lattice points.  The factor is allowed to depend on the ambient
dimension, but not on the particular box or convex restriction. -/
def CenteredSymmetricReductionStatement : Prop :=
  ∀ d : ℕ, 0 < d →
    ∃ pointFactor : ℕ, ∃ volumeFactor : ℝ, 1 ≤ volumeFactor ∧
      ∀ (B : IntegerBox d)
        (Omega : Set (ConvexDensity.EuclideanPoint d)) (eta : ℝ),
        ConvexDensity.IsConvexBody (boxRealization B) →
        0 < eta → Convex ℝ Omega → Omega ⊆ boxRealization B →
        (boxLatticePointsIn B Omega).Nonempty →
        ConvexDensity.relativeVolume Omega (boxRealization B) ≤
          ENNReal.ofReal eta →
        Nonempty
          (SymmetricReductionData B Omega eta pointFactor volumeFactor)

/-- The finite-hull determinant estimate supplies the complete centering and
symmetric-body package.  All discrete fields (exact lattice section and its
`2^d` cardinal cost) are constructed here. -/
theorem centeredSymmetricReduction_of_finiteHullDeterminant
    (hDeterminant : FiniteHullDeterminantCancellationStatement) :
    CenteredSymmetricReductionStatement := by
  intro d hd
  obtain ⟨volumeFactor, hvolumeFactor, hvolume⟩ := hDeterminant d hd
  refine ⟨2 ^ d, volumeFactor, hvolumeFactor, ?_⟩
  intro B Omega eta hB heta hOmega hsub hnonempty hrelative
  obtain ⟨center, hcenter⟩ := hnonempty
  have hcarrierNonempty : B.carrier.Nonempty := by
    exact ⟨center, (mem_latticeRestriction.mp hcenter).1⟩
  have hHullSubBox : finiteLatticeHull B Omega ⊆ boxRealization B :=
    (finiteLatticeHull_subset hOmega).trans hsub
  have hbounded : Bornology.IsVonNBounded ℝ
      (coordinateDifferenceBody (finiteLatticeHull B Omega)) :=
    bounded_coordinateDifferenceBody_of_subset hB hHullSubBox
  have hvolumeOmega :
      (MeasureTheory.volume : MeasureTheory.Measure
          (ConvexDensity.EuclideanPoint d)) Omega ≤
        ENNReal.ofReal eta *
          (MeasureTheory.volume : MeasureTheory.Measure
            (ConvexDensity.EuclideanPoint d)) (boxRealization B) :=
    (ConvexDensity.relativeVolume_le_iff hB eta).mp hrelative
  have hvfNonneg : 0 ≤ volumeFactor := le_trans zero_le_one hvolumeFactor
  refine ⟨{
    center := center
    center_mem := hcenter
    body := finiteHullDifferenceBody B Omega
    body_isSymmetricConvex :=
      closedDifferenceBody_isRelativeSymmetricConvexBody
        (convex_finiteLatticeHull B Omega) hbounded
    centered_mem_body := centered_mem_finiteHullDifferenceBody hcenter
    johnPoints := finiteHullJohnPoints B Omega
    johnPoints_exact := fun z ↦ mem_finiteHullJohnPoints_iff hOmega hsub
    johnPoints_card_le := finiteHullJohnPoints_card_le hcarrierNonempty Omega
    body_volume_le := ?_ }⟩
  calc
    (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
          (finiteHullDifferenceBody B Omega) ≤
        ENNReal.ofReal volumeFactor *
          (MeasureTheory.volume : MeasureTheory.Measure
            (ConvexDensity.EuclideanPoint d)) Omega :=
      hvolume B Omega hOmega hsub
    _ ≤ ENNReal.ofReal volumeFactor *
        (ENNReal.ofReal eta *
          (MeasureTheory.volume : MeasureTheory.Measure
            (ConvexDensity.EuclideanPoint d)) (boxRealization B)) := by
      gcongr
    _ = ENNReal.ofReal (volumeFactor * eta) *
        (MeasureTheory.volume : MeasureTheory.Measure
          (ConvexDensity.EuclideanPoint d)) (boxRealization B) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hvfNonneg]

/-- The source-strength discrete-John output for a possibly
lower-dimensional symmetric convex set.  Its rank is effective: in the
ambient-rank branch the lattice section genuinely has full rank.  Small or
zero John radii are allowed and are handled by the additive-one estimate
in `FullRankVolumeBridgeStatement`. -/
def EffectiveDiscreteJohnStatement : Prop :=
  ∀ d : ℕ, ∃ factorBound : ℕ,
    ∀ pointFactor : ℕ, ∀ volumeFactor eta : ℝ,
      ∀ (B : IntegerBox d)
        (Omega : Set (ConvexDensity.EuclideanPoint d))
        (S : SymmetricReductionData B Omega eta pointFactor volumeFactor),
        ∃ factor : ℕ, factor ≤ factorBound ∧
          Nonempty (DiscreteJohn.Certificate S.johnPoints
            (DiscreteJohn.RankReduction.sectionRank S.johnPoints) factor)

/-- Compatibility statement between ambient discrete John and the
effective-rank theorem used by PZ.  It is discharged immediately below by
passing to the intrinsic lattice coordinates developed in
`DiscreteJohnSection`. -/
def ActiveDiscreteJohnUpgradeStatement : Prop :=
  DiscreteJohn.DiscreteJohnStatement → EffectiveDiscreteJohnStatement

/-- The intrinsic-coordinate construction in `DiscreteJohnSection` supplies
the formerly missing active-rank upgrade.  Nonemptiness of the lattice
section follows from the retained center, whose translate by its negative is
zero. -/
theorem activeDiscreteJohnUpgrade_of_discreteJohnSection :
    ActiveDiscreteJohnUpgradeStatement := by
  intro hJohn
  obtain hEffective :=
    DiscreteJohn.RankReduction.effectiveSectionDiscreteJohn_of_discreteJohn
      hJohn
  intro d
  obtain ⟨factorBound, hfactorBound⟩ := hEffective d
  refine ⟨factorBound, ?_⟩
  intro pointFactor volumeFactor eta B Omega S
  have hcenteredNonempty :
      (centeredBoxLatticePointsIn B Omega S.center).Nonempty := by
    refine ⟨0, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨S.center, S.center_mem, by simp⟩
  have hjohnNonempty : S.johnPoints.Nonempty :=
    hcenteredNonempty.mono S.centered_subset_johnPoints
  exact hfactorBound S.body S.body_isSymmetricConvex.balanced
    S.body_isSymmetricConvex.convex S.body_isSymmetricConvex.isClosed
    S.body_isSymmetricConvex.bounded S.johnPoints S.johnPoints_exact
    hjohnNonempty

/-- The remaining continuous-volume input in the full-rank branch.

Once the lattice section has full rank, the geometry-of-numbers argument
bounds its outer box by body volume plus the unavoidable lattice rounding
term.  The additive one is essential when the body is small; the application
threshold absorbs it.  Keeping that argument in this proposition makes the
exact gap beyond the already formalized discrete theorem explicit. -/
def FullRankVolumeBridgeStatement : Prop :=
  ∀ d factorBound pointFactor : ℕ, ∀ volumeFactor : ℝ, 0 < d →
    1 ≤ volumeFactor →
    ∃ volumeConstant : ℝ, 1 ≤ volumeConstant ∧
      ∀ (B : IntegerBox d)
        (Omega : Set (ConvexDensity.EuclideanPoint d)) (eta : ℝ)
        (S : SymmetricReductionData B Omega eta pointFactor volumeFactor)
        (rank factor : ℕ)
        (C : DiscreteJohn.Certificate S.johnPoints rank factor),
        0 < eta →
        factor ≤ factorBound →
        rank = DiscreteJohn.RankReduction.sectionRank S.johnPoints →
        rank = d →
        (C.outer.volume : ℝ) ≤
          volumeConstant * (eta * (B.carrier.card : ℝ) + 1)

/-- The exact missing geometric existence theorem corresponding to PZ
Lemma 7.

The lower-rank alternative feeds a dimension drop.  In full rank, the inner
progression vertices and convexity place a continuous parallelepiped inside
`Omega`; the nonzero integral determinant then yields the displayed
outer-volume saving.  The rank-sensitive certificate construction is now
checked; the latter continuous determinant/volume estimate is isolated in
`FullRankVolumeBridgeStatement`. -/
def PZLemmaSevenStatement : Prop :=
  ∀ d : ℕ, 0 < d →
    ∃ factorBound : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ (B : IntegerBox d)
        (Omega : Set (ConvexDensity.EuclideanPoint d)) (eta : ℝ),
        ConvexDensity.IsConvexBody (boxRealization B) →
        0 < eta → Convex ℝ Omega → Omega ⊆ boxRealization B →
        (boxLatticePointsIn B Omega).Nonempty →
        ConvexDensity.relativeVolume Omega (boxRealization B) ≤
          ENNReal.ofReal eta →
        1 ≤ eta * (B.carrier.card : ℝ) →
        ∃ J : CenteredDiscreteJohnCertificate B Omega,
          J.factor ≤ factorBound ∧
            (J.certificate.outer.volume : ℝ) ≤
              constant * (B.carrier.card : ℝ) ∧
            (J.rank < d ∨
              (J.rank = d ∧
                (J.certificate.outer.volume : ℝ) ≤
                  constant * eta * (B.carrier.card : ℝ)))

/-! ### Checked adapter from the active discrete-John theorem -/

/-- Bounding the discrete-John factor, rank, and symmetric lattice
population gives a uniform coarse outer-volume estimate.  This is the
estimate used by the rank-drop branch; it does not use continuous volume. -/
theorem outer_volume_le_coarse {d pointFactor factorBound : ℕ}
    {B : IntegerBox d} {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (J : CenteredDiscreteJohnCertificate B Omega)
    (hfactor : J.factor ≤ factorBound)
    (hpoints : J.johnPoints.card ≤ pointFactor * B.carrier.card) :
    J.certificate.outer.volume ≤
      ((2 * factorBound + 1) ^ d * pointFactor) * B.carrier.card := by
  have hbase : 2 * J.factor + 1 ≤ 2 * factorBound + 1 := by omega
  have hpowBase :
      (2 * J.factor + 1) ^ J.rank ≤
        (2 * factorBound + 1) ^ J.rank :=
    Nat.pow_le_pow_left hbase _
  have hpowRank :
      (2 * factorBound + 1) ^ J.rank ≤
        (2 * factorBound + 1) ^ d :=
    Nat.pow_le_pow_right (by omega) J.rank_le
  calc
    J.certificate.outer.volume ≤
        (2 * J.factor + 1) ^ J.rank * J.johnPoints.card :=
      J.outer_volume_le_factor_mul_johnPoints
    _ ≤ (2 * factorBound + 1) ^ d *
        (pointFactor * B.carrier.card) :=
      Nat.mul_le_mul (hpowBase.trans hpowRank) hpoints
    _ = ((2 * factorBound + 1) ^ d * pointFactor) *
        B.carrier.card := by simp [Nat.mul_assoc]

/-- `DiscreteJohnStatement`, together with precisely the centering and
full-rank continuous-volume bridges above, implies the source-shaped PZ
Lemma 7 output.  In particular, the rank dichotomy and the entire coarse
rank-drop estimate are proved here rather than hidden in a hypothesis. -/
theorem pzLemmaSeven_of_discreteJohn
    (hJohn : DiscreteJohn.DiscreteJohnStatement)
    (hUpgrade : ActiveDiscreteJohnUpgradeStatement)
    (hSymmetric : CenteredSymmetricReductionStatement)
    (hFullRank : FullRankVolumeBridgeStatement) :
    PZLemmaSevenStatement := by
  intro d hd
  obtain ⟨factorBound, hJohn_d⟩ := hUpgrade hJohn d
  obtain ⟨pointFactor, volumeFactor, hvolumeFactor,
    hSymmetric_d⟩ := hSymmetric d hd
  obtain ⟨volumeConstant, hvolumeConstant, hFullRank_d⟩ :=
    hFullRank d factorBound pointFactor volumeFactor hd hvolumeFactor
  let coarseNat : ℕ := (2 * factorBound + 1) ^ d * pointFactor
  let constant : ℝ := max (2 * volumeConstant) (coarseNat : ℝ)
  have honeTwoVolume : 1 ≤ 2 * volumeConstant := by
    nlinarith [hvolumeConstant]
  have hconstant : 1 ≤ constant :=
    honeTwoVolume.trans (le_max_left _ _)
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro B Omega eta hB heta hOmega hsub hnonempty hrelative hscale
  let S : SymmetricReductionData B Omega eta pointFactor volumeFactor :=
    Classical.choice
      (hSymmetric_d B Omega eta hB heta hOmega hsub hnonempty hrelative)
  obtain ⟨factor, hfactor, hcertificate⟩ :=
    hJohn_d pointFactor volumeFactor eta B Omega S
  let rank : ℕ := DiscreteJohn.RankReduction.sectionRank S.johnPoints
  have hrank : rank ≤ d :=
    DiscreteJohn.RankReduction.sectionRank_le S.johnPoints
  let C : DiscreteJohn.Certificate S.johnPoints rank factor :=
    Classical.choice hcertificate
  let J : CenteredDiscreteJohnCertificate B Omega := {
    center := S.center
    center_mem := S.center_mem
    johnPoints := S.johnPoints
    centered_subset_johnPoints := S.centered_subset_johnPoints
    rank := rank
    rank_le := hrank
    factor := factor
    certificate := C }
  have hcoarseNat : J.certificate.outer.volume ≤
      coarseNat * B.carrier.card := by
    exact outer_volume_le_coarse J hfactor S.johnPoints_card_le
  have hcoarseReal : (J.certificate.outer.volume : ℝ) ≤
      (coarseNat : ℝ) * (B.carrier.card : ℝ) := by
    exact_mod_cast hcoarseNat
  have hcoarse : (J.certificate.outer.volume : ℝ) ≤
      constant * (B.carrier.card : ℝ) := by
    exact hcoarseReal.trans (mul_le_mul_of_nonneg_right
      (le_max_right (2 * volumeConstant) (coarseNat : ℝ))
      (Nat.cast_nonneg _))
  refine ⟨J, hfactor, hcoarse, ?_⟩
  by_cases hranklt : rank < d
  · exact Or.inl hranklt
  · have hrankeq : rank = d := by omega
    have hsharpPlus : (C.outer.volume : ℝ) ≤
        volumeConstant * (eta * (B.carrier.card : ℝ) + 1) :=
      hFullRank_d B Omega eta S rank factor C heta hfactor rfl hrankeq
    have habsorb :
        volumeConstant * (eta * (B.carrier.card : ℝ) + 1) ≤
          (2 * volumeConstant) * eta * (B.carrier.card : ℝ) := by
      have hvolumeNonneg : 0 ≤ volumeConstant := hvolumeConstant.trans' zero_le_one
      nlinarith
    have hsharp : (C.outer.volume : ℝ) ≤
        (2 * volumeConstant) * eta * (B.carrier.card : ℝ) :=
      hsharpPlus.trans habsorb
    refine Or.inr ⟨hrankeq, hsharp.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left (2 * volumeConstant)
        (coarseNat : ℝ)) heta.le)
      (Nat.cast_nonneg _)

/-- The checked intrinsic-rank reduction removes the explicit upgrade
premise from the usable discrete-John adapter. -/
theorem pzLemmaSeven_of_discreteJohnSection
    (hJohn : DiscreteJohn.DiscreteJohnStatement)
    (hSymmetric : CenteredSymmetricReductionStatement)
    (hFullRank : FullRankVolumeBridgeStatement) :
    PZLemmaSevenStatement :=
  pzLemmaSeven_of_discreteJohn hJohn
    activeDiscreteJohnUpgrade_of_discreteJohnSection hSymmetric hFullRank

/-- Usable PZ Lemma 7 adapter with only the finite-hull determinant estimate
and the full-rank inner-parallelepiped estimate left as geometric inputs. -/
theorem pzLemmaSeven_of_discreteJohnFiniteHull
    (hJohn : DiscreteJohn.DiscreteJohnStatement)
    (hDeterminant : FiniteHullDeterminantCancellationStatement)
    (hFullRank : FullRankVolumeBridgeStatement) :
    PZLemmaSevenStatement :=
  pzLemmaSeven_of_discreteJohnSection hJohn
    (centeredSymmetricReduction_of_finiteHullDeterminant hDeterminant)
    hFullRank

/-- Final discrete-John adapter exposing only the genuine full-span
maximal-simplex estimate and the full-rank parallelepiped estimate.  Every
rank-deficient/measure-zero case is already discharged. -/
theorem pzLemmaSeven_of_discreteJohnMaximalSimplex
    (hJohn : DiscreteJohn.DiscreteJohnStatement)
    (hFullSpan : FullSpanFiniteHullDeterminantCancellationStatement)
    (hFullRank : FullRankVolumeBridgeStatement) :
    PZLemmaSevenStatement :=
  pzLemmaSeven_of_discreteJohnFiniteHull hJohn
    (finiteHullDeterminantCancellation_of_fullSpan hFullSpan) hFullRank

/-- Mahler extraction now supplies discrete John unconditionally.  Thus the
only remaining inputs to the source-shaped Lemma 7 adapter are the two
continuous full-dimensional volume estimates. -/
theorem pzLemmaSeven_of_maximalSimplex
    (hFullSpan : FullSpanFiniteHullDeterminantCancellationStatement)
    (hFullRank : FullRankVolumeBridgeStatement) :
    PZLemmaSevenStatement :=
  pzLemmaSeven_of_discreteJohnMaximalSimplex
    DiscreteJohn.MahlerExtraction.discreteJohnStatement hFullSpan hFullRank

/-! ## Axis-parallel rounding after coordinates have been chosen -/

/-- A lattice restriction lying in an explicit real axis-parallel box is
contained in the checked outward-rounded integer box. -/
theorem latticeRestriction_subset_roundedIntegerBox {d : ℕ}
    {A : Finset (BoxPoint d)}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    {lower upper : Fin d → ℝ}
    (henclose : Omega ⊆ BoxDiscretization.realBox lower upper) :
    latticeRestriction A Omega ⊆
      (roundedIntegerBox lower upper).carrier := by
  intro z hz
  have hzOmega := (mem_latticeRestriction.mp hz).2
  change z ∈ (BoxDiscretization.roundedBox lower upper).carrier
  exact BoxDiscretization.lattice_mem_roundedBox_of_mem_realBox
    (henclose hzOmega)

/-- The checked product estimate transfers verbatim to the public box. -/
theorem roundedIntegerBox_card_cast_le {d : ℕ}
    {lower upper : Fin d → ℝ} (hlu : ∀ i, lower i ≤ upper i) :
    ((roundedIntegerBox lower upper).carrier.card : ℝ) ≤
      ∏ i, (upper i - lower i + 3) := by
  exact BoxDiscretization.card_roundedBox_cast_le hlu

/-- Complete, checked rounding step from an explicit enclosure/product pair. -/
theorem exists_integerBox_of_axisParallel_enclosure {d : ℕ}
    {A : Finset (BoxPoint d)}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    {lower upper : Fin d → ℝ} {bound : ℝ}
    (hlu : ∀ i, lower i ≤ upper i)
    (henclose : Omega ⊆ BoxDiscretization.realBox lower upper)
    (hproduct : (∏ i, (upper i - lower i + 3)) ≤ bound) :
    ∃ B' : IntegerBox d,
      latticeRestriction A Omega ⊆ B'.carrier ∧
        (B'.carrier.card : ℝ) ≤ bound := by
  refine ⟨roundedIntegerBox lower upper,
    latticeRestriction_subset_roundedIntegerBox henclose, ?_⟩
  exact (roundedIntegerBox_card_cast_le hlu).trans hproduct

/- Explicit axis-parallel enclosure data, useful only after an appropriate
integral coordinate system has already been constructed. -/
structure AxisParallelEnclosureInput {d : ℕ}
    (Omega : Set (ConvexDensity.EuclideanPoint d)) (bound : ℝ) where
  lower : Fin d → ℝ
  upper : Fin d → ℝ
  lower_le_upper : ∀ i, lower i ≤ upper i
  subset_realBox : Omega ⊆ BoxDiscretization.realBox lower upper
  enlargedSideProduct_le :
    (∏ i, (upper i - lower i + 3)) ≤ bound

/-- An enclosure witness supplies exactly the public integer box promised by
the discretization half of the same-dimension step. -/
theorem AxisParallelEnclosureInput.exists_integerBox {d : ℕ}
    {A : Finset (BoxPoint d)}
    {Omega : Set (ConvexDensity.EuclideanPoint d)} {bound : ℝ}
    (E : AxisParallelEnclosureInput Omega bound) :
    ∃ B' : IntegerBox d,
      latticeRestriction A Omega ⊆ B'.carrier ∧
        (B'.carrier.card : ℝ) ≤ bound :=
  exists_integerBox_of_axisParallel_enclosure E.lower_le_upper
    E.subset_realBox E.enlargedSideProduct_le

end OneStepAssembly

end

end Erdos186.PZ

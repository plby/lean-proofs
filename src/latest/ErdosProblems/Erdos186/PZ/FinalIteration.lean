import ErdosProblems.Erdos186.DensityIteration
import ErdosProblems.Erdos186.PZ.FinalIteration.Numerics

/-!
# The final Pham--Zakharov density iteration

This file is the interface between the geometric one-step argument and the
finite bookkeeping which finishes the proof of the Pham--Zakharov box
theorem.  In particular, the hypothesis of the main theorem below is not an
abstract completed iteration and is not the desired box bound.  It is a
constructor for one more *concrete* state: the state contains an actual
integer box, an actual nonaveraging finite set in that box, and the strict
supercritical density certificate used in the paper.

The local constructor is partial: it may be used only while the current
dimension and population satisfy frozen applicability bounds.  The dimension
envelope is a state-level theorem, while the population stopping exclusion is
deduced along every trace from a uniform per-step power-retention estimate and
one initial-cardinality budget.  Classical choice then iterates the concrete
outputs for the finite frozen horizon, and the excess budget gives the
contradiction.

The separate file `PZ/FinalIteration/Numerics.lean` records the translation
between `boxExponent` and `pzExponent`, including Observation 15.  It can be
used by a concrete proof of the one-step constructor.
-/

namespace Erdos186.PZ.FinalIteration

open Finset
open scoped BigOperators

noncomputable section

/-! ## Source-faithful partial iteration with a frozen initial set

The paper obtains persistence globally, not as an output of a single local
step.  The definitions below give the public composition boundary.
The initial counterexample is frozen; a local step may be called only while
the current state is `Applicable`; and applicability of every prefix is
proved from the complete trace.
-/

namespace Partial

/-- A concrete state without any locally assumed size or dimension
persistence. -/
structure State (ζ : ℝ) where
  dimension : ℕ
  dimension_pos : 0 < dimension
  zeta_pos : 0 < ζ
  box : IntegerBox dimension
  points : Finset (BoxPoint dimension)
  points_subset_box : points ⊆ box.carrier
  nonaveraging : IsBoxNonaveraging points
  points_nonempty : points.Nonempty
  excess : ℝ
  excess_nonneg : 0 ≤ excess
  density_certificate :
    (boxExponent dimension + ζ + excess) *
        Real.log (box.carrier.card : ℝ) <
      Real.log (points.card : ℝ)

namespace State

/-- A strict supercritical density certificate forces at least two points.
This elementary fact is kept at the state level because both the dimension
envelope and the one-step assembly need the logarithm of the containing box
to be strictly positive. -/
theorem two_le_points_card {zeta : ℝ} (current : State zeta) :
    2 ≤ current.points.card := by
  have hboxNat : 1 ≤ current.box.carrier.card :=
    (Nat.succ_le_iff.mpr current.points_nonempty.card_pos).trans
      (Finset.card_le_card current.points_subset_box)
  have hlogBox : 0 ≤ Real.log (current.box.carrier.card : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hboxNat
  have htotalPos :
      0 < boxExponent current.dimension + zeta + current.excess := by
    have hbox := boxExponent_pos current.dimension_pos
    linarith [current.zeta_pos, current.excess_nonneg]
  have hlogPoints : 0 < Real.log (current.points.card : ℝ) := by
    exact (mul_nonneg htotalPos.le hlogBox).trans_lt
      current.density_certificate
  have hone : (1 : ℝ) < (current.points.card : ℝ) :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogPoints
  exact_mod_cast hone

/-- The total density exponent of a concrete state is strictly below one.
This follows only from strict density and containment, and therefore applies
uniformly to every trace state rather than requiring a separate dimension
persistence invariant. -/
theorem totalExponent_lt_one {zeta : ℝ} (current : State zeta) :
    boxExponent current.dimension + zeta + current.excess < 1 := by
  have hboxTwo : 2 ≤ current.box.carrier.card :=
    (two_le_points_card current).trans
      (Finset.card_le_card current.points_subset_box)
  have hboxPos : (0 : ℝ) < (current.box.carrier.card : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hboxTwo)
  have hpointsPos : (0 : ℝ) < (current.points.card : ℝ) := by
    exact_mod_cast current.points_nonempty.card_pos
  have hlogBoxPos : 0 < Real.log (current.box.carrier.card : ℝ) :=
    Real.log_pos (by exact_mod_cast hboxTwo)
  have hlogPointsLe :
      Real.log (current.points.card : ℝ) ≤
        Real.log (current.box.carrier.card : ℝ) :=
    Real.log_le_log hpointsPos (by
      exact_mod_cast Finset.card_le_card current.points_subset_box)
  have htotalLog :
      (boxExponent current.dimension + zeta + current.excess) *
          Real.log (current.box.carrier.card : ℝ) <
        Real.log (current.box.carrier.card : ℝ) :=
    current.density_certificate.trans_le hlogPointsLe
  nlinarith

/-- A fixed positive exponent loss gives a finite dimension ceiling for
every concrete state.  The ceiling depends only on `zeta`, not on the box,
population, trace length, or any choices made by the one-step theorem. -/
theorem exists_uniform_dimensionCeiling {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ dimensionCeiling : ℕ, ∀ current : State zeta,
      current.dimension ≤ dimensionCeiling := by
  obtain ⟨dimensionCeiling, hceiling⟩ := exists_nat_gt (2 / zeta)
  refine ⟨dimensionCeiling, ?_⟩
  intro current
  by_contra hnot
  have hceilingLt : dimensionCeiling < current.dimension :=
    Nat.lt_of_not_ge hnot
  have hceilingPos : 0 < dimensionCeiling := by
    have hpositive : (0 : ℝ) < (dimensionCeiling : ℝ) :=
      (div_pos (by norm_num : (0 : ℝ) < 2) hzeta).trans hceiling
    exact_mod_cast hpositive
  have hdimensionTwo : 2 ≤ current.dimension := by
    omega
  have hformula :
      boxExponent current.dimension =
        1 - 2 / ((current.dimension : ℝ) + 1) := by
    rw [boxExponent_eq_real_fraction hdimensionTwo]
    have hdenom : (current.dimension : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hexponent := current.totalExponent_lt_one
  have hzetaLt : zeta < 2 / ((current.dimension : ℝ) + 1) := by
    rw [hformula] at hexponent
    linarith [current.excess_nonneg]
  have hdimensionLt : (current.dimension : ℝ) < 2 / zeta := by
    rw [lt_div_iff₀ hzeta]
    have hscaled :
        zeta * ((current.dimension : ℝ) + 1) < 2 := by
      exact (lt_div_iff₀ (by positivity :
        (0 : ℝ) < (current.dimension : ℝ) + 1)).mp hzetaLt
    nlinarith
  have hcastCeilingLt : (dimensionCeiling : ℝ) <
      (current.dimension : ℝ) := by
    exact_mod_cast hceilingLt
  linarith

/-- Containment forces the excess of every concrete state to be at most
one.  This is deliberately proved directly from the actual finsets. -/
theorem excess_le_one {ζ : ℝ} (current : State ζ) : current.excess ≤ 1 := by
  have hpoints : 1 ≤ current.points.card :=
    Nat.succ_le_iff.mpr current.points_nonempty.card_pos
  have hboxNat : 1 ≤ current.box.carrier.card :=
    hpoints.trans (Finset.card_le_card current.points_subset_box)
  have hpointsPos : 0 < (current.points.card : ℝ) := by
    exact_mod_cast current.points_nonempty.card_pos
  have hcard : (current.points.card : ℝ) ≤
      (current.box.carrier.card : ℝ) := by
    exact_mod_cast Finset.card_le_card current.points_subset_box
  have hlogCard :
      Real.log (current.points.card : ℝ) ≤
        Real.log (current.box.carrier.card : ℝ) :=
    Real.log_le_log hpointsPos hcard
  have hlogBox : 0 ≤ Real.log (current.box.carrier.card : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hboxNat
  have hboxExponent : 0 ≤ boxExponent current.dimension := by
    exact (boxExponent_pos current.dimension_pos).le
  have hbase : 0 ≤ boxExponent current.dimension + ζ := by
    linarith [current.zeta_pos]
  have htotal :
      current.excess * Real.log (current.box.carrier.card : ℝ) <
        Real.log (current.points.card : ℝ) := by
    have hcompare :
        current.excess * Real.log (current.box.carrier.card : ℝ) ≤
          (boxExponent current.dimension + ζ + current.excess) *
            Real.log (current.box.carrier.card : ℝ) := by
      nlinarith [mul_nonneg hbase hlogBox]
    exact hcompare.trans_lt current.density_certificate
  by_contra h
  have hexcess : 1 < current.excess := lt_of_not_ge h
  have hboxStrict : 0 < Real.log (current.box.carrier.card : ℝ) := by
    by_contra hzero
    have hz : Real.log (current.box.carrier.card : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hzero) hlogBox
    rw [hz] at htotal
    linarith
  nlinarith

end State

/-- The three global conditions under which the analytic one-step theorem may
be applied.  The upper population bound freezes all source parameters from
the initial counterexample. -/
def Applicable {ζ : ℝ}
    (dimensionCeiling pointThreshold populationCeiling : ℕ)
    (current : State ζ) : Prop :=
  current.dimension ≤ dimensionCeiling ∧
    pointThreshold ≤ current.points.card ∧
    current.points.card ≤ populationCeiling

/-- One concrete output of the reduction/intersection/convex-density step.

No applicability condition is imposed on `next`.  Dimension persistence is
state-level; population persistence is supplied by the controlled wrapper
below and then iterated over a complete prefix trace. -/
structure StepOutput {K : ℕ} {ζ changeGain sameGain : ℝ}
    (current : State ζ) where
  next : State ζ
  /-- Restrictions never increase the population; in particular all later
  populations remain bounded by the frozen initial cardinality. -/
  points_card_le : next.points.card ≤ current.points.card
  kind : DensityIteration.StepKind
  retention : ℝ
  retention_pos : 0 < retention
  retention_le_one : retention ≤ 1
  population_retained :
    retention * (current.points.card : ℝ) ≤ (next.points.card : ℝ)
  /-- The population ratio from the irreducible replacement.  It is kept
  separate from the convex scale in the same-dimension branch. -/
  structuralRatio : ℝ
  structuralRatio_pos : 0 < structuralRatio
  structuralRatio_le_one : structuralRatio ≤ 1
  /-- The convex-density volume scale. -/
  convexScale : ℝ
  convexScale_pos : 0 < convexScale
  convexScale_le_one : convexScale ≤ 1
  /-- The fixed-dimensional implicit constant in the discretized box
  estimate.  It is explicit so that a concrete package can absorb its
  products over a same-dimension run. -/
  boxConstant : ℝ
  one_le_boxConstant : 1 ≤ boxConstant
  transition :
    match kind with
    | .up =>
        current.dimension < next.dimension ∧
          current.excess + changeGain ≤ next.excess
    | .down =>
        next.dimension < current.dimension ∧
          current.excess + changeGain ≤ next.excess
    | .same =>
        next.dimension = current.dimension ∧
          current.excess + sameGain ≤ next.excess ∧
          retention =
            convexScale ^
                (convexDensityExponent current.dimension + ζ / 2) *
              structuralRatio ∧
          (next.box.carrier.card : ℝ) ≤
            boxConstant * convexScale * structuralRatio ^ K *
              (current.box.carrier.card : ℝ)

/-- Convex-scale exponent in the point-retention product of a same-rank run. -/
def sameRunQ (dimension : ℕ) (zeta : ℝ) : ℝ :=
  convexDensityExponent dimension + zeta / 2

/-- Intermediate exponent used to transfer the initial density inequality
along a same-rank run. -/
def sameRunLambda (dimension : ℕ) (zeta : ℝ) : ℝ :=
  convexDensityExponent dimension + 3 * zeta / 4

/-- Exponent which absorbs the fixed box constant into the convex scale in
a same-rank run. -/
def sameRunA (dimension : ℕ) (zeta : ℝ) : ℝ :=
  sameRunQ dimension zeta / sameRunLambda dimension zeta

/-- A source-controlled iteration step.  The raw geometric `StepOutput`
records the exact branch estimates, while this wrapper records the uniform
power retention needed to iterate those estimates without allowing a rank
change to collapse an arbitrarily large population to a fixed finite set. -/
structure PowerControlledStepOutput {K : ℕ}
    {ζ changeGain sameGain rho : ℝ} (current : State ζ)
    extends StepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) current where
  points_power_retained :
    (current.points.card : ℝ) ^ (1 - rho) ≤ (next.points.card : ℝ)

/-- The source-faithful branch control on a raw geometric step.  A
dimension-changing move pays the fixed replacement power loss; a
same-dimension move instead absorbs its fixed box constant into the convex
scale, so an arbitrarily long same-dimension run can be telescoped before
any population power is charged. -/
structure BranchControlledStepOutput {K : ℕ}
    {ζ changeGain sameGain rhoChange : ℝ} (current : State ζ)
    extends StepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) current where
  change_points_power_retained :
    kind ≠ .same →
      (current.points.card : ℝ) ^ (1 - rhoChange) ≤
        (next.points.card : ℝ)
  same_box_absorbed :
    kind = .same →
      boxConstant * convexScale ≤
        convexScale ^ sameRunA current.dimension ζ

/-- A local one-step theorem, applicable only under the current global
dimension and population bounds. -/
def OneStepConstructor
    (dimensionCeiling pointThreshold populationCeiling K : ℕ)
    (ζ changeGain sameGain rho : ℝ) : Prop :=
  ∀ current : State ζ,
    Applicable dimensionCeiling pointThreshold populationCeiling current →
      Nonempty (PowerControlledStepOutput (K := K)
        (changeGain := changeGain) (sameGain := sameGain) (rho := rho) current)

/-- Source-faithful local constructor: only dimension-changing branches pay
the frozen replacement power loss. -/
def BranchApplicable
    (dimensionCeiling pointThreshold populationCeiling : ℕ)
    (populationFloor : ℝ) (current : State ζ) : Prop :=
  Applicable dimensionCeiling pointThreshold populationCeiling current ∧
    populationFloor ≤ (current.points.card : ℝ)

/-- Source-faithful local constructor: only dimension-changing branches pay
the frozen replacement power loss, and the exact real population floor from
the maximal-run trace remains available to frozen source estimates. -/
def BranchOneStepConstructor
    (dimensionCeiling pointThreshold populationCeiling K : ℕ)
    (ζ changeGain sameGain rhoChange populationFloor : ℝ) : Prop :=
  ∀ current : State ζ,
    BranchApplicable dimensionCeiling pointThreshold populationCeiling
      populationFloor current →
      Nonempty (BranchControlledStepOutput (K := K)
        (changeGain := changeGain) (sameGain := sameGain)
        (rhoChange := rhoChange) current)

/-- A finite concrete trace, indexed by its first state, last state, and
number of transitions. -/
inductive Trace (K : ℕ) (ζ changeGain sameGain rho : ℝ) :
    ℕ → State ζ → State ζ → Type
  | nil (current : State ζ) :
      Trace K ζ changeGain sameGain rho 0 current current
  | snoc {length : ℕ} {first current : State ζ}
      (tracePrefix :
        Trace K ζ changeGain sameGain rho length first current)
      (step : PowerControlledStepOutput (K := K)
        (changeGain := changeGain) (sameGain := sameGain) (rho := rho) current) :
      Trace K ζ changeGain sameGain rho (length + 1) first step.next

/-- A source-faithful trace whose local control distinguishes dimension
changes from telescoped same-dimension steps. -/
inductive BranchTrace (K : ℕ)
    (ζ changeGain sameGain rhoChange : ℝ) :
    ℕ → State ζ → State ζ → Type
  | nil (current : State ζ) :
      BranchTrace K ζ changeGain sameGain rhoChange 0 current current
  | snoc {length : ℕ} {first current : State ζ}
      (tracePrefix :
        BranchTrace K ζ changeGain sameGain rhoChange length first current)
      (step : BranchControlledStepOutput (K := K)
        (changeGain := changeGain) (sameGain := sameGain)
        (rhoChange := rhoChange) current) :
      BranchTrace K ζ changeGain sameGain rhoChange (length + 1) first step.next

namespace StepOutput

variable {K : ℕ} {ζ changeGain sameGain rho : ℝ}
variable {current : State ζ}

/-- Attach the source's power-retention estimate to a raw geometric step so
that it can be inserted into a controlled trace. -/
def withPowerRetention
    (step : StepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) current)
    (hpower : (current.points.card : ℝ) ^ (1 - rho) ≤
      (step.next.points.card : ℝ)) :
    PowerControlledStepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) (rho := rho) current where
  toStepOutput := step
  points_power_retained := hpower

/-- Attach the two branch-specific source estimates to a raw geometric
step. -/
def withBranchControl
    {rhoChange : ℝ}
    (step : StepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) current)
    (hchangePower : step.kind ≠ .same →
      (current.points.card : ℝ) ^ (1 - rhoChange) ≤
        (step.next.points.card : ℝ))
    (hsameBox : step.kind = .same →
      step.boxConstant * step.convexScale ≤
        step.convexScale ^ sameRunA current.dimension ζ) :
    BranchControlledStepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) (rhoChange := rhoChange) current where
  toStepOutput := step
  change_points_power_retained := hchangePower
  same_box_absorbed := hsameBox

/-- Every branch raises the excess by the common minimum gain. -/
theorem excess_add_uniformGain_le
    (step : StepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) current) :
    current.excess + DensityIteration.Iteration.uniformGain
      changeGain sameGain ≤ step.next.excess := by
  have hchange :
      DensityIteration.Iteration.uniformGain changeGain sameGain ≤
        changeGain := min_le_left _ _
  have hsame :
      DensityIteration.Iteration.uniformGain changeGain sameGain ≤
        sameGain := min_le_right _ _
  have htransition := step.transition
  cases hkind : step.kind with
  | up =>
      simp only [hkind] at htransition
      linarith [htransition.2]
  | down =>
      simp only [hkind] at htransition
      linarith [htransition.2]
  | same =>
      simp only [hkind] at htransition
      linarith [htransition.2.1]

end StepOutput

namespace Trace

variable {K : ℕ} {ζ changeGain sameGain rho : ℝ}
variable {length : ℕ} {first last : State ζ}

/-- Population is antitone along every concrete trace. -/
theorem points_card_le_first
    (trace : Trace (K := K) (ζ := ζ) (changeGain := changeGain)
      (sameGain := sameGain) (rho := rho) length first last) :
    last.points.card ≤ first.points.card := by
  induction trace with
  | nil => exact le_rfl
  | snoc tracePrefix step ih =>
      exact step.points_card_le.trans ih

/-- Excess gains telescope along a finite partial trace. -/
theorem excess_lower_bound
    (trace : Trace (K := K) (ζ := ζ) (changeGain := changeGain)
      (sameGain := sameGain) (rho := rho)
      length first last) :
    first.excess + (length : ℝ) *
        DensityIteration.Iteration.uniformGain changeGain sameGain ≤
      last.excess := by
  induction trace with
  | nil => simp
  | @snoc n first current tracePrefix step ih =>
      calc
        first.excess + ((n + 1 : ℕ) : ℝ) *
              DensityIteration.Iteration.uniformGain changeGain sameGain =
            (first.excess + (n : ℝ) *
              DensityIteration.Iteration.uniformGain changeGain sameGain) +
                DensityIteration.Iteration.uniformGain changeGain sameGain := by
          push_cast
          ring
        _ ≤ current.excess +
              DensityIteration.Iteration.uniformGain changeGain sameGain :=
          by linarith [ih]
        _ ≤ step.next.excess := step.toStepOutput.excess_add_uniformGain_le

/-- Iterating a uniform per-step power-retention estimate multiplies its
exponent.  This is the source-faithful finite-trace population invariant. -/
theorem points_rpow_one_sub_rho_pow_length_le
    (trace : Trace (K := K) (ζ := ζ) (changeGain := changeGain)
      (sameGain := sameGain) (rho := rho) length first last)
    (hrhoOne : rho < 1) :
    (first.points.card : ℝ) ^ ((1 - rho) ^ length) ≤
      (last.points.card : ℝ) := by
  have honeSubNonneg : 0 ≤ 1 - rho := sub_nonneg.mpr hrhoOne.le
  induction trace with
  | nil => simp
  | @snoc n first current tracePrefix step ih =>
      have hraised :
          ((first.points.card : ℝ) ^ ((1 - rho) ^ n)) ^ (1 - rho) ≤
            (current.points.card : ℝ) ^ (1 - rho) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          ih honeSubNonneg
      calc
        (first.points.card : ℝ) ^ ((1 - rho) ^ (n + 1)) =
            ((first.points.card : ℝ) ^ ((1 - rho) ^ n)) ^
              (1 - rho) := by
          rw [pow_succ, Real.rpow_mul (Nat.cast_nonneg _)]
        _ ≤ (current.points.card : ℝ) ^ (1 - rho) := hraised
        _ ≤ (step.next.points.card : ℝ) := step.points_power_retained

/-- The state-level exponent obstruction supplies a single dimension ceiling
for every trace, uniformly in its length and in all step choices.  This is
the exact dimension-persistence input needed when constructing a `Package`;
in particular no finite-horizon rank recursion is necessary. -/
theorem exists_uniform_dimensionCeiling {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ dimensionCeiling : ℕ,
      ∀ {K length : ℕ} {changeGain sameGain : ℝ}
        {rho : ℝ}
        {first last : State zeta},
        Nonempty (Trace (K := K) (ζ := zeta)
          (changeGain := changeGain) (sameGain := sameGain) (rho := rho)
          length first last) →
        last.dimension ≤ dimensionCeiling := by
  obtain ⟨dimensionCeiling, hdimension⟩ :=
    State.exists_uniform_dimensionCeiling hzeta
  exact ⟨dimensionCeiling, fun _htrace ↦ hdimension _⟩

end Trace

namespace BranchTrace

variable {K : ℕ} {ζ changeGain sameGain rhoChange : ℝ}
variable {length : ℕ} {first last : State ζ}

/-- Population is antitone along a branch-controlled trace. -/
theorem points_card_le_first
    (trace : BranchTrace (K := K) (ζ := ζ)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange) length first last) :
    last.points.card ≤ first.points.card := by
  induction trace with
  | nil => exact le_rfl
  | snoc tracePrefix step ih =>
      exact step.points_card_le.trans ih

/-- Excess gains telescope along a branch-controlled trace. -/
theorem excess_lower_bound
    (trace : BranchTrace (K := K) (ζ := ζ)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange) length first last) :
    first.excess + (length : ℝ) *
        DensityIteration.Iteration.uniformGain changeGain sameGain ≤
      last.excess := by
  induction trace with
  | nil => simp
  | @snoc n first current tracePrefix step ih =>
      calc
        first.excess + ((n + 1 : ℕ) : ℝ) *
              DensityIteration.Iteration.uniformGain changeGain sameGain =
            (first.excess + (n : ℝ) *
              DensityIteration.Iteration.uniformGain changeGain sameGain) +
                DensityIteration.Iteration.uniformGain changeGain sameGain := by
          push_cast
          ring
        _ ≤ current.excess +
              DensityIteration.Iteration.uniformGain changeGain sameGain :=
          by linarith [ih]
        _ ≤ step.next.excess := step.toStepOutput.excess_add_uniformGain_le

/-- Number of dimension-changing moves in a branch-controlled trace. -/
def changeCount {length : ℕ} {first last : State ζ} :
    BranchTrace (K := K) (ζ := ζ) (changeGain := changeGain)
      (sameGain := sameGain) (rhoChange := rhoChange)
      length first last → ℕ
  | .nil _ => 0
  | .snoc tracePrefix step =>
      if step.kind = .same then changeCount tracePrefix
      else changeCount tracePrefix + 1

/-- Only dimension-changing moves are charged to `changeGain`; positive
same-dimension gains ensure that the intervening moves cannot undo this
accounting. -/
theorem change_excess_lower_bound
    (trace : BranchTrace (K := K) (ζ := ζ)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange) length first last)
    (hsameGain : 0 ≤ sameGain) :
    first.excess + (changeCount trace : ℝ) * changeGain ≤ last.excess := by
  induction trace with
  | nil => simp [changeCount]
  | @snoc n first current tracePrefix step ih =>
      by_cases hsame : step.kind = .same
      · have htransition := step.transition
        simp only [hsame] at htransition
        simp only [changeCount, hsame, if_pos]
        exact ih.trans (by linarith [htransition.2.1])
      · have htransition := step.transition
        cases hkind : step.kind with
        | up =>
            simp only [hkind] at htransition
            simp [changeCount, hkind]
            push_cast
            linarith [ih, htransition.2]
        | down =>
            simp only [hkind] at htransition
            simp [changeCount, hkind]
            push_cast
            linarith [ih, htransition.2]
        | same => exact (hsame hkind).elim

/-- A fixed Archimedean budget bounds the number of changing moves in every
trace, independently of the (possibly very long) same-dimension runs. -/
theorem changeCount_lt
    (trace : BranchTrace (K := K) (ζ := ζ)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange) length first last)
    (hchangeGain : 0 < changeGain) (hsameGain : 0 ≤ sameGain)
    {changeSteps : ℕ}
    (hbudget : 1 ≤ (changeSteps : ℝ) * changeGain) :
    changeCount trace < changeSteps := by
  have hexcess := trace.change_excess_lower_bound hsameGain
  have hstrict : (changeCount trace : ℝ) * changeGain < 1 := by
    have hlast : last.excess < 1 := by
      have hbox := boxExponent_pos last.dimension_pos
      linarith [last.totalExponent_lt_one, last.zeta_pos]
    linarith [first.excess_nonneg]
  by_contra hnot
  have hle : changeSteps ≤ changeCount trace := Nat.le_of_not_gt hnot
  have hcast : (changeSteps : ℝ) ≤ changeCount trace := by exact_mod_cast hle
  have hmul := mul_le_mul_of_nonneg_right hcast hchangeGain.le
  linarith

/-- The state-level exponent obstruction also supplies the dimension ceiling
for branch-controlled traces. -/
theorem exists_uniform_dimensionCeiling {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ dimensionCeiling : ℕ,
      ∀ {K length : ℕ} {changeGain sameGain rhoChange : ℝ}
        {first last : State zeta},
        Nonempty (BranchTrace (K := K) (ζ := zeta)
          (changeGain := changeGain) (sameGain := sameGain)
          (rhoChange := rhoChange) length first last) →
        last.dimension ≤ dimensionCeiling := by
  obtain ⟨dimensionCeiling, hdimension⟩ :=
    State.exists_uniform_dimensionCeiling hzeta
  exact ⟨dimensionCeiling, fun _htrace ↦ hdimension _⟩

end BranchTrace

/-! ### The maximal same-dimension `U,V` persistence calculation -/

/-- Numerical input accumulated along one maximal same-dimension run.

`U` is the product of the convex scales and `V` the product of the
structural ratios.  The hypotheses `point_product` and `box_product` are
the telescoped forms of the two separate estimates in `StepOutput` after
the fixed constants have been absorbed. -/
structure SameDimensionPersistenceInput where
  U : ℝ
  V : ℝ
  boxStart : ℝ
  pointsStart : ℝ
  pointsEnd : ℝ
  K : ℕ
  a : ℝ
  q : ℝ
  densityExponent : ℝ
  lambda : ℝ
  U_pos : 0 < U
  U_le_one : U ≤ 1
  V_pos : 0 < V
  V_le_one : V ≤ 1
  boxStart_pos : 0 < boxStart
  pointsStart_pos : 0 < pointsStart
  densityExponent_pos : 0 < densityExponent
  lambda_nonneg : 0 ≤ lambda
  q_le_a_mul_lambda : q ≤ a * lambda
  one_le_K_mul_lambda : 1 ≤ (K : ℝ) * lambda
  lambda_lt_densityExponent : lambda < densityExponent
  start_density :
    boxStart ^ densityExponent < pointsStart
  point_product :
    U ^ q * V * pointsStart ≤ pointsEnd
  box_product :
    1 ≤ U ^ a * V ^ K * boxStart

namespace SameDimensionPersistenceInput

/-- The box obstruction converts the two accumulated scale products into
the exact lower bound used in equations (24)--(25) of Pham--Zakharov. -/
theorem box_rpow_neg_lambda_le_product
    (X : SameDimensionPersistenceInput) :
    X.boxStart ^ (-X.lambda) ≤ X.U ^ X.q * X.V := by
  have hlogU : Real.log X.U ≤ 0 :=
    Real.log_nonpos X.U_pos.le X.U_le_one
  have hlogV : Real.log X.V ≤ 0 :=
    Real.log_nonpos X.V_pos.le X.V_le_one
  have hUcompare :
      (X.a * X.lambda) * Real.log X.U ≤ X.q * Real.log X.U :=
    mul_le_mul_of_nonpos_right X.q_le_a_mul_lambda hlogU
  have hVcompare :
      ((X.K : ℝ) * X.lambda) * Real.log X.V ≤ Real.log X.V := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonpos_right X.one_le_K_mul_lambda hlogV)
  have hboxLog :
      0 ≤ X.a * Real.log X.U + (X.K : ℝ) * Real.log X.V +
        Real.log X.boxStart := by
    have hlogNonneg := Real.log_nonneg X.box_product
    rw [Real.log_mul
        (mul_pos (Real.rpow_pos_of_pos X.U_pos _)
          (pow_pos X.V_pos X.K)).ne' X.boxStart_pos.ne',
      Real.log_mul (Real.rpow_pos_of_pos X.U_pos _).ne'
        (pow_pos X.V_pos X.K).ne',
      Real.log_rpow X.U_pos, Real.log_pow] at hlogNonneg
    simpa [mul_assoc, add_assoc] using hlogNonneg
  have hscaled :
      0 ≤ X.lambda *
        (X.a * Real.log X.U + (X.K : ℝ) * Real.log X.V +
          Real.log X.boxStart) :=
    mul_nonneg X.lambda_nonneg hboxLog
  have hlogGoal :
      Real.log (X.boxStart ^ (-X.lambda)) ≤
        Real.log (X.U ^ X.q * X.V) := by
    rw [Real.log_rpow X.boxStart_pos,
      Real.log_mul (Real.rpow_pos_of_pos X.U_pos _).ne' X.V_pos.ne',
      Real.log_rpow X.U_pos]
    nlinarith
  by_contra h
  have hreverse : X.U ^ X.q * X.V <
      X.boxStart ^ (-X.lambda) := lt_of_not_ge h
  have hlogReverse := Real.log_lt_log
    (mul_pos (Real.rpow_pos_of_pos X.U_pos _) X.V_pos) hreverse
  linarith

/-- Closing a same-dimension run costs one fixed power `σ`, rather than one
loss per step.  This is the named bridge used to prove
`Package.population_persists`. -/
theorem pointsStart_rpow_sigma_le_pointsEnd
    (X : SameDimensionPersistenceInput) :
    X.pointsStart ^
        (1 - X.lambda / X.densityExponent) ≤ X.pointsEnd := by
  have hproduct := X.box_rpow_neg_lambda_le_product
  have hlogDensity :=
    Real.log_lt_log (Real.rpow_pos_of_pos X.boxStart_pos _)
      X.start_density
  rw [Real.log_rpow X.boxStart_pos] at hlogDensity
  have hratio : 0 ≤ X.lambda / X.densityExponent :=
    div_nonneg X.lambda_nonneg X.densityExponent_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hlogDensity.le hratio
  have hcancel :
      (X.lambda / X.densityExponent) * X.densityExponent = X.lambda := by
    exact div_mul_cancel₀ X.lambda X.densityExponent_pos.ne'
  have hpowerTransfer :
      X.pointsStart ^
          (1 - X.lambda / X.densityExponent) ≤
        X.boxStart ^ (-X.lambda) * X.pointsStart := by
    have hscaled' :
        X.lambda * Real.log X.boxStart ≤
          (X.lambda / X.densityExponent) *
            Real.log X.pointsStart := by
      calc
        X.lambda * Real.log X.boxStart =
            ((X.lambda / X.densityExponent) * X.densityExponent) *
              Real.log X.boxStart := by rw [hcancel]
        _ = (X.lambda / X.densityExponent) *
              (X.densityExponent * Real.log X.boxStart) := by ring
        _ ≤ (X.lambda / X.densityExponent) *
              Real.log X.pointsStart := hscaled
    have hlogGoal :
        Real.log (X.pointsStart ^
            (1 - X.lambda / X.densityExponent)) ≤
          Real.log (X.boxStart ^ (-X.lambda) *
            X.pointsStart) := by
      rw [Real.log_rpow X.pointsStart_pos,
        Real.log_mul (Real.rpow_pos_of_pos X.boxStart_pos _).ne'
          X.pointsStart_pos.ne',
        Real.log_rpow X.boxStart_pos]
      nlinarith [hscaled']
    by_contra h
    have hreverse :
        X.boxStart ^ (-X.lambda) * X.pointsStart <
          X.pointsStart ^
            (1 - X.lambda / X.densityExponent) := lt_of_not_ge h
    have hlogReverse := Real.log_lt_log
      (mul_pos (Real.rpow_pos_of_pos X.boxStart_pos _) X.pointsStart_pos)
      hreverse
    linarith
  calc
    X.pointsStart ^
        (1 - X.lambda / X.densityExponent)
        ≤ X.boxStart ^ (-X.lambda) * X.pointsStart := hpowerTransfer
    _ ≤ (X.U ^ X.q * X.V) * X.pointsStart :=
      mul_le_mul_of_nonneg_right hproduct X.pointsStart_pos.le
    _ ≤ X.pointsEnd := X.point_product

end SameDimensionPersistenceInput

/-! ### Freezing the finite horizon

The analytic part of the one-step argument supplies two positive gains.  No
further geometric input is needed to choose a horizon which exceeds the
remaining excess budget.  Keeping this choice here prevents every concrete
assembly from repeating the same Archimedean argument. -/

/-- Positive gains determine a finite horizon whose accumulated uniform gain
already exceeds the remaining excess budget of the initial state. -/
theorem exists_steps_exponent_budget {ζ changeGain sameGain : ℝ}
    (initial : State ζ) (hchange : 0 < changeGain)
    (hsame : 0 < sameGain) :
    ∃ steps : ℕ,
      1 < initial.excess + (steps : ℝ) *
        DensityIteration.Iteration.uniformGain changeGain sameGain := by
  let gain := DensityIteration.Iteration.uniformGain changeGain sameGain
  have hgain : 0 < gain := lt_min hchange hsame
  obtain ⟨steps, hsteps⟩ := exists_nat_gt ((1 - initial.excess) / gain)
  refine ⟨steps, ?_⟩
  have hbudget : 1 - initial.excess < (steps : ℝ) * gain := by
    exact (div_lt_iff₀ hgain).mp hsteps
  dsimp [gain] at hbudget ⊢
  linarith

/-- A positive uniform gain admits a near-minimal integer horizon.  The
upper bound is the quantitative ingredient needed when the per-step power
loss is frozen only after the initial population has been seen. -/
theorem exists_steps_unit_budget_with_upper {gain : ℝ} (hgain : 0 < gain) :
    ∃ steps : ℕ,
      1 < (steps : ℝ) * gain ∧
        (steps : ℝ) * gain ≤ 1 + gain := by
  let steps : ℕ := Nat.floor (1 / gain) + 1
  have hinvNonneg : 0 ≤ 1 / gain := by positivity
  have hlower : 1 / gain < (steps : ℝ) := by
    dsimp only [steps]
    push_cast
    exact Nat.lt_floor_add_one (1 / gain)
  have hupper : (steps : ℝ) ≤ 1 / gain + 1 := by
    dsimp only [steps]
    push_cast
    linarith [Nat.floor_le hinvNonneg]
  refine ⟨steps, ?_, ?_⟩
  · have hmul := mul_lt_mul_of_pos_right hlower hgain
    rw [div_mul_cancel₀ 1 hgain.ne'] at hmul
    exact hmul
  · have hmul := mul_le_mul_of_nonneg_right hupper hgain.le
    rw [add_mul, div_mul_cancel₀ 1 hgain.ne', one_mul] at hmul
    linarith

/-- Bernoulli's inequality keeps at least a square-root exponent whenever
the accumulated power loss over the frozen horizon is at most one half. -/
theorem one_half_le_one_sub_rho_pow
    {steps : ℕ} {rho : ℝ} (hrhoOne : rho ≤ 1)
    (hbudget : (steps : ℝ) * rho ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ (1 - rho) ^ steps := by
  have hbernoulli :
      1 + (steps : ℝ) * (-rho) ≤ (1 + (-rho)) ^ steps :=
    one_add_mul_le_pow (by linarith) steps
  have hbernoulli' :
      1 - (steps : ℝ) * rho ≤ (1 - rho) ^ steps := by
    simpa only [mul_neg, sub_eq_add_neg] using hbernoulli
  nlinarith

/-- Freeze both a contradiction horizon and a compatible global per-step
power loss from an initial-dependent positive gain. -/
theorem exists_steps_rho_unit_budget
    {gain : ℝ} (hgain : 0 < gain) :
    ∃ steps : ℕ, ∃ rho : ℝ,
      1 < (steps : ℝ) * gain ∧
      0 < rho ∧ rho < 1 ∧
      (1 / 2 : ℝ) ≤ (1 - rho) ^ steps := by
  obtain ⟨steps, hlower, hupper⟩ :=
    exists_steps_unit_budget_with_upper hgain
  let rho : ℝ := gain / (2 * (1 + gain))
  have honeGain : 0 < 1 + gain := by linarith
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  have hrhoOne : rho < 1 := by
    dsimp only [rho]
    rw [div_lt_one (mul_pos (by norm_num) honeGain)]
    linarith
  have hstepsRho : (steps : ℝ) * rho ≤ 1 / 2 := by
    dsimp only [rho]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos (by norm_num) honeGain)).2
    nlinarith
  exact ⟨steps, rho, hlower, hrho, hrhoOne,
    one_half_le_one_sub_rho_pow hrhoOne.le hstepsRho⟩

/-- A private threshold bounded by the square root of the frozen initial
population satisfies the package budget for any compounded exponent at
least one half. -/
theorem initial_population_budget_of_le_sqrt
    {pointThreshold pointCard steps : ℕ} {rho : ℝ}
    (hpointCard : 1 ≤ pointCard)
    (hexponent : (1 / 2 : ℝ) ≤ (1 - rho) ^ steps)
    (hthreshold : (pointThreshold : ℝ) ≤ Real.sqrt pointCard) :
    (pointThreshold : ℝ) ≤
      (pointCard : ℝ) ^ ((1 - rho) ^ steps) := by
  apply hthreshold.trans
  rw [Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hpointCard
  · norm_num at hexponent ⊢
    exact hexponent

/-- Source-facing combination of the frozen horizon, compatible power loss,
and square-root population budget.  This is the exact numerical package
needed after the two gains and the private point threshold have been chosen
from the actual initial counterexample. -/
theorem exists_frozen_horizon_power_budget_of_le_sqrt
    {changeGain sameGain : ℝ}
    (hchangeGain : 0 < changeGain) (hsameGain : 0 < sameGain)
    {pointThreshold pointCard : ℕ} (hpointCard : 1 ≤ pointCard)
    (hthreshold : (pointThreshold : ℝ) ≤ Real.sqrt pointCard) :
    ∃ steps : ℕ, ∃ rho : ℝ,
      0 < rho ∧ rho < 1 ∧
      1 < (steps : ℝ) *
        DensityIteration.Iteration.uniformGain changeGain sameGain ∧
      (pointThreshold : ℝ) ≤
        (pointCard : ℝ) ^ ((1 - rho) ^ steps) := by
  have hgain : 0 <
      DensityIteration.Iteration.uniformGain changeGain sameGain := by
    exact lt_min hchangeGain hsameGain
  obtain ⟨steps, rho, hsteps, hrho, hrhoOne, hexponent⟩ :=
    exists_steps_rho_unit_budget hgain
  exact ⟨steps, rho, hrho, hrhoOne, hsteps,
    initial_population_budget_of_le_sqrt hpointCard hexponent hthreshold⟩

/-- For a fixed finite horizon and a genuine power-retention exponent, one
public cardinality threshold absorbs all population loss.  This is the
threshold-selection lemma used when constructing `initial_population_budget`
in a concrete package. -/
theorem exists_initial_population_threshold
    (pointThreshold steps : ℕ) {rho : ℝ} (hrhoOne : rho < 1) :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ n : ℕ, M ≤ n →
        (pointThreshold : ℝ) ≤
          (n : ℝ) ^ ((1 - rho) ^ steps) := by
  have hexponent : 0 < (1 - rho) ^ steps :=
    pow_pos (sub_pos.mpr hrhoOne) _
  have htendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ (n : ℝ) ^ ((1 - rho) ^ steps))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexponent).comp tendsto_natCast_atTop_atTop
  have heventually : ∀ᶠ n : ℕ in Filter.atTop,
      (pointThreshold : ℝ) ≤
        (n : ℝ) ^ ((1 - rho) ^ steps) :=
    htendsto.eventually (Filter.eventually_ge_atTop (pointThreshold : ℝ))
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp heventually
  refine ⟨max 2 M₀, le_max_left _ _, ?_⟩
  intro n hn
  exact hM₀ n ((le_max_right 2 M₀).trans hn)

/-- A positive critical exponent converts a sufficiently large public box
threshold into any fixed private population threshold.  This is the exact
bridge used after negating the final box bound: strict supercriticality
forces the counterexample set itself to be large enough for the one-step
constructor. -/
theorem exists_box_threshold_for_supercritical_population
    (pointThreshold : ℕ) {criticalExponent : ℝ}
    (hcriticalExponent : 0 < criticalExponent) :
    ∃ boxThreshold : ℕ, 2 ≤ boxThreshold ∧
      ∀ {boxCard pointCard : ℕ}, boxThreshold ≤ boxCard →
        (boxCard : ℝ) ^ criticalExponent < (pointCard : ℝ) →
        pointThreshold ≤ pointCard := by
  have heventually : ∀ᶠ boxCard : ℕ in Filter.atTop,
      (pointThreshold : ℝ) ≤ (boxCard : ℝ) ^ criticalExponent := by
    have htendsto : Filter.Tendsto
        (fun boxCard : ℕ ↦ (boxCard : ℝ) ^ criticalExponent)
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hcriticalExponent).comp
        tendsto_natCast_atTop_atTop
    exact htendsto.eventually
      (Filter.eventually_ge_atTop (pointThreshold : ℝ))
  obtain ⟨growthThreshold, hgrowth⟩ := Filter.eventually_atTop.1 heventually
  let boxThreshold := max 2 growthThreshold
  refine ⟨boxThreshold, le_max_left _ _, ?_⟩
  intro boxCard pointCard hboxLarge hcritical
  have hgrowthLarge : growthThreshold ≤ boxCard :=
    (le_max_right 2 growthThreshold).trans hboxLarge
  have hpointCast : (pointThreshold : ℝ) < (pointCard : ℝ) :=
    (hgrowth boxCard hgrowthLarge).trans_lt hcritical
  exact_mod_cast hpointCast.le

/-- The public box threshold can therefore be chosen so that every strict
counterexample supplies the initial power budget required by `Package` over
the entire frozen iteration horizon. -/
theorem exists_box_threshold_initial_population_budget
    (pointThreshold steps : ℕ) {criticalExponent rho : ℝ}
    (hcriticalExponent : 0 < criticalExponent) (hrhoOne : rho < 1) :
    ∃ boxThreshold : ℕ, 2 ≤ boxThreshold ∧
      ∀ {boxCard pointCard : ℕ}, boxThreshold ≤ boxCard →
        (boxCard : ℝ) ^ criticalExponent < (pointCard : ℝ) →
        (pointThreshold : ℝ) ≤
          (pointCard : ℝ) ^ ((1 - rho) ^ steps) := by
  obtain ⟨initialThreshold, _hinitialThresholdTwo, hinitialBudget⟩ :=
    exists_initial_population_threshold pointThreshold steps hrhoOne
  obtain ⟨boxThreshold, hboxThresholdTwo, hpopulation⟩ :=
    exists_box_threshold_for_supercritical_population initialThreshold
      hcriticalExponent
  refine ⟨boxThreshold, hboxThresholdTwo, ?_⟩
  intro boxCard pointCard hboxLarge hcritical
  exact hinitialBudget pointCard
    (hpopulation hboxLarge hcritical)

/-- All parameters frozen after choosing the initial counterexample.

The package stores a state-level dimension envelope and one initial power
budget.  Population persistence for every trace prefix is then a theorem,
not an independently supplied field. -/
structure LegacyPackage {ζ : ℝ} (initial : State ζ) where
  dimensionCeiling : ℕ
  pointThreshold : ℕ
  steps : ℕ
  K : ℕ
  changeGain : ℝ
  sameGain : ℝ
  rho : ℝ
  changeGain_pos : 0 < changeGain
  sameGain_pos : 0 < sameGain
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  exponent_budget :
    1 < initial.excess + (steps : ℝ) *
      DensityIteration.Iteration.uniformGain changeGain sameGain
  /-- The globally proved dimension envelope for every trace prefix. -/
  dimension_persists :
    ∀ {length : ℕ} {last : State ζ}, length ≤ steps →
      Nonempty (Trace (K := K) (ζ := ζ) (changeGain := changeGain)
        (sameGain := sameGain) (rho := rho)
        length initial last) →
      last.dimension ≤ dimensionCeiling
  /-- The public initial-cardinality threshold absorbs the finite product of
  per-step power losses over the frozen horizon. -/
  initial_population_budget :
    (pointThreshold : ℝ) ≤
      (initial.points.card : ℝ) ^ ((1 - rho) ^ steps)
  oneStep : OneStepConstructor dimensionCeiling pointThreshold
    initial.points.card K ζ
    changeGain sameGain rho

namespace LegacyPackage

variable {ζ : ℝ} {initial : State ζ}

/-- The controlled trace invariant and the single initial power budget imply
the stopping exclusion for every prefix of the frozen horizon. -/
theorem population_persists
    (P : LegacyPackage initial) {length : ℕ} {last : State ζ}
    (hlength : length ≤ P.steps)
    (trace : Trace (K := P.K) (ζ := ζ) (changeGain := P.changeGain)
      (sameGain := P.sameGain) (rho := P.rho) length initial last) :
    P.pointThreshold ≤ last.points.card := by
  have honeSubNonneg : 0 ≤ 1 - P.rho := sub_nonneg.mpr P.rho_lt_one.le
  have honeSubOne : 1 - P.rho ≤ 1 := by linarith [P.rho_pos]
  have hpowExponent : (1 - P.rho) ^ P.steps ≤ (1 - P.rho) ^ length :=
    pow_le_pow_of_le_one honeSubNonneg honeSubOne hlength
  have hinitialOne : (1 : ℝ) ≤ (initial.points.card : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr initial.points_nonempty.card_pos
  have hexponentMono :
      (initial.points.card : ℝ) ^ ((1 - P.rho) ^ P.steps) ≤
        (initial.points.card : ℝ) ^ ((1 - P.rho) ^ length) :=
    Real.rpow_le_rpow_of_exponent_le hinitialOne hpowExponent
  have htrace := trace.points_rpow_one_sub_rho_pow_length_le
    P.rho_lt_one
  have hcast : (P.pointThreshold : ℝ) ≤ (last.points.card : ℝ) :=
    P.initial_population_budget.trans (hexponentMono.trans htrace)
  exact_mod_cast hcast

/-- Every prefix within the frozen horizon retains enough points for the
next analytic step. -/
theorem pointThreshold_le_of_trace
    (P : LegacyPackage initial) {length : ℕ} {last : State ζ}
    (hlength : length ≤ P.steps)
    (trace : Trace (K := P.K) (ζ := ζ) (changeGain := P.changeGain)
      (sameGain := P.sameGain) (rho := P.rho)
      length initial last) :
    P.pointThreshold ≤ last.points.card := by
  exact P.population_persists hlength trace

/-- Every trace prefix is applicable; this is the global persistence lemma
which replaces the locally circular `next.minimum_card_le` requirement. -/
theorem applicable_of_trace
    (P : LegacyPackage initial) {length : ℕ} {last : State ζ}
    (hlength : length ≤ P.steps)
    (trace : Trace (K := P.K) (ζ := ζ) (changeGain := P.changeGain)
      (sameGain := P.sameGain) (rho := P.rho)
      length initial last) :
    Applicable P.dimensionCeiling P.pointThreshold initial.points.card last := by
  exact ⟨P.dimension_persists hlength ⟨trace⟩,
    P.pointThreshold_le_of_trace hlength trace,
    trace.points_card_le_first⟩

/-- The partial one-step theorem constructs a concrete trace of every length
up to the frozen horizon. -/
theorem exists_trace (P : LegacyPackage initial) :
    ∀ length : ℕ, length ≤ P.steps →
      ∃ last : State ζ, Nonempty
        (Trace (K := P.K) (ζ := ζ) (changeGain := P.changeGain)
          (sameGain := P.sameGain) (rho := P.rho)
          length initial last) := by
  intro length hlength
  induction length with
  | zero => exact ⟨initial, ⟨Trace.nil initial⟩⟩
  | succ length ih =>
      obtain ⟨current, ⟨tracePrefix⟩⟩ := ih (by omega)
      have happlicable := P.applicable_of_trace (by omega) tracePrefix
      let step := Classical.choice (P.oneStep current happlicable)
      exact ⟨step.next, ⟨Trace.snoc tracePrefix step⟩⟩

/-- The global finite-horizon contradiction. -/
theorem false_of_partialOneStep (P : LegacyPackage initial) : False := by
  obtain ⟨last, ⟨trace⟩⟩ := P.exists_trace P.steps (le_refl _)
  have hlower := trace.excess_lower_bound
  have hupper := last.excess_le_one
  linarith [P.exponent_budget]

end LegacyPackage

/-- The initial partial state attached to an actual strict counterexample. -/
noncomputable def initialState {d : ℕ} {ζ : ℝ}
    (hd : 0 < d) (hζ : 0 < ζ)
    (B : IntegerBox d) (A : Finset (BoxPoint d))
    (hA : A ⊆ B.carrier) (hNA : IsBoxNonaveraging A)
    (hBtwo : 2 ≤ B.carrier.card)
    (hcritical :
      (B.carrier.card : ℝ) ^ (boxExponent d + ζ) < (A.card : ℝ)) :
    State ζ where
  dimension := d
  dimension_pos := hd
  zeta_pos := hζ
  box := B
  points := A
  points_subset_box := hA
  nonaveraging := hNA
  points_nonempty := by
    have hBpos : 0 < (B.carrier.card : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hBtwo)
    have hpowpos :
        0 < (B.carrier.card : ℝ) ^ (boxExponent d + ζ) :=
      Real.rpow_pos_of_pos hBpos _
    have hApos : 0 < (A.card : ℝ) := hpowpos.trans hcritical
    exact Finset.card_pos.mp (by exact_mod_cast hApos)
  excess := 0
  excess_nonneg := le_rfl
  density_certificate := by
    have hBpos : 0 < (B.carrier.card : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hBtwo)
    have hpowpos :
        0 < (B.carrier.card : ℝ) ^ (boxExponent d + ζ) :=
      Real.rpow_pos_of_pos hBpos _
    have hlog := Real.log_lt_log hpowpos hcritical
    rw [Real.log_rpow hBpos] at hlog
    simpa [mul_comm] using hlog

end Partial

/-- The exact constructor proposition required by the final box theorem.

This named proposition is the output boundary for the composition of CFP,
irreducible replacement, intersection, convex density, and the global
dimension/population bookkeeping.  It freezes the package only after an
actual strict counterexample has been supplied. -/
def LegacyOneStepPackageStatement : Prop :=
  ∀ d : ℕ, ∀ hd : 0 < d, ∀ ζ : ℝ, ∀ hζ : 0 < ζ,
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ (B : IntegerBox d) (A : Finset (BoxPoint d))
        (hA : A ⊆ B.carrier) (hNA : IsBoxNonaveraging A)
        (_hlarge : M ≤ B.carrier.card)
        (hBtwo : 2 ≤ B.carrier.card)
        (hcritical :
          (B.carrier.card : ℝ) ^ (boxExponent d + ζ) <
            (A.card : ℝ)),
        let initial := @Partial.initialState d ζ hd hζ B A hA hNA
          hBtwo hcritical
        Nonempty (Partial.LegacyPackage initial)

/-- **Final Pham--Zakharov box theorem from the concrete partial one-step
construction.**

For fixed `d, ζ`, the hypothesis first chooses a public box threshold.  Only
after an actual strict counterexample is supplied does it freeze the initial
population and return the finite-horizon partial-step package.  The package
contains no assumed prefix-persistence proposition:
`Partial.Package.population_persists` derives it from controlled steps and
the frozen initial power budget before constructing the next step. -/
theorem legacyPzBoxBound_of_oneStep
    (oneStep : LegacyOneStepPackageStatement) :
    PZBoxBound := by
  intro d hd ζ hζ
  obtain ⟨M, hMtwo, hconstruct⟩ := oneStep d hd ζ hζ
  refine ⟨M, ?_⟩
  intro B A hA hNA hlarge
  by_contra hbound
  have hcritical :
      (B.carrier.card : ℝ) ^ (boxExponent d + ζ) < (A.card : ℝ) :=
    lt_of_not_ge hbound
  let initial := @Partial.initialState d ζ hd hζ B A hA hNA
    (hMtwo.trans hlarge) hcritical
  let P : Partial.LegacyPackage initial :=
    Classical.choice
      (hconstruct B A hA hNA hlarge (hMtwo.trans hlarge) hcritical)
  exact P.false_of_partialOneStep

end

end Erdos186.PZ.FinalIteration

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

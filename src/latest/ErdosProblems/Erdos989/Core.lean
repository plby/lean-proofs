/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.Ring

/-!
# Core definitions for Erdős problem 989

This module contains the elementary formal framework shared by the lower- and
upper-bound developments.  The informal maximum over disk centers is expanded
into center quantifiers, since local finiteness does not imply that the errors
are bounded as the center varies.
-/

namespace Erdos989

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- An infinite, locally finite planar point set.

Local finiteness is stated using compact sets, so in particular every closed
disk contains only finitely many points of `A`. -/
def IsAdmissible (A : Set Plane) : Prop :=
  A.Infinite ∧ ∀ K : Set Plane, IsCompact K → (A ∩ K).Finite

namespace IsAdmissible

theorem infinite {A : Set Plane} (hA : IsAdmissible A) : A.Infinite :=
  hA.1

theorem inter_compact_finite {A : Set Plane} (hA : IsAdmissible A)
    {K : Set Plane} (hK : IsCompact K) : (A ∩ K).Finite :=
  hA.2 K hK

/-- An admissible point set has finite intersection with every closed disk. -/
theorem inter_closedBall_finite {A : Set Plane} (hA : IsAdmissible A)
    (x : Plane) (r : ℝ) : (A ∩ Metric.closedBall x r).Finite :=
  hA.inter_compact_finite (ProperSpace.isCompact_closedBall x r)

end IsAdmissible

/-- The number of points of `A` in the closed disk with center `x` and radius
`r`.  For admissible sets, `diskCount_eq_toFinset_card` below shows explicitly
that this total `ncard` is the cardinality of a finite set. -/
noncomputable def diskCount (A : Set Plane) (x : Plane) (r : ℝ) : ℕ :=
  (A ∩ Metric.closedBall x r).ncard

/-- Absolute discrepancy between the number of points in a closed disk and
the Euclidean area `π r²` of that disk. -/
noncomputable def diskError (A : Set Plane) (x : Plane) (r : ℝ) : ℝ :=
  |(diskCount A x r : ℝ) - Real.pi * r ^ 2|

theorem diskCount_eq_toFinset_card {A : Set Plane} (hA : IsAdmissible A)
    (x : Plane) (r : ℝ) :
    diskCount A x r = (hA.inter_closedBall_finite x r).toFinset.card := by
  exact Set.ncard_eq_toFinset_card _ (hA.inter_closedBall_finite x r)

theorem diskError_nonneg (A : Set Plane) (x : Plane) (r : ℝ) :
    0 ≤ diskError A x r :=
  abs_nonneg _

/-- A closed disk in the plane has exactly area `π r²`.  The hypothesis
`0 ≤ r` is necessary because Mathlib's ball-volume formula uses the positive
part of the radius. -/
theorem volume_closedBall_plane (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall x r) = Real.pi * r ^ 2 := by
  rw [Measure.real, EuclideanSpace.volume_closedBall_fin_two]
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr, Real.pi_nonneg]
  ring

/-- The universal lower-growth conclusion for one point set, with the
informal maximum expanded as existence of a center for every large radius. -/
def LowerGrowth (A : Set Plane) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, ∀ r ≥ R, ∃ x : Plane,
    c * Real.sqrt r ≤ diskError A x r

/-- The upper-growth conclusion for one point set, with the informal maximum
expanded as a bound uniform over every center. -/
def UpperGrowth (A : Set Plane) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, ∀ r ≥ R, ∀ x : Plane,
    diskError A x r ≤ C * Real.sqrt (r * Real.log r)

/-- The literal universal fixed-radius square-root lower estimate appearing in
the problem-page note. -/
def HasUniversalSqrtLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, ∀ A : Set Plane, IsAdmissible A →
    ∀ r ≥ R, ∃ x : Plane, c * Real.sqrt r ≤ diskError A x r

/-- Beck's fixed-radius upper construction.  The admissible set may depend on
the radius, while the constants are absolute and the estimate is uniform over
all centers at that radius. -/
def HasSqrtLogUpperConstruction : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ, ∀ r ≥ R, ∃ A : Set Plane,
    IsAdmissible A ∧ ∀ x : Plane,
      diskError A x r ≤ C * Real.sqrt (r * Real.log r)

/-- The literal global upper statement in the problem-page note: one
admissible set works at every sufficiently large radius.  This is strictly
stronger in its quantifier order than `HasSqrtLogUpperConstruction`. -/
def HasGlobalSqrtLogUpperBound : Prop :=
  ∃ A : Set Plane, IsAdmissible A ∧ ∃ C : ℝ, 0 < C ∧ ∃ R : ℝ,
    ∀ r ≥ R, ∀ x : Plane,
      diskError A x r ≤ C * Real.sqrt (r * Real.log r)

/-- The literal quantitative resolution requested in the problem-page note:
the universal prescribed-radius square-root lower bound together with one
global point set satisfying the square-root-log upper bound. -/
def Resolution : Prop :=
  HasUniversalSqrtLowerBound ∧ HasGlobalSqrtLogUpperBound

/-! ## The source-correct fixed-scale conclusion

The fixed-scale construction has quantifier order `∀ r, ∃ A`.  The next
small logical example records, inside Lean, why this order cannot simply be
rewritten as `∃ A, ∀ r`.  It does not claim that the disk-specific global
statement is false; it proves that the proposed interchange is not a valid
logical inference.
-/

/-- There is a relation having a witness separately at every scale but no
single witness that works at every scale. -/
def HasFixedScaleButNoGlobalWitness : Prop :=
  ∃ P : ℕ → ℕ → Prop,
    (∀ scale : ℕ, ∃ witness : ℕ, P witness scale) ∧
      ¬ ∃ witness : ℕ, ∀ scale : ℕ, P witness scale

/-- Equality of natural numbers is the canonical counterexample to swapping
`∀ scale, ∃ witness` into `∃ witness, ∀ scale`. -/
theorem hasFixedScaleButNoGlobalWitness : HasFixedScaleButNoGlobalWitness := by
  refine ⟨fun witness scale : ℕ ↦ witness = scale, ?_, ?_⟩
  · exact fun scale ↦ ⟨scale, rfl⟩
  · rintro ⟨witness, h⟩
    have hzero : witness = 0 := h 0
    have hone : witness = 1 := h 1
    exact Nat.zero_ne_one (hzero.symm.trans hone)

/-- The strongest unconditional conclusion formalized here: Beck's
source-correct fixed-scale upper construction, together with the checked
logical counterexample preventing an unjustified quantifier swap. -/
def SourceCorrectFixedScaleResolution : Prop :=
  HasSqrtLogUpperConstruction ∧ HasFixedScaleButNoGlobalWitness

/-- A single global upper-bound witness supplies, in particular, a witness at
each prescribed scale. -/
theorem fixedScaleUpper_of_global (h : HasGlobalSqrtLogUpperBound) :
    HasSqrtLogUpperConstruction := by
  rcases h with ⟨A, hA, C, hC, R, hbound⟩
  exact ⟨C, hC, R, fun r hr ↦ ⟨A, hA, hbound r hr⟩⟩

theorem lowerGrowth_of_universal
    (h : HasUniversalSqrtLowerBound) {A : Set Plane} (hA : IsAdmissible A) :
    LowerGrowth A := by
  rcases h with ⟨c, hc, R, hbound⟩
  exact ⟨c, hc, R, hbound A hA⟩

/-- The lower-growth estimate implies that disk errors exceed every prescribed
real threshold. -/
theorem diskError_unbounded_of_lowerGrowth {A : Set Plane} (hA : LowerGrowth A) :
    ∀ T : ℝ, ∃ r : ℝ, ∃ x : Plane, T < diskError A x r := by
  rcases hA with ⟨c, hc, R, hlower⟩
  intro T
  have hsqrt : ∀ᶠ r : ℝ in atTop, T / c < Real.sqrt r :=
    Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop (T / c))
  have hboth : ∀ᶠ r : ℝ in atTop, T / c < Real.sqrt r ∧ R ≤ r :=
    hsqrt.and (eventually_ge_atTop R)
  rcases hboth.exists with ⟨r, hr, hR⟩
  rcases hlower r hR with ⟨x, hx⟩
  refine ⟨r, x, ?_⟩
  have hT : T < c * Real.sqrt r := by
    rw [div_lt_iff₀ hc] at hr
    simpa [mul_comm] using hr
  exact hT.trans_le hx

theorem all_diskErrors_unbounded_of_universal
    (h : HasUniversalSqrtLowerBound) (A : Set Plane) (hA : IsAdmissible A) :
    ∀ T : ℝ, ∃ r : ℝ, ∃ x : Plane, T < diskError A x r :=
  diskError_unbounded_of_lowerGrowth (lowerGrowth_of_universal h hA)

end Erdos989

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Separation.Lemmas
import ErdosProblems.Erdos909.Transfinite

/-!
# A continuum-sized schedule of Euclidean continua

This file supplies the set-theoretic schedule used by the Anderson--Keisler
construction.  Every nondegenerate compact connected subset of a positive
finite-dimensional Euclidean space occurs in the schedule, every initial
segment of the stage order has cardinality strictly below the continuum, and
every scheduled target itself has cardinality continuum.
-/

open Set Topology TopologicalSpace
open scoped Cardinal

namespace Erdos909

noncomputable section

/-- The positive finite-dimensional Euclidean ambient space. -/
abbrev ContinuumAmbient (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The exact class of targets used in the Bernstein recursion. -/
def IsNondegenerateContinuum {X : Type*} [TopologicalSpace X] (C : Set X) : Prop :=
  IsCompact C ∧ IsConnected C ∧ ¬ C.Subsingleton

/-- A compact target is represented by a sequence with dense range. -/
abbrev ContinuumCode (m : ℕ) := ℕ → ContinuumAmbient m

lemma mk_continuumAmbient (m : ℕ) (hm : 0 < m) :
    Cardinal.mk (ContinuumAmbient m) = Cardinal.continuum := by
  let i : Fin m := ⟨0, hm⟩
  let encode : ContinuumAmbient m → (ℕ → ℝ) := fun x k ↦
    if h : k < m then x ⟨k, h⟩ else 0
  have hencode : Function.Injective encode := by
    intro x y hxy
    ext j
    have hj := congrFun hxy j.1
    simpa [encode, j.2] using hj
  let embed : ℝ → ContinuumAmbient m := fun r ↦ EuclideanSpace.single i r
  have hembed : Function.Injective embed := by
    intro x y hxy
    have hi := congrArg (fun z : ContinuumAmbient m ↦ z i) hxy
    simpa [embed, i] using hi
  apply le_antisymm
  · calc
      Cardinal.mk (ContinuumAmbient m) ≤ Cardinal.mk (ℕ → ℝ) :=
        Cardinal.mk_le_of_injective hencode
      _ = Cardinal.continuum := by
        rw [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_id,
          Cardinal.mk_real, Cardinal.lift_id, Cardinal.continuum_power_aleph0]
  · rw [← Cardinal.mk_real]
    exact Cardinal.mk_le_of_injective hembed

lemma mk_continuumCode (m : ℕ) (hm : 0 < m) :
    Cardinal.mk (ContinuumCode m) = Cardinal.continuum := by
  simp [ContinuumCode, mk_continuumAmbient m hm,
    Cardinal.continuum_power_aleph0]

/-- A fixed enumeration of all sequence codes by the initial ordinal of the
continuum. -/
noncomputable def continuumStageEquivCode (m : ℕ) (hm : 0 < m) :
    ContinuumStage ≃ ContinuumCode m :=
  Classical.choice <| Cardinal.eq.mp <| by
    rw [Cardinal.mk_ord_toType, mk_continuumCode m hm]

/-- Every proper initial stage has cardinality below continuum. -/
lemma mk_Iio_continuumStage_lt (i : ContinuumStage) :
    Cardinal.mk (Set.Iio i) < Cardinal.continuum := by
  simpa [ContinuumStage] using Cardinal.mk_Iio_lt i (by simp)

/-- The closed unit ball is the harmless target used when a sequence code
does not decode to a nondegenerate continuum. -/
def fallbackContinuum (m : ℕ) : Set (ContinuumAmbient m) :=
  Metric.closedBall 0 1

lemma fallbackContinuum_isNondegenerateContinuum (m : ℕ) (hm : 0 < m) :
    IsNondegenerateContinuum (fallbackContinuum m) := by
  let i : Fin m := ⟨0, hm⟩
  let e : ContinuumAmbient m := EuclideanSpace.single i 1
  have he : e ∈ fallbackContinuum m := by
    simp [fallbackContinuum, e]
  have hzero : (0 : ContinuumAmbient m) ∈ fallbackContinuum m := by
    simp [fallbackContinuum]
  have hne : e ≠ 0 := by
    intro h
    have hi := congrArg (fun z : ContinuumAmbient m ↦ z i) h
    simpa [e, i] using hi
  refine ⟨isCompact_closedBall _ _,
    ⟨⟨0, hzero⟩, (convex_closedBall (0 : ContinuumAmbient m) 1).isPreconnected⟩, ?_⟩
  intro hs
  exact hne (hs he hzero)

/-- The closed set decoded by a sequence. -/
def decodedTarget {m : ℕ} (code : ContinuumCode m) : Set (ContinuumAmbient m) :=
  closure (Set.range code)

/-- The target at a stage.  Valid continuum codes decode to their closures;
all other codes are sent to the fixed unit ball. -/
def continuumTarget (m : ℕ) (hm : 0 < m) (i : ContinuumStage) :
    Set (ContinuumAmbient m) := by
  classical
  let C := decodedTarget (continuumStageEquivCode m hm i)
  exact if IsNondegenerateContinuum C then C else fallbackContinuum m

lemma continuumTarget_isNondegenerateContinuum (m : ℕ) (hm : 0 < m)
    (i : ContinuumStage) :
    IsNondegenerateContinuum (continuumTarget m hm i) := by
  classical
  unfold continuumTarget
  dsimp only
  split_ifs with h
  · exact h
  · exact fallbackContinuum_isNondegenerateContinuum m hm

/-- Every nondegenerate Euclidean continuum occurs exactly as one scheduled
target (codes need not be unique). -/
lemma exists_continuumTarget_eq (m : ℕ) (hm : 0 < m)
    {C : Set (ContinuumAmbient m)} (hC : IsNondegenerateContinuum C) :
    ∃ i : ContinuumStage, continuumTarget m hm i = C := by
  classical
  obtain ⟨t, htC, htcount, hCt⟩ := EMetric.countable_closure_of_compact hC.1
  have htne : t.Nonempty := by
    by_contra h
    have ht : t = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    subst t
    simp only [closure_empty] at hCt
    exact hC.2.1.nonempty.ne_empty hCt
  obtain ⟨code, hcode⟩ := htcount.exists_eq_range htne
  let i : ContinuumStage := (continuumStageEquivCode m hm).symm code
  refine ⟨i, ?_⟩
  have hdecoded : decodedTarget (continuumStageEquivCode m hm i) = C := by
    rw [show continuumStageEquivCode m hm i = code by simp [i]]
    rw [decodedTarget, ← hcode]
    exact hCt.symm
  unfold continuumTarget
  dsimp only
  rw [hdecoded]
  simp [hC]

/-- A nondegenerate connected subset of a metric space cannot have cardinal
strictly below continuum.  The key Mathlib input says that every completely
regular space of smaller cardinality is totally separated. -/
lemma mk_eq_continuum_of_isConnected_not_subsingleton
    {X : Type*} [MetricSpace X] {C : Set X}
    (hconn : IsConnected C) (hnd : ¬ C.Subsingleton)
    (hupper : Cardinal.mk C ≤ Cardinal.continuum) :
    Cardinal.mk C = Cardinal.continuum := by
  apply le_antisymm hupper
  by_contra hle
  have hlt : Cardinal.mk C < Cardinal.continuum := lt_of_not_ge hle
  letI : TotallySeparatedSpace C :=
    CompletelyRegularSpace.totallySeparatedSpace_of_cardinalMk_lt_continuum hlt
  letI : PreconnectedSpace C := Subtype.preconnectedSpace hconn.isPreconnected
  have hs : Subsingleton C := subsingleton_of_preconnected_totallyDisconnected
  apply hnd
  intro x hx y hy
  exact congrArg Subtype.val (hs.elim ⟨x, hx⟩ ⟨y, hy⟩)

lemma mk_continuumTarget (m : ℕ) (hm : 0 < m) (i : ContinuumStage) :
    Cardinal.mk (continuumTarget m hm i) = Cardinal.continuum := by
  have htarget := continuumTarget_isNondegenerateContinuum m hm i
  apply mk_eq_continuum_of_isConnected_not_subsingleton htarget.2.1 htarget.2.2
  rw [← mk_continuumAmbient m hm]
  exact Cardinal.mk_set_le _

/-- The indexed family of all nondegenerate compact connected Euclidean
subsets. -/
abbrev EuclideanContinuum (m : ℕ) :=
  {C : Set (ContinuumAmbient m) // IsNondegenerateContinuum C}

/-- Regard an indexed Euclidean continuum as a target set. -/
def euclideanContinuumTarget {m : ℕ} (C : EuclideanContinuum m) :
    Set (ContinuumAmbient m) := C.1

/-- The stage schedule, now valued in the exact subtype indexing all
nondegenerate Euclidean continua. -/
noncomputable def scheduledEuclideanContinuum (m : ℕ) (hm : 0 < m) :
    ContinuumStage → EuclideanContinuum m := fun i ↦
  ⟨continuumTarget m hm i, continuumTarget_isNondegenerateContinuum m hm i⟩

lemma scheduledEuclideanContinuum_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (scheduledEuclideanContinuum m hm) := by
  intro C
  obtain ⟨i, hi⟩ := exists_continuumTarget_eq m hm C.property
  refine ⟨i, Subtype.ext ?_⟩
  exact hi

/-- There are at most continuum many nondegenerate Euclidean continua.  The
surjective stage schedule proves the bound without separately coding the
hyperspace of compact sets. -/
lemma mk_euclideanContinuum_le (m : ℕ) (hm : 0 < m) :
    Cardinal.mk (EuclideanContinuum m) ≤ Cardinal.continuum := by
  calc
    Cardinal.mk (EuclideanContinuum m) ≤ Cardinal.mk ContinuumStage :=
      Cardinal.mk_le_of_surjective (scheduledEuclideanContinuum_surjective m hm)
    _ = Cardinal.continuum := by simp [ContinuumStage]

/-- Every member of the indexed family is itself continuum-sized. -/
lemma mk_euclideanContinuumTarget (m : ℕ) (hm : 0 < m)
    (C : EuclideanContinuum m) :
    Cardinal.mk (euclideanContinuumTarget C) = Cardinal.continuum := by
  apply mk_eq_continuum_of_isConnected_not_subsingleton C.property.2.1 C.property.2.2
  rw [← mk_continuumAmbient m hm]
  exact Cardinal.mk_set_le _

/-- The subtype-indexed family is nonempty in positive dimension. -/
lemma euclideanContinuum_nonempty (m : ℕ) (hm : 0 < m) :
    Nonempty (EuclideanContinuum m) :=
  ⟨⟨fallbackContinuum m, fallbackContinuum_isNondegenerateContinuum m hm⟩⟩

/-- The indexed family bundled with
`exists_set_meeting_indexed_targets_avoiding`. -/
theorem exists_set_meeting_indexed_continua_avoiding
    (m : ℕ) (hm : 0 < m)
    (avoid : Set (ContinuumAmbient m))
    (obstruction : Set (ContinuumAmbient m × ContinuumAmbient m))
    (havoid : avoid.Countable)
    (hdiag : {x | (x, x) ∈ obstruction}.Countable)
    (hleft : ∀ y, {x | (x, y) ∈ obstruction}.Countable)
    (hright : ∀ y, {x | (y, x) ∈ obstruction}.Countable) :
    ∃ K : Set (ContinuumAmbient m),
      (∀ C, IsNondegenerateContinuum C → (K ∩ C).Nonempty) ∧
      Disjoint K avoid ∧
      Disjoint (K ×ˢ K) obstruction := by
  letI : Nonempty (EuclideanContinuum m) := euclideanContinuum_nonempty m hm
  obtain ⟨K, hmeet, hKavoid, hKobstruction⟩ :=
    exists_set_meeting_indexed_targets_avoiding
      (fun C : EuclideanContinuum m ↦ euclideanContinuumTarget C)
      avoid obstruction (mk_euclideanContinuum_le m hm)
      (mk_euclideanContinuumTarget m hm) havoid hdiag hleft hright
  refine ⟨K, ?_, hKavoid, hKobstruction⟩
  intro C hC
  exact hmeet ⟨C, hC⟩

/-- The continuum schedule, packaged with the independent-selector theorem.
The resulting set meets every nondegenerate Euclidean continuum while
avoiding the prescribed countable unary obstruction and the binary
obstruction on its square. -/
theorem exists_set_meeting_all_continua_avoiding
    (m : ℕ) (hm : 0 < m)
    (avoid : Set (ContinuumAmbient m))
    (obstruction : Set (ContinuumAmbient m × ContinuumAmbient m))
    (havoid : avoid.Countable)
    (hdiag : {x | (x, x) ∈ obstruction}.Countable)
    (hleft : ∀ y, {x | (x, y) ∈ obstruction}.Countable)
    (hright : ∀ y, {x | (y, x) ∈ obstruction}.Countable) :
    ∃ K : Set (ContinuumAmbient m),
      (∀ C, IsNondegenerateContinuum C → (K ∩ C).Nonempty) ∧
      Disjoint K avoid ∧
      Disjoint (K ×ˢ K) obstruction := by
  obtain ⟨K, hmeet, hKavoid, hKobstruction⟩ :=
    exists_set_meeting_targets_avoiding (continuumTarget m hm) avoid obstruction
      (mk_continuumTarget m hm) havoid hdiag hleft hright
  refine ⟨K, ?_, hKavoid, hKobstruction⟩
  intro C hC
  obtain ⟨i, hi⟩ := exists_continuumTarget_eq m hm hC
  simpa [hi] using hmeet i

end

end Erdos909

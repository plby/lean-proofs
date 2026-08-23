/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Prop45YColumns
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMapLaw

/-!
# Grouping the adaptive column holding vector by domino base

The `Y`/`Y'` terminal parsers produce one iid geometric coordinate for every
active deleted run.  This file groups those chronological coordinates by
their fixed column-domino base.  The resulting block sums have the product
negative-binomial law.  Conditioning by the literal mixed stopped-source
constraint then gives the capped product law on any selected family of free
dominoes.

This is the column analogue of `Erdos1166HLOZStoppedBlockGrouping` and the
probabilistic part of `Erdos1166HLOZStoppedMapLaw`.  It is deliberately
parametrized by the parser's `baseAt`: identifying that function and the
mixed event with a concrete stopped terminal path is a deterministic source
obligation, not a replacement probability assumption.
-/

namespace Erdos1166.HLOZColumnBlockGrouping

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

open HLOZDecomposition HLOZUrn HLOZProp48Truncated
open HLOZConditionalProduct HLOZStoppedMapLaw
open HLOZColumnPairRuns HLOZProp47Prop45YColumns
open HLOZSourceInstantiation

/-! ## Exact reindexing by the fixed column base -/

noncomputable def columnRunBaseSet {q : ℕ}
    (baseAt : Fin q → Site) : Finset Site :=
  Finset.univ.image baseAt

abbrev ColumnRunBase {q : ℕ} (baseAt : Fin q → Site) :=
  {x : Site // x ∈ columnRunBaseSet baseAt}

abbrev ColumnRunIndex {q : ℕ} (baseAt : Fin q → Site)
    (b : ColumnRunBase baseAt) :=
  {i : Fin q // baseAt i = b.1}

theorem baseAt_mem_columnRunBaseSet {q : ℕ}
    (baseAt : Fin q → Site) (i : Fin q) :
    baseAt i ∈ columnRunBaseSet baseAt := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- Every chronological run coordinate is uniquely its base together with
its position in that base's fiber. -/
noncomputable def columnRunSigmaEquiv {q : ℕ}
    (baseAt : Fin q → Site) :
    Fin q ≃ Σ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b where
  toFun i :=
    ⟨⟨baseAt i, baseAt_mem_columnRunBaseSet baseAt i⟩, ⟨i, rfl⟩⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨b, i, hi⟩
    have hb : (⟨baseAt i, baseAt_mem_columnRunBaseSet baseAt i⟩ :
        ColumnRunBase baseAt) = b := Subtype.ext hi
    cases hb
    rfl

noncomputable def columnBlockMeasurableEquiv {q : ℕ}
    (baseAt : Fin q → Site) :
    (Fin q → ℕ) ≃ᵐ
      (∀ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b → ℕ) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : Σ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b ↦ ℕ)
    (columnRunSigmaEquiv baseAt)).trans
    (MeasurableEquiv.piCurry
      (fun (b : ColumnRunBase baseAt)
        (_ : ColumnRunIndex baseAt b) ↦ ℕ))

noncomputable def columnBlockVector {q : ℕ}
    (baseAt : Fin q → Site) (v : Fin q → ℕ) :
    ∀ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b → ℕ :=
  columnBlockMeasurableEquiv baseAt v

theorem measurable_columnBlockVector {q : ℕ}
    (baseAt : Fin q → Site) :
    Measurable (columnBlockVector baseAt) :=
  (columnBlockMeasurableEquiv baseAt).measurable

noncomputable def columnBlockRunMeasure {q : ℕ}
    (baseAt : Fin q → Site) :
    Measure (∀ b : ColumnRunBase baseAt,
      ColumnRunIndex baseAt b → ℕ) :=
  Measure.pi fun _b ↦ Measure.pi fun _i ↦ runMeasure

instance columnBlockRunMeasure_isProbabilityMeasure {q : ℕ}
    (baseAt : Fin q → Site) :
    IsProbabilityMeasure (columnBlockRunMeasure baseAt) := by
  unfold columnBlockRunMeasure
  infer_instance

theorem runVectorMeasure_map_columnBlockVector {q : ℕ}
    (baseAt : Fin q → Site) :
    (runVectorMeasure q).map (columnBlockVector baseAt) =
      columnBlockRunMeasure baseAt := by
  let e := columnRunSigmaEquiv baseAt
  let E := MeasurableEquiv.piCongrLeft
    (fun _ : Σ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b ↦ ℕ) e
  let C :
      ((z : Σ b : ColumnRunBase baseAt,
          ColumnRunIndex baseAt b) → ℕ) ≃ᵐ
        (∀ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b → ℕ) :=
    MeasurableEquiv.piCurry
      (fun (b : ColumnRunBase baseAt)
        (_ : ColumnRunIndex baseAt b) ↦ ℕ)
  have hfun : columnBlockVector baseAt = C ∘ E := rfl
  rw [hfun, runVectorMeasure, ← Measure.infinitePi_eq_pi]
  rw [← Measure.map_map C.measurable E.measurable]
  have hE : (Measure.infinitePi fun _ : Fin q ↦ runMeasure).map E =
      Measure.infinitePi
        (fun _ : Σ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b ↦
          runMeasure) := by
    exact Measure.infinitePi_map_piCongrLeft
      (fun _ : Σ b : ColumnRunBase baseAt,
        ColumnRunIndex baseAt b ↦ runMeasure) e
  rw [hE]
  have hC : (Measure.infinitePi
      (fun _ : Σ b : ColumnRunBase baseAt,
        ColumnRunIndex baseAt b ↦ runMeasure)).map C =
      Measure.infinitePi (fun b : ColumnRunBase baseAt ↦
        Measure.infinitePi
          (fun _ : ColumnRunIndex baseAt b ↦ runMeasure)) := by
    exact Measure.infinitePi_map_piCurry
      (fun (_b : ColumnRunBase baseAt)
        (_i : ColumnRunIndex baseAt _b) ↦ runMeasure)
  rw [hC]
  unfold columnBlockRunMeasure
  rw [Measure.infinitePi_eq_pi]
  congr 1
  funext b
  rw [Measure.infinitePi_eq_pi]

/-- Sum the holding-run coordinates belonging to each column domino. -/
def columnBlockSums {q : ℕ} (baseAt : Fin q → Site)
    (w : ∀ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b → ℕ) :
    ColumnRunBase baseAt → ℕ :=
  fun b ↦ ∑ i, w b i

theorem measurable_columnBlockSums {q : ℕ}
    (baseAt : Fin q → Site) :
    Measurable (columnBlockSums baseAt) :=
  measurable_of_countable _

noncomputable def columnBlockNegBinMeasure {q : ℕ}
    (baseAt : Fin q → Site) :
    Measure (ColumnRunBase baseAt → ℕ) :=
  Measure.pi fun b ↦ negBinMeasure (Fintype.card (ColumnRunIndex baseAt b))

instance columnBlockNegBinMeasure_isProbabilityMeasure {q : ℕ}
    (baseAt : Fin q → Site) :
    IsProbabilityMeasure (columnBlockNegBinMeasure baseAt) := by
  unfold columnBlockNegBinMeasure
  infer_instance

theorem columnBlockSum_map_eq_negBinMeasure {q : ℕ}
    (baseAt : Fin q → Site) (b : ColumnRunBase baseAt) :
    (Measure.pi fun _ : ColumnRunIndex baseAt b ↦ runMeasure).map
        (fun w ↦ ∑ i, w i) =
      negBinMeasure (Fintype.card (ColumnRunIndex baseAt b)) := by
  let I := ColumnRunIndex baseAt b
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let E := MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℕ) e
  have hpres : MeasurePreserving E
      (runVectorMeasure (Fintype.card I))
      (Measure.pi fun _ : I ↦ runMeasure) := by
    unfold runVectorMeasure
    exact measurePreserving_piCongrLeft (fun _ : I ↦ runMeasure) e
  have hsum : (fun w : I → ℕ ↦ ∑ i, w i) ∘ E =
      runSum (Fintype.card I) := by
    funext v
    unfold runSum
    simp only [Function.comp_apply, E, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_eq_cast]
    change (∑ i : I, v (e.symm i)) = ∑ k, v k
    exact e.symm.sum_comp v
  rw [← hpres.map_eq, Measure.map_map
    (measurable_of_countable (fun w : I → ℕ ↦ ∑ i, w i)) E.measurable]
  rw [hsum]
  rfl

theorem columnBlockRunMeasure_map_sums {q : ℕ}
    (baseAt : Fin q → Site) :
    (columnBlockRunMeasure baseAt).map (columnBlockSums baseAt) =
      columnBlockNegBinMeasure baseAt := by
  unfold columnBlockRunMeasure columnBlockSums columnBlockNegBinMeasure
  rw [Measure.pi_map_pi fun _ ↦
    (measurable_of_countable
      (fun w : ColumnRunIndex baseAt _ → ℕ ↦ ∑ i, w i)).aemeasurable]
  congr 1
  funext b
  exact columnBlockSum_map_eq_negBinMeasure baseAt b

/-- Direct flat-vector form of the column block-sum law. -/
theorem runVectorMeasure_map_columnBlockSums {q : ℕ}
    (baseAt : Fin q → Site) :
    (runVectorMeasure q).map
        (fun v ↦ columnBlockSums baseAt (columnBlockVector baseAt v)) =
      columnBlockNegBinMeasure baseAt := by
  change (runVectorMeasure q).map
      (columnBlockSums baseAt ∘ columnBlockVector baseAt) = _
  rw [← Measure.map_map (measurable_columnBlockSums baseAt)
    (measurable_columnBlockVector baseAt)]
  rw [runVectorMeasure_map_columnBlockVector,
    columnBlockRunMeasure_map_sums]

/-! ## The mixed stopped-source event -/

def columnMixedBlockSumEvent {q : ℕ} (baseAt : Fin q → Site)
    (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    Set (ColumnRunBase baseAt → ℕ) :=
  {u | ∀ b,
    if _hC : b.1 ∈ creationSet ∨ b.1 + paperE1 ∈ creationSet then
      max (externalLeft b + u b) (externalRight b + u b) = m ∧
        (externalLeft b + u b = m ↔ b.1 ∈ creationSet) ∧
        (externalRight b + u b = m ↔ b.1 + paperE1 ∈ creationSet)
    else
      max (externalLeft b + u b) (externalRight b + u b) < m}

noncomputable def columnMixedBlockValues {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    ∀ b : ColumnRunBase baseAt, Finset ℕ :=
  fun b ↦ (Finset.range (m + 1)).filter fun u ↦
    if _hC : b.1 ∈ creationSet ∨ b.1 + paperE1 ∈ creationSet then
      max (externalLeft b + u) (externalRight b + u) = m ∧
        (externalLeft b + u = m ↔ b.1 ∈ creationSet) ∧
        (externalRight b + u = m ↔ b.1 + paperE1 ∈ creationSet)
    else
      max (externalLeft b + u) (externalRight b + u) < m

theorem columnMixedBlockSumEvent_eq_blockEvent {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    columnMixedBlockSumEvent baseAt m creationSet
        externalLeft externalRight =
      blockEvent
        (columnMixedBlockValues baseAt m creationSet
          externalLeft externalRight) := by
  ext u
  constructor
  · intro hu b
    rw [columnMixedBlockValues, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hu b⟩
    have hb := hu b
    split at hb <;> omega
  · intro hu b
    exact (Finset.mem_filter.mp (hu b)).2

theorem measurableSet_columnMixedBlockSumEvent {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    MeasurableSet (columnMixedBlockSumEvent baseAt m creationSet
      externalLeft externalRight) :=
  (Set.to_countable _).measurableSet

theorem columnBlockNegBinMeasure_cond_mixed_eq_pi_cond {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hpos : ∀ b, negBinMeasure
      (Fintype.card (ColumnRunIndex baseAt b))
        (columnMixedBlockValues baseAt m creationSet
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    (columnBlockNegBinMeasure baseAt)[|
      columnMixedBlockSumEvent baseAt m creationSet
        externalLeft externalRight] =
      Measure.pi (fun b ↦
        (negBinMeasure (Fintype.card (ColumnRunIndex baseAt b)))[|
          (columnMixedBlockValues baseAt m creationSet
            externalLeft externalRight b : Set ℕ)]) := by
  rw [columnMixedBlockSumEvent_eq_blockEvent]
  unfold columnBlockNegBinMeasure
  exact HLOZIncompleteStoppedBlocks.pi_cond_blockEvent_eq_pi_cond _ _ hpos

theorem columnRunIndex_nonempty {q : ℕ} (baseAt : Fin q → Site)
    (b : ColumnRunBase baseAt) :
    Nonempty (ColumnRunIndex baseAt b) := by
  rcases Finset.mem_image.mp b.2 with ⟨i, _hi, hib⟩
  exact ⟨⟨i, hib⟩⟩

/-- A nonempty mixed block event supplies positivity of every factor. -/
theorem columnMixedCoordinatePos_of_event_nonempty {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent baseAt m creationSet
      externalLeft externalRight).Nonempty) :
    ∀ b, negBinMeasure (Fintype.card (ColumnRunIndex baseAt b))
      (columnMixedBlockValues baseAt m creationSet
        externalLeft externalRight b : Set ℕ) ≠ 0 := by
  obtain ⟨u, hu⟩ := hEvent
  rw [columnMixedBlockSumEvent_eq_blockEvent] at hu
  intro b
  apply negBinMeasure_ne_zero_of_nonempty
  · exact Fintype.card_pos_iff.mpr (columnRunIndex_nonempty baseAt b)
  · exact ⟨u b, hu b⟩

theorem runVectorMeasure_cond_map_columnBlockSums {q : ℕ}
    (baseAt : Fin q → Site)
    (E : Set (ColumnRunBase baseAt → ℕ)) (hE : MeasurableSet E) :
    ((runVectorMeasure q)[|
      (fun v ↦ columnBlockSums baseAt
        (columnBlockVector baseAt v)) ⁻¹' E]).map
      (fun v ↦ columnBlockSums baseAt (columnBlockVector baseAt v)) =
        (columnBlockNegBinMeasure baseAt)[|E] := by
  let f := fun v ↦ columnBlockSums baseAt (columnBlockVector baseAt v)
  have hf : Measurable f :=
    (measurable_columnBlockSums baseAt).comp
      (measurable_columnBlockVector baseAt)
  have hmapCond : ((runVectorMeasure q)[|f ⁻¹' E]).map f =
      ((runVectorMeasure q).map f)[|E] := by
    ext s hs
    rw [Measure.map_apply hf hs, cond_apply (hE.preimage hf), cond_apply hE,
      Measure.map_apply hf hE, Measure.map_apply hf (hE.inter hs)]
    rfl
  rw [hmapCond]
  change ((runVectorMeasure q).map
    (fun v ↦ columnBlockSums baseAt (columnBlockVector baseAt v)))[|E] = _
  rw [runVectorMeasure_map_columnBlockSums]

/-! ## Active/free marginal and the capped profile -/

abbrev ColumnActiveFreeBase {q : ℕ} (baseAt : Fin q → Site)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt)) :=
  {b : ColumnRunBase baseAt //
    b ∈ activeBases ∧ b.1 ∉ creationSet ∧ b.1 + paperE1 ∉ creationSet}

def restrictColumnActiveFreeBase {q : ℕ} (baseAt : Fin q → Site)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (u : ColumnRunBase baseAt → ℕ) :
    ColumnActiveFreeBase baseAt creationSet activeBases → ℕ :=
  fun b ↦ u b.1

theorem measurable_restrictColumnActiveFreeBase {q : ℕ}
    (baseAt : Fin q → Site) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt)) :
    Measurable (restrictColumnActiveFreeBase baseAt creationSet activeBases) :=
  measurable_of_countable _

def columnActiveFreeShape {q : ℕ} (baseAt : Fin q → Site)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt)) :
    ColumnActiveFreeBase baseAt creationSet activeBases → ℕ :=
  fun b ↦ Fintype.card (ColumnRunIndex baseAt b.1)

def columnActiveFreeCapProfile {q : ℕ} (baseAt : Fin q → Site)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    ColumnActiveFreeBase baseAt creationSet activeBases → ℕ :=
  fun b ↦ max (externalLeft b.1) (externalRight b.1)

theorem columnMixedBlockValues_activeFree_eq_sourceBelowSet {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (b : ColumnActiveFreeBase baseAt creationSet activeBases) :
    (columnMixedBlockValues baseAt m creationSet
        externalLeft externalRight b.1 : Set ℕ) =
      sourceBelowSet m
        (columnActiveFreeCapProfile baseAt creationSet activeBases
          externalLeft externalRight b) := by
  ext u
  have hbC : ¬ (b.1.1 ∈ creationSet ∨
      b.1.1 + paperE1 ∈ creationSet) :=
    not_or_intro b.2.2.1 b.2.2.2
  simp only [columnMixedBlockValues, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_range, hbC, sourceBelowSet, Set.mem_ofPred_eq,
    columnActiveFreeCapProfile]
  by_cases hle : externalLeft b.1 ≤ externalRight b.1
  · rw [max_eq_right hle]
    have hadd : externalLeft b.1 + u ≤ externalRight b.1 + u :=
      Nat.add_le_add_right hle u
    rw [max_eq_right hadd]
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨by omega, h⟩
  · have hle' : externalRight b.1 ≤ externalLeft b.1 :=
      Nat.le_of_not_ge hle
    rw [max_eq_left hle']
    have hadd : externalRight b.1 + u ≤ externalLeft b.1 + u :=
      Nat.add_le_add_right hle' u
    rw [max_eq_left hadd]
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨by omega, h⟩

/-- Marginalizing creation and inactive column dominoes gives exactly the
capped Proposition-4.3 product on the selected active/free coordinates. -/
theorem columnBlockNegBinMeasure_cond_mixed_map_activeFree {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hpos : ∀ b, negBinMeasure
      (Fintype.card (ColumnRunIndex baseAt b))
        (columnMixedBlockValues baseAt m creationSet
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    ((columnBlockNegBinMeasure baseAt)[|
      columnMixedBlockSumEvent baseAt m creationSet
        externalLeft externalRight]).map
        (restrictColumnActiveFreeBase baseAt creationSet activeBases) =
      sourceCappedProfileMeasure m
        (columnActiveFreeShape baseAt creationSet activeBases)
        (columnActiveFreeCapProfile baseAt creationSet activeBases
          externalLeft externalRight) := by
  let μ : ColumnRunBase baseAt → Measure ℕ := fun b ↦
    (negBinMeasure (Fintype.card (ColumnRunIndex baseAt b)))[|
      (columnMixedBlockValues baseAt m creationSet
        externalLeft externalRight b : Set ℕ)]
  letI (b : ColumnRunBase baseAt) : IsProbabilityMeasure (μ b) :=
    cond_isProbabilityMeasure (hpos b)
  letI (b : ColumnActiveFreeBase baseAt creationSet activeBases) :
      IsProbabilityMeasure
        ((negBinMeasure (Fintype.card (ColumnRunIndex baseAt b.1)))[|
          sourceBelowSet m
            (columnActiveFreeCapProfile baseAt creationSet activeBases
              externalLeft externalRight b)]) := by
    apply cond_isProbabilityMeasure
    rw [← columnMixedBlockValues_activeFree_eq_sourceBelowSet
      baseAt m creationSet activeBases externalLeft externalRight b]
    exact hpos b.1
  rw [columnBlockNegBinMeasure_cond_mixed_eq_pi_cond
    baseAt m creationSet externalLeft externalRight hpos]
  unfold sourceCappedProfileMeasure
  change (Measure.pi μ).map (fun u b ↦ u b.1) = Measure.pi (fun b ↦
    (negBinMeasure (Fintype.card (ColumnRunIndex baseAt b.1)))[|
      sourceBelowSet m
        (columnActiveFreeCapProfile baseAt creationSet activeBases
          externalLeft externalRight b)])
  rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
  rw [Measure.map_infinitePi_infinitePi_of_inj
    (f := fun b : ColumnActiveFreeBase baseAt creationSet activeBases ↦ b.1)
    Subtype.val_injective]
  congr 1
  funext b
  unfold μ
  rw [columnMixedBlockValues_activeFree_eq_sourceBelowSet]

/-! ## Concrete forward and primed terminal parsers -/

noncomputable def forwardTerminalBlockSums
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    Path → ColumnRunBase h.baseAt → ℕ :=
  fun s ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt
      (pathConditionalSelectiveRunVector h.encoding s))

theorem measurable_forwardTerminalBlockSums
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    Measurable (forwardTerminalBlockSums h) :=
  (measurable_columnBlockSums h.baseAt).comp
    ((measurable_columnBlockVector h.baseAt).comp
      (measurable_pathConditionalSelectiveRunVector h.encoding))

/-- Before imposing the stopped source event, grouping the concrete forward
terminal parser gives the exact product negative-binomial law. -/
theorem forwardTerminalBlockSums_hasLaw
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    HasLaw (forwardTerminalBlockSums h)
      (columnBlockNegBinMeasure h.baseAt)
      simpleRandomWalkLaw[|selectiveTerminalPathAtom start specs] := by
  let X := pathConditionalSelectiveRunVector h.encoding
  let S := fun v ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt v)
  have hS : Measurable S :=
    (measurable_columnBlockSums h.baseAt).comp
      (measurable_columnBlockVector h.baseAt)
  have hSLaw : HasLaw S (columnBlockNegBinMeasure h.baseAt)
      (runVectorMeasure h.encoding.q) := by
    exact ⟨hS.aemeasurable, runVectorMeasure_map_columnBlockSums h.baseAt⟩
  change HasLaw
    (fun s : ℕ → Site ↦ columnBlockSums h.baseAt
      (columnBlockVector h.baseAt
        (pathConditionalSelectiveRunVector h.encoding s)))
    (columnBlockNegBinMeasure h.baseAt)
    simpleRandomWalkLaw[|selectiveTerminalPathAtom start specs]
  simpa only [X, S, Function.comp_apply] using
    hSLaw.fun_comp
      (pathConditionalSelectiveRunVector_hasLaw h.encoding h.valid)

noncomputable def primedTerminalBlockSums
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    Path → ColumnRunBase h.baseAt → ℕ :=
  fun s ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt
      (pathConditionalPrimedSelectiveRunVector h.encoding s))

theorem measurable_primedTerminalBlockSums
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    Measurable (primedTerminalBlockSums h) :=
  (measurable_columnBlockSums h.baseAt).comp
    ((measurable_columnBlockVector h.baseAt).comp
      (measurableEmbedding_simpleRandomWalk.measurable_extend
        (measurable_conditionalPrimedSelectiveRunVector h.encoding)
        measurable_const))

/-- Independently conditioned primed/backward terminal parser analogue. -/
theorem primedTerminalBlockSums_hasLaw
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    HasLaw (primedTerminalBlockSums h)
      (columnBlockNegBinMeasure h.baseAt)
      simpleRandomWalkLaw[|primedSelectiveTerminalPathAtom start specs] := by
  let X := pathConditionalPrimedSelectiveRunVector h.encoding
  let S := fun v ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt v)
  have hS : Measurable S :=
    (measurable_columnBlockSums h.baseAt).comp
      (measurable_columnBlockVector h.baseAt)
  have hSLaw : HasLaw S (columnBlockNegBinMeasure h.baseAt)
      (runVectorMeasure h.encoding.q) := by
    exact ⟨hS.aemeasurable, runVectorMeasure_map_columnBlockSums h.baseAt⟩
  change HasLaw
    (fun s : ℕ → Site ↦ columnBlockSums h.baseAt
      (columnBlockVector h.baseAt
        (pathConditionalPrimedSelectiveRunVector h.encoding s)))
    (columnBlockNegBinMeasure h.baseAt)
    simpleRandomWalkLaw[|primedSelectiveTerminalPathAtom start specs]
  simpa only [X, S, Function.comp_apply] using
    hSLaw.fun_comp
      (pathConditionalPrimedSelectiveRunVector_hasLaw h.encoding h.valid)

theorem measurableSet_primedSelectiveTerminalPathAtom
    (start : ℕ) (specs : List (Bool × IncrementPair)) :
    MeasurableSet (primedSelectiveTerminalPathAtom start specs) :=
  measurableEmbedding_simpleRandomWalk.measurableSet_image.2
    (measurableSet_primedSelectiveTerminalLabelsEqFrom start specs)

noncomputable def forwardTerminalMixedPathAtom
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) : Set Path :=
  selectiveTerminalPathAtom start specs ∩
    forwardTerminalBlockSums h ⁻¹'
      columnMixedBlockSumEvent h.baseAt level creationSet
        externalLeft externalRight

noncomputable def primedTerminalMixedPathAtom
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) : Set Path :=
  primedSelectiveTerminalPathAtom start specs ∩
    primedTerminalBlockSums h ⁻¹'
      columnMixedBlockSumEvent h.baseAt level creationSet
        externalLeft externalRight

theorem measurableSet_forwardTerminalMixedPathAtom
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    MeasurableSet (forwardTerminalMixedPathAtom h level creationSet
      externalLeft externalRight) := by
  exact (measurableSet_selectiveTerminalPathAtom start specs).inter
    ((measurableSet_columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).preimage
        (measurable_forwardTerminalBlockSums h))

theorem measurableSet_primedTerminalMixedPathAtom
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    MeasurableSet (primedTerminalMixedPathAtom h level creationSet
      externalLeft externalRight) := by
  exact (measurableSet_primedSelectiveTerminalPathAtom start specs).inter
    ((measurableSet_columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).preimage
        (measurable_primedTerminalBlockSums h))

theorem forwardTerminalBlockSums_hasLaw_on_mixed
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    HasLaw (forwardTerminalBlockSums h)
      ((columnBlockNegBinMeasure h.baseAt)[|
        columnMixedBlockSumEvent h.baseAt level creationSet
          externalLeft externalRight])
      simpleRandomWalkLaw[|forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
  let E := columnMixedBlockSumEvent h.baseAt level creationSet
    externalLeft externalRight
  have hE : MeasurableSet E :=
    measurableSet_columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight
  have hcond := HasLaw.cond_preimage
    (forwardTerminalBlockSums_hasLaw h)
    (measurable_forwardTerminalBlockSums h) E hE
  rw [cond_cond_eq_cond_inter
    (measurableSet_selectiveTerminalPathAtom start specs)
    (hE.preimage (measurable_forwardTerminalBlockSums h))] at hcond
  exact hcond

theorem primedTerminalBlockSums_hasLaw_on_mixed
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    HasLaw (primedTerminalBlockSums h)
      ((columnBlockNegBinMeasure h.baseAt)[|
        columnMixedBlockSumEvent h.baseAt level creationSet
          externalLeft externalRight])
      simpleRandomWalkLaw[|primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
  let E := columnMixedBlockSumEvent h.baseAt level creationSet
    externalLeft externalRight
  have hE : MeasurableSet E :=
    measurableSet_columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight
  have hcond := HasLaw.cond_preimage
    (primedTerminalBlockSums_hasLaw h)
    (measurable_primedTerminalBlockSums h) E hE
  rw [cond_cond_eq_cond_inter
    (measurableSet_primedSelectiveTerminalPathAtom start specs)
    (hE.preimage (measurable_primedTerminalBlockSums h))] at hcond
  exact hcond

noncomputable def forwardTerminalActiveFreeVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Path → ColumnActiveFreeBase h.baseAt creationSet activeBases → ℕ :=
  fun s ↦ restrictColumnActiveFreeBase h.baseAt creationSet activeBases
    (forwardTerminalBlockSums h s)

noncomputable def primedTerminalActiveFreeVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Path → ColumnActiveFreeBase h.baseAt creationSet activeBases → ℕ :=
  fun s ↦ restrictColumnActiveFreeBase h.baseAt creationSet activeBases
    (primedTerminalBlockSums h s)

theorem measurable_forwardTerminalActiveFreeVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Measurable (forwardTerminalActiveFreeVector h creationSet activeBases) :=
  (measurable_restrictColumnActiveFreeBase h.baseAt creationSet activeBases).comp
    (measurable_forwardTerminalBlockSums h)

theorem measurable_primedTerminalActiveFreeVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Measurable (primedTerminalActiveFreeVector h creationSet activeBases) :=
  (measurable_restrictColumnActiveFreeBase h.baseAt creationSet activeBases).comp
    (measurable_primedTerminalBlockSums h)

/-- Exact forward column stopped-source law on a literal terminal atom.
The only premise is nonemptiness of the deterministic mixed block event. -/
theorem forwardTerminalActiveFree_hasLaw_on_mixed
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty) :
    HasLaw (forwardTerminalActiveFreeVector h creationSet activeBases)
      (sourceCappedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases)
        (columnActiveFreeCapProfile h.baseAt creationSet activeBases
          externalLeft externalRight))
      simpleRandomWalkLaw[|forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
  let R := restrictColumnActiveFreeBase h.baseAt creationSet activeBases
  have hblock := forwardTerminalBlockSums_hasLaw_on_mixed h level creationSet
    externalLeft externalRight
  have hpos := columnMixedCoordinatePos_of_event_nonempty h.baseAt level
    creationSet externalLeft externalRight hEvent
  have hR : HasLaw R
      (sourceCappedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases)
        (columnActiveFreeCapProfile h.baseAt creationSet activeBases
          externalLeft externalRight))
      ((columnBlockNegBinMeasure h.baseAt)[|
        columnMixedBlockSumEvent h.baseAt level creationSet
          externalLeft externalRight]) := by
    refine ⟨(measurable_restrictColumnActiveFreeBase h.baseAt creationSet
      activeBases).aemeasurable, ?_⟩
    exact columnBlockNegBinMeasure_cond_mixed_map_activeFree h.baseAt level
      creationSet activeBases externalLeft externalRight hpos
  change HasLaw
    (fun s : Path ↦ restrictColumnActiveFreeBase h.baseAt creationSet activeBases
      (forwardTerminalBlockSums h s))
    (sourceCappedProfileMeasure level
      (columnActiveFreeShape h.baseAt creationSet activeBases)
      (columnActiveFreeCapProfile h.baseAt creationSet activeBases
        externalLeft externalRight))
    simpleRandomWalkLaw[|forwardTerminalMixedPathAtom h level creationSet
      externalLeft externalRight]
  simpa only [R, Function.comp_apply] using hR.fun_comp hblock

theorem primedTerminalActiveFree_hasLaw_on_mixed
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty) :
    HasLaw (primedTerminalActiveFreeVector h creationSet activeBases)
      (sourceCappedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases)
        (columnActiveFreeCapProfile h.baseAt creationSet activeBases
          externalLeft externalRight))
      simpleRandomWalkLaw[|primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
  let R := restrictColumnActiveFreeBase h.baseAt creationSet activeBases
  have hblock := primedTerminalBlockSums_hasLaw_on_mixed h level creationSet
    externalLeft externalRight
  have hpos := columnMixedCoordinatePos_of_event_nonempty h.baseAt level
    creationSet externalLeft externalRight hEvent
  have hR : HasLaw R
      (sourceCappedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases)
        (columnActiveFreeCapProfile h.baseAt creationSet activeBases
          externalLeft externalRight))
      ((columnBlockNegBinMeasure h.baseAt)[|
        columnMixedBlockSumEvent h.baseAt level creationSet
          externalLeft externalRight]) := by
    refine ⟨(measurable_restrictColumnActiveFreeBase h.baseAt creationSet
      activeBases).aemeasurable, ?_⟩
    exact columnBlockNegBinMeasure_cond_mixed_map_activeFree h.baseAt level
      creationSet activeBases externalLeft externalRight hpos
  change HasLaw
    (fun s : Path ↦ restrictColumnActiveFreeBase h.baseAt creationSet activeBases
      (primedTerminalBlockSums h s))
    (sourceCappedProfileMeasure level
      (columnActiveFreeShape h.baseAt creationSet activeBases)
      (columnActiveFreeCapProfile h.baseAt creationSet activeBases
        externalLeft externalRight))
    simpleRandomWalkLaw[|primedTerminalMixedPathAtom h level creationSet
      externalLeft externalRight]
  simpa only [R, Function.comp_apply] using hR.fun_comp hblock

/-- Winner-selected forward coordinates have the exact source truncated
product law once the fixed external winner identity is supplied. -/
theorem forwardTerminalActiveFree_truncated_hasLaw
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile h.baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape h.baseAt creationSet activeBases b) :
    HasLaw (forwardTerminalActiveFreeVector h creationSet activeBases)
      (sourceTruncatedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases))
      simpleRandomWalkLaw[|forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
  have hLaw := forwardTerminalActiveFree_hasLaw_on_mixed h level creationSet
    activeBases externalLeft externalRight hEvent
  rw [sourceCappedProfileMeasure_eq_truncated _ _ _ hwinning] at hLaw
  exact hLaw

/-- Primed/backward analogue, kept on its independently conditioned atom. -/
theorem primedTerminalActiveFree_truncated_hasLaw
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile h.baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape h.baseAt creationSet activeBases b) :
    HasLaw (primedTerminalActiveFreeVector h creationSet activeBases)
      (sourceTruncatedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases))
      simpleRandomWalkLaw[|primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
  have hLaw := primedTerminalActiveFree_hasLaw_on_mixed h level creationSet
    activeBases externalLeft externalRight hEvent
  rw [sourceCappedProfileMeasure_eq_truncated _ _ _ hwinning] at hLaw
  exact hLaw

/-- Unnormalized path-space law in the exact shape consumed by the stopped
atom connectors for Lemma 4.10 and Proposition 4.9. -/
theorem forwardTerminalActiveFree_truncated_path_map_law
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile h.baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape h.baseAt creationSet activeBases b) :
    (simpleRandomWalkLaw.restrict
      (forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight)).map
        (forwardTerminalActiveFreeVector h creationSet activeBases) =
      simpleRandomWalkLaw
          (forwardTerminalMixedPathAtom h level creationSet
            externalLeft externalRight) •
        sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases) := by
  exact map_restrict_eq_smul_of_hasLaw_cond
    (measurableSet_forwardTerminalMixedPathAtom h level creationSet
      externalLeft externalRight)
    (measurable_forwardTerminalActiveFreeVector h creationSet activeBases)
    (forwardTerminalActiveFree_truncated_hasLaw h level creationSet
      activeBases externalLeft externalRight hEvent hwinning)

theorem primedTerminalActiveFree_truncated_path_map_law
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt))
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile h.baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape h.baseAt creationSet activeBases b) :
    (simpleRandomWalkLaw.restrict
      (primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight)).map
        (primedTerminalActiveFreeVector h creationSet activeBases) =
      simpleRandomWalkLaw
          (primedTerminalMixedPathAtom h level creationSet
            externalLeft externalRight) •
        sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases) := by
  exact map_restrict_eq_smul_of_hasLaw_cond
    (measurableSet_primedTerminalMixedPathAtom h level creationSet
      externalLeft externalRight)
    (measurable_primedTerminalActiveFreeVector h creationSet activeBases)
    (primedTerminalActiveFree_truncated_hasLaw h level creationSet
      activeBases externalLeft externalRight hEvent hwinning)

/-! ## Source winner filters

The forward parser inserts its holding runs from the left/even endpoint of
each column domino.  It therefore supplies the left-winner branch, with ties
assigned to the left.  The separately conditioned primed parser supplies the
strict-right branch.  The following filters and lemmas isolate precisely the
one pathwise input needed to identify the negative-binomial shape: the number
of decoded holding opportunities at a base is the appropriate deleted-path
external local time. -/

noncomputable def columnForwardLeftWinnerBases {q : ℕ}
    (baseAt : Fin q → Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (candidateBases : Finset (ColumnRunBase baseAt)) :
    Finset (ColumnRunBase baseAt) :=
  candidateBases.filter fun b ↦ externalRight b ≤ externalLeft b

noncomputable def columnPrimedStrictRightWinnerBases {q : ℕ}
    (baseAt : Fin q → Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (candidateBases : Finset (ColumnRunBase baseAt)) :
    Finset (ColumnRunBase baseAt) :=
  candidateBases.filter fun b ↦ externalLeft b < externalRight b

theorem columnForwardLeftWinner_cap_eq_shape {q : ℕ}
    (baseAt : Fin q → Site) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (candidateBases : Finset (ColumnRunBase baseAt))
    (hleft : ∀ b, Fintype.card (ColumnRunIndex baseAt b) = externalLeft b) :
    ∀ b : ColumnActiveFreeBase baseAt creationSet
        (columnForwardLeftWinnerBases baseAt externalLeft externalRight
          candidateBases),
      columnActiveFreeCapProfile baseAt creationSet
          (columnForwardLeftWinnerBases baseAt externalLeft externalRight
            candidateBases) externalLeft externalRight b =
        columnActiveFreeShape baseAt creationSet
          (columnForwardLeftWinnerBases baseAt externalLeft externalRight
            candidateBases) b := by
  intro b
  have hwin : externalRight b.1 ≤ externalLeft b.1 :=
    (Finset.mem_filter.mp b.2.1).2
  unfold columnActiveFreeCapProfile columnActiveFreeShape
  rw [max_eq_left hwin, hleft]

theorem columnPrimedStrictRightWinner_cap_eq_shape {q : ℕ}
    (baseAt : Fin q → Site) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (candidateBases : Finset (ColumnRunBase baseAt))
    (hright : ∀ b,
      Fintype.card (ColumnRunIndex baseAt b) = externalRight b) :
    ∀ b : ColumnActiveFreeBase baseAt creationSet
        (columnPrimedStrictRightWinnerBases baseAt externalLeft externalRight
          candidateBases),
      columnActiveFreeCapProfile baseAt creationSet
          (columnPrimedStrictRightWinnerBases baseAt externalLeft externalRight
            candidateBases) externalLeft externalRight b =
        columnActiveFreeShape baseAt creationSet
          (columnPrimedStrictRightWinnerBases baseAt externalLeft externalRight
            candidateBases) b := by
  intro b
  have hwin : externalLeft b.1 ≤ externalRight b.1 :=
    (Nat.le_of_lt (Finset.mem_filter.mp b.2.1).2)
  unfold columnActiveFreeCapProfile columnActiveFreeShape
  rw [max_eq_right hwin, hright]

/-- Nonemptiness of the concrete mixed atom also proves that every selected
winner profile lies strictly below the stopping level. -/
theorem columnActiveFreeShape_lt_of_mixed_nonempty {q : ℕ}
    (baseAt : Fin q → Site) (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape baseAt creationSet activeBases b) :
    ∀ b, columnActiveFreeShape baseAt creationSet activeBases b < level := by
  intro b
  rw [← hwinning b]
  apply cap_lt_of_negBin_sourceBelowSet_ne_zero
  rw [← columnMixedBlockValues_activeFree_eq_sourceBelowSet
    baseAt level creationSet activeBases externalLeft externalRight b]
  exact columnMixedCoordinatePos_of_event_nonempty baseAt level creationSet
    externalLeft externalRight hEvent b.1

/-- Forward column terminal atom with the source left-winner split.  The
shape identity is reduced to the literal base-multiplicity equality. -/
theorem forwardTerminalLeftWinner_truncated_path_map_law
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (candidateBases : Finset (ColumnRunBase h.baseAt))
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hleft : ∀ b,
      Fintype.card (ColumnRunIndex h.baseAt b) = externalLeft b) :
    (simpleRandomWalkLaw.restrict
      (forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight)).map
        (forwardTerminalActiveFreeVector h creationSet
          (columnForwardLeftWinnerBases h.baseAt externalLeft externalRight
            candidateBases)) =
      simpleRandomWalkLaw
          (forwardTerminalMixedPathAtom h level creationSet
            externalLeft externalRight) •
        sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet
            (columnForwardLeftWinnerBases h.baseAt externalLeft externalRight
              candidateBases)) := by
  apply forwardTerminalActiveFree_truncated_path_map_law
    h level creationSet
      (columnForwardLeftWinnerBases h.baseAt externalLeft externalRight
        candidateBases)
    externalLeft externalRight hEvent
  exact columnForwardLeftWinner_cap_eq_shape h.baseAt creationSet
    externalLeft externalRight candidateBases hleft

/-- Independently conditioned primed terminal atom with the source strict
right-winner split. -/
theorem primedTerminalStrictRightWinner_truncated_path_map_law
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ)
    (candidateBases : Finset (ColumnRunBase h.baseAt))
    (hEvent : (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hright : ∀ b,
      Fintype.card (ColumnRunIndex h.baseAt b) = externalRight b) :
    (simpleRandomWalkLaw.restrict
      (primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight)).map
        (primedTerminalActiveFreeVector h creationSet
          (columnPrimedStrictRightWinnerBases h.baseAt externalLeft
            externalRight candidateBases)) =
      simpleRandomWalkLaw
          (primedTerminalMixedPathAtom h level creationSet
            externalLeft externalRight) •
        sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet
            (columnPrimedStrictRightWinnerBases h.baseAt externalLeft
              externalRight candidateBases)) := by
  apply primedTerminalActiveFree_truncated_path_map_law
    h level creationSet
      (columnPrimedStrictRightWinnerBases h.baseAt externalLeft externalRight
        candidateBases)
    externalLeft externalRight hEvent
  exact columnPrimedStrictRightWinner_cap_eq_shape h.baseAt creationSet
    externalLeft externalRight candidateBases hright

end Erdos1166.HLOZColumnBlockGrouping

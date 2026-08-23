/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZColumnTerminalRestart
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedHistoryFactorization

/-!
# Full chronological complement for the column terminal parsers

The column block-grouping theorem gives the marginal law of the active
winner coordinates.  Proposition 4.9 conditions on more of the stopped
history, so that marginal is not enough: the coordinates outside the active
set must retain their complete chronological run vectors.  This file proves
the exact active-sum/full-complement product factorization of the conditioned
column law.  No history-measurability assertion is made here; the output is
the measure-theoretic input needed for that separate deterministic step.
-/

namespace Erdos1166.HLOZColumnFullComplement

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

open HLOZDecomposition HLOZUrn HLOZProp48Truncated
open HLOZIncompleteStoppedBlocks
open HLOZConditionalProduct
open HLOZColumnPairRuns HLOZProp47Prop45YColumns
open HLOZColumnBlockGrouping HLOZColumnTerminalRestart HLOZStoppedMapLaw
open HLOZStoppedHistoryFactorization
open HLOZSourceInstantiation

abbrev Path := ℕ → Site

@[simp] theorem YPhaseTerminalClockInputs_encoding_q
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs) :
    h.encoding.q = selectiveActiveCount specs := rfl

@[simp] theorem YPrimedPhaseTerminalClockInputs_encoding_q
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs) :
    h.encoding.q =
      (canonicalPrimedSelectivePairVectorEncoding start specs h.valid).q := rfl

/-! ## Complement of the active/free bases -/

/-- Column bases not retained by the active/free projection. -/
abbrev ColumnComplementBase {q : ℕ} (baseAt : Fin q → Site)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt)) :=
  {b : ColumnRunBase baseAt //
    ¬(b ∈ activeBases ∧ b.1 ∉ creationSet ∧
      b.1 + paperE1 ∉ creationSet)}

/-- Restrict a block-sum vector to all nonactive coordinates. -/
def restrictColumnComplementBase {q : ℕ} (baseAt : Fin q → Site)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (u : ColumnRunBase baseAt → ℕ) :
    ColumnComplementBase baseAt creationSet activeBases → ℕ :=
  fun b ↦ u b.1

theorem measurable_restrictColumnComplementBase {q : ℕ}
    (baseAt : Fin q → Site) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt)) :
    Measurable
      (restrictColumnComplementBase baseAt creationSet activeBases) :=
  measurable_of_countable _

/-- Coordinatewise conditioned negative-binomial law on the complementary
column bases. -/
noncomputable def columnMixedComplementMeasure {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    Measure (ColumnComplementBase baseAt creationSet activeBases → ℕ) :=
  Measure.pi fun b ↦
    (negBinMeasure (Fintype.card (ColumnRunIndex baseAt b.1)))[|
      (columnMixedBlockValues baseAt m creationSet
        externalLeft externalRight b.1 : Set ℕ)]

theorem columnMixedComplementMeasure_isProbabilityMeasure {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hpos : ∀ b, negBinMeasure
      (Fintype.card (ColumnRunIndex baseAt b))
        (columnMixedBlockValues baseAt m creationSet
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    IsProbabilityMeasure
      (columnMixedComplementMeasure baseAt m creationSet activeBases
        externalLeft externalRight) := by
  unfold columnMixedComplementMeasure
  letI (b : ColumnComplementBase baseAt creationSet activeBases) :
      IsProbabilityMeasure
        ((negBinMeasure (Fintype.card (ColumnRunIndex baseAt b.1)))[|
          (columnMixedBlockValues baseAt m creationSet
            externalLeft externalRight b.1 : Set ℕ)]) :=
    cond_isProbabilityMeasure (hpos b.1)
  infer_instance

/-- Exact active/complement product decomposition of the conditioned
column block-sum law. -/
theorem columnBlockNegBinMeasure_cond_mixed_map_active_complement {q : ℕ}
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
        (fun u ↦
          (restrictColumnActiveFreeBase baseAt creationSet activeBases u,
            restrictColumnComplementBase baseAt creationSet activeBases u)) =
      (sourceCappedProfileMeasure m
        (columnActiveFreeShape baseAt creationSet activeBases)
        (columnActiveFreeCapProfile baseAt creationSet activeBases
          externalLeft externalRight)).prod
        (columnMixedComplementMeasure baseAt m creationSet activeBases
          externalLeft externalRight) := by
  classical
  let p : ColumnRunBase baseAt → Prop := fun b ↦
    b ∈ activeBases ∧ b.1 ∉ creationSet ∧
      b.1 + paperE1 ∉ creationSet
  let μ : ColumnRunBase baseAt → Measure ℕ := fun b ↦
    (negBinMeasure (Fintype.card (ColumnRunIndex baseAt b)))[|
      (columnMixedBlockValues baseAt m creationSet
        externalLeft externalRight b : Set ℕ)]
  letI (b : ColumnRunBase baseAt) : IsProbabilityMeasure (μ b) :=
    cond_isProbabilityMeasure (hpos b)
  rw [columnBlockNegBinMeasure_cond_mixed_eq_pi_cond
    baseAt m creationSet externalLeft externalRight hpos]
  change (Measure.pi μ).map
      (fun u ↦
        (restrictColumnActiveFreeBase baseAt creationSet activeBases u,
          restrictColumnComplementBase baseAt creationSet activeBases u)) = _
  have hsplit := (measurePreserving_piEquivPiSubtypeProd μ p).map_eq
  have hfun : (fun u : ColumnRunBase baseAt → ℕ ↦
      (restrictColumnActiveFreeBase baseAt creationSet activeBases u,
        restrictColumnComplementBase baseAt creationSet activeBases u)) =
      MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : ColumnRunBase baseAt ↦ ℕ) p := by
    rfl
  rw [hfun, hsplit]
  congr 1
  · unfold sourceCappedProfileMeasure
    congr 1
    funext b
    unfold μ
    rw [columnMixedBlockValues_activeFree_eq_sourceBelowSet]
    rfl

/-! ## Complete chronological complement -/

/-- Conditional law of all chronological runs in one column-base fiber. -/
noncomputable def columnMixedBlockRunMeasure {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (b : ColumnRunBase baseAt) :
    Measure (ColumnRunIndex baseAt b → ℕ) :=
  (Measure.pi fun _ : ColumnRunIndex baseAt b ↦ runMeasure)[|
    (fun w ↦ ∑ i, w i) ⁻¹'
      (columnMixedBlockValues baseAt m creationSet
        externalLeft externalRight b : Set ℕ)]

theorem columnMixedBlockRunMeasure_map_sum {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (b : ColumnRunBase baseAt) :
    (columnMixedBlockRunMeasure baseAt m creationSet
        externalLeft externalRight b).map (fun w ↦ ∑ i, w i) =
      (negBinMeasure (Fintype.card (ColumnRunIndex baseAt b)))[|
        (columnMixedBlockValues baseAt m creationSet
          externalLeft externalRight b : Set ℕ)] := by
  let f := fun w : ColumnRunIndex baseAt b → ℕ ↦ ∑ i, w i
  let E := (columnMixedBlockValues baseAt m creationSet
    externalLeft externalRight b : Set ℕ)
  have hf : Measurable f := measurable_of_countable _
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have hmapCond :
      ((Measure.pi fun _ : ColumnRunIndex baseAt b ↦ runMeasure)[|
        f ⁻¹' E]).map f =
        ((Measure.pi fun _ : ColumnRunIndex baseAt b ↦ runMeasure).map f)[|
          E] := by
    ext s hs
    rw [Measure.map_apply hf hs, cond_apply (hE.preimage hf), cond_apply hE,
      Measure.map_apply hf hE, Measure.map_apply hf (hE.inter hs)]
    rfl
  simpa only [columnMixedBlockRunMeasure, f, E,
    columnBlockSum_map_eq_negBinMeasure] using hmapCond

theorem columnMixedBlockRunMeasure_isProbabilityMeasure {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (b : ColumnRunBase baseAt)
    (hpos : negBinMeasure (Fintype.card (ColumnRunIndex baseAt b))
      (columnMixedBlockValues baseAt m creationSet
        externalLeft externalRight b : Set ℕ) ≠ 0) :
    IsProbabilityMeasure
      (columnMixedBlockRunMeasure baseAt m creationSet
        externalLeft externalRight b) := by
  unfold columnMixedBlockRunMeasure
  apply cond_isProbabilityMeasure
  let f := fun w : ColumnRunIndex baseAt b → ℕ ↦ ∑ i, w i
  let E := (columnMixedBlockValues baseAt m creationSet
    externalLeft externalRight b : Set ℕ)
  have heval :
      ((Measure.pi fun _ : ColumnRunIndex baseAt b ↦ runMeasure).map f) E =
        (Measure.pi fun _ : ColumnRunIndex baseAt b ↦ runMeasure) (f ⁻¹' E) :=
    Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete
  rw [show (Measure.pi fun _ : ColumnRunIndex baseAt b ↦ runMeasure).map f =
      negBinMeasure (Fintype.card (ColumnRunIndex baseAt b)) by
        simpa only [f] using columnBlockSum_map_eq_negBinMeasure baseAt b]
      at heval
  exact heval.symm ▸ hpos

/-- Full chronological run vectors on all complementary column bases. -/
abbrev ColumnComplementRuns {q : ℕ} (baseAt : Fin q → Site)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt)) :=
  ∀ b : ColumnComplementBase baseAt creationSet activeBases,
    ColumnRunIndex baseAt b.1 → ℕ

/-- Restrict a nested run vector to the complementary bases without
summing repeated visits. -/
def restrictColumnComplementRuns {q : ℕ} (baseAt : Fin q → Site)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (w : ∀ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b → ℕ) :
    ColumnComplementRuns baseAt creationSet activeBases :=
  fun b ↦ w b.1

theorem measurable_restrictColumnComplementRuns {q : ℕ}
    (baseAt : Fin q → Site) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt)) :
    Measurable
      (restrictColumnComplementRuns baseAt creationSet activeBases) :=
  measurable_of_countable _

/-- Product law of the complete chronological complement. -/
noncomputable def columnMixedComplementRunMeasure {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    Measure (ColumnComplementRuns baseAt creationSet activeBases) :=
  Measure.pi fun b ↦ columnMixedBlockRunMeasure baseAt m creationSet
    externalLeft externalRight b.1

theorem columnMixedComplementRunMeasure_isProbabilityMeasure {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hpos : ∀ b, negBinMeasure
      (Fintype.card (ColumnRunIndex baseAt b))
        (columnMixedBlockValues baseAt m creationSet
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    IsProbabilityMeasure
      (columnMixedComplementRunMeasure baseAt m creationSet activeBases
        externalLeft externalRight) := by
  unfold columnMixedComplementRunMeasure
  letI (b : ColumnComplementBase baseAt creationSet activeBases) :
      IsProbabilityMeasure
        (columnMixedBlockRunMeasure baseAt m creationSet
          externalLeft externalRight b.1) :=
    columnMixedBlockRunMeasure_isProbabilityMeasure baseAt m creationSet
      externalLeft externalRight b.1 (hpos b.1)
  infer_instance

/-- Mixed stopped constraint before summing the chronological vectors. -/
def columnMixedBlockRunEvent {q : ℕ} (baseAt : Fin q → Site)
    (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    Set (∀ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b → ℕ) :=
  Set.pi Set.univ fun b ↦
    (fun w ↦ ∑ i, w i) ⁻¹'
      (columnMixedBlockValues baseAt m creationSet
        externalLeft externalRight b : Set ℕ)

theorem measurableSet_columnMixedBlockRunEvent {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    MeasurableSet (columnMixedBlockRunEvent baseAt m creationSet
      externalLeft externalRight) := by
  exact MeasurableSet.univ_pi fun _ ↦ MeasurableSet.of_discrete

/-- The mixed event on the flat chronological vector is exactly the
preimage of the run-level event under the block reindexing. -/
theorem columnBlockVector_preimage_mixedRunEvent {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    columnBlockVector baseAt ⁻¹'
        columnMixedBlockRunEvent baseAt m creationSet
          externalLeft externalRight =
      (fun v ↦ columnBlockSums baseAt (columnBlockVector baseAt v)) ⁻¹'
        columnMixedBlockSumEvent baseAt m creationSet
          externalLeft externalRight := by
  rw [columnMixedBlockSumEvent_eq_blockEvent]
  ext v
  simp only [Set.mem_preimage, columnMixedBlockRunEvent, Set.mem_pi,
    Set.mem_univ, true_implies, blockEvent, Set.mem_ofPred_eq,
    columnBlockSums]
  constructor <;> intro h b <;> exact h b

/-- Conditioning commutes with the block-vector pushforward when the
conditioning event is pulled back from the block-vector space. -/
theorem cond_preimage_map_columnBlockVector {q : ℕ}
    (baseAt : Fin q → Site) (μ : Measure (Fin q → ℕ))
    (E : Set (∀ b : ColumnRunBase baseAt,
      ColumnRunIndex baseAt b → ℕ)) (hE : MeasurableSet E) :
    (μ[|columnBlockVector baseAt ⁻¹' E]).map
        (columnBlockVector baseAt) =
      (μ.map (columnBlockVector baseAt))[|E] := by
  ext s hs
  rw [Measure.map_apply (measurable_columnBlockVector baseAt) hs,
    cond_apply (hE.preimage (measurable_columnBlockVector baseAt)),
    cond_apply hE,
    Measure.map_apply (measurable_columnBlockVector baseAt) hE,
    Measure.map_apply (measurable_columnBlockVector baseAt) (hE.inter hs)]
  rfl

/-- The complete conditioned flat holding vector, reindexed by column base,
has the chronological block-run law. -/
theorem runVectorMeasure_cond_mixed_map_columnBlockVector {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ) :
    ((runVectorMeasure q)[|
      (fun v ↦ columnBlockSums baseAt (columnBlockVector baseAt v)) ⁻¹'
        columnMixedBlockSumEvent baseAt m creationSet
          externalLeft externalRight]).map (columnBlockVector baseAt) =
      (columnBlockRunMeasure baseAt)[|
        columnMixedBlockRunEvent baseAt m creationSet
          externalLeft externalRight] := by
  rw [← columnBlockVector_preimage_mixedRunEvent]
  rw [cond_preimage_map_columnBlockVector]
  · exact runVectorMeasure_map_columnBlockVector baseAt ▸ rfl
  · exact measurableSet_columnMixedBlockRunEvent baseAt m creationSet
      externalLeft externalRight

private theorem pi_cond_pi_eq_pi_cond
    {B : Type*} [Fintype B]
    {X : B → Type*} [∀ b, MeasurableSpace (X b)]
    [∀ b, MeasurableSingletonClass (X b)] [∀ b, Countable (X b)]
    (μ : ∀ b, Measure (X b)) [∀ b, IsProbabilityMeasure (μ b)]
    (E : ∀ b, Set (X b)) (hE : ∀ b, MeasurableSet (E b))
    (hpos : ∀ b, μ b (E b) ≠ 0) :
    (Measure.pi μ)[|Set.pi Set.univ E] =
      Measure.pi (fun b ↦ (μ b)[|E b]) := by
  letI (b : B) : IsProbabilityMeasure ((μ b)[|E b]) :=
    cond_isProbabilityMeasure (hpos b)
  have hmEvent : MeasurableSet (Set.pi Set.univ E) :=
    MeasurableSet.univ_pi hE
  apply Measure.ext_of_singleton
  intro x
  rw [cond_apply hmEvent, Measure.pi_singleton]
  rw [show Set.pi Set.univ E ∩ {x} =
      Set.pi Set.univ (fun b ↦ E b ∩ {x b}) by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · rintro ⟨hy, rfl⟩ b
      exact ⟨hy b, rfl⟩
    · intro hy
      have hyx : y = x := funext fun b ↦ (hy b).2
      exact ⟨fun b ↦ (hy b).1, hyx⟩]
  rw [Measure.pi_pi, Measure.pi_pi]
  simp_rw [cond_apply (hE _)]
  rw [Finset.prod_mul_distrib]
  congr 1
  apply ENNReal.prod_inv_distrib
  intro i _hi _j _hj _hij
  exact Or.inl (hpos i)

theorem columnBlockRunMeasure_cond_mixed_eq_pi_run_cond {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hpos : ∀ b, negBinMeasure
      (Fintype.card (ColumnRunIndex baseAt b))
        (columnMixedBlockValues baseAt m creationSet
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    (columnBlockRunMeasure baseAt)[|
        columnMixedBlockRunEvent baseAt m creationSet
          externalLeft externalRight] =
      Measure.pi fun b ↦ columnMixedBlockRunMeasure baseAt m creationSet
        externalLeft externalRight b := by
  let μ := fun b : ColumnRunBase baseAt ↦
    Measure.pi fun _ : ColumnRunIndex baseAt b ↦ runMeasure
  let E := fun b : ColumnRunBase baseAt ↦
    (fun w : ColumnRunIndex baseAt b → ℕ ↦ ∑ i, w i) ⁻¹'
      (columnMixedBlockValues baseAt m creationSet
        externalLeft externalRight b : Set ℕ)
  have hE : ∀ b, MeasurableSet (E b) := fun _ ↦ MeasurableSet.of_discrete
  have hrunpos : ∀ b, μ b (E b) ≠ 0 := by
    intro b
    have heval :
        (Measure.map
          (fun w : ColumnRunIndex baseAt b → ℕ ↦ ∑ i, w i)
          (μ b))
            (columnMixedBlockValues baseAt m creationSet
              externalLeft externalRight b : Set ℕ) =
          μ b (E b) :=
      Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete
    rw [show (Measure.map
        (fun w : ColumnRunIndex baseAt b → ℕ ↦ ∑ i, w i) (μ b)) =
        negBinMeasure (Fintype.card (ColumnRunIndex baseAt b)) by
          simpa only [μ] using columnBlockSum_map_eq_negBinMeasure baseAt b]
        at heval
    exact heval.symm ▸ hpos b
  simpa only [columnBlockRunMeasure, columnMixedBlockRunEvent,
    columnMixedBlockRunMeasure, μ, E] using
      pi_cond_pi_eq_pi_cond μ E hE hrunpos

/-- Exact active-sum/full-chronological-complement factorization. -/
theorem columnBlockRunMeasure_cond_mixed_map_active_fullComplement {q : ℕ}
    (baseAt : Fin q → Site) (m : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hpos : ∀ b, negBinMeasure
      (Fintype.card (ColumnRunIndex baseAt b))
        (columnMixedBlockValues baseAt m creationSet
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    ((columnBlockRunMeasure baseAt)[|
      columnMixedBlockRunEvent baseAt m creationSet
        externalLeft externalRight]).map
        (fun w ↦
          ((fun b : ColumnActiveFreeBase baseAt creationSet activeBases ↦
              ∑ i, w b.1 i),
            restrictColumnComplementRuns baseAt creationSet activeBases w)) =
      (sourceCappedProfileMeasure m
        (columnActiveFreeShape baseAt creationSet activeBases)
        (columnActiveFreeCapProfile baseAt creationSet activeBases
          externalLeft externalRight)).prod
        (columnMixedComplementRunMeasure baseAt m creationSet activeBases
          externalLeft externalRight) := by
  classical
  let p : ColumnRunBase baseAt → Prop := fun b ↦
    b ∈ activeBases ∧ b.1 ∉ creationSet ∧
      b.1 + paperE1 ∉ creationSet
  let μ : (b : ColumnRunBase baseAt) →
      Measure (ColumnRunIndex baseAt b → ℕ) := fun b ↦
    columnMixedBlockRunMeasure baseAt m creationSet
      externalLeft externalRight b
  letI (b : ColumnRunBase baseAt) : IsProbabilityMeasure (μ b) :=
    columnMixedBlockRunMeasure_isProbabilityMeasure baseAt m creationSet
      externalLeft externalRight b (hpos b)
  let activeFullLaw := Measure.pi fun b :
      ColumnActiveFreeBase baseAt creationSet activeBases ↦ μ b.1
  let complementLaw := columnMixedComplementRunMeasure baseAt m creationSet
    activeBases externalLeft externalRight
  let sumActive := fun
      w : ∀ b : ColumnActiveFreeBase baseAt creationSet activeBases,
        ColumnRunIndex baseAt b.1 → ℕ ↦
    fun b ↦ ∑ i, w b i
  have hcond :
      (columnBlockRunMeasure baseAt)[|
        columnMixedBlockRunEvent baseAt m creationSet
          externalLeft externalRight] = Measure.pi μ := by
    simpa only [μ] using
      columnBlockRunMeasure_cond_mixed_eq_pi_run_cond
        baseAt m creationSet externalLeft externalRight hpos
  have hsplit : (Measure.pi μ).map
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun b : ColumnRunBase baseAt ↦
          ColumnRunIndex baseAt b → ℕ) p) =
      activeFullLaw.prod complementLaw := by
    simpa only [activeFullLaw, complementLaw, p, μ,
      columnMixedComplementRunMeasure] using
      (measurePreserving_piEquivPiSubtypeProd μ p).map_eq
  have hactive : activeFullLaw.map sumActive =
      sourceCappedProfileMeasure m
        (columnActiveFreeShape baseAt creationSet activeBases)
        (columnActiveFreeCapProfile baseAt creationSet activeBases
          externalLeft externalRight) := by
    dsimp only [activeFullLaw, sumActive]
    rw [Measure.pi_map_pi]
    · congr 1
      funext b
      simpa only [μ, columnActiveFreeShape,
        columnActiveFreeCapProfile,
        columnMixedBlockValues_activeFree_eq_sourceBelowSet] using
        columnMixedBlockRunMeasure_map_sum baseAt m creationSet
          externalLeft externalRight b.1
    · intro b
      exact (measurable_of_countable _).aemeasurable
  have hsum : Measurable sumActive := measurable_of_countable _
  have hsplitMeas : Measurable
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun b : ColumnRunBase baseAt ↦
          ColumnRunIndex baseAt b → ℕ) p) :=
    (MeasurableEquiv.piEquivPiSubtypeProd
      (fun b : ColumnRunBase baseAt ↦
        ColumnRunIndex baseAt b → ℕ) p).measurable
  rw [hcond]
  change (Measure.pi μ).map
      ((Prod.map sumActive id) ∘
        MeasurableEquiv.piEquivPiSubtypeProd
          (fun b : ColumnRunBase baseAt ↦
            ColumnRunIndex baseAt b → ℕ) p) = _
  rw [← Measure.map_map (hsum.prodMap measurable_id) hsplitMeas, hsplit]
  rw [← Measure.map_prod_map activeFullLaw complementLaw hsum measurable_id]
  rw [hactive, Measure.map_id]

/-! ## Concrete terminal-path factorization -/

/-- Complete chronological nonactive coordinates decoded by the forward
terminal parser. -/
noncomputable def forwardTerminalFullComplementPath
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Path → ColumnComplementRuns h.baseAt creationSet activeBases :=
  fun s ↦ restrictColumnComplementRuns h.baseAt creationSet activeBases
    (columnBlockVector h.baseAt
      (pathConditionalSelectiveRunVector
        (canonicalSelectivePairVectorEncoding start specs h.valid) s))

theorem measurable_forwardTerminalFullComplementPath
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Measurable
      (forwardTerminalFullComplementPath h creationSet activeBases) :=
  (measurable_restrictColumnComplementRuns h.baseAt creationSet
    activeBases).comp
      ((measurable_columnBlockVector h.baseAt).comp
        (measurable_pathConditionalSelectiveRunVector
          (canonicalSelectivePairVectorEncoding start specs h.valid)))

/-- Complete chronological nonactive coordinates decoded by the separately
conditioned primed/backward terminal parser. -/
noncomputable def primedTerminalFullComplementPath
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Path → ColumnComplementRuns h.baseAt creationSet activeBases :=
  fun s ↦ restrictColumnComplementRuns h.baseAt creationSet activeBases
    (columnBlockVector h.baseAt
      (pathConditionalPrimedSelectiveRunVector
        (canonicalPrimedSelectivePairVectorEncoding start specs h.valid) s))

theorem measurable_primedTerminalFullComplementPath
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Measurable
      (primedTerminalFullComplementPath h creationSet activeBases) :=
  (measurable_restrictColumnComplementRuns h.baseAt creationSet
    activeBases).comp
      ((measurable_columnBlockVector h.baseAt).comp
        (measurableEmbedding_simpleRandomWalk.measurable_extend
          (measurable_conditionalPrimedSelectiveRunVector
            (canonicalPrimedSelectivePairVectorEncoding start specs h.valid))
          measurable_const))

/-- Conditioning the complete forward terminal holding vector by the mixed
stopped-source event keeps its exact flat-vector conditional law. -/
theorem forwardTerminalRunVector_hasLaw_on_mixed
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    HasLaw (pathConditionalSelectiveRunVector h.encoding)
      ((runVectorMeasure h.encoding.q)[|
        (fun v ↦ columnBlockSums h.baseAt
          (columnBlockVector h.baseAt v)) ⁻¹'
            columnMixedBlockSumEvent h.baseAt level creationSet
              externalLeft externalRight])
      simpleRandomWalkLaw[|forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
  let X := pathConditionalSelectiveRunVector h.encoding
  let E : Set (Fin h.encoding.q → ℕ) := (fun v ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt v)) ⁻¹'
      columnMixedBlockSumEvent h.baseAt level creationSet
        externalLeft externalRight
  have hE : MeasurableSet E :=
    (measurableSet_columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).preimage
        ((measurable_columnBlockSums h.baseAt).comp
          (measurable_columnBlockVector h.baseAt))
  have hcond := HasLaw.cond_preimage
    (pathConditionalSelectiveRunVector_hasLaw h.encoding h.valid)
    (measurable_pathConditionalSelectiveRunVector h.encoding) E hE
  have hP :
      simpleRandomWalkLaw[|selectiveTerminalPathAtom start specs][|
          pathConditionalSelectiveRunVector h.encoding ⁻¹' E] =
        simpleRandomWalkLaw[|forwardTerminalMixedPathAtom h level creationSet
          externalLeft externalRight] := by
    rw [cond_cond_eq_cond_inter
      (measurableSet_selectiveTerminalPathAtom start specs)
      (hE.preimage
        (measurable_pathConditionalSelectiveRunVector h.encoding))
      simpleRandomWalkLaw]
    rfl
  rw [← hP]
  simpa only [E] using hcond

/-- Primed/backward analogue of the complete conditioned holding-vector
law. -/
theorem primedTerminalRunVector_hasLaw_on_mixed
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (level : ℕ) (creationSet : Finset Site)
    (externalLeft externalRight : ColumnRunBase h.baseAt → ℕ) :
    HasLaw (pathConditionalPrimedSelectiveRunVector h.encoding)
      ((runVectorMeasure h.encoding.q)[|
        (fun v ↦ columnBlockSums h.baseAt
          (columnBlockVector h.baseAt v)) ⁻¹'
            columnMixedBlockSumEvent h.baseAt level creationSet
              externalLeft externalRight])
      simpleRandomWalkLaw[|primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
  let X := pathConditionalPrimedSelectiveRunVector h.encoding
  let E : Set (Fin h.encoding.q → ℕ) := (fun v ↦ columnBlockSums h.baseAt
    (columnBlockVector h.baseAt v)) ⁻¹'
      columnMixedBlockSumEvent h.baseAt level creationSet
        externalLeft externalRight
  have hX : Measurable X :=
    measurableEmbedding_simpleRandomWalk.measurable_extend
      (measurable_conditionalPrimedSelectiveRunVector h.encoding)
      measurable_const
  have hE : MeasurableSet E :=
    (measurableSet_columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight).preimage
        ((measurable_columnBlockSums h.baseAt).comp
          (measurable_columnBlockVector h.baseAt))
  have hcond := HasLaw.cond_preimage
    (pathConditionalPrimedSelectiveRunVector_hasLaw h.encoding h.valid)
    hX E hE
  have hP :
      simpleRandomWalkLaw[|primedSelectiveTerminalPathAtom start specs][|
          pathConditionalPrimedSelectiveRunVector h.encoding ⁻¹' E] =
        simpleRandomWalkLaw[|primedTerminalMixedPathAtom h level creationSet
          externalLeft externalRight] := by
    rw [cond_cond_eq_cond_inter
      (measurableSet_primedSelectiveTerminalPathAtom start specs)
      (hE.preimage hX) simpleRandomWalkLaw]
    rfl
  rw [← hP]
  simpa only [E] using hcond

/-- Generic path-space lift of the exact active/full-chronological-complement
factorization.  It applies to either terminal parser once its complete iid
holding vector is available. -/
theorem terminalActiveFullComplement_hasLaw_on_mixed
    {Ω : Type*} [MeasurableSpace Ω] {q : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P]
    (baseAt : Fin q → Site) (X : Ω → Fin q → ℕ)
    (A : Set Ω) (hA : MeasurableSet A) (hX : Measurable X)
    (hLaw : HasLaw X (runVectorMeasure q) P[|A])
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent baseAt level creationSet
      externalLeft externalRight).Nonempty) :
    HasLaw
      (fun ω ↦
        ((fun b : ColumnActiveFreeBase baseAt creationSet activeBases ↦
            ∑ i, columnBlockVector baseAt (X ω) b.1 i),
          restrictColumnComplementRuns baseAt creationSet activeBases
            (columnBlockVector baseAt (X ω))))
      ((sourceCappedProfileMeasure level
        (columnActiveFreeShape baseAt creationSet activeBases)
        (columnActiveFreeCapProfile baseAt creationSet activeBases
          externalLeft externalRight)).prod
        (columnMixedComplementRunMeasure baseAt level creationSet
          activeBases externalLeft externalRight))
      P[|A ∩ X ⁻¹' ((fun v ↦ columnBlockSums baseAt
        (columnBlockVector baseAt v)) ⁻¹'
          columnMixedBlockSumEvent baseAt level creationSet
            externalLeft externalRight)] := by
  let E := (fun v ↦ columnBlockSums baseAt
    (columnBlockVector baseAt v)) ⁻¹'
      columnMixedBlockSumEvent baseAt level creationSet
        externalLeft externalRight
  have hE : MeasurableSet E :=
    (measurableSet_columnMixedBlockSumEvent baseAt level creationSet
      externalLeft externalRight).preimage
        ((measurable_columnBlockSums baseAt).comp
          (measurable_columnBlockVector baseAt))
  have hCond := HasLaw.cond_preimage hLaw hX E hE
  rw [cond_cond_eq_cond_inter hA (hE.preimage hX) P] at hCond
  let B := ∀ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b → ℕ
  let G : B →
      (ColumnActiveFreeBase baseAt creationSet activeBases → ℕ) ×
        ColumnComplementRuns baseAt creationSet activeBases := fun w ↦
    ((fun b ↦ ∑ i, w b.1 i),
      restrictColumnComplementRuns baseAt creationSet activeBases w)
  let F : (Fin q → ℕ) →
      (ColumnActiveFreeBase baseAt creationSet activeBases → ℕ) ×
        ColumnComplementRuns baseAt creationSet activeBases :=
    G ∘ columnBlockVector baseAt
  have hG : Measurable G := measurable_of_countable _
  have hF : Measurable F :=
    hG.comp (measurable_columnBlockVector baseAt)
  have hpos := columnMixedCoordinatePos_of_event_nonempty baseAt level
    creationSet externalLeft externalRight hEvent
  have hMap : ((runVectorMeasure q)[|E]).map F =
      (sourceCappedProfileMeasure level
        (columnActiveFreeShape baseAt creationSet activeBases)
        (columnActiveFreeCapProfile baseAt creationSet activeBases
          externalLeft externalRight)).prod
        (columnMixedComplementRunMeasure baseAt level creationSet
          activeBases externalLeft externalRight) := by
    change ((runVectorMeasure q)[|E]).map
      (G ∘ columnBlockVector baseAt) = _
    rw [← Measure.map_map hG (measurable_columnBlockVector baseAt)]
    rw [runVectorMeasure_cond_mixed_map_columnBlockVector]
    simpa only [G, B] using
      columnBlockRunMeasure_cond_mixed_map_active_fullComplement
        baseAt level creationSet activeBases externalLeft externalRight hpos
  have hFLaw : HasLaw F
      ((sourceCappedProfileMeasure level
        (columnActiveFreeShape baseAt creationSet activeBases)
        (columnActiveFreeCapProfile baseAt creationSet activeBases
          externalLeft externalRight)).prod
        (columnMixedComplementRunMeasure baseAt level creationSet
          activeBases externalLeft externalRight)) ((runVectorMeasure q)[|E]) :=
    ⟨hF.aemeasurable, hMap⟩
  simpa only [E, F, G, B, Function.comp_apply] using
    hFLaw.fun_comp hCond

/-- Winner identification replaces the capped active marginal by the source
truncated law while retaining the entire chronological complement. -/
theorem terminalActiveFullComplement_truncated_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {q : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P]
    (baseAt : Fin q → Site) (X : Ω → Fin q → ℕ)
    (A : Set Ω) (hA : MeasurableSet A) (hX : Measurable X)
    (hLaw : HasLaw X (runVectorMeasure q) P[|A])
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape baseAt creationSet activeBases b) :
    HasLaw
      (fun ω ↦
        ((fun b : ColumnActiveFreeBase baseAt creationSet activeBases ↦
            ∑ i, columnBlockVector baseAt (X ω) b.1 i),
          restrictColumnComplementRuns baseAt creationSet activeBases
            (columnBlockVector baseAt (X ω))))
      ((sourceTruncatedProfileMeasure level
        (columnActiveFreeShape baseAt creationSet activeBases)).prod
        (columnMixedComplementRunMeasure baseAt level creationSet
          activeBases externalLeft externalRight))
      P[|A ∩ X ⁻¹' ((fun v ↦ columnBlockSums baseAt
        (columnBlockVector baseAt v)) ⁻¹'
          columnMixedBlockSumEvent baseAt level creationSet
            externalLeft externalRight)] := by
  have h := terminalActiveFullComplement_hasLaw_on_mixed P baseAt X A hA hX
    hLaw level creationSet activeBases externalLeft externalRight hEvent
  rw [sourceCappedProfileMeasure_eq_truncated _ _ _ hwinning] at h
  exact h

/-- Unnormalized path-space form of the chronological-complement law.  This
is the form used by source atoms and subsequent history refinements. -/
theorem terminalActiveFullComplement_truncated_path_map_law
    {Ω : Type*} [MeasurableSpace Ω] {q : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P]
    (baseAt : Fin q → Site) (X : Ω → Fin q → ℕ)
    (A : Set Ω) (hA : MeasurableSet A) (hX : Measurable X)
    (hLaw : HasLaw X (runVectorMeasure q) P[|A])
    (level : ℕ) (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase baseAt))
    (externalLeft externalRight : ColumnRunBase baseAt → ℕ)
    (hEvent : (columnMixedBlockSumEvent baseAt level creationSet
      externalLeft externalRight).Nonempty)
    (hwinning : ∀ b,
      columnActiveFreeCapProfile baseAt creationSet activeBases
        externalLeft externalRight b =
      columnActiveFreeShape baseAt creationSet activeBases b) :
    (P.restrict (A ∩ X ⁻¹' ((fun v ↦ columnBlockSums baseAt
      (columnBlockVector baseAt v)) ⁻¹'
        columnMixedBlockSumEvent baseAt level creationSet
          externalLeft externalRight))).map
      (fun ω ↦
        ((fun b : ColumnActiveFreeBase baseAt creationSet activeBases ↦
            ∑ i, columnBlockVector baseAt (X ω) b.1 i),
          restrictColumnComplementRuns baseAt creationSet activeBases
            (columnBlockVector baseAt (X ω)))) =
      P (A ∩ X ⁻¹' ((fun v ↦ columnBlockSums baseAt
        (columnBlockVector baseAt v)) ⁻¹'
          columnMixedBlockSumEvent baseAt level creationSet
            externalLeft externalRight)) •
        ((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape baseAt creationSet activeBases)).prod
          (columnMixedComplementRunMeasure baseAt level creationSet
            activeBases externalLeft externalRight)) := by
  let E := (fun v ↦ columnBlockSums baseAt
    (columnBlockVector baseAt v)) ⁻¹'
      columnMixedBlockSumEvent baseAt level creationSet
        externalLeft externalRight
  have hE : MeasurableSet E :=
    (measurableSet_columnMixedBlockSumEvent baseAt level creationSet
      externalLeft externalRight).preimage
        ((measurable_columnBlockSums baseAt).comp
          (measurable_columnBlockVector baseAt))
  let G : (∀ b : ColumnRunBase baseAt, ColumnRunIndex baseAt b → ℕ) →
      (ColumnActiveFreeBase baseAt creationSet activeBases → ℕ) ×
        ColumnComplementRuns baseAt creationSet activeBases := fun w ↦
    ((fun b ↦ ∑ i, w b.1 i),
      restrictColumnComplementRuns baseAt creationSet activeBases w)
  have hStat : Measurable
      (fun ω ↦
        ((fun b : ColumnActiveFreeBase baseAt creationSet activeBases ↦
            ∑ i, columnBlockVector baseAt (X ω) b.1 i),
          restrictColumnComplementRuns baseAt creationSet activeBases
            (columnBlockVector baseAt (X ω)))) := by
    change Measurable (G ∘ columnBlockVector baseAt ∘ X)
    exact (measurable_of_countable G).comp
      ((measurable_columnBlockVector baseAt).comp hX)
  exact map_restrict_eq_smul_of_hasLaw_cond
    (hA.inter (hE.preimage hX)) hStat
    (terminalActiveFullComplement_truncated_hasLaw P baseAt X A hA hX hLaw
      level creationSet activeBases externalLeft externalRight hEvent hwinning)

/-! ## Full complement with the post-terminal direction retained -/

/-- Complete forward terminal statistic before adjoining the first fresh
direction.  Unlike the active marginal, the second component remembers every
chronological run coordinate on every nonactive base. -/
noncomputable def forwardIncrementTerminalActiveFullComplementVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    (ℕ → Direction) →
      (ColumnActiveFreeBase h.baseAt creationSet activeBases → ℕ) ×
        ColumnComplementRuns h.baseAt creationSet activeBases :=
  fun omega ↦
    (forwardIncrementTerminalActiveFreeVector h creationSet activeBases omega,
      restrictColumnComplementRuns h.baseAt creationSet activeBases
        (columnBlockVector h.baseAt
          (conditionalSelectiveRunVector h.encoding omega)))

theorem measurable_forwardIncrementTerminalActiveFullComplementVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Measurable
      (forwardIncrementTerminalActiveFullComplementVector h creationSet
        activeBases) := by
  exact (measurable_forwardIncrementTerminalActiveFreeVector h creationSet
      activeBases).prodMk
    ((measurable_restrictColumnComplementRuns h.baseAt creationSet activeBases).comp
      ((measurable_columnBlockVector h.baseAt).comp
        (measurable_conditionalSelectiveRunVector h.encoding)))

/-- On the literal forward mixed atom, the active winner totals and the full
chronological complement have the exact truncated product law. -/
theorem forwardIncrementTerminalActiveFullComplement_truncated_hasLaw
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
    HasLaw
      (forwardIncrementTerminalActiveFullComplementVector h creationSet
        activeBases)
      ((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
        (columnMixedComplementRunMeasure h.baseAt level creationSet
          activeBases externalLeft externalRight))
      incrementLaw[|forwardTerminalMixedIncrementAtom h level creationSet
        externalLeft externalRight] := by
  have hraw := terminalActiveFullComplement_truncated_hasLaw
    incrementLaw h.baseAt (conditionalSelectiveRunVector h.encoding)
      (selectiveTerminalLabelsEqFrom start specs)
      (measurableSet_selectiveTerminalLabelsEqFrom start specs)
      (measurable_conditionalSelectiveRunVector h.encoding)
      (conditionalSelectiveRunVector_hasLaw h.encoding h.valid)
      level creationSet activeBases externalLeft externalRight hEvent hwinning
  change HasLaw
    (fun omega ↦
      ((fun b : ColumnActiveFreeBase h.baseAt creationSet activeBases ↦
          ∑ i, columnBlockVector h.baseAt
            (conditionalSelectiveRunVector h.encoding omega) b.1 i),
        restrictColumnComplementRuns h.baseAt creationSet activeBases
          (columnBlockVector h.baseAt
            (conditionalSelectiveRunVector h.encoding omega))))
    ((sourceTruncatedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
      (columnMixedComplementRunMeasure h.baseAt level creationSet
        activeBases externalLeft externalRight))
    incrementLaw[|selectiveTerminalLabelsEqFrom start specs ∩
      conditionalSelectiveRunVector h.encoding ⁻¹'
        ((fun v ↦ columnBlockSums h.baseAt
          (columnBlockVector h.baseAt v)) ⁻¹'
          columnMixedBlockSumEvent h.baseAt level creationSet
            externalLeft externalRight)]
  exact hraw

/-- The first direction after the adaptive terminal endpoint is independent
of both the active winner profile and the complete chronological complement.
The factors are reassociated so the active profile and fresh direction match
the Proposition-4.9 statistic. -/
theorem forwardIncrementTerminalActiveFullComplement_prod_fresh_hasLaw
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
    HasLaw
      (fun omega ↦
        ((forwardIncrementTerminalActiveFreeVector h creationSet
            activeBases omega,
          incrementShiftAfter (selectiveEncodedEndTime h.encoding) omega 0),
        restrictColumnComplementRuns h.baseAt creationSet activeBases
          (columnBlockVector h.baseAt
            (conditionalSelectiveRunVector h.encoding omega))))
      (((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
            directionLaw).prod
        (columnMixedComplementRunMeasure h.baseAt level creationSet
          activeBases externalLeft externalRight))
      incrementLaw[|forwardTerminalMixedIncrementAtom h level creationSet
        externalLeft externalRight] := by
  let activeLaw := sourceTruncatedProfileMeasure level
    (columnActiveFreeShape h.baseAt creationSet activeBases)
  let complementLaw := columnMixedComplementRunMeasure h.baseAt level
    creationSet activeBases externalLeft externalRight
  let G := fun v : Fin h.encoding.q → ℕ ↦
    ((fun b : ColumnActiveFreeBase h.baseAt creationSet activeBases ↦
        ∑ i, columnBlockVector h.baseAt v b.1 i),
      restrictColumnComplementRuns h.baseAt creationSet activeBases
        (columnBlockVector h.baseAt v))
  have hG : Measurable G := measurable_of_countable _
  have hSplit := forwardIncrementTerminalActiveFullComplement_truncated_hasLaw
    h level creationSet activeBases externalLeft externalRight hEvent hwinning
  have hSplit' : HasLaw
      (fun omega ↦ G (conditionalSelectiveRunVector h.encoding omega))
      (activeLaw.prod complementLaw)
      incrementLaw[|selectiveTerminalRestrictedAtom h.encoding
        (fun v ↦ columnBlockSums h.baseAt (columnBlockVector h.baseAt v))
        (columnMixedBlockSumEvent h.baseAt level creationSet
          externalLeft externalRight)] := by
    have hfun :
        (fun omega ↦ G (conditionalSelectiveRunVector h.encoding omega)) =
          forwardIncrementTerminalActiveFullComplementVector h creationSet
            activeBases := by
      funext omega
      rfl
    rw [hfun]
    simpa only [activeLaw, complementLaw,
      forwardTerminalMixedIncrementAtom] using hSplit
  have hFresh := selectiveTerminal_hasLaw_prod_fresh h.encoding
    (fun v ↦ columnBlockSums h.baseAt (columnBlockVector h.baseAt v))
    (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight)
    G hG (activeLaw.prod complementLaw) hSplit'
  have hRebracket := hasLaw_split_prod_direction hFresh id measurable_id
    Measure.map_id
  simp only [id_eq] at hRebracket
  have hfun :
      (fun omega ↦
        (((G (conditionalSelectiveRunVector h.encoding omega)).1,
            incrementShiftAfter (selectiveEncodedEndTime h.encoding) omega 0),
          (G (conditionalSelectiveRunVector h.encoding omega)).2)) =
        (fun omega ↦
          ((forwardIncrementTerminalActiveFreeVector h creationSet
              activeBases omega,
            incrementShiftAfter (selectiveEncodedEndTime h.encoding) omega 0),
          restrictColumnComplementRuns h.baseAt creationSet activeBases
            (columnBlockVector h.baseAt
              (conditionalSelectiveRunVector h.encoding omega)))) := by
    funext omega
    rfl
  rw [hfun] at hRebracket
  simpa only [activeLaw, complementLaw,
    forwardTerminalMixedIncrementAtom] using hRebracket

/-- Unnormalized path-space form of the forward active × fresh-direction ×
full-complement factorization. -/
theorem forwardTerminalActiveFullComplement_prod_fresh_truncated_path_map_law
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
        (fun s ↦
          ((forwardTerminalActiveFreeVector h creationSet activeBases s,
              forwardTerminalNextDirection h s),
            forwardTerminalFullComplementPath h creationSet activeBases s)) =
      simpleRandomWalkLaw
          (forwardTerminalMixedPathAtom h level creationSet
            externalLeft externalRight) •
        (((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
            directionLaw).prod
          (columnMixedComplementRunMeasure h.baseAt level creationSet
            activeBases externalLeft externalRight)) := by
  let f := fun v ↦ columnBlockSums h.baseAt (columnBlockVector h.baseAt v)
  let E := columnMixedBlockSumEvent h.baseAt level creationSet
    externalLeft externalRight
  let A := forwardTerminalMixedIncrementAtom h level creationSet
    externalLeft externalRight
  have hA : MeasurableSet A :=
    measurableSet_pastEvent (selectiveEncodedEndTime h.encoding) A (by
      exact selectiveTerminalRestrictedAtom_past h.encoding f E)
  have hStat : Measurable
      (fun s ↦
        ((forwardTerminalActiveFreeVector h creationSet activeBases s,
            forwardTerminalNextDirection h s),
          forwardTerminalFullComplementPath h creationSet activeBases s)) :=
    ((measurable_forwardTerminalActiveFreeVector h creationSet activeBases).prodMk
      (measurable_forwardTerminalNextDirection h)).prodMk
        (measurable_forwardTerminalFullComplementPath h creationSet activeBases)
  have hInc := forwardIncrementTerminalActiveFullComplement_prod_fresh_hasLaw
    h level creationSet activeBases externalLeft externalRight hEvent hwinning
  let J := fun omega ↦
    ((forwardIncrementTerminalActiveFreeVector h creationSet
        activeBases omega,
      incrementShiftAfter (selectiveEncodedEndTime h.encoding) omega 0),
    restrictColumnComplementRuns h.baseAt creationSet activeBases
      (columnBlockVector h.baseAt
        (conditionalSelectiveRunVector h.encoding omega)))
  have hJ : Measurable J :=
    ((measurable_forwardIncrementTerminalActiveFreeVector h creationSet
        activeBases).prodMk
      ((measurable_pi_apply 0).comp
        (measurable_incrementShiftAfter
          (measurable_selectiveEncodedEndTime h.encoding)))).prodMk
      ((measurable_restrictColumnComplementRuns h.baseAt creationSet
          activeBases).comp
        ((measurable_columnBlockVector h.baseAt).comp
          (measurable_conditionalSelectiveRunVector h.encoding)))
  have hPath : HasLaw
      (fun s ↦
        ((forwardTerminalActiveFreeVector h creationSet activeBases s,
            forwardTerminalNextDirection h s),
          forwardTerminalFullComplementPath h creationSet activeBases s))
      (((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
            directionLaw).prod
        (columnMixedComplementRunMeasure h.baseAt level creationSet
          activeBases externalLeft externalRight))
      simpleRandomWalkLaw[|forwardTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
    rw [simpleRandomWalkLaw,
      ← forwardTerminalMixedIncrementAtom_image h level creationSet
        externalLeft externalRight]
    apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk hA
    · exact hJ
    · intro omega _homega
      dsimp only [J]
      apply Prod.ext
      · apply Prod.ext
        · change restrictColumnActiveFreeBase h.baseAt creationSet activeBases
              (forwardTerminalBlockSums h (simpleRandomWalk omega)) =
            forwardIncrementTerminalActiveFreeVector h creationSet
              activeBases omega
          rw [forwardIncrementTerminalActiveFreeVector_apply,
            forwardTerminalBlockSums,
            pathConditionalSelectiveRunVector_simpleRandomWalk]
        · simpa only [forwardTerminalNextDirection, Function.comp_apply] using
            (liftIncrementStatisticToPath_simpleRandomWalk
              (fun omega ↦ incrementShiftAfter
                (selectiveEncodedEndTime h.encoding) omega 0) omega)
      · simp only [forwardTerminalFullComplementPath,
          pathConditionalSelectiveRunVector_simpleRandomWalk]
        rfl
    · simpa only [A] using hInc
  exact map_restrict_eq_smul_of_hasLaw_cond
    (measurableSet_forwardTerminalMixedPathAtom h level creationSet
      externalLeft externalRight) hStat hPath

/-! ### Primed/backward terminal phase -/

noncomputable def primedIncrementTerminalActiveFullComplementVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    (ℕ → Direction) →
      (ColumnActiveFreeBase h.baseAt creationSet activeBases → ℕ) ×
        ColumnComplementRuns h.baseAt creationSet activeBases :=
  fun omega ↦
    (primedIncrementTerminalActiveFreeVector h creationSet activeBases omega,
      restrictColumnComplementRuns h.baseAt creationSet activeBases
        (columnBlockVector h.baseAt
          (conditionalPrimedSelectiveRunVector h.encoding omega)))

theorem measurable_primedIncrementTerminalActiveFullComplementVector
    {m k start : ℕ} {specs : List (Bool × IncrementPair)}
    (h : YPrimedPhaseTerminalClockInputs m k start specs)
    (creationSet : Finset Site)
    (activeBases : Finset (ColumnRunBase h.baseAt)) :
    Measurable
      (primedIncrementTerminalActiveFullComplementVector h creationSet
        activeBases) := by
  exact (measurable_primedIncrementTerminalActiveFreeVector h creationSet
      activeBases).prodMk
    ((measurable_restrictColumnComplementRuns h.baseAt creationSet activeBases).comp
      ((measurable_columnBlockVector h.baseAt).comp
        (measurable_conditionalPrimedSelectiveRunVector h.encoding)))

theorem primedIncrementTerminalActiveFullComplement_truncated_hasLaw
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
    HasLaw
      (primedIncrementTerminalActiveFullComplementVector h creationSet
        activeBases)
      ((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
        (columnMixedComplementRunMeasure h.baseAt level creationSet
          activeBases externalLeft externalRight))
      incrementLaw[|primedTerminalMixedIncrementAtom h level creationSet
        externalLeft externalRight] := by
  have hraw := terminalActiveFullComplement_truncated_hasLaw
    incrementLaw h.baseAt (conditionalPrimedSelectiveRunVector h.encoding)
      (primedSelectiveTerminalLabelsEqFrom start specs)
      (measurableSet_primedSelectiveTerminalLabelsEqFrom start specs)
      (measurable_conditionalPrimedSelectiveRunVector h.encoding)
      (conditionalPrimedSelectiveRunVector_hasLaw h.encoding h.valid)
      level creationSet activeBases externalLeft externalRight hEvent hwinning
  change HasLaw
    (fun omega ↦
      ((fun b : ColumnActiveFreeBase h.baseAt creationSet activeBases ↦
          ∑ i, columnBlockVector h.baseAt
            (conditionalPrimedSelectiveRunVector h.encoding omega) b.1 i),
        restrictColumnComplementRuns h.baseAt creationSet activeBases
          (columnBlockVector h.baseAt
            (conditionalPrimedSelectiveRunVector h.encoding omega))))
    ((sourceTruncatedProfileMeasure level
        (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
      (columnMixedComplementRunMeasure h.baseAt level creationSet
        activeBases externalLeft externalRight))
    incrementLaw[|primedSelectiveTerminalLabelsEqFrom start specs ∩
      conditionalPrimedSelectiveRunVector h.encoding ⁻¹'
        ((fun v ↦ columnBlockSums h.baseAt
          (columnBlockVector h.baseAt v)) ⁻¹'
          columnMixedBlockSumEvent h.baseAt level creationSet
            externalLeft externalRight)]
  exact hraw

theorem primedIncrementTerminalActiveFullComplement_prod_fresh_hasLaw
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
    HasLaw
      (fun omega ↦
        ((primedIncrementTerminalActiveFreeVector h creationSet
            activeBases omega,
          incrementShiftAfter (primedEncodedEndTime h.encoding) omega 0),
        restrictColumnComplementRuns h.baseAt creationSet activeBases
          (columnBlockVector h.baseAt
            (conditionalPrimedSelectiveRunVector h.encoding omega))))
      (((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
            directionLaw).prod
        (columnMixedComplementRunMeasure h.baseAt level creationSet
          activeBases externalLeft externalRight))
      incrementLaw[|primedTerminalMixedIncrementAtom h level creationSet
        externalLeft externalRight] := by
  let activeLaw := sourceTruncatedProfileMeasure level
    (columnActiveFreeShape h.baseAt creationSet activeBases)
  let complementLaw := columnMixedComplementRunMeasure h.baseAt level
    creationSet activeBases externalLeft externalRight
  let G := fun v : Fin h.encoding.q → ℕ ↦
    ((fun b : ColumnActiveFreeBase h.baseAt creationSet activeBases ↦
        ∑ i, columnBlockVector h.baseAt v b.1 i),
      restrictColumnComplementRuns h.baseAt creationSet activeBases
        (columnBlockVector h.baseAt v))
  have hG : Measurable G := measurable_of_countable _
  have hSplit := primedIncrementTerminalActiveFullComplement_truncated_hasLaw
    h level creationSet activeBases externalLeft externalRight hEvent hwinning
  have hSplit' : HasLaw
      (fun omega ↦ G (conditionalPrimedSelectiveRunVector h.encoding omega))
      (activeLaw.prod complementLaw)
      incrementLaw[|primedTerminalRestrictedAtom h.encoding
        (fun v ↦ columnBlockSums h.baseAt (columnBlockVector h.baseAt v))
        (columnMixedBlockSumEvent h.baseAt level creationSet
          externalLeft externalRight)] := by
    have hfun :
        (fun omega ↦ G (conditionalPrimedSelectiveRunVector h.encoding omega)) =
          primedIncrementTerminalActiveFullComplementVector h creationSet
            activeBases := by
      funext omega
      rfl
    rw [hfun]
    simpa only [activeLaw, complementLaw,
      primedTerminalMixedIncrementAtom] using hSplit
  have hFresh := primedTerminal_hasLaw_prod_fresh h.encoding
    (fun v ↦ columnBlockSums h.baseAt (columnBlockVector h.baseAt v))
    (columnMixedBlockSumEvent h.baseAt level creationSet
      externalLeft externalRight)
    G hG (activeLaw.prod complementLaw) hSplit'
  have hRebracket := hasLaw_split_prod_direction hFresh id measurable_id
    Measure.map_id
  simp only [id_eq] at hRebracket
  have hfun :
      (fun omega ↦
        (((G (conditionalPrimedSelectiveRunVector h.encoding omega)).1,
            incrementShiftAfter (primedEncodedEndTime h.encoding) omega 0),
          (G (conditionalPrimedSelectiveRunVector h.encoding omega)).2)) =
        (fun omega ↦
          ((primedIncrementTerminalActiveFreeVector h creationSet
              activeBases omega,
            incrementShiftAfter (primedEncodedEndTime h.encoding) omega 0),
          restrictColumnComplementRuns h.baseAt creationSet activeBases
            (columnBlockVector h.baseAt
              (conditionalPrimedSelectiveRunVector h.encoding omega)))) := by
    funext omega
    rfl
  rw [hfun] at hRebracket
  simpa only [activeLaw, complementLaw,
    primedTerminalMixedIncrementAtom] using hRebracket

/-- Unnormalized path-space form for the independently conditioned backward
terminal phase.  The fresh direction is the original unswapped increment. -/
theorem primedTerminalActiveFullComplement_prod_fresh_truncated_path_map_law
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
        (fun s ↦
          ((primedTerminalActiveFreeVector h creationSet activeBases s,
              primedTerminalNextDirection h s),
            primedTerminalFullComplementPath h creationSet activeBases s)) =
      simpleRandomWalkLaw
          (primedTerminalMixedPathAtom h level creationSet
            externalLeft externalRight) •
        (((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
            directionLaw).prod
          (columnMixedComplementRunMeasure h.baseAt level creationSet
            activeBases externalLeft externalRight)) := by
  let f := fun v ↦ columnBlockSums h.baseAt (columnBlockVector h.baseAt v)
  let E := columnMixedBlockSumEvent h.baseAt level creationSet
    externalLeft externalRight
  let A := primedTerminalMixedIncrementAtom h level creationSet
    externalLeft externalRight
  have hA : MeasurableSet A :=
    measurableSet_pastEvent (primedEncodedEndTime h.encoding) A (by
      exact primedTerminalRestrictedAtom_past h.encoding f E)
  have hStat : Measurable
      (fun s ↦
        ((primedTerminalActiveFreeVector h creationSet activeBases s,
            primedTerminalNextDirection h s),
          primedTerminalFullComplementPath h creationSet activeBases s)) :=
    ((measurable_primedTerminalActiveFreeVector h creationSet activeBases).prodMk
      (measurable_primedTerminalNextDirection h)).prodMk
        (measurable_primedTerminalFullComplementPath h creationSet activeBases)
  have hInc := primedIncrementTerminalActiveFullComplement_prod_fresh_hasLaw
    h level creationSet activeBases externalLeft externalRight hEvent hwinning
  let J := fun omega ↦
    ((primedIncrementTerminalActiveFreeVector h creationSet
        activeBases omega,
      incrementShiftAfter (primedEncodedEndTime h.encoding) omega 0),
    restrictColumnComplementRuns h.baseAt creationSet activeBases
      (columnBlockVector h.baseAt
        (conditionalPrimedSelectiveRunVector h.encoding omega)))
  have hJ : Measurable J :=
    ((measurable_primedIncrementTerminalActiveFreeVector h creationSet
        activeBases).prodMk
      ((measurable_pi_apply 0).comp
        (measurable_incrementShiftAfter
          (measurable_primedEncodedEndTime h.encoding)))).prodMk
      ((measurable_restrictColumnComplementRuns h.baseAt creationSet
          activeBases).comp
        ((measurable_columnBlockVector h.baseAt).comp
          (measurable_conditionalPrimedSelectiveRunVector h.encoding)))
  have hPath : HasLaw
      (fun s ↦
        ((primedTerminalActiveFreeVector h creationSet activeBases s,
            primedTerminalNextDirection h s),
          primedTerminalFullComplementPath h creationSet activeBases s))
      (((sourceTruncatedProfileMeasure level
          (columnActiveFreeShape h.baseAt creationSet activeBases)).prod
            directionLaw).prod
        (columnMixedComplementRunMeasure h.baseAt level creationSet
          activeBases externalLeft externalRight))
      simpleRandomWalkLaw[|primedTerminalMixedPathAtom h level creationSet
        externalLeft externalRight] := by
    rw [simpleRandomWalkLaw,
      ← primedTerminalMixedIncrementAtom_image h level creationSet
        externalLeft externalRight]
    apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk hA
    · exact hJ
    · intro omega _homega
      dsimp only [J]
      apply Prod.ext
      · apply Prod.ext
        · change restrictColumnActiveFreeBase h.baseAt creationSet activeBases
              (primedTerminalBlockSums h (simpleRandomWalk omega)) =
            primedIncrementTerminalActiveFreeVector h creationSet
              activeBases omega
          rw [primedIncrementTerminalActiveFreeVector_apply,
            primedTerminalBlockSums,
            pathConditionalPrimedSelectiveRunVector_simpleRandomWalk]
        · simpa only [primedTerminalNextDirection, Function.comp_apply] using
            (liftIncrementStatisticToPath_simpleRandomWalk
              (fun omega ↦ incrementShiftAfter
                (primedEncodedEndTime h.encoding) omega 0) omega)
      · simp only [primedTerminalFullComplementPath,
          pathConditionalPrimedSelectiveRunVector_simpleRandomWalk]
        rfl
    · simpa only [A] using hInc
  exact map_restrict_eq_smul_of_hasLaw_cond
    (measurableSet_primedTerminalMixedPathAtom h level creationSet
      externalLeft externalRight) hStat hPath

end Erdos1166.HLOZColumnFullComplement

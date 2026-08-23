import ErdosProblems.Erdos1166.Erdos1166HLOZIncompleteStoppedBlocks

/-!
# Grouping a stopped run vector by its external base

This file contains only the deterministic reindexing needed in the stopped-law
audit.  It separates the `q + 1` geometric run coordinates into the fibers of
`stoppedExternalBaseAt`, proves that the iid product measure is preserved by
that reindexing, and then sums each fiber to obtain the corresponding product
of negative-binomial laws.  No mixed stopped-event constraint is used here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1166.HLOZIncompleteStoppedBlocks

open HLOZDecomposition HLOZReconstruction HLOZActualStopped HLOZPrimedStopped

/-- Every chronological stopped-run coordinate is uniquely the pair of its
external base and its position inside that base's fiber. -/
noncomputable def stoppedExternalSigmaEquiv {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    Fin (q + 1) ≃ Σ b : StoppedExternalBase a labels,
      StoppedExternalIndex a labels b where
  toFun i :=
    ⟨⟨stoppedExternalBaseAt a labels i,
        stoppedExternalBaseAt_mem a labels i⟩, ⟨i, rfl⟩⟩
  invFun z := z.2.1
  left_inv i := rfl
  right_inv z := by
    rcases z with ⟨b, i, hi⟩
    have hb : (⟨stoppedExternalBaseAt a labels i,
        stoppedExternalBaseAt_mem a labels i⟩ :
        StoppedExternalBase a labels) = b := Subtype.ext hi
    cases hb
    rfl

/-- The same reindexing, expressed directly on dependent vectors. -/
noncomputable def stoppedPaperBlockEquiv {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    (Fin (q + 1) → ℕ) ≃
      (∀ b : StoppedExternalBase a labels,
        StoppedExternalIndex a labels b → ℕ) :=
  (Equiv.piCongrLeft
    (fun _ : Σ b : StoppedExternalBase a labels,
      StoppedExternalIndex a labels b ↦ ℕ)
    (stoppedExternalSigmaEquiv a labels)).trans
    (Equiv.piCurry
      (fun (b : StoppedExternalBase a labels)
        (_ : StoppedExternalIndex a labels b) ↦ ℕ))

/-- The block grouping is a measurable equivalence. -/
noncomputable def stoppedPaperBlockMeasurableEquiv {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    (Fin (q + 1) → ℕ) ≃ᵐ
      (∀ b : StoppedExternalBase a labels,
        StoppedExternalIndex a labels b → ℕ) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : Σ b : StoppedExternalBase a labels,
      StoppedExternalIndex a labels b ↦ ℕ)
    (stoppedExternalSigmaEquiv a labels)).trans
    (MeasurableEquiv.piCurry
      (fun (b : StoppedExternalBase a labels)
        (_ : StoppedExternalIndex a labels b) ↦ ℕ))

@[simp] theorem stoppedPaperBlockMeasurableEquiv_apply {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) :
    stoppedPaperBlockMeasurableEquiv a labels v =
      stoppedPaperBlockVector a labels v := by
  let e := stoppedExternalSigmaEquiv a labels
  apply (Equiv.piCurry
    (fun (b : StoppedExternalBase a labels)
      (_ : StoppedExternalIndex a labels b) ↦ ℕ)).symm.injective
  funext z
  obtain ⟨j, rfl⟩ := e.surjective z
  change (Equiv.piCongrLeft (fun _ : Σ b : StoppedExternalBase a labels,
      StoppedExternalIndex a labels b ↦ ℕ) e v) (e j) = v j
  exact Equiv.piCongrLeft_apply_apply _ _ _ _

theorem measurable_stoppedPaperBlockVector {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    Measurable (stoppedPaperBlockVector a labels) := by
  convert (stoppedPaperBlockMeasurableEquiv a labels).measurable using 1
  funext v
  exact (stoppedPaperBlockMeasurableEquiv_apply a labels v).symm

/-- The nested iid geometric product: first over external bases, then over
the chronological coordinates belonging to each base. -/
noncomputable def stoppedBlockRunMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    Measure (∀ b : StoppedExternalBase a labels,
      StoppedExternalIndex a labels b → ℕ) :=
  Measure.pi fun _b ↦ Measure.pi fun _i ↦ HLOZUrn.runMeasure

instance stoppedBlockRunMeasure_isProbabilityMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    IsProbabilityMeasure (stoppedBlockRunMeasure a labels) := by
  unfold stoppedBlockRunMeasure
  infer_instance

/-- Reindexing the flat iid run vector by external base gives exactly the
nested iid geometric product. -/
theorem runVectorMeasure_map_stoppedPaperBlockVector {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    (HLOZUrn.runVectorMeasure (q + 1)).map
        (stoppedPaperBlockVector a labels) =
      stoppedBlockRunMeasure a labels := by
  let e := stoppedExternalSigmaEquiv a labels
  let E := MeasurableEquiv.piCongrLeft
    (fun _ : Σ b : StoppedExternalBase a labels,
      StoppedExternalIndex a labels b ↦ ℕ) e
  let C :
      ((z : Σ b : StoppedExternalBase a labels,
          StoppedExternalIndex a labels b) → ℕ) ≃ᵐ
        (∀ b : StoppedExternalBase a labels,
          StoppedExternalIndex a labels b → ℕ) :=
    MeasurableEquiv.piCurry
      (fun (b : StoppedExternalBase a labels)
        (_ : StoppedExternalIndex a labels b) ↦ ℕ)
  have hfun : stoppedPaperBlockVector a labels = C ∘ E := by
    funext v b i
    symm
    exact congrFun (congrFun
      (stoppedPaperBlockMeasurableEquiv_apply a labels v) b) i
  rw [hfun, HLOZUrn.runVectorMeasure, ← Measure.infinitePi_eq_pi]
  rw [← Measure.map_map C.measurable E.measurable]
  have hE : (Measure.infinitePi fun _ : Fin (q + 1) ↦
      HLOZUrn.runMeasure).map E =
      Measure.infinitePi (fun _ : Σ b : StoppedExternalBase a labels,
        StoppedExternalIndex a labels b ↦ HLOZUrn.runMeasure) := by
    exact Measure.infinitePi_map_piCongrLeft
      (fun _ : Σ b : StoppedExternalBase a labels,
        StoppedExternalIndex a labels b ↦ HLOZUrn.runMeasure) e
  rw [hE]
  have hC : (Measure.infinitePi
      (fun _ : Σ b : StoppedExternalBase a labels,
        StoppedExternalIndex a labels b ↦ HLOZUrn.runMeasure)).map C =
      Measure.infinitePi (fun _b : StoppedExternalBase a labels ↦
        Measure.infinitePi (fun _i : StoppedExternalIndex a labels _b ↦
          HLOZUrn.runMeasure)) := by
    exact Measure.infinitePi_map_piCurry
      (fun (_b : StoppedExternalBase a labels)
        (_i : StoppedExternalIndex a labels _b) ↦ HLOZUrn.runMeasure)
  rw [hC]
  unfold stoppedBlockRunMeasure
  rw [Measure.infinitePi_eq_pi]
  congr 1
  funext b
  rw [Measure.infinitePi_eq_pi]

/-- Sum all geometric holding-run coordinates assigned to each external
base. -/
def stoppedPaperBlockSums {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (w : ∀ b : StoppedExternalBase a labels,
      StoppedExternalIndex a labels b → ℕ) :
    StoppedExternalBase a labels → ℕ :=
  fun b ↦ ∑ i, w b i

theorem measurable_stoppedPaperBlockSums {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    Measurable (stoppedPaperBlockSums a labels) :=
  measurable_of_countable _

/-- The product of the negative-binomial laws, with one shape parameter per
external-base fiber. -/
noncomputable def stoppedBlockNegBinMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    Measure (StoppedExternalBase a labels → ℕ) :=
  Measure.pi fun b ↦
    HLOZUrn.negBinMeasure (Fintype.card (StoppedExternalIndex a labels b))

instance stoppedBlockNegBinMeasure_isProbabilityMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    IsProbabilityMeasure (stoppedBlockNegBinMeasure a labels) := by
  unfold stoppedBlockNegBinMeasure
  infer_instance

/-- Summing one reindexed iid fiber gives its negative-binomial law. -/
theorem stoppedBlockSum_map_eq_negBinMeasure {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (b : StoppedExternalBase a labels) :
    (Measure.pi fun _ : StoppedExternalIndex a labels b ↦
        HLOZUrn.runMeasure).map (fun w ↦ ∑ i, w i) =
      HLOZUrn.negBinMeasure
        (Fintype.card (StoppedExternalIndex a labels b)) := by
  let I := StoppedExternalIndex a labels b
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let E := MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℕ) e
  have hpres : MeasurePreserving E
      (HLOZUrn.runVectorMeasure (Fintype.card I))
      (Measure.pi fun _ : I ↦ HLOZUrn.runMeasure) := by
    unfold HLOZUrn.runVectorMeasure
    exact measurePreserving_piCongrLeft (fun _ : I ↦ HLOZUrn.runMeasure) e
  have hsum : (fun w : I → ℕ ↦ ∑ i, w i) ∘ E =
      HLOZUrn.runSum (Fintype.card I) := by
    funext v
    unfold HLOZUrn.runSum
    simp only [Function.comp_apply, E, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_eq_cast]
    change (∑ i : I, v (e.symm i)) = ∑ k, v k
    exact e.symm.sum_comp v
  rw [← hpres.map_eq, Measure.map_map
    (measurable_of_countable (fun w : I → ℕ ↦ ∑ i, w i))
    E.measurable]
  rw [hsum]
  rfl

/-- Coordinatewise block summation maps the nested geometric product to the
product of the appropriate negative-binomial laws. -/
theorem stoppedBlockRunMeasure_map_blockSums {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    (stoppedBlockRunMeasure a labels).map
        (stoppedPaperBlockSums a labels) =
      stoppedBlockNegBinMeasure a labels := by
  unfold stoppedBlockRunMeasure stoppedPaperBlockSums
    stoppedBlockNegBinMeasure
  rw [Measure.pi_map_pi fun _ ↦
    (measurable_of_countable
      (fun w : StoppedExternalIndex a labels _ → ℕ ↦ ∑ i, w i)).aemeasurable]
  congr 1
  funext b
  exact stoppedBlockSum_map_eq_negBinMeasure a labels b

/-- Direct flat-vector formulation: group by external base and sum each
block. -/
theorem runVectorMeasure_map_stoppedPaperBlockSums {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    (HLOZUrn.runVectorMeasure (q + 1)).map
        (fun v ↦ stoppedPaperBlockSums a labels
          (stoppedPaperBlockVector a labels v)) =
      stoppedBlockNegBinMeasure a labels := by
  change (HLOZUrn.runVectorMeasure (q + 1)).map
      (stoppedPaperBlockSums a labels ∘ stoppedPaperBlockVector a labels) = _
  rw [← Measure.map_map (measurable_stoppedPaperBlockSums a labels)
    (measurable_stoppedPaperBlockVector a labels)]
  rw [runVectorMeasure_map_stoppedPaperBlockVector,
    stoppedBlockRunMeasure_map_blockSums]

/-- The exact per-base sum condition corresponding to the mixed (4.7)/(4.8)
domino constraint, once the two external local-time contributions have been
fixed.  On a domino meeting `C`, the resulting local-time maximum is `m` and
the level-`m` endpoint is prescribed by membership in `C`; on every disjoint
domino the maximum is strictly below `m`. -/
def stoppedMixedBlockSumEvent {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (m : ℕ) (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    Set (StoppedExternalBase a labels → ℕ) :=
  {u | ∀ b,
    if _hC : b.1 ∈ C ∨ b.1 + paperE1 ∈ C then
      max (externalLeft b + u b) (externalRight b + u b) = m ∧
        (externalLeft b + u b = m ↔ b.1 ∈ C) ∧
        (externalRight b + u b = m ↔ b.1 + paperE1 ∈ C)
    else
      max (externalLeft b + u b) (externalRight b + u b) < m}

@[simp] theorem mem_stoppedMixedBlockSumEvent_iff {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (m : ℕ) (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (u : StoppedExternalBase a labels → ℕ) :
    u ∈ stoppedMixedBlockSumEvent a labels m C externalLeft externalRight ↔
      ∀ b,
        if _hC : b.1 ∈ C ∨ b.1 + paperE1 ∈ C then
          max (externalLeft b + u b) (externalRight b + u b) = m ∧
            (externalLeft b + u b = m ↔ b.1 ∈ C) ∧
            (externalRight b + u b = m ↔ b.1 + paperE1 ∈ C)
        else
          max (externalLeft b + u b) (externalRight b + u b) < m := by
  rfl

theorem measurableSet_stoppedMixedBlockSumEvent {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (m : ℕ) (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    MeasurableSet
      (stoppedMixedBlockSumEvent a labels m C externalLeft externalRight) :=
  (Set.to_countable _).measurableSet

/-- The finite allowed set for one mixed block-sum coordinate.  On a domino
meeting `C` this is an equality/endpoint constraint; on a disjoint domino it
is the corresponding strict lower truncation. -/
noncomputable def stoppedMixedBlockValues {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (m : ℕ) (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    ∀ b : StoppedExternalBase a labels, Finset ℕ :=
  fun b ↦ (Finset.range (m + 1)).filter fun u ↦
    if _hC : b.1 ∈ C ∨ b.1 + paperE1 ∈ C then
      max (externalLeft b + u) (externalRight b + u) = m ∧
        (externalLeft b + u = m ↔ b.1 ∈ C) ∧
        (externalRight b + u = m ↔ b.1 + paperE1 ∈ C)
    else
      max (externalLeft b + u) (externalRight b + u) < m

/-- The mixed block-sum event is exactly the product of its equality factors
on creation-intersecting dominoes and its truncated factors on disjoint
dominoes. -/
theorem stoppedMixedBlockSumEvent_eq_blockEvent {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (m : ℕ) (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    stoppedMixedBlockSumEvent a labels m C externalLeft externalRight =
      HLOZConditionalProduct.blockEvent
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight) := by
  ext u
  constructor
  · intro hu b
    rw [stoppedMixedBlockValues, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hu b⟩
    have hb := hu b
    split at hb <;> omega
  · intro hu b
    exact (Finset.mem_filter.mp (hu b)).2

/-- Conditioning a finite product probability measure on a product of
finite coordinate events preserves the product structure. -/
theorem pi_cond_blockEvent_eq_pi_cond
    {B : Type*} [Fintype B]
    {X : B → Type*} [∀ b, MeasurableSpace (X b)]
    [∀ b, MeasurableSingletonClass (X b)] [∀ b, Countable (X b)]
    (μ : ∀ b, Measure (X b)) [∀ b, IsProbabilityMeasure (μ b)]
    (E : ∀ b, Finset (X b))
    (hpos : ∀ b, μ b (E b : Set (X b)) ≠ 0) :
    (Measure.pi μ)[|HLOZConditionalProduct.blockEvent E] =
      Measure.pi (fun b ↦ (μ b)[|(E b : Set (X b))]) := by
  letI (b : B) : IsProbabilityMeasure ((μ b)[|(E b : Set (X b))]) :=
    cond_isProbabilityMeasure (hpos b)
  have hEvent : HLOZConditionalProduct.blockEvent E =
      Set.pi Set.univ fun b ↦ (E b : Set (X b)) := by
    ext x
    simp [HLOZConditionalProduct.blockEvent]
  have hmEvent : MeasurableSet (HLOZConditionalProduct.blockEvent E) := by
    rw [hEvent]
    exact MeasurableSet.univ_pi (fun b ↦ (E b).measurableSet)
  apply Measure.ext_of_singleton
  intro x
  rw [cond_apply hmEvent, Measure.pi_singleton]
  rw [show HLOZConditionalProduct.blockEvent E ∩ {x} =
      Set.pi Set.univ (fun b ↦ (E b : Set (X b)) ∩ {x b}) by
    ext y
    simp only [Set.mem_inter_iff, HLOZConditionalProduct.blockEvent,
      Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ,
      true_implies]
    constructor
    · rintro ⟨hy, rfl⟩ b
      exact ⟨hy b, rfl⟩
    · intro hy
      have hyx : y = x := funext fun b ↦ (hy b).2
      exact ⟨fun b ↦ (hy b).1, hyx⟩]
  rw [hEvent, Measure.pi_pi, Measure.pi_pi]
  simp_rw [cond_apply (E _).measurableSet]
  rw [Finset.prod_mul_distrib]
  congr 1
  apply ENNReal.prod_inv_distrib
  intro i _hi _j _hj _hij
  exact Or.inl (hpos i)

/-- Product factorization of the conditioned mixed block-sum law. -/
theorem stoppedBlockNegBinMeasure_cond_mixed_eq_pi_cond {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (m : ℕ) (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (hpos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    (stoppedBlockNegBinMeasure a labels)[|
      stoppedMixedBlockSumEvent a labels m C
        externalLeft externalRight] =
      Measure.pi (fun b ↦
        (HLOZUrn.negBinMeasure
          (Fintype.card (StoppedExternalIndex a labels b)))[|
            (stoppedMixedBlockValues a labels m C
              externalLeft externalRight b : Set ℕ)]) := by
  rw [stoppedMixedBlockSumEvent_eq_blockEvent]
  unfold stoppedBlockNegBinMeasure
  exact pi_cond_blockEvent_eq_pi_cond _ _ hpos

/-- Conditioning on an event determined only by the per-base block sums
commutes with the block-sum pushforward.  This is the probabilistic half of
the mixed stopped-event reduction: once a stopped source finset is identified
with the preimage of a measurable sum event, its block sums have the
correspondingly conditioned product negative-binomial law. -/
theorem runVectorMeasure_cond_map_stoppedPaperBlockSums {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (E : Set (StoppedExternalBase a labels → ℕ))
    (hE : MeasurableSet E) :
    ((HLOZUrn.runVectorMeasure (q + 1))[|
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v)) ⁻¹' E]).map
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v)) =
      (stoppedBlockNegBinMeasure a labels)[|E] := by
  let f := fun v ↦ stoppedPaperBlockSums a labels
    (stoppedPaperBlockVector a labels v)
  have hf : Measurable f :=
    (measurable_stoppedPaperBlockSums a labels).comp
      (measurable_stoppedPaperBlockVector a labels)
  have hmapCond :
      ((HLOZUrn.runVectorMeasure (q + 1))[|f ⁻¹' E]).map f =
        ((HLOZUrn.runVectorMeasure (q + 1)).map f)[|E] := by
    ext s hs
    rw [Measure.map_apply hf hs, cond_apply (hE.preimage hf), cond_apply hE,
      Measure.map_apply hf hE, Measure.map_apply hf (hE.inter hs)]
    rfl
  rw [hmapCond]
  change ((HLOZUrn.runVectorMeasure (q + 1)).map
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v)))[|E] = _
  rw [runVectorMeasure_map_stoppedPaperBlockSums]

/-- Has-law formulation of
`runVectorMeasure_cond_map_stoppedPaperBlockSums`. -/
theorem stoppedPaperBlockSums_hasLaw_conditional {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (E : Set (StoppedExternalBase a labels → ℕ))
    (hE : MeasurableSet E) :
    HasLaw
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v))
      ((stoppedBlockNegBinMeasure a labels)[|E])
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (fun v ↦ stoppedPaperBlockSums a labels
          (stoppedPaperBlockVector a labels v)) ⁻¹' E]) := by
  refine ⟨((measurable_stoppedPaperBlockSums a labels).comp
    (measurable_stoppedPaperBlockVector a labels)).aemeasurable, ?_⟩
  exact runVectorMeasure_cond_map_stoppedPaperBlockSums a labels E hE

/-- Finset-facing transfer lemma for the stopped-source partitions.  A caller
only has to prove the deterministic identification of its admissible vector
finset with the preimage of the desired block-sum event. -/
theorem stoppedPaperBlockSums_hasLaw_conditional_finset {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (A : Finset (Fin (q + 1) → ℕ))
    (E : Set (StoppedExternalBase a labels → ℕ))
    (hE : MeasurableSet E)
    (hAE : (A : Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v)) ⁻¹' E) :
    HasLaw
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v))
      ((stoppedBlockNegBinMeasure a labels)[|E])
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (A : Set (Fin (q + 1) → ℕ))]) := by
  rw [hAE]
  exact stoppedPaperBlockSums_hasLaw_conditional a labels E hE

/-- Specialized mixed-domino version of the finset transfer lemma.  The
sole source-specific premise is now the deterministic stopped reconstruction
identity `hA`; the target law is the product negative-binomial law conditioned
by the exact mixed (4.7)/(4.8) block-sum event. -/
theorem stoppedPaperBlockSums_hasLaw_mixed_finset {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (m : ℕ) (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (A : Finset (Fin (q + 1) → ℕ))
    (hA : (A : Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v)) ⁻¹'
        stoppedMixedBlockSumEvent a labels m C
          externalLeft externalRight) :
    HasLaw
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v))
      ((stoppedBlockNegBinMeasure a labels)[|
        stoppedMixedBlockSumEvent a labels m C
          externalLeft externalRight])
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (A : Set (Fin (q + 1) → ℕ))]) := by
  exact stoppedPaperBlockSums_hasLaw_conditional_finset a labels A
    (stoppedMixedBlockSumEvent a labels m C externalLeft externalRight)
    (measurableSet_stoppedMixedBlockSumEvent a labels m C
      externalLeft externalRight) hA

/-- Fully factorized mixed stopped law: creation-intersecting bases carry
their equality-coordinate conditional negative-binomial laws, while disjoint
bases carry their strict-truncation conditional negative-binomial laws. -/
theorem stoppedPaperBlockSums_hasLaw_mixed_product_finset {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (m : ℕ) (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (A : Finset (Fin (q + 1) → ℕ))
    (hA : (A : Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v)) ⁻¹'
        stoppedMixedBlockSumEvent a labels m C
          externalLeft externalRight)
    (hpos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    HasLaw
      (fun v ↦ stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v))
      (Measure.pi (fun b ↦
        (HLOZUrn.negBinMeasure
          (Fintype.card (StoppedExternalIndex a labels b)))[|
            (stoppedMixedBlockValues a labels m C
              externalLeft externalRight b : Set ℕ)]))
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (A : Set (Fin (q + 1) → ℕ))]) := by
  rw [← stoppedBlockNegBinMeasure_cond_mixed_eq_pi_cond
    a labels m C externalLeft externalRight hpos]
  exact stoppedPaperBlockSums_hasLaw_mixed_finset a labels m C
    externalLeft externalRight A hA

end Erdos1166.HLOZIncompleteStoppedBlocks

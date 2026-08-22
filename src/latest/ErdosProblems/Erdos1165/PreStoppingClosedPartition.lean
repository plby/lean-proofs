import ErdosProblems.Erdos1165.SpatialInsertionClosedFiber

open scoped BigOperators ENNReal

/-!
# Prefix-free closed pre-stopping partitions

The closed-prefix event in this module appends an auxiliary retained closer to
the insertion word.  That closer makes the variable-length family prefix-free,
so its finite unions are measurable disjoint unions whose `fairSteps` mass can
be transported exactly to the capped coordinate weights and their
away-domino-total marginals.

Identification of these deterministic closed-prefix events with the past at a
random stopping time is deliberately separate; no stopped-past disintegration
is asserted here.
-/

namespace Erdos1165.PreStoppingFiber

open MeasureTheory
open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber

/-! Exact finite pre-stopping fibres of closed insertion words. -/

/-- The finite block prefix obtained by pairing the first `2n` increments. -/
def pairedBlockPrefix (n : ℕ) (ω : StepPath) : List Block :=
  List.ofFn (pairDirections (stepPrefix (2 * n) ω))

@[simp] theorem pairedBlockPrefix_length (n : ℕ) (ω : StepPath) :
    (pairedBlockPrefix n ω).length = n := by
  simp [pairedBlockPrefix]

@[simp] theorem pairDirections_blockListDirections (w : List Block) :
    pairDirections (blockListDirections w) = fun k ↦ w.get k := by
  funext k
  apply Prod.ext
  · simp [pairDirections, blockListDirections, flattenBlockVector]
  · have hk : (2 * k.val + 1) / 2 = k.val := by omega
    simp [pairDirections, blockListDirections, flattenBlockVector, hk]

theorem pairedBlockPrefix_eq_of_mem_closedGapCylinder
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (q : Fin (i + 1) → ℕ) (a : RetainedBlock o) {ω : StepPath}
    (hω : ω ∈ closedGapCylinder r q a) :
    pairedBlockPrefix (closedGapWord r q a).length ω = closedGapWord r q a := by
  unfold closedGapCylinder at hω
  unfold pairedBlockPrefix
  rw [hω, pairDirections_blockListDirections]
  exact List.ofFn_get _

theorem pairedBlockPrefix_mono {ω : StepPath} {n m : ℕ} (hnm : n ≤ m) :
    pairedBlockPrefix n ω <+: pairedBlockPrefix m ω := by
  rw [List.prefix_iff_eq_take]
  rw [pairedBlockPrefix_length]
  apply List.ext_get
  · simp [pairedBlockPrefix, hnm]
  · intro k hk₁ hk₂
    simp only [pairedBlockPrefix, List.get_eq_getElem, List.getElem_ofFn,
      List.getElem_take]
    rfl

/-- Appending the auxiliary retained block makes closed insertion words
prefix-free, even though their lengths depend on the gap vector. -/
theorem closedGapWord_prefix_free
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (a : RetainedBlock o) {q q' : Fin (i + 1) → ℕ}
    (hprefix : closedGapWord r q a <+: closedGapWord r q' a) : q = q' := by
  classical
  rcases hprefix with ⟨t, ht⟩
  have hfilter := congrArg (deleteRemovableBlocks o) ht
  have hclosed (u : Fin (i + 1) → ℕ) :
      deleteRemovableBlocks o (closedGapWord r u a) = retainedWord r ++ [(a : Block)] := by
    rw [closedGapWord]
    have hi := deleteRemovableBlocks_insertGapVector r u
    unfold deleteRemovableBlocks at hi ⊢
    rw [List.filter_append, hi]
    simp [a.property]
  rw [deleteRemovableBlocks, List.filter_append] at hfilter
  change deleteRemovableBlocks o (closedGapWord r q a) ++
      deleteRemovableBlocks o t =
    deleteRemovableBlocks o (closedGapWord r q' a) at hfilter
  rw [hclosed, hclosed] at hfilter
  have htfilter : deleteRemovableBlocks o t = [] := by
    apply List.append_cancel_left (as := retainedWord r ++ [(a : Block)])
    simpa using hfilter
  have ht_nil : t = [] := by
    by_contra htne
    have hlast_mem : t.getLast htne ∈ t := List.getLast_mem htne
    have hlast : t.getLast htne = (a : Block) := by
      have hleftne : closedGapWord r q a ++ t ≠ [] := by
        simp [closedGapWord]
      have hrightne : closedGapWord r q' a ≠ [] := by
        simp [closedGapWord]
      have hlast_eq := List.getLast_congr hleftne hrightne ht
      rw [List.getLast_append_of_right_ne_nil _ _ htne] at hlast_eq
      simpa [closedGapWord] using hlast_eq
    have hmemfilter : (a : Block) ∈ deleteRemovableBlocks o t := by
      rw [deleteRemovableBlocks, List.mem_filter]
      constructor
      · rw [← hlast]
        exact hlast_mem
      · simp [a.property]
    rw [htfilter] at hmemfilter
    have hnot : (a : Block) ∉ ([] : List Block) := by simp
    exact hnot hmemfilter
  subst t
  simp only [List.append_nil] at ht
  apply insertGapVector_injective r
  unfold closedGapWord at ht
  exact List.append_cancel_right ht

/-- Distinct gap vectors give disjoint closed cylinders, despite the varying
cylinder lengths. -/
theorem disjoint_closedGapCylinder_of_ne
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (a : RetainedBlock o) {q q' : Fin (i + 1) → ℕ} (hqq' : q ≠ q') :
    Disjoint (closedGapCylinder r q a) (closedGapCylinder r q' a) := by
  rw [Set.disjoint_left]
  intro ω hω hω'
  apply hqq'
  rcases le_total (closedGapWord r q a).length (closedGapWord r q' a).length with hle | hle
  · apply closedGapWord_prefix_free r a
    rw [← pairedBlockPrefix_eq_of_mem_closedGapCylinder r q a hω,
      ← pairedBlockPrefix_eq_of_mem_closedGapCylinder r q' a hω']
    exact pairedBlockPrefix_mono hle
  · symm
    apply closedGapWord_prefix_free r a
    rw [← pairedBlockPrefix_eq_of_mem_closedGapCylinder r q' a hω',
      ← pairedBlockPrefix_eq_of_mem_closedGapCylinder r q a hω]
    exact pairedBlockPrefix_mono hle

theorem measurableSet_closedGapCylinder
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (q : Fin (i + 1) → ℕ) (a : RetainedBlock o) :
    MeasurableSet (closedGapCylinder r q a) := by
  unfold closedGapCylinder
  exact measurableSet_eq_fun (measurable_stepPrefix _) measurable_const

/-! ## The finite capped measurable partition -/

/-- One admissible atom of the capped closed fibre; inadmissible coordinates
are represented by the empty set so the indexing type stays a finite product. -/
noncomputable def closedCappedAtom
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (q : CappedCoordinates i cap) : Set StepPath := by
  classical
  exact if DominoTruncation x r m D (fun k ↦ (q k : ℕ)) then
    closedGapCylinder r (fun k ↦ (q k : ℕ)) a else ∅

theorem measurableSet_closedCappedAtom
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (q : CappedCoordinates i cap) :
    MeasurableSet (closedCappedAtom x r m cap D a q) := by
  classical
  unfold closedCappedAtom
  split <;> simp [measurableSet_closedGapCylinder]

theorem pairwise_disjoint_closedCappedAtom
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) :
    Pairwise fun q q' : CappedCoordinates i cap ↦
      Disjoint (closedCappedAtom x r m cap D a q)
        (closedCappedAtom x r m cap D a q') := by
  classical
  intro q q' hqq'
  have hnat : (fun k ↦ (q k : ℕ)) ≠ fun k ↦ (q' k : ℕ) := by
    intro h
    apply hqq'
    funext k
    apply Fin.ext
    exact congrFun h k
  unfold closedCappedAtom
  split <;> split
  · exact disjoint_closedGapCylinder_of_ne r a hnat
  · simp
  · simp
  · simp

theorem fairSteps_closedCappedAtom
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (q : CappedCoordinates i cap) :
    fairSteps (closedCappedAtom x r m cap D a q) =
      ENNReal.ofReal
        (closedConditionedMass x r m D (fun k ↦ (q k : ℕ)) a) := by
  classical
  by_cases hq : DominoTruncation x r m D (fun k ↦ (q k : ℕ))
  · rw [closedCappedAtom, if_pos hq, closedConditionedMass, if_pos hq,
      fairSteps_closedGapCylinder]
    rfl
  · rw [closedCappedAtom, if_neg hq, closedConditionedMass, if_neg hq]
    simp

theorem closedConditionedMass_nonneg
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (q : Fin (i + 1) → ℕ) (a : RetainedBlock o) :
    0 ≤ closedConditionedMass x r m D q a := by
  classical
  unfold closedConditionedMass
  split
  · unfold closedGapMass uniformBlockWordMass
    positivity
  · simp

/-- The measurable finite union of all capped insertion vectors satisfying
the away-from-`D` endpoint cutoffs. -/
noncomputable def closedCappedFiberEvent
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) : Set StepPath :=
  ⋃ q : CappedCoordinates i cap, closedCappedAtom x r m cap D a q

theorem measurableSet_closedCappedFiberEvent
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) :
    MeasurableSet (closedCappedFiberEvent x r m cap D a) := by
  classical
  exact MeasurableSet.iUnion fun q ↦
    measurableSet_closedCappedAtom x r m cap D a q

/-- Exact `fairSteps` mass of the finite capped pre-stopping fibre. -/
theorem fairSteps_closedCappedFiberEvent
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) :
    fairSteps (closedCappedFiberEvent x r m cap D a) =
      ENNReal.ofReal (closedCappedPartition x r m cap D a) := by
  classical
  unfold closedCappedFiberEvent
  rw [measure_iUnion (pairwise_disjoint_closedCappedAtom x r m cap D a)
    (measurableSet_closedCappedAtom x r m cap D a)]
  simp_rw [fairSteps_closedCappedAtom]
  rw [tsum_fintype]
  unfold closedCappedPartition
  rw [ENNReal.ofReal_sum_of_nonneg]
  intro q _
  exact closedConditionedMass_nonneg x r m D (fun k ↦ (q k : ℕ)) a

/-! ## Regrouping the same partition by away-domino totals -/

/-- A capped atom selected by a prescribed vector of totals on the dominoes
away from `D`.  Coordinates on dominoes based in `D` are not constrained. -/
noncomputable def closedCappedAwayTotalsAtom
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (ℓ : AwayDomino x r D → ℕ)
    (q : CappedCoordinates i cap) : Set StepPath := by
  classical
  exact if (∀ b : AwayDomino x r D,
      dominoLazyTotal x r (fun k ↦ (q k : ℕ)) b.1 = ℓ b) then
    closedCappedAtom x r m cap D a q else ∅

theorem measurableSet_closedCappedAwayTotalsAtom
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (ℓ : AwayDomino x r D → ℕ)
    (q : CappedCoordinates i cap) :
    MeasurableSet (closedCappedAwayTotalsAtom x r m cap D a ℓ q) := by
  classical
  unfold closedCappedAwayTotalsAtom
  split <;> simp [measurableSet_closedCappedAtom]

theorem pairwise_disjoint_closedCappedAwayTotalsAtom
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (ℓ : AwayDomino x r D → ℕ) :
    Pairwise fun q q' : CappedCoordinates i cap ↦
      Disjoint (closedCappedAwayTotalsAtom x r m cap D a ℓ q)
        (closedCappedAwayTotalsAtom x r m cap D a ℓ q') := by
  classical
  intro q q' hqq'
  unfold closedCappedAwayTotalsAtom
  split <;> split
  · exact pairwise_disjoint_closedCappedAtom x r m cap D a hqq'
  · simp
  · simp
  · simp

theorem fairSteps_closedCappedAwayTotalsAtom
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (ℓ : AwayDomino x r D → ℕ)
    (q : CappedCoordinates i cap) :
    fairSteps (closedCappedAwayTotalsAtom x r m cap D a ℓ q) =
      ENNReal.ofReal (if (∀ b : AwayDomino x r D,
          dominoLazyTotal x r (fun k ↦ (q k : ℕ)) b.1 = ℓ b) then
        closedConditionedMass x r m D (fun k ↦ (q k : ℕ)) a else 0) := by
  classical
  by_cases hq : ∀ b : AwayDomino x r D,
      dominoLazyTotal x r (fun k ↦ (q k : ℕ)) b.1 = ℓ b
  · rw [closedCappedAwayTotalsAtom, if_pos hq, if_pos hq,
      fairSteps_closedCappedAtom]
  · rw [closedCappedAwayTotalsAtom, if_neg hq, if_neg hq]
    simp

/-- The finite union over all capped coordinate vectors with the prescribed
away-domino total vector.  This is the actual distinguished-coordinate
marginal: no coordinate above a domino in `D` is fixed. -/
noncomputable def closedCappedAwayTotalsEvent
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (ℓ : AwayDomino x r D → ℕ) : Set StepPath :=
  ⋃ q : CappedCoordinates i cap,
    closedCappedAwayTotalsAtom x r m cap D a ℓ q

/-- The corresponding real finite sum, with all distinguished coordinates
summed out. -/
noncomputable def closedCappedAwayTotalsMass
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (ℓ : AwayDomino x r D → ℕ) : ℝ :=
  ∑ q : CappedCoordinates i cap,
    if (∀ b : AwayDomino x r D,
        dominoLazyTotal x r (fun k ↦ (q k : ℕ)) b.1 = ℓ b) then
      closedConditionedMass x r m D (fun k ↦ (q k : ℕ)) a else 0

theorem measurableSet_closedCappedAwayTotalsEvent
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (ℓ : AwayDomino x r D → ℕ) :
    MeasurableSet (closedCappedAwayTotalsEvent x r m cap D a ℓ) := by
  classical
  exact MeasurableSet.iUnion fun q ↦
    measurableSet_closedCappedAwayTotalsAtom x r m cap D a ℓ q

/-- Exact `fairSteps` mass of a fixed away-domino-total fibre, after finite
marginalization over all distinguished coordinates. -/
theorem fairSteps_closedCappedAwayTotalsEvent
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (ℓ : AwayDomino x r D → ℕ) :
    fairSteps (closedCappedAwayTotalsEvent x r m cap D a ℓ) =
      ENNReal.ofReal (closedCappedAwayTotalsMass x r m cap D a ℓ) := by
  classical
  unfold closedCappedAwayTotalsEvent
  rw [measure_iUnion
    (pairwise_disjoint_closedCappedAwayTotalsAtom x r m cap D a ℓ)
    (measurableSet_closedCappedAwayTotalsAtom x r m cap D a ℓ)]
  simp_rw [fairSteps_closedCappedAwayTotalsAtom]
  rw [tsum_fintype]
  unfold closedCappedAwayTotalsMass
  rw [ENNReal.ofReal_sum_of_nonneg]
  intro q _
  split
  · exact closedConditionedMass_nonneg x r m D (fun k ↦ (q k : ℕ)) a
  · simp

/-- Different total vectors label disjoint measurable unions. -/
theorem disjoint_closedCappedAwayTotalsEvent_of_ne
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) {ℓ ℓ' : AwayDomino x r D → ℕ} (hℓ : ℓ ≠ ℓ') :
    Disjoint (closedCappedAwayTotalsEvent x r m cap D a ℓ)
      (closedCappedAwayTotalsEvent x r m cap D a ℓ') := by
  classical
  rw [Set.disjoint_left]
  intro ω hω hω'
  rcases Set.mem_iUnion.mp hω with ⟨q, hq⟩
  rcases Set.mem_iUnion.mp hω' with ⟨q', hq'⟩
  have htotal : ∀ b : AwayDomino x r D,
      dominoLazyTotal x r (fun k ↦ (q k : ℕ)) b.1 = ℓ b := by
    by_contra h
    rw [closedCappedAwayTotalsAtom, if_neg h] at hq
    exact hq
  have htotal' : ∀ b : AwayDomino x r D,
      dominoLazyTotal x r (fun k ↦ (q' k : ℕ)) b.1 = ℓ' b := by
    by_contra h
    rw [closedCappedAwayTotalsAtom, if_neg h] at hq'
    exact hq'
  rw [closedCappedAwayTotalsAtom, if_pos htotal] at hq
  rw [closedCappedAwayTotalsAtom, if_pos htotal'] at hq'
  by_cases hqq' : q = q'
  · subst q'
    apply hℓ
    funext b
    exact (htotal b).symm.trans (htotal' b)
  · exact Set.disjoint_left.mp
      (pairwise_disjoint_closedCappedAtom x r m cap D a hqq') hq hq'

/-- The unnormalized capped marginal of one away domino at a fixed total. -/
noncomputable def cappedAwayDominoTotalMass
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (b : AwayDomino x r D) (ℓ : ℕ) : ℝ :=
  ∑ v : CoordinatesAt x r b.1 → Fin (cap + 1),
    if (∑ k, (v k : ℕ)) = ℓ then
      conditionedCappedDominoMass x r m cap D b.1 v else 0

/-- For a distinguished domino take its full capped partition function; for
an away domino take the fixed-total marginal. -/
noncomputable def cappedDominoAwayMarginalMass
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (ℓ : AwayDomino x r D → ℕ) (b : ExternalDomino x r) : ℝ := by
  classical
  exact if hb : b.1 ∈ D then cappedDominoPartition x r m cap D b
    else cappedAwayDominoTotalMass x r m cap D ⟨b, hb⟩ (ℓ ⟨b, hb⟩)

/-- Exact product evaluation of the distinguished-coordinate marginal.  The
distinguished local factors are full partition functions; only away dominoes
retain fixed-total factors. -/
theorem closedCappedAwayTotalsMass_factorization
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (ℓ : AwayDomino x r D → ℕ) :
    closedCappedAwayTotalsMass x r m cap D a ℓ =
      (1 / 15 : ℝ) ^ (i + 1) *
        ∏ b : ExternalDomino x r,
          cappedDominoAwayMarginalMass x r m cap D ℓ b := by
  classical
  let E := groupByDominoEquiv x r (Fin (cap + 1))
  let F : (b : ExternalDomino x r) →
      (CoordinatesAt x r b → Fin (cap + 1)) → ℝ := fun b v ↦ by
    exact if hb : b.1 ∈ D then
      conditionedCappedDominoMass x r m cap D b v
    else if (∑ k, (v k : ℕ)) = ℓ ⟨b, hb⟩ then
      conditionedCappedDominoMass x r m cap D b v else 0
  unfold closedCappedAwayTotalsMass
  simp_rw [closedConditionedMass_eq_const_mul]
  have hfactor :
      (∑ q : CappedCoordinates i cap,
        if (∀ b : AwayDomino x r D,
            dominoLazyTotal x r (fun k ↦ (q k : ℕ)) b.1 = ℓ b) then
          (1 / 15 : ℝ) ^ (i + 1) *
            conditionedGapVectorMass x r m D (fun k ↦ (q k : ℕ)) else 0) =
        (1 / 15 : ℝ) ^ (i + 1) *
          ∑ q : CappedCoordinates i cap,
            if (∀ b : AwayDomino x r D,
                dominoLazyTotal x r (fun k ↦ (q k : ℕ)) b.1 = ℓ b) then
              conditionedGapVectorMass x r m D (fun k ↦ (q k : ℕ)) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : ∀ b : AwayDomino x r D,
        dominoLazyTotal x r (fun k ↦ (q k : ℕ)) b.1 = ℓ b
    · simp [hq]
    · simp
  rw [hfactor]
  congr 1
  calc
    (∑ q : CappedCoordinates i cap,
        if (∀ b : AwayDomino x r D,
            dominoLazyTotal x r (fun k ↦ (q k : ℕ)) b.1 = ℓ b) then
          conditionedGapVectorMass x r m D (fun k ↦ (q k : ℕ)) else 0) =
        ∑ Q : (b : ExternalDomino x r) →
            CoordinatesAt x r b → Fin (cap + 1),
          if (∀ b : AwayDomino x r D,
              (∑ k, (Q b.1 k : ℕ)) = ℓ b) then
            ∏ b : ExternalDomino x r,
              conditionedCappedDominoMass x r m cap D b (Q b) else 0 := by
      apply Fintype.sum_equiv E
      intro q
      rw [conditionedGapVectorMass_eq_capped_product]
      congr 1
    _ = ∑ Q : (b : ExternalDomino x r) →
            CoordinatesAt x r b → Fin (cap + 1),
          ∏ b : ExternalDomino x r, F b (Q b) := by
      apply Finset.sum_congr rfl
      intro Q _
      by_cases hQ : ∀ b : AwayDomino x r D,
          (∑ k, (Q b.1 k : ℕ)) = ℓ b
      · rw [if_pos hQ]
        apply Finset.prod_congr rfl
        intro b _
        by_cases hb : b.1 ∈ D
        · simp [F, hb]
        · simp [F, hb, hQ ⟨b, hb⟩]
      · rw [if_neg hQ]
        push Not at hQ
        obtain ⟨b, hb⟩ := hQ
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ b.1)
        simp [F, b.2, hb]
    _ = ∏ b : ExternalDomino x r,
          ∑ v : CoordinatesAt x r b → Fin (cap + 1), F b v :=
      (Fintype.prod_sum fun b v ↦ F b v).symm
    _ = ∏ b : ExternalDomino x r,
          cappedDominoAwayMarginalMass x r m cap D ℓ b := by
      apply Finset.prod_congr rfl
      intro b _
      by_cases hb : b.1 ∈ D
      · simp [F, cappedDominoAwayMarginalMass, cappedDominoPartition, hb]
      · simp [F, cappedDominoAwayMarginalMass, cappedAwayDominoTotalMass, hb]

end Erdos1165.PreStoppingFiber

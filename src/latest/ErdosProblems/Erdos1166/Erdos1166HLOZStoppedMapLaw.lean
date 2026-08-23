import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedBlockGrouping
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMixedReconstruction
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedSourcePartition
import ErdosProblems.Erdos1166.Erdos1166HLOZProp48Truncated
import ErdosProblems.Erdos1166.Erdos1166HLOZSourceInstantiation

/-!
# Stopped profile laws with the fresh direction retained

This file supplies the probability transport needed by the stopped-profile
connector.  The source partition and block-grouping modules identify the law
of the lazy block sums on a stopped past event.  The first theorem below shows
that any such stopped-past statistic is jointly distributed with the next
increment as the product with the uniform `Direction` law.  In particular,
the direction is not encoded as an event of the lazy vector.
-/

namespace Erdos1166.HLOZStoppedMapLaw

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open HLOZDecomposition HLOZActualStopped HLOZIncompleteStoppedBlocks
  HLOZMixedCreationBlocks HLOZStoppedSourcePartition HLOZProp48Truncated
  HLOZStoppedMixedReconstruction HLOZSourceInstantiation

/-- Natural realization of the source stopping time, kept local so this
probability connector does not depend on the later source-object layer. -/
noncomputable def stoppedCreationTime (m k : ℕ)
    (ω : ℕ → Direction) : ℕ :=
  (firstKSitesReachLevel m k (simpleRandomWalk ω)).untopA

theorem measurable_stoppedCreationTime (m k : ℕ) :
    Measurable (stoppedCreationTime m k) :=
  ((isStoppingTime_firstKSitesReachLevel m k).measurable'.untopA).comp
    measurable_simpleRandomWalk

/-- A prefix cylinder of length `n` belongs to the strict increment history
at `n`: it uses precisely coordinates `0,…,n-1`. -/
theorem measurableSet_stoppedPrefixAtom_iidHistory (p : StoppedPrefix) :
    MeasurableSet[iidHistory (X := Direction) p.1]
      (stoppedPrefixAtom p) := by
  unfold stoppedPrefixAtom prefixAtom
  let _ : MeasurableSpace (ℕ → Direction) :=
    iidHistory (X := Direction) p.1
  let f : (ℕ → Direction) → Prefix p.1 :=
    (Finset.range p.1).restrict
  change MeasurableSet (f ⁻¹' ({p.2} : Set (Prefix p.1)))
  apply MeasurableSet.preimage (measurableSet_singleton p.2)
  dsimp only [f]
  apply measurable_pi_lambda
  intro i
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le i.1
    (le_iSup_of_le (Finset.mem_range.mp i.2) le_rfl)

/-- A statistic of the stopped past is independent of the first fresh
direction.  The fiber hypothesis is the precise adaptedness statement: after
fixing both the statistic and the stopping time, the event only uses
coordinates strictly before the stopping time. -/
theorem hasLaw_prod_direction_after
    {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    (τ : (ℕ → Direction) → ℕ) (A : Set (ℕ → Direction))
    (X : (ℕ → Direction) → β) (ν : Measure β)
    (hτ : Measurable τ)
    (hA : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (A ∩ {ω | τ ω = k}))
    (hX : Measurable X)
    (hXpast : ∀ b k, MeasurableSet[iidHistory (X := Direction) k]
      ((A ∩ X ⁻¹' {b}) ∩ {ω | τ ω = k}))
    (hLaw : HasLaw X ν incrementLaw[|A]) :
    HasLaw (fun ω ↦ (X ω, incrementShiftAfter τ ω 0))
      (ν.prod directionLaw) incrementLaw[|A] := by
  let Y : (ℕ → Direction) → Direction :=
    fun ω ↦ incrementShiftAfter τ ω 0
  have hY : Measurable Y :=
    (measurable_pi_apply 0).comp (measurable_incrementShiftAfter hτ)
  have hAmeas : MeasurableSet A := measurableSet_pastEvent τ A hA
  constructor
  · exact (hX.prodMk hY).aemeasurable
  · apply Measure.ext_of_singleton
    rintro ⟨b, d⟩
    have hsingleton : ({(b, d)} : Set (β × Direction)) = {b} ×ˢ {d} := by
      ext z
      simp
    have hB : MeasurableSet
        ({v : Fin 1 → Direction | v 0 = d} : Set (Fin 1 → Direction)) :=
      MeasurableSet.of_discrete
    have hblock :
        (Measure.infinitePi fun _ : Fin 1 ↦ directionLaw)
            {v : Fin 1 → Direction | v 0 = d} = directionLaw {d} := by
      change (Measure.infinitePi fun _ : Fin 1 ↦ directionLaw)
          ((fun v : Fin 1 → Direction ↦ v 0) ⁻¹' {d}) = directionLaw {d}
      rw [← Measure.map_apply (measurable_pi_apply 0)
        (measurableSet_singleton d)]
      rw [Measure.infinitePi_map_eval]
    have hpre :
        A ∩ (fun ω ↦ (X ω, Y ω)) ⁻¹' ({(b, d)} : Set (β × Direction)) =
          (A ∩ X ⁻¹' {b}) ∩
            iidBlockAfter (X := Direction) τ 1 ⁻¹'
              {v : Fin 1 → Direction | v 0 = d} := by
      ext ω
      simp only [hsingleton, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_prod, Set.mem_singleton_iff, Y, incrementShiftAfter,
        Fin.isValue]
      tauto
    have hrestart :
        incrementLaw
            ((A ∩ X ⁻¹' {b}) ∩
              iidBlockAfter (X := Direction) τ 1 ⁻¹'
                {v : Fin 1 → Direction | v 0 = d}) =
          incrementLaw (A ∩ X ⁻¹' {b}) * directionLaw {d} := by
      simpa only [incrementLaw, hblock] using
        (measure_inter_iidBlockAfter_eq_mul directionLaw τ 1
          (A ∩ X ⁻¹' {b}) (hXpast b) hB)
    have hb := hLaw.measure_eq (measurableSet_singleton b)
    rw [cond_apply hAmeas] at hb
    change (incrementLaw A)⁻¹ * incrementLaw (A ∩ X ⁻¹' {b}) =
      ν {b} at hb
    rw [Measure.map_apply (hX.prodMk hY) (measurableSet_singleton (b, d)),
      cond_apply hAmeas, hpre, hrestart, hsingleton, Measure.prod_prod]
    calc
      (incrementLaw A)⁻¹ *
          (incrementLaw (A ∩ X ⁻¹' {b}) * directionLaw {d}) =
          ((incrementLaw A)⁻¹ * incrementLaw (A ∩ X ⁻¹' {b})) *
            directionLaw {d} := (mul_assoc _ _ _).symm
      _ = ν {b} * directionLaw {d} := by rw [hb]

/-! ### Active free winning bases -/

/-- The coordinates retained for Proposition 4.7 are free dominoes,
disjoint from the level-creation set `C`.  `activeBases` is the further
fixed-path filter (the adjacent source-band union in the application).
Creation dominoes are deliberately absent: their constrained blocks are
marginalized before this coordinate restriction. -/
abbrev ActiveFreeStoppedBase {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels)) :=
  {b : StoppedExternalBase a labels //
    b ∈ activeBases ∧ b.1 ∉ C ∧ b.1 + paperE1 ∉ C}

/-- Select the member with the larger fixed external profile.  Ties are
resolved toward the base (the even member), making the selection unique. -/
def activeFreeWinningSite {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (b : ActiveFreeStoppedBase a labels C activeBases) : Site :=
  if externalLeft b.1 < externalRight b.1 then b.1.1 + paperE1 else b.1.1

/-- External profile of the selected winning member. -/
def activeFreeSelectedProfile {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    ActiveFreeStoppedBase a labels C activeBases → ℕ :=
  fun b ↦ if externalLeft b.1 < externalRight b.1 then
    externalRight b.1 else externalLeft b.1

/-- Proposition 4.3's cap is the larger external local time on the free
domino. -/
def activeFreeCapProfile {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    ActiveFreeStoppedBase a labels C activeBases → ℕ :=
  fun b ↦ max (externalLeft b.1) (externalRight b.1)

theorem activeFreeSelectedProfile_eq_cap {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :
    activeFreeSelectedProfile a labels C activeBases externalLeft externalRight =
      activeFreeCapProfile a labels C activeBases externalLeft externalRight := by
  funext b
  unfold activeFreeSelectedProfile activeFreeCapProfile
  split_ifs with h
  · exact (max_eq_right (Nat.le_of_lt h)).symm
  · exact (max_eq_left (Nat.le_of_not_gt h)).symm

/-- Restrict a full stopped block-sum vector to the active free bases. -/
def restrictActiveFreeStoppedBase {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels))
    (u : StoppedExternalBase a labels → ℕ) :
    ActiveFreeStoppedBase a labels C activeBases → ℕ :=
  fun b ↦ u b.1

theorem measurable_restrictActiveFreeStoppedBase {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels)) :
    Measurable (restrictActiveFreeStoppedBase a labels C activeBases) :=
  measurable_of_countable _

/-- The raw negative-binomial shape supplied by the unprimed block grouping.
For a right/odd winner this need not equal the cap; that mismatch is retained
in the capped law below and must be resolved by the primed decomposition. -/
def activeFreeStoppedShape {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels)) :
    ActiveFreeStoppedBase a labels C activeBases → ℕ :=
  fun b ↦ Fintype.card (StoppedExternalIndex a labels b.1)

/-- On a free domino the mixed source constraint is exactly the strict
below-`m` truncation at the larger external profile. -/
theorem stoppedMixedBlockValues_activeFree_eq_sourceBelowSet {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site) (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (b : ActiveFreeStoppedBase a labels C activeBases) :
    (stoppedMixedBlockValues a labels m C externalLeft externalRight b.1 :
        Set ℕ) =
      sourceBelowSet m
        (activeFreeCapProfile a labels C activeBases
          externalLeft externalRight b) := by
  ext u
  have hbC : ¬ (b.1.1 ∈ C ∨ b.1.1 + paperE1 ∈ C) :=
    not_or_intro b.2.2.1 b.2.2.2
  simp only [stoppedMixedBlockValues, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_range, hbC, sourceBelowSet,
    Set.mem_ofPred_eq, activeFreeCapProfile]
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

/-- A nonzero strict-below factor forces its cap to lie below the stopping
level.  This elementary consequence lets source atom constructors derive the
profile bound instead of accepting it as separate data. -/
theorem cap_lt_of_negBin_sourceBelowSet_ne_zero
    (shape m cap : ℕ)
    (h : HLOZUrn.negBinMeasure shape (sourceBelowSet m cap) ≠ 0) :
    cap < m := by
  by_contra hnot
  have hempty : sourceBelowSet m cap = ∅ := by
    ext u
    simp [sourceBelowSet]
    omega
  rw [hempty, measure_empty] at h
  exact h rfl

/-- Every external base occurs at at least one chronological stopped-run
coordinate. -/
theorem stoppedExternalIndex_nonempty {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (b : StoppedExternalBase a labels) :
    Nonempty (StoppedExternalIndex a labels b) := by
  have hbList : b.1 ∈ stoppedExternalBasesFrom a (List.ofFn labels) := by
    simpa only [stoppedExternalBaseSet, List.mem_toFinset] using b.2
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hbList
  let j : Fin (q + 1) := Fin.cast (by simp) i
  refine ⟨⟨j, ?_⟩⟩
  unfold stoppedExternalBaseAt
  have hcast : Fin.cast
      (by simp [stoppedExternalBasesFrom_length]) j = i := by
    apply Fin.ext
    rfl
  rw [hcast]
  exact hi

/-- A nonempty coordinate set has positive negative-binomial mass whenever
the shape is positive. -/
theorem negBinMeasure_ne_zero_of_nonempty
    (i : ℕ) {E : Set ℕ} (hi : 1 ≤ i) (hE : E.Nonempty) :
    HLOZUrn.negBinMeasure i E ≠ 0 := by
  obtain ⟨u, hu⟩ := hE
  have hmono : HLOZUrn.negBinMeasure i ({u} : Set ℕ) ≤
      HLOZUrn.negBinMeasure i E := measure_mono (by simpa)
  intro hzero
  rw [hzero] at hmono
  have hsingleton : HLOZUrn.negBinMeasure i ({u} : Set ℕ) = 0 :=
    nonpos_iff_eq_zero.mp hmono
  have hreal : (HLOZUrn.negBinMeasure i).real ({u} : Set ℕ) = 0 := by
    rw [measureReal_def, hsingleton]
    simp
  rw [HLOZUrn.negBinMeasure_real_singleton] at hreal
  exact (HLOZProp48SourceBands.negBinMass_pos i u hi).ne' hreal

/-- Nonemptiness of the mixed product event supplies every coordinate
positivity premise needed to condition its negative-binomial factors. -/
theorem stoppedMixedCoordinatePos_of_event_nonempty {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (hEvent : (stoppedMixedBlockSumEvent a labels m C
      externalLeft externalRight).Nonempty) :
    ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0 := by
  obtain ⟨u, hu⟩ := hEvent
  rw [stoppedMixedBlockSumEvent_eq_blockEvent] at hu
  intro b
  apply negBinMeasure_ne_zero_of_nonempty
  · exact Fintype.card_pos_iff.mpr
      (stoppedExternalIndex_nonempty a labels b)
  · exact ⟨u b, hu b⟩

/-- Marginalize all creation and inactive blocks from the factorized mixed
law.  The result is the capped Proposition 4.3 product on the active free
coordinates; no truncated-law equality is assumed here. -/
theorem stoppedBlockNegBinMeasure_cond_mixed_map_activeFree {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (C : Finset Site) (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (hpos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b))
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    ((stoppedBlockNegBinMeasure a labels)[|
      stoppedMixedBlockSumEvent a labels m C
        externalLeft externalRight]).map
        (restrictActiveFreeStoppedBase a labels C activeBases) =
      sourceCappedProfileMeasure m
        (activeFreeStoppedShape a labels C activeBases)
        (activeFreeCapProfile a labels C activeBases
          externalLeft externalRight) := by
  let μ : StoppedExternalBase a labels → Measure ℕ := fun b ↦
    (HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex a labels b)))[|
        (stoppedMixedBlockValues a labels m C
          externalLeft externalRight b : Set ℕ)]
  letI (b : StoppedExternalBase a labels) : IsProbabilityMeasure (μ b) :=
    cond_isProbabilityMeasure (hpos b)
  letI (b : ActiveFreeStoppedBase a labels C activeBases) :
      IsProbabilityMeasure
        ((HLOZUrn.negBinMeasure
          (Fintype.card (StoppedExternalIndex a labels b.1)))[|
            sourceBelowSet m
              (activeFreeCapProfile a labels C activeBases
                externalLeft externalRight b)]) := by
    apply cond_isProbabilityMeasure
    rw [← stoppedMixedBlockValues_activeFree_eq_sourceBelowSet
      a labels m C activeBases externalLeft externalRight b]
    exact hpos b.1
  rw [stoppedBlockNegBinMeasure_cond_mixed_eq_pi_cond
    a labels m C externalLeft externalRight hpos]
  unfold sourceCappedProfileMeasure
  change (Measure.pi μ).map
      (fun u b ↦ u b.1) = Measure.pi (fun b ↦
        (HLOZUrn.negBinMeasure
          (Fintype.card (StoppedExternalIndex a labels b.1)))[|
            sourceBelowSet m
              (activeFreeCapProfile a labels C activeBases
                externalLeft externalRight b)])
  rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
  rw [Measure.map_infinitePi_infinitePi_of_inj
    (f := fun b : ActiveFreeStoppedBase a labels C activeBases ↦ b.1)
    Subtype.val_injective]
  congr 1
  funext b
  unfold μ
  rw [stoppedMixedBlockValues_activeFree_eq_sourceBelowSet]

/-- Applying a measurable transformation to the first component of a joint
product law transforms only that marginal. -/
theorem hasLaw_map_fst_prod_direction
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {P : Measure (ℕ → Direction)} {X : (ℕ → Direction) → β}
    {Y : (ℕ → Direction) → Direction} {μ : Measure β}
    {ν : Measure γ} [SFinite μ]
    (hXY : HasLaw (fun ω ↦ (X ω, Y ω)) (μ.prod directionLaw) P)
    (f : β → γ) (hf : Measurable f) (hmap : μ.map f = ν) :
    HasLaw (fun ω ↦ (f (X ω), Y ω))
      (ν.prod directionLaw) P := by
  let F : β × Direction → γ × Direction := Prod.map f id
  have hF : Measurable F := hf.prodMap measurable_id
  have hFmap : (μ.prod directionLaw).map F = ν.prod directionLaw := by
    rw [← Measure.map_prod_map μ directionLaw hf measurable_id,
      Measure.map_id, hmap]
  have hFLaw : HasLaw F (ν.prod directionLaw) (μ.prod directionLaw) :=
    ⟨hF.aemeasurable, hFmap⟩
  simpa only [F, Prod.map_apply, id_eq] using hFLaw.fun_comp hXY

/-- Undo conditioning in a law statement.  The zero-mass case is included,
so this has exactly the unnormalized form used by source atom map laws. -/
theorem map_restrict_eq_smul_of_hasLaw_cond
    {Omega beta : Type*} [MeasurableSpace Omega] [MeasurableSpace beta]
    {mu : Measure Omega} [IsFiniteMeasure mu] {A : Set Omega}
    {X : Omega → beta} {nu : Measure beta}
    (hA : MeasurableSet A) (hX : Measurable X)
    (hLaw : HasLaw X nu mu[|A]) :
    (mu.restrict A).map X = mu A • nu := by
  by_cases hA0 : mu A = 0
  · rw [Measure.restrict_eq_zero.mpr hA0, Measure.map_zero, hA0, zero_smul]
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hX hB, Measure.restrict_apply (hB.preimage hX),
    Measure.smul_apply, smul_eq_mul]
  have h := hLaw.measure_eq hB
  rw [cond_apply hA] at h
  change (mu A)⁻¹ * mu (A ∩ X ⁻¹' B) = nu B at h
  rw [Set.inter_comm]
  calc
    mu (A ∩ X ⁻¹' B) = 1 * mu (A ∩ X ⁻¹' B) :=
      (one_mul _).symm
    _ = (mu A * (mu A)⁻¹) * mu (A ∩ X ⁻¹' B) := by
      rw [ENNReal.mul_inv_cancel hA0 (measure_ne_top mu A)]
    _ = mu A * ((mu A)⁻¹ * mu (A ∩ X ⁻¹' B)) := mul_assoc ..
    _ = mu A * nu B := by rw [h]

/-- Measurable extension of an increment statistic to walk-path space. -/
noncomputable def liftIncrementStatisticToPath
    {beta : Type*} [Nonempty beta] (X : (ℕ → Direction) → beta) :
    (ℕ → Site) → beta :=
  Function.extend simpleRandomWalk X fun _ ↦ Classical.choice inferInstance

theorem measurable_liftIncrementStatisticToPath
    {beta : Type*} [MeasurableSpace beta] [Nonempty beta]
    {X : (ℕ → Direction) → beta} (hX : Measurable X) :
    Measurable (liftIncrementStatisticToPath X) := by
  exact measurableEmbedding_simpleRandomWalk.measurable_extend hX
    (measurable_const' fun _ _ ↦ rfl)

@[simp] theorem liftIncrementStatisticToPath_simpleRandomWalk
    {beta : Type*} [Nonempty beta] (X : (ℕ → Direction) → beta)
    (omega : ℕ → Direction) :
    liftIncrementStatisticToPath X (simpleRandomWalk omega) = X omega := by
  exact measurableEmbedding_simpleRandomWalk.injective.extend_apply X _ omega

/-- Transport an increment-space conditional law through the injective walk
encoding, and undo conditioning.  Its conclusion has exactly the measure
shape of `StoppedEquation447Atom.map_law`. -/
theorem liftIncrementStatistic_path_map_law
    {beta : Type*} [MeasurableSpace beta] [Nonempty beta]
    {A : Set (ℕ → Direction)} {X : (ℕ → Direction) → beta}
    {nu : Measure beta} (hA : MeasurableSet A) (hX : Measurable X)
    (hLaw : HasLaw X nu incrementLaw[|A]) :
    (simpleRandomWalkLaw.restrict (simpleRandomWalk '' A)).map
        (liftIncrementStatisticToPath X) =
      simpleRandomWalkLaw (simpleRandomWalk '' A) • nu := by
  have hPathA : MeasurableSet (simpleRandomWalk '' A) :=
    measurableEmbedding_simpleRandomWalk.measurableSet_image.2 hA
  have hPathLaw : HasLaw (liftIncrementStatisticToPath X) nu
      simpleRandomWalkLaw[|simpleRandomWalk '' A] := by
    rw [simpleRandomWalkLaw]
    apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk hA hX
    · intro omega _homega
      exact liftIncrementStatisticToPath_simpleRandomWalk X omega
    · exact hLaw
  exact map_restrict_eq_smul_of_hasLaw_cond hPathA
    (measurable_liftIncrementStatisticToPath hX) hPathLaw

/-- Convert the honest capped law to the truncated law only when the selected
winning-member profile has been identified with the raw block shape.  This
premise is automatic in the matching (even/unprimed or odd/primed)
decomposition, but is intentionally visible for a right/odd winner in the
unprimed decomposition. -/
theorem hasLaw_sourceCapped_prod_direction_to_truncated
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → (ι → ℕ) × Direction}
    (m : ℕ) (profile capProfile : ι → ℕ)
    (hwinning : ∀ x, capProfile x = profile x)
    (hLaw : HasLaw X
      ((sourceCappedProfileMeasure m profile capProfile).prod directionLaw) P) :
    HasLaw X ((sourceTruncatedProfileMeasure m profile).prod directionLaw) P := by
  rw [sourceCappedProfileMeasure_eq_truncated m profile capProfile hwinning]
    at hLaw
  exact hLaw

/-- Each decoded-vector fiber of the unprimed-even source atom is a strict
past event at `T_m^k`.  This discharges the nontrivial adaptedness premise of
the fresh-direction restart from the finite stopped-prefix partition. -/
theorem unprimedEven_vectorFiberPast {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) (v : Fin (q + 1) → ℕ)
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (((actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
            stoppedSourceCondition m k C) ∩
          (actualStoppedVector m k labels
            (unprimedEvenSourceConstraint m k C labels)) ⁻¹' {v}) ∩
        {ω | stoppedCreationTime m k ω = n}) := by
  classical
  rw [unprimedEven_source_partition m k C labels hm hk hfree]
  let E := unprimedEvenSourceConstraint m k C labels
  let p := reconstructedStoppedPrefix labels v
  change MeasurableSet[
    iidHistory (X := Direction) n]
      ((actualStoppedVectorEvent m k labels E ∩
          (actualStoppedVector m k labels E) ⁻¹' {v}) ∩
        {ω | stoppedCreationTime m k ω = n})
  have hfiber := actualStoppedVector_fiber_inter_event
    m k labels hnondist E v
  change actualStoppedVectorEvent m k labels E ∩
      (actualStoppedVector m k labels E) ⁻¹' {v} =
    (if v ∈ actualAdmissibleStoppedVectors m k labels E then
      stoppedPrefixAtom p else ∅) at hfiber
  rw [hfiber]
  by_cases hv : v ∈ actualAdmissibleStoppedVectors m k labels E
  · rw [if_pos hv]
    have hpstop : IsFirstKStoppedPrefix m k p :=
      (Finset.mem_filter.mp hv).2
    have hpT := prefixAtom_subset_firstKSitesReachLevel_fiber hpstop
    by_cases hpn : p.1 = n
    · have hsubset : stoppedPrefixAtom p ⊆
          {ω | stoppedCreationTime m k ω = n} := by
        intro ω hω
        have hT := hpT hω
        change firstKSitesReachLevel m k (simpleRandomWalk ω) = p.1 at hT
        change stoppedCreationTime m k ω = n
        unfold stoppedCreationTime
        rw [hT]
        exact hpn
      rw [Set.inter_eq_left.mpr hsubset, ← hpn]
      exact measurableSet_stoppedPrefixAtom_iidHistory p
    · have hempty : stoppedPrefixAtom p ∩
          {ω | stoppedCreationTime m k ω = n} = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨hωp, hωn⟩
        have hT := hpT hωp
        change firstKSitesReachLevel m k (simpleRandomWalk ω) = p.1 at hT
        have htime : stoppedCreationTime m k ω = p.1 := by
          unfold stoppedCreationTime
          rw [hT]
          simp
        exact hpn (htime.symm.trans hωn)
      rw [hempty]
      exact @MeasurableSet.empty _ (iidHistory (X := Direction) n)
  · rw [if_neg hv, Set.empty_inter]
    exact @MeasurableSet.empty _ (iidHistory (X := Direction) n)

/-- The entire unprimed-even source atom is known at the stopped horizon.
It is the countable union of the decoded-vector fibers above. -/
theorem unprimedEven_sourcePast {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      ((actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
          stoppedSourceCondition m k C) ∩
        {ω | stoppedCreationTime m k ω = n}) := by
  let A := actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m k C
  let X := actualStoppedVector m k labels
    (unprimedEvenSourceConstraint m k C labels)
  have heq : A ∩ {ω | stoppedCreationTime m k ω = n} =
      ⋃ v : Fin (q + 1) → ℕ,
        ((A ∩ X ⁻¹' {v}) ∩ {ω | stoppedCreationTime m k ω = n}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff, A, X]
    constructor
    · intro h
      exact ⟨actualStoppedVector m k labels
        (unprimedEvenSourceConstraint m k C labels) ω, ⟨h.1, rfl⟩, h.2⟩
    · rintro ⟨v, ⟨hA, _hv⟩, hn⟩
      exact ⟨hA, hn⟩
  rw [show (actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
      stoppedSourceCondition m k C) ∩
        {ω | stoppedCreationTime m k ω = n} =
      A ∩ {ω | stoppedCreationTime m k ω = n} by rfl, heq]
  exact MeasurableSet.iUnion fun v ↦
    unprimedEven_vectorFiberPast m k C labels hnondist hm hk hfree v n

/-! ### Source-specific stopped law -/

/-- Checked reduction of the unprimed-even stopped source atom to the exact
joint law required by (4.47).  It composes:

* the stopped source partition;
* grouping iid holding runs by external domino base;
* restriction to the active winning-base subtype; and
* strong restart for the next, still-unrevealed direction.

The source-specific bridge `hGroupedEvent` is the deterministic stopped
reconstruction identity.  Coordinate positivity is enough to derive, rather
than assume, the capped Proposition 4.3 marginal.  The preceding two lemmas
prove internally that the chosen unprimed-even atom and its decoded-vector
fibers are known strictly before `T_m^k`.  In particular,
this theorem is deliberately not instantiated on the unprimed-odd or
primed-even full-terminal atoms, which already fix the direction at their
nominal horizon. -/
theorem unprimedEven_activeFreeWinning_capped_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (externalLeft externalRight :
      StoppedExternalBase (0, 0) labels → ℕ)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels))
    (hGroupedEvent :
      (actualAdmissibleStoppedVectors m k labels
          (unprimedEvenSourceConstraint m k C labels) :
        Set (Fin (q + 1) → ℕ)) =
        (fun v ↦ stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (0, 0) labels m C
            externalLeft externalRight)
    (hMixedCoordinatePos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card (StoppedExternalIndex (0, 0) labels b))
        (stoppedMixedBlockValues (0, 0) labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    HasLaw
      (fun ω ↦
        (restrictActiveFreeStoppedBase (0, 0) labels C activeBases
            (stoppedPaperBlockSums (0, 0) labels
              (stoppedPaperBlockVector (0, 0) labels
                (actualStoppedVector m k labels
                  (unprimedEvenSourceConstraint m k C labels) ω))),
          incrementShiftAfter
            (stoppedCreationTime m k) ω 0))
      ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)
          (activeFreeCapProfile (0, 0) labels C activeBases
            externalLeft externalRight)).prod directionLaw)
      incrementLaw[|
        actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
          stoppedSourceCondition m k C] := by
  let E := unprimedEvenSourceConstraint m k C labels
  let A := actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
    stoppedSourceCondition m k C
  let X := actualStoppedVector m k labels E
  let τ := stoppedCreationTime m k
  let S := fun v : Fin (q + 1) → ℕ ↦
    stoppedPaperBlockSums (0, 0) labels
      (stoppedPaperBlockVector (0, 0) labels v)
  let R := restrictActiveFreeStoppedBase (0, 0) labels C activeBases
  have hτ : Measurable τ := measurable_stoppedCreationTime m k
  have hX : Measurable X :=
    measurable_actualStoppedVector m k labels hnondist E
  have hsource : HasLaw X
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels E : Set _)])
      incrementLaw[|A] := by
    simpa only [E, A, X] using
      unprimedEven_source_hasLaw m k C labels hnondist hm hk hfree
  have hjoint : HasLaw (fun ω ↦ (X ω, incrementShiftAfter τ ω 0))
      (((HLOZUrn.runVectorMeasure (q + 1))[|
          (actualAdmissibleStoppedVectors m k labels E : Set _)]).prod
        directionLaw) incrementLaw[|A] := by
    apply hasLaw_prod_direction_after τ A X _ hτ
    · intro n
      simpa only [A, τ] using
        unprimedEven_sourcePast m k C labels hnondist hm hk hfree n
    · exact hX
    · intro v n
      simpa only [A, X, τ, Set.inter_assoc] using
        unprimedEven_vectorFiberPast m k C labels hnondist hm hk hfree v n
    · exact hsource
  have hgrouped := stoppedPaperBlockSums_hasLaw_mixed_finset
    (0, 0) labels m C externalLeft externalRight
    (actualAdmissibleStoppedVectors m k labels E) hGroupedEvent
  have hmapS :
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels E : Set _)]).map S =
        (stoppedBlockNegBinMeasure (0, 0) labels)[|
          stoppedMixedBlockSumEvent (0, 0) labels m C
            externalLeft externalRight] := by
    simpa only [S] using hgrouped.map_eq
  have hCappedLaw := stoppedBlockNegBinMeasure_cond_mixed_map_activeFree
    (0, 0) labels m C activeBases externalLeft externalRight
      hMixedCoordinatePos
  have hmapRS :
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels E : Set _)]).map
          (fun v ↦ R (S v)) =
        sourceCappedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)
          (activeFreeCapProfile (0, 0) labels C activeBases
            externalLeft externalRight) := by
    change ((HLOZUrn.runVectorMeasure (q + 1))[|
      (actualAdmissibleStoppedVectors m k labels E : Set _)]).map
        (R ∘ S) = _
    have hR : Measurable R :=
      measurable_restrictActiveFreeStoppedBase (0, 0) labels C activeBases
    have hS : Measurable S :=
      (measurable_stoppedPaperBlockSums (0, 0) labels).comp
        (measurable_stoppedPaperBlockVector (0, 0) labels)
    rw [← Measure.map_map hR hS, hmapS]
    exact hCappedLaw
  have hRS : Measurable (fun v ↦ R (S v)) :=
    (measurable_restrictActiveFreeStoppedBase
      (0, 0) labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums (0, 0) labels).comp
        (measurable_stoppedPaperBlockVector (0, 0) labels))
  simpa only [A, X, τ, S, R] using
    hasLaw_map_fst_prod_direction hjoint (fun v ↦ R (S v)) hRS hmapRS

/-- Source-specialized form of
`unprimedEven_activeFreeWinning_capped_map_law`.  The stopped reconstruction
identity is discharged from the literal source facts: the creation set has
cardinality `k`, the fixed off-base path constraints hold, and the terminal
base belongs to the creation set.  Nonemptiness of the resulting mixed event
then discharges all coordinate-positivity obligations. -/
theorem unprimedEven_activeFreeWinning_capped_map_law_of_source {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C)
    (hterminal : stoppedTerminalBase labels ∈ C)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels))
    (hMixedEvent : (stoppedMixedBlockSumEvent (0, 0) labels m C
      (stoppedExternalLeft (0, 0) labels)
      (stoppedExternalRight (0, 0) labels)).Nonempty) :
    HasLaw
      (fun ω ↦
        (restrictActiveFreeStoppedBase (0, 0) labels C activeBases
            (stoppedPaperBlockSums (0, 0) labels
              (stoppedPaperBlockVector (0, 0) labels
                (actualStoppedVector m k labels
                  (unprimedEvenSourceConstraint m k C labels) ω))),
          incrementShiftAfter
            (stoppedCreationTime m k) ω 0))
      ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (0, 0) labels C activeBases)
          (activeFreeCapProfile (0, 0) labels C activeBases
            (stoppedExternalLeft (0, 0) labels)
            (stoppedExternalRight (0, 0) labels))).prod directionLaw)
      incrementLaw[|
        actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
          stoppedSourceCondition m k C] := by
  apply unprimedEven_activeFreeWinning_capped_map_law
    m k C labels hnondist hm hk hfree
    (stoppedExternalLeft (0, 0) labels)
    (stoppedExternalRight (0, 0) labels) activeBases
  · exact actualAdmissible_unprimedEvenSourceConstraint_eq_mixedBlockPreimage
      m k C labels hm hcard hfree hoff hterminal
  · exact stoppedMixedCoordinatePos_of_event_nonempty
      (0, 0) labels m C _ _ hMixedEvent

end Erdos1166.HLOZStoppedMapLaw

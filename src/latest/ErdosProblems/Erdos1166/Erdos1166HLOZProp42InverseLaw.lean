import ErdosProblems.Erdos1166.Erdos1166HLOZInverseClockProfile

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ProbabilityTheory

namespace Erdos1166.HLOZProp42InverseLaw

open Erdos1166 HLOZDecomposition HLOZActualStopped HLOZReconstruction
  HLOZIncompleteStoppedBlocks HLOZProp45SourceClock
  HLOZSourceInstantiation

/-! ### Selecting the first coordinates of one external-site block -/

/-- Completed external-base indices, in chronological order, at which the
fixed external path is at `x`. -/
noncomputable def completedVisitIndexList {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) : List (Fin q) :=
  (List.finRange q).filter fun i ↦
    stoppedExternalBaseAt (0, 0) labels i.castSucc = x

theorem completedVisitIndexList_nodup {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) :
    (completedVisitIndexList labels x).Nodup := by
  exact (List.nodup_finRange q).filter _

theorem completedVisitIndexList_length {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) :
    (completedVisitIndexList labels x).length =
      Fintype.card (CompletedExternalIndex labels x) := by
  classical
  rw [← List.toFinset_card_of_nodup
    (completedVisitIndexList_nodup labels x)]
  rw [Fintype.card_subtype]
  simp [completedVisitIndexList]

/-- The injective embedding of the first `cut` visits to `x` into the full
run vector.  The completed list intentionally omits the unfinished terminal
coordinate of a stopped prefix. -/
noncomputable def completedPrefixEmbedding {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length) :
    Fin cut → Fin q :=
  fun i ↦ (completedVisitIndexList labels x).get (Fin.castLE hcut i)

theorem completedPrefixEmbedding_injective {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length) :
    Function.Injective (completedPrefixEmbedding labels x hcut) := by
  intro i j hij
  have hindices :=
    (completedVisitIndexList_nodup labels x).get_inj_iff.mp hij
  exact (Fin.castLE_injective hcut) hindices

noncomputable def decodedHoldingPrefix {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length)
    (v : Fin q → ℕ) : ℕ :=
  ∑ i : Fin cut, v (completedPrefixEmbedding labels x hcut i)

/-- Any chronological prefix of one fixed-site block is a sum of `cut`
distinct iid geometric coordinates, hence has the negative-binomial law. -/
theorem decodedHoldingPrefix_hasLaw {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length) :
    HasLaw (decodedHoldingPrefix labels x hcut)
      (HLOZUrn.negBinMeasure cut) (HLOZUrn.runVectorMeasure q) := by
  exact runSubvectorSum_hasLaw (completedPrefixEmbedding labels x hcut)
    (completedPrefixEmbedding_injective labels x hcut)

noncomputable def conditionalDecodedHoldingPrefix {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length)
    (ω : ℕ → Direction) : ℕ :=
  decodedHoldingPrefix labels x hcut
    (listVectorToFin labels
      (conditionalPairRunVector 0 (List.ofFn labels) ω))

theorem conditionalDecodedHoldingPrefix_hasLaw {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length) :
    HasLaw (conditionalDecodedHoldingPrefix labels x hcut)
      (HLOZUrn.negBinMeasure cut)
      incrementLaw[|firstPairExternalPathEqFrom 0
        (externalPathFromLabels (List.ofFn labels))] := by
  have hvec := conditionalPairRunVector_hasLaw 0 (List.ofFn labels) (by
    intro p hp
    rw [List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩
    exact hnondist i)
  have hcast := (listVectorToFin_hasLaw labels).fun_comp hvec
  exact (decodedHoldingPrefix_hasLaw labels x hcut).fun_comp hcast

theorem measurable_conditionalDecodedHoldingPrefix {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length) :
    Measurable (conditionalDecodedHoldingPrefix labels x hcut) := by
  unfold conditionalDecodedHoldingPrefix
  have hruns : Measurable
      (conditionalPairRunVector 0 (List.ofFn labels)) :=
    measurable_conditionalPairRunVector 0 (List.ofFn labels) (by
      intro p hp
      rw [List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact hnondist i)
  exact (measurable_of_countable (decodedHoldingPrefix labels x hcut)).comp
    ((measurable_of_countable (listVectorToFin labels)).comp hruns)

noncomputable def pathDecodedHoldingPrefix {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length) :
    (ℕ → Site) → ℕ :=
  Function.extend simpleRandomWalk
    (conditionalDecodedHoldingPrefix labels x hcut) 0

theorem measurable_pathDecodedHoldingPrefix {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length) :
    Measurable (pathDecodedHoldingPrefix labels x hcut) := by
  apply measurableEmbedding_simpleRandomWalk.measurable_extend
  · exact measurable_conditionalDecodedHoldingPrefix labels hnondist x hcut
  · exact measurable_const

theorem pathDecodedHoldingPrefix_simpleRandomWalk {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length)
    (ω : ℕ → Direction) :
    pathDecodedHoldingPrefix labels x hcut (simpleRandomWalk ω) =
      conditionalDecodedHoldingPrefix labels x hcut ω := by
  unfold pathDecodedHoldingPrefix
  exact simpleRandomWalk_injective.extend_apply _ _ ω

/-- Path-space version of Proposition 4.2 for the selected chronological
prefix of a fixed external-site block. -/
theorem pathDecodedHoldingPrefix_hasLaw {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length) :
    HasLaw (pathDecodedHoldingPrefix labels x hcut)
      (HLOZUrn.negBinMeasure cut)
      simpleRandomWalkLaw[|externalPathWalkAtom (List.ofFn labels)] := by
  rw [simpleRandomWalkLaw]
  apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk
    (measurableSet_externalPathAtom 0 (List.ofFn labels))
  · exact measurable_conditionalDecodedHoldingPrefix labels hnondist x hcut
  · intro ω _
    exact pathDecodedHoldingPrefix_simpleRandomWalk labels x hcut ω
  · exact conditionalDecodedHoldingPrefix_hasLaw labels hnondist x hcut

/-- Once the deterministic inverse-clock identification is available on a
fixed external-path atom, the Proposition 4.2 law transfers without any
additional probabilistic premise.  This isolates the remaining clock
reconstruction statement from the completed probability argument. -/
theorem inverseClockHoldingPrefix_hasLaw_on_externalPathAtom {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length)
    (hclock : ∀ s ∈ externalPathWalkAtom (List.ofFn labels),
      inverseClockHoldingPrefix s (2 * q) cut x =
        pathDecodedHoldingPrefix labels x hcut s) :
    HasLaw (fun s ↦ inverseClockHoldingPrefix s (2 * q) cut x)
      (HLOZUrn.negBinMeasure cut)
      simpleRandomWalkLaw[|externalPathWalkAtom (List.ofFn labels)] := by
  apply (pathDecodedHoldingPrefix_hasLaw labels hnondist x hcut).congr
  filter_upwards [ae_cond_mem
    (measurableSet_externalPathWalkAtom (List.ofFn labels))] with s hs
  exact hclock s hs

/-! ### Measure-preserving reversal of shifted pairs -/

/-- Swap the even and odd coordinates inside every increment pair.  This is
the coordinate transport that turns the primed distinguished pair
`(-e₁,+e₁)` into the unprimed pair `(+e₁,-e₁)`. -/
def adjacentPairSwap : ℕ ≃ ℕ :=
  Equiv.natSumNatEquivNat.symm |>.trans
    (Equiv.sumComm ℕ ℕ) |>.trans Equiv.natSumNatEquivNat

@[simp] theorem adjacentPairSwap_even (n : ℕ) :
    adjacentPairSwap (2 * n) = 2 * n + 1 := by
  simp [adjacentPairSwap, Equiv.natSumNatEquivNat_apply]

@[simp] theorem adjacentPairSwap_odd (n : ℕ) :
    adjacentPairSwap (2 * n + 1) = 2 * n := by
  simp [adjacentPairSwap, Equiv.natSumNatEquivNat_apply]

theorem adjacentPairSwap_involutive : Function.Involutive adjacentPairSwap := by
  intro n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩ <;> simp

theorem adjacentPairSwap_symm : adjacentPairSwap.symm = adjacentPairSwap := by
  apply Equiv.ext
  intro n
  apply adjacentPairSwap.injective
  rw [adjacentPairSwap.apply_symm_apply, adjacentPairSwap_involutive]

def swapAdjacentPairs (ω : ℕ → Direction) : ℕ → Direction :=
  fun n ↦ ω (adjacentPairSwap n)

theorem measurable_swapAdjacentPairs : Measurable swapAdjacentPairs := by
  apply measurable_pi_lambda
  intro n
  exact measurable_pi_apply (adjacentPairSwap n)

/-- Reversing every pair preserves the iid increment law. -/
theorem swapAdjacentPairs_hasLaw :
    HasLaw swapAdjacentPairs incrementLaw incrementLaw := by
  constructor
  · exact measurable_swapAdjacentPairs.aemeasurable
  · unfold incrementLaw swapAdjacentPairs
    have hfun : (fun ω : ℕ → Direction ↦ fun n ↦ ω (adjacentPairSwap n)) =
        MeasurableEquiv.piCongrLeft (fun _ : ℕ ↦ Direction)
          adjacentPairSwap := by
      funext ω n
      conv_rhs => rw [← adjacentPairSwap_involutive n]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rw [hfun]
    exact Measure.infinitePi_map_piCongrLeft
      (fun _ : ℕ ↦ directionLaw) adjacentPairSwap

noncomputable def swappedIncrementShiftAfter
    (τ : (ℕ → Direction) → ℕ) (ω : ℕ → Direction) : ℕ → Direction :=
  swapAdjacentPairs (incrementShiftAfter τ ω)

theorem measurable_swappedIncrementShiftAfter
    {τ : (ℕ → Direction) → ℕ} (hτ : Measurable τ) :
    Measurable (swappedIncrementShiftAfter τ) :=
  measurable_swapAdjacentPairs.comp (measurable_incrementShiftAfter hτ)

/-- A random restart followed by pair reversal is still a fresh iid
increment sequence.  This is the probabilistic transport required by the
one-step-shifted primed deletion. -/
theorem swappedIncrementShiftAfter_hasLaw_cond
    (τ : (ℕ → Direction) → ℕ) (A : Set (ℕ → Direction))
    (hτ : Measurable τ)
    (hA : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (A ∩ { ω | τ ω = k }))
    (hApos : incrementLaw A ≠ 0) :
    HasLaw (swappedIncrementShiftAfter τ) incrementLaw incrementLaw[|A] := by
  exact swapAdjacentPairs_hasLaw.fun_comp
    (incrementShiftAfter_hasLaw_cond τ A hτ hA hApos)

/-- Negative-binomial selected-prefix law after a source stopping/restart
and the shifted-pair reversal.  The conditioning event is exactly the past
atom intersected with the pulled-back fixed external-path atom. -/
theorem conditionalDecodedHoldingPrefix_swapped_after_hasLaw
    {q cut : ℕ} (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (completedVisitIndexList labels x).length)
    (τ : (ℕ → Direction) → ℕ) (A : Set (ℕ → Direction))
    (hτ : Measurable τ)
    (hA : ∀ k, MeasurableSet[iidHistory (X := Direction) k]
      (A ∩ { ω | τ ω = k }))
    (hApos : incrementLaw A ≠ 0) :
    HasLaw
      (fun ω ↦ conditionalDecodedHoldingPrefix labels x hcut
        (swappedIncrementShiftAfter τ ω))
      (HLOZUrn.negBinMeasure cut)
      incrementLaw[|A ∩
        swappedIncrementShiftAfter τ ⁻¹'
          firstPairExternalPathEqFrom 0
            (externalPathFromLabels (List.ofFn labels))] := by
  let E := firstPairExternalPathEqFrom 0
    (externalPathFromLabels (List.ofFn labels))
  have hE : MeasurableSet E := measurableSet_externalPathAtom 0 _
  have hY := swappedIncrementShiftAfter_hasLaw_cond τ A hτ hA hApos
  have hYm : Measurable (swappedIncrementShiftAfter τ) :=
    measurable_swappedIncrementShiftAfter hτ
  have hYcond := Erdos1166.HasLaw.cond_preimage hY hYm E hE
  have hdecoder := conditionalDecodedHoldingPrefix_hasLaw labels hnondist x hcut
  have hcomp := hdecoder.fun_comp hYcond
  have hAmeas : MeasurableSet A := measurableSet_pastEvent τ A hA
  rw [cond_cond_eq_cond_inter hAmeas (hE.preimage hYm)] at hcomp
  exact hcomp

/-! ### Exact finite-mixture transfer -/

theorem HasLaw.cond_inter_eq_mul
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {ν : Measure β} {X : Ω → β} {A : Set Ω}
    (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hA_top : P A ≠ ∞)
    (hLaw : HasLaw X ν P[|A]) (B : Set β) (hB : MeasurableSet B) :
    P (A ∩ X ⁻¹' B) = P A * ν B := by
  have h := hLaw.measure_eq hB
  rw [cond_apply hA] at h
  change (P A)⁻¹ * P (A ∩ X ⁻¹' B) = ν B at h
  calc
    P (A ∩ X ⁻¹' B) = 1 * P (A ∩ X ⁻¹' B) := (one_mul _).symm
    _ = (P A * (P A)⁻¹) * P (A ∩ X ⁻¹' B) := by
      rw [ENNReal.mul_inv_cancel hA0 hA_top]
    _ = P A * ((P A)⁻¹ * P (A ∩ X ⁻¹' B)) := mul_assoc ..
    _ = P A * ν B := by exact congrArg (P A * ·) h

/-- If a statistic has the same conditional law on every atom of a finite
disjoint partition, then it has that law conditioned on their union.  Zero
mass atoms are allowed and are discarded automatically. -/
theorem HasLaw.cond_iUnion_finset
    {Ω β ι : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsFiniteMeasure P] {ν : Measure β} {X : Ω → β}
    (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hdisj : ((s : Set ι)).PairwiseDisjoint A)
    (hpos : P (⋃ i ∈ s, A i) ≠ 0)
    (hLaw : ∀ i ∈ s, P (A i) ≠ 0 → HasLaw X ν P[|A i])
    (hX : Measurable X) :
    HasLaw X ν P[|⋃ i ∈ s, A i] := by
  classical
  let U : Set Ω := ⋃ i ∈ s, A i
  have hU : MeasurableSet U := by
    dsimp only [U]
    exact Finset.measurableSet_biUnion s hA
  have hUtop : P U ≠ ∞ := measure_ne_top P U
  constructor
  · exact hX.aemeasurable
  · apply Measure.ext fun B hB ↦ ?_
    rw [Measure.map_apply hX hB, cond_apply hU]
    have hinter : U ∩ X ⁻¹' B = ⋃ i ∈ s, (A i ∩ X ⁻¹' B) := by
      ext ω
      simp only [U, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
      aesop
    rw [hinter]
    have hdisj' : ((s : Set ι)).PairwiseDisjoint
        (fun i ↦ A i ∩ X ⁻¹' B) := by
      intro i hi j hj hij
      exact (hdisj hi hj hij).mono inter_subset_left inter_subset_left
    rw [measure_biUnion_finset hdisj'
      (fun i hi ↦ (hA i hi).inter (hX hB))]
    have hterm : ∀ i ∈ s,
        P (A i ∩ X ⁻¹' B) = P (A i) * ν B := by
      intro i hi
      by_cases hz : P (A i) = 0
      · rw [hz, zero_mul]
        exact measure_mono_null inter_subset_left hz
      · exact HasLaw.cond_inter_eq_mul (hA i hi) hz
          (measure_ne_top P (A i)) (hLaw i hi hz) B hB
    rw [Finset.sum_congr rfl fun i hi ↦ hterm i hi]
    rw [← Finset.sum_mul]
    have hmeasureU : P U = ∑ i ∈ s, P (A i) := by
      dsimp only [U]
      exact measure_biUnion_finset hdisj hA
    rw [← hmeasureU, ← mul_assoc,
      ENNReal.inv_mul_cancel hpos hUtop, one_mul]

end Erdos1166.HLOZProp42InverseLaw

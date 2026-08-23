import ErdosProblems.Erdos1166.Erdos1166HLOZConditionalPairRuns

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory

namespace Erdos1166

open HLOZUrn

/-- Conditioning the actual finite run vector on any measurable constraint
filters its iid geometric product law by that constraint.  This is the
measure-level form needed for the past blocks in Proposition 4.3. -/
theorem conditionalPairRunVector_hasLaw_filtered
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair)
    (E : Set (Fin labels.length → ℕ)) (hE : MeasurableSet E) :
    HasLaw (conditionalPairRunVector start labels)
      (HLOZUrn.runVectorMeasure labels.length)[|E]
      (incrementLaw[|firstPairExternalPathEqFrom start
        (externalPathFromLabels labels)])[|
          conditionalPairRunVector start labels ⁻¹' E] := by
  exact HasLaw.cond_preimage
    (conditionalPairRunVector_hasLaw start labels hnondist)
    (measurable_conditionalPairRunVector start labels hnondist) E hE

/-- Equivalent one-step conditioning form: fix the finite external path and
impose the entire past run-vector constraint in one event. -/
theorem conditionalPairRunVector_hasLaw_on_inter
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair)
    (E : Set (Fin labels.length → ℕ)) (hE : MeasurableSet E) :
    HasLaw (conditionalPairRunVector start labels)
      (HLOZUrn.runVectorMeasure labels.length)[|E]
      incrementLaw[|
        firstPairExternalPathEqFrom start (externalPathFromLabels labels) ∩
          conditionalPairRunVector start labels ⁻¹' E] := by
  rw [← cond_cond_eq_cond_inter
    (measurableSet_externalPathAtom start labels)
    ((measurable_conditionalPairRunVector start labels hnondist) hE)
    incrementLaw]
  exact conditionalPairRunVector_hasLaw_filtered start labels hnondist E hE

/-- Support/denominator certificate for a nonempty constrained product law. -/
theorem externalPathAtom_inter_runConstraint_pos
    (start : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair)
    (E : Set (Fin labels.length → ℕ)) (hE : MeasurableSet E)
    (hEpos : HLOZUrn.runVectorMeasure labels.length E ≠ 0) :
    incrementLaw
      (firstPairExternalPathEqFrom start (externalPathFromLabels labels) ∩
        conditionalPairRunVector start labels ⁻¹' E) ≠ 0 := by
  have hLaw := conditionalPairRunVector_hasLaw start labels hnondist
  have heq := hLaw.measure_eq hE
  intro hzero
  have hzero' : incrementLaw
      (firstPairExternalPathEqFrom start (externalPathFromLabels labels) ∩
        { ω | E (conditionalPairRunVector start labels ω) }) = 0 :=
    hzero
  have hcondzero : incrementLaw[|firstPairExternalPathEqFrom start
        (externalPathFromLabels labels)]
      { ω | E (conditionalPairRunVector start labels ω) } = 0 := by
    calc
      incrementLaw[|firstPairExternalPathEqFrom start
          (externalPathFromLabels labels)]
          { ω | E (conditionalPairRunVector start labels ω) } =
          (incrementLaw (firstPairExternalPathEqFrom start
            (externalPathFromLabels labels)))⁻¹ *
            incrementLaw
              (firstPairExternalPathEqFrom start
                (externalPathFromLabels labels) ∩
                { ω | E (conditionalPairRunVector start labels ω) }) :=
        cond_apply (measurableSet_externalPathAtom start labels)
          incrementLaw _
      _ = (incrementLaw (firstPairExternalPathEqFrom start
            (externalPathFromLabels labels)))⁻¹ * 0 :=
        congrArg ((incrementLaw (firstPairExternalPathEqFrom start
          (externalPathFromLabels labels)))⁻¹ * ·) hzero'
      _ = 0 := mul_zero _
  rw [hcondzero] at heq
  exact hEpos heq.symm

/-- Generic path-to-increment lift of a finite stopping-time fiber. -/
theorem measurableSet_pathStoppingTime_fiber_iidHistory
    {τ : (ℕ → Site) → WithTop ℕ}
    (hτ : IsStoppingTime HLOZFoundation.canonicalFiltration τ) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      {ω : ℕ → Direction | τ (simpleRandomWalk ω) = n} := by
  have hPath : MeasurableSet[HLOZFoundation.canonicalFiltration n]
      {s : ℕ → Site | τ s = n} :=
    hτ.measurableSet_eq_of_countable n
  exact HLOZFoundation.measurable_simpleRandomWalk_iidHistory_canonicalFiltration
    n hPath

/-- Pullback of an arbitrary event known at a path stopping time, on each
finite stopping fiber, is an increment-past event. -/
theorem measurableSet_pathStoppedEvent_inter_fiber_iidHistory
    {τ : (ℕ → Site) → WithTop ℕ}
    (hτ : IsStoppingTime HLOZFoundation.canonicalFiltration τ)
    (M : Set (ℕ → Site)) (hM : MeasurableSet[hτ.measurableSpace] M)
    (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹' M ∩
        {ω : ℕ → Direction | τ (simpleRandomWalk ω) = n}) := by
  have hPath : MeasurableSet[HLOZFoundation.canonicalFiltration n]
      (M ∩ {s : ℕ → Site | τ s = n}) := by
    exact (hτ.measurableSet_inter_eq_iff M n).mp
      (hM.inter (hτ.measurableSet_eq' n))
  have hPre :=
    HLOZFoundation.measurable_simpleRandomWalk_iidHistory_canonicalFiltration
      n hPath
  simpa only [Set.preimage_inter, Set.preimage_ofPred_eq] using hPre

/-- The source event `M_m^k = {T_m^k < T_(m+1)^1}` is known at the
stopping time `T_m^k`. -/
theorem measurableSet_hlozMAtThreshold
    (m k : ℕ) :
    MeasurableSet[
      (isStoppingTime_firstKSitesReachLevel m k).measurableSpace]
      {s : ℕ → Site |
        firstKSitesReachLevel m k s <
          firstKSitesReachLevel (m + 1) 1 s} := by
  have hle : MeasurableSet[
      (isStoppingTime_firstKSitesReachLevel m k).measurableSpace]
      {s : ℕ → Site |
        firstKSitesReachLevel (m + 1) 1 s ≤
          firstKSitesReachLevel m k s} :=
    IsStoppingTime.measurableSet_stopping_time_le
      (isStoppingTime_firstKSitesReachLevel (m + 1) 1)
      (isStoppingTime_firstKSitesReachLevel m k)
  have heq : {s : ℕ → Site |
        firstKSitesReachLevel m k s <
          firstKSitesReachLevel (m + 1) 1 s} =
      {s : ℕ → Site |
        firstKSitesReachLevel (m + 1) 1 s ≤
          firstKSitesReachLevel m k s}ᶜ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  rw [heq]
  exact hle.compl

/-- Exact increment-history lift of the stopped source event
`M_m^k ∩ {T_m^k=n}`.  This is a PAST event, unlike the post-stopping
restart cylinders. -/
theorem measurableSet_hlozM_inter_thresholdFiber_iidHistory
    (m k n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (simpleRandomWalk ⁻¹'
          {s : ℕ → Site |
            firstKSitesReachLevel m k s <
              firstKSitesReachLevel (m + 1) 1 s} ∩
        {ω : ℕ → Direction |
          firstKSitesReachLevel m k (simpleRandomWalk ω) = n}) := by
  exact measurableSet_pathStoppedEvent_inter_fiber_iidHistory
    (isStoppingTime_firstKSitesReachLevel m k)
    {s : ℕ → Site |
      firstKSitesReachLevel m k s < firstKSitesReachLevel (m + 1) 1 s}
    (measurableSet_hlozMAtThreshold m k) n

/-- Actual past-event interface for Proposition 4.3.  Once reconstruction
identifies the stopped path atom `M_m^k ∩ {T_m^k=n}` with a measurable
constraint `E` on its finite run vector, the conditional law is precisely
the iid geometric product filtered by `E`. -/
theorem conditionalPairRunVector_hasLaw_on_hlozM_thresholdFiber
    (start m k n : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair)
    (E : Set (Fin labels.length → ℕ)) (hE : MeasurableSet E)
    (hbridge :
      firstPairExternalPathEqFrom start (externalPathFromLabels labels) ∩
          (simpleRandomWalk ⁻¹'
            {s : ℕ → Site |
              firstKSitesReachLevel m k s <
                firstKSitesReachLevel (m + 1) 1 s} ∩
            {ω : ℕ → Direction |
              firstKSitesReachLevel m k (simpleRandomWalk ω) = n}) =
        firstPairExternalPathEqFrom start (externalPathFromLabels labels) ∩
          conditionalPairRunVector start labels ⁻¹' E) :
    HasLaw (conditionalPairRunVector start labels)
      (HLOZUrn.runVectorMeasure labels.length)[|E]
      incrementLaw[|
        firstPairExternalPathEqFrom start (externalPathFromLabels labels) ∩
          (simpleRandomWalk ⁻¹'
            {s : ℕ → Site |
              firstKSitesReachLevel m k s <
                firstKSitesReachLevel (m + 1) 1 s} ∩
            {ω : ℕ → Direction |
              firstKSitesReachLevel m k (simpleRandomWalk ω) = n})] := by
  rw [hbridge]
  exact conditionalPairRunVector_hasLaw_on_inter
    start labels hnondist E hE

end Erdos1166

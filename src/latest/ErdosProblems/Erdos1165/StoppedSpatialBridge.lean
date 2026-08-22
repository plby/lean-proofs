import ErdosProblems.Erdos1165.SpatialInsertionConditional

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165

/-!
# Stopped finite spatial-fibre bridge

This module connects the finite fixed-external-word masses from
`SpatialInsertionConditional` to the canonical fair-step measure after an
arbitrary finite stopping time.  The final theorem is deliberately phrased in
terms of a concrete family of pairwise-disjoint fixed-horizon future events:
constructing that family from the variable-length spatial insertion words is
the remaining finite encoding step.
-/

/-- A useful companion to `fairSteps_map_stepBlock`: the initial finite
increment vector has `fairBlock` law. -/
theorem fairSteps_map_stepPrefix' (k : ℕ) :
    fairSteps.map (stepPrefix k) = fairBlock k := by
  have heq : stepBlock 0 k = stepPrefix k := by
    funext ω j
    simp [stepBlock, stepPrefix]
  rw [← heq, fairSteps_map_stepBlock]

/-- A concrete event at the atom `{τ=n}`, with arbitrary finite prefix data.
Choosing `S` to specify an external word, favorite set, and level data gives
the finite stopped-past atom needed below. -/
def stoppedPrefixAtom (τ : StepPath → ℕ) (n : ℕ)
    (S : Set (Fin n → Direction)) : Set StepPath :=
  {ω | τ ω = n ∧ stepPrefix n ω ∈ S}

theorem isMeasurableAtStopping_stoppedPrefixAtom
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ) (n : ℕ)
    (S : Set (Fin n → Direction)) :
    IsMeasurableAtStopping τ (stoppedPrefixAtom τ n S) := by
  intro t
  by_cases htn : t = n
  · subst t
    have hS : MeasurableSet S := (Set.to_countable S).measurableSet
    have heq : stoppedPrefixAtom τ n S ∩ {ω | τ ω = n} =
        {ω | τ ω = n} ∩ stepPrefix n ⁻¹' S := by
      ext ω
      constructor
      · rintro ⟨⟨hτn, hSω⟩, _⟩
        exact ⟨hτn, hSω⟩
      · rintro ⟨hτn, hSω⟩
        exact ⟨⟨hτn, hSω⟩, hτn⟩
    have hpre : MeasurableSet[incrementFiltration n] (stepPrefix n ⁻¹' S) := by
      rw [incrementFiltration_apply]
      exact ⟨S, hS, rfl⟩
    rw [heq]
    exact (hτ.measurableSet_eq n).inter hpre
  · have heq : stoppedPrefixAtom τ n S ∩ {ω | τ ω = t} = ∅ := by
      ext ω
      simp only [stoppedPrefixAtom, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false]
      constructor
      · rintro ⟨⟨hn, _⟩, ht⟩
        exact htn (ht.symm.trans hn)
      · intro hfalse
        exact False.elim hfalse
    rw [heq]
    change MeasurableSet[incrementFiltration t] (∅ : Set StepPath)
    exact @MeasurableSet.empty StepPath (incrementFiltration t)

end Erdos1165

namespace Erdos1165.SpatialInsertionFiber

open LazyDecomposition PathInsertion

/-- The finite direction-block event underlying one fixed external word and
one total deleted-block count. -/
def fixedExternalTotalDirections {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (j : ℕ) :
    Set (Fin (2 * (i + j)) → Direction) :=
  Set.range fun g : GapPattern i j ↦ insertionCodeDirections (g, r)

theorem measurableSet_fixedExternalTotalDirections
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (j : ℕ) :
    MeasurableSet (fixedExternalTotalDirections r j) :=
  (Set.to_countable _).measurableSet

theorem fixedExternalTotalCylinder_eq_preimage
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (j : ℕ) :
    fixedExternalTotalCylinder r j =
      stepPrefix (2 * (i + j)) ⁻¹' fixedExternalTotalDirections r j := by
  ext ω
  simp [fixedExternalTotalCylinder, fixedExternalTotalDirections, eq_comm]

/-- Fresh finite product-law evaluation of the insertion fibre. -/
theorem fairBlock_fixedExternalTotalDirections
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (j : ℕ) :
    fairBlock (2 * (i + j)) (fixedExternalTotalDirections r j) =
      ENNReal.ofReal (fixedExternalJointMass i j) := by
  rw [← fairSteps_fixedExternalTotalCylinder_eq_ofReal r j]
  rw [fixedExternalTotalCylinder_eq_preimage]
  rw [← Measure.map_apply (measurable_stepPrefix _)
    (measurableSet_fixedExternalTotalDirections r j)]
  rw [Erdos1165.fairSteps_map_stepPrefix']

/-- Exact stopped-past/future-fibre factorization.  This applies in particular
when `A` is `stoppedPrefixAtom τ n S`, where `S` fixes all desired external,
favorite, and level data observable by time `n`. -/
theorem stopped_fixedExternalTotalDirections_factorization
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    {A : Set StepPath} (hA : IsMeasurableAtStopping τ A)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (j : ℕ) :
    fairSteps (A ∩ postStoppingBlock τ (2 * (i + j)) ⁻¹'
        fixedExternalTotalDirections r j) =
      fairSteps A * ENNReal.ofReal (fixedExternalJointMass i j) := by
  rw [strongMarkov_stoppedEvent_set hτ hA]
  rw [fairBlock_fixedExternalTotalDirections]

/-! ## Abstract fixed-horizon capped spatial fibre bridge -/

/-- If a family of pairwise-disjoint finite future-block events realizes the
already-proved spatial joint weights up to a common positive factor,
conditioning after an arbitrary positive stopped-past atom gives exactly the
normalized away-domino product law. -/
theorem stopped_cappedSpatialFiber_conditional_factorization
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    {A : Set StepPath} (hA : IsMeasurableAtStopping τ A)
    (hApos : fairSteps A ≠ 0)
    {o : Orientation} {i K : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (c : ℝ) (hc : 0 < c)
    (C : TruncatedDominoTotals x r m D → Set (Fin K → Direction))
    (hCdis : Pairwise fun z z' ↦ Disjoint (C z) (C z'))
    (hCmass : ∀ z, fairBlock K (C z) =
      ENNReal.ofReal (c * truncatedTotalsJointMass x r m D z))
    (ℓ : TruncatedDominoTotals x r m D) :
    (fairSteps (A ∩ postStoppingBlock τ K ⁻¹' C ℓ)).toReal /
        (fairSteps (A ∩ postStoppingBlock τ K ⁻¹' (⋃ z, C z))).toReal =
      ∏ b : AwayDomino x r D,
        truncatedDominoMass x r m b.1 (ℓ b) := by
  classical
  have hCmeas : ∀ z, MeasurableSet (C z) := fun z ↦
    (Set.to_countable (C z)).measurableSet
  have hUnionMass : fairBlock K (⋃ z, C z) =
      ENNReal.ofReal (c * ∑ z, truncatedTotalsJointMass x r m D z) := by
    rw [measure_iUnion hCdis hCmeas]
    simp_rw [hCmass]
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [Finset.mul_sum]
    · intro z _
      apply mul_nonneg hc.le
      unfold truncatedTotalsJointMass fixedExternalJointMass uniformBlockWordMass
      positivity
  rw [strongMarkov_stoppedEvent_set hτ hA, hCmass]
  rw [strongMarkov_stoppedEvent_set hτ hA, hUnionMass]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
    · have hAreal : (fairSteps A).toReal ≠ 0 := by
        rw [ENNReal.toReal_ne_zero]
        exact ⟨hApos, measure_ne_top fairSteps A⟩
      rw [← mul_assoc, ← mul_assoc]
      rw [mul_div_mul_left _ _ (mul_ne_zero hAreal hc.ne')]
      exact truncatedTotals_conditional_factorization x r m D ℓ
    · exact mul_nonneg hc.le (Finset.sum_nonneg fun z _ ↦ by
        unfold truncatedTotalsJointMass fixedExternalJointMass uniformBlockWordMass
        positivity)
  · exact mul_nonneg hc.le (by
      unfold truncatedTotalsJointMass fixedExternalJointMass uniformBlockWordMass
      positivity)

/-- Concrete specialization of the abstract bridge to an atom `{τ=n}` with
arbitrary finite prefix data `S`. -/
theorem stoppedPrefixAtom_cappedSpatialFiber_conditional_factorization
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (n : ℕ) (S : Set (Fin n → Direction))
    (hApos : fairSteps (Erdos1165.stoppedPrefixAtom τ n S) ≠ 0)
    {o : Orientation} {i K : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (c : ℝ) (hc : 0 < c)
    (C : TruncatedDominoTotals x r m D → Set (Fin K → Direction))
    (hCdis : Pairwise fun z z' ↦ Disjoint (C z) (C z'))
    (hCmass : ∀ z, fairBlock K (C z) =
      ENNReal.ofReal (c * truncatedTotalsJointMass x r m D z))
    (ℓ : TruncatedDominoTotals x r m D) :
    (fairSteps (Erdos1165.stoppedPrefixAtom τ n S ∩
        postStoppingBlock τ K ⁻¹' C ℓ)).toReal /
      (fairSteps (Erdos1165.stoppedPrefixAtom τ n S ∩
        postStoppingBlock τ K ⁻¹' (⋃ z, C z))).toReal =
      ∏ b : AwayDomino x r D,
        truncatedDominoMass x r m b.1 (ℓ b) := by
  exact stopped_cappedSpatialFiber_conditional_factorization hτ
    (Erdos1165.isMeasurableAtStopping_stoppedPrefixAtom hτ n S)
    hApos x r m D c hc C hCdis hCmass ℓ

/-- The finite capped-level-clock specialization requested for the HLOZ
approximation.  The set `S` may encode a fixed external word together with
all favorite/level data on the atom where the capped level time equals `n`. -/
theorem truncatedLevelPrefixAtom_cappedSpatialFiber_conditional_factorization
    (levelM levelK cutoff n : ℕ) (S : Set (Fin n → Direction))
    (hApos : fairSteps (Erdos1165.stoppedPrefixAtom
      (StoppedInsertion.truncatedLevelTime levelM levelK cutoff) n S) ≠ 0)
    {o : Orientation} {i K : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (c : ℝ) (hc : 0 < c)
    (C : TruncatedDominoTotals x r m D → Set (Fin K → Direction))
    (hCdis : Pairwise fun z z' ↦ Disjoint (C z) (C z'))
    (hCmass : ∀ z, fairBlock K (C z) =
      ENNReal.ofReal (c * truncatedTotalsJointMass x r m D z))
    (ℓ : TruncatedDominoTotals x r m D) :
    (fairSteps (Erdos1165.stoppedPrefixAtom
        (StoppedInsertion.truncatedLevelTime levelM levelK cutoff) n S ∩
      postStoppingBlock (StoppedInsertion.truncatedLevelTime levelM levelK cutoff) K ⁻¹'
        C ℓ)).toReal /
      (fairSteps (Erdos1165.stoppedPrefixAtom
          (StoppedInsertion.truncatedLevelTime levelM levelK cutoff) n S ∩
        postStoppingBlock (StoppedInsertion.truncatedLevelTime levelM levelK cutoff) K ⁻¹'
          (⋃ z, C z))).toReal =
      ∏ b : AwayDomino x r D,
        truncatedDominoMass x r m b.1 (ℓ b) := by
  exact stoppedPrefixAtom_cappedSpatialFiber_conditional_factorization
    (StoppedInsertion.isFiniteStoppingTime_truncatedLevelTime levelM levelK cutoff)
    n S hApos x r m D c hc C hCdis hCmass ℓ

end Erdos1165.SpatialInsertionFiber

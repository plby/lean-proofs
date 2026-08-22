import ErdosProblems.Erdos1165.PreStoppingSpatialLaw
import ErdosProblems.Erdos1165.PreStoppingClosedPartition
import ErdosProblems.Erdos1165.PreStoppingCapRemoval
import ErdosProblems.Erdos1165.PreStoppingCutoff
import ErdosProblems.Erdos1165.HLOZSpatialAdapter

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.PreStoppingConditionalLaw

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber
open ShiftedPrefixBridge PrefixLevelTruncation PrefixConditionalLaw
open PreStoppingFiber PreStoppingSpatialLaw

noncomputable section

/-!
# The stopped-prefix form of the HLOZ spatial conditional law

This file collects the four independently checked ingredients of the spatial
insertion argument.

* `PreStoppingSpatialLaw` identifies the actual event `M_m^k`, on a stopped
  insertion atom, with distinguished-coordinate data and the literal
  prefix-corrected truncations on every other domino.
* `PrefixConditionalLaw` computes the normalized law after the distinguished
  coordinates have been marginalized.
* `PreStoppingClosedPartition` realizes every finite capped marginal as an
  actual measurable union of fair-walk cylinders.
* `PreStoppingCapRemoval` and `PreStoppingCutoff` remove respectively the
  insertion-coordinate cap and the artificial level-clock cutoff.

Thus the two main theorems below are the literal finite stopped-fibre version
of HLOZ (6.7), in the local-time convention of this development: a terminal
favorite level `m` imposes the strict upper bound `m + 1`.
-/

/-! ## Normalized product masses and screen probabilities -/

/-- The normalized point mass of an away-domino total vector, with arbitrary
per-domino upper cutoffs. -/
noncomputable def normalizedUpperTotalsMass
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    (ell : UpperTruncatedDominoTotals x r D upper) : ℝ :=
  upperTotalsJointMass x r D upper ell /
    ∑ z : UpperTruncatedDominoTotals x r D upper,
      upperTotalsJointMass x r D upper z

/-- The conditional probability, in one finite product fibre, of an arbitrary
predicate on the away-domino total vector. -/
noncomputable def upperProductScreenMass
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    (screen : UpperTruncatedDominoTotals x r D upper → Prop)
    [DecidablePred screen] : ℝ :=
  ∑ ell : UpperTruncatedDominoTotals x r D upper,
    if screen ell then normalizedUpperTotalsMass x r D upper ell else 0

/-- A finite screen probability is exactly the sum of the independent
one-domino truncated negative-binomial point masses. -/
theorem upperProductScreenMass_eq_product
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (D : Finset Point)
    (upper : ExternalDomino x r → ℕ)
    (screen : UpperTruncatedDominoTotals x r D upper → Prop)
    [DecidablePred screen] :
    upperProductScreenMass x r D upper screen =
      ∑ ell : UpperTruncatedDominoTotals x r D upper,
        if screen ell then
          ∏ b : AwayDomino x r D,
            upperTruncatedDominoMass x r upper b.1 (ell b)
        else 0 := by
  classical
  unfold upperProductScreenMass normalizedUpperTotalsMass
  apply Finset.sum_congr rfl
  intro ell _
  by_cases hell : screen ell
  · rw [if_pos hell, if_pos hell]
    exact upperTotals_conditional_factorization x r D upper ell
  · simp [hell]

/-! ## Literal stopped conditional product law -/

/-- Even-orientation stopped form of HLOZ (6.7).  The first conjunct is the
exact pathwise statement that `M_m^k` imposes precisely the distinguished
condition and the coordinatewise truncations away from the favorite
dominoes.  The second conjunct is the normalized conditional joint mass after
an arbitrary finite distinguished-coordinate marginal has been summed out.
-/
theorem even_stoppedConditionalProductLaw
    {i : ℕ} (m k cutoff n : ℕ) (omega : StepPath) (hk : 0 < k)
    (hn : n < cutoff) (htime : truncatedLevelTime m k cutoff omega = n)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks omega n = insertGapVector r q)
    {delta : Type*} [Fintype delta] (distinguishedMass : delta → ℝ)
    (hDist : (∑ d, distinguishedMass d) ≠ 0)
    (ell : EvenPrefixDominoTotals omega n r (m + 1)
      (favoriteDominoBases .even (trajectory omega) n)) :
    (levelFavorite (trajectory omega) m k ↔
        EvenDistinguishedCondition omega n r q (m + 1)
            (favoriteDominoBases .even (trajectory omega) n) ∧
          EvenPrefixDominoTruncation omega n r q (m + 1)
            (favoriteDominoBases .even (trajectory omega) n)) ∧
      (∑ d, upperTotalsJointMass (0, 0) r
            (favoriteDominoBases .even (trajectory omega) n)
            (fun b ↦ m + 1 - fixedEvenPrefixDominoMax omega n r b) ell *
          distinguishedMass d) /
          (∑ z : EvenPrefixDominoTotals omega n r (m + 1)
              (favoriteDominoBases .even (trajectory omega) n),
            ∑ d, upperTotalsJointMass (0, 0) r
                (favoriteDominoBases .even (trajectory omega) n)
                (fun b ↦ m + 1 - fixedEvenPrefixDominoMax omega n r b) z *
              distinguishedMass d) =
        ∏ b : AwayDomino (0, 0) r
            (favoriteDominoBases .even (trajectory omega) n),
          upperTruncatedDominoMass (0, 0) r
            (fun c ↦ m + 1 - fixedEvenPrefixDominoMax omega n r c)
            b.1 (ell b) := by
  constructor
  · exact
      even_levelFavorite_iff_distinguished_and_dominoTruncation_at_stoppedAtom
        m k cutoff n omega hk hn htime r q hword
  · exact distinguished_marginal_conditional_factorization
      (0, 0) r (favoriteDominoBases .even (trajectory omega) n)
      (fun b ↦ m + 1 - fixedEvenPrefixDominoMax omega n r b)
      distinguishedMass hDist ell

/-- Shifted-orientation stopped form of HLOZ (6.7), including the dropped
time-zero visit and the possible terminal singleton in the frozen local-time
cutoff. -/
theorem shifted_stoppedConditionalProductLaw
    {i : ℕ} (m k cutoff n : ℕ) (omega : StepPath) (hk : 0 < k)
    (hn : n < cutoff) (hpos : 0 < n)
    (htime : truncatedLevelTime m k cutoff omega = n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks omega n = insertGapVector r q)
    {delta : Type*} [Fintype delta] (distinguishedMass : delta → ℝ)
    (hDist : (∑ d, distinguishedMass d) ≠ 0)
    (ell : ShiftedPrefixDominoTotals omega n r (m + 1)
      (favoriteDominoBases .shifted (trajectory omega) n)) :
    (levelFavorite (trajectory omega) m k ↔
        ShiftedDistinguishedCondition omega n r q (m + 1)
            (favoriteDominoBases .shifted (trajectory omega) n) ∧
          ShiftedPrefixDominoTruncation omega n r q (m + 1)
            (favoriteDominoBases .shifted (trajectory omega) n)) ∧
      (∑ d, upperTotalsJointMass (trajectory omega 1) r
            (favoriteDominoBases .shifted (trajectory omega) n)
            (fun b ↦ m + 1 - fixedShiftedPrefixDominoMax omega n r b) ell *
          distinguishedMass d) /
          (∑ z : ShiftedPrefixDominoTotals omega n r (m + 1)
              (favoriteDominoBases .shifted (trajectory omega) n),
            ∑ d, upperTotalsJointMass (trajectory omega 1) r
                (favoriteDominoBases .shifted (trajectory omega) n)
                (fun b ↦ m + 1 - fixedShiftedPrefixDominoMax omega n r b) z *
              distinguishedMass d) =
        ∏ b : AwayDomino (trajectory omega 1) r
            (favoriteDominoBases .shifted (trajectory omega) n),
          upperTruncatedDominoMass (trajectory omega 1) r
            (fun c ↦ m + 1 - fixedShiftedPrefixDominoMax omega n r c)
            b.1 (ell b) := by
  constructor
  · exact
      shifted_levelFavorite_iff_distinguished_and_dominoTruncation_at_stoppedAtom
        m k cutoff n omega hk hn hpos htime r q hword
  · exact distinguished_marginal_conditional_factorization
      (trajectory omega 1) r
      (favoriteDominoBases .shifted (trajectory omega) n)
      (fun b ↦ m + 1 - fixedShiftedPrefixDominoMax omega n r b)
      distinguishedMass hDist ell

/-! ## The literal one-domino formula (6.7) -/

theorem even_stoppedConditionalMass_6_7
    {i : ℕ} (m k cutoff n : ℕ) (omega : StepPath) (hk : 0 < k)
    (hn : n < cutoff) (htime : truncatedLevelTime m k cutoff omega = n)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks omega n = insertGapVector r q)
    (b : AwayDomino (0, 0) r
      (favoriteDominoBases .even (trajectory omega) n))
    (ell : Fin (m + 1 - fixedEvenPrefixDominoMax omega n r b.1)) :
    (levelFavorite (trajectory omega) m k ↔
        EvenDistinguishedCondition omega n r q (m + 1)
            (favoriteDominoBases .even (trajectory omega) n) ∧
          EvenPrefixDominoTruncation omega n r q (m + 1)
            (favoriteDominoBases .even (trajectory omega) n)) ∧
      fixedExternalJointMass (dominoExternalMultiplicity (0, 0) r b.1) ell /
          (∑ j ∈ Finset.range
              (m + 1 - fixedEvenPrefixDominoMax omega n r b.1),
            fixedExternalJointMass
              (dominoExternalMultiplicity (0, 0) r b.1) j) =
        upperTruncatedDominoMass (0, 0) r
          (fun c ↦ m + 1 - fixedEvenPrefixDominoMax omega n r c) b.1 ell := by
  constructor
  · exact
      even_levelFavorite_iff_distinguished_and_dominoTruncation_at_stoppedAtom
        m k cutoff n omega hk hn htime r q hword
  · exact oneDomino_upperConditionalMass (0, 0) r
      (fun c ↦ m + 1 - fixedEvenPrefixDominoMax omega n r c) b.1 ell

theorem shifted_stoppedConditionalMass_6_7
    {i : ℕ} (m k cutoff n : ℕ) (omega : StepPath) (hk : 0 < k)
    (hn : n < cutoff) (hpos : 0 < n)
    (htime : truncatedLevelTime m k cutoff omega = n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks omega n = insertGapVector r q)
    (b : AwayDomino (trajectory omega 1) r
      (favoriteDominoBases .shifted (trajectory omega) n))
    (ell : Fin (m + 1 - fixedShiftedPrefixDominoMax omega n r b.1)) :
    (levelFavorite (trajectory omega) m k ↔
        ShiftedDistinguishedCondition omega n r q (m + 1)
            (favoriteDominoBases .shifted (trajectory omega) n) ∧
          ShiftedPrefixDominoTruncation omega n r q (m + 1)
            (favoriteDominoBases .shifted (trajectory omega) n)) ∧
      fixedExternalJointMass
            (dominoExternalMultiplicity (trajectory omega 1) r b.1) ell /
          (∑ j ∈ Finset.range
              (m + 1 - fixedShiftedPrefixDominoMax omega n r b.1),
            fixedExternalJointMass
              (dominoExternalMultiplicity (trajectory omega 1) r b.1) j) =
        upperTruncatedDominoMass (trajectory omega 1) r
          (fun c ↦ m + 1 - fixedShiftedPrefixDominoMax omega n r c)
          b.1 ell := by
  constructor
  · exact
      shifted_levelFavorite_iff_distinguished_and_dominoTruncation_at_stoppedAtom
        m k cutoff n omega hk hn hpos htime r q hword
  · exact oneDomino_upperConditionalMass (trajectory omega 1) r
      (fun c ↦ m + 1 - fixedShiftedPrefixDominoMax omega n r c) b.1 ell

/-! ## Actual finite cylinder masses and both cutoff removals -/

/-- The finite distinguished marginal is an actual measurable fair-walk
event and has exactly the product mass computed in
`PreStoppingClosedPartition`. -/
theorem fairSteps_closedCappedAwayTotalsEvent_factorization
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m cap : ℕ) (D : Finset Point)
    (a : RetainedBlock o) (ell : AwayDomino x r D → ℕ) :
    fairSteps (closedCappedAwayTotalsEvent x r m cap D a ell) =
      ENNReal.ofReal
        ((1 / 15 : ℝ) ^ (i + 1) *
          ∏ b : ExternalDomino x r,
            cappedDominoAwayMarginalMass x r m cap D ell b) := by
  rw [fairSteps_closedCappedAwayTotalsEvent,
    closedCappedAwayTotalsMass_factorization]

/-- Coordinate-cap convergence and clock-cutoff convergence can be used
simultaneously on every actual `M_m^k` path.  No global recurrence input is
needed for the clock statement. -/
theorem stoppedFiber_cap_and_clock_removal
    (tau : StepPath → ℕ)
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (tail : List Direction) (P : (Fin (i + 1) → ℕ) → Prop)
    (m k : ℕ) (omega : StepPath) (hk : 0 < k)
    (hM : levelFavorite (trajectory omega) m k) :
    Tendsto
        (fun cap ↦ fairSteps (coherentCappedFiberEvent tau r cap tail P))
        atTop
        (nhds (fairSteps (unboundedPreStoppingFiberEvent tau r tail P))) ∧
      Tendsto (fun cutoff ↦ truncatedLevelTime m k cutoff omega) atTop
        (nhds (unboundedLevelTimeNat m k omega)) := by
  exact ⟨tendsto_fairSteps_coherentCappedFiberEvent tau r tail P,
    tendsto_truncatedLevelTime_nat_of_levelFavorite m k omega hk hM⟩

/-! ## Restricted-real screen certificate -/

/-- Data left after the stopped product law has been applied on every finite
cap.  `productProbability` is the finite sum of product point masses (for
example `upperProductScreenMass`); `disintegrate` is only the identification
of that discrete probability with the corresponding capped path event.

In particular, this certificate does *not* assume the desired screen-measure
inequality.  That inequality is derived below from `product_bound` and cap
removal. -/
structure CappedProductScreenCertificate {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath) (cost : ℝ≥0∞) where
  screened : index → ℕ → Set WalkPath
  fiber : index → ℕ → Set WalkPath
  productProbability : index → ℕ → ℝ
  measurable_screened : ∀ z cap, MeasurableSet (screened z cap)
  monotone_screened : ∀ z, Monotone (screened z)
  /-- Cap exhaustion is needed only inside the stopped-past atom. -/
  next_subset : ∀ z, piece z ∩ next ⊆ ⋃ cap, screened z cap
  product_bound : ∀ z cap, productProbability z cap ≤ cost.toReal
  disintegrate : ∀ z cap,
    (simpleRandomWalk.restrict (piece z)).real (screened z cap) =
      productProbability z cap *
        (simpleRandomWalk.restrict (piece z)).real (fiber z cap)

/-- An increasing family of finite product screens gives the exact
`AtomwiseRestrictedRealScreen` interface consumed by `HLOZSpatialAdapter`.
The proof first derives the uniform finite-cap estimate from the normalized
product probability, then uses continuity from below. -/
theorem atomwiseRestrictedRealScreen_of_cappedProductCertificate
    {index : Type*} (piece : index → Set WalkPath) (next : Set WalkPath)
    (cost : ℝ≥0∞) (hcost : cost ≠ ∞)
    (certificate : CappedProductScreenCertificate piece next cost) :
    HLOZSpatialAdapter.AtomwiseRestrictedRealScreen piece next cost := by
  let screenUnion : index → Set WalkPath :=
    fun z ↦ ⋃ cap, certificate.screened z cap
  refine ⟨screenUnion, ?_, ?_, ?_⟩
  · intro z
    exact MeasurableSet.iUnion fun cap ↦ certificate.measurable_screened z cap
  · exact certificate.next_subset
  · intro z
    let nu := simpleRandomWalk.restrict (piece z)
    have hfinite : ∀ cap,
        nu.real (certificate.screened z cap) ≤
          (cost * simpleRandomWalk (piece z)).toReal := by
      intro cap
      calc
        nu.real (certificate.screened z cap) =
            certificate.productProbability z cap *
              nu.real (certificate.fiber z cap) := certificate.disintegrate z cap
        _ ≤ cost.toReal * nu.real (certificate.fiber z cap) :=
          mul_le_mul_of_nonneg_right (certificate.product_bound z cap)
            ENNReal.toReal_nonneg
        _ ≤ cost.toReal * nu.real Set.univ := by
          apply mul_le_mul_of_nonneg_left
          · exact measureReal_mono (Set.subset_univ _)
          · exact ENNReal.toReal_nonneg
        _ = (cost * simpleRandomWalk (piece z)).toReal := by
          change cost.toReal *
              ((simpleRandomWalk.restrict (piece z)) Set.univ).toReal = _
          rw [Measure.restrict_apply MeasurableSet.univ]
          simp only [Set.univ_inter]
          rw [ENNReal.toReal_mul]
    apply ENNReal.toReal_mono
      (ENNReal.mul_ne_top hcost (by finiteness))
    change nu (screenUnion z) ≤ cost * simpleRandomWalk (piece z)
    rw [show screenUnion z = ⋃ cap, certificate.screened z cap from rfl]
    rw [(certificate.monotone_screened z).measure_iUnion]
    apply iSup_le
    intro cap
    exact (ENNReal.toReal_le_toReal (by finiteness)
      (ENNReal.mul_ne_top hcost (by finiteness))).mp (hfinite cap)

/-- Direct constructor for the adapter screen from the stopped product law.
The external word, domino orientation, number of retained blocks, favorite
dominoes, and prefix-corrected upper cutoffs may all depend on both the
stopped-past atom and the finite cap.  The only analytic input is
`product_bound`, a bound on the explicit finite sum of the product masses.
The only path-space input is `disintegrate`, identifying that finite
probability with the corresponding capped path event. -/
theorem atomwiseRestrictedRealScreen_of_upperProductDisintegration
    {index : Type*} (piece : index → Set WalkPath) (next : Set WalkPath)
    (cost : ℝ≥0∞) (hcost : cost ≠ ∞)
    (orientation : index → ℕ → Orientation)
    (retainedCount : index → ℕ → ℕ)
    (x : index → ℕ → Point)
    (r : ∀ z cap,
      Fin (retainedCount z cap) → RetainedBlock (orientation z cap))
    (D : index → ℕ → Finset Point)
    (upper : ∀ z cap, ExternalDomino (x z cap) (r z cap) → ℕ)
    (screenPredicate : ∀ z cap,
      UpperTruncatedDominoTotals (x z cap) (r z cap) (D z cap)
        (upper z cap) → Prop)
    [screenDecidable : ∀ z cap, DecidablePred (screenPredicate z cap)]
    (screened fiber : index → ℕ → Set WalkPath)
    (hmeasurable : ∀ z cap, MeasurableSet (screened z cap))
    (hmonotone : ∀ z, Monotone (screened z))
    (hnext : ∀ z, piece z ∩ next ⊆ ⋃ cap, screened z cap)
    (hproduct : ∀ z cap,
      upperProductScreenMass (x z cap) (r z cap) (D z cap)
          (upper z cap) (screenPredicate z cap) ≤ cost.toReal)
    (hdisintegrate : ∀ z cap,
      (simpleRandomWalk.restrict (piece z)).real (screened z cap) =
        upperProductScreenMass (x z cap) (r z cap) (D z cap)
            (upper z cap) (screenPredicate z cap) *
          (simpleRandomWalk.restrict (piece z)).real (fiber z cap)) :
    HLOZSpatialAdapter.AtomwiseRestrictedRealScreen piece next cost := by
  apply atomwiseRestrictedRealScreen_of_cappedProductCertificate
    piece next cost hcost
  exact
    { screened := screened
      fiber := fiber
      productProbability := fun z cap ↦
        upperProductScreenMass (x z cap) (r z cap) (D z cap)
          (upper z cap) (screenPredicate z cap)
      measurable_screened := hmeasurable
      monotone_screened := hmonotone
      next_subset := hnext
      product_bound := hproduct
      disintegrate := hdisintegrate }

end

end Erdos1165.PreStoppingConditionalLaw

/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingCappedMarginalization

/-!
# Physical-prefix stopped product disintegration

The phase-shifted endpoint chain starts after a nonempty physical prefix.
Consequently the stopped cylinder is not the translated suffix cylinder used
by `tilingPreStoppingFiberEvent`: it must remember that prefix.  This file
gives the corresponding literal stopped atoms and their exact real mass.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.TilingPrefixedStoppedProductDisintegration

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber
open VariableStoppedFiber VariableStoppedTracePartition
open PreStoppingFiber PreStoppingConditionalLaw
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open TilingStoppedProductDisintegration
open TilingCappedMarginalization FiniteDominoProductLaw
open CappedCoordinateMassCertificate HLOZTraceCappedProductScreening
open HLOZPathEvents HLOZStoppedSpatialScreening

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The complete physical cylinder word: the orientation-dependent initial
prefix followed by the stateful inserted suffix. -/
def prefixedTilingInsertionPrefixList (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (q : Fin (i + 1) → ℕ) (tail : List Direction) : List Direction :=
  initial ++ tilingInsertionPrefixList t x r q tail

@[simp] theorem prefixedTilingInsertionPrefixList_length
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) :
    (prefixedTilingInsertionPrefixList initial t x r q tail).length =
      initial.length + (2 * (i + ∑ k, q k) + tail.length) := by
  simp [prefixedTilingInsertionPrefixList]

def prefixedTilingStoppedInsertionAtom (τ : StepPath → ℕ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) : Set StepPath :=
  let v := prefixedTilingInsertionPrefixList initial t x r q tail
  {ω | τ ω = v.length ∧ incrementPrefixList v.length ω = v}

def PrefixedTilingStoppingAccepted (τ : StepPath → ℕ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) : Prop :=
  let v := prefixedTilingInsertionPrefixList initial t x r q tail
  τ (extendPrefix (directionVectorOfList v)) = v.length

theorem prefixedTilingStoppedInsertionAtom_eq_cylinder
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction)
    (hacc : PrefixedTilingStoppingAccepted τ initial t x r q tail) :
    prefixedTilingStoppedInsertionAtom τ initial t x r q tail =
      {ω | stepPrefix
          (prefixedTilingInsertionPrefixList initial t x r q tail).length ω =
        directionVectorOfList
          (prefixedTilingInsertionPrefixList initial t x r q tail)} := by
  ext ω
  unfold prefixedTilingStoppedInsertionAtom
  simp only [Set.mem_setOf_eq]
  rw [incrementPrefixList_eq_iff_stepPrefix_eq_directionVector]
  constructor
  · exact fun h ↦ h.2
  · intro hp
    refine ⟨?_, hp⟩
    apply stoppingTime_eq_of_stepPrefix_eq hτ hacc
    rw [stepPrefix_extendPrefix]
    exact hp

theorem fairSteps_prefixedTilingStoppedInsertionAtom
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction)
    (hacc : PrefixedTilingStoppingAccepted τ initial t x r q tail) :
    fairSteps (prefixedTilingStoppedInsertionAtom τ initial t x r q tail) =
      (1 / 4 : ℝ≥0∞) ^
        (prefixedTilingInsertionPrefixList initial t x r q tail).length := by
  rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
    hτ initial t x r q tail hacc]
  exact fairSteps_stepPrefix_singleton_mass _ _

noncomputable def prefixedTilingInsertionPrefixMass
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) : ℝ :=
  (1 / 4 : ℝ) ^
    (prefixedTilingInsertionPrefixList initial t x r q tail).length

/-- The fibre-wide physical-prefix factor. -/
noncomputable def prefixedPrefixFiberConstant
    (initial : List Direction) (i : ℕ) (tail : List Direction) : ℝ :=
  (1 / 4 : ℝ) ^ initial.length * prefixFiberConstant i tail

theorem prefixedPrefixFiberConstant_nonneg
    (initial : List Direction) (i : ℕ) (tail : List Direction) :
    0 ≤ prefixedPrefixFiberConstant initial i tail := by
  unfold prefixedPrefixFiberConstant
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (VariableStoppedProductDisintegration.prefixFiberConstant_nonneg i tail)

theorem prefixedTilingInsertionPrefixMass_eq_const_mul_gapVectorMass
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction) :
    prefixedTilingInsertionPrefixMass initial t x r q tail =
      prefixedPrefixFiberConstant initial i tail * gapVectorMass q := by
  unfold prefixedTilingInsertionPrefixMass prefixedPrefixFiberConstant
    prefixedTilingInsertionPrefixList
  rw [List.length_append, pow_add]
  change (1 / 4 : ℝ) ^ initial.length *
      tilingInsertionPrefixMass t x r q tail =
    (1 / 4 : ℝ) ^ initial.length * prefixFiberConstant i tail *
      gapVectorMass q
  rw [tilingInsertionPrefixMass_eq_const_mul_gapVectorMass]
  ring

theorem fairSteps_prefixedTilingStoppedInsertionAtom_eq_ofReal
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (q : Fin (i + 1) → ℕ)
    (tail : List Direction)
    (hacc : PrefixedTilingStoppingAccepted τ initial t x r q tail) :
    fairSteps (prefixedTilingStoppedInsertionAtom τ initial t x r q tail) =
      ENNReal.ofReal
        (prefixedTilingInsertionPrefixMass initial t x r q tail) := by
  rw [fairSteps_prefixedTilingStoppedInsertionAtom
    hτ initial t x r q tail hacc]
  unfold prefixedTilingInsertionPrefixMass
  rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 1 / 4)]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  norm_num

theorem prefixedTilingInsertionPrefixList_injective
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (tail : List Direction) :
    Function.Injective (fun q : Fin (i + 1) → ℕ ↦
      prefixedTilingInsertionPrefixList initial t x r q tail) := by
  intro q q' h
  apply tilingInsertionPrefixList_injective t x r tail
  exact List.append_cancel_left h

theorem prefixedTilingStoppedInsertionAtom_pairwise_disjoint
    (τ : StepPath → ℕ) (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) :
    Pairwise fun q q' : Fin (i + 1) → ℕ ↦
      Disjoint (prefixedTilingStoppedInsertionAtom τ initial t x r q tail)
        (prefixedTilingStoppedInsertionAtom τ initial t x r q' tail) := by
  intro q q' hqq'
  rw [Set.disjoint_left]
  intro ω hq hq'
  apply hqq'
  apply prefixedTilingInsertionPrefixList_injective initial t x r tail
  have hlen :
      (prefixedTilingInsertionPrefixList initial t x r q tail).length =
        (prefixedTilingInsertionPrefixList initial t x r q' tail).length :=
    hq.1.symm.trans hq'.1
  unfold prefixedTilingStoppedInsertionAtom at hq hq'
  simp only [Set.mem_ofPred_eq] at hq hq'
  rw [hlen] at hq
  exact hq.2.symm.trans hq'.2

/-- Capped coordinates satisfying the physical-prefix stopping rule. -/
abbrev PrefixedTilingAcceptedCappedCoordinates
    (τ : StepPath → ℕ) (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :=
  {q : TilingCappedCoordinates i cap //
    P q ∧ PrefixedTilingStoppingAccepted τ initial t x r
      (fun k ↦ (q k : ℕ)) tail}

noncomputable instance prefixedTilingAcceptedCappedCoordinatesFintype
    (τ : StepPath → ℕ) (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    Fintype
      (PrefixedTilingAcceptedCappedCoordinates τ initial t x r cap tail P) :=
  Fintype.ofFinite _

/-- Finite union of physical-prefix accepted stopped atoms. -/
def prefixedTilingPreStoppingFiberEvent
    (τ : StepPath → ℕ) (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) : Set StepPath :=
  ⋃ q : PrefixedTilingAcceptedCappedCoordinates
      τ initial t x r cap tail P,
    prefixedTilingStoppedInsertionAtom τ initial t x r
      (fun k ↦ (q.1 k : ℕ)) tail

theorem prefixedTilingAcceptedCappedAtoms_pairwise_disjoint
    (τ : StepPath → ℕ) (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    Pairwise fun q q' : PrefixedTilingAcceptedCappedCoordinates
        τ initial t x r cap tail P ↦
      Disjoint
        (prefixedTilingStoppedInsertionAtom τ initial t x r
          (fun k ↦ (q.1 k : ℕ)) tail)
        (prefixedTilingStoppedInsertionAtom τ initial t x r
          (fun k ↦ (q'.1 k : ℕ)) tail) := by
  intro q q' hqq'
  apply prefixedTilingStoppedInsertionAtom_pairwise_disjoint
    τ initial t x r tail
  intro h
  apply hqq'
  apply Subtype.ext
  funext k
  apply Fin.ext
  exact congrFun h k

theorem measurableSet_prefixedTilingPreStoppingFiberEvent
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    MeasurableSet
      (prefixedTilingPreStoppingFiberEvent τ initial t x r cap tail P) := by
  classical
  exact MeasurableSet.iUnion fun q ↦ by
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      hτ initial t x r _ tail q.2.2]
    exact measurableSet_eq_fun (measurable_stepPrefix _) measurable_const

theorem prefixedTilingPreStoppingFiberEvent_mono
    (τ : StepPath → ℕ) (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) {P Q : TilingCappedCoordinates i cap → Prop}
    (hQP : ∀ q, Q q → P q) :
    prefixedTilingPreStoppingFiberEvent τ initial t x r cap tail Q ⊆
      prefixedTilingPreStoppingFiberEvent τ initial t x r cap tail P := by
  classical
  intro ω hω
  rcases Set.mem_iUnion.mp hω with ⟨q, hq⟩
  apply Set.mem_iUnion.mpr
  exact ⟨⟨q.1, hQP q.1 q.2.1, q.2.2⟩, hq⟩

/-- A natural-coordinate predicate gives a monotone family of capped
physical-prefix fibres for a fixed stopping clock. -/
theorem monotone_prefixedTilingPreStoppingFiberEvent_of_natPredicate
    (τ : StepPath → ℕ) (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) (P : (Fin (i + 1) → ℕ) → Prop) :
    Monotone fun cap ↦ prefixedTilingPreStoppingFiberEvent
      τ initial t x r cap tail (fun q ↦ P (fun j ↦ (q j : ℕ))) := by
  intro cap cap' hcap ω hω
  rcases Set.mem_iUnion.mp hω with ⟨q, hq⟩
  let q' : TilingCappedCoordinates i cap' := fun j ↦
    Fin.castLE (Nat.succ_le_succ hcap) (q.1 j)
  have hval : ∀ j, (q' j : ℕ) = (q.1 j : ℕ) := fun _ ↦ rfl
  have hP : P (fun j ↦ (q' j : ℕ)) := by
    simpa only [hval] using q.2.1
  have haccepted : PrefixedTilingStoppingAccepted τ initial t x r
      (fun j ↦ (q' j : ℕ)) tail := by
    simpa only [hval] using q.2.2
  apply Set.mem_iUnion.mpr
  refine ⟨⟨q', hP, haccepted⟩, ?_⟩
  simpa only [hval] using hq

/-- Every accepted natural-valued physical-prefix insertion atom occurs in
the cofinal cap schedule `capStart + stage`. -/
theorem prefixedTilingStoppedInsertionAtom_subset_iUnion_cofinalCaps
    (τ : StepPath → ℕ) (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) (capStart : ℕ)
    (P : (Fin (i + 1) → ℕ) → Prop) (q : Fin (i + 1) → ℕ)
    (hP : P q)
    (haccepted : PrefixedTilingStoppingAccepted τ initial t x r q tail) :
    prefixedTilingStoppedInsertionAtom τ initial t x r q tail ⊆
      ⋃ stage, prefixedTilingPreStoppingFiberEvent τ initial t x r
        (capStart + stage) tail (fun qc ↦ P (fun j ↦ (qc j : ℕ))) := by
  classical
  let stage := ∑ j, q j
  have hle (j : Fin (i + 1)) : q j ≤ capStart + stage := by
    have hj : q j ≤ stage :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  let qc : TilingCappedCoordinates i (capStart + stage) := fun j ↦
    ⟨q j, Nat.lt_succ_of_le (hle j)⟩
  have hval : ∀ j, (qc j : ℕ) = q j := fun _ ↦ rfl
  intro ω hω
  apply Set.mem_iUnion.mpr
  refine ⟨stage, Set.mem_iUnion.mpr ⟨⟨qc, ?_, ?_⟩, ?_⟩⟩
  · simpa only [hval] using hP
  · simpa only [hval] using haccepted
  · simpa only [hval] using hω

theorem fairSteps_prefixedTilingPreStoppingFiberEvent
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    fairSteps
        (prefixedTilingPreStoppingFiberEvent τ initial t x r cap tail P) =
      ENNReal.ofReal
        (∑ q : PrefixedTilingAcceptedCappedCoordinates
            τ initial t x r cap tail P,
          prefixedTilingInsertionPrefixMass initial t x r
            (fun k ↦ (q.1 k : ℕ)) tail) := by
  classical
  have hmeas : ∀ q : PrefixedTilingAcceptedCappedCoordinates
      τ initial t x r cap tail P,
      MeasurableSet (prefixedTilingStoppedInsertionAtom τ initial t x r
        (fun k ↦ (q.1 k : ℕ)) tail) := by
    intro q
    rw [prefixedTilingStoppedInsertionAtom_eq_cylinder
      hτ initial t x r _ tail q.2.2]
    exact measurableSet_eq_fun (measurable_stepPrefix _) measurable_const
  have hdis : Pairwise fun q q' : PrefixedTilingAcceptedCappedCoordinates
      τ initial t x r cap tail P ↦
      Disjoint
        (prefixedTilingStoppedInsertionAtom τ initial t x r
          (fun k ↦ (q.1 k : ℕ)) tail)
        (prefixedTilingStoppedInsertionAtom τ initial t x r
          (fun k ↦ (q'.1 k : ℕ)) tail) :=
    prefixedTilingAcceptedCappedAtoms_pairwise_disjoint
      τ initial t x r cap tail P
  unfold prefixedTilingPreStoppingFiberEvent
  rw [measure_iUnion hdis hmeas]
  simp_rw [show ∀ q : PrefixedTilingAcceptedCappedCoordinates
      τ initial t x r cap tail P,
      fairSteps (prefixedTilingStoppedInsertionAtom τ initial t x r
          (fun k ↦ (q.1 k : ℕ)) tail) =
        ENNReal.ofReal (prefixedTilingInsertionPrefixMass initial t x r
          (fun k ↦ (q.1 k : ℕ)) tail) from
    fun q ↦ fairSteps_prefixedTilingStoppedInsertionAtom_eq_ofReal
      hτ initial t x r _ tail q.2.2]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
  intro q _
  unfold prefixedTilingInsertionPrefixMass
  positivity

/-- Explicit geometric mass of the accepted physical-prefix coordinates. -/
noncomputable def prefixedTilingStoppedAcceptedGeometricMass
    (τ : StepPath → ℕ) (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) : ℝ :=
  ∑ q : PrefixedTilingAcceptedCappedCoordinates
      τ initial t x r cap tail P,
    gapVectorMass (fun j ↦ (q.1 j : ℕ))

theorem prefixedTilingStoppedAcceptedGeometricMass_nonneg
    (τ : StepPath → ℕ) (initial : List Direction) {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    0 ≤ prefixedTilingStoppedAcceptedGeometricMass
      τ initial t x r cap tail P := by
  unfold prefixedTilingStoppedAcceptedGeometricMass
  exact Finset.sum_nonneg fun q _ ↦
    VariableStoppedProductDisintegration.gapVectorMass_nonneg _

theorem fairSteps_prefixedTilingPreStoppingFiberEvent_eq_geometricSum
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    fairSteps
        (prefixedTilingPreStoppingFiberEvent τ initial t x r cap tail P) =
      ENNReal.ofReal
        (prefixedPrefixFiberConstant initial i tail *
          prefixedTilingStoppedAcceptedGeometricMass
            τ initial t x r cap tail P) := by
  rw [fairSteps_prefixedTilingPreStoppingFiberEvent
    hτ initial t x r cap tail P]
  congr 1
  simp_rw [prefixedTilingInsertionPrefixMass_eq_const_mul_gapVectorMass]
  unfold prefixedTilingStoppedAcceptedGeometricMass
  rw [Finset.mul_sum]

noncomputable instance instDecidablePredPrefixedTilingStoppingAccepted
    (τ : StepPath → ℕ) (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) :
    DecidablePred (fun q : TilingCappedCoordinates i cap ↦
      PrefixedTilingStoppingAccepted τ initial t x r
        (fun k ↦ (q k : ℕ)) tail) :=
  Classical.decPred _

theorem fairSteps_real_prefixedTilingPreStoppingFiberEvent
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    fairSteps.real
        (prefixedTilingPreStoppingFiberEvent τ initial t x r cap tail P) =
      prefixedPrefixFiberConstant initial i tail *
        prefixedTilingStoppedAcceptedGeometricMass
          τ initial t x r cap tail P := by
  rw [Measure.real,
    fairSteps_prefixedTilingPreStoppingFiberEvent_eq_geometricSum
      hτ initial t x r cap tail P]
  exact ENNReal.toReal_ofReal (mul_nonneg
    (prefixedPrefixFiberConstant_nonneg initial i tail)
    (prefixedTilingStoppedAcceptedGeometricMass_nonneg
      τ initial t x r cap tail P))

theorem simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    simpleRandomWalk
        (walkLift (prefixedTilingPreStoppingFiberEvent
          τ initial t x r cap tail P)) =
      ENNReal.ofReal
        (prefixedPrefixFiberConstant initial i tail *
          prefixedTilingStoppedAcceptedGeometricMass
            τ initial t x r cap tail P) := by
  have hmeas := measurableSet_prefixedTilingPreStoppingFiberEvent
    hτ initial t x r cap tail P
  rw [simpleRandomWalk_walkLift hmeas]
  exact fairSteps_prefixedTilingPreStoppingFiberEvent_eq_geometricSum
    hτ initial t x r cap tail P

theorem simpleRandomWalk_real_walkLift_prefixedTilingPreStoppingFiberEvent
    {τ : StepPath → ℕ} (hτ : IsFiniteStoppingTime τ)
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (cap : ℕ) (tail : List Direction)
    (P : TilingCappedCoordinates i cap → Prop) :
    simpleRandomWalk.real
        (walkLift (prefixedTilingPreStoppingFiberEvent
          τ initial t x r cap tail P)) =
      prefixedPrefixFiberConstant initial i tail *
        prefixedTilingStoppedAcceptedGeometricMass
          τ initial t x r cap tail P := by
  have hmeas := measurableSet_prefixedTilingPreStoppingFiberEvent
    hτ initial t x r cap tail P
  rw [Measure.real, simpleRandomWalk_walkLift hmeas]
  exact fairSteps_real_prefixedTilingPreStoppingFiberEvent
    hτ initial t x r cap tail P

theorem prefixedTilingStoppedAcceptedGeometricMass_eq_indicatorSum
    (τ : StepPath → ℕ) (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) (P : TilingCappedCoordinates i cap → Prop)
    [DecidablePred P] :
    prefixedTilingStoppedAcceptedGeometricMass
        τ initial t x r cap tail P =
      ∑ q : TilingCappedCoordinates i cap,
        if P q ∧ PrefixedTilingStoppingAccepted τ initial t x r
            (fun k ↦ (q k : ℕ)) tail then
          gapVectorMass (fun k ↦ (q k : ℕ)) else 0 := by
  classical
  unfold prefixedTilingStoppedAcceptedGeometricMass
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subtype
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Exact finite product law with the physical-prefix stopping acceptance.
The initial word changes only the common cylinder factor; the normalized
coordinate product remains the same geometric product. -/
theorem prefixedTilingStoppedAcceptedGeometricMass_product_of_factorization
    (τ : StepPath → ℕ) (initial : List Direction) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction)
    (base screened : TilingCappedCoordinates i cap → Prop)
    [DecidablePred base] [DecidablePred screened]
    (D : Finset Point)
    (selected : TilingDistinguishedCoordinates (cap := cap) t x r D → Prop)
    [DecidablePred selected]
    (upper : TilingCappedMarginalization.TilingAwayDomino t x r D → ℕ)
    (screen : FiniteDominoProductLaw.TruncatedTotals upper → Prop)
    [DecidablePred screen]
    (hbase : ∀ q,
      base q ∧ PrefixedTilingStoppingAccepted τ initial t x r
          (fun k ↦ (q k : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
            (splitTilingCoordinatesEquiv t x r D q).2)
    (hscreen : ∀ q,
      screened q ∧ PrefixedTilingStoppingAccepted τ initial t x r
          (fun k ↦ (q k : ℕ)) tail ↔
        selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
          TilingAwayTotalsScreen t x r D upper screen
            (splitTilingCoordinatesEquiv t x r D q).2)
    (htotal : (∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
      FiniteDominoProductLaw.jointMass
        (tilingAwayPointMass (cap := cap) t x r D) upper ℓ) ≠ 0) :
    prefixedTilingStoppedAcceptedGeometricMass
        τ initial t x r cap tail screened =
      FiniteDominoProductLaw.screenMass
          (tilingAwayPointMass (cap := cap) t x r D) upper screen *
        prefixedTilingStoppedAcceptedGeometricMass
          τ initial t x r cap tail base := by
  classical
  have hbaseMass :
      prefixedTilingStoppedAcceptedGeometricMass
          τ initial t x r cap tail base =
        ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
          FiniteDominoProductLaw.distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ℓ := by
    rw [prefixedTilingStoppedAcceptedGeometricMass_eq_indicatorSum]
    calc
      (∑ q : TilingCappedCoordinates i cap,
          if base q ∧ PrefixedTilingStoppingAccepted τ initial t x r
              (fun k ↦ (q k : ℕ)) tail then
            gapVectorMass (fun k ↦ (q k : ℕ)) else 0) =
          ∑ q : TilingCappedCoordinates i cap,
            if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
                TilingAwayTotalsScreen t x r D upper (fun _ ↦ True)
                  (splitTilingCoordinatesEquiv t x r D q).2 then
              gapVectorMass (fun k ↦ (q k : ℕ)) else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        exact if_congr (hbase q) rfl rfl
      _ = ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
          FiniteDominoProductLaw.distinguishedAwayMass
            (tilingAwayPointMass (cap := cap) t x r D) upper
            (fun d ↦ if selected d then
              tilingDistinguishedAssignmentMass t x r D d else 0) ℓ := by
        simpa using (tilingCappedScreenedMass_factorization
          t x r D selected upper (fun _ ↦ True))
  have hscreenMass :
      prefixedTilingStoppedAcceptedGeometricMass
          τ initial t x r cap tail screened =
        ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
          if screen ℓ then
            FiniteDominoProductLaw.distinguishedAwayMass
              (tilingAwayPointMass (cap := cap) t x r D) upper
              (fun d ↦ if selected d then
                tilingDistinguishedAssignmentMass t x r D d else 0) ℓ
          else 0 := by
    rw [prefixedTilingStoppedAcceptedGeometricMass_eq_indicatorSum]
    calc
      (∑ q : TilingCappedCoordinates i cap,
          if screened q ∧ PrefixedTilingStoppingAccepted τ initial t x r
              (fun k ↦ (q k : ℕ)) tail then
            gapVectorMass (fun k ↦ (q k : ℕ)) else 0) =
          ∑ q : TilingCappedCoordinates i cap,
            if selected ((splitTilingCoordinatesEquiv t x r D q).1) ∧
                TilingAwayTotalsScreen t x r D upper screen
                  (splitTilingCoordinatesEquiv t x r D q).2 then
              gapVectorMass (fun k ↦ (q k : ℕ)) else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        exact if_congr (hscreen q) rfl rfl
      _ = ∑ ℓ : FiniteDominoProductLaw.TruncatedTotals upper,
          if screen ℓ then
            FiniteDominoProductLaw.distinguishedAwayMass
              (tilingAwayPointMass (cap := cap) t x r D) upper
              (fun d ↦ if selected d then
                tilingDistinguishedAssignmentMass t x r D d else 0) ℓ
          else 0 := tilingCappedScreenedMass_factorization
            t x r D selected upper screen
  rw [hscreenMass, hbaseMass]
  exact (screenMass_mul_distinguishedBase
    (tilingAwayPointMass (cap := cap) t x r D) upper screen
    (fun d ↦ if selected d then
      tilingDistinguishedAssignmentMass t x r D d else 0) htotal).symm

end

end Erdos1165.TilingPrefixedStoppedProductDisintegration

import ErdosProblems.Erdos1165.TilingTypedTransitionFactorization
import ErdosProblems.Erdos1165.HLOZShellZeroReplacementProduct
import ErdosProblems.Erdos1165.HLOZShellZeroReplacementWindows

/-!
# Pathwise shell-zero replacement on typed tiling fibres

HLOZ's initial-shell comparison replaces selected away-domino totals in the
upper window by totals in an artificial window above level `m`.  Such a
replacement need not remain accepted by the old rank-`k` clock: it can create
new level-`m` sites.  Consequently this module does not claim old-stage
invariance.  It records the honest coordinate replacement and refines every
replacement event by the newly created rank and its complete finite physical
prefix.  These creation-prefix atoms are globally disjoint, even when the
replacement changes the physical stopping time.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.TilingTypedShellZeroReplacement

open HLOZPathEvents HLOZSpatialAdapter
open HLOZShellZeroReplacementProduct
open HLOZShellZeroReplacementWindows
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingCappedMarginalization TilingTypedFavoriteTrace
open TilingTypedFavoriteFactorization TilingStoppedAcceptanceFactorization
open TilingDistinguishedTraceInvariant
open TilingStoppedProductDisintegration
open SpatialInsertionFiber
open PreStoppingFiber VariableStoppedFiber VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-! ## Replacing only the away coordinates -/

/-- Replace all away coordinates while leaving every distinguished coordinate
literal unchanged. -/
def replaceTypedAwayCoordinates {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (away : TilingAwayCoordinates (cap := cap) t (0, 0)
      (typedRetained z) (typedDistinguished z)) :
    TilingCappedCoordinates (typedRetainedCount z) cap :=
  (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
    (typedDistinguished z)).symm
      ((splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).1, away)

theorem split_replaceTypedAwayCoordinates {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (away : TilingAwayCoordinates (cap := cap) t (0, 0)
      (typedRetained z) (typedDistinguished z)) :
    splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) (replaceTypedAwayCoordinates z q away) =
      ((splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
        (typedDistinguished z) q).1, away) :=
  (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
    (typedDistinguished z)).apply_symm_apply _

theorem distinguished_replaceTypedAwayCoordinates {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (away : TilingAwayCoordinates (cap := cap) t (0, 0)
      (typedRetained z) (typedDistinguished z)) :
    (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
      (typedDistinguished z) (replaceTypedAwayCoordinates z q away)).1 =
    (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
      (typedDistinguished z) q).1 := by
  rw [split_replaceTypedAwayCoordinates]

theorem away_replaceTypedAwayCoordinates {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (away : TilingAwayCoordinates (cap := cap) t (0, 0)
      (typedRetained z) (typedDistinguished z)) :
    (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
      (typedDistinguished z) (replaceTypedAwayCoordinates z q away)).2 = away := by
  rw [split_replaceTypedAwayCoordinates]

theorem replaceTypedAwayCoordinates_injective {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) :
    Function.Injective (replaceTypedAwayCoordinates z q) := by
  intro away away' h
  have := congrArg (fun q' ↦
    (splitTilingCoordinatesEquiv t (0, 0) (typedRetained z)
      (typedDistinguished z) q').2) h
  simpa only [away_replaceTypedAwayCoordinates] using this

/-! ## Globally disjoint creation-prefix atoms -/

/-- A complete finite physical prefix, including its physical horizon. -/
abbrev CreationPrefixCode := Σ n : ℕ, Fin (n + 1) → Point

/-- Paths having the prescribed physical prefix and creating the prescribed
level-`m` rank at its endpoint. -/
def creationPrefixAtom (m rank : ℕ) (code : CreationPrefixCode) :
    Set WalkPath :=
  {s | pathPrefix s code.1 = code.2 ∧
    ThresholdCreation s m rank code.1}

theorem measurableSet_creationPrefixAtom (m rank : ℕ)
    (code : CreationPrefixCode) :
    MeasurableSet (creationPrefixAtom m rank code) := by
  exact (measurableSet_eq_fun (measurable_pathPrefix code.1) measurable_const).inter
    (measurableSet_thresholdCreationSet m rank code.1)

/-- Fixing the same creation rank makes complete creation-prefix atoms
pairwise disjoint.  Equal horizons force unequal prefixes; unequal horizons
contradict uniqueness of the creation time. -/
theorem disjoint_creationPrefixAtom_of_ne (m rank : ℕ)
    {code code' : CreationPrefixCode} (hne : code ≠ code') :
    Disjoint (creationPrefixAtom m rank code)
      (creationPrefixAtom m rank code') := by
  rcases code with ⟨n, p⟩
  rcases code' with ⟨n', p'⟩
  rw [Set.disjoint_left]
  intro s hs hs'
  have hn : n = n' := thresholdCreation_time_unique hs.2 hs'.2
  subst n'
  have hp : p = p' := hs.1.symm.trans hs'.1
  subst p'
  exact hne rfl

theorem pairwise_disjoint_creationPrefixAtom (m rank : ℕ) :
    Pairwise fun code code' : CreationPrefixCode ↦
      Disjoint (creationPrefixAtom m rank code)
        (creationPrefixAtom m rank code') :=
  fun _ _ hne ↦ disjoint_creationPrefixAtom_of_ne m rank hne

/-- The physical creation-prefix code of one reconstructed typed insertion
word. -/
def typedInsertionCreationPrefixCode {t : DominoTiling}
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) :
    CreationPrefixCode :=
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  ⟨v.length, pathPrefix (typedInsertionWalk z q) v.length⟩

theorem typedInsertionWalk_mem_creationPrefixAtom_iff
    {t : DominoTiling} (z : TypedFavoriteTilingTraceCode t)
    {cap m rank : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap) :
    typedInsertionWalk z q ∈ creationPrefixAtom m rank
        (typedInsertionCreationPrefixCode z q) ↔
      let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
        (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
      ThresholdCreation (typedInsertionWalk z q) m rank v.length := by
  simp [creationPrefixAtom, typedInsertionCreationPrefixCode]

theorem typedInsertionWalk_mem_creationPrefixAtom_of_stoppingAccepted
    {t : DominoTiling} (m rank : ℕ)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m rank z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    typedInsertionWalk z q ∈ creationPrefixAtom m rank
      (typedInsertionCreationPrefixCode z q) := by
  rw [typedInsertionWalk_mem_creationPrefixAtom_iff]
  exact (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
    m rank (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z)
    (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q)).mp haccepted

/-- Every continuation in an accepted stopped insertion cylinder belongs to
the same complete creation-prefix atom.  This is the direct pathwise bridge
used for a replacement `B_η`: the walk after the recorded prefix is entirely
irrelevant. -/
theorem walkLift_tilingStoppedInsertionAtom_subset_creationPrefixAtom
    {t : DominoTiling} (m rank : ℕ)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m rank z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    walkLift (tilingStoppedInsertionAtom (typedStoppingTime m rank z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) ⊆
        creationPrefixAtom m rank (typedInsertionCreationPrefixCode z q) := by
  intro s hs
  rcases hs with ⟨hvalid, homega⟩
  let v := tilingInsertionPrefixList t (0, 0) (typedRetained z)
    (fun j ↦ (q j : ℕ)) (typedBoundaryTail z).1
  let canonical := typedInsertionWalk z q
  have hp : pathPrefix (trajectory (stepsOfWalk s)) v.length =
      pathPrefix canonical v.length := by
    exact pathPrefix_eq_canonical_of_mem_tilingStoppedInsertionAtom
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1 (stepsOfWalk s) homega
  have hs_eq : trajectory (stepsOfWalk s) = s := hvalid
  rw [hs_eq] at hp
  have hcanonical : ThresholdCreation canonical m rank v.length := by
    exact (tilingStoppingAccepted_truncatedLevelTime_iff_thresholdCreation
      m rank (typedCoordinateCutoff z cap) t (0, 0) (typedRetained z)
      (fun j ↦ (q j : ℕ)) (typedBoundaryTail z)
      (tilingInsertionPrefixList_lt_typedCoordinateCutoff z cap q)).mp haccepted
  have hcreation : ThresholdCreation s m rank v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp (Nat.le_refl v.length)).mpr
      hcanonical
  change pathPrefix s v.length = pathPrefix canonical v.length ∧
    ThresholdCreation s m rank v.length
  exact ⟨hp, hcreation⟩

theorem measurableSet_walkLift_tilingStoppedInsertionAtom
    {t : DominoTiling} (m rank : ℕ)
    (z : TypedFavoriteTilingTraceCode t) {cap : ℕ}
    (q : TilingCappedCoordinates (typedRetainedCount z) cap)
    (haccepted : TilingStoppingAccepted (typedStoppingTime m rank z cap)
      t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
      (typedBoundaryTail z).1) :
    MeasurableSet
      (walkLift (tilingStoppedInsertionAtom (typedStoppingTime m rank z cap)
        t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
        (typedBoundaryTail z).1)) := by
  apply measurableSet_walkLift
  rw [tilingStoppedInsertionAtom_eq_cylinder
    (isFiniteStoppingTime_typedStoppingTime m rank z cap)
    t (0, 0) (typedRetained z) (fun j ↦ (q j : ℕ))
    (typedBoundaryTail z).1 haccepted]
  exact measurableSet_eq_fun (measurable_stepPrefix _) measurable_const

/-! ## Exact adapter to the global shell-zero summation certificate -/

/-- Concrete disjointness data for a family of shell-zero replacements.  A
replacement is allowed to impose extra conditions, but it must reveal an
injective complete prefix at which one fixed new rank is created. -/
structure CreationPrefixReplacementData
    {Index : Type*} [Countable Index]
    (mu : Measure WalkPath) (source : Set WalkPath) (q : ℝ≥0∞)
    (m rank : ℕ) where
  sourceAtom : Index → Set WalkPath
  replacement : Index → Set WalkPath
  code : Index → CreationPrefixCode
  code_injective : Function.Injective code
  source_subset : source ⊆ ⋃ z, sourceAtom z
  atom_le : ∀ z, mu (sourceAtom z) ≤ q * mu (replacement z)
  measurable_replacement : ∀ z, MeasurableSet (replacement z)
  replacement_subset : ∀ z,
    replacement z ⊆ creationPrefixAtom m rank (code z)

theorem CreationPrefixReplacementData.disjoint_replacement
    {Index : Type*} [Countable Index]
    {mu : Measure WalkPath} {source : Set WalkPath} {q : ℝ≥0∞}
    {m rank : ℕ}
    (data : CreationPrefixReplacementData
      (Index := Index) mu source q m rank) :
    Pairwise fun z w ↦ Disjoint (data.replacement z) (data.replacement w) := by
  intro z w hzw
  exact (disjoint_creationPrefixAtom_of_ne m rank
    (fun h ↦ hzw (data.code_injective h))).mono
      (data.replacement_subset z) (data.replacement_subset w)

/-- Turn the pathwise creation-prefix construction into the exact global
certificate consumed by `HLOZShellZeroReplacementProduct`.  In particular,
pairwise disjointness is now a theorem rather than a premise at the global
summation layer. -/
def globalDisjointReplacementCertificateOfCreationPrefixes
    {Index : Type*} [Countable Index]
    (mu : Measure WalkPath) (source : Set WalkPath) (q : ℝ≥0∞)
    (m rank : ℕ)
    (data : CreationPrefixReplacementData
      (Index := Index) mu source q m rank) :
    GlobalDisjointReplacementCertificate
      (Index := Index) mu source q where
  sourceAtom := data.sourceAtom
  replacement := data.replacement
  source_subset := data.source_subset
  atom_le := data.atom_le
  measurable_replacement := data.measurable_replacement
  disjoint_replacement := data.disjoint_replacement

/-- Exact-product version of the creation-prefix adapter.  The finite
`I₀/I₁` calculation supplies `atom`; creation-prefix injectivity supplies
the pairwise-disjoint `B_η` summation required by the global theorem. -/
def globalDisjointReplacementCertificateOfCreationPrefixAtomProducts
    {Index : Type*} [Countable Index]
    (mu : Measure WalkPath) [IsFiniteMeasure mu]
    (source : Set WalkPath)
    (sourceAtom replacement : Index → Set WalkPath)
    (code : Index → CreationPrefixCode)
    (q : ℝ) (m rank : ℕ)
    (hcode : Function.Injective code)
    (hsource : source ⊆ ⋃ z, sourceAtom z)
    (hmeasurable : ∀ z, MeasurableSet (replacement z))
    (hsubset : ∀ z, replacement z ⊆ creationPrefixAtom m rank (code z))
    (atom : ∀ z, ReplacementAtomProductCertificate
      mu (sourceAtom z) (replacement z) q) :
    GlobalDisjointReplacementCertificate
      (Index := Index) mu source (ENNReal.ofReal q) :=
  globalDisjointReplacementCertificateOfAtomProducts
    mu source sourceAtom replacement q hsource hmeasurable
      (fun z w hzw ↦
        (disjoint_creationPrefixAtom_of_ne m rank
          (fun h ↦ hzw (hcode h))).mono (hsubset z) (hsubset w))
      atom

/-! ## Exact two-clock stopped-fibre atom products -/

/-- When a coordinate predicate itself guarantees acceptance by its chosen
clock, the stopped coordinate mass is the unrestricted finite predicate
sum.  This is the form used to insert the literal `I₁` and `I₀`
coordinate products. -/
theorem tilingStoppedAcceptedGeometricMass_eq_predicateSum
    (tau : StepPath → ℕ) {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : List Direction) (P : TilingCappedCoordinates i cap → Prop)
    [DecidablePred P]
    (haccepted : ∀ q, P q →
      TilingStoppingAccepted tau t x r (fun j ↦ (q j : ℕ)) tail) :
    tilingStoppedAcceptedGeometricMass tau t x r cap tail P =
      ∑ q : TilingCappedCoordinates i cap,
        if P q then gapVectorMass (fun j ↦ (q j : ℕ)) else 0 := by
  classical
  rw [tilingStoppedAcceptedGeometricMass_eq_indicatorSum]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hP : P q
  · simp [hP, haccepted q hP]
  · simp [hP]

/-- A source fibre and its shell-zero replacement may be stopped at
different threshold ranks.  Their retained tiling word and boundary tail
are nevertheless identical, so their exact cylinder masses have the same
external factor.  This constructor reduces the path-level atom comparison
to the displayed finite coordinate-mass comparison; no probability
inequality is assumed. -/
noncomputable def stoppedFiberReplacementAtomProductCertificate
    {tauSource tauReplacement : StepPath → ℕ}
    (hsourceStopping : IsFiniteStoppingTime tauSource)
    (hreplacementStopping : IsFiniteStoppingTime tauReplacement)
    {i cap : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (tail : List Direction)
    (sourcePredicate replacementPredicate :
      TilingCappedCoordinates i cap → Prop)
    (q : ℝ) (hq : 0 ≤ q)
    (hcoordinate :
      tilingStoppedAcceptedGeometricMass tauSource t x r cap tail
          sourcePredicate ≤
        q * tilingStoppedAcceptedGeometricMass tauReplacement
          t x r cap tail replacementPredicate) :
    ReplacementAtomProductCertificate simpleRandomWalk
      (walkLift (tilingPreStoppingFiberEvent tauSource t x r cap tail
        sourcePredicate))
      (walkLift (tilingPreStoppingFiberEvent tauReplacement t x r cap tail
        replacementPredicate)) q where
  sourceProductMass :=
    tilingStoppedAcceptedGeometricMass tauSource t x r cap tail
      sourcePredicate
  replacementProductMass :=
    tilingStoppedAcceptedGeometricMass tauReplacement t x r cap tail
      replacementPredicate
  commonExternalFactor := prefixFiberConstant i tail
  source_eq := by
    rw [simpleRandomWalk_real_walkLift_tilingPreStoppingFiberEvent
      hsourceStopping]
    exact mul_comm _ _
  replacement_eq := by
    rw [simpleRandomWalk_real_walkLift_tilingPreStoppingFiberEvent
      hreplacementStopping]
    exact mul_comm _ _
  product_bound := hcoordinate
  q_nonneg := hq
  replacementProductMass_nonneg :=
    tilingStoppedAcceptedGeometricMass_nonneg tauReplacement t x r cap tail
      replacementPredicate
  commonExternalFactor_nonneg :=
    VariableStoppedProductDisintegration.prefixFiberConstant_nonneg i tail

/-! ## Countable families of exact stopped-fibre replacements -/

/-- All finite data for a countable family of two-clock stopped-fibre atom
comparisons.  Tiling words, caps, and both stopping clocks may depend on the
external trace label. -/
structure StoppedFiberReplacementAtomFamily
    (Index : Type*) (q : ℝ) where
  tiling : Index → DominoTiling
  retainedCount : Index → ℕ
  start : Index → Point
  retained : ∀ z, TilingRetainedWord (tiling z) (start z) (retainedCount z)
  cap : Index → ℕ
  tail : Index → List Direction
  sourceStoppingTime : Index → StepPath → ℕ
  replacementStoppingTime : Index → StepPath → ℕ
  sourceIsStoppingTime : ∀ z, IsFiniteStoppingTime (sourceStoppingTime z)
  replacementIsStoppingTime : ∀ z,
    IsFiniteStoppingTime (replacementStoppingTime z)
  sourcePredicate : ∀ z,
    TilingCappedCoordinates (retainedCount z) (cap z) → Prop
  replacementPredicate : ∀ z,
    TilingCappedCoordinates (retainedCount z) (cap z) → Prop
  q_nonneg : 0 ≤ q
  coordinate_bound : ∀ z,
    tilingStoppedAcceptedGeometricMass (sourceStoppingTime z)
        (tiling z) (start z) (retained z) (cap z) (tail z)
        (sourcePredicate z) ≤
      q * tilingStoppedAcceptedGeometricMass (replacementStoppingTime z)
        (tiling z) (start z) (retained z) (cap z) (tail z)
        (replacementPredicate z)

def StoppedFiberReplacementAtomFamily.sourceAtom
    {Index : Type*} {q : ℝ}
    (data : StoppedFiberReplacementAtomFamily Index q) (z : Index) :
    Set WalkPath :=
  walkLift (tilingPreStoppingFiberEvent (data.sourceStoppingTime z)
    (data.tiling z) (data.start z) (data.retained z) (data.cap z)
    (data.tail z) (data.sourcePredicate z))

def StoppedFiberReplacementAtomFamily.replacementAtom
    {Index : Type*} {q : ℝ}
    (data : StoppedFiberReplacementAtomFamily Index q) (z : Index) :
    Set WalkPath :=
  walkLift (tilingPreStoppingFiberEvent (data.replacementStoppingTime z)
    (data.tiling z) (data.start z) (data.retained z) (data.cap z)
    (data.tail z) (data.replacementPredicate z))

theorem StoppedFiberReplacementAtomFamily.measurable_replacementAtom
    {Index : Type*} {q : ℝ}
    (data : StoppedFiberReplacementAtomFamily Index q) (z : Index) :
    MeasurableSet (data.replacementAtom z) := by
  apply measurableSet_walkLift
  exact measurableSet_tilingPreStoppingFiberEvent
    (data.replacementIsStoppingTime z) (data.tiling z) (data.start z)
      (data.retained z) (data.cap z) (data.tail z)
      (data.replacementPredicate z)

theorem StoppedFiberReplacementAtomFamily.measurable_sourceAtom
    {Index : Type*} {q : ℝ}
    (data : StoppedFiberReplacementAtomFamily Index q) (z : Index) :
    MeasurableSet (data.sourceAtom z) := by
  apply measurableSet_walkLift
  exact measurableSet_tilingPreStoppingFiberEvent
    (data.sourceIsStoppingTime z) (data.tiling z) (data.start z)
      (data.retained z) (data.cap z) (data.tail z)
      (data.sourcePredicate z)

noncomputable def
    StoppedFiberReplacementAtomFamily.atomProductCertificate
    {Index : Type*} {q : ℝ}
    (data : StoppedFiberReplacementAtomFamily Index q) (z : Index) :
    ReplacementAtomProductCertificate simpleRandomWalk
      (data.sourceAtom z) (data.replacementAtom z) q :=
  stoppedFiberReplacementAtomProductCertificate
    (data.sourceIsStoppingTime z) (data.replacementIsStoppingTime z)
    (data.tiling z) (data.start z) (data.retained z) (data.tail z)
    (data.sourcePredicate z) (data.replacementPredicate z)
    q data.q_nonneg (data.coordinate_bound z)

/-- The countable stopped-fibre source is literally covered by its atoms,
and exact atom products plus the source-faithful threshold-jump mechanism
give the global shell-zero certificate. -/
noncomputable def globalStoppedFiberReplacementCertificate
    {Index : Type*} [Countable Index] (q : ℝ)
    (data : StoppedFiberReplacementAtomFamily Index q)
    (jump : ThresholdJumpReplacementFamily data.replacementAtom) :
    GlobalDisjointReplacementCertificate
      (Index := Index) simpleRandomWalk
      (⋃ z, data.sourceAtom z) (ENNReal.ofReal q) :=
  globalDisjointReplacementCertificateOfAtomProductsAndThresholdJump
    simpleRandomWalk (⋃ z, data.sourceAtom z) data.sourceAtom
      data.replacementAtom q (by exact Set.Subset.rfl)
      data.measurable_replacementAtom jump data.atomProductCertificate

/-- Version for a named path event once its deterministic stopped-trace
decomposition has been proved.  All remaining certificate fields are
derived from the exact stopped-fibre coordinate comparison and threshold
jump. -/
noncomputable def globalStoppedFiberReplacementCertificateOfSubset
    {Index : Type*} [Countable Index] (q : ℝ)
    (data : StoppedFiberReplacementAtomFamily Index q)
    (source : Set WalkPath)
    (hsource : source ⊆ ⋃ z, data.sourceAtom z)
    (jump : ThresholdJumpReplacementFamily data.replacementAtom) :
    GlobalDisjointReplacementCertificate
      (Index := Index) simpleRandomWalk source (ENNReal.ofReal q) :=
  globalDisjointReplacementCertificateOfAtomProductsAndThresholdJump
    simpleRandomWalk source data.sourceAtom data.replacementAtom q hsource
      data.measurable_replacementAtom jump data.atomProductCertificate

end

end Erdos1165.TilingTypedShellZeroReplacement

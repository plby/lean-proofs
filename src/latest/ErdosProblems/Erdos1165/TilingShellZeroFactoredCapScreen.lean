/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroLiteralScreen
import ErdosProblems.Erdos1165.TilingOrientedShellZeroSourcePartition
import ErdosProblems.Erdos1165.TilingPrefixedStoppedProductDisintegration
import ErdosProblems.Erdos1165.HLOZShellZeroExternalWindow
import ErdosProblems.Erdos1165.HLOZLazyOverflowClosure
import ErdosProblems.Erdos1165.TilingPrefixedConditionalCappedMarginalization

/-!
# Cap-coherent factored shell-zero screens

The retained trace does not bound the deleted-excursion coordinates.  This
module therefore uses an increasing union of finite caps.  At every cap the
source and replacement clocks are allowed to differ, but their factorizations
have the same distinguished-coordinate marginal.  Both common-factor mass
identities and both full trace-atom equalities are derived below.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.TilingShellZeroFactoredCapScreen

open HLOZPathEvents HLOZProposition48Candidates
open HLOZShellZeroCentralCount HLOZShellZeroExactCountScreen
open HLOZShellZeroCentralTail
open HLOZShellZeroExternalWindow
open HLOZLazyOverflowClosure
open HLOZShellZeroReplacementWindows
open TilingCappedMarginalization TilingFavoriteTraceSupport
open LazyDecomposition TilingLazyDecomposition TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber TilingStoppedProductDisintegration
open TilingTypedShellZeroReplacement VariableStoppedFiber
open TilingVariableStoppedTracePartition VariableStoppedTracePartition
open TilingShellZeroLiteralScreen
open TilingOrientedShellZeroSourcePartition
open TilingPrefixedStoppedProductDisintegration
open TilingPrefixedConditionalCappedMarginalization
open FiniteDominoProductLaw HeterogeneousProductTail

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Canonical-support version of one exact oriented source atom.  Every
prefixed stopped cylinder is lifted through `walkLift`, hence lies in
`validStepWalk`; retaining this intersection avoids the impossible demand
that such cylinders cover arbitrary non-trajectory path functions. -/
def orientedValidShellZeroExactSourceTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total : ℕ)
    (z : OrientedTypedFavoriteTilingTraceCode t) : Set WalkPath :=
  orientedShellZeroExactSourceTraceAtom t o m k w low externalLow
    externalHigh total z ∩ validStepWalk

/-- Canonical-support version of the fixed-central replacement atom. -/
def orientedValidShellZeroReplacementTraceAtom
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh total central : ℕ)
    (z : OrientedTypedFavoriteTilingTraceCode t) : Set WalkPath :=
  orientedShellZeroReplacementTraceAtom t o m k w low externalLow
    externalHigh total central z ∩ validStepWalk

/-- The source event seen by literal stopped fibres.  Its simple-random-walk
mass is exactly that of the unqualified source event because the omitted
complement of `validStepWalk` is null. -/
def orientedValidShellZeroSourceEvent
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh cut : ℕ) : Set WalkPath :=
  orientedShellZeroSourceEvent t o m k w low externalLow externalHigh cut ∩
    validStepWalk

theorem simpleRandomWalk_orientedValidShellZeroSourceEvent
    (t : DominoTiling) (o : Orientation)
    (m k w low externalLow externalHigh cut : ℕ) :
    simpleRandomWalk
        (orientedValidShellZeroSourceEvent t o m k w low externalLow
          externalHigh cut) =
      simpleRandomWalk
        (orientedShellZeroSourceEvent t o m k w low externalLow
          externalHigh cut) := by
  apply le_antisymm
  · exact measure_mono inter_subset_left
  · calc
      simpleRandomWalk
          (orientedShellZeroSourceEvent t o m k w low externalLow
            externalHigh cut) ≤
          simpleRandomWalk
            ((orientedShellZeroSourceEvent t o m k w low externalLow
                externalHigh cut ∩ validStepWalk) ∪ validStepWalkᶜ) := by
        apply measure_mono
        intro s hs
        by_cases hv : s ∈ validStepWalk
        · exact Or.inl ⟨hs, hv⟩
        · exact Or.inr hv
      _ ≤ simpleRandomWalk
            (orientedShellZeroSourceEvent t o m k w low externalLow
              externalHigh cut ∩ validStepWalk) +
            simpleRandomWalk validStepWalkᶜ := measure_union_le _ _
      _ = simpleRandomWalk
          (orientedValidShellZeroSourceEvent t o m k w low externalLow
            externalHigh cut) := by
        rw [simpleRandomWalk_validStepWalk_compl, add_zero]
        rfl

private lemma ite_eq_ite_of_iff {α : Type*} {p q : Prop}
    [Decidable p] [Decidable q] {a b c d : α} (hpq : p ↔ q)
    (hac : a = c) (hbd : b = d) :
    (if p then a else b) = if q then c else d := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (hpq.mp hp), hac]
  · rw [if_neg hp, if_neg (fun hq ↦ hp (hpq.mpr hq)), hbd]

/-- Retained trace codes that actually occur on one exact source slice.
Invalid raw external words, and exact counts whose slice is empty, carry no
stopped-coordinate obligation. -/
abbrev LiteralShellZeroSupportedTraceIndex
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ) :=
  {z : OrientedTypedFavoriteTilingTraceCode t //
    (orientedValidShellZeroExactSourceTraceAtom t o m k (shellWidth48 m) low
      externalLow externalHigh total z).Nonempty}

/-- Every coordinate lies in the source window. -/
def allSourceVector
    {Coordinate : Type*} [Fintype Coordinate]
    {State : Coordinate → Type*}
    (source : ∀ c, State c → Prop) (ell : ∀ c, State c) : Prop :=
  ∀ c, source c (ell c)

/-- A literal exact-`central` mixture: the subset `A` records precisely the
coordinates left in the source window; its complement is moved to the
replacement window. -/
def exactSourceSubsetVector
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop) (central : ℕ)
    (ell : ∀ c, State c) : Prop :=
  ∃ A ∈ (Finset.univ : Finset Coordinate).powersetCard central,
    ∀ c, (c ∈ A → source c (ell c)) ∧
      (c ∉ A → replacement c (ell c))

noncomputable instance instDecidablePredAllSourceVector
    {Coordinate : Type*} [Fintype Coordinate]
    {State : Coordinate → Type*}
    (source : ∀ c, State c → Prop) : DecidablePred (allSourceVector source) :=
  Classical.decPred _

noncomputable instance instDecidablePredExactSourceSubsetVector
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop) (central : ℕ) :
    DecidablePred (exactSourceSubsetVector source replacement central) :=
  Classical.decPred _

lemma sum_allSourceVector_eq_product
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*} [∀ c, Fintype (State c)]
    (weight : ∀ c, State c → ℝ)
    (source : ∀ c, State c → Prop) [∀ c, DecidablePred (source c)] :
    (∑ ell : ∀ c, State c,
        if allSourceVector source ell then productPointMass weight ell else 0) =
      allUpperProductMass
        (fun c ↦ ∑ v, if source c v then weight c v else 0) := by
  classical
  unfold allUpperProductMass
  calc
    (∑ ell : ∀ c, State c,
        if allSourceVector source ell then productPointMass weight ell else 0) =
        ∑ ell : ∀ c, State c,
          ∏ c, if source c (ell c) then weight c (ell c) else 0 := by
      apply Finset.sum_congr rfl
      intro ell _
      unfold productPointMass
      by_cases h : allSourceVector source ell
      · rw [if_pos h]
        apply Finset.prod_congr rfl
        intro c _
        simp [(h c)]
      · rw [if_neg h]
        have h' : ¬∀ c, source c (ell c) := h
        obtain ⟨c, hc⟩ := not_forall.mp h'
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ c)
        simp [hc]
    _ = ∏ c, ∑ v, if source c v then weight c v else 0 :=
      (Fintype.prod_sum
        (fun c v ↦ if source c v then weight c v else 0)).symm

private lemma exactSourceSubsetVector_unique
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*}
    (source replacement : ∀ c, State c → Prop)
    (hdisjoint : ∀ c v, ¬(source c v ∧ replacement c v))
    (ell : ∀ c, State c) {A B : Finset Coordinate}
    (hA : ∀ c, (c ∈ A → source c (ell c)) ∧
      (c ∉ A → replacement c (ell c)))
    (hB : ∀ c, (c ∈ B → source c (ell c)) ∧
      (c ∉ B → replacement c (ell c))) : A = B := by
  ext c
  constructor
  · intro hcA
    by_contra hcB
    exact hdisjoint c (ell c) ⟨(hA c).1 hcA, (hB c).2 hcB⟩
  · intro hcB
    by_contra hcA
    exact hdisjoint c (ell c) ⟨(hB c).1 hcB, (hA c).2 hcA⟩

private lemma sum_fixedSourceSubsetVector_eq_mixedSubsetProductMass
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*} [∀ c, Fintype (State c)]
    (weight : ∀ c, State c → ℝ)
    (source replacement : ∀ c, State c → Prop)
    [∀ c, DecidablePred (source c)] [∀ c, DecidablePred (replacement c)]
    (A : Finset Coordinate) :
    (∑ ell : ∀ c, State c,
        if (∀ c, (c ∈ A → source c (ell c)) ∧
            (c ∉ A → replacement c (ell c))) then
          productPointMass weight ell else 0) =
      mixedSubsetProductMass
        (fun c ↦ ∑ v, if source c v then weight c v else 0)
        (fun c ↦ ∑ v, if replacement c v then weight c v else 0) A := by
  classical
  calc
    (∑ ell : ∀ c, State c,
        if (∀ c, (c ∈ A → source c (ell c)) ∧
            (c ∉ A → replacement c (ell c))) then
          productPointMass weight ell else 0) =
        ∑ ell : ∀ c, State c,
          ∏ c, if c ∈ A then
            (if source c (ell c) then weight c (ell c) else 0)
          else (if replacement c (ell c) then weight c (ell c) else 0) := by
      apply Finset.sum_congr rfl
      intro ell _
      by_cases h : ∀ c, (c ∈ A → source c (ell c)) ∧
          (c ∉ A → replacement c (ell c))
      · rw [if_pos h]
        unfold productPointMass
        apply Finset.prod_congr rfl
        intro c _
        by_cases hc : c ∈ A
        · simp [hc, (h c).1 hc]
        · simp [hc, (h c).2 hc]
      · rw [if_neg h]
        obtain ⟨c, hc⟩ := not_forall.mp h
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ c)
        by_cases hcA : c ∈ A
        · have hnsource : ¬ source c (ell c) := by
            intro hsource
            exact hc ⟨fun _ ↦ hsource, fun hnot ↦ (hnot hcA).elim⟩
          simp [hcA, hnsource]
        · have hnreplacement : ¬ replacement c (ell c) := by
            intro hreplacement
            exact hc ⟨fun hmem ↦ (hcA hmem).elim, fun _ ↦ hreplacement⟩
          simp [hcA, hnreplacement]
    _ = ∏ c, ∑ v, if c ∈ A then
          (if source c v then weight c v else 0)
        else (if replacement c v then weight c v else 0) :=
      (Fintype.prod_sum (fun c v ↦ if c ∈ A then
        (if source c v then weight c v else 0)
      else (if replacement c v then weight c v else 0))).symm
    _ = mixedSubsetProductMass
        (fun c ↦ ∑ v, if source c v then weight c v else 0)
        (fun c ↦ ∑ v, if replacement c v then weight c v else 0) A := by
      unfold mixedSubsetProductMass
      rw [← Finset.prod_compl_mul_prod A]
      rw [mul_comm]
      congr 1
      · apply Finset.prod_congr rfl
        intro c hc
        simp [hc]
      · apply Finset.prod_congr rfl
        intro c hc
        simp only [Finset.mem_compl] at hc
        simp [hc]

lemma sum_exactSourceSubsetVector_eq_exactUpperCountProductMass
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {State : Coordinate → Type*} [∀ c, Fintype (State c)]
    (weight : ∀ c, State c → ℝ)
    (source replacement : ∀ c, State c → Prop)
    [∀ c, DecidablePred (source c)] [∀ c, DecidablePred (replacement c)]
    (hdisjoint : ∀ c v, ¬(source c v ∧ replacement c v))
    (central : ℕ) :
    (∑ ell : ∀ c, State c,
        if exactSourceSubsetVector source replacement central ell then
          productPointMass weight ell else 0) =
      exactUpperCountProductMass
        (fun c ↦ ∑ v, if source c v then weight c v else 0)
        (fun c ↦ ∑ v, if replacement c v then weight c v else 0)
        central := by
  classical
  unfold exactUpperCountProductMass
  let P := (Finset.univ : Finset Coordinate).powersetCard central
  calc
    (∑ ell : ∀ c, State c,
        if exactSourceSubsetVector source replacement central ell then
          productPointMass weight ell else 0) =
        ∑ ell : ∀ c, State c, ∑ A ∈ P,
          if (∀ c, (c ∈ A → source c (ell c)) ∧
              (c ∉ A → replacement c (ell c))) then
            productPointMass weight ell else 0 := by
      apply Finset.sum_congr rfl
      intro ell _
      by_cases h : exactSourceSubsetVector source replacement central ell
      · rcases h with ⟨A, hAcard, hA⟩
        rw [if_pos ⟨A, hAcard, hA⟩]
        rw [Finset.sum_eq_single A]
        · rw [if_pos hA]
        · intro B hB hBA
          by_cases hBpred : ∀ c, (c ∈ B → source c (ell c)) ∧
              (c ∉ B → replacement c (ell c))
          · exact (hBA (exactSourceSubsetVector_unique source replacement
              hdisjoint ell hBpred hA)).elim
          · simp [hBpred]
        · exact fun hnot ↦ (hnot hAcard).elim
      · rw [if_neg h]
        symm
        apply Finset.sum_eq_zero
        intro A hAcard
        have hApred : ¬ ∀ c, (c ∈ A → source c (ell c)) ∧
            (c ∉ A → replacement c (ell c)) := by
          intro hA
          exact h ⟨A, by simpa [P] using hAcard, hA⟩
        simp [hApred]
    _ = ∑ A ∈ P, ∑ ell : ∀ c, State c,
          if (∀ c, (c ∈ A → source c (ell c)) ∧
              (c ∉ A → replacement c (ell c))) then
            productPointMass weight ell else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ A ∈ P,
        mixedSubsetProductMass
          (fun c ↦ ∑ v, if source c v then weight c v else 0)
          (fun c ↦ ∑ v, if replacement c v then weight c v else 0) A := by
      apply Finset.sum_congr rfl
      intro A _
      exact sum_fixedSourceSubsetVector_eq_mixedSubsetProductMass
        weight source replacement A

/-- The two-clock, cap-coherent typed product screen for one exact source
count and one retained external trace.  It asks for literal finite
factorizations and cap coverage, but no atom equality and no probability or
mass inequality. -/
structure LiteralShellZeroFactoredCapData
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (z : OrientedTypedFavoriteTilingTraceCode t) where
  retainedCount : ℕ → ℕ
  /-- The actual coordinate cutoff used at one logical stage.  This may
  start above zero; the logical stage remains `ℕ`, so a trace-dependent
  cofinal tail of cutoffs is representable without impossible small caps. -/
  coordinateCap : ℕ → ℕ
  capStart : ℕ
  coordinateCap_eq : ∀ cap, coordinateCap cap = capStart + cap
  start : ℕ → Point
  retained : ∀ cap, TilingRetainedWord t (start cap) (retainedCount cap)
  /-- Physical prefix preceding the orientation-normalized retained chain. -/
  initial : ℕ → List Direction
  tail : ℕ → List Direction
  sourceStoppingTime : ℕ → StepPath → ℕ
  replacementStoppingTime : ℕ → StepPath → ℕ
  sourceIsStoppingTime : ∀ cap, IsFiniteStoppingTime (sourceStoppingTime cap)
  replacementIsStoppingTime : ∀ cap,
    IsFiniteStoppingTime (replacementStoppingTime cap)
  sourcePredicate : ∀ cap,
    TilingCappedCoordinates (retainedCount cap) (coordinateCap cap) → Prop
  replacementPredicate : ∀ cap,
    TilingCappedCoordinates (retainedCount cap) (coordinateCap cap) → Prop
  distinguished : ℕ → Finset Point
  selected : ∀ cap, TilingDistinguishedCoordinates (cap := coordinateCap cap)
    t (start cap) (retained cap) (distinguished cap) → Prop
  upper : ∀ cap, TilingCappedMarginalization.TilingAwayDomino
    t (start cap) (retained cap)
    (distinguished cap) → ℕ
  upper_pos : ∀ cap b, 0 < upper cap b
  windows : ∀ cap, TilingShellZeroCoordinateWindowData
    (cap := coordinateCap cap) (m := m) (total := total)
      t (start cap) (retained cap)
      (distinguished cap) (upper cap)
  source_factorization : ∀ cap q,
    sourcePredicate cap q ∧ PrefixedTilingStoppingAccepted
        (sourceStoppingTime cap) (initial cap) t (start cap) (retained cap)
          (fun j ↦ (q j : ℕ)) (tail cap) ↔
      selected cap ((splitTilingCoordinatesEquiv t (start cap)
        (retained cap) (distinguished cap) q).1) ∧
      TilingAwayTotalsScreen t (start cap) (retained cap)
        (distinguished cap) (upper cap)
        (allSourceVector fun b v ↦ tilingShellZeroSourceCoordinate
          (cap := coordinateCap cap) (m := m) (w := shellWidth48 m)
          t (start cap) (retained cap) (distinguished cap) (upper cap) b v)
        ((splitTilingCoordinatesEquiv t (start cap) (retained cap)
          (distinguished cap) q).2)
  replacement_factorization : ∀ cap q,
    replacementPredicate cap q ∧
        PrefixedTilingStoppingAccepted (replacementStoppingTime cap)
          (initial cap) t (start cap) (retained cap)
            (fun j ↦ (q j : ℕ)) (tail cap) ↔
      selected cap ((splitTilingCoordinatesEquiv t (start cap)
        (retained cap) (distinguished cap) q).1) ∧
      TilingAwayTotalsScreen t (start cap) (retained cap)
        (distinguished cap) (upper cap)
        (exactSourceSubsetVector
          (fun b v ↦ tilingShellZeroSourceCoordinate
            (cap := coordinateCap cap) (m := m) (w := shellWidth48 m)
            t (start cap) (retained cap) (distinguished cap) (upper cap) b v)
          (fun b v ↦ tilingShellZeroReplacementCoordinate
            (cap := coordinateCap cap) (m := m) (w := shellWidth48 m)
            t (start cap) (retained cap) (distinguished cap) (upper cap) b v)
          (centralReplacementUpperCount shellZeroLocalRatioConstant total))
        ((splitTilingCoordinatesEquiv t (start cap) (retained cap)
          (distinguished cap) q).2)
  source_subset : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (sourceStoppingTime cap)
      (initial cap) t (start cap) (retained cap) (coordinateCap cap) (tail cap)
        (sourcePredicate cap)) ⊆
      orientedValidShellZeroExactSourceTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total z
  replacement_subset : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (replacementStoppingTime cap)
      (initial cap) t (start cap) (retained cap) (coordinateCap cap) (tail cap)
        (replacementPredicate cap)) ⊆
      orientedValidShellZeroReplacementTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total
          (centralReplacementUpperCount shellZeroLocalRatioConstant total) z
  source_covered :
    orientedValidShellZeroExactSourceTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total z ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (sourceStoppingTime cap) (initial cap) t (start cap) (retained cap)
          (coordinateCap cap) (tail cap)
          (sourcePredicate cap))
  replacement_covered :
    orientedValidShellZeroReplacementTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total
          (centralReplacementUpperCount shellZeroLocalRatioConstant total) z ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (replacementStoppingTime cap) (initial cap) t (start cap) (retained cap)
          (coordinateCap cap)
          (tail cap) (replacementPredicate cap))
  source_monotone : Monotone fun cap ↦
    walkLift (prefixedTilingPreStoppingFiberEvent (sourceStoppingTime cap)
      (initial cap) t (start cap) (retained cap) (coordinateCap cap) (tail cap)
        (sourcePredicate cap))

/-- Cofinal geometric data on one finite coordinate cap.  Unlike
`TilingShellZeroCoordinateWindowData`, this record contains no large-`m`
arithmetic: it records only the exact support cardinality, membership of
each retained base count in the chosen external interval, and the finite
upper/cap bounds.  The three numerical window inequalities are supplied
later, at the analytic use site. -/
structure LiteralShellZeroCoordinateSupportData
    {i cap m externalLow externalHigh total : ℕ}
    (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingCappedMarginalization.TilingAwayDomino
      t x r D → ℕ) where
  card : Fintype.card
      (TilingCappedMarginalization.TilingAwayDomino t x r D) = total
  externalWindow : ∀ b : TilingCappedMarginalization.TilingAwayDomino
      t x r D,
    externalLow ≤ Fintype.card (TilingCoordinatesAt t x r b.1) ∧
      Fintype.card (TilingCoordinatesAt t x r b.1) < externalHigh
  sourceUpper : ∀ (b : TilingCappedMarginalization.TilingAwayDomino
      t x r D) (v : ℕ),
    v ∈ shellZeroSourceFailureWindow m (shellWidth48 m)
        (Fintype.card (TilingCoordinatesAt t x r b.1)) →
      v < upper b
  replacementUpper : ∀ (b : TilingCappedMarginalization.TilingAwayDomino
      t x r D) (v : ℕ),
    v ∈ shellZeroReplacementFailureWindow m (shellWidth48 m)
        (Fintype.card (TilingCoordinatesAt t x r b.1)) →
      v < upper b
  sourceCap : ∀ (b : TilingCappedMarginalization.TilingAwayDomino
      t x r D) (v : ℕ),
    v ∈ shellZeroSourceFailureWindow m (shellWidth48 m)
        (Fintype.card (TilingCoordinatesAt t x r b.1)) →
      v ≤ cap
  replacementCap : ∀ (b : TilingCappedMarginalization.TilingAwayDomino
      t x r D) (v : ℕ),
    v ∈ shellZeroReplacementFailureWindow m (shellWidth48 m)
        (Fintype.card (TilingCoordinatesAt t x r b.1)) →
      v ≤ cap

/-- Add the eventual scalar external-window arithmetic to the literal
geometric data.  This is the unique conversion point at which the
large-`m` retained-count estimates enter a stopped fibre. -/
theorem LiteralShellZeroCoordinateSupportData.toWindowData
    {i cap m externalLow externalHigh total : ℕ}
    {t : DominoTiling} {x : Point}
    {r : TilingRetainedWord t x i} {D : Finset Point}
    {upper : TilingCappedMarginalization.TilingAwayDomino
      t x r D → ℕ}
    (data : LiteralShellZeroCoordinateSupportData
      (cap := cap) (m := m) (externalLow := externalLow)
      (externalHigh := externalHigh) (total := total) t x r D upper)
    (harithmetic : ShellZeroExternalWindowArithmeticAt m externalLow
      externalHigh) :
    TilingShellZeroCoordinateWindowData (cap := cap) (m := m)
      (total := total) t x r D upper where
  card := data.card
  thick := fun b ↦
    (harithmetic _ (data.externalWindow b).1
      (data.externalWindow b).2).1
  translate := fun b ↦
    (harithmetic _ (data.externalWindow b).1
      (data.externalWindow b).2).2.1
  center := fun b ↦
    (harithmetic _ (data.externalWindow b).1
      (data.externalWindow b).2).2.2
  sourceUpper := data.sourceUpper
  replacementUpper := data.replacementUpper
  sourceCap := data.sourceCap
  replacementCap := data.replacementCap

/-- Primitive stopped-coordinate input for the shell-zero comparison.  The
two factorization fields are the literal screened identities at their two
different creation clocks.  There is deliberately no unscreened replacement
base: raised-rank acceptance depends on the number of coordinates moved into
`I₀`, so such a base would not be invariant under the away vector.  The two
screened identities nevertheless have exactly the same distinguished
selector, which supplies the common factor used below.  This structure also
contains no eventual numerical window arithmetic. -/
structure LiteralShellZeroStoppedCoordinateSpec
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (z : OrientedTypedFavoriteTilingTraceCode t) where
  retainedCount : ℕ → ℕ
  /-- Actual cap at a logical cap-union stage.  Concrete stopped fibres use
  a trace-dependent increasing cofinal sequence (typically `capStart + n`),
  so no geometric window data is demanded below its first admissible cap. -/
  coordinateCap : ℕ → ℕ
  capStart : ℕ
  coordinateCap_eq : ∀ cap, coordinateCap cap = capStart + cap
  start : ℕ → Point
  retained : ∀ cap, TilingRetainedWord t (start cap) (retainedCount cap)
  /-- Physical prefix preceding the orientation-normalized retained chain. -/
  initial : ℕ → List Direction
  tail : ℕ → List Direction
  sourceStoppingTime : ℕ → StepPath → ℕ
  replacementStoppingTime : ℕ → StepPath → ℕ
  sourceIsStoppingTime : ∀ cap, IsFiniteStoppingTime (sourceStoppingTime cap)
  replacementIsStoppingTime : ∀ cap,
    IsFiniteStoppingTime (replacementStoppingTime cap)
  sourcePredicate : ∀ cap,
    TilingCappedCoordinates (retainedCount cap) (coordinateCap cap) → Prop
  replacementPredicate : ∀ cap,
    TilingCappedCoordinates (retainedCount cap) (coordinateCap cap) → Prop
  distinguished : ℕ → Finset Point
  selected : ∀ cap, TilingDistinguishedCoordinates (cap := coordinateCap cap)
    t (start cap) (retained cap) (distinguished cap) → Prop
  upper : ∀ cap, TilingCappedMarginalization.TilingAwayDomino
    t (start cap) (retained cap) (distinguished cap) → ℕ
  upper_pos : ∀ cap b, 0 < upper cap b
  coordinateSupport : ∀ cap, LiteralShellZeroCoordinateSupportData
    (cap := coordinateCap cap) (m := m) (externalLow := externalLow)
      (externalHigh := externalHigh) (total := total)
      t (start cap) (retained cap) (distinguished cap) (upper cap)
  source_factorization : ∀ cap q,
    sourcePredicate cap q ∧ PrefixedTilingStoppingAccepted
        (sourceStoppingTime cap) (initial cap) t (start cap) (retained cap)
          (fun j ↦ (q j : ℕ)) (tail cap) ↔
      selected cap ((splitTilingCoordinatesEquiv t (start cap)
        (retained cap) (distinguished cap) q).1) ∧
      TilingAwayTotalsScreen t (start cap) (retained cap)
        (distinguished cap) (upper cap)
        (allSourceVector fun b v ↦ tilingShellZeroSourceCoordinate
          (cap := coordinateCap cap) (m := m) (w := shellWidth48 m)
          t (start cap) (retained cap) (distinguished cap) (upper cap) b v)
        ((splitTilingCoordinatesEquiv t (start cap) (retained cap)
          (distinguished cap) q).2)
  replacement_factorization : ∀ cap q,
    replacementPredicate cap q ∧
        PrefixedTilingStoppingAccepted (replacementStoppingTime cap)
          (initial cap) t (start cap) (retained cap)
            (fun j ↦ (q j : ℕ)) (tail cap) ↔
      selected cap ((splitTilingCoordinatesEquiv t (start cap)
        (retained cap) (distinguished cap) q).1) ∧
      TilingAwayTotalsScreen t (start cap) (retained cap)
        (distinguished cap) (upper cap)
        (exactSourceSubsetVector
          (fun b v ↦ tilingShellZeroSourceCoordinate
            (cap := coordinateCap cap) (m := m) (w := shellWidth48 m)
            t (start cap) (retained cap) (distinguished cap) (upper cap) b v)
          (fun b v ↦ tilingShellZeroReplacementCoordinate
            (cap := coordinateCap cap) (m := m) (w := shellWidth48 m)
            t (start cap) (retained cap) (distinguished cap) (upper cap) b v)
          (centralReplacementUpperCount shellZeroLocalRatioConstant total))
        ((splitTilingCoordinatesEquiv t (start cap) (retained cap)
          (distinguished cap) q).2)
  source_sound : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (sourceStoppingTime cap)
      (initial cap) t (start cap) (retained cap) (coordinateCap cap) (tail cap)
        (sourcePredicate cap)) ⊆
      orientedValidShellZeroExactSourceTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total z
  replacement_sound : ∀ cap,
    walkLift (prefixedTilingPreStoppingFiberEvent (replacementStoppingTime cap)
      (initial cap) t (start cap) (retained cap) (coordinateCap cap) (tail cap)
        (replacementPredicate cap)) ⊆
      orientedValidShellZeroReplacementTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total
          (centralReplacementUpperCount shellZeroLocalRatioConstant total) z
  source_complete :
    orientedValidShellZeroExactSourceTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total z ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (sourceStoppingTime cap) (initial cap) t (start cap) (retained cap)
          (coordinateCap cap) (tail cap)
          (sourcePredicate cap))
  replacement_complete :
    orientedValidShellZeroReplacementTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total
          (centralReplacementUpperCount shellZeroLocalRatioConstant total) z ⊆
      ⋃ cap, walkLift (prefixedTilingPreStoppingFiberEvent
        (replacementStoppingTime cap) (initial cap) t (start cap) (retained cap)
          (coordinateCap cap)
          (tail cap)
          (replacementPredicate cap))
  source_monotone : Monotone fun cap ↦
    walkLift (prefixedTilingPreStoppingFiberEvent (sourceStoppingTime cap)
      (initial cap) t (start cap) (retained cap) (coordinateCap cap) (tail cap)
        (sourcePredicate cap))

/-- Build the cap product data from the literal stopped-coordinate spec.
The eventual external-window arithmetic is attached only here. -/
noncomputable def LiteralShellZeroStoppedCoordinateSpec.toFactoredCapData
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : OrientedTypedFavoriteTilingTraceCode t}
    (data : LiteralShellZeroStoppedCoordinateSpec t o m k low externalLow
      externalHigh total z)
    (hexternal : ShellZeroExternalWindowArithmeticAt m externalLow
      externalHigh) :
    LiteralShellZeroFactoredCapData t o m k low externalLow externalHigh
      total z where
  retainedCount := data.retainedCount
  coordinateCap := data.coordinateCap
  capStart := data.capStart
  coordinateCap_eq := data.coordinateCap_eq
  start := data.start
  retained := data.retained
  initial := data.initial
  tail := data.tail
  sourceStoppingTime := data.sourceStoppingTime
  replacementStoppingTime := data.replacementStoppingTime
  sourceIsStoppingTime := data.sourceIsStoppingTime
  replacementIsStoppingTime := data.replacementIsStoppingTime
  sourcePredicate := data.sourcePredicate
  replacementPredicate := data.replacementPredicate
  distinguished := data.distinguished
  selected := data.selected
  upper := data.upper
  upper_pos := data.upper_pos
  windows := fun cap ↦ (data.coordinateSupport cap).toWindowData hexternal
  source_factorization := data.source_factorization
  replacement_factorization := data.replacement_factorization
  source_subset := data.source_sound
  replacement_subset := data.replacement_sound
  source_covered := data.source_complete
  replacement_covered := data.replacement_complete
  source_monotone := data.source_monotone

/- The distinguished-coordinate contribution common to both clocks.  It is
the same term because the two literal screened factorizations use the same
physical prefix, retained word, distinguished set, and selector. -/
noncomputable def LiteralShellZeroFactoredCapData.distinguishedCommonMass
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : OrientedTypedFavoriteTilingTraceCode t}
    (data : LiteralShellZeroFactoredCapData t o m k low externalLow
      externalHigh total z) (cap : ℕ) : ℝ := by
  classical
  exact ∑ ell : TruncatedTotals (data.upper cap),
    distinguishedAwayMass
      (tilingAwayPointMass (cap := data.coordinateCap cap) t (data.start cap)
        (data.retained cap) (data.distinguished cap))
      (data.upper cap)
      (fun d ↦ if data.selected cap d then
        tilingDistinguishedAssignmentMass t (data.start cap)
          (data.retained cap) (data.distinguished cap) d else 0) ell

theorem LiteralShellZeroFactoredCapData.distinguishedCommonMass_nonneg
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : OrientedTypedFavoriteTilingTraceCode t}
    (data : LiteralShellZeroFactoredCapData t o m k low externalLow
      externalHigh total z) (cap : ℕ) :
    0 ≤ data.distinguishedCommonMass cap := by
  classical
  unfold LiteralShellZeroFactoredCapData.distinguishedCommonMass
    distinguishedAwayMass
  apply Finset.sum_nonneg
  intro ell _
  apply Finset.sum_nonneg
  intro d _
  apply mul_nonneg
  · unfold jointMass tilingAwayPointMass
    exact Finset.prod_nonneg fun b _ ↦
      tilingAwayExactTotalMass_nonneg t (data.start cap)
        (data.retained cap) (data.distinguished cap) b (ell b)
  · by_cases hd : data.selected cap d
    · simp only [hd, if_true]
      unfold tilingDistinguishedAssignmentMass
      exact Finset.prod_nonneg fun b _ ↦
        Finset.prod_nonneg fun j _ ↦
          PathInsertion.geometricGapMass_nonneg (d b j : ℕ)
    · simp [hd]

theorem LiteralShellZeroFactoredCapData.sourceMass_eq
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : OrientedTypedFavoriteTilingTraceCode t}
    (data : LiteralShellZeroFactoredCapData t o m k low externalLow
      externalHigh total z) (cap : ℕ) :
    prefixedTilingStoppedAcceptedGeometricMass (data.sourceStoppingTime cap)
        (data.initial cap) t (data.start cap) (data.retained cap)
          (data.coordinateCap cap)
          (data.tail cap)
          (data.sourcePredicate cap) =
      tilingShellZeroAllSourceProductMass (cap := data.coordinateCap cap) (m := m)
          t (data.start cap) (data.retained cap) (data.distinguished cap)
            (data.upper cap) *
        data.distinguishedCommonMass cap := by
  classical
  let source := fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
    t (data.start cap) (data.retained cap) (data.distinguished cap)
      (data.upper cap) b v
  rw [prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
    (data.sourceStoppingTime cap) (data.initial cap) t (data.start cap)
    (data.retained cap)
    (data.tail cap) (data.sourcePredicate cap)
    (data.distinguished cap) (data.selected cap) (data.upper cap)
    (allSourceVector source)
    (data.source_factorization cap)
    (tilingAwayPointMass_normalization_ne_zero_of_upper_pos
      t (data.start cap) (data.retained cap) (data.distinguished cap)
        (data.upper cap) (data.upper_pos cap))]
  unfold LiteralShellZeroFactoredCapData.distinguishedCommonMass
  congr 1
  rw [screenMass_eq_product]
  let weight := fun b (v : Fin (data.upper cap b)) ↦
    coordinateMass
      (tilingAwayPointMass (cap := data.coordinateCap cap) t (data.start cap)
        (data.retained cap) (data.distinguished cap))
      (data.upper cap) b (v : ℕ)
  change (∑ ell, if allSourceVector source ell then
      productPointMass weight ell else 0) = _
  rw [sum_allSourceVector_eq_product]
  unfold tilingShellZeroAllSourceProductMass
  congr 1
  funext b
  unfold tilingShellZeroSourceCoordinateMass
  apply Finset.sum_congr rfl
  intro v _
  exact ite_eq_ite_of_iff (by rfl) rfl rfl

theorem LiteralShellZeroFactoredCapData.replacementMass_eq
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : OrientedTypedFavoriteTilingTraceCode t}
    (data : LiteralShellZeroFactoredCapData t o m k low externalLow
      externalHigh total z) (cap : ℕ) :
    prefixedTilingStoppedAcceptedGeometricMass
        (data.replacementStoppingTime cap) (data.initial cap) t
          (data.start cap) (data.retained cap) (data.coordinateCap cap)
          (data.tail cap)
          (data.replacementPredicate cap) =
      tilingShellZeroCentralReplacementProductMass
        (cap := data.coordinateCap cap) (m := m)
          t (data.start cap) (data.retained cap) (data.distinguished cap)
            (data.upper cap)
              (centralReplacementUpperCount shellZeroLocalRatioConstant total) *
        data.distinguishedCommonMass cap := by
  classical
  let source := fun b v ↦ tilingShellZeroSourceCoordinate
    (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
    t (data.start cap) (data.retained cap) (data.distinguished cap)
      (data.upper cap) b v
  let replacement := fun b v ↦ tilingShellZeroReplacementCoordinate
    (cap := data.coordinateCap cap) (m := m) (w := shellWidth48 m)
    t (data.start cap) (data.retained cap) (data.distinguished cap)
      (data.upper cap) b v
  rw [prefixedTilingStoppedAcceptedGeometricMass_eq_screenMass_mul_distinguishedBase
    (data.replacementStoppingTime cap) (data.initial cap) t (data.start cap)
    (data.retained cap) (data.tail cap) (data.replacementPredicate cap)
    (data.distinguished cap)
    (data.selected cap) (data.upper cap)
    (exactSourceSubsetVector source replacement
      (centralReplacementUpperCount shellZeroLocalRatioConstant total))
    (data.replacement_factorization cap)
    (tilingAwayPointMass_normalization_ne_zero_of_upper_pos
      t (data.start cap) (data.retained cap) (data.distinguished cap)
        (data.upper cap) (data.upper_pos cap))]
  unfold LiteralShellZeroFactoredCapData.distinguishedCommonMass
  congr 1
  rw [screenMass_eq_product]
  let weight := fun b (v : Fin (data.upper cap b)) ↦
    coordinateMass
      (tilingAwayPointMass (cap := data.coordinateCap cap) t (data.start cap)
        (data.retained cap) (data.distinguished cap))
      (data.upper cap) b (v : ℕ)
  change (∑ ell, if exactSourceSubsetVector source replacement
      (centralReplacementUpperCount shellZeroLocalRatioConstant total) ell
      then productPointMass weight ell else 0) = _
  rw [sum_exactSourceSubsetVector_eq_exactUpperCountProductMass]
  · unfold tilingShellZeroCentralReplacementProductMass
    congr 1
    · funext b
      unfold tilingShellZeroSourceCoordinateMass
      apply Finset.sum_congr rfl
      intro v _
      exact ite_eq_ite_of_iff (by rfl) rfl rfl
    · funext b
      unfold tilingShellZeroReplacementCoordinateMass
      apply Finset.sum_congr rfl
      intro v _
      exact ite_eq_ite_of_iff (by rfl) rfl rfl
  · exact tilingShellZeroCoordinate_disjoint t (data.start cap)
      (data.retained cap) (data.distinguished cap) (data.upper cap)
        (data.windows cap).translate

theorem LiteralShellZeroFactoredCapData.coordinate_bound
    {t : DominoTiling} {o : Orientation}
    {m k low externalLow externalHigh total : ℕ}
    {z : OrientedTypedFavoriteTilingTraceCode t}
    (data : LiteralShellZeroFactoredCapData t o m k low externalLow
      externalHigh total z) (harithmetic : ShellZeroWindowArithmeticAt m)
    (cap : ℕ) :
    prefixedTilingStoppedAcceptedGeometricMass (data.sourceStoppingTime cap)
        (data.initial cap) t (data.start cap) (data.retained cap)
          (data.coordinateCap cap)
          (data.tail cap)
          (data.sourcePredicate cap) ≤
      centralReplacementRatio shellZeroLocalRatioConstant total *
        prefixedTilingStoppedAcceptedGeometricMass
          (data.replacementStoppingTime cap) (data.initial cap) t
            (data.start cap)
          (data.retained cap) (data.coordinateCap cap) (data.tail cap)
            (data.replacementPredicate cap) := by
  let common := data.distinguishedCommonMass cap
  have hproduct := tilingAllSourceProductMass_le_centralReplacement
    t (data.start cap) (data.retained cap) (data.distinguished cap)
      (data.upper cap) harithmetic (data.windows cap)
  have hcommon : 0 ≤ common := data.distinguishedCommonMass_nonneg cap
  rw [data.sourceMass_eq cap, data.replacementMass_eq cap]
  calc
    tilingShellZeroAllSourceProductMass (cap := data.coordinateCap cap) (m := m)
          t (data.start cap) (data.retained cap) (data.distinguished cap)
            (data.upper cap) * common ≤
        (centralReplacementRatio shellZeroLocalRatioConstant total *
          tilingShellZeroCentralReplacementProductMass
            (cap := data.coordinateCap cap) (m := m)
              t (data.start cap) (data.retained cap)
              (data.distinguished cap) (data.upper cap)
                (centralReplacementUpperCount
                  shellZeroLocalRatioConstant total)) * common :=
      mul_le_mul_of_nonneg_right hproduct hcommon
    _ = centralReplacementRatio shellZeroLocalRatioConstant total *
        (tilingShellZeroCentralReplacementProductMass
          (cap := data.coordinateCap cap) (m := m)
            t (data.start cap) (data.retained cap)
            (data.distinguished cap) (data.upper cap)
              (centralReplacementUpperCount shellZeroLocalRatioConstant total) *
          common) := by ring

/-- The finite-cap family at one exact source count. -/
noncomputable def literalShellZeroFactoredCapFamily
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (data : ∀ eta : LiteralShellZeroSupportedTraceIndex t o m k low
        externalLow externalHigh total,
      LiteralShellZeroFactoredCapData t o m k low externalLow externalHigh
        total eta.1)
    (harithmetic : ShellZeroWindowArithmeticAt m) :
    MonotoneCapStoppedFiberReplacementAtomFamily
      (LiteralShellZeroSupportedTraceIndex t o m k low externalLow
        externalHigh total)
      (centralReplacementRatio shellZeroLocalRatioConstant total) where
  sourceCap := fun cap eta ↦
    walkLift (prefixedTilingPreStoppingFiberEvent
      ((data eta).sourceStoppingTime cap) ((data eta).initial cap) t
      ((data eta).start cap) ((data eta).retained cap)
      ((data eta).coordinateCap cap) ((data eta).tail cap)
      ((data eta).sourcePredicate cap))
  replacementCap := fun cap eta ↦
    walkLift (prefixedTilingPreStoppingFiberEvent
      ((data eta).replacementStoppingTime cap) ((data eta).initial cap) t
      ((data eta).start cap) ((data eta).retained cap)
      ((data eta).coordinateCap cap) ((data eta).tail cap)
      ((data eta).replacementPredicate cap))
  measurable_replacementCap := fun cap eta ↦ by
    apply measurableSet_walkLift
    exact measurableSet_prefixedTilingPreStoppingFiberEvent
      ((data eta).replacementIsStoppingTime cap) ((data eta).initial cap) t
      ((data eta).start cap) ((data eta).retained cap)
      ((data eta).coordinateCap cap) ((data eta).tail cap)
      ((data eta).replacementPredicate cap)
  cap_le := fun cap eta ↦ by
    rw [simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
        ((data eta).sourceIsStoppingTime cap),
      simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
        ((data eta).replacementIsStoppingTime cap),
      ← ENNReal.ofReal_mul
        (centralReplacementRatio_nonneg
          shellZeroLocalRatioConstant_pos.le total)]
    apply ENNReal.ofReal_le_ofReal
    have hcommon : 0 ≤ prefixedPrefixFiberConstant
        ((data eta).initial cap) ((data eta).retainedCount cap)
          ((data eta).tail cap) :=
      prefixedPrefixFiberConstant_nonneg _ _ _
    calc
      prefixedPrefixFiberConstant ((data eta).initial cap)
            ((data eta).retainedCount cap) ((data eta).tail cap) *
          prefixedTilingStoppedAcceptedGeometricMass
            ((data eta).sourceStoppingTime cap) ((data eta).initial cap) t
            ((data eta).start cap) ((data eta).retained cap)
            ((data eta).coordinateCap cap) ((data eta).tail cap)
            ((data eta).sourcePredicate cap) ≤
        prefixedPrefixFiberConstant ((data eta).initial cap)
            ((data eta).retainedCount cap) ((data eta).tail cap) *
          (centralReplacementRatio shellZeroLocalRatioConstant total *
            prefixedTilingStoppedAcceptedGeometricMass
              ((data eta).replacementStoppingTime cap)
              ((data eta).initial cap) t ((data eta).start cap)
              ((data eta).retained cap) ((data eta).coordinateCap cap)
              ((data eta).tail cap) ((data eta).replacementPredicate cap)) :=
        mul_le_mul_of_nonneg_left
          ((data eta).coordinate_bound harithmetic cap) hcommon
      _ = centralReplacementRatio shellZeroLocalRatioConstant total *
          (prefixedPrefixFiberConstant ((data eta).initial cap)
              ((data eta).retainedCount cap) ((data eta).tail cap) *
            prefixedTilingStoppedAcceptedGeometricMass
              ((data eta).replacementStoppingTime cap)
              ((data eta).initial cap) t ((data eta).start cap)
              ((data eta).retained cap) ((data eta).coordinateCap cap)
              ((data eta).tail cap)
              ((data eta).replacementPredicate cap)) := by ring
  source_monotone := fun eta ↦ (data eta).source_monotone

theorem literalShellZeroFactoredCapFamily_sourceAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ eta : LiteralShellZeroSupportedTraceIndex t o m k low
        externalLow externalHigh total,
      LiteralShellZeroFactoredCapData t o m k low externalLow externalHigh
        total eta.1)
    (eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
      externalHigh total) :
    (literalShellZeroFactoredCapFamily t o m k low externalLow externalHigh
      total data harithmetic).sourceAtom eta =
      orientedValidShellZeroExactSourceTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total eta.1 := by
  apply Set.Subset.antisymm
  · intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
    exact (data eta).source_subset cap hcap
  · exact (data eta).source_covered

theorem literalShellZeroFactoredCapFamily_replacementAtom
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh total : ℕ)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ eta : LiteralShellZeroSupportedTraceIndex t o m k low
        externalLow externalHigh total,
      LiteralShellZeroFactoredCapData t o m k low externalLow externalHigh
        total eta.1)
    (eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
      externalHigh total) :
    (literalShellZeroFactoredCapFamily t o m k low externalLow externalHigh
      total data harithmetic).replacementAtom eta =
      orientedValidShellZeroReplacementTraceAtom t o m k (shellWidth48 m) low
        externalLow externalHigh total
          (centralReplacementUpperCount shellZeroLocalRatioConstant total)
            eta.1 := by
  apply Set.Subset.antisymm
  · intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨cap, hcap⟩
    exact (data eta).replacement_subset cap hcap
  · exact (data eta).replacement_covered

/-- The genuine cap-union exact-count shell-zero screen.  Atom equalities,
two-clock common factors, source coverage, and variable-clock disjointness
are all conclusions. -/
noncomputable def literalShellZeroExactCountFactoredCapScreen
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh shellScale : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ (n : ℕ),
      ∀ eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
        externalHigh (initialBudget48 shellScale + 1 + n),
      LiteralShellZeroFactoredCapData t o m k low externalLow externalHigh
        (initialBudget48 shellScale + 1 + n) eta.1) :
    LiteralShellZeroExactCountCapStoppedFiberScreen
      (orientedValidShellZeroSourceEvent t o m k (shellWidth48 m) low externalLow
        externalHigh (initialBudget48 shellScale)) shellScale where
  sourceRank := k
  Index := fun n ↦ LiteralShellZeroSupportedTraceIndex t o m k low
    externalLow externalHigh (initialBudget48 shellScale + 1 + n)
  indexCountable := fun _ ↦ inferInstance
  family := fun n ↦ literalShellZeroFactoredCapFamily t o m k low externalLow
    externalHigh (initialBudget48 shellScale + 1 + n) (data n) harithmetic
  source_subset := by
    intro s hs
    rcases hs with ⟨⟨hreach, hD, htheta, hcut⟩, hvalid⟩
    let total := (orientedTilingVTwoBases t o
      (shellZeroSourceTotalWindow m (shellWidth48 m)) s
        (creationTimeNat m k s)).card
    have htotal : initialBudget48 shellScale + 1 ≤ total := by
      dsimp only [total]
      omega
    let n := total - (initialBudget48 shellScale + 1)
    have htotalEq : initialBudget48 shellScale + 1 + n = total :=
      Nat.add_sub_of_le htotal
    have hsatom : s ∈ orientedValidShellZeroExactSourceTraceAtom t o m k
        (shellWidth48 m) low externalLow externalHigh
          (initialBudget48 shellScale + 1 + n)
          (orientedTypedCreationTraceCode t o m k (shellWidth48 m) s) := by
      refine ⟨⟨⟨hreach, hD, htheta, ?_⟩, rfl⟩, hvalid⟩
      change total = initialBudget48 shellScale + 1 + n
      exact htotalEq.symm
    let eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
        externalHigh (initialBudget48 shellScale + 1 + n) :=
      ⟨orientedTypedCreationTraceCode t o m k (shellWidth48 m) s,
        ⟨s, hsatom⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨n, Set.mem_iUnion.mpr ⟨eta, ?_⟩⟩
    rw [literalShellZeroFactoredCapFamily_sourceAtom t o m k low externalLow
      externalHigh _ harithmetic]
    exact hsatom
  disjoint_replacement := by
    intro n eta eta' hne
    rw [literalShellZeroFactoredCapFamily_replacementAtom
      t o m k low externalLow externalHigh
        (initialBudget48 shellScale + 1 + n) harithmetic (data n) eta,
      literalShellZeroFactoredCapFamily_replacementAtom
      t o m k low externalLow externalHigh
        (initialBudget48 shellScale + 1 + n) harithmetic (data n) eta']
    exact (pairwise_disjoint_of_variableClockThresholdJump
      (orientedShellZeroVariableClockJump t o m k (shellWidth48 m) low
        externalLow externalHigh (initialBudget48 shellScale + 1 + n)
        (centralReplacementUpperCount shellZeroLocalRatioConstant
          (initialBudget48 shellScale + 1 + n)) hm (by
            unfold replacementCreationRank replacementNewCount
            omega))
      (fun h ↦ hne (Subtype.ext h))).mono inter_subset_left
        inter_subset_left

theorem simpleRandomWalk_shellZeroSourceEvent_le_of_factoredCapData
    (t : DominoTiling) (o : Orientation)
    (m k low externalLow externalHigh shellScale : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : ∀ (n : ℕ),
      ∀ eta : LiteralShellZeroSupportedTraceIndex t o m k low externalLow
        externalHigh (initialBudget48 shellScale + 1 + n),
      LiteralShellZeroFactoredCapData t o m k low externalLow externalHigh
        (initialBudget48 shellScale + 1 + n) eta.1) :
    simpleRandomWalk
        (orientedShellZeroSourceEvent t o m k (shellWidth48 m) low externalLow
          externalHigh (initialBudget48 shellScale)) ≤
      centralReplacementTailCost shellZeroLocalRatioConstant
        (initialBudget48 shellScale) := by
  rw [← simpleRandomWalk_orientedValidShellZeroSourceEvent]
  exact (literalShellZeroExactCountFactoredCapScreen t o m k low externalLow
    externalHigh shellScale hm hk harithmetic data).measure_le

end

end Erdos1165.TilingShellZeroFactoredCapScreen

/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveProfileCodeAssembly

/-!
# Truncated recursive profile completions

A recursive profile word can be revealed only through a prescribed number
of child generations.  The revealed object records every retained inward
piece and final escape at those generations, while deeper child words remain
unrestricted.  A completion is literally a full recursive code whose
structural projection is the chosen revealed prefix.

This representation is deliberately fibre-based.  It gives genuine nested
events and exact stopped-word masses without identifying a completion with a
synthetic cylinder.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AnnularRecursiveProfilePrefixCompletion

open AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileCodeAssembly
open AnnularDecoratedProfileCode AnnularErasedParentSpineProfileRow
open AnnularOffspringKernelRadial AnnularProfileClocks MarkedBoundaryVisitKernel
open MarkedBridgeFactorization ThickPoint

noncomputable section

mutual
  /-- The part of one recursive gap code visible through `depth` child
  generations.  At depth zero nothing inside the gap has been fixed. -/
  def RecursiveProfileGapPrefixCode
      (n k : ℕ) (center : Point) :
      (depth : ℕ) → (tree : ProfileRefinementTree) →
        ProfileCycleMiddlePoint n k center →
        ProfileCycleOuterPoint n k center → Type
    | 0, _tree, _u, _w => Unit
    | _d + 1, .leaf, u, w =>
        RecursiveProfileGapCode n k center .leaf u w
    | d + 1, .node forest, u, w =>
        RecursiveProfileForestPrefixCode n k center (d + 1) forest u w

  /-- A forest prefix retains the chronological parent spine at every
  visible generation and recursively projects each child one generation
  less deeply. -/
  def RecursiveProfileForestPrefixCode
      (n k : ℕ) (center : Point) :
      (depth : ℕ) → (forest : ProfileRefinementForest) →
        ProfileCycleMiddlePoint n k center →
        ProfileCycleOuterPoint n k center → Type
    | 0, _forest, _u, _w => Unit
    | _d + 1, .nil, u, w =>
        RecursiveProfileForestCode n k center .nil u w
    | d + 1, .cons child tail, u, w =>
        Σ z : ProfileCycleInnerPoint n k center,
          Σ v : ProfileCycleMiddlePoint n k center,
            ProfileInwardWordCode n k center u z ×
              RecursiveProfileGapPrefixCode n (k + 1) center d child z v ×
                RecursiveProfileForestPrefixCode n k center (d + 1)
                  tail v w
end

mutual
  /-- Structural projection of a full recursive gap code to a retained
  prefix. -/
  def recursiveProfileGapPrefix
      (n k : ℕ) (center : Point) :
      ∀ (depth : ℕ) (tree : ProfileRefinementTree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        RecursiveProfileGapCode n k center tree u w →
          RecursiveProfileGapPrefixCode n k center depth tree u w
    | 0, _tree, _u, _w, _code => by
        simpa only [RecursiveProfileGapPrefixCode] using ()
    | _d + 1, .leaf, _u, _w, code => code
    | d + 1, .node forest, u, w, code =>
        recursiveProfileForestPrefix n k center (d + 1) forest u w code

  /-- Forest version of the structural prefix projection. -/
  def recursiveProfileForestPrefix
      (n k : ℕ) (center : Point) :
      ∀ (depth : ℕ) (forest : ProfileRefinementForest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        RecursiveProfileForestCode n k center forest u w →
          RecursiveProfileForestPrefixCode n k center depth forest u w
    | 0, _forest, _u, _w, _code => by
        simpa only [RecursiveProfileForestPrefixCode] using ()
    | _d + 1, .nil, _u, _w, code => code
    | d + 1, .cons child tail, _u, w, code =>
        ⟨code.1, code.2.1, code.2.2.1,
          recursiveProfileGapPrefix n (k + 1) center d child
            code.1 code.2.1 code.2.2.2.1,
          recursiveProfileForestPrefix n k center (d + 1) tail
            code.2.1 w code.2.2.2.2⟩
end

/-- Canonical empty retained prefix. -/
def recursiveProfileGapPrefixZero
    (n k : ℕ) (center : Point) (tree : ProfileRefinementTree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    RecursiveProfileGapPrefixCode n k center 0 tree u w := by
  simpa only [RecursiveProfileGapPrefixCode] using ()

@[simp] theorem recursiveProfileGapPrefix_zero
    (n k : ℕ) (center : Point) (tree : ProfileRefinementTree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (code : RecursiveProfileGapCode n k center tree u w) :
    recursiveProfileGapPrefix n k center 0 tree u w code =
      recursiveProfileGapPrefixZero n k center tree u w := by
  simp only [recursiveProfileGapPrefix, recursiveProfileGapPrefixZero]

/-- Full recursive codes completing a fixed retained gap prefix. -/
def RecursiveProfileGapCompletionCode
    (depth n k : ℕ) (center : Point)
    (tree : ProfileRefinementTree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (pfx : RecursiveProfileGapPrefixCode n k center depth tree u w) :=
  {code : RecursiveProfileGapCode n k center tree u w //
    recursiveProfileGapPrefix n k center depth tree u w code = pfx}

/-- Only prefixes actually attained by a full code are retained as indices.
This removes empty atoms while preserving a source-independent countable
code space. -/
def RecursiveProfileGapRetainedPrefixCode
    (depth n k : ℕ) (center : Point)
    (tree : ProfileRefinementTree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :=
  Set.range (recursiveProfileGapPrefix n k center depth tree u w)

/-- The attained retained-prefix code space is countable. -/
theorem recursiveProfileGapRetainedPrefixCodeCountable
    (depth n k : ℕ) (center : Point)
    (tree : ProfileRefinementTree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    Countable (RecursiveProfileGapRetainedPrefixCode depth n k center tree
      u w) := by
  letI : Countable (RecursiveProfileGapCode n k center tree u w) :=
    recursiveProfileGapCodeCountable n k center tree u w
  exact (Set.countable_range
    (recursiveProfileGapPrefix n k center depth tree u w)).to_subtype

/-- Completing the empty prefix is the same as choosing an arbitrary full
recursive code. -/
def recursiveProfileGapCompletionCodeZeroEquiv
    (n k : ℕ) (center : Point) (tree : ProfileRefinementTree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    RecursiveProfileGapCompletionCode 0 n k center tree u w
        (recursiveProfileGapPrefixZero n k center tree u w) ≃
      RecursiveProfileGapCode n k center tree u w where
  toFun := Subtype.val
  invFun := fun code ↦
    (Subtype.mk code
      (recursiveProfileGapPrefix_zero n k center tree u w code) :
      RecursiveProfileGapCompletionCode 0 n k center tree u w
        (recursiveProfileGapPrefixZero n k center tree u w))
  left_inv := fun code ↦ Subtype.ext rfl
  right_inv := fun _ ↦ rfl

/-- A completion fibre is countable because the full literal recursive code
is countable. -/
noncomputable def recursiveProfileGapCompletionCodeCountable
    (depth n k : ℕ) (center : Point)
    (tree : ProfileRefinementTree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (pfx : RecursiveProfileGapPrefixCode n k center depth tree u w) :
    Countable (RecursiveProfileGapCompletionCode depth n k center tree u w
      pfx) := by
  letI : Countable (RecursiveProfileGapCode n k center tree u w) :=
    recursiveProfileGapCodeCountable n k center tree u w
  exact Subtype.val_injective.countable

/-- Literal stopped event obtained by completing one retained recursive
prefix in every possible way. -/
def recursiveProfileGapCompletionEvent
    (depth n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
    (tree : ProfileRefinementTree)
    (hfit : profileRefinementTreeFits n k tree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (pfx : RecursiveProfileGapPrefixCode n k center depth tree u w) :
    Set StepPath :=
  stoppedWordEvent (fun code : RecursiveProfileGapCompletionCode depth n k
    center tree u w pfx ↦
      (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree hfit
        u w code.1).1)

/-- The completion fibre itself is a prefix-free stopped-event code. -/
def recursiveProfileGapCompletionStoppedEventCode
    (depth n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
    (tree : ProfileRefinementTree)
    (hfit : profileRefinementTreeFits n k tree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (pfx : RecursiveProfileGapPrefixCode n k center depth tree u w) :
    StoppedEventCode (recursiveProfileGapCompletionEvent depth n k center hn
      hk0 tree hfit u w pfx) where
  Code := RecursiveProfileGapCompletionCode depth n k center tree u w pfx
  countableCode := recursiveProfileGapCompletionCodeCountable depth n k center
    tree u w pfx
  word := fun code ↦
    (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree hfit
      u w code.1).1
  prefixFree_word := by
    apply prefixFree_of_boundaryFirst _
    · intro left right hword
      apply Subtype.ext
      apply recursiveProfileGapBoundaryExitWordCode_injective
        n k center hn hk0 tree hfit u w
      exact Subtype.ext hword
    · exact fun code ↦
        (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree hfit
          u w code.1).2.1
  event_eq := rfl

/-- Exact fair-walk mass of a genuine retained-prefix completion event. -/
theorem fairSteps_recursiveProfileGapCompletionEvent
    (depth n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
    (tree : ProfileRefinementTree)
    (hfit : profileRefinementTreeFits n k tree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (pfx : RecursiveProfileGapPrefixCode n k center depth tree u w) :
    fairSteps (recursiveProfileGapCompletionEvent depth n k center hn hk0
      tree hfit u w pfx) =
      ∑' code : RecursiveProfileGapCompletionCode depth n k center tree u w
        pfx, recursiveProfileGapCodeMass n k center tree u w code.1 := by
  rw [(recursiveProfileGapCompletionStoppedEventCode depth n k center hn hk0
    tree hfit u w pfx).mass_eq]
  change (∑' code : RecursiveProfileGapCompletionCode depth n k center tree
    u w pfx, stoppedWordMass
      (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree hfit
        u w code.1).1) = _
  apply tsum_congr
  intro code
  rw [recursiveProfileGapBoundaryExitWordCode_val]
  exact stoppedWordMass_recursiveProfileGapList n k center tree u w code.1

/-- Completion event indexed by an attained retained prefix. -/
def recursiveProfileGapRetainedAtom
    (depth n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
    (tree : ProfileRefinementTree)
    (hfit : profileRefinementTreeFits n k tree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (r : RecursiveProfileGapRetainedPrefixCode depth n k center tree u w) :
    Set StepPath :=
  recursiveProfileGapCompletionEvent depth n k center hn hk0 tree hfit u w r.1

/-- Every retained-prefix atom is measurable. -/
theorem measurableSet_recursiveProfileGapRetainedAtom
    (depth n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
    (tree : ProfileRefinementTree)
    (hfit : profileRefinementTreeFits n k tree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (r : RecursiveProfileGapRetainedPrefixCode depth n k center tree u w) :
    MeasurableSet (recursiveProfileGapRetainedAtom depth n k center hn hk0
      tree hfit u w r) := by
  letI : Countable (RecursiveProfileGapCompletionCode depth n k center tree u
      w r.1) := recursiveProfileGapCompletionCodeCountable depth n k center
        tree u w r.1
  exact measurableSet_stoppedWordEvent _

/-- Distinct retained prefixes give disjoint genuine completion events. -/
theorem recursiveProfileGapRetainedAtom_pairwise
    (depth n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
    (tree : ProfileRefinementTree)
    (hfit : profileRefinementTreeFits n k tree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    Pairwise fun r s : RecursiveProfileGapRetainedPrefixCode depth n k center
        tree u w ↦
      Disjoint (recursiveProfileGapRetainedAtom depth n k center hn hk0 tree
        hfit u w r)
        (recursiveProfileGapRetainedAtom depth n k center hn hk0 tree hfit u
          w s) := by
  intro r s hrs
  rw [Set.disjoint_left]
  intro omega hr hs
  simp only [recursiveProfileGapRetainedAtom,
    recursiveProfileGapCompletionEvent, stoppedWordEvent, Set.mem_iUnion]
    at hr hs
  obtain ⟨cr, hcr⟩ := hr
  obtain ⟨cs, hcs⟩ := hs
  have hcode : cr.1 ≠ cs.1 := by
    intro h
    apply hrs
    apply Subtype.ext
    rw [← cr.2, ← cs.2, h]
  have hfreeFull := (recursiveProfileGapStoppedEventCode n k center hn hk0 tree
    hfit u w).prefixFree_word
  have hfree := hfreeFull hcode
  exact Set.disjoint_left.mp hfree hcr hcs

/-- The retained-prefix atoms partition the complete recursive gap event. -/
theorem iUnion_recursiveProfileGapRetainedAtom
    (depth n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
    (tree : ProfileRefinementTree)
    (hfit : profileRefinementTreeFits n k tree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    (⋃ r : RecursiveProfileGapRetainedPrefixCode depth n k center tree u w,
      recursiveProfileGapRetainedAtom depth n k center hn hk0 tree hfit u w
        r) =
      stoppedWordEvent (fun code : RecursiveProfileGapCode n k center tree u w
        ↦ (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree
          hfit u w code).1) := by
  ext omega
  constructor
  · intro homega
    simp only [Set.mem_iUnion] at homega
    obtain ⟨r, hr⟩ := homega
    simp only [recursiveProfileGapRetainedAtom,
      recursiveProfileGapCompletionEvent, stoppedWordEvent,
      Set.mem_iUnion] at hr ⊢
    obtain ⟨code, hcode⟩ := hr
    exact ⟨code.1, hcode⟩
  · intro homega
    simp only [stoppedWordEvent, Set.mem_iUnion] at homega
    obtain ⟨code, hcode⟩ := homega
    let r : RecursiveProfileGapRetainedPrefixCode depth n k center tree u w :=
      ⟨recursiveProfileGapPrefix n k center depth tree u w code,
        ⟨code, rfl⟩⟩
    refine Set.mem_iUnion.2 ⟨r, ?_⟩
    simp only [recursiveProfileGapRetainedAtom,
      recursiveProfileGapCompletionEvent, stoppedWordEvent,
      Set.mem_iUnion]
    let completion : RecursiveProfileGapCompletionCode depth n k center tree u
        w r.1 := ⟨code, rfl⟩
    refine ⟨completion, ?_⟩
    simpa only [completion] using hcode

/-- At depth zero the unique retained prefix has the complete unrestricted
recursive row as its mass. -/
theorem fairSteps_recursiveProfileGapCompletionEvent_zero
    (n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
    (tree : ProfileRefinementTree)
    (hfit : profileRefinementTreeFits n k tree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    fairSteps (recursiveProfileGapCompletionEvent 0 n k center hn hk0 tree
      hfit u w (recursiveProfileGapPrefixZero n k center tree u w)) =
      recursiveProfileGapKernelENNReal n k center tree u w := by
  rw [fairSteps_recursiveProfileGapCompletionEvent]
  change (∑' code : RecursiveProfileGapCompletionCode 0 n k center tree u w
      (recursiveProfileGapPrefixZero n k center tree u w),
        recursiveProfileGapCodeMass n k center tree u w
          ((recursiveProfileGapCompletionCodeZeroEquiv n k center tree u w)
            code)) = _
  rw [(recursiveProfileGapCompletionCodeZeroEquiv n k center tree u w).tsum_eq]
  exact tsum_recursiveProfileGapCodeMass n k center tree u w

end


end Erdos1165.AnnularRecursiveProfilePrefixCompletion

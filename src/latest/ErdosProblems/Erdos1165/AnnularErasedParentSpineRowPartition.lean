/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularDecoratedProfileRow
import ErdosProblems.Erdos1165.AnnularRecursiveErasedProfileFactorization

/-!
# The countable row of erased annular parent spines

Fix the successive inner entrances and middle-boundary return endpoints of a
parent renewal gap.  What remains after deleting the child returns is a tuple
of canonical first-hit words: one middle-to-inner word before every child and
one final middle-to-outer word.  This file enumerates that retained tuple and
proves that its literal stopped-word mass is exactly the product of the
corresponding `skeletonExitKernel`s.

The theorem is deliberately about the erased complement.  It never multiplies
a complete parent-gap kernel by a child kernel, and consequently never counts
an inner-to-middle interval twice.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularErasedParentSpineRowPartition

open AlternatingConcatPrefixFree AnnularDecoratedProfileRow
open AnnularOffspringKernelRadial
open AnnularProfileClocks MarkedBoundaryVisitKernel
open MarkedBridgeFactorization TerminalSkeletonInvariance
open TerminalSequentialVisitLaw TerminalSkeletonWords ThickPoint

noncomputable section

/-- The middle point from which retained piece `j` starts.  Coordinate zero
is the parent entrance; coordinate `j+1` is the return endpoint of child `j`.
-/
def middleStage {q : ℕ} (start : Point) (returnPoint : Fin q → Point) :
    Fin (q + 1) → Point :=
  Fin.cons start returnPoint

/-- Subtype-valued version of `middleStage` used by the literal profile
kernels. -/
def profileMiddleStage {q n k : ℕ} {center : Point}
    (start : ProfileCycleMiddlePoint n k center)
    (returnPoint : Fin q → ProfileCycleMiddlePoint n k center) :
    Fin (q + 1) → ProfileCycleMiddlePoint n k center :=
  fun i ↦ Fin.cases start returnPoint i

@[simp] theorem coe_profileMiddleStage {q n k : ℕ} {center : Point}
    (start : ProfileCycleMiddlePoint n k center)
    (returnPoint : Fin q → ProfileCycleMiddlePoint n k center)
    (i : Fin (q + 1)) :
    ((profileMiddleStage start returnPoint i :
      ProfileCycleMiddlePoint n k center) : Point) =
      middleStage start.1 (fun j ↦ (returnPoint j).1) i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · rfl

/-- All retained words of an erased parent gap at fixed entrance/return/exit
endpoints.  The first component contains the `q` inward words and the second
component contains the final escape word. -/
abbrev ErasedParentSpineCode
    (q : ℕ) (boundary : Set Point) (start : Point)
    (innerPoint returnPoint : Fin q → Point) (outerPoint : Point) :=
  ((j : Fin q) → BoundaryExitWordCode boundary
      (middleStage start returnPoint j.castSucc) (innerPoint j)) ×
    BoundaryExitWordCode boundary
      (middleStage start returnPoint (Fin.last q)) outerPoint

/-- The compressed terminal-skeleton code whose retained pieces are exactly
the inward words followed by the final escape word.  The endpoint arrays are
the fixed child entrance/return endpoints at which deleted child words will
later be reinserted. -/
def erasedParentTerminalSkeletonCode
    {q : ℕ} {boundary : Set Point} {start : Point}
    {innerPoint returnPoint : Fin q → Point} {outerPoint : Point}
    (code : ErasedParentSpineCode q boundary start innerPoint returnPoint
      outerPoint) : TerminalSkeletonCode q :=
  (⟨Fin.lastCases (List.ofFn code.2.1.2)
      (fun j ↦ List.ofFn (code.1 j).1.2)⟩,
    (innerPoint, returnPoint))

/-- The single stopped word used to bookkeep the retained complement mass.
Its directions are the concatenation of the retained inward words and final
escape word; deleted child words do not occur in it. -/
def erasedParentSpineWord
    {q : ℕ} {boundary : Set Point} {start : Point}
    {innerPoint returnPoint : Fin q → Point} {outerPoint : Point}
    (code : ErasedParentSpineCode q boundary start innerPoint returnPoint
      outerPoint) : StoppedWord :=
  retainedTerminalWord (fun i : Fin 0 ↦ Fin.elim0 i)
    (erasedParentTerminalSkeletonCode code)

/-- Literal product mass of all retained pieces of one spine code. -/
def erasedParentSpineProductMass
    {q : ℕ} {boundary : Set Point} {start : Point}
    {innerPoint returnPoint : Fin q → Point} {outerPoint : Point}
    (code : ErasedParentSpineCode q boundary start innerPoint returnPoint
      outerPoint) : ℝ≥0∞ :=
  (∏ j, stoppedWordMass (code.1 j).1) * stoppedWordMass code.2.1

/-- The bookkeeping stopped word has exactly the product mass of its retained
pieces.  This is only a length calculation; no Markov or probability premise
enters. -/
theorem stoppedWordMass_erasedParentSpineWord
    {q : ℕ} {boundary : Set Point} {start : Point}
    {innerPoint returnPoint : Fin q → Point} {outerPoint : Point}
    (code : ErasedParentSpineCode q boundary start innerPoint returnPoint
      outerPoint) :
    stoppedWordMass (erasedParentSpineWord code) =
      erasedParentSpineProductMass code := by
  unfold stoppedWordMass erasedParentSpineProductMass
  rw [erasedParentSpineWord, retainedTerminalWord_length]
  simp only [Nat.zero_add, retainedTerminalLength,
    erasedParentTerminalSkeletonCode]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, List.length_ofFn,
    stoppedWordMass]
  rw [pow_add, ← Finset.prod_pow_eq_pow_sum]

private theorem tsum_pi_stoppedWordMass
    {q : ℕ} {Code : Fin q → Type*} [∀ j, Countable (Code j)]
    (word : (j : Fin q) → Code j → StoppedWord) :
    (∑' c : (j : Fin q) → Code j,
        ∏ j, stoppedWordMass (word j (c j))) =
      ∏ j, ∑' cj, stoppedWordMass (word j cj) := by
  classical
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        (∑' c : (j : Fin (q + 1)) → Code j,
            ∏ j, stoppedWordMass (word j (c j))) =
            ∑' p : Code 0 × ((j : Fin q) → Code j.succ),
              ∏ j, stoppedWordMass
                (word j ((Fin.consEquiv Code) p j)) := by
                  exact (Equiv.tsum_eq (Fin.consEquiv Code)
                    (fun c ↦ ∏ j, stoppedWordMass (word j (c j)))).symm
        _ = ∑' p : Code 0 × ((j : Fin q) → Code j.succ),
              stoppedWordMass (word 0 p.1) *
                ∏ j, stoppedWordMass (word j.succ (p.2 j)) := by
                  apply tsum_congr
                  intro p
                  rw [Fin.prod_univ_succ]
                  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
        _ = ∑' c0 : Code 0, ∑' tail : (j : Fin q) → Code j.succ,
              stoppedWordMass (word 0 c0) *
                ∏ j, stoppedWordMass (word j.succ (tail j)) :=
                  (@ENNReal.tsum_prod (Code 0)
                    ((j : Fin q) → Code j.succ)
                    (fun c0 tail ↦ stoppedWordMass (word 0 c0) *
                      ∏ j, stoppedWordMass (word j.succ (tail j))))
        _ = ∑' c0 : Code 0, stoppedWordMass (word 0 c0) *
              ∑' tail : (j : Fin q) → Code j.succ,
                ∏ j, stoppedWordMass (word j.succ (tail j)) := by
                  congr 1
                  funext c0
                  exact ENNReal.tsum_mul_left
        _ = ∑' c0 : Code 0, stoppedWordMass (word 0 c0) *
              ∏ j : Fin q, ∑' cj, stoppedWordMass (word j.succ cj) := by
                  rw [ih (Code := fun j : Fin q ↦ Code j.succ)
                    (fun j cj ↦ word j.succ cj)]
        _ = (∑' c0 : Code 0, stoppedWordMass (word 0 c0)) *
              ∏ j : Fin q, ∑' cj, stoppedWordMass (word j.succ cj) :=
                ENNReal.tsum_mul_right
        _ = ∏ j : Fin (q + 1), ∑' cj, stoppedWordMass (word j cj) := by
              rw [Fin.prod_univ_succ]

/-- Canonical first-boundary word codes sum to the corresponding endpoint
kernel.  Both disjointness and pathwise coverage are supplied by the literal
`StoppedEventCode`, rather than assumed as a mass identity. -/
theorem tsum_stoppedWordMass_boundaryExitWordCode
    (boundary : Set Point) (start endpoint : Point) :
    (∑' code : BoundaryExitWordCode boundary start endpoint,
        stoppedWordMass code.1) =
      skeletonExitKernel boundary start endpoint := by
  rw [skeletonExitKernel_eq_canonical]
  symm
  exact (boundaryExitStoppedEventCode boundary start endpoint).mass_eq

/-- Exact all-spines disintegration at fixed endpoint data. -/
theorem tsum_erasedParentSpineProductMass
    (q : ℕ) (boundary : Set Point) (start : Point)
    (innerPoint returnPoint : Fin q → Point) (outerPoint : Point) :
    (∑' code : ErasedParentSpineCode q boundary start innerPoint
        returnPoint outerPoint,
        erasedParentSpineProductMass code) =
      (∏ j, skeletonExitKernel boundary
          (middleStage start returnPoint j.castSucc) (innerPoint j)) *
        skeletonExitKernel boundary
          (middleStage start returnPoint (Fin.last q)) outerPoint := by
  classical
  unfold erasedParentSpineProductMass
  change (∑' code :
      (((j : Fin q) → BoundaryExitWordCode boundary
          (middleStage start returnPoint j.castSucc) (innerPoint j)) ×
        BoundaryExitWordCode boundary
          (middleStage start returnPoint (Fin.last q)) outerPoint),
      (∏ j, stoppedWordMass (code.1 j).1) *
        stoppedWordMass code.2.1) = _
  let Inward := (j : Fin q) → BoundaryExitWordCode boundary
    (middleStage start returnPoint j.castSucc) (innerPoint j)
  let Escape := BoundaryExitWordCode boundary
    (middleStage start returnPoint (Fin.last q)) outerPoint
  calc
    (∑' code : Inward × Escape,
        (∏ j, stoppedWordMass (code.1 j).1) *
          stoppedWordMass code.2.1) =
        ∑' inward : Inward, ∑' escape : Escape,
          (∏ j, stoppedWordMass (inward j).1) *
            stoppedWordMass escape.1 :=
      @ENNReal.tsum_prod Inward Escape
        (fun inward escape ↦
          (∏ j, stoppedWordMass (inward j).1) *
            stoppedWordMass escape.1)
    _ = ∑' inward : Inward,
          (∏ j, stoppedWordMass (inward j).1) *
            ∑' escape : Escape, stoppedWordMass escape.1 := by
      congr 1
      funext inward
      exact ENNReal.tsum_mul_left
    _ = (∑' inward : Inward,
          ∏ j, stoppedWordMass (inward j).1) *
            ∑' escape : Escape, stoppedWordMass escape.1 :=
      ENNReal.tsum_mul_right
    _ = (∏ j, ∑' inward : BoundaryExitWordCode boundary
          (middleStage start returnPoint j.castSucc) (innerPoint j),
          stoppedWordMass inward.1) *
            ∑' escape : Escape, stoppedWordMass escape.1 := by
      rw [tsum_pi_stoppedWordMass]
    _ = (∏ j, skeletonExitKernel boundary
          (middleStage start returnPoint j.castSucc) (innerPoint j)) *
        skeletonExitKernel boundary
          (middleStage start returnPoint (Fin.last q)) outerPoint := by
      rw [show (∏ j, ∑' inward : BoundaryExitWordCode boundary
            (middleStage start returnPoint j.castSucc) (innerPoint j),
            stoppedWordMass inward.1) =
          ∏ j, skeletonExitKernel boundary
            (middleStage start returnPoint j.castSucc) (innerPoint j) by
        apply Finset.prod_congr rfl
        intro j _hj
        exact tsum_stoppedWordMass_boundaryExitWordCode boundary
          (middleStage start returnPoint j.castSucc) (innerPoint j)]
      rw [show (∑' escape : Escape, stoppedWordMass escape.1) =
          skeletonExitKernel boundary
            (middleStage start returnPoint (Fin.last q)) outerPoint by
        simpa only [Escape] using
          tsum_stoppedWordMass_boundaryExitWordCode boundary
            (middleStage start returnPoint (Fin.last q)) outerPoint]

/-- Profile form of the all-spines disintegration.  The right-hand side is
exactly the retained inward factors and final escape factor used by the
decorated-renewal kernel. -/
theorem tsum_profileErasedParentSpineProductMass
    (q n k : ℕ) (center : Point)
    (start : ProfileCycleMiddlePoint n k center)
    (innerPoint : Fin q → ProfileCycleInnerPoint n k center)
    (returnPoint : Fin q → ProfileCycleMiddlePoint n k center)
    (outerPoint : ProfileCycleOuterPoint n k center) :
    (∑' code : ErasedParentSpineCode q
        (profileInnerBoundary n (k + 1) center ∪
          profileOuterBoundary n k center)
        start.1 (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1)
        outerPoint.1,
        erasedParentSpineProductMass code) =
      (∏ j, profileInwardKernelENNReal n k center
          (profileMiddleStage start returnPoint j.castSucc) (innerPoint j)) *
        profileEscapeKernelENNReal n k center
          (profileMiddleStage start returnPoint (Fin.last q)) outerPoint := by
  simpa only [profileInwardKernelENNReal, profileEscapeKernelENNReal,
    AnnularOffspringKernel.annularEscapeKernel,
    coe_profileMiddleStage] using
      tsum_erasedParentSpineProductMass q
        (profileInnerBoundary n (k + 1) center ∪
          profileOuterBoundary n k center)
        start.1 (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1)
        outerPoint.1

/-! ## Unique fully reassembled words -/

/-- Chronological concatenation of retained inward words and deleted child
returns, followed by the retained final escape word. -/
def interleavedErasedParentList : ∀ (q : ℕ),
    (Fin q → List Direction) → (Fin q → List Direction) →
      List Direction → List Direction
  | 0, _inward, _child, escape => escape
  | q + 1, inward, child, escape =>
      inward 0 ++ child 0 ++
        interleavedErasedParentList q (fun j ↦ inward j.succ)
          (fun j ↦ child j.succ) escape

/-- Alternating prefix-free word families parse uniquely even when both the
retained pieces and deleted child pieces vary. -/
theorem interleavedErasedParentList_injective_of_prefixFree :
    ∀ (q : ℕ) (Inward Child : Fin q → Type*) (Escape : Type*)
      (inwardWord : (j : Fin q) → Inward j → List Direction)
      (childWord : (j : Fin q) → Child j → List Direction)
      (escapeWord : Escape → List Direction),
      (∀ j, PrefixFree (fun c ↦ listStoppedWord (inwardWord j c))) →
      (∀ j, PrefixFree (fun c ↦ listStoppedWord (childWord j c))) →
      PrefixFree (fun c ↦ listStoppedWord (escapeWord c)) →
      Function.Injective
        (fun code : ((j : Fin q) → Inward j) ×
            (((j : Fin q) → Child j) × Escape) ↦
          interleavedErasedParentList q
            (fun j ↦ inwardWord j (code.1 j))
            (fun j ↦ childWord j (code.2.1 j))
            (escapeWord code.2.2)) := by
  intro q
  induction q with
  | zero =>
      intro Inward Child Escape inwardWord childWord escapeWord
        _hinward _hchild hescape
      rintro ⟨inward, child, escape⟩ ⟨inward', child', escape'⟩ hwords
      have hescapeCode : escape = escape' := by
        apply eq_of_prefixes_of_prefixFree escapeWord hescape
          (tailC := []) (tailD := [])
        simpa only [interleavedErasedParentList, List.append_nil] using hwords
      have hinwardEq : inward = inward' := by
        funext j
        exact Fin.elim0 j
      have hchildEq : child = child' := by
        funext j
        exact Fin.elim0 j
      exact Prod.ext hinwardEq (Prod.ext hchildEq hescapeCode)
  | succ q ih =>
      intro Inward Child Escape inwardWord childWord escapeWord
        hinward hchild hescape
      rintro ⟨inward, child, escape⟩ ⟨inward', child', escape'⟩ hwords
      have hwordsAssoc :
          inwardWord 0 (inward 0) ++
              (childWord 0 (child 0) ++
                interleavedErasedParentList q
                  (fun j ↦ inwardWord j.succ (inward j.succ))
                  (fun j ↦ childWord j.succ (child j.succ))
                  (escapeWord escape)) =
            inwardWord 0 (inward' 0) ++
              (childWord 0 (child' 0) ++
                interleavedErasedParentList q
                  (fun j ↦ inwardWord j.succ (inward' j.succ))
                  (fun j ↦ childWord j.succ (child' j.succ))
                  (escapeWord escape')) := by
        simpa only [interleavedErasedParentList, List.append_assoc] using hwords
      have hinwardZero : inward 0 = inward' 0 :=
        eq_of_prefixes_of_prefixFree (inwardWord 0) (hinward 0) hwordsAssoc
      rw [hinwardZero] at hwordsAssoc
      have hafterInward :
          childWord 0 (child 0) ++
              interleavedErasedParentList q
                (fun j ↦ inwardWord j.succ (inward j.succ))
                (fun j ↦ childWord j.succ (child j.succ))
                (escapeWord escape) =
            childWord 0 (child' 0) ++
              interleavedErasedParentList q
                (fun j ↦ inwardWord j.succ (inward' j.succ))
                (fun j ↦ childWord j.succ (child' j.succ))
                (escapeWord escape') :=
        List.append_cancel_left hwordsAssoc
      have hchildZero : child 0 = child' 0 :=
        eq_of_prefixes_of_prefixFree (childWord 0) (hchild 0) hafterInward
      rw [hchildZero] at hafterInward
      have htailWords :
          interleavedErasedParentList q
                (fun j ↦ inwardWord j.succ (inward j.succ))
                (fun j ↦ childWord j.succ (child j.succ))
                (escapeWord escape) =
            interleavedErasedParentList q
                (fun j ↦ inwardWord j.succ (inward' j.succ))
                (fun j ↦ childWord j.succ (child' j.succ))
                (escapeWord escape') :=
        List.append_cancel_left hafterInward
      have htail :
          (⟨(fun j : Fin q ↦ inward j.succ),
              ⟨(fun j : Fin q ↦ child j.succ), escape⟩⟩ :
            ((j : Fin q) → Inward j.succ) ×
              (((j : Fin q) → Child j.succ) × Escape)) =
            (⟨(fun j : Fin q ↦ inward' j.succ),
              ⟨(fun j : Fin q ↦ child' j.succ), escape'⟩⟩ :
            ((j : Fin q) → Inward j.succ) ×
              (((j : Fin q) → Child j.succ) × Escape)) := by
        apply ih
          (fun j : Fin q ↦ Inward j.succ)
          (fun j : Fin q ↦ Child j.succ) Escape
          (fun j c ↦ inwardWord j.succ c)
          (fun j c ↦ childWord j.succ c) escapeWord
          (fun j ↦ hinward j.succ) (fun j ↦ hchild j.succ) hescape
        exact htailWords
      have hinwardTail : (fun j : Fin q ↦ inward j.succ) =
          (fun j : Fin q ↦ inward' j.succ) := congrArg Prod.fst htail
      have htailSecond := congrArg Prod.snd htail
      have hchildTail : (fun j : Fin q ↦ child j.succ) =
          (fun j : Fin q ↦ child' j.succ) := congrArg Prod.fst htailSecond
      have hescapeEq : escape = escape' := congrArg Prod.snd htailSecond
      have hinwardEq : inward = inward' := by
        funext j
        refine Fin.cases hinwardZero (fun i ↦ ?_) j
        exact congrFun hinwardTail i
      have hchildEq : child = child' := by
        funext j
        refine Fin.cases hchildZero (fun i ↦ ?_) j
        exact congrFun hchildTail i
      exact Prod.ext hinwardEq (Prod.ext hchildEq hescapeEq)

/-- The fixed-endpoint code of a fully reassembled parent word: retained
inward words, deleted child returns, and the retained escape word. -/
abbrev ErasedParentAssemblyCode
    (q : ℕ) (retainedBoundary childBoundary : Set Point) (start : Point)
    (innerPoint returnPoint : Fin q → Point) (outerPoint : Point) :=
  ((j : Fin q) → BoundaryExitWordCode retainedBoundary
      (middleStage start returnPoint j.castSucc) (innerPoint j)) ×
    (((j : Fin q) → BoundaryExitWordCode childBoundary
        (innerPoint j) (returnPoint j)) ×
      BoundaryExitWordCode retainedBoundary
        (middleStage start returnPoint (Fin.last q)) outerPoint)

/-- The literal fully reassembled parent word. -/
def erasedParentAssemblyWord
    {q : ℕ} {retainedBoundary childBoundary : Set Point} {start : Point}
    {innerPoint returnPoint : Fin q → Point} {outerPoint : Point}
    (code : ErasedParentAssemblyCode q retainedBoundary childBoundary start
      innerPoint returnPoint outerPoint) : StoppedWord :=
  listStoppedWord <| interleavedErasedParentList q
    (fun j ↦ List.ofFn (code.1 j).1.2)
    (fun j ↦ List.ofFn (code.2.1 j).1.2)
    (List.ofFn code.2.2.1.2)

/-- Literal product of the retained inward, deleted child, and retained
escape cylinder masses of one complete code. -/
def erasedParentAssemblyProductMass
    {q : ℕ} {retainedBoundary childBoundary : Set Point} {start : Point}
    {innerPoint returnPoint : Fin q → Point} {outerPoint : Point}
    (code : ErasedParentAssemblyCode q retainedBoundary childBoundary start
      innerPoint returnPoint outerPoint) : ℝ≥0∞ :=
  (∏ j, stoppedWordMass (code.1 j).1) *
    (∏ j, stoppedWordMass (code.2.1 j).1) *
      stoppedWordMass code.2.2.1

theorem interleavedErasedParentList_length : ∀ (q : ℕ)
    (inward child : Fin q → List Direction) (escape : List Direction),
    (interleavedErasedParentList q inward child escape).length =
      (∑ j, (inward j).length) + (∑ j, (child j).length) +
        escape.length := by
  intro q
  induction q with
  | zero =>
      intro inward child escape
      simp [interleavedErasedParentList]
  | succ q ih =>
      intro inward child escape
      simp only [interleavedErasedParentList, List.length_append]
      rw [ih]
      rw [Fin.sum_univ_succ (fun j ↦ (inward j).length),
        Fin.sum_univ_succ (fun j ↦ (child j).length)]
      omega

/-- Exact cylinder mass of one fully reassembled code. -/
theorem stoppedWordMass_erasedParentAssemblyWord
    {q : ℕ} {retainedBoundary childBoundary : Set Point} {start : Point}
    {innerPoint returnPoint : Fin q → Point} {outerPoint : Point}
    (code : ErasedParentAssemblyCode q retainedBoundary childBoundary start
      innerPoint returnPoint outerPoint) :
    stoppedWordMass (erasedParentAssemblyWord code) =
      erasedParentAssemblyProductMass code := by
  unfold stoppedWordMass erasedParentAssemblyWord
    erasedParentAssemblyProductMass
  simp only [listStoppedWord_length]
  rw [interleavedErasedParentList_length, pow_add, pow_add,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  simp only [stoppedWordMass, List.length_ofFn]

/-- The complete fixed-endpoint assembly has no duplicate code: its finite
direction word uniquely recovers every retained piece and every deleted child
word. -/
theorem erasedParentAssemblyWord_injective
    (q : ℕ) (retainedBoundary childBoundary : Set Point) (start : Point)
    (innerPoint returnPoint : Fin q → Point) (outerPoint : Point) :
    Function.Injective
      (erasedParentAssemblyWord (q := q)
        (retainedBoundary := retainedBoundary)
        (childBoundary := childBoundary) (start := start)
        (innerPoint := innerPoint) (returnPoint := returnPoint)
        (outerPoint := outerPoint)) := by
  intro left right hword
  apply interleavedErasedParentList_injective_of_prefixFree q
    (fun j ↦ BoundaryExitWordCode retainedBoundary
      (middleStage start returnPoint j.castSucc) (innerPoint j))
    (fun j ↦ BoundaryExitWordCode childBoundary
      (innerPoint j) (returnPoint j))
    (BoundaryExitWordCode retainedBoundary
      (middleStage start returnPoint (Fin.last q)) outerPoint)
    (fun _ c ↦ List.ofFn c.1.2) (fun _ c ↦ List.ofFn c.1.2)
    (fun c ↦ List.ofFn c.1.2)
  · intro j
    simpa only [listStoppedWord_ofFn] using
      prefixFree_boundaryExitWordCode retainedBoundary
        (middleStage start returnPoint j.castSucc) (innerPoint j)
  · intro j
    simpa only [listStoppedWord_ofFn] using
      prefixFree_boundaryExitWordCode childBoundary
        (innerPoint j) (returnPoint j)
  · simpa only [listStoppedWord_ofFn] using
      prefixFree_boundaryExitWordCode retainedBoundary
        (middleStage start returnPoint (Fin.last q)) outerPoint
  · have hlists := congrArg (fun word : StoppedWord ↦ List.ofFn word.2) hword
    simpa only [erasedParentAssemblyWord, listStoppedWord_toList] using hlists

/-- The fixed-endpoint parent words are exactly the range of their unique
retained-spine/deleted-child assembly codes.  This is the surjectivity half
of the code decomposition, packaged without choosing an inverse. -/
def erasedParentAssemblyEquivRange
    (q : ℕ) (retainedBoundary childBoundary : Set Point) (start : Point)
    (innerPoint returnPoint : Fin q → Point) (outerPoint : Point) :
    ErasedParentAssemblyCode q retainedBoundary childBoundary start
        innerPoint returnPoint outerPoint ≃
      Set.range (erasedParentAssemblyWord (q := q)
        (retainedBoundary := retainedBoundary)
        (childBoundary := childBoundary) (start := start)
        (innerPoint := innerPoint) (returnPoint := returnPoint)
        (outerPoint := outerPoint)) :=
  Equiv.ofInjective _
    (erasedParentAssemblyWord_injective q retainedBoundary childBoundary
      start innerPoint returnPoint outerPoint)

/-- Regard a fully reassembled word as a canonical parent first-boundary
word once the geometric first-hit and endpoint facts have been proved. -/
def erasedParentBoundaryExitWordCode
    {q : ℕ} {retainedBoundary childBoundary parentBoundary : Set Point}
    {start : Point} {innerPoint returnPoint : Fin q → Point}
    {outerPoint : Point}
    (hfirst : ∀ code : ErasedParentAssemblyCode q retainedBoundary
      childBoundary start innerPoint returnPoint outerPoint,
      AbsoluteBoundaryFirstAt parentBoundary start
        (extendStoppedWord (erasedParentAssemblyWord code))
        (erasedParentAssemblyWord code).1)
    (hendpoint : ∀ code : ErasedParentAssemblyCode q retainedBoundary
      childBoundary start innerPoint returnPoint outerPoint,
      PlanarPotential.trajectoryFrom start
        (extendStoppedWord (erasedParentAssemblyWord code))
        (erasedParentAssemblyWord code).1 = outerPoint)
    (code : ErasedParentAssemblyCode q retainedBoundary childBoundary start
      innerPoint returnPoint outerPoint) :
    BoundaryExitWordCode parentBoundary start outerPoint :=
  ⟨erasedParentAssemblyWord code, hfirst code, hendpoint code⟩

/-- Exact parent first-boundary geometry makes the fully reassembled word
family prefix-free.  Injectivity above is the only non-geometric uniqueness
input. -/
theorem prefixFree_erasedParentAssemblyWord
    {q : ℕ} {retainedBoundary childBoundary parentBoundary : Set Point}
    {start : Point} {innerPoint returnPoint : Fin q → Point}
    {outerPoint : Point}
    (hfirst : ∀ code : ErasedParentAssemblyCode q retainedBoundary
      childBoundary start innerPoint returnPoint outerPoint,
      AbsoluteBoundaryFirstAt parentBoundary start
        (extendStoppedWord (erasedParentAssemblyWord code))
        (erasedParentAssemblyWord code).1)
    (hendpoint : ∀ code : ErasedParentAssemblyCode q retainedBoundary
      childBoundary start innerPoint returnPoint outerPoint,
      PlanarPotential.trajectoryFrom start
        (extendStoppedWord (erasedParentAssemblyWord code))
        (erasedParentAssemblyWord code).1 = outerPoint) :
    PrefixFree (erasedParentAssemblyWord (q := q)
      (retainedBoundary := retainedBoundary)
      (childBoundary := childBoundary) (start := start)
      (innerPoint := innerPoint) (returnPoint := returnPoint)
      (outerPoint := outerPoint)) := by
  let parentCode := erasedParentBoundaryExitWordCode hfirst hendpoint
  have hinjective := erasedParentAssemblyWord_injective q retainedBoundary
    childBoundary start innerPoint returnPoint outerPoint
  intro left right hne
  have hparentNe : parentCode left ≠ parentCode right := by
    intro heq
    apply hne
    apply hinjective
    exact congrArg Subtype.val heq
  simpa only [parentCode, erasedParentBoundaryExitWordCode] using
    (prefixFree_boundaryExitWordCode parentBoundary start outerPoint hparentNe)

/-- Bundled prefix-free stopped-event code for the entire fixed-endpoint
parent row.  Its coverage is the literal union of all uniquely assembled
words. -/
def erasedParentAssemblyStoppedEventCode
    {q : ℕ} {retainedBoundary childBoundary parentBoundary : Set Point}
    {start : Point} {innerPoint returnPoint : Fin q → Point}
    {outerPoint : Point}
    (hfirst : ∀ code : ErasedParentAssemblyCode q retainedBoundary
      childBoundary start innerPoint returnPoint outerPoint,
      AbsoluteBoundaryFirstAt parentBoundary start
        (extendStoppedWord (erasedParentAssemblyWord code))
        (erasedParentAssemblyWord code).1)
    (hendpoint : ∀ code : ErasedParentAssemblyCode q retainedBoundary
      childBoundary start innerPoint returnPoint outerPoint,
      PlanarPotential.trajectoryFrom start
        (extendStoppedWord (erasedParentAssemblyWord code))
        (erasedParentAssemblyWord code).1 = outerPoint) :
    StoppedEventCode (stoppedWordEvent
      (erasedParentAssemblyWord (q := q)
        (retainedBoundary := retainedBoundary)
        (childBoundary := childBoundary) (start := start)
        (innerPoint := innerPoint) (returnPoint := returnPoint)
        (outerPoint := outerPoint))) where
  Code := ErasedParentAssemblyCode q retainedBoundary childBoundary start
    innerPoint returnPoint outerPoint
  countableCode := inferInstance
  word := erasedParentAssemblyWord
  prefixFree_word := prefixFree_erasedParentAssemblyWord hfirst hendpoint
  event_eq := rfl

/-- Summing every complete fixed-endpoint assembly code gives exactly the
chronological product of its inward, child-return, and escape endpoint
kernels. -/
theorem tsum_erasedParentAssemblyProductMass
    (q : ℕ) (retainedBoundary childBoundary : Set Point) (start : Point)
    (innerPoint returnPoint : Fin q → Point) (outerPoint : Point) :
    (∑' code : ErasedParentAssemblyCode q retainedBoundary childBoundary
        start innerPoint returnPoint outerPoint,
        erasedParentAssemblyProductMass code) =
      (∏ j, skeletonExitKernel retainedBoundary
          (middleStage start returnPoint j.castSucc) (innerPoint j)) *
        (∏ j, skeletonExitKernel childBoundary
          (innerPoint j) (returnPoint j)) *
        skeletonExitKernel retainedBoundary
          (middleStage start returnPoint (Fin.last q)) outerPoint := by
  classical
  let Inward := (j : Fin q) → BoundaryExitWordCode retainedBoundary
    (middleStage start returnPoint j.castSucc) (innerPoint j)
  let Child := (j : Fin q) → BoundaryExitWordCode childBoundary
    (innerPoint j) (returnPoint j)
  let Escape := BoundaryExitWordCode retainedBoundary
    (middleStage start returnPoint (Fin.last q)) outerPoint
  let inwardMass : Inward → ℝ≥0∞ := fun inward ↦
    ∏ j, stoppedWordMass (inward j).1
  let childMass : Child → ℝ≥0∞ := fun child ↦
    ∏ j, stoppedWordMass (child j).1
  let escapeMass : Escape → ℝ≥0∞ := fun escape ↦
    stoppedWordMass escape.1
  change (∑' code : Inward × (Child × Escape),
      inwardMass code.1 * childMass code.2.1 * escapeMass code.2.2) = _
  calc
    (∑' code : Inward × (Child × Escape),
        inwardMass code.1 * childMass code.2.1 * escapeMass code.2.2) =
        ∑' inward : Inward, ∑' child : Child, ∑' escape : Escape,
          inwardMass inward * childMass child * escapeMass escape := by
      calc
        _ = ∑' inward : Inward, ∑' pair : Child × Escape,
              inwardMass inward * childMass pair.1 * escapeMass pair.2 :=
          @ENNReal.tsum_prod Inward (Child × Escape)
            (fun inward pair ↦
              inwardMass inward * childMass pair.1 * escapeMass pair.2)
        _ = _ := by
          congr 1
          funext inward
          exact @ENNReal.tsum_prod Child Escape
            (fun child escape ↦
              inwardMass inward * childMass child * escapeMass escape)
    _ = ∑' inward : Inward, ∑' child : Child,
          (inwardMass inward * childMass child) *
            ∑' escape : Escape, escapeMass escape := by
      congr 1
      funext inward
      congr 1
      funext child
      exact ENNReal.tsum_mul_left
    _ = ∑' inward : Inward,
          ((∑' child : Child,
              inwardMass inward * childMass child) *
            ∑' escape : Escape, escapeMass escape) := by
      congr 1
      funext inward
      rw [ENNReal.tsum_mul_right]
    _ = ∑' inward : Inward,
          (inwardMass inward *
              (∑' child : Child, childMass child)) *
            ∑' escape : Escape, escapeMass escape := by
      congr 1
      funext inward
      rw [ENNReal.tsum_mul_left]
    _ = ∑' inward : Inward,
          inwardMass inward *
            ((∑' child : Child, childMass child) *
              ∑' escape : Escape, escapeMass escape) := by
      simp only [mul_assoc]
    _ = (∑' inward : Inward, inwardMass inward) *
          ((∑' child : Child, childMass child) *
            ∑' escape : Escape, escapeMass escape) :=
      ENNReal.tsum_mul_right
    _ = (∏ j, skeletonExitKernel retainedBoundary
          (middleStage start returnPoint j.castSucc) (innerPoint j)) *
        (∏ j, skeletonExitKernel childBoundary
          (innerPoint j) (returnPoint j)) *
        skeletonExitKernel retainedBoundary
          (middleStage start returnPoint (Fin.last q)) outerPoint := by
      rw [show (∑' inward : Inward, inwardMass inward) =
          ∏ j, skeletonExitKernel retainedBoundary
            (middleStage start returnPoint j.castSucc) (innerPoint j) by
        unfold inwardMass Inward
        rw [tsum_pi_stoppedWordMass]
        apply Finset.prod_congr rfl
        intro j _hj
        exact tsum_stoppedWordMass_boundaryExitWordCode retainedBoundary
          (middleStage start returnPoint j.castSucc) (innerPoint j)]
      rw [show (∑' child : Child, childMass child) =
          ∏ j, skeletonExitKernel childBoundary
            (innerPoint j) (returnPoint j) by
        unfold childMass Child
        rw [tsum_pi_stoppedWordMass]
        apply Finset.prod_congr rfl
        intro j _hj
        exact tsum_stoppedWordMass_boundaryExitWordCode childBoundary
          (innerPoint j) (returnPoint j)]
      rw [show (∑' escape : Escape, escapeMass escape) =
          skeletonExitKernel retainedBoundary
            (middleStage start returnPoint (Fin.last q)) outerPoint by
        simpa only [escapeMass, Escape] using
          tsum_stoppedWordMass_boundaryExitWordCode retainedBoundary
            (middleStage start returnPoint (Fin.last q)) outerPoint]
      ac_rfl

/-- Exact probability mass of the fixed-endpoint assembled parent row.  The
first-boundary hypotheses are pathwise and serve only to certify disjointness;
the mass identity itself is derived from literal fair-walk cylinders. -/
theorem fairSteps_erasedParentAssemblyEvent
    {q : ℕ} {retainedBoundary childBoundary parentBoundary : Set Point}
    {start : Point} {innerPoint returnPoint : Fin q → Point}
    {outerPoint : Point}
    (hfirst : ∀ code : ErasedParentAssemblyCode q retainedBoundary
      childBoundary start innerPoint returnPoint outerPoint,
      AbsoluteBoundaryFirstAt parentBoundary start
        (extendStoppedWord (erasedParentAssemblyWord code))
        (erasedParentAssemblyWord code).1)
    (hendpoint : ∀ code : ErasedParentAssemblyCode q retainedBoundary
      childBoundary start innerPoint returnPoint outerPoint,
      PlanarPotential.trajectoryFrom start
        (extendStoppedWord (erasedParentAssemblyWord code))
        (erasedParentAssemblyWord code).1 = outerPoint) :
    fairSteps (stoppedWordEvent
        (erasedParentAssemblyWord (q := q)
          (retainedBoundary := retainedBoundary)
          (childBoundary := childBoundary) (start := start)
          (innerPoint := innerPoint) (returnPoint := returnPoint)
          (outerPoint := outerPoint))) =
      (∏ j, skeletonExitKernel retainedBoundary
          (middleStage start returnPoint j.castSucc) (innerPoint j)) *
        (∏ j, skeletonExitKernel childBoundary
          (innerPoint j) (returnPoint j)) *
        skeletonExitKernel retainedBoundary
          (middleStage start returnPoint (Fin.last q)) outerPoint := by
  rw [(erasedParentAssemblyStoppedEventCode hfirst hendpoint).mass_eq]
  change (∑' code : ErasedParentAssemblyCode q retainedBoundary
    childBoundary start innerPoint returnPoint outerPoint,
      stoppedWordMass (erasedParentAssemblyWord code)) = _
  rw [show (∑' code : ErasedParentAssemblyCode q retainedBoundary
      childBoundary start innerPoint returnPoint outerPoint,
        stoppedWordMass (erasedParentAssemblyWord code)) =
      ∑' code : ErasedParentAssemblyCode q retainedBoundary
        childBoundary start innerPoint returnPoint outerPoint,
        erasedParentAssemblyProductMass code by
      apply tsum_congr
      exact stoppedWordMass_erasedParentAssemblyWord]
  exact tsum_erasedParentAssemblyProductMass q retainedBoundary childBoundary
    start innerPoint returnPoint outerPoint

end

end Erdos1165.AnnularErasedParentSpineRowPartition

/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveDecoratedProfileCode
import ErdosProblems.Erdos1165.AnnularErasedParentSpineProfileRow

/-!
# Physical assembly of recursive profile codes

The recursive decorated code records every retained parent-spine piece and
every recursively refined child return exactly once.  This file turns such a
code into its literal first-exit word.  The depth predicate is essential:
an internal node at level `k` uses the level-`k+1` profile boundary, and hence
is physically meaningful only while `k+1 <= n`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AnnularRecursiveProfileCodeAssembly

open AlternatingConcatPrefixFree AnnularDecoratedProfileCode
open AnnularErasedParentSpineProfileRow
open AnnularOffspringKernelRadial AnnularProfileClocks
open AnnularRecursiveDecoratedProfileCode
open MarkedBoundaryVisitKernel MarkedBridgeFactorization ThickPoint
open TerminalGlobalExitSplice
open TerminalSequentialVisitLaw

noncomputable section

mutual
  /-- A recursive tree fits below level `n` when every internal node has a
  genuine next profile boundary. -/
  def profileRefinementTreeFits (n k : ℕ) :
      ProfileRefinementTree → Prop
    | .leaf => True
    | .node children => k + 1 ≤ n ∧ profileRefinementForestFits n k children

  /-- Every child in a parent forest is realized one profile level deeper;
  the tail remains at the parent level. -/
  def profileRefinementForestFits (n k : ℕ) :
      ProfileRefinementForest → Prop
    | .nil => True
    | .cons child tail =>
        profileRefinementTreeFits n (k + 1) child ∧
          profileRefinementForestFits n k tail
end

theorem stoppedWordMass_listStoppedWord_append
    (left right : List Direction) :
    stoppedWordMass (listStoppedWord (left ++ right)) =
      stoppedWordMass (listStoppedWord left) *
        stoppedWordMass (listStoppedWord right) := by
  unfold stoppedWordMass
  simp only [listStoppedWord_length, List.length_append, pow_add]

mutual
  /-- The literal direction list assembled from one recursive tree code. -/
  def recursiveProfileGapList
      (n k : ℕ) (center : Point) :
      ∀ (tree : ProfileRefinementTree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        RecursiveProfileGapCode n k center tree u w → List Direction
    | .leaf, _u, _w, code => List.ofFn code.1.2
    | .node children, u, w, code =>
        recursiveProfileForestList n k center children u w code

  /-- Chronological assembly of a forest: retained inward word, one child
  word, then the remaining parent forest. -/
  def recursiveProfileForestList
      (n k : ℕ) (center : Point) :
      ∀ (forest : ProfileRefinementForest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        RecursiveProfileForestCode n k center forest u w → List Direction
    | .nil, _u, _w, code => List.ofFn code.1.2
    | .cons child tail, u, w, code =>
        List.ofFn code.2.2.1.1.2 ++
          recursiveProfileGapList n (k + 1) center child
            code.1 code.2.1 code.2.2.2.1 ++
          recursiveProfileForestList n k center tail
            code.2.1 w code.2.2.2.2
end

mutual
  /-- The assembled list has exactly the product mass recorded by the
  recursive literal code. -/
  theorem stoppedWordMass_recursiveProfileGapList
      (n k : ℕ) (center : Point) :
      ∀ (tree : ProfileRefinementTree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center)
        (code : RecursiveProfileGapCode n k center tree u w),
        stoppedWordMass (listStoppedWord
          (recursiveProfileGapList n k center tree u w code)) =
          recursiveProfileGapCodeMass n k center tree u w code
    | .leaf, _u, _w, code => by
        simpa only [recursiveProfileGapList, listStoppedWord_ofFn,
          recursiveProfileGapCodeMass]
    | .node children, u, w, code =>
        stoppedWordMass_recursiveProfileForestList n k center children u w code

  /-- Forest version of the exact literal mass identity. -/
  theorem stoppedWordMass_recursiveProfileForestList
      (n k : ℕ) (center : Point) :
      ∀ (forest : ProfileRefinementForest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center)
        (code : RecursiveProfileForestCode n k center forest u w),
        stoppedWordMass (listStoppedWord
          (recursiveProfileForestList n k center forest u w code)) =
          recursiveProfileForestCodeMass n k center forest u w code
    | .nil, _u, _w, code => by
        simpa only [recursiveProfileForestList, listStoppedWord_ofFn,
          recursiveProfileForestCodeMass]
    | .cons child tail, u, w, code => by
        simp only [recursiveProfileForestList,
          recursiveProfileForestCodeMass]
        rw [stoppedWordMass_listStoppedWord_append,
          stoppedWordMass_listStoppedWord_append]
        simp only [listStoppedWord_ofFn]
        rw [stoppedWordMass_recursiveProfileGapList,
          stoppedWordMass_recursiveProfileForestList]
end

mutual
  /-- Assemble an admissible recursive tree into its canonical parent
  first-boundary code. -/
  def recursiveProfileGapBoundaryExitWordCode
      (n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k) :
      ∀ (tree : ProfileRefinementTree)
        (hfit : profileRefinementTreeFits n k tree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        RecursiveProfileGapCode n k center tree u w →
          BoundaryExitWordCode (profileOuterBoundary n k center) u.1 w.1
    | .leaf, _hfit, _u, _w, code => code
    | .node children, hfit, u, w, code =>
        recursiveProfileForestBoundaryExitWordCode n k center hn hk0
          hfit.1 children hfit.2 u w code

  /-- Assemble an admissible chronological forest into one parent
  first-boundary word. -/
  def recursiveProfileForestBoundaryExitWordCode
      (n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
      (hk : k + 1 ≤ n) :
      ∀ (forest : ProfileRefinementForest)
        (hfit : profileRefinementForestFits n k forest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        RecursiveProfileForestCode n k center forest u w →
          BoundaryExitWordCode (profileOuterBoundary n k center) u.1 w.1
    | .nil, _hfit, u, w, code => ⟨code.1, by
        simpa only [listStoppedWord_ofFn, List.length_ofFn] using
          absoluteBoundaryFirstAt_listStoppedWord
            (profileEscapeWord_firstHits_outer u.1 w code),
        code.2.2⟩
    | .cons child tail, hfit, u, w, code => by
        let inward := code.2.2.1
        let childCode := recursiveProfileGapBoundaryExitWordCode
          n (k + 1) center hn (by omega) child hfit.1
            code.1 code.2.1 code.2.2.2.1
        let tailCode := recursiveProfileForestBoundaryExitWordCode
          n k center hn hk0 hk tail hfit.2 code.2.1 w code.2.2.2.2
        let word := List.ofFn inward.1.2 ++ List.ofFn childCode.1.2 ++
          List.ofFn tailCode.1.2
        have hinwardEnd : wordEndpoint u.1 (List.ofFn inward.1.2) = code.1.1 :=
          boundaryExitWordCode_wordEndpoint inward
        have hchildEnd : wordEndpoint code.1.1
            (List.ofFn childCode.1.2) = code.2.1.1 :=
          boundaryExitWordCode_wordEndpoint childCode
        have hinwardAvoid : WordAvoids (profileOuterBoundary n k center) u.1
            (List.ofFn inward.1.2) :=
          profileInwardWord_avoids_outer hn hk0 hk u.1 code.1 inward
        have hchildWithin : WordWithin (disc center (scaleRadius n k))
            code.1.1 (List.ofFn childCode.1.2) :=
          profileChildWord_within_parentDisc hk code.1 code.2.1.1 childCode
        have hchildAvoid : WordAvoids (profileOuterBoundary n k center)
            code.1.1 (List.ofFn childCode.1.2) :=
          hchildWithin.avoids
            (fun _ hz ↦ parentDisc_disjoint_profileOuterBoundary hn hk0 hk hz)
        have hprefix : WordAvoids (profileOuterBoundary n k center) u.1
            (List.ofFn inward.1.2 ++ List.ofFn childCode.1.2) := by
          apply WordAvoids.append hinwardAvoid
          rw [hinwardEnd]
          exact hchildAvoid
        have htailFirst : WordFirstHitsAtEnd
            (profileOuterBoundary n k center) code.2.1.1
            (List.ofFn tailCode.1.2) :=
          wordFirstHitsAtEnd_boundaryExitWordCode tailCode
        have hfirst : WordFirstHitsAtEnd (profileOuterBoundary n k center)
            u.1 word := by
          apply WordFirstHitsAtEnd.append hprefix
          rw [wordEndpoint_append, hinwardEnd, hchildEnd]
          exact htailFirst
        have hend : wordEndpoint u.1 word = w.1 := by
          simp only [word, wordEndpoint_append, hinwardEnd, hchildEnd]
          exact boundaryExitWordCode_wordEndpoint tailCode
        exact ⟨listStoppedWord word,
          absoluteBoundaryFirstAt_listStoppedWord hfirst,
          trajectoryFrom_listStoppedWord_endpoint hend⟩
end

end

mutual
  /-- The physical boundary code stores exactly the recursively assembled
  literal list. -/
  theorem recursiveProfileGapBoundaryExitWordCode_val
      (n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k) :
      ∀ (tree : ProfileRefinementTree)
        (hfit : profileRefinementTreeFits n k tree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center)
        (code : RecursiveProfileGapCode n k center tree u w),
        (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree
          hfit u w code).1 =
            listStoppedWord (recursiveProfileGapList n k center tree u w code)
    | .leaf, _hfit, _u, _w, code => by
        simp only [recursiveProfileGapBoundaryExitWordCode,
          recursiveProfileGapList, listStoppedWord_ofFn]
    | .node children, hfit, u, w, code =>
        recursiveProfileForestBoundaryExitWordCode_val n k center hn hk0
          hfit.1 children hfit.2 u w code

  /-- Forest version of the stored-word identity. -/
  theorem recursiveProfileForestBoundaryExitWordCode_val
      (n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
      (hk : k + 1 ≤ n) :
      ∀ (forest : ProfileRefinementForest)
        (hfit : profileRefinementForestFits n k forest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center)
        (code : RecursiveProfileForestCode n k center forest u w),
        (recursiveProfileForestBoundaryExitWordCode n k center hn hk0 hk
          forest hfit u w code).1 =
            listStoppedWord
              (recursiveProfileForestList n k center forest u w code)
    | .nil, _hfit, _u, _w, code => by
        simp only [recursiveProfileForestBoundaryExitWordCode,
          recursiveProfileForestList, listStoppedWord_ofFn]
    | .cons child tail, hfit, u, w, code => by
        simp only [recursiveProfileForestBoundaryExitWordCode,
          recursiveProfileForestList]
        have hchild := recursiveProfileGapBoundaryExitWordCode_val
          n (k + 1) center hn (by omega) child hfit.1
            code.1 code.2.1 code.2.2.2.1
        have hchildList := congrArg
          (fun stopped : StoppedWord ↦ List.ofFn stopped.2) hchild
        simp only [listStoppedWord_toList] at hchildList
        have htail := recursiveProfileForestBoundaryExitWordCode_val
          n k center hn hk0 hk tail hfit.2 code.2.1 w code.2.2.2.2
        have htailList := congrArg
          (fun stopped : StoppedWord ↦ List.ofFn stopped.2) htail
        simp only [listStoppedWord_toList] at htailList
        rw [hchildList, htailList]
end

theorem sigmaBoundaryExitWordCode_injective
    {Endpoint : Type*} {boundary : Set Point} {start : Point}
    (point : Endpoint → Point) (hpoint : Function.Injective point) :
    Function.Injective (fun code : Σ endpoint : Endpoint,
      BoundaryExitWordCode boundary start (point endpoint) ↦ code.2.1) := by
  rintro ⟨endpoint, code⟩ ⟨endpoint', code'⟩ hword
  change code.1 = code'.1 at hword
  have hendpointPoint : point endpoint = point endpoint' := by
    rw [← code.2.2, ← code'.2.2, hword]
  have hendpoint : endpoint = endpoint' := hpoint hendpointPoint
  subst endpoint'
  have hcode : code = code' := Subtype.ext hword
  subst code'
  rfl

theorem prefixFree_of_boundaryFirst
    {Code : Type*} (word : Code → StoppedWord)
    (hword : Function.Injective word)
    (boundary : Set Point) (start : Point)
    (hfirst : ∀ c, AbsoluteBoundaryFirstAt boundary start
      (extendStoppedWord (word c)) (word c).1) :
    PrefixFree word := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro omega hc hd
  have hcfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    hc (hfirst c)
  have hdfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder
    hd (hfirst d)
  have hlen : (word c).1 = (word d).1 :=
    absoluteBoundaryFirstAt_unique hcfirst hdfirst
  apply hcd
  apply hword
  apply Sigma.ext hlen
  apply (Fin.heq_fun_iff hlen).2
  intro i
  change stepPrefix (word c).1 omega = (word c).2 at hc
  change stepPrefix (word d).1 omega = (word d).2 at hd
  have hci := congrFun hc i
  have hdi := congrFun hd ⟨(i : ℕ), hlen ▸ i.2⟩
  simpa only [stepPrefix] using hci.symm.trans hdi

theorem prefixFree_sigmaBoundaryExitWordCode
    {Endpoint : Type*} {boundary : Set Point} {start : Point}
    (point : Endpoint → Point) (hpoint : Function.Injective point) :
    PrefixFree (fun code : Σ endpoint : Endpoint,
      BoundaryExitWordCode boundary start (point endpoint) ↦ code.2.1) := by
  apply prefixFree_of_boundaryFirst _
    (sigmaBoundaryExitWordCode_injective point hpoint) boundary start
  exact fun code ↦ code.2.2.1

mutual
  /-- The physical assembled word uniquely determines its recursive tree
  code. -/
  theorem recursiveProfileGapBoundaryExitWordCode_injective
      (n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k) :
      ∀ (tree : ProfileRefinementTree)
        (hfit : profileRefinementTreeFits n k tree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        Function.Injective
          (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree
            hfit u w)
    | .leaf, _hfit, _u, _w => by
        intro left right h
        simpa only [recursiveProfileGapBoundaryExitWordCode,
          RecursiveProfileGapCode] using h
    | .node children, hfit, u, w =>
        recursiveProfileForestBoundaryExitWordCode_injective
          n k center hn hk0 hfit.1 children hfit.2 u w

  /-- Chronological parsing is unique for every admissible recursive
  forest.  The retained word is parsed first, then its child return, then
  the remaining parent forest. -/
  theorem recursiveProfileForestBoundaryExitWordCode_injective
      (n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
      (hk : k + 1 ≤ n) :
      ∀ (forest : ProfileRefinementForest)
        (hfit : profileRefinementForestFits n k forest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        Function.Injective
          (recursiveProfileForestBoundaryExitWordCode n k center hn hk0 hk
            forest hfit u w)
    | .nil, _hfit, _u, _w => by
        intro left right hout
        apply Subtype.ext
        have hval := congrArg Subtype.val hout
        simpa only [recursiveProfileForestBoundaryExitWordCode] using hval
    | .cons child tail, hfit, u, w => by
        rintro ⟨z, v, inward, childCode, tailCode⟩
          ⟨z', v', inward', childCode', tailCode'⟩ hout
        have hval := congrArg Subtype.val hout
        simp only [recursiveProfileForestBoundaryExitWordCode] at hval
        have hwords := congrArg
          (fun stopped : StoppedWord ↦ List.ofFn stopped.2) hval
        simp only [listStoppedWord_toList] at hwords
        have hchildLeft := recursiveProfileGapBoundaryExitWordCode_val
          n (k + 1) center hn (by omega) child hfit.1 z v childCode
        have hchildLeftList := congrArg
          (fun stopped : StoppedWord ↦ List.ofFn stopped.2) hchildLeft
        simp only [listStoppedWord_toList] at hchildLeftList
        have hchildRight := recursiveProfileGapBoundaryExitWordCode_val
          n (k + 1) center hn (by omega) child hfit.1 z' v' childCode'
        have hchildRightList := congrArg
          (fun stopped : StoppedWord ↦ List.ofFn stopped.2) hchildRight
        simp only [listStoppedWord_toList] at hchildRightList
        have htailLeft := recursiveProfileForestBoundaryExitWordCode_val
          n k center hn hk0 hk tail hfit.2 v w tailCode
        have htailLeftList := congrArg
          (fun stopped : StoppedWord ↦ List.ofFn stopped.2) htailLeft
        simp only [listStoppedWord_toList] at htailLeftList
        have htailRight := recursiveProfileForestBoundaryExitWordCode_val
          n k center hn hk0 hk tail hfit.2 v' w tailCode'
        have htailRightList := congrArg
          (fun stopped : StoppedWord ↦ List.ofFn stopped.2) htailRight
        simp only [listStoppedWord_toList] at htailRightList
        rw [hchildLeftList, hchildRightList, htailLeftList, htailRightList]
          at hwords
        rw [List.append_assoc, List.append_assoc] at hwords
        let InwardCode := Σ z0 : ProfileCycleInnerPoint n k center,
          ProfileInwardWordCode n k center u z0
        let inwardList : InwardCode → List Direction :=
          fun code ↦ List.ofFn code.2.1.2
        have hinwardFree : PrefixFree
            (fun code : InwardCode ↦ listStoppedWord (inwardList code)) := by
          simpa only [InwardCode, inwardList, listStoppedWord_ofFn] using
            prefixFree_sigmaBoundaryExitWordCode
              (fun z0 : ProfileCycleInnerPoint n k center ↦ z0.1)
              (fun _ _ h ↦ Subtype.ext h)
        have hinward : (⟨z, inward⟩ : InwardCode) = ⟨z', inward'⟩ := by
          apply eq_of_prefixes_of_prefixFree inwardList hinwardFree
          simpa only [inwardList] using hwords
        cases hinward
        have hafterInward :
            recursiveProfileGapList n (k + 1) center child z v childCode ++
                recursiveProfileForestList n k center tail v w tailCode =
              recursiveProfileGapList n (k + 1) center child z v' childCode' ++
                recursiveProfileForestList n k center tail v' w tailCode' :=
          List.append_cancel_left hwords
        let ChildCode := Σ v0 : ProfileCycleMiddlePoint n k center,
          RecursiveProfileGapCode n (k + 1) center child z v0
        let childStopped : ChildCode → StoppedWord := fun code ↦
          (recursiveProfileGapBoundaryExitWordCode n (k + 1) center hn
            (by omega) child hfit.1 z code.1 code.2).1
        have hchildStoppedInjective : Function.Injective childStopped := by
          rintro ⟨v0, c0⟩ ⟨v1, c1⟩ hc
          have hc' :
              (recursiveProfileGapBoundaryExitWordCode n (k + 1) center hn
                (by omega) child hfit.1 z v0 c0).1 =
              (recursiveProfileGapBoundaryExitWordCode n (k + 1) center hn
                (by omega) child hfit.1 z v1 c1).1 := by
            simpa only [childStopped] using hc
          have hvPoint : v0.1 = v1.1 := by
            rw [← (recursiveProfileGapBoundaryExitWordCode n (k + 1)
                center hn (by omega) child hfit.1 z v0 c0).2.2,
              ← (recursiveProfileGapBoundaryExitWordCode n (k + 1)
                center hn (by omega) child hfit.1 z v1 c1).2.2,
              hc']
          have hv : v0 = v1 := Subtype.ext hvPoint
          subst v1
          have hcCode : c0 = c1 :=
            recursiveProfileGapBoundaryExitWordCode_injective
              n (k + 1) center hn (by omega) child hfit.1 z v0
                (Subtype.ext hc')
          subst c1
          rfl
        have hchildFreeStopped : PrefixFree childStopped := by
          apply prefixFree_of_boundaryFirst childStopped
            hchildStoppedInjective (profileOuterBoundary n (k + 1) center) z.1
          exact fun code ↦
            (recursiveProfileGapBoundaryExitWordCode n (k + 1) center hn
              (by omega) child hfit.1 z code.1 code.2).2.1
        let childList : ChildCode → List Direction := fun code ↦
          recursiveProfileGapList n (k + 1) center child z code.1 code.2
        have hchildFunctions :
            (fun code : ChildCode ↦ listStoppedWord (childList code)) =
              childStopped := by
          funext code
          exact (recursiveProfileGapBoundaryExitWordCode_val
            n (k + 1) center hn (by omega) child hfit.1 z code.1 code.2).symm
        have hchildFree : PrefixFree
            (fun code : ChildCode ↦ listStoppedWord (childList code)) := by
          rw [hchildFunctions]
          exact hchildFreeStopped
        have hchild : (⟨v, childCode⟩ : ChildCode) =
            ⟨v', childCode'⟩ := by
          apply eq_of_prefixes_of_prefixFree childList hchildFree
          exact hafterInward
        cases hchild
        have htailList :
            recursiveProfileForestList n k center tail v w tailCode =
              recursiveProfileForestList n k center tail v w tailCode' :=
          List.append_cancel_left hafterInward
        have htailStopped :
            (recursiveProfileForestBoundaryExitWordCode n k center hn hk0 hk
              tail hfit.2 v w tailCode).1 =
            (recursiveProfileForestBoundaryExitWordCode n k center hn hk0 hk
              tail hfit.2 v w tailCode').1 := by
          rw [recursiveProfileForestBoundaryExitWordCode_val,
            recursiveProfileForestBoundaryExitWordCode_val]
          exact congrArg listStoppedWord htailList
        have htail : tailCode = tailCode' :=
          recursiveProfileForestBoundaryExitWordCode_injective
            n k center hn hk0 hk tail hfit.2 v w (Subtype.ext htailStopped)
        subst tailCode'
        rfl
end

mutual
  /-- Recursive literal tree codes are countable. -/
  noncomputable def recursiveProfileGapCodeCountable
      (n k : ℕ) (center : Point) :
      ∀ (tree : ProfileRefinementTree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        Countable (RecursiveProfileGapCode n k center tree u w)
    | .leaf, u, w => by
        change Countable (BoundaryExitWordCode
          (profileOuterBoundary n k center) u.1 w.1)
        exact inferInstance
    | .node children, u, w =>
        recursiveProfileForestCodeCountable n k center children u w

  /-- Recursive literal forest codes are countable. -/
  noncomputable def recursiveProfileForestCodeCountable
      (n k : ℕ) (center : Point) :
      ∀ (forest : ProfileRefinementForest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        Countable (RecursiveProfileForestCode n k center forest u w)
    | .nil, u, w => by
        change Countable (ProfileEscapeWordCode n k center u w)
        exact inferInstance
    | .cons child tail, u, w => by
        letI childCountable (z : ProfileCycleInnerPoint n k center)
            (v : ProfileCycleMiddlePoint n k center) :
            Countable (RecursiveProfileGapCode n (k + 1) center child z v) :=
          recursiveProfileGapCodeCountable n (k + 1) center child z v
        letI tailCountable (v : ProfileCycleMiddlePoint n k center) :
            Countable (RecursiveProfileForestCode n k center tail v w) :=
          recursiveProfileForestCodeCountable n k center tail v w
        change Countable (Σ z : ProfileCycleInnerPoint n k center,
          Σ v : ProfileCycleMiddlePoint n k center,
            ProfileInwardWordCode n k center u z ×
              RecursiveProfileGapCode n (k + 1) center child z v ×
                RecursiveProfileForestCode n k center tail v w)
        exact inferInstance
end

/-- The assembled recursive gap words form a prefix-free literal stopped
event.  Injectivity is the structural parsing theorem above; first-boundary
geometry is carried by the assembled `BoundaryExitWordCode`. -/
def recursiveProfileGapStoppedEventCode
    (n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
    (tree : ProfileRefinementTree)
    (hfit : profileRefinementTreeFits n k tree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    StoppedEventCode (stoppedWordEvent (fun code :
      RecursiveProfileGapCode n k center tree u w ↦
        (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree
          hfit u w code).1)) where
  Code := RecursiveProfileGapCode n k center tree u w
  countableCode := recursiveProfileGapCodeCountable n k center tree u w
  word := fun code ↦
    (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree
      hfit u w code).1
  prefixFree_word := by
    apply prefixFree_of_boundaryFirst _
    · intro left right h
      apply recursiveProfileGapBoundaryExitWordCode_injective
        n k center hn hk0 tree hfit u w
      exact Subtype.ext h
    · exact fun code ↦
        (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree
          hfit u w code).2.1
  event_eq := rfl

/-- Exact fair-walk mass of the physical recursive gap event.  Every child
interval is charged once, because the literal word is the chronological
retained-spine/child assembly rather than a product of a full parent word
with a child word. -/
theorem fairSteps_recursiveProfileGapEvent
    (n k : ℕ) (center : Point) (hn : 2 ≤ n) (hk0 : 0 < k)
    (tree : ProfileRefinementTree)
    (hfit : profileRefinementTreeFits n k tree)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center) :
    fairSteps (stoppedWordEvent (fun code :
      RecursiveProfileGapCode n k center tree u w ↦
        (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree
          hfit u w code).1)) =
      recursiveProfileGapKernelENNReal n k center tree u w := by
  rw [(recursiveProfileGapStoppedEventCode n k center hn hk0 tree hfit u w).mass_eq]
  change (∑' code : RecursiveProfileGapCode n k center tree u w,
    stoppedWordMass
      (recursiveProfileGapBoundaryExitWordCode n k center hn hk0 tree
        hfit u w code).1) = _
  calc
    _ = ∑' code : RecursiveProfileGapCode n k center tree u w,
        recursiveProfileGapCodeMass n k center tree u w code := by
      apply tsum_congr
      intro code
      rw [recursiveProfileGapBoundaryExitWordCode_val]
      exact stoppedWordMass_recursiveProfileGapList n k center tree u w code
    _ = recursiveProfileGapKernelENNReal n k center tree u w :=
      tsum_recursiveProfileGapCodeMass n k center tree u w


end Erdos1165.AnnularRecursiveProfileCodeAssembly

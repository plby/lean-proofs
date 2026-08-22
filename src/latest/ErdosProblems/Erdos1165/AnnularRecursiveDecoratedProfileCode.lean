/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularDecoratedProfileCode

/-!
# Recursive erased-parent profile codes

A tree records one profile gap and a forest records its ordered child gaps.
A leaf is an unrestricted first-exit word from the current profile outer
boundary.  An internal node inserts its recursively refined child returns
between the retained inward pieces and final escape.  Thus every physical
child interval appears exactly once.

The code and its kernel are defined by the same mutual recursion.  The exact
`tsum` identity below is the code-level recursive factorization needed by the
concrete asymmetric tail.
-/

open scoped ENNReal

namespace Erdos1165.AnnularRecursiveDecoratedProfileCode

open AnnularDecoratedProfileCode AnnularDecoratedProfileRow
open AnnularOffspringKernelRadial AnnularProfileClocks
open MarkedBoundaryVisitKernel MarkedBridgeFactorization ThickPoint

noncomputable section

mutual
  /-- One recursively refined profile gap. -/
  inductive ProfileRefinementTree : Type
    | leaf : ProfileRefinementTree
    | node (children : ProfileRefinementForest) : ProfileRefinementTree
    deriving Countable

  /-- Ordered child gaps inside one parent gap. -/
  inductive ProfileRefinementForest : Type
    | nil : ProfileRefinementForest
    | cons (head : ProfileRefinementTree) (tail : ProfileRefinementForest) :
        ProfileRefinementForest
    deriving Countable
end

mutual
  /-- Literal recursive code for one profile-gap tree. -/
  def RecursiveProfileGapCode
      (n k : ℕ) (center : Point) :
      ProfileRefinementTree → ProfileCycleMiddlePoint n k center →
        ProfileCycleOuterPoint n k center → Type
    | .leaf, u, w =>
        BoundaryExitWordCode (profileOuterBoundary n k center) u.1 w.1
    | .node children, u, w =>
        RecursiveProfileForestCode n k center children u w

  /-- Literal chronological code for an ordered forest of child gaps. -/
  def RecursiveProfileForestCode
      (n k : ℕ) (center : Point) :
      ProfileRefinementForest → ProfileCycleMiddlePoint n k center →
        ProfileCycleOuterPoint n k center → Type
    | .nil, u, w => ProfileEscapeWordCode n k center u w
    | .cons child tail, u, w =>
        Σ z : ProfileCycleInnerPoint n k center,
          Σ v : ProfileCycleMiddlePoint n k center,
            ProfileInwardWordCode n k center u z ×
              RecursiveProfileGapCode n (k + 1) center child z v ×
                RecursiveProfileForestCode n k center tail v w
end

mutual
  /-- Recursive literal product mass of one gap tree. -/
  def recursiveProfileGapCodeMass
      (n k : ℕ) (center : Point) :
      ∀ (tree : ProfileRefinementTree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        RecursiveProfileGapCode n k center tree u w → ℝ≥0∞
    | .leaf, _u, _w, code => stoppedWordMass code.1
    | .node children, u, w, code =>
        recursiveProfileForestCodeMass n k center children u w code

  /-- Recursive product mass of the retained pieces and child gaps in a
  chronological forest code. -/
  def recursiveProfileForestCodeMass
      (n k : ℕ) (center : Point) :
      ∀ (forest : ProfileRefinementForest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        RecursiveProfileForestCode n k center forest u w → ℝ≥0∞
    | .nil, _u, _w, code => stoppedWordMass code.1
    | .cons child tail, u, w, code =>
        stoppedWordMass code.2.2.1.1 *
          recursiveProfileGapCodeMass n (k + 1) center child
            code.1 code.2.1 code.2.2.2.1 *
          recursiveProfileForestCodeMass n k center tail
            code.2.1 w code.2.2.2.2
end

mutual
  /-- Physical kernel of one recursive gap tree. -/
  def recursiveProfileGapKernelENNReal
      (n k : ℕ) (center : Point) :
      ProfileRefinementTree → ProfileCycleMiddlePoint n k center →
        ProfileCycleOuterPoint n k center → ℝ≥0∞
    | .leaf, u, w =>
        skeletonExitKernel (profileOuterBoundary n k center) u.1 w.1
    | .node children, u, w =>
        recursiveProfileForestKernelENNReal n k center children u w

  /-- Chronological erased-parent kernel for an ordered recursive forest. -/
  def recursiveProfileForestKernelENNReal
      (n k : ℕ) (center : Point) :
      ProfileRefinementForest → ProfileCycleMiddlePoint n k center →
        ProfileCycleOuterPoint n k center → ℝ≥0∞
    | .nil, u, w => profileEscapeKernelENNReal n k center u w
    | .cons child tail, u, w =>
        ∑ z, profileInwardKernelENNReal n k center u z *
          ∑ v, recursiveProfileGapKernelENNReal n (k + 1) center child z v *
            recursiveProfileForestKernelENNReal n k center tail v w
end

private theorem tsum_stoppedWordMass_boundaryExitWordCode
    (boundary : Set Point) (start endpoint : Point) :
    (∑' code : BoundaryExitWordCode boundary start endpoint,
        stoppedWordMass code.1) =
      skeletonExitKernel boundary start endpoint := by
  rw [skeletonExitKernel_eq_canonical]
  symm
  exact (boundaryExitStoppedEventCode boundary start endpoint).mass_eq

mutual
  /-- Exact total literal mass of a fixed recursive gap tree. -/
  theorem tsum_recursiveProfileGapCodeMass
      (n k : ℕ) (center : Point) :
      ∀ (tree : ProfileRefinementTree)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        (∑' code : RecursiveProfileGapCode n k center tree u w,
          recursiveProfileGapCodeMass n k center tree u w code) =
        recursiveProfileGapKernelENNReal n k center tree u w
    | .leaf, u, w =>
        tsum_stoppedWordMass_boundaryExitWordCode
          (profileOuterBoundary n k center) u.1 w.1
    | .node children, u, w =>
        tsum_recursiveProfileForestCodeMass n k center children u w

  /-- Exact total literal mass of a chronological recursive child forest. -/
  theorem tsum_recursiveProfileForestCodeMass
      (n k : ℕ) (center : Point) :
      ∀ (forest : ProfileRefinementForest)
        (u : ProfileCycleMiddlePoint n k center)
        (w : ProfileCycleOuterPoint n k center),
        (∑' code : RecursiveProfileForestCode n k center forest u w,
          recursiveProfileForestCodeMass n k center forest u w code) =
        recursiveProfileForestKernelENNReal n k center forest u w
    | .nil, u, w => by
        simpa only [RecursiveProfileForestCode,
          recursiveProfileForestCodeMass,
          recursiveProfileForestKernelENNReal,
          ProfileEscapeWordCode, profileEscapeKernelENNReal,
          AnnularOffspringKernel.annularEscapeKernel] using
          tsum_stoppedWordMass_boundaryExitWordCode
            (profileInnerBoundary n (k + 1) center ∪
              profileOuterBoundary n k center) u.1 w.1
    | .cons child tail, u, w => by
        rw [recursiveProfileForestKernelENNReal]
        change (∑' code : Σ z : ProfileCycleInnerPoint n k center,
            Σ v : ProfileCycleMiddlePoint n k center,
              ProfileInwardWordCode n k center u z ×
                RecursiveProfileGapCode n (k + 1) center child z v ×
                  RecursiveProfileForestCode n k center tail v w,
          stoppedWordMass code.2.2.1.1 *
            recursiveProfileGapCodeMass n (k + 1) center child
              code.1 code.2.1 code.2.2.2.1 *
            recursiveProfileForestCodeMass n k center tail
              code.2.1 w code.2.2.2.2) = _
        rw [ENNReal.tsum_sigma', tsum_fintype]
        apply Finset.sum_congr rfl
        intro z _hz
        rw [ENNReal.tsum_sigma', tsum_fintype, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _hv
        change (∑' code : ProfileInwardWordCode n k center u z ×
            (RecursiveProfileGapCode n (k + 1) center child z v ×
              RecursiveProfileForestCode n k center tail v w),
          stoppedWordMass code.1.1 *
            recursiveProfileGapCodeMass n (k + 1) center child z v
              code.2.1 *
            recursiveProfileForestCodeMass n k center tail v w
              code.2.2) = _
        rw [ENNReal.tsum_prod']
        calc
          (∑' inward : ProfileInwardWordCode n k center u z,
              ∑' rest : RecursiveProfileGapCode n (k + 1) center child z v ×
                  RecursiveProfileForestCode n k center tail v w,
                stoppedWordMass inward.1 *
                  recursiveProfileGapCodeMass n (k + 1) center child z v
                    rest.1 *
                  recursiveProfileForestCodeMass n k center tail v w
                    rest.2) =
              (∑' inward : ProfileInwardWordCode n k center u z,
                stoppedWordMass inward.1) *
                (∑' rest : RecursiveProfileGapCode n (k + 1) center
                    child z v × RecursiveProfileForestCode n k center
                      tail v w,
                  recursiveProfileGapCodeMass n (k + 1) center child z v
                    rest.1 *
                  recursiveProfileForestCodeMass n k center tail v w
                    rest.2) := by
                calc
                  _ = ∑' inward : ProfileInwardWordCode n k center u z,
                      stoppedWordMass inward.1 *
                        (∑' rest : RecursiveProfileGapCode n (k + 1) center
                            child z v × RecursiveProfileForestCode n k center
                              tail v w,
                          recursiveProfileGapCodeMass n (k + 1) center
                              child z v rest.1 *
                            recursiveProfileForestCodeMass n k center tail
                              v w rest.2) := by
                        apply tsum_congr
                        intro inward
                        calc
                          _ = ∑' rest : RecursiveProfileGapCode n (k + 1)
                                center child z v ×
                              RecursiveProfileForestCode n k center tail v w,
                              stoppedWordMass inward.1 *
                                (recursiveProfileGapCodeMass n (k + 1)
                                    center child z v rest.1 *
                                  recursiveProfileForestCodeMass n k center
                                    tail v w rest.2) := by
                                  apply tsum_congr
                                  intro rest
                                  ac_rfl
                          _ = _ := ENNReal.tsum_mul_left
                  _ = _ := ENNReal.tsum_mul_right
          _ = profileInwardKernelENNReal n k center u z *
                (∑' rest : RecursiveProfileGapCode n (k + 1) center
                    child z v × RecursiveProfileForestCode n k center
                      tail v w,
                  recursiveProfileGapCodeMass n (k + 1) center child z v
                    rest.1 *
                  recursiveProfileForestCodeMass n k center tail v w
                    rest.2) := by
                rw [show (∑' inward : ProfileInwardWordCode n k center u z,
                    stoppedWordMass inward.1) =
                    profileInwardKernelENNReal n k center u z by
                  simpa only [ProfileInwardWordCode,
                    profileInwardKernelENNReal] using
                    tsum_stoppedWordMass_boundaryExitWordCode
                      (profileInnerBoundary n (k + 1) center ∪
                        profileOuterBoundary n k center) u.1 z.1]
          _ = profileInwardKernelENNReal n k center u z *
                ((∑' childCode : RecursiveProfileGapCode n (k + 1)
                    center child z v,
                    recursiveProfileGapCodeMass n (k + 1) center child z v
                      childCode) *
                  (∑' tailCode : RecursiveProfileForestCode n k center
                      tail v w,
                    recursiveProfileForestCodeMass n k center tail v w
                      tailCode)) := by
                congr 1
                rw [ENNReal.tsum_prod']
                calc
                  _ = ∑' childCode : RecursiveProfileGapCode n (k + 1)
                        center child z v,
                      recursiveProfileGapCodeMass n (k + 1) center child z v
                        childCode *
                        (∑' tailCode : RecursiveProfileForestCode n k center
                            tail v w,
                          recursiveProfileForestCodeMass n k center tail v w
                            tailCode) := by
                          apply tsum_congr
                          intro childCode
                          simpa only [Prod.fst, Prod.snd] using
                            (ENNReal.tsum_mul_left :
                              (∑' tailCode : RecursiveProfileForestCode n k
                                  center tail v w,
                                recursiveProfileGapCodeMass n (k + 1) center
                                    child z v childCode *
                                  recursiveProfileForestCodeMass n k center
                                    tail v w tailCode) =
                                recursiveProfileGapCodeMass n (k + 1) center
                                    child z v childCode *
                                  ∑' tailCode : RecursiveProfileForestCode n k
                                    center tail v w,
                                    recursiveProfileForestCodeMass n k center
                                      tail v w tailCode)
                  _ = _ := ENNReal.tsum_mul_right
          _ = profileInwardKernelENNReal n k center u z *
                (recursiveProfileGapKernelENNReal n (k + 1) center
                    child z v *
                  recursiveProfileForestKernelENNReal n k center
                    tail v w) := by
                rw [tsum_recursiveProfileGapCodeMass,
                  tsum_recursiveProfileForestCodeMass]
end

end

end Erdos1165.AnnularRecursiveDecoratedProfileCode

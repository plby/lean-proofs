/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedRemoteRenewal
import ErdosProblems.Erdos1165.AnnularRecursiveProfileCodeAssembly

/-!
# Literal codes for the padded multi-bridge renewal

The analytic padded renewal is a finite recursion of first-boundary kernels.
This file supplies the matching literal code space.  A code records, in
chronological order, whether a pending coarse bridge exits directly or first
enters the padded predecessor boundary, and whether an active bridge escapes
or consumes the next recursively decorated child.

The total stopped-word product mass of the code space is exactly
`heterogeneousPreludeMultiRenewalKernel`.  Keeping this literal code is what
allows a successful coarse tuple to be injected into the padded row without
duplicating its mass when the retained profile prefix is summed out.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricPaddedPreludeCode

open AnnularBoundaryExcursionKernel AnnularOffspringKernel
open AnnularProfileClocks AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileCodeAssembly AlternatingConcatPrefixFree
open AnnularRecursiveWeightedRenewal AsymmetricPaddedRemoteRenewal
open MarkedBoundaryVisitKernel MarkedBridgeFactorization ThickPoint

noncomputable section

private def paddedPreludeCodeWeight {Near Middle Exit : Type*} :
    List ((Near ⊕ Middle) × Exit) → ℕ
  | [] => 0
  | (Sum.inl _, _) :: rest => 2 + paddedPreludeCodeWeight rest
  | (Sum.inr _, _) :: rest => 1 + paddedPreludeCodeWeight rest

/-- Literal choices in the preliminary-entrance, multi-segment padded
renewal.  The five boundary-word fields correspond exactly to the five
kernels in `heterogeneousPreludeMultiRenewalKernel`. -/
inductive PaddedPreludeMultiCode
    (n l p : ℕ) (center : Point) :
    List ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
      PaddedOuterPoint n l center) →
    List ProfileRefinementTree → Type
  | done : PaddedPreludeMultiCode n l p center [] []
  | pendingDirect {start w segments trees}
      (first : BoundaryExitWordCode
        (profileInnerBoundary n (p - 1) center ∪
          profileInnerBoundary n l center) start.1 w.1)
      (rest : PaddedPreludeMultiCode n l p center segments trees) :
      PaddedPreludeMultiCode n l p center
        ((Sum.inl start, w) :: segments) trees
  | pendingEnter {start w segments trees}
      (u : PaddedMiddlePoint n p center)
      (first : BoundaryExitWordCode
        (profileInnerBoundary n (p - 1) center ∪
          profileInnerBoundary n l center) start.1 u.1)
      (rest : PaddedPreludeMultiCode n l p center
        ((Sum.inr u, w) :: segments) trees) :
      PaddedPreludeMultiCode n l p center
        ((Sum.inl start, w) :: segments) trees
  | activeEscapeDone {u w segments}
      (first : BoundaryExitWordCode
        (profileInnerBoundary n p center ∪
          profileInnerBoundary n l center) u.1 w.1)
      (rest : PaddedPreludeMultiCode n l p center segments []) :
      PaddedPreludeMultiCode n l p center
        ((Sum.inr u, w) :: segments) []
  | activeEscape {u w segments tree trees}
      (first : BoundaryExitWordCode
        (profileInnerBoundary n p center ∪
          profileInnerBoundary n l center) u.1 w.1)
      (rest : PaddedPreludeMultiCode n l p center segments (tree :: trees)) :
      PaddedPreludeMultiCode n l p center
        ((Sum.inr u, w) :: segments) (tree :: trees)
  | activeChild {u w segments tree trees}
      (z : PaddedInnerPoint n p center)
      (v : PaddedMiddlePoint n p center)
      (first : BoundaryExitWordCode
        (profileInnerBoundary n p center ∪
          profileInnerBoundary n l center) u.1 z.1)
      (child : RecursiveProfileGapCode n p center tree z v)
      (rest : PaddedPreludeMultiCode n l p center
        ((Sum.inr v, w) :: segments) trees) :
      PaddedPreludeMultiCode n l p center
        ((Sum.inr u, w) :: segments) (tree :: trees)

/-- Product of the literal stopped-word masses in a padded prelude code. -/
def paddedPreludeMultiCodeMass
    (n l p : ℕ) (center : Point) :
    {segments : List
      ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center)} →
    {trees : List ProfileRefinementTree} →
      PaddedPreludeMultiCode n l p center segments trees → ℝ≥0∞
  | _, _, .done => 1
  | _, _, .pendingDirect first rest =>
      stoppedWordMass first.1 * paddedPreludeMultiCodeMass n l p center rest
  | _, _, .pendingEnter _ first rest =>
      stoppedWordMass first.1 * paddedPreludeMultiCodeMass n l p center rest
  | _, _, .activeEscapeDone first rest =>
      stoppedWordMass first.1 * paddedPreludeMultiCodeMass n l p center rest
  | _, _, .activeEscape first rest =>
      stoppedWordMass first.1 * paddedPreludeMultiCodeMass n l p center rest
  | _, _, .activeChild z v first child rest =>
      stoppedWordMass first.1 *
        recursiveProfileGapCodeMass n p center _ z v child *
          paddedPreludeMultiCodeMass n l p center rest

private def doneCodeEquiv (n l p : ℕ) (center : Point) :
    PaddedPreludeMultiCode n l p center [] [] ≃ Unit where
  toFun := fun _ => ()
  invFun := fun _ => .done
  left_inv := by intro code; cases code; rfl
  right_inv := by intro x; cases x; rfl

private def pendingCodeEquiv
    (n l p : ℕ) (center : Point)
    (start : PaddedNearPoint n l center)
    (w : PaddedOuterPoint n l center)
    (segments : List
      ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center))
    (trees : List ProfileRefinementTree) :
    PaddedPreludeMultiCode n l p center
        ((Sum.inl start, w) :: segments) trees ≃
      (BoundaryExitWordCode
          (profileInnerBoundary n (p - 1) center ∪
            profileInnerBoundary n l center) start.1 w.1 ×
        PaddedPreludeMultiCode n l p center segments trees) ⊕
      (Σ u : PaddedMiddlePoint n p center,
        BoundaryExitWordCode
            (profileInnerBoundary n (p - 1) center ∪
              profileInnerBoundary n l center) start.1 u.1 ×
          PaddedPreludeMultiCode n l p center
            ((Sum.inr u, w) :: segments) trees) where
  toFun
    | .pendingDirect first rest => .inl (first, rest)
    | .pendingEnter u first rest => .inr ⟨u, first, rest⟩
  invFun
    | .inl (first, rest) => .pendingDirect first rest
    | .inr ⟨u, first, rest⟩ => .pendingEnter u first rest
  left_inv := by intro code; cases code <;> rfl
  right_inv := by rintro (code | ⟨u, first, rest⟩) <;> rfl

private def activeDoneCodeEquiv
    (n l p : ℕ) (center : Point)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (segments : List
      ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center)) :
    PaddedPreludeMultiCode n l p center
        ((Sum.inr u, w) :: segments) [] ≃
      BoundaryExitWordCode
          (profileInnerBoundary n p center ∪
            profileInnerBoundary n l center) u.1 w.1 ×
        PaddedPreludeMultiCode n l p center segments [] where
  toFun
    | .activeEscapeDone first rest => (first, rest)
  invFun
    | (first, rest) => .activeEscapeDone first rest
  left_inv := by intro code; cases code; rfl
  right_inv := by rintro ⟨first, rest⟩; rfl

private def activeCodeEquiv
    (n l p : ℕ) (center : Point)
    (u : PaddedMiddlePoint n p center)
    (w : PaddedOuterPoint n l center)
    (segments : List
      ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center))
    (tree : ProfileRefinementTree) (trees : List ProfileRefinementTree) :
    PaddedPreludeMultiCode n l p center
        ((Sum.inr u, w) :: segments) (tree :: trees) ≃
      (BoundaryExitWordCode
          (profileInnerBoundary n p center ∪
            profileInnerBoundary n l center) u.1 w.1 ×
        PaddedPreludeMultiCode n l p center segments (tree :: trees)) ⊕
      (Σ z : PaddedInnerPoint n p center,
        Σ v : PaddedMiddlePoint n p center,
          BoundaryExitWordCode
              (profileInnerBoundary n p center ∪
                profileInnerBoundary n l center) u.1 z.1 ×
            RecursiveProfileGapCode n p center tree z v ×
              PaddedPreludeMultiCode n l p center
                ((Sum.inr v, w) :: segments) trees) where
  toFun
    | .activeEscape first rest => .inl (first, rest)
    | .activeChild z v first child rest =>
        .inr ⟨z, v, first, child, rest⟩
  invFun
    | .inl (first, rest) => .activeEscape first rest
    | .inr ⟨z, v, first, child, rest⟩ =>
        .activeChild z v first child rest
  left_inv := by intro code; cases code <;> rfl
  right_inv := by
    rintro (code | ⟨z, v, first, child, rest⟩) <;> rfl

private theorem ennreal_tsum_sum {A B : Type}
    (f : A ⊕ B → ℝ≥0∞) :
    (∑' x, f x) = (∑' a, f (.inl a)) + ∑' b, f (.inr b) := by
  let e := Equiv.sumEquivSigmaBool A B
  calc
    (∑' x, f x) =
        ∑' q : (Σ b : Bool, bif b then B else A), f (e.symm q) := by
          exact (Equiv.tsum_eq e.symm f).symm
    _ = ∑' b : Bool, ∑' x : bif b then B else A,
          f (e.symm ⟨b, x⟩) := ENNReal.tsum_sigma' _
    _ = (∑' a, f (.inl a)) + ∑' b, f (.inr b) := by
      rw [tsum_fintype]
      simp [e, Equiv.sumEquivSigmaBool, add_comm]

private theorem ennreal_tsum_product {A B : Type}
    (f : A → ℝ≥0∞) (g : B → ℝ≥0∞) :
    (∑' q : A × B, f q.1 * g q.2) = (∑' a, f a) * ∑' b, g b := by
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_left]
  exact ENNReal.tsum_mul_right

private theorem ennreal_tsum_tripleProduct {A B C : Type}
    (f : A → ℝ≥0∞) (g : B → ℝ≥0∞) (h : C → ℝ≥0∞) :
    (∑' q : A × (B × C), f q.1 * g q.2.1 * h q.2.2) =
      (∑' a, f a) * (∑' b, g b) * ∑' c, h c := by
  calc
    _ = ∑' q : A × (B × C), f q.1 * (g q.2.1 * h q.2.2) := by
      apply tsum_congr
      intro q
      ac_rfl
    _ = (∑' a, f a) * ∑' q : B × C, g q.1 * h q.2 :=
      ennreal_tsum_product f (fun q : B × C ↦ g q.1 * h q.2)
    _ = _ := by rw [ennreal_tsum_product, mul_assoc]

private theorem tsum_boundaryExitWordMass
    (boundary : Set Point) (start endpoint : Point) :
    (∑' code : BoundaryExitWordCode boundary start endpoint,
      stoppedWordMass code.1) = skeletonExitKernel boundary start endpoint := by
  rw [skeletonExitKernel_eq_canonical]
  symm
  exact (boundaryExitStoppedEventCode boundary start endpoint).mass_eq

/-- Exact Tonelli expansion of the padded prelude recursion into literal
first-boundary and recursive-child codes. -/
theorem tsum_paddedPreludeMultiCodeMass_eq
    (n l p : ℕ) (center : Point) :
    ∀ (segments : List
        ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
          PaddedOuterPoint n l center))
      (trees : List ProfileRefinementTree),
      (∑' code : PaddedPreludeMultiCode n l p center segments trees,
        paddedPreludeMultiCodeMass n l p center code) =
      heterogeneousPreludeMultiRenewalKernel
        (paddedPreludeEntryKernelENNReal n l p center)
        (paddedPreludeDirectKernelENNReal n l p center)
        (paddedInwardKernelENNReal n l p center)
        (recursiveProfileGapKernelENNReal n p center)
        (paddedEscapeKernelENNReal n l p center) segments trees
  | [], [] => by
      calc
        (∑' code : PaddedPreludeMultiCode n l p center [] [],
            paddedPreludeMultiCodeMass n l p center code) =
            ∑' x : Unit, paddedPreludeMultiCodeMass n l p center
              ((doneCodeEquiv n l p center).symm x) := by
                exact (Equiv.tsum_eq (doneCodeEquiv n l p center).symm
                  (paddedPreludeMultiCodeMass n l p center)).symm
        _ = 1 := by simp [doneCodeEquiv, paddedPreludeMultiCodeMass]
        _ = _ := by rw [heterogeneousPreludeMultiRenewalKernel]
  | [], _tree :: _rest => by
      rw [heterogeneousPreludeMultiRenewalKernel]
      let : IsEmpty (PaddedPreludeMultiCode n l p center [] (_tree :: _rest)) :=
        ⟨fun code => nomatch code⟩
      exact tsum_empty
  | (Sum.inl start, w) :: segments, trees => by
      rw [show (∑' code : PaddedPreludeMultiCode n l p center
          ((Sum.inl start, w) :: segments) trees,
          paddedPreludeMultiCodeMass n l p center code) =
          (∑' code : BoundaryExitWordCode
              (profileInnerBoundary n (p - 1) center ∪
                profileInnerBoundary n l center) start.1 w.1 ×
                PaddedPreludeMultiCode n l p center segments trees,
            stoppedWordMass code.1.1 *
              paddedPreludeMultiCodeMass n l p center code.2) +
          ∑' code : Σ u : PaddedMiddlePoint n p center,
              BoundaryExitWordCode
                (profileInnerBoundary n (p - 1) center ∪
                  profileInnerBoundary n l center) start.1 u.1 ×
                PaddedPreludeMultiCode n l p center
                  ((Sum.inr u, w) :: segments) trees,
            stoppedWordMass code.2.1.1 *
              paddedPreludeMultiCodeMass n l p center code.2.2 by
        calc
          _ = ∑' choice, paddedPreludeMultiCodeMass n l p center
                ((pendingCodeEquiv n l p center start w segments trees).symm
                  choice) := by
              exact (Equiv.tsum_eq
                (pendingCodeEquiv n l p center start w segments trees).symm
                (paddedPreludeMultiCodeMass n l p center)).symm
          _ = _ := by
            rw [ennreal_tsum_sum]
            rfl]
      rw [ENNReal.tsum_prod', ENNReal.tsum_sigma']
      simp_rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right]
      simp_rw [ENNReal.tsum_mul_right]
      rw [tsum_boundaryExitWordMass]
      simp_rw [tsum_boundaryExitWordMass]
      rw [tsum_paddedPreludeMultiCodeMass_eq n l p center segments trees]
      rw [heterogeneousPreludeMultiRenewalKernel]
      simp only [paddedPreludeDirectKernelENNReal,
        paddedPreludeEntryKernelENNReal]
      congr 1
      calc
        _ = ∑' middle : PaddedMiddlePoint n p center,
              skeletonExitKernel
                  (profileInnerBoundary n (p - 1) center ∪
                    profileInnerBoundary n l center) start.1 middle.1 *
                heterogeneousPreludeMultiRenewalKernel
                  (paddedPreludeEntryKernelENNReal n l p center)
                  (paddedPreludeDirectKernelENNReal n l p center)
                  (paddedInwardKernelENNReal n l p center)
                  (recursiveProfileGapKernelENNReal n p center)
                  (paddedEscapeKernelENNReal n l p center)
                  ((Sum.inr middle, w) :: segments) trees := by
            apply tsum_congr
            intro middle
            rw [tsum_paddedPreludeMultiCodeMass_eq n l p center
              ((Sum.inr middle, w) :: segments) trees]
        _ = _ := tsum_fintype _
  | (Sum.inr u, w) :: segments, [] => by
      rw [show (∑' code : PaddedPreludeMultiCode n l p center
          ((Sum.inr u, w) :: segments) [],
          paddedPreludeMultiCodeMass n l p center code) =
          ∑' code : BoundaryExitWordCode
              (profileInnerBoundary n p center ∪
                profileInnerBoundary n l center) u.1 w.1 ×
                PaddedPreludeMultiCode n l p center segments [],
            stoppedWordMass code.1.1 *
              paddedPreludeMultiCodeMass n l p center code.2 by
        exact (Equiv.tsum_eq
          (activeDoneCodeEquiv n l p center u w segments).symm
          (paddedPreludeMultiCodeMass n l p center)).symm]
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right,
        tsum_boundaryExitWordMass,
        tsum_paddedPreludeMultiCodeMass_eq n l p center]
      rw [heterogeneousPreludeMultiRenewalKernel]
      rfl
  | (Sum.inr u, w) :: segments, tree :: rest => by
      rw [show (∑' code : PaddedPreludeMultiCode n l p center
          ((Sum.inr u, w) :: segments) (tree :: rest),
          paddedPreludeMultiCodeMass n l p center code) =
          (∑' code : BoundaryExitWordCode
              (profileInnerBoundary n p center ∪
                profileInnerBoundary n l center) u.1 w.1 ×
                PaddedPreludeMultiCode n l p center segments (tree :: rest),
            stoppedWordMass code.1.1 *
              paddedPreludeMultiCodeMass n l p center code.2) +
          ∑' code : Σ z : PaddedInnerPoint n p center,
              Σ v : PaddedMiddlePoint n p center,
                BoundaryExitWordCode
                    (profileInnerBoundary n p center ∪
                      profileInnerBoundary n l center) u.1 z.1 ×
                  RecursiveProfileGapCode n p center tree z v ×
                    PaddedPreludeMultiCode n l p center
                      ((Sum.inr v, w) :: segments) rest,
            stoppedWordMass code.2.2.1.1 *
              recursiveProfileGapCodeMass n p center tree code.1 code.2.1
                code.2.2.2.1 *
              paddedPreludeMultiCodeMass n l p center code.2.2.2.2 by
        calc
          _ = ∑' choice, paddedPreludeMultiCodeMass n l p center
                ((activeCodeEquiv n l p center u w segments tree rest).symm
                  choice) := by
              exact (Equiv.tsum_eq
                (activeCodeEquiv n l p center u w segments tree rest).symm
                (paddedPreludeMultiCodeMass n l p center)).symm
          _ = _ := by
            rw [ennreal_tsum_sum]
            rfl]
      rw [ENNReal.tsum_prod', ENNReal.tsum_sigma']
      simp_rw [ENNReal.tsum_sigma']
      simp_rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right]
      simp_rw [ENNReal.tsum_mul_right]
      simp_rw [ENNReal.tsum_mul_left]
      simp_rw [ENNReal.tsum_mul_right]
      rw [tsum_boundaryExitWordMass]
      simp_rw [tsum_boundaryExitWordMass]
      simp_rw [tsum_recursiveProfileGapCodeMass]
      rw [tsum_paddedPreludeMultiCodeMass_eq n l p center
        segments (tree :: rest)]
      rw [heterogeneousPreludeMultiRenewalKernel]
      simp only [paddedEscapeKernelENNReal, paddedInwardKernelENNReal]
      congr 1
      calc
        _ = ∑' z : PaddedInnerPoint n p center,
              ∑' v : PaddedMiddlePoint n p center,
                skeletonExitKernel
                    (profileInnerBoundary n p center ∪
                      profileInnerBoundary n l center) u.1 z.1 *
                  recursiveProfileGapKernelENNReal n p center tree z v *
                    heterogeneousPreludeMultiRenewalKernel
                      (paddedPreludeEntryKernelENNReal n l p center)
                      (paddedPreludeDirectKernelENNReal n l p center)
                      (paddedInwardKernelENNReal n l p center)
                      (recursiveProfileGapKernelENNReal n p center)
                      (paddedEscapeKernelENNReal n l p center)
                      ((Sum.inr v, w) :: segments) rest := by
            apply tsum_congr
            intro z
            apply tsum_congr
            intro v
            rw [tsum_paddedPreludeMultiCodeMass_eq n l p center
              ((Sum.inr v, w) :: segments) rest]
        _ = ∑ z : PaddedInnerPoint n p center,
              ∑ v : PaddedMiddlePoint n p center,
                skeletonExitKernel
                    (profileInnerBoundary n p center ∪
                      profileInnerBoundary n l center) u.1 z.1 *
                  recursiveProfileGapKernelENNReal n p center tree z v *
                    heterogeneousPreludeMultiRenewalKernel
                      (paddedPreludeEntryKernelENNReal n l p center)
                      (paddedPreludeDirectKernelENNReal n l p center)
                      (paddedInwardKernelENNReal n l p center)
                      (recursiveProfileGapKernelENNReal n p center)
                      (paddedEscapeKernelENNReal n l p center)
                      ((Sum.inr v, w) :: segments) rest := by
            rw [tsum_fintype]
            simp_rw [tsum_fintype]
        _ = _ := by
            apply Finset.sum_congr rfl
            intro z _hz
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro v _hv
            simp only [mul_assoc, paddedEscapeKernelENNReal]
termination_by segments trees =>
  paddedPreludeCodeWeight segments + trees.length
decreasing_by
  all_goals simp [paddedPreludeCodeWeight]

/-! ## Literal assembly of a padded code -/

/-- Prepend a finite word to the first word of a nonempty chronological
segment list.  The empty case is included only to keep the operation total;
the indexed padded code never uses it there. -/
def prependHead (pre : List Direction) :
    List (List Direction) → List (List Direction)
  | [] => [pre]
  | word :: rest => (pre ++ word) :: rest

@[simp] theorem prependHead_prependHead
    (left right : List Direction) (words : List (List Direction)) :
    prependHead left (prependHead right words) =
      prependHead (left ++ right) words := by
  cases words <;> simp [prependHead, List.append_assoc]

/-- The chronological coarse bridge words assembled by a padded prelude
code.  Transition constructors extend the current segment, whereas escape
and direct-exit constructors finish it. -/
def paddedPreludeMultiCodeWords
    (n l p : ℕ) (center : Point) :
    {segments : List
      ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center)} →
    {trees : List ProfileRefinementTree} →
      PaddedPreludeMultiCode n l p center segments trees →
        List (List Direction)
  | _, _, .done => []
  | _, _, .pendingDirect first rest =>
      List.ofFn first.1.2 :: paddedPreludeMultiCodeWords n l p center rest
  | _, _, .pendingEnter _ first rest =>
      prependHead (List.ofFn first.1.2)
        (paddedPreludeMultiCodeWords n l p center rest)
  | _, _, .activeEscapeDone first rest =>
      List.ofFn first.1.2 :: paddedPreludeMultiCodeWords n l p center rest
  | _, _, .activeEscape first rest =>
      List.ofFn first.1.2 :: paddedPreludeMultiCodeWords n l p center rest
  | _, _, .activeChild z v first child rest =>
      prependHead
        (List.ofFn first.1.2 ++
          AnnularRecursiveProfileCodeAssembly.recursiveProfileGapList
            n p center _ z v child)
        (paddedPreludeMultiCodeWords n l p center rest)

theorem paddedPreludeMultiCodeWords_length
    (n l p : ℕ) (center : Point) :
    ∀ {segments : List
        ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
          PaddedOuterPoint n l center)}
      {trees : List ProfileRefinementTree}
      (code : PaddedPreludeMultiCode n l p center segments trees),
      (paddedPreludeMultiCodeWords n l p center code).length = segments.length
  | _, _, .done => rfl
  | _, _, .pendingDirect first rest => by
      simp only [paddedPreludeMultiCodeWords, List.length_cons,
        paddedPreludeMultiCodeWords_length n l p center rest]
  | _, _, .pendingEnter u first rest => by
      have hrest := paddedPreludeMultiCodeWords_length n l p center rest
      simp only [List.length_cons] at hrest ⊢
      unfold paddedPreludeMultiCodeWords
      cases hwords : paddedPreludeMultiCodeWords n l p center rest with
      | nil => simp_all
      | cons word words =>
          simp only [prependHead, List.length_cons]
          simp only [hwords, List.length_cons] at hrest
          omega
  | _, _, .activeEscapeDone first rest => by
      simp only [paddedPreludeMultiCodeWords, List.length_cons,
        paddedPreludeMultiCodeWords_length n l p center rest]
  | _, _, .activeEscape first rest => by
      simp only [paddedPreludeMultiCodeWords, List.length_cons,
        paddedPreludeMultiCodeWords_length n l p center rest]
  | _, _, .activeChild z v first child rest => by
      have hrest := paddedPreludeMultiCodeWords_length n l p center rest
      simp only [List.length_cons] at hrest ⊢
      unfold paddedPreludeMultiCodeWords
      cases hwords : paddedPreludeMultiCodeWords n l p center rest with
      | nil => simp_all
      | cons word words =>
          simp only [prependHead, List.length_cons]
          simp only [hwords, List.length_cons] at hrest
          omega

/-- Product of stopped-word masses of a chronological list of direction
words. -/
def stoppedWordListMass (words : List (List Direction)) : ℝ≥0∞ :=
  (words.map fun word ↦ stoppedWordMass (listStoppedWord word)).prod

private theorem stoppedWordListMass_prependHead
    (pre : List Direction) (words : List (List Direction))
    (hwords : words ≠ []) :
    stoppedWordListMass (prependHead pre words) =
      stoppedWordMass (listStoppedWord pre) * stoppedWordListMass words := by
  cases words with
  | nil => exact (hwords rfl).elim
  | cons word rest =>
      simp only [prependHead, stoppedWordListMass, List.map_cons,
        List.prod_cons]
      rw [AnnularRecursiveProfileCodeAssembly.stoppedWordMass_listStoppedWord_append]
      ac_rfl

/-- The product mass recorded by a padded code is exactly the product mass
of its assembled coarse bridge words. -/
theorem paddedPreludeMultiCodeMass_eq_words
    (n l p : ℕ) (center : Point) :
    ∀ {segments : List
        ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
          PaddedOuterPoint n l center)}
      {trees : List ProfileRefinementTree}
      (code : PaddedPreludeMultiCode n l p center segments trees),
      paddedPreludeMultiCodeMass n l p center code =
        stoppedWordListMass
          (paddedPreludeMultiCodeWords n l p center code)
  | _, _, .done => rfl
  | _, _, .pendingDirect first rest => by
      simp only [paddedPreludeMultiCodeMass, paddedPreludeMultiCodeWords,
        stoppedWordListMass, List.map_cons, List.prod_cons,
        listStoppedWord_ofFn,
        paddedPreludeMultiCodeMass_eq_words n l p center rest]
  | _, _, .pendingEnter u first rest => by
      rw [paddedPreludeMultiCodeMass, paddedPreludeMultiCodeWords,
        paddedPreludeMultiCodeMass_eq_words n l p center rest,
        stoppedWordListMass_prependHead]
      · simp only [listStoppedWord_ofFn]
      · intro hnil
        have hlen := paddedPreludeMultiCodeWords_length n l p center rest
        rw [hnil] at hlen
        simp at hlen
  | _, _, .activeEscapeDone first rest => by
      simp only [paddedPreludeMultiCodeMass, paddedPreludeMultiCodeWords,
        stoppedWordListMass, List.map_cons, List.prod_cons,
        listStoppedWord_ofFn,
        paddedPreludeMultiCodeMass_eq_words n l p center rest]
  | _, _, .activeEscape first rest => by
      simp only [paddedPreludeMultiCodeMass, paddedPreludeMultiCodeWords,
        stoppedWordListMass, List.map_cons, List.prod_cons,
        listStoppedWord_ofFn,
        paddedPreludeMultiCodeMass_eq_words n l p center rest]
  | _, _, .activeChild z v first child rest => by
      rw [paddedPreludeMultiCodeMass, paddedPreludeMultiCodeWords,
        paddedPreludeMultiCodeMass_eq_words n l p center rest,
        stoppedWordListMass_prependHead]
      · rw [AnnularRecursiveProfileCodeAssembly.stoppedWordMass_listStoppedWord_append,
          listStoppedWord_ofFn,
          AnnularRecursiveProfileCodeAssembly.stoppedWordMass_recursiveProfileGapList]
      · intro hnil
        have hlen := paddedPreludeMultiCodeWords_length n l p center rest
        rw [hnil] at hlen
        simp at hlen

end

end Erdos1165.AsymmetricPaddedPreludeCode

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Basic semantic objects for Erdős Problem 260

The paper uses `ℕ = {1, 2, ...}`.  Lean's natural numbers include zero, so the
weighted support term is defined to be zero at index zero.  Dyadic blocks use
the paper's half-open convention `(X, 2X]`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos260

/-- Binary entropy, in base two.  It lives in the basic layer because the
fixed entropy-parameter hierarchy is part of every coherent scale family. -/
def binaryEntropy (x : ℝ) : ℝ :=
  -x * Real.logb 2 x - (1 - x) * Real.logb 2 (1 - x)

/-- The binary digit associated with a support set. -/
def digit (S : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact if n ∈ S then 1 else 0

/-- The `n`th summand of the weighted binary support series. -/
def weightedSupportTerm (S : Set ℕ) (n : ℕ) : ℝ :=
  by
    classical
    exact if n ∈ S then (n : ℝ) / (2 : ℝ) ^ n else 0

/-- The weighted binary expansion attached to a support set. -/
def weightedBinarySeries (S : Set ℕ) : ℝ :=
  ∑' n : ℕ, weightedSupportTerm S n

/-- Removing the zero index turns an arbitrary support into the paper's
positive support without changing any weighted summand. -/
def positiveSupport (S : Set ℕ) : Set ℕ :=
  {n | n ∈ S ∧ 0 < n}

@[simp]
theorem weightedSupportTerm_positiveSupport (S : Set ℕ) (n : ℕ) :
    weightedSupportTerm (positiveSupport S) n = weightedSupportTerm S n := by
  by_cases hn : n = 0
  · subst n
    simp [weightedSupportTerm, positiveSupport]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    by_cases hmem : n ∈ S
    · simp [weightedSupportTerm, positiveSupport, hnpos, hmem]
    · simp [weightedSupportTerm, positiveSupport, hmem]

theorem positiveSupport_infinite {S : Set ℕ} (hS : S.Infinite) :
    (positiveSupport S).Infinite := by
  have heq : positiveSupport S = S \ ({0} : Set ℕ) := by
    ext n
    simp [positiveSupport, Nat.pos_iff_ne_zero]
  have hdiff : (S \ ({0} : Set ℕ)).Infinite :=
    hS.sdiff (Set.finite_singleton 0)
  simpa [heq] using hdiff

/-- Number of support points in `[1, X]`. -/
def supportCount (S : Set ℕ) (X : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 X).filter fun n => n ∈ S).card

/-- Number of support points in the paper's block `(X, 2X]`. -/
def dyadicBlockCount (S : Set ℕ) (X : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Ioc X (2 * X)).filter fun n => n ∈ S).card

@[simp]
theorem dyadicBlockCount_positiveSupport (S : Set ℕ) (X : ℕ) :
    dyadicBlockCount (positiveSupport S) X = dyadicBlockCount S X := by
  classical
  unfold dyadicBlockCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, positiveSupport,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hIoc, hS, _⟩
    exact ⟨hIoc, hS⟩
  · rintro ⟨hIoc, hS⟩
    exact ⟨hIoc, hS, lt_of_le_of_lt (Nat.zero_le X) hIoc.1⟩

/-- The dyadic scale `X = 2^L`. -/
def dyadicScale (L : ℕ) : ℕ := 2 ^ L

/-- A strictly increasing positive enumeration of an infinite support set. -/
structure SupportEnumeration (S : Set ℕ) where
  a : ℕ → ℕ
  strictMono : StrictMono a
  positive : ∀ n, 0 < a n
  range_eq : Set.range a = S

/-- The canonical increasing enumeration of an infinite positive support. -/
def supportEnumerationOfInfinite (S : Set ℕ) (hInfinite : S.Infinite)
    (hPositive : ∀ n ∈ S, 0 < n) : SupportEnumeration S where
  a := Nat.nth fun n => n ∈ S
  strictMono := by
    apply Nat.nth_strictMono
    simpa only [Set.setOf_mem_eq] using hInfinite
  positive := by
    intro k
    apply hPositive _
    apply Nat.nth_mem_of_infinite
    simpa only [Set.setOf_mem_eq] using hInfinite
  range_eq := by
    apply Nat.range_nth_of_infinite
    simpa only [Set.setOf_mem_eq] using hInfinite

/-- Consecutive gap in a support enumeration. -/
def supportGap {S : Set ℕ} (e : SupportEnumeration S) (k : ℕ) : ℕ :=
  e.a (k + 1) - e.a k

/-- A gap word is an ordered finite list of natural-number gaps. -/
abbrev GapWord := List ℕ

namespace GapWord

/-- Every entry of a genuine gap word is positive. -/
def Positive (w : GapWord) : Prop := ∀ g ∈ w, 0 < g

/-- Spatial span of a gap word. -/
def span (w : GapWord) : ℕ := w.sum

/-- Span of the first `r` gaps. -/
def prefixSpan (w : GapWord) (r : ℕ) : ℕ := (w.take r).sum

/-- The first prefix whose span is strictly larger than `bound`, or the whole
word if there is no such prefix. -/
def firstPrefixAbove : GapWord → ℕ → GapWord
  | [], _ => []
  | g :: gs, bound =>
      if bound < g then [g]
      else g :: firstPrefixAbove gs (bound - g)

theorem firstPrefixAbove_isPrefix (w : GapWord) (bound : ℕ) :
    (w.firstPrefixAbove bound).IsPrefix w := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAbove]
  | cons g gs ih =>
      simp only [firstPrefixAbove]
      split_ifs with h
      · simp
      · rcases ih (bound - g) with ⟨tail, htail⟩
        exact ⟨tail, by simpa using congrArg (List.cons g) htail⟩

theorem firstPrefixAbove_length_le (w : GapWord) (bound : ℕ) :
    (w.firstPrefixAbove bound).length ≤ w.length :=
  (firstPrefixAbove_isPrefix w bound).length_le

theorem firstPrefixAbove_positive (w : GapWord) (bound : ℕ)
    (hpositive : w.Positive) : (w.firstPrefixAbove bound).Positive := by
  intro g hg
  exact hpositive g ((firstPrefixAbove_isPrefix w bound).mem hg)

/-- If the full word crosses the target, the selected prefix crosses it
strictly as well. -/
theorem lt_span_firstPrefixAbove_of_lt_span (w : GapWord) (bound : ℕ)
    (hcross : bound < w.span) : bound < (w.firstPrefixAbove bound).span := by
  induction w generalizing bound with
  | nil => simp [GapWord.span] at hcross
  | cons g gs ih =>
      simp only [firstPrefixAbove]
      by_cases hbg : bound < g
      · simp [hbg, GapWord.span]
      · rw [if_neg hbg]
        simp only [GapWord.span, List.sum_cons]
        have hgle : g ≤ bound := Nat.le_of_not_gt hbg
        have htail : bound - g < GapWord.span gs := by
          simp only [GapWord.span, List.sum_cons] at hcross
          simp only [GapWord.span]
          omega
        have hrec : bound - g <
            (firstPrefixAbove gs (bound - g)).sum := by
          simpa only [GapWord.span] using ih (bound - g) htail
        omega

/-- Minimal crossing overshoots the target by at most one gap. -/
theorem span_firstPrefixAbove_le_add (w : GapWord) (bound cap : ℕ)
    (hcap : ∀ g ∈ w, g ≤ cap) :
    (w.firstPrefixAbove bound).span ≤ bound + cap := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAbove, GapWord.span]
  | cons g gs ih =>
      have hgcap : g ≤ cap := hcap g (by simp)
      have htailcap : ∀ x ∈ gs, x ≤ cap := by
        intro x hx
        exact hcap x (by simp [hx])
      simp only [firstPrefixAbove]
      by_cases hbg : bound < g
      · simp [hbg, GapWord.span]
        omega
      · rw [if_neg hbg]
        simp only [GapWord.span, List.sum_cons]
        have hrec : (firstPrefixAbove gs (bound - g)).sum ≤
            (bound - g) + cap := by
          simpa only [GapWord.span] using ih (bound - g) htailcap
        omega

theorem span_firstPrefixAbove_le_span (w : GapWord) (bound : ℕ) :
    (w.firstPrefixAbove bound).span ≤ w.span := by
  let p := w.firstPrefixAbove bound
  have hp : p.IsPrefix w := firstPrefixAbove_isPrefix w bound
  obtain ⟨tail, htail⟩ := hp
  have hsum : w.span = p.span + tail.sum := by
    rw [← htail]
    simp [GapWord.span]
  change p.span ≤ w.span
  omega

/-- The first prefix whose span is at least `bound`, used for completed
logarithmic blocks.  This is deliberately separate from the strict prefix
selection used for the initial affine-locking prefix. -/
def firstPrefixAtLeast : GapWord → ℕ → GapWord
  | [], _ => []
  | g :: gs, bound =>
      if bound ≤ g then [g]
      else g :: firstPrefixAtLeast gs (bound - g)

theorem firstPrefixAtLeast_isPrefix (w : GapWord) (bound : ℕ) :
    (w.firstPrefixAtLeast bound).IsPrefix w := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAtLeast]
  | cons g gs ih =>
      simp only [firstPrefixAtLeast]
      by_cases hbg : bound ≤ g
      · simp [hbg]
      · rw [if_neg hbg]
        rcases ih (bound - g) with ⟨tail, htail⟩
        exact ⟨tail, by simpa using congrArg (List.cons g) htail⟩

theorem firstPrefixAtLeast_positive (w : GapWord) (bound : ℕ)
    (hpositive : w.Positive) : (w.firstPrefixAtLeast bound).Positive := by
  intro g hg
  exact hpositive g ((firstPrefixAtLeast_isPrefix w bound).mem hg)

theorem span_firstPrefixAtLeast_ge (w : GapWord) (bound : ℕ)
    (hcross : bound ≤ w.span) :
    bound ≤ (w.firstPrefixAtLeast bound).span := by
  induction w generalizing bound with
  | nil =>
      simp [firstPrefixAtLeast, GapWord.span] at hcross ⊢
      exact hcross
  | cons g gs ih =>
      simp only [firstPrefixAtLeast]
      by_cases hbg : bound ≤ g
      · simp [hbg, GapWord.span]
      · rw [if_neg hbg]
        simp only [GapWord.span, List.sum_cons]
        have htail : bound - g ≤ GapWord.span gs := by
          change bound - g ≤ gs.sum
          simp only [GapWord.span, List.sum_cons] at hcross
          omega
        have hrec := ih (bound - g) htail
        simp only [GapWord.span] at hrec ⊢
        omega

theorem firstPrefixAtLeast_ne_nil (w : GapWord) (bound : ℕ)
    (hbound : 0 < bound) (hcross : bound ≤ w.span) :
    w.firstPrefixAtLeast bound ≠ [] := by
  intro hempty
  have hspan := span_firstPrefixAtLeast_ge w bound hcross
  rw [hempty] at hspan
  simp [GapWord.span] at hspan
  omega

theorem prefixSpan_firstPrefixAtLeast_lt (w : GapWord) (bound : ℕ)
    (hbound : 0 < bound) :
    ∀ r < (w.firstPrefixAtLeast bound).length,
      (w.firstPrefixAtLeast bound).prefixSpan r < bound := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAtLeast]
  | cons g gs ih =>
      simp only [firstPrefixAtLeast]
      by_cases hbg : bound ≤ g
      · rw [if_pos hbg]
        intro r hr
        have hr0 : r = 0 := by simp at hr; omega
        subst r
        simpa [GapWord.prefixSpan] using hbound
      · rw [if_neg hbg]
        intro r hr
        have hglt : g < bound := Nat.lt_of_not_ge hbg
        cases r with
        | zero => simpa [GapWord.prefixSpan] using hbound
        | succ r =>
            have hrTail : r < (firstPrefixAtLeast gs (bound - g)).length := by
              simpa using hr
            have htailBound : 0 < bound - g := by omega
            have hrec := ih (bound - g) htailBound r hrTail
            simp only [GapWord.prefixSpan, List.take_succ_cons, List.sum_cons]
            simp only [GapWord.prefixSpan] at hrec
            omega

theorem firstPrefixAtLeast_append_drop (w : GapWord) (bound : ℕ) :
    w.firstPrefixAtLeast bound ++
        w.drop (w.firstPrefixAtLeast bound).length = w := by
  induction w generalizing bound with
  | nil => simp [firstPrefixAtLeast]
  | cons g gs ih =>
      simp only [firstPrefixAtLeast]
      by_cases hbg : bound ≤ g
      · simp [hbg]
      · rw [if_neg hbg]
        simp only [List.length_cons, List.drop_succ_cons, List.cons_append,
          List.cons.injEq, true_and]
        exact ih (bound - g)

/-- A block is the shortest nonempty prefix of its remaining word whose span
reaches `bound`.  This predicate is used to specify the greedy decomposition
without hiding a choice function. -/
def IsGreedyBlock (bound : ℕ) (block : GapWord) : Prop :=
  block ≠ [] ∧ bound ≤ span block ∧
    ∀ r < block.length, prefixSpan block r < bound

theorem firstPrefixAtLeast_isGreedyBlock (w : GapWord) (bound : ℕ)
    (hbound : 0 < bound) (hcross : bound ≤ w.span) :
    IsGreedyBlock bound (w.firstPrefixAtLeast bound) := by
  exact ⟨firstPrefixAtLeast_ne_nil w bound hbound hcross,
    span_firstPrefixAtLeast_ge w bound hcross,
    prefixSpan_firstPrefixAtLeast_lt w bound hbound⟩

/-- A genuine greedy block decomposition of a word. -/
def IsGreedyDecomposition (w : GapWord) (bound : ℕ)
    (blocks : List GapWord) : Prop :=
  blocks.flatten = w ∧ ∀ block ∈ blocks, IsGreedyBlock bound block

/-- Output of the deterministic greedy logarithmic-block procedure.  Only
completed blocks are placed in `completed`; the final short suffix is retained
separately rather than silently discarded. -/
structure GreedyDecomposition where
  completed : List GapWord
  remainder : GapWord
  deriving DecidableEq, Repr

def greedyDecomposeAux : ℕ → GapWord → ℕ → GreedyDecomposition
  | 0, w, _ => ⟨[], w⟩
  | fuel + 1, w, bound =>
      if 0 < bound ∧ bound ≤ span w then
        let block := firstPrefixAtLeast w bound
        let tail := w.drop block.length
        let result := greedyDecomposeAux fuel tail bound
        ⟨block :: result.completed, result.remainder⟩
      else
        ⟨[], w⟩

def greedyDecompose (w : GapWord) (bound : ℕ) : GreedyDecomposition :=
  greedyDecomposeAux w.length w bound

/-- Semantic contract for a greedy decomposition with an explicit incomplete
remainder. -/
def GreedyDecomposition.Valid (w : GapWord) (bound : ℕ)
    (result : GreedyDecomposition) : Prop :=
  result.completed.flatten ++ result.remainder = w ∧
    (∀ block ∈ result.completed, IsGreedyBlock bound block) ∧
    result.remainder.span < bound

theorem greedyDecomposeAux_valid (fuel : ℕ) (w : GapWord) (bound : ℕ)
    (hfuel : w.length ≤ fuel) (hbound : 0 < bound) :
    (greedyDecomposeAux fuel w bound).Valid w bound := by
  induction fuel generalizing w with
  | zero =>
      have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst w
      exact ⟨by simp [greedyDecomposeAux], by simp [greedyDecomposeAux],
        by simpa [greedyDecomposeAux, GapWord.span] using hbound⟩
  | succ fuel ih =>
      unfold greedyDecomposeAux
      by_cases hcross : bound ≤ w.span
      · rw [if_pos ⟨hbound, hcross⟩]
        let block := w.firstPrefixAtLeast bound
        let tail := w.drop block.length
        let result := greedyDecomposeAux fuel tail bound
        have hblock : IsGreedyBlock bound block := by
          exact firstPrefixAtLeast_isGreedyBlock w bound hbound hcross
        have happend : block ++ tail = w := by
          exact firstPrefixAtLeast_append_drop w bound
        have hblockLength : 0 < block.length := List.length_pos_iff.mpr hblock.1
        have hblockLe : block.length ≤ w.length :=
          (firstPrefixAtLeast_isPrefix w bound).length_le
        have htailLength : tail.length ≤ fuel := by
          dsimp [tail]
          rw [List.length_drop]
          omega
        have hresult : result.Valid tail bound := by
          exact ih tail htailLength
        rcases hresult with ⟨hflatten, hblocks, hremainder⟩
        change
          (block :: result.completed).flatten ++ result.remainder = w ∧
            (∀ b ∈ block :: result.completed, IsGreedyBlock bound b) ∧
              result.remainder.span < bound
        constructor
        · simp only [List.flatten_cons, List.append_assoc]
          rw [hflatten, happend]
        constructor
        · intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hblock
          · exact hblocks b hb
        · exact hremainder
      · rw [if_neg (by simp [hbound, hcross])]
        exact ⟨by simp, by simp, Nat.lt_of_not_ge hcross⟩

theorem greedyDecompose_valid (w : GapWord) (bound : ℕ)
    (hbound : 0 < bound) :
    (greedyDecompose w bound).Valid w bound := by
  exact greedyDecomposeAux_valid w.length w bound le_rfl hbound

end GapWord

/-- An order-`offset+1` window anchored at an index. -/
structure AnchoredWindow where
  anchor : ℕ
  offset : ℕ
  valid : offset ≤ anchor

/-- Ordered gaps in an anchored window. -/
def windowGapWord {S : Set ℕ} (e : SupportEnumeration S)
    (w : AnchoredWindow) : GapWord :=
  (List.range (w.offset + 1)).map fun j =>
    supportGap e (w.anchor - w.offset + j)

/-- Spatial span of an anchored window. -/
def windowSpan {S : Set ℕ} (e : SupportEnumeration S)
    (w : AnchoredWindow) : ℕ :=
  (windowGapWord e w).span

/-- A window-threshold pair is represented by its discrete anchor and real
threshold.  The surrounding scale context determines the actual window. -/
abbrev WindowThreshold := ℕ × ℝ

/-- Closed threshold interval used by the paper. -/
def thresholdInterval (L C0 : ℕ) (cI : ℝ) : Set ℝ :=
  Set.Icc (2 * (L : ℝ) + C0) (2 * (L : ℝ) + C0 + cI * L)

/-- Structural constants fixed before scale-dependent choices. -/
structure StructuralParams where
  Caff : ℝ
  B : ℝ
  Gamma : ℝ
  rho : ℝ
  cI : ℝ
  C0 : ℕ
  Caff_gt : 2 < Caff
  B_gt : 2 < B
  Gamma_gt : 1 < Gamma
  rho_pos : 0 < rho
  rho_lt : rho < 1 / 6
  cI_pos : 0 < cI

/-- The window-density parameter is chosen after the structural constants,
together with the two strict entropy margins used in the rare and exterior
counts. -/
structure EntropyParams where
  structural : StructuralParams
  kappa : ℝ
  kappa_pos : 0 < kappa
  /-- The initial-prefix entropy argument lies in the monotone half of binary
  entropy.  This hypothesis is used by the binomial-composition estimate and
  cannot be recovered merely from the two strict entropy margins. -/
  kappa_initial_half :
    kappa / (structural.Caff + 1) ≤ 1 / 2
  /-- The post-exit-prefix entropy argument likewise lies in `[0,1/2]`. -/
  kappa_exterior_half :
    kappa / (structural.Gamma + 1) ≤ 1 / 2
  initial_margin :
    (structural.Caff + 1) *
        binaryEntropy (kappa / (structural.Caff + 1)) <
      1 / 2 - 3 * structural.rho
  total_margin :
    (structural.Caff + 1) *
          binaryEntropy (kappa / (structural.Caff + 1)) +
        (structural.Gamma + 1) *
          binaryEntropy (kappa / (structural.Gamma + 1)) <
      1 - 2 * structural.rho

/-- Rational support data from which integral carries are defined. -/
structure RationalSupport where
  S : Set ℕ
  eta : ℚ
  infinite : S.Infinite
  positive : ∀ n, n ∈ S → 0 < n
  hasSum : HasSum (weightedSupportTerm S) (eta : ℝ)

namespace RationalSupport

/-- Normalize arbitrary public support data by deleting the zero index. -/
def normalize (S : Set ℕ) (eta : ℚ) (hinfinite : S.Infinite)
    (hsum : HasSum (weightedSupportTerm S) (eta : ℝ)) : RationalSupport where
  S := positiveSupport S
  eta := eta
  infinite := positiveSupport_infinite hinfinite
  positive := by
    intro n hn
    exact hn.2
  hasSum := hsum.congr_fun fun n =>
    weightedSupportTerm_positiveSupport S n

end RationalSupport

/-- A scale-specific system of overlapping windows and thresholds. -/
structure WindowSystem where
  rational : RationalSupport
  enumeration : SupportEnumeration rational.S
  structural : StructuralParams
  entropy : EntropyParams
  entropy_structural : entropy.structural = structural
  L : ℕ
  s : ℕ
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon

namespace WindowSystem

def X (W : WindowSystem) : ℕ := dyadicScale W.L

def m (W : WindowSystem) : ℕ := W.s + 1

def anchors (W : WindowSystem) : Finset ℕ :=
  (Finset.range (2 * W.X + 1)).filter fun k =>
    W.X < W.enumeration.a k ∧ W.enumeration.a k ≤ 2 * W.X

def window (W : WindowSystem) (k : ℕ) (hk : W.s ≤ k) : AnchoredWindow :=
  ⟨k, W.s, hk⟩

def rawWindowSpan (W : WindowSystem) (k : ℕ) : ℕ :=
  if hk : W.s ≤ k then windowSpan W.enumeration (W.window k hk) else 0

def rawWindowGapWord (W : WindowSystem) (k : ℕ) : GapWord :=
  if hk : W.s ≤ k then windowGapWord W.enumeration (W.window k hk) else []

def thresholds (W : WindowSystem) : Set ℝ :=
  thresholdInterval W.L W.structural.C0 W.structural.cI

def pairSet (W : WindowSystem) : Set WindowThreshold :=
  {e | e.1 ∈ W.anchors ∧ e.2 ∈ W.thresholds}

def excess (W : WindowSystem) (e : WindowThreshold) : ℝ :=
  max ((W.rawWindowSpan e.1 : ℝ) - e.2 - W.epsilon * W.L) 0

def boundedPairs (W : WindowSystem) (Z0 : ℕ) : Set WindowThreshold :=
  W.pairSet ∩ {e | W.excess e ≤ W.m * Z0}

def largePairs (W : WindowSystem) (Z0 : ℕ) : Set WindowThreshold :=
  W.pairSet ∩ {e | W.m * Z0 < W.excess e}

end WindowSystem

end Erdos260

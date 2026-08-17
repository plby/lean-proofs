/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.TwoLargeForest
import ErdosProblems.Erdos622.ShiftedGaussian
import ErdosProblems.Erdos622.ShiftedWindowCount
import ErdosProblems.Erdos622.OriginalSideForest
import ErdosProblems.Erdos622.OneSmallIntermediate
import ErdosProblems.Erdos622.CompactBoundedForest
import ErdosProblems.Erdos622.BoundedInternal
import ErdosProblems.Erdos622.TwoLargeFinish
import ErdosProblems.Erdos622.ForwardSmallFinish

/-!
# The two-large-cover case for the almost-bipartite regime

This downstream module combines the graph-independent sampled-Alon
machinery in `TwoLargeForest`, the shifted compact Gaussian window, and the
already proved one-small-cover tail estimates.  Keeping the case theorem
here avoids an import cycle through `IntermediateImbalance`.
-/

namespace Erdos622
namespace TwoLargeCase

open Filter Finset Real Set
open scoped BigOperators Topology SimpleGraph

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Undo the balanced-cut standardization for arbitrary positive endpoint
capacities.  The order is worth recording explicitly: the upper endpoint
controls `x-y`, while the magnitude of the lower endpoint controls `y-x`. -/
lemma standardized_balanced_window_bounds
    {n x y : ℕ} {a b : ℝ}
    (hn : 0 < n) (hy : y ≤ n)
    (hwindow : BinomialCLT.standardizedBinomialPoint (2 * n)
        (x + (n - y)) ∈
      Set.Icc (-(a * Real.sqrt 2)) (b * Real.sqrt 2)) :
    ((x : ℝ) - y ≤ b * Real.sqrt n) ∧
      ((y : ℝ) - x ≤ a * Real.sqrt n) := by
  have hsqrtn : 0 < Real.sqrt n :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2pow : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hnum :
      (2 * (x + (n - y)) : ℝ) - (2 * n : ℝ) =
        2 * ((x : ℝ) - y) := by
    push_cast [Nat.cast_sub hy]
    ring
  constructor
  · have hu := hwindow.2
    unfold BinomialCLT.standardizedBinomialPoint at hu
    norm_num at hu
    rw [Nat.cast_sub hy,
      div_le_iff₀ (mul_pos hsqrt2 hsqrtn), hnum] at hu
    nlinarith [hsqrt2pow]
  · have hl := hwindow.1
    unfold BinomialCLT.standardizedBinomialPoint at hl
    norm_num at hl
    rw [Nat.cast_sub hy,
      le_div_iff₀ (mul_pos hsqrt2 hsqrtn), hnum] at hl
    field_simp at hl
    rw [hsqrt2pow] at hl
    nlinarith

/-- A natural lower bound by `floor(sqrt n) / K` becomes a uniform positive
real lower bound after normalization by `sqrt n`.  The factor four absorbs
both integer divisions. -/
lemma eventually_sqrtCover_ratio_mem
    {K M : ℕ} (hK : 0 < K) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℕ,
      sqrtCoverThreshold K n ≤ c → c ≤ M * Nat.sqrt n →
        (c : ℝ) / Real.sqrt n ∈
          Set.Icc (1 / (4 * K : ℝ)) (M : ℝ) := by
  filter_upwards [eventually_ge_atTop ((2 * K) ^ 2)] with n hn
  intro c hcLower hcUpper
  let s := Nat.sqrt n
  have h2Ks : 2 * K ≤ s := by
    rw [Nat.le_sqrt]
    simpa [s, pow_two] using hn
  have hKs : K ≤ s := by omega
  have hspos : 0 < s := lt_of_lt_of_le (by omega : 0 < 2 * K) h2Ks
  have hsdiv : s ≤ 2 * K * (s / K) := by
    have hdecomp := Nat.div_add_mod s K
    have hmod : s % K < K := Nat.mod_lt s hK
    nlinarith
  have hsqrtPos : 0 < Real.sqrt n := by
    apply Real.sqrt_pos.2
    have : 0 < n := by
      have hsSq : 0 < s ^ 2 := by positivity
      exact lt_of_lt_of_le hsSq (by simpa [s] using Nat.sqrt_le' n)
    exact_mod_cast this
  have hsqrtUpper : Real.sqrt n ≤ 2 * s := by
    have hsFloor : Real.sqrt n < (s : ℝ) + 1 := by
      simpa [s] using Real.real_sqrt_lt_nat_sqrt_succ (a := n)
    have hsOne : (1 : ℝ) ≤ s := by exact_mod_cast hspos
    linarith
  have hcLowerR : Real.sqrt n / (4 * K : ℝ) ≤ c := by
    have hsdivR : (s : ℝ) ≤
        2 * (K : ℝ) * ((s / K : ℕ) : ℝ) := by
      exact_mod_cast hsdiv
    have hcR : ((s / K : ℕ) : ℝ) ≤ c := by
      exact_mod_cast (show s / K ≤ c from by
        simpa [sqrtCoverThreshold, s] using hcLower)
    have hKReal : (0 : ℝ) < K := by exact_mod_cast hK
    calc
      Real.sqrt n / (4 * K : ℝ) ≤ (2 * s : ℝ) / (4 * K) := by
        gcongr
      _ = (s : ℝ) / (2 * K) := by ring
      _ ≤ (s / K : ℕ) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)]
        nlinarith
      _ ≤ c := hcR
  constructor
  · rw [le_div_iff₀ hsqrtPos]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcLowerR
  · rw [div_le_iff₀ hsqrtPos]
    have hcUpperR : (c : ℝ) ≤ M * s := by exact_mod_cast hcUpper
    exact hcUpperR.trans
      (mul_le_mul_of_nonneg_left
        (show (s : ℝ) ≤ Real.sqrt n by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity),
            show ((s : ℝ) ^ 2) ≤ n by
              exact_mod_cast (by simpa [s] using Nat.sqrt_le' n)])
        (by positivity))

/-- A union bound for four exceptional families of samples.  This small
finite lemma keeps the final window subtraction independent of the concrete
definitions of the matching, sampled-Alon, and balancing failures. -/
theorem four_failure_count_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F₁ F₂ F₃ F₄ : Finset V → Prop) {δ₁ δ₂ δ₃ δ₄ : ℝ}
    (h₁ : (almostBipartiteCount (Finset.univ : Finset V) F₁ : ℝ) ≤
      δ₁ * (2 : ℝ) ^ Fintype.card V)
    (h₂ : (almostBipartiteCount (Finset.univ : Finset V) F₂ : ℝ) ≤
      δ₂ * (2 : ℝ) ^ Fintype.card V)
    (h₃ : (almostBipartiteCount (Finset.univ : Finset V) F₃ : ℝ) ≤
      δ₃ * (2 : ℝ) ^ Fintype.card V)
    (h₄ : (almostBipartiteCount (Finset.univ : Finset V) F₄ : ℝ) ≤
      δ₄ * (2 : ℝ) ^ Fintype.card V) :
    (almostBipartiteCount (Finset.univ : Finset V)
      (fun S ↦ F₁ S ∨ F₂ S ∨ F₃ S ∨ F₄ S) : ℝ) ≤
        (δ₁ + δ₂ + δ₃ + δ₄) * (2 : ℝ) ^ Fintype.card V := by
  have h12 := almostBipartiteCount_or_le
    (Finset.univ : Finset V) F₁ F₂
  have h34 := almostBipartiteCount_or_le
    (Finset.univ : Finset V) F₃ F₄
  have houter := almostBipartiteCount_or_le
    (Finset.univ : Finset V) (fun S ↦ F₁ S ∨ F₂ S)
      (fun S ↦ F₃ S ∨ F₄ S)
  have houter' :
      almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ F₁ S ∨ F₂ S ∨ F₃ S ∨ F₄ S) ≤
        almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ F₁ S ∨ F₂ S) +
          almostBipartiteCount (Finset.univ : Finset V)
            (fun S ↦ F₃ S ∨ F₄ S) := by
    simpa only [or_assoc] using houter
  have hleft :
      (almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ F₁ S ∨ F₂ S) : ℝ) ≤
          (δ₁ + δ₂) * (2 : ℝ) ^ Fintype.card V := by
    calc
      _ ≤ (almostBipartiteCount (Finset.univ : Finset V) F₁ : ℝ) +
          almostBipartiteCount (Finset.univ : Finset V) F₂ := by
        exact_mod_cast h12
      _ ≤ δ₁ * (2 : ℝ) ^ Fintype.card V +
          δ₂ * (2 : ℝ) ^ Fintype.card V := add_le_add h₁ h₂
      _ = _ := by ring
  have hright :
      (almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ F₃ S ∨ F₄ S) : ℝ) ≤
          (δ₃ + δ₄) * (2 : ℝ) ^ Fintype.card V := by
    calc
      _ ≤ (almostBipartiteCount (Finset.univ : Finset V) F₃ : ℝ) +
          almostBipartiteCount (Finset.univ : Finset V) F₄ := by
        exact_mod_cast h34
      _ ≤ δ₃ * (2 : ℝ) ^ Fintype.card V +
          δ₄ * (2 : ℝ) ^ Fintype.card V := add_le_add h₃ h₄
      _ = _ := by ring
  calc
    _ ≤ (almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ F₁ S ∨ F₂ S) : ℝ) +
        almostBipartiteCount (Finset.univ : Finset V)
          (fun S ↦ F₃ S ∨ F₄ S) := by
      exact_mod_cast houter'
    _ ≤ (δ₁ + δ₂) * (2 : ℝ) ^ Fintype.card V +
        (δ₃ + δ₄) * (2 : ℝ) ^ Fintype.card V :=
      add_le_add hleft hright
    _ = _ := by ring

/-- Turn the real threshold in the random-cover event into an integral
linear-forest capacity.  The natural floor is the only rounding needed in
the compact two-large argument. -/
lemma matching_floor_induce_internalGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A S : Finset V} {u : ℝ}
    (hu : 0 ≤ u)
    (h : RandomCover.HasMatchingAtLeast (internalGraph G A) S u) :
    ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) ⌊u⌋₊ := by
  apply RandomCover.HasMatchingAtLeast.induce_internalGraph
  obtain ⟨N, hNmatching, hNS, hNcard⟩ := h
  exact ⟨N, hNmatching, hNS, (Nat.floor_le hu).trans hNcard⟩

/-- The spare half of the matching shrink pays for taking a natural floor.
This is stated without a normalized parameter so it can be used in either
orientation of the bounded-internal construction. -/
lemma matching_floor_capacity
    {c : ℕ} {s eps sigma : ℝ}
    (hs : 0 < s) (hsigma : 0 < sigma)
    (hepsc : eps * c ≤ sigma * s / 2)
    (hlarge : 1 ≤ sigma * s / 2) :
    ((c : ℝ) / s / 4 - sigma) * s ≤
      (⌊(1 / 4 - eps) * (c : ℝ)⌋₊ : ℝ) := by
  have hthreshold :
      ((c : ℝ) / s / 4 - sigma) * s + 1 ≤
        (1 / 4 - eps) * (c : ℝ) := by
    field_simp [ne_of_gt hs]
    nlinarith
  have hfloor := Nat.lt_floor_add_one ((1 / 4 - eps) * (c : ℝ))
  linarith

/-- Finite subtraction wrapper for the three forest mechanisms.  All
probabilistic estimates enter only through the four failure counts, while
the graph-theoretic conclusion is the exact original-cut transfer lemma. -/
theorem goodSample_count_of_three_forest_failures
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {A B T A₀ B₀ : Finset V}
    (P F₁ F₂ F₃ F₄ : Finset V → Prop)
    {leftBalanced leftOriginal right : ℕ}
    {R δ₁ δ₂ δ₃ δ₄ : ℝ}
    (hcut : IsCut A B) (hTA : T ⊆ A)
    (hA₀ : A₀ = A \ T) (hB₀ : B₀ = B ∪ T)
    (hleftBalanced : ∀ S, ¬ F₁ S →
      ContainsLinearForestWith (G.induce (S : Set V))
        (restrictedPart S A₀) leftBalanced)
    (hleftOriginal : ∀ S, ¬ F₂ S →
      ContainsLinearForestWith (G.induce (S : Set V))
        (restrictedPart S A) leftOriginal)
    (hright : ∀ S, ¬ F₃ S →
      ContainsLinearForestWith (G.induce (S : Set V))
        (restrictedPart S B₀) right)
    (hwindows : ∀ S, P S → ¬ F₄ S →
      (S ∩ A₀).card + 2 * (S ∩ T).card ≤
          (S ∩ B₀).card + max leftBalanced leftOriginal ∧
        (S ∩ B₀).card ≤
          (S ∩ A₀).card + max (2 * (S ∩ T).card) right)
    (hwindow : R ≤
      (almostBipartiteCount (Finset.univ : Finset V) P : ℝ))
    (h₁ : (almostBipartiteCount (Finset.univ : Finset V) F₁ : ℝ) ≤
      δ₁ * (2 : ℝ) ^ Fintype.card V)
    (h₂ : (almostBipartiteCount (Finset.univ : Finset V) F₂ : ℝ) ≤
      δ₂ * (2 : ℝ) ^ Fintype.card V)
    (h₃ : (almostBipartiteCount (Finset.univ : Finset V) F₃ : ℝ) ≤
      δ₃ * (2 : ℝ) ^ Fintype.card V)
    (h₄ : (almostBipartiteCount (Finset.univ : Finset V) F₄ : ℝ) ≤
      δ₄ * (2 : ℝ) ^ Fintype.card V) :
    R - (δ₁ + δ₂ + δ₃ + δ₄) *
        (2 : ℝ) ^ Fintype.card V ≤
      (almostBipartiteCount (Finset.univ : Finset V)
        (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  let Failure : Finset V → Prop := fun S ↦ F₁ S ∨ F₂ S ∨ F₃ S ∨ F₄ S
  have hfailure :
      (almostBipartiteCount (Finset.univ : Finset V) Failure : ℝ) ≤
        (δ₁ + δ₂ + δ₃ + δ₄) *
          (2 : ℝ) ^ Fintype.card V := by
    exact four_failure_count_le F₁ F₂ F₃ F₄ h₁ h₂ h₃ h₄
  apply AlmostBipartiteRegimeCounts.goodSample_count_of_window_failure
    G P Failure R (δ₁ + δ₂ + δ₃ + δ₄) _ hwindow hfailure
  intro S _hS hPS hnot
  have hn₁ : ¬ F₁ S := by intro h; exact hnot (Or.inl h)
  have hn₂ : ¬ F₂ S := by intro h; exact hnot (Or.inr (Or.inl h))
  have hn₃ : ¬ F₃ S := by intro h; exact hnot (Or.inr (Or.inr (Or.inl h)))
  have hn₄ : ¬ F₄ S := by intro h; exact hnot (Or.inr (Or.inr (Or.inr h)))
  exact TwoLargeForest.IsKGoodSample.of_balanced_transfer_three_forests
    hcut hTA hA₀ hB₀ (hleftBalanced S hn₁)
      (hleftOriginal S hn₂) (hright S hn₃)
      (hwindows S hPS hn₄).1 (hwindows S hPS hn₄).2

/-- Scalar subtraction used after the four exceptional families have been
removed from the shifted window.  Keeping it outside the graph theorem
prevents arithmetic normalization from traversing a very large context. -/
lemma shifted_density_subtraction {delta margin p q : ℝ}
    (hmargin : 0 ≤ margin) (hp : 0 ≤ p)
    (h : ((1 / 2 : ℝ) + margin / 2) * p - delta * p ≤ q) :
    ((1 / 2 : ℝ) - delta) * p ≤ q := by
  have hcoef : (1 / 2 : ℝ) - delta ≤
      (1 / 2 : ℝ) + margin / 2 - delta := by
    linarith only [hmargin]
  calc
    ((1 / 2 : ℝ) - delta) * p ≤
        ((1 / 2 : ℝ) + margin / 2 - delta) * p :=
      mul_le_mul_of_nonneg_right hcoef hp
    _ = ((1 / 2 : ℝ) + margin / 2) * p - delta * p := sub_mul _ _ _
    _ ≤ q := h

/-- The small-transfer arm has only three exceptional families. -/
lemma three_failure_density_subtraction {delta delta₀ margin p q : ℝ}
    (hdelta : 0 < delta) (hdelta₀ : delta₀ = delta / 4)
    (hmargin : 0 ≤ margin) (hp : 0 ≤ p)
    (h : ((1 / 2 : ℝ) + margin / 2) * p - 3 * delta₀ * p ≤ q) :
    ((1 / 2 : ℝ) - delta) * p ≤ q := by
  have hcoef : (1 / 2 : ℝ) - delta ≤
      (1 / 2 : ℝ) + margin / 2 - 3 * delta₀ := by
    rw [hdelta₀]
    linarith only [hdelta, hmargin]
  calc
    ((1 / 2 : ℝ) - delta) * p ≤
        ((1 / 2 : ℝ) + margin / 2 - 3 * delta₀) * p :=
      mul_le_mul_of_nonneg_right hcoef hp
    _ = ((1 / 2 : ℝ) + margin / 2) * p - 3 * delta₀ * p :=
      sub_mul _ _ _
    _ ≤ q := h

/-- Compact core of the two-large-cover argument.  Both minimum covers are
between the structural square-root threshold and a fixed multiple of
`sqrt n`; the orientation-free bounded-internal lemma then supplies the
matching/linear-forest pair used by the shifted Gaussian window. -/
theorem eventually_compact_twoLargeCover_goodSample_count
    {delta : ℝ} (hdelta : 0 < delta) {K M₀ : ℕ}
    (hK : 0 < K) (hM₀ : 0 < M₀) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B T A₀ B₀ C D : Finset (Fin (2 * n))),
        G.IsRegularOfDegree (n + 1) → IsAlmostBipartiteCut G A B →
        T ⊆ A → T.card = A.card - n → A₀ = A \ T → B₀ = B ∪ T →
        IsCut A₀ B₀ → A₀.card = n → B₀.card = n →
        IsMinimumVertexCoverOn G A₀ C →
        IsMinimumVertexCoverOn G B₀ D →
        A.card - n ≤ Nat.sqrt n →
        sqrtCoverThreshold K n ≤ C.card →
        sqrtCoverThreshold K n ≤ D.card →
        C.card ≤ M₀ * Nat.sqrt n → D.card ≤ M₀ * Nat.sqrt n →
        ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  let eta₀ : ℝ := 1 / (4 * K : ℝ)
  let eta : ℝ := min eta₀ (4 / (M₀ : ℝ))
  let M : ℝ := max (M₀ : ℝ) (16 * K : ℝ)
  have heta₀ : 0 < eta₀ := by dsimp [eta₀]; positivity
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hetaM : eta ≤ M := by
    calc
      eta ≤ eta₀ := min_le_left _ _
      _ ≤ M := by
        dsimp [eta₀, M]
        apply le_max_of_le_right
        have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
        have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * K)]
        nlinarith [sq_nonneg ((K : ℝ) - 1)]
  obtain ⟨rho, margin, hrho, hmargin, hwindow⟩ :=
    ShiftedWindowCount.eventually_uniform_balancedCut_shrunken_capacity_count
      heta hetaM
  obtain ⟨sigma, hsigma, htwoSigma, hsigmaM, hsigmaOne⟩ :=
    AlmostBipartiteRegimeCounts.exists_auxiliary_capacity_shrink hrho hM
  let eps : ℝ := sigma / (2 * M)
  let delta₀ : ℝ := delta / 4
  let K₀ : ℕ := max (256 * K) (16 * M₀)
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepsHalf : eps < 1 / 2 := by
    have hsigmaleM : sigma < M := hsigmaOne.trans_le (by
      dsimp [M]
      apply le_max_of_le_right
      have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith)
    dsimp [eps]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
    linarith
  have hepsQuarter : eps < 1 / 4 := by
    have hMsixteen : (16 : ℝ) ≤ M := by
      dsimp [M]
      exact le_max_of_le_right (by
        have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
        nlinarith)
    dsimp [eps]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * M)]
    nlinarith
  have hdelta₀ : 0 < delta₀ := by dsimp [delta₀]; positivity
  have hK₀ : 0 < K₀ := by
    dsimp [K₀]
    exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hsigmaM₀ : sigma * (M₀ : ℝ) < 1 := by
    calc
      sigma * (M₀ : ℝ) ≤ sigma * M :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hsigma.le
      _ < 1 := hsigmaM
  have heta₀M₀ : eta₀ ≤ (M₀ : ℝ) := by
    dsimp [eta₀]
    have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hMreal : (1 : ℝ) ≤ M₀ := by exact_mod_cast hM₀
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * K)]
    nlinarith [sq_nonneg ((K : ℝ) - 1)]
  have hmatching := eventually_minimumCoverOn_ambient_randomMatching_count_le
    (L := K) hK heps hepsHalf hdelta₀
  have hforest :=
    CompactBoundedForest.eventually_compact_bounded_sample_forest
      heta₀ (show (0 : ℝ) < M₀ by exact_mod_cast hM₀)
      hsigma hdelta₀ heta₀M₀ hsigmaM₀
  have htransfer := ShiftedWindowCount.eventually_balancingSet_bad_count_le
    (show 0 < sigma / 2 by positivity) hdelta₀
  have horiginal :=
    OriginalSideForest.eventually_originalSide_linearForest_count
      hdelta₀ hK₀
  have hratio := eventually_sqrtCover_ratio_mem hK hM₀
  have hround : ∀ᶠ n : ℕ in atTop,
      1 ≤ sigma * Real.sqrt n / 2 := by
    have hsqrtTop : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hevent := hsqrtTop.eventually_ge_atTop (2 / sigma)
    filter_upwards [hevent] with n hn
    have := mul_le_mul_of_nonneg_left hn hsigma.le
    field_simp at this ⊢
    nlinarith
  filter_upwards [hwindow, hmatching, hforest, htransfer, horiginal,
      hratio, hround, eventually_gt_atTop (0 : ℕ)] with
      n hnWindow hnMatching hnForest hnTransfer hnOriginal hnRatio
        hnRound hnpos
  intro G A B T A₀ B₀ C D hreg hAB hTA hTcard hA₀ hB₀ hcut₀
    hA₀card hB₀card hC hD hdUpper hClower hDlower hCupper hDupper
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  have hCratio := hnRatio C.card hClower hCupper
  have hDratio := hnRatio D.card hDlower hDupper
  have hCupperReal : (C.card : ℝ) ≤ M₀ * Real.sqrt n := by
    calc
      (C.card : ℝ) ≤ ((M₀ * Nat.sqrt n : ℕ) : ℝ) := by
        exact_mod_cast hCupper
      _ = (M₀ : ℝ) * (Nat.sqrt n : ℝ) := by norm_cast
      _ ≤ (M₀ : ℝ) * Real.sqrt n :=
        mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by positivity)
  have hDupperReal : (D.card : ℝ) ≤ M₀ * Real.sqrt n := by
    calc
      (D.card : ℝ) ≤ ((M₀ * Nat.sqrt n : ℕ) : ℝ) := by
        exact_mod_cast hDupper
      _ = (M₀ : ℝ) * (Nat.sqrt n : ℝ) := by norm_cast
      _ ≤ (M₀ : ℝ) * Real.sqrt n :=
        mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by positivity)
  rcases BoundedInternal.exists_boundedInternal_either_orientation
      G hreg hcut₀ hA₀card hB₀card hC.1 hD.1 with horient | horient
  · rcases horient with ⟨JA, JB, hJAG, hJBG, hJAsupp, hJBsupp,
      hJAbip, hJBbip, hJAdeg, hJBdeg, hJAedge, hJBedge⟩
    have hCeta : eta₀ * Real.sqrt n ≤ C.card := by
      exact (le_div_iff₀ hsqrt).mp hCratio.1
    obtain ⟨right, hrightCap, hrightBad⟩ :=
      hnForest C D (B₀ \ D) JB hCeta hCupperReal hDupperReal
        hJBbip hJBdeg hJBedge
    have hmatchingBad := hnMatching (Fin (2 * n)) G A₀ C hC hClower
    let alpha : ℝ := (C.card : ℝ) / Real.sqrt n
    let kappa : ℝ := ((A.card - n : ℕ) : ℝ) / Real.sqrt n
    have halpha : alpha ∈ Set.Icc eta M := by
      constructor
      · exact (min_le_left _ _).trans hCratio.1
      · exact hCratio.2.trans (le_max_left _ _)
    have hkappa : kappa ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [kappa]
        exact div_nonneg (by positivity) hsqrt.le
      · rw [div_le_one hsqrt]
        calc
          ((A.card - n : ℕ) : ℝ) ≤ (Nat.sqrt n : ℝ) := by
            exact Nat.cast_le.2 hdUpper
          _ ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
    have hwindowCount := hnWindow B₀ A₀ hcut₀.symm hB₀card hA₀card
      alpha halpha kappa hkappa
    have hepsc : eps * (C.card : ℝ) ≤ sigma * Real.sqrt n / 2 := by
      have hCM : (C.card : ℝ) ≤ M * Real.sqrt n :=
        hCupperReal.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsqrt.le)
      dsimp [eps]
      have h := mul_le_mul_of_nonneg_left hCM (show 0 ≤ sigma / (2 * M) by positivity)
      field_simp [ne_of_gt hM] at h ⊢
      nlinarith
    let left : ℕ := ⌊(1 / 4 - eps) * (C.card : ℝ)⌋₊
    have hleftCap : (alpha / 4 - sigma) * Real.sqrt n ≤ left := by
      dsimp [alpha, left]
      exact matching_floor_capacity hsqrt hsigma hepsc hnRound
    have hthresholdNonneg : 0 ≤ (1 / 4 - eps) * (C.card : ℝ) := by
      exact mul_nonneg (by linarith) (by positivity)
    have htransferBad := hnTransfer T (hTcard.trans_le hdUpper)
    by_cases hdLarge : sqrtCoverThreshold K₀ n < A.card - n
    · have horiginalBad := hnOriginal G A B hreg hAB hdUpper hdLarge
      rw [Fintype.card_fin] at hmatchingBad
      exact TwoLargeFinish.forward_large_finish
        (delta := delta) (delta₀ := delta₀) (margin := margin)
        (rho := rho) (sigma := sigma) (eps := eps)
        (alpha := alpha) (kappa := kappa) (n := n) (right := right)
        G A B T A₀ B₀ C JB (by rfl) hmargin hsigma htwoSigma hnpos
        hAB hTA hTcard hA₀ hB₀ hA₀card (by rfl)
        (heta.trans_le halpha.1) hleftCap hrightCap hthresholdNonneg
        hwindowCount hmatchingBad horiginalBad hJBG hJBsupp
        hrightBad htransferBad
    · have hdSmall : A.card - n ≤ sqrtCoverThreshold K₀ n :=
        Nat.le_of_not_gt hdLarge
      have h64K : 64 * K ≤ K₀ := by
        dsimp [K₀]
        omega
      have hdSmall64 : A.card - n ≤ sqrtCoverThreshold (64 * K) n := by
        apply hdSmall.trans
        simpa only [sqrtCoverThreshold] using
          (Nat.div_le_div_left h64K (Nat.mul_pos (by norm_num) hK)
            (a := Nat.sqrt n))
      have hkappaAlpha : kappa ≤ alpha / 64 := by
        change ((A.card - n : ℕ) : ℝ) / Real.sqrt n ≤
          ((C.card : ℝ) / Real.sqrt n) / 64
        exact CompactBoundedForest.small_transfer_ratio hK hdSmall64 hClower
      have hwindowRawSmall :
          ((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n) ≤
            (almostBipartiteCount
              (Finset.univ : Finset (Fin (2 * n)))
              (fun S ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
                ((S ∩ B₀).card + (n - (S ∩ A₀).card)) ∈
                  Set.Icc
                    (-((max (alpha / 4 - kappa) (15 * kappa) - rho) *
                      Real.sqrt 2))
                    ((max (1 / alpha) kappa - rho) * Real.sqrt 2)) : ℝ) := by
        have hp : 0 < (2 : ℝ) ^ (2 * n) := by positivity
        exact (lt_div_iff₀ hp).mp hwindowCount |>.le
      have hsmall := ForwardSmallFinish.small_transfer_goodSample_count
        (delta := delta₀) (margin := margin) (sigma := sigma) (rho := rho)
        (alpha := alpha) (kappa := kappa) (eps := eps)
        G (A := A) (B := B) (T := T) (A₀ := A₀) (B₀ := B₀)
        (C := C) (right := right) (JB := JB)
        hnpos hsigma htwoSigma hAB.1 hTA hA₀ hB₀ hA₀card hTcard
        (by rfl) (heta.trans_le halpha.1) hkappaAlpha hleftCap hrightCap
        hthresholdNonneg hwindowRawSmall
        (by simpa [Fintype.card_fin] using hmatchingBad)
        hJBG hJBsupp hrightBad htransferBad
      exact three_failure_density_subtraction hdelta (by rfl) hmargin.le
        (pow_nonneg (by norm_num) _) hsmall
  · rcases horient with ⟨JA, JB, hJAG, hJBG, hJAsupp, hJBsupp,
      hJAbip, hJBbip, hJAdeg, hJBdeg, hJAedge, hJBedge⟩
    have hDeta : eta₀ * Real.sqrt n ≤ D.card := by
      exact (le_div_iff₀ hsqrt).mp hDratio.1
    obtain ⟨left, hleftCapBeta, hleftBad⟩ :=
      hnForest D C (A₀ \ C) JB hDeta hDupperReal hCupperReal
        hJBbip hJBdeg hJBedge
    have hmatchingBad := hnMatching (Fin (2 * n)) G B₀ D hD hDlower
    rw [Fintype.card_fin] at hmatchingBad
    let beta : ℝ := (D.card : ℝ) / Real.sqrt n
    let alpha : ℝ := 4 / beta
    let kappa : ℝ := ((A.card - n : ℕ) : ℝ) / Real.sqrt n
    have halpha : alpha ∈ Set.Icc eta M := by
      simpa only [alpha, beta, eta, eta₀, M] using
        (AlmostBipartiteRegimeCounts.reciprocal_four_mem_cover_window
          hK hM₀ hDratio)
    have hbeta : 0 < beta := heta₀.trans_le hDratio.1
    have hkappa : kappa ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [kappa]
        exact div_nonneg (by positivity) hsqrt.le
      · rw [div_le_one hsqrt]
        calc
          ((A.card - n : ℕ) : ℝ) ≤ (Nat.sqrt n : ℝ) := by
            exact Nat.cast_le.2 hdUpper
          _ ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
    have hwindowCount := hnWindow B₀ A₀ hcut₀.symm hB₀card hA₀card
      alpha halpha kappa hkappa
    have hepsD : eps * (D.card : ℝ) ≤ sigma * Real.sqrt n / 2 := by
      have hDM : (D.card : ℝ) ≤ M * Real.sqrt n :=
        hDupperReal.trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hsqrt.le)
      dsimp [eps]
      have h := mul_le_mul_of_nonneg_left hDM
        (show 0 ≤ sigma / (2 * M) by positivity)
      field_simp [ne_of_gt hM] at h ⊢
      nlinarith
    let right : ℕ := ⌊(1 / 4 - eps) * (D.card : ℝ)⌋₊
    have hleftCap : (alpha / 4 - sigma) * Real.sqrt n ≤ left := by
      dsimp [alpha, beta]
      convert hleftCapBeta using 1 <;> field_simp [hsqrt.ne']
    have hrightCap : (1 / alpha - sigma) * Real.sqrt n ≤ right := by
      have hcap := matching_floor_capacity hsqrt hsigma hepsD hnRound
      dsimp [alpha, beta, right]
      convert hcap using 1 <;> field_simp [hsqrt.ne']
    have htransferBad := hnTransfer T (hTcard.trans_le hdUpper)
    by_cases hdLarge : sqrtCoverThreshold K₀ n < A.card - n
    · have horiginalBad := hnOriginal G A B hreg hAB hdUpper hdLarge
      exact TwoLargeFinish.swapped_large_finish
        (delta := delta) (delta₀ := delta₀) (margin := margin)
        (eta := eta) (M := M) (rho := rho) (sigma := sigma)
        (eps := eps) (K₀ := left) (n := n)
        G A B T A₀ B₀ C D JB hdelta (by rfl) hmargin heta
        (by simpa only [alpha, beta] using halpha.1)
        (by simpa only [alpha, beta] using halpha.2)
        hrho hsigma htwoSigma hepsQuarter hnpos hnRound hAB hTA hTcard
        hA₀ hB₀ hcut₀ hA₀card hB₀card hD hJBG hJBsupp hdUpper
        hkappa.2 hleftCapBeta hleftBad hmatchingBad hepsD
        htransferBad horiginalBad
        (fun a ha k hk ↦
          hnWindow B₀ A₀ hcut₀.symm hB₀card hA₀card a ha k hk)
    · have hdSmall : A.card - n ≤ sqrtCoverThreshold K₀ n :=
        Nat.le_of_not_gt hdLarge
      have hK₀M₀ : 16 * M₀ ≤ K₀ := by
        dsimp [K₀]
        exact le_max_right _ _
      have hkappaAlpha : kappa ≤ alpha / 64 := by
        change ((A.card - n : ℕ) : ℝ) / Real.sqrt n ≤
          (4 / ((D.card : ℝ) / Real.sqrt n)) / 64
        exact
          AlmostBipartiteRegimeCounts.normalized_le_reciprocal_cover_div_sixtyFour
            hK₀ hM₀ hnpos hK₀M₀ hdSmall hbeta hDratio.2
      exact TwoLargeFinish.swapped_small_finish
        (delta := delta) (delta₀ := delta₀) (margin := margin)
        (rho := rho) (sigma := sigma) (eps := eps)
        (alpha := alpha) (kappa := kappa) (n := n) (left := left)
        G A B T A₀ B₀ D JB hdelta (by rfl) hmargin hrho hsigma
        htwoSigma hepsQuarter hnpos hnRound hAB hTA hTcard hA₀ hB₀
        hA₀card hJBG hJBsupp (heta.trans_le halpha.1) (by rfl)
        hkappaAlpha hleftCap hepsD hrightCap
        hleftBad hmatchingBad htransferBad hwindowCount

/-- Unconditional two-large-cover endpoint.  Covers in a fixed compact
square-root range are handled by the shifted three-forest argument above;
if either cover is larger, the corresponding one-small product theorem
applies because a sufficiently large cover forces its product inequality. -/
theorem eventually_twoLargeCover_goodSample_count
    (delta : ℝ) (hdelta : 0 < delta) (K : ℕ) (hK : 16 ≤ K) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n)))
        (A B T A₀ B₀ C D : Finset (Fin (2 * n))),
        G.IsRegularOfDegree (n + 1) → IsAlmostBipartiteCut G A B →
        T ⊆ A → T.card = A.card - n → A₀ = A \ T → B₀ = B ∪ T →
        IsCut A₀ B₀ → A₀.card = n → B₀.card = n →
        IsMinimumVertexCoverOn G A₀ C →
        IsMinimumVertexCoverOn G B₀ D →
        A.card - n ≤ Nat.sqrt n →
        sqrtCoverThreshold K n ≤ C.card →
        sqrtCoverThreshold K n ≤ D.card →
        ((1 / 2 : ℝ) - delta) * (2 : ℝ) ^ (2 * n) ≤
          (almostBipartiteCount
            (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  obtain ⟨L, hL, hright, hleft⟩ :=
    AlmostBipartiteRegimeCounts.exists_common_scale_eventually_sqrtImbalance_oneSmallCover_counts
      hdelta
  let M₀ : ℕ := 4 * L
  have hKpos : 0 < K := by omega
  have hLpos : 0 < L := by omega
  have hM₀pos : 0 < M₀ := by dsimp [M₀]; positivity
  have hcompact := eventually_compact_twoLargeCover_goodSample_count
    hdelta hKpos hM₀pos
  have hforce :=
    AlmostBipartiteRegimeCounts.eventually_large_sqrtCover_forces_product
      hLpos (show 4 * L ≤ M₀ by rfl)
  filter_upwards [hright, hleft, hcompact, hforce] with
      n hnRight hnLeft hnCompact hnForce
  intro G A B T A₀ B₀ C D hreg hAB hTA hTcard hA₀ hB₀ hcut₀
    hA₀card hB₀card hC hD hdUpper hClower hDlower
  by_cases hCupper : C.card ≤ M₀ * Nat.sqrt n
  · by_cases hDupper : D.card ≤ M₀ * Nat.sqrt n
    · exact hnCompact G A B T A₀ B₀ C D hreg hAB hTA hTcard hA₀ hB₀
        hcut₀ hA₀card hB₀card hC hD hdUpper hClower hDlower
        hCupper hDupper
    · obtain ⟨E, hE⟩ := exists_minimumVertexCoverOn G A
      have hBT : Disjoint B T := hAB.1.1.symm.mono_right hTA
      have hprod := hnForce D.card (lt_of_not_ge hDupper)
      exact hnRight G A B E T B₀ D hreg hAB hE hdUpper hTcard hBT
        hB₀ hD hprod
  · have hprod := hnForce C.card (lt_of_not_ge hCupper)
    exact hnLeft G A B T A₀ C hAB.1
      (by exact_mod_cast hAB.2.1) hdUpper hA₀ hC hprod

end

end TwoLargeCase
end Erdos622

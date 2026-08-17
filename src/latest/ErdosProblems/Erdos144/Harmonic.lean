/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.EqualSums
import ErdosProblems.Erdos144.HarmonicProb
import ErdosProblems.Erdos144.HarmonicBlocks
import ErdosProblems.Erdos144.HarmonicFactorization
import ErdosProblems.Erdos144.HarmonicMoments
import ErdosProblems.Erdos144.HarmonicOctaves
import ErdosProblems.Erdos144.HarmonicRegularity
import ErdosProblems.Erdos321.SignedPairs
import ErdosProblems.Erdos448.Basic
import ErdosProblems.Erdos697.Erdos697Bernoulli

/-!
# The finite harmonic Bernoulli model for Erdős Problem 144

This file packages the finite probability space used in the
Maier--Tenenbaum argument.  The sample points are subsets of a finite set
of positive integers and the integer `i` is present with probability
`1 / i`.  We record the equal-subsum event and the exact complement and
monotonicity identities needed by the analytic part of the argument.
-/

open scoped BigOperators

namespace Erdos144.Harmonic

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The inclusion probability in the harmonic random-set model. -/
def probability (i : ℕ) : ℝ := 1 / (i : ℝ)

/-- Finite harmonic probabilities depend only on the underlying predicate,
not on the particular decidability procedures used to build their filters. -/
theorem prob_congr (I : Finset ℕ) (P Q : Finset ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ S, P S ↔ Q S) :
    Erdos144.HarmonicProb.prob I P = Erdos144.HarmonicProb.prob I Q := by
  unfold Erdos144.HarmonicProb.prob
  apply Finset.sum_congr
  · ext S
    simp [hPQ S]
  · intro S hS
    rfl

/-! ## Explicit scales -/

/-- Loss parameter in the global signed-difference estimate. -/
def xi (s : ℕ) : ℕ := 8 * 9 ^ s

/-- Number of independent fresh-pair stages. -/
def stageCount (s : ℕ) : ℕ := xi s ^ 3

/-- Eight-adic exponent separating successive fresh intervals. -/
def stageStride (s : ℕ) : ℕ := 4 * s

/-- Exponent of the bottom of the global harmonic reservoir. -/
def lowerExponent (s : ℕ) : ℕ := s * stageCount s ^ 2

/-- Bottom index of the harmonic reservoir. -/
def lowerScale (s : ℕ) : ℕ := 8 ^ lowerExponent s

/-- Top index after `j` fresh-pair stages. -/
def stageTop (s j : ℕ) : ℕ :=
  8 ^ (20 * lowerExponent s + stageStride s * j)

/-- Final top index. -/
def finalTop (s : ℕ) : ℕ := stageTop s (stageCount s)

/-- A deliberately loose but explicit selected-cardinality cutoff.  Its
extra factor `xi s` makes its Chernoff tail negligible and leaves ample room
for a block mesh that is still tiny compared with `lowerScale s`. -/
def cardinalCutoff (s : ℕ) : ℕ :=
  xi s * (20 * lowerExponent s + stageStride s * stageCount s + 1)

/-- Mesh used by the downstream prime-block transfer. -/
def transferMesh (s : ℕ) : ℕ := max 1 (cardinalCutoff s ^ 2)

theorem xi_pos (s : ℕ) : 0 < xi s := by
  simp [xi]

theorem stageCount_pos (s : ℕ) : 0 < stageCount s := by
  simp [stageCount, xi]

theorem cardinalCutoff_pos (s : ℕ) : 0 < cardinalCutoff s := by
  exact Nat.mul_pos (xi_pos s) (by positivity)

@[simp] theorem transferMesh_eq (s : ℕ) :
    transferMesh s = cardinalCutoff s ^ 2 := by
  rw [transferMesh, max_eq_right]
  exact pow_pos (cardinalCutoff_pos s) 2

/-- The absolute stage top is the lower scale times an exact eight-adic
depth. -/
theorem stageTop_eq_lowerScale_mul_depth (s j : ℕ) :
    stageTop s j = lowerScale s *
      8 ^ (19 * lowerExponent s + stageStride s * j) := by
  rw [stageTop, lowerScale, ← pow_add]
  congr 1
  omega

/-- The fresh interval `(xi*D,3*xi*D]` fits before the next stage top. -/
theorem three_mul_xi_le_eight_pow_stride {s : ℕ} (hs : 1 ≤ s) :
    3 * xi s ≤ 8 ^ stageStride s := by
  have htwentyfour : 24 ≤ 24 ^ s := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 24) hs
  calc
    3 * xi s = 24 * 9 ^ s := by rw [xi]; ring
    _ ≤ 24 ^ s * 9 ^ s := Nat.mul_le_mul_right (9 ^ s) htwentyfour
    _ = (24 * 9) ^ s := by rw [mul_pow]
    _ ≤ 4096 ^ s := Nat.pow_le_pow_left (by norm_num) s
    _ = (8 ^ 4) ^ s := by norm_num
    _ = 8 ^ stageStride s := by simp [stageStride, pow_mul]

theorem freshInterval_le_nextStageTop {s j : ℕ} (hs : 1 ≤ s) :
    3 * (xi s * stageTop s j) ≤ stageTop s (j + 1) := by
  unfold stageTop
  calc
    3 * (xi s * 8 ^ (20 * lowerExponent s + stageStride s * j)) =
        8 ^ (20 * lowerExponent s + stageStride s * j) * (3 * xi s) := by ring
    _ ≤ 8 ^ (20 * lowerExponent s + stageStride s * j) *
        8 ^ stageStride s :=
      Nat.mul_le_mul_left _ (three_mul_xi_le_eight_pow_stride hs)
    _ = 8 ^ ((20 * lowerExponent s + stageStride s * j) +
        stageStride s) := (pow_add _ _ _).symm
    _ = 8 ^ (20 * lowerExponent s + stageStride s * (j + 1)) := by
      congr 1
      ring

/-- The selected-cardinality cutoff is strictly below its square mesh. -/
theorem cardinalCutoff_lt_transferMesh (s : ℕ) :
    cardinalCutoff s < transferMesh s := by
  rw [transferMesh_eq]
  have htwo : 2 ≤ cardinalCutoff s := by
    have hpow9 : 1 ≤ 9 ^ s := Nat.one_le_pow s 9 (by omega)
    have hxi : 8 ≤ xi s := by
      simpa [xi] using Nat.mul_le_mul_left 8 hpow9
    have hfac : 1 ≤
        20 * lowerExponent s + stageStride s * stageCount s + 1 := by omega
    have hmul := Nat.mul_le_mul_left (xi s) hfac
    have hxicut : xi s ≤ cardinalCutoff s := by
      simpa [cardinalCutoff] using hmul
    omega
  nlinarith

/-- A finite set contains a nontrivial zero signed sum, written as two
disjoint nonempty equal subsums. -/
def HasEqualSubsums (T : Finset ℕ) : Prop :=
  ∃ A B : Finset ℕ,
    A ⊆ T ∧ B ⊆ T ∧ Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
      ∑ i ∈ A, i = ∑ i ∈ B, i

/-- Successful samples from a finite harmonic Bernoulli space. -/
def equalSubsumEvent (s : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact s.powerset.filter HasEqualSubsums

/-- Successful samples subject to a cardinality cutoff. -/
def boundedEqualSubsumEvent (s : Finset ℕ) (K : ℕ) :
    Finset (Finset ℕ) := by
  classical
  exact s.powerset.filter fun T ↦ HasEqualSubsums T ∧ T.card ≤ K

/-- Samples that do not contain equal subsums. -/
def noEqualSubsumEvent (s : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact s.powerset.filter fun T ↦ ¬ HasEqualSubsums T

@[simp] theorem mem_equalSubsumEvent {s T : Finset ℕ} :
  T ∈ equalSubsumEvent s ↔ T ⊆ s ∧ HasEqualSubsums T := by
  simp [equalSubsumEvent]

@[simp] theorem mem_boundedEqualSubsumEvent {s T : Finset ℕ} {K : ℕ} :
    T ∈ boundedEqualSubsumEvent s K ↔
      T ⊆ s ∧ HasEqualSubsums T ∧ T.card ≤ K := by
  simp [boundedEqualSubsumEvent]

@[simp] theorem mem_noEqualSubsumEvent {s T : Finset ℕ} :
    T ∈ noEqualSubsumEvent s ↔ T ⊆ s ∧ ¬ HasEqualSubsums T := by
  simp [noEqualSubsumEvent]

/-- Equal subsums persist when more integers are selected. -/
theorem HasEqualSubsums.mono {S T : Finset ℕ} (hST : S ⊆ T)
    (hS : HasEqualSubsums S) : HasEqualSubsums T := by
  obtain ⟨A, B, hAS, hBS, hAB, hA, hB, hsum⟩ := hS
  exact ⟨A, B, hAS.trans hST, hBS.trans hST, hAB, hA, hB, hsum⟩

/-- The elementary subset-sum pigeonhole criterion implies success. -/
theorem hasEqualSubsums_of_pigeonhole {T : Finset ℕ}
    (hpos : ∀ i ∈ T, 0 < i)
    (hcard : (∑ i ∈ T, i) + 1 < 2 ^ T.card) :
    HasEqualSubsums T := by
  obtain ⟨A, B, hAT, hBT, hdisj, hA, hB, hsum⟩ :=
    EqualSums.exists_disjoint_nonempty_equal_sum T id
      (by simpa using hpos) (by simpa using hcard)
  exact ⟨A, B, hAT, hBT, hdisj, hA, hB, by simpa using hsum⟩

/-- On positive indices the harmonic inclusion probabilities lie in
`[0,1]`. -/
theorem probability_mem_unitInterval {s : Finset ℕ}
    (hpos : ∀ i ∈ s, 0 < i) {i : ℕ} (hi : i ∈ s) :
    0 ≤ probability i ∧ probability i ≤ 1 := by
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hpos i hi
  constructor
  · exact one_div_nonneg.mpr (by positivity)
  · exact (div_le_one (by positivity : (0 : ℝ) < i)).mpr hiR

/-- The exclusion product on an integer interval telescopes exactly. -/
theorem prod_Ioc_one_sub_probability (a k : ℕ) (ha : 0 < a) :
    (∏ i ∈ Finset.Ioc a (a + k), (1 - probability i)) =
      (a : ℝ) / (a + k : ℕ) := by
  induction k with
  | zero => simp [ha.ne']
  | succ k ih =>
      rw [show a + (k + 1) = a + k + 1 by omega,
        Finset.prod_Ioc_succ_top (by omega : a ≤ a + k), ih]
      have hak : (0 : ℝ) < a + k := by positivity
      have haks : (0 : ℝ) < a + k + 1 := by positivity
      rw [probability]
      field_simp
      push_cast
      ring

/-- Removing coordinates from an exclusion product can only increase it. -/
theorem prod_one_sub_probability_le_sdiff
    {s T : Finset ℕ} (hpos : ∀ i ∈ s, 0 < i) :
    (∏ i ∈ s, (1 - probability i)) ≤
      ∏ i ∈ s \ T, (1 - probability i) := by
  apply Finset.prod_le_prod_of_subset_of_le_one Finset.sdiff_subset
  · intro i hi
    have hiunit := probability_mem_unitInterval hpos hi
    linarith
  · intro i hi _
    have hiunit := probability_mem_unitInterval hpos hi
    linarith

/-- Lower bound for the probability weight of selecting exactly a
prescribed fresh pair in an interval.  Keeping the two omitted exclusion
factors would give the slightly sharper source constant; this form is
enough for the iteration. -/
theorem pair_weight_lower_bound
    {a k n m : ℕ} (ha : 0 < a) (hm : 0 < m) :
    probability n * probability (n + m) *
        ((a : ℝ) / (a + k : ℕ)) ≤
      Erdos697.Bernoulli.weight (Finset.Ioc a (a + k)) probability
        {n, n + m} := by
  let s := Finset.Ioc a (a + k)
  have hspos : ∀ i ∈ s, 0 < i := by
    intro i hi
    exact ha.trans (Finset.mem_Ioc.mp hi).1
  have hprod := prod_one_sub_probability_le_sdiff
    (s := s) (T := {n, n + m}) hspos
  have hpairnonneg : 0 ≤ probability n * probability (n + m) := by
    exact mul_nonneg (by simp [probability])
      (one_div_nonneg.mpr (by positivity))
  have hmul := mul_le_mul_of_nonneg_left hprod hpairnonneg
  rw [prod_Ioc_one_sub_probability a k ha] at hmul
  have hne : n ≠ n + m := by omega
  have hsel : (∏ i ∈ ({n, n + m} : Finset ℕ), probability i) =
      probability n * probability (n + m) := by
    rw [Finset.prod_insert (by simpa using hne)]
    simp
  unfold Erdos697.Bernoulli.weight
  rw [hsel]
  exact hmul

/-- Exact partition of the harmonic probability space into success and
failure. -/
theorem sum_weight_equal_add_noEqual (s : Finset ℕ) :
    (∑ T ∈ equalSubsumEvent s,
        Erdos697.Bernoulli.weight s probability T) +
      ∑ T ∈ noEqualSubsumEvent s,
        Erdos697.Bernoulli.weight s probability T = 1 := by
  classical
  rw [← Erdos697.Bernoulli.sum_weight_powerset s probability]
  simp only [equalSubsumEvent, noEqualSubsumEvent, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  by_cases h : HasEqualSubsums T <;> simp [h]

/-- A failure-probability estimate gives the corresponding success lower
bound. -/
theorem one_sub_failure_le_success (s : Finset ℕ) :
    1 - (∑ T ∈ noEqualSubsumEvent s,
      Erdos697.Bernoulli.weight s probability T) ≤
      ∑ T ∈ equalSubsumEvent s,
        Erdos697.Bernoulli.weight s probability T := by
  rw [← sum_weight_equal_add_noEqual s]
  linarith

/-- In fact the previous inequality is an equality; the weak form is
often more convenient for chaining estimates. -/
theorem sum_weight_equal_eq_one_sub_failure (s : Finset ℕ) :
    (∑ T ∈ equalSubsumEvent s,
        Erdos697.Bernoulli.weight s probability T) =
      1 - ∑ T ∈ noEqualSubsumEvent s,
        Erdos697.Bernoulli.weight s probability T := by
  linarith [sum_weight_equal_add_noEqual s]

/-- Intersecting success with a cardinality cutoff loses at most the
failure mass plus the upper-cardinality tail. -/
theorem one_sub_failure_sub_cardTail_le_bounded
    (s : Finset ℕ) (hs : ∀ i ∈ s, 1 ≤ i) (K : ℕ) :
    1 - Erdos144.HarmonicProb.prob s (fun T ↦ ¬ HasEqualSubsums T) -
        Erdos144.HarmonicProb.prob s (fun T ↦ K < T.card) ≤
      Erdos144.HarmonicProb.prob s
        (fun T ↦ HasEqualSubsums T ∧ T.card ≤ K) := by
  classical
  let Q : Finset ℕ → Prop := fun T ↦ HasEqualSubsums T ∧ T.card ≤ K
  let F : Finset ℕ → Prop := fun T ↦ ¬ HasEqualSubsums T
  let H : Finset ℕ → Prop := fun T ↦ K < T.card
  have hnotQ : Erdos144.HarmonicProb.prob s (fun T ↦ ¬ Q T) ≤
      Erdos144.HarmonicProb.prob s (fun T ↦ F T ∨ H T) := by
    apply Erdos144.HarmonicProb.prob_mono s _ _ hs
    intro T hT
    simp only [Q, F, H] at hT ⊢
    by_cases hEq : HasEqualSubsums T
    · right
      exact Nat.lt_of_not_ge (fun hcard ↦ hT ⟨hEq, hcard⟩)
    · exact Or.inl hEq
  have hor := Erdos144.HarmonicProb.prob_or_le s F H hs
  have hcomp := Erdos144.HarmonicProb.prob_add_prob_not s Q
  dsimp only [Q, F, H] at hnotQ hor hcomp ⊢
  linarith

/-! ## Summing disjoint fresh-pair events -/

/-- The finite family of exact two-point samples indexed by a set of
positive represented differences and a set of fresh starting points. -/
def freshPairFamily (M N : Finset ℕ) : Finset (Finset ℕ) :=
  (M ×ˢ N).image fun q ↦ HarmonicBlocks.freshPair q.1 q.2

theorem card_freshPairFamily (M N : Finset ℕ)
    (hM : ∀ m ∈ M, 0 < m) :
    (freshPairFamily M N).card = M.card * N.card := by
  have hinj : Set.InjOn
      (fun q : ℕ × ℕ ↦ HarmonicBlocks.freshPair q.1 q.2)
      (↑(M ×ˢ N) : Set (ℕ × ℕ)) := by
    intro q hq q' hq' heq
    have hqf : q ∈ M ×ˢ N := hq
    have hqf' : q' ∈ M ×ˢ N := hq'
    have hmq : 0 < q.1 := hM q.1 (Finset.mem_product.mp hqf).1
    have hmq' : 0 < q'.1 := hM q'.1 (Finset.mem_product.mp hqf').1
    have hdata := (HarmonicBlocks.freshPair_eq_iff hmq hmq').mp heq
    exact Prod.ext hdata.2 hdata.1
  rw [freshPairFamily, Finset.card_image_of_injOn hinj,
    Finset.card_product]

/-- Because a positive fresh pair remembers its two parameters, the exact
pair events are disjoint and their masses add without a union-bound loss. -/
theorem card_mul_lowerBound_le_sum_freshPairWeights
    (I M N : Finset ℕ) (hM : ∀ m ∈ M, 0 < m) (c : ℝ)
    (hlower : ∀ m ∈ M, ∀ n ∈ N,
      c ≤ Erdos697.Bernoulli.weight I probability
        (HarmonicBlocks.freshPair m n)) :
    ((M.card * N.card : ℕ) : ℝ) * c ≤
      ∑ T ∈ freshPairFamily M N,
        Erdos697.Bernoulli.weight I probability T := by
  let f : ℕ × ℕ → Finset ℕ := fun q ↦
    HarmonicBlocks.freshPair q.1 q.2
  have hinj : Set.InjOn f (↑(M ×ˢ N) : Set (ℕ × ℕ)) := by
    intro q hq q' hq' heq
    have hqf : q ∈ M ×ˢ N := hq
    have hqf' : q' ∈ M ×ˢ N := hq'
    have hmq : 0 < q.1 := hM q.1 (Finset.mem_product.mp hqf).1
    have hmq' : 0 < q'.1 := hM q'.1 (Finset.mem_product.mp hqf').1
    have hdata := (HarmonicBlocks.freshPair_eq_iff hmq hmq').mp heq
    exact Prod.ext hdata.2 hdata.1
  have hsum : (∑ q ∈ M ×ˢ N, c) ≤
      ∑ q ∈ M ×ˢ N,
        Erdos697.Bernoulli.weight I probability (f q) := by
    apply Finset.sum_le_sum
    intro q hq
    exact hlower q.1 (Finset.mem_product.mp hq).1 q.2
      (Finset.mem_product.mp hq).2
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product] at hsum
  have hsumImage :
      (∑ q ∈ M ×ˢ N,
          Erdos697.Bernoulli.weight I probability (f q)) =
        ∑ T ∈ (M ×ˢ N).image f,
          Erdos697.Bernoulli.weight I probability T := by
    exact (Finset.sum_image (s := M ×ˢ N) (g := f)
      (f := fun T ↦ Erdos697.Bernoulli.weight I probability T) hinj).symm
  calc
    ((M.card * N.card : ℕ) : ℝ) * c ≤
        ∑ q ∈ M ×ˢ N,
          Erdos697.Bernoulli.weight I probability (f q) := hsum
    _ = ∑ T ∈ freshPairFamily M N,
          Erdos697.Bernoulli.weight I probability T := by
      simpa [freshPairFamily, f] using hsumImage

/-- Uniform two-hit lower bound on the standard fresh interval. -/
theorem freshPair_weight_lower_on_standard_interval
    {a m n : ℕ} (ha : 0 < a) (han : a < n) (hna : n ≤ 2 * a)
    (hm : 0 < m) (hma : m ≤ a) :
    1 / (27 * (a : ℝ) ^ 2) ≤
      Erdos697.Bernoulli.weight (Finset.Ioc a (3 * a)) probability
        (HarmonicBlocks.freshPair m n) := by
  have hnmb : n + m ≤ 3 * a := by omega
  change 1 / (27 * (a : ℝ) ^ 2) ≤
    Erdos697.Bernoulli.weight (Finset.Ioc a (3 * a))
      (fun i : ℕ ↦ 1 / (i : ℝ)) (HarmonicBlocks.freshPair m n)
  rw [HarmonicBlocks.harmonic_weight_freshPair a (3 * a) m n
    ha han hm hnmb]
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hnNat : 1 < n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast hnNat
  have hnmR : (1 : ℝ) < n + m := by
    exact_mod_cast (lt_of_lt_of_le hnNat (Nat.le_add_right n m))
  have hnCast : (n : ℝ) ≤ 2 * a := by exact_mod_cast hna
  have hnUpper : (n : ℝ) - 1 ≤ 2 * a := by linarith
  have hnmCast : (n + m : ℝ) ≤ 3 * a := by exact_mod_cast hnmb
  have hnmUpper : (n + m : ℝ) - 1 ≤ 3 * a := by
    linarith
  have hxy : ((n : ℝ) - 1) * ((n + m : ℝ) - 1) ≤
      6 * (a : ℝ) ^ 2 := by nlinarith
  have h3a : ((3 * a : ℕ) : ℝ) = 3 * (a : ℝ) := by norm_num
  rw [h3a]
  apply (div_le_div_iff₀
    (by positivity : (0 : ℝ) < 27 * (a : ℝ) ^ 2)
    (by positivity : (0 : ℝ) <
      3 * (a : ℝ) * ((n : ℝ) - 1) * ((n + m : ℝ) - 1))).2
  nlinarith

/-- Summed fresh-pair mass supplied by a finite family of positive
differences bounded by the old scale.  This is the quantitative local step:
each difference can be paired with every starting point in `(a,2a]`, and
the resulting exact two-point samples are distinct. -/
theorem freshPairFamily_mass_lower_on_standard_interval
    {a : ℕ} (ha : 0 < a) (M : Finset ℕ)
    (hMpos : ∀ m ∈ M, 0 < m) (hMle : ∀ m ∈ M, m ≤ a) :
    (((M.card * (Finset.Ioc a (2 * a)).card : ℕ) : ℝ) /
        (27 * (a : ℝ) ^ 2)) ≤
      ∑ T ∈ freshPairFamily M (Finset.Ioc a (2 * a)),
        Erdos697.Bernoulli.weight (Finset.Ioc a (3 * a)) probability T := by
  have h := card_mul_lowerBound_le_sum_freshPairWeights
    (Finset.Ioc a (3 * a)) M (Finset.Ioc a (2 * a)) hMpos
      (1 / (27 * (a : ℝ) ^ 2)) (by
        intro m hm n hn
        exact freshPair_weight_lower_on_standard_interval ha
          (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2
          (hMpos m hm) (hMle m hm))
  simpa [div_eq_mul_inv] using h

/-! ## Positive values in the full ternary signed image -/

/-- Positive values in the full ternary signed image, transported to
natural numbers for the fresh-pair construction. -/
def positiveFullNatDifferenceSet (S : Finset ℕ) : Finset ℕ :=
  ((HarmonicBlocks.fullSignedDifferenceSet S).filter fun z ↦ 0 < z).image
    Int.toNat

@[simp] theorem mem_positiveFullNatDifferenceSet_iff
    {S : Finset ℕ} {m : ℕ} :
    m ∈ positiveFullNatDifferenceSet S ↔
      0 < m ∧ (m : ℤ) ∈ HarmonicBlocks.fullSignedDifferenceSet S := by
  constructor
  · intro hm
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm
    have hzdata := Finset.mem_filter.mp hz
    have hznonneg : 0 ≤ z := hzdata.2.le
    constructor
    · exact Int.pos_iff_toNat_pos.mp hzdata.2
    · rw [Int.toNat_of_nonneg hznonneg]
      exact hzdata.1
  · rintro ⟨hm, hmD⟩
    rw [positiveFullNatDifferenceSet, Finset.mem_image]
    refine ⟨(m : ℤ), ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨hmD, by exact_mod_cast hm⟩

/-- Negating every ternary sign negates a value in the full signed image. -/
theorem neg_mem_fullSignedDifferenceSet {S : Finset ℕ} {z : ℤ}
    (hz : z ∈ HarmonicBlocks.fullSignedDifferenceSet S) :
    -z ∈ HarmonicBlocks.fullSignedDifferenceSet S := by
  rw [HarmonicBlocks.fullSignedDifferenceSet, Finset.mem_image] at hz ⊢
  obtain ⟨a, _ha, rfl⟩ := hz
  refine ⟨(fun i ↦ HarmonicBlocks.swapSign (a i)), ?_, ?_⟩
  · simp [HarmonicBlocks.signedStates]
  · exact HarmonicBlocks.signedValue_swapSign S a

private theorem card_positiveFullNatDifferenceSet (S : Finset ℕ) :
    (positiveFullNatDifferenceSet S).card =
      ((HarmonicBlocks.fullSignedDifferenceSet S).filter fun z ↦ 0 < z).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hxpos := (Finset.mem_filter.mp hx).2
  have hypos := (Finset.mem_filter.mp hy).2
  calc
    x = (x.toNat : ℤ) := (Int.toNat_of_nonneg hxpos.le).symm
    _ = (y.toNat : ℤ) := by rw [hxy]
    _ = y := Int.toNat_of_nonneg hypos.le

/-- The full signed image consists of zero and symmetric positive/negative
pairs. -/
theorem card_fullSignedDifferenceSet_eq_two_mul_positiveFullNat_add_one
    (S : Finset ℕ) :
    (HarmonicBlocks.fullSignedDifferenceSet S).card =
      2 * (positiveFullNatDifferenceSet S).card + 1 := by
  let D := HarmonicBlocks.fullSignedDifferenceSet S
  let P := D.filter fun z ↦ 0 < z
  let N := D.filter fun z ↦ z < 0
  have hzero : (0 : ℤ) ∈ D := by
    change (0 : ℤ) ∈ HarmonicBlocks.fullSignedDifferenceSet S
    rw [HarmonicBlocks.fullSignedDifferenceSet, Finset.mem_image]
    refine ⟨fun _ ↦ 0, by simp [HarmonicBlocks.signedStates], ?_⟩
    simp [HarmonicBlocks.signedValue]
  have hpartition : D = (P ∪ {0}) ∪ N := by
    ext z
    simp only [Finset.mem_union, Finset.mem_singleton]
    change z ∈ D ↔ (z ∈ P ∨ z = 0) ∨ z ∈ N
    simp only [P, N, Finset.mem_filter]
    constructor
    · intro hz
      rcases lt_trichotomy z 0 with hzneg | rfl | hzpos
      · exact Or.inr ⟨hz, hzneg⟩
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl ⟨hz, hzpos⟩)
    · rintro ((⟨hz, _⟩ | rfl) | ⟨hz, _⟩)
      · exact hz
      · exact hzero
      · exact hz
  have hP0 : Disjoint P ({0} : Finset ℤ) := by
    rw [Finset.disjoint_left]
    intro z hzP hz0
    rw [Finset.mem_singleton] at hz0
    subst z
    exact (lt_irrefl 0) (Finset.mem_filter.mp hzP).2
  have hPN : Disjoint (P ∪ ({0} : Finset ℤ)) N := by
    rw [Finset.disjoint_left]
    intro z hzPN hzN
    have hzneg := (Finset.mem_filter.mp hzN).2
    rw [Finset.mem_union, Finset.mem_singleton] at hzPN
    rcases hzPN with hzP | rfl
    · exact (not_lt_of_ge (Finset.mem_filter.mp hzP).2.le) hzneg
    · exact (lt_irrefl 0) hzneg
  have hNP : N.card = P.card := by
    have hset : N = P.image fun z ↦ -z := by
      ext z
      constructor
      · intro hz
        have hzdata := Finset.mem_filter.mp hz
        rw [Finset.mem_image]
        refine ⟨-z, ?_, by simp⟩
        exact Finset.mem_filter.mpr ⟨by
          change -z ∈ HarmonicBlocks.fullSignedDifferenceSet S
          exact neg_mem_fullSignedDifferenceSet hzdata.1
        , by linarith⟩
      · intro hz
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        have hwdata := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨by
          change -w ∈ HarmonicBlocks.fullSignedDifferenceSet S
          exact neg_mem_fullSignedDifferenceSet hwdata.1
        , by linarith⟩
    rw [hset, Finset.card_image_of_injective]
    intro x y hxy
    exact neg_injective hxy
  change D.card = 2 * (positiveFullNatDifferenceSet S).card + 1
  rw [hpartition, Finset.card_union_of_disjoint hPN,
    Finset.card_union_of_disjoint hP0, hNP]
  rw [card_positiveFullNatDifferenceSet]
  change P.card + 1 + P.card = 2 * P.card + 1
  omega

/-- A small normalized full-cube energy and enough ternary states force many
positive represented natural differences.  The constants leave a factor
four before the symmetry loss, which is useful in the fresh-pair step. -/
theorem positiveFullNat_card_large_of_energy
    {S : Finset ℕ} {D ξ : ℕ} (hξD : ξ < D)
    (hstates : 8 * D ≤ ξ * 3 ^ S.card)
    (hoff : 8 * D * HarmonicOctaves.offDiagonalSignedEnergy S ≤
      ξ * (3 ^ S.card) ^ 2) :
    D ≤ ξ * (positiveFullNatDifferenceSet S).card := by
  let A := 3 ^ S.card
  let E := HarmonicOctaves.offDiagonalSignedEnergy S
  have hdiag : 8 * D * A ≤ ξ * A ^ 2 := by
    calc
      8 * D * A ≤ (ξ * A) * A := Nat.mul_le_mul_right A hstates
      _ = ξ * A ^ 2 := by ring
  have htotal : 8 * D * (A + E) ≤ 2 * (ξ * A ^ 2) := by
    calc
      8 * D * (A + E) = 8 * D * A + 8 * D * E := by ring
      _ ≤ ξ * A ^ 2 + ξ * A ^ 2 := Nat.add_le_add hdiag (by
        simpa [A, E] using hoff)
      _ = 2 * (ξ * A ^ 2) := by ring
  have henergy : 4 * D *
      HarmonicBlocks.fullSignedDifferenceEnergy S ≤ ξ * A ^ 2 := by
    have htwice : 2 * (4 * D * (A + E)) ≤ 2 * (ξ * A ^ 2) := by
      convert htotal using 1 <;> ring
    have hhalf := Nat.le_of_mul_le_mul_left htwice (by omega : 0 < 2)
    simpa [HarmonicOctaves.fullSignedDifferenceEnergy_eq_diagonal_add_offDiagonal,
      A, E] using hhalf
  have hfull : 4 * D ≤
      ξ * (HarmonicBlocks.fullSignedDifferenceSet S).card := by
    apply HarmonicBlocks.fullDifference_card_lower_of_energy S (4 * D) ξ
    simpa [A] using henergy
  rw [card_fullSignedDifferenceSet_eq_two_mul_positiveFullNat_add_one] at hfull
  have hfull' : 4 * D ≤
      2 * (ξ * (positiveFullNatDifferenceSet S).card) + ξ := by
    calc
      4 * D ≤ ξ * (2 * (positiveFullNatDifferenceSet S).card + 1) := hfull
      _ = 2 * (ξ * (positiveFullNatDifferenceSet S).card) + ξ := by ring
  by_contra h
  have hsmall : ξ * (positiveFullNatDifferenceSet S).card < D :=
    Nat.lt_of_not_ge h
  omega

/-! ## Markov extraction of a low-energy reservoir -/

/-- Off-diagonal signed energy normalized by the square of the ternary-cube
size. -/
def normalizedOffDiagonalEnergy (S : Finset ℕ) : ℝ :=
  (HarmonicOctaves.offDiagonalSignedEnergy S : ℝ) /
    (9 : ℝ) ^ S.card

theorem normalizedOffDiagonalEnergy_nonneg (S : Finset ℕ) :
    0 ≤ normalizedOffDiagonalEnergy S := by
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

/-- Markov's inequality restricted to an arbitrary good event. -/
theorem prob_good_and_normalizedOffDiagonalEnergy_ge_le
    (I : Finset ℕ) (hI : ∀ n ∈ I, 1 ≤ n)
    (Good : Finset ℕ → Prop) [DecidablePred Good]
    (c : ℝ) (hc : 0 < c) :
    Erdos144.HarmonicProb.prob I
        (fun S ↦ Good S ∧ c ≤ normalizedOffDiagonalEnergy S) ≤
      HarmonicOctaves.normalizedOffDiagonalExpectation I Good / c := by
  let F : Finset ℕ → ℝ := fun S ↦
    if Good S then normalizedOffDiagonalEnergy S else 0
  calc
    Erdos144.HarmonicProb.prob I
        (fun S ↦ Good S ∧ c ≤ normalizedOffDiagonalEnergy S) ≤
        Erdos144.HarmonicProb.prob I (fun S ↦ c ≤ F S) := by
      apply Erdos144.HarmonicProb.prob_mono I _ _ hI
      intro S hS
      simp [F, hS.1, hS.2]
    _ ≤ (∑ S ∈ I.powerset,
          Erdos144.HarmonicProb.weight I S * F S) / c := by
      exact Erdos144.HarmonicProb.prob_le_expectation_div I F c hI
        (fun S _ ↦ by
          dsimp [F]
          split_ifs
          · exact normalizedOffDiagonalEnergy_nonneg S
          · exact le_rfl) hc
    _ = HarmonicOctaves.normalizedOffDiagonalExpectation I Good / c := by
      congr 1
      simp only [Erdos144.HarmonicProb.weight]
      rw [show Erdos144.HarmonicProb.param =
        (fun i : ℕ ↦ 1 / (i : ℝ)) by rfl]
      simp only [F, HarmonicOctaves.normalizedOffDiagonalExpectation,
        Finset.sum_filter, mul_ite, mul_zero]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : Good S <;>
        simp [hS, normalizedOffDiagonalEnergy, Erdos144.HarmonicProb.param,
          div_eq_mul_inv, mul_assoc]

/-- Integral form of the normalized off-diagonal energy cutoff. -/
def OffDiagonalEnergyControlled (D ξ : ℕ) (S : Finset ℕ) : Prop :=
  8 * D * HarmonicOctaves.offDiagonalSignedEnergy S ≤
    ξ * (3 ^ S.card) ^ 2

/-- The expectation estimate converts to the precise exceptional-mass bound
used at one stage of the iteration. -/
theorem prob_regular_and_not_offDiagonalEnergyControlled_le
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    {D s ξ : ℕ} (hI : ∀ n ∈ I, 1 ≤ n) (hD : 0 < D) (hξ : 0 < ξ)
    (hexpect : HarmonicOctaves.normalizedOffDiagonalExpectation I Good ≤
      1200 * (8 : ℝ) ^ s / D) :
    Erdos144.HarmonicProb.prob I
        (fun S ↦ Good S ∧ ¬ OffDiagonalEnergyControlled D ξ S) ≤
      9600 * (8 : ℝ) ^ s / ξ := by
  let c : ℝ := (ξ : ℝ) / (8 * D : ℕ)
  have hc : 0 < c := by
    exact div_pos (by exact_mod_cast hξ) (by positivity)
  have hmono : Erdos144.HarmonicProb.prob I
      (fun S ↦ Good S ∧ ¬ OffDiagonalEnergyControlled D ξ S) ≤
      Erdos144.HarmonicProb.prob I
        (fun S ↦ Good S ∧ c ≤ normalizedOffDiagonalEnergy S) := by
    apply Erdos144.HarmonicProb.prob_mono I _ _ hI
    intro S hS
    refine ⟨hS.1, ?_⟩
    have hbad : ξ * (3 ^ S.card) ^ 2 <
        8 * D * HarmonicOctaves.offDiagonalSignedEnergy S :=
      Nat.lt_of_not_ge hS.2
    have hpow : ((3 : ℝ) ^ S.card) ^ 2 = (9 : ℝ) ^ S.card := by
      calc
        ((3 : ℝ) ^ S.card) ^ 2 = (3 : ℝ) ^ (S.card * 2) := by
          rw [pow_mul]
        _ = (3 : ℝ) ^ (2 * S.card) := by rw [mul_comm]
        _ = ((3 : ℝ) ^ 2) ^ S.card := by rw [pow_mul]
        _ = (9 : ℝ) ^ S.card := by norm_num
    have hbadR0 : (ξ : ℝ) * ((3 : ℝ) ^ S.card) ^ 2 <
        (8 * D : ℕ) *
          (HarmonicOctaves.offDiagonalSignedEnergy S : ℝ) := by
      exact_mod_cast hbad
    have hbadR : (ξ : ℝ) * (9 : ℝ) ^ S.card <
        (8 * D : ℕ) *
          (HarmonicOctaves.offDiagonalSignedEnergy S : ℝ) := by
      simpa [hpow] using hbadR0
    dsimp [c, normalizedOffDiagonalEnergy]
    have hden : (0 : ℝ) < (8 * D : ℕ) := by positivity
    have hpowpos : (0 : ℝ) < (9 : ℝ) ^ S.card := by positivity
    apply le_of_lt
    rw [div_lt_div_iff₀ hden hpowpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbadR
  calc
    Erdos144.HarmonicProb.prob I
        (fun S ↦ Good S ∧ ¬ OffDiagonalEnergyControlled D ξ S) ≤
        Erdos144.HarmonicProb.prob I
          (fun S ↦ Good S ∧ c ≤ normalizedOffDiagonalEnergy S) := hmono
    _ ≤ HarmonicOctaves.normalizedOffDiagonalExpectation I Good / c :=
      prob_good_and_normalizedOffDiagonalEnergy_ge_le I hI Good c hc
    _ ≤ (1200 * (8 : ℝ) ^ s / D) / c := by
      gcongr
    _ = 9600 * (8 : ℝ) ^ s / ξ := by
      dsimp [c]
      have hDR : (0 : ℝ) < D := by exact_mod_cast hD
      have hξR : (0 : ℝ) < ξ := by exact_mod_cast hξ
      norm_num [Nat.cast_mul]
      field_simp
      ring

/-- Exceptional old reservoirs used by the one-step recurrence. -/
def ReservoirIrregular (D R s ξ : ℕ) (S : Finset ℕ) : Prop :=
  ¬ HarmonicOctaves.OctaveRegular D R s S ∨
    (HarmonicOctaves.OctaveRegular D R s S ∧
      ¬ OffDiagonalEnergyControlled D ξ S) ∨
    (ξ : ℝ) * (D : ℝ) < ∑ i ∈ S, (i : ℝ)

/-- Union of regularity, energy, and selected-sum exceptional masses. -/
theorem prob_reservoirIrregular_le
    {I : Finset ℕ} {D R s ξ : ℕ}
    (hI : ∀ n ∈ I, 1 ≤ n) (hID : I ⊆ Finset.Icc 1 D)
    (hD : 0 < D) (hξ : 0 < ξ) (regularityError : ℝ)
    (hregularity : Erdos144.HarmonicProb.prob I
      (fun S ↦ ¬ HarmonicOctaves.OctaveRegular D R s S) ≤
        regularityError)
    (hexpect : HarmonicOctaves.normalizedOffDiagonalExpectation I
        (HarmonicOctaves.OctaveRegular D R s) ≤
      1200 * (8 : ℝ) ^ s / D) :
    Erdos144.HarmonicProb.prob I (ReservoirIrregular D R s ξ) ≤
      regularityError + 9600 * (8 : ℝ) ^ s / ξ + 1 / (ξ : ℝ) := by
  let BadRegularity : Finset ℕ → Prop := fun S ↦
    ¬ HarmonicOctaves.OctaveRegular D R s S
  let BadEnergy : Finset ℕ → Prop := fun S ↦
    HarmonicOctaves.OctaveRegular D R s S ∧
      ¬ OffDiagonalEnergyControlled D ξ S
  let BadSum : Finset ℕ → Prop := fun S ↦
    (ξ : ℝ) * (D : ℝ) < ∑ i ∈ S, (i : ℝ)
  have henergy : Erdos144.HarmonicProb.prob I BadEnergy ≤
      9600 * (8 : ℝ) ^ s / ξ := by
    exact prob_regular_and_not_offDiagonalEnergyControlled_le hI hD hξ hexpect
  have hsum : Erdos144.HarmonicProb.prob I BadSum ≤ 1 / (ξ : ℝ) := by
    exact HarmonicMoments.prob_selected_sum_gt_le_inv I
      (by exact_mod_cast hξ) hD hID
  rw [prob_congr I (ReservoirIrregular D R s ξ)
    (fun S ↦ BadRegularity S ∨ BadEnergy S ∨ BadSum S) (by
      intro S
      simp only [ReservoirIrregular, BadRegularity, BadEnergy, BadSum])]
  calc
    Erdos144.HarmonicProb.prob I
        (fun S ↦ BadRegularity S ∨ BadEnergy S ∨ BadSum S) ≤
        Erdos144.HarmonicProb.prob I BadRegularity +
          Erdos144.HarmonicProb.prob I (fun S ↦ BadEnergy S ∨ BadSum S) :=
      Erdos144.HarmonicProb.prob_or_le I BadRegularity
        (fun S ↦ BadEnergy S ∨ BadSum S) hI
    _ ≤ Erdos144.HarmonicProb.prob I BadRegularity +
        (Erdos144.HarmonicProb.prob I BadEnergy +
          Erdos144.HarmonicProb.prob I BadSum) := by
      gcongr
      exact Erdos144.HarmonicProb.prob_or_le I BadEnergy BadSum hI
    _ ≤ regularityError +
        (9600 * (8 : ℝ) ^ s / ξ + 1 / (ξ : ℝ)) := by
      exact add_le_add hregularity (add_le_add henergy hsum)
    _ = regularityError + 9600 * (8 : ℝ) ^ s / ξ +
        1 / (ξ : ℝ) := by ring

/-! ## Signed differences and their energy -/

/-- Integer sum on the positive side minus the sum on the negative side of
a canonical disjoint signed pair. -/
def signedSum (r : Σ _ : Finset ℕ, Finset ℕ) : ℤ :=
  (∑ i ∈ r.1, (i : ℤ)) - ∑ i ∈ r.2, (i : ℤ)

/-- All signed subset-sum differences supported on `B`. -/
def signedDifferenceSet (B : Finset ℕ) : Finset ℤ :=
  (Erdos321.disjointPairs B).image signedSum

/-- Collision energy of the signed-sum map. -/
def signedEnergy (B : Finset ℕ) : ℕ :=
  Erdos448.occupiedBinEnergy (Erdos321.disjointPairs B) signedSum

theorem mem_disjointPairs_data {B : Finset ℕ}
    {r : Σ _ : Finset ℕ, Finset ℕ}
    (hr : r ∈ Erdos321.disjointPairs B) :
    r.1 ⊆ B ∧ r.2 ⊆ B ∧ Disjoint r.1 r.2 := by
  rw [Erdos321.disjointPairs, Finset.mem_sigma] at hr
  have hU := Finset.mem_powerset.mp hr.1
  have hVdiff := Finset.mem_powerset.mp hr.2
  have hV : r.2 ⊆ B := hVdiff.trans Finset.sdiff_subset
  refine ⟨hU, hV, Finset.disjoint_left.mpr ?_⟩
  intro i hiU hiV
  exact (Finset.mem_sdiff.mp (hVdiff hiV)).2 hiU

@[simp] theorem signedSum_emptyPair :
    signedSum (Sigma.mk ∅ ∅) = 0 := by
  simp [signedSum]

/-- Zero is always a signed difference (via the empty pair). -/
theorem zero_mem_signedDifferenceSet (B : Finset ℕ) :
    0 ∈ signedDifferenceSet B := by
  rw [signedDifferenceSet, Finset.mem_image]
  refine ⟨Sigma.mk ∅ ∅, ?_, signedSum_emptyPair⟩
  simp [Erdos321.disjointPairs]

/-- Swapping the two sides negates a signed sum. -/
theorem signedSum_swap (r : Σ _ : Finset ℕ, Finset ℕ) :
    signedSum (Sigma.mk r.2 r.1) = -signedSum r := by
  simp [signedSum]

/-- The signed-difference set is symmetric under negation. -/
theorem neg_mem_signedDifferenceSet {B : Finset ℕ} {z : ℤ}
    (hz : z ∈ signedDifferenceSet B) :
    -z ∈ signedDifferenceSet B := by
  rw [signedDifferenceSet, Finset.mem_image] at hz ⊢
  obtain ⟨r, hr, rfl⟩ := hz
  refine ⟨Sigma.mk r.2 r.1, ?_, signedSum_swap r⟩
  rw [Erdos321.disjointPairs, Finset.mem_sigma] at hr ⊢
  have hU := Finset.mem_powerset.mp hr.1
  have hVdiff := Finset.mem_powerset.mp hr.2
  constructor
  · exact Finset.mem_powerset.mpr (hVdiff.trans Finset.sdiff_subset)
  · rw [Finset.mem_powerset]
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi, fun hiV ↦
      (Finset.mem_sdiff.mp (hVdiff hiV)).2 hi⟩

/-- Positive represented signed differences. -/
def positiveSignedDifferenceSet (B : Finset ℕ) : Finset ℤ :=
  (signedDifferenceSet B).filter fun z ↦ 0 < z

/-- Negative represented signed differences. -/
def negativeSignedDifferenceSet (B : Finset ℕ) : Finset ℤ :=
  (signedDifferenceSet B).filter fun z ↦ z < 0

/-- Positive differences, transported to natural numbers for the fresh-pair
construction `n,n+m`. -/
def positiveNatDifferenceSet (B : Finset ℕ) : Finset ℕ :=
  (positiveSignedDifferenceSet B).image Int.toNat

@[simp] theorem mem_positiveNatDifferenceSet_iff {B : Finset ℕ} {m : ℕ} :
    m ∈ positiveNatDifferenceSet B ↔
      0 < m ∧ (m : ℤ) ∈ signedDifferenceSet B := by
  constructor
  · intro hm
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm
    have hzdata := Finset.mem_filter.mp hz
    have hznonneg : 0 ≤ z := hzdata.2.le
    constructor
    · exact Int.pos_iff_toNat_pos.mp hzdata.2
    · rw [Int.toNat_of_nonneg hznonneg]
      exact hzdata.1
  · rintro ⟨hm, hmD⟩
    rw [positiveNatDifferenceSet, Finset.mem_image]
    refine ⟨(m : ℤ), ?_, by simp⟩
    exact Finset.mem_filter.mpr ⟨hmD, by exact_mod_cast hm⟩

theorem card_positiveNatDifferenceSet (B : Finset ℕ) :
    (positiveNatDifferenceSet B).card =
      (positiveSignedDifferenceSet B).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  have hxpos := (Finset.mem_filter.mp hx).2
  have hypos := (Finset.mem_filter.mp hy).2
  have hxnonneg : 0 ≤ x := hxpos.le
  have hynonneg : 0 ≤ y := hypos.le
  calc
    x = (x.toNat : ℤ) := (Int.toNat_of_nonneg hxnonneg).symm
    _ = (y.toNat : ℤ) := by rw [hxy]
    _ = y := Int.toNat_of_nonneg hynonneg

/-- Negation bijects positive and negative represented differences. -/
theorem card_negativeSignedDifferenceSet_eq_positive (B : Finset ℕ) :
    (negativeSignedDifferenceSet B).card =
      (positiveSignedDifferenceSet B).card := by
  have hset : negativeSignedDifferenceSet B =
      (positiveSignedDifferenceSet B).image fun z ↦ -z := by
    ext z
    constructor
    · intro hz
      have hzdata := Finset.mem_filter.mp hz
      rw [Finset.mem_image]
      refine ⟨-z, ?_, by simp⟩
      rw [positiveSignedDifferenceSet, Finset.mem_filter]
      exact ⟨by simpa using neg_mem_signedDifferenceSet hzdata.1,
        by linarith⟩
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hwdata := Finset.mem_filter.mp hw
      rw [negativeSignedDifferenceSet, Finset.mem_filter]
      exact ⟨neg_mem_signedDifferenceSet hwdata.1, by linarith⟩
  rw [hset, Finset.card_image_of_injective]
  intro x y hxy
  exact neg_injective hxy

/-- Apart from zero, signed differences occur in positive/negative pairs. -/
theorem card_signedDifferenceSet_eq_two_mul_positive_add_one
    (B : Finset ℕ) :
    (signedDifferenceSet B).card =
      2 * (positiveSignedDifferenceSet B).card + 1 := by
  let D := signedDifferenceSet B
  let P := positiveSignedDifferenceSet B
  let N := negativeSignedDifferenceSet B
  have hpartition : D = (P ∪ {0}) ∪ N := by
    ext z
    simp only [Finset.mem_union, Finset.mem_singleton]
    change z ∈ signedDifferenceSet B ↔
      (z ∈ positiveSignedDifferenceSet B ∨ z = 0) ∨
        z ∈ negativeSignedDifferenceSet B
    constructor
    · intro hz
      rcases lt_trichotomy z 0 with hzneg | rfl | hzpos
      · exact Or.inr (Finset.mem_filter.mpr ⟨hz, hzneg⟩)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hz, hzpos⟩))
    · rintro ((hz | rfl) | hz)
      · exact (Finset.mem_filter.mp hz).1
      · exact zero_mem_signedDifferenceSet B
      · exact (Finset.mem_filter.mp hz).1
  have hP0 : Disjoint P ({0} : Finset ℤ) := by
    rw [Finset.disjoint_left]
    intro z hzP hz0
    rw [Finset.mem_singleton] at hz0
    subst z
    exact (lt_irrefl 0) (Finset.mem_filter.mp hzP).2
  have hPN : Disjoint (P ∪ ({0} : Finset ℤ)) N := by
    rw [Finset.disjoint_left]
    intro z hzPN hzN
    have hzneg := (Finset.mem_filter.mp hzN).2
    rw [Finset.mem_union, Finset.mem_singleton] at hzPN
    rcases hzPN with hzP | rfl
    · have hzpos := (Finset.mem_filter.mp hzP).2
      linarith
    · exact (lt_irrefl 0) hzneg
  change D.card = 2 * P.card + 1
  rw [hpartition, Finset.card_union_of_disjoint hPN,
    Finset.card_union_of_disjoint hP0]
  have hNP : N.card = P.card := by
    simpa [N, P] using card_negativeSignedDifferenceSet_eq_positive B
  rw [hNP]
  simp
  omega

/-- Natural positive differences make up exactly one half of the nonzero
signed-difference set. -/
theorem card_signedDifferenceSet_eq_two_mul_positiveNat_add_one
    (B : Finset ℕ) :
    (signedDifferenceSet B).card =
      2 * (positiveNatDifferenceSet B).card + 1 := by
  rw [card_positiveNatDifferenceSet]
  exact card_signedDifferenceSet_eq_two_mul_positive_add_one B

/-- A global signed-difference spread bound yields quantitatively many
positive natural differences (with a harmless factor `3`). -/
theorem three_mul_loss_positiveNat_card
    {B : Finset ℕ} {D xi : ℕ} (hxiD : xi < D)
    (hspread : D ≤ xi * (signedDifferenceSet B).card) :
    D ≤ 3 * xi * (positiveNatDifferenceSet B).card := by
  have hcard := card_signedDifferenceSet_eq_two_mul_positiveNat_add_one B
  have hpos : 0 < (positiveNatDifferenceSet B).card := by
    by_contra h
    have hz : (positiveNatDifferenceSet B).card = 0 :=
      Nat.eq_zero_of_not_pos h
    rw [hcard, hz] at hspread
    simp at hspread
    exact (not_le_of_gt hxiD) hspread
  calc
    D ≤ xi * (signedDifferenceSet B).card := hspread
    _ = xi * (2 * (positiveNatDifferenceSet B).card + 1) := by rw [hcard]
    _ ≤ 3 * xi * (positiveNatDifferenceSet B).card := by nlinarith

/-- The finite Cauchy--Schwarz energy inequality for harmonic signed
differences. -/
theorem card_disjointPairs_sq_le_difference_card_mul_energy
    (B : Finset ℕ) :
    (3 ^ B.card) ^ 2 ≤ (signedDifferenceSet B).card * signedEnergy B := by
  simpa [signedDifferenceSet, signedEnergy, Erdos321.card_disjointPairs] using
    Erdos448.card_sq_le_card_image_mul_occupiedBinEnergy
      (Erdos321.disjointPairs B) signedSum

/-- A nonempty canonical signed pair of signed sum zero is precisely an
equal-subsum witness. -/
theorem hasEqualSubsums_of_signedPair {B : Finset ℕ}
    {r : Σ _ : Finset ℕ, Finset ℕ}
    (hr : r ∈ Erdos321.disjointPairs B)
    (hBpos : ∀ i ∈ B, 0 < i)
    (hne : r.1.Nonempty ∨ r.2.Nonempty) (hsum : signedSum r = 0) :
    HasEqualSubsums B := by
  have hdata := mem_disjointPairs_data hr
  have hsums : ∑ i ∈ r.1, i = ∑ i ∈ r.2, i := by
    have hcast : (∑ i ∈ r.1, (i : ℤ)) = ∑ i ∈ r.2, (i : ℤ) := by
      simpa [signedSum, sub_eq_zero] using hsum
    have hcast' : ((∑ i ∈ r.1, i : ℕ) : ℤ) =
        ((∑ i ∈ r.2, i : ℕ) : ℤ) := by
      simpa only [Nat.cast_sum] using hcast
    exact Int.ofNat_inj.mp hcast'
  have hboth : r.1.Nonempty ∧ r.2.Nonempty := by
    rcases hne with hleft | hright
    · refine ⟨hleft, ?_⟩
      by_contra h
      have : r.2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hzero : ∑ i ∈ r.1, i = 0 := by simpa [this] using hsums
      have hpos : 0 < ∑ i ∈ r.1, i :=
        Finset.sum_pos (fun i hi ↦ hBpos i (hdata.1 hi)) hleft
      exact (Nat.ne_of_gt hpos) hzero
    · refine ⟨?_, hright⟩
      by_contra h
      have : r.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hzero : ∑ i ∈ r.2, i = 0 := by simpa [this] using hsums.symm
      have hpos : 0 < ∑ i ∈ r.2, i :=
        Finset.sum_pos (fun i hi ↦ hBpos i (hdata.2.1 hi)) hright
      exact (Nat.ne_of_gt hpos) hzero
  exact ⟨r.1, r.2, hdata.1, hdata.2.1, hdata.2.2,
    hboth.1, hboth.2, hsums⟩

/-- A positive old signed difference can be cancelled by a fresh pair
`n,n+m`.  This is the deterministic global-to-local step in the
Maier--Tenenbaum iteration. -/
theorem hasEqualSubsums_of_positive_difference
    {B T : Finset ℕ} {m n : ℕ}
    (hBT : B ⊆ T) (hm : 0 < m)
    (hmDiff : (m : ℤ) ∈ signedDifferenceSet B)
    (hnB : n ∉ B) (hnmB : n + m ∉ B)
    (hnT : n ∈ T) (hnmT : n + m ∈ T) :
    HasEqualSubsums T := by
  rw [signedDifferenceSet, Finset.mem_image] at hmDiff
  obtain ⟨r, hr, hrsum⟩ := hmDiff
  have hdata := mem_disjointPairs_data hr
  have hsumInt :
      (∑ i ∈ r.1, (i : ℤ)) = (∑ i ∈ r.2, (i : ℤ)) + m := by
    rw [← hrsum]
    simp [signedSum]
  have hsumNat : ∑ i ∈ r.1, i = (∑ i ∈ r.2, i) + m := by
    have hcast : ((∑ i ∈ r.1, i : ℕ) : ℤ) =
        (((∑ i ∈ r.2, i : ℕ) + m : ℕ) : ℤ) := by
      simpa only [Nat.cast_sum, Nat.cast_add] using hsumInt
    exact Int.ofNat_inj.mp hcast
  let A := insert n r.1
  let C := insert (n + m) r.2
  have hnR1 : n ∉ r.1 := fun h ↦ hnB (hdata.1 h)
  have hnmR2 : n + m ∉ r.2 := fun h ↦ hnmB (hdata.2.1 h)
  have hn_ne : n ≠ n + m := by omega
  refine ⟨A, C, ?_, ?_, ?_, ⟨n, by simp [A]⟩,
    ⟨n + m, by simp [C]⟩, ?_⟩
  · intro i hi
    change i ∈ insert n r.1 at hi
    rw [Finset.mem_insert] at hi
    exact hi.elim (fun h ↦ h ▸ hnT) (fun h ↦ hBT (hdata.1 h))
  · intro i hi
    change i ∈ insert (n + m) r.2 at hi
    rw [Finset.mem_insert] at hi
    exact hi.elim (fun h ↦ h ▸ hnmT) (fun h ↦ hBT (hdata.2.1 h))
  · rw [Finset.disjoint_left]
    intro i hiA hiC
    change i ∈ insert n r.1 at hiA
    change i ∈ insert (n + m) r.2 at hiC
    rw [Finset.mem_insert] at hiA hiC
    rcases hiA with rfl | hiA
    · rcases hiC with heq | hiC
      · exact hn_ne heq
      · exact hnB (hdata.2.1 hiC)
    · rcases hiC with rfl | hiC
      · exact hnmB (hdata.1 hiA)
      · exact Finset.disjoint_left.mp hdata.2.2 hiA hiC
  · simp [A, C, hnR1, hnmR2, hsumNat]
    omega

/-- A represented positive difference in an old reservoir is converted into
an equal-subsum collision after adjoining its fresh pair. -/
theorem hasEqualSubsums_union_freshPair_of_mem_positiveDifference
    {B : Finset ℕ} {m n : ℕ}
    (hm : m ∈ positiveNatDifferenceSet B)
    (hnB : n ∉ B) (hnmB : n + m ∉ B) :
    HasEqualSubsums (B ∪ HarmonicBlocks.freshPair m n) := by
  have hmdata := mem_positiveNatDifferenceSet_iff.mp hm
  apply hasEqualSubsums_of_positive_difference
    (B := B) (T := B ∪ HarmonicBlocks.freshPair m n)
    Finset.subset_union_left hmdata.1 hmdata.2 hnB hnmB
  · exact Finset.mem_union_right B (by simp [HarmonicBlocks.freshPair])
  · exact Finset.mem_union_right B (by simp [HarmonicBlocks.freshPair])

/-- A collision between two distinct subsets of positive integers can be
cancelled to the disjoint nonempty form used by `HasEqualSubsums`. -/
theorem hasEqualSubsums_of_subsetSumCollision {S : Finset ℕ}
    (hpos : ∀ i ∈ S, 0 < i)
    (hcollision : HarmonicBlocks.HasSubsetSumCollision S) :
    HasEqualSubsums S := by
  rcases hcollision with ⟨U, V, hUS, hVS, hne, hsum⟩
  obtain ⟨A, B, hAU, hBV, hAB, hA, hB, hsumAB⟩ :=
    EqualSums.disjoint_nonempty_equal_sums_of_ne id
      (fun i hi ↦ hpos i (hUS hi)) (fun i hi ↦ hpos i (hVS hi))
      hne (by simpa using hsum)
  exact ⟨A, B, hAU.trans hUS, hBV.trans hVS, hAB, hA, hB,
    by simpa using hsumAB⟩

/-- A positive value in the full ternary image is killed by its fresh pair. -/
theorem hasEqualSubsums_union_freshPair_of_mem_positiveFullDifference
    {B : Finset ℕ} {m n : ℕ}
    (hBpos : ∀ i ∈ B, 0 < i) (hnpos : 0 < n)
    (hm : m ∈ positiveFullNatDifferenceSet B)
    (hnB : n ∉ B) (hnmB : n + m ∉ B) :
    HasEqualSubsums (B ∪ HarmonicBlocks.freshPair m n) := by
  have hmdata := mem_positiveFullNatDifferenceSet_iff.mp hm
  have hrep := HarmonicBlocks.representsDifference_of_nat_mem_fullSignedDifferenceSet
    hmdata.2
  apply hasEqualSubsums_of_subsetSumCollision
  · intro i hi
    rcases Finset.mem_union.mp hi with hiB | hiF
    · exact hBpos i hiB
    · rw [HarmonicBlocks.mem_freshPair] at hiF
      rcases hiF with rfl | rfl
      · exact hnpos
      · omega
  · exact HarmonicBlocks.collision_of_difference_and_freshPair
      hmdata.1 hrep hnB hnmB

/-- Every positive full signed value is at most the sum of its supporting
selected set. -/
theorem positiveFullDifference_le_sum {B : Finset ℕ} {m : ℕ}
    (hm : m ∈ positiveFullNatDifferenceSet B) :
    m ≤ ∑ i ∈ B, i := by
  have hmdata := mem_positiveFullNatDifferenceSet_iff.mp hm
  rcases HarmonicBlocks.representsDifference_of_nat_mem_fullSignedDifferenceSet
      hmdata.2 with ⟨A, C, hAB, hCB, _hdisj, hsum⟩
  have hmA : m ≤ A.sum id := by omega
  have hABsum : A.sum id ≤ B.sum id := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hAB
      (fun i _ _ ↦ Nat.zero_le i)
  simpa only [Finset.sum_apply, id_eq] using hmA.trans hABsum

/-- Exact fresh two-point samples generated by all positive full differences
of an old reservoir. -/
def reservoirFreshSamples (D R s ξ : ℕ) (B : Finset ℕ) :
    Finset (Finset ℕ) :=
  if ReservoirIrregular D R s ξ B then ∅ else
    freshPairFamily (positiveFullNatDifferenceSet B)
      (Finset.Ioc (ξ * D) (2 * (ξ * D)))

/-- One complete global-to-local stage.  All analytic work is isolated in
the old-reservoir irregular-mass bound and the ternary-state lower bound;
the conclusion is the affine recurrence consumed by the iteration. -/
theorem harmonic_extension_bad_bound
    {C D R s ξ : ℕ} (hD : 0 < D) (hξ2 : 2 ≤ ξ) (hξD : ξ < D)
    (delta : ℝ)
    (hstates : ∀ B ∈ (Finset.Ioc C D).powerset,
      ¬ ReservoirIrregular D R s ξ B → 8 * D ≤ ξ * 3 ^ B.card)
    (hirregular : Erdos144.HarmonicProb.prob (Finset.Ioc C D)
      (ReservoirIrregular D R s ξ) ≤ delta) :
    Erdos144.HarmonicProb.prob
        (Finset.Ioc C D ∪ Finset.Ioc (ξ * D) (3 * (ξ * D)))
        (fun T ↦ ¬ HasEqualSubsums T) ≤
      (1 - 1 / (27 * (ξ : ℝ) ^ 2)) *
          Erdos144.HarmonicProb.prob (Finset.Ioc C D)
            (fun B ↦ ¬ HasEqualSubsums B) +
        (1 / (27 * (ξ : ℝ) ^ 2)) * delta := by
  let I := Finset.Ioc C D
  let a := ξ * D
  let J := Finset.Ioc a (3 * a)
  let q : ℝ := 1 / (27 * (ξ : ℝ) ^ 2)
  have hξ : 0 < ξ := by omega
  have ha : 0 < a := Nat.mul_pos hξ hD
  have hDa : D < a := by
    have := Nat.mul_lt_mul_of_pos_right hξ2 hD
    simpa [a] using this
  have hIJ : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro n hnI hnJ
    have hnD := (Finset.mem_Ioc.mp hnI).2
    have han := (Finset.mem_Ioc.mp hnJ).1
    omega
  have hIpos : ∀ n ∈ I, 1 ≤ n := by
    intro n hn
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hJpos : ∀ n ∈ J, 1 ≤ n := by
    intro n hn
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    have hξR : (1 : ℝ) ≤ ξ := by exact_mod_cast (show 1 ≤ ξ by omega)
    have hden : (1 : ℝ) ≤ 27 * (ξ : ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 27 * (ξ : ℝ) ^ 2)]
    simpa only [one_mul] using hden
  have hsampleSubset : ∀ B ∈ I.powerset,
      reservoirFreshSamples D R s ξ B ⊆ J.powerset := by
    intro B hB F hF
    by_cases hreg : ReservoirIrregular D R s ξ B
    · simp [reservoirFreshSamples, hreg] at hF
    simp only [reservoirFreshSamples, hreg, if_false] at hF
    rw [Finset.mem_powerset]
    rw [freshPairFamily, Finset.mem_image] at hF
    rcases hF with ⟨mn, hmn, rfl⟩
    have hm := (Finset.mem_product.mp hmn).1
    have hn := Finset.mem_Ioc.mp (Finset.mem_product.mp hmn).2
    intro x hx
    rw [HarmonicBlocks.mem_freshPair] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_Ioc.mpr ⟨hn.1, hn.2.trans (by omega)⟩
    · have hmle : mn.1 ≤ a := by
        have hnotSum : ¬ ((ξ : ℝ) * (D : ℝ) <
            ∑ i ∈ B, (i : ℝ)) := by
          intro hsum
          exact hreg (Or.inr (Or.inr hsum))
        have hsumNat : ∑ i ∈ B, i ≤ a := by
          have hsumReal : ((∑ i ∈ B, i : ℕ) : ℝ) ≤
              (ξ : ℝ) * (D : ℝ) := by
            simpa only [Nat.cast_sum] using le_of_not_gt hnotSum
          exact_mod_cast hsumReal
        exact (positiveFullDifference_le_sum hm).trans hsumNat
      exact Finset.mem_Ioc.mpr ⟨lt_of_lt_of_le hn.1 (Nat.le_add_right _ _),
        by omega⟩
  apply HarmonicFactorization.extension_bad_bound_of_sampleFamilies
    hIJ hIpos hJpos HasEqualSubsums (ReservoirIrregular D R s ξ)
      (reservoirFreshSamples D R s ξ) q delta hq0 hq1
      (fun _ _ hsub hsuccess ↦ hsuccess.mono hsub) hsampleSubset
  · intro B hB hbad hregular F hF
    simp only [reservoirFreshSamples, hregular, if_false] at hF
    rw [freshPairFamily, Finset.mem_image] at hF
    rcases hF with ⟨mn, hmn, rfl⟩
    have hm := (Finset.mem_product.mp hmn).1
    have hn := Finset.mem_Ioc.mp (Finset.mem_product.mp hmn).2
    have hBsub := Finset.mem_powerset.mp hB
    apply hasEqualSubsums_union_freshPair_of_mem_positiveFullDifference
    · intro i hi
      have := (Finset.mem_Ioc.mp (hBsub hi)).1
      omega
    · exact lt_trans ha hn.1
    · exact hm
    · intro hnB
      have := (Finset.mem_Ioc.mp (hBsub hnB)).2
      omega
    · intro hnmB
      have := (Finset.mem_Ioc.mp (hBsub hnmB)).2
      omega
  · intro B hB hbad hregular
    have hOct : HarmonicOctaves.OctaveRegular D R s B := by
      by_contra h
      exact hregular (Or.inl h)
    have hEnergy : OffDiagonalEnergyControlled D ξ B := by
      by_contra h
      exact hregular (Or.inr (Or.inl ⟨hOct, h⟩))
    have hnotSum : ¬ ((ξ : ℝ) * (D : ℝ) <
        ∑ i ∈ B, (i : ℝ)) := by
      intro h
      exact hregular (Or.inr (Or.inr h))
    let M := positiveFullNatDifferenceSet B
    have hMcard : D ≤ ξ * M.card :=
      positiveFullNat_card_large_of_energy hξD
        (hstates B hB hregular) hEnergy
    have hsumNat : ∑ i ∈ B, i ≤ a := by
      have hsumReal : ((∑ i ∈ B, i : ℕ) : ℝ) ≤
          (ξ : ℝ) * (D : ℝ) := by
        simpa only [Nat.cast_sum] using le_of_not_gt hnotSum
      exact_mod_cast hsumReal
    have hMpos : ∀ m ∈ M, 0 < m := by
      intro m hm
      exact (mem_positiveFullNatDifferenceSet_iff.mp hm).1
    have hMle : ∀ m ∈ M, m ≤ a := by
      intro m hm
      exact (positiveFullDifference_le_sum hm).trans hsumNat
    have hfamily := freshPairFamily_mass_lower_on_standard_interval
      ha M hMpos hMle
    have hNcard : (Finset.Ioc a (2 * a)).card = a := by
      rw [Nat.card_Ioc]
      omega
    rw [hNcard] at hfamily
    have hnumeric : q ≤
        (((M.card * a : ℕ) : ℝ) / (27 * (a : ℝ) ^ 2)) := by
      have hMR : (D : ℝ) ≤ (ξ : ℝ) * M.card := by exact_mod_cast hMcard
      dsimp [q, a]
      have hξR : (0 : ℝ) < ξ := by exact_mod_cast hξ
      have hDR : (0 : ℝ) < D := by exact_mod_cast hD
      push_cast
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 27 * (ξ : ℝ) ^ 2)
        (by positivity : (0 : ℝ) < 27 * ((ξ : ℝ) * D) ^ 2)]
      nlinarith
    calc
      q ≤ ∑ F ∈ reservoirFreshSamples D R s ξ B,
          HarmonicProb.weight J F := by
        apply hnumeric.trans
        simp only [reservoirFreshSamples, hregular, if_false]
        change (((M.card * a : ℕ) : ℝ) / (27 * (a : ℝ) ^ 2)) ≤
          ∑ F ∈ freshPairFamily M (Finset.Ioc a (2 * a)),
            HarmonicProb.weight J F
        unfold HarmonicProb.weight
        rw [show HarmonicProb.param = probability by rfl]
        simpa only [J] using hfamily
      _ = HarmonicProb.prob J
          (fun F ↦ F ∈ reservoirFreshSamples D R s ξ B) := by
        symm
        exact HarmonicFactorization.prob_mem_sampleFamily (hsampleSubset B hB)
  · apply le_trans (Erdos144.HarmonicProb.prob_mono I _ _ hIpos ?_) hirregular
    intro B hB
    exact hB.2

end

end Erdos144.Harmonic

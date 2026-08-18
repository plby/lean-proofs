/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.Hypergraph
import ErdosProblems.Erdos136.McDiarmid

/-!
# Regularising a finite conflict system

This file isolates the regularisation step used before the conflict-free
matching process.  It is the finite, specialised (`ell = 4`) version of
Lemmas 8.5 and 8.6 of Glock--Joos--Kim--Kuehn--Lichev.

There are three logically separate pieces.

* `badPairConflicts` adds the two-conflicts forced by excessive common
  conflict links.  The definitions `conditionC4Count` and
  `conditionC5Count` are the literal local counts called (C4) and (C5) in
  the source.
* `completionTarget`, `degreeDeficit`, and `completionWeight` are the
  source formulas (8.2)--(8.5).  `exists_weightedCompletionLayer` is the
  finite probabilistic bridge: simultaneous estimates for a random layer
  are extracted from the proved McDiarmid inequality and a strict union
  bound.
* `RegularizationCertificate` is the exact interface consumed by the core
  random-greedy theorem.  `regularizedCoreTransfer` proves that an outcome
  for the enlarged system is an outcome for the original system.

No probabilistic principle is assumed: all probability masses are the
explicit finite sums from `Erdos136.McDiarmid`.
-/

namespace Erdos136
namespace CFMRegularization

open Finset
open Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V : Type*} [DecidableEq V]

/-! ## A finite registry of large-parameter requirements -/

/-- A named finite collection of estimates which hold for all sufficiently
large real values of the degree parameter.  Keeping the requirements in one
finite registry makes every subsequent parameter absorption use a single
cutoff. -/
structure LargeDRegistry (ι : Type*) where
  active : Finset ι
  condition : ι -> ℝ -> Prop
  eventually_condition : ∀ i ∈ active, ∀ᶠ d : ℝ in atTop, condition i d

/-- Every finite registry admits one common real cutoff. -/
theorem LargeDRegistry.exists_cutoff {ι : Type*} (R : LargeDRegistry ι) :
    ∃ d0 : ℝ, ∀ d, d0 ≤ d -> ∀ i ∈ R.active, R.condition i d := by
  exact Filter.eventually_atTop.mp
    ((Finset.eventually_all R.active).2 R.eventually_condition)

/-- Natural-parameter version used when the degree parameter is supplied as
a natural number and then cast to `ℝ`. -/
theorem exists_nat_threshold_finset {ι : Type*} (I : Finset ι)
    (P : ι -> ℕ -> Prop)
    (hP : ∀ i ∈ I, ∀ᶠ d : ℕ in atTop, P i d) :
    ∃ d0 : ℕ, ∀ d, d0 ≤ d -> ∀ i ∈ I, P i d := by
  exact Filter.eventually_atTop.mp ((Finset.eventually_all I).2 hP)

/-- Every fixed constant is eventually bounded by a positive real power. -/
theorem eventually_const_le_rpow_real (K a : ℝ) (ha : 0 < a) :
    ∀ᶠ d : ℝ in atTop, K ≤ Real.rpow d a := by
  exact (tendsto_rpow_atTop ha).eventually_ge_atTop K

/-- Constants and lower powers are absorbed by a strictly higher power. -/
theorem eventually_const_mul_rpow_le_rpow_real
    (K a b : ℝ) (hab : a < b) :
    ∀ᶠ d : ℝ in atTop, K * Real.rpow d a ≤ Real.rpow d b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  filter_upwards [eventually_const_le_rpow_real K (b - a) hgap,
      eventually_ge_atTop (1 : ℝ)] with d hK hd
  have hd0 : 0 ≤ d := zero_le_one.trans hd
  calc
    K * Real.rpow d a = Real.rpow d a * K := by ring
    _ ≤ Real.rpow d a * Real.rpow d (b - a) :=
      mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg hd0 a)
    _ = Real.rpow d b := by
      change d ^ a * d ^ (b - a) = d ^ b
      rw [← Real.rpow_add (zero_lt_one.trans_le hd)]
      congr 1
      ring

/-- The same absorption with a positive fixed scale on the right. -/
theorem eventually_const_mul_rpow_le_const_mul_rpow_real
    (K L a b : ℝ) (hL : 0 < L) (hab : a < b) :
    ∀ᶠ d : ℝ in atTop,
      K * Real.rpow d a ≤ L * Real.rpow d b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  filter_upwards [eventually_const_le_rpow_real (K / L) (b - a) hgap,
      eventually_ge_atTop (1 : ℝ)] with d hK hd
  have hd0 : 0 ≤ d := zero_le_one.trans hd
  have hnonneg : 0 ≤ L * Real.rpow d a :=
    mul_nonneg hL.le (Real.rpow_nonneg hd0 a)
  calc
    K * Real.rpow d a = (L * Real.rpow d a) * (K / L) := by
      field_simp [ne_of_gt hL]
    _ ≤ (L * Real.rpow d a) * Real.rpow d (b - a) :=
      mul_le_mul_of_nonneg_left hK hnonneg
    _ = L * Real.rpow d b := by
      change L * d ^ a * d ^ (b - a) = L * d ^ b
      rw [mul_assoc, ← Real.rpow_add (zero_lt_one.trans_le hd)]
      congr 2
      ring

/-- A finite sum of fixed lower-order power terms is eventually absorbed by
one higher power. -/
theorem eventually_sum_const_mul_rpow_le_rpow_real {ι : Type*}
    (I : Finset ι) (hI : I.Nonempty) (K a : ι -> ℝ) (b : ℝ)
    (ha : ∀ i ∈ I, a i < b) :
    ∀ᶠ d : ℝ in atTop,
      (∑ i ∈ I, K i * Real.rpow d (a i)) ≤ Real.rpow d b := by
  have hcard : 0 < (I.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hI
  have hscale : 0 < (1 / (I.card : ℝ) : ℝ) := one_div_pos.mpr hcard
  have hall : ∀ᶠ d : ℝ in atTop,
      ∀ i ∈ I,
        K i * Real.rpow d (a i) ≤
          (1 / (I.card : ℝ)) * Real.rpow d b :=
    (Finset.eventually_all I).2 fun i hi =>
      eventually_const_mul_rpow_le_const_mul_rpow_real
        (K i) (1 / (I.card : ℝ)) (a i) b hscale (ha i hi)
  filter_upwards [hall] with d hd
  calc
    (∑ i ∈ I, K i * Real.rpow d (a i)) ≤
        ∑ _i ∈ I, (1 / (I.card : ℝ)) * Real.rpow d b :=
      Finset.sum_le_sum fun i hi => hd i hi
    _ = Real.rpow d b := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- The deliberately tiny regularisation exponent used when the input
error parameter is `eta`. -/
def rawRegularizationEps (eta : ℝ) : ℝ := eta / 10000

/-- A uniform upper range for the input error. -/
def rawRegularizationEta0 : ℝ := 1 / 10

/-- The genuinely asymptotic numerical requirements used in passing
from the raw conflict system to the three-stage regularised system. -/
inductive RawRegularizationRequirement
  | degreeAtLeastTwo
  | inverseInputSmall
  | badPairAbsorption
  | testInfluence
  | accumulatedLoss
  | entropyPower
  | entropyLog
  deriving DecidableEq

/-- A finite large-degree registry for the raw-to-regularised parameter
conversion.  The concentration scale `d^(1-10 eps)` is deliberately below
all the degree, codegree and test-loss scales occurring in stages 2--4,
while the entropy scale is `d^(eta^3)`. -/
def rawRegularizationRegistry (ell : ℕ) (eta : ℝ)
    (heta0 : 0 < eta) (hetaSmall : eta < 1 / 10) :
    LargeDRegistry RawRegularizationRequirement where
  active := { .degreeAtLeastTwo, .inverseInputSmall,
    .badPairAbsorption, .testInfluence, .accumulatedLoss, .entropyPower,
    .entropyLog }
  condition r d := match r with
    | .degreeAtLeastTwo => 2 ≤ d
    | .inverseInputSmall => Real.rpow d (-eta) ≤ 1 / 2
    | .badPairAbsorption =>
        (ell : ℝ) * Real.rpow d (1 - 2 * eta / 3) ≤
          Real.rpow d (1 - rawRegularizationEps eta / 3)
    | .testInfluence =>
        8 * (ell : ℝ) * d ≤ Real.rpow d (2 + rawRegularizationEps eta / 5)
    | .accumulatedLoss =>
        336 * Real.rpow d (-2 * rawRegularizationEps eta) ≤
          Real.rpow d (-rawRegularizationEps eta)
    | .entropyPower =>
        12 * Real.rpow d (eta ^ 3) ≤
          Real.rpow d (1 - 10 * rawRegularizationEps eta)
    | .entropyLog =>
        4 * Real.log 12 ≤
          Real.rpow d (1 - 10 * rawRegularizationEps eta)
  eventually_condition := by
    intro r _hr
    cases r with
    | degreeAtLeastTwo => exact eventually_ge_atTop 2
    | inverseInputSmall =>
        have h := eventually_const_mul_rpow_le_rpow_real
          2 (-eta) 0 (by linarith)
        filter_upwards [h] with d hd
        have hz : Real.rpow d 0 = 1 := Real.rpow_zero d
        rw [hz] at hd
        nlinarith
    | badPairAbsorption =>
        exact eventually_const_mul_rpow_le_rpow_real (ell : ℝ)
          (1 - 2 * eta / 3) (1 - rawRegularizationEps eta / 3) (by
            simp only [rawRegularizationEps]
            linarith)
    | testInfluence =>
        have h := eventually_const_mul_rpow_le_rpow_real (8 * (ell : ℝ)) 1
            (2 + rawRegularizationEps eta / 5) (by
              simp only [rawRegularizationEps]
              linarith)
        filter_upwards [h] with d hd
        simpa using hd
    | accumulatedLoss =>
        exact eventually_const_mul_rpow_le_rpow_real 336
          (-2 * rawRegularizationEps eta) (-rawRegularizationEps eta) (by
            simp only [rawRegularizationEps]
            linarith)
    | entropyPower =>
        apply eventually_const_mul_rpow_le_rpow_real 12
          (eta ^ 3) (1 - 10 * rawRegularizationEps eta)
        have heta1 : eta < 1 := hetaSmall.trans (by norm_num)
        have heta2lt : eta ^ 2 < 1 := by nlinarith [sq_nonneg eta]
        have heta3lt : eta ^ 3 < eta := by
          have := mul_lt_mul_of_pos_left heta2lt heta0
          nlinarith
        simp only [rawRegularizationEps]
        linarith
    | entropyLog =>
        have h := eventually_const_mul_rpow_le_rpow_real
          (4 * Real.log 12) 0 (1 - 10 * rawRegularizationEps eta) (by
            simp only [rawRegularizationEps]
            linarith)
        filter_upwards [h] with d hd
        have hz : Real.rpow d 0 = 1 := Real.rpow_zero d
        rw [hz, mul_one] at hd
        exact hd

/-- A convenient named package obtained after passing the common cutoff. -/
structure RawRegularizationCutoffSpec (ell : ℕ) (eta d : ℝ) : Prop where
  rankAtLeastFour : 4 ≤ ell
  degreeAtLeastTwo : 2 ≤ d
  inverseInputSmall : Real.rpow d (-eta) ≤ 1 / 2
  badPairAbsorption :
    (ell : ℝ) * Real.rpow d (1 - 2 * eta / 3) ≤
      Real.rpow d (1 - rawRegularizationEps eta / 3)
  testInfluence :
    8 * (ell : ℝ) * d ≤ Real.rpow d (2 + rawRegularizationEps eta / 5)
  accumulatedLoss :
    336 * Real.rpow d (-2 * rawRegularizationEps eta) ≤
      Real.rpow d (-rawRegularizationEps eta)
  entropyPower :
    12 * Real.rpow d (eta ^ 3) ≤
      Real.rpow d (1 - 10 * rawRegularizationEps eta)
  entropyLog :
    4 * Real.log 12 ≤
      Real.rpow d (1 - 10 * rawRegularizationEps eta)

/-- The registry gives one common real cutoff for every raw-to-regularised
numerical absorption. -/
theorem exists_rawRegularizationCutoff (ell : ℕ) (eta : ℝ)
    (hell : 4 ≤ ell) (heta0 : 0 < eta)
    (hetaSmall : eta < rawRegularizationEta0) :
    ∃ d0 : ℝ, ∀ d, d0 ≤ d → RawRegularizationCutoffSpec ell eta d := by
  have hetaSmall' : eta < 1 / 10 := by
    simpa [rawRegularizationEta0] using hetaSmall
  let R := rawRegularizationRegistry ell eta heta0 hetaSmall'
  obtain ⟨d0, hd0⟩ := R.exists_cutoff
  refine ⟨d0, fun d hd => ?_⟩
  have hreq (r : RawRegularizationRequirement) : R.condition r d := by
    apply hd0 d hd r
    cases r <;> simp [R, rawRegularizationRegistry]
  constructor
  · exact hell
  · simpa [R, rawRegularizationRegistry] using
      hreq .degreeAtLeastTwo
  · simpa [R, rawRegularizationRegistry] using
      hreq .inverseInputSmall
  · simpa [R, rawRegularizationRegistry] using
      hreq .badPairAbsorption
  · simpa [R, rawRegularizationRegistry] using
      hreq .testInfluence
  · simpa [R, rawRegularizationRegistry] using
      hreq .accumulatedLoss
  · simpa [R, rawRegularizationRegistry] using
      hreq .entropyPower
  · simpa [R, rawRegularizationRegistry] using
      hreq .entropyLog

/-- The elementary exponent hierarchy behind the registry. -/
theorem rawRegularization_exponent_relations (eta : ℝ)
    (heta0 : 0 < eta) (hetaSmall : eta < 1 / 10) :
    0 < rawRegularizationEps eta ∧
    rawRegularizationEps eta < eta ∧
    -2 * rawRegularizationEps eta < -rawRegularizationEps eta ∧
    1 - 2 * eta / 3 < 1 - rawRegularizationEps eta / 3 ∧
    eta ^ 3 < 1 - 10 * rawRegularizationEps eta ∧
    1 - 10 * rawRegularizationEps eta < 1 - 3 * rawRegularizationEps eta ∧
    1 - 3 * rawRegularizationEps eta < 1 - rawRegularizationEps eta / 4 := by
  have heta1 : eta < 1 := hetaSmall.trans (by norm_num)
  have heta2lt : eta ^ 2 < 1 := by nlinarith [sq_nonneg eta]
  have heta3lt : eta ^ 3 < eta := by
    have := mul_lt_mul_of_pos_left heta2lt heta0
    nlinarith
  simp only [rawRegularizationEps]
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- At any degree beyond the cutoff, the concentration power dominates the
entropy power in precisely the form expected by the finite failure-budget
lemma. -/
theorem RawRegularizationCutoffSpec.failureBudget
    {ell : ℕ} {eta d : ℝ} (h : RawRegularizationCutoffSpec ell eta d) :
    12 * Real.rpow d (eta ^ 3) ≤
        Real.rpow d (1 - 10 * rawRegularizationEps eta) ∧
      4 * Real.log 12 ≤
        Real.rpow d (1 - 10 * rawRegularizationEps eta) :=
  ⟨h.entropyPower, h.entropyLog⟩

/-- The single concentration scale may be relaxed to all standard stage
scales between `1-10 eps` and `1-eps/4`. -/
theorem RawRegularizationCutoffSpec.concentrationScale_le
    {ell : ℕ} {eta d a : ℝ} (h : RawRegularizationCutoffSpec ell eta d)
    (ha : 1 - 10 * rawRegularizationEps eta ≤ a) :
    Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤ Real.rpow d a := by
  exact Real.rpow_le_rpow_of_exponent_le
    (le_trans (by norm_num : (1 : ℝ) ≤ 2) h.degreeAtLeastTwo) ha

/-- The accumulated three-stage loss (`16+64+256 = 336`) is at most the
final `d^-eps` allowance. -/
theorem RawRegularizationCutoffSpec.threeStageLoss
    {ell : ℕ} {eta d X : ℝ} (h : RawRegularizationCutoffSpec ell eta d)
    (hX : 0 ≤ X) :
    336 * (X * Real.rpow d (-2 * rawRegularizationEps eta)) ≤
      X * Real.rpow d (-rawRegularizationEps eta) := by
  calc
    336 * (X * Real.rpow d (-2 * rawRegularizationEps eta)) =
        X * (336 * Real.rpow d (-2 * rawRegularizationEps eta)) := by ring
    _ ≤ X * Real.rpow d (-rawRegularizationEps eta) :=
      mul_le_mul_of_nonneg_left h.accumulatedLoss hX


/-! ## Bad pairs and the literal (C4), (C5) counts -/

/-- Two host edges are a bad pair when they are disjoint and some common
link count exceeds the prescribed bound.  `cutoff s` controls links of
cardinality `s`; for the specialised theorem only `s = 1,2,3` occur. -/
def IsBadPair (H : Hypergraph V) (C : ConflictSystem V)
    (cutoff : Fin 3 -> ℕ) (e f : Finset V) : Prop :=
  e ∈ H ∧ f ∈ H ∧ e ≠ f ∧ Disjoint e f ∧
    ∃ s : Fin 3,
      cutoff s <
        ((conflictLinkLayer C e (s.1 + 1)) ∩
          conflictLinkLayer C f (s.1 + 1)).card

/-- The auxiliary two-conflicts recording all bad pairs. -/
def badPairConflicts (H : Hypergraph V) (C : ConflictSystem V)
    (cutoff : Fin 3 -> ℕ) : ConflictSystem V :=
  (H.powersetCard 2).filter fun p =>
    ∃ e ∈ p, ∃ f ∈ p, IsBadPair H C cutoff e f

@[simp] theorem mem_badPairConflicts
    {H : Hypergraph V} {C : ConflictSystem V} {cutoff : Fin 3 -> ℕ}
    {p : Hypergraph V} :
    p ∈ badPairConflicts H C cutoff ↔
      p ⊆ H ∧ p.card = 2 ∧
        ∃ e ∈ p, ∃ f ∈ p, IsBadPair H C cutoff e f := by
  simp [badPairConflicts, and_assoc]

theorem badPairConflicts_isConflictSystem
    (H : Hypergraph V) (C : ConflictSystem V) (cutoff : Fin 3 -> ℕ) :
    IsConflictSystem H (badPairConflicts H C cutoff) := by
  intro p hp
  exact (mem_badPairConflicts.mp hp).1

theorem badPairConflicts_uniform_two
    (H : Hypergraph V) (C : ConflictSystem V) (cutoff : Fin 3 -> ℕ) :
    IsUniform (badPairConflicts H C cutoff) 2 := by
  intro p hp
  exact (mem_badPairConflicts.mp hp).2.1

/-- Even without using any sparsity hypothesis, the bad-pair degree at a
host edge is at most the number of host edges.  The proof injects a pair
containing `e` into its unique singleton after erasing `e`.  Applications
replace `H.card` by the sharper source bound `d^(1-eps/3)`. -/
theorem degree_badPairConflicts_le_host_card
    (H : Hypergraph V) (C : ConflictSystem V) (cutoff : Fin 3 -> ℕ)
    (e : Finset V) :
    degree (badPairConflicts H C cutoff) e ≤ H.card := by
  rw [degree]
  calc
    ((badPairConflicts H C cutoff).filter fun p => e ∈ p).card
        ≤ (H.powersetCard 1).card := by
          apply Finset.card_le_card_of_injOn (fun p => p.erase e)
          · intro p hp
            have hp' := Finset.mem_filter.mp hp
            have hpB := mem_badPairConflicts.mp hp'.1
            apply Finset.mem_powersetCard.mpr
            refine ⟨Finset.erase_subset e p |>.trans hpB.1, ?_⟩
            rw [Finset.card_erase_of_mem hp'.2, hpB.2.1]
          · intro p hp q hq heq
            have hep : e ∈ p := (Finset.mem_filter.mp hp).2
            have heqmem : e ∈ q := (Finset.mem_filter.mp hq).2
            change p.erase e = q.erase e at heq
            calc
              p = insert e (p.erase e) := (Finset.insert_erase hep).symm
              _ = insert e (q.erase e) := by rw [heq]
              _ = q := Finset.insert_erase heqmem
    _ = H.card := by simp

/-- The neighbours of `e` in the two-conflict layer. -/
def twoConflictNeighbors (H : Hypergraph V) (C : ConflictSystem V)
    (e : Finset V) : Hypergraph V :=
  H.filter fun f => f ≠ e ∧ {e, f} ∈ conflictLayer C 2

/-- The source condition (C4): two-conflict neighbours of `e` which use
the host vertex `v`. -/
def conditionC4Count (H : Hypergraph V) (C : ConflictSystem V)
    (e : Finset V) (v : V) : ℕ :=
  ((twoConflictNeighbors H C e).filter fun f => v ∈ f).card

/-- The source condition (C5): common two-conflict neighbours of two
disjoint host edges. -/
def conditionC5Count (H : Hypergraph V) (C : ConflictSystem V)
    (e f : Finset V) : ℕ :=
  ((twoConflictNeighbors H C e) ∩ twoConflictNeighbors H C f).card

theorem conditionC4Count_le_neighbors_card
    (H : Hypergraph V) (C : ConflictSystem V) (e : Finset V) (v : V) :
    conditionC4Count H C e v ≤ (twoConflictNeighbors H C e).card := by
  exact Finset.card_filter_le _ _

theorem conditionC5Count_le_left
    (H : Hypergraph V) (C : ConflictSystem V) (e f : Finset V) :
    conditionC5Count H C e f ≤ (twoConflictNeighbors H C e).card := by
  exact Finset.card_le_card Finset.inter_subset_left

/-! ### The counting bound behind the bad-pair degree estimate -/

/-- Partners whose common `s`-link with `e` is larger than `cutoff`. -/
def badPartnersAt (H : Hypergraph V) (C : ConflictSystem V)
    (s cutoff : ℕ) (e : Finset V) : Hypergraph V :=
  H.filter fun f =>
    cutoff < ((conflictLinkLayer C e s) ∩ conflictLinkLayer C f s).card

/-- Double-count common members of a fixed finite family `A` and the
families `B f`. -/
theorem sum_card_inter_eq_sum_filter_card
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (F : Finset X) (A : Finset Y) (B : X -> Finset Y) :
    ∑ x ∈ F, (A ∩ B x).card =
      ∑ y ∈ A, (F.filter fun x => y ∈ B x).card := by
  calc
    ∑ x ∈ F, (A ∩ B x).card =
        ∑ x ∈ F, ∑ y ∈ A, if y ∈ B x then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [show A ∩ B x = A.filter (fun y => y ∈ B x) by ext y; simp]
          rw [Finset.card_filter]
    _ = ∑ y ∈ A, ∑ x ∈ F, if y ∈ B x then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ y ∈ A, (F.filter fun x => y ∈ B x).card := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [Finset.card_filter]

/-- Finite Markov counting: if each member of the fixed link has at most
`K` partner extensions, then the number of partners whose common link has
more than `cutoff` members is at most the displayed product ratio.  This
is the combinatorial heart of the degree bound in Lemma 8.5. -/
theorem cutoff_succ_mul_badPartnersAt_card_le
    (H : Hypergraph V) (C : ConflictSystem V)
    (s cutoff K : ℕ) (e : Finset V)
    (hext : ∀ S ∈ conflictLinkLayer C e s,
      ((H.filter fun f => S ∈ conflictLinkLayer C f s).card) ≤ K) :
    (cutoff + 1) * (badPartnersAt H C s cutoff e).card ≤
      (conflictLinkLayer C e s).card * K := by
  let L := conflictLinkLayer C e s
  let bad := badPartnersAt H C s cutoff e
  have hlower :
      bad.card * (cutoff + 1) ≤
        ∑ f ∈ bad, (L ∩ conflictLinkLayer C f s).card := by
    calc
      bad.card * (cutoff + 1) = ∑ _f ∈ bad, (cutoff + 1 : ℕ) := by simp
      _ ≤ ∑ f ∈ bad, (L ∩ conflictLinkLayer C f s).card := by
        apply Finset.sum_le_sum
        intro f hf
        have hlarge := (Finset.mem_filter.mp hf).2
        dsimp [L]
        omega
  have hmono :
      (∑ f ∈ bad, (L ∩ conflictLinkLayer C f s).card) ≤
        ∑ f ∈ H, (L ∩ conflictLinkLayer C f s).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro _ _ _
      omega
  have hupper :
      (∑ f ∈ H, (L ∩ conflictLinkLayer C f s).card) ≤ L.card * K := by
    rw [sum_card_inter_eq_sum_filter_card]
    calc
      (∑ S ∈ L, (H.filter fun f => S ∈ conflictLinkLayer C f s).card)
          ≤ ∑ _S ∈ L, K := by
            apply Finset.sum_le_sum
            intro S hS
            exact hext S hS
      _ = L.card * K := by simp
  rw [Nat.mul_comm]
  exact hlower.trans (hmono.trans hupper)

/-! ## Bad pairs do not kill trackable tests -/

/-- The real-power cutoff which is exactly the upper bound in (W3). -/
def trackableCutoff (d eta : ℝ) (s : Fin 3) : ℕ :=
  Nat.floor (Real.rpow d ((s.1 + 1 : ℕ) - eta))

/-- A positive member of a trackable test cannot contain an auxiliary bad
pair.  This is the threshold contradiction used in Lemma 8.5. -/
theorem trackable_conflictFree_badPairs
    {H : Hypergraph V} {C : ConflictSystem V} {j ell : ℕ}
    {d eta : ℝ} {w : TestWeight V}
    (hell : 4 ≤ ell)
    (hw : IsTrackable H C j ell d eta w)
    {S : Hypergraph V} (hSH : S ∈ H.powersetCard j) (hwS : 0 < w S) :
    ConflictFree (badPairConflicts H C (trackableCutoff d eta)) S := by
  intro p hpB hpS
  obtain ⟨_hpH, hp2, e, hep, f, hfp, hbad⟩ := mem_badPairConflicts.mp hpB
  obtain ⟨_heH, _hfH, hef, _hdisj, s, hsbad⟩ := hbad
  have hse : e ∈ S := hpS hep
  have hsf : f ∈ S := hpS hfp
  have hspos : 1 ≤ s.1 + 1 := by omega
  have hsell : s.1 + 1 < ell := by
    have hslt : s.1 < 3 := s.2
    omega
  have hupper := hw.link_intersection_upper hSH hwS hse hsf hef hspos hsell
  have hfloor :
      ((conflictLinkLayer C e (s.1 + 1)) ∩
        conflictLinkLayer C f (s.1 + 1)).card ≤
        trackableCutoff d eta s := by
    exact Nat.le_floor hupper
  exact (not_lt_of_ge hfloor) hsbad

/-- The same threshold contradiction when the auxiliary bad-pair exponent
is smaller than the input trackability exponent.  This is the form used by
the raw-to-regularised theorem, whose internal error is a fixed small
fraction of the source error. -/
theorem trackable_conflictFree_badPairs_of_eta_le
    {H : Hypergraph V} {C : ConflictSystem V} {j ell : ℕ}
    {d etaRaw etaBad : ℝ} {w : TestWeight V}
    (hell : 4 ≤ ell) (hd : 1 ≤ d) (heta : etaBad ≤ etaRaw)
    (hw : IsTrackable H C j ell d etaRaw w)
    {S : Hypergraph V} (hSH : S ∈ H.powersetCard j) (hwS : 0 < w S) :
    ConflictFree (badPairConflicts H C (trackableCutoff d etaBad)) S := by
  intro p hpB hpS
  obtain ⟨_hpH, _hp2, e, hep, f, hfp, hbad⟩ :=
    mem_badPairConflicts.mp hpB
  obtain ⟨_heH, _hfH, hef, _hdisj, s, hsbad⟩ := hbad
  have hse : e ∈ S := hpS hep
  have hsf : f ∈ S := hpS hfp
  have hspos : 1 ≤ s.1 + 1 := by omega
  have hsell : s.1 + 1 < ell := by omega
  have hraw :=
    hw.link_intersection_upper hSH hwS hse hsf hef hspos hsell
  have hupper :
      (((conflictLinkLayer C e (s.1 + 1)) ∩
        conflictLinkLayer C f (s.1 + 1)).card : ℝ) ≤
        Real.rpow d ((s.1 + 1 : ℕ) - etaBad) :=
    hraw.trans (Real.rpow_le_rpow_of_exponent_le hd (by linarith))
  have hfloor :
      ((conflictLinkLayer C e (s.1 + 1)) ∩
        conflictLinkLayer C f (s.1 + 1)).card ≤
        trackableCutoff d etaBad s := by
    exact Nat.le_floor hupper
  exact (not_lt_of_ge hfloor) hsbad

/-! ### The sharp bad-pair degree estimate -/

/-- Erasing the distinguished host edge identifies its rank-`s` conflict
link with the incident part of the rank-`s+1` conflict layer. -/
theorem card_conflictLinkLayer_eq_degree_layer
    (C : ConflictSystem V) (e : Finset V) (s : ℕ) :
    (conflictLinkLayer C e s).card =
      degree (conflictLayer C (s + 1)) e := by
  rw [conflictLinkLayer, conflictLayer, conflictLink, degree]
  let F := (C.filter fun c => e ∈ c).filter fun c => (c.erase e).card = s
  have himage :
      ((C.filter fun c => e ∈ c).image fun c => c.erase e).filter
          (fun c => c.card = s) = F.image fun c => c.erase e := by
    ext t
    dsimp only [F]
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨c, hc, rfl⟩, ht⟩
      exact ⟨c, ⟨hc, ht⟩, rfl⟩
    · rintro ⟨c, ⟨hc, ht⟩, rfl⟩
      exact ⟨⟨c, hc, rfl⟩, ht⟩
  rw [himage]
  have hinj : Set.InjOn (fun c : Hypergraph V => c.erase e) F := by
    intro c hc c' hc' hcc'
    have hec : e ∈ c :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
    have hec' : e ∈ c' :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hc').1).2
    dsimp only at hcc'
    calc
      c = insert e (c.erase e) := (insert_erase hec).symm
      _ = insert e (c'.erase e) := by rw [hcc']
      _ = c' := insert_erase hec'
  rw [card_image_iff.mpr hinj]
  change F.card = ((C.filter fun c => c.card = s + 1).filter fun c => e ∈ c).card
  congr 1
  ext c
  simp only [F, Finset.mem_filter]
  constructor
  · intro hcF
    have hc : c ∈ C := hcF.1.1
    have hec : e ∈ c := hcF.1.2
    have hcard : (c.erase e).card = s := hcF.2
    have hcpos : 0 < c.card := Finset.card_pos.mpr ⟨e, hec⟩
    refine ⟨⟨hc, ?_⟩, hec⟩
    rw [card_erase_of_mem hec] at hcard
    omega
  · intro hcL
    have hc : c ∈ C := hcL.1.1
    have hcard : c.card = s + 1 := hcL.1.2
    have hec : e ∈ c := hcL.2
    refine ⟨⟨hc, hec⟩, ?_⟩
    rw [card_erase_of_mem hec, hcard]
    omega

/-- Partners extending a fixed link member inject into the corresponding
conflict-layer codegree. -/
theorem partner_extensions_le_codegree
    (H : Hypergraph V) (C : ConflictSystem V)
    (S : Hypergraph V) (s : ℕ) :
    (H.filter fun f => S ∈ conflictLinkLayer C f s).card ≤
      codegree (conflictLayer C (s + 1)) S := by
  rw [codegree]
  apply Finset.card_le_card_of_injOn (fun f : Finset V => insert f S)
  · intro f hf
    have hlink : S ∈ conflictLinkLayer C f s := (Finset.mem_filter.mp hf).2
    obtain ⟨⟨c, hcC, hfc, herase⟩, hScard⟩ :=
      mem_conflictLinkLayer.mp hlink
    have hfc_eq : c = insert f S := by
      calc
        c = insert f (c.erase f) := (Finset.insert_erase hfc).symm
        _ = insert f S := by rw [herase]
    have hfS : f ∉ S := by
      rw [← herase]
      simp
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · simpa [← hfc_eq] using hcC
      · rw [Finset.card_insert_of_notMem hfS, hScard]
    · exact Finset.subset_insert f S
  · intro f hf g hg heq
    have hlinkf : S ∈ conflictLinkLayer C f s := (Finset.mem_filter.mp hf).2
    have hlinkg : S ∈ conflictLinkLayer C g s := (Finset.mem_filter.mp hg).2
    obtain ⟨⟨cf, _hcfC, _hfcf, herasef⟩, _⟩ :=
      mem_conflictLinkLayer.mp hlinkf
    obtain ⟨⟨cg, _hcgC, _hgcg, heraseg⟩, _⟩ :=
      mem_conflictLinkLayer.mp hlinkg
    have hfS : f ∉ S := by rw [← herasef]; simp
    have hgS : g ∉ S := by rw [← heraseg]; simp
    dsimp only at heq
    have hmem : f ∈ insert g S := by
      rw [← heq]
      exact Finset.mem_insert_self f S
    exact (Finset.mem_insert.mp hmem).resolve_right hfS

theorem IsBadPair.symm' {H : Hypergraph V} {C : ConflictSystem V}
    {cutoff : Fin 3 → ℕ} {e f : Finset V}
    (h : IsBadPair H C cutoff e f) : IsBadPair H C cutoff f e := by
  rcases h with ⟨heH, hfH, hef, hdisj, s, hs⟩
  refine ⟨hfH, heH, Ne.symm hef, hdisj.symm, s, ?_⟩
  simpa [Finset.inter_comm] using hs

def allBadPartners (H : Hypergraph V) (C : ConflictSystem V)
    (cutoff : Fin 3 → ℕ) (e : Finset V) : Hypergraph V :=
  Finset.univ.biUnion fun s : Fin 3 =>
    badPartnersAt H C (s.1 + 1) (cutoff s) e

/-- Every auxiliary pair through `e` has a unique other member, which is
one of the three possible bad-link partners of `e`. -/
theorem degree_badPairConflicts_le_allBadPartners
    (H : Hypergraph V) (C : ConflictSystem V)
    (cutoff : Fin 3 → ℕ) (e : Finset V) :
    degree (badPairConflicts H C cutoff) e ≤
      (allBadPartners H C cutoff e).card := by
  rw [degree]
  calc
    ((badPairConflicts H C cutoff).filter fun p => e ∈ p).card
        ≤ ((allBadPartners H C cutoff e).powersetCard 1).card := by
      apply Finset.card_le_card_of_injOn (fun p => p.erase e)
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        obtain ⟨_hpH, hp2, x, hxp, y, hyp, hxybad⟩ :=
          mem_badPairConflicts.mp hp'.1
        have hxy : x ≠ y := hxybad.2.2.1
        have hp_eq : p = {x, y} := by
          apply Finset.Subset.antisymm
          · intro z hzp
            have hzxy : z = x ∨ z = y := by
              by_contra hz
              push Not at hz
              have hthree : ({x, y, z} : Hypergraph V) ⊆ p := by
                simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
                exact ⟨hxp, hyp, hzp⟩
              have hcardthree : ({x, y, z} : Hypergraph V).card = 3 := by
                have hxmem : x ∉ ({y, z} : Hypergraph V) := by
                  simp [hxy, Ne.symm hz.1]
                have hymem : y ∉ ({z} : Hypergraph V) := by
                  simpa using Ne.symm hz.2
                rw [Finset.card_insert_of_notMem hxmem,
                  Finset.card_insert_of_notMem hymem]
                simp
              have hle := Finset.card_le_card hthree
              rw [hcardthree, hp2] at hle
              omega
            simpa [hzxy]
          · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
            exact ⟨hxp, hyp⟩
        have hexy : e = x ∨ e = y := by
          rw [hp_eq] at hp'
          simpa using hp'.2
        apply Finset.mem_powersetCard.mpr
        constructor
        · intro f hferase
          have hfp : f ∈ p := (Finset.mem_erase.mp hferase).2
          have hfe : f ≠ e := (Finset.mem_erase.mp hferase).1
          have hfxy : f = x ∨ f = y := by
            rw [hp_eq] at hfp
            simpa using hfp
          have hefBad : IsBadPair H C cutoff e f := by
            rcases hexy with rfl | rfl
            · rcases hfxy with rfl | rfl
              · exact False.elim (hfe rfl)
              · exact hxybad
            · rcases hfxy with rfl | rfl
              · exact hxybad.symm'
              · exact False.elim (hfe rfl)
          obtain ⟨_heH, hfH, _hef, _hdisj, s, hs⟩ := hefBad
          apply Finset.mem_biUnion.mpr
          refine ⟨s, Finset.mem_univ s, ?_⟩
          exact Finset.mem_filter.mpr ⟨hfH, hs⟩
        · rw [Finset.card_erase_of_mem hp'.2, hp2]
      · intro p hp q hq heq
        have hep : e ∈ p := (Finset.mem_filter.mp hp).2
        have heqmem : e ∈ q := (Finset.mem_filter.mp hq).2
        dsimp only at heq
        calc
          p = insert e (p.erase e) := (Finset.insert_erase hep).symm
          _ = insert e (q.erase e) := by rw [heq]
          _ = q := Finset.insert_erase heqmem
    _ = (allBadPartners H C cutoff e).card := by simp

theorem degree_badPairConflicts_le_sum_badPartners
    (H : Hypergraph V) (C : ConflictSystem V)
    (cutoff : Fin 3 → ℕ) (e : Finset V) :
    degree (badPairConflicts H C cutoff) e ≤
      ∑ s : Fin 3, (badPartnersAt H C (s.1 + 1) (cutoff s) e).card := by
  exact (degree_badPairConflicts_le_allBadPartners H C cutoff e).trans
    (Finset.card_biUnion_le.trans_eq (by simp))

/-- The original C1--C3 bounds give the sharp Markov estimate for one
nontrivial common-link rank. -/
theorem badPartnersAt_trackableCutoff_bound
    (H : Hypergraph V) (C : ConflictSystem V)
    {d eps eta : ℝ} (hC : IsBounded C d 4 eps) (hd : 0 < d)
    (k : ℕ) (hk2 : 2 ≤ k) (hk3 : k ≤ 3) (e : Finset V) :
    ((badPartnersAt H C k
        (Nat.floor (Real.rpow d ((k : ℝ) - eta))) e).card : ℝ) ≤
      (4 * Real.rpow d (k : ℝ) * Real.rpow d (1 - eps)) /
        Real.rpow d ((k : ℝ) - eta) := by
  let K := Nat.floor (Real.rpow d (1 - eps))
  have hext : ∀ S ∈ conflictLinkLayer C e k,
      (H.filter fun f => S ∈ conflictLinkLayer C f k).card ≤ K := by
    intro S hS
    have hScard : S.card = k := (mem_conflictLinkLayer.mp hS).2
    apply Nat.le_floor
    calc
      ((H.filter fun f => S ∈ conflictLinkLayer C f k).card : ℝ) ≤
          (codegree (conflictLayer C (k + 1)) S : ℝ) := by
        exact_mod_cast partner_extensions_le_codegree H C S k
      _ ≤ Real.rpow d (((k + 1 : ℕ) : ℝ) - (k : ℝ) - eps) :=
        hC.layer_codegree (by omega) (by omega) hk2 (by omega) S hScard
      _ = Real.rpow d (1 - eps) := by
        congr 1
        push_cast
        ring
  have hmark := cutoff_succ_mul_badPartnersAt_card_le H C k
    (Nat.floor (Real.rpow d ((k : ℝ) - eta))) K e hext
  have hmarkR :
      (((Nat.floor (Real.rpow d ((k : ℝ) - eta)) + 1) : ℕ) : ℝ) *
          ((badPartnersAt H C k
            (Nat.floor (Real.rpow d ((k : ℝ) - eta))) e).card : ℝ) ≤
        ((conflictLinkLayer C e k).card : ℝ) * (K : ℝ) := by
    exact_mod_cast hmark
  have hlink : ((conflictLinkLayer C e k).card : ℝ) ≤
      4 * Real.rpow d (k : ℝ) := by
    rw [card_conflictLinkLayer_eq_degree_layer]
    calc
      (degree (conflictLayer C (k + 1)) e : ℝ) ≤
          4 * Real.rpow d (((k + 1 : ℕ) : ℝ) - 1) :=
        hC.layer_degree (by omega) (by omega) e
      _ = 4 * Real.rpow d (k : ℝ) := by
        congr 2
        push_cast
        ring
  have hK : (K : ℝ) ≤ Real.rpow d (1 - eps) := by
    exact Nat.floor_le (Real.rpow_nonneg hd.le _)
  have hprod : ((conflictLinkLayer C e k).card : ℝ) * (K : ℝ) ≤
      4 * Real.rpow d (k : ℝ) * Real.rpow d (1 - eps) := by
    exact mul_le_mul hlink hK (Nat.cast_nonneg K)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hd.le _))
  have hden : 0 < Real.rpow d ((k : ℝ) - eta) := Real.rpow_pos_of_pos hd _
  have hfloor : Real.rpow d ((k : ℝ) - eta) ≤
      (((Nat.floor (Real.rpow d ((k : ℝ) - eta)) + 1) : ℕ) : ℝ) := by
    norm_num
    exact (Nat.lt_floor_add_one _).le
  apply (le_div_iff₀ hden).2
  calc
    ((badPartnersAt H C k
        (Nat.floor (Real.rpow d ((k : ℝ) - eta))) e).card : ℝ) *
          Real.rpow d ((k : ℝ) - eta) =
        Real.rpow d ((k : ℝ) - eta) *
          ((badPartnersAt H C k
            (Nat.floor (Real.rpow d ((k : ℝ) - eta))) e).card : ℝ) := by ring
    _ ≤ (((Nat.floor (Real.rpow d ((k : ℝ) - eta)) + 1) : ℕ) : ℝ) *
          ((badPartnersAt H C k
            (Nat.floor (Real.rpow d ((k : ℝ) - eta))) e).card : ℝ) := by
      apply mul_le_mul_of_nonneg_right hfloor
      positivity
    _ ≤ ((conflictLinkLayer C e k).card : ℝ) * (K : ℝ) := hmarkR
    _ ≤ 4 * Real.rpow d (k : ℝ) * Real.rpow d (1 - eps) := hprod

theorem badPartner_ratio_eq (d eps eta : ℝ) (hd : 0 < d) (k : ℕ) :
    (4 * Real.rpow d (k : ℝ) * Real.rpow d (1 - eps)) /
        Real.rpow d ((k : ℝ) - eta) =
      4 * Real.rpow d (1 - eps + eta) := by
  rw [show 4 * Real.rpow d (k : ℝ) * Real.rpow d (1 - eps) /
      Real.rpow d ((k : ℝ) - eta) =
      4 * ((Real.rpow d (k : ℝ) * Real.rpow d (1 - eps)) /
        Real.rpow d ((k : ℝ) - eta)) by ring]
  congr 1
  change d ^ (k : ℝ) * d ^ (1 - eps) / d ^ ((k : ℝ) - eta) =
    d ^ (1 - eps + eta)
  rw [← Real.rpow_add hd (k : ℝ) (1 - eps)]
  rw [← Real.rpow_sub hd ((k : ℝ) + (1 - eps)) ((k : ℝ) - eta)]
  congr 1
  ring

theorem conflictLinkLayer_one_eq_empty_of_bounded
    {C : ConflictSystem V} {d eps : ℝ}
    (hC : IsBounded C d 4 eps) (e : Finset V) :
    conflictLinkLayer C e 1 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨⟨c, hcC, hec, herase⟩, hScard⟩ :=
    mem_conflictLinkLayer.mp hS
  have hcpos : 0 < c.card := Finset.card_pos.mpr ⟨e, hec⟩
  have hccard : c.card = 2 := by
    have herasecard : (c.erase e).card = 1 := by rw [herase, hScard]
    rw [Finset.card_erase_of_mem hec] at herasecard
    omega
  have hge := (hC.conflict_card hcC).1
  omega

theorem badPartnersAt_one_eq_empty_of_bounded
    (H : Hypergraph V) {C : ConflictSystem V} {d eps : ℝ}
    (hC : IsBounded C d 4 eps) (cutoff : ℕ) (e : Finset V) :
    badPartnersAt H C 1 cutoff e = ∅ := by
  rw [badPartnersAt, conflictLinkLayer_one_eq_empty_of_bounded hC e]
  simp

/-- Summing the two nonzero link ranks gives the source's
`8 d^(1-eps+eta)` bad-pair degree estimate. -/
theorem degree_badPairConflicts_trackableCutoff_le
    (H : Hypergraph V) (C : ConflictSystem V)
    {d eps eta : ℝ} (hC : IsBounded C d 4 eps) (hd : 0 < d)
    (e : Finset V) :
    (degree (badPairConflicts H C (trackableCutoff d eta)) e : ℝ) ≤
      8 * Real.rpow d (1 - eps + eta) := by
  have hnat := degree_badPairConflicts_le_sum_badPartners H C
    (trackableCutoff d eta) e
  have hreal :
      (degree (badPairConflicts H C (trackableCutoff d eta)) e : ℝ) ≤
        ∑ s : Fin 3,
          ((badPartnersAt H C (s.1 + 1)
            (trackableCutoff d eta s) e).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (degree (badPairConflicts H C (trackableCutoff d eta)) e : ℝ) ≤
        ∑ s : Fin 3,
          ((badPartnersAt H C (s.1 + 1)
            (trackableCutoff d eta s) e).card : ℝ) := hreal
    _ ≤ ∑ s : Fin 3, if s.1 = 0 then 0 else
          4 * Real.rpow d (1 - eps + eta) := by
      apply Finset.sum_le_sum
      intro s _hs
      by_cases hs0 : s.1 = 0
      · simp only [hs0, ↓reduceIte]
        have hs : s = (0 : Fin 3) := Fin.ext hs0
        rw [hs]
        rw [badPartnersAt_one_eq_empty_of_bounded H hC]
        simp
      · simp only [hs0, ↓reduceIte]
        rw [trackableCutoff]
        have hk2 : 2 ≤ s.1 + 1 := by omega
        have hk3 : s.1 + 1 ≤ 3 := by omega
        exact (badPartnersAt_trackableCutoff_bound H C hC hd
          (s.1 + 1) hk2 hk3 e).trans_eq
            (badPartner_ratio_eq d eps eta hd (s.1 + 1))
    _ = 8 * Real.rpow d (1 - eps + eta) := by
      simp only [Fin.sum_univ_succ, Fin.val_zero, ↓reduceIte, Fin.val_succ]
      norm_num
      ring

theorem degree_badPairConflicts_trackableCutoff_target
    (H : Hypergraph V) (C : ConflictSystem V)
    {d eps eta : ℝ} (hC : IsBounded C d 4 eps) (hd : 0 < d)
    (habsorb : 8 * Real.rpow d (1 - eps + eta) ≤
      Real.rpow d (1 - eta)) (e : Finset V) :
    (degree (badPairConflicts H C (trackableCutoff d eta)) e : ℝ) ≤
      Real.rpow d (1 - eta) :=
  (degree_badPairConflicts_trackableCutoff_le H C hC hd e).trans habsorb

/-- If every original conflict has rank four, all link layers below rank
three are empty. -/
theorem conflictLinkLayer_eq_empty_of_card_four_of_lt_three
    {C : ConflictSystem V} (hcard : ∀ c ∈ C, c.card = 4)
    (e : Finset V) (s : ℕ) (hs : s < 3) :
    conflictLinkLayer C e s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨⟨c, hcC, hec, herase⟩, hScard⟩ :=
    mem_conflictLinkLayer.mp hS
  have hcpos : 0 < c.card := Finset.card_pos.mpr ⟨e, hec⟩
  have herasecard : (c.erase e).card = s := by rw [herase, hScard]
  rw [Finset.card_erase_of_mem hec, hcard c hcC] at herasecard
  omega

theorem badPartnersAt_eq_empty_of_card_four_of_lt_three
    (H : Hypergraph V) {C : ConflictSystem V}
    (hcard : ∀ c ∈ C, c.card = 4)
    (s cutoff : ℕ) (hs : s < 3) (e : Finset V) :
    badPartnersAt H C s cutoff e = ∅ := by
  rw [badPartnersAt,
    conflictLinkLayer_eq_empty_of_card_four_of_lt_three hcard e s hs]
  simp

/-- Rank-three version of the Markov estimate with the original arbitrary
boundedness parameter `ell`. -/
theorem badPartnersAt_three_trackableCutoff_bound_card_four
    (H : Hypergraph V) (C : ConflictSystem V)
    {d etaRaw etaBad : ℝ} {ell : ℕ}
    (hC : IsBounded C d ell etaRaw) (hell : 4 ≤ ell) (hd : 0 < d)
    (e : Finset V) :
    ((badPartnersAt H C 3
        (Nat.floor (Real.rpow d (3 - etaBad))) e).card : ℝ) ≤
      ((ell : ℝ) * Real.rpow d 3 * Real.rpow d (1 - etaRaw)) /
        Real.rpow d (3 - etaBad) := by
  let K := Nat.floor (Real.rpow d (1 - etaRaw))
  have hext : ∀ S ∈ conflictLinkLayer C e 3,
      (H.filter fun f => S ∈ conflictLinkLayer C f 3).card ≤ K := by
    intro S hS
    have hScard : S.card = 3 := (mem_conflictLinkLayer.mp hS).2
    apply Nat.le_floor
    calc
      ((H.filter fun f => S ∈ conflictLinkLayer C f 3).card : ℝ) ≤
          (codegree (conflictLayer C 4) S : ℝ) := by
        exact_mod_cast partner_extensions_le_codegree H C S 3
      _ ≤ Real.rpow d ((4 : ℝ) - (3 : ℝ) - etaRaw) :=
        hC.layer_codegree (j := 4) (j' := 3)
          (by norm_num) hell (by norm_num) (by norm_num) S hScard
      _ = Real.rpow d (1 - etaRaw) := by norm_num
  have hmark := cutoff_succ_mul_badPartnersAt_card_le H C 3
    (Nat.floor (Real.rpow d (3 - etaBad))) K e hext
  have hmarkR :
      (((Nat.floor (Real.rpow d (3 - etaBad)) + 1) : ℕ) : ℝ) *
          ((badPartnersAt H C 3
            (Nat.floor (Real.rpow d (3 - etaBad))) e).card : ℝ) ≤
        ((conflictLinkLayer C e 3).card : ℝ) * (K : ℝ) := by
    exact_mod_cast hmark
  have hlink : ((conflictLinkLayer C e 3).card : ℝ) ≤
      (ell : ℝ) * Real.rpow d 3 := by
    rw [card_conflictLinkLayer_eq_degree_layer]
    convert hC.layer_degree (j := 4) (by norm_num) hell e using 1 <;>
      norm_num
  have hK : (K : ℝ) ≤ Real.rpow d (1 - etaRaw) :=
    Nat.floor_le (Real.rpow_nonneg hd.le _)
  have hprod : ((conflictLinkLayer C e 3).card : ℝ) * (K : ℝ) ≤
      (ell : ℝ) * Real.rpow d 3 * Real.rpow d (1 - etaRaw) := by
    exact mul_le_mul hlink hK (Nat.cast_nonneg K)
      (mul_nonneg (Nat.cast_nonneg ell) (Real.rpow_nonneg hd.le _))
  have hden : 0 < Real.rpow d (3 - etaBad) := Real.rpow_pos_of_pos hd _
  have hfloor : Real.rpow d (3 - etaBad) ≤
      (((Nat.floor (Real.rpow d (3 - etaBad)) + 1) : ℕ) : ℝ) := by
    norm_num
    exact (Nat.lt_floor_add_one _).le
  apply (le_div_iff₀ hden).2
  calc
    ((badPartnersAt H C 3
        (Nat.floor (Real.rpow d (3 - etaBad))) e).card : ℝ) *
          Real.rpow d (3 - etaBad) =
        Real.rpow d (3 - etaBad) *
          ((badPartnersAt H C 3
            (Nat.floor (Real.rpow d (3 - etaBad))) e).card : ℝ) := by ring
    _ ≤ (((Nat.floor (Real.rpow d (3 - etaBad)) + 1) : ℕ) : ℝ) *
          ((badPartnersAt H C 3
            (Nat.floor (Real.rpow d (3 - etaBad))) e).card : ℝ) := by
      apply mul_le_mul_of_nonneg_right hfloor
      positivity
    _ ≤ ((conflictLinkLayer C e 3).card : ℝ) * (K : ℝ) := hmarkR
    _ ≤ (ell : ℝ) * Real.rpow d 3 * Real.rpow d (1 - etaRaw) := hprod

theorem badPartner_ratio_eq_general (d etaRaw etaBad : ℝ)
    (ell : ℕ) (hd : 0 < d) :
    ((ell : ℝ) * Real.rpow d 3 * Real.rpow d (1 - etaRaw)) /
        Real.rpow d (3 - etaBad) =
      (ell : ℝ) * Real.rpow d (1 - etaRaw + etaBad) := by
  rw [show (ell : ℝ) * Real.rpow d 3 * Real.rpow d (1 - etaRaw) /
      Real.rpow d (3 - etaBad) =
      (ell : ℝ) * ((Real.rpow d 3 * Real.rpow d (1 - etaRaw)) /
        Real.rpow d (3 - etaBad)) by ring]
  congr 1
  change d ^ (3 : ℝ) * d ^ (1 - etaRaw) / d ^ (3 - etaBad) =
    d ^ (1 - etaRaw + etaBad)
  rw [← Real.rpow_add hd (3 : ℝ) (1 - etaRaw)]
  rw [← Real.rpow_sub hd ((3 : ℝ) + (1 - etaRaw)) (3 - etaBad)]
  congr 1
  ring

/-- Raw rank-four conflicts produce only the rank-three bad-link term, so
the auxiliary degree has coefficient `ell` rather than the coarse `8`. -/
theorem degree_badPairConflicts_trackableCutoff_le_card_four
    (H : Hypergraph V) (C : ConflictSystem V)
    {d etaRaw etaBad : ℝ} {ell : ℕ}
    (hC : IsBounded C d ell etaRaw) (hcard : ∀ c ∈ C, c.card = 4)
    (hell : 4 ≤ ell) (hd : 0 < d) (e : Finset V) :
    (degree (badPairConflicts H C (trackableCutoff d etaBad)) e : ℝ) ≤
      (ell : ℝ) * Real.rpow d (1 - etaRaw + etaBad) := by
  have hnat := degree_badPairConflicts_le_sum_badPartners H C
    (trackableCutoff d etaBad) e
  have hreal :
      (degree (badPairConflicts H C (trackableCutoff d etaBad)) e : ℝ) ≤
        ∑ s : Fin 3,
          ((badPartnersAt H C (s.1 + 1)
            (trackableCutoff d etaBad s) e).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (degree (badPairConflicts H C (trackableCutoff d etaBad)) e : ℝ) ≤
        ∑ s : Fin 3,
          ((badPartnersAt H C (s.1 + 1)
            (trackableCutoff d etaBad s) e).card : ℝ) := hreal
    _ ≤ ∑ s : Fin 3, if s.1 = 2 then
          (ell : ℝ) * Real.rpow d (1 - etaRaw + etaBad) else 0 := by
      apply Finset.sum_le_sum
      intro s _hs
      by_cases hs2 : s.1 = 2
      · simp only [hs2, ↓reduceIte]
        have hs : s = (2 : Fin 3) := Fin.ext hs2
        rw [hs, trackableCutoff]
        exact (badPartnersAt_three_trackableCutoff_bound_card_four
          H C hC hell hd e).trans_eq
            (badPartner_ratio_eq_general d etaRaw etaBad ell hd)
      · simp only [hs2, ↓reduceIte]
        have hlt : s.1 + 1 < 3 := by omega
        rw [badPartnersAt_eq_empty_of_card_four_of_lt_three
          H hcard (s.1 + 1) (trackableCutoff d etaBad s) hlt e]
        simp
    _ = (ell : ℝ) * Real.rpow d (1 - etaRaw + etaBad) := by
      simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
      norm_num

theorem degree_badPairConflicts_trackableCutoff_target_card_four
    (H : Hypergraph V) (C : ConflictSystem V)
    {d etaRaw etaBad : ℝ} {ell : ℕ}
    (hC : IsBounded C d ell etaRaw) (hcard : ∀ c ∈ C, c.card = 4)
    (hell : 4 ≤ ell) (hd : 0 < d)
    (habsorb : (ell : ℝ) * Real.rpow d (1 - etaRaw + etaBad) ≤
      Real.rpow d (1 - etaBad)) (e : Finset V) :
    (degree (badPairConflicts H C (trackableCutoff d etaBad)) e : ℝ) ≤
      Real.rpow d (1 - etaBad) :=
  (degree_badPairConflicts_trackableCutoff_le_card_four
    H C hC hcard hell hd e).trans habsorb

/-! ## The source completion weights -/

/-- Maximum degree of one conflict layer, measured on host edges. -/
def layerMaxDegree (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ) : ℕ :=
  H.sup fun e => degree (conflictLayer C j) e

theorem degree_layer_le_layerMaxDegree {H : Hypergraph V}
    {C : ConflictSystem V} {j : ℕ} {e : Finset V} (he : e ∈ H) :
    degree (conflictLayer C j) e ≤ layerMaxDegree H C j := by
  exact Finset.le_sup he

/-- Source-faithful boundedness for a regularised conflict system.  Unlike
`Erdos136.IsBounded`, this deliberately permits the auxiliary two-conflicts
required by Lemma 8.5.  The clauses are precisely (C1)--(C5), specialised
to conflict sizes at most four. -/
def IsRegularizedBounded (H : Hypergraph V) (C : ConflictSystem V)
    (d Gamma eta : ℝ) : Prop :=
  (∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4) ∧
  (∑ r ∈ Finset.Icc 2 4,
      (layerMaxDegree H C r : ℝ) / Real.rpow d ((r : ℝ) - 1)) ≤ Gamma ∧
  ((((Finset.Icc 2 4).filter fun r => conflictLayer C r ≠ ∅).card : ℕ) : ℝ) ≤ Gamma ∧
  (∀ r, 2 ≤ r -> r ≤ 4 -> ∀ q, 2 ≤ q -> q < r -> ∀ root,
    root.card = q ->
      (codegree (conflictLayer C r) root : ℝ) ≤
        Real.rpow d ((r : ℝ) - (q : ℝ) - eta)) ∧
  (∀ e ∈ H, ∀ v,
    (conditionC4Count H C e v : ℝ) ≤ Real.rpow d (1 - eta)) ∧
  (∀ e ∈ H, ∀ f ∈ H, Disjoint e f ->
    (conditionC5Count H C e f : ℝ) ≤ Real.rpow d (1 - eta))

theorem IsRegularizedBounded.conflict_card
    {H : Hypergraph V} {C : ConflictSystem V} {d Gamma eta : ℝ}
    (hC : IsRegularizedBounded H C d Gamma eta)
    {c : Hypergraph V} (hc : c ∈ C) :
    2 ≤ c.card ∧ c.card ≤ 4 :=
  hC.1 c hc

theorem IsRegularizedBounded.layer_codegree
    {H : Hypergraph V} {C : ConflictSystem V} {d Gamma eta : ℝ}
    (hC : IsRegularizedBounded H C d Gamma eta)
    {r q : ℕ} (hr2 : 2 ≤ r) (hr4 : r ≤ 4)
    (hq2 : 2 ≤ q) (hqr : q < r) (root : Hypergraph V)
    (hroot : root.card = q) :
    (codegree (conflictLayer C r) root : ℝ) ≤
      Real.rpow d ((r : ℝ) - (q : ℝ) - eta) :=
  hC.2.2.2.1 r hr2 hr4 q hq2 hqr root hroot

/-- Specialised target degree from (8.2), with `ell = 4`. -/
def completionTarget (d eps layerDelta : ℝ) (j : ℕ) : ℝ :=
  (1 + Real.rpow d (-eps / 4)) *
    max (Real.rpow d ((j : ℝ) - 1 - eps / 600)) layerDelta

/-- The deficit `a(e)` before completing layer `j`. -/
def degreeDeficit (C : ConflictSystem V) (j : ℕ) (target : ℝ)
    (e : Finset V) : ℝ :=
  target - degree (conflictLayer C j) e

/-- Sum of all deficits on the host edge set. -/
def totalDeficit (H : Hypergraph V) (a : Finset V -> ℝ) : ℝ :=
  ∑ e ∈ H, a e

/-- The independent selection weight from (8.5):
`(j-1)! * prod_(e in A) a(e) / (sum_e a(e))^(j-1)`. -/
def completionWeight (H : Hypergraph V) (j : ℕ)
    (a : Finset V -> ℝ) (A : Hypergraph V) : ℝ :=
  (Nat.factorial (j - 1) : ℝ) * (∏ e ∈ A, a e) /
    (totalDeficit H a) ^ (j - 1)

/-- The exact deficit window (8.4) used at one source completion stage. -/
def HasSourceDeficitBoundsAtTarget (H : Hypergraph V)
    (C : ConflictSystem V) (d eps Gamma target : ℝ) (j : ℕ) : Prop :=
  2 ≤ j ∧ j ≤ 4 ∧
  ∀ e ∈ H,
    Real.rpow d ((j : ℝ) - 1 - 2 * eps) ≤
        degreeDeficit C j target e ∧
      degreeDeficit C j target e ≤
        4 * Gamma * Real.rpow d ((j : ℝ) - 1)

def HasSourceDeficitBounds (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma : ℝ) (j : ℕ) : Prop :=
  2 ≤ j ∧ j ≤ 4 ∧
  let D := completionTarget d eps (layerMaxDegree H C j : ℝ) j
  ∀ e ∈ H,
    Real.rpow d ((j : ℝ) - 1 - 2 * eps) ≤ degreeDeficit C j D e ∧
      degreeDeficit C j D e ≤ 4 * Gamma * Real.rpow d ((j : ℝ) - 1)

theorem hasSourceDeficitBounds_iff_atTarget
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma : ℝ) (j : ℕ) :
    HasSourceDeficitBounds H C d eps Gamma j ↔
      HasSourceDeficitBoundsAtTarget H C d eps Gamma
        (completionTarget d eps (layerMaxDegree H C j : ℝ) j) j := by
  rfl

theorem completionWeight_nonneg
    (H : Hypergraph V) (j : ℕ) (a : Finset V → ℝ)
    (ha : ∀ e ∈ H, 0 ≤ a e)
    {A : Hypergraph V} (hAH : A ⊆ H) :
    0 ≤ completionWeight H j a A := by
  apply div_nonneg
  · apply mul_nonneg
    · positivity
    · apply Finset.prod_nonneg
      intro e heA
      exact ha e (hAH heA)
  · apply pow_nonneg
    rw [totalDeficit]
    apply Finset.sum_nonneg
    intro e he
    exact ha e he

/-- Candidate new conflicts at stage `j`: matchings which contain no old
conflict. -/
def completionCandidates (H : Hypergraph V) (C : ConflictSystem V)
    (j : ℕ) : ConflictSystem V :=
  (H.powersetCard j).filter fun A => IsMatching H A ∧ ConflictFree C A

@[simp] theorem mem_completionCandidates
    {H : Hypergraph V} {C : ConflictSystem V} {j : ℕ} {A : Hypergraph V} :
    A ∈ completionCandidates H C j ↔
      A ⊆ H ∧ A.card = j ∧ IsMatching H A ∧ ConflictFree C A := by
  simp [completionCandidates, and_assoc]

theorem completionCandidates_isConflictSystem
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ) :
    IsConflictSystem H (completionCandidates H C j) := by
  intro A hA
  exact (mem_completionCandidates.mp hA).1

theorem completionCandidates_uniform
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ) :
    IsUniform (completionCandidates H C j) j := by
  intro A hA
  exact (mem_completionCandidates.mp hA).2.1

/-- Finite index type for the literal candidate family. -/
abbrev CompletionIndex (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ) :=
  {A // A ∈ completionCandidates H C j}

/-- An enumeration of all candidate completions. -/
def completionCandidate (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (i : Fin (Fintype.card (CompletionIndex H C j))) : Hypergraph V :=
  ((Fintype.equivFin (CompletionIndex H C j)).symm i).1

theorem completionCandidate_injective
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ) :
    Function.Injective (completionCandidate H C j) := by
  intro i i' hii'
  apply (Fintype.equivFin (CompletionIndex H C j)).symm.injective
  apply Subtype.ext
  exact hii'

theorem completionCandidate_mem (H : Hypergraph V) (C : ConflictSystem V)
    (j : ℕ) (i : Fin (Fintype.card (CompletionIndex H C j))) :
    completionCandidate H C j i ∈ completionCandidates H C j :=
  ((Fintype.equivFin (CompletionIndex H C j)).symm i).2

/-- The source Bernoulli bias obtained by substituting the deficit into
formula (8.5). -/
def sourceCompletionBiasAtTarget (H : Hypergraph V) (C : ConflictSystem V)
    (j : ℕ) (target : ℝ)
    (i : Fin (Fintype.card (CompletionIndex H C j))) : ℝ :=
  completionWeight H j (degreeDeficit C j target)
    (completionCandidate H C j i)

/-- Convenience wrapper whose target uses the current layer maximum.  In the
three-stage construction the more general `sourceCompletionBiasAtTarget` is
used with the fixed pre-regularisation layer maximum. -/
def sourceCompletionBias (H : Hypergraph V) (C : ConflictSystem V)
    (d eps : ℝ) (j : ℕ)
    (i : Fin (Fintype.card (CompletionIndex H C j))) : ℝ :=
  let D := completionTarget d eps (layerMaxDegree H C j : ℝ) j
  sourceCompletionBiasAtTarget H C j D i

theorem sourceCompletionBiasAtTarget_nonneg
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma target : ℝ) (j : ℕ)
    (hd : 0 ≤ d)
    (hdef : HasSourceDeficitBoundsAtTarget H C d eps Gamma target j)
    (i : Fin (Fintype.card (CompletionIndex H C j))) :
    0 ≤ sourceCompletionBiasAtTarget H C j target i := by
  apply completionWeight_nonneg
  · intro e he
    exact (Real.rpow_nonneg hd _).trans (hdef.2.2 e he).1
  · exact (mem_completionCandidates.mp
      (completionCandidate_mem H C j i)).1

theorem sourceCompletionBiasAtTarget_mem_Icc
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma target : ℝ) (j : ℕ)
    (hd : 0 ≤ d)
    (hdef : HasSourceDeficitBoundsAtTarget H C d eps Gamma target j)
    (hupper : ∀ i, sourceCompletionBiasAtTarget H C j target i ≤ 1) :
    ∀ i, sourceCompletionBiasAtTarget H C j target i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  exact ⟨sourceCompletionBiasAtTarget_nonneg H C d eps Gamma target j
    hd hdef i, hupper i⟩

theorem card_mul_le_totalDeficit
    (H : Hypergraph V) (a : Finset V → ℝ) (L : ℝ)
    (ha : ∀ e ∈ H, L ≤ a e) :
    (H.card : ℝ) * L ≤ totalDeficit H a := by
  rw [totalDeficit]
  calc
    (H.card : ℝ) * L = ∑ _e ∈ H, L := by simp
    _ ≤ ∑ e ∈ H, a e := by
      apply Finset.sum_le_sum
      intro e he
      exact ha e he

theorem totalDeficit_le_card_mul
    (H : Hypergraph V) (a : Finset V → ℝ) (U : ℝ)
    (ha : ∀ e ∈ H, a e ≤ U) :
    totalDeficit H a ≤ (H.card : ℝ) * U := by
  rw [totalDeficit]
  calc
    ∑ e ∈ H, a e ≤ ∑ _e ∈ H, U := by
      apply Finset.sum_le_sum
      intro e he
      exact ha e he
    _ = (H.card : ℝ) * U := by simp

/-- Weighted elementary symmetric sum on a finite set. -/
def elementaryWeight {α : Type*} [DecidableEq α]
    (s : Finset α) (k : ℕ) (a : α → ℝ) : ℝ :=
  ∑ t ∈ s.powersetCard k, ∏ x ∈ t, a x

theorem elementaryWeight_zero {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) :
    elementaryWeight s 0 a = 1 := by
  simp [elementaryWeight]

theorem elementaryWeight_succ_insert {α : Type*} [DecidableEq α]
    {s : Finset α} {x : α} (hx : x ∉ s) (k : ℕ) (a : α → ℝ) :
    elementaryWeight (insert x s) (k + 1) a =
      elementaryWeight s (k + 1) a + a x * elementaryWeight s k a := by
  rw [elementaryWeight, elementaryWeight, elementaryWeight,
    show k + 1 = k.succ by omega, Finset.powersetCard_succ_insert hx]
  have hdisj : Disjoint (s.powersetCard k.succ)
      ((s.powersetCard k).image (insert x)) := by
    rw [Finset.disjoint_left]
    intro t ht hti
    have hts : t ⊆ s := (Finset.mem_powersetCard.mp ht).1
    obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp hti
    have hxu : x ∉ u := fun hxu => hx ((Finset.mem_powersetCard.mp hu).1 hxu)
    have hxt : x ∈ t := by rw [← hut]; exact Finset.mem_insert_self x u
    exact hx (hts hxt)
  rw [Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_image]
  · calc
      (∑ u ∈ s.powersetCard k, ∏ y ∈ insert x u, a y) =
          ∑ u ∈ s.powersetCard k, a x * ∏ y ∈ u, a y := by
            apply Finset.sum_congr rfl
            intro u hu
            have hxu : x ∉ u := fun hxu =>
              hx ((Finset.mem_powersetCard.mp hu).1 hxu)
            rw [Finset.prod_insert hxu]
      _ = a x * ∑ u ∈ s.powersetCard k, ∏ y ∈ u, a y := by
            rw [Finset.mul_sum]
  · intro u hu v hv huv
    have hxu : x ∉ u := fun hxu => hx ((Finset.mem_powersetCard.mp hu).1 hxu)
    have hxv : x ∉ v := fun hxv => hx ((Finset.mem_powersetCard.mp hv).1 hxv)
    have := congrArg (Finset.erase · x) huv
    simpa [hxu, hxv] using this

theorem elementaryWeight_one {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) :
    elementaryWeight s 1 a = ∑ x ∈ s, a x := by
  induction s using Finset.induction_on with
  | empty =>
      rw [elementaryWeight, Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | @insert x s hx ih =>
      rw [elementaryWeight_succ_insert hx 0]
      simp [ih, elementaryWeight_zero, hx]
      ring

theorem two_mul_elementaryWeight_two {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) :
    2 * elementaryWeight s 2 a =
      (∑ x ∈ s, a x) ^ 2 - ∑ x ∈ s, (a x) ^ 2 := by
  induction s using Finset.induction_on with
  | empty =>
      rw [elementaryWeight, Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | @insert x s hx ih =>
      rw [elementaryWeight_succ_insert hx 1, elementaryWeight_one]
      simp only [Finset.sum_insert hx]
      norm_num at *
      calc
        2 * (elementaryWeight s 2 a + a x * ∑ y ∈ s, a y) =
            2 * elementaryWeight s 2 a + 2 * a x * ∑ y ∈ s, a y := by ring
        _ = ((∑ y ∈ s, a y) ^ 2 - ∑ y ∈ s, (a y) ^ 2) +
            2 * a x * ∑ y ∈ s, a y := by rw [ih]
        _ = (a x + ∑ y ∈ s, a y) ^ 2 -
            (a x ^ 2 + ∑ y ∈ s, (a y) ^ 2) := by ring

theorem six_mul_elementaryWeight_three {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) :
    6 * elementaryWeight s 3 a =
      (∑ x ∈ s, a x) ^ 3 -
        3 * (∑ x ∈ s, a x) * (∑ x ∈ s, (a x) ^ 2) +
        2 * ∑ x ∈ s, (a x) ^ 3 := by
  induction s using Finset.induction_on with
  | empty =>
      rw [elementaryWeight, Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | @insert x s hx ih =>
      rw [elementaryWeight_succ_insert hx 2]
      have htwo := two_mul_elementaryWeight_two s a
      simp only [Finset.sum_insert hx]
      norm_num at *
      calc
        6 * (elementaryWeight s 3 a + a x * elementaryWeight s 2 a) =
            6 * elementaryWeight s 3 a + 3 * a x *
              (2 * elementaryWeight s 2 a) := by ring
        _ = ((∑ y ∈ s, a y) ^ 3 -
              3 * (∑ y ∈ s, a y) * (∑ y ∈ s, (a y) ^ 2) +
              2 * ∑ y ∈ s, (a y) ^ 3) +
            3 * a x * ((∑ y ∈ s, a y) ^ 2 -
              ∑ y ∈ s, (a y) ^ 2) := by rw [ih, htwo]
        _ = (a x + ∑ y ∈ s, a y) ^ 3 -
              3 * (a x + ∑ y ∈ s, a y) *
                (a x ^ 2 + ∑ y ∈ s, (a y) ^ 2) +
              2 * (a x ^ 3 + ∑ y ∈ s, (a y) ^ 3) := by ring

theorem sum_sq_le_upper_mul_sum {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (U : ℝ)
    (ha0 : ∀ x ∈ s, 0 ≤ a x) (haU : ∀ x ∈ s, a x ≤ U) :
    (∑ x ∈ s, (a x) ^ 2) ≤ U * ∑ x ∈ s, a x := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  have h0 := ha0 x hx
  have hU := haU x hx
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr hU)]

theorem elementaryWeight_two_lower {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (U : ℝ)
    (ha0 : ∀ x ∈ s, 0 ≤ a x) (haU : ∀ x ∈ s, a x ≤ U) :
    (∑ x ∈ s, a x) ^ 2 - U * (∑ x ∈ s, a x) ≤
      2 * elementaryWeight s 2 a := by
  rw [two_mul_elementaryWeight_two]
  linarith [sum_sq_le_upper_mul_sum s a U ha0 haU]

theorem elementaryWeight_three_lower {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (U : ℝ)
    (ha0 : ∀ x ∈ s, 0 ≤ a x) (haU : ∀ x ∈ s, a x ≤ U) :
    (∑ x ∈ s, a x) ^ 3 -
        3 * U * (∑ x ∈ s, a x) ^ 2 ≤
      6 * elementaryWeight s 3 a := by
  have hsum0 : 0 ≤ ∑ x ∈ s, a x := by
    apply Finset.sum_nonneg
    intro x hx
    exact ha0 x hx
  have hsquares := sum_sq_le_upper_mul_sum s a U ha0 haU
  have hcubes : 0 ≤ ∑ x ∈ s, (a x) ^ 3 := by
    apply Finset.sum_nonneg
    intro x hx
    exact pow_nonneg (ha0 x hx) _
  have hthreeSum : 0 ≤ 3 * (∑ x ∈ s, a x) :=
    mul_nonneg (by norm_num) hsum0
  have hweightedSquares :
      3 * (∑ x ∈ s, a x) * (∑ x ∈ s, (a x) ^ 2) ≤
        3 * U * (∑ x ∈ s, a x) ^ 2 := by
    calc
      3 * (∑ x ∈ s, a x) * (∑ x ∈ s, (a x) ^ 2) ≤
          3 * (∑ x ∈ s, a x) *
            (U * ∑ x ∈ s, a x) :=
        mul_le_mul_of_nonneg_left hsquares hthreeSum
      _ = 3 * U * (∑ x ∈ s, a x) ^ 2 := by ring
  rw [six_mul_elementaryWeight_three]
  linarith

theorem elementaryWeight_nonneg {α : Type*} [DecidableEq α]
    (s : Finset α) (k : ℕ) (a : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) :
    0 ≤ elementaryWeight s k a := by
  apply Finset.sum_nonneg
  intro t ht
  apply Finset.prod_nonneg
  intro x hx
  exact ha x ((Finset.mem_powersetCard.mp ht).1 hx)

theorem sum_cube_nonneg {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) :
    0 ≤ ∑ x ∈ s, (a x) ^ 3 := by
  apply Finset.sum_nonneg
  intro x hx
  exact pow_nonneg (ha x hx) 3

theorem term_le_sum_of_nonneg {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α → ℝ} {x : α}
    (hx : x ∈ s) (ha : ∀ y ∈ s, 0 ≤ a y) :
    a x ≤ ∑ y ∈ s, a y := by
  exact Finset.single_le_sum (fun y hy => ha y hy) hx

theorem sum_cube_le_sum_mul_sum_sq {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) :
    (∑ x ∈ s, (a x) ^ 3) ≤
      (∑ x ∈ s, a x) * ∑ x ∈ s, (a x) ^ 2 := by
  calc
    (∑ x ∈ s, (a x) ^ 3) ≤
        ∑ x ∈ s, (∑ y ∈ s, a y) * (a x) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      have hxs := term_le_sum_of_nonneg hx ha
      have hsquare : 0 ≤ (a x) ^ 2 := sq_nonneg (a x)
      calc
        (a x) ^ 3 = a x * (a x) ^ 2 := by ring
        _ ≤ (∑ y ∈ s, a y) * (a x) ^ 2 :=
          mul_le_mul_of_nonneg_right hxs hsquare
    _ = (∑ x ∈ s, a x) * ∑ x ∈ s, (a x) ^ 2 := by
      rw [Finset.mul_sum]

theorem elementaryWeight_one_exact {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) :
    (Nat.factorial 1 : ℝ) * elementaryWeight s 1 a =
      (∑ x ∈ s, a x) ^ 1 := by
  simp [elementaryWeight_one]

theorem elementaryWeight_two_upper {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ)
    (_ha : ∀ x ∈ s, 0 ≤ a x) :
    (Nat.factorial 2 : ℝ) * elementaryWeight s 2 a ≤
      (∑ x ∈ s, a x) ^ 2 := by
  have hsq : 0 ≤ ∑ x ∈ s, (a x) ^ 2 := by positivity
  rw [show (Nat.factorial 2 : ℝ) = 2 by norm_num,
    two_mul_elementaryWeight_two]
  linarith

theorem elementaryWeight_two_error {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (U : ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x)
    (haU : ∀ x ∈ s, a x ≤ U) :
    |(Nat.factorial 2 : ℝ) * elementaryWeight s 2 a -
        (∑ x ∈ s, a x) ^ 2| ≤
      U * (∑ x ∈ s, a x) := by
  have hlower := elementaryWeight_two_lower s a U ha haU
  have hupper := elementaryWeight_two_upper s a ha
  norm_num at hlower hupper ⊢
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

theorem elementaryWeight_three_upper {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x) :
    (Nat.factorial 3 : ℝ) * elementaryWeight s 3 a ≤
      (∑ x ∈ s, a x) ^ 3 := by
  let S : ℝ := ∑ x ∈ s, a x
  let Q : ℝ := ∑ x ∈ s, (a x) ^ 2
  let R : ℝ := ∑ x ∈ s, (a x) ^ 3
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun x hx => ha x hx
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hR : R ≤ S * Q := by
    simpa [R, S, Q] using sum_cube_le_sum_mul_sum_sq s a ha
  have hSQ : 0 ≤ S * Q := mul_nonneg hS hQ
  rw [show (Nat.factorial 3 : ℝ) = 6 by norm_num,
    six_mul_elementaryWeight_three]
  change S ^ 3 - 3 * S * Q + 2 * R ≤ S ^ 3
  linarith

theorem elementaryWeight_three_error {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (U : ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x)
    (haU : ∀ x ∈ s, a x ≤ U) :
    |(Nat.factorial 3 : ℝ) * elementaryWeight s 3 a -
        (∑ x ∈ s, a x) ^ 3| ≤
      3 * U * (∑ x ∈ s, a x) ^ 2 := by
  have hlower := elementaryWeight_three_lower s a U ha haU
  have hupper := elementaryWeight_three_upper s a ha
  norm_num at hlower hupper ⊢
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

theorem elementaryWeight_two_normalized_error {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (U S : ℝ)
    (hSdef : S = ∑ x ∈ s, a x) (hS : 0 < S)
    (ha : ∀ x ∈ s, 0 ≤ a x)
    (haU : ∀ x ∈ s, a x ≤ U) :
    |(Nat.factorial 2 : ℝ) * elementaryWeight s 2 a / S ^ 2 - 1| ≤
      U / S := by
  have herr := elementaryWeight_two_error s a U ha haU
  rw [← hSdef] at herr
  have hS2 : 0 < S ^ 2 := pow_pos hS 2
  calc
    |(Nat.factorial 2 : ℝ) * elementaryWeight s 2 a / S ^ 2 - 1| =
        |((Nat.factorial 2 : ℝ) * elementaryWeight s 2 a - S ^ 2) /
          S ^ 2| := by
            congr 1
            field_simp
    _ =
        |(Nat.factorial 2 : ℝ) * elementaryWeight s 2 a - S ^ 2| /
          S ^ 2 := by
            rw [abs_div, abs_of_pos hS2]
    _ ≤ (U * S) / S ^ 2 :=
      div_le_div_of_nonneg_right herr hS2.le
    _ = U / S := by field_simp

theorem elementaryWeight_three_normalized_error {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (U S : ℝ)
    (hSdef : S = ∑ x ∈ s, a x) (hS : 0 < S)
    (ha : ∀ x ∈ s, 0 ≤ a x)
    (haU : ∀ x ∈ s, a x ≤ U) :
    |(Nat.factorial 3 : ℝ) * elementaryWeight s 3 a / S ^ 3 - 1| ≤
      3 * U / S := by
  have herr := elementaryWeight_three_error s a U ha haU
  rw [← hSdef] at herr
  have hS3 : 0 < S ^ 3 := pow_pos hS 3
  calc
    |(Nat.factorial 3 : ℝ) * elementaryWeight s 3 a / S ^ 3 - 1| =
        |((Nat.factorial 3 : ℝ) * elementaryWeight s 3 a - S ^ 3) /
          S ^ 3| := by
            congr 1
            field_simp
    _ =
        |(Nat.factorial 3 : ℝ) * elementaryWeight s 3 a - S ^ 3| /
          S ^ 3 := by
            rw [abs_div, abs_of_pos hS3]
    _ ≤ (3 * U * S ^ 2) / S ^ 3 :=
      div_le_div_of_nonneg_right herr hS3.le
    _ = 3 * U / S := by field_simp

/-- Uniform lower approximation in exactly the three ranks used by the
completion stages. -/
theorem elementaryWeight_low_degree_lower {α : Type*} [DecidableEq α]
    (s : Finset α) (k : ℕ) (a : α → ℝ) (U : ℝ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (hU : 0 ≤ U)
    (ha : ∀ x ∈ s, 0 ≤ a x)
    (haU : ∀ x ∈ s, a x ≤ U) :
    (∑ x ∈ s, a x) ^ k - (k : ℝ) ^ 2 * U *
        (∑ x ∈ s, a x) ^ (k - 1) ≤
      (Nat.factorial k : ℝ) * elementaryWeight s k a := by
  rcases hk with rfl | rfl | rfl
  · rw [elementaryWeight_one]
    norm_num
    exact hU
  · have hstrong := elementaryWeight_two_lower s a U ha haU
    have hS : 0 ≤ ∑ x ∈ s, a x :=
      Finset.sum_nonneg fun x hx => ha x hx
    have hUS : 0 ≤ U * ∑ x ∈ s, a x := mul_nonneg hU hS
    norm_num at hstrong ⊢
    linarith
  · have hstrong := elementaryWeight_three_lower s a U ha haU
    have hS2 : 0 ≤ U * (∑ x ∈ s, a x) ^ 2 :=
      mul_nonneg hU (sq_nonneg _)
    norm_num at hstrong ⊢
    linarith

/-- Two-sided form of the low-rank weighted-subset approximation. -/
theorem elementaryWeight_low_degree_error {α : Type*} [DecidableEq α]
    (s : Finset α) (k : ℕ) (a : α → ℝ) (U : ℝ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (hU : 0 ≤ U)
    (ha : ∀ x ∈ s, 0 ≤ a x)
    (haU : ∀ x ∈ s, a x ≤ U) :
    |(Nat.factorial k : ℝ) * elementaryWeight s k a -
        (∑ x ∈ s, a x) ^ k| ≤
      (k : ℝ) ^ 2 * U * (∑ x ∈ s, a x) ^ (k - 1) := by
  rcases hk with rfl | rfl | rfl
  · rw [elementaryWeight_one]
    norm_num
    exact hU
  · have hstrong := elementaryWeight_two_error s a U ha haU
    have hS : 0 ≤ ∑ x ∈ s, a x :=
      Finset.sum_nonneg fun x hx => ha x hx
    have hUS : 0 ≤ U * ∑ x ∈ s, a x := mul_nonneg hU hS
    norm_num at hstrong ⊢
    linarith
  · have hstrong := elementaryWeight_three_error s a U ha haU
    have hS2 : 0 ≤ U * (∑ x ∈ s, a x) ^ 2 :=
      mul_nonneg hU (sq_nonneg _)
    norm_num at hstrong ⊢
    linarith

/-- Pointwise deficit-window bound for every host `j`-set, including the
forbidden sets omitted from the completion-candidate family. -/
theorem completionWeight_le_deficit_bound
    (H : Hypergraph V) (C : ConflictSystem V)
    (target L U : ℝ) (j : ℕ)
    (hH : H.Nonempty) (hL : 0 < L) (hU : 0 ≤ U)
    (hlower : ∀ e ∈ H, L ≤ degreeDeficit C j target e)
    (hupper : ∀ e ∈ H, degreeDeficit C j target e ≤ U)
    {A : Hypergraph V} (hAH : A ⊆ H) (hAj : A.card = j) :
    completionWeight H j (degreeDeficit C j target) A ≤
      (Nat.factorial (j - 1) : ℝ) * U ^ j /
        (((H.card : ℝ) * L) ^ (j - 1)) := by
  let a := degreeDeficit C j target
  have hprod : (∏ e ∈ A, a e) ≤ U ^ j := by
    calc
      (∏ e ∈ A, a e) ≤ ∏ _e ∈ A, U := by
        apply Finset.prod_le_prod
        · intro e he
          exact (hL.le.trans (hlower e (hAH he)))
        · intro e he
          exact hupper e (hAH he)
      _ = U ^ j := by simp [hAj]
  have hbase : 0 < (H.card : ℝ) * L :=
    mul_pos (by exact_mod_cast Finset.card_pos.mpr hH) hL
  have htotalLower : (H.card : ℝ) * L ≤ totalDeficit H a :=
    card_mul_le_totalDeficit H a L hlower
  have htotal : 0 < totalDeficit H a := hbase.trans_le htotalLower
  have hfactor : 0 ≤ (Nat.factorial (j - 1) : ℝ) := by positivity
  rw [completionWeight]
  apply (div_le_div_iff₀ (pow_pos htotal _) (pow_pos hbase _)).2
  calc
    ((Nat.factorial (j - 1) : ℝ) * ∏ e ∈ A, a e) *
        (((H.card : ℝ) * L) ^ (j - 1)) ≤
      ((Nat.factorial (j - 1) : ℝ) * U ^ j) *
        (((H.card : ℝ) * L) ^ (j - 1)) := by
          gcongr
    _ ≤ ((Nat.factorial (j - 1) : ℝ) * U ^ j) *
        (totalDeficit H a) ^ (j - 1) := by
          gcongr

/-- Direct pointwise bound on the source bias from the deficit window.
This is the algebraic part of (8.5); subsequent large-`d` absorption turns
the displayed right side into the paper's `d^(j-1+3eps)/n^(j-1)`. -/
theorem sourceCompletionBiasAtTarget_le_deficit_bound
    (H : Hypergraph V) (C : ConflictSystem V)
    (target L U : ℝ) (j : ℕ)
    (hH : H.Nonempty) (hL : 0 < L) (hU : 0 ≤ U)
    (hlower : ∀ e ∈ H, L ≤ degreeDeficit C j target e)
    (hupper : ∀ e ∈ H, degreeDeficit C j target e ≤ U)
    (i : Fin (Fintype.card (CompletionIndex H C j))) :
    sourceCompletionBiasAtTarget H C j target i ≤
      (Nat.factorial (j - 1) : ℝ) * U ^ j /
        (((H.card : ℝ) * L) ^ (j - 1)) := by
  rw [sourceCompletionBiasAtTarget]
  exact completionWeight_le_deficit_bound H C target L U j hH hL hU
    hlower hupper
    (mem_completionCandidates.mp (completionCandidate_mem H C j i)).1
    (mem_completionCandidates.mp (completionCandidate_mem H C j i)).2.1

/-! ## Finite independent selection and simultaneous concentration -/

/-- A family selected by independent bits from an enumerated list of
candidate conflicts. -/
def sampledCompletionLayer {n : ℕ} (candidate : Fin n -> Hypergraph V)
    (x : Fin n -> Bool) : ConflictSystem V :=
  (Finset.univ.filter fun i => x i = true).image candidate

theorem sampledCompletionLayer_subset_range {n : ℕ}
    (candidate : Fin n -> Hypergraph V) (x : Fin n -> Bool) :
    sampledCompletionLayer candidate x ⊆ Finset.univ.image candidate := by
  intro A hA
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
  exact Finset.mem_image_of_mem candidate (Finset.mem_univ i)

theorem sampledSourceCompletionLayer_subset_candidates
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (x : Fin (Fintype.card (CompletionIndex H C j)) -> Bool) :
    sampledCompletionLayer (completionCandidate H C j) x ⊆
      completionCandidates H C j := by
  intro A hA
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
  exact completionCandidate_mem H C j i

theorem sampledSourceCompletionLayer_isConflictSystem
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (x : Fin (Fintype.card (CompletionIndex H C j)) -> Bool) :
    IsConflictSystem H
      (sampledCompletionLayer (completionCandidate H C j) x) := by
  intro A hA
  exact (mem_completionCandidates.mp
    (sampledSourceCompletionLayer_subset_candidates H C j x hA)).1

theorem sampledSourceCompletionLayer_uniform
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (x : Fin (Fintype.card (CompletionIndex H C j)) -> Bool) :
    IsUniform (sampledCompletionLayer (completionCandidate H C j) x) j :=
  (completionCandidates_uniform H C j).mono
    (sampledSourceCompletionLayer_subset_candidates H C j x)

/-- Every sampled root codegree is bounded by the corresponding candidate
codegree, independently of the probabilistic estimate. -/
theorem sampledSourceCompletionLayer_codegree_le
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (x : Fin (Fintype.card (CompletionIndex H C j)) -> Bool)
    (root : Hypergraph V) :
    codegree (sampledCompletionLayer (completionCandidate H C j) x) root ≤
      codegree (completionCandidates H C j) root :=
  codegree_mono_hypergraph
    (sampledSourceCompletionLayer_subset_candidates H C j x) root

/-- Each selected completion is itself a matching and is free of all old
conflicts, before it is inserted into the conflict system. -/
theorem sampledSourceCompletionLayer_members_safe
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (x : Fin (Fintype.card (CompletionIndex H C j)) -> Bool)
    {A : Hypergraph V}
    (hA : A ∈ sampledCompletionLayer (completionCandidate H C j) x) :
    IsMatching H A ∧ ConflictFree C A := by
  exact (mem_completionCandidates.mp
    (sampledSourceCompletionLayer_subset_candidates H C j x hA)).2.2

/-- The sampled completion layer is disjoint from the old conflict layer:
every candidate is old-conflict-free, so it cannot itself be an old
conflict. -/
theorem conflictLayer_disjoint_sampledSourceCompletionLayer
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (x : Fin (Fintype.card (CompletionIndex H C j)) → Bool) :
    Disjoint (conflictLayer C j)
      (sampledCompletionLayer (completionCandidate H C j) x) := by
  rw [Finset.disjoint_left]
  intro A hAC hAsampled
  have hsafe := sampledSourceCompletionLayer_members_safe H C j x hAsampled
  have hAC' := (Finset.mem_filter.mp hAC).1
  exact hsafe.2 A hAC' Finset.Subset.rfl

theorem degree_union_of_disjoint {X : Type*} [DecidableEq X]
    {K L : Hypergraph X} (hKL : Disjoint K L) (e : X) :
    degree (K ∪ L) e = degree K e + degree L e := by
  rw [degree, degree, degree, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_filter_filter hKL

/-- A linear statistic of a selected layer.  Taking `P A` to mean that
`A` contains a fixed root gives the degree and codegree variables in the
regularisation proof. -/
def sampledCount {n : ℕ} (candidate : Fin n -> Hypergraph V)
    (P : Hypergraph V -> Prop) (x : Fin n -> Bool) : ℝ :=
  ∑ i, if x i = true ∧ P (candidate i) then 1 else 0

/-- With an injective candidate enumeration, the linear statistic really is
the cardinality of the corresponding subfamily of the sampled layer. -/
theorem sampledCount_eq_filter_card {n : ℕ}
    (candidate : Fin n -> Hypergraph V) (hinj : Function.Injective candidate)
    (P : Hypergraph V -> Prop) (x : Fin n -> Bool) :
    sampledCount candidate P x =
      (((sampledCompletionLayer candidate x).filter P).card : ℝ) := by
  let I : Finset (Fin n) :=
    Finset.univ.filter fun i => x i = true ∧ P (candidate i)
  have himage :
      (sampledCompletionLayer candidate x).filter P = I.image candidate := by
    ext A
    constructor
    · intro hA
      obtain ⟨hAlayer, hPA⟩ := Finset.mem_filter.mp hA
      obtain ⟨i, hiSelected, hci⟩ := Finset.mem_image.mp hAlayer
      have hxi : x i = true := (Finset.mem_filter.mp hiSelected).2
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, hci⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, hxi, ?_⟩
      simpa [hci] using hPA
    · intro hA
      obtain ⟨i, hiI, hci⟩ := Finset.mem_image.mp hA
      obtain ⟨_iuniv, hxi, hPi⟩ := Finset.mem_filter.mp hiI
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · apply Finset.mem_image.mpr
        refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩, hci⟩
      · simpa [← hci] using hPi
  rw [himage, Finset.card_image_iff.mpr (Set.injOn_of_injective hinj)]
  rw [sampledCount]
  change (∑ i, if x i = true ∧ P (candidate i) then (1 : ℝ) else 0) =
    (I.card : ℝ)
  rw [show I.card = ∑ i, if x i = true ∧ P (candidate i) then 1 else 0 by
    simp only [I, Finset.card_filter]]
  norm_cast

/-- Changing one independent selection bit changes every degree/codegree
count by at most one. -/
theorem sampledCount_boundedDiff {n : ℕ}
    (candidate : Fin n -> Hypergraph V) (P : Hypergraph V -> Prop)
    (i : Fin n) (x y : Fin n -> Bool)
    (hxy : ∀ q, q ≠ i -> x q = y q) :
    |sampledCount candidate P x - sampledCount candidate P y| ≤ 1 := by
  let gx : Fin n -> ℝ := fun q =>
    if x q = true ∧ P (candidate q) then 1 else 0
  let gy : Fin n -> ℝ := fun q =>
    if y q = true ∧ P (candidate q) then 1 else 0
  have hrest :
      ∑ q ∈ (Finset.univ.erase i), gx q =
        ∑ q ∈ (Finset.univ.erase i), gy q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqi : q ≠ i := (Finset.mem_erase.mp hq).1
    simp only [gx, gy, hxy q hqi]
  have hxsplit : sampledCount candidate P x =
      (∑ q ∈ (Finset.univ.erase i), gx q) + gx i := by
    simpa [sampledCount, gx] using
      (Finset.sum_erase_add (Finset.univ : Finset (Fin n)) gx
        (Finset.mem_univ i)).symm
  have hysplit : sampledCount candidate P y =
      (∑ q ∈ (Finset.univ.erase i), gy q) + gy i := by
    simpa [sampledCount, gy] using
      (Finset.sum_erase_add (Finset.univ : Finset (Fin n)) gy
        (Finset.mem_univ i)).symm
  rw [hxsplit, hysplit, hrest]
  have hgx : gx i = 0 ∨ gx i = 1 := by
    simp only [gx]
    split_ifs <;> simp
  have hgy : gy i = 0 ∨ gy i = 1 := by
    simp only [gy]
    split_ifs <;> simp
  rcases hgx with hgx | hgx <;> rcases hgy with hgy | hgy <;>
    rw [hgx, hgy] <;> norm_num

/-- The mean of one coordinate indicator under the finite Bernoulli product
mass is its prescribed bias. -/
theorem weightedMean_bit_true_varying {n : ℕ}
    (p : Fin n -> ℝ) (i : Fin n) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
      (fun x : Fin n -> Bool => if x i = true then 1 else 0) = p i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [McDiarmid.weightedMean_succ]
          have hsection :
              McDiarmid.sectionAverage (McDiarmid.bernoulliWeight p)
                (fun x : Fin (n + 1) -> Bool =>
                  if x 0 = true then (1 : ℝ) else 0) =
                fun _ : Fin n -> Bool => p 0 := by
            funext y
            simp [McDiarmid.sectionAverage, McDiarmid.bernoulliWeight]
          rw [hsection]
          simp only [McDiarmid.weightedMean]
          rw [← Finset.sum_mul,
            McDiarmid.sum_productMass_eq_one n
              (fun i z => McDiarmid.bernoulliWeight p i.succ z)
              (fun i => McDiarmid.bernoulliWeight_sum_one p i.succ)]
          simp
      | succ i =>
          rw [McDiarmid.weightedMean_succ]
          have hsection :
              McDiarmid.sectionAverage (McDiarmid.bernoulliWeight p)
                (fun x : Fin (n + 1) -> Bool =>
                  if x i.succ = true then (1 : ℝ) else 0) =
                fun x : Fin n -> Bool => if x i = true then 1 else 0 := by
            funext y
            simp [McDiarmid.sectionAverage, McDiarmid.bernoulliWeight]
          rw [hsection]
          exact ih (fun q => p q.succ) i

/-- Every sampled incidence count has the expected weighted-sum mean. -/
theorem weightedMean_sampledCount {n : ℕ}
    (p : Fin n -> ℝ) (candidate : Fin n -> Hypergraph V)
    (P : Hypergraph V -> Prop) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (sampledCount candidate P) =
      ∑ i, p i * (if P (candidate i) then 1 else 0) := by
  simp only [McDiarmid.weightedMean, sampledCount, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hPi : P (candidate i)
  · simpa [hPi, McDiarmid.weightedMean] using
      weightedMean_bit_true_varying p i
  · simp [hPi]

/-- Weight of test members destroyed by a selected completion layer.  Old
conflicts are handled separately; this is the random statistic used for
Property (VI). -/
def sampledKilledWeight {n : ℕ} (H : Hypergraph V) (testJ : ℕ)
    (w : TestWeight V) (candidate : Fin n -> Hypergraph V)
    (x : Fin n -> Bool) : ℝ :=
  ∑ S ∈ H.powersetCard testJ,
    if ∃ i, x i = true ∧ candidate i ⊆ S then w S else 0

theorem sampledCount_nonneg {n : ℕ} (candidate : Fin n -> Hypergraph V)
    (P : Hypergraph V -> Prop) (x : Fin n -> Bool) :
    0 ≤ sampledCount candidate P x := by
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem one_le_sampledCount_of_selected {n : ℕ}
    (candidate : Fin n -> Hypergraph V) (P : Hypergraph V -> Prop)
    (x : Fin n -> Bool) {i : Fin n} (hxi : x i = true)
    (hiP : P (candidate i)) :
    1 ≤ sampledCount candidate P x := by
  unfold sampledCount
  calc
    (1 : ℝ) = if x i = true ∧ P (candidate i) then 1 else 0 := by
      simp [hxi, hiP]
    _ ≤ ∑ q, if x q = true ∧ P (candidate q) then 1 else 0 := by
      have hsingle :
          (if x i = true ∧ P (candidate i) then (1 : ℝ) else 0) ≤
            ∑ q ∈ (Finset.univ : Finset (Fin n)),
              if x q = true ∧ P (candidate q) then 1 else 0 :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin n)))
          (f := fun q =>
            if x q = true ∧ P (candidate q) then (1 : ℝ) else 0)
          (fun q _hq => by split_ifs <;> norm_num)
          (Finset.mem_univ i)
      simpa using hsingle

/-- Union bound before taking expectations: a test killed by at least one
selected candidate is charged to all selected candidates that it contains. -/
theorem sampledKilledWeight_le_incidenceSum {n : ℕ}
    (H : Hypergraph V) (testJ : ℕ) (w : TestWeight V)
    (candidate : Fin n -> Hypergraph V) (hw : ∀ S, 0 ≤ w S)
    (x : Fin n -> Bool) :
    sampledKilledWeight H testJ w candidate x ≤
      ∑ S ∈ H.powersetCard testJ,
        w S * sampledCount candidate (fun A => A ⊆ S) x := by
  rw [sampledKilledWeight]
  apply Finset.sum_le_sum
  intro S _hS
  by_cases hkill : ∃ i, x i = true ∧ candidate i ⊆ S
  · obtain ⟨i, hxi, hiS⟩ := hkill
    rw [if_pos ⟨i, hxi, hiS⟩]
    have hone := one_le_sampledCount_of_selected candidate
      (fun A => A ⊆ S) x hxi hiS
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (hw S)
  · rw [if_neg hkill]
    exact mul_nonneg (hw S)
      (sampledCount_nonneg candidate (fun A => A ⊆ S) x)

theorem bernoulli_weightedMean_mono {n : ℕ}
    (p : Fin n -> ℝ) (f g : (Fin n -> Bool) -> ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hfg : ∀ x, f x ≤ g x) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p) f ≤
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p) g := by
  unfold McDiarmid.weightedMean
  apply Finset.sum_le_sum
  intro x _hx
  exact mul_le_mul_of_nonneg_left (hfg x)
    (McDiarmid.productMass_nonneg _
      (McDiarmid.bernoulliWeight_nonneg p hp) x)

/-- Exact expectation of the incidence-union-bound statistic. -/
theorem weightedMean_incidenceSum {n : ℕ}
    (H : Hypergraph V) (testJ : ℕ) (w : TestWeight V)
    (candidate : Fin n -> Hypergraph V) (p : Fin n -> ℝ) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (fun x => ∑ S ∈ H.powersetCard testJ,
          w S * sampledCount candidate (fun A => A ⊆ S) x) =
      ∑ i, p i * testExtension w H testJ (candidate i) := by
  have hS (S : Hypergraph V) :
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (fun x => w S * sampledCount candidate (fun A => A ⊆ S) x) =
        w S * ∑ i, p i *
          (if candidate i ⊆ S then (1 : ℝ) else 0) := by
    calc
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (fun x => w S * sampledCount candidate (fun A => A ⊆ S) x) =
          w S * McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
            (sampledCount candidate (fun A => A ⊆ S)) := by
        unfold McDiarmid.weightedMean
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = w S * ∑ i, p i *
          (if candidate i ⊆ S then (1 : ℝ) else 0) := by
        rw [weightedMean_sampledCount]
        congr 1
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hiS : candidate i ⊆ S <;> simp [hiS]
  calc
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (fun x => ∑ S ∈ H.powersetCard testJ,
          w S * sampledCount candidate (fun A => A ⊆ S) x) =
        ∑ S ∈ H.powersetCard testJ,
          w S * ∑ i, p i *
            (if candidate i ⊆ S then (1 : ℝ) else 0) := by
      unfold McDiarmid.weightedMean
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _hS
      simpa [McDiarmid.weightedMean, Finset.mul_sum] using hS S
    _ = ∑ i, p i * testExtension w H testJ (candidate i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [testExtension, Finset.mul_sum]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _hS
      by_cases hiS : candidate i ⊆ S <;> simp [hiS] <;> ring

/-- The source expectation bound for killed test mass, before substituting
the pointwise upper bound on the completion probabilities. -/
theorem weightedMean_sampledKilledWeight_le {n : ℕ}
    (H : Hypergraph V) (testJ : ℕ) (w : TestWeight V)
    (candidate : Fin n -> Hypergraph V) (p : Fin n -> ℝ)
    (hw : ∀ S, 0 ≤ w S) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (sampledKilledWeight H testJ w candidate) ≤
      ∑ i, p i * testExtension w H testJ (candidate i) := by
  calc
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (sampledKilledWeight H testJ w candidate) ≤
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (fun x => ∑ S ∈ H.powersetCard testJ,
          w S * sampledCount candidate (fun A => A ⊆ S) x) :=
      bernoulli_weightedMean_mono p _ _ hp
        (sampledKilledWeight_le_incidenceSum H testJ w candidate hw)
    _ = ∑ i, p i * testExtension w H testJ (candidate i) :=
      weightedMean_incidenceSum H testJ w candidate p

/-! ## Finite biased-Bernoulli Chernoff bounds

The following namespace gives direct finite-product MGF and Chernoff bounds for
coordinate-indicator sums.  It uses the same explicit weighted masses as
`McDiarmid`, so no measure-theoretic independence assumptions are hidden.
-/

namespace ChernoffFinite

open Finset Real
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

def bitCount {n : ℕ} (active : Fin n → Prop) (x : Fin n → Bool) : ℝ :=
  ∑ i, if x i = true ∧ active i then 1 else 0

def bitMean {n : ℕ} (p : Fin n → ℝ) (active : Fin n → Prop) : ℝ :=
  ∑ i, if active i then p i else 0

lemma sum_product_apply {n : ℕ} (g : Fin n → Bool → ℝ) :
    ∑ x : Fin n → Bool, ∏ i, g i (x i) = ∏ i, ∑ b : Bool, g i b := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [McDiarmid.sum_fin_succ_eq]
      simp_rw [Fin.prod_univ_succ]
      simp_rw [Fin.cons_zero, Fin.cons_succ]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      rw [← Finset.mul_sum, ih]

lemma exp_mul_bitCount {n : ℕ} (active : Fin n → Prop)
    (x : Fin n → Bool) (lam : ℝ) :
    exp (lam * bitCount active x) =
      ∏ i, exp (lam * (if x i = true ∧ active i then 1 else 0)) := by
  rw [bitCount, Finset.mul_sum, Real.exp_sum]

lemma weightedMean_exp_bitCount_exact {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (lam : ℝ) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (fun x ↦ exp (lam * bitCount active x)) =
      ∏ i, (1 + (if active i then p i else 0) * (exp lam - 1)) := by
  simp only [McDiarmid.weightedMean, McDiarmid.productMass,
    exp_mul_bitCount]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_product_apply
    (fun i b ↦ McDiarmid.bernoulliWeight p i b *
      exp (lam * (if b = true ∧ active i then 1 else 0)))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Fintype.sum_bool]
  by_cases ha : active i
  · simp [McDiarmid.bernoulliWeight, ha]
    ring
  · simp [McDiarmid.bernoulliWeight, ha]

lemma weightedMean_exp_bitCount_le {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (lam : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (fun x ↦ exp (lam * bitCount active x)) ≤
      exp (bitMean p active * (exp lam - 1)) := by
  rw [weightedMean_exp_bitCount_exact]
  rw [bitMean, Finset.sum_mul, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    by_cases ha : active i
    · have hp0 := (hp i).1
      have hp1 := (hp i).2
      have hpe : 0 ≤ p i * exp lam := mul_nonneg hp0 (exp_pos lam).le
      simp only [ha, if_true]
      nlinarith
    · simp [ha]
  · intro i hi
    simpa [add_comm] using
      add_one_le_exp ((if active i then p i else 0) * (exp lam - 1))

lemma eventMass_upper_le_mgf {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (lam a : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | a ≤ bitCount active x} ≤
      exp (-lam * a) *
        McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (fun x ↦ exp (lam * bitCount active x)) := by
  rw [McDiarmid.eventMass]
  calc
    ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ {x | a ≤ bitCount active x}),
          McDiarmid.productMass (McDiarmid.bernoulliWeight p) x
        ≤ ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ {x | a ≤ bitCount active x}),
          exp (-lam * a) *
            (McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
              exp (lam * bitCount active x)) := by
          apply Finset.sum_le_sum
          intro x hx
          have hax : a ≤ bitCount active x := by
            simpa using (Finset.mem_filter.mp hx).2
          have hm : 0 ≤ McDiarmid.productMass
              (McDiarmid.bernoulliWeight p) x :=
            McDiarmid.productMass_nonneg _
              (McDiarmid.bernoulliWeight_nonneg p hp) x
          have he : 1 ≤ exp (lam * (bitCount active x - a)) :=
            (one_le_exp_iff.mpr (mul_nonneg hlam (sub_nonneg.mpr hax)))
          calc
            McDiarmid.productMass (McDiarmid.bernoulliWeight p) x =
                McDiarmid.productMass (McDiarmid.bernoulliWeight p) x * 1 := by ring
            _ ≤ McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
                exp (lam * (bitCount active x - a)) :=
              mul_le_mul_of_nonneg_left he hm
            _ = exp (-lam * a) *
                (McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
                  exp (lam * bitCount active x)) := by
              have hexp : exp (lam * (bitCount active x - a)) =
                  exp (-lam * a) * exp (lam * bitCount active x) := by
                rw [← exp_add]
                congr 1
                ring
              rw [hexp]
              ring
    _ ≤ ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
          exp (-lam * a) *
            (McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
              exp (lam * bitCount active x)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro x hx hnot
          exact mul_nonneg (exp_pos _).le
            (mul_nonneg
              (McDiarmid.productMass_nonneg _
                (McDiarmid.bernoulliWeight_nonneg p hp) x)
              (exp_pos _).le)
    _ = exp (-lam * a) *
        McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (fun x ↦ exp (lam * bitCount active x)) := by
          rw [McDiarmid.weightedMean, Finset.mul_sum]

lemma bitMean_nonneg {n : ℕ} (p : Fin n → ℝ)
    (active : Fin n → Prop) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ bitMean p active := by
  apply Finset.sum_nonneg
  intro i hi
  by_cases ha : active i <;> simp [ha, hp i]

lemma eventMass_upper_chernoff_param {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (lam a : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | a ≤ bitCount active x} ≤
      exp (-lam * a + bitMean p active * (exp lam - 1)) := by
  calc
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | a ≤ bitCount active x} ≤
        exp (-lam * a) *
          McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
            (fun x ↦ exp (lam * bitCount active x)) :=
      eventMass_upper_le_mgf p active lam a hp hlam
    _ ≤ exp (-lam * a) *
          exp (bitMean p active * (exp lam - 1)) :=
      mul_le_mul_of_nonneg_left
        (weightedMean_exp_bitCount_le p active lam hp) (exp_pos _).le
    _ = exp (-lam * a + bitMean p active * (exp lam - 1)) := by
      rw [exp_add]

lemma exp_neg_le_quadratic {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    exp (-d) ≤ 1 - d + d ^ 2 / 2 := by
  have habs : |-d| ≤ 1 := by simpa [abs_of_nonneg hd0]
  have h := Real.exp_bound habs (n := 4) (by norm_num)
  have hu := (abs_le.mp h).2
  rw [abs_neg, abs_of_nonneg hd0] at hu
  norm_num [Finset.sum_range_succ] at hu
  have hd3 : 0 ≤ d ^ 3 := pow_nonneg hd0 3
  have hd4le : d ^ 4 ≤ d ^ 3 := by
    nlinarith [mul_nonneg hd3 hd0]
  nlinarith

lemma upper_rate {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    d ^ 2 / 3 ≤ (1 + d) * log (1 + d) - d := by
  have hden : 0 < d + 2 := by linarith
  have hlog := Real.le_log_one_add_of_nonneg hd0
  have hmul : (1 + d) * (2 * d / (d + 2)) ≤
      (1 + d) * log (1 + d) :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  have hdiv : d ^ 2 / 3 ≤ d ^ 2 / (d + 2) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hden).2
    nlinarith [sq_nonneg d]
  have hid : (1 + d) * (2 * d / (d + 2)) - d =
      d ^ 2 / (d + 2) := by
    field_simp
    ring
  rw [← hid] at hdiv
  linarith

lemma eventMass_lower_le_mgf {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (lam a : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | bitCount active x ≤ a} ≤
      exp (lam * a) *
        McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (fun x ↦ exp (-lam * bitCount active x)) := by
  rw [McDiarmid.eventMass]
  calc
    ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ {x | bitCount active x ≤ a}),
          McDiarmid.productMass (McDiarmid.bernoulliWeight p) x
        ≤ ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ {x | bitCount active x ≤ a}),
          exp (lam * a) *
            (McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
              exp (-lam * bitCount active x)) := by
          apply Finset.sum_le_sum
          intro x hx
          have hxa : bitCount active x ≤ a := by
            simpa using (Finset.mem_filter.mp hx).2
          have hm : 0 ≤ McDiarmid.productMass
              (McDiarmid.bernoulliWeight p) x :=
            McDiarmid.productMass_nonneg _
              (McDiarmid.bernoulliWeight_nonneg p hp) x
          have he : 1 ≤ exp (lam * (a - bitCount active x)) :=
            one_le_exp_iff.mpr (mul_nonneg hlam (sub_nonneg.mpr hxa))
          calc
            McDiarmid.productMass (McDiarmid.bernoulliWeight p) x =
                McDiarmid.productMass (McDiarmid.bernoulliWeight p) x * 1 := by ring
            _ ≤ McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
                exp (lam * (a - bitCount active x)) :=
              mul_le_mul_of_nonneg_left he hm
            _ = exp (lam * a) *
                (McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
                  exp (-lam * bitCount active x)) := by
              have hexp : exp (lam * (a - bitCount active x)) =
                  exp (lam * a) * exp (-lam * bitCount active x) := by
                rw [← exp_add]
                congr 1
                ring
              rw [hexp]
              ring
    _ ≤ ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
          exp (lam * a) *
            (McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
              exp (-lam * bitCount active x)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro x hx hnot
          exact mul_nonneg (exp_pos _).le
            (mul_nonneg
              (McDiarmid.productMass_nonneg _
                (McDiarmid.bernoulliWeight_nonneg p hp) x)
              (exp_pos _).le)
    _ = exp (lam * a) *
        McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (fun x ↦ exp (-lam * bitCount active x)) := by
          rw [McDiarmid.weightedMean, Finset.mul_sum]

lemma eventMass_lower_chernoff_param {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (lam a : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | bitCount active x ≤ a} ≤
      exp (lam * a + bitMean p active * (exp (-lam) - 1)) := by
  calc
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | bitCount active x ≤ a} ≤
        exp (lam * a) *
          McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
            (fun x ↦ exp (-lam * bitCount active x)) :=
      eventMass_lower_le_mgf p active lam a hp hlam
    _ ≤ exp (lam * a) *
          exp (bitMean p active * (exp (-lam) - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
      simpa only [neg_mul] using
        weightedMean_exp_bitCount_le p active (-lam) hp
    _ = exp (lam * a + bitMean p active * (exp (-lam) - 1)) := by
      rw [exp_add]

theorem eventMass_upper_multiplicative {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (d : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | (1 + d) * bitMean p active ≤ bitCount active x} ≤
      exp (-(d ^ 2 * bitMean p active) / 3) := by
  have hmu : 0 ≤ bitMean p active :=
    bitMean_nonneg p active (fun i ↦ (hp i).1)
  have hpos : 0 < 1 + d := by linarith
  have hlam : 0 ≤ log (1 + d) := Real.log_nonneg (by linarith)
  have h := eventMass_upper_chernoff_param p active (log (1 + d))
    ((1 + d) * bitMean p active) hp hlam
  rw [Real.exp_log hpos] at h
  refine h.trans (exp_le_exp.mpr ?_)
  have hr := upper_rate hd0 hd1
  have hmul := mul_le_mul_of_nonneg_right hr hmu
  nlinarith

theorem eventMass_lower_multiplicative {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (d : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | bitCount active x ≤ (1 - d) * bitMean p active} ≤
      exp (-(d ^ 2 * bitMean p active) / 3) := by
  have hmu : 0 ≤ bitMean p active :=
    bitMean_nonneg p active (fun i ↦ (hp i).1)
  have h := eventMass_lower_chernoff_param p active d
    ((1 - d) * bitMean p active) hp hd0
  refine h.trans (exp_le_exp.mpr ?_)
  have he := exp_neg_le_quadratic hd0 hd1
  have hmul := mul_le_mul_of_nonneg_left he hmu
  have hsqmu : 0 ≤ d ^ 2 * bitMean p active :=
    mul_nonneg (sq_nonneg d) hmu
  nlinarith

theorem eventMass_double_threshold {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (t : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (ht : 0 ≤ t) (hmean : bitMean p active ≤ t) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | 2 * t ≤ bitCount active x} ≤ exp (-t / 3) := by
  have hlog0 : 0 ≤ log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have h := eventMass_upper_chernoff_param p active (log 2) (2 * t) hp hlog0
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  refine h.trans (exp_le_exp.mpr ?_)
  have hlog : (2 / 3 : ℝ) ≤ log 2 := by
    convert (Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) zero_le_one) using 1 <;>
      norm_num
  have hlogmul := mul_le_mul_of_nonneg_right hlog ht
  nlinarith

theorem eventMass_two_sided_multiplicative {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (d : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | d * bitMean p active ≤
          |bitCount active x - bitMean p active|} ≤
      2 * exp (-(d ^ 2 * bitMean p active) / 3) := by
  let mu := bitMean p active
  let E : Set (Fin n → Bool) :=
    {x | (1 + d) * mu ≤ bitCount active x}
  let F : Set (Fin n → Bool) :=
    {x | bitCount active x ≤ (1 - d) * mu}
  have hset :
      {x | d * bitMean p active ≤
        |bitCount active x - bitMean p active|} = E ∪ F := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, E, F, mu]
    by_cases hs : 0 ≤ bitCount active x - bitMean p active
    · rw [abs_of_nonneg hs]
      constructor
      · intro h
        left
        nlinarith
      · rintro (h | h)
        · nlinarith
        · nlinarith
    · have hs' : bitCount active x - bitMean p active ≤ 0 := le_of_not_ge hs
      rw [abs_of_nonpos hs']
      constructor
      · intro h
        right
        nlinarith
      · rintro (h | h)
        · nlinarith
        · nlinarith
  rw [hset]
  calc
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p) (E ∪ F) ≤
        McDiarmid.eventMass (McDiarmid.bernoulliWeight p) E +
          McDiarmid.eventMass (McDiarmid.bernoulliWeight p) F :=
      McDiarmid.eventMass_union_le (McDiarmid.bernoulliWeight p)
        (McDiarmid.bernoulliWeight_nonneg p hp) E F
    _ ≤ exp (-(d ^ 2 * bitMean p active) / 3) +
          exp (-(d ^ 2 * bitMean p active) / 3) := by
      apply add_le_add
      · simpa [E, mu] using eventMass_upper_multiplicative p active d hp hd0 hd1
      · simpa [F, mu] using eventMass_lower_multiplicative p active d hp hd0 hd1
    _ = 2 * exp (-(d ^ 2 * bitMean p active) / 3) := by ring

end

end ChernoffFinite

namespace BlockChernoff

open Real

/-- The indicator that every coordinate in `B` was selected. -/
def blockIndicator {n : ℕ} (B : Finset (Fin n)) (x : Fin n → Bool) : ℝ :=
  ∏ i ∈ B, if x i then 1 else 0

/-- The number of coordinate blocks all of whose coordinates were selected. -/
def blockCount {n m : ℕ} (B : Fin m → Finset (Fin n))
    (x : Fin n → Bool) : ℝ :=
  ∑ a, blockIndicator (B a) x

/-- The sum of the success probabilities of the blocks. -/
def blockMean {n m : ℕ} (p : Fin n → ℝ)
    (B : Fin m → Finset (Fin n)) : ℝ :=
  ∑ a, ∏ i ∈ B a, p i

lemma blockIndicator_eq_one_iff {n : ℕ} (B : Finset (Fin n))
    (x : Fin n → Bool) :
    blockIndicator B x = 1 ↔ ∀ i ∈ B, x i = true := by
  constructor
  · intro h i hi
    cases hxi : x i with
    | false =>
        have hz : blockIndicator B x = 0 := by
          unfold blockIndicator
          apply Finset.prod_eq_zero hi
          simp [hxi]
        rw [h] at hz
        norm_num at hz
    | true => rfl
  · intro h
    unfold blockIndicator
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]

lemma blockIndicator_eq_zero_or_one {n : ℕ} (B : Finset (Fin n))
    (x : Fin n → Bool) :
    blockIndicator B x = 0 ∨ blockIndicator B x = 1 := by
  by_cases h : ∀ i ∈ B, x i = true
  · exact Or.inr ((blockIndicator_eq_one_iff B x).2 h)
  · left
    obtain ⟨i, hi⟩ := Classical.not_forall.mp h
    obtain ⟨hiB, hix⟩ := Classical.not_imp.mp hi
    unfold blockIndicator
    apply Finset.prod_eq_zero hiB
    simp [hix]

lemma blockIndicator_eq_ite {n : ℕ} (B : Finset (Fin n))
    (x : Fin n → Bool) :
    blockIndicator B x = if (∀ i ∈ B, x i = true) then 1 else 0 := by
  by_cases h : ∀ i ∈ B, x i = true
  · rw [(blockIndicator_eq_one_iff B x).2 h]
    simp only [if_pos h]
  · have hn : blockIndicator B x ≠ 1 :=
      fun h1 ↦ h ((blockIndicator_eq_one_iff B x).1 h1)
    rcases blockIndicator_eq_zero_or_one B x with h0 | h1
    · simp [h, h0]
    · exact (hn h1).elim

lemma blockCount_eq_filter_card {n m : ℕ}
    (B : Fin m → Finset (Fin n)) (x : Fin n → Bool) :
    blockCount B x =
      (((Finset.univ : Finset (Fin m)).filter
        (fun a ↦ ∀ i ∈ B a, x i = true)).card : ℝ) := by
  rw [blockCount]
  simp_rw [blockIndicator_eq_ite]
  simp

lemma exp_mul_blockIndicator {n : ℕ} (B : Finset (Fin n))
    (x : Fin n → Bool) (lam : ℝ) :
    exp (lam * blockIndicator B x) =
      1 + (exp lam - 1) * blockIndicator B x := by
  rcases blockIndicator_eq_zero_or_one B x with h | h <;> rw [h] <;> simp

lemma weightedMean_coordIndicatorProd {n : ℕ} (p : Fin n → ℝ)
    (S : Finset (Fin n)) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (fun x ↦ ∏ i ∈ S, if x i then (1 : ℝ) else 0) =
      ∏ i ∈ S, p i := by
  simp only [McDiarmid.weightedMean, McDiarmid.productMass]
  have hprod (x : Fin n → Bool) :
      (∏ i, McDiarmid.bernoulliWeight p i (x i)) *
          (∏ i ∈ S, if x i then (1 : ℝ) else 0) =
        ∏ i, McDiarmid.bernoulliWeight p i (x i) *
          (if i ∈ S then (if x i then (1 : ℝ) else 0) else 1) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    simp
  simp_rw [hprod]
  change (∑ x : Fin n → Bool, ∏ i,
      (fun i b ↦ McDiarmid.bernoulliWeight p i b *
        (if i ∈ S then (if b then (1 : ℝ) else 0) else 1)) i (x i)) = _
  have hcoord (i : Fin n) :
      (∑ b : Bool, McDiarmid.bernoulliWeight p i b *
          (if i ∈ S then (if b then (1 : ℝ) else 0) else 1)) =
        if i ∈ S then p i else 1 := by
    rw [Fintype.sum_bool]
    by_cases hi : i ∈ S <;> simp [hi, McDiarmid.bernoulliWeight]
  calc
    (∑ x : Fin n → Bool, ∏ i,
        (fun i b ↦ McDiarmid.bernoulliWeight p i b *
          (if i ∈ S then (if b then (1 : ℝ) else 0) else 1)) i (x i)) =
        ∏ i, ∑ b : Bool, McDiarmid.bernoulliWeight p i b *
          (if i ∈ S then (if b then (1 : ℝ) else 0) else 1) :=
      ChernoffFinite.sum_product_apply
        (fun i b ↦ McDiarmid.bernoulliWeight p i b *
          (if i ∈ S then (if b then (1 : ℝ) else 0) else 1))
    _ = ∏ i ∈ S, p i := by
      simp_rw [hcoord]
      simp

lemma blockIndicator_product {n m : ℕ} (B : Fin m → Finset (Fin n))
    (T : Finset (Fin m))
    (hdisj : (↑T : Set (Fin m)).PairwiseDisjoint B)
    (x : Fin n → Bool) :
    ∏ a ∈ T, blockIndicator (B a) x =
      ∏ i ∈ T.biUnion B, if x i then (1 : ℝ) else 0 := by
  rw [Finset.prod_biUnion hdisj]
  simp only [blockIndicator]

lemma weightedMean_blockIndicator_product {n m : ℕ}
    (p : Fin n → ℝ) (B : Fin m → Finset (Fin n))
    (T : Finset (Fin m))
    (hdisj : (↑T : Set (Fin m)).PairwiseDisjoint B) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (fun x ↦ ∏ a ∈ T, blockIndicator (B a) x) =
      ∏ a ∈ T, ∏ i ∈ B a, p i := by
  simp_rw [blockIndicator_product B T hdisj]
  rw [weightedMean_coordIndicatorProd]
  rw [Finset.prod_biUnion hdisj]

lemma exp_mul_blockCount {n m : ℕ} (B : Fin m → Finset (Fin n))
    (x : Fin n → Bool) (lam : ℝ) :
    exp (lam * blockCount B x) =
      ∏ a, (1 + (exp lam - 1) * blockIndicator (B a) x) := by
  rw [blockCount, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro a ha
  exact exp_mul_blockIndicator (B a) x lam

lemma weightedMean_blockMGF_exact {n m : ℕ}
    (p : Fin n → ℝ) (B : Fin m → Finset (Fin n))
    (hdisj : (Set.univ : Set (Fin m)).PairwiseDisjoint B)
    (lam : ℝ) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (fun x ↦ exp (lam * blockCount B x)) =
      ∏ a, (1 + (∏ i ∈ B a, p i) * (exp lam - 1)) := by
  let c : ℝ := exp lam - 1
  have hsub (T : Finset (Fin m)) :
      (↑T : Set (Fin m)).PairwiseDisjoint B :=
    fun a ha b hb hab ↦ hdisj (by simp) (by simp) hab
  have hexpand (x : Fin n → Bool) :
      (∏ a, (1 + c * blockIndicator (B a) x)) =
        ∑ T ∈ (Finset.univ : Finset (Fin m)).powerset,
          ∏ a ∈ (Finset.univ : Finset (Fin m)) \ T,
            c * blockIndicator (B a) x := by
    simpa using Finset.prod_add (fun _ : Fin m ↦ (1 : ℝ))
      (fun a ↦ c * blockIndicator (B a) x) Finset.univ
  calc
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (fun x ↦ exp (lam * blockCount B x)) =
        ∑ T ∈ (Finset.univ : Finset (Fin m)).powerset,
          c ^ ((Finset.univ : Finset (Fin m)) \ T).card *
            ∏ a ∈ (Finset.univ : Finset (Fin m)) \ T,
              ∏ i ∈ B a, p i := by
      rw [McDiarmid.weightedMean]
      simp_rw [exp_mul_blockCount,
        show exp lam - 1 = c from rfl, hexpand, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T hT
      let K : Finset (Fin m) := (Finset.univ : Finset (Fin m)) \ T
      have hfactor (x : Fin n → Bool) :
          (∏ a ∈ K, c * blockIndicator (B a) x) =
            c ^ K.card * ∏ a ∈ K, blockIndicator (B a) x := by
        rw [Finset.prod_mul_distrib]
        simp
      calc
        ∑ x, McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
              ∏ a ∈ K, c * blockIndicator (B a) x =
            c ^ K.card *
              McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
                (fun x ↦ ∏ a ∈ K, blockIndicator (B a) x) := by
          rw [McDiarmid.weightedMean, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          rw [hfactor]
          ring
        _ = c ^ K.card * ∏ a ∈ K, ∏ i ∈ B a, p i := by
          rw [weightedMean_blockIndicator_product p B K (hsub K)]
        _ = c ^ ((Finset.univ : Finset (Fin m)) \ T).card *
              ∏ a ∈ (Finset.univ : Finset (Fin m)) \ T,
                ∏ i ∈ B a, p i := by rfl
    _ = ∏ a, (1 + (∏ i ∈ B a, p i) * (exp lam - 1)) := by
      calc
        ∑ T ∈ (Finset.univ : Finset (Fin m)).powerset,
            c ^ ((Finset.univ : Finset (Fin m)) \ T).card *
              ∏ a ∈ (Finset.univ : Finset (Fin m)) \ T,
                ∏ i ∈ B a, p i =
            ∑ T ∈ (Finset.univ : Finset (Fin m)).powerset,
              ∏ a ∈ (Finset.univ : Finset (Fin m)) \ T,
                c * (∏ i ∈ B a, p i) := by
          apply Finset.sum_congr rfl
          intro T hT
          rw [Finset.prod_mul_distrib]
          simp
        _ = ∏ a, (1 + (∏ i ∈ B a, p i) * (exp lam - 1)) := by
          have h := (Finset.prod_add (fun _ : Fin m ↦ (1 : ℝ))
            (fun a ↦ c * (∏ i ∈ B a, p i)) Finset.univ).symm
          simpa [c, mul_comm] using h

lemma blockProbability_mem_Icc {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (B : Finset (Fin n)) :
    (∏ i ∈ B, p i) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg fun i hi ↦ (hp i).1
  · exact Finset.prod_le_one (fun i hi ↦ (hp i).1) (fun i hi ↦ (hp i).2)

lemma blockMean_nonneg {n m : ℕ} (p : Fin n → ℝ)
    (B : Fin m → Finset (Fin n))
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ blockMean p B := by
  apply Finset.sum_nonneg
  intro a ha
  exact (blockProbability_mem_Icc p hp (B a)).1

lemma weightedMean_blockMGF_le {n m : ℕ}
    (p : Fin n → ℝ) (B : Fin m → Finset (Fin n))
    (hdisj : (Set.univ : Set (Fin m)).PairwiseDisjoint B)
    (lam : ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (fun x ↦ exp (lam * blockCount B x)) ≤
      exp (blockMean p B * (exp lam - 1)) := by
  rw [weightedMean_blockMGF_exact p B hdisj]
  rw [blockMean, Finset.sum_mul, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro a ha
    have hq := blockProbability_mem_Icc p hp (B a)
    have hqe : 0 ≤ (∏ i ∈ B a, p i) * exp lam :=
      mul_nonneg hq.1 (exp_pos lam).le
    have hq1 := hq.2
    nlinarith
  · intro a ha
    simpa [add_comm] using
      add_one_le_exp ((∏ i ∈ B a, p i) * (exp lam - 1))

lemma eventMass_block_upper_le_mgf {n m : ℕ}
    (p : Fin n → ℝ) (B : Fin m → Finset (Fin n))
    (lam a : ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hlam : 0 ≤ lam) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | a ≤ blockCount B x} ≤
      exp (-lam * a) *
        McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (fun x ↦ exp (lam * blockCount B x)) := by
  rw [McDiarmid.eventMass]
  calc
    ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ {x | a ≤ blockCount B x}),
          McDiarmid.productMass (McDiarmid.bernoulliWeight p) x
        ≤ ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ {x | a ≤ blockCount B x}),
          exp (-lam * a) *
            (McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
              exp (lam * blockCount B x)) := by
          apply Finset.sum_le_sum
          intro x hx
          have hax : a ≤ blockCount B x := by
            simpa using (Finset.mem_filter.mp hx).2
          have hm : 0 ≤ McDiarmid.productMass
              (McDiarmid.bernoulliWeight p) x :=
            McDiarmid.productMass_nonneg _
              (McDiarmid.bernoulliWeight_nonneg p hp) x
          have he : 1 ≤ exp (lam * (blockCount B x - a)) :=
            one_le_exp_iff.mpr (mul_nonneg hlam (sub_nonneg.mpr hax))
          calc
            McDiarmid.productMass (McDiarmid.bernoulliWeight p) x =
                McDiarmid.productMass (McDiarmid.bernoulliWeight p) x * 1 := by ring
            _ ≤ McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
                exp (lam * (blockCount B x - a)) :=
              mul_le_mul_of_nonneg_left he hm
            _ = exp (-lam * a) *
                (McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
                  exp (lam * blockCount B x)) := by
              have hexp : exp (lam * (blockCount B x - a)) =
                  exp (-lam * a) * exp (lam * blockCount B x) := by
                rw [← exp_add]
                congr 1
                ring
              rw [hexp]
              ring
    _ ≤ ∑ x ∈ (Finset.univ : Finset (Fin n → Bool)),
          exp (-lam * a) *
            (McDiarmid.productMass (McDiarmid.bernoulliWeight p) x *
              exp (lam * blockCount B x)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro x hx hnot
          exact mul_nonneg (exp_pos _).le
            (mul_nonneg
              (McDiarmid.productMass_nonneg _
                (McDiarmid.bernoulliWeight_nonneg p hp) x)
              (exp_pos _).le)
    _ = exp (-lam * a) *
        McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (fun x ↦ exp (lam * blockCount B x)) := by
          rw [McDiarmid.weightedMean, Finset.mul_sum]

lemma eventMass_block_upper_chernoff_param {n m : ℕ}
    (p : Fin n → ℝ) (B : Fin m → Finset (Fin n))
    (hdisj : (Set.univ : Set (Fin m)).PairwiseDisjoint B)
    (lam a : ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hlam : 0 ≤ lam) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | a ≤ blockCount B x} ≤
      exp (-lam * a + blockMean p B * (exp lam - 1)) := by
  calc
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | a ≤ blockCount B x} ≤
        exp (-lam * a) *
          McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
            (fun x ↦ exp (lam * blockCount B x)) :=
      eventMass_block_upper_le_mgf p B lam a hp hlam
    _ ≤ exp (-lam * a) * exp (blockMean p B * (exp lam - 1)) :=
      mul_le_mul_of_nonneg_left
        (weightedMean_blockMGF_le p B hdisj lam hp) (exp_pos _).le
    _ = exp (-lam * a + blockMean p B * (exp lam - 1)) := by
      rw [exp_add]

theorem eventMass_block_upper_multiplicative {n m : ℕ}
    (p : Fin n → ℝ) (B : Fin m → Finset (Fin n))
    (hdisj : (Set.univ : Set (Fin m)).PairwiseDisjoint B)
    (d : ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | (1 + d) * blockMean p B ≤ blockCount B x} ≤
      exp (-(d ^ 2 * blockMean p B) / 3) := by
  have hmu : 0 ≤ blockMean p B := blockMean_nonneg p B hp
  have hpos : 0 < 1 + d := by linarith
  have hlam : 0 ≤ log (1 + d) := Real.log_nonneg (by linarith)
  have h := eventMass_block_upper_chernoff_param p B hdisj (log (1 + d))
    ((1 + d) * blockMean p B) hp hlam
  rw [Real.exp_log hpos] at h
  refine h.trans (exp_le_exp.mpr ?_)
  have hr := ChernoffFinite.upper_rate hd0 hd1
  have hmul := mul_le_mul_of_nonneg_right hr hmu
  nlinarith

theorem eventMass_block_double_threshold {n m : ℕ}
    (p : Fin n → ℝ) (B : Fin m → Finset (Fin n))
    (hdisj : (Set.univ : Set (Fin m)).PairwiseDisjoint B)
    (t : ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (ht : 0 ≤ t) (hmean : blockMean p B ≤ t) :
    McDiarmid.eventMass (McDiarmid.bernoulliWeight p)
        {x | 2 * t ≤ blockCount B x} ≤ exp (-t / 3) := by
  have hlog0 : 0 ≤ log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have h := eventMass_block_upper_chernoff_param p B hdisj (log 2) (2 * t) hp hlog0
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  refine h.trans (exp_le_exp.mpr ?_)
  have hlog : (2 / 3 : ℝ) ≤ log 2 := by
    convert (Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) zero_le_one) using 1 <;>
      norm_num
  have hlogmul := mul_le_mul_of_nonneg_right hlog ht
  nlinarith


end BlockChernoff

/-! ### Exact source-weighted incidence means -/

/-- Replace the finite enumeration of completion candidates by the literal
finite candidate family in a source-biased mean. -/
theorem bitMean_sourceCompletion_eq_sum_candidates
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (target : ℝ) (P : Hypergraph V → Prop) :
    ChernoffFinite.bitMean (sourceCompletionBiasAtTarget H C j target)
        (fun i => P (completionCandidate H C j i)) =
      ∑ A ∈ completionCandidates H C j,
        if P A then completionWeight H j (degreeDeficit C j target) A else 0 := by
  rw [ChernoffFinite.bitMean]
  let E := (Fintype.equivFin (CompletionIndex H C j)).symm
  calc
    (∑ i : Fin (Fintype.card (CompletionIndex H C j)),
        if P (completionCandidate H C j i) then
          sourceCompletionBiasAtTarget H C j target i else 0) =
      ∑ q : CompletionIndex H C j,
        if P q.1 then completionWeight H j (degreeDeficit C j target) q.1 else 0 := by
          apply Fintype.sum_equiv E
          intro i
          rfl
    _ = ∑ A ∈ completionCandidates H C j,
        if P A then completionWeight H j (degreeDeficit C j target) A else 0 := by
          simpa using Finset.sum_attach (completionCandidates H C j)
            (fun A => if P A then
              completionWeight H j (degreeDeficit C j target) A else 0)

/-- The weighted sum of the `(k+1)`-subsets containing a distinguished
element is the corresponding rank-`k` elementary symmetric sum. -/
theorem incidentProdSum_insert
    {s : Hypergraph V} {e : Finset V} (he : e ∉ s)
    (k : ℕ) (a : Finset V → ℝ) :
    (∑ A ∈ (insert e s).powersetCard (k + 1),
        if e ∈ A then ∏ f ∈ A, a f else 0) =
      a e * elementaryWeight s k a := by
  rw [show k + 1 = k.succ by omega, Finset.powersetCard_succ_insert he]
  have hdisj : Disjoint (s.powersetCard k.succ)
      ((s.powersetCard k).image (insert e)) := by
    rw [Finset.disjoint_left]
    intro t ht hti
    have hts : t ⊆ s := (Finset.mem_powersetCard.mp ht).1
    obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp hti
    have het : e ∈ t := by rw [← hut]; exact Finset.mem_insert_self e u
    exact he (hts het)
  rw [Finset.sum_union hdisj]
  have hfirst :
      (∑ A ∈ s.powersetCard k.succ,
        if e ∈ A then ∏ f ∈ A, a f else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro A hA
    have heA : e ∉ A := fun heA =>
      he ((Finset.mem_powersetCard.mp hA).1 heA)
    simp [heA]
  rw [hfirst, zero_add, Finset.sum_image]
  · rw [elementaryWeight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    have heA : e ∉ A := fun heA =>
      he ((Finset.mem_powersetCard.mp hA).1 heA)
    simp [heA]
  · intro A hA B hB hAB
    have heA : e ∉ A := fun heA =>
      he ((Finset.mem_powersetCard.mp hA).1 heA)
    have heB : e ∉ B := fun heB =>
      he ((Finset.mem_powersetCard.mp hB).1 heB)
    have h := congrArg (Finset.erase · e) hAB
    simpa [heA, heB] using h

theorem incidentProdSum
    (H : Hypergraph V) {e : Finset V} (heH : e ∈ H)
    {j : ℕ} (hj : 1 ≤ j) (a : Finset V → ℝ) :
    (∑ A ∈ H.powersetCard j,
        if e ∈ A then ∏ f ∈ A, a f else 0) =
      a e * elementaryWeight (H.erase e) (j - 1) a := by
  have hH : H = insert e (H.erase e) := (Finset.insert_erase heH).symm
  calc
    (∑ A ∈ H.powersetCard j,
        if e ∈ A then ∏ f ∈ A, a f else 0) =
        ∑ A ∈ (insert e (H.erase e)).powersetCard ((j - 1) + 1),
          if e ∈ A then ∏ f ∈ A, a f else 0 := by
            rw [← hH]
            congr 2 <;> omega
    _ = a e * elementaryWeight (H.erase e) (j - 1) a :=
      incidentProdSum_insert
        (fun hmem => (Finset.mem_erase.mp hmem).1 rfl) (j - 1) a

theorem fullIncidentCompletionWeight_eq
    (H : Hypergraph V) {e : Finset V} (heH : e ∈ H)
    {j : ℕ} (hj : 1 ≤ j) (a : Finset V → ℝ) :
    (∑ A ∈ H.powersetCard j,
        if e ∈ A then completionWeight H j a A else 0) =
      (Nat.factorial (j - 1) : ℝ) * a e *
          elementaryWeight (H.erase e) (j - 1) a /
        (totalDeficit H a) ^ (j - 1) := by
  simp only [completionWeight]
  have hpoint : ∀ A : Hypergraph V,
      (if e ∈ A then
          (Nat.factorial (j - 1) : ℝ) * (∏ f ∈ A, a f) /
            (totalDeficit H a) ^ (j - 1)
        else 0) =
      (Nat.factorial (j - 1) : ℝ) *
          (if e ∈ A then ∏ f ∈ A, a f else 0) /
            (totalDeficit H a) ^ (j - 1) := by
    intro A
    by_cases heA : e ∈ A <;> simp [heA]
  simp_rw [hpoint]
  rw [← Finset.sum_div, ← Finset.mul_sum,
    incidentProdSum H heH hj a]
  ring

theorem sum_erase_eq_totalDeficit_sub
    (H : Hypergraph V) {e : Finset V} (heH : e ∈ H)
    (a : Finset V → ℝ) :
    (∑ f ∈ H.erase e, a f) = totalDeficit H a - a e := by
  rw [totalDeficit]
  have h := Finset.sum_erase_add (s := H) a heH
  linarith

/-- Uniform normalized form of the full weighted-subset estimate for the
three completion ranks.  Removing the distinguished edge changes the
normalizing sum by at most its upper deficit `U`; the constant `12` leaves
uniform slack for ranks one, two and three. -/
theorem elementaryWeight_erase_normalized_error
    (H : Hypergraph V) {e : Finset V} (heH : e ∈ H)
    (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (a : Finset V → ℝ) (U : ℝ)
    (hU : 0 ≤ U) (ha0 : ∀ f ∈ H, 0 ≤ a f)
    (haU : ∀ f ∈ H, a f ≤ U)
    (hT : 0 < totalDeficit H a) :
    |(Nat.factorial k : ℝ) * elementaryWeight (H.erase e) k a /
        (totalDeficit H a) ^ k - 1| ≤
      12 * U / totalDeficit H a := by
  let T := totalDeficit H a
  let S := ∑ f ∈ H.erase e, a f
  have hae0 : 0 ≤ a e := ha0 e heH
  have haeU : a e ≤ U := haU e heH
  have hSdef : S = T - a e := by
    simpa [S, T] using sum_erase_eq_totalDeficit_sub H heH a
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun f hf => ha0 f (Finset.erase_subset _ _ hf)
  have hST : S ≤ T := by rw [hSdef]; linarith
  have ha0e : ∀ f ∈ H.erase e, 0 ≤ a f :=
    fun f hf => ha0 f (Finset.erase_subset _ _ hf)
  have haUe : ∀ f ∈ H.erase e, a f ≤ U :=
    fun f hf => haU f (Finset.erase_subset _ _ hf)
  rcases hk with rfl | rfl | rfl
  · rw [elementaryWeight_one]
    norm_num
    change |S / T - 1| ≤ 12 * U / T
    have hTne : T ≠ 0 := ne_of_gt hT
    have hrewrite : S / T - 1 = -(a e / T) := by
      rw [← div_self hTne, ← sub_div, hSdef]
      ring
    rw [hrewrite, abs_neg, abs_of_nonneg (div_nonneg hae0 hT.le)]
    exact div_le_div_of_nonneg_right (by linarith) hT.le
  · have herr := elementaryWeight_two_error (H.erase e) a U ha0e haUe
    have hS2T2 : 0 ≤ T ^ 2 - S ^ 2 := by nlinarith
    have hdiff : |(2 : ℝ) * elementaryWeight (H.erase e) 2 a - T ^ 2| ≤
        4 * U * T := by
      calc
        |(2 : ℝ) * elementaryWeight (H.erase e) 2 a - T ^ 2| =
            |((2 : ℝ) * elementaryWeight (H.erase e) 2 a - S ^ 2) +
              (S ^ 2 - T ^ 2)| := by ring_nf
        _ ≤ |(2 : ℝ) * elementaryWeight (H.erase e) 2 a - S ^ 2| +
              |S ^ 2 - T ^ 2| := abs_add_le _ _
        _ ≤ U * S + (T ^ 2 - S ^ 2) := by
          apply add_le_add
          · simpa [S] using herr
          · rw [abs_of_nonpos (by linarith)]
            ring_nf
            exact le_rfl
        _ ≤ 4 * U * T := by
          rw [hSdef]
          nlinarith [mul_nonneg hU hT.le]
    have hT2 : 0 < T ^ 2 := pow_pos hT 2
    change |(2 : ℝ) * elementaryWeight (H.erase e) 2 a / T ^ 2 - 1| ≤
      12 * U / T
    have hT2ne : T ^ 2 ≠ 0 := ne_of_gt hT2
    rw [show (2 : ℝ) * elementaryWeight (H.erase e) 2 a / T ^ 2 - 1 =
      ((2 : ℝ) * elementaryWeight (H.erase e) 2 a - T ^ 2) / T ^ 2 by
        calc
          _ = (2 : ℝ) * elementaryWeight (H.erase e) 2 a / T ^ 2 -
              T ^ 2 / T ^ 2 := by rw [div_self hT2ne]
          _ = _ := (sub_div _ _ _).symm]
    rw [abs_div, abs_of_pos hT2]
    calc
      |(2 : ℝ) * elementaryWeight (H.erase e) 2 a - T ^ 2| / T ^ 2 ≤
          (4 * U * T) / T ^ 2 := div_le_div_of_nonneg_right hdiff hT2.le
      _ = 4 * U / T := by field_simp [ne_of_gt hT]
      _ ≤ 12 * U / T := div_le_div_of_nonneg_right (by linarith) hT.le
  · have herr := elementaryWeight_three_error (H.erase e) a U ha0e haUe
    norm_num at herr
    have hS2le : S ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hS0 hST 2
    have hS3T3 : 0 ≤ T ^ 3 - S ^ 3 :=
      sub_nonneg.mpr (pow_le_pow_left₀ hS0 hST 3)
    have hTSle : T * S ≤ T ^ 2 := by
      calc
        T * S ≤ T * T := mul_le_mul_of_nonneg_left hST hT.le
        _ = T ^ 2 := by ring
    have hpowerDiff : T ^ 3 - S ^ 3 ≤ 3 * U * T ^ 2 := by
      have hbracket : T ^ 2 + T * S + S ^ 2 ≤ 3 * T ^ 2 := by linarith
      calc
        T ^ 3 - S ^ 3 = a e * (T ^ 2 + T * S + S ^ 2) := by
          rw [hSdef]
          ring
        _ ≤ a e * (3 * T ^ 2) :=
          mul_le_mul_of_nonneg_left hbracket hae0
        _ ≤ U * (3 * T ^ 2) :=
          mul_le_mul_of_nonneg_right haeU (by positivity)
        _ = 3 * U * T ^ 2 := by ring
    have hdiff : |(6 : ℝ) * elementaryWeight (H.erase e) 3 a - T ^ 3| ≤
        8 * U * T ^ 2 := by
      calc
        |(6 : ℝ) * elementaryWeight (H.erase e) 3 a - T ^ 3| =
            |((6 : ℝ) * elementaryWeight (H.erase e) 3 a - S ^ 3) +
              (S ^ 3 - T ^ 3)| := by ring_nf
        _ ≤ |(6 : ℝ) * elementaryWeight (H.erase e) 3 a - S ^ 3| +
              |S ^ 3 - T ^ 3| := abs_add_le _ _
        _ ≤ 3 * U * S ^ 2 + (T ^ 3 - S ^ 3) := by
          apply add_le_add
          · simpa [S] using herr
          · rw [abs_of_nonpos (by linarith)]
            ring_nf
            exact le_rfl
        _ ≤ 8 * U * T ^ 2 := by
          have hfirst : 3 * U * S ^ 2 ≤ 3 * U * T ^ 2 :=
            mul_le_mul_of_nonneg_left hS2le (mul_nonneg (by norm_num) hU)
          have hUT2 : 0 ≤ U * T ^ 2 := mul_nonneg hU (sq_nonneg T)
          linarith
    have hT3 : 0 < T ^ 3 := pow_pos hT 3
    change |(6 : ℝ) * elementaryWeight (H.erase e) 3 a / T ^ 3 - 1| ≤
      12 * U / T
    have hT3ne : T ^ 3 ≠ 0 := ne_of_gt hT3
    rw [show (6 : ℝ) * elementaryWeight (H.erase e) 3 a / T ^ 3 - 1 =
      ((6 : ℝ) * elementaryWeight (H.erase e) 3 a - T ^ 3) / T ^ 3 by
        calc
          _ = (6 : ℝ) * elementaryWeight (H.erase e) 3 a / T ^ 3 -
              T ^ 3 / T ^ 3 := by rw [div_self hT3ne]
          _ = _ := (sub_div _ _ _).symm]
    rw [abs_div, abs_of_pos hT3]
    calc
      |(6 : ℝ) * elementaryWeight (H.erase e) 3 a - T ^ 3| / T ^ 3 ≤
          (8 * U * T ^ 2) / T ^ 3 := div_le_div_of_nonneg_right hdiff hT3.le
      _ = 8 * U / T := by field_simp [ne_of_gt hT]
      _ ≤ 12 * U / T := div_le_div_of_nonneg_right (by linarith) hT.le

theorem fullIncidentCompletionWeight_error
    (H : Hypergraph V) {e : Finset V} (heH : e ∈ H)
    (j : ℕ) (hj2 : 2 ≤ j) (hj4 : j ≤ 4)
    (a : Finset V → ℝ) (U : ℝ)
    (hU : 0 ≤ U) (ha0 : ∀ f ∈ H, 0 ≤ a f)
    (haU : ∀ f ∈ H, a f ≤ U)
    (hT : 0 < totalDeficit H a) :
    |(∑ A ∈ H.powersetCard j,
        if e ∈ A then completionWeight H j a A else 0) - a e| ≤
      12 * U ^ 2 / totalDeficit H a := by
  have hk : j - 1 = 1 ∨ j - 1 = 2 ∨ j - 1 = 3 := by omega
  have hratio := elementaryWeight_erase_normalized_error H heH
    (j - 1) hk a U hU ha0 haU hT
  rw [fullIncidentCompletionWeight_eq H heH (by omega) a]
  let R := (Nat.factorial (j - 1) : ℝ) *
          elementaryWeight (H.erase e) (j - 1) a /
        totalDeficit H a ^ (j - 1)
  rw [show (Nat.factorial (j - 1) : ℝ) * a e *
        elementaryWeight (H.erase e) (j - 1) a /
          totalDeficit H a ^ (j - 1) = a e * R by
    simp only [R]
    ring]
  change |a e * R - a e| ≤ 12 * U ^ 2 / totalDeficit H a
  have hae0 := ha0 e heH
  have haeU := haU e heH
  have hstep : |a e * R - a e| ≤ a e * (12 * U / totalDeficit H a) := by
    rw [show a e * R - a e = a e * (R - 1) by ring, abs_mul,
      abs_of_nonneg hae0]
    exact mul_le_mul_of_nonneg_left (by simpa [R] using hratio) hae0
  calc
    |a e * R - a e| ≤ a e * (12 * U / totalDeficit H a) := hstep
    _ ≤ U * (12 * U / totalDeficit H a) :=
      mul_le_mul_of_nonneg_right haeU
        (div_nonneg (mul_nonneg (by norm_num) hU) hT.le)
    _ = 12 * U ^ 2 / totalDeficit H a := by ring

/-- Full incident `j`-sets excluded by matching or old-conflict safety. -/
def forbiddenIncidentCompletions (H : Hypergraph V)
    (C : ConflictSystem V) (j : ℕ) (e : Finset V) :
    Finset (Hypergraph V) :=
  ((H.powersetCard j) \ completionCandidates H C j).filter (e ∈ ·)

theorem completionCandidates_subset_powersetCard
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ) :
    completionCandidates H C j ⊆ H.powersetCard j := by
  intro A hA
  exact Finset.mem_powersetCard.mpr
    ⟨(mem_completionCandidates.mp hA).1,
      (mem_completionCandidates.mp hA).2.1⟩

/-- The omitted incident weight is exactly the full source mean minus the
mean over admissible completion candidates. -/
theorem forbiddenIncidentWeight_eq_full_sub_mean
    (H : Hypergraph V) (C : ConflictSystem V)
    (j : ℕ) (target : ℝ) (e : Finset V) :
    (∑ A ∈ forbiddenIncidentCompletions H C j e,
        completionWeight H j (degreeDeficit C j target) A) =
      (∑ A ∈ H.powersetCard j,
          if e ∈ A then completionWeight H j
            (degreeDeficit C j target) A else 0) -
        ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C j target)
          (fun i => e ∈ completionCandidate H C j i) := by
  have hmean := bitMean_sourceCompletion_eq_sum_candidates H C j target
    (fun A => e ∈ A)
  let f : Hypergraph V → ℝ := fun A => if e ∈ A then
    completionWeight H j (degreeDeficit C j target) A else 0
  have hleft : (∑ A ∈ H.powersetCard j, f A) =
      ∑ A ∈ H.powersetCard j,
        if e ∈ A then completionWeight H j
          (degreeDeficit C j target) A else 0 := by
    apply Finset.sum_congr rfl
    intro A hA
    by_cases heA : e ∈ A <;> simp [f, heA]
  have hright : (∑ A ∈ completionCandidates H C j, f A) =
      ∑ A ∈ completionCandidates H C j,
        if e ∈ A then completionWeight H j
          (degreeDeficit C j target) A else 0 := by
    apply Finset.sum_congr rfl
    intro A hA
    by_cases heA : e ∈ A <;> simp [f, heA]
  have hmeanF :
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C j target)
          (fun i => e ∈ completionCandidate H C j i) =
        ∑ A ∈ completionCandidates H C j, f A := by
    refine hmean.trans ?_
    apply Finset.sum_congr rfl
    intro A hA
    by_cases heA : e ∈ A <;> simp [f, heA]
  have hpartitionF :
      (∑ A ∈ forbiddenIncidentCompletions H C j e,
          completionWeight H j (degreeDeficit C j target) A) =
        (∑ A ∈ H.powersetCard j, f A) -
          ∑ A ∈ completionCandidates H C j, f A := by
    rw [forbiddenIncidentCompletions, Finset.sum_filter]
    calc
      (∑ A ∈ H.powersetCard j \ completionCandidates H C j,
          if e ∈ A then completionWeight H j
            (degreeDeficit C j target) A else 0) =
          ∑ A ∈ H.powersetCard j \ completionCandidates H C j, f A := by
            apply Finset.sum_congr rfl
            intro A hA
            by_cases heA : e ∈ A <;> simp [f, heA]
      _ = (∑ A ∈ H.powersetCard j, f A) -
          ∑ A ∈ completionCandidates H C j, f A :=
        Finset.sum_sdiff_eq_sub
          (completionCandidates_subset_powersetCard H C j)
  linarith [hpartitionF, hmeanF, hleft]

theorem forbiddenIncidentWeight_le_card_mul
    (H : Hypergraph V) (C : ConflictSystem V)
    (j : ℕ) (target pmax : ℝ) (e : Finset V)
    (hmax : ∀ A ∈ H.powersetCard j,
      completionWeight H j (degreeDeficit C j target) A ≤ pmax) :
    (∑ A ∈ forbiddenIncidentCompletions H C j e,
        completionWeight H j (degreeDeficit C j target) A) ≤
      ((forbiddenIncidentCompletions H C j e).card : ℝ) * pmax := by
  calc
    (∑ A ∈ forbiddenIncidentCompletions H C j e,
        completionWeight H j (degreeDeficit C j target) A) ≤
      ∑ _A ∈ forbiddenIncidentCompletions H C j e, pmax := by
        apply Finset.sum_le_sum
        intro A hA
        have hAF : A ∈ H.powersetCard j :=
          (Finset.mem_sdiff.mp (Finset.mem_filter.mp hA).1).1
        exact hmax A hAF
    _ = ((forbiddenIncidentCompletions H C j e).card : ℝ) * pmax := by simp

/-- Complete expectation-room estimate for property (I), with the only
remaining combinatorial input being the cardinality of the explicitly
defined forbidden incident family. -/
theorem sourceIncidentMean_error
    (H : Hypergraph V) (C : ConflictSystem V)
    (j : ℕ) (hj2 : 2 ≤ j) (hj4 : j ≤ 4)
    (target U pmax : ℝ) {e : Finset V} (heH : e ∈ H)
    (hU : 0 ≤ U)
    (ha0 : ∀ f ∈ H, 0 ≤ degreeDeficit C j target f)
    (haU : ∀ f ∈ H, degreeDeficit C j target f ≤ U)
    (hT : 0 < totalDeficit H (degreeDeficit C j target))
    (hmax : ∀ A ∈ H.powersetCard j,
      completionWeight H j (degreeDeficit C j target) A ≤ pmax) :
    |ChernoffFinite.bitMean
        (sourceCompletionBiasAtTarget H C j target)
        (fun i => e ∈ completionCandidate H C j i) -
      degreeDeficit C j target e| ≤
      12 * U ^ 2 / totalDeficit H (degreeDeficit C j target) +
        ((forbiddenIncidentCompletions H C j e).card : ℝ) * pmax := by
  let F : ℝ := ∑ A ∈ H.powersetCard j,
    if e ∈ A then completionWeight H j (degreeDeficit C j target) A else 0
  let M : ℝ := ∑ A ∈ forbiddenIncidentCompletions H C j e,
    completionWeight H j (degreeDeficit C j target) A
  let E : ℝ := ChernoffFinite.bitMean
    (sourceCompletionBiasAtTarget H C j target)
    (fun i => e ∈ completionCandidate H C j i)
  have hFM : M = F - E := by
    simpa [F, M, E] using forbiddenIncidentWeight_eq_full_sub_mean
      H C j target e
  have hM0 : 0 ≤ M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro A hA
    apply completionWeight_nonneg H j (degreeDeficit C j target) ha0
    have hAF : A ∈ H.powersetCard j :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hA).1).1
    exact (Finset.mem_powersetCard.mp hAF).1
  have hFerr : |F - degreeDeficit C j target e| ≤
      12 * U ^ 2 / totalDeficit H (degreeDeficit C j target) := by
    simpa [F] using fullIncidentCompletionWeight_error H heH j hj2 hj4
      (degreeDeficit C j target) U hU ha0 haU hT
  have hMmax : M ≤
      ((forbiddenIncidentCompletions H C j e).card : ℝ) * pmax := by
    simpa [M] using forbiddenIncidentWeight_le_card_mul
      H C j target pmax e hmax
  have hE : E = F - M := by linarith
  change |E - degreeDeficit C j target e| ≤ _
  rw [hE]
  calc
    |F - M - degreeDeficit C j target e| =
        |(F - degreeDeficit C j target e) - M| := by ring_nf
    _ ≤ |F - degreeDeficit C j target e| + |M| := abs_sub _ _
    _ = |F - degreeDeficit C j target e| + M := by rw [abs_of_nonneg hM0]
    _ ≤ _ := add_le_add hFerr hMmax

/-- A strict union bound for the explicit finite Bernoulli product measure
has a point outside every indexed bad event. -/
theorem exists_bernoulli_avoiding_of_eventMass_sum_lt_one
    {n : ℕ} {ι : Type*} [Fintype ι]
    (p : Fin n -> ℝ) (Bad : ι -> Set (Fin n -> Bool))
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hfail :
      (∑ a : ι,
        McDiarmid.eventMass (McDiarmid.bernoulliWeight p) (Bad a)) < 1) :
    ∃ x : Fin n -> Bool, ∀ a, x ∉ Bad a := by
  let w := McDiarmid.bernoulliWeight p
  have hw0 : ∀ i q, 0 ≤ w i q := McDiarmid.bernoulliWeight_nonneg p hp
  have hw1 : ∀ i, ∑ q : Bool, w i q = 1 :=
    McDiarmid.bernoulliWeight_sum_one p
  have hunion : McDiarmid.eventMass w
      (⋃ a ∈ (Finset.univ : Finset ι), Bad a) < 1 := by
    refine (McDiarmid.eventMass_biUnion_le_sum w hw0 Finset.univ Bad).trans_lt ?_
    simpa using hfail
  by_contra hnone
  push Not at hnone
  have hall : (⋃ a ∈ (Finset.univ : Finset ι), Bad a) = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := hnone x
    exact Set.mem_iUnion_of_mem a
      (Set.mem_iUnion_of_mem (Finset.mem_univ a) ha)
  rw [hall, McDiarmid.eventMass_univ w hw1] at hunion
  exact (lt_irrefl (1 : ℝ)) hunion

/-- One finite Bernoulli sample simultaneously satisfies the relative
Chernoff estimates used for degrees, the upper-tail Chernoff estimates used
for codegrees and common links, and the bounded-difference estimates used
for destroyed test mass.  This is the literal probabilistic engine behind
properties (I)--(VI), with every bad-event mass displayed in the
hypothesis. -/
theorem exists_bernoulli_chernoff_mcdiarmid
    {n : ℕ} {ιrel ιupper ιbd : Type*}
    [Fintype ιrel] [Fintype ιupper] [Fintype ιbd]
    (p : Fin n → ℝ)
    (activeRel : ιrel → Fin n → Prop) (delta : ιrel → ℝ)
    (activeUpper : ιupper → Fin n → Prop) (threshold : ιupper → ℝ)
    (f : ιbd → (Fin n → Bool) → ℝ)
    (b : ιbd → Fin n → ℝ) (gap : ιbd → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hdelta0 : ∀ a, 0 ≤ delta a) (hdelta1 : ∀ a, delta a ≤ 1)
    (hthreshold0 : ∀ a, 0 ≤ threshold a)
    (hupperMean : ∀ a,
      ChernoffFinite.bitMean p (activeUpper a) ≤ threshold a)
    (hb : ∀ a i, 0 ≤ b a i)
    (hbd : ∀ a i (x y : Fin n → Bool),
      (∀ q, q ≠ i → x q = y q) → |f a x - f a y| ≤ b a i)
    (hgap : ∀ a, 0 ≤ gap a)
    (hfail :
      (∑ a : ιrel,
          2 * Real.exp (-(delta a ^ 2 *
            ChernoffFinite.bitMean p (activeRel a)) / 3)) +
        (∑ a : ιupper, Real.exp (-threshold a / 3)) +
        (∑ a : ιbd,
          Real.exp (-2 * gap a ^ 2 / ∑ i, (b a i) ^ 2)) < 1) :
    ∃ x : Fin n → Bool,
      (∀ a,
        |ChernoffFinite.bitCount (activeRel a) x -
            ChernoffFinite.bitMean p (activeRel a)| <
          delta a * ChernoffFinite.bitMean p (activeRel a)) ∧
      (∀ a, ChernoffFinite.bitCount (activeUpper a) x <
        2 * threshold a) ∧
      (∀ a, f a x <
        McDiarmid.weightedMean (McDiarmid.bernoulliWeight p) (f a) +
          gap a) := by
  let Bad : Sum ιrel (Sum ιupper ιbd) → Set (Fin n → Bool)
    | Sum.inl a =>
        {x | delta a * ChernoffFinite.bitMean p (activeRel a) ≤
          |ChernoffFinite.bitCount (activeRel a) x -
            ChernoffFinite.bitMean p (activeRel a)|}
    | Sum.inr (Sum.inl a) =>
        {x | 2 * threshold a ≤
          ChernoffFinite.bitCount (activeUpper a) x}
    | Sum.inr (Sum.inr a) =>
        {x | McDiarmid.weightedMean (McDiarmid.bernoulliWeight p) (f a) +
          gap a ≤ f a x}
  have hmass :
      (∑ a : Sum ιrel (Sum ιupper ιbd),
        McDiarmid.eventMass (McDiarmid.bernoulliWeight p) (Bad a)) < 1 := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    rw [add_assoc] at hfail
    refine (add_le_add ?_ (add_le_add ?_ ?_)).trans_lt hfail
    · apply Finset.sum_le_sum
      intro a _ha
      exact ChernoffFinite.eventMass_two_sided_multiplicative
        p (activeRel a) (delta a) hp (hdelta0 a) (hdelta1 a)
    · apply Finset.sum_le_sum
      intro a _ha
      exact ChernoffFinite.eventMass_double_threshold
        p (activeUpper a) (threshold a) hp (hthreshold0 a)
          (hupperMean a)
    · apply Finset.sum_le_sum
      intro a _ha
      exact McDiarmid.bernoulli_mcdiarmid_upper n p (f a) (b a) hp
        (hb a) (hbd a) (gap a) (hgap a)
  obtain ⟨x, hx⟩ :=
    exists_bernoulli_avoiding_of_eventMass_sum_lt_one p Bad hp hmass
  refine ⟨x, ?_, ?_, ?_⟩
  · intro a
    have h := hx (Sum.inl a)
    change ¬delta a * ChernoffFinite.bitMean p (activeRel a) ≤
      |ChernoffFinite.bitCount (activeRel a) x -
        ChernoffFinite.bitMean p (activeRel a)| at h
    exact lt_of_not_ge h
  · intro a
    have h := hx (Sum.inr (Sum.inl a))
    change ¬2 * threshold a ≤
      ChernoffFinite.bitCount (activeUpper a) x at h
    exact lt_of_not_ge h
  · intro a
    have h := hx (Sum.inr (Sum.inr a))
    change ¬McDiarmid.weightedMean (McDiarmid.bernoulliWeight p) (f a) +
      gap a ≤ f a x at h
    exact lt_of_not_ge h

/-- Simultaneous finite extraction for relative linear, one-sided linear,
disjoint-block, and bounded-difference observables. -/
theorem exists_bernoulli_chernoff_block_mcdiarmid
    {n : ℕ} {ιrel ιupper ιblock ιbd : Type*}
    [Fintype ιrel] [Fintype ιupper] [Fintype ιblock] [Fintype ιbd]
    (p : Fin n → ℝ)
    (activeRel : ιrel → Fin n → Prop) (delta : ιrel → ℝ)
    (activeUpper : ιupper → Fin n → Prop) (threshold : ιupper → ℝ)
    (blockSize : ιblock → ℕ)
    (blocks : ∀ a, Fin (blockSize a) → Finset (Fin n))
    (blockThreshold : ιblock → ℝ)
    (f : ιbd → (Fin n → Bool) → ℝ)
    (b : ιbd → Fin n → ℝ) (gap : ιbd → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hdelta0 : ∀ a, 0 ≤ delta a) (hdelta1 : ∀ a, delta a ≤ 1)
    (hthreshold0 : ∀ a, 0 ≤ threshold a)
    (hupperMean : ∀ a,
      ChernoffFinite.bitMean p (activeUpper a) ≤ threshold a)
    (hblockDisj : ∀ a,
      (Set.univ : Set (Fin (blockSize a))).PairwiseDisjoint (blocks a))
    (hblockThreshold0 : ∀ a, 0 ≤ blockThreshold a)
    (hblockMean : ∀ a,
      BlockChernoff.blockMean p (blocks a) ≤ blockThreshold a)
    (hb : ∀ a i, 0 ≤ b a i)
    (hbd : ∀ a i (x y : Fin n → Bool),
      (∀ q, q ≠ i → x q = y q) → |f a x - f a y| ≤ b a i)
    (hgap : ∀ a, 0 ≤ gap a)
    (hfail :
      (∑ a : ιrel,
          2 * Real.exp (-(delta a ^ 2 *
            ChernoffFinite.bitMean p (activeRel a)) / 3)) +
        (∑ a : ιupper, Real.exp (-threshold a / 3)) +
        (∑ a : ιblock, Real.exp (-blockThreshold a / 3)) +
        (∑ a : ιbd,
          Real.exp (-2 * gap a ^ 2 / ∑ i, (b a i) ^ 2)) < 1) :
    ∃ x : Fin n → Bool,
      (∀ a,
        |ChernoffFinite.bitCount (activeRel a) x -
            ChernoffFinite.bitMean p (activeRel a)| <
          delta a * ChernoffFinite.bitMean p (activeRel a)) ∧
      (∀ a, ChernoffFinite.bitCount (activeUpper a) x <
        2 * threshold a) ∧
      (∀ a, BlockChernoff.blockCount (blocks a) x <
        2 * blockThreshold a) ∧
      (∀ a, f a x <
        McDiarmid.weightedMean (McDiarmid.bernoulliWeight p) (f a) +
          gap a) := by
  let Bad : Sum ιrel (Sum ιupper (Sum ιblock ιbd)) →
      Set (Fin n → Bool)
    | Sum.inl a =>
        {x | delta a * ChernoffFinite.bitMean p (activeRel a) ≤
          |ChernoffFinite.bitCount (activeRel a) x -
            ChernoffFinite.bitMean p (activeRel a)|}
    | Sum.inr (Sum.inl a) =>
        {x | 2 * threshold a ≤
          ChernoffFinite.bitCount (activeUpper a) x}
    | Sum.inr (Sum.inr (Sum.inl a)) =>
        {x | 2 * blockThreshold a ≤
          BlockChernoff.blockCount (blocks a) x}
    | Sum.inr (Sum.inr (Sum.inr a)) =>
        {x | McDiarmid.weightedMean (McDiarmid.bernoulliWeight p) (f a) +
          gap a ≤ f a x}
  have hmass :
      (∑ a : Sum ιrel (Sum ιupper (Sum ιblock ιbd)),
        McDiarmid.eventMass (McDiarmid.bernoulliWeight p) (Bad a)) < 1 := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
      Fintype.sum_sum_type]
    rw [add_assoc, add_assoc] at hfail
    refine (add_le_add ?_ (add_le_add ?_ (add_le_add ?_ ?_))).trans_lt hfail
    · apply Finset.sum_le_sum
      intro a _ha
      exact ChernoffFinite.eventMass_two_sided_multiplicative
        p (activeRel a) (delta a) hp (hdelta0 a) (hdelta1 a)
    · apply Finset.sum_le_sum
      intro a _ha
      exact ChernoffFinite.eventMass_double_threshold
        p (activeUpper a) (threshold a) hp (hthreshold0 a)
          (hupperMean a)
    · apply Finset.sum_le_sum
      intro a _ha
      exact BlockChernoff.eventMass_block_double_threshold
        p (blocks a) (hblockDisj a) (blockThreshold a) hp
          (hblockThreshold0 a) (hblockMean a)
    · apply Finset.sum_le_sum
      intro a _ha
      exact McDiarmid.bernoulli_mcdiarmid_upper n p (f a) (b a) hp
        (hb a) (hbd a) (gap a) (hgap a)
  obtain ⟨x, hx⟩ :=
    exists_bernoulli_avoiding_of_eventMass_sum_lt_one p Bad hp hmass
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro a
    have h := hx (Sum.inl a)
    change ¬delta a * ChernoffFinite.bitMean p (activeRel a) ≤
      |ChernoffFinite.bitCount (activeRel a) x -
        ChernoffFinite.bitMean p (activeRel a)| at h
    exact lt_of_not_ge h
  · intro a
    have h := hx (Sum.inr (Sum.inl a))
    change ¬2 * threshold a ≤
      ChernoffFinite.bitCount (activeUpper a) x at h
    exact lt_of_not_ge h
  · intro a
    have h := hx (Sum.inr (Sum.inr (Sum.inl a)))
    change ¬2 * blockThreshold a ≤
      BlockChernoff.blockCount (blocks a) x at h
    exact lt_of_not_ge h
  · intro a
    have h := hx (Sum.inr (Sum.inr (Sum.inr a)))
    change ¬McDiarmid.weightedMean (McDiarmid.bernoulliWeight p) (f a) +
      gap a ≤ f a x at h
    exact lt_of_not_ge h


/-- Toggling candidate `i` changes the destroyed test weight by at most the
weight of the tests extending that candidate.  This is the exact weighted
counterpart of the source bound `d_Z(C)`. -/
theorem sampledKilledWeight_boundedDiff {n : ℕ}
    (H : Hypergraph V) (testJ : ℕ) (w : TestWeight V)
    (candidate : Fin n -> Hypergraph V) (hw : ∀ S, 0 ≤ w S)
    (i : Fin n) (x y : Fin n -> Bool)
    (hxy : ∀ q, q ≠ i -> x q = y q) :
    |sampledKilledWeight H testJ w candidate x -
        sampledKilledWeight H testJ w candidate y| ≤
      testExtension w H testJ (candidate i) := by
  rw [sampledKilledWeight, sampledKilledWeight,
    testExtension, ← Finset.sum_sub_distrib]
  calc
    |∑ S ∈ H.powersetCard testJ,
        ((if ∃ q, x q = true ∧ candidate q ⊆ S then w S else 0) -
          if ∃ q, y q = true ∧ candidate q ⊆ S then w S else 0)|
        ≤ ∑ S ∈ H.powersetCard testJ,
          |((if ∃ q, x q = true ∧ candidate q ⊆ S then w S else 0) -
            if ∃ q, y q = true ∧ candidate q ⊆ S then w S else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ H.powersetCard testJ,
        if candidate i ⊆ S then w S else 0 := by
      apply Finset.sum_le_sum
      intro S _hS
      by_cases hiS : candidate i ⊆ S
      · simp only [hiS, if_true]
        by_cases hxkill : ∃ q, x q = true ∧ candidate q ⊆ S <;>
          by_cases hykill : ∃ q, y q = true ∧ candidate q ⊆ S <;>
          simp [hxkill, hykill, abs_of_nonneg (hw S)] <;> exact hw S
      · have hkill_iff :
            (∃ q, x q = true ∧ candidate q ⊆ S) ↔
              ∃ q, y q = true ∧ candidate q ⊆ S := by
          constructor
          · rintro ⟨q, hxq, hqS⟩
            have hqi : q ≠ i := by
              intro hqi
              subst q
              exact hiS hqS
            exact ⟨q, (hxy q hqi) ▸ hxq, hqS⟩
          · rintro ⟨q, hyq, hqS⟩
            have hqi : q ≠ i := by
              intro hqi
              subst q
              exact hiS hqS
            exact ⟨q, (hxy q hqi).symm ▸ hyq, hqS⟩
        simp only [hiS, if_false]
        rcases hkill_iff with ⟨hforward, hbackward⟩
        by_cases hxkill : ∃ q, x q = true ∧ candidate q ⊆ S
        · have hykill := hforward hxkill
          simp [hxkill, hykill]
        · have hykill : ¬∃ q, y q = true ∧ candidate q ⊆ S := by
            exact fun h => hxkill (hbackward h)
          simp [hxkill, hykill]
    _ = ∑ S ∈ (H.powersetCard testJ).filter (candidate i ⊆ ·), w S := by
      simp only [Finset.sum_filter]
    _ = ∑ S ∈ (H.powersetCard testJ).filter (candidate i ⊆ ·), w S := rfl

theorem exists_bernoulli_simultaneously_close
    {n : ℕ} {ι : Type*} [Fintype ι]
    (p : Fin n -> ℝ) (f : ι -> (Fin n -> Bool) -> ℝ)
    (b : ι -> Fin n -> ℝ) (t : ι -> ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ a i, 0 ≤ b a i)
    (hbd : ∀ a i (x y : Fin n -> Bool),
      (∀ q, q ≠ i -> x q = y q) -> |f a x - f a y| ≤ b a i)
    (ht : ∀ a, 0 ≤ t a)
    (hfail :
      (∑ a : ι,
        2 * Real.exp (-2 * (t a) ^ 2 / ∑ i, (b a i) ^ 2)) < 1) :
    ∃ x : Fin n -> Bool, ∀ a,
      |f a x - McDiarmid.weightedMean (McDiarmid.bernoulliWeight p) (f a)| < t a := by
  let w := McDiarmid.bernoulliWeight p
  let E : ι -> Set (Fin n -> Bool) := fun a =>
    {x | t a ≤ |f a x - McDiarmid.weightedMean w (f a)|}
  have hw0 : ∀ i q, 0 ≤ w i q := McDiarmid.bernoulliWeight_nonneg p hp
  have hw1 : ∀ i, ∑ q : Bool, w i q = 1 := McDiarmid.bernoulliWeight_sum_one p
  have hmass : McDiarmid.eventMass w (⋃ a ∈ (Finset.univ : Finset ι), E a) < 1 := by
    calc
      McDiarmid.eventMass w (⋃ a ∈ (Finset.univ : Finset ι), E a)
          ≤ ∑ a ∈ (Finset.univ : Finset ι), McDiarmid.eventMass w (E a) :=
            McDiarmid.eventMass_biUnion_le_sum w hw0 Finset.univ E
      _ ≤ ∑ a ∈ (Finset.univ : Finset ι),
          2 * Real.exp (-2 * (t a) ^ 2 / ∑ i, (b a i) ^ 2) := by
            apply Finset.sum_le_sum
            intro a _ha
            exact McDiarmid.bernoulli_mcdiarmid_two_sided n p (f a) (b a)
              hp (hb a) (hbd a) (t a) (ht a)
      _ < 1 := by simpa using hfail
  by_contra hnone
  push Not at hnone
  have hall : (⋃ a ∈ (Finset.univ : Finset ι), E a) = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := hnone x
    apply Set.mem_iUnion.mpr
    refine ⟨a, ?_⟩
    apply Set.mem_iUnion.mpr
    exact ⟨Finset.mem_univ a, ha⟩
  rw [hall, McDiarmid.eventMass_univ w hw1] at hmass
  exact (lt_irrefl (1 : ℝ)) hmass

/-- Simultaneous concentration of any finite family of incidence counts.
This is the concrete specialization used for degrees, all two- and
three-codegrees, C4/C5 counts, and test-loss counts. -/
theorem exists_sampledCounts_close
    {n : ℕ} {ι : Type*} [Fintype ι]
    (candidate : Fin n -> Hypergraph V) (P : ι -> Hypergraph V -> Prop)
    (p : Fin n -> ℝ) (t : ι -> ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (ht : ∀ a, 0 ≤ t a)
    (hfail :
      (∑ a : ι, 2 * Real.exp (-2 * (t a) ^ 2 / n)) < 1) :
    ∃ x : Fin n -> Bool, ∀ a,
      |sampledCount candidate (P a) x -
        McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (sampledCount candidate (P a))| < t a := by
  let b : ι -> Fin n -> ℝ := fun _ _ => 1
  apply exists_bernoulli_simultaneously_close p
    (fun a => sampledCount candidate (P a)) b t hp
  · intro _ _
    norm_num [b]
  · intro a i x y hxy
    simpa [b] using sampledCount_boundedDiff candidate (P a) i x y hxy
  · exact ht
  · simpa [b] using hfail

/-- A completion layer satisfying any finite list of decoded requirements
exists as soon as the McDiarmid failure bounds have total mass below one.
The output is an actual subfamily of the enumerated candidates. -/
theorem exists_weightedCompletionLayer
    {n : ℕ} {ι : Type*} [Fintype ι]
    (candidate : Fin n -> Hypergraph V)
    (p : Fin n -> ℝ) (f : ι -> (Fin n -> Bool) -> ℝ)
    (b : ι -> Fin n -> ℝ) (t : ι -> ℝ)
    (Requirement : ConflictSystem V -> Prop)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ a i, 0 ≤ b a i)
    (hbd : ∀ a i (x y : Fin n -> Bool),
      (∀ q, q ≠ i -> x q = y q) -> |f a x - f a y| ≤ b a i)
    (ht : ∀ a, 0 ≤ t a)
    (hfail :
      (∑ a : ι,
        2 * Real.exp (-2 * (t a) ^ 2 / ∑ i, (b a i) ^ 2)) < 1)
    (hdecode : ∀ x, (∀ a,
      |f a x - McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight p) (f a)| < t a) ->
      Requirement (sampledCompletionLayer candidate x)) :
    ∃ A : ConflictSystem V,
      A ⊆ Finset.univ.image candidate ∧ Requirement A := by
  obtain ⟨x, hx⟩ := exists_bernoulli_simultaneously_close p f b t
    hp hb hbd ht hfail
  exact ⟨sampledCompletionLayer candidate x,
    sampledCompletionLayer_subset_range candidate x, hdecode x hx⟩

/-- The preceding extraction with the literal candidate enumeration and
the literal source weights (8.5).  Thus each of stages `j = 2,3,4` can use
this theorem without introducing an abstract probability distribution. -/
theorem exists_sourceWeightedCompletionLayer
    {ι : Type*} [Fintype ι]
    (H : Hypergraph V) (C : ConflictSystem V) (d eps : ℝ) (j : ℕ)
    (f : ι ->
      (Fin (Fintype.card (CompletionIndex H C j)) -> Bool) -> ℝ)
    (b : ι -> Fin (Fintype.card (CompletionIndex H C j)) -> ℝ)
    (t : ι -> ℝ) (Requirement : ConflictSystem V -> Prop)
    (hp : ∀ i, sourceCompletionBias H C d eps j i ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ a i, 0 ≤ b a i)
    (hbd : ∀ a i
      (x y : Fin (Fintype.card (CompletionIndex H C j)) -> Bool),
      (∀ q, q ≠ i -> x q = y q) -> |f a x - f a y| ≤ b a i)
    (ht : ∀ a, 0 ≤ t a)
    (hfail :
      (∑ a : ι,
        2 * Real.exp (-2 * (t a) ^ 2 / ∑ i, (b a i) ^ 2)) < 1)
    (hdecode : ∀ x, (∀ a,
      |f a x - McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (sourceCompletionBias H C d eps j))
        (f a)| < t a) ->
      Requirement (sampledCompletionLayer (completionCandidate H C j) x)) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H C j ∧ Requirement A := by
  obtain ⟨A, hA, hReq⟩ := exists_weightedCompletionLayer
    (completionCandidate H C j) (sourceCompletionBias H C d eps j)
    f b t Requirement hp hb hbd ht hfail hdecode
  refine ⟨A, ?_, hReq⟩
  intro a ha
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp (hA ha)
  exact completionCandidate_mem H C j i

/-- Target-parametric form used while iterating stages `2,3,4`: candidates
are tested against the current conflict system, while the target remains
anchored at the fixed pre-regularisation layer maximum. -/
theorem exists_sourceWeightedCompletionLayerAtTarget
    {ι : Type*} [Fintype ι]
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ) (target : ℝ)
    (f : ι ->
      (Fin (Fintype.card (CompletionIndex H C j)) -> Bool) -> ℝ)
    (b : ι -> Fin (Fintype.card (CompletionIndex H C j)) -> ℝ)
    (t : ι -> ℝ) (Requirement : ConflictSystem V -> Prop)
    (hp : ∀ i,
      sourceCompletionBiasAtTarget H C j target i ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ a i, 0 ≤ b a i)
    (hbd : ∀ a i
      (x y : Fin (Fintype.card (CompletionIndex H C j)) -> Bool),
      (∀ q, q ≠ i -> x q = y q) -> |f a x - f a y| ≤ b a i)
    (ht : ∀ a, 0 ≤ t a)
    (hfail :
      (∑ a : ι,
        2 * Real.exp (-2 * (t a) ^ 2 / ∑ i, (b a i) ^ 2)) < 1)
    (hdecode : ∀ x, (∀ a,
      |f a x - McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight
          (sourceCompletionBiasAtTarget H C j target))
        (f a)| < t a) ->
      Requirement (sampledCompletionLayer (completionCandidate H C j) x)) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H C j ∧ Requirement A := by
  obtain ⟨A, hA, hReq⟩ := exists_weightedCompletionLayer
    (completionCandidate H C j)
    (sourceCompletionBiasAtTarget H C j target)
    f b t Requirement hp hb hbd ht hfail hdecode
  refine ⟨A, ?_, hReq⟩
  intro a ha
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp (hA ha)
  exact completionCandidate_mem H C j i

/-! ## Updating a layer and retaining original conflicts -/

/-- Inclusion-minimal members of `C` which are matchings in the host.  This
is the source's initial `1`-admissible conflict system: nonmatching
conflicts are irrelevant to a matching, and strict supersets are redundant. -/
def minimalMatchingCore (H : Hypergraph V) (C : ConflictSystem V) :
    ConflictSystem V :=
  C.filter fun c => IsMatching H c ∧
    ¬∃ c' ∈ C, IsMatching H c' ∧ c' ⊂ c

@[simp] theorem mem_minimalMatchingCore
    {H : Hypergraph V} {C : ConflictSystem V} {c : Hypergraph V} :
    c ∈ minimalMatchingCore H C ↔
      c ∈ C ∧ IsMatching H c ∧
        ¬∃ c' ∈ C, IsMatching H c' ∧ c' ⊂ c := by
  simp [minimalMatchingCore, and_assoc]

theorem minimalMatchingCore_members_match
    {H : Hypergraph V} {C : ConflictSystem V} {c : Hypergraph V}
    (hc : c ∈ minimalMatchingCore H C) : IsMatching H c :=
  (mem_minimalMatchingCore.mp hc).2.1

theorem minimalMatchingCore_isConflictSystem
    {H : Hypergraph V} {C : ConflictSystem V}
    (hC : IsConflictSystem H C) :
    IsConflictSystem H (minimalMatchingCore H C) := by
  intro c hc
  exact hC c (mem_minimalMatchingCore.mp hc).1

theorem minimalMatchingCore_antichain
    {H : Hypergraph V} {C : ConflictSystem V}
    {c c' : Hypergraph V}
    (hc : c ∈ minimalMatchingCore H C)
    (hc' : c' ∈ minimalMatchingCore H C)
    (hne : c ≠ c') : ¬c ⊆ c' := by
  intro hsub
  have hstrict : c ⊂ c' := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  exact (mem_minimalMatchingCore.mp hc').2.2
    ⟨c, (mem_minimalMatchingCore.mp hc).1,
      (mem_minimalMatchingCore.mp hc).2.1, hstrict⟩

/-! ### Deterministic transfer through the bad-pair minimal core -/

theorem minimalMatchingCore_subset_badPairCore
    (H : Hypergraph V) (C : ConflictSystem V) :
    minimalMatchingCore H C ⊆ C := by
  intro c hc
  exact (mem_minimalMatchingCore.mp hc).1

theorem minimalCore_union_layer_two_subset_right
    (H : Hypergraph V) {C B : ConflictSystem V}
    {d eps : ℝ} {ell : ℕ} (hC : IsBounded C d ell eps) :
    conflictLayer (minimalMatchingCore H (C ∪ B)) 2 ⊆
      conflictLayer B 2 := by
  intro c hc
  have hcU : c ∈ C ∪ B :=
    minimalMatchingCore_subset_badPairCore H (C ∪ B)
      (Finset.mem_filter.mp hc).1
  have hcard : c.card = 2 := (Finset.mem_filter.mp hc).2
  apply Finset.mem_filter.mpr
  refine ⟨?_, hcard⟩
  rcases Finset.mem_union.mp hcU with hcC | hcB
  · have hge := (hC.conflict_card hcC).1
    omega
  · exact hcB

theorem minimalCore_union_layer_ge_three_subset_left
    (H : Hypergraph V) {C B : ConflictSystem V}
    (hB : IsUniform B 2) (r : ℕ) (hr : 3 ≤ r) :
    conflictLayer (minimalMatchingCore H (C ∪ B)) r ⊆
      conflictLayer C r := by
  intro c hc
  have hcU : c ∈ C ∪ B :=
    minimalMatchingCore_subset_badPairCore H (C ∪ B)
      (Finset.mem_filter.mp hc).1
  have hcard : c.card = r := (Finset.mem_filter.mp hc).2
  apply Finset.mem_filter.mpr
  refine ⟨?_, hcard⟩
  rcases Finset.mem_union.mp hcU with hcC | hcB
  · exact hcC
  · have hc2 := hB c hcB
    omega

theorem twoConflictNeighbors_card_le_layer_degree
    (H : Hypergraph V) (C : ConflictSystem V) (e : Finset V) :
    (twoConflictNeighbors H C e).card ≤ degree (conflictLayer C 2) e := by
  rw [degree]
  apply Finset.card_le_card_of_injOn (fun f : Finset V => {e, f})
  · intro f hf
    have hf' := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨hf'.2.2, by simp⟩
  · intro f hf g _hg heq
    have hfe : f ≠ e := (Finset.mem_filter.mp hf).2.1
    dsimp only at heq
    have hmem : f ∈ ({e, g} : Hypergraph V) := by
      rw [← heq]
      simp
    have : f ∈ ({g} : Hypergraph V) :=
      (Finset.mem_insert.mp hmem).resolve_left hfe
    simpa using this

theorem conditionC4Count_le_layer_degree
    (H : Hypergraph V) (C : ConflictSystem V) (e : Finset V) (v : V) :
    conditionC4Count H C e v ≤ degree (conflictLayer C 2) e :=
  (conditionC4Count_le_neighbors_card H C e v).trans
    (twoConflictNeighbors_card_le_layer_degree H C e)

theorem conditionC5Count_le_layer_degree
    (H : Hypergraph V) (C : ConflictSystem V) (e f : Finset V) :
    conditionC5Count H C e f ≤ degree (conflictLayer C 2) e :=
  (conditionC5Count_le_left H C e f).trans
    (twoConflictNeighbors_card_le_layer_degree H C e)

theorem trackable_conflictFree_minimalCore_with_badPairs
    {H : Hypergraph V} {C : ConflictSystem V} {j ell : ℕ}
    {d eta : ℝ} {w : TestWeight V}
    (hell : 4 ≤ ell) (hw : IsTrackable H C j ell d eta w)
    {S : Hypergraph V} (hSH : S ∈ H.powersetCard j) (hwS : 0 < w S) :
    ConflictFree
      (minimalMatchingCore H
        (C ∪ badPairConflicts H C (trackableCutoff d eta))) S := by
  intro c hcCore hcS
  have hcU : c ∈ C ∪ badPairConflicts H C (trackableCutoff d eta) :=
    minimalMatchingCore_subset_badPairCore H _ hcCore
  rcases Finset.mem_union.mp hcU with hcC | hcB
  · have hz := hw.eq_zero_of_contains_conflict hSH ⟨c, hcC, hcS⟩
    linarith
  · exact trackable_conflictFree_badPairs hell hw hSH hwS c hcB hcS

theorem trackable_conflictFree_minimalCore_with_badPairs_of_eta_le
    {H : Hypergraph V} {C : ConflictSystem V} {j ell : ℕ}
    {d etaRaw etaBad : ℝ} {w : TestWeight V}
    (hell : 4 ≤ ell) (hd : 1 ≤ d) (heta : etaBad ≤ etaRaw)
    (hw : IsTrackable H C j ell d etaRaw w)
    {S : Hypergraph V} (hSH : S ∈ H.powersetCard j) (hwS : 0 < w S) :
    ConflictFree
      (minimalMatchingCore H
        (C ∪ badPairConflicts H C (trackableCutoff d etaBad))) S := by
  intro c hcCore hcS
  have hcU : c ∈ C ∪ badPairConflicts H C (trackableCutoff d etaBad) :=
    minimalMatchingCore_subset_badPairCore H _ hcCore
  rcases Finset.mem_union.mp hcU with hcC | hcB
  · have hz := hw.eq_zero_of_contains_conflict hSH ⟨c, hcC, hcS⟩
    linarith
  · exact trackable_conflictFree_badPairs_of_eta_le hell hd heta hw
      hSH hwS c hcB hcS

theorem conflictLayer_eq_self_of_uniform
    {C : ConflictSystem V} {r : ℕ} (hC : IsUniform C r) :
    conflictLayer C r = C := by
  ext c
  simp only [conflictLayer, Finset.mem_filter]
  constructor
  · exact And.left
  · intro hc
    exact ⟨hc, hC c hc⟩

/-- The original C1--C3 bounds, the sharp auxiliary pair degree, and the
normalised degree sum imply the complete C1--C5 package for the minimal
core. -/
theorem minimalCore_with_badPairs_isRegularizedBounded_of_degreeSum
    (H : Hypergraph V) (C : ConflictSystem V)
    {d eps eta Gamma : ℝ} {ell : ℕ}
    (hC : IsBounded C d ell eps)
    (hCcard : ∀ c ∈ C, c.card = 4) (hell : 4 ≤ ell)
    (hd : 1 ≤ d)
    (heta : eta ≤ eps)
    (hBdegree : ∀ e ∈ H,
      (degree (badPairConflicts H C (trackableCutoff d eta)) e : ℝ) ≤
        Real.rpow d (1 - eta))
    (hGamma : 3 ≤ 2 * Gamma)
    (hdegreeSum :
      (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H
          (minimalMatchingCore H
            (C ∪ badPairConflicts H C (trackableCutoff d eta))) r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤ 2 * Gamma) :
    IsRegularizedBounded H
      (minimalMatchingCore H
        (C ∪ badPairConflicts H C (trackableCutoff d eta)))
      d (2 * Gamma) eta := by
  let B := badPairConflicts H C (trackableCutoff d eta)
  let C0 := minimalMatchingCore H (C ∪ B)
  have hBuniform : IsUniform B 2 := by
    exact badPairConflicts_uniform_two H C _
  have hlayer2 : conflictLayer C0 2 ⊆ conflictLayer B 2 := by
    exact minimalCore_union_layer_two_subset_right H hC
  have hlayerB : conflictLayer B 2 = B :=
    conflictLayer_eq_self_of_uniform hBuniform
  refine ⟨?_, hdegreeSum, ?_, ?_, ?_, ?_⟩
  · intro c hc0
    have hcU : c ∈ C ∪ B :=
      minimalMatchingCore_subset_badPairCore H (C ∪ B) hc0
    rcases Finset.mem_union.mp hcU with hcC | hcB
    · rw [hCcard c hcC]
      omega
    · rw [hBuniform c hcB]
      omega
  · calc
      ((((Finset.Icc 2 4).filter fun r => conflictLayer C0 r ≠ ∅).card : ℕ) : ℝ) ≤
          ((Finset.Icc 2 4).card : ℕ) := by
        exact_mod_cast Finset.card_filter_le _ _
      _ = 3 := by norm_num
      _ ≤ 2 * Gamma := hGamma
  · intro r hr2 hr4 q hq2 hqr root hroot
    have hr3 : 3 ≤ r := by omega
    have hsub : conflictLayer C0 r ⊆ conflictLayer C r :=
      minimalCore_union_layer_ge_three_subset_left H hBuniform r hr3
    calc
      (codegree (conflictLayer C0 r) root : ℝ) ≤
          (codegree (conflictLayer C r) root : ℝ) := by
        exact_mod_cast codegree_mono_hypergraph hsub root
      _ ≤ Real.rpow d ((r : ℝ) - (q : ℝ) - eps) :=
        hC.layer_codegree hr3 (hr4.trans hell) hq2 hqr root hroot
      _ ≤ Real.rpow d ((r : ℝ) - (q : ℝ) - eta) := by
        exact Real.rpow_le_rpow_of_exponent_le hd (by linarith)
  · intro e heH v
    calc
      (conditionC4Count H C0 e v : ℝ) ≤
          (degree (conflictLayer C0 2) e : ℝ) := by
        exact_mod_cast conditionC4Count_le_layer_degree H C0 e v
      _ ≤ (degree (conflictLayer B 2) e : ℝ) := by
        exact_mod_cast degree_mono hlayer2 e
      _ = (degree B e : ℝ) := by rw [hlayerB]
      _ ≤ Real.rpow d (1 - eta) := hBdegree e heH
  · intro e heH f _hfH _hdisj
    calc
      (conditionC5Count H C0 e f : ℝ) ≤
          (degree (conflictLayer C0 2) e : ℝ) := by
        exact_mod_cast conditionC5Count_le_layer_degree H C0 e f
      _ ≤ (degree (conflictLayer B 2) e : ℝ) := by
        exact_mod_cast degree_mono hlayer2 e
      _ = (degree B e : ℝ) := by rw [hlayerB]
      _ ≤ Real.rpow d (1 - eta) := hBdegree e heH

/-- Every matching conflict contains an inclusion-minimal matching
conflict. -/
theorem matchingConflict_contains_minimalMatchingCore
    {H : Hypergraph V} {C : ConflictSystem V}
    {c : Hypergraph V} (hc : c ∈ C) (hmatch : IsMatching H c) :
    ∃ c' ∈ minimalMatchingCore H C, c' ⊆ c := by
  let S : Finset (Hypergraph V) :=
    C.filter fun c' => IsMatching H c' ∧ c' ⊆ c
  have hS : S.Nonempty := by
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, hmatch, Finset.Subset.rfl⟩⟩
  obtain ⟨c', hc'S, hc'min⟩ :=
    Finset.exists_min_image S Finset.card hS
  have hc'data := Finset.mem_filter.mp hc'S
  refine ⟨c', mem_minimalMatchingCore.mpr ⟨hc'data.1, hc'data.2.1, ?_⟩,
    hc'data.2.2⟩
  rintro ⟨b, hbC, hbmatch, hbstrict⟩
  have hbS : b ∈ S := Finset.mem_filter.mpr
    ⟨hbC, hbmatch, hbstrict.1.trans hc'data.2.2⟩
  have hle := hc'min b hbS
  have hlt := Finset.card_lt_card hbstrict
  omega

/-- Add the selected `j`-sets and delete old strict supersets of one of
them.  This is the deterministic update in Lemma 8.6. -/
def addCompletionLayer (C A : ConflictSystem V) : ConflictSystem V :=
  A ∪ C.filter fun c => ¬∃ a ∈ A, a ⊂ c

theorem selected_subset_addCompletionLayer (C A : ConflictSystem V) :
    A ⊆ addCompletionLayer C A := by
  exact Finset.subset_union_left

/-- Every old conflict contains a conflict in the updated system. -/
theorem oldConflict_contains_updated {C A : ConflictSystem V}
    {c : Hypergraph V} (hc : c ∈ C) :
    ∃ c' ∈ addCompletionLayer C A, c' ⊆ c := by
  by_cases hkill : ∃ a ∈ A, a ⊂ c
  · obtain ⟨a, haA, hac⟩ := hkill
    exact ⟨a, Finset.mem_union_left _ haA, hac.1⟩
  · exact ⟨c, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc, hkill⟩),
      Finset.Subset.rfl⟩

/-- Iterating the three completion stages preserves the covering property:
every original conflict contains a final conflict. -/
theorem originalConflict_contains_threeStageUpdate
    {H : Hypergraph V} {C B A2 A3 A4 R : ConflictSystem V}
    (hR : R =
      addCompletionLayer
        (addCompletionLayer
          (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3) A4)
    {c : Hypergraph V} (hc : c ∈ C) (hmatch : IsMatching H c) :
    ∃ c' ∈ R, c' ⊆ c := by
  have hc0 : c ∈ C ∪ B := Finset.mem_union_left B hc
  obtain ⟨c1, hc1, hc1c⟩ :=
    matchingConflict_contains_minimalMatchingCore hc0 hmatch
  obtain ⟨c2, hc2, hc2c1⟩ :=
    oldConflict_contains_updated
      (C := minimalMatchingCore H (C ∪ B)) (A := A2) hc1
  obtain ⟨c3, hc3, hc3c2⟩ :=
    oldConflict_contains_updated
      (C := addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2)
      (A := A3) hc2
  obtain ⟨c4, hc4, hc4c3⟩ :=
    oldConflict_contains_updated
      (C := addCompletionLayer
        (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3)
      (A := A4) hc3
  refine ⟨c4, ?_, hc4c3.trans (hc3c2.trans (hc2c1.trans hc1c))⟩
  rwa [hR]

theorem conflictFree_addCompletionLayer_imp_old
    {C A : ConflictSystem V} {M : Hypergraph V}
    (hM : ConflictFree (addCompletionLayer C A) M) :
    ConflictFree C M := by
  intro c hc hsub
  obtain ⟨c', hc'new, hc'c⟩ := oldConflict_contains_updated (A := A) hc
  exact hM c' hc'new (hc'c.trans hsub)

theorem addCompletionLayer_isConflictSystem {H : Hypergraph V}
    {C A : ConflictSystem V} (hC : IsConflictSystem H C)
    (hA : IsConflictSystem H A) :
    IsConflictSystem H (addCompletionLayer C A) := by
  intro c hc
  rcases Finset.mem_union.mp hc with hcA | hcC
  · exact hA c hcA
  · exact hC c (Finset.mem_filter.mp hcC).1

theorem addCompletionLayer_members_match
    {H : Hypergraph V} {C A : ConflictSystem V} {j : ℕ}
    (hCmatch : ∀ c ∈ C, IsMatching H c)
    (hA : A ⊆ completionCandidates H C j) :
    ∀ c ∈ addCompletionLayer C A, IsMatching H c := by
  intro c hc
  rcases Finset.mem_union.mp hc with hcA | hcC
  · exact (mem_completionCandidates.mp (hA hcA)).2.2.1
  · exact hCmatch c (Finset.mem_filter.mp hcC).1

/-- The deterministic update preserves the source antichain invariant. -/
theorem addCompletionLayer_antichain
    {H : Hypergraph V} {C A : ConflictSystem V} {j : ℕ}
    (hCantichain : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' -> ¬c ⊆ c')
    (hA : A ⊆ completionCandidates H C j) :
    ∀ c ∈ addCompletionLayer C A, ∀ c' ∈ addCompletionLayer C A,
      c ≠ c' -> ¬c ⊆ c' := by
  intro c hc c' hc' hne hsub
  rcases Finset.mem_union.mp hc with hcA | hcC <;>
    rcases Finset.mem_union.mp hc' with hc'A | hc'C
  · have hcj := (mem_completionCandidates.mp (hA hcA)).2.1
    have hc'j := (mem_completionCandidates.mp (hA hc'A)).2.1
    have hcard := Finset.card_le_card hsub
    rw [hcj, hc'j] at hcard
    apply hne
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  · have hcdata := mem_completionCandidates.mp (hA hcA)
    have hc'Cdata := Finset.mem_filter.mp hc'C
    have hstrict : c ⊂ c' := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    exact hc'Cdata.2 ⟨c, hcA, hstrict⟩
  · have hcdata := Finset.mem_filter.mp hcC
    have hc'Adata := mem_completionCandidates.mp (hA hc'A)
    exact hc'Adata.2.2.2 c hcdata.1 hsub
  · have hcdata := Finset.mem_filter.mp hcC
    have hc'data := Finset.mem_filter.mp hc'C
    exact hCantichain c hcdata.1 c' hc'data.1 hne hsub

/-! ## Restricting test weights after regularisation -/

/-- The finite positive support of a test weight on its intended host
domain.  Lemma 8.6 removes members of each test system, not whole test
systems; this is the weighted analogue of that finite family. -/
def positiveSupport (H : Hypergraph V) (j : ℕ) (w : TestWeight V) :
    Finset (Hypergraph V) :=
  (H.powersetCard j).filter fun S => 0 < w S

/-- Positive-support tests which are destroyed by an enlarged conflict
system. -/
def killedSupport (H : Hypergraph V) (D : ConflictSystem V)
    (j : ℕ) (w : TestWeight V) : Finset (Hypergraph V) :=
  (positiveSupport H j w).filter fun S => ¬ConflictFree D S

/-- Total weight lost when the test is restricted to `D`-free members. -/
def killedWeight (H : Hypergraph V) (D : ConflictSystem V)
    (j : ℕ) (w : TestWeight V) : ℝ :=
  ∑ S ∈ killedSupport H D j w, w S

/-- Pointwise restriction of a test weight to the members which remain
conflict-free. -/
def restrictWeight (D : ConflictSystem V) (w : TestWeight V) : TestWeight V :=
  fun S => if ConflictFree D S then w S else 0

/-- The `0`--`1` test attached to the positive support of a weight.  Running
the same McDiarmid estimate for this test gives the cardinality half of
property (VI), while running it for `w` gives the lost-mass half. -/
def positiveSupportIndicator (H : Hypergraph V) (j : ℕ)
    (w : TestWeight V) : TestWeight V :=
  fun S => if S ∈ positiveSupport H j w then 1 else 0

theorem positiveSupport_supportIndicator
    (H : Hypergraph V) (j : ℕ) (w : TestWeight V) :
    positiveSupport H j (positiveSupportIndicator H j w) =
      positiveSupport H j w := by
  ext S
  constructor
  · intro hS
    have hdata := Finset.mem_filter.mp hS
    by_cases hmem : S ∈ positiveSupport H j w
    · exact hmem
    · simp [positiveSupportIndicator, hmem] at hdata
  · intro hS
    have hdata := Finset.mem_filter.mp hS
    apply Finset.mem_filter.mpr
    exact ⟨hdata.1, by simp [positiveSupportIndicator, hS]⟩

theorem killedSupport_supportIndicator
    (H : Hypergraph V) (D : ConflictSystem V) (j : ℕ)
    (w : TestWeight V) :
    killedSupport H D j (positiveSupportIndicator H j w) =
      killedSupport H D j w := by
  simp only [killedSupport, positiveSupport_supportIndicator]

/-- Destroyed mass of the support indicator is exactly the number of
destroyed positive-support members. -/
theorem killedWeight_supportIndicator
    (H : Hypergraph V) (D : ConflictSystem V) (j : ℕ)
    (w : TestWeight V) :
    killedWeight H D j (positiveSupportIndicator H j w) =
      ((killedSupport H D j w).card : ℝ) := by
  rw [killedWeight, killedSupport_supportIndicator]
  calc
    (∑ S ∈ killedSupport H D j w,
        positiveSupportIndicator H j w S) =
        ∑ _S ∈ killedSupport H D j w, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hpos : S ∈ positiveSupport H j w :=
        (Finset.mem_filter.mp hS).1
      simp [positiveSupportIndicator, hpos]
    _ = ((killedSupport H D j w).card : ℝ) := by simp

theorem positiveSupportIndicator_nonneg
    (H : Hypergraph V) (j : ℕ) (w : TestWeight V) (S : Hypergraph V) :
    0 ≤ positiveSupportIndicator H j w S := by
  simp only [positiveSupportIndicator]
  split_ifs <;> norm_num

theorem positiveSupportIndicator_freeZero
    {H : Hypergraph V} {C : ConflictSystem V} {j : ℕ}
    {w : TestWeight V}
    (hfreeZero : ∀ S ∈ H.powersetCard j,
      (∃ c ∈ C, c ⊆ S) → w S = 0) :
    ∀ S ∈ H.powersetCard j,
      (∃ c ∈ C, c ⊆ S) → positiveSupportIndicator H j w S = 0 := by
  intro S hSH hcontains
  have hz := hfreeZero S hSH hcontains
  have hnmem : S ∉ positiveSupport H j w := by
    intro hS
    have hpos := (Finset.mem_filter.mp hS).2
    linarith
  simp [positiveSupportIndicator, hnmem]

theorem testTotal_positiveSupportIndicator
    (H : Hypergraph V) (j : ℕ) (w : TestWeight V) :
    testTotal (positiveSupportIndicator H j w) H j =
      ((positiveSupport H j w).card : ℝ) := by
  let s := H.powersetCard j
  let t := positiveSupport H j w
  have ht : t ⊆ s := Finset.filter_subset _ _
  rw [testTotal]
  change (∑ S ∈ s, if S ∈ t then (1 : ℝ) else 0) = (t.card : ℝ)
  calc
    (∑ S ∈ s, if S ∈ t then (1 : ℝ) else 0) =
        (((s.filter fun S => S ∈ t).card : ℕ) : ℝ) := by
      rw [Finset.card_filter]
      norm_cast
    _ = (t.card : ℝ) := by
      have heq : s.filter (fun S => S ∈ t) = t := by
        ext S
        simp only [mem_filter]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨ht h, h⟩
      rw [heq]

/-- If the old test has zero weight on old-conflicting members, the random
destroyed-weight statistic is exactly the mass killed by the updated
conflict system. -/
theorem killedWeight_addCompletionLayer_eq_sampledKilledWeight {n : ℕ}
    (H : Hypergraph V) (C : ConflictSystem V) (testJ : ℕ)
    (w : TestWeight V) (candidate : Fin n -> Hypergraph V)
    (x : Fin n -> Bool)
    (hw : ∀ S, 0 ≤ w S)
    (hfreeZero : ∀ S ∈ H.powersetCard testJ,
      (∃ c ∈ C, c ⊆ S) -> w S = 0) :
    killedWeight H
        (addCompletionLayer C (sampledCompletionLayer candidate x)) testJ w =
      sampledKilledWeight H testJ w candidate x := by
  rw [killedWeight, killedSupport, positiveSupport, sampledKilledWeight]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hSH
  by_cases hpos : 0 < w S
  · have holdfree : ConflictFree C S := by
      intro c hcC hcS
      have hz := hfreeZero S hSH ⟨c, hcC, hcS⟩
      linarith
    have hiff :
        ¬ConflictFree
            (addCompletionLayer C (sampledCompletionLayer candidate x)) S ↔
          ∃ i, x i = true ∧ candidate i ⊆ S := by
      constructor
      · intro hnfree
        obtain ⟨c, hcnew, hcS⟩ := not_conflictFree_iff.mp hnfree
        rcases Finset.mem_union.mp hcnew with hcA | hcold
        · obtain ⟨i, hi, _hic⟩ := Finset.mem_image.mp hcA
          subst c
          exact ⟨i, (Finset.mem_filter.mp hi).2, hcS⟩
        · exact (holdfree c (Finset.mem_filter.mp hcold).1 hcS).elim
      · rintro ⟨i, hxi, hiS⟩
        apply not_conflictFree_iff.mpr
        refine ⟨candidate i, selected_subset_addCompletionLayer C _ ?_, hiS⟩
        exact Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩, rfl⟩
    by_cases hnfree :
        ¬ConflictFree
          (addCompletionLayer C (sampledCompletionLayer candidate x)) S
    · have hselected := hiff.mp hnfree
      simp [hpos, hnfree, hselected]
    · have hselected : ¬∃ i, x i = true ∧ candidate i ⊆ S := by
        exact fun h => hnfree (hiff.mpr h)
      simp [hpos, hnfree, hselected]
  · have hz : w S = 0 := le_antisymm (not_lt.mp hpos) (hw S)
    simp [hpos, hz]

@[simp] theorem restrictWeight_apply_free {D : ConflictSystem V}
    {w : TestWeight V} {S : Hypergraph V} (hS : ConflictFree D S) :
    restrictWeight D w S = w S := by
  simp [restrictWeight, hS]

@[simp] theorem restrictWeight_apply_not_free {D : ConflictSystem V}
    {w : TestWeight V} {S : Hypergraph V} (hS : ¬ConflictFree D S) :
    restrictWeight D w S = 0 := by
  simp [restrictWeight, hS]

theorem restrictWeight_nonneg {D : ConflictSystem V} {w : TestWeight V}
    (hw : ∀ S, 0 ≤ w S) (S : Hypergraph V) :
    0 ≤ restrictWeight D w S := by
  simp only [restrictWeight]
  split_ifs
  · exact hw S
  · exact le_rfl

theorem restrictWeight_le {D : ConflictSystem V} {w : TestWeight V}
    (hw : ∀ S, 0 ≤ w S) (S : Hypergraph V) :
    restrictWeight D w S ≤ w S := by
  simp only [restrictWeight]
  split_ifs
  · exact le_rfl
  · exact hw S

/-- Restricting first to the old system and then to one completion update
is the same as restricting directly to the update.  This is the
deterministic identity which lets the three stagewise loss estimates
accumulate without deleting test indices. -/
theorem restrictWeight_addCompletionLayer_comp
    (C A : ConflictSystem V) (w : TestWeight V) :
    restrictWeight (addCompletionLayer C A) (restrictWeight C w) =
      restrictWeight (addCompletionLayer C A) w := by
  funext S
  by_cases hnew : ConflictFree (addCompletionLayer C A) S
  · have hold : ConflictFree C S :=
      conflictFree_addCompletionLayer_imp_old hnew
    simp [restrictWeight, hnew, hold]
  · simp [restrictWeight, hnew]

/-- The restricted total is the original total minus exactly the killed
mass.  This identity is the deterministic bridge used after Property VI. -/
theorem testTotal_restrictWeight_add_killedWeight
    (H : Hypergraph V) (D : ConflictSystem V) (j : ℕ)
    (w : TestWeight V) (hw : ∀ S, 0 ≤ w S) :
    testTotal (restrictWeight D w) H j + killedWeight H D j w =
      testTotal w H j := by
  rw [testTotal, testTotal, killedWeight]
  rw [killedSupport, positiveSupport]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hpos : 0 < w S
  · by_cases hfree : ConflictFree D S
    · simp [restrictWeight, hfree, killedSupport, positiveSupport, hS, hpos]
    · simp [restrictWeight, hfree, killedSupport, positiveSupport, hS, hpos]
  · have hz : w S = 0 := le_antisymm (not_lt.mp hpos) (hw S)
    simp [restrictWeight, killedSupport, positiveSupport, hS, hpos, hz]

/-- Lost mass telescopes across one completion stage: the final loss of the
original weight is its old loss plus the newly killed mass of its
old-system restriction. -/
theorem killedWeight_addCompletionLayer_telescope
    (H : Hypergraph V) (C A : ConflictSystem V) (j : ℕ)
    (w : TestWeight V) (hw : ∀ S, 0 ≤ w S) :
    killedWeight H (addCompletionLayer C A) j w =
      killedWeight H C j w +
        killedWeight H (addCompletionLayer C A) j (restrictWeight C w) := by
  have htotalNew := testTotal_restrictWeight_add_killedWeight
    H (addCompletionLayer C A) j w hw
  have htotalOld := testTotal_restrictWeight_add_killedWeight H C j w hw
  have htotalStep := testTotal_restrictWeight_add_killedWeight
    H (addCompletionLayer C A) j (restrictWeight C w)
      (restrictWeight_nonneg hw)
  rw [restrictWeight_addCompletionLayer_comp] at htotalStep
  linarith

/-- The positive-support members killed before and during one completion
stage form a disjoint union. -/
theorem killedSupport_addCompletionLayer_union
    (H : Hypergraph V) (C A : ConflictSystem V) (j : ℕ)
    (w : TestWeight V) :
    killedSupport H (addCompletionLayer C A) j w =
      killedSupport H C j w ∪
        killedSupport H (addCompletionLayer C A) j (restrictWeight C w) := by
  ext S
  simp only [killedSupport, positiveSupport, Finset.mem_filter,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨hSH, hpos⟩, hnnew⟩
    by_cases hold : ConflictFree C S
    · exact Or.inr ⟨⟨hSH, by simpa [restrictWeight, hold] using hpos⟩, hnnew⟩
    · exact Or.inl ⟨⟨hSH, hpos⟩, hold⟩
  · rintro (⟨⟨hSH, hpos⟩, hnold⟩ | ⟨⟨hSH, hpos⟩, hnnew⟩)
    · refine ⟨⟨hSH, hpos⟩, ?_⟩
      intro hnew
      exact hnold (conflictFree_addCompletionLayer_imp_old hnew)
    · refine ⟨⟨hSH, ?_⟩, hnnew⟩
      by_cases hold : ConflictFree C S
      · simpa [restrictWeight, hold] using hpos
      · simp [restrictWeight, hold] at hpos

theorem killedSupport_addCompletionLayer_disjoint
    (H : Hypergraph V) (C A : ConflictSystem V) (j : ℕ)
    (w : TestWeight V) :
    Disjoint (killedSupport H C j w)
      (killedSupport H (addCompletionLayer C A) j (restrictWeight C w)) := by
  rw [Finset.disjoint_left]
  intro S hSold hSnew
  have hnold : ¬ConflictFree C S := (Finset.mem_filter.mp hSold).2
  have hposRestrict : 0 < restrictWeight C w S :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hSnew).1).2
  rw [restrictWeight] at hposRestrict
  split at hposRestrict
  next hfree => exact hnold hfree
  next => linarith

theorem killedSupport_addCompletionLayer_telescope
    (H : Hypergraph V) (C A : ConflictSystem V) (j : ℕ)
    (w : TestWeight V) :
    (killedSupport H (addCompletionLayer C A) j w).card =
      (killedSupport H C j w).card +
        (killedSupport H (addCompletionLayer C A) j
          (restrictWeight C w)).card := by
  rw [killedSupport_addCompletionLayer_union,
    Finset.card_union_of_disjoint
      (killedSupport_addCompletionLayer_disjoint H C A j w)]

theorem testTotal_restrictWeight_le
    (H : Hypergraph V) (D : ConflictSystem V) (j : ℕ)
    (w : TestWeight V) (hw : ∀ S, 0 ≤ w S) :
    testTotal (restrictWeight D w) H j ≤ testTotal w H j := by
  apply Finset.sum_le_sum
  intro S _hS
  exact restrictWeight_le hw S

theorem testExtension_restrictWeight_le
    (H : Hypergraph V) (D : ConflictSystem V) (j : ℕ)
    (root : Hypergraph V) (w : TestWeight V) (hw : ∀ S, 0 ≤ w S) :
    testExtension (restrictWeight D w) H j root ≤
      testExtension w H j root := by
  apply Finset.sum_le_sum
  intro S _hS
  exact restrictWeight_le hw S

/-- Deterministic test-transfer step after the probabilistic killed-mass
estimate.  The two displayed comparisons are exactly the elementary
large-`d` absorptions used to pass from `eps` to `eps / 5`; the remaining
hypothesis is Property (V) for the final regularised system. -/
theorem restrictWeight_isTrackable
    {H : Hypergraph V} {C D : ConflictSystem V} {j : ℕ}
    {ell : ℕ} {d eps : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C j ell d eps w)
    (hlarge : Real.rpow d ((j : ℝ) + eps / 5) ≤
      testTotal (restrictWeight D w) H j)
    (hext : ∀ j', 1 ≤ j' -> j' < j ->
      testTotal w H j / Real.rpow d ((j' : ℝ) + eps) ≤
        testTotal (restrictWeight D w) H j /
          Real.rpow d ((j' : ℝ) + eps / 5))
    (hlinks : ∀ S ∈ H.powersetCard j, 0 < w S -> ConflictFree D S ->
      ∀ e ∈ S, ∀ f ∈ S, e ≠ f -> ∀ j', 1 ≤ j' -> j' < ell ->
        ((((conflictLinkLayer D e j') ∩
          conflictLinkLayer D f j').card : ℝ) ≤
            Real.rpow d ((j' : ℝ) - eps / 5))) :
    IsTrackable H D j ell d (eps / 5) (restrictWeight D w) := by
  refine ⟨?_, hlarge, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact restrictWeight_nonneg hw.1.1
    · intro S
      exact (restrictWeight_le hw.1.1 S).trans (hw.1.2.1 S)
    · intro S hcard
      simp only [restrictWeight]
      split_ifs
      · exact hw.1.2.2.1 S hcard
      · rfl
    · intro S hmatch
      simp only [restrictWeight]
      split_ifs
      · exact hw.1.2.2.2 S hmatch
      · rfl
  · intro j' hj' hj'j root hrootH hrootcard
    exact (testExtension_restrictWeight_le H D j root w hw.1.1).trans
      ((hw.2.2.1 j' hj' hj'j root hrootH hrootcard).trans
        (hext j' hj' hj'j))
  · intro S hSH hpos e he f hf hef j' hj' hj'4
    have hnonneg := hw.1.1 S
    have hle := restrictWeight_le (D := D) hw.1.1 S
    have hwpos : 0 < w S := hpos.trans_le hle
    have hfree : ConflictFree D S := by
      by_contra hnfree
      rw [restrictWeight_apply_not_free hnfree] at hpos
      exact (lt_irrefl 0) hpos
    exact hlinks S hSH hwpos hfree e he f hf hef j' hj' hj'4
  · intro S hSH hcontains
    have hnfree : ¬ConflictFree D S := by
      exact not_conflictFree_iff.mpr hcontains
    exact restrictWeight_apply_not_free hnfree

/-! ## The specialised regularisation certificate -/

/-- The exact source degree interval `(1 plus-or-minus err) D`. -/
def InRelativeInterval (x D err : ℝ) : Prop :=
  (1 - err) * D ≤ x ∧ x ≤ (1 + err) * D

/-- Literal deterministic properties (I)--(V) in the `j`th random
completion step of GJKKL Lemma 8.6, specialised to `ell = 4`. -/
def HasStagePropertiesIV
    (H : Hypergraph V) (base next : ConflictSystem V)
    (d eps : ℝ) (j : ℕ) : Prop :=
  2 ≤ j ∧ j ≤ 4 ∧
  (∀ e ∈ H,
    InRelativeInterval (degree (conflictLayer next j) e : ℝ)
      (completionTarget d eps (layerMaxDegree H base j : ℝ) j)
      (Real.rpow d (-eps))) ∧
  (∀ q, 2 ≤ q → q < j → ∀ root, root.card = q →
    (codegree (conflictLayer next j) root : ℝ) ≤
      Real.rpow d ((j : ℝ) - (q : ℝ) - eps / 4)) ∧
  (j = 2 → ∀ e ∈ H, ∀ v,
    (conditionC4Count H next e v : ℝ) ≤
      Real.rpow d (1 - eps / 4)) ∧
  (j = 2 → ∀ e ∈ H, ∀ f ∈ H, Disjoint e f →
    (conditionC5Count H next e f : ℝ) ≤
      Real.rpow d (1 - eps / 4)) ∧
  (∀ e ∈ H, ∀ f ∈ H, Disjoint e f →
    {e, f} ∉ conflictLayer next 2 →
    ((((conflictLinkLayer next e (j - 1)) ∩
      conflictLinkLayer next f (j - 1)).card : ℕ) : ℝ) ≤
      Real.rpow d ((j - 1 : ℕ) - eps / 4))

@[simp] theorem mem_conflictLayer_addCompletionLayer
    {C A : ConflictSystem V} {r : ℕ} {c : Hypergraph V} :
    c ∈ conflictLayer (addCompletionLayer C A) r ↔
      (c ∈ A ∧ c.card = r) ∨
      (c ∈ C ∧ (¬ ∃ a ∈ A, a ⊂ c) ∧ c.card = r) := by
  simp only [conflictLayer, addCompletionLayer, mem_filter, mem_union]
  aesop

/-- Completion at uniformity `j` leaves every smaller conflict layer
literally unchanged. -/
theorem conflictLayer_addCompletionLayer_of_lt
    {C A : ConflictSystem V} {r j : ℕ}
    (hA : IsUniform A j) (hrj : r < j) :
    conflictLayer (addCompletionLayer C A) r = conflictLayer C r := by
  ext c
  rw [mem_conflictLayer_addCompletionLayer]
  simp only [mem_conflictLayer]
  constructor
  · rintro (⟨hcA, hcr⟩ | ⟨hcC, _, hcr⟩)
    · have hcj := hA c hcA
      omega
    · exact ⟨hcC, hcr⟩
  · rintro ⟨hcC, hcr⟩
    refine Or.inr ⟨hcC, ?_, hcr⟩
    rintro ⟨a, haA, hac⟩
    have haj := hA a haA
    have hlt := Finset.card_lt_card hac
    omega

/-- At the current uniformity no old conflict is deleted, so the new
layer is exactly the union of the old layer and the sampled layer. -/
theorem conflictLayer_addCompletionLayer_eq
    {C A : ConflictSystem V} {j : ℕ}
    (hA : IsUniform A j) :
    conflictLayer (addCompletionLayer C A) j = conflictLayer C j ∪ A := by
  ext c
  rw [mem_conflictLayer_addCompletionLayer]
  simp only [mem_union, mem_conflictLayer]
  constructor
  · rintro (⟨hcA, hcj⟩ | ⟨hcC, _, hcj⟩)
    · exact Or.inr hcA
    · exact Or.inl ⟨hcC, hcj⟩
  · rintro (⟨hcC, hcj⟩ | hcA)
    · refine Or.inr ⟨hcC, ?_, hcj⟩
      rintro ⟨a, haA, hac⟩
      have haj := hA a haA
      have hlt := Finset.card_lt_card hac
      omega
    · exact Or.inl ⟨hcA, hA c hcA⟩

/-- Exact count decoding for property (I): the new degree is the old
degree plus the selected Bernoulli incidence count. -/
theorem degree_addCompletionLayer_sampled_eq
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (x : Fin (Fintype.card (CompletionIndex H C j)) → Bool)
    (e : Finset V) :
    (degree
        (conflictLayer
          (addCompletionLayer C
            (sampledCompletionLayer (completionCandidate H C j) x)) j) e : ℝ) =
      degree (conflictLayer C j) e +
        sampledCount (completionCandidate H C j) (fun A => e ∈ A) x := by
  rw [conflictLayer_addCompletionLayer_eq
    (sampledSourceCompletionLayer_uniform H C j x)]
  rw [degree_union_of_disjoint
    (conflictLayer_disjoint_sampledSourceCompletionLayer H C j x)]
  rw [sampledCount_eq_filter_card (completionCandidate H C j)
    (completionCandidate_injective H C j) (fun A => e ∈ A) x]
  norm_cast
  simp only [degree]
  congr 1
  apply congrArg Finset.card
  ext A
  simp only [Finset.mem_filter]

theorem bitCount_degree_eq_sampledCount
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (e : Finset V)
    (x : Fin (Fintype.card (CompletionIndex H C j)) → Bool) :
    ChernoffFinite.bitCount
        (fun i => e ∈ completionCandidate H C j i) x =
      sampledCount (completionCandidate H C j) (fun A => e ∈ A) x := rfl

theorem weightedMean_sampledDegree_eq_bitMean
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ)
    (target : ℝ) (e : Finset V) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight
          (sourceCompletionBiasAtTarget H C j target))
        (sampledCount (completionCandidate H C j) (fun A => e ∈ A)) =
      ChernoffFinite.bitMean
        (sourceCompletionBiasAtTarget H C j target)
        (fun i => e ∈ completionCandidate H C j i) := by
  rw [weightedMean_sampledCount]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hmem : e ∈ completionCandidate H C j i <;> simp [hmem]

/-- The elementary numerical decoding of property (I).  `room` is the
source expectation error (the `d^(-2 eps)` margin in the paper), and the
strict sampled deviation fits inside the remaining `d^(-eps)` window. -/
theorem inRelativeInterval_of_mean_room
    {old count mean D err room : ℝ}
    (hmean : |old + mean - D| ≤ room)
    (hdev : |count - mean| < err * D - room) :
    InRelativeInterval (old + count) D err := by
  have habs : |old + count - D| < err * D := by
    calc
      |old + count - D| = |(count - mean) + (old + mean - D)| := by ring_nf
      _ ≤ |count - mean| + |old + mean - D| := abs_add_le _ _
      _ < (err * D - room) + room := add_lt_add_of_lt_of_le hdev hmean
      _ = err * D := by ring
  have hsides := (abs_lt.mp habs)
  constructor <;> linarith

/-- Property (I) for one completion stage, extracted directly from the
finite Bernoulli product measure.  The hypotheses are precisely the
weighted-subset expectation estimate and the remaining numerical margin;
there is no selected-layer or certificate premise. -/
theorem exists_sourceWeightedCompletionLayer_degrees
    (H : Hypergraph V) (C : ConflictSystem V) (stage : ℕ)
    (target err : ℝ)
    (delta room : {e // e ∈ H} → ℝ)
    (hp : ∀ i, sourceCompletionBiasAtTarget H C stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hdelta0 : ∀ e, 0 ≤ delta e) (hdelta1 : ∀ e, delta e ≤ 1)
    (hmean : ∀ e : {e // e ∈ H},
      |(degree (conflictLayer C stage) e.1 : ℝ) +
          ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H C stage target)
            (fun i => e.1 ∈ completionCandidate H C stage i) - target| ≤
        room e)
    (hmargin : ∀ e : {e // e ∈ H},
      delta e * ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C stage target)
          (fun i => e.1 ∈ completionCandidate H C stage i) ≤
        err * target - room e)
    (hfail :
      (∑ e : {e // e ∈ H},
        2 * Real.exp (-(delta e ^ 2 *
          ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H C stage target)
            (fun i => e.1 ∈ completionCandidate H C stage i)) / 3)) < 1) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H C stage ∧
      ∀ e ∈ H,
        InRelativeInterval
          (degree (conflictLayer (addCompletionLayer C A) stage) e : ℝ)
          target err := by
  let p := sourceCompletionBiasAtTarget H C stage target
  let active : {e // e ∈ H} →
      Fin (Fintype.card (CompletionIndex H C stage)) → Prop :=
    fun e i => e.1 ∈ completionCandidate H C stage i
  let Bad : {e // e ∈ H} →
      Set (Fin (Fintype.card (CompletionIndex H C stage)) → Bool) :=
    fun e => {x | delta e * ChernoffFinite.bitMean p (active e) ≤
      |ChernoffFinite.bitCount (active e) x -
        ChernoffFinite.bitMean p (active e)|}
  have hmass :
      (∑ e : {e // e ∈ H},
        McDiarmid.eventMass (McDiarmid.bernoulliWeight p) (Bad e)) < 1 := by
    refine (Finset.sum_le_sum fun e _he => ?_).trans_lt (by simpa [p, active] using hfail)
    exact ChernoffFinite.eventMass_two_sided_multiplicative
      p (active e) (delta e) hp (hdelta0 e) (hdelta1 e)
  obtain ⟨x, hx⟩ :=
    exists_bernoulli_avoiding_of_eventMass_sum_lt_one p Bad hp hmass
  let A := sampledCompletionLayer (completionCandidate H C stage) x
  refine ⟨A, sampledSourceCompletionLayer_subset_candidates H C stage x, ?_⟩
  intro e he
  let ee : {e // e ∈ H} := ⟨e, he⟩
  have hdev0 := hx ee
  change ¬delta ee * ChernoffFinite.bitMean p (active ee) ≤
    |ChernoffFinite.bitCount (active ee) x -
      ChernoffFinite.bitMean p (active ee)| at hdev0
  have hdev :
      |ChernoffFinite.bitCount (active ee) x -
        ChernoffFinite.bitMean p (active ee)| < err * target - room ee :=
    (lt_of_not_ge hdev0).trans_le (by simpa [p, active] using hmargin ee)
  rw [degree_addCompletionLayer_sampled_eq]
  apply inRelativeInterval_of_mean_room (room := room ee)
  · simpa [p, active, ee] using hmean ee
  · simpa [p, active, ee, bitCount_degree_eq_sampledCount] using hdev

/-- A link layer depends only on the conflict layer one rank higher. -/
theorem conflictLinkLayer_congr_of_layer_succ_eq
    {C D : ConflictSystem V} {s : ℕ}
    (h : conflictLayer C (s + 1) = conflictLayer D (s + 1))
    (e : Finset V) :
    conflictLinkLayer C e s = conflictLinkLayer D e s := by
  ext t
  simp only [conflictLinkLayer, conflictLayer, conflictLink, mem_filter,
    mem_image]
  constructor
  · rintro ⟨⟨u, ⟨huC, heu⟩, hut⟩, hts⟩
    have hupos : 0 < u.card := Finset.card_pos.mpr ⟨e, heu⟩
    have hecard : (u.erase e).card + 1 = u.card := by
      rw [Finset.card_erase_of_mem heu]
      omega
    have hucard : u.card = s + 1 := by
      rw [hut, hts] at hecard
      omega
    have huLayerC : u ∈ conflictLayer C (s + 1) := by
      exact Finset.mem_filter.mpr ⟨huC, hucard⟩
    have huLayerD : u ∈ conflictLayer D (s + 1) := by
      rw [← h]
      exact huLayerC
    exact ⟨⟨u, ⟨(Finset.mem_filter.mp huLayerD).1, heu⟩, hut⟩, hts⟩
  · rintro ⟨⟨u, ⟨huD, heu⟩, hut⟩, hts⟩
    have hupos : 0 < u.card := Finset.card_pos.mpr ⟨e, heu⟩
    have hecard : (u.erase e).card + 1 = u.card := by
      rw [Finset.card_erase_of_mem heu]
      omega
    have hucard : u.card = s + 1 := by
      rw [hut, hts] at hecard
      omega
    have huLayerD : u ∈ conflictLayer D (s + 1) := by
      exact Finset.mem_filter.mpr ⟨huD, hucard⟩
    have huLayerC : u ∈ conflictLayer C (s + 1) := by
      rw [h]
      exact huLayerD
    exact ⟨⟨u, ⟨(Finset.mem_filter.mp huLayerC).1, heu⟩, hut⟩, hts⟩

/-- Later completion stages preserve the link bound established at an
earlier stage. -/
theorem conflictLinkLayer_addCompletionLayer_of_succ_lt
    {C A : ConflictSystem V} {s j : ℕ}
    (hA : IsUniform A j) (hsj : s + 1 < j) (e : Finset V) :
    conflictLinkLayer (addCompletionLayer C A) e s =
      conflictLinkLayer C e s := by
  apply conflictLinkLayer_congr_of_layer_succ_eq
  exact conflictLayer_addCompletionLayer_of_lt hA hsj

/-- The C4 statistic depends only on the two-conflict layer. -/
theorem conditionC4Count_congr_of_layer_two_eq
    {C D : ConflictSystem V}
    (h : conflictLayer C 2 = conflictLayer D 2)
    (H : Hypergraph V) (e : Finset V) (v : V) :
    conditionC4Count H C e v = conditionC4Count H D e v := by
  simp only [conditionC4Count, twoConflictNeighbors]
  rw [h]

/-- The C5 statistic depends only on the two-conflict layer. -/
theorem conditionC5Count_congr_of_layer_two_eq
    {C D : ConflictSystem V}
    (h : conflictLayer C 2 = conflictLayer D 2)
    (H : Hypergraph V) (e f : Finset V) :
    conditionC5Count H C e f = conditionC5Count H D e f := by
  simp only [conditionC5Count, twoConflictNeighbors]
  rw [h]

/-- Completion at stage 3 or 4 preserves both special two-conflict
statistics. -/
theorem conditionC4Count_addCompletionLayer_of_two_lt
    {C A : ConflictSystem V} {j : ℕ}
    (hA : IsUniform A j) (hj : 2 < j)
    (H : Hypergraph V) (e : Finset V) (v : V) :
    conditionC4Count H (addCompletionLayer C A) e v =
      conditionC4Count H C e v := by
  apply conditionC4Count_congr_of_layer_two_eq
  exact conflictLayer_addCompletionLayer_of_lt hA hj

theorem conditionC5Count_addCompletionLayer_of_two_lt
    {C A : ConflictSystem V} {j : ℕ}
    (hA : IsUniform A j) (hj : 2 < j)
    (H : Hypergraph V) (e f : Finset V) :
    conditionC5Count H (addCompletionLayer C A) e f =
      conditionC5Count H C e f := by
  apply conditionC5Count_congr_of_layer_two_eq
  exact conflictLayer_addCompletionLayer_of_lt hA hj

section UpperObservables

variable [Fintype V]

/-- The roots which occur in property (II) at completion rank `stage`. -/
abbrev StageCodegreeIndex (V : Type*) [Fintype V] [DecidableEq V]
    (stage : ℕ) :=
  {root : Hypergraph V // 2 ≤ root.card ∧ root.card < stage}

/-- The roots of the stage-two C4 observables.  The proof field makes this
type empty at stages three and four. -/
structure StageC4Index (H : Hypergraph V) (stage : ℕ) where
  edge : Finset V
  edge_mem : edge ∈ H
  vertex : V
  stage_eq : stage = 2

deriving instance Fintype for StageC4Index

/-- Non-oriented pairs index one block-count observable each. -/
structure HostEdgePair (H : Hypergraph V) where
  left : Finset V
  left_mem : left ∈ H
  right : Finset V
  right_mem : right ∈ H
  disjoint : Disjoint left right

deriving instance Fintype for HostEdgePair

structure StageC5BlockIndex (H : Hypergraph V) (stage : ℕ) where
  pair : HostEdgePair H
  stage_eq : stage = 2

deriving instance Fintype for StageC5BlockIndex

structure StageCommonBlockIndex (H : Hypergraph V)
    (current : ConflictSystem V) where
  pair : HostEdgePair H
  nonconflict : {pair.left, pair.right} ∉ conflictLayer current 2

deriving instance Fintype for StageCommonBlockIndex

/-- Linear observables are precisely (II) and (III). -/
abbrev StageLinearUpperIndex (H : Hypergraph V) (stage : ℕ) :=
  Sum (StageCodegreeIndex V stage) (StageC4Index H stage)

/-- Block observables are precisely (IV) and (V). -/
abbrev StageBlockUpperIndex (H : Hypergraph V)
    (current : ConflictSystem V) (stage : ℕ) :=
  Sum (StageC5BlockIndex H stage) (StageCommonBlockIndex H current)

def stageBlockLeft {H : Hypergraph V} {current : ConflictSystem V}
    {stage : ℕ} (a : StageBlockUpperIndex H current stage) : Finset V :=
  match a with
  | Sum.inl a => a.pair.left
  | Sum.inr a => a.pair.left

def stageBlockRight {H : Hypergraph V} {current : ConflictSystem V}
    {stage : ℕ} (a : StageBlockUpperIndex H current stage) : Finset V :=
  match a with
  | Sum.inl a => a.pair.right
  | Sum.inr a => a.pair.right

/-- Property-(II) codegrees split as the old codegree plus the selected
candidate incidence count. -/
theorem codegree_addCompletionLayer_sampled_eq
    (H : Hypergraph V) (C : ConflictSystem V) (stage : ℕ)
    (x : Fin (Fintype.card (CompletionIndex H C stage)) → Bool)
    (root : Hypergraph V) :
    (codegree
        (conflictLayer
          (addCompletionLayer C
            (sampledCompletionLayer (completionCandidate H C stage) x))
          stage) root : ℝ) =
      codegree (conflictLayer C stage) root +
        sampledCount (completionCandidate H C stage) (fun A => root ⊆ A) x := by
  rw [conflictLayer_addCompletionLayer_eq
    (sampledSourceCompletionLayer_uniform H C stage x)]
  rw [show codegree
      (conflictLayer C stage ∪
        sampledCompletionLayer (completionCandidate H C stage) x) root =
      codegree (conflictLayer C stage) root +
        codegree
          (sampledCompletionLayer (completionCandidate H C stage) x) root by
    change
      (((conflictLayer C stage ∪
        sampledCompletionLayer (completionCandidate H C stage) x).filter
          fun A => root ⊆ A).card) =
        ((conflictLayer C stage).filter fun A => root ⊆ A).card +
          ((sampledCompletionLayer (completionCandidate H C stage) x).filter
            fun A => root ⊆ A).card
    rw [Finset.filter_union]
    rw [Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro A hAold hAnew
    exact (Finset.disjoint_left.mp
      (conflictLayer_disjoint_sampledSourceCompletionLayer H C stage x))
      (Finset.mem_filter.mp hAold).1 (Finset.mem_filter.mp hAnew).1]
  rw [sampledCount_eq_filter_card (completionCandidate H C stage)
    (completionCandidate_injective H C stage) (fun A => root ⊆ A) x]
  norm_cast
  simp only [codegree]
  congr 1
  apply congrArg Finset.card
  ext A
  simp only [Finset.mem_filter]

/-! ### Exact block observables for properties (IV) and (V) -/

abbrev CompletionCoordinate (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) :=
  Fin (Fintype.card (CompletionIndex H current stage))

/-- Coordinate `i` supplies the link remainder `T` at the root edge `e`. -/
def CandidateRealizesRemainder (H : Hypergraph V)
    (current : ConflictSystem V) (stage : ℕ)
    (e : Finset V) (T : Hypergraph V)
    (i : CompletionCoordinate H current stage) : Prop :=
  e ∈ completionCandidate H current stage i ∧
    (completionCandidate H current stage i).erase e = T

theorem candidateRealizesRemainder_injective
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (e : Finset V) (T : Hypergraph V)
    {i i' : CompletionCoordinate H current stage}
    (hi : CandidateRealizesRemainder H current stage e T i)
    (hi' : CandidateRealizesRemainder H current stage e T i') :
    i = i' := by
  apply completionCandidate_injective H current stage
  calc
    completionCandidate H current stage i =
        insert e ((completionCandidate H current stage i).erase e) :=
      (Finset.insert_erase hi.1).symm
    _ = insert e T := by rw [hi.2]
    _ = insert e ((completionCandidate H current stage i').erase e) := by
      rw [hi'.2]
    _ = completionCandidate H current stage i' :=
      Finset.insert_erase hi'.1

/-- The coordinates which must be selected to create a common link
remainder.  A side already present in `current` contributes no coordinate;
an absent side contributes its unique completion coordinate. -/
def commonLinkRequiredCoordinates (H : Hypergraph V)
    (current : ConflictSystem V) (stage : ℕ)
    (e f : Finset V) (T : Hypergraph V) :
    Finset (CompletionCoordinate H current stage) :=
  Finset.univ.filter fun i =>
    (T ∉ conflictLinkLayer current e (stage - 1) ∧
      CandidateRealizesRemainder H current stage e T i) ∨
    (T ∉ conflictLinkLayer current f (stage - 1) ∧
      CandidateRealizesRemainder H current stage f T i)

/-- Remainders which can become new common links in this completion stage.
The two availability clauses are the exact old-or-candidate alternatives. -/
abbrev CommonLinkBlockLabel (H : Hypergraph V)
    (current : ConflictSystem V) (stage : ℕ) (e f : Finset V) :=
  {T : Hypergraph V //
    T.card = stage - 1 ∧
    (T ∈ conflictLinkLayer current e (stage - 1) ∨
      ∃ i, CandidateRealizesRemainder H current stage e T i) ∧
    (T ∈ conflictLinkLayer current f (stage - 1) ∨
      ∃ i, CandidateRealizesRemainder H current stage f T i) ∧
    ¬(T ∈ conflictLinkLayer current e (stage - 1) ∧
      T ∈ conflictLinkLayer current f (stage - 1))}

abbrev StageBlockLabel (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (a : StageBlockUpperIndex H current stage) :=
  CommonLinkBlockLabel H current stage (stageBlockLeft a) (stageBlockRight a)

def stageBlockFamily (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (a : StageBlockUpperIndex H current stage)
    (i : Fin (Fintype.card (StageBlockLabel H current stage a))) :
    Finset (CompletionCoordinate H current stage) :=
  let T := (Fintype.equivFin (StageBlockLabel H current stage a)).symm i
  commonLinkRequiredCoordinates H current stage
    (stageBlockLeft a) (stageBlockRight a) T.1

def allCoordinatesSelected {n : ℕ} (x : Fin n → Bool)
    (block : Finset (Fin n)) : Prop :=
  ∀ i ∈ block, x i = true

/-- The exact nonlinear observable for the new part of one common-link
intersection.  Every summand is a conjunction of one or two coordinates. -/
def commonLinkBlockCount (H : Hypergraph V)
    (current : ConflictSystem V) (stage : ℕ)
    (e f : Finset V)
    (x : CompletionCoordinate H current stage → Bool) : ℕ :=
  (Finset.univ.filter fun T : CommonLinkBlockLabel H current stage e f =>
    allCoordinatesSelected x
      (commonLinkRequiredCoordinates H current stage e f T.1)).card

/-- Exact membership decoder for one side of a sampled completion. -/
theorem mem_conflictLinkLayer_addCompletionLayer_sampled_iff
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hstage : 1 ≤ stage)
    (x : CompletionCoordinate H current stage → Bool)
    (e : Finset V) (T : Hypergraph V) :
    T ∈ conflictLinkLayer
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        e (stage - 1) ↔
      T ∈ conflictLinkLayer current e (stage - 1) ∨
        ∃ i, x i = true ∧
          CandidateRealizesRemainder H current stage e T i := by
  let A := sampledCompletionLayer (completionCandidate H current stage) x
  have hu : IsUniform A stage :=
    sampledSourceCompletionLayer_uniform H current stage x
  constructor
  · intro hT
    obtain ⟨⟨c, hcnew, hec, hcerase⟩, hTcard⟩ :=
      mem_conflictLinkLayer.mp hT
    have hccard : c.card = stage := by
      have := Finset.card_erase_add_one hec
      rw [hcerase, hTcard] at this
      omega
    have hcLayer : c ∈ conflictLayer
        (addCompletionLayer current A) stage :=
      mem_conflictLayer.mpr ⟨hcnew, hccard⟩
    rw [conflictLayer_addCompletionLayer_eq hu] at hcLayer
    rcases Finset.mem_union.mp hcLayer with hcold | hcA
    · exact Or.inl (mem_conflictLinkLayer.mpr
        ⟨⟨c, (mem_conflictLayer.mp hcold).1, hec, hcerase⟩, hTcard⟩)
    · obtain ⟨i, hi, hic⟩ := Finset.mem_image.mp hcA
      refine Or.inr ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
      subst c
      exact ⟨hec, hcerase⟩
  · intro hT
    apply mem_conflictLinkLayer.mpr
    rcases hT with hold | hnew
    · obtain ⟨⟨c, hcold, hec, hcerase⟩, hTcard⟩ :=
        mem_conflictLinkLayer.mp hold
      have hccard : c.card = stage := by
        have := Finset.card_erase_add_one hec
        rw [hcerase, hTcard] at this
        omega
      refine ⟨⟨c, ?_, hec, hcerase⟩, hTcard⟩
      have hcLayer : c ∈ conflictLayer current stage :=
        mem_conflictLayer.mpr ⟨hcold, hccard⟩
      have : c ∈ conflictLayer (addCompletionLayer current A) stage := by
        rw [conflictLayer_addCompletionLayer_eq hu]
        exact Finset.mem_union_left _ hcLayer
      exact (mem_conflictLayer.mp this).1
    · obtain ⟨i, hxi, hi⟩ := hnew
      let c := completionCandidate H current stage i
      have hcA : c ∈ A := by
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩, rfl⟩
      have hcLayer : c ∈ conflictLayer (addCompletionLayer current A) stage := by
        rw [conflictLayer_addCompletionLayer_eq hu]
        exact Finset.mem_union_right _ hcA
      refine ⟨⟨c, (mem_conflictLayer.mp hcLayer).1, hi.1, hi.2⟩, ?_⟩
      have hcstage := completionCandidates_uniform H current stage c
        (completionCandidate_mem H current stage i)
      have := Finset.card_erase_add_one hi.1
      rw [hcstage, hi.2] at this
      omega

theorem not_mem_remainder_of_mem_conflictLinkLayer
    {C : ConflictSystem V} {stage : ℕ} {e : Finset V} {T : Hypergraph V}
    (hT : T ∈ conflictLinkLayer C e (stage - 1)) :
    e ∉ T := by
  obtain ⟨⟨c, _hc, _hec, hcerase⟩, _hcard⟩ :=
    mem_conflictLinkLayer.mp hT
  rw [← hcerase]
  simp

theorem not_mem_remainder_of_candidateRealizes
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    {e : Finset V} {T : Hypergraph V}
    {i : CompletionCoordinate H current stage}
    (hi : CandidateRealizesRemainder H current stage e T i) :
    e ∉ T := by
  rw [← hi.2]
  simp

theorem CommonLinkBlockLabel.not_mem_left
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (e f : Finset V) (T : CommonLinkBlockLabel H current stage e f) :
    e ∉ T.1 := by
  rcases T.2.2.1 with hold | ⟨i, hi⟩
  · exact not_mem_remainder_of_mem_conflictLinkLayer hold
  · exact not_mem_remainder_of_candidateRealizes H current stage hi

theorem CommonLinkBlockLabel.not_mem_right
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (e f : Finset V) (T : CommonLinkBlockLabel H current stage e f) :
    f ∉ T.1 := by
  rcases T.2.2.2.1 with hold | ⟨i, hi⟩
  · exact not_mem_remainder_of_mem_conflictLinkLayer hold
  · exact not_mem_remainder_of_candidateRealizes H current stage hi

/-- On a statically admissible remainder, selecting every required
coordinate is equivalent to making the remainder occur in both final
links. -/
theorem allCoordinatesSelected_commonLinkRequired_iff
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hstage : 1 ≤ stage) (e f : Finset V)
    (T : CommonLinkBlockLabel H current stage e f)
    (x : CompletionCoordinate H current stage → Bool) :
    allCoordinatesSelected x
        (commonLinkRequiredCoordinates H current stage e f T.1) ↔
      T.1 ∈ conflictLinkLayer
          (addCompletionLayer current
            (sampledCompletionLayer (completionCandidate H current stage) x))
          e (stage - 1) ∧
      T.1 ∈ conflictLinkLayer
          (addCompletionLayer current
            (sampledCompletionLayer (completionCandidate H current stage) x))
          f (stage - 1) := by
  rw [mem_conflictLinkLayer_addCompletionLayer_sampled_iff
      H current stage hstage x e T.1,
    mem_conflictLinkLayer_addCompletionLayer_sampled_iff
      H current stage hstage x f T.1]
  constructor
  · intro hall
    constructor
    · by_cases hold : T.1 ∈ conflictLinkLayer current e (stage - 1)
      · exact Or.inl hold
      · obtain ⟨i, hi⟩ := T.2.2.1.resolve_left hold
        right
        refine ⟨i, ?_, hi⟩
        apply hall i
        simp only [commonLinkRequiredCoordinates, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact Or.inl ⟨hold, hi⟩
    · by_cases hold : T.1 ∈ conflictLinkLayer current f (stage - 1)
      · exact Or.inl hold
      · obtain ⟨i, hi⟩ := T.2.2.2.1.resolve_left hold
        right
        refine ⟨i, ?_, hi⟩
        apply hall i
        simp only [commonLinkRequiredCoordinates, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact Or.inr ⟨hold, hi⟩
  · rintro ⟨hefinal, hffinal⟩ i hiBlock
    simp only [commonLinkRequiredCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and] at hiBlock
    rcases hiBlock with ⟨heold, hie⟩ | ⟨hfold, hif⟩
    · rcases hefinal with hold | ⟨i', hi'x, hi'e⟩
      · exact (heold hold).elim
      · rwa [candidateRealizesRemainder_injective H current stage e T.1
          hie hi'e]
    · rcases hffinal with hold | ⟨i', hi'x, hi'f⟩
      · exact (hfold hold).elim
      · rwa [candidateRealizesRemainder_injective H current stage f T.1
          hif hi'f]

/-- Different common-link remainders use disjoint coordinate blocks.  The
cross-oriented case is excluded because an `e`-remainder never contains
`e`, while one candidate realizing both orientations would force it to
contain the opposite root. -/
theorem disjoint_commonLinkRequiredCoordinates
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (e f : Finset V) (T U : CommonLinkBlockLabel H current stage e f)
    (hTU : T ≠ U) :
    Disjoint
      (commonLinkRequiredCoordinates H current stage e f T.1)
      (commonLinkRequiredCoordinates H current stage e f U.1) := by
  rw [Finset.disjoint_left]
  intro i hiT hiU
  simp only [commonLinkRequiredCoordinates, Finset.mem_filter,
    Finset.mem_univ, true_and] at hiT hiU
  rcases hiT with ⟨_, hieT⟩ | ⟨_, hifT⟩ <;>
    rcases hiU with ⟨_, hieU⟩ | ⟨_, hifU⟩
  · apply hTU
    apply Subtype.ext
    exact hieT.2.symm.trans hieU.2
  · by_cases hef : e = f
    · subst f
      apply hTU
      apply Subtype.ext
      exact hieT.2.symm.trans hifU.2
    · exact T.not_mem_right H current stage e f (by
        rw [← hieT.2]
        exact Finset.mem_erase.mpr ⟨Ne.symm hef, hifU.1⟩)
  · by_cases hef : e = f
    · subst f
      apply hTU
      apply Subtype.ext
      exact hifT.2.symm.trans hieU.2
    · exact T.not_mem_left H current stage e f (by
        rw [← hifT.2]
        exact Finset.mem_erase.mpr ⟨hef, hieU.1⟩)
  · apply hTU
    apply Subtype.ext
    exact hifT.2.symm.trans hifU.2

theorem stageBlockFamily_pairwiseDisjoint
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (a : StageBlockUpperIndex H current stage) :
    (Set.univ : Set (Fin (Fintype.card
      (StageBlockLabel H current stage a)))).PairwiseDisjoint
        (stageBlockFamily H current stage a) := by
  intro i _hi k _hk hik
  apply disjoint_commonLinkRequiredCoordinates H current stage
  intro hlabels
  apply hik
  exact (Fintype.equivFin (StageBlockLabel H current stage a)).symm.injective
    (Subtype.ext (congrArg Subtype.val hlabels))

theorem card_filter_stageBlockFamily_eq_commonLinkBlockCount
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (a : StageBlockUpperIndex H current stage)
    (x : CompletionCoordinate H current stage → Bool) :
    (Finset.univ.filter fun i : Fin (Fintype.card
        (StageBlockLabel H current stage a)) =>
      allCoordinatesSelected x (stageBlockFamily H current stage a i)).card =
      commonLinkBlockCount H current stage
        (stageBlockLeft a) (stageBlockRight a) x := by
  let E := Fintype.equivFin (StageBlockLabel H current stage a)
  let P : Fin (Fintype.card (StageBlockLabel H current stage a)) → Prop :=
    fun i => allCoordinatesSelected x (stageBlockFamily H current stage a i)
  let Q : StageBlockLabel H current stage a → Prop :=
    fun T => allCoordinatesSelected x
      (commonLinkRequiredCoordinates H current stage
        (stageBlockLeft a) (stageBlockRight a) T.1)
  let EQ : {i // P i} ≃ {T // Q T} :=
    { toFun := fun i => ⟨E.symm i.1, by simpa [P, Q, stageBlockFamily, E] using i.2⟩
      invFun := fun T => ⟨E T.1, by simpa [P, Q, stageBlockFamily, E] using T.2⟩
      left_inv := fun i => by apply Subtype.ext; exact E.apply_symm_apply i.1
      right_inv := fun T => by apply Subtype.ext; exact E.symm_apply_apply T.1 }
  change (Finset.univ.filter P).card = (Finset.univ.filter Q).card
  rw [← Fintype.card_subtype P, ← Fintype.card_subtype Q]
  exact Fintype.card_congr EQ

theorem commonLinkRequiredCoordinates_card_le_two
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (e f : Finset V) (T : CommonLinkBlockLabel H current stage e f) :
    (commonLinkRequiredCoordinates H current stage e f T.1).card ≤ 2 := by
  calc
    (commonLinkRequiredCoordinates H current stage e f T.1).card ≤
        (Finset.univ : Finset Bool).card := by
      apply Finset.card_le_card_of_injOn
        (fun i => if CandidateRealizesRemainder H current stage e T.1 i
          then true else false)
      · intro i _hi
        exact Finset.mem_univ _
      · intro i hi k hk hik
        have hi' :
            (T.1 ∉ conflictLinkLayer current e (stage - 1) ∧
                CandidateRealizesRemainder H current stage e T.1 i) ∨
              (T.1 ∉ conflictLinkLayer current f (stage - 1) ∧
                CandidateRealizesRemainder H current stage f T.1 i) :=
          (Finset.mem_filter.mp hi).2
        have hk' :
            (T.1 ∉ conflictLinkLayer current e (stage - 1) ∧
                CandidateRealizesRemainder H current stage e T.1 k) ∨
              (T.1 ∉ conflictLinkLayer current f (stage - 1) ∧
                CandidateRealizesRemainder H current stage f T.1 k) :=
          (Finset.mem_filter.mp hk).2
        by_cases hie : CandidateRealizesRemainder H current stage e T.1 i
        · have hke : CandidateRealizesRemainder H current stage e T.1 k := by
            by_contra hkne
            simp [hie, hkne] at hik
          exact candidateRealizesRemainder_injective H current stage e T.1 hie hke
        · have hif : CandidateRealizesRemainder H current stage f T.1 i := by
            rcases hi' with h | h
            · exact (hie h.2).elim
            · exact h.2
          have hke : ¬CandidateRealizesRemainder H current stage e T.1 k := by
            intro hke
            simp [hie, hke] at hik
          have hkf : CandidateRealizesRemainder H current stage f T.1 k := by
            rcases hk' with h | h
            · exact (hke h.2).elim
            · exact h.2
          exact candidateRealizesRemainder_injective H current stage f T.1 hif hkf
    _ = 2 := by simp

theorem commonLinkRequiredCoordinates_nonempty
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (e f : Finset V) (T : CommonLinkBlockLabel H current stage e f) :
    (commonLinkRequiredCoordinates H current stage e f T.1).Nonempty := by
  by_cases heold : T.1 ∈ conflictLinkLayer current e (stage - 1)
  · have hfold : T.1 ∉ conflictLinkLayer current f (stage - 1) := by
      exact fun hf => T.2.2.2.2 ⟨heold, hf⟩
    obtain ⟨i, hi⟩ := T.2.2.2.1.resolve_left hfold
    refine ⟨i, ?_⟩
    simp only [commonLinkRequiredCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inr ⟨hfold, hi⟩
  · obtain ⟨i, hi⟩ := T.2.2.1.resolve_left heold
    refine ⟨i, ?_⟩
    simp only [commonLinkRequiredCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inl ⟨heold, hi⟩

theorem commonLinkIntersection_addCompletionLayer_le_blockCount
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hstage : 1 ≤ stage) (e f : Finset V)
    (x : CompletionCoordinate H current stage → Bool) :
    ((conflictLinkLayer
          (addCompletionLayer current
            (sampledCompletionLayer (completionCandidate H current stage) x))
          e (stage - 1) ∩
        conflictLinkLayer
          (addCompletionLayer current
            (sampledCompletionLayer (completionCandidate H current stage) x))
          f (stage - 1)).card) ≤
      ((conflictLinkLayer current e (stage - 1) ∩
        conflictLinkLayer current f (stage - 1)).card) +
        commonLinkBlockCount H current stage e f x := by
  let finalE := conflictLinkLayer
    (addCompletionLayer current
      (sampledCompletionLayer (completionCandidate H current stage) x))
    e (stage - 1)
  let finalF := conflictLinkLayer
    (addCompletionLayer current
      (sampledCompletionLayer (completionCandidate H current stage) x))
    f (stage - 1)
  let oldBoth := conflictLinkLayer current e (stage - 1) ∩
    conflictLinkLayer current f (stage - 1)
  let newlyCommon := (finalE ∩ finalF).filter fun T => T ∉ oldBoth
  let successful :=
    Finset.univ.filter fun T : CommonLinkBlockLabel H current stage e f =>
      allCoordinatesSelected x
        (commonLinkRequiredCoordinates H current stage e f T.1)
  have hcover : finalE ∩ finalF ⊆ oldBoth ∪ newlyCommon := by
    intro T hT
    by_cases hold : T ∈ oldBoth
    · exact Finset.mem_union_left _ hold
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hT, hold⟩)
  have hnewImage : newlyCommon ⊆ successful.image Subtype.val := by
    intro T hT
    have hTF : T ∈ finalE ∩ finalF := (Finset.mem_filter.mp hT).1
    have hnotOld : T ∉ oldBoth := (Finset.mem_filter.mp hT).2
    have heFinal : T ∈ finalE := (Finset.mem_inter.mp hTF).1
    have hfFinal : T ∈ finalF := (Finset.mem_inter.mp hTF).2
    have heAvail :=
      (mem_conflictLinkLayer_addCompletionLayer_sampled_iff
        H current stage hstage x e T).mp heFinal
    have hfAvail :=
      (mem_conflictLinkLayer_addCompletionLayer_sampled_iff
        H current stage hstage x f T).mp hfFinal
    have heAvail' :
        T ∈ conflictLinkLayer current e (stage - 1) ∨
          ∃ i, CandidateRealizesRemainder H current stage e T i := by
      rcases heAvail with h | ⟨i, _hxi, hi⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi⟩
    have hfAvail' :
        T ∈ conflictLinkLayer current f (stage - 1) ∨
          ∃ i, CandidateRealizesRemainder H current stage f T i := by
      rcases hfAvail with h | ⟨i, _hxi, hi⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi⟩
    have hTcard : T.card = stage - 1 :=
      (mem_conflictLinkLayer.mp heFinal).2
    have hnotBoth : ¬(T ∈ conflictLinkLayer current e (stage - 1) ∧
        T ∈ conflictLinkLayer current f (stage - 1)) := by
      simpa [oldBoth] using hnotOld
    let label : CommonLinkBlockLabel H current stage e f :=
      ⟨T, hTcard, heAvail', hfAvail', hnotBoth⟩
    have hselected : allCoordinatesSelected x
        (commonLinkRequiredCoordinates H current stage e f label.1) :=
      (allCoordinatesSelected_commonLinkRequired_iff
        H current stage hstage e f label x).mpr ⟨heFinal, hfFinal⟩
    apply Finset.mem_image.mpr
    exact ⟨label, Finset.mem_filter.mpr
      ⟨Finset.mem_univ label, hselected⟩, rfl⟩
  calc
    (finalE ∩ finalF).card ≤ (oldBoth ∪ newlyCommon).card :=
      Finset.card_le_card hcover
    _ ≤ oldBoth.card + newlyCommon.card := Finset.card_union_le _ _
    _ ≤ oldBoth.card + (successful.image Subtype.val).card := by
      exact Nat.add_le_add_left (Finset.card_le_card hnewImage) _
    _ = oldBoth.card + successful.card := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
    _ = (conflictLinkLayer current e (stage - 1) ∩
          conflictLinkLayer current f (stage - 1)).card +
          commonLinkBlockCount H current stage e f x := by
      rfl

/-- For a genuine conflict system, one-links are exactly singleton images
of two-conflict neighbours. -/
theorem conflictLinkLayer_one_eq_image_twoConflictNeighbors
    (H : Hypergraph V) (C : ConflictSystem V)
    (hC : IsConflictSystem H C) (e : Finset V) :
    conflictLinkLayer C e 1 =
      (twoConflictNeighbors H C e).image fun g => ({g} : Hypergraph V) := by
  ext T
  constructor
  · intro hT
    obtain ⟨⟨c, hcC, hec, hcerase⟩, hTcard⟩ :=
      mem_conflictLinkLayer.mp hT
    obtain ⟨g, rfl⟩ := Finset.card_eq_one.mp hTcard
    have hcg : g ∈ c := by
      have : g ∈ c.erase e := by simpa [hcerase]
      exact (Finset.mem_erase.mp this).2
    have hge : g ≠ e := by
      intro h
      subst g
      have : e ∈ c.erase e := by simpa [hcerase]
      simpa using this
    have hc2 : c.card = 2 := by
      have hcard := Finset.card_erase_add_one hec
      rw [hcerase] at hcard
      simp at hcard
      omega
    have hpair : {e, g} = c := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hec
        · exact hcg
      · rw [hc2]
        simp [Ne.symm hge]
    apply Finset.mem_image.mpr
    refine ⟨g, ?_, rfl⟩
    simp only [twoConflictNeighbors, Finset.mem_filter]
    refine ⟨hC c hcC hcg, hge, ?_⟩
    apply mem_conflictLayer.mpr
    rw [hpair]
    exact ⟨hcC, hc2⟩
  · intro hT
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hT
    have hg' := Finset.mem_filter.mp hg
    apply mem_conflictLinkLayer.mpr
    refine ⟨⟨{e, g}, (mem_conflictLayer.mp hg'.2.2).1, ?_, ?_⟩, by simp⟩
    · simp
    · simp [Ne.symm hg'.2.1]

theorem conditionC5Count_eq_commonOneLinks
    (H : Hypergraph V) (C : ConflictSystem V)
    (hC : IsConflictSystem H C) (e f : Finset V) :
    conditionC5Count H C e f =
      (conflictLinkLayer C e 1 ∩ conflictLinkLayer C f 1).card := by
  rw [conditionC5Count,
    conflictLinkLayer_one_eq_image_twoConflictNeighbors H C hC e,
    conflictLinkLayer_one_eq_image_twoConflictNeighbors H C hC f,
    ← Finset.image_inter _ _ (fun _ _ h => Finset.singleton_injective h),
    Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_injective h)]

theorem conditionC5Count_addCompletionLayer_le_blockCount
    (H : Hypergraph V) (current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (e f : Finset V)
    (x : CompletionCoordinate H current 2 → Bool) :
    conditionC5Count H
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current 2) x))
        e f ≤
      conditionC5Count H current e f +
        commonLinkBlockCount H current 2 e f x := by
  let A := sampledCompletionLayer (completionCandidate H current 2) x
  have hA : IsConflictSystem H A := by
    intro c hc
    exact completionCandidates_isConflictSystem H current 2 c
      (sampledSourceCompletionLayer_subset_candidates H current 2 x hc)
  have hfinal : IsConflictSystem H (addCompletionLayer current A) :=
    addCompletionLayer_isConflictSystem hcurrent hA
  rw [conditionC5Count_eq_commonOneLinks H _ hfinal,
    conditionC5Count_eq_commonOneLinks H current hcurrent]
  simpa [A] using
    (commonLinkIntersection_addCompletionLayer_le_blockCount
      H current 2 (by norm_num) e f x)

/-- A selected two-conflict contributes to the C4 observable rooted at
`(e,v)` exactly when its other host edge contains `v`. -/
def CandidateCreatesC4 (e : Finset V) (v : V) (A : Hypergraph V) : Prop :=
  e ∈ A ∧ ∃ g ∈ A, g ≠ e ∧ v ∈ g

def stageLinearUpperActive (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (a : StageLinearUpperIndex H stage)
    (i : CompletionCoordinate H current stage) : Prop :=
  match a with
  | Sum.inl q => q.1 ⊆ completionCandidate H current stage i
  | Sum.inr c4 => CandidateCreatesC4 c4.edge c4.vertex
      (completionCandidate H current stage i)

theorem conditionC4Count_addCompletionLayer_le_selected
    (H : Hypergraph V) (current : ConflictSystem V)
    (e : Finset V) (v : V)
    (x : CompletionCoordinate H current 2 → Bool) :
    conditionC4Count H
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current 2) x))
        e v ≤
      conditionC4Count H current e v +
        ((sampledCompletionLayer (completionCandidate H current 2) x).filter
          fun A => CandidateCreatesC4 e v A).card := by
  let A := sampledCompletionLayer (completionCandidate H current 2) x
  let newNeighbors := H.filter fun g => g ≠ e ∧ {e, g} ∈ A
  have hu : IsUniform A 2 :=
    sampledSourceCompletionLayer_uniform H current 2 x
  have hneighbors :
      twoConflictNeighbors H (addCompletionLayer current A) e =
        twoConflictNeighbors H current e ∪ newNeighbors := by
    ext g
    simp only [twoConflictNeighbors, Finset.mem_filter, Finset.mem_union]
    rw [show conflictLayer (addCompletionLayer current A) 2 =
        conflictLayer current 2 ∪ A from
      conflictLayer_addCompletionLayer_eq hu]
    simp only [newNeighbors, Finset.mem_filter, Finset.mem_union]
    aesop
  have hnew : (newNeighbors.filter fun g => v ∈ g).card ≤
      (A.filter fun B => CandidateCreatesC4 e v B).card := by
    apply Finset.card_le_card_of_injOn (fun g => ({e, g} : Hypergraph V))
    · intro g hg
      have hg' := Finset.mem_filter.mp hg
      have hgnew := Finset.mem_filter.mp hg'.1
      apply Finset.mem_filter.mpr
      refine ⟨hgnew.2.2, ?_⟩
      refine ⟨by simp, g, by simp, hgnew.2.1, hg'.2⟩
    · intro g hg h hh hpair
      have hgne : g ≠ e :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).2.1
      have hhne : h ≠ e :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).2.1
      have herase := congrArg (Finset.erase · e) hpair
      simpa [Ne.symm hgne, Ne.symm hhne] using herase
  rw [conditionC4Count, hneighbors, Finset.filter_union]
  calc
    (((twoConflictNeighbors H current e).filter fun g => v ∈ g) ∪
        (newNeighbors.filter fun g => v ∈ g)).card ≤
      ((twoConflictNeighbors H current e).filter fun g => v ∈ g).card +
        (newNeighbors.filter fun g => v ∈ g).card :=
      Finset.card_union_le _ _
    _ ≤ ((twoConflictNeighbors H current e).filter fun g => v ∈ g).card +
        (A.filter fun B => CandidateCreatesC4 e v B).card :=
      Nat.add_le_add_left hnew _
    _ = conditionC4Count H current e v +
        ((sampledCompletionLayer (completionCandidate H current 2) x).filter
          fun B => CandidateCreatesC4 e v B).card := by
      rfl

/-- The simultaneous upper bounds delivered by the ordinary Bernoulli
Chernoff family. -/
def LinearUpperBounds (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (x : CompletionCoordinate H current stage → Bool)
    (threshold : StageLinearUpperIndex H stage → ℝ) : Prop :=
  ∀ a, ChernoffFinite.bitCount (stageLinearUpperActive H current stage a) x <
    2 * threshold a

/-- The simultaneous upper bounds delivered by the disjoint-block
Bernoulli Chernoff family. -/
def BlockUpperBounds (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (x : CompletionCoordinate H current stage → Bool)
    (threshold : StageBlockUpperIndex H current stage → ℝ) : Prop :=
  ∀ a, (commonLinkBlockCount H current stage
      (stageBlockLeft a) (stageBlockRight a) x : ℝ) < 2 * threshold a

def PropertyIIRoom (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ)
    (threshold : StageLinearUpperIndex H stage → ℝ) : Prop :=
  ∀ root : StageCodegreeIndex V stage,
    (codegree (conflictLayer current stage) root.1 : ℝ) +
        2 * threshold (Sum.inl root) ≤
      Real.rpow d ((stage : ℝ) - (root.1.card : ℝ) - eps / 4)

def PropertyIIIRoom (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ)
    (threshold : StageLinearUpperIndex H stage → ℝ) : Prop :=
  ∀ (hs : stage = 2) (e : Finset V) (he : e ∈ H) (v : V),
    (conditionC4Count H current e v : ℝ) +
        2 * threshold (Sum.inr (StageC4Index.mk e he v hs)) ≤
      Real.rpow d (1 - eps / 4)

def PropertyIVRoom (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ)
    (threshold : StageBlockUpperIndex H current stage → ℝ) : Prop :=
  ∀ (hs : stage = 2) (e : Finset V) (he : e ∈ H)
    (f : Finset V) (hf : f ∈ H) (hdisj : Disjoint e f),
    let pair : HostEdgePair H := HostEdgePair.mk e he f hf hdisj
    (conditionC5Count H current e f : ℝ) +
        2 * threshold (Sum.inl (StageC5BlockIndex.mk pair hs)) ≤
      Real.rpow d (1 - eps / 4)

def PropertyVRoom (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ)
    (threshold : StageBlockUpperIndex H current stage → ℝ) : Prop :=
  ∀ (e : Finset V) (he : e ∈ H)
    (f : Finset V) (hf : f ∈ H) (hdisj : Disjoint e f)
    (hnot : {e, f} ∉ conflictLayer current 2),
    let pair : HostEdgePair H := HostEdgePair.mk e he f hf hdisj
    ((conflictLinkLayer current e (stage - 1) ∩
        conflictLinkLayer current f (stage - 1)).card : ℝ) +
        2 * threshold (Sum.inr (StageCommonBlockIndex.mk pair hnot)) ≤
      Real.rpow d ((stage - 1 : ℕ) - eps / 4)

def StagePropertyII (H : Hypergraph V) (next : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ) : Prop :=
  ∀ q, 2 ≤ q → q < stage → ∀ root : Hypergraph V, root.card = q →
    (codegree (conflictLayer next stage) root : ℝ) ≤
      Real.rpow d ((stage : ℝ) - (q : ℝ) - eps / 4)

def StagePropertyIII (H : Hypergraph V) (next : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ) : Prop :=
  stage = 2 → ∀ e ∈ H, ∀ v,
    (conditionC4Count H next e v : ℝ) ≤ Real.rpow d (1 - eps / 4)

def StagePropertyIV (H : Hypergraph V) (next : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ) : Prop :=
  stage = 2 → ∀ e ∈ H, ∀ f ∈ H, Disjoint e f →
    (conditionC5Count H next e f : ℝ) ≤ Real.rpow d (1 - eps / 4)

def StagePropertyV (H : Hypergraph V) (next : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, Disjoint e f →
    {e, f} ∉ conflictLayer next 2 →
    ((conflictLinkLayer next e (stage - 1) ∩
      conflictLinkLayer next f (stage - 1)).card : ℝ) ≤
      Real.rpow d ((stage - 1 : ℕ) - eps / 4)

/-- The bit count for a property-(II) index is the exact sampled codegree
increment at that root. -/
theorem bitCount_stageLinearUpperActive_codegree
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (root : Hypergraph V) (hroot : 2 ≤ root.card ∧ root.card < stage)
    (x : CompletionCoordinate H current stage → Bool) :
    ChernoffFinite.bitCount
        (stageLinearUpperActive H current stage
          (Sum.inl (⟨root, hroot⟩ : StageCodegreeIndex V stage))) x =
      sampledCount (completionCandidate H current stage)
        (fun B => root ⊆ B) x := rfl

/-- The bit count for a property-(III) index is the exact number of selected
completion candidates which create the indicated C4 witness. -/
theorem bitCount_stageLinearUpperActive_C4
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (e : Finset V) (he : e ∈ H) (v : V) (hs : stage = 2)
    (x : CompletionCoordinate H current stage → Bool) :
    ChernoffFinite.bitCount
        (stageLinearUpperActive H current stage
          (Sum.inr (StageC4Index.mk e he v hs))) x =
      sampledCount (completionCandidate H current stage)
        (fun B => CandidateCreatesC4 e v B) x := rfl

/-- A property-(II) sampled increment is bounded by its avoided linear
observable. -/
theorem propertyIISampledCount_le
    (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ)
    (x : CompletionCoordinate H current stage → Bool)
    (linearThreshold : StageLinearUpperIndex H stage → ℝ)
    (hlinear : LinearUpperBounds H current stage x linearThreshold)
    (root : StageCodegreeIndex V stage) :
    sampledCount (completionCandidate H current stage)
        (fun B => root.1 ⊆ B) x ≤
      2 * linearThreshold (Sum.inl root) := by
  rw [← bitCount_stageLinearUpperActive_codegree
    H current stage root.1 root.2 x]
  exact (hlinear (Sum.inl root)).le

theorem codegree_addCompletionLayer_sampled_le_of_count
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (x : CompletionCoordinate H current stage → Bool)
    (root : Hypergraph V) (bound target : ℝ)
    (hcount : sampledCount (completionCandidate H current stage)
      (fun B => root ⊆ B) x ≤ bound)
    (hroom : (codegree (conflictLayer current stage) root : ℝ) + bound ≤ target) :
    (codegree (conflictLayer
      (addCompletionLayer current
        (sampledCompletionLayer (completionCandidate H current stage) x))
      stage) root : ℝ) ≤ target := by
  rw [codegree_addCompletionLayer_sampled_eq H current stage x root]
  calc
    (codegree (conflictLayer current stage) root : ℝ) +
        sampledCount (completionCandidate H current stage)
          (fun B => root ⊆ B) x ≤
        (codegree (conflictLayer current stage) root : ℝ) + bound :=
      add_le_add_right hcount (codegree (conflictLayer current stage) root : ℝ)
    _ ≤ target := hroom

/-- Property (II) decoded from the linear upper-observable bounds. -/
theorem stagePropertyII_of_linearBounds
    (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ)
    (x : CompletionCoordinate H current stage → Bool)
    (linearThreshold : StageLinearUpperIndex H stage → ℝ)
    (hlinear : LinearUpperBounds H current stage x linearThreshold)
    (hroom : PropertyIIRoom H current d eps stage linearThreshold) :
    StagePropertyII H
      (addCompletionLayer current
        (sampledCompletionLayer (completionCandidate H current stage) x))
      d eps stage := by
  rw [StagePropertyII]
  intro q hq2 hqstage root hroot
  let indexed : StageCodegreeIndex V stage :=
    ⟨root, by constructor <;> omega⟩
  have hcount := propertyIISampledCount_le H current stage x
    linearThreshold hlinear indexed
  have hr := hroom indexed
  apply codegree_addCompletionLayer_sampled_le_of_count H current stage x root
    (2 * linearThreshold (Sum.inl indexed))
  · simpa [indexed] using hcount
  · simpa [indexed, hroot] using hr

theorem conditionC4Count_addCompletionLayer_real_le_selected
    (H : Hypergraph V) (current : ConflictSystem V)
    (e : Finset V) (v : V)
    (x : CompletionCoordinate H current 2 → Bool) :
    (conditionC4Count H
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current 2) x))
        e v : ℝ) ≤
      (conditionC4Count H current e v : ℝ) +
        (((sampledCompletionLayer
          (completionCandidate H current 2) x).filter
            fun B => CandidateCreatesC4 e v B).card : ℝ) := by
  exact_mod_cast conditionC4Count_addCompletionLayer_le_selected
    H current e v x

theorem propertyIIISampledCount_le
    (H : Hypergraph V) (current : ConflictSystem V)
    (x : CompletionCoordinate H current 2 → Bool)
    (linearThreshold : StageLinearUpperIndex H 2 → ℝ)
    (hlinear : LinearUpperBounds H current 2 x linearThreshold)
    (e : Finset V) (he : e ∈ H) (v : V) :
    (((sampledCompletionLayer
      (completionCandidate H current 2) x).filter
        fun B => CandidateCreatesC4 e v B).card : ℝ) ≤
      2 * linearThreshold
        (Sum.inr (StageC4Index.mk e he v rfl)) := by
  have hbit := hlinear (Sum.inr (StageC4Index.mk e he v rfl))
  rw [bitCount_stageLinearUpperActive_C4 H current 2 e he v rfl x,
    sampledCount_eq_filter_card (completionCandidate H current 2)
      (completionCandidate_injective H current 2)
      (fun B => CandidateCreatesC4 e v B) x] at hbit
  exact hbit.le

theorem conditionC4Count_addCompletionLayer_le_of_count
    (H : Hypergraph V) (current : ConflictSystem V)
    (e : Finset V) (v : V)
    (x : CompletionCoordinate H current 2 → Bool)
    (bound target : ℝ)
    (hcount : (((sampledCompletionLayer
      (completionCandidate H current 2) x).filter
        fun B => CandidateCreatesC4 e v B).card : ℝ) ≤ bound)
    (hroom : (conditionC4Count H current e v : ℝ) + bound ≤ target) :
    (conditionC4Count H
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current 2) x))
        e v : ℝ) ≤ target := by
  calc
    (conditionC4Count H
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current 2) x))
        e v : ℝ) ≤
        (conditionC4Count H current e v : ℝ) +
          (((sampledCompletionLayer
            (completionCandidate H current 2) x).filter
              fun B => CandidateCreatesC4 e v B).card : ℝ) :=
      conditionC4Count_addCompletionLayer_real_le_selected H current e v x
    _ ≤ (conditionC4Count H current e v : ℝ) + bound :=
      add_le_add_right hcount (conditionC4Count H current e v : ℝ)
    _ ≤ target := hroom

theorem stagePropertyIII_two_of_linearBounds
    (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ)
    (x : CompletionCoordinate H current 2 → Bool)
    (linearThreshold : StageLinearUpperIndex H 2 → ℝ)
    (hlinear : LinearUpperBounds H current 2 x linearThreshold)
    (hroom : PropertyIIIRoom H current d eps 2 linearThreshold) :
    StagePropertyIII H
      (addCompletionLayer current
        (sampledCompletionLayer (completionCandidate H current 2) x))
      d eps 2 := by
  rw [StagePropertyIII]
  intro _ e he v
  let a : StageLinearUpperIndex H 2 :=
    Sum.inr (StageC4Index.mk e he v rfl)
  have hcount := propertyIIISampledCount_le H current x
    linearThreshold hlinear e he v
  apply conditionC4Count_addCompletionLayer_le_of_count H current e v x
    (2 * linearThreshold a)
  · simpa [a] using hcount
  · simpa [a] using hroom rfl e he v

/-- Property (III) decoded from its stage-two linear observables. -/
theorem stagePropertyIII_of_linearBounds
    (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ)
    (x : CompletionCoordinate H current stage → Bool)
    (linearThreshold : StageLinearUpperIndex H stage → ℝ)
    (hlinear : LinearUpperBounds H current stage x linearThreshold)
    (hroom : PropertyIIIRoom H current d eps stage linearThreshold) :
    StagePropertyIII H
      (addCompletionLayer current
        (sampledCompletionLayer (completionCandidate H current stage) x))
      d eps stage := by
  rw [StagePropertyIII]
  intro hs
  subst stage
  have htwo := stagePropertyIII_two_of_linearBounds H current d eps x
    linearThreshold hlinear hroom
  rw [StagePropertyIII] at htwo
  exact htwo rfl

theorem conditionC5Count_addCompletionLayer_real_le_blockCount
    (H : Hypergraph V) (current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (e f : Finset V)
    (x : CompletionCoordinate H current 2 → Bool) :
    (conditionC5Count H
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current 2) x))
        e f : ℝ) ≤
      (conditionC5Count H current e f : ℝ) +
        (commonLinkBlockCount H current 2 e f x : ℝ) := by
  exact_mod_cast conditionC5Count_addCompletionLayer_le_blockCount
    H current hcurrent e f x

theorem propertyIVBlockCount_le
    (H : Hypergraph V) (current : ConflictSystem V)
    (x : CompletionCoordinate H current 2 → Bool)
    (blockThreshold : StageBlockUpperIndex H current 2 → ℝ)
    (hblock : BlockUpperBounds H current 2 x blockThreshold)
    (pair : HostEdgePair H) :
    (commonLinkBlockCount H current 2 pair.left pair.right x : ℝ) ≤
      2 * blockThreshold
        (Sum.inl (StageC5BlockIndex.mk pair rfl)) := by
  have h := hblock (Sum.inl (StageC5BlockIndex.mk pair rfl))
  simpa [stageBlockLeft, stageBlockRight] using h.le

theorem stagePropertyIV_two_of_blockBounds
    (H : Hypergraph V) (current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (d eps : ℝ)
    (x : CompletionCoordinate H current 2 → Bool)
    (blockThreshold : StageBlockUpperIndex H current 2 → ℝ)
    (hblock : BlockUpperBounds H current 2 x blockThreshold)
    (hroom : PropertyIVRoom H current d eps 2 blockThreshold) :
    StagePropertyIV H
      (addCompletionLayer current
        (sampledCompletionLayer (completionCandidate H current 2) x))
      d eps 2 := by
  rw [StagePropertyIV]
  intro _ e he f hf hdisj
  let pair : HostEdgePair H := HostEdgePair.mk e he f hf hdisj
  let a : StageBlockUpperIndex H current 2 :=
    Sum.inl (StageC5BlockIndex.mk pair rfl)
  have hcount := propertyIVBlockCount_le H current x
    blockThreshold hblock pair
  calc
    (conditionC5Count H
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current 2) x)) e f : ℝ) ≤
        (conditionC5Count H current e f : ℝ) +
          (commonLinkBlockCount H current 2 e f x : ℝ) :=
      conditionC5Count_addCompletionLayer_real_le_blockCount
        H current hcurrent e f x
    _ ≤ (conditionC5Count H current e f : ℝ) +
        2 * blockThreshold a := by
      simpa [a, pair] using add_le_add_left hcount
        (conditionC5Count H current e f : ℝ)
    _ ≤ Real.rpow d (1 - eps / 4) := by
      simpa [a, pair] using hroom rfl e he f hf hdisj

/-- Property (IV) decoded from the exact stage-two block observables. -/
theorem stagePropertyIV_of_blockBounds
    (H : Hypergraph V) (current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (d eps : ℝ) (stage : ℕ)
    (x : CompletionCoordinate H current stage → Bool)
    (blockThreshold : StageBlockUpperIndex H current stage → ℝ)
    (hblock : BlockUpperBounds H current stage x blockThreshold)
    (hroom : PropertyIVRoom H current d eps stage blockThreshold) :
    StagePropertyIV H
      (addCompletionLayer current
        (sampledCompletionLayer (completionCandidate H current stage) x))
      d eps stage := by
  rw [StagePropertyIV]
  intro hs
  subst stage
  have htwo := stagePropertyIV_two_of_blockBounds H current hcurrent d eps x
    blockThreshold hblock hroom
  rw [StagePropertyIV] at htwo
  exact htwo rfl

theorem conflictLayer_two_subset_addCompletionLayer_sampled
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hstage2 : 2 ≤ stage)
    (x : CompletionCoordinate H current stage → Bool) :
    conflictLayer current 2 ⊆
      conflictLayer
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x)) 2 := by
  have hu := sampledSourceCompletionLayer_uniform H current stage x
  by_cases hs : stage = 2
  · subst stage
    rw [conflictLayer_addCompletionLayer_eq hu]
    exact Finset.subset_union_left
  · have hlt : 2 < stage := by omega
    rw [conflictLayer_addCompletionLayer_of_lt hu hlt]

/-- Property (V) decoded from its exact common-link block observables. -/
theorem commonLinkIntersection_addCompletionLayer_real_le_blockCount
    (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (hstage : 1 ≤ stage) (e f : Finset V)
    (x : CompletionCoordinate H current stage → Bool) :
    (((conflictLinkLayer
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        e (stage - 1)) ∩
      conflictLinkLayer
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        f (stage - 1)).card : ℝ) ≤
      (((conflictLinkLayer current e (stage - 1)) ∩
        conflictLinkLayer current f (stage - 1)).card : ℝ) +
        (commonLinkBlockCount H current stage e f x : ℝ) := by
  exact_mod_cast commonLinkIntersection_addCompletionLayer_le_blockCount
    H current stage hstage e f x

theorem propertyVBlockCount_le
    (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (x : CompletionCoordinate H current stage → Bool)
    (blockThreshold : StageBlockUpperIndex H current stage → ℝ)
    (hblock : BlockUpperBounds H current stage x blockThreshold)
    (pair : HostEdgePair H)
    (hnot : {pair.left, pair.right} ∉ conflictLayer current 2) :
    (commonLinkBlockCount H current stage pair.left pair.right x : ℝ) ≤
      2 * blockThreshold
        (Sum.inr (StageCommonBlockIndex.mk pair hnot)) := by
  have h := hblock (Sum.inr (StageCommonBlockIndex.mk pair hnot))
  simpa [stageBlockLeft, stageBlockRight] using h.le

theorem commonLinkIntersection_addCompletionLayer_le_of_count
    (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (hstage : 1 ≤ stage) (e f : Finset V)
    (x : CompletionCoordinate H current stage → Bool)
    (bound target : ℝ)
    (hcount : (commonLinkBlockCount H current stage e f x : ℝ) ≤ bound)
    (hroom :
      (((conflictLinkLayer current e (stage - 1)) ∩
        conflictLinkLayer current f (stage - 1)).card : ℝ) + bound ≤ target) :
    (((conflictLinkLayer
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        e (stage - 1)) ∩
      conflictLinkLayer
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        f (stage - 1)).card : ℝ) ≤ target := by
  calc
    (((conflictLinkLayer
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        e (stage - 1)) ∩
      conflictLinkLayer
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        f (stage - 1)).card : ℝ) ≤
        (((conflictLinkLayer current e (stage - 1)) ∩
          conflictLinkLayer current f (stage - 1)).card : ℝ) +
          (commonLinkBlockCount H current stage e f x : ℝ) :=
      commonLinkIntersection_addCompletionLayer_real_le_blockCount
        H current stage hstage e f x
    _ ≤ (((conflictLinkLayer current e (stage - 1)) ∩
          conflictLinkLayer current f (stage - 1)).card : ℝ) + bound :=
      add_le_add_right hcount
        (((conflictLinkLayer current e (stage - 1)) ∩
          conflictLinkLayer current f (stage - 1)).card : ℝ)
    _ ≤ target := hroom

theorem stagePropertyVAtPair_of_blockBounds
    (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ) (hstage2 : 2 ≤ stage)
    (x : CompletionCoordinate H current stage → Bool)
    (blockThreshold : StageBlockUpperIndex H current stage → ℝ)
    (hblock : BlockUpperBounds H current stage x blockThreshold)
    (hroom : PropertyVRoom H current d eps stage blockThreshold)
    (pair : HostEdgePair H)
    (hnot : {pair.left, pair.right} ∉ conflictLayer current 2) :
    (((conflictLinkLayer
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        pair.left (stage - 1)) ∩
      conflictLinkLayer
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        pair.right (stage - 1)).card : ℝ) ≤
      Real.rpow d ((stage - 1 : ℕ) - eps / 4) := by
  let a : StageBlockUpperIndex H current stage :=
    Sum.inr (StageCommonBlockIndex.mk pair hnot)
  have hcount := propertyVBlockCount_le H current stage x
    blockThreshold hblock pair hnot
  apply commonLinkIntersection_addCompletionLayer_le_of_count H current stage
    (by omega) pair.left pair.right x (2 * blockThreshold a)
  · simpa [a] using hcount
  · simpa [a] using hroom pair.left pair.left_mem pair.right
      pair.right_mem pair.disjoint hnot

theorem stagePropertyV_of_blockBounds
    (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ) (hstage2 : 2 ≤ stage)
    (x : CompletionCoordinate H current stage → Bool)
    (blockThreshold : StageBlockUpperIndex H current stage → ℝ)
    (hblock : BlockUpperBounds H current stage x blockThreshold)
    (hroom : PropertyVRoom H current d eps stage blockThreshold) :
    StagePropertyV H
      (addCompletionLayer current
        (sampledCompletionLayer (completionCandidate H current stage) x))
      d eps stage := by
  rw [StagePropertyV]
  intro e he f hf hdisj hnotFinal
  have hnotCurrent : {e, f} ∉ conflictLayer current 2 := fun h =>
    hnotFinal (conflictLayer_two_subset_addCompletionLayer_sampled
      H current stage hstage2 x h)
  let pair : HostEdgePair H := HostEdgePair.mk e he f hf hdisj
  simpa [pair] using stagePropertyVAtPair_of_blockBounds H current d eps
    stage hstage2 x blockThreshold hblock hroom pair hnotCurrent

/-- The deterministic specialization consumed after the linear and block
Chernoff families have both been avoided. -/
theorem hasStagePropertiesIV_of_observableBounds
    (H : Hypergraph V) (base current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (d eps : ℝ) (stage : ℕ) (hstage2 : 2 ≤ stage) (hstage4 : stage ≤ 4)
    (x : CompletionCoordinate H current stage → Bool)
    (linearThreshold : StageLinearUpperIndex H stage → ℝ)
    (blockThreshold : StageBlockUpperIndex H current stage → ℝ)
    (hdegree : ∀ e ∈ H,
      InRelativeInterval
        (degree (conflictLayer
          (addCompletionLayer current
            (sampledCompletionLayer (completionCandidate H current stage) x))
          stage) e : ℝ)
        (completionTarget d eps (layerMaxDegree H base stage : ℝ) stage)
        (Real.rpow d (-eps)))
    (hlinear : LinearUpperBounds H current stage x linearThreshold)
    (hblock : BlockUpperBounds H current stage x blockThreshold)
    (hII : PropertyIIRoom H current d eps stage linearThreshold)
    (hIII : PropertyIIIRoom H current d eps stage linearThreshold)
    (hIV : PropertyIVRoom H current d eps stage blockThreshold)
    (hV : PropertyVRoom H current d eps stage blockThreshold) :
    HasStagePropertiesIV H base
      (addCompletionLayer current
        (sampledCompletionLayer (completionCandidate H current stage) x))
      d eps stage := by
  refine ⟨hstage2, hstage4, hdegree, ?_, ?_, ?_, ?_⟩
  · exact stagePropertyII_of_linearBounds H current d eps stage x
      linearThreshold hlinear hII
  · exact stagePropertyIII_of_linearBounds H current d eps stage x
      linearThreshold hlinear hIII
  · exact stagePropertyIV_of_blockBounds H current hcurrent d eps stage x
      blockThreshold hblock hIV
  · exact stagePropertyV_of_blockBounds H current d eps stage hstage2 x
      blockThreshold hblock hV

end UpperObservables

/-! ### Active weighted tests are defined after the stage extractor. -/

/-- One source-weighted completion stage, including the literal
McDiarmid control of every supplied test weight.  The degree and local
count observables are exposed as finite Chernoff families; `hdecode` is the
deterministic identification of those observables with properties (I)--(V).
Property (VI) is not part of that interface: it is proved here from the
compiled bounded-difference theorem and the exact incidence sensitivity
`testExtension`. -/
theorem exists_regularizationStage
    {ιrel ιupper ιtest : Type*}
    [Fintype ιrel] [Fintype ιupper] [Fintype ιtest]
    (H : Hypergraph V) (base current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ) (target : ℝ)
    (activeRel : ιrel →
      Fin (Fintype.card (CompletionIndex H current stage)) → Prop)
    (delta : ιrel → ℝ)
    (activeUpper : ιupper →
      Fin (Fintype.card (CompletionIndex H current stage)) → Prop)
    (threshold : ιupper → ℝ)
    (testJ : ιtest → ℕ) (w : ιtest → TestWeight V)
    (gap killLimit : ιtest → ℝ)
    (hp : ∀ i, sourceCompletionBiasAtTarget H current stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hdelta0 : ∀ a, 0 ≤ delta a) (hdelta1 : ∀ a, delta a ≤ 1)
    (hthreshold0 : ∀ a, 0 ≤ threshold a)
    (hupperMean : ∀ a,
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (activeUpper a) ≤ threshold a)
    (hw : ∀ a S, 0 ≤ w a S)
    (hfreeZero : ∀ a S, S ∈ H.powersetCard (testJ a) →
      (∃ c ∈ current, c ⊆ S) → w a S = 0)
    (hgap : ∀ a, 0 ≤ gap a)
    (hkillMean : ∀ a,
      McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight
            (sourceCompletionBiasAtTarget H current stage target))
          (sampledKilledWeight H (testJ a) (w a)
            (completionCandidate H current stage)) + gap a ≤ killLimit a)
    (hfail :
      (∑ a : ιrel,
          2 * Real.exp (-(delta a ^ 2 *
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (activeRel a)) / 3)) +
        (∑ a : ιupper, Real.exp (-threshold a / 3)) +
        (∑ a : ιtest,
          Real.exp (-2 * gap a ^ 2 /
            ∑ i, (testExtension (w a) H (testJ a)
              (completionCandidate H current stage i)) ^ 2)) < 1)
    (hdecode : ∀ x,
      (∀ a,
        |ChernoffFinite.bitCount (activeRel a) x -
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (activeRel a)| <
          delta a * ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H current stage target)
            (activeRel a)) →
      (∀ a, ChernoffFinite.bitCount (activeUpper a) x <
        2 * threshold a) →
      HasStagePropertiesIV H base
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        d eps stage) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H current stage ∧
      HasStagePropertiesIV H base (addCompletionLayer current A)
        d eps stage ∧
      ∀ a, killedWeight H (addCompletionLayer current A)
        (testJ a) (w a) < killLimit a := by
  let p := sourceCompletionBiasAtTarget H current stage target
  let candidate := completionCandidate H current stage
  let f : ιtest →
      (Fin (Fintype.card (CompletionIndex H current stage)) → Bool) → ℝ :=
    fun a => sampledKilledWeight H (testJ a) (w a) candidate
  let b : ιtest →
      Fin (Fintype.card (CompletionIndex H current stage)) → ℝ :=
    fun a i => testExtension (w a) H (testJ a) (candidate i)
  have hb : ∀ a i, 0 ≤ b a i := by
    intro a i
    apply Finset.sum_nonneg
    intro S _hS
    exact hw a S
  have hbd : ∀ a i
      (x y : Fin (Fintype.card (CompletionIndex H current stage)) → Bool),
      (∀ q, q ≠ i → x q = y q) → |f a x - f a y| ≤ b a i := by
    intro a i x y hxy
    exact sampledKilledWeight_boundedDiff H (testJ a) (w a) candidate
      (hw a) i x y hxy
  obtain ⟨x, hrel, hupper, htest⟩ :=
    exists_bernoulli_chernoff_mcdiarmid p activeRel delta activeUpper
      threshold f b gap hp hdelta0 hdelta1 hthreshold0 hupperMean hb hbd
      hgap (by simpa [p, b] using hfail)
  let A := sampledCompletionLayer candidate x
  refine ⟨A, ?_, hdecode x hrel hupper, ?_⟩
  · exact sampledSourceCompletionLayer_subset_candidates H current stage x
  · intro a
    rw [killedWeight_addCompletionLayer_eq_sampledKilledWeight H current
      (testJ a) (w a) candidate x (hw a) (hfreeZero a)]
    exact (htest a).trans_le (by simpa [p, f] using hkillMean a)

/-- One source-weighted completion stage with relative, linear upper,
disjoint-block upper, and destroyed-test observables. -/
theorem exists_regularizationStageWithBlocks
    {ιrel ιupper ιblock ιtest : Type*}
    [Fintype ιrel] [Fintype ιupper] [Fintype ιblock] [Fintype ιtest]
    (H : Hypergraph V) (base current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ) (target : ℝ)
    (activeRel : ιrel →
      Fin (Fintype.card (CompletionIndex H current stage)) → Prop)
    (delta : ιrel → ℝ)
    (activeUpper : ιupper →
      Fin (Fintype.card (CompletionIndex H current stage)) → Prop)
    (threshold : ιupper → ℝ)
    (blockSize : ιblock → ℕ)
    (blocks : ∀ a, Fin (blockSize a) →
      Finset (Fin (Fintype.card (CompletionIndex H current stage))))
    (blockThreshold : ιblock → ℝ)
    (testJ : ιtest → ℕ) (w : ιtest → TestWeight V)
    (gap killLimit : ιtest → ℝ)
    (hp : ∀ i, sourceCompletionBiasAtTarget H current stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hdelta0 : ∀ a, 0 ≤ delta a) (hdelta1 : ∀ a, delta a ≤ 1)
    (hthreshold0 : ∀ a, 0 ≤ threshold a)
    (hupperMean : ∀ a,
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (activeUpper a) ≤ threshold a)
    (hblockDisj : ∀ a,
      (Set.univ : Set (Fin (blockSize a))).PairwiseDisjoint (blocks a))
    (hblockThreshold0 : ∀ a, 0 ≤ blockThreshold a)
    (hblockMean : ∀ a,
      BlockChernoff.blockMean
          (sourceCompletionBiasAtTarget H current stage target)
          (blocks a) ≤ blockThreshold a)
    (hw : ∀ a S, 0 ≤ w a S)
    (hfreeZero : ∀ a S, S ∈ H.powersetCard (testJ a) →
      (∃ c ∈ current, c ⊆ S) → w a S = 0)
    (hgap : ∀ a, 0 ≤ gap a)
    (hkillMean : ∀ a,
      McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight
            (sourceCompletionBiasAtTarget H current stage target))
          (sampledKilledWeight H (testJ a) (w a)
            (completionCandidate H current stage)) + gap a ≤ killLimit a)
    (hfail :
      (∑ a : ιrel,
          2 * Real.exp (-(delta a ^ 2 *
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (activeRel a)) / 3)) +
        (∑ a : ιupper, Real.exp (-threshold a / 3)) +
        (∑ a : ιblock, Real.exp (-blockThreshold a / 3)) +
        (∑ a : ιtest,
          Real.exp (-2 * gap a ^ 2 /
            ∑ i, (testExtension (w a) H (testJ a)
              (completionCandidate H current stage i)) ^ 2)) < 1)
    (hdecode : ∀ x,
      (∀ a,
        |ChernoffFinite.bitCount (activeRel a) x -
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (activeRel a)| <
          delta a * ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H current stage target)
            (activeRel a)) →
      (∀ a, ChernoffFinite.bitCount (activeUpper a) x <
        2 * threshold a) →
      (∀ a, BlockChernoff.blockCount (blocks a) x <
        2 * blockThreshold a) →
      HasStagePropertiesIV H base
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        d eps stage) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H current stage ∧
      HasStagePropertiesIV H base (addCompletionLayer current A)
        d eps stage ∧
      ∀ a, killedWeight H (addCompletionLayer current A)
        (testJ a) (w a) < killLimit a := by
  let p := sourceCompletionBiasAtTarget H current stage target
  let candidate := completionCandidate H current stage
  let f : ιtest →
      (Fin (Fintype.card (CompletionIndex H current stage)) → Bool) → ℝ :=
    fun a => sampledKilledWeight H (testJ a) (w a) candidate
  let b : ιtest →
      Fin (Fintype.card (CompletionIndex H current stage)) → ℝ :=
    fun a i => testExtension (w a) H (testJ a) (candidate i)
  have hb : ∀ a i, 0 ≤ b a i := by
    intro a i
    apply Finset.sum_nonneg
    intro S _hS
    exact hw a S
  have hbd : ∀ a i
      (x y : Fin (Fintype.card (CompletionIndex H current stage)) → Bool),
      (∀ q, q ≠ i → x q = y q) → |f a x - f a y| ≤ b a i := by
    intro a i x y hxy
    exact sampledKilledWeight_boundedDiff H (testJ a) (w a) candidate
      (hw a) i x y hxy
  obtain ⟨x, hrel, hupper, hblock, htest⟩ :=
    exists_bernoulli_chernoff_block_mcdiarmid p activeRel delta activeUpper
      threshold blockSize blocks blockThreshold f b gap hp hdelta0 hdelta1
      hthreshold0 hupperMean hblockDisj hblockThreshold0 hblockMean hb hbd
      hgap (by simpa [p, b] using hfail)
  let A := sampledCompletionLayer candidate x
  refine ⟨A, ?_, hdecode x hrel hupper hblock, ?_⟩
  · exact sampledSourceCompletionLayer_subset_candidates H current stage x
  · intro a
    rw [killedWeight_addCompletionLayer_eq_sampledKilledWeight H current
      (testJ a) (w a) candidate x (hw a) (hfreeZero a)]
    exact (htest a).trans_le (by simpa [p, f] using hkillMean a)


/-- Pair each weighted test with its support indicator, so one invocation
of `exists_regularizationStage` proves both quantitative clauses of (VI). -/
def pairedStageTestJ {ι : Type*} (testJ : ι → ℕ) : Sum ι ι → ℕ
  | Sum.inl a => testJ a
  | Sum.inr a => testJ a

def pairedStageTestWeight {ι : Type*} (H : Hypergraph V)
    (testJ : ι → ℕ) (w : ι → TestWeight V) : Sum ι ι → TestWeight V
  | Sum.inl a => positiveSupportIndicator H (testJ a) (w a)
  | Sum.inr a => w a

/-- Source-weighted completion with simultaneous per-support and lost-mass
control for every test index.  No test index is removed. -/
theorem exists_regularizationStage_supportAndWeight
    {ιrel ιupper ι : Type*}
    [Fintype ιrel] [Fintype ιupper] [Fintype ι]
    (H : Hypergraph V) (base current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ) (target : ℝ)
    (activeRel : ιrel →
      Fin (Fintype.card (CompletionIndex H current stage)) → Prop)
    (delta : ιrel → ℝ)
    (activeUpper : ιupper →
      Fin (Fintype.card (CompletionIndex H current stage)) → Prop)
    (threshold : ιupper → ℝ)
    (testJ : ι → ℕ) (w : ι → TestWeight V)
    (gap limit : Sum ι ι → ℝ)
    (hp : ∀ i, sourceCompletionBiasAtTarget H current stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hdelta0 : ∀ a, 0 ≤ delta a) (hdelta1 : ∀ a, delta a ≤ 1)
    (hthreshold0 : ∀ a, 0 ≤ threshold a)
    (hupperMean : ∀ a,
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (activeUpper a) ≤ threshold a)
    (hw : ∀ a S, 0 ≤ w a S)
    (hfreeZero : ∀ a S, S ∈ H.powersetCard (testJ a) →
      (∃ c ∈ current, c ⊆ S) → w a S = 0)
    (hgap : ∀ a, 0 ≤ gap a)
    (hkillMean : ∀ a : Sum ι ι,
      McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight
            (sourceCompletionBiasAtTarget H current stage target))
          (sampledKilledWeight H (pairedStageTestJ testJ a)
            (pairedStageTestWeight H testJ w a)
            (completionCandidate H current stage)) + gap a ≤ limit a)
    (hfail :
      (∑ a : ιrel,
          2 * Real.exp (-(delta a ^ 2 *
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (activeRel a)) / 3)) +
        (∑ a : ιupper, Real.exp (-threshold a / 3)) +
        (∑ a : Sum ι ι,
          Real.exp (-2 * gap a ^ 2 /
            ∑ i, (testExtension (pairedStageTestWeight H testJ w a) H
              (pairedStageTestJ testJ a)
              (completionCandidate H current stage i)) ^ 2)) < 1)
    (hdecode : ∀ x,
      (∀ a,
        |ChernoffFinite.bitCount (activeRel a) x -
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (activeRel a)| <
          delta a * ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H current stage target)
            (activeRel a)) →
      (∀ a, ChernoffFinite.bitCount (activeUpper a) x <
        2 * threshold a) →
      HasStagePropertiesIV H base
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        d eps stage) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H current stage ∧
      HasStagePropertiesIV H base (addCompletionLayer current A)
        d eps stage ∧
      (∀ a, ((killedSupport H (addCompletionLayer current A)
        (testJ a) (w a)).card : ℝ) < limit (Sum.inl a)) ∧
      (∀ a, killedWeight H (addCompletionLayer current A)
        (testJ a) (w a) < limit (Sum.inr a)) := by
  have hpairNonneg : ∀ a S, 0 ≤ pairedStageTestWeight H testJ w a S := by
    intro a S
    cases a with
    | inl a => exact positiveSupportIndicator_nonneg H (testJ a) (w a) S
    | inr a => exact hw a S
  have hpairFree : ∀ a S, S ∈ H.powersetCard (pairedStageTestJ testJ a) →
      (∃ c ∈ current, c ⊆ S) → pairedStageTestWeight H testJ w a S = 0 := by
    intro a S hSH hcontains
    cases a with
    | inl a =>
        exact positiveSupportIndicator_freeZero (hfreeZero a) S hSH hcontains
    | inr a => exact hfreeZero a S hSH hcontains
  obtain ⟨A, hA, hstage, hkill⟩ := exists_regularizationStage
    H base current d eps stage target activeRel delta activeUpper threshold
    (pairedStageTestJ testJ) (pairedStageTestWeight H testJ w) gap limit hp
    hdelta0 hdelta1 hthreshold0 hupperMean hpairNonneg hpairFree hgap
    hkillMean hfail hdecode
  refine ⟨A, hA, hstage, ?_, ?_⟩
  · intro a
    simpa [pairedStageTestJ, pairedStageTestWeight,
      killedWeight_supportIndicator] using hkill (Sum.inl a)
  · intro a
    simpa [pairedStageTestJ, pairedStageTestWeight] using hkill (Sum.inr a)

/-- The final deterministic payload obtained by composing stages `2,3,4`.
This packages exactly the fields of `RegularizationCertificate` which are
propagated from properties (I)--(V). -/
structure ThreeStageProperties
    (H : Hypergraph V) (base final : ConflictSystem V)
    (d eps : ℝ) : Prop where
  layerDegree : ∀ r, 2 ≤ r → r ≤ 4 → ∀ e ∈ H,
    InRelativeInterval (degree (conflictLayer final r) e : ℝ)
      (completionTarget d eps (layerMaxDegree H base r : ℝ) r)
      (Real.rpow d (-eps))
  layerCodegree : ∀ r q, 2 ≤ r → r ≤ 4 → 2 ≤ q → q < r →
    ∀ root, root.card = q →
      (codegree (conflictLayer final r) root : ℝ) ≤
        Real.rpow d ((r : ℝ) - (q : ℝ) - eps / 4)
  conditionC4 : ∀ e ∈ H, ∀ v,
    (conditionC4Count H final e v : ℝ) ≤
      Real.rpow d (1 - eps / 4)
  conditionC5 : ∀ e ∈ H, ∀ f ∈ H, Disjoint e f →
    (conditionC5Count H final e f : ℝ) ≤
      Real.rpow d (1 - eps / 4)
  commonLinks : ∀ e ∈ H, ∀ f ∈ H, Disjoint e f →
    {e, f} ∉ conflictLayer final 2 → ∀ s : Fin 3,
      (((conflictLinkLayer final e (s.1 + 1)) ∩
        conflictLinkLayer final f (s.1 + 1)).card : ℝ) ≤
          Real.rpow d ((s.1 + 1 : ℕ) - eps / 4)

theorem addCompletionLayer_conflict_card
    {C A : ConflictSystem V} {stage : ℕ}
    (hC : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    (hA : IsUniform A stage) (hs2 : 2 ≤ stage) (hs4 : stage ≤ 4) :
    ∀ c ∈ addCompletionLayer C A, 2 ≤ c.card ∧ c.card ≤ 4 := by
  intro c hc
  rcases Finset.mem_union.mp hc with hcA | hcC
  · rw [hA c hcA]
    exact ⟨hs2, hs4⟩
  · exact hC c (Finset.mem_filter.mp hcC).1

/-- Once the degree-sum absorption is supplied, the composed properties
(I)--(V) imply the full `(d,4,3 Gamma,eps/4)` boundedness package. -/
theorem ThreeStageProperties.isRegularizedBounded
    {H : Hypergraph V} {base final : ConflictSystem V}
    {d eps Gamma : ℝ}
    (h : ThreeStageProperties H base final d eps)
    (hcard : ∀ c ∈ final, 2 ≤ c.card ∧ c.card ≤ 4)
    (hGamma : 1 ≤ Gamma)
    (hdegreeSum :
      (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H final r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤ 3 * Gamma) :
    IsRegularizedBounded H final d (3 * Gamma) (eps / 4) := by
  refine ⟨hcard, hdegreeSum, ?_, ?_, h.conditionC4, h.conditionC5⟩
  · calc
      ((((Finset.Icc 2 4).filter fun r =>
          conflictLayer final r ≠ ∅).card : ℕ) : ℝ) ≤
          ((Finset.Icc 2 4).card : ℕ) := by
            exact_mod_cast Finset.card_filter_le _ _
      _ = 3 := by norm_num
      _ ≤ 3 * Gamma := by nlinarith
  · intro r hr2 hr4 q hq2 hqr root hroot
    exact h.layerCodegree r q hr2 hr4 hq2 hqr root hroot

/-- Properties (I)--(V) survive the later completion layers and assemble
into their final form. -/
theorem threeStageProperties_of_stageProperties
    (H : Hypergraph V) (base C0 A2 A3 A4 : ConflictSystem V)
    (d eps : ℝ)
    (hA2 : A2 ⊆ completionCandidates H C0 2)
    (hA3 : A3 ⊆ completionCandidates H (addCompletionLayer C0 A2) 3)
    (hA4 : A4 ⊆ completionCandidates H
      (addCompletionLayer (addCompletionLayer C0 A2) A3) 4)
    (h2 : HasStagePropertiesIV H base (addCompletionLayer C0 A2) d eps 2)
    (h3 : HasStagePropertiesIV H base
      (addCompletionLayer (addCompletionLayer C0 A2) A3) d eps 3)
    (h4 : HasStagePropertiesIV H base
      (addCompletionLayer
        (addCompletionLayer (addCompletionLayer C0 A2) A3) A4)
      d eps 4) :
    ThreeStageProperties H base
      (addCompletionLayer
        (addCompletionLayer (addCompletionLayer C0 A2) A3) A4)
      d eps := by
  let C2 := addCompletionLayer C0 A2
  let C3 := addCompletionLayer C2 A3
  let R := addCompletionLayer C3 A4
  have hu2 : IsUniform A2 2 :=
    (completionCandidates_uniform H C0 2).mono hA2
  have hu3 : IsUniform A3 3 :=
    (completionCandidates_uniform H C2 3).mono hA3
  have hu4 : IsUniform A4 4 :=
    (completionCandidates_uniform H C3 4).mono hA4
  have hR2 : conflictLayer R 2 = conflictLayer C2 2 := by
    rw [show R = addCompletionLayer C3 A4 by rfl,
      conflictLayer_addCompletionLayer_of_lt hu4 (by omega),
      show C3 = addCompletionLayer C2 A3 by rfl,
      conflictLayer_addCompletionLayer_of_lt hu3 (by omega)]
  have hR3 : conflictLayer R 3 = conflictLayer C3 3 := by
    rw [show R = addCompletionLayer C3 A4 by rfl,
      conflictLayer_addCompletionLayer_of_lt hu4 (by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr2 hr4 e he
    interval_cases r
    · rw [show conflictLayer R 2 = conflictLayer C2 2 from hR2]
      exact h2.2.2.1 e he
    · rw [show conflictLayer R 3 = conflictLayer C3 3 from hR3]
      exact h3.2.2.1 e he
    · exact h4.2.2.1 e he
  · intro r q hr2 hr4 hq2 hqr root hroot
    interval_cases r
    · omega
    · rw [show conflictLayer R 3 = conflictLayer C3 3 from hR3]
      exact h3.2.2.2.1 q hq2 hqr root hroot
    · exact h4.2.2.2.1 q hq2 hqr root hroot
  · intro e he v
    rw [conditionC4Count_addCompletionLayer_of_two_lt hu4 (by omega),
      conditionC4Count_addCompletionLayer_of_two_lt hu3 (by omega)]
    exact h2.2.2.2.2.1 rfl e he v
  · intro e he f hf hdisj
    rw [conditionC5Count_addCompletionLayer_of_two_lt hu4 (by omega),
      conditionC5Count_addCompletionLayer_of_two_lt hu3 (by omega)]
    exact h2.2.2.2.2.2.1 rfl e he f hf hdisj
  · intro e he f hf hdisj hnot s
    fin_cases s
    · have hnot2 : {e, f} ∉ conflictLayer C2 2 := by
        rwa [← hR2]
      have hbound := h2.2.2.2.2.2.2 e he f hf hdisj hnot2
      rw [conflictLinkLayer_addCompletionLayer_of_succ_lt
          (s := 1) (j := 4) hu4 (by norm_num) e,
        conflictLinkLayer_addCompletionLayer_of_succ_lt
          (s := 1) (j := 4) hu4 (by norm_num) f,
        conflictLinkLayer_addCompletionLayer_of_succ_lt
          (s := 1) (j := 3) hu3 (by norm_num) e,
        conflictLinkLayer_addCompletionLayer_of_succ_lt
          (s := 1) (j := 3) hu3 (by norm_num) f]
      simpa using hbound
    · have hnot3 : {e, f} ∉ conflictLayer C3 2 := by
        have h23 : conflictLayer C3 2 = conflictLayer C2 2 :=
          conflictLayer_addCompletionLayer_of_lt hu3 (by omega)
        rw [h23]
        rwa [← hR2]
      have hbound := h3.2.2.2.2.2.2 e he f hf hdisj hnot3
      rw [conflictLinkLayer_addCompletionLayer_of_succ_lt
          (s := 2) (j := 4) hu4 (by norm_num) e,
        conflictLinkLayer_addCompletionLayer_of_succ_lt
          (s := 2) (j := 4) hu4 (by norm_num) f]
      simpa using hbound
    · exact h4.2.2.2.2.2.2 e he f hf hdisj hnot

theorem threeStage_conflict_card
    (H : Hypergraph V) (C B A2 A3 A4 : ConflictSystem V)
    (hC : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    (hB : IsUniform B 2)
    (hA2 : A2 ⊆ completionCandidates H (minimalMatchingCore H (C ∪ B)) 2)
    (hA3 : A3 ⊆ completionCandidates H
      (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) 3)
    (hA4 : A4 ⊆ completionCandidates H
      (addCompletionLayer
        (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3) 4) :
    ∀ c ∈ addCompletionLayer
      (addCompletionLayer
        (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3) A4,
      2 ≤ c.card ∧ c.card ≤ 4 := by
  let C0 := minimalMatchingCore H (C ∪ B)
  let C2 := addCompletionLayer C0 A2
  let C3 := addCompletionLayer C2 A3
  have hC0 : ∀ c ∈ C0, 2 ≤ c.card ∧ c.card ≤ 4 := by
    intro c hc
    rcases Finset.mem_union.mp (mem_minimalMatchingCore.mp hc).1 with hcC | hcB
    · exact hC c hcC
    · rw [hB c hcB]
      omega
  have hu2 : IsUniform A2 2 :=
    (completionCandidates_uniform H C0 2).mono hA2
  have hu3 : IsUniform A3 3 :=
    (completionCandidates_uniform H C2 3).mono hA3
  have hu4 : IsUniform A4 4 :=
    (completionCandidates_uniform H C3 4).mono hA4
  have hC2 : ∀ c ∈ C2, 2 ≤ c.card ∧ c.card ≤ 4 :=
    addCompletionLayer_conflict_card hC0 hu2 (by norm_num) (by norm_num)
  have hC3 : ∀ c ∈ C3, 2 ≤ c.card ∧ c.card ≤ 4 :=
    addCompletionLayer_conflict_card hC2 hu3 (by norm_num) (by norm_num)
  exact addCompletionLayer_conflict_card hC3 hu4 (by norm_num) (by norm_num)

/-- Literal specialised output of Lemmas 8.5--8.6.  The three selected
families make the construction visible, while the remaining fields are the
regularity properties handed to the core matching process. -/
structure RegularizationCertificate
    {ι : Type*} [Fintype ι]
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma : ℝ) (ell : ℕ)
    (j : ι -> ℕ) (w : ι -> TestWeight V) where
  badPairs : ConflictSystem V
  completion2 : ConflictSystem V
  completion3 : ConflictSystem V
  completion4 : ConflictSystem V
  regularized : ConflictSystem V
  badPairs_definition :
    badPairs = badPairConflicts H C (fun s =>
      Nat.floor (Real.rpow d ((s.1 + 1 : ℕ) - eps / 3)))
  construction :
    regularized =
      addCompletionLayer
        (addCompletionLayer
          (addCompletionLayer
            (minimalMatchingCore H (C ∪ badPairs)) completion2) completion3)
        completion4
  badPairs_uniform : IsUniform badPairs 2
  badPairs_degree : ∀ e ∈ H,
    (degree badPairs e : ℝ) ≤ Real.rpow d (1 - eps / 3)
  completion2_uniform : IsUniform completion2 2
  completion3_uniform : IsUniform completion3 3
  completion4_uniform : IsUniform completion4 4
  isConflictSystem : IsConflictSystem H regularized
  bounded : IsRegularizedBounded H regularized d (3 * Gamma) (eps / 4)
  conflictMatching : ∀ c ∈ regularized, IsMatching H c
  antichain : ∀ c ∈ regularized, ∀ c' ∈ regularized, c ≠ c' -> ¬c ⊆ c'
  layerDegree : ∀ r, 2 ≤ r -> r ≤ 4 -> ∀ e ∈ H,
      InRelativeInterval (degree (conflictLayer regularized r) e : ℝ)
        (completionTarget d eps
          (layerMaxDegree H (minimalMatchingCore H (C ∪ badPairs)) r : ℝ) r)
        (Real.rpow d (-eps))
  layerCodegree : ∀ r q, 2 ≤ r -> r ≤ 4 -> 2 ≤ q -> q < r ->
    ∀ root, root.card = q ->
      (codegree (conflictLayer regularized r) root : ℝ) ≤
        Real.rpow d ((r : ℝ) - (q : ℝ) - eps / 4)
  conditionC4 : ∀ e ∈ H, ∀ v,
    (conditionC4Count H regularized e v : ℝ) ≤
      Real.rpow d (1 - eps / 4)
  conditionC5 : ∀ e ∈ H, ∀ f ∈ H, Disjoint e f ->
    (conditionC5Count H regularized e f : ℝ) ≤
      Real.rpow d (1 - eps / 4)
  commonLinks : ∀ e ∈ H, ∀ f ∈ H, Disjoint e f ->
    {e, f} ∉ conflictLayer regularized 2 -> ∀ s : Fin 3,
      (((conflictLinkLayer regularized e (s.1 + 1)) ∩
        conflictLinkLayer regularized f (s.1 + 1)).card : ℝ) ≤
          Real.rpow d ((s.1 + 1 : ℕ) - eps / 4)
  restrictedWeight : ι -> TestWeight V
  restrictedWeight_definition : ∀ a,
    restrictedWeight a = CFMRegularization.restrictWeight regularized (w a)
  /-- Weighted loss is the source-faithful output for arbitrary test
  functions.  An unweighted bound on the cardinality of the positive
  support is deliberately not required: trackability controls weighted
  extensions, and Lemma 8.7 transfers the finite-system conclusion by
  restricting the weight pointwise. -/
  killedWeight_small : ∀ a,
    killedWeight H regularized (j a) (w a) ≤
      testTotal (w a) H (j a) / Real.rpow d eps
  survivingTrackable : ∀ a,
    IsTrackable H regularized (j a) ell d (eps / 5) (restrictedWeight a)

/-- Assemble the public certificate from the three probabilistically
selected layers.  All structural fields, all of (I)--(V), and the
restricted-weight definition are proved here; callers only supply the
stagewise analytic outputs, final boundedness absorption, and the final
test estimates. -/
def regularizationCertificate_of_threeStages
    {ι : Type*} [Fintype ι]
    (H : Hypergraph V) (C B A2 A3 A4 : ConflictSystem V)
    (d eps Gamma : ℝ) (ell : ℕ)
    (j : ι → ℕ) (w : ι → TestWeight V)
    (hC : IsConflictSystem H C)
    (hCcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    (hGamma : 1 ≤ Gamma)
    (hBdef : B = badPairConflicts H C (fun s =>
      Nat.floor (Real.rpow d ((s.1 + 1 : ℕ) - eps / 3))))
    (hBdegree : ∀ e ∈ H,
      (degree B e : ℝ) ≤ Real.rpow d (1 - eps / 3))
    (hA2 : A2 ⊆ completionCandidates H (minimalMatchingCore H (C ∪ B)) 2)
    (hA3 : A3 ⊆ completionCandidates H
      (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) 3)
    (hA4 : A4 ⊆ completionCandidates H
      (addCompletionLayer
        (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3) 4)
    (h2 : HasStagePropertiesIV H (minimalMatchingCore H (C ∪ B))
      (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) d eps 2)
    (h3 : HasStagePropertiesIV H (minimalMatchingCore H (C ∪ B))
      (addCompletionLayer
        (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3)
      d eps 3)
    (h4 : HasStagePropertiesIV H (minimalMatchingCore H (C ∪ B))
      (addCompletionLayer
        (addCompletionLayer
          (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3) A4)
      d eps 4)
    (hdegreeSum :
      (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H
          (addCompletionLayer
            (addCompletionLayer
              (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3) A4)
          r : ℝ) / Real.rpow d ((r : ℝ) - 1)) ≤ 3 * Gamma)
    (hkillWeight : ∀ a,
      killedWeight H
        (addCompletionLayer
          (addCompletionLayer
            (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3) A4)
        (j a) (w a) ≤ testTotal (w a) H (j a) / Real.rpow d eps)
    (hsurvive : ∀ a,
      IsTrackable H
        (addCompletionLayer
          (addCompletionLayer
            (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3) A4)
        (j a) ell d (eps / 5)
        (restrictWeight
          (addCompletionLayer
            (addCompletionLayer
              (addCompletionLayer (minimalMatchingCore H (C ∪ B)) A2) A3) A4)
          (w a))) :
    RegularizationCertificate H C d eps Gamma ell j w := by
  let C0 := minimalMatchingCore H (C ∪ B)
  let C2 := addCompletionLayer C0 A2
  let C3 := addCompletionLayer C2 A3
  let R := addCompletionLayer C3 A4
  have hBsys : IsConflictSystem H B := by
    rw [hBdef]
    exact badPairConflicts_isConflictSystem H C _
  have hCB : IsConflictSystem H (C ∪ B) := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact hC c hc
    · exact hBsys c hc
  have hC0sys : IsConflictSystem H C0 :=
    minimalMatchingCore_isConflictSystem hCB
  have hA2sys : IsConflictSystem H A2 := by
    intro c hc
    exact completionCandidates_isConflictSystem H C0 2 c (hA2 hc)
  have hA3sys : IsConflictSystem H A3 := by
    intro c hc
    exact completionCandidates_isConflictSystem H C2 3 c (hA3 hc)
  have hA4sys : IsConflictSystem H A4 := by
    intro c hc
    exact completionCandidates_isConflictSystem H C3 4 c (hA4 hc)
  have hC2sys : IsConflictSystem H C2 :=
    addCompletionLayer_isConflictSystem hC0sys hA2sys
  have hC3sys : IsConflictSystem H C3 :=
    addCompletionLayer_isConflictSystem hC2sys hA3sys
  have hRsys : IsConflictSystem H R :=
    addCompletionLayer_isConflictSystem hC3sys hA4sys
  have hmatch0 : ∀ c ∈ C0, IsMatching H c :=
    fun c hc => minimalMatchingCore_members_match hc
  have hmatch2 : ∀ c ∈ C2, IsMatching H c :=
    addCompletionLayer_members_match hmatch0 hA2
  have hmatch3 : ∀ c ∈ C3, IsMatching H c :=
    addCompletionLayer_members_match hmatch2 hA3
  have hmatchR : ∀ c ∈ R, IsMatching H c :=
    addCompletionLayer_members_match hmatch3 hA4
  have hanti0 : ∀ c ∈ C0, ∀ c' ∈ C0, c ≠ c' → ¬c ⊆ c' :=
    fun c hc c' hc' hne => minimalMatchingCore_antichain hc hc' hne
  have hanti2 : ∀ c ∈ C2, ∀ c' ∈ C2, c ≠ c' → ¬c ⊆ c' :=
    addCompletionLayer_antichain hanti0 hA2
  have hanti3 : ∀ c ∈ C3, ∀ c' ∈ C3, c ≠ c' → ¬c ⊆ c' :=
    addCompletionLayer_antichain hanti2 hA3
  have hantiR : ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' → ¬c ⊆ c' :=
    addCompletionLayer_antichain hanti3 hA4
  have hthree : ThreeStageProperties H C0 R d eps :=
    threeStageProperties_of_stageProperties H C0 C0 A2 A3 A4 d eps
      hA2 hA3 hA4 h2 h3 h4
  have hfinalcard : ∀ c ∈ R, 2 ≤ c.card ∧ c.card ≤ 4 :=
    threeStage_conflict_card H C B A2 A3 A4 hCcard
      (by rw [hBdef]; exact badPairConflicts_uniform_two H C _) hA2 hA3 hA4
  have hbounded : IsRegularizedBounded H R d (3 * Gamma) (eps / 4) :=
    hthree.isRegularizedBounded hfinalcard hGamma hdegreeSum
  refine
    { badPairs := B
      completion2 := A2
      completion3 := A3
      completion4 := A4
      regularized := R
      badPairs_definition := hBdef
      construction := rfl
      badPairs_uniform := by rw [hBdef]; exact badPairConflicts_uniform_two H C _
      badPairs_degree := hBdegree
      completion2_uniform := (completionCandidates_uniform H C0 2).mono hA2
      completion3_uniform := (completionCandidates_uniform H C2 3).mono hA3
      completion4_uniform := (completionCandidates_uniform H C3 4).mono hA4
      isConflictSystem := hRsys
      bounded := hbounded
      conflictMatching := hmatchR
      antichain := hantiR
      layerDegree := ?_
      layerCodegree := hthree.layerCodegree
      conditionC4 := hthree.conditionC4
      conditionC5 := hthree.conditionC5
      commonLinks := hthree.commonLinks
      restrictedWeight := fun a => restrictWeight R (w a)
      restrictedWeight_definition := fun _ => rfl
      killedWeight_small := hkillWeight
      survivingTrackable := hsurvive }
  intro r hr2 hr4
  exact hthree.layerDegree r hr2 hr4

/-- The certificate really transfers conflict-freeness back to the original
system; this lemma does not rely on the displayed construction equation. -/
theorem RegularizationCertificate.conflictFree_original
    {ι : Type*} [Fintype ι]
    {H : Hypergraph V} {C : ConflictSystem V} {d eps Gamma : ℝ}
    {ell : ℕ}
    {j : ι -> ℕ} {w : ι -> TestWeight V}
    (R : RegularizationCertificate H C d eps Gamma ell j w)
    {M : Hypergraph V} (hmatch : IsMatching H M)
    (hM : ConflictFree R.regularized M) :
    ConflictFree C M := by
  intro c hc hsub
  obtain ⟨c', hc'R, hc'c⟩ := originalConflict_contains_threeStageUpdate
    R.construction hc (hmatch.mono hsub)
  exact hM c' hc'R (hc'c.trans hsub)

/-- Interface to the random-greedy core.  Any conclusion `Q` obtained for
the regularised system is retained, while conflict-freeness is transferred
to the original system. -/
theorem regularizedCoreTransfer
    {ι : Type*} [Fintype ι]
    {H : Hypergraph V} {C : ConflictSystem V} {d eps Gamma : ℝ}
    {ell : ℕ}
    {j : ι -> ℕ} {w : ι -> TestWeight V}
    (R : RegularizationCertificate H C d eps Gamma ell j w)
    (Q : Hypergraph V -> Prop)
    (hcore : ∃ M, IsMatching H M ∧ ConflictFree R.regularized M ∧ Q M) :
    ∃ M, IsMatching H M ∧ ConflictFree C M ∧ Q M := by
  obtain ⟨M, hmatch, hfree, hQ⟩ := hcore
  exact ⟨M, hmatch, R.conflictFree_original hmatch hfree, hQ⟩

/-! ### Source deficit windows for the three completion stages -/

theorem degree_le_sum_pair_codegrees_vertexFinset
    {H : Hypergraph V} {r : ℕ} (hH : IsUniform H r) (hr : 2 ≤ r)
    (v : V) :
    degree H v ≤
      ∑ w ∈ (vertexFinset H).erase v, codegree H {v, w} := by
  let F : V → Hypergraph V := fun w => H.filter fun e => {v, w} ⊆ e
  have hsub : H.filter (v ∈ ·) ⊆
      ((vertexFinset H).erase v).biUnion F := by
    intro e he
    have heH : e ∈ H := (Finset.mem_filter.mp he).1
    have hve : v ∈ e := (Finset.mem_filter.mp he).2
    have herase : (e.erase v).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hecard : e.card ≤ 1 := by
        rw [← Finset.card_erase_add_one hve, hempty]
        simp
      rw [hH e heH] at hecard
      omega
    obtain ⟨w, hwe⟩ := herase
    have hwne : w ≠ v := (Finset.mem_erase.mp hwe).1
    have hwv : w ∈ vertexFinset H :=
      edge_subset_vertexFinset heH (Finset.mem_of_mem_erase hwe)
    apply Finset.mem_biUnion.mpr
    refine ⟨w, Finset.mem_erase.mpr ⟨hwne, hwv⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨heH, ?_⟩
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hve, Finset.mem_of_mem_erase hwe⟩
  calc
    degree H v = (H.filter (v ∈ ·)).card := rfl
    _ ≤ (((vertexFinset H).erase v).biUnion F).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ w ∈ (vertexFinset H).erase v, (F w).card :=
      Finset.card_biUnion_le
    _ = ∑ w ∈ (vertexFinset H).erase v, codegree H {v, w} := by rfl

theorem degree_le_vertex_card_mul_pair_bound
    {H : Hypergraph V} {r : ℕ} (hH : IsUniform H r) (hr : 2 ≤ r)
    {L : ℝ} (hL : 0 ≤ L)
    (hcodeg : ∀ s, s.card = 2 → (codegree H s : ℝ) ≤ L)
    (v : V) :
    (degree H v : ℝ) ≤ ((vertexFinset H).card : ℝ) * L := by
  calc
    (degree H v : ℝ) ≤
        (∑ w ∈ (vertexFinset H).erase v, codegree H {v, w} : ℕ) := by
      exact_mod_cast degree_le_sum_pair_codegrees_vertexFinset hH hr v
    _ = ∑ w ∈ (vertexFinset H).erase v, (codegree H {v, w} : ℝ) := by
      norm_cast
    _ ≤ ∑ _w ∈ (vertexFinset H).erase v, L := by
      apply Finset.sum_le_sum
      intro w hw
      apply hcodeg
      have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
      simp [Ne.symm hwne]
    _ = (((vertexFinset H).erase v).card : ℝ) * L := by simp
    _ ≤ ((vertexFinset H).card : ℝ) * L := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) hL

theorem maxDegreeLE_floor_of_vertex_degree_upper
    {H : Hypergraph V} {d : ℝ}
    (hupper : ∀ v ∈ vertexFinset H, (degree H v : ℝ) ≤ d) :
    MaxDegreeLE H (Nat.floor d) := by
  intro v
  by_cases hv : v ∈ vertexFinset H
  · exact Nat.le_floor (hupper v hv)
  · rw [degree_eq_zero_of_not_mem_vertexFinset hv]
    exact Nat.zero_le _

theorem half_rpow_le_vertexFinset_card
    {H : Hypergraph V} {d eta : ℝ}
    (hH : IsUniform H 8) (hne : H.Nonempty) (hd : 0 < d)
    (hsmall : Real.rpow d (-eta) ≤ 1 / 2)
    (hlower : ∀ v ∈ vertexFinset H,
      (1 - Real.rpow d (-eta)) * d ≤ (degree H v : ℝ))
    (hcodeg : ∀ s, s.card = 2 →
      (codegree H s : ℝ) ≤ Real.rpow d (1 - eta)) :
    Real.rpow d eta / 2 ≤ ((vertexFinset H).card : ℝ) := by
  obtain ⟨e, heH⟩ := hne
  have hecard : e.card = 8 := hH e heH
  have he_nonempty : e.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    simp [he] at hecard
  obtain ⟨v, hve⟩ := he_nonempty
  have hvactive : v ∈ vertexFinset H := edge_subset_vertexFinset heH hve
  have hpair := degree_le_vertex_card_mul_pair_bound hH (by norm_num)
    (Real.rpow_nonneg hd.le _) hcodeg v
  have hlower' : d / 2 ≤ (degree H v : ℝ) := by
    calc
      d / 2 ≤ (1 - Real.rpow d (-eta)) * d := by nlinarith
      _ ≤ (degree H v : ℝ) := hlower v hvactive
  have hmul : d / 2 ≤
      ((vertexFinset H).card : ℝ) * Real.rpow d (1 - eta) :=
    hlower'.trans hpair
  have hpowpos : 0 < Real.rpow d (1 - eta) := Real.rpow_pos_of_pos hd _
  apply le_of_mul_le_mul_right _ hpowpos
  calc
    Real.rpow d eta / 2 * Real.rpow d (1 - eta) =
        (Real.rpow d eta * Real.rpow d (1 - eta)) / 2 := by ring
    _ = Real.rpow d (eta + (1 - eta)) / 2 := by
      congr 1
      exact (Real.rpow_add hd eta (1 - eta)).symm
    _ = d / 2 := by
      have : eta + (1 - eta) = 1 := by ring
      rw [this]
      congr 1
      exact Real.rpow_one d
    _ ≤ ((vertexFinset H).card : ℝ) * Real.rpow d (1 - eta) := hmul

theorem sixteenth_rpow_le_vertexFinset_card
    {H : Hypergraph V} {d eta : ℝ}
    (hH : IsUniform H 8) (hne : H.Nonempty) (hd : 0 < d)
    (hsmall : Real.rpow d (-eta) ≤ 1 / 2)
    (hlower : ∀ v ∈ vertexFinset H,
      (1 - Real.rpow d (-eta)) * d ≤ (degree H v : ℝ))
    (hcodeg : ∀ s, s.card = 2 →
      (codegree H s : ℝ) ≤ Real.rpow d (1 - eta)) :
    Real.rpow d eta / 16 ≤ ((vertexFinset H).card : ℝ) := by
  have hhalf := half_rpow_le_vertexFinset_card hH hne hd hsmall hlower hcodeg
  have hp : 0 ≤ Real.rpow d eta := Real.rpow_nonneg hd.le _
  nlinarith

theorem thirtysecond_rpow_le_host_card
    {H : Hypergraph V} {d eta : ℝ}
    (hH : IsUniform H 8) (hne : H.Nonempty) (hd : 0 < d)
    (hsmall : Real.rpow d (-eta) ≤ 1 / 2)
    (hlower : ∀ v ∈ vertexFinset H,
      (1 - Real.rpow d (-eta)) * d ≤ (degree H v : ℝ))
    (hcodeg : ∀ s, s.card = 2 →
      (codegree H s : ℝ) ≤ Real.rpow d (1 - eta)) :
    Real.rpow d (1 + eta) / 32 ≤ (H.card : ℝ) := by
  have hvertices := half_rpow_le_vertexFinset_card hH hne hd hsmall hlower hcodeg
  have hdeg : ∀ v ∈ vertexFinset H, d / 2 ≤ (degree H v : ℝ) := by
    intro v hv
    exact (by nlinarith : d / 2 ≤ (1 - Real.rpow d (-eta)) * d) |>.trans
      (hlower v hv)
  have hsum : ((vertexFinset H).card : ℝ) * (d / 2) ≤
      ∑ v ∈ vertexFinset H, (degree H v : ℝ) := by
    calc
      ((vertexFinset H).card : ℝ) * (d / 2) =
          ∑ _v ∈ vertexFinset H, d / 2 := by simp
      _ ≤ ∑ v ∈ vertexFinset H, (degree H v : ℝ) :=
        Finset.sum_le_sum fun v hv => hdeg v hv
  have hhandshake :
      (∑ v ∈ vertexFinset H, (degree H v : ℝ)) = 8 * (H.card : ℝ) := by
    norm_cast
    simpa using sum_degree_vertexFinset_of_uniform hH
  have hprod : Real.rpow d eta / 2 * (d / 2) ≤ 8 * (H.card : ℝ) := by
    calc
      Real.rpow d eta / 2 * (d / 2) ≤
          ((vertexFinset H).card : ℝ) * (d / 2) := by
        exact mul_le_mul_of_nonneg_right hvertices (by positivity)
      _ ≤ ∑ v ∈ vertexFinset H, (degree H v : ℝ) := hsum
      _ = 8 * (H.card : ℝ) := hhandshake
  have hrpow : Real.rpow d (1 + eta) = Real.rpow d eta * d := by
    calc
      Real.rpow d (1 + eta) = Real.rpow d (eta + 1) := by congr 1 <;> ring
      _ = Real.rpow d eta * Real.rpow d 1 := Real.rpow_add hd eta 1
      _ = Real.rpow d eta * d := by
        congr 1
        exact Real.rpow_one d
  rw [hrpow]
  nlinarith

theorem conflictLayer_minimalMatchingCore_union_two_subset
    {H : Hypergraph V} {C B : ConflictSystem V} {j : ℕ}
    (hB : IsUniform B 2) (hj : 3 ≤ j) :
    conflictLayer (minimalMatchingCore H (C ∪ B)) j ⊆ conflictLayer C j := by
  intro c hc
  have hc' := Finset.mem_filter.mp hc
  have hcCore := (mem_minimalMatchingCore.mp hc'.1).1
  apply Finset.mem_filter.mpr
  refine ⟨?_, hc'.2⟩
  rcases Finset.mem_union.mp hcCore with hcC | hcB
  · exact hcC
  · have := hB c hcB
    omega

theorem layerMaxDegree_minimalMatchingCore_union_two_le
    {H : Hypergraph V} {C B : ConflictSystem V}
    {d eta : ℝ} {ell j : ℕ}
    (hC : IsBounded C d ell eta) (hB : IsUniform B 2)
    (hj3 : 3 ≤ j) (hjell : j ≤ ell) :
    (layerMaxDegree H (minimalMatchingCore H (C ∪ B)) j : ℝ) ≤
      (ell : ℝ) * Real.rpow d ((j : ℝ) - 1) := by
  let R := (ell : ℝ) * Real.rpow d ((j : ℝ) - 1)
  have hR0 : 0 ≤ R := by
    exact (Nat.cast_nonneg (degree (conflictLayer C j) ∅)).trans
      (hC.2.1 j hj3 hjell ∅)
  have hsup :
      layerMaxDegree H (minimalMatchingCore H (C ∪ B)) j ≤ Nat.floor R := by
    unfold layerMaxDegree
    apply Finset.sup_le
    intro e heH
    apply Nat.le_floor
    calc
      (degree (conflictLayer (minimalMatchingCore H (C ∪ B)) j) e : ℝ) ≤
          (degree (conflictLayer C j) e : ℝ) := by
        exact_mod_cast degree_mono
          (conflictLayer_minimalMatchingCore_union_two_subset hB hj3) e
      _ ≤ R := hC.2.1 j hj3 hjell e
  calc
    (layerMaxDegree H (minimalMatchingCore H (C ∪ B)) j : ℝ) ≤
        (Nat.floor R : ℕ) := by exact_mod_cast hsup
    _ ≤ R := Nat.floor_le hR0

theorem conflictLayer_addCompletionLayer_subset_of_ne
    {C A : ConflictSystem V} {r k : ℕ}
    (hA : IsUniform A k) (hrk : r ≠ k) :
    conflictLayer (addCompletionLayer C A) r ⊆ conflictLayer C r := by
  intro c hc
  rw [mem_conflictLayer_addCompletionLayer] at hc
  rcases hc with ⟨hcA, hcr⟩ | ⟨hcC, _hminimal, hcr⟩
  · exact False.elim (hrk (hcr.symm.trans (hA c hcA)))
  · exact mem_conflictLayer.mpr ⟨hcC, hcr⟩

theorem conflictLayer_stageThree_subset_base
    (base A2 : ConflictSystem V) (hA2 : IsUniform A2 2) :
    conflictLayer (addCompletionLayer base A2) 3 ⊆
      conflictLayer base 3 := by
  exact conflictLayer_addCompletionLayer_subset_of_ne hA2 (by omega)

theorem conflictLayer_stageFour_subset_base
    (base A2 A3 : ConflictSystem V)
    (hA2 : IsUniform A2 2) (hA3 : IsUniform A3 3) :
    conflictLayer (addCompletionLayer (addCompletionLayer base A2) A3) 4 ⊆
      conflictLayer base 4 := by
  exact (conflictLayer_addCompletionLayer_subset_of_ne hA3 (by omega)).trans
    (conflictLayer_addCompletionLayer_subset_of_ne hA2 (by omega))

theorem hasSourceDeficitBoundsAtTarget_of_layer_subset
    (H : Hypergraph V) (base current : ConflictSystem V)
    {d eps Gamma : ℝ} {j : ℕ}
    (hd : 2 ≤ d) (heps : 0 < eps) (hGamma : 1 ≤ Gamma)
    (hj2 : 2 ≤ j) (hj4 : j ≤ 4)
    (hcurrent : conflictLayer current j ⊆ conflictLayer base j)
    (hbase : (layerMaxDegree H base j : ℝ) ≤
      Gamma * Real.rpow d ((j : ℝ) - 1)) :
    HasSourceDeficitBoundsAtTarget H current d eps Gamma
      (completionTarget d eps (layerMaxDegree H base j : ℝ) j) j := by
  refine ⟨hj2, hj4, ?_⟩
  intro e he
  let delta : ℝ := layerMaxDegree H base j
  let p : ℝ := Real.rpow d ((j : ℝ) - 1)
  let baseline : ℝ := Real.rpow d ((j : ℝ) - 1 - eps / 600)
  let t : ℝ := Real.rpow d (-eps / 4)
  let m : ℝ := max baseline delta
  have hd1 : 1 ≤ d := hd.trans' (by norm_num)
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact Real.rpow_nonneg hd0.le _
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact Real.rpow_le_one_of_one_le_of_nonpos hd1 (by linarith)
  have hp0 : 0 ≤ p := by
    dsimp [p]
    exact Real.rpow_nonneg hd0.le _
  have hbaseline0 : 0 ≤ baseline := by
    dsimp [baseline]
    exact Real.rpow_nonneg hd0.le _
  have hdelta0 : 0 ≤ delta := by positivity
  have hm0 : 0 ≤ m := hbaseline0.trans (le_max_left baseline delta)
  have hdegCurrentBase :
      (degree (conflictLayer current j) e : ℝ) ≤
        degree (conflictLayer base j) e := by
    exact_mod_cast degree_mono hcurrent e
  have hdegBaseDelta :
      (degree (conflictLayer base j) e : ℝ) ≤ delta := by
    dsimp [delta]
    exact_mod_cast degree_layer_le_layerMaxDegree he
  have hdegCurrentM :
      (degree (conflictLayer current j) e : ℝ) ≤ m :=
    (hdegCurrentBase.trans hdegBaseDelta).trans (le_max_right _ _)
  have hpowMul : t * baseline =
      Real.rpow d ((j : ℝ) - 1 - eps / 4 - eps / 600) := by
    dsimp [t, baseline]
    rw [← Real.rpow_add hd0]
    congr 1
    ring
  have hlowPow :
      Real.rpow d ((j : ℝ) - 1 - 2 * eps) ≤ t * baseline := by
    rw [hpowMul]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have hlower :
      Real.rpow d ((j : ℝ) - 1 - 2 * eps) ≤
        degreeDeficit current j
          (completionTarget d eps (layerMaxDegree H base j : ℝ) j) e := by
    calc
      Real.rpow d ((j : ℝ) - 1 - 2 * eps) ≤ t * baseline := hlowPow
      _ ≤ t * m := mul_le_mul_of_nonneg_left (le_max_left _ _) ht0
      _ = (1 + t) * m - m := by ring
      _ ≤ (1 + t) * m - (degree (conflictLayer current j) e : ℝ) :=
        sub_le_sub_left hdegCurrentM _
      _ = degreeDeficit current j
          (completionTarget d eps (layerMaxDegree H base j : ℝ) j) e := by
        rfl
  have hbaselineP : baseline ≤ p := by
    dsimp [baseline, p]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have hpGammaP : p ≤ Gamma * p := by nlinarith
  have hdeltaGammaP : delta ≤ Gamma * p := by
    simpa [delta, p] using hbase
  have hmGammaP : m ≤ Gamma * p :=
    max_le (hbaselineP.trans hpGammaP) hdeltaGammaP
  have hfactor2 : 1 + t ≤ 2 := by linarith
  have htargetUpper : (1 + t) * m ≤ 2 * (Gamma * p) := by
    exact mul_le_mul hfactor2 hmGammaP hm0 (by norm_num)
  have hupper :
      degreeDeficit current j
          (completionTarget d eps (layerMaxDegree H base j : ℝ) j) e ≤
        4 * Gamma * Real.rpow d ((j : ℝ) - 1) := by
    calc
      degreeDeficit current j
          (completionTarget d eps (layerMaxDegree H base j : ℝ) j) e ≤
          (1 + t) * m := by
        rw [degreeDeficit, completionTarget]
        exact sub_le_self _ (by positivity)
      _ ≤ 2 * (Gamma * p) := htargetUpper
      _ ≤ 4 * Gamma * Real.rpow d ((j : ℝ) - 1) := by
        change 2 * (Gamma * p) ≤ 4 * Gamma * p
        nlinarith
  exact ⟨hlower, hupper⟩

theorem hasSourceDeficitBoundsAtTarget_stageTwo
    (H : Hypergraph V) (base : ConflictSystem V)
    {d eps Gamma : ℝ}
    (hd : 2 ≤ d) (heps : 0 < eps) (hGamma : 1 ≤ Gamma)
    (hbase : (layerMaxDegree H base 2 : ℝ) ≤
      Gamma * Real.rpow d ((2 : ℝ) - 1)) :
    HasSourceDeficitBoundsAtTarget H base d eps Gamma
      (completionTarget d eps (layerMaxDegree H base 2 : ℝ) 2) 2 := by
  exact hasSourceDeficitBoundsAtTarget_of_layer_subset H base base hd heps hGamma
    (by norm_num) (by norm_num) Finset.Subset.rfl hbase

theorem hasSourceDeficitBoundsAtTarget_stageThree
    (H : Hypergraph V) (base A2 : ConflictSystem V)
    {d eps Gamma : ℝ}
    (hd : 2 ≤ d) (heps : 0 < eps) (hGamma : 1 ≤ Gamma)
    (hA2 : IsUniform A2 2)
    (hbase : (layerMaxDegree H base 3 : ℝ) ≤
      Gamma * Real.rpow d ((3 : ℝ) - 1)) :
    HasSourceDeficitBoundsAtTarget H (addCompletionLayer base A2)
      d eps Gamma
      (completionTarget d eps (layerMaxDegree H base 3 : ℝ) 3) 3 := by
  exact hasSourceDeficitBoundsAtTarget_of_layer_subset H base
    (addCompletionLayer base A2) hd heps hGamma (by norm_num) (by norm_num)
    (conflictLayer_stageThree_subset_base base A2 hA2) hbase

theorem hasSourceDeficitBoundsAtTarget_stageFour
    (H : Hypergraph V) (base A2 A3 : ConflictSystem V)
    {d eps Gamma : ℝ}
    (hd : 2 ≤ d) (heps : 0 < eps) (hGamma : 1 ≤ Gamma)
    (hA2 : IsUniform A2 2) (hA3 : IsUniform A3 3)
    (hbase : (layerMaxDegree H base 4 : ℝ) ≤
      Gamma * Real.rpow d ((4 : ℝ) - 1)) :
    HasSourceDeficitBoundsAtTarget H
      (addCompletionLayer (addCompletionLayer base A2) A3)
      d eps Gamma
      (completionTarget d eps (layerMaxDegree H base 4 : ℝ) 4) 4 := by
  exact hasSourceDeficitBoundsAtTarget_of_layer_subset H base
    (addCompletionLayer (addCompletionLayer base A2) A3)
    hd heps hGamma (by norm_num) (by norm_num)
    (conflictLayer_stageFour_subset_base base A2 A3 hA2 hA3) hbase

theorem totalDeficit_lower_of_sourceBounds
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma target : ℝ) (j : ℕ)
    (hdef : HasSourceDeficitBoundsAtTarget H C d eps Gamma target j) :
    (H.card : ℝ) * Real.rpow d ((j : ℝ) - 1 - 2 * eps) ≤
      totalDeficit H (degreeDeficit C j target) := by
  exact card_mul_le_totalDeficit H (degreeDeficit C j target)
    (Real.rpow d ((j : ℝ) - 1 - 2 * eps))
    (fun e he => (hdef.2.2 e he).1)

theorem totalDeficit_pos_of_sourceBounds
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma target : ℝ) (j : ℕ)
    (hH : H.Nonempty) (hd : 0 < d)
    (hdef : HasSourceDeficitBoundsAtTarget H C d eps Gamma target j) :
    0 < totalDeficit H (degreeDeficit C j target) := by
  have hcard : 0 < (H.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hH
  have hbase : 0 < Real.rpow d ((j : ℝ) - 1 - 2 * eps) :=
    Real.rpow_pos_of_pos hd _
  exact (mul_pos hcard hbase).trans_le
    (totalDeficit_lower_of_sourceBounds H C d eps Gamma target j hdef)

theorem sourceCompletionBiasAtTarget_le_sourcePmax
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma target : ℝ) (j : ℕ)
    (hH : H.Nonempty) (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (hdef : HasSourceDeficitBoundsAtTarget H C d eps Gamma target j)
    (i : Fin (Fintype.card (CompletionIndex H C j))) :
    sourceCompletionBiasAtTarget H C j target i ≤
      (Nat.factorial (j - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ j /
        (((H.card : ℝ) *
          Real.rpow d ((j : ℝ) - 1 - 2 * eps)) ^ (j - 1)) := by
  apply sourceCompletionBiasAtTarget_le_deficit_bound H C target
    (Real.rpow d ((j : ℝ) - 1 - 2 * eps))
    (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) j hH
  · exact Real.rpow_pos_of_pos hd _
  · exact mul_nonneg (mul_nonneg (by norm_num) hGamma)
      (Real.rpow_nonneg hd.le _)
  · exact fun e he => (hdef.2.2 e he).1
  · exact fun e he => (hdef.2.2 e he).2

theorem sourceCompletionBiasAtTarget_mem_Icc_of_sourcePmax_le_one
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma target : ℝ) (j : ℕ)
    (hH : H.Nonempty) (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (hdef : HasSourceDeficitBoundsAtTarget H C d eps Gamma target j)
    (hpmaxOne :
      (Nat.factorial (j - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ j /
        (((H.card : ℝ) *
          Real.rpow d ((j : ℝ) - 1 - 2 * eps)) ^ (j - 1)) ≤ 1) :
    ∀ i, sourceCompletionBiasAtTarget H C j target i ∈ Set.Icc (0 : ℝ) 1 := by
  apply sourceCompletionBiasAtTarget_mem_Icc H C d eps Gamma target j hd.le hdef
  intro i
  exact (sourceCompletionBiasAtTarget_le_sourcePmax H C d eps Gamma
    target j hH hd hGamma hdef i).trans hpmaxOne

theorem completionWeight_le_sourcePmax
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma target : ℝ) (j : ℕ)
    (hH : H.Nonempty) (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (hdef : HasSourceDeficitBoundsAtTarget H C d eps Gamma target j)
    (A : Hypergraph V) (hA : A ∈ H.powersetCard j) :
    completionWeight H j (degreeDeficit C j target) A ≤
      (Nat.factorial (j - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ j /
        (((H.card : ℝ) *
          Real.rpow d ((j : ℝ) - 1 - 2 * eps)) ^ (j - 1)) := by
  obtain ⟨hAH, hAj⟩ := Finset.mem_powersetCard.mp hA
  apply completionWeight_le_deficit_bound H C target
    (Real.rpow d ((j : ℝ) - 1 - 2 * eps))
    (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) j hH
  · exact Real.rpow_pos_of_pos hd _
  · exact mul_nonneg (mul_nonneg (by norm_num) hGamma)
      (Real.rpow_nonneg hd.le _)
  · exact fun e he => (hdef.2.2 e he).1
  · exact fun e he => (hdef.2.2 e he).2
  · exact hAH
  · exact hAj

theorem sourceIncidentMean_room_of_forbidden_card
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma target pmax forbiddenRoom : ℝ) (j : ℕ)
    (hH : H.Nonempty) (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (hdef : HasSourceDeficitBoundsAtTarget H C d eps Gamma target j)
    (hpmax :
      (Nat.factorial (j - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ j /
        (((H.card : ℝ) *
          Real.rpow d ((j : ℝ) - 1 - 2 * eps)) ^ (j - 1)) ≤ pmax)
    (e : Finset V) (heH : e ∈ H)
    (hforbidden :
      ((forbiddenIncidentCompletions H C j e).card : ℝ) * pmax ≤
        forbiddenRoom) :
    |(degree (conflictLayer C j) e : ℝ) +
        ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C j target)
          (fun i => e ∈ completionCandidate H C j i) - target| ≤
      12 * (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ 2 /
          totalDeficit H (degreeDeficit C j target) + forbiddenRoom := by
  have ha0 : ∀ f ∈ H, 0 ≤ degreeDeficit C j target f := by
    intro f hf
    exact (Real.rpow_nonneg hd.le _).trans (hdef.2.2 f hf).1
  have haU : ∀ f ∈ H, degreeDeficit C j target f ≤
      4 * Gamma * Real.rpow d ((j : ℝ) - 1) :=
    fun f hf => (hdef.2.2 f hf).2
  have hweight : ∀ A ∈ H.powersetCard j,
      completionWeight H j (degreeDeficit C j target) A ≤ pmax := by
    intro A hA
    exact (completionWeight_le_sourcePmax H C d eps Gamma target j
      hH hd hGamma hdef A hA).trans hpmax
  have herr := sourceIncidentMean_error H C j hdef.1 hdef.2.1 target
    (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) pmax heH
    (mul_nonneg (mul_nonneg (by norm_num) hGamma)
      (Real.rpow_nonneg hd.le _)) ha0 haU
    (totalDeficit_pos_of_sourceBounds H C d eps Gamma target j hH hd hdef)
    hweight
  have hrewrite :
      (degree (conflictLayer C j) e : ℝ) +
          ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H C j target)
            (fun i => e ∈ completionCandidate H C j i) - target =
        ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H C j target)
            (fun i => e ∈ completionCandidate H C j i) -
          degreeDeficit C j target e := by
    simp only [degreeDeficit]
    ring
  rw [hrewrite]
  exact herr.trans (by linarith)

theorem sourceIncidentMean_room
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eps Gamma target pmax room : ℝ) (j : ℕ)
    (hH : H.Nonempty) (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (hdef : HasSourceDeficitBoundsAtTarget H C d eps Gamma target j)
    (hpmax :
      (Nat.factorial (j - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ j /
        (((H.card : ℝ) *
          Real.rpow d ((j : ℝ) - 1 - 2 * eps)) ^ (j - 1)) ≤ pmax)
    (e : Finset V) (heH : e ∈ H)
    (hroom :
      12 * (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ 2 /
          totalDeficit H (degreeDeficit C j target) +
        ((forbiddenIncidentCompletions H C j e).card : ℝ) * pmax ≤
          room) :
    |(degree (conflictLayer C j) e : ℝ) +
        ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C j target)
          (fun i => e ∈ completionCandidate H C j i) - target| ≤ room := by
  exact (sourceIncidentMean_room_of_forbidden_card H C d eps Gamma
    target pmax
      (((forbiddenIncidentCompletions H C j e).card : ℝ) * pmax)
      j hH hd hGamma hdef hpmax e heH le_rfl).trans hroom

theorem sourceIncidentMean_bounds_of_room
    {H : Hypergraph V} {C : ConflictSystem V} {j : ℕ} {target room : ℝ}
    {e : Finset V}
    (hroom :
      |(degree (conflictLayer C j) e : ℝ) +
          ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H C j target)
            (fun i => e ∈ completionCandidate H C j i) - target| ≤ room) :
    degreeDeficit C j target e - room ≤
        ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C j target)
          (fun i => e ∈ completionCandidate H C j i) ∧
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C j target)
          (fun i => e ∈ completionCandidate H C j i) ≤
        degreeDeficit C j target e + room := by
  rw [abs_le] at hroom
  simp only [degreeDeficit]
  constructor <;> linarith [hroom.1, hroom.2]

theorem halfRelativeDeviation_fits_margin
    {H : Hypergraph V} {C : ConflictSystem V} {j : ℕ}
    {target err room : ℝ} {e : Finset V}
    (herr0 : 0 ≤ err) (herr1 : err ≤ 1)
    (hroom0 : 0 ≤ room)
    (hroomSmall : room ≤ err * target / 4)
    (hmeanRoom :
      |(degree (conflictLayer C j) e : ℝ) +
          ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H C j target)
            (fun i => e ∈ completionCandidate H C j i) - target| ≤ room) :
    (err / 2) *
        ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C j target)
          (fun i => e ∈ completionCandidate H C j i) ≤
      err * target - room := by
  have hmeanUpper := (sourceIncidentMean_bounds_of_room hmeanRoom).2
  have hdefUpper : degreeDeficit C j target e ≤ target := by
    simp only [degreeDeficit]
    exact sub_le_self _ (Nat.cast_nonneg _)
  have hmeanTarget :
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C j target)
          (fun i => e ∈ completionCandidate H C j i) ≤
        target + room := by linarith
  have hhalf0 : 0 ≤ err / 2 := div_nonneg herr0 (by norm_num)
  have hmul : (err / 2) *
        ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C j target)
          (fun i => e ∈ completionCandidate H C j i) ≤
      (err / 2) * (target + room) :=
    mul_le_mul_of_nonneg_left hmeanTarget hhalf0
  have heroom : err * room ≤ room := by
    nlinarith [mul_le_mul_of_nonneg_right herr1 hroom0]
  nlinarith

theorem sourceIncidentMean_lower_of_room
    {H : Hypergraph V} {C : ConflictSystem V} {j : ℕ}
    {target room L : ℝ} {e : Finset V}
    (hL : L ≤ degreeDeficit C j target e)
    (hroomSmall : room ≤ L / 2)
    (hmeanRoom :
      |(degree (conflictLayer C j) e : ℝ) +
          ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H C j target)
            (fun i => e ∈ completionCandidate H C j i) - target| ≤ room) :
    L / 2 ≤
      ChernoffFinite.bitMean
        (sourceCompletionBiasAtTarget H C j target)
        (fun i => e ∈ completionCandidate H C j i) := by
  have hmeanLower := (sourceIncidentMean_bounds_of_room hmeanRoom).1
  linarith

theorem sourceIncident_chernoffExponent_lower
    {H : Hypergraph V} {C : ConflictSystem V} {j : ℕ}
    {target err room L : ℝ} {e : Finset V}
    (_herr0 : 0 ≤ err)
    (hL : L ≤ degreeDeficit C j target e)
    (hroomSmall : room ≤ L / 2)
    (hmeanRoom :
      |(degree (conflictLayer C j) e : ℝ) +
          ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H C j target)
            (fun i => e ∈ completionCandidate H C j i) - target| ≤ room) :
    err ^ 2 * L / 8 ≤
      (err / 2) ^ 2 *
        ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H C j target)
          (fun i => e ∈ completionCandidate H C j i) := by
  have hmeanLower := sourceIncidentMean_lower_of_room hL hroomSmall hmeanRoom
  have hmul := mul_le_mul_of_nonneg_left hmeanLower (sq_nonneg (err / 2))
  nlinarith

/-! ### Finite large-parameter failure budget -/

/-- A common entropy bound and a common Chernoff scale make the sum of
the three failure families in `exists_bernoulli_chernoff_mcdiarmid` less
than one. -/
theorem failureSum_lt_one_of_exp_card_bounds
    {ιrel ιupper ιbd : Type*}
    [Fintype ιrel] [Fintype ιupper] [Fintype ιbd]
    (x y : ℝ) (zrel : ιrel → ℝ) (zupper : ιupper → ℝ)
    (zbd : ιbd → ℝ)
    (hpower : 12 * y ≤ x)
    (hlog : 4 * Real.log 12 ≤ x)
    (hcardRel : (Fintype.card ιrel : ℝ) ≤ Real.exp y)
    (hcardUpper : (Fintype.card ιupper : ℝ) ≤ Real.exp y)
    (hcardBd : (Fintype.card ιbd : ℝ) ≤ Real.exp y)
    (hzrel : ∀ i, x ≤ zrel i)
    (hzupper : ∀ i, x ≤ zupper i)
    (hzbd : ∀ i, x / 3 ≤ zbd i) :
    (∑ i : ιrel, 2 * Real.exp (-(zrel i) / 3)) +
        (∑ i : ιupper, Real.exp (-(zupper i) / 3)) +
        (∑ i : ιbd, Real.exp (-(zbd i))) < 1 := by
  have hquarter : Real.exp (-x / 4) ≤ (1 / 12 : ℝ) := by
    calc
      Real.exp (-x / 4) ≤ Real.exp (-Real.log 12) := by
        rw [Real.exp_le_exp]
        nlinarith
      _ = 1 / 12 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 12)]
        norm_num
  have hexponent : y - x / 3 ≤ -x / 4 := by nlinarith
  have hrel :
      (∑ i : ιrel, 2 * Real.exp (-(zrel i) / 3)) ≤ (1 / 6 : ℝ) := by
    calc
      (∑ i : ιrel, 2 * Real.exp (-(zrel i) / 3)) ≤
          ∑ _i : ιrel, 2 * Real.exp (-x / 3) := by
        apply Finset.sum_le_sum
        intro i _hi
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [Real.exp_le_exp]
        linarith [hzrel i]
      _ = (Fintype.card ιrel : ℝ) * (2 * Real.exp (-x / 3)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
      _ ≤ Real.exp y * (2 * Real.exp (-x / 3)) := by
        exact mul_le_mul_of_nonneg_right hcardRel
          (mul_nonneg (by norm_num) (Real.exp_nonneg _))
      _ = 2 * Real.exp (y - x / 3) := by
        calc
          Real.exp y * (2 * Real.exp (-x / 3)) =
              2 * (Real.exp y * Real.exp (-x / 3)) := by ring
          _ = 2 * Real.exp (y - x / 3) := by
            rw [← Real.exp_add]
            congr 2
            ring
      _ ≤ 2 * Real.exp (-x / 4) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hexponent) (by norm_num)
      _ ≤ 1 / 6 := by nlinarith
  have hupper :
      (∑ i : ιupper, Real.exp (-(zupper i) / 3)) ≤ (1 / 12 : ℝ) := by
    calc
      (∑ i : ιupper, Real.exp (-(zupper i) / 3)) ≤
          ∑ _i : ιupper, Real.exp (-x / 3) := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [Real.exp_le_exp]
        linarith [hzupper i]
      _ = (Fintype.card ιupper : ℝ) * Real.exp (-x / 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
      _ ≤ Real.exp y * Real.exp (-x / 3) := by
        exact mul_le_mul_of_nonneg_right hcardUpper (Real.exp_nonneg _)
      _ = Real.exp (y - x / 3) := by
        rw [show -x / 3 = -(x / 3) by ring, ← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (-x / 4) := Real.exp_le_exp.mpr hexponent
      _ ≤ 1 / 12 := hquarter
  have hbd :
      (∑ i : ιbd, Real.exp (-(zbd i))) ≤ (1 / 12 : ℝ) := by
    calc
      (∑ i : ιbd, Real.exp (-(zbd i))) ≤
          ∑ _i : ιbd, Real.exp (-x / 3) := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [Real.exp_le_exp]
        linarith [hzbd i]
      _ = (Fintype.card ιbd : ℝ) * Real.exp (-x / 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
      _ ≤ Real.exp y * Real.exp (-x / 3) := by
        exact mul_le_mul_of_nonneg_right hcardBd (Real.exp_nonneg _)
      _ = Real.exp (y - x / 3) := by
        rw [show -x / 3 = -(x / 3) by ring, ← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (-x / 4) := Real.exp_le_exp.mpr hexponent
      _ ≤ 1 / 12 := hquarter
  linarith

theorem chernoffMcDiarmid_failureSum_lt_one_of_exp_card_bounds
    {ιrel ιupper ιbd : Type*}
    [Fintype ιrel] [Fintype ιupper] [Fintype ιbd]
    (x y : ℝ) (delta mean : ιrel → ℝ)
    (threshold : ιupper → ℝ) (gap influenceSq : ιbd → ℝ)
    (hpower : 12 * y ≤ x)
    (hlog : 4 * Real.log 12 ≤ x)
    (hcardRel : (Fintype.card ιrel : ℝ) ≤ Real.exp y)
    (hcardUpper : (Fintype.card ιupper : ℝ) ≤ Real.exp y)
    (hcardBd : (Fintype.card ιbd : ℝ) ≤ Real.exp y)
    (hzrel : ∀ i, x ≤ delta i ^ 2 * mean i)
    (hzupper : ∀ i, x ≤ threshold i)
    (hzbd : ∀ i, x / 3 ≤ 2 * gap i ^ 2 / influenceSq i) :
    (∑ i : ιrel,
          2 * Real.exp (-(delta i ^ 2 * mean i) / 3)) +
        (∑ i : ιupper, Real.exp (-threshold i / 3)) +
        (∑ i : ιbd,
          Real.exp (-2 * gap i ^ 2 / influenceSq i)) < 1 := by
  have h := failureSum_lt_one_of_exp_card_bounds x y
    (fun i => delta i ^ 2 * mean i) threshold
    (fun i => 2 * gap i ^ 2 / influenceSq i)
    hpower hlog hcardRel hcardUpper hcardBd hzrel hzupper hzbd
  simpa only [neg_div, neg_mul] using h

/-- The finite registry containing the two numerical absorptions used by
the failure budget. -/
def failureBudgetRegistry (a b : ℝ) (ha : 0 < a) (hab : b < a) :
    LargeDRegistry Bool where
  active := Finset.univ
  condition i d := if i = true then
      12 * Real.rpow d b ≤ Real.rpow d a
    else
      4 * Real.log 12 ≤ Real.rpow d a
  eventually_condition := by
    intro i _hi
    cases i with
    | false =>
        have h := eventually_const_mul_rpow_le_rpow_real
          (4 * Real.log 12) 0 a ha
        simp only [Bool.false_eq_true, ↓reduceIte]
        filter_upwards [h] with d hd
        simpa using hd
    | true =>
        simp only [↓reduceIte]
        exact eventually_const_mul_rpow_le_rpow_real 12 b a hab

theorem failureBudgetRegistry_exists_cutoff
    (a b : ℝ) (ha : 0 < a) (hab : b < a) :
    ∃ d0 : ℝ, ∀ d, d0 ≤ d →
      12 * Real.rpow d b ≤ Real.rpow d a ∧
      4 * Real.log 12 ≤ Real.rpow d a := by
  let R := failureBudgetRegistry a b ha hab
  obtain ⟨d0, hd0⟩ := R.exists_cutoff
  refine ⟨d0, fun d hd => ?_⟩
  constructor
  · have h := hd0 d hd true (Finset.mem_univ true)
    simpa [R, failureBudgetRegistry] using h
  · have h := hd0 d hd false (Finset.mem_univ false)
    simpa [R, failureBudgetRegistry] using h

theorem exists_chernoffMcDiarmid_failureSum_cutoff
    {ιrel ιupper ιbd : Type*}
    [Fintype ιrel] [Fintype ιupper] [Fintype ιbd]
    (a b : ℝ) (ha : 0 < a) (hab : b < a) :
    ∃ d0 : ℝ, ∀ d, d0 ≤ d →
      ∀ (delta mean : ιrel → ℝ) (threshold : ιupper → ℝ)
        (gap influenceSq : ιbd → ℝ),
      (Fintype.card ιrel : ℝ) ≤ Real.exp (Real.rpow d b) →
      (Fintype.card ιupper : ℝ) ≤ Real.exp (Real.rpow d b) →
      (Fintype.card ιbd : ℝ) ≤ Real.exp (Real.rpow d b) →
      (∀ i, Real.rpow d a ≤ delta i ^ 2 * mean i) →
      (∀ i, Real.rpow d a ≤ threshold i) →
      (∀ i, Real.rpow d a / 3 ≤
        2 * gap i ^ 2 / influenceSq i) →
      (∑ i : ιrel,
          2 * Real.exp (-(delta i ^ 2 * mean i) / 3)) +
        (∑ i : ιupper, Real.exp (-threshold i / 3)) +
        (∑ i : ιbd,
          Real.exp (-2 * gap i ^ 2 / influenceSq i)) < 1 := by
  obtain ⟨d0, hd0⟩ := failureBudgetRegistry_exists_cutoff a b ha hab
  refine ⟨d0, ?_⟩
  intro d hd delta mean threshold gap influenceSq
    hcardRel hcardUpper hcardBd hzrel hzupper hzbd
  exact chernoffMcDiarmid_failureSum_lt_one_of_exp_card_bounds
    (Real.rpow d a) (Real.rpow d b) delta mean threshold gap influenceSq
    (hd0 d hd).1 (hd0 d hd).2 hcardRel hcardUpper hcardBd
    hzrel hzupper hzbd

/-- Scaled entropy is the form used when observable counts are bounded by
a fixed power of the host size. -/
def scaledFailureBudgetRegistry (K a b : ℝ) (ha : 0 < a) (hab : b < a) :
    LargeDRegistry Bool where
  active := Finset.univ
  condition i d := if i = true then
      12 * (K * Real.rpow d b) ≤ Real.rpow d a
    else
      4 * Real.log 12 ≤ Real.rpow d a
  eventually_condition := by
    intro i _hi
    cases i with
    | false =>
        have h := eventually_const_mul_rpow_le_rpow_real
          (4 * Real.log 12) 0 a ha
        simp only [Bool.false_eq_true, ↓reduceIte]
        filter_upwards [h] with d hd
        simpa using hd
    | true =>
        simp only [↓reduceIte]
        have h := eventually_const_mul_rpow_le_rpow_real (12 * K) b a hab
        filter_upwards [h] with d hd
        simpa only [mul_assoc] using hd

theorem scaledFailureBudgetRegistry_exists_cutoff
    (K a b : ℝ) (ha : 0 < a) (hab : b < a) :
    ∃ d0 : ℝ, ∀ d, d0 ≤ d →
      12 * (K * Real.rpow d b) ≤ Real.rpow d a ∧
      4 * Real.log 12 ≤ Real.rpow d a := by
  let R := scaledFailureBudgetRegistry K a b ha hab
  obtain ⟨d0, hd0⟩ := R.exists_cutoff
  refine ⟨d0, fun d hd => ?_⟩
  constructor
  · have h := hd0 d hd true (Finset.mem_univ true)
    simpa [R, scaledFailureBudgetRegistry] using h
  · have h := hd0 d hd false (Finset.mem_univ false)
    simpa [R, scaledFailureBudgetRegistry] using h

theorem exists_chernoffMcDiarmid_failureSum_scaledEntropy_cutoff
    {ιrel ιupper ιbd : Type*}
    [Fintype ιrel] [Fintype ιupper] [Fintype ιbd]
    (K a b : ℝ) (ha : 0 < a) (hab : b < a) :
    ∃ d0 : ℝ, ∀ d, d0 ≤ d →
      ∀ (delta mean : ιrel → ℝ) (threshold : ιupper → ℝ)
        (gap influenceSq : ιbd → ℝ),
      (Fintype.card ιrel : ℝ) ≤
        Real.exp (K * Real.rpow d b) →
      (Fintype.card ιupper : ℝ) ≤
        Real.exp (K * Real.rpow d b) →
      (Fintype.card ιbd : ℝ) ≤
        Real.exp (K * Real.rpow d b) →
      (∀ i, Real.rpow d a ≤ delta i ^ 2 * mean i) →
      (∀ i, Real.rpow d a ≤ threshold i) →
      (∀ i, Real.rpow d a / 3 ≤
        2 * gap i ^ 2 / influenceSq i) →
      (∑ i : ιrel,
          2 * Real.exp (-(delta i ^ 2 * mean i) / 3)) +
        (∑ i : ιupper, Real.exp (-threshold i / 3)) +
        (∑ i : ιbd,
          Real.exp (-2 * gap i ^ 2 / influenceSq i)) < 1 := by
  obtain ⟨d0, hd0⟩ :=
    scaledFailureBudgetRegistry_exists_cutoff K a b ha hab
  refine ⟨d0, ?_⟩
  intro d hd delta mean threshold gap influenceSq
    hcardRel hcardUpper hcardBd hzrel hzupper hzbd
  exact chernoffMcDiarmid_failureSum_lt_one_of_exp_card_bounds
    (Real.rpow d a) (K * Real.rpow d b) delta mean threshold gap influenceSq
    (hd0 d hd).1 (hd0 d hd).2 hcardRel hcardUpper hcardBd
    hzrel hzupper hzbd

end
/-! ### Weighted test loss in a source completion stage -/

theorem testExtension_eq_weight_of_subset_card
    (H : Hypergraph V) (j : ℕ) (w : TestWeight V)
    (root : Hypergraph V) (hroot : root ⊆ H) (hcard : root.card = j) :
    testExtension w H j root = w root := by
  rw [testExtension]
  have hfilter :
      (H.powersetCard j).filter (root ⊆ ·) = {root} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hSH, hScard⟩, hrootS⟩
      exact (Finset.eq_of_subset_of_card_le hrootS
        (by rw [hcard, hScard])).symm
    · rintro rfl
      exact ⟨⟨hroot, hcard⟩, Finset.Subset.rfl⟩
  rw [hfilter]
  simp

theorem testExtension_eq_zero_of_test_card_lt_root
    (H : Hypergraph V) (j : ℕ) (w : TestWeight V)
    (root : Hypergraph V) (hcard : j < root.card) :
    testExtension w H j root = 0 := by
  rw [testExtension]
  apply Finset.sum_eq_zero
  intro S hS
  obtain ⟨hSpow, hrootS⟩ := Finset.mem_filter.mp hS
  have hrootcard : root.card ≤ S.card := Finset.card_le_card hrootS
  have hScard : S.card = j := (Finset.mem_powersetCard.mp hSpow).2
  omega

theorem testWeight_le_testExtension
    (H : Hypergraph V) (j : ℕ) (w : TestWeight V)
    (hw : ∀ T, 0 ≤ w T) (root S : Hypergraph V)
    (hS : S ∈ H.powersetCard j) (hrootS : root ⊆ S) :
    w S ≤ testExtension w H j root := by
  rw [testExtension]
  exact Finset.single_le_sum
    (fun T _hT => hw T) (Finset.mem_filter.mpr ⟨hS, hrootS⟩)

theorem card_candidates_contained_le_two_pow {n : ℕ}
    (candidate : Fin n → Hypergraph V)
    (hinj : Function.Injective candidate) (S : Hypergraph V) :
    ((Finset.univ.filter fun i => candidate i ⊆ S).card : ℝ) ≤
      (2 : ℝ) ^ S.card := by
  let I : Finset (Fin n) :=
    Finset.univ.filter fun i => candidate i ⊆ S
  have himage : I.image candidate ⊆ S.powerset := by
    intro A hA
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hA
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hiI).2
  have hcard : I.card ≤ S.powerset.card := by
    rw [← Finset.card_image_of_injective I hinj]
    exact Finset.card_le_card himage
  have hcard' : I.card ≤ 2 ^ S.card := by
    simpa only [Finset.card_powerset] using hcard
  exact_mod_cast hcard'

theorem sum_testExtension_le_two_pow_mul_total {n : ℕ}
    (H : Hypergraph V) (testJ : ℕ) (w : TestWeight V)
    (candidate : Fin n → Hypergraph V)
    (hinj : Function.Injective candidate)
    (hw : ∀ S, 0 ≤ w S) :
    (∑ i, testExtension w H testJ (candidate i)) ≤
      (2 : ℝ) ^ testJ * testTotal w H testJ := by
  simp only [testExtension, testTotal, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ S ∈ H.powersetCard testJ,
        ∑ i, if candidate i ⊆ S then w S else 0) =
        ∑ S ∈ H.powersetCard testJ,
          ((Finset.univ.filter fun i => candidate i ⊆ S).card : ℝ) * w S := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ S ∈ H.powersetCard testJ, (2 : ℝ) ^ testJ * w S := by
      apply Finset.sum_le_sum
      intro S hS
      have hcardS : S.card = testJ := (Finset.mem_powersetCard.mp hS).2
      have hc := card_candidates_contained_le_two_pow candidate hinj S
      rw [hcardS] at hc
      exact mul_le_mul_of_nonneg_right hc (hw S)
    _ = (2 : ℝ) ^ testJ * ∑ S ∈ H.powersetCard testJ, w S := by
      rw [Finset.mul_sum]

theorem weightedMean_sampledKilledWeight_le_pmax_mul_sumExtension {n : ℕ}
    (H : Hypergraph V) (testJ : ℕ) (w : TestWeight V)
    (candidate : Fin n → Hypergraph V) (p : Fin n → ℝ)
    (pmax : ℝ) (hw : ∀ S, 0 ≤ w S)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i, p i ≤ pmax) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (sampledKilledWeight H testJ w candidate) ≤
      pmax * ∑ i, testExtension w H testJ (candidate i) := by
  calc
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (sampledKilledWeight H testJ w candidate) ≤
        ∑ i, p i * testExtension w H testJ (candidate i) :=
      weightedMean_sampledKilledWeight_le H testJ w candidate p hw hp
    _ ≤ ∑ i, pmax * testExtension w H testJ (candidate i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hpmax i)
        (testExtension_nonneg hw H testJ (candidate i))
    _ = pmax * ∑ i, testExtension w H testJ (candidate i) := by
      rw [Finset.mul_sum]

theorem weightedMean_sampledKilledWeight_le_pmax_mul_two_pow_total {n : ℕ}
    (H : Hypergraph V) (testJ : ℕ) (w : TestWeight V)
    (candidate : Fin n → Hypergraph V)
    (hinj : Function.Injective candidate) (p : Fin n → ℝ)
    (pmax : ℝ) (hw : ∀ S, 0 ≤ w S)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i, p i ≤ pmax) (hpmax0 : 0 ≤ pmax) :
    McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
        (sampledKilledWeight H testJ w candidate) ≤
      pmax * ((2 : ℝ) ^ testJ * testTotal w H testJ) := by
  exact (weightedMean_sampledKilledWeight_le_pmax_mul_sumExtension
    H testJ w candidate p pmax hw hp hpmax).trans
      (mul_le_mul_of_nonneg_left
        (sum_testExtension_le_two_pow_mul_total H testJ w candidate hinj hw)
        hpmax0)

theorem sum_sq_testExtension_le_upper_mul_two_pow_total {n : ℕ}
    (H : Hypergraph V) (testJ : ℕ) (w : TestWeight V)
    (candidate : Fin n → Hypergraph V)
    (hinj : Function.Injective candidate) (U : ℝ)
    (hw : ∀ S, 0 ≤ w S) (hU0 : 0 ≤ U)
    (hU : ∀ i, testExtension w H testJ (candidate i) ≤ U) :
    (∑ i, (testExtension w H testJ (candidate i)) ^ 2) ≤
      U * ((2 : ℝ) ^ testJ * testTotal w H testJ) := by
  calc
    (∑ i, (testExtension w H testJ (candidate i)) ^ 2) ≤
        U * ∑ i, testExtension w H testJ (candidate i) := by
      simpa only [Finset.sum_attach, Finset.mem_univ] using
        sum_sq_le_upper_mul_sum (Finset.univ : Finset (Fin n))
          (fun i => testExtension w H testJ (candidate i)) U
          (fun i _ => testExtension_nonneg hw H testJ (candidate i))
          (fun i _ => hU i)
    _ ≤ U * ((2 : ℝ) ^ testJ * testTotal w H testJ) := by
      exact mul_le_mul_of_nonneg_left
        (sum_testExtension_le_two_pow_mul_total H testJ w candidate hinj hw)
        hU0

theorem two_pow_le_sixteen_of_le_four (j : ℕ) (hj : j ≤ 4) :
    (2 : ℝ) ^ j ≤ 16 := by
  have hnat : 2 ^ j ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hj
  norm_num at hnat ⊢
  exact_mod_cast hnat

theorem trackable_root_extension_le_four_mul_ratio
    {H : Hypergraph V} {C : ConflictSystem V}
    {testJ : ℕ} {d eps : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C testJ 4 d eps w)
    (hd : 0 < d) (stage : ℕ) (hstage : 1 ≤ stage)
    (root : Hypergraph V) (hroot : root ⊆ H)
    (hrootcard : root.card = stage) :
    testExtension w H testJ root ≤
      4 * (testTotal w H testJ /
        Real.rpow d ((stage : ℝ) + eps)) := by
  have hden : 0 < Real.rpow d ((stage : ℝ) + eps) :=
    Real.rpow_pos_of_pos hd _
  have htotal0 : 0 ≤ testTotal w H testJ :=
    testTotal_nonneg hw.isTestFunction.nonneg H testJ
  have hratio0 :
      0 ≤ testTotal w H testJ /
        Real.rpow d ((stage : ℝ) + eps) :=
    div_nonneg htotal0 hden.le
  rcases lt_trichotomy stage testJ with hlt | heq | hgt
  · exact (hw.extension_upper hstage hlt root hroot hrootcard).trans
      (by nlinarith)
  · subst testJ
    rw [testExtension_eq_weight_of_subset_card H stage w root hroot hrootcard]
    have hwroot : w root ≤ 4 := by
      simpa using hw.isTestFunction.le root
    have hratio1 :
        1 ≤ testTotal w H stage /
          Real.rpow d ((stage : ℝ) + eps) := by
      rw [le_div_iff₀ hden]
      simpa using hw.total_lower
    nlinarith
  · have hz : testExtension w H testJ root = 0 :=
      testExtension_eq_zero_of_test_card_lt_root H testJ w root
        (by simpa [hrootcard] using hgt)
    rw [hz]
    positivity

theorem trackable_sum_sq_completionCandidate_le
    (H : Hypergraph V) (Ccurrent Ctest : ConflictSystem V)
    (testJ stage : ℕ) (d eps : ℝ) (w : TestWeight V)
    (hw : IsTrackable H Ctest testJ 4 d eps w)
    (hd : 0 < d) (hstage : 1 ≤ stage) :
    (∑ i, (testExtension w H testJ
      (completionCandidate H Ccurrent stage i)) ^ 2) ≤
      (4 * (testTotal w H testJ /
          Real.rpow d ((stage : ℝ) + eps))) *
        ((2 : ℝ) ^ testJ * testTotal w H testJ) := by
  let candidate := completionCandidate H Ccurrent stage
  have hU0 : 0 ≤ 4 * (testTotal w H testJ /
      Real.rpow d ((stage : ℝ) + eps)) := by
    have ht := testTotal_nonneg hw.isTestFunction.nonneg H testJ
    have hd' : 0 ≤ Real.rpow d ((stage : ℝ) + eps) :=
      (Real.rpow_pos_of_pos hd _).le
    positivity
  apply sum_sq_testExtension_le_upper_mul_two_pow_total
    H testJ w candidate (completionCandidate_injective H Ccurrent stage)
    _ hw.isTestFunction.nonneg hU0
  intro i
  have hi := mem_completionCandidates.mp
    (completionCandidate_mem H Ccurrent stage i)
  exact trackable_root_extension_le_four_mul_ratio hw hd stage hstage
    (candidate i) hi.1 hi.2.1

theorem trackable_sum_sq_completionCandidate_le_sixtyFour
    (H : Hypergraph V) (Ccurrent Ctest : ConflictSystem V)
    (testJ stage : ℕ) (d eps : ℝ) (w : TestWeight V)
    (hw : IsTrackable H Ctest testJ 4 d eps w)
    (hd : 0 < d) (hstage : 1 ≤ stage) (htestJ : testJ ≤ 4) :
    (∑ i, (testExtension w H testJ
      (completionCandidate H Ccurrent stage i)) ^ 2) ≤
      64 * (testTotal w H testJ) ^ 2 /
        Real.rpow d ((stage : ℝ) + eps) := by
  have hbase := trackable_sum_sq_completionCandidate_le
    H Ccurrent Ctest testJ stage d eps w hw hd hstage
  have hpow := two_pow_le_sixteen_of_le_four testJ htestJ
  have ht0 : 0 ≤ testTotal w H testJ :=
    testTotal_nonneg hw.isTestFunction.nonneg H testJ
  have hden : 0 < Real.rpow d ((stage : ℝ) + eps) :=
    Real.rpow_pos_of_pos hd _
  calc
    (∑ i, (testExtension w H testJ
      (completionCandidate H Ccurrent stage i)) ^ 2) ≤
        (4 * (testTotal w H testJ /
          Real.rpow d ((stage : ℝ) + eps))) *
          ((2 : ℝ) ^ testJ * testTotal w H testJ) := hbase
    _ ≤ (4 * (testTotal w H testJ /
          Real.rpow d ((stage : ℝ) + eps))) *
          (16 * testTotal w H testJ) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right hpow ht0
      · positivity
    _ = 64 * (testTotal w H testJ) ^ 2 /
          Real.rpow d ((stage : ℝ) + eps) := by
      field_simp
      ring

theorem weightedMean_sourceKilledWeight_le_sixteen_mul
    (H : Hypergraph V) (C : ConflictSystem V)
    (testJ stage : ℕ) (target pmax : ℝ) (w : TestWeight V)
    (hw : ∀ S, 0 ≤ w S)
    (hp : ∀ i, sourceCompletionBiasAtTarget H C stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i,
      sourceCompletionBiasAtTarget H C stage target i ≤ pmax)
    (hpmax0 : 0 ≤ pmax) (htestJ : testJ ≤ 4) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight
          (sourceCompletionBiasAtTarget H C stage target))
        (sampledKilledWeight H testJ w
          (completionCandidate H C stage)) ≤
      16 * pmax * testTotal w H testJ := by
  have h :=
    weightedMean_sampledKilledWeight_le_pmax_mul_two_pow_total
      H testJ w (completionCandidate H C stage)
      (completionCandidate_injective H C stage)
      (sourceCompletionBiasAtTarget H C stage target)
      pmax hw hp hpmax hpmax0
  have hpow := two_pow_le_sixteen_of_le_four testJ htestJ
  have ht0 := testTotal_nonneg hw H testJ
  calc
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight
          (sourceCompletionBiasAtTarget H C stage target))
        (sampledKilledWeight H testJ w
          (completionCandidate H C stage)) ≤
        pmax * ((2 : ℝ) ^ testJ * testTotal w H testJ) := h
    _ ≤ pmax * (16 * testTotal w H testJ) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow ht0) hpmax0
    _ = 16 * pmax * testTotal w H testJ := by ring

/-- Property-(VI) threshold used after completion stage `stage`. -/
noncomputable def stageKilledWeightLimit
    (stage : ℕ) (d eps total : ℝ) : ℝ :=
  (4 : ℝ) ^ stage * total / Real.rpow d (2 * eps)

/-- The McDiarmid deviation is half the final property-(VI) threshold. -/
noncomputable def stageKilledWeightGap
    (stage : ℕ) (d eps total : ℝ) : ℝ :=
  stageKilledWeightLimit stage d eps total / 2

theorem stageKilledWeightGap_nonneg (stage : ℕ) {d eps total : ℝ}
    (hd : 0 < d) (htotal : 0 ≤ total) :
    0 ≤ stageKilledWeightGap stage d eps total := by
  unfold stageKilledWeightGap stageKilledWeightLimit
  exact div_nonneg
    (div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) htotal)
      (Real.rpow_nonneg hd.le _)) (by norm_num)

theorem mean_add_stageKilledWeightGap_le_limit
    (stage : ℕ) (d eps total mean : ℝ)
    (hmean : mean ≤ stageKilledWeightGap stage d eps total) :
    mean + stageKilledWeightGap stage d eps total ≤
      stageKilledWeightLimit stage d eps total := by
  calc
    mean + stageKilledWeightGap stage d eps total ≤
        stageKilledWeightGap stage d eps total +
          stageKilledWeightGap stage d eps total :=
      add_le_add_left hmean _
    _ = stageKilledWeightLimit stage d eps total := by
      unfold stageKilledWeightGap
      ring

theorem weightedMean_sourceKilledWeight_le_stageGap
    (H : Hypergraph V) (C : ConflictSystem V)
    (testJ stage : ℕ) (d eps target pmax : ℝ) (w : TestWeight V)
    (hw : ∀ S, 0 ≤ w S)
    (hp : ∀ i, sourceCompletionBiasAtTarget H C stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i,
      sourceCompletionBiasAtTarget H C stage target i ≤ pmax)
    (hpmax0 : 0 ≤ pmax) (htestJ : testJ ≤ 4)
    (hcoefficient :
      16 * pmax ≤ (4 : ℝ) ^ stage /
        (2 * Real.rpow d (2 * eps))) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight
          (sourceCompletionBiasAtTarget H C stage target))
        (sampledKilledWeight H testJ w
          (completionCandidate H C stage)) ≤
      stageKilledWeightGap stage d eps (testTotal w H testJ) := by
  have hmean := weightedMean_sourceKilledWeight_le_sixteen_mul
    H C testJ stage target pmax w hw hp hpmax hpmax0 htestJ
  have ht0 := testTotal_nonneg hw H testJ
  calc
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight
          (sourceCompletionBiasAtTarget H C stage target))
        (sampledKilledWeight H testJ w
          (completionCandidate H C stage)) ≤
        16 * pmax * testTotal w H testJ := hmean
    _ ≤ ((4 : ℝ) ^ stage /
          (2 * Real.rpow d (2 * eps))) * testTotal w H testJ :=
      mul_le_mul_of_nonneg_right hcoefficient ht0
    _ = stageKilledWeightGap stage d eps (testTotal w H testJ) := by
      unfold stageKilledWeightGap stageKilledWeightLimit
      ring

theorem weightedMean_sourceKilledWeight_add_gap_le_limit
    (H : Hypergraph V) (C : ConflictSystem V)
    (testJ stage : ℕ) (d eps target pmax : ℝ) (w : TestWeight V)
    (hw : ∀ S, 0 ≤ w S)
    (hp : ∀ i, sourceCompletionBiasAtTarget H C stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i,
      sourceCompletionBiasAtTarget H C stage target i ≤ pmax)
    (hpmax0 : 0 ≤ pmax) (htestJ : testJ ≤ 4)
    (hcoefficient :
      16 * pmax ≤ (4 : ℝ) ^ stage /
        (2 * Real.rpow d (2 * eps))) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight
          (sourceCompletionBiasAtTarget H C stage target))
        (sampledKilledWeight H testJ w
          (completionCandidate H C stage)) +
        stageKilledWeightGap stage d eps (testTotal w H testJ) ≤
      stageKilledWeightLimit stage d eps (testTotal w H testJ) := by
  apply mean_add_stageKilledWeightGap_le_limit
  exact weightedMean_sourceKilledWeight_le_stageGap
    H C testJ stage d eps target pmax w hw hp hpmax hpmax0 htestJ hcoefficient

theorem trackable_sum_sq_completionCandidate_le_total_sq_div_d
    (H : Hypergraph V) (Ccurrent Ctest : ConflictSystem V)
    (testJ stage : ℕ) (d eps : ℝ) (w : TestWeight V)
    (hw : IsTrackable H Ctest testJ 4 d eps w)
    (hd : 0 < d) (hstage : 1 ≤ stage) (htestJ : testJ ≤ 4)
    (habsorb : 64 * d ≤ Real.rpow d ((stage : ℝ) + eps)) :
    (∑ i, (testExtension w H testJ
      (completionCandidate H Ccurrent stage i)) ^ 2) ≤
      (testTotal w H testJ) ^ 2 / d := by
  have hraw := trackable_sum_sq_completionCandidate_le_sixtyFour
    H Ccurrent Ctest testJ stage d eps w hw hd hstage htestJ
  have ht2 : 0 ≤ (testTotal w H testJ) ^ 2 := sq_nonneg _
  have hden : 0 < Real.rpow d ((stage : ℝ) + eps) :=
    Real.rpow_pos_of_pos hd _
  calc
    (∑ i, (testExtension w H testJ
      (completionCandidate H Ccurrent stage i)) ^ 2) ≤
        64 * (testTotal w H testJ) ^ 2 /
          Real.rpow d ((stage : ℝ) + eps) := hraw
    _ ≤ (testTotal w H testJ) ^ 2 / d := by
      rw [div_le_div_iff₀ hden hd]
      have hm := mul_le_mul_of_nonneg_left habsorb ht2
      nlinarith

theorem two_pow_le_eight_of_le_three (j : ℕ) (hj : j ≤ 3) :
    (2 : ℝ) ^ j ≤ 8 := by
  have hnat : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj
  norm_num at hnat ⊢
  exact_mod_cast hnat

theorem trackable_root_extension_le_ell_mul_ratio
    {H : Hypergraph V} {C : ConflictSystem V}
    {testJ ell : ℕ} {d eps : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C testJ ell d eps w)
    (hell : 1 ≤ ell) (hd : 0 < d) (stage : ℕ) (hstage : 1 ≤ stage)
    (root : Hypergraph V) (hroot : root ⊆ H)
    (hrootcard : root.card = stage) :
    testExtension w H testJ root ≤
      (ell : ℝ) * (testTotal w H testJ /
        Real.rpow d ((stage : ℝ) + eps)) := by
  have hden : 0 < Real.rpow d ((stage : ℝ) + eps) :=
    Real.rpow_pos_of_pos hd _
  have htotal0 : 0 ≤ testTotal w H testJ :=
    testTotal_nonneg hw.isTestFunction.nonneg H testJ
  have hratio0 :
      0 ≤ testTotal w H testJ /
        Real.rpow d ((stage : ℝ) + eps) :=
    div_nonneg htotal0 hden.le
  have hellReal : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
  rcases lt_trichotomy stage testJ with hlt | heq | hgt
  · exact (hw.extension_upper hstage hlt root hroot hrootcard).trans
      (by nlinarith)
  · subst testJ
    rw [testExtension_eq_weight_of_subset_card H stage w root hroot hrootcard]
    have hwroot : w root ≤ (ell : ℝ) := by
      simpa using hw.isTestFunction.le root
    have hratio1 :
        1 ≤ testTotal w H stage /
          Real.rpow d ((stage : ℝ) + eps) := by
      rw [le_div_iff₀ hden]
      simpa using hw.total_lower
    nlinarith [mul_le_mul_of_nonneg_left hratio1 (by positivity : (0 : ℝ) ≤ ell)]
  · have hz : testExtension w H testJ root = 0 :=
      testExtension_eq_zero_of_test_card_lt_root H testJ w root
        (by simpa [hrootcard] using hgt)
    rw [hz]
    positivity

theorem trackable_sum_sq_completionCandidate_le_total_sq_div_d_of_ell
    (H : Hypergraph V) (Ccurrent Ctest : ConflictSystem V)
    (testJ ell stage : ℕ) (d eps : ℝ) (w : TestWeight V)
    (hw : IsTrackable H Ctest testJ ell d eps w)
    (hell : 1 ≤ ell) (hd : 0 < d) (hstage : 1 ≤ stage)
    (htestJ : testJ ≤ 3)
    (habsorb : 8 * (ell : ℝ) * d ≤
      Real.rpow d ((stage : ℝ) + eps)) :
    (∑ i, (testExtension w H testJ
      (completionCandidate H Ccurrent stage i)) ^ 2) ≤
      (testTotal w H testJ) ^ 2 / d := by
  let candidate := completionCandidate H Ccurrent stage
  have hU0 : 0 ≤ (ell : ℝ) * (testTotal w H testJ /
      Real.rpow d ((stage : ℝ) + eps)) := by
    have ht0 : 0 ≤ testTotal w H testJ :=
      testTotal_nonneg hw.isTestFunction.nonneg H testJ
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg ht0 (Real.rpow_nonneg hd.le _))
  have hbase :
      (∑ i, (testExtension w H testJ (candidate i)) ^ 2) ≤
        ((ell : ℝ) * (testTotal w H testJ /
          Real.rpow d ((stage : ℝ) + eps))) *
          ((2 : ℝ) ^ testJ * testTotal w H testJ) := by
    apply sum_sq_testExtension_le_upper_mul_two_pow_total
      H testJ w candidate (completionCandidate_injective H Ccurrent stage)
      _ hw.isTestFunction.nonneg hU0
    intro i
    have hi := mem_completionCandidates.mp
      (completionCandidate_mem H Ccurrent stage i)
    exact trackable_root_extension_le_ell_mul_ratio hw hell hd stage hstage
      (candidate i) hi.1 hi.2.1
  have hpow := two_pow_le_eight_of_le_three testJ htestJ
  have ht0 : 0 ≤ testTotal w H testJ :=
    testTotal_nonneg hw.isTestFunction.nonneg H testJ
  have ht2 : 0 ≤ (testTotal w H testJ) ^ 2 := sq_nonneg _
  have hden : 0 < Real.rpow d ((stage : ℝ) + eps) :=
    Real.rpow_pos_of_pos hd _
  calc
    (∑ i, (testExtension w H testJ
      (completionCandidate H Ccurrent stage i)) ^ 2) ≤
        ((ell : ℝ) * (testTotal w H testJ /
          Real.rpow d ((stage : ℝ) + eps))) *
          ((2 : ℝ) ^ testJ * testTotal w H testJ) := hbase
    _ ≤ ((ell : ℝ) * (testTotal w H testJ /
          Real.rpow d ((stage : ℝ) + eps))) *
          (8 * testTotal w H testJ) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right hpow ht0
      · positivity
    _ = (8 * (ell : ℝ)) * (testTotal w H testJ) ^ 2 /
          Real.rpow d ((stage : ℝ) + eps) := by
      field_simp
    _ ≤ (testTotal w H testJ) ^ 2 / d := by
      rw [div_le_div_iff₀ hden hd]
      have hm := mul_le_mul_of_nonneg_right habsorb ht2
      nlinarith

theorem stageKilledWeightGap_mcdiarmid_scale
    (stage : ℕ) {d eps total influenceSq : ℝ}
    (hd : 0 < d) (htotal : 0 < total) (hinfluence : 0 < influenceSq)
    (hinfluenceUpper : influenceSq ≤ total ^ 2 / d) :
    ((4 : ℝ) ^ stage) ^ 2 / 2 * Real.rpow d (1 - 4 * eps) ≤
      2 * (stageKilledWeightGap stage d eps total) ^ 2 / influenceSq := by
  have htotalSqDiv : 0 < total ^ 2 / d := by positivity
  have hgapSq : 0 ≤ 2 * (stageKilledWeightGap stage d eps total) ^ 2 := by
    positivity
  have hcompare :
      2 * (stageKilledWeightGap stage d eps total) ^ 2 /
          (total ^ 2 / d) ≤
        2 * (stageKilledWeightGap stage d eps total) ^ 2 /
          influenceSq :=
    div_le_div_of_nonneg_left hgapSq hinfluence hinfluenceUpper
  have hrpow : 0 < Real.rpow d (2 * eps) :=
    Real.rpow_pos_of_pos hd _
  have hrpowSq :
      (Real.rpow d (2 * eps)) ^ 2 = Real.rpow d (4 * eps) := by
    calc
      (Real.rpow d (2 * eps)) ^ 2 =
          Real.rpow (Real.rpow d (2 * eps)) (2 : ℝ) := by
        exact (Real.rpow_natCast (Real.rpow d (2 * eps)) 2).symm
      _ = Real.rpow d ((2 * eps) * 2) :=
        (Real.rpow_mul hd.le (2 * eps) 2).symm
      _ = Real.rpow d (4 * eps) := by
        exact congrArg (Real.rpow d) (by ring)
  have hquot : d / Real.rpow d (4 * eps) =
      Real.rpow d (1 - 4 * eps) := by
    have h := Real.rpow_sub hd 1 (4 * eps)
    rw [Real.rpow_one] at h
    exact h.symm
  calc
    ((4 : ℝ) ^ stage) ^ 2 / 2 * Real.rpow d (1 - 4 * eps) =
        2 * (stageKilledWeightGap stage d eps total) ^ 2 /
          (total ^ 2 / d) := by
      rw [← hquot, ← hrpowSq]
      unfold stageKilledWeightGap stageKilledWeightLimit
      field_simp
    _ ≤ 2 * (stageKilledWeightGap stage d eps total) ^ 2 /
          influenceSq := hcompare

theorem stageKilledWeightGap_mcdiarmid_scale_relaxed
    (stage : ℕ) {d eps total influenceSq : ℝ}
    (hd : 0 < d) (htotal : 0 < total) (hinfluence : 0 < influenceSq)
    (hinfluenceUpper : influenceSq ≤ total ^ 2 / d) :
    (4 : ℝ) ^ stage / 2 * Real.rpow d (1 - 4 * eps) ≤
      2 * (stageKilledWeightGap stage d eps total) ^ 2 / influenceSq := by
  apply (mul_le_mul_of_nonneg_right ?_
    (Real.rpow_nonneg hd.le _)).trans
    (stageKilledWeightGap_mcdiarmid_scale stage hd htotal hinfluence
      hinfluenceUpper)
  have hpow : 1 ≤ (4 : ℝ) ^ stage := by
    exact one_le_pow₀ (by norm_num)
  nlinarith [sq_nonneg ((4 : ℝ) ^ stage - 1)]

theorem trackable_completionCandidate_influenceSq_pos
    (H : Hypergraph V) (Ccurrent Ctest : ConflictSystem V)
    (testJ stage : ℕ) (d eps : ℝ) (w : TestWeight V)
    (hw : IsTrackable H Ctest testJ 4 d eps w)
    (hd : 0 < d) (hstage : stage ≤ testJ)
    (hfree : ∀ S ∈ H.powersetCard testJ, 0 < w S →
      ConflictFree Ccurrent S) :
    0 < ∑ i, (testExtension w H testJ
      (completionCandidate H Ccurrent stage i)) ^ 2 := by
  have htotal : 0 < testTotal w H testJ :=
    (Real.rpow_pos_of_pos hd ((testJ : ℝ) + eps)).trans_le hw.total_lower
  have htotal' : 0 < ∑ S ∈ H.powersetCard testJ, w S := by
    simpa [testTotal] using htotal
  obtain ⟨S, hS, hwS⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (s := H.powersetCard testJ)
      (f := w) (fun S _ => hw.isTestFunction.nonneg S)).mp htotal'
  have hScard : S.card = testJ := (Finset.mem_powersetCard.mp hS).2
  obtain ⟨root, hrootS, hrootcard⟩ :=
    Finset.exists_subset_card_eq (s := S)
      (by simpa [hScard] using hstage)
  have hmatchS : IsMatching H S := by
    by_contra hn
    have hz := hw.isTestFunction.eq_zero_of_not_matching hn
    linarith
  have hrootmem : root ∈ completionCandidates H Ccurrent stage := by
    rw [mem_completionCandidates]
    exact ⟨hrootS.trans (Finset.mem_powersetCard.mp hS).1,
      hrootcard, hmatchS.mono hrootS,
      (hfree S hS hwS).mono_family hrootS⟩
  let q : CompletionIndex H Ccurrent stage := ⟨root, hrootmem⟩
  let i : Fin (Fintype.card (CompletionIndex H Ccurrent stage)) :=
    Fintype.equivFin (CompletionIndex H Ccurrent stage) q
  have hcand : completionCandidate H Ccurrent stage i = root := by
    simp [completionCandidate, i, q]
  have hext : 0 < testExtension w H testJ
      (completionCandidate H Ccurrent stage i) := by
    rw [hcand]
    exact hwS.trans_le
      (testWeight_le_testExtension H testJ w hw.isTestFunction.nonneg
        root S hS hrootS)
  apply Finset.sum_pos'
  · intro a ha
    positivity
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    positivity

theorem trackable_completionCandidate_influenceSq_pos_of_freeZero
    (H : Hypergraph V) (Ccurrent Ctest : ConflictSystem V)
    (testJ stage : ℕ) (d eps : ℝ) (w : TestWeight V)
    (hw : IsTrackable H Ctest testJ 4 d eps w)
    (hd : 0 < d) (hstage : stage ≤ testJ)
    (hfreeZero : ∀ S ∈ H.powersetCard testJ,
      (∃ c ∈ Ccurrent, c ⊆ S) → w S = 0) :
    0 < ∑ i, (testExtension w H testJ
      (completionCandidate H Ccurrent stage i)) ^ 2 := by
  apply trackable_completionCandidate_influenceSq_pos
    H Ccurrent Ctest testJ stage d eps w hw hd hstage
  intro S hS hwS
  intro c hc hsub
  have hz := hfreeZero S hS ⟨c, hc, hsub⟩
  linarith

theorem sampledKilledWeight_completionCandidate_eq_zero_of_test_card_lt_stage
    (H : Hypergraph V) (C : ConflictSystem V)
    (testJ stage : ℕ) (w : TestWeight V)
    (hcard : testJ < stage)
    (x : Fin (Fintype.card (CompletionIndex H C stage)) → Bool) :
    sampledKilledWeight H testJ w (completionCandidate H C stage) x = 0 := by
  rw [sampledKilledWeight]
  apply Finset.sum_eq_zero
  intro S hS
  have hScard : S.card = testJ := (Finset.mem_powersetCard.mp hS).2
  simp only [ite_eq_right_iff]
  rintro ⟨i, hxi, hiS⟩
  have histage : (completionCandidate H C stage i).card = stage :=
    (mem_completionCandidates.mp (completionCandidate_mem H C stage i)).2.1
  have hle := Finset.card_le_card hiS
  omega

theorem trackable_stageKilledWeightGap_mcdiarmid_scale
    (H : Hypergraph V) (Ccurrent Ctest : ConflictSystem V)
    (testJ stage : ℕ) (d eps : ℝ) (w : TestWeight V)
    (hw : IsTrackable H Ctest testJ 4 d eps w)
    (hd : 0 < d) (hstage1 : 1 ≤ stage) (hstageJ : stage ≤ testJ)
    (htestJ : testJ ≤ 4)
    (hfreeZero : ∀ S ∈ H.powersetCard testJ,
      (∃ c ∈ Ccurrent, c ⊆ S) → w S = 0)
    (habsorb : 64 * d ≤ Real.rpow d ((stage : ℝ) + eps)) :
    (4 : ℝ) ^ stage / 2 * Real.rpow d (1 - 4 * eps) ≤
      2 * (stageKilledWeightGap stage d eps (testTotal w H testJ)) ^ 2 /
        ∑ i, (testExtension w H testJ
          (completionCandidate H Ccurrent stage i)) ^ 2 := by
  have htotal : 0 < testTotal w H testJ :=
    (Real.rpow_pos_of_pos hd ((testJ : ℝ) + eps)).trans_le hw.total_lower
  have hpos := trackable_completionCandidate_influenceSq_pos_of_freeZero
    H Ccurrent Ctest testJ stage d eps w hw hd hstageJ hfreeZero
  have hupp := trackable_sum_sq_completionCandidate_le_total_sq_div_d
    H Ccurrent Ctest testJ stage d eps w hw hd hstage1 htestJ habsorb
  exact stageKilledWeightGap_mcdiarmid_scale_relaxed stage hd htotal hpos hupp

/-! ### Source forbidden-completion cardinal estimates -/

noncomputable section
 
def rootedJSets (H : Hypergraph V) (j : ℕ) (root : Hypergraph V) :
    Finset (Hypergraph V) :=
  (H.powersetCard j).filter (root ⊆ ·)

theorem sdiff_injective_on_rooted_family (root : Hypergraph V) :
    Set.InjOn (fun A : Hypergraph V => A \ root) {A | root ⊆ A} := by
  intro A hA B hB hEq
  ext e
  by_cases he : e ∈ root
  · exact iff_of_true (hA he) (hB he)
  · have hmem : e ∈ A \ root ↔ e ∈ B \ root := by
      change A \ root = B \ root at hEq
      rw [hEq]
    simpa [he] using hmem

theorem card_rootedJSets_le_choose (H : Hypergraph V) (j : ℕ)
    (root : Hypergraph V) (_hrootH : root ⊆ H) :
    (rootedJSets H j root).card ≤ Nat.choose H.card (j - root.card) := by
  let F := rootedJSets H j root
  let E := F.image fun A => A \ root
  have hinj : Set.InjOn (fun A : Hypergraph V => A \ root)
      (↑F : Set (Hypergraph V)) := by
    apply (sdiff_injective_on_rooted_family root).mono
    intro A hA
    exact (Finset.mem_filter.mp hA).2
  have hcardE : E.card = F.card := by
    simpa [E] using Finset.card_image_iff.mpr hinj
  have hsub : E ⊆ H.powersetCard (j - root.card) := by
    intro T hT
    obtain ⟨A, hAF, rfl⟩ := Finset.mem_image.mp hT
    have hAj : A ∈ H.powersetCard j := (Finset.mem_filter.mp hAF).1
    have hrootA : root ⊆ A := (Finset.mem_filter.mp hAF).2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · exact Finset.sdiff_subset.trans (Finset.mem_powersetCard.mp hAj).1
    · rw [Finset.card_sdiff_of_subset hrootA,
        (Finset.mem_powersetCard.mp hAj).2]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_powersetCard, hcardE] at hle
  simpa [F] using hle

theorem card_rootedJSets_le_pow (H : Hypergraph V) (j : ℕ)
    (root : Hypergraph V) (hrootH : root ⊆ H) :
    (rootedJSets H j root).card ≤ H.card ^ (j - root.card) :=
  (card_rootedJSets_le_choose H j root hrootH).trans
    (Nat.choose_le_pow H.card (j - root.card))

theorem card_rootCover_le
    (H : Hypergraph V) (j k : ℕ) (roots : Finset (Hypergraph V))
    (hroots : ∀ root ∈ roots, root ⊆ H ∧ root.card = k) :
    (roots.biUnion (rootedJSets H j)).card ≤
      roots.card * H.card ^ (j - k) := by
  calc
    (roots.biUnion (rootedJSets H j)).card ≤
        ∑ root ∈ roots, (rootedJSets H j root).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _root ∈ roots, H.card ^ (j - k) := by
      apply Finset.sum_le_sum
      intro root hroot
      have hr := hroots root hroot
      simpa [hr.2] using card_rootedJSets_le_pow H j root hr.1
    _ = _ := by simp

def meetingNeighbors (H : Hypergraph V) (e : Finset V) : Hypergraph V :=
  H.filter fun f => f ≠ e ∧ ¬ Disjoint e f

theorem meetingNeighbors_subset_starUnion (H : Hypergraph V) (e : Finset V) :
    meetingNeighbors H e ⊆ e.biUnion (fun v => H.filter fun f => v ∈ f) := by
  intro f hf
  have hf' := Finset.mem_filter.mp hf
  have hnd := hf'.2.2
  rw [Finset.not_disjoint_iff] at hnd
  obtain ⟨v, hve, hvf⟩ := hnd
  exact Finset.mem_biUnion.mpr
    ⟨v, hve, Finset.mem_filter.mpr ⟨hf'.1, hvf⟩⟩

theorem card_meetingNeighbors_le_eight_mul
    {H : Hypergraph V} {D : ℕ} (hmax : MaxDegreeLE H D)
    {e : Finset V} (hecard : e.card = 8) :
    (meetingNeighbors H e).card ≤ 8 * D := by
  calc
    (meetingNeighbors H e).card ≤
        (e.biUnion (fun v => H.filter fun f => v ∈ f)).card :=
      Finset.card_le_card (meetingNeighbors_subset_starUnion H e)
    _ ≤ ∑ v ∈ e, (H.filter fun f => v ∈ f).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ e, degree H v := by rfl
    _ ≤ ∑ _v ∈ e, D := by
      apply Finset.sum_le_sum
      intro v hv
      exact hmax v
    _ = 8 * D := by simp [hecard]

def meetingPairsAway (H : Hypergraph V) (e : Finset V) :
    Finset (Finset V × Finset V) :=
  (H.erase e).biUnion fun f =>
    ((meetingNeighbors H f).erase e).image fun g => (f, g)

theorem mem_meetingPairsAway
    {H : Hypergraph V} {e f g : Finset V}
    (hp : (f, g) ∈ meetingPairsAway H e) :
    f ∈ H ∧ g ∈ H ∧ f ≠ e ∧ g ≠ e ∧ f ≠ g ∧ ¬ Disjoint f g := by
  obtain ⟨f', hf', hp'⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨g', hg', hpair⟩ := Finset.mem_image.mp hp'
  rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
  have hfE := Finset.mem_erase.mp hf'
  have hgE := Finset.mem_erase.mp hg'
  have hgN := Finset.mem_filter.mp hgE.2
  exact ⟨hfE.2, hgN.1, hfE.1, hgE.1, hgN.2.1.symm, hgN.2.2⟩

theorem card_meetingPairsAway_le
    {H : Hypergraph V} {D : ℕ} (huniform : IsUniform H 8)
    (hmax : MaxDegreeLE H D) (e : Finset V) :
    (meetingPairsAway H e).card ≤ H.card * (8 * D) := by
  calc
    (meetingPairsAway H e).card ≤
        ∑ f ∈ H.erase e,
          (((meetingNeighbors H f).erase e).image fun g => (f, g)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ H.erase e, 8 * D := by
      apply Finset.sum_le_sum
      intro f hf
      calc
        (((meetingNeighbors H f).erase e).image fun g => (f, g)).card ≤
            ((meetingNeighbors H f).erase e).card := Finset.card_image_le
        _ ≤ (meetingNeighbors H f).card :=
          Finset.card_le_card (Finset.erase_subset _ _)
        _ ≤ 8 * D := card_meetingNeighbors_le_eight_mul hmax
          (huniform f (Finset.mem_erase.mp hf).2)
    _ ≤ ∑ _f ∈ H, 8 * D :=
      Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
    _ = H.card * (8 * D) := by simp

def nonmatchingIncidentSets (H : Hypergraph V) (j : ℕ) (e : Finset V) :
    Finset (Hypergraph V) :=
  (H.powersetCard j).filter fun A => e ∈ A ∧ ¬ IsMatching H A

def meetingPairRootsAt (H : Hypergraph V) (e : Finset V) :
    Finset (Hypergraph V) :=
  (meetingNeighbors H e).image fun f => {e, f}

def meetingTripleRootsAway (H : Hypergraph V) (e : Finset V) :
    Finset (Hypergraph V) :=
  (meetingPairsAway H e).image fun p => {e, p.1, p.2}

theorem meetingPairRootsAt_properties
    {H : Hypergraph V} {e : Finset V} (heH : e ∈ H) :
    ∀ root ∈ meetingPairRootsAt H e, root ⊆ H ∧ root.card = 2 := by
  intro root hroot
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hroot
  have hf' := Finset.mem_filter.mp hf
  constructor
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact heH
    · exact hf'.1
  · simp [Ne.symm hf'.2.1]

theorem meetingTripleRootsAway_properties
    {H : Hypergraph V} {e : Finset V} (heH : e ∈ H) :
    ∀ root ∈ meetingTripleRootsAway H e, root ⊆ H ∧ root.card = 3 := by
  intro root hroot
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hroot
  have hp' := mem_meetingPairsAway hp
  constructor
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact heH
    · exact hp'.1
    · exact hp'.2.1
  · have hef : e ≠ p.1 := Ne.symm hp'.2.2.1
    have heg : e ≠ p.2 := Ne.symm hp'.2.2.2.1
    have hfg : p.1 ≠ p.2 := hp'.2.2.2.2.1
    simp [hef, heg, hfg]

theorem nonmatchingIncidentSets_cover
    {H : Hypergraph V} {j : ℕ} {e : Finset V} (heH : e ∈ H) :
    nonmatchingIncidentSets H j e ⊆
      (meetingPairRootsAt H e).biUnion (rootedJSets H j) ∪
      (meetingTripleRootsAway H e).biUnion (rootedJSets H j) := by
  intro A hA
  have hAf := Finset.mem_filter.mp hA
  have hAH := (Finset.mem_powersetCard.mp hAf.1).1
  have hnotPD : ¬ PairwiseDisjoint A := fun hPD => hAf.2.2 ⟨hAH, hPD⟩
  simp only [PairwiseDisjoint] at hnotPD
  push Not at hnotPD
  obtain ⟨f, hfA, g, hgA, hfg, hmeet⟩ := hnotPD
  by_cases hfe : f = e
  · subst f
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨{e, g}, ?_, Finset.mem_filter.mpr ⟨hAf.1, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨g,
        Finset.mem_filter.mpr ⟨hAH hgA, hfg.symm, hmeet⟩, rfl⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hAf.2.1
      · exact hgA
  · by_cases hge : g = e
    · subst g
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨{e, f}, ?_, Finset.mem_filter.mpr ⟨hAf.1, ?_⟩⟩
      · exact Finset.mem_image.mpr ⟨f,
          Finset.mem_filter.mpr ⟨hAH hfA, hfe, fun hd => hmeet hd.symm⟩, rfl⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hAf.2.1
        · exact hfA
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨{e, f, g}, ?_, Finset.mem_filter.mpr ⟨hAf.1, ?_⟩⟩
      · apply Finset.mem_image.mpr
        refine ⟨(f, g), ?_, rfl⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨f, Finset.mem_erase.mpr ⟨hfe, hAH hfA⟩, ?_⟩
        apply Finset.mem_image.mpr
        refine ⟨g, Finset.mem_erase.mpr ⟨hge, ?_⟩, rfl⟩
        exact Finset.mem_filter.mpr ⟨hAH hgA, hfg.symm, hmeet⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hAf.2.1
        · exact hfA
        · exact hgA

 
theorem card_nonmatchingIncidentSets_le
    {H : Hypergraph V} {D j : ℕ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    {e : Finset V} (heH : e ∈ H) :
    (nonmatchingIncidentSets H j e).card ≤
      (8 * D) * H.card ^ (j - 2) +
        (H.card * (8 * D)) * H.card ^ (j - 3) := by
  calc
    (nonmatchingIncidentSets H j e).card ≤
        ((meetingPairRootsAt H e).biUnion (rootedJSets H j) ∪
          (meetingTripleRootsAway H e).biUnion (rootedJSets H j)).card :=
      Finset.card_le_card (nonmatchingIncidentSets_cover heH)
    _ ≤ ((meetingPairRootsAt H e).biUnion (rootedJSets H j)).card +
          ((meetingTripleRootsAway H e).biUnion (rootedJSets H j)).card :=
      Finset.card_union_le _ _
    _ ≤ (meetingPairRootsAt H e).card * H.card ^ (j - 2) +
          (meetingTripleRootsAway H e).card * H.card ^ (j - 3) :=
      Nat.add_le_add
        (card_rootCover_le H j 2 _ (meetingPairRootsAt_properties heH))
        (card_rootCover_le H j 3 _ (meetingTripleRootsAway_properties heH))
    _ ≤ (8 * D) * H.card ^ (j - 2) +
          (H.card * (8 * D)) * H.card ^ (j - 3) := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_right _
          (Finset.card_image_le.trans
            (card_meetingNeighbors_le_eight_mul hmax (huniform e heH)))
      · exact Nat.mul_le_mul_right _
          (Finset.card_image_le.trans
            (card_meetingPairsAway_le huniform hmax e))

def conflictRootsAt (C : ConflictSystem V) (r : ℕ) (e : Finset V) :
    Finset (Hypergraph V) :=
  (conflictLayer C r).filter (e ∈ ·)

def conflictRootsAwayAug (C : ConflictSystem V) (r : ℕ) (e : Finset V) :
    Finset (Hypergraph V) :=
  ((conflictLayer C r).filter (e ∉ ·)).image (insert e)

theorem card_conflictRootsAt_eq_degree
    (C : ConflictSystem V) (r : ℕ) (e : Finset V) :
    (conflictRootsAt C r e).card = degree (conflictLayer C r) e := by
  rfl

theorem vertexFinset_conflictLayer_subset_host
    {H : Hypergraph V} {C : ConflictSystem V}
    (hC : IsConflictSystem H C) (r : ℕ) :
    vertexFinset (conflictLayer C r) ⊆ H := by
  intro e he
  obtain ⟨c, hcLayer, hec⟩ := mem_vertexFinset.mp he
  exact hC c (mem_conflictLayer.mp hcLayer).1 hec

theorem card_conflictLayer_le_card_mul_degreeBound
    {H : Hypergraph V} {C : ConflictSystem V} {r Delta : ℕ}
    (hC : IsConflictSystem H C) (hr : 1 ≤ r)
    (hDelta : ∀ e ∈ H, degree (conflictLayer C r) e ≤ Delta) :
    (conflictLayer C r).card ≤ H.card * Delta := by
  have hsum := sum_degree_vertexFinset_of_uniform (conflictLayer_uniform C r)
  have hcard_le_sum : (conflictLayer C r).card ≤
      ∑ e ∈ vertexFinset (conflictLayer C r),
        degree (conflictLayer C r) e := by
    rw [hsum]
    calc
      (conflictLayer C r).card = 1 * (conflictLayer C r).card := by simp
      _ ≤ r * (conflictLayer C r).card := Nat.mul_le_mul_right _ hr
  calc
    (conflictLayer C r).card ≤
        ∑ e ∈ vertexFinset (conflictLayer C r),
          degree (conflictLayer C r) e := hcard_le_sum
    _ ≤ ∑ _e ∈ vertexFinset (conflictLayer C r), Delta := by
      apply Finset.sum_le_sum
      intro e he
      exact hDelta e (vertexFinset_conflictLayer_subset_host hC r he)
    _ = (vertexFinset (conflictLayer C r)).card * Delta := by simp
    _ ≤ H.card * Delta := Nat.mul_le_mul_right Delta
      (Finset.card_le_card (vertexFinset_conflictLayer_subset_host hC r))

theorem card_conflictRootsAwayAug_le
    {H : Hypergraph V} {C : ConflictSystem V} {r Delta : ℕ}
    (hC : IsConflictSystem H C) (hr : 1 ≤ r)
    (hDelta : ∀ e ∈ H, degree (conflictLayer C r) e ≤ Delta)
    (e : Finset V) :
    (conflictRootsAwayAug C r e).card ≤ H.card * Delta := by
  calc
    (conflictRootsAwayAug C r e).card ≤
        ((conflictLayer C r).filter (e ∉ ·)).card := Finset.card_image_le
    _ ≤ (conflictLayer C r).card := Finset.card_filter_le _ _
    _ ≤ H.card * Delta :=
      card_conflictLayer_le_card_mul_degreeBound hC hr hDelta

theorem conflictRootsAt_properties
    {H : Hypergraph V} {C : ConflictSystem V} (hC : IsConflictSystem H C)
    {r : ℕ} {e : Finset V} :
    ∀ root ∈ conflictRootsAt C r e, root ⊆ H ∧ root.card = r := by
  intro root hroot
  have hr := Finset.mem_filter.mp hroot
  exact ⟨hC root (mem_conflictLayer.mp hr.1).1,
    (mem_conflictLayer.mp hr.1).2⟩

theorem conflictRootsAwayAug_properties
    {H : Hypergraph V} {C : ConflictSystem V} (hC : IsConflictSystem H C)
    {r : ℕ} {e : Finset V} (heH : e ∈ H) :
    ∀ root ∈ conflictRootsAwayAug C r e,
      root ⊆ H ∧ root.card = r + 1 := by
  intro root hroot
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hroot
  have hc' := Finset.mem_filter.mp hc
  have hcLayer := mem_conflictLayer.mp hc'.1
  constructor
  · intro f hf
    simp only [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact heH
    · exact hC c hcLayer.1 hf
  · rw [Finset.card_insert_of_notMem hc'.2, hcLayer.2]

def unsafeIncidentSets (H : Hypergraph V) (C : ConflictSystem V)
    (j : ℕ) (e : Finset V) : Finset (Hypergraph V) :=
  (H.powersetCard j).filter fun A =>
    e ∈ A ∧ ∃ c ∈ C, c ⊆ A

theorem unsafeIncidentSets_cover_two
    {H : Hypergraph V} {C : ConflictSystem V} {e : Finset V}
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4) :
    unsafeIncidentSets H C 2 e ⊆
      (conflictRootsAt C 2 e).biUnion (rootedJSets H 2) := by
  intro A hA
  have hAf := Finset.mem_filter.mp hA
  obtain ⟨c, hcC, hcA⟩ := hAf.2.2
  have hAcard := (Finset.mem_powersetCard.mp hAf.1).2
  have hcge := (hcard c hcC).1
  have hccard : c.card = 2 := by
    have := Finset.card_le_card hcA
    omega
  have hcEq : c = A := Finset.eq_of_subset_of_card_le hcA (by omega)
  have hec : e ∈ c := hcEq.symm ▸ hAf.2.1
  exact Finset.mem_biUnion.mpr ⟨c,
    Finset.mem_filter.mpr ⟨mem_conflictLayer.mpr ⟨hcC, hccard⟩, hec⟩,
    Finset.mem_filter.mpr ⟨hAf.1, hcA⟩⟩

theorem unsafeIncidentSets_cover_three
    {H : Hypergraph V} {C : ConflictSystem V} {e : Finset V}
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4) :
    unsafeIncidentSets H C 3 e ⊆
      (conflictRootsAt C 2 e).biUnion (rootedJSets H 3) ∪
      (conflictRootsAwayAug C 2 e).biUnion (rootedJSets H 3) ∪
      (conflictRootsAt C 3 e).biUnion (rootedJSets H 3) := by
  intro A hA
  have hAf := Finset.mem_filter.mp hA
  obtain ⟨c, hcC, hcA⟩ := hAf.2.2
  have hAcard := (Finset.mem_powersetCard.mp hAf.1).2
  have hcle : c.card ≤ 3 := by simpa [hAcard] using Finset.card_le_card hcA
  have hcge := (hcard c hcC).1
  interval_cases hcsize : c.card
  · by_cases hec : e ∈ c
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨c,
        Finset.mem_filter.mpr ⟨mem_conflictLayer.mpr ⟨hcC, hcsize⟩, hec⟩,
        Finset.mem_filter.mpr ⟨hAf.1, hcA⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨insert e c, Finset.mem_image.mpr ⟨c, ?_, rfl⟩,
        Finset.mem_filter.mpr ⟨hAf.1, Finset.insert_subset hAf.2.1 hcA⟩⟩
      exact Finset.mem_filter.mpr
        ⟨mem_conflictLayer.mpr ⟨hcC, hcsize⟩, hec⟩
  · have hcEq : c = A := Finset.eq_of_subset_of_card_le hcA (by omega)
    have hec : e ∈ c := hcEq.symm ▸ hAf.2.1
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨c,
      Finset.mem_filter.mpr ⟨mem_conflictLayer.mpr ⟨hcC, hcsize⟩, hec⟩,
      Finset.mem_filter.mpr ⟨hAf.1, hcA⟩⟩

theorem unsafeIncidentSets_cover_four
    {H : Hypergraph V} {C : ConflictSystem V} {e : Finset V}
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4) :
    unsafeIncidentSets H C 4 e ⊆
      (conflictRootsAt C 2 e).biUnion (rootedJSets H 4) ∪
      (conflictRootsAwayAug C 2 e).biUnion (rootedJSets H 4) ∪
      (conflictRootsAt C 3 e).biUnion (rootedJSets H 4) ∪
      (conflictRootsAwayAug C 3 e).biUnion (rootedJSets H 4) ∪
      (conflictRootsAt C 4 e).biUnion (rootedJSets H 4) := by
  intro A hA
  have hAf := Finset.mem_filter.mp hA
  obtain ⟨c, hcC, hcA⟩ := hAf.2.2
  have hAcard := (Finset.mem_powersetCard.mp hAf.1).2
  have hcle : c.card ≤ 4 := by simpa [hAcard] using Finset.card_le_card hcA
  have hcge := (hcard c hcC).1
  interval_cases hcsize : c.card
  · by_cases hec : e ∈ c
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨c,
        Finset.mem_filter.mpr ⟨mem_conflictLayer.mpr ⟨hcC, hcsize⟩, hec⟩,
        Finset.mem_filter.mpr ⟨hAf.1, hcA⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨insert e c, Finset.mem_image.mpr ⟨c, ?_, rfl⟩,
        Finset.mem_filter.mpr ⟨hAf.1, Finset.insert_subset hAf.2.1 hcA⟩⟩
      exact Finset.mem_filter.mpr
        ⟨mem_conflictLayer.mpr ⟨hcC, hcsize⟩, hec⟩
  · by_cases hec : e ∈ c
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨c,
        Finset.mem_filter.mpr ⟨mem_conflictLayer.mpr ⟨hcC, hcsize⟩, hec⟩,
        Finset.mem_filter.mpr ⟨hAf.1, hcA⟩⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨insert e c, Finset.mem_image.mpr ⟨c, ?_, rfl⟩,
        Finset.mem_filter.mpr ⟨hAf.1, Finset.insert_subset hAf.2.1 hcA⟩⟩
      exact Finset.mem_filter.mpr
        ⟨mem_conflictLayer.mpr ⟨hcC, hcsize⟩, hec⟩
  · have hcEq : c = A := Finset.eq_of_subset_of_card_le hcA (by omega)
    have hec : e ∈ c := hcEq.symm ▸ hAf.2.1
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨c,
      Finset.mem_filter.mpr ⟨mem_conflictLayer.mpr ⟨hcC, hcsize⟩, hec⟩,
      Finset.mem_filter.mpr ⟨hAf.1, hcA⟩⟩

 
theorem tripleRootCover_two_eq_empty
    (H : Hypergraph V) (roots : Finset (Hypergraph V))
    (hroots : ∀ root ∈ roots, root.card = 3) :
    roots.biUnion (rootedJSets H 2) = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨A, hA⟩ := hne
  obtain ⟨root, hroot, hrooted⟩ := Finset.mem_biUnion.mp hA
  have hrootA := (Finset.mem_filter.mp hrooted).2
  have hAcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hrooted).1).2
  have := Finset.card_le_card hrootA
  rw [hroots root hroot, hAcard] at this
  omega

theorem card_nonmatchingIncidentSets_two_le
    {H : Hypergraph V} {D : ℕ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    {e : Finset V} (heH : e ∈ H) :
    (nonmatchingIncidentSets H 2 e).card ≤ 8 * D := by
  have hempty : (meetingTripleRootsAway H e).biUnion (rootedJSets H 2) = ∅ :=
    tripleRootCover_two_eq_empty H _
      (fun root hroot => (meetingTripleRootsAway_properties heH root hroot).2)
  have hcover := nonmatchingIncidentSets_cover (j := 2) heH
  rw [hempty, Finset.union_empty] at hcover
  calc
    (nonmatchingIncidentSets H 2 e).card ≤
        ((meetingPairRootsAt H e).biUnion (rootedJSets H 2)).card :=
      Finset.card_le_card hcover
    _ ≤ (meetingPairRootsAt H e).card * H.card ^ (2 - 2) :=
      card_rootCover_le H 2 2 _ (meetingPairRootsAt_properties heH)
    _ ≤ 8 * D := by
      simp only [Nat.sub_self, pow_zero, mul_one]
      exact Finset.card_image_le.trans
        (card_meetingNeighbors_le_eight_mul hmax (huniform e heH))

theorem card_conflictRootAtCover_le
    {H : Hypergraph V} {C : ConflictSystem V} (hC : IsConflictSystem H C)
    {j r Delta : ℕ} {e : Finset V} (heH : e ∈ H)
    (hDelta : ∀ f ∈ H, degree (conflictLayer C r) f ≤ Delta) :
    ((conflictRootsAt C r e).biUnion (rootedJSets H j)).card ≤
      Delta * H.card ^ (j - r) := by
  calc
    ((conflictRootsAt C r e).biUnion (rootedJSets H j)).card ≤
        (conflictRootsAt C r e).card * H.card ^ (j - r) :=
      card_rootCover_le H j r _ (conflictRootsAt_properties hC)
    _ ≤ Delta * H.card ^ (j - r) := by
      apply Nat.mul_le_mul_right
      rw [card_conflictRootsAt_eq_degree]
      exact hDelta e heH

theorem card_conflictRootAwayCover_le
    {H : Hypergraph V} {C : ConflictSystem V} (hC : IsConflictSystem H C)
    {j r Delta : ℕ} {e : Finset V} (heH : e ∈ H) (hr : 1 ≤ r)
    (hDelta : ∀ f ∈ H, degree (conflictLayer C r) f ≤ Delta) :
    ((conflictRootsAwayAug C r e).biUnion (rootedJSets H j)).card ≤
      (H.card * Delta) * H.card ^ (j - (r + 1)) := by
  calc
    ((conflictRootsAwayAug C r e).biUnion (rootedJSets H j)).card ≤
        (conflictRootsAwayAug C r e).card * H.card ^ (j - (r + 1)) :=
      card_rootCover_le H j (r + 1) _
        (conflictRootsAwayAug_properties hC heH)
    _ ≤ (H.card * Delta) * H.card ^ (j - (r + 1)) :=
      Nat.mul_le_mul_right _ (card_conflictRootsAwayAug_le hC hr hDelta e)

theorem card_union_three_le {X : Type*} [DecidableEq X]
    (A B C : Finset X) :
    (A ∪ B ∪ C).card ≤ A.card + B.card + C.card := by
  exact (Finset.card_union_le (A ∪ B) C).trans
    (Nat.add_le_add_right (Finset.card_union_le A B) C.card)

theorem card_union_five_le {X : Type*} [DecidableEq X]
    (A B C D E : Finset X) :
    (A ∪ B ∪ C ∪ D ∪ E).card ≤
      A.card + B.card + C.card + D.card + E.card := by
  exact (Finset.card_union_le (A ∪ B ∪ C ∪ D) E).trans
    (Nat.add_le_add_right
      ((Finset.card_union_le (A ∪ B ∪ C) D).trans
        (Nat.add_le_add_right (card_union_three_le A B C) D.card)) E.card)

theorem card_unsafeIncidentSets_two_le
    {H : Hypergraph V} {C : ConflictSystem V} (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    {Delta2 : ℕ} {e : Finset V} (heH : e ∈ H)
    (hDelta2 : ∀ f ∈ H, degree (conflictLayer C 2) f ≤ Delta2) :
    (unsafeIncidentSets H C 2 e).card ≤ Delta2 := by
  calc
    (unsafeIncidentSets H C 2 e).card ≤
        ((conflictRootsAt C 2 e).biUnion (rootedJSets H 2)).card :=
      Finset.card_le_card (unsafeIncidentSets_cover_two hcard)
    _ ≤ Delta2 * H.card ^ (2 - 2) :=
      card_conflictRootAtCover_le hC heH hDelta2
    _ = Delta2 := by simp

theorem card_unsafeIncidentSets_three_le
    {H : Hypergraph V} {C : ConflictSystem V} (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    {Delta2 Delta3 : ℕ} {e : Finset V} (heH : e ∈ H)
    (hDelta2 : ∀ f ∈ H, degree (conflictLayer C 2) f ≤ Delta2)
    (hDelta3 : ∀ f ∈ H, degree (conflictLayer C 3) f ≤ Delta3) :
    (unsafeIncidentSets H C 3 e).card ≤
      Delta2 * H.card + H.card * Delta2 + Delta3 := by
  let A := (conflictRootsAt C 2 e).biUnion (rootedJSets H 3)
  let B := (conflictRootsAwayAug C 2 e).biUnion (rootedJSets H 3)
  let D := (conflictRootsAt C 3 e).biUnion (rootedJSets H 3)
  calc
    (unsafeIncidentSets H C 3 e).card ≤ (A ∪ B ∪ D).card := by
      exact Finset.card_le_card (unsafeIncidentSets_cover_three hcard)
    _ ≤ A.card + B.card + D.card := card_union_three_le A B D
    _ ≤ (Delta2 * H.card ^ (3 - 2)) +
          ((H.card * Delta2) * H.card ^ (3 - (2 + 1))) +
          (Delta3 * H.card ^ (3 - 3)) := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (card_conflictRootAtCover_le hC heH hDelta2)
          (card_conflictRootAwayCover_le hC heH (by omega) hDelta2))
        (card_conflictRootAtCover_le hC heH hDelta3)
    _ = Delta2 * H.card + H.card * Delta2 + Delta3 := by ring

theorem card_unsafeIncidentSets_four_le
    {H : Hypergraph V} {C : ConflictSystem V} (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    {Delta2 Delta3 Delta4 : ℕ} {e : Finset V} (heH : e ∈ H)
    (hDelta2 : ∀ f ∈ H, degree (conflictLayer C 2) f ≤ Delta2)
    (hDelta3 : ∀ f ∈ H, degree (conflictLayer C 3) f ≤ Delta3)
    (hDelta4 : ∀ f ∈ H, degree (conflictLayer C 4) f ≤ Delta4) :
    (unsafeIncidentSets H C 4 e).card ≤
      Delta2 * H.card ^ 2 + (H.card * Delta2) * H.card +
        Delta3 * H.card + H.card * Delta3 + Delta4 := by
  let A := (conflictRootsAt C 2 e).biUnion (rootedJSets H 4)
  let B := (conflictRootsAwayAug C 2 e).biUnion (rootedJSets H 4)
  let D := (conflictRootsAt C 3 e).biUnion (rootedJSets H 4)
  let E := (conflictRootsAwayAug C 3 e).biUnion (rootedJSets H 4)
  let F := (conflictRootsAt C 4 e).biUnion (rootedJSets H 4)
  calc
    (unsafeIncidentSets H C 4 e).card ≤ (A ∪ B ∪ D ∪ E ∪ F).card := by
      exact Finset.card_le_card (unsafeIncidentSets_cover_four hcard)
    _ ≤ A.card + B.card + D.card + E.card + F.card :=
      card_union_five_le A B D E F
    _ ≤ (Delta2 * H.card ^ (4 - 2)) +
          ((H.card * Delta2) * H.card ^ (4 - (2 + 1))) +
          (Delta3 * H.card ^ (4 - 3)) +
          ((H.card * Delta3) * H.card ^ (4 - (3 + 1))) +
          (Delta4 * H.card ^ (4 - 4)) := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (card_conflictRootAtCover_le hC heH hDelta2)
              (card_conflictRootAwayCover_le hC heH (by omega) hDelta2))
            (card_conflictRootAtCover_le hC heH hDelta3))
          (card_conflictRootAwayCover_le hC heH (by omega) hDelta3))
        (card_conflictRootAtCover_le hC heH hDelta4)
    _ = Delta2 * H.card ^ 2 + (H.card * Delta2) * H.card +
        Delta3 * H.card + H.card * Delta3 + Delta4 := by ring

theorem forbiddenIncidentCompletions_subset_nonmatching_union_unsafe
    (H : Hypergraph V) (C : ConflictSystem V) (j : ℕ) (e : Finset V) :
    forbiddenIncidentCompletions H C j e ⊆
      nonmatchingIncidentSets H j e ∪ unsafeIncidentSets H C j e := by
  intro A hA
  have hAf := Finset.mem_filter.mp hA
  have hsdiff := Finset.mem_sdiff.mp hAf.1
  have hpow := Finset.mem_powersetCard.mp hsdiff.1
  by_cases hmatch : IsMatching H A
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hsdiff.1, hAf.2, ?_⟩
    have hnfree : ¬ ConflictFree C A := by
      intro hfree
      exact hsdiff.2 (mem_completionCandidates.mpr
        ⟨hpow.1, hpow.2, hmatch, hfree⟩)
    simp only [ConflictFree] at hnfree
    push Not at hnfree
    exact hnfree
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hsdiff.1, hAf.2, hmatch⟩

theorem card_forbiddenIncidentCompletions_two_le
    {H : Hypergraph V} {C : ConflictSystem V} {D : ℕ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    {e : Finset V} (heH : e ∈ H) :
    (forbiddenIncidentCompletions H C 2 e).card ≤
      8 * D + layerMaxDegree H C 2 := by
  calc
    (forbiddenIncidentCompletions H C 2 e).card ≤
        (nonmatchingIncidentSets H 2 e ∪ unsafeIncidentSets H C 2 e).card :=
      Finset.card_le_card
        (forbiddenIncidentCompletions_subset_nonmatching_union_unsafe H C 2 e)
    _ ≤ (nonmatchingIncidentSets H 2 e).card +
        (unsafeIncidentSets H C 2 e).card := Finset.card_union_le _ _
    _ ≤ 8 * D + layerMaxDegree H C 2 := Nat.add_le_add
      (card_nonmatchingIncidentSets_two_le huniform hmax heH)
      (card_unsafeIncidentSets_two_le hC hcard heH
        (fun f hf => degree_layer_le_layerMaxDegree hf))

theorem card_forbiddenIncidentCompletions_three_le
    {H : Hypergraph V} {C : ConflictSystem V} {D : ℕ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    {e : Finset V} (heH : e ∈ H) :
    (forbiddenIncidentCompletions H C 3 e).card ≤
      (8 * D) * H.card + H.card * (8 * D) +
        (layerMaxDegree H C 2 * H.card +
          H.card * layerMaxDegree H C 2 + layerMaxDegree H C 3) := by
  calc
    (forbiddenIncidentCompletions H C 3 e).card ≤
        (nonmatchingIncidentSets H 3 e ∪ unsafeIncidentSets H C 3 e).card :=
      Finset.card_le_card
        (forbiddenIncidentCompletions_subset_nonmatching_union_unsafe H C 3 e)
    _ ≤ (nonmatchingIncidentSets H 3 e).card +
        (unsafeIncidentSets H C 3 e).card := Finset.card_union_le _ _
    _ ≤ ((8 * D) * H.card ^ (3 - 2) +
          (H.card * (8 * D)) * H.card ^ (3 - 3)) +
        (layerMaxDegree H C 2 * H.card +
          H.card * layerMaxDegree H C 2 + layerMaxDegree H C 3) :=
      Nat.add_le_add (card_nonmatchingIncidentSets_le huniform hmax heH)
        (card_unsafeIncidentSets_three_le hC hcard heH
          (fun f hf => degree_layer_le_layerMaxDegree hf)
          (fun f hf => degree_layer_le_layerMaxDegree hf))
    _ = _ := by ring

theorem card_forbiddenIncidentCompletions_four_le
    {H : Hypergraph V} {C : ConflictSystem V} {D : ℕ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    {e : Finset V} (heH : e ∈ H) :
    (forbiddenIncidentCompletions H C 4 e).card ≤
      (8 * D) * H.card ^ 2 + (H.card * (8 * D)) * H.card +
        (layerMaxDegree H C 2 * H.card ^ 2 +
          (H.card * layerMaxDegree H C 2) * H.card +
          layerMaxDegree H C 3 * H.card +
          H.card * layerMaxDegree H C 3 + layerMaxDegree H C 4) := by
  calc
    (forbiddenIncidentCompletions H C 4 e).card ≤
        (nonmatchingIncidentSets H 4 e ∪ unsafeIncidentSets H C 4 e).card :=
      Finset.card_le_card
        (forbiddenIncidentCompletions_subset_nonmatching_union_unsafe H C 4 e)
    _ ≤ (nonmatchingIncidentSets H 4 e).card +
        (unsafeIncidentSets H C 4 e).card := Finset.card_union_le _ _
    _ ≤ ((8 * D) * H.card ^ (4 - 2) +
          (H.card * (8 * D)) * H.card ^ (4 - 3)) +
        (layerMaxDegree H C 2 * H.card ^ 2 +
          (H.card * layerMaxDegree H C 2) * H.card +
          layerMaxDegree H C 3 * H.card +
          H.card * layerMaxDegree H C 3 + layerMaxDegree H C 4) :=
      Nat.add_le_add (card_nonmatchingIncidentSets_le huniform hmax heH)
        (card_unsafeIncidentSets_four_le hC hcard heH
          (fun f hf => degree_layer_le_layerMaxDegree hf)
          (fun f hf => degree_layer_le_layerMaxDegree hf)
          (fun f hf => degree_layer_le_layerMaxDegree hf))
    _ = _ := by ring

/-- The common analytic absorption behind stages 2, 3, and 4.  Once the
combinatorial estimate has the form `K*d*n^(j-2)`, the source bias and the
host-size lower bound leave the exponent gap `eta - 5*eps`. -/

 
theorem forbiddenMass_absorbed
    {j : ℕ} (hj2 : 2 ≤ j)
    {d n eps eta K pmax : ℝ} {m : ℕ}
    (hd : 0 < d)
    (hK : 0 ≤ K)
    (hpmax0 : 0 ≤ pmax)
    (hcard : (m : ℝ) ≤ K * d * n ^ (j - 2))
    (hpmax : pmax ≤
      Real.rpow d ((j : ℝ) - 1 + 3 * eps) / n ^ (j - 1))
    (hhost : Real.rpow d (1 + eta) ≤ n)
    (habsorb : K ≤ Real.rpow d (eta - 5 * eps)) :
    (m : ℝ) * pmax ≤ Real.rpow d ((j : ℝ) - 1 - 2 * eps) := by
  have hnpos : 0 < n :=
    (Real.rpow_pos_of_pos hd (1 + eta)).trans_le hhost
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  have hpowpos : 0 < n ^ (j - 1) := pow_pos hnpos _
  have hnum0 : 0 ≤ K * d * n ^ (j - 2) := by positivity
  have hsource0 : 0 ≤ Real.rpow d ((j : ℝ) - 1 + 3 * eps) :=
    (Real.rpow_pos_of_pos hd _).le
  have hjpred : j - 1 = (j - 2) + 1 := by omega
  calc
    (m : ℝ) * pmax ≤ (K * d * n ^ (j - 2)) * pmax :=
      mul_le_mul_of_nonneg_right hcard hpmax0
    _ ≤ (K * d * n ^ (j - 2)) *
        (Real.rpow d ((j : ℝ) - 1 + 3 * eps) / n ^ (j - 1)) :=
      mul_le_mul_of_nonneg_left hpmax hnum0
    _ = K * d * Real.rpow d ((j : ℝ) - 1 + 3 * eps) / n := by
      rw [hjpred, pow_succ]
      field_simp
    _ ≤ K * d * Real.rpow d ((j : ℝ) - 1 + 3 * eps) /
        Real.rpow d (1 + eta) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact Real.rpow_pos_of_pos hd _
      · exact hhost
    _ ≤ Real.rpow d (eta - 5 * eps) * d *
        Real.rpow d ((j : ℝ) - 1 + 3 * eps) /
          Real.rpow d (1 + eta) := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hd.le _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right habsorb hd.le)
        (Real.rpow_nonneg hd.le _)
    _ = Real.rpow d ((j : ℝ) - 1 - 2 * eps) := by
      have hd1 : d = Real.rpow d 1 := (Real.rpow_one d).symm
      nth_rewrite 2 [hd1]
      have hexp :
          eta - 5 * eps + 1 + ((j : ℝ) - 1 + 3 * eps) - (1 + eta) =
            (j : ℝ) - 1 - 2 * eps := by ring
      have hA : Real.rpow d (eta - 5 * eps) * Real.rpow d 1 =
          Real.rpow d (eta - 5 * eps + 1) := by
        have h := (Real.rpow_add hd (eta - 5 * eps) 1).symm
        change Real.rpow d (eta - 5 * eps) * Real.rpow d 1 =
          Real.rpow d (eta - 5 * eps + 1) at h
        exact h
      have hB : Real.rpow d (eta - 5 * eps + 1) *
          Real.rpow d ((j : ℝ) - 1 + 3 * eps) =
            Real.rpow d (eta - 5 * eps + 1 + ((j : ℝ) - 1 + 3 * eps)) := by
        have h := (Real.rpow_add hd (eta - 5 * eps + 1)
          ((j : ℝ) - 1 + 3 * eps)).symm
        change Real.rpow d (eta - 5 * eps + 1) *
          Real.rpow d ((j : ℝ) - 1 + 3 * eps) =
            Real.rpow d (eta - 5 * eps + 1 + ((j : ℝ) - 1 + 3 * eps)) at h
        exact h
      have hC : Real.rpow d
            (eta - 5 * eps + 1 + ((j : ℝ) - 1 + 3 * eps)) /
          Real.rpow d (1 + eta) =
            Real.rpow d
              (eta - 5 * eps + 1 + ((j : ℝ) - 1 + 3 * eps) - (1 + eta)) := by
        have h := (Real.rpow_sub hd
          (eta - 5 * eps + 1 + ((j : ℝ) - 1 + 3 * eps)) (1 + eta)).symm
        change Real.rpow d
            (eta - 5 * eps + 1 + ((j : ℝ) - 1 + 3 * eps)) /
          Real.rpow d (1 + eta) =
            Real.rpow d
              (eta - 5 * eps + 1 + ((j : ℝ) - 1 + 3 * eps) - (1 + eta)) at h
        exact h
      rw [hA, hB, hC, hexp]

/-- Source-specialised form with the internal regularisation scale
`eps = eta / 10000`.  The finite large-`d` registry only has to discharge
the displayed coefficient absorption. -/
theorem forbiddenMass_absorbed_rawEps
    {j : ℕ} (hj2 : 2 ≤ j)
    {d n eta K pmax : ℝ} {m : ℕ}
    (hd : 0 < d)
    (hK : 0 ≤ K)
    (hpmax0 : 0 ≤ pmax)
    (hcard : (m : ℝ) ≤ K * d * n ^ (j - 2))
    (hpmax : pmax ≤
      Real.rpow d ((j : ℝ) - 1 + 3 * (eta / 10000)) /
        n ^ (j - 1))
    (hhost : Real.rpow d (1 + eta) ≤ n)
    (habsorb : K ≤
      Real.rpow d (eta - 5 * (eta / 10000))) :
    (m : ℝ) * pmax ≤
      Real.rpow d ((j : ℝ) - 1 - 2 * (eta / 10000)) :=
  forbiddenMass_absorbed hj2 hd hK hpmax0 hcard hpmax hhost habsorb

end

/-! ### Source means for upper observables -/

noncomputable section

theorem ChernoffFinite.bitMean_le_card_mul_pointwise {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (pmax : ℝ)
    (hp : ∀ i, active i → p i ≤ pmax) :
    ChernoffFinite.bitMean p active ≤
      ((Finset.univ.filter active).card : ℝ) * pmax := by
  rw [ChernoffFinite.bitMean]
  calc
    (∑ i, if active i then p i else 0) ≤
        ∑ i, if active i then pmax else 0 := by
      apply Finset.sum_le_sum
      intro i _hi
      split_ifs with h
      · exact hp i h
      · exact le_rfl
    _ = ((Finset.univ.filter active).card : ℝ) * pmax := by
      rw [← Finset.sum_filter]
      simp

theorem ChernoffFinite.bitMean_le_count_mul_pointwise {n : ℕ}
    (p : Fin n → ℝ) (active : Fin n → Prop) (pmax count : ℝ)
    (hpmax0 : 0 ≤ pmax) (hp : ∀ i, active i → p i ≤ pmax)
    (hcount : ((Finset.univ.filter active).card : ℝ) ≤ count) :
    ChernoffFinite.bitMean p active ≤ count * pmax := by
  exact (ChernoffFinite.bitMean_le_card_mul_pointwise p active pmax hp).trans
    (mul_le_mul_of_nonneg_right hcount hpmax0)

theorem BlockChernoff.blockProbability_le_pointwise_of_nonempty {n : ℕ}
    (p : Fin n → ℝ) (B : Finset (Fin n)) (pmax : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i, p i ≤ pmax) (hB : B.Nonempty) :
    (∏ i ∈ B, p i) ≤ pmax := by
  obtain ⟨i, hi⟩ := hB
  have hrest1 : (∏ k ∈ B.erase i, p k) ≤ 1 := by
    exact Finset.prod_le_one (fun k hk ↦ (hp k).1) (fun k hk ↦ (hp k).2)
  rw [← Finset.mul_prod_erase B p hi]
  calc
    p i * ∏ k ∈ B.erase i, p k ≤ p i * 1 :=
      mul_le_mul_of_nonneg_left hrest1 (hp i).1
    _ ≤ pmax := by simpa using hpmax i

theorem BlockChernoff.blockMean_le_count_mul_pointwise_of_nonempty
    {n m : ℕ} (p : Fin n → ℝ) (B : Fin m → Finset (Fin n))
    (pmax count : ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i, p i ≤ pmax) (hB : ∀ a, (B a).Nonempty)
    (hpmax0 : 0 ≤ pmax) (hcount : (m : ℝ) ≤ count) :
    BlockChernoff.blockMean p B ≤ count * pmax := by
  rw [BlockChernoff.blockMean]
  calc
    (∑ a, ∏ i ∈ B a, p i) ≤ ∑ _a : Fin m, pmax := by
      apply Finset.sum_le_sum
      intro a _ha
      exact BlockChernoff.blockProbability_le_pointwise_of_nonempty
        p (B a) pmax hp hpmax (hB a)
    _ = (m : ℝ) * pmax := by simp
    _ ≤ count * pmax := mul_le_mul_of_nonneg_right hcount hpmax0

theorem BlockChernoff.blockProbability_le_pow_pointwise {n : ℕ}
    (p : Fin n → ℝ) (B : Finset (Fin n)) (pmax : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpmax : ∀ i, p i ≤ pmax) :
    (∏ i ∈ B, p i) ≤ pmax ^ B.card := by
  calc
    (∏ i ∈ B, p i) ≤ ∏ _i ∈ B, pmax := by
      apply Finset.prod_le_prod
      · intro i hi
        exact hp i
      · intro i hi
        exact hpmax i
    _ = pmax ^ B.card := by simp

/-- Sharp form for blocks of size one or two.  This is the useful estimate
for old-new versus new-new common links. -/
theorem BlockChernoff.blockMean_le_one_two_counts
    {n m : ℕ} (p : Fin n → ℝ) (B : Fin m → Finset (Fin n))
    (pmax countOne countTwo : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i, p i ≤ pmax)
    (hBne : ∀ a, (B a).Nonempty) (hBtwo : ∀ a, (B a).card ≤ 2)
    (hpmax0 : 0 ≤ pmax)
    (hcountOne : ((Finset.univ.filter fun a => (B a).card = 1).card : ℝ) ≤
      countOne)
    (hcountTwo : ((Finset.univ.filter fun a => (B a).card ≠ 1).card : ℝ) ≤
      countTwo) :
    BlockChernoff.blockMean p B ≤ countOne * pmax + countTwo * pmax ^ 2 := by
  rw [BlockChernoff.blockMean,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a => (B a).card = 1) (fun a => ∏ i ∈ B a, p i)]
  apply add_le_add
  · calc
      ∑ a ∈ Finset.univ.filter (fun a => (B a).card = 1),
          ∏ i ∈ B a, p i ≤
          ∑ _a ∈ Finset.univ.filter (fun a => (B a).card = 1), pmax := by
        apply Finset.sum_le_sum
        intro a ha
        exact BlockChernoff.blockProbability_le_pointwise_of_nonempty
          p (B a) pmax hp hpmax (hBne a)
      _ = ((Finset.univ.filter fun a => (B a).card = 1).card : ℝ) * pmax := by
        simp
      _ ≤ countOne * pmax := mul_le_mul_of_nonneg_right hcountOne hpmax0
  · calc
      ∑ a ∈ Finset.univ.filter (fun a => (B a).card ≠ 1),
          ∏ i ∈ B a, p i ≤
          ∑ _a ∈ Finset.univ.filter (fun a => (B a).card ≠ 1), pmax ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        have hne : (B a).card ≠ 1 := (Finset.mem_filter.mp ha).2
        have hpos : 0 < (B a).card := Finset.card_pos.mpr (hBne a)
        have hle : (B a).card ≤ 2 := hBtwo a
        have hcard : (B a).card = 2 := by omega
        simpa [hcard] using BlockChernoff.blockProbability_le_pow_pointwise
          p (B a) pmax (fun i => (hp i).1) hpmax
      _ = ((Finset.univ.filter fun a => (B a).card ≠ 1).card : ℝ) *
          pmax ^ 2 := by simp
      _ ≤ countTwo * pmax ^ 2 :=
        mul_le_mul_of_nonneg_right hcountTwo (sq_nonneg pmax)

namespace UpperObservables

variable [Fintype V]

theorem stageCodegreeActive_card_le_pow
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (root : StageCodegreeIndex V stage) :
    (Finset.univ.filter
        (stageLinearUpperActive H current stage (Sum.inl root))).card ≤
      H.card ^ (stage - root.1.card) := by
  let F := Finset.univ.filter
    (stageLinearUpperActive H current stage (Sum.inl root))
  let target := (H \ root.1).powersetCard (stage - root.1.card)
  have hinj : F.card ≤ target.card := by
    apply Finset.card_le_card_of_injOn
      (fun i ↦ completionCandidate H current stage i \ root.1)
    · intro i hi
      have hiActive : root.1 ⊆ completionCandidate H current stage i :=
        (Finset.mem_filter.mp hi).2
      have hiCand := mem_completionCandidates.mp
        (completionCandidate_mem H current stage i)
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro e he
        exact Finset.mem_sdiff.mpr
          ⟨hiCand.1 (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩
      · rw [Finset.card_sdiff,
          show root.1 ∩ completionCandidate H current stage i = root.1 from
            Finset.inter_eq_left.mpr hiActive,
          hiCand.2.1]
    · intro i hi k hk hik
      apply completionCandidate_injective H current stage
      have hiActive : root.1 ⊆ completionCandidate H current stage i :=
        (Finset.mem_filter.mp hi).2
      have hkActive : root.1 ⊆ completionCandidate H current stage k :=
        (Finset.mem_filter.mp hk).2
      change completionCandidate H current stage i \ root.1 =
        completionCandidate H current stage k \ root.1 at hik
      calc
        completionCandidate H current stage i =
            root.1 ∪ (completionCandidate H current stage i \ root.1) :=
          (Finset.union_sdiff_of_subset hiActive).symm
        _ = root.1 ∪ (completionCandidate H current stage k \ root.1) := by rw [hik]
        _ = completionCandidate H current stage k :=
          Finset.union_sdiff_of_subset hkActive
  calc
    F.card ≤ target.card := hinj
    _ = Nat.choose (H \ root.1).card (stage - root.1.card) := by simp [target]
    _ ≤ (H \ root.1).card ^ (stage - root.1.card) := Nat.choose_le_pow _ _
    _ ≤ H.card ^ (stage - root.1.card) := by
      exact Nat.pow_le_pow_left
        (Finset.card_le_card (Finset.sdiff_subset : H \ root.1 ⊆ H)) _

theorem stageC4Active_card_le_degree
    (H : Hypergraph V) (current : ConflictSystem V)
    (e : Finset V) (he : e ∈ H) (v : V) :
    (Finset.univ.filter
      (stageLinearUpperActive H current 2
        (Sum.inr (StageC4Index.mk e he v rfl)))).card ≤ degree H v := by
  let F := Finset.univ.filter
    (stageLinearUpperActive H current 2
      (Sum.inr (StageC4Index.mk e he v rfl)))
  let target := (H.filter fun g ↦ v ∈ g).powersetCard 1
  have hinj : F.card ≤ target.card := by
    apply Finset.card_le_card_of_injOn
      (fun i ↦ (completionCandidate H current 2 i).erase e)
    · intro i hi
      have hcreate : CandidateCreatesC4 e v
          (completionCandidate H current 2 i) := (Finset.mem_filter.mp hi).2
      obtain ⟨heA, g, hgA, hge, hgv⟩ := hcreate
      have hCand := mem_completionCandidates.mp
        (completionCandidate_mem H current 2 i)
      have hcard : ((completionCandidate H current 2 i).erase e).card = 1 := by
        rw [Finset.card_erase_of_mem heA, hCand.2.1]
      have hgerase : g ∈ (completionCandidate H current 2 i).erase e :=
        Finset.mem_erase.mpr ⟨hge, hgA⟩
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro f hf
        have hfg : f = g :=
          Finset.card_le_one.mp (by omega :
            ((completionCandidate H current 2 i).erase e).card ≤ 1)
            f hf g hgerase
        subst f
        exact Finset.mem_filter.mpr ⟨hCand.1 hgA, hgv⟩
      · exact hcard
    · intro i hi k hk hik
      apply completionCandidate_injective H current 2
      have hiCreate : CandidateCreatesC4 e v
          (completionCandidate H current 2 i) := (Finset.mem_filter.mp hi).2
      have hkCreate : CandidateCreatesC4 e v
          (completionCandidate H current 2 k) := (Finset.mem_filter.mp hk).2
      change (completionCandidate H current 2 i).erase e =
        (completionCandidate H current 2 k).erase e at hik
      calc
        completionCandidate H current 2 i =
            insert e ((completionCandidate H current 2 i).erase e) :=
          (Finset.insert_erase hiCreate.1).symm
        _ = insert e ((completionCandidate H current 2 k).erase e) := by rw [hik]
        _ = completionCandidate H current 2 k :=
          Finset.insert_erase hkCreate.1
  calc
    F.card ≤ target.card := hinj
    _ = degree H v := by simp [target, degree]

theorem stageBlockFamily_nonempty
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (a : StageBlockUpperIndex H current stage)
    (i : Fin (Fintype.card (StageBlockLabel H current stage a))) :
    (stageBlockFamily H current stage a i).Nonempty := by
  exact commonLinkRequiredCoordinates_nonempty H current stage
    (stageBlockLeft a) (stageBlockRight a)
    ((Fintype.equivFin (StageBlockLabel H current stage a)).symm i)

theorem stageBlockFamily_card_le_two
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (a : StageBlockUpperIndex H current stage)
    (i : Fin (Fintype.card (StageBlockLabel H current stage a))) :
    (stageBlockFamily H current stage a i).card ≤ 2 := by
  exact commonLinkRequiredCoordinates_card_le_two H current stage
    (stageBlockLeft a) (stageBlockRight a)
    ((Fintype.equivFin (StageBlockLabel H current stage a)).symm i)

theorem candidateRealizesRemainder_same_coordinate_root_eq
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    {e f : Finset V} {T : Hypergraph V}
    {i : CompletionCoordinate H current stage}
    (he : CandidateRealizesRemainder H current stage e T i)
    (hf : CandidateRealizesRemainder H current stage f T i) : e = f := by
  have heq : insert e T = insert f T := by
    calc
      insert e T = completionCandidate H current stage i := by
        rw [← he.2]
        exact Finset.insert_erase he.1
      _ = insert f T := by
        rw [← hf.2]
        exact (Finset.insert_erase hf.1).symm
  have heT := not_mem_remainder_of_candidateRealizes H current stage he
  have : e ∈ insert f T := by
    rw [← heq]
    simp
  simpa [heT] using this

theorem stageBlockLeft_mem (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (a : StageBlockUpperIndex H current stage) :
    stageBlockLeft a ∈ H := by
  rcases a with a | a
  · exact a.pair.left_mem
  · exact a.pair.left_mem

theorem stageBlockRight_mem (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (a : StageBlockUpperIndex H current stage) :
    stageBlockRight a ∈ H := by
  rcases a with a | a
  · exact a.pair.right_mem
  · exact a.pair.right_mem

theorem stageBlock_disjoint (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (a : StageBlockUpperIndex H current stage) :
    Disjoint (stageBlockLeft a) (stageBlockRight a) := by
  rcases a with a | a
  · exact a.pair.disjoint
  · exact a.pair.disjoint

theorem stageBlockLabel_old_side_of_card_one
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hhostNonempty : ∀ e ∈ H, e.Nonempty)
    (a : StageBlockUpperIndex H current stage)
    (T : StageBlockLabel H current stage a)
    (hcard : (commonLinkRequiredCoordinates H current stage
      (stageBlockLeft a) (stageBlockRight a) T.1).card = 1) :
    T.1 ∈ conflictLinkLayer current (stageBlockLeft a) (stage - 1) ∨
      T.1 ∈ conflictLinkLayer current (stageBlockRight a) (stage - 1) := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨ie, hie⟩ := T.2.2.1.resolve_left hnot.1
  obtain ⟨if_, hif⟩ := T.2.2.2.1.resolve_left hnot.2
  have hieMem : ie ∈ commonLinkRequiredCoordinates H current stage
      (stageBlockLeft a) (stageBlockRight a) T.1 := by
    simp only [commonLinkRequiredCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inl ⟨hnot.1, hie⟩
  have hifMem : if_ ∈ commonLinkRequiredCoordinates H current stage
      (stageBlockLeft a) (stageBlockRight a) T.1 := by
    simp only [commonLinkRequiredCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inr ⟨hnot.2, hif⟩
  have hne : ie ≠ if_ := by
    intro heq
    subst if_
    have hef : stageBlockLeft a = stageBlockRight a :=
      candidateRealizesRemainder_same_coordinate_root_eq
        H current stage hie hif
    have hleftEmpty : stageBlockLeft a = ∅ := by
      have hd := stageBlock_disjoint H current stage a
      rw [← hef] at hd
      apply Finset.Subset.antisymm
      · intro z hz
        exact ((Finset.disjoint_left.mp hd) hz hz).elim
      · exact Finset.empty_subset _
    exact (hhostNonempty (stageBlockLeft a)
      (stageBlockLeft_mem H current stage a)).ne_empty hleftEmpty
  have htwo : 1 < (commonLinkRequiredCoordinates H current stage
      (stageBlockLeft a) (stageBlockRight a) T.1).card :=
    Finset.one_lt_card.mpr ⟨ie, hieMem, if_, hifMem, hne⟩
  omega

theorem stageBlockFamily_card_one_count_le_old_links
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hhostNonempty : ∀ e ∈ H, e.Nonempty)
    (a : StageBlockUpperIndex H current stage) :
    (Finset.univ.filter fun i =>
      (stageBlockFamily H current stage a i).card = 1).card ≤
      (conflictLinkLayer current (stageBlockLeft a) (stage - 1)).card +
        (conflictLinkLayer current (stageBlockRight a) (stage - 1)).card := by
  let E := (Fintype.equivFin (StageBlockLabel H current stage a)).symm
  let old := conflictLinkLayer current (stageBlockLeft a) (stage - 1) ∪
    conflictLinkLayer current (stageBlockRight a) (stage - 1)
  calc
    (Finset.univ.filter fun i =>
        (stageBlockFamily H current stage a i).card = 1).card ≤ old.card := by
      apply Finset.card_le_card_of_injOn (fun i ↦ (E i).1)
      · intro i hi
        apply Finset.mem_union.mpr
        apply stageBlockLabel_old_side_of_card_one H current stage
          hhostNonempty a (E i)
        exact (Finset.mem_filter.mp hi).2
      · intro i hi k hk hik
        apply E.injective
        exact Subtype.ext hik
    _ ≤ (conflictLinkLayer current (stageBlockLeft a) (stage - 1)).card +
        (conflictLinkLayer current (stageBlockRight a) (stage - 1)).card :=
      Finset.card_union_le _ _

theorem stageBlockLabel_card_le_pow
    (H : Hypergraph V) (current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current) (stage : ℕ)
    (a : StageBlockUpperIndex H current stage) :
    Fintype.card (StageBlockLabel H current stage a) ≤
      H.card ^ (stage - 1) := by
  let target := H.powersetCard (stage - 1)
  have htoTarget (T : StageBlockLabel H current stage a) : T.1 ∈ target := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, T.2.1⟩
    rcases T.2.2.1 with hold | ⟨i, hi⟩
    · obtain ⟨⟨c, hc, hec, herase⟩, _hcard⟩ :=
        mem_conflictLinkLayer.mp hold
      rw [← herase]
      exact (Finset.erase_subset _ c).trans (hcurrent c hc)
    · rw [← hi.2]
      exact (Finset.erase_subset _ _).trans
        (completionCandidates_isConflictSystem H current stage _
          (completionCandidate_mem H current stage i))
  have hinj : Fintype.card (StageBlockLabel H current stage a) ≤ target.card := by
    rw [← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun T ↦ T.1)
    · intro T _hT
      exact htoTarget T
    · intro T _hT U _hU hTU
      exact Subtype.ext hTU
  calc
    Fintype.card (StageBlockLabel H current stage a) ≤ target.card := hinj
    _ = Nat.choose H.card (stage - 1) := by simp [target]
    _ ≤ H.card ^ (stage - 1) := Nat.choose_le_pow _ _

theorem stageLinearUpperMean_le_of_active_card
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (target pmax count : ℝ) (a : StageLinearUpperIndex H stage)
    (hpmax0 : 0 ≤ pmax)
    (hpmax : ∀ i, sourceCompletionBiasAtTarget H current stage target i ≤ pmax)
    (hcount : ((Finset.univ.filter
      (stageLinearUpperActive H current stage a)).card : ℝ) ≤ count) :
    ChernoffFinite.bitMean
        (sourceCompletionBiasAtTarget H current stage target)
        (stageLinearUpperActive H current stage a) ≤ count * pmax := by
  exact ChernoffFinite.bitMean_le_count_mul_pointwise
    _ _ pmax count hpmax0 (fun i _hi ↦ hpmax i) hcount

theorem stageCodegreeUpperMean_le_pow_mul
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (target pmax : ℝ) (root : StageCodegreeIndex V stage)
    (hpmax0 : 0 ≤ pmax)
    (hpmax : ∀ i, sourceCompletionBiasAtTarget H current stage target i ≤ pmax) :
    ChernoffFinite.bitMean
        (sourceCompletionBiasAtTarget H current stage target)
        (stageLinearUpperActive H current stage (Sum.inl root)) ≤
      (H.card : ℝ) ^ (stage - root.1.card) * pmax := by
  apply stageLinearUpperMean_le_of_active_card H current stage target pmax
    ((H.card : ℝ) ^ (stage - root.1.card)) (Sum.inl root) hpmax0 hpmax
  exact_mod_cast stageCodegreeActive_card_le_pow H current stage root

theorem stageC4UpperMean_le_degree_mul
    (H : Hypergraph V) (current : ConflictSystem V)
    (target pmax : ℝ) (e : Finset V) (he : e ∈ H) (v : V)
    (hpmax0 : 0 ≤ pmax)
    (hpmax : ∀ i, sourceCompletionBiasAtTarget H current 2 target i ≤ pmax) :
    ChernoffFinite.bitMean
        (sourceCompletionBiasAtTarget H current 2 target)
        (stageLinearUpperActive H current 2
          (Sum.inr (StageC4Index.mk e he v rfl))) ≤
      (degree H v : ℝ) * pmax := by
  apply stageLinearUpperMean_le_of_active_card H current 2 target pmax
    (degree H v : ℝ) (Sum.inr (StageC4Index.mk e he v rfl)) hpmax0 hpmax
  exact_mod_cast stageC4Active_card_le_degree H current e he v

/-- The direct source threshold for the linear families: host-card power for
codegrees, and the host vertex degree for the stage-two C4 count. -/
def sourceLinearUpperThreshold (H : Hypergraph V)
    (current : ConflictSystem V) (stage : ℕ) (pmax : ℝ) :
    StageLinearUpperIndex H stage → ℝ
  | Sum.inl root => (H.card : ℝ) ^ (stage - root.1.card) * pmax
  | Sum.inr c4 => (degree H c4.vertex : ℝ) * pmax

theorem sourceLinearUpperThreshold_nonneg
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (pmax : ℝ) (hpmax0 : 0 ≤ pmax) :
    ∀ a, 0 ≤ sourceLinearUpperThreshold H current stage pmax a := by
  rintro (root | c4) <;> simp only [sourceLinearUpperThreshold] <;> positivity

theorem stageLinearUpperMean_le_sourceThreshold
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (target pmax : ℝ) (hpmax0 : 0 ≤ pmax)
    (hpmax : ∀ i, sourceCompletionBiasAtTarget H current stage target i ≤ pmax) :
    ∀ a, ChernoffFinite.bitMean
        (sourceCompletionBiasAtTarget H current stage target)
        (stageLinearUpperActive H current stage a) ≤
      sourceLinearUpperThreshold H current stage pmax a := by
  rintro (root | ⟨e, he, v, hs⟩)
  · exact stageCodegreeUpperMean_le_pow_mul H current stage target pmax
      root hpmax0 hpmax
  · subst stage
    exact stageC4UpperMean_le_degree_mul H current target pmax
      e he v hpmax0 hpmax

theorem stageBlockUpperMean_le_of_label_card
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (target pmax count : ℝ) (a : StageBlockUpperIndex H current stage)
    (hp : ∀ i, sourceCompletionBiasAtTarget H current stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i, sourceCompletionBiasAtTarget H current stage target i ≤ pmax)
    (hpmax0 : 0 ≤ pmax)
    (hcount : (Fintype.card (StageBlockLabel H current stage a) : ℝ) ≤ count) :
    BlockChernoff.blockMean
        (sourceCompletionBiasAtTarget H current stage target)
        (stageBlockFamily H current stage a) ≤ count * pmax := by
  exact BlockChernoff.blockMean_le_count_mul_pointwise_of_nonempty
    _ _ pmax count hp hpmax (stageBlockFamily_nonempty H current stage a)
      hpmax0 hcount

theorem stageBlockUpperMean_le_pow_mul
    (H : Hypergraph V) (current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current) (stage : ℕ)
    (target pmax : ℝ) (a : StageBlockUpperIndex H current stage)
    (hp : ∀ i, sourceCompletionBiasAtTarget H current stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i, sourceCompletionBiasAtTarget H current stage target i ≤ pmax)
    (hpmax0 : 0 ≤ pmax) :
    BlockChernoff.blockMean
        (sourceCompletionBiasAtTarget H current stage target)
        (stageBlockFamily H current stage a) ≤
      (H.card : ℝ) ^ (stage - 1) * pmax := by
  apply stageBlockUpperMean_le_of_label_card H current stage target pmax
    ((H.card : ℝ) ^ (stage - 1)) a hp hpmax hpmax0
  exact_mod_cast stageBlockLabel_card_le_pow H current hcurrent stage a

/-- Refined block expectation: one-coordinate (old-new) labels are counted
separately, while all remaining labels have two coordinates and therefore
pay `pmax²`. -/
theorem stageBlockUpperMean_le_one_two
    (H : Hypergraph V) (current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current) (stage : ℕ)
    (target pmax countOne : ℝ)
    (a : StageBlockUpperIndex H current stage)
    (hp : ∀ i, sourceCompletionBiasAtTarget H current stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i, sourceCompletionBiasAtTarget H current stage target i ≤ pmax)
    (hpmax0 : 0 ≤ pmax)
    (hcountOne : ((Finset.univ.filter fun i =>
      (stageBlockFamily H current stage a i).card = 1).card : ℝ) ≤ countOne) :
    BlockChernoff.blockMean
        (sourceCompletionBiasAtTarget H current stage target)
        (stageBlockFamily H current stage a) ≤
      countOne * pmax + (H.card : ℝ) ^ (stage - 1) * pmax ^ 2 := by
  apply BlockChernoff.blockMean_le_one_two_counts
    _ _ pmax countOne ((H.card : ℝ) ^ (stage - 1)) hp hpmax
    (stageBlockFamily_nonempty H current stage a)
    (stageBlockFamily_card_le_two H current stage a) hpmax0 hcountOne
  have hfilter :
      (Finset.univ.filter fun i =>
        (stageBlockFamily H current stage a i).card ≠ 1).card ≤
      Fintype.card (StageBlockLabel H current stage a) := by
    simpa using Finset.card_le_card
      (Finset.filter_subset (fun i =>
        (stageBlockFamily H current stage a i).card ≠ 1) Finset.univ)
  exact_mod_cast hfilter.trans
    (stageBlockLabel_card_le_pow H current hcurrent stage a)

/-- Source-faithful block threshold: old-new labels are charged to the two
old links and new-new labels pay two point-mass factors. -/
def sourceRefinedBlockUpperThreshold (H : Hypergraph V)
    (current : ConflictSystem V) (stage : ℕ) (pmax : ℝ) :
    StageBlockUpperIndex H current stage → ℝ := fun a ↦
  (((conflictLinkLayer current (stageBlockLeft a) (stage - 1)).card : ℝ) +
      ((conflictLinkLayer current (stageBlockRight a) (stage - 1)).card : ℝ)) *
      pmax + (H.card : ℝ) ^ (stage - 1) * pmax ^ 2

theorem sourceRefinedBlockUpperThreshold_eq_degrees
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hstage : 1 ≤ stage) (pmax : ℝ)
    (a : StageBlockUpperIndex H current stage) :
    sourceRefinedBlockUpperThreshold H current stage pmax a =
      ((degree (conflictLayer current stage) (stageBlockLeft a) : ℝ) +
        (degree (conflictLayer current stage) (stageBlockRight a) : ℝ)) *
        pmax + (H.card : ℝ) ^ (stage - 1) * pmax ^ 2 := by
  rw [sourceRefinedBlockUpperThreshold,
    card_conflictLinkLayer_eq_degree_layer,
    card_conflictLinkLayer_eq_degree_layer,
    show stage - 1 + 1 = stage by omega]

theorem sourceRefinedBlockUpperThreshold_nonneg
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (pmax : ℝ) (hpmax0 : 0 ≤ pmax) :
    ∀ a, 0 ≤ sourceRefinedBlockUpperThreshold H current stage pmax a := by
  intro a
  simp only [sourceRefinedBlockUpperThreshold]
  positivity

theorem stageBlockUpperMean_le_refinedSourceThreshold
    (H : Hypergraph V) (current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (hhostNonempty : ∀ e ∈ H, e.Nonempty) (stage : ℕ)
    (target pmax : ℝ)
    (hp : ∀ i, sourceCompletionBiasAtTarget H current stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i, sourceCompletionBiasAtTarget H current stage target i ≤ pmax)
    (hpmax0 : 0 ≤ pmax) :
    ∀ a, BlockChernoff.blockMean
        (sourceCompletionBiasAtTarget H current stage target)
        (stageBlockFamily H current stage a) ≤
      sourceRefinedBlockUpperThreshold H current stage pmax a := by
  intro a
  apply stageBlockUpperMean_le_one_two H current hcurrent stage target pmax
    (((conflictLinkLayer current (stageBlockLeft a) (stage - 1)).card : ℝ) +
      ((conflictLinkLayer current (stageBlockRight a) (stage - 1)).card : ℝ))
    a hp hpmax hpmax0
  exact_mod_cast stageBlockFamily_card_one_count_le_old_links H current stage
    hhostNonempty a

/-- Thresholds after replacing the literal host cardinal and local degrees
by external scales `N`, `D`, and `layerBound`. -/

def hostBoundLinearUpperThreshold (H : Hypergraph V) (stage : ℕ)
    (N D pmax : ℝ) : StageLinearUpperIndex H stage → ℝ
  | Sum.inl root => N ^ (stage - root.1.card) * pmax
  | Sum.inr _ => D * pmax

def hostBoundBlockUpperThreshold (H : Hypergraph V)
    (current : ConflictSystem V) (stage : ℕ)
    (N layerBound pmax : ℝ) : StageBlockUpperIndex H current stage → ℝ :=
  fun _ ↦ 2 * layerBound * pmax + N ^ (stage - 1) * pmax ^ 2

theorem hostBoundLinearUpperThreshold_nonneg
    (H : Hypergraph V) (stage : ℕ) (N D pmax : ℝ)
    (hN : 0 ≤ N) (hD : 0 ≤ D) (hpmax : 0 ≤ pmax) :
    ∀ a, 0 ≤ hostBoundLinearUpperThreshold H stage N D pmax a := by
  rintro (root | c4) <;> simp only [hostBoundLinearUpperThreshold] <;> positivity

theorem hostBoundBlockUpperThreshold_nonneg
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (N layerBound pmax : ℝ)
    (hN : 0 ≤ N) (hlayer : 0 ≤ layerBound) (hpmax : 0 ≤ pmax) :
    ∀ a, 0 ≤ hostBoundBlockUpperThreshold H current stage
      N layerBound pmax a := by
  intro a
  simp only [hostBoundBlockUpperThreshold]
  positivity

theorem stageLinearUpperMean_le_hostBoundThreshold
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (target pmax N D : ℝ) (hpmax0 : 0 ≤ pmax)
    (hN : (H.card : ℝ) ≤ N)
    (hD : ∀ v, (degree H v : ℝ) ≤ D)
    (hpmax : ∀ i, sourceCompletionBiasAtTarget H current stage target i ≤ pmax) :
    ∀ a, ChernoffFinite.bitMean
        (sourceCompletionBiasAtTarget H current stage target)
        (stageLinearUpperActive H current stage a) ≤
      hostBoundLinearUpperThreshold H stage N D pmax a := by
  rintro (root | ⟨e, he, v, hs⟩)
  · calc
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (stageLinearUpperActive H current stage (Sum.inl root)) ≤
          (H.card : ℝ) ^ (stage - root.1.card) * pmax :=
        stageCodegreeUpperMean_le_pow_mul H current stage target pmax
          root hpmax0 hpmax
      _ ≤ N ^ (stage - root.1.card) * pmax := by
        gcongr
      _ = hostBoundLinearUpperThreshold H stage N D pmax (Sum.inl root) := rfl
  · subst stage
    calc
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current 2 target)
          (stageLinearUpperActive H current 2
            (Sum.inr (StageC4Index.mk e he v rfl))) ≤
          (degree H v : ℝ) * pmax :=
        stageC4UpperMean_le_degree_mul H current target pmax e he v hpmax0 hpmax
      _ ≤ D * pmax := mul_le_mul_of_nonneg_right (hD v) hpmax0
      _ = hostBoundLinearUpperThreshold H 2 N D pmax
          (Sum.inr (StageC4Index.mk e he v rfl)) := rfl

theorem stageBlockUpperMean_le_hostBoundThreshold
    (H : Hypergraph V) (current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (hhostNonempty : ∀ e ∈ H, e.Nonempty)
    (stage : ℕ) (hstage : 1 ≤ stage)
    (target pmax N layerBound : ℝ)
    (hp : ∀ i, sourceCompletionBiasAtTarget H current stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hpmax : ∀ i, sourceCompletionBiasAtTarget H current stage target i ≤ pmax)
    (hpmax0 : 0 ≤ pmax) (hN : (H.card : ℝ) ≤ N)
    (hlayer : ∀ e ∈ H,
      (degree (conflictLayer current stage) e : ℝ) ≤ layerBound) :
    ∀ a, BlockChernoff.blockMean
        (sourceCompletionBiasAtTarget H current stage target)
        (stageBlockFamily H current stage a) ≤
      hostBoundBlockUpperThreshold H current stage N layerBound pmax a := by
  intro a
  calc
    BlockChernoff.blockMean
        (sourceCompletionBiasAtTarget H current stage target)
        (stageBlockFamily H current stage a) ≤
        sourceRefinedBlockUpperThreshold H current stage pmax a :=
      stageBlockUpperMean_le_refinedSourceThreshold H current hcurrent
        hhostNonempty stage target pmax hp hpmax hpmax0 a
    _ = ((degree (conflictLayer current stage) (stageBlockLeft a) : ℝ) +
          (degree (conflictLayer current stage) (stageBlockRight a) : ℝ)) *
          pmax + (H.card : ℝ) ^ (stage - 1) * pmax ^ 2 :=
      sourceRefinedBlockUpperThreshold_eq_degrees H current stage hstage pmax a
    _ ≤ 2 * layerBound * pmax + N ^ (stage - 1) * pmax ^ 2 := by
      have hleft := hlayer (stageBlockLeft a)
        (stageBlockLeft_mem H current stage a)
      have hright := hlayer (stageBlockRight a)
        (stageBlockRight_mem H current stage a)
      have hsum :
          (degree (conflictLayer current stage) (stageBlockLeft a) : ℝ) +
              (degree (conflictLayer current stage) (stageBlockRight a) : ℝ) ≤
            2 * layerBound := by linarith
      have hpow : (H.card : ℝ) ^ (stage - 1) ≤ N ^ (stage - 1) :=
        pow_le_pow_left₀ (by positivity) hN _
      exact add_le_add
        (mul_le_mul_of_nonneg_right hsum hpmax0)
        (mul_le_mul_of_nonneg_right hpow (sq_nonneg pmax))
    _ = hostBoundBlockUpperThreshold H current stage N layerBound pmax a := rfl

theorem hostBoundThreshold_propertyRooms
    (H : Hypergraph V) (current : ConflictSystem V)
    (d eps pmax N D layerBound : ℝ) (stage : ℕ)
    (hII : ∀ root : StageCodegreeIndex V stage,
      (codegree (conflictLayer current stage) root.1 : ℝ) +
          2 * (N ^ (stage - root.1.card) * pmax) ≤
        Real.rpow d ((stage : ℝ) - (root.1.card : ℝ) - eps / 4))
    (hIII : ∀ (hs : stage = 2) (e : Finset V) (he : e ∈ H) (v : V),
      (conditionC4Count H current e v : ℝ) + 2 * (D * pmax) ≤
        Real.rpow d (1 - eps / 4))
    (hIV : ∀ (hs : stage = 2) (e : Finset V) (he : e ∈ H)
      (f : Finset V) (hf : f ∈ H) (hdisj : Disjoint e f),
      (conditionC5Count H current e f : ℝ) +
          2 * (2 * layerBound * pmax + N ^ (stage - 1) * pmax ^ 2) ≤
        Real.rpow d (1 - eps / 4))
    (hV : ∀ (e : Finset V) (he : e ∈ H)
      (f : Finset V) (hf : f ∈ H) (hdisj : Disjoint e f)
      (hnot : {e, f} ∉ conflictLayer current 2),
      ((conflictLinkLayer current e (stage - 1) ∩
          conflictLinkLayer current f (stage - 1)).card : ℝ) +
          2 * (2 * layerBound * pmax + N ^ (stage - 1) * pmax ^ 2) ≤
        Real.rpow d ((stage - 1 : ℕ) - eps / 4)) :
    PropertyIIRoom H current d eps stage
        (hostBoundLinearUpperThreshold H stage N D pmax) ∧
      PropertyIIIRoom H current d eps stage
        (hostBoundLinearUpperThreshold H stage N D pmax) ∧
      PropertyIVRoom H current d eps stage
        (hostBoundBlockUpperThreshold H current stage N layerBound pmax) ∧
      PropertyVRoom H current d eps stage
        (hostBoundBlockUpperThreshold H current stage N layerBound pmax) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro root
    simpa [hostBoundLinearUpperThreshold] using hII root
  · intro hs e he v
    simpa [hostBoundLinearUpperThreshold] using hIII hs e he v
  · intro hs e he f hf hdisj
    simpa [hostBoundBlockUpperThreshold] using hIV hs e he f hf hdisj
  · intro e he f hf hdisj hnot
    simpa [hostBoundBlockUpperThreshold] using hV e he f hf hdisj hnot

end UpperObservables
end

/-! ### Concrete source-weighted completion stages -/

noncomputable section

variable [Fintype V]


abbrev ConcreteStageDegreeIndex (H : Hypergraph V) := {e // e ∈ H}

abbrev concreteStageDegreeActive (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (e : ConcreteStageDegreeIndex H)
    (i : CompletionCoordinate H current stage) : Prop :=
  e.1 ∈ completionCandidate H current stage i

abbrev concreteStageBlockSize (H : Hypergraph V) (current : ConflictSystem V)
    (stage : ℕ) (a : StageBlockUpperIndex H current stage) : ℕ :=
  Fintype.card (StageBlockLabel H current stage a)

noncomputable def concreteStageBlockEquiv
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (a : StageBlockUpperIndex H current stage) :
    StageBlockLabel H current stage a ≃
      Fin (concreteStageBlockSize H current stage a) :=
  Fintype.equivFin _

def concreteStageBlockFamily
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (a : StageBlockUpperIndex H current stage)
    (i : Fin (concreteStageBlockSize H current stage a)) :
    Finset (CompletionCoordinate H current stage) :=
  let T := (concreteStageBlockEquiv H current stage a).symm i
  commonLinkRequiredCoordinates H current stage
    (stageBlockLeft a) (stageBlockRight a) T.1

theorem concreteStageBlockFamily_pairwiseDisjoint
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (a : StageBlockUpperIndex H current stage) :
    (Set.univ : Set (Fin (concreteStageBlockSize H current stage a))).PairwiseDisjoint
      (concreteStageBlockFamily H current stage a) := by
  intro i _hi k _hk hik
  apply disjoint_commonLinkRequiredCoordinates H current stage
  intro hlabels
  apply hik
  exact (concreteStageBlockEquiv H current stage a).symm.injective
    (Subtype.ext (congrArg Subtype.val hlabels))

theorem blockCount_concreteStageBlockFamily_eq
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (a : StageBlockUpperIndex H current stage)
    (x : CompletionCoordinate H current stage → Bool) :
    BlockChernoff.blockCount (concreteStageBlockFamily H current stage a) x =
      (commonLinkBlockCount H current stage
        (stageBlockLeft a) (stageBlockRight a) x : ℝ) := by
  rw [BlockChernoff.blockCount_eq_filter_card]
  let E := concreteStageBlockEquiv H current stage a
  let P : Fin (concreteStageBlockSize H current stage a) → Prop :=
    fun i => ∀ q ∈ concreteStageBlockFamily H current stage a i, x q = true
  let Q : StageBlockLabel H current stage a → Prop :=
    fun T => allCoordinatesSelected x
      (commonLinkRequiredCoordinates H current stage
        (stageBlockLeft a) (stageBlockRight a) T.1)
  let EQ : {i // P i} ≃ {T // Q T} :=
    { toFun := fun i => ⟨E.symm i.1, by
          simpa [P, Q, concreteStageBlockFamily, E,
            allCoordinatesSelected] using i.2⟩
      invFun := fun T => ⟨E T.1, by
          simpa [P, Q, concreteStageBlockFamily, E,
            allCoordinatesSelected] using T.2⟩
      left_inv := fun i => by apply Subtype.ext; exact E.apply_symm_apply i.1
      right_inv := fun T => by apply Subtype.ext; exact E.symm_apply_apply T.1 }
  rw [commonLinkBlockCount]
  change (((Finset.univ.filter P).card : ℕ) : ℝ) =
    (((Finset.univ.filter Q).card : ℕ) : ℝ)
  norm_cast
  rw [← Fintype.card_subtype P, ← Fintype.card_subtype Q]
  exact Fintype.card_congr EQ

theorem exists_concreteRegularizationStageWeighted_nonempty
    {ι : Type*} [Fintype ι]
    (H : Hypergraph V) (base current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (d eps Gamma : ℝ) (stage : ℕ) (target pmax : ℝ)
    (degreeDelta degreeRoom : ConcreteStageDegreeIndex H → ℝ)
    (linearThreshold : StageLinearUpperIndex H stage → ℝ)
    (blockThreshold : StageBlockUpperIndex H current stage → ℝ)
    (testJ : ι → ℕ) (w : ι → TestWeight V)
    (gap limit : ι → ℝ)
    (hH : H.Nonempty) (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (htarget : target = completionTarget d eps
      (layerMaxDegree H base stage : ℝ) stage)
    (hdef : HasSourceDeficitBoundsAtTarget H current d eps Gamma target stage)
    (hweightMax : ∀ A ∈ H.powersetCard stage,
      completionWeight H stage (degreeDeficit current stage target) A ≤ pmax)
    (hpmaxOne : pmax ≤ 1)
    (hdegreeRoom : ∀ e : ConcreteStageDegreeIndex H,
      12 * (4 * Gamma * Real.rpow d ((stage : ℝ) - 1)) ^ 2 /
          totalDeficit H (degreeDeficit current stage target) +
        ((forbiddenIncidentCompletions H current stage e.1).card : ℝ) * pmax ≤
          degreeRoom e)
    (hdegreeMargin : ∀ e : ConcreteStageDegreeIndex H,
      degreeDelta e * ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (concreteStageDegreeActive H current stage e) ≤
        Real.rpow d (-eps) * target - degreeRoom e)
    (hdelta0 : ∀ e, 0 ≤ degreeDelta e)
    (hdelta1 : ∀ e, degreeDelta e ≤ 1)
    (hlinear0 : ∀ a, 0 ≤ linearThreshold a)
    (hlinearMean : ∀ a,
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (stageLinearUpperActive H current stage a) ≤
        linearThreshold a)
    (hblock0 : ∀ a, 0 ≤ blockThreshold a)
    (hblockMean : ∀ a,
      BlockChernoff.blockMean
          (sourceCompletionBiasAtTarget H current stage target)
          (concreteStageBlockFamily H current stage a) ≤
        blockThreshold a)
    (hII : PropertyIIRoom H current d eps stage linearThreshold)
    (hIII : PropertyIIIRoom H current d eps stage linearThreshold)
    (hIV : PropertyIVRoom H current d eps stage blockThreshold)
    (hV : PropertyVRoom H current d eps stage blockThreshold)
    (hw : ∀ a S, 0 ≤ w a S)
    (hfreeZero : ∀ a S, S ∈ H.powersetCard (testJ a) →
      (∃ c ∈ current, c ⊆ S) → w a S = 0)
    (hgap : ∀ a, 0 ≤ gap a)
    (hkillRoom : ∀ a : ι,
      (∑ i, pmax * testExtension (w a) H (testJ a)
          (completionCandidate H current stage i)) + gap a ≤ limit a)
    (hfail :
      (∑ e : ConcreteStageDegreeIndex H,
          2 * Real.exp (-(degreeDelta e ^ 2 *
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (concreteStageDegreeActive H current stage e)) / 3)) +
        (∑ a : StageLinearUpperIndex H stage,
          Real.exp (-linearThreshold a / 3)) +
        (∑ a : StageBlockUpperIndex H current stage,
          Real.exp (-blockThreshold a / 3)) +
        (∑ a : ι,
          Real.exp (-2 * gap a ^ 2 /
            ∑ i, (testExtension (w a) H (testJ a)
              (completionCandidate H current stage i)) ^ 2)) < 1) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H current stage ∧
      HasStagePropertiesIV H base (addCompletionLayer current A) d eps stage ∧
      (∀ a, killedWeight H (addCompletionLayer current A)
        (testJ a) (w a) < limit a) := by
  let U : ℝ := 4 * Gamma * Real.rpow d ((stage : ℝ) - 1)
  let p := sourceCompletionBiasAtTarget H current stage target
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have ha0 : ∀ e ∈ H, 0 ≤ degreeDeficit current stage target e := by
    intro e he
    exact (Real.rpow_nonneg hd.le _).trans (hdef.2.2 e he).1
  have haU : ∀ e ∈ H, degreeDeficit current stage target e ≤ U := by
    intro e he
    exact hdef.2.2 e he |>.2
  have hLpos : 0 < Real.rpow d ((stage : ℝ) - 1 - 2 * eps) :=
    Real.rpow_pos_of_pos hd _
  have hcardpos : 0 < (H.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hH
  have htotal : 0 < totalDeficit H (degreeDeficit current stage target) := by
    apply (mul_pos hcardpos hLpos).trans_le
    apply card_mul_le_totalDeficit
    intro e he
    exact (hdef.2.2 e he).1
  have hprobMax : ∀ i, p i ≤ pmax := by
    intro i
    apply hweightMax
    exact Finset.mem_powersetCard.mpr
      ⟨(mem_completionCandidates.mp (completionCandidate_mem H current stage i)).1,
       (mem_completionCandidates.mp (completionCandidate_mem H current stage i)).2.1⟩
  have hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1 := by
    apply sourceCompletionBiasAtTarget_mem_Icc H current d eps Gamma target stage
      hd.le hdef
    intro i
    exact (hprobMax i).trans hpmaxOne
  have hdegreeMean : ∀ e : ConcreteStageDegreeIndex H,
      |(degree (conflictLayer current stage) e.1 : ℝ) +
          ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e) - target| ≤
        degreeRoom e := by
    intro e
    have herr := sourceIncidentMean_error H current stage hdef.1 hdef.2.1
      target U pmax e.2 hU ha0 haU htotal hweightMax
    have herr' :
        |ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e) -
          degreeDeficit current stage target e.1| ≤ degreeRoom e := by
      apply herr.trans
      simpa [U, p, concreteStageDegreeActive] using hdegreeRoom e
    rw [show (degree (conflictLayer current stage) e.1 : ℝ) +
        ChernoffFinite.bitMean p
          (concreteStageDegreeActive H current stage e) - target =
        ChernoffFinite.bitMean p
          (concreteStageDegreeActive H current stage e) -
            degreeDeficit current stage target e.1 by
      simp [degreeDeficit]
      ring]
    exact herr'
  /- Interrupted duplicate of the restricted-active wrapper body.  The
  checked live wrapper is completed at the end of this file.  Keeping this
  nested recovery comment avoids a large destructive rewrite.
  have hkillMean : ∀ a : ActiveStageTest H current stage testJ w,
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (sampledKilledWeight H (testJ a.1) (w a.1)
            (completionCandidate H current stage)) + gap a.1 ≤ limit a.1 := by
    intro a
    have hmean := weightedMean_sampledKilledWeight_le H
      (testJ a.1) (w a.1) (completionCandidate H current stage) p (hw a.1) hp
    calc
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (sampledKilledWeight H (testJ a.1) (w a.1)
            (completionCandidate H current stage)) + gap a.1 ≤
          (∑ i, p i * testExtension (w a.1) H (testJ a.1)
            (completionCandidate H current stage i)) + gap a.1 :=
        add_le_add hmean le_rfl
      _ ≤ (∑ i, pmax * testExtension (w a.1) H (testJ a.1)
            (completionCandidate H current stage i)) + gap a.1 := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro i _hi
          apply mul_le_mul_of_nonneg_right (hprobMax i)
          exact testExtension_nonneg (hw a.1) H (testJ a.1) _
        · exact le_rfl
      _ ≤ limit a.1 := hkillRoom a
  have hdecode : ∀ x,
      (∀ e,
        |ChernoffFinite.bitCount
            (concreteStageDegreeActive H current stage e) x -
          ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e)| <
          degreeDelta e * ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e)) →
      (∀ a, ChernoffFinite.bitCount
            (restrictedStageLinearUpperActive H current stage a) x <
        2 * linearThreshold a) →
      (∀ a, BlockChernoff.blockCount
          (concreteStageBlockFamily H current stage a) x <
        2 * blockThreshold a) →
      HasStagePropertiesIV H base
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        d eps stage := by
    intro x hrel hlinear hblock
    have hdegree : ∀ e ∈ H,
        InRelativeInterval
          (degree (conflictLayer
            (addCompletionLayer current
              (sampledCompletionLayer (completionCandidate H current stage) x))
            stage) e : ℝ)
          (completionTarget d eps (layerMaxDegree H base stage : ℝ) stage)
          (Real.rpow d (-eps)) := by
      intro e he
      let ee : ConcreteStageDegreeIndex H := ⟨e, he⟩
      have hdev := (hrel ee).trans_le (hdegreeMargin ee)
      rw [degree_addCompletionLayer_sampled_eq]
      have hinterval := inRelativeInterval_of_mean_room
        (hdegreeMean ee) (by
          simpa [p, ee, concreteStageDegreeActive,
            bitCount_degree_eq_sampledCount] using hdev)
      simpa [htarget] using hinterval
    have hlinearProps := stagePropertiesIIIII_of_restrictedLinearBounds
      H current hcurrent d eps hd.le stage hdef.2.1 x linearThreshold
      hlinear hII hIII
    have hblockBounds : BlockUpperBounds H current stage x blockThreshold := by
      intro a
      rw [← blockCount_concreteStageBlockFamily_eq H current stage a x]
      exact hblock a
    refine ⟨hdef.1, hdef.2.1, hdegree, hlinearProps.1, hlinearProps.2, ?_, ?_⟩
    · exact stagePropertyIV_of_blockBounds H current hcurrent d eps stage x
        blockThreshold hblockBounds hIV
    · exact stagePropertyV_of_blockBounds H current d eps stage hdef.1 x
        blockThreshold hblockBounds hV
  exact exists_regularizationStageWithBlocks_activeTests
    H base current d eps stage target
    (concreteStageDegreeActive H current stage) degreeDelta
    (restrictedStageLinearUpperActive H current stage) linearThreshold
    (concreteStageBlockSize H current stage)
    (concreteStageBlockFamily H current stage) blockThreshold
    testJ w gap limit hp hdelta0 hdelta1 hlinear0 hlinearMean
    (concreteStageBlockFamily_pairwiseDisjoint H current stage)
    hblock0 hblockMean hw hfreeZero hgap hlimitPos hkillMean hfail hdecode

end
end CFMRegularization
end Erdos136
  -/
  have hkillMean : ∀ a : ι,
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (sampledKilledWeight H (testJ a) (w a)
            (completionCandidate H current stage)) + gap a ≤ limit a := by
    intro a
    have hmean := weightedMean_sampledKilledWeight_le H
      (testJ a) (w a) (completionCandidate H current stage) p (hw a) hp
    calc
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (sampledKilledWeight H (testJ a) (w a)
            (completionCandidate H current stage)) + gap a ≤
          (∑ i, p i * testExtension (w a) H (testJ a)
            (completionCandidate H current stage i)) + gap a :=
        add_le_add hmean le_rfl
      _ ≤ (∑ i, pmax * testExtension (w a) H (testJ a)
            (completionCandidate H current stage i)) + gap a := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro i _hi
          apply mul_le_mul_of_nonneg_right (hprobMax i)
          exact testExtension_nonneg (hw a) H (testJ a) _
        · exact le_rfl
      _ ≤ limit a := hkillRoom a
  have hdecode : ∀ x,
      (∀ e,
        |ChernoffFinite.bitCount
            (concreteStageDegreeActive H current stage e) x -
          ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e)| <
          degreeDelta e * ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e)) →
      (∀ a, ChernoffFinite.bitCount
            (stageLinearUpperActive H current stage a) x <
        2 * linearThreshold a) →
      (∀ a, BlockChernoff.blockCount
          (concreteStageBlockFamily H current stage a) x <
        2 * blockThreshold a) →
      HasStagePropertiesIV H base
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        d eps stage := by
    intro x hrel hlinear hblock
    apply hasStagePropertiesIV_of_observableBounds H base current
      hcurrent d eps stage hdef.1 hdef.2.1 x linearThreshold blockThreshold
    · intro e he
      let ee : ConcreteStageDegreeIndex H := ⟨e, he⟩
      have hdev := (hrel ee).trans_le (hdegreeMargin ee)
      rw [degree_addCompletionLayer_sampled_eq]
      have hinterval := inRelativeInterval_of_mean_room
        (hdegreeMean ee) (by
          simpa [p, ee, concreteStageDegreeActive,
            bitCount_degree_eq_sampledCount] using hdev)
      simpa [htarget] using hinterval
    · exact hlinear
    · intro a
      rw [← blockCount_concreteStageBlockFamily_eq H current stage a x]
      exact hblock a
    · exact hII
    · exact hIII
    · exact hIV
    · exact hV
  exact exists_regularizationStageWithBlocks
    H base current d eps stage target
    (concreteStageDegreeActive H current stage) degreeDelta
    (stageLinearUpperActive H current stage) linearThreshold
    (concreteStageBlockSize H current stage)
    (concreteStageBlockFamily H current stage) blockThreshold
    testJ w gap limit hp hdelta0 hdelta1 hlinear0 hlinearMean
    (concreteStageBlockFamily_pairwiseDisjoint H current stage)
    hblock0 hblockMean hw hfreeZero hgap hkillMean hfail hdecode

theorem assemble_threeConcreteStagesWeighted
    {ι : Type*} [Fintype ι]
    (H : Hypergraph V) (base C0 A2 A3 A4 : ConflictSystem V)
    (d eps : ℝ) (testJ : ι → ℕ) (w : ι → TestWeight V)
    (limit2 limit3 limit4 : ι → ℝ)
    (hw0 : ∀ a S, 0 ≤ w a S)
    (hA2 : A2 ⊆ completionCandidates H C0 2)
    (hA3 : A3 ⊆ completionCandidates H (addCompletionLayer C0 A2) 3)
    (hA4 : A4 ⊆ completionCandidates H
      (addCompletionLayer (addCompletionLayer C0 A2) A3) 4)
    (h2 : HasStagePropertiesIV H base (addCompletionLayer C0 A2) d eps 2)
    (h3 : HasStagePropertiesIV H base
      (addCompletionLayer (addCompletionLayer C0 A2) A3) d eps 3)
    (h4 : HasStagePropertiesIV H base
      (addCompletionLayer
        (addCompletionLayer (addCompletionLayer C0 A2) A3) A4) d eps 4)
    (hw2 : ∀ a,
      killedWeight H (addCompletionLayer C0 A2)
        (testJ a) (w a) < limit2 a)
    (hw3 : ∀ a,
      killedWeight H
        (addCompletionLayer (addCompletionLayer C0 A2) A3)
        (testJ a) (restrictWeight (addCompletionLayer C0 A2) (w a)) <
          limit3 a)
    (hw4 : ∀ a,
      killedWeight H
        (addCompletionLayer
          (addCompletionLayer (addCompletionLayer C0 A2) A3) A4)
        (testJ a)
        (restrictWeight
          (addCompletionLayer (addCompletionLayer C0 A2) A3) (w a)) <
          limit4 a) :
    ThreeStageProperties H base
      (addCompletionLayer
        (addCompletionLayer (addCompletionLayer C0 A2) A3) A4) d eps ∧
    (∀ a,
      killedWeight H
        (addCompletionLayer
          (addCompletionLayer (addCompletionLayer C0 A2) A3) A4)
        (testJ a) (w a) < limit2 a + limit3 a + limit4 a) := by
  let C2 := addCompletionLayer C0 A2
  let C3 := addCompletionLayer C2 A3
  let R := addCompletionLayer C3 A4
  refine ⟨threeStageProperties_of_stageProperties H base C0 A2 A3 A4 d eps
    hA2 hA3 hA4 h2 h3 h4, ?_⟩
  intro a
  have ht3 := killedWeight_addCompletionLayer_telescope
    H C2 A3 (testJ a) (w a) (hw0 a)
  have ht4 := killedWeight_addCompletionLayer_telescope
    H C3 A4 (testJ a) (w a) (hw0 a)
  have heq :
      killedWeight H R (testJ a) (w a) =
        killedWeight H C2 (testJ a) (w a) +
        killedWeight H C3 (testJ a) (restrictWeight C2 (w a)) +
        killedWeight H R (testJ a) (restrictWeight C3 (w a)) := by
    linarith
  rw [show addCompletionLayer
    (addCompletionLayer (addCompletionLayer C0 A2) A3) A4 = R by rfl]
  rw [heq]
  have h2' := hw2 a
  have h3' := hw3 a
  have h4' := hw4 a
  change killedWeight H C2 (testJ a) (w a) < _ at h2'
  change killedWeight H C3 (testJ a)
    (restrictWeight C2 (w a)) < _ at h3'
  change killedWeight H R (testJ a)
    (restrictWeight C3 (w a)) < _ at h4'
  linarith

end
/-! ### Deterministic raw bad-pair core data -/

theorem conflictLayer_eq_empty_of_card_four
    (C : ConflictSystem V) (hcard : ∀ c ∈ C, c.card = 4)
    (r : ℕ) (hr : r ≠ 4) :
    conflictLayer C r = ∅ := by
  ext c
  simp only [mem_conflictLayer]
  constructor
  · rintro ⟨hc, hcr⟩
    exact (hr (hcr.symm.trans (hcard c hc))).elim
  · simp

theorem layerMaxDegree_eq_zero_of_layer_eq_empty
    (H : Hypergraph V) (C : ConflictSystem V) (r : ℕ)
    (h : conflictLayer C r = ∅) :
    layerMaxDegree H C r = 0 := by
  unfold layerMaxDegree
  apply Finset.sup_eq_zero.mpr
  intro e he
  rw [h]
  simp [degree]

theorem layerMaxDegree_le_of_degree_bound
    (H : Hypergraph V) (C : ConflictSystem V) (r : ℕ) (D : ℝ)
    (hD0 : 0 ≤ D)
    (hdegree : ∀ e ∈ H, (degree (conflictLayer C r) e : ℝ) ≤ D) :
    (layerMaxDegree H C r : ℝ) ≤ D := by
  have hsup : layerMaxDegree H C r ≤ Nat.floor D := by
    unfold layerMaxDegree
    apply Finset.sup_le
    intro e he
    exact Nat.le_floor (hdegree e he)
  exact (by exact_mod_cast hsup :
      (layerMaxDegree H C r : ℝ) ≤ (Nat.floor D : ℕ)) |>.trans
    (Nat.floor_le hD0)

theorem layerMaxDegree_minimalBadCore_two_le
    (H : Hypergraph V) (C B : ConflictSystem V)
    {d eta : ℝ} {ell : ℕ}
    (hC : IsBounded C d ell eta) (hB : IsUniform B 2)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hBdegree : ∀ e ∈ H, (degree B e : ℝ) ≤ D) :
    (layerMaxDegree H (minimalMatchingCore H (C ∪ B)) 2 : ℝ) ≤ D := by
  apply layerMaxDegree_le_of_degree_bound H
    (minimalMatchingCore H (C ∪ B)) 2 D hD0
  intro e he
  calc
    (degree (conflictLayer (minimalMatchingCore H (C ∪ B)) 2) e : ℝ) ≤
        degree (conflictLayer B 2) e := by
      exact_mod_cast degree_mono (minimalCore_union_layer_two_subset_right H hC) e
    _ = degree B e := by rw [conflictLayer_eq_self_of_uniform hB]
    _ ≤ D := hBdegree e he

theorem layerMaxDegree_minimalBadCore_three_eq_zero
    (H : Hypergraph V) (C B : ConflictSystem V)
    (hCcard : ∀ c ∈ C, c.card = 4) (hB : IsUniform B 2) :
    layerMaxDegree H (minimalMatchingCore H (C ∪ B)) 3 = 0 := by
  apply layerMaxDegree_eq_zero_of_layer_eq_empty
  ext c
  constructor
  · intro hc
    have hcC := minimalCore_union_layer_ge_three_subset_left H hB 3
      (by norm_num) hc
    rw [conflictLayer_eq_empty_of_card_four C hCcard 3 (by norm_num)] at hcC
    simpa using hcC
  · simp

theorem layerMaxDegree_minimalBadCore_four_le
    (H : Hypergraph V) (C B : ConflictSystem V)
    {d eta : ℝ} {ell : ℕ}
    (hC : IsBounded C d ell eta) (hB : IsUniform B 2) (hell : 4 ≤ ell) :
    (layerMaxDegree H (minimalMatchingCore H (C ∪ B)) 4 : ℝ) ≤
      (ell : ℝ) * Real.rpow d 3 := by
  have h := layerMaxDegree_minimalMatchingCore_union_two_le
    (H := H) (C := C) (B := B) (d := d) (eta := eta)
      hC hB (by norm_num) hell
  norm_num at h ⊢
  exact h

/-! ### Polynomial restricted linear observables -/

namespace UpperObservables

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Property-(II) roots restricted to actual host edges. -/
abbrev RestrictedStageCodegreeIndex (H : Hypergraph V) (stage : ℕ) :=
  {root : Hypergraph V // root ⊆ H ∧ 2 ≤ root.card ∧ root.card < stage}

/-- Property-(III) roots restricted to active host vertices. -/
structure RestrictedStageC4Index (H : Hypergraph V) (stage : ℕ) where
  edge : Finset V
  edge_mem : edge ∈ H
  vertex : V
  vertex_mem : vertex ∈ vertexFinset H
  stage_eq : stage = 2

deriving instance Fintype for RestrictedStageC4Index

/-- The polynomial-size replacement for `StageLinearUpperIndex`. -/
abbrev RestrictedStageLinearUpperIndex (H : Hypergraph V) (stage : ℕ) :=
  Sum (RestrictedStageCodegreeIndex H stage)
    (RestrictedStageC4Index H stage)

def restrictedStageLinearToFull (H : Hypergraph V) (stage : ℕ) :
    RestrictedStageLinearUpperIndex H stage → StageLinearUpperIndex H stage
  | Sum.inl root => Sum.inl ⟨root.1, root.2.2⟩
  | Sum.inr c4 => Sum.inr
      (StageC4Index.mk c4.edge c4.edge_mem c4.vertex c4.stage_eq)

def restrictedStageLinearUpperActive
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (a : RestrictedStageLinearUpperIndex H stage)
    (i : CompletionCoordinate H current stage) : Prop :=
  stageLinearUpperActive H current stage
    (restrictedStageLinearToFull H stage a) i

@[simp] theorem restrictedStageLinearUpperActive_inl
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (root : RestrictedStageCodegreeIndex H stage)
    (i : CompletionCoordinate H current stage) :
    restrictedStageLinearUpperActive H current stage (Sum.inl root) i ↔
      root.1 ⊆ completionCandidate H current stage i := by
  rfl

@[simp] theorem restrictedStageLinearUpperActive_inr
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (c4 : RestrictedStageC4Index H stage)
    (i : CompletionCoordinate H current stage) :
    restrictedStageLinearUpperActive H current stage (Sum.inr c4) i ↔
      CandidateCreatesC4 c4.edge c4.vertex
        (completionCandidate H current stage i) := by
  rfl

theorem restrictedStageCodegreeIndex_card_le
    (H : Hypergraph V) (stage : ℕ) (hstage4 : stage ≤ 4) :
    Fintype.card (RestrictedStageCodegreeIndex H stage) ≤
      H.card ^ 2 + H.card ^ 3 := by
  let S : Finset (Hypergraph V) := H.powersetCard 2 ∪ H.powersetCard 3
  let f : RestrictedStageCodegreeIndex H stage → {root // root ∈ S} :=
    fun root => ⟨root.1, by
      have hcard : root.1.card = 2 ∨ root.1.card = 3 := by omega
      rcases hcard with hcard | hcard
      · exact Finset.mem_union_left _
          (Finset.mem_powersetCard.mpr ⟨root.2.1, hcard⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_powersetCard.mpr ⟨root.2.1, hcard⟩)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val hab
  have hcard : Fintype.card (RestrictedStageCodegreeIndex H stage) ≤ S.card := by
    have hraw := Fintype.card_le_of_injective f hf
    rw [Fintype.card_coe S] at hraw
    exact hraw
  calc
    Fintype.card (RestrictedStageCodegreeIndex H stage) ≤ S.card := hcard
    _ ≤ (H.powersetCard 2).card + (H.powersetCard 3).card :=
      Finset.card_union_le _ _
    _ = Nat.choose H.card 2 + Nat.choose H.card 3 := by simp
    _ ≤ H.card ^ 2 + H.card ^ 3 :=
      Nat.add_le_add (Nat.choose_le_pow _ _) (Nat.choose_le_pow _ _)

theorem restrictedStageC4Index_card_le
    (H : Hypergraph V) (stage : ℕ) :
    Fintype.card (RestrictedStageC4Index H stage) ≤
      H.card * (vertexFinset H).card := by
  let f : RestrictedStageC4Index H stage →
      {e // e ∈ H} × {v // v ∈ vertexFinset H} :=
    fun a => (⟨a.edge, a.edge_mem⟩, ⟨a.vertex, a.vertex_mem⟩)
  have hf : Function.Injective f := by
    rintro ⟨e, he, v, hv, hs⟩ ⟨e', he', v', hv', hs'⟩ hab
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩
    rfl
  have hraw := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod, Fintype.card_coe H,
    Fintype.card_coe (vertexFinset H)] at hraw
  exact hraw

theorem restrictedStageLinearUpperIndex_card_le
    (H : Hypergraph V) (stage : ℕ) (hstage4 : stage ≤ 4) :
    Fintype.card (RestrictedStageLinearUpperIndex H stage) ≤
      H.card ^ 2 + H.card ^ 3 +
        H.card * (vertexFinset H).card := by
  rw [Fintype.card_sum]
  exact Nat.add_le_add
    (restrictedStageCodegreeIndex_card_le H stage hstage4)
    (restrictedStageC4Index_card_le H stage)

theorem stageLinearUpperActive_codegree_false_of_not_subset
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (root : StageCodegreeIndex V stage) (hroot : ¬root.1 ⊆ H)
    (i : CompletionCoordinate H current stage) :
    ¬stageLinearUpperActive H current stage (Sum.inl root) i := by
  intro hi
  apply hroot
  exact hi.trans (mem_completionCandidates.mp
    (completionCandidate_mem H current stage i)).1

theorem stageLinearUpperActive_C4_false_of_not_mem_vertexFinset
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (c4 : StageC4Index H stage) (hv : c4.vertex ∉ vertexFinset H)
    (i : CompletionCoordinate H current stage) :
    ¬stageLinearUpperActive H current stage (Sum.inr c4) i := by
  intro hi
  obtain ⟨_heA, g, hgA, _hge, hvg⟩ := hi
  have hgH : g ∈ H := (mem_completionCandidates.mp
    (completionCandidate_mem H current stage i)).1 hgA
  exact hv (mem_vertexFinset.mpr ⟨g, hgH, hvg⟩)

theorem bitCount_stageLinearUpperActive_codegree_eq_zero_of_not_subset
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (root : StageCodegreeIndex V stage) (hroot : ¬root.1 ⊆ H)
    (x : CompletionCoordinate H current stage → Bool) :
    ChernoffFinite.bitCount
      (stageLinearUpperActive H current stage (Sum.inl root)) x = 0 := by
  rw [ChernoffFinite.bitCount]
  apply Finset.sum_eq_zero
  intro i _hi
  simp [stageLinearUpperActive_codegree_false_of_not_subset
    H current stage root hroot i]

theorem bitMean_stageLinearUpperActive_codegree_eq_zero_of_not_subset
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (p : CompletionCoordinate H current stage → ℝ)
    (root : StageCodegreeIndex V stage) (hroot : ¬root.1 ⊆ H) :
    ChernoffFinite.bitMean p
      (stageLinearUpperActive H current stage (Sum.inl root)) = 0 := by
  rw [ChernoffFinite.bitMean]
  apply Finset.sum_eq_zero
  intro i _hi
  simp [stageLinearUpperActive_codegree_false_of_not_subset
    H current stage root hroot i]

theorem bitCount_stageLinearUpperActive_C4_eq_zero_of_not_mem_vertexFinset
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (c4 : StageC4Index H stage) (hv : c4.vertex ∉ vertexFinset H)
    (x : CompletionCoordinate H current stage → Bool) :
    ChernoffFinite.bitCount
      (stageLinearUpperActive H current stage (Sum.inr c4)) x = 0 := by
  rw [ChernoffFinite.bitCount]
  apply Finset.sum_eq_zero
  intro i _hi
  simp [stageLinearUpperActive_C4_false_of_not_mem_vertexFinset
    H current stage c4 hv i]

theorem bitMean_stageLinearUpperActive_C4_eq_zero_of_not_mem_vertexFinset
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (p : CompletionCoordinate H current stage → ℝ)
    (c4 : StageC4Index H stage) (hv : c4.vertex ∉ vertexFinset H) :
    ChernoffFinite.bitMean p
      (stageLinearUpperActive H current stage (Sum.inr c4)) = 0 := by
  rw [ChernoffFinite.bitMean]
  apply Finset.sum_eq_zero
  intro i _hi
  simp [stageLinearUpperActive_C4_false_of_not_mem_vertexFinset
    H current stage c4 hv i]

omit [Fintype V] in
theorem codegree_conflictLayer_eq_zero_of_not_subset
    {H : Hypergraph V} {D : ConflictSystem V}
    (hD : IsConflictSystem H D) (stage : ℕ) (root : Hypergraph V)
    (hroot : ¬root ⊆ H) :
    codegree (conflictLayer D stage) root = 0 := by
  rw [codegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hcLayer hrootc
  apply hroot
  exact hrootc.trans (hD c (mem_conflictLayer.mp hcLayer).1)

omit [Fintype V] in
theorem conditionC4Count_eq_zero_of_not_mem_vertexFinset
    (H : Hypergraph V) (D : ConflictSystem V)
    (e : Finset V) (v : V) (hv : v ∉ vertexFinset H) :
    conditionC4Count H D e v = 0 := by
  rw [conditionC4Count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g hg hvg
  exact hv (mem_vertexFinset.mpr
    ⟨g, (Finset.mem_filter.mp hg).1, hvg⟩)

def RestrictedLinearUpperBounds
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (x : CompletionCoordinate H current stage → Bool)
    (threshold : RestrictedStageLinearUpperIndex H stage → ℝ) : Prop :=
  ∀ a, ChernoffFinite.bitCount
      (restrictedStageLinearUpperActive H current stage a) x <
    2 * threshold a

def RestrictedPropertyIIRoom
    (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ)
    (threshold : RestrictedStageLinearUpperIndex H stage → ℝ) : Prop :=
  ∀ root : RestrictedStageCodegreeIndex H stage,
    (codegree (conflictLayer current stage) root.1 : ℝ) +
        2 * threshold (Sum.inl root) ≤
      Real.rpow d ((stage : ℝ) - (root.1.card : ℝ) - eps / 4)

def RestrictedPropertyIIIRoom
    (H : Hypergraph V) (current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ)
    (threshold : RestrictedStageLinearUpperIndex H stage → ℝ) : Prop :=
  ∀ c4 : RestrictedStageC4Index H stage,
    (conditionC4Count H current c4.edge c4.vertex : ℝ) +
        2 * threshold (Sum.inr c4) ≤ Real.rpow d (1 - eps / 4)

theorem bitCount_restrictedStageLinearUpperActive_codegree
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (root : RestrictedStageCodegreeIndex H stage)
    (x : CompletionCoordinate H current stage → Bool) :
    ChernoffFinite.bitCount
        (restrictedStageLinearUpperActive H current stage (Sum.inl root)) x =
      sampledCount (completionCandidate H current stage)
        (fun B => root.1 ⊆ B) x := rfl

theorem bitCount_restrictedStageLinearUpperActive_C4
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (c4 : RestrictedStageC4Index H stage)
    (x : CompletionCoordinate H current stage → Bool) :
    ChernoffFinite.bitCount
        (restrictedStageLinearUpperActive H current stage (Sum.inr c4)) x =
      sampledCount (completionCandidate H current stage)
        (fun B => CandidateCreatesC4 c4.edge c4.vertex B) x := rfl

theorem stagePropertiesIIIII_of_restrictedLinearBounds
    (H : Hypergraph V) (current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (d eps : ℝ) (hd : 0 ≤ d) (stage : ℕ) (hstage4 : stage ≤ 4)
    (x : CompletionCoordinate H current stage → Bool)
    (threshold : RestrictedStageLinearUpperIndex H stage → ℝ)
    (hlinear : RestrictedLinearUpperBounds H current stage x threshold)
    (hII : RestrictedPropertyIIRoom H current d eps stage threshold)
    (hIII : RestrictedPropertyIIIRoom H current d eps stage threshold) :
    StagePropertyII H
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        d eps stage ∧
      StagePropertyIII H
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        d eps stage := by
  classical
  let A := sampledCompletionLayer (completionCandidate H current stage) x
  have hA : IsConflictSystem H A := by
    intro c hc
    exact completionCandidates_isConflictSystem H current stage c
      (sampledSourceCompletionLayer_subset_candidates H current stage x hc)
  have hnext : IsConflictSystem H (addCompletionLayer current A) :=
    addCompletionLayer_isConflictSystem hcurrent hA
  constructor
  · rw [StagePropertyII]
    intro q hq2 hqstage root hroot
    by_cases hrootH : root ⊆ H
    · let indexed : RestrictedStageCodegreeIndex H stage :=
        ⟨root, hrootH, by omega, by omega⟩
      have hcount : sampledCount (completionCandidate H current stage)
          (fun B => root ⊆ B) x ≤ 2 * threshold (Sum.inl indexed) := by
        rw [← bitCount_restrictedStageLinearUpperActive_codegree
          H current stage indexed x]
        exact (hlinear (Sum.inl indexed)).le
      apply codegree_addCompletionLayer_sampled_le_of_count
        H current stage x root (2 * threshold (Sum.inl indexed))
      · simpa [indexed] using hcount
      · simpa [RestrictedPropertyIIRoom, indexed, hroot] using hII indexed
    · change (codegree (conflictLayer (addCompletionLayer current A) stage)
          root : ℝ) ≤ _
      rw [codegree_conflictLayer_eq_zero_of_not_subset hnext stage root hrootH]
      simpa only [Nat.cast_zero, Real.rpow_eq_pow] using
        Real.rpow_nonneg hd ((stage : ℝ) - (q : ℝ) - eps / 4)
  · rw [StagePropertyIII]
    intro hstage2
    subst stage
    intro e he v
    by_cases hv : v ∈ vertexFinset H
    · let indexed : RestrictedStageC4Index H 2 :=
        RestrictedStageC4Index.mk e he v hv rfl
      have hcount :
          (((sampledCompletionLayer (completionCandidate H current 2) x).filter
            fun B => CandidateCreatesC4 e v B).card : ℝ) ≤
            2 * threshold (Sum.inr indexed) := by
        have hbit := hlinear (Sum.inr indexed)
        rw [bitCount_restrictedStageLinearUpperActive_C4
            H current 2 indexed x,
          sampledCount_eq_filter_card (completionCandidate H current 2)
            (completionCandidate_injective H current 2)
            (fun B => CandidateCreatesC4 e v B) x] at hbit
        exact hbit.le
      apply conditionC4Count_addCompletionLayer_le_of_count
        H current e v x (2 * threshold (Sum.inr indexed))
      · exact hcount
      · simpa [RestrictedPropertyIIIRoom, indexed] using hIII indexed
    · rw [conditionC4Count_eq_zero_of_not_mem_vertexFinset
        H (addCompletionLayer current A) e v hv]
      simpa only [Nat.cast_zero, Real.rpow_eq_pow] using
        Real.rpow_nonneg hd (1 - eps / 4)

end UpperObservables

end CFMRegularization
end Erdos136

/- The live copy of this wrapper is placed after the active-test API below.
This preserved draft is nested in a comment only to keep the interrupted
edit recoverable while the source is assembled in small patches.

namespace Erdos136
namespace CFMRegularization

open Finset
open scoped BigOperators
open UpperObservables

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V : Type*} [Fintype V]

/-- Source-weighted completion at one rank, with the polynomial restricted
linear family and only the genuinely active weighted tests in the finite
failure sum. -/
theorem exists_concreteRegularizationStageRestrictedActive_nonempty
    {ι : Type*} [Fintype ι]
    (H : Hypergraph V) (base current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (d eps Gamma : ℝ) (stage : ℕ) (target pmax : ℝ)
    (degreeDelta degreeRoom : ConcreteStageDegreeIndex H → ℝ)
    (linearThreshold : RestrictedStageLinearUpperIndex H stage → ℝ)
    (blockThreshold : StageBlockUpperIndex H current stage → ℝ)
    (testJ : ι → ℕ) (w : ι → TestWeight V)
    (gap limit : ι → ℝ)
    (hH : H.Nonempty) (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (htarget : target = completionTarget d eps
      (layerMaxDegree H base stage : ℝ) stage)
    (hdef : HasSourceDeficitBoundsAtTarget H current d eps Gamma target stage)
    (hweightMax : ∀ A ∈ H.powersetCard stage,
      completionWeight H stage (degreeDeficit current stage target) A ≤ pmax)
    (hpmaxOne : pmax ≤ 1)
    (hdegreeRoom : ∀ e : ConcreteStageDegreeIndex H,
      12 * (4 * Gamma * Real.rpow d ((stage : ℝ) - 1)) ^ 2 /
          totalDeficit H (degreeDeficit current stage target) +
        ((forbiddenIncidentCompletions H current stage e.1).card : ℝ) * pmax ≤
          degreeRoom e)
    (hdegreeMargin : ∀ e : ConcreteStageDegreeIndex H,
      degreeDelta e * ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (concreteStageDegreeActive H current stage e) ≤
        Real.rpow d (-eps) * target - degreeRoom e)
    (hdelta0 : ∀ e, 0 ≤ degreeDelta e)
    (hdelta1 : ∀ e, degreeDelta e ≤ 1)
    (hlinear0 : ∀ a, 0 ≤ linearThreshold a)
    (hlinearMean : ∀ a,
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (restrictedStageLinearUpperActive H current stage a) ≤
        linearThreshold a)
    (hblock0 : ∀ a, 0 ≤ blockThreshold a)
    (hblockMean : ∀ a,
      BlockChernoff.blockMean
          (sourceCompletionBiasAtTarget H current stage target)
          (concreteStageBlockFamily H current stage a) ≤
        blockThreshold a)
    (hII : RestrictedPropertyIIRoom H current d eps stage linearThreshold)
    (hIII : RestrictedPropertyIIIRoom H current d eps stage linearThreshold)
    (hIV : PropertyIVRoom H current d eps stage blockThreshold)
    (hV : PropertyVRoom H current d eps stage blockThreshold)
    (hw : ∀ a S, 0 ≤ w a S)
    (hfreeZero : ∀ a S, S ∈ H.powersetCard (testJ a) →
      (∃ c ∈ current, c ⊆ S) → w a S = 0)
    (hgap : ∀ a : ActiveStageTest H current stage testJ w, 0 ≤ gap a.1)
    (hlimitPos : ∀ a, 0 < limit a)
    (hkillRoom : ∀ a : ActiveStageTest H current stage testJ w,
      (∑ i, pmax * testExtension (w a.1) H (testJ a.1)
          (completionCandidate H current stage i)) + gap a.1 ≤ limit a.1)
    (hfail :
      (∑ e : ConcreteStageDegreeIndex H,
          2 * Real.exp (-(degreeDelta e ^ 2 *
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (concreteStageDegreeActive H current stage e)) / 3)) +
        (∑ a : RestrictedStageLinearUpperIndex H stage,
          Real.exp (-linearThreshold a / 3)) +
        (∑ a : StageBlockUpperIndex H current stage,
          Real.exp (-blockThreshold a / 3)) +
        (∑ a : ActiveStageTest H current stage testJ w,
          Real.exp (-2 * gap a.1 ^ 2 /
            ∑ i, (testExtension (w a.1) H (testJ a.1)
              (completionCandidate H current stage i)) ^ 2)) < 1) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H current stage ∧
      HasStagePropertiesIV H base (addCompletionLayer current A) d eps stage ∧
      ∀ a, killedWeight H (addCompletionLayer current A)
        (testJ a) (w a) < limit a := by
  let U : ℝ := 4 * Gamma * Real.rpow d ((stage : ℝ) - 1)
  let p := sourceCompletionBiasAtTarget H current stage target
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have ha0 : ∀ e ∈ H, 0 ≤ degreeDeficit current stage target e := by
    intro e he
    exact (Real.rpow_nonneg hd.le _).trans (hdef.2.2 e he).1
  have haU : ∀ e ∈ H, degreeDeficit current stage target e ≤ U := by
    intro e he
    exact hdef.2.2 e he |>.2
  have hLpos : 0 < Real.rpow d ((stage : ℝ) - 1 - 2 * eps) :=
    Real.rpow_pos_of_pos hd _
  have hcardpos : 0 < (H.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hH
  have htotal : 0 < totalDeficit H (degreeDeficit current stage target) := by
    apply (mul_pos hcardpos hLpos).trans_le
    apply card_mul_le_totalDeficit
    intro e he
    exact (hdef.2.2 e he).1
  have hprobMax : ∀ i, p i ≤ pmax := by
    intro i
    apply hweightMax
    exact Finset.mem_powersetCard.mpr
      ⟨(mem_completionCandidates.mp (completionCandidate_mem H current stage i)).1,
       (mem_completionCandidates.mp (completionCandidate_mem H current stage i)).2.1⟩
  have hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1 := by
    apply sourceCompletionBiasAtTarget_mem_Icc H current d eps Gamma target stage
      hd.le hdef
    intro i
    exact (hprobMax i).trans hpmaxOne
  have hdegreeMean : ∀ e : ConcreteStageDegreeIndex H,
      |(degree (conflictLayer current stage) e.1 : ℝ) +
          ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e) - target| ≤
        degreeRoom e := by
    intro e
    have herr := sourceIncidentMean_error H current stage hdef.1 hdef.2.1
      target U pmax e.2 hU ha0 haU htotal hweightMax
    have herr' :
        |ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e) -
          degreeDeficit current stage target e.1| ≤ degreeRoom e := by
      apply herr.trans
      simpa [U, p, concreteStageDegreeActive] using hdegreeRoom e
    rw [show (degree (conflictLayer current stage) e.1 : ℝ) +
        ChernoffFinite.bitMean p
          (concreteStageDegreeActive H current stage e) - target =
        ChernoffFinite.bitMean p
          (concreteStageDegreeActive H current stage e) -
            degreeDeficit current stage target e.1 by
      simp [degreeDeficit]
      ring]
    exact herr'
  have hkillMean : ∀ a : ActiveStageTest H current stage testJ w,
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (sampledKilledWeight H (testJ a.1) (w a.1)
            (completionCandidate H current stage)) + gap a.1 ≤ limit a.1 := by
    intro a
    have hmean := weightedMean_sampledKilledWeight_le H
      (testJ a.1) (w a.1) (completionCandidate H current stage) p (hw a.1) hp
    calc
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (sampledKilledWeight H (testJ a.1) (w a.1)
            (completionCandidate H current stage)) + gap a.1 ≤
          (∑ i, p i * testExtension (w a.1) H (testJ a.1)
            (completionCandidate H current stage i)) + gap a.1 :=
        add_le_add hmean le_rfl
      _ ≤ (∑ i, pmax * testExtension (w a.1) H (testJ a.1)
            (completionCandidate H current stage i)) + gap a.1 := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro i _hi
          apply mul_le_mul_of_nonneg_right (hprobMax i)
          exact testExtension_nonneg (hw a.1) H (testJ a.1) _
        · exact le_rfl
      _ ≤ limit a.1 := hkillRoom a
  have hdecode : ∀ x,
      (∀ e,
        |ChernoffFinite.bitCount
            (concreteStageDegreeActive H current stage e) x -
          ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e)| <
          degreeDelta e * ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e)) →
      (∀ a, ChernoffFinite.bitCount
            (restrictedStageLinearUpperActive H current stage a) x <
        2 * linearThreshold a) →
      (∀ a, BlockChernoff.blockCount
          (concreteStageBlockFamily H current stage a) x <
        2 * blockThreshold a) →
      HasStagePropertiesIV H base
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        d eps stage := by
    intro x hrel hlinear hblock
    have hdegree : ∀ e ∈ H,
        InRelativeInterval
          (degree (conflictLayer
            (addCompletionLayer current
              (sampledCompletionLayer (completionCandidate H current stage) x))
            stage) e : ℝ)
          (completionTarget d eps (layerMaxDegree H base stage : ℝ) stage)
          (Real.rpow d (-eps)) := by
      intro e he
      let ee : ConcreteStageDegreeIndex H := ⟨e, he⟩
      have hdev := (hrel ee).trans_le (hdegreeMargin ee)
      rw [degree_addCompletionLayer_sampled_eq]
      have hinterval := inRelativeInterval_of_mean_room
        (hdegreeMean ee) (by
          simpa [p, ee, concreteStageDegreeActive,
            bitCount_degree_eq_sampledCount] using hdev)
      simpa [htarget] using hinterval
    have hlinearProps := stagePropertiesIIIII_of_restrictedLinearBounds
      H current hcurrent d eps hd.le stage hdef.2.1 x linearThreshold
      hlinear hII hIII
    have hblockBounds : BlockUpperBounds H current stage x blockThreshold := by
      intro a
      rw [← blockCount_concreteStageBlockFamily_eq H current stage a x]
      exact hblock a
    refine ⟨hdef.1, hdef.2.1, hdegree, hlinearProps.1, hlinearProps.2, ?_, ?_⟩
    · exact stagePropertyIV_of_blockBounds H current hcurrent d eps stage x
        blockThreshold hblockBounds hIV
    · exact stagePropertyV_of_blockBounds H current d eps stage hdef.1 x
        blockThreshold hblockBounds hV
  exact exists_regularizationStageWithBlocks_activeTests
    H base current d eps stage target
    (concreteStageDegreeActive H current stage) degreeDelta
    (restrictedStageLinearUpperActive H current stage) linearThreshold
    (concreteStageBlockSize H current stage)
    (concreteStageBlockFamily H current stage) blockThreshold
    testJ w gap limit hp hdelta0 hdelta1 hlinear0 hlinearMean
    (concreteStageBlockFamily_pairwiseDisjoint H current stage)
    hblock0 hblockMean hw hfreeZero hgap hlimitPos hkillMean hfail hdecode

end
end CFMRegularization
end Erdos136
-/

namespace Erdos136
namespace CFMRegularization

/-! ### Active weighted tests -/

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Sum of squared coordinate sensitivities of one test at one completion
stage.  This is the denominator in the McDiarmid failure term. -/
noncomputable def stageTestInfluenceSq
    {V ι : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (testJ : ι → ℕ) (w : ι → TestWeight V) (a : ι) : ℝ :=
  ∑ i, (testExtension (w a) H (testJ a)
    (completionCandidate H current stage i)) ^ 2

/-- Only tests whose rank reaches the current completion rank and whose
McDiarmid denominator is strictly positive enter the probabilistic family. -/
def IsActiveStageTest
    {V ι : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (testJ : ι → ℕ) (w : ι → TestWeight V) (a : ι) : Prop :=
  stage ≤ testJ a ∧ 0 < stageTestInfluenceSq H current stage testJ w a

/-- Finite subtype used as the `ιtest` argument of
`exists_regularizationStageWithBlocks`. -/
abbrev ActiveStageTest
    {V ι : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (testJ : ι → ℕ) (w : ι → TestWeight V) :=
  {a : ι // IsActiveStageTest H current stage testJ w a}

theorem stageTestInfluenceSq_nonneg
    {V ι : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (testJ : ι → ℕ) (w : ι → TestWeight V) (a : ι) :
    0 ≤ stageTestInfluenceSq H current stage testJ w a := by
  unfold stageTestInfluenceSq
  positivity

theorem testExtension_eq_zero_of_influenceSq_eq_zero
    {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V)
    (testJ stage : ℕ) (w : TestWeight V)
    (hsq : (∑ i, (testExtension w H testJ
      (completionCandidate H current stage i)) ^ 2) = 0) :
    ∀ i, testExtension w H testJ
      (completionCandidate H current stage i) = 0 := by
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (s := (Finset.univ : Finset
      (Fin (Fintype.card (CompletionIndex H current stage)))))
    (f := fun i => (testExtension w H testJ
      (completionCandidate H current stage i)) ^ 2)
    (fun i _ => sq_nonneg _)).mp hsq
  intro i
  have hi := hall i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

theorem sampledKilledWeight_eq_zero_of_influenceSq_eq_zero
    {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V)
    (testJ stage : ℕ) (w : TestWeight V)
    (hw : ∀ S, 0 ≤ w S)
    (hsq : (∑ i, (testExtension w H testJ
      (completionCandidate H current stage i)) ^ 2) = 0)
    (x : Fin (Fintype.card (CompletionIndex H current stage)) → Bool) :
    sampledKilledWeight H testJ w
      (completionCandidate H current stage) x = 0 := by
  have hext := testExtension_eq_zero_of_influenceSq_eq_zero
    H current testJ stage w hsq
  rw [sampledKilledWeight]
  apply Finset.sum_eq_zero
  intro S hS
  by_cases hkill : ∃ i, x i = true ∧
      completionCandidate H current stage i ⊆ S
  · have hkill' := hkill
    obtain ⟨i, _hxi, hiS⟩ := hkill
    have hle : w S ≤ testExtension w H testJ
        (completionCandidate H current stage i) := by
      rw [testExtension]
      exact Finset.single_le_sum (fun T _hT => hw T)
        (Finset.mem_filter.mpr ⟨hS, hiS⟩)
    have hz : w S = 0 := by
      apply le_antisymm
      · simpa [hext i] using hle
      · exact hw S
    simp [hkill', hz]
  · simp [hkill]

theorem sampledKilledWeight_eq_zero_of_not_active
    {V ι : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (testJ : ι → ℕ) (w : ι → TestWeight V)
    (hw : ∀ a S, 0 ≤ w a S) {a : ι}
    (ha : ¬IsActiveStageTest H current stage testJ w a)
    (x : Fin (Fintype.card (CompletionIndex H current stage)) → Bool) :
    sampledKilledWeight H (testJ a) (w a)
      (completionCandidate H current stage) x = 0 := by
  by_cases hj : stage ≤ testJ a
  · have hnotpos : ¬0 < stageTestInfluenceSq H current stage testJ w a := by
      exact fun hpos => ha ⟨hj, hpos⟩
    have hsq : stageTestInfluenceSq H current stage testJ w a = 0 :=
      le_antisymm (not_lt.mp hnotpos)
        (stageTestInfluenceSq_nonneg H current stage testJ w a)
    exact sampledKilledWeight_eq_zero_of_influenceSq_eq_zero
      H current (testJ a) stage (w a) (hw a) (by simpa [stageTestInfluenceSq] using hsq) x
  · rw [sampledKilledWeight]
    apply Finset.sum_eq_zero
    intro S hS
    have hScard : S.card = testJ a :=
      (Finset.mem_powersetCard.mp hS).2
    simp only [ite_eq_right_iff]
    rintro ⟨i, hxi, hiS⟩
    have histage : (completionCandidate H current stage i).card = stage :=
      (mem_completionCandidates.mp
        (completionCandidate_mem H current stage i)).2.1
    have hle := Finset.card_le_card hiS
    omega

/-- Select exactly a prescribed subfamily of completion candidates. -/
noncomputable def completionLayerSelectionBits
    {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (A : ConflictSystem V) :
    Fin (Fintype.card (CompletionIndex H current stage)) → Bool :=
  fun i => decide (completionCandidate H current stage i ∈ A)

theorem sampledCompletionLayer_selectionBits_eq
    {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (A : ConflictSystem V) (hA : A ⊆ completionCandidates H current stage) :
    sampledCompletionLayer (completionCandidate H current stage)
      (completionLayerSelectionBits H current stage A) = A := by
  ext B
  constructor
  · intro hB
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hB
    have hbit := (Finset.mem_filter.mp hi).2
    simpa [completionLayerSelectionBits] using hbit
  · intro hB
    let q : CompletionIndex H current stage := ⟨B, hA hB⟩
    let i : Fin (Fintype.card (CompletionIndex H current stage)) :=
      Fintype.equivFin (CompletionIndex H current stage) q
    have hcand : completionCandidate H current stage i = B := by
      simp [completionCandidate, i, q]
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, hcand⟩
    simp [completionLayerSelectionBits, hcand, hB]

theorem killedWeight_eq_zero_of_not_active
    {V ι : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (testJ : ι → ℕ) (w : ι → TestWeight V)
    (hw : ∀ a S, 0 ≤ w a S)
    (hfreeZero : ∀ a S, S ∈ H.powersetCard (testJ a) →
      (∃ c ∈ current, c ⊆ S) → w a S = 0)
    (A : ConflictSystem V) (hA : A ⊆ completionCandidates H current stage)
    {a : ι} (ha : ¬IsActiveStageTest H current stage testJ w a) :
    killedWeight H (addCompletionLayer current A) (testJ a) (w a) = 0 := by
  let x := completionLayerSelectionBits H current stage A
  have hAx : sampledCompletionLayer
      (completionCandidate H current stage) x = A :=
    sampledCompletionLayer_selectionBits_eq H current stage A hA
  rw [← hAx]
  rw [killedWeight_addCompletionLayer_eq_sampledKilledWeight H current
    (testJ a) (w a) (completionCandidate H current stage) x
    (hw a) (hfreeZero a)]
  exact sampledKilledWeight_eq_zero_of_not_active
    H current stage testJ w hw ha x

/-- Extend a strict killed-mass estimate from the active subtype to every
original test.  Inactive tests have exactly zero new loss. -/
theorem killedWeight_lt_all_of_active
    {V ι : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (testJ : ι → ℕ) (w : ι → TestWeight V)
    (hw : ∀ a S, 0 ≤ w a S)
    (hfreeZero : ∀ a S, S ∈ H.powersetCard (testJ a) →
      (∃ c ∈ current, c ⊆ S) → w a S = 0)
    (A : ConflictSystem V) (hA : A ⊆ completionCandidates H current stage)
    (limit : ι → ℝ) (hlimit : ∀ a, 0 < limit a)
    (hactive : ∀ a : ActiveStageTest H current stage testJ w,
      killedWeight H (addCompletionLayer current A)
        (testJ a.1) (w a.1) < limit a.1) :
    ∀ a, killedWeight H (addCompletionLayer current A)
      (testJ a) (w a) < limit a := by
  intro a
  by_cases ha : IsActiveStageTest H current stage testJ w a
  · exact hactive ⟨a, ha⟩
  · rw [killedWeight_eq_zero_of_not_active H current stage testJ w hw
      hfreeZero A hA ha]
    exact hlimit a

theorem card_activeStageTest_le
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (testJ : ι → ℕ) (w : ι → TestWeight V) :
    Fintype.card (ActiveStageTest H current stage testJ w) ≤
      Fintype.card ι := by
  exact Fintype.card_subtype_le _

theorem activeStageTest_property
    {V ι : Type*} [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (testJ : ι → ℕ) (w : ι → TestWeight V)
    (a : ActiveStageTest H current stage testJ w) :
    stage ≤ testJ a.1 ∧
      0 < ∑ i, (testExtension (w a.1) H (testJ a.1)
        (completionCandidate H current stage i)) ^ 2 := by
  simpa [IsActiveStageTest, stageTestInfluenceSq] using a.2

theorem sum_sq_testExtension_mono
    {V : Type*} [DecidableEq V] {n : ℕ}
    (H : Hypergraph V) (testJ : ℕ)
    (w' w : TestWeight V) (candidate : Fin n → Hypergraph V)
    (hw' : ∀ S, 0 ≤ w' S) (hw : ∀ S, 0 ≤ w S)
    (hext : ∀ i, testExtension w' H testJ (candidate i) ≤
      testExtension w H testJ (candidate i)) :
    (∑ i, (testExtension w' H testJ (candidate i)) ^ 2) ≤
      ∑ i, (testExtension w H testJ (candidate i)) ^ 2 := by
  apply Finset.sum_le_sum
  intro i hi
  have hlo := testExtension_nonneg hw' H testJ (candidate i)
  have hhi := testExtension_nonneg hw H testJ (candidate i)
  nlinarith [hext i]

theorem sum_sq_testExtension_restrictWeight_le
    {V : Type*} [DecidableEq V] {n : ℕ}
    (H : Hypergraph V) (D : ConflictSystem V) (testJ : ℕ)
    (w : TestWeight V) (candidate : Fin n → Hypergraph V)
    (hw : ∀ S, 0 ≤ w S) :
    (∑ i, (testExtension (restrictWeight D w) H testJ
      (candidate i)) ^ 2) ≤
      ∑ i, (testExtension w H testJ (candidate i)) ^ 2 := by
  apply sum_sq_testExtension_mono H testJ (restrictWeight D w) w candidate
    (restrictWeight_nonneg hw) hw
  intro i
  exact testExtension_restrictWeight_le H D testJ (candidate i) w hw

theorem sum_sq_testExtension_two_restrictWeights_le
    {V : Type*} [DecidableEq V] {n : ℕ}
    (H : Hypergraph V) (D₁ D₂ : ConflictSystem V) (testJ : ℕ)
    (w : TestWeight V) (candidate : Fin n → Hypergraph V)
    (hw : ∀ S, 0 ≤ w S) :
    (∑ i, (testExtension (restrictWeight D₂ (restrictWeight D₁ w))
      H testJ (candidate i)) ^ 2) ≤
      ∑ i, (testExtension w H testJ (candidate i)) ^ 2 := by
  exact (sum_sq_testExtension_restrictWeight_le H D₂ testJ
    (restrictWeight D₁ w) candidate (restrictWeight_nonneg hw)).trans
      (sum_sq_testExtension_restrictWeight_le H D₁ testJ w candidate hw)

/-- Invoke the four-family stage extractor only on tests with a genuinely
positive McDiarmid denominator, then extend its loss conclusion to all test
indices using the deterministic inactive-zero theorem. -/
theorem exists_regularizationStageWithBlocks_activeTests
    {V ιrel ιupper ιblock ι : Type*} [DecidableEq V]
    [Fintype ιrel] [Fintype ιupper] [Fintype ιblock] [Fintype ι]
    (H : Hypergraph V) (base current : ConflictSystem V)
    (d eps : ℝ) (stage : ℕ) (target : ℝ)
    (activeRel : ιrel →
      Fin (Fintype.card (CompletionIndex H current stage)) → Prop)
    (delta : ιrel → ℝ)
    (activeUpper : ιupper →
      Fin (Fintype.card (CompletionIndex H current stage)) → Prop)
    (threshold : ιupper → ℝ)
    (blockSize : ιblock → ℕ)
    (blocks : ∀ a, Fin (blockSize a) →
      Finset (Fin (Fintype.card (CompletionIndex H current stage))))
    (blockThreshold : ιblock → ℝ)
    (testJ : ι → ℕ) (w : ι → TestWeight V)
    (gap limit : ι → ℝ)
    (hp : ∀ i, sourceCompletionBiasAtTarget H current stage target i ∈
      Set.Icc (0 : ℝ) 1)
    (hdelta0 : ∀ a, 0 ≤ delta a) (hdelta1 : ∀ a, delta a ≤ 1)
    (hthreshold0 : ∀ a, 0 ≤ threshold a)
    (hupperMean : ∀ a,
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (activeUpper a) ≤ threshold a)
    (hblockDisj : ∀ a,
      (Set.univ : Set (Fin (blockSize a))).PairwiseDisjoint (blocks a))
    (hblockThreshold0 : ∀ a, 0 ≤ blockThreshold a)
    (hblockMean : ∀ a,
      BlockChernoff.blockMean
          (sourceCompletionBiasAtTarget H current stage target)
          (blocks a) ≤ blockThreshold a)
    (hw : ∀ a S, 0 ≤ w a S)
    (hfreeZero : ∀ a S, S ∈ H.powersetCard (testJ a) →
      (∃ c ∈ current, c ⊆ S) → w a S = 0)
    (hgap : ∀ a : ActiveStageTest H current stage testJ w,
      0 ≤ gap a.1)
    (hlimitPos : ∀ a, 0 < limit a)
    (hkillMean : ∀ a : ActiveStageTest H current stage testJ w,
      McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight
            (sourceCompletionBiasAtTarget H current stage target))
          (sampledKilledWeight H (testJ a.1) (w a.1)
            (completionCandidate H current stage)) + gap a.1 ≤ limit a.1)
    (hfail :
      (∑ a : ιrel,
          2 * Real.exp (-(delta a ^ 2 *
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (activeRel a)) / 3)) +
        (∑ a : ιupper, Real.exp (-threshold a / 3)) +
        (∑ a : ιblock, Real.exp (-blockThreshold a / 3)) +
        (∑ a : ActiveStageTest H current stage testJ w,
          Real.exp (-2 * gap a.1 ^ 2 /
            ∑ i, (testExtension (w a.1) H (testJ a.1)
              (completionCandidate H current stage i)) ^ 2)) < 1)
    (hdecode : ∀ x,
      (∀ a,
        |ChernoffFinite.bitCount (activeRel a) x -
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (activeRel a)| <
          delta a * ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H current stage target)
            (activeRel a)) →
      (∀ a, ChernoffFinite.bitCount (activeUpper a) x <
        2 * threshold a) →
      (∀ a, BlockChernoff.blockCount (blocks a) x <
        2 * blockThreshold a) →
      HasStagePropertiesIV H base
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        d eps stage) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H current stage ∧
      HasStagePropertiesIV H base (addCompletionLayer current A)
        d eps stage ∧
      ∀ a, killedWeight H (addCompletionLayer current A)
        (testJ a) (w a) < limit a := by
  let activeJ : ActiveStageTest H current stage testJ w → ℕ :=
    fun a => testJ a.1
  let activeW : ActiveStageTest H current stage testJ w → TestWeight V :=
    fun a => w a.1
  let activeGap : ActiveStageTest H current stage testJ w → ℝ :=
    fun a => gap a.1
  let activeLimit : ActiveStageTest H current stage testJ w → ℝ :=
    fun a => limit a.1
  obtain ⟨A, hA, hstage, hactive⟩ :=
    exists_regularizationStageWithBlocks
      H base current d eps stage target activeRel delta activeUpper threshold
      blockSize blocks blockThreshold activeJ activeW activeGap activeLimit hp
      hdelta0 hdelta1 hthreshold0 hupperMean hblockDisj hblockThreshold0
      hblockMean
      (fun a S => hw a.1 S)
      (fun a S hS hcontains => hfreeZero a.1 S hS hcontains)
      (by simpa [activeGap] using hgap)
      (by simpa [activeJ, activeW, activeGap, activeLimit] using hkillMean)
      (by simpa [activeJ, activeW, activeGap] using hfail)
      hdecode
  refine ⟨A, hA, hstage, ?_⟩
  apply killedWeight_lt_all_of_active H current stage testJ w hw hfreeZero
    A hA limit hlimitPos
  simpa [activeJ, activeW, activeLimit] using hactive


end CFMRegularization
end Erdos136

namespace Erdos136
namespace CFMRegularization

open Finset
open scoped BigOperators
open UpperObservables

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V : Type*} [Fintype V]

/-- Source-weighted completion at one rank, with the polynomial restricted
linear family and only the genuinely active weighted tests in the finite
failure sum. -/
theorem exists_concreteRegularizationStageRestrictedActive_nonempty
    {ι : Type*} [Fintype ι]
    (H : Hypergraph V) (base current : ConflictSystem V)
    (hcurrent : IsConflictSystem H current)
    (d eps Gamma : ℝ) (stage : ℕ) (target pmax : ℝ)
    (degreeDelta degreeRoom : ConcreteStageDegreeIndex H → ℝ)
    (linearThreshold : RestrictedStageLinearUpperIndex H stage → ℝ)
    (blockThreshold : StageBlockUpperIndex H current stage → ℝ)
    (testJ : ι → ℕ) (w : ι → TestWeight V)
    (gap limit : ι → ℝ)
    (hH : H.Nonempty) (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (htarget : target = completionTarget d eps
      (layerMaxDegree H base stage : ℝ) stage)
    (hdef : HasSourceDeficitBoundsAtTarget H current d eps Gamma target stage)
    (hweightMax : ∀ A ∈ H.powersetCard stage,
      completionWeight H stage (degreeDeficit current stage target) A ≤ pmax)
    (hpmaxOne : pmax ≤ 1)
    (hdegreeRoom : ∀ e : ConcreteStageDegreeIndex H,
      12 * (4 * Gamma * Real.rpow d ((stage : ℝ) - 1)) ^ 2 /
          totalDeficit H (degreeDeficit current stage target) +
        ((forbiddenIncidentCompletions H current stage e.1).card : ℝ) * pmax ≤
          degreeRoom e)
    (hdegreeMargin : ∀ e : ConcreteStageDegreeIndex H,
      degreeDelta e * ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (concreteStageDegreeActive H current stage e) ≤
        Real.rpow d (-eps) * target - degreeRoom e)
    (hdelta0 : ∀ e, 0 ≤ degreeDelta e)
    (hdelta1 : ∀ e, degreeDelta e ≤ 1)
    (hlinear0 : ∀ a, 0 ≤ linearThreshold a)
    (hlinearMean : ∀ a,
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (restrictedStageLinearUpperActive H current stage a) ≤
        linearThreshold a)
    (hblock0 : ∀ a, 0 ≤ blockThreshold a)
    (hblockMean : ∀ a,
      BlockChernoff.blockMean
          (sourceCompletionBiasAtTarget H current stage target)
          (concreteStageBlockFamily H current stage a) ≤
        blockThreshold a)
    (hII : RestrictedPropertyIIRoom H current d eps stage linearThreshold)
    (hIII : RestrictedPropertyIIIRoom H current d eps stage linearThreshold)
    (hIV : PropertyIVRoom H current d eps stage blockThreshold)
    (hV : PropertyVRoom H current d eps stage blockThreshold)
    (hw : ∀ a S, 0 ≤ w a S)
    (hfreeZero : ∀ a S, S ∈ H.powersetCard (testJ a) →
      (∃ c ∈ current, c ⊆ S) → w a S = 0)
    (hgap : ∀ a : ActiveStageTest H current stage testJ w, 0 ≤ gap a.1)
    (hlimitPos : ∀ a, 0 < limit a)
    (hkillRoom : ∀ a : ActiveStageTest H current stage testJ w,
      (∑ i, pmax * testExtension (w a.1) H (testJ a.1)
          (completionCandidate H current stage i)) + gap a.1 ≤ limit a.1)
    (hfail :
      (∑ e : ConcreteStageDegreeIndex H,
          2 * Real.exp (-(degreeDelta e ^ 2 *
            ChernoffFinite.bitMean
              (sourceCompletionBiasAtTarget H current stage target)
              (concreteStageDegreeActive H current stage e)) / 3)) +
        (∑ a : RestrictedStageLinearUpperIndex H stage,
          Real.exp (-linearThreshold a / 3)) +
        (∑ a : StageBlockUpperIndex H current stage,
          Real.exp (-blockThreshold a / 3)) +
        (∑ a : ActiveStageTest H current stage testJ w,
          Real.exp (-2 * gap a.1 ^ 2 /
            ∑ i, (testExtension (w a.1) H (testJ a.1)
              (completionCandidate H current stage i)) ^ 2)) < 1) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H current stage ∧
      HasStagePropertiesIV H base (addCompletionLayer current A) d eps stage ∧
      ∀ a, killedWeight H (addCompletionLayer current A)
        (testJ a) (w a) < limit a := by
  let U : ℝ := 4 * Gamma * Real.rpow d ((stage : ℝ) - 1)
  let p := sourceCompletionBiasAtTarget H current stage target
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have ha0 : ∀ e ∈ H, 0 ≤ degreeDeficit current stage target e := by
    intro e he
    exact (Real.rpow_nonneg hd.le _).trans (hdef.2.2 e he).1
  have haU : ∀ e ∈ H, degreeDeficit current stage target e ≤ U := by
    intro e he
    exact hdef.2.2 e he |>.2
  have hLpos : 0 < Real.rpow d ((stage : ℝ) - 1 - 2 * eps) :=
    Real.rpow_pos_of_pos hd _
  have hcardpos : 0 < (H.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hH
  have htotal : 0 < totalDeficit H (degreeDeficit current stage target) := by
    apply (mul_pos hcardpos hLpos).trans_le
    apply card_mul_le_totalDeficit
    intro e he
    exact (hdef.2.2 e he).1
  have hprobMax : ∀ i, p i ≤ pmax := by
    intro i
    apply hweightMax
    exact Finset.mem_powersetCard.mpr
      ⟨(mem_completionCandidates.mp (completionCandidate_mem H current stage i)).1,
       (mem_completionCandidates.mp (completionCandidate_mem H current stage i)).2.1⟩
  have hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1 := by
    apply sourceCompletionBiasAtTarget_mem_Icc H current d eps Gamma target stage
      hd.le hdef
    intro i
    exact (hprobMax i).trans hpmaxOne
  have hdegreeMean : ∀ e : ConcreteStageDegreeIndex H,
      |(degree (conflictLayer current stage) e.1 : ℝ) +
          ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e) - target| ≤
        degreeRoom e := by
    intro e
    have herr := sourceIncidentMean_error H current stage hdef.1 hdef.2.1
      target U pmax e.2 hU ha0 haU htotal hweightMax
    have herr' :
        |ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e) -
          degreeDeficit current stage target e.1| ≤ degreeRoom e := by
      apply herr.trans
      simpa [U, p, concreteStageDegreeActive] using hdegreeRoom e
    rw [show (degree (conflictLayer current stage) e.1 : ℝ) +
        ChernoffFinite.bitMean p
          (concreteStageDegreeActive H current stage e) - target =
        ChernoffFinite.bitMean p
          (concreteStageDegreeActive H current stage e) -
            degreeDeficit current stage target e.1 by
      simp [degreeDeficit]
      ring]
    exact herr'
  have hkillMean : ∀ a : ActiveStageTest H current stage testJ w,
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (sampledKilledWeight H (testJ a.1) (w a.1)
            (completionCandidate H current stage)) + gap a.1 ≤ limit a.1 := by
    intro a
    have hmean := weightedMean_sampledKilledWeight_le H
      (testJ a.1) (w a.1) (completionCandidate H current stage) p (hw a.1) hp
    calc
      McDiarmid.weightedMean (McDiarmid.bernoulliWeight p)
          (sampledKilledWeight H (testJ a.1) (w a.1)
            (completionCandidate H current stage)) + gap a.1 ≤
          (∑ i, p i * testExtension (w a.1) H (testJ a.1)
            (completionCandidate H current stage i)) + gap a.1 :=
        add_le_add hmean le_rfl
      _ ≤ (∑ i, pmax * testExtension (w a.1) H (testJ a.1)
            (completionCandidate H current stage i)) + gap a.1 := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro i _hi
          apply mul_le_mul_of_nonneg_right (hprobMax i)
          exact testExtension_nonneg (hw a.1) H (testJ a.1) _
        · exact le_rfl
      _ ≤ limit a.1 := hkillRoom a
  have hdecode : ∀ x,
      (∀ e,
        |ChernoffFinite.bitCount
            (concreteStageDegreeActive H current stage e) x -
          ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e)| <
          degreeDelta e * ChernoffFinite.bitMean p
            (concreteStageDegreeActive H current stage e)) →
      (∀ a, ChernoffFinite.bitCount
            (restrictedStageLinearUpperActive H current stage a) x <
        2 * linearThreshold a) →
      (∀ a, BlockChernoff.blockCount
          (concreteStageBlockFamily H current stage a) x <
        2 * blockThreshold a) →
      HasStagePropertiesIV H base
        (addCompletionLayer current
          (sampledCompletionLayer (completionCandidate H current stage) x))
        d eps stage := by
    intro x hrel hlinear hblock
    have hdegree : ∀ e ∈ H,
        InRelativeInterval
          (degree (conflictLayer
            (addCompletionLayer current
              (sampledCompletionLayer (completionCandidate H current stage) x))
            stage) e : ℝ)
          (completionTarget d eps (layerMaxDegree H base stage : ℝ) stage)
          (Real.rpow d (-eps)) := by
      intro e he
      let ee : ConcreteStageDegreeIndex H := ⟨e, he⟩
      have hdev := (hrel ee).trans_le (hdegreeMargin ee)
      rw [degree_addCompletionLayer_sampled_eq]
      have hinterval := inRelativeInterval_of_mean_room
        (hdegreeMean ee) (by
          simpa [p, ee, concreteStageDegreeActive,
            bitCount_degree_eq_sampledCount] using hdev)
      simpa [htarget] using hinterval
    have hlinearProps := stagePropertiesIIIII_of_restrictedLinearBounds
      H current hcurrent d eps hd.le stage hdef.2.1 x linearThreshold
      hlinear hII hIII
    have hblockBounds : BlockUpperBounds H current stage x blockThreshold := by
      intro a
      rw [← blockCount_concreteStageBlockFamily_eq H current stage a x]
      exact hblock a
    refine ⟨hdef.1, hdef.2.1, hdegree, hlinearProps.1, hlinearProps.2, ?_, ?_⟩
    · exact stagePropertyIV_of_blockBounds H current hcurrent d eps stage x
        blockThreshold hblockBounds hIV
    · exact stagePropertyV_of_blockBounds H current d eps stage hdef.1 x
        blockThreshold hblockBounds hV
  exact exists_regularizationStageWithBlocks_activeTests
    H base current d eps stage target
    (concreteStageDegreeActive H current stage) degreeDelta
    (restrictedStageLinearUpperActive H current stage) linearThreshold
    (concreteStageBlockSize H current stage)
    (concreteStageBlockFamily H current stage) blockThreshold
    testJ w gap limit hp hdelta0 hdelta1 hlinear0 hlinearMean
    (concreteStageBlockFamily_pairwiseDisjoint H current stage)
    hblock0 hblockMean hw hfreeZero hgap hlimitPos hkillMean hfail hdecode

end
end CFMRegularization
end Erdos136

namespace Erdos136.CFMRegularization

open Finset Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-! A four-family version of the finite failure budget used by a concrete
regularisation stage.  The four families are degree, linear (II--III),
block (IV--V), and tracked-test observables. -/

private theorem sum_exp_neg_div_three_le
    {ι : Type*} [Fintype ι] (x y : ℝ) (z : ι → ℝ)
    (hcard : (Fintype.card ι : ℝ) ≤ Real.exp y)
    (hz : ∀ i, x ≤ z i)
    (hbase : Real.exp (y - x / 3) ≤ (1 / 16 : ℝ)) :
    (∑ i : ι, Real.exp (-(z i) / 3)) ≤ 1 / 16 := by
  calc
    (∑ i : ι, Real.exp (-(z i) / 3)) ≤
        ∑ _i : ι, Real.exp (-x / 3) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [Real.exp_le_exp]
      linarith [hz i]
    _ = (Fintype.card ι : ℝ) * Real.exp (-x / 3) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_cast
    _ ≤ Real.exp y * Real.exp (-x / 3) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
    _ = Real.exp (y - x / 3) := by
      rw [show -x / 3 = -(x / 3) by ring, ← Real.exp_add]
      ring_nf
    _ ≤ 1 / 16 := hbase

theorem fourFamily_failureSum_lt_one_of_exp_card_bounds
    {ιrel ιlinear ιblock ιtest : Type*}
    [Fintype ιrel] [Fintype ιlinear] [Fintype ιblock] [Fintype ιtest]
    (x y : ℝ) (zrel : ιrel → ℝ) (zlinear : ιlinear → ℝ)
    (zblock : ιblock → ℝ) (ztest : ιtest → ℝ)
    (hpower : 16 * y ≤ x)
    (hlog : 5 * Real.log 16 ≤ x)
    (hcardRel : (Fintype.card ιrel : ℝ) ≤ Real.exp y)
    (hcardLinear : (Fintype.card ιlinear : ℝ) ≤ Real.exp y)
    (hcardBlock : (Fintype.card ιblock : ℝ) ≤ Real.exp y)
    (hcardTest : (Fintype.card ιtest : ℝ) ≤ Real.exp y)
    (hzrel : ∀ i, x ≤ zrel i)
    (hzlinear : ∀ i, x ≤ zlinear i)
    (hzblock : ∀ i, x ≤ zblock i)
    (hztest : ∀ i, x / 3 ≤ ztest i) :
    (∑ i : ιrel, 2 * Real.exp (-(zrel i) / 3)) +
        (∑ i : ιlinear, Real.exp (-(zlinear i) / 3)) +
        (∑ i : ιblock, Real.exp (-(zblock i) / 3)) +
        (∑ i : ιtest, Real.exp (-(ztest i))) < 1 := by
  have hx0 : 0 ≤ x := by
    have hlog0 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    linarith
  have hyx : y - x / 3 ≤ -x / 5 := by linarith
  have hxlog : Real.log 16 ≤ x / 5 := by linarith
  have hbase : Real.exp (y - x / 3) ≤ (1 / 16 : ℝ) := by
    calc
      Real.exp (y - x / 3) ≤ Real.exp (-x / 5) :=
        Real.exp_le_exp.mpr hyx
      _ ≤ Real.exp (-Real.log 16) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = 1 / 16 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
        norm_num
  have hrel :
      (∑ i : ιrel, 2 * Real.exp (-(zrel i) / 3)) ≤ 1 / 8 := by
    calc
      (∑ i : ιrel, 2 * Real.exp (-(zrel i) / 3)) =
          2 * ∑ i : ιrel, Real.exp (-(zrel i) / 3) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * (1 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (sum_exp_neg_div_three_le x y zrel hcardRel hzrel hbase) (by norm_num)
      _ = 1 / 8 := by norm_num
  have hlinear := sum_exp_neg_div_three_le x y zlinear hcardLinear hzlinear hbase
  have hblock := sum_exp_neg_div_three_le x y zblock hcardBlock hzblock hbase
  have htest : (∑ i : ιtest, Real.exp (-(ztest i))) ≤ 1 / 16 := by
    calc
      (∑ i : ιtest, Real.exp (-(ztest i))) ≤
          ∑ _i : ιtest, Real.exp (-x / 3) := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [Real.exp_le_exp]
        linarith [hztest i]
      _ = (Fintype.card ιtest : ℝ) * Real.exp (-x / 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
      _ ≤ Real.exp y * Real.exp (-x / 3) :=
        mul_le_mul_of_nonneg_right hcardTest (Real.exp_nonneg _)
      _ = Real.exp (y - x / 3) := by
        rw [show -x / 3 = -(x / 3) by ring, ← Real.exp_add]
        ring_nf
      _ ≤ 1 / 16 := hbase
  linarith

theorem fourFamily_chernoffMcDiarmid_failureSum_lt_one
    {ιrel ιlinear ιblock ιtest : Type*}
    [Fintype ιrel] [Fintype ιlinear] [Fintype ιblock] [Fintype ιtest]
    (x y : ℝ) (delta mean : ιrel → ℝ)
    (linearThreshold : ιlinear → ℝ) (blockThreshold : ιblock → ℝ)
    (gap influenceSq : ιtest → ℝ)
    (hpower : 16 * y ≤ x) (hlog : 5 * Real.log 16 ≤ x)
    (hcardRel : (Fintype.card ιrel : ℝ) ≤ Real.exp y)
    (hcardLinear : (Fintype.card ιlinear : ℝ) ≤ Real.exp y)
    (hcardBlock : (Fintype.card ιblock : ℝ) ≤ Real.exp y)
    (hcardTest : (Fintype.card ιtest : ℝ) ≤ Real.exp y)
    (hzrel : ∀ i, x ≤ delta i ^ 2 * mean i)
    (hzlinear : ∀ i, x ≤ linearThreshold i)
    (hzblock : ∀ i, x ≤ blockThreshold i)
    (hztest : ∀ i, x / 3 ≤ 2 * gap i ^ 2 / influenceSq i) :
    (∑ i : ιrel,
          2 * Real.exp (-(delta i ^ 2 * mean i) / 3)) +
        (∑ i : ιlinear, Real.exp (-linearThreshold i / 3)) +
        (∑ i : ιblock, Real.exp (-blockThreshold i / 3)) +
        (∑ i : ιtest,
          Real.exp (-2 * gap i ^ 2 / influenceSq i)) < 1 := by
  simpa only [neg_div, neg_mul] using
    fourFamily_failureSum_lt_one_of_exp_card_bounds x y
      (fun i => delta i ^ 2 * mean i) linearThreshold blockThreshold
      (fun i => 2 * gap i ^ 2 / influenceSq i)
      hpower hlog hcardRel hcardLinear hcardBlock hcardTest
      hzrel hzlinear hzblock hztest

/-! The finite requirements needed to turn the source-scale expectation
bounds into the fixed one-eighth thresholds used for (II)--(V). -/

inductive RawObservableRequirement
  | oldRoom
  | linearMean
  | blockMean
  | thresholdScale
  | entropyPower
  | entropyLog
  deriving DecidableEq

def rawObservableRegistry (eta Gamma K : ℝ)
    (heta0 : 0 < eta) (hetaSmall : eta < 1 / 10) :
    LargeDRegistry RawObservableRequirement where
  active := { .oldRoom, .linearMean, .blockMean, .thresholdScale,
    .entropyPower, .entropyLog }
  condition r d :=
    let eps := rawRegularizationEps eta
    match r with
    | .oldRoom => 4 * Real.rpow d (-eps / 3) ≤ Real.rpow d (-eps / 4)
    | .linearMean =>
        256 * Real.rpow d (10 * eps - eta) ≤ Real.rpow d (-eps / 4)
    | .blockMean =>
        256 * (4 * Gamma + 1) * Real.rpow d (20 * eps - eta) ≤
          Real.rpow d (-eps / 4)
    | .thresholdScale =>
        8 * Real.rpow d (1 - 10 * eps) ≤ Real.rpow d (1 - eps / 4)
    | .entropyPower =>
        16 * (K * Real.rpow d (eta ^ 3)) ≤
          Real.rpow d (1 - 10 * eps)
    | .entropyLog =>
        5 * Real.log 16 ≤ Real.rpow d (1 - 10 * eps)
  eventually_condition := by
    intro r _hr
    let eps := rawRegularizationEps eta
    have heps0 : 0 < eps := by
      dsimp [eps, rawRegularizationEps]
      positivity
    have heta3 : eta ^ 3 < 1 - 10 * eps := by
      have h := rawRegularization_exponent_relations eta heta0 hetaSmall
      simpa [eps] using h.2.2.2.2.1
    cases r with
    | oldRoom =>
        exact eventually_const_mul_rpow_le_rpow_real 4 (-eps / 3) (-eps / 4)
          (by linarith)
    | linearMean =>
        exact eventually_const_mul_rpow_le_rpow_real 256 (10 * eps - eta) (-eps / 4)
          (by dsimp [eps, rawRegularizationEps]; linarith)
    | blockMean =>
        have h := eventually_const_mul_rpow_le_rpow_real
          (256 * (4 * Gamma + 1)) (20 * eps - eta) (-eps / 4)
          (by dsimp [eps, rawRegularizationEps]; linarith)
        filter_upwards [h] with d hd
        simpa [mul_assoc] using hd
    | thresholdScale =>
        exact eventually_const_mul_rpow_le_rpow_real 8
          (1 - 10 * eps) (1 - eps / 4) (by linarith)
    | entropyPower =>
        have h := eventually_const_mul_rpow_le_rpow_real
          (16 * K) (eta ^ 3) (1 - 10 * eps) heta3
        filter_upwards [h] with d hd
        simpa [mul_assoc] using hd
    | entropyLog =>
        have h := eventually_const_mul_rpow_le_rpow_real
          (5 * Real.log 16) 0 (1 - 10 * eps) (by
            dsimp [eps, rawRegularizationEps]
            linarith)
        filter_upwards [h] with d hd
        simpa using hd

structure RawObservableCutoffSpec (eta Gamma K d : ℝ) : Prop where
  degreeAtLeastTwo : 2 ≤ d
  oldRoom :
    4 * Real.rpow d (-rawRegularizationEps eta / 3) ≤
      Real.rpow d (-rawRegularizationEps eta / 4)
  linearMean :
    256 * Real.rpow d (10 * rawRegularizationEps eta - eta) ≤
      Real.rpow d (-rawRegularizationEps eta / 4)
  blockMean :
    256 * (4 * Gamma + 1) *
        Real.rpow d (20 * rawRegularizationEps eta - eta) ≤
      Real.rpow d (-rawRegularizationEps eta / 4)
  thresholdScale :
    8 * Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
      Real.rpow d (1 - rawRegularizationEps eta / 4)
  entropyPower :
    16 * (K * Real.rpow d (eta ^ 3)) ≤
      Real.rpow d (1 - 10 * rawRegularizationEps eta)
  entropyLog :
    5 * Real.log 16 ≤
      Real.rpow d (1 - 10 * rawRegularizationEps eta)

theorem exists_rawObservableCutoff (eta Gamma K : ℝ)
    (heta0 : 0 < eta) (hetaSmall : eta < 1 / 10) :
    ∃ d0 : ℝ, ∀ d, d0 ≤ d → RawObservableCutoffSpec eta Gamma K d := by
  let R := rawObservableRegistry eta Gamma K heta0 hetaSmall
  obtain ⟨dR, hdR⟩ := R.exists_cutoff
  let d0 := max 2 dR
  refine ⟨d0, fun d hd => ?_⟩
  have hd2 : 2 ≤ d := (le_max_left 2 dR).trans hd
  have hdRegistry : dR ≤ d := (le_max_right 2 dR).trans hd
  have hreq (r : RawObservableRequirement) : R.condition r d := by
    apply hdR d hdRegistry r
    cases r <;> simp [R, rawObservableRegistry]
  refine ⟨hd2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [R, rawObservableRegistry] using hreq .oldRoom
  · simpa [R, rawObservableRegistry] using hreq .linearMean
  · simpa [R, rawObservableRegistry] using hreq .blockMean
  · simpa [R, rawObservableRegistry] using hreq .thresholdScale
  · simpa [R, rawObservableRegistry] using hreq .entropyPower
  · simpa [R, rawObservableRegistry] using hreq .entropyLog

theorem RawObservableCutoffSpec.failureBudget
    {eta Gamma K d : ℝ} (h : RawObservableCutoffSpec eta Gamma K d) :
    16 * (K * Real.rpow d (eta ^ 3)) ≤
        Real.rpow d (1 - 10 * rawRegularizationEps eta) ∧
      5 * Real.log 16 ≤
        Real.rpow d (1 - 10 * rawRegularizationEps eta) :=
  ⟨h.entropyPower, h.entropyLog⟩

/-- The raw cutoff discharges the exact four-family failure sum appearing
in `exists_concreteSourceWeightedRegularizationStage`. -/
theorem RawObservableCutoffSpec.fourFamilyFailure
    {eta Gamma K d : ℝ} (h : RawObservableCutoffSpec eta Gamma K d)
    {ιrel ιlinear ιblock ιtest : Type*}
    [Fintype ιrel] [Fintype ιlinear] [Fintype ιblock] [Fintype ιtest]
    (delta mean : ιrel → ℝ)
    (linearThreshold : ιlinear → ℝ) (blockThreshold : ιblock → ℝ)
    (gap influenceSq : ιtest → ℝ)
    (hcardRel : (Fintype.card ιrel : ℝ) ≤
      Real.exp (K * Real.rpow d (eta ^ 3)))
    (hcardLinear : (Fintype.card ιlinear : ℝ) ≤
      Real.exp (K * Real.rpow d (eta ^ 3)))
    (hcardBlock : (Fintype.card ιblock : ℝ) ≤
      Real.exp (K * Real.rpow d (eta ^ 3)))
    (hcardTest : (Fintype.card ιtest : ℝ) ≤
      Real.exp (K * Real.rpow d (eta ^ 3)))
    (hzrel : ∀ i,
      Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
        delta i ^ 2 * mean i)
    (hzlinear : ∀ i,
      Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
        linearThreshold i)
    (hzblock : ∀ i,
      Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
        blockThreshold i)
    (hztest : ∀ i,
      Real.rpow d (1 - 10 * rawRegularizationEps eta) / 3 ≤
        2 * gap i ^ 2 / influenceSq i) :
    (∑ i : ιrel,
          2 * Real.exp (-(delta i ^ 2 * mean i) / 3)) +
        (∑ i : ιlinear, Real.exp (-linearThreshold i / 3)) +
        (∑ i : ιblock, Real.exp (-blockThreshold i / 3)) +
        (∑ i : ιtest,
          Real.exp (-2 * gap i ^ 2 / influenceSq i)) < 1 := by
  exact fourFamily_chernoffMcDiarmid_failureSum_lt_one
    (Real.rpow d (1 - 10 * rawRegularizationEps eta))
    (K * Real.rpow d (eta ^ 3)) delta mean linearThreshold blockThreshold
    gap influenceSq h.entropyPower h.entropyLog hcardRel hcardLinear
    hcardBlock hcardTest hzrel hzlinear hzblock hztest

/-- One generic calculation covers (II), (III), and the old part of
(IV)--(V): an old `eps/3` term plus twice a source mean of exponent
`3 eps - eta` fits below the `eps/4` target. -/
theorem RawObservableCutoffSpec.linearObservableRoom
    {eta Gamma K d r old mean : ℝ}
    (h : RawObservableCutoffSpec eta Gamma K d)
    (hold : old ≤ Real.rpow d (r - rawRegularizationEps eta / 3))
    (hmean : mean ≤ 32 *
      Real.rpow d (r + 10 * rawRegularizationEps eta - eta)) :
    old + 2 * mean ≤
      Real.rpow d (r - rawRegularizationEps eta / 4) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) h.degreeAtLeastTwo
  let eps := rawRegularizationEps eta
  have hold' : old ≤
      Real.rpow d r * Real.rpow d (-eps / 3) := by
    calc
      old ≤ Real.rpow d (r - rawRegularizationEps eta / 3) := hold
      _ = Real.rpow d (r + (-eps / 3)) := by
        congr 1
        dsimp [eps]
        ring
      _ = Real.rpow d r * Real.rpow d (-eps / 3) :=
        Real.rpow_add hd _ _
  have hmean' : mean ≤ 32 *
      (Real.rpow d r * Real.rpow d (10 * eps - eta)) := by
    calc
      mean ≤ 32 * Real.rpow d (r + 10 * rawRegularizationEps eta - eta) := hmean
      _ = 32 * Real.rpow d (r + (10 * eps - eta)) := by
        congr 2
        dsimp [eps]
        ring
      _ = 32 * (Real.rpow d r * Real.rpow d (10 * eps - eta)) := by
        congr 1
        exact Real.rpow_add hd _ _
  have holdQuarter :
      4 * old ≤ Real.rpow d r * Real.rpow d (-eps / 4) := by
    calc
      4 * old ≤ 4 * (Real.rpow d r * Real.rpow d (-eps / 3)) :=
        mul_le_mul_of_nonneg_left hold' (by norm_num)
      _ = Real.rpow d r * (4 * Real.rpow d (-eps / 3)) := by ring
      _ ≤ Real.rpow d r * Real.rpow d (-eps / 4) :=
        mul_le_mul_of_nonneg_left h.oldRoom (Real.rpow_nonneg hd.le _)
  have hmeanEighth :
      8 * mean ≤ Real.rpow d r * Real.rpow d (-eps / 4) := by
    calc
      8 * mean ≤ 8 * (32 *
          (Real.rpow d r * Real.rpow d (10 * eps - eta))) :=
        mul_le_mul_of_nonneg_left hmean' (by norm_num)
      _ = Real.rpow d r * (256 * Real.rpow d (10 * eps - eta)) := by ring
      _ ≤ Real.rpow d r * Real.rpow d (-eps / 4) :=
        mul_le_mul_of_nonneg_left h.linearMean (Real.rpow_nonneg hd.le _)
  have htarget : Real.rpow d r * Real.rpow d (-eps / 4) =
      Real.rpow d (r - eps / 4) := by
    calc
      Real.rpow d r * Real.rpow d (-eps / 4) =
          Real.rpow d (r + (-eps / 4)) := (Real.rpow_add hd _ _).symm
      _ = Real.rpow d (r - eps / 4) := by congr 1 <;> ring
  rw [← htarget]
  have ht0 : 0 ≤ Real.rpow d r * Real.rpow d (-eps / 4) :=
    mul_nonneg (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hd.le _)
  nlinarith

/-- The refined one/two-coordinate block mean has exponent
`6 eps - eta`; this is the common numerical room for (IV) and (V). -/
theorem RawObservableCutoffSpec.blockObservableRoom
    {eta Gamma K d r old mean : ℝ}
    (h : RawObservableCutoffSpec eta Gamma K d)
    (hGamma : 0 ≤ Gamma)
    (hold : old ≤ Real.rpow d (r - rawRegularizationEps eta / 3))
    (hmean : mean ≤ 32 * (4 * Gamma + 1) *
      Real.rpow d (r + 20 * rawRegularizationEps eta - eta)) :
    old + 2 * mean ≤
      Real.rpow d (r - rawRegularizationEps eta / 4) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) h.degreeAtLeastTwo
  let eps := rawRegularizationEps eta
  have hold' : old ≤ Real.rpow d r * Real.rpow d (-eps / 3) := by
    calc
      old ≤ Real.rpow d (r - rawRegularizationEps eta / 3) := hold
      _ = Real.rpow d (r + (-eps / 3)) := by
        congr 1
        dsimp [eps]
        ring
      _ = Real.rpow d r * Real.rpow d (-eps / 3) :=
        Real.rpow_add hd _ _
  have hmean' : mean ≤
      32 * (4 * Gamma + 1) *
        (Real.rpow d r * Real.rpow d (20 * eps - eta)) := by
    calc
      mean ≤ 32 * (4 * Gamma + 1) *
          Real.rpow d (r + 20 * rawRegularizationEps eta - eta) := hmean
      _ = 32 * (4 * Gamma + 1) * Real.rpow d (r + (20 * eps - eta)) := by
        congr 2
        dsimp [eps]
        ring
      _ = 32 * (4 * Gamma + 1) *
          (Real.rpow d r * Real.rpow d (20 * eps - eta)) := by
        congr 2
        exact Real.rpow_add hd _ _
  have holdQuarter :
      4 * old ≤ Real.rpow d r * Real.rpow d (-eps / 4) := by
    calc
      4 * old ≤ 4 * (Real.rpow d r * Real.rpow d (-eps / 3)) :=
        mul_le_mul_of_nonneg_left hold' (by norm_num)
      _ = Real.rpow d r * (4 * Real.rpow d (-eps / 3)) := by ring
      _ ≤ Real.rpow d r * Real.rpow d (-eps / 4) :=
        mul_le_mul_of_nonneg_left h.oldRoom (Real.rpow_nonneg hd.le _)
  have hmeanEighth :
      8 * mean ≤ Real.rpow d r * Real.rpow d (-eps / 4) := by
    calc
      8 * mean ≤
          8 * (32 * (4 * Gamma + 1) *
            (Real.rpow d r * Real.rpow d (20 * eps - eta))) :=
        mul_le_mul_of_nonneg_left hmean' (by norm_num)
      _ = Real.rpow d r *
          (256 * (4 * Gamma + 1) * Real.rpow d (20 * eps - eta)) := by ring
      _ ≤ Real.rpow d r * Real.rpow d (-eps / 4) :=
        mul_le_mul_of_nonneg_left h.blockMean (Real.rpow_nonneg hd.le _)
  have htarget : Real.rpow d r * Real.rpow d (-eps / 4) =
      Real.rpow d (r - eps / 4) := by
    calc
      Real.rpow d r * Real.rpow d (-eps / 4) =
          Real.rpow d (r + (-eps / 4)) := (Real.rpow_add hd _ _).symm
      _ = Real.rpow d (r - eps / 4) := by congr 1 <;> ring
  rw [← htarget]
  have ht0 : 0 ≤ Real.rpow d r * Real.rpow d (-eps / 4) :=
    mul_nonneg (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hd.le _)
  nlinarith

/-- Every one-eighth threshold at an observable rank `r ≥ 1` dominates
the common failure scale `d^(1-10 eps)`. -/
theorem RawObservableCutoffSpec.failureScale_le_eighthThreshold
    {eta Gamma K d r : ℝ} (h : RawObservableCutoffSpec eta Gamma K d)
    (hr : 1 ≤ r) :
    Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
      Real.rpow d (r - rawRegularizationEps eta / 4) / 8 := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) h.degreeAtLeastTwo
  have hd1 : 1 ≤ d := (by norm_num : (1 : ℝ) ≤ 2).trans h.degreeAtLeastTwo
  have hmono : Real.rpow d (1 - rawRegularizationEps eta / 4) ≤
      Real.rpow d (r - rawRegularizationEps eta / 4) :=
    Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
  have hs := h.thresholdScale.trans hmono
  nlinarith

/-- Fixed one-eighth thresholds.  Inflating the actual source means to
these thresholds gives both deterministic room and a uniform failure
exponent. -/
def rawLinearObservableThreshold {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (d eta : ℝ) (stage : ℕ) :
    StageLinearUpperIndex H stage → ℝ
  | Sum.inl root =>
      Real.rpow d ((stage : ℝ) - (root.1.card : ℝ) -
        rawRegularizationEps eta / 4) / 8
  | Sum.inr _ =>
      Real.rpow d (1 - rawRegularizationEps eta / 4) / 8

def rawBlockObservableThreshold {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (current : ConflictSystem V)
    (d eta : ℝ) (stage : ℕ) :
    StageBlockUpperIndex H current stage → ℝ := fun _ =>
  Real.rpow d (((stage - 1 : ℕ) : ℝ) -
    rawRegularizationEps eta / 4) / 8

theorem RawObservableCutoffSpec.linearMean_le_eighthTarget
    {eta Gamma K d r mean : ℝ}
    (h : RawObservableCutoffSpec eta Gamma K d)
    (hmean : mean ≤ 32 *
      Real.rpow d (r + 10 * rawRegularizationEps eta - eta)) :
    mean ≤ Real.rpow d (r - rawRegularizationEps eta / 4) / 8 := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) h.degreeAtLeastTwo
  let eps := rawRegularizationEps eta
  have hmean' : mean ≤ 32 *
      (Real.rpow d r * Real.rpow d (10 * eps - eta)) := by
    calc
      mean ≤ 32 * Real.rpow d (r + 10 * rawRegularizationEps eta - eta) := hmean
      _ = 32 * Real.rpow d (r + (10 * eps - eta)) := by
        congr 2
        dsimp [eps]
        ring
      _ = 32 * (Real.rpow d r * Real.rpow d (10 * eps - eta)) := by
        congr 1
        exact Real.rpow_add hd _ _
  have h8 : 8 * mean ≤
      Real.rpow d r * Real.rpow d (-eps / 4) := by
    calc
      8 * mean ≤ 8 * (32 *
          (Real.rpow d r * Real.rpow d (10 * eps - eta))) :=
        mul_le_mul_of_nonneg_left hmean' (by norm_num)
      _ = Real.rpow d r * (256 * Real.rpow d (10 * eps - eta)) := by ring
      _ ≤ Real.rpow d r * Real.rpow d (-eps / 4) :=
        mul_le_mul_of_nonneg_left h.linearMean (Real.rpow_nonneg hd.le _)
  have htarget : Real.rpow d r * Real.rpow d (-eps / 4) =
      Real.rpow d (r - eps / 4) := by
    calc
      Real.rpow d r * Real.rpow d (-eps / 4) =
          Real.rpow d (r + (-eps / 4)) := (Real.rpow_add hd _ _).symm
      _ = Real.rpow d (r - eps / 4) := by congr 1 <;> ring
  rw [htarget] at h8
  linarith

theorem RawObservableCutoffSpec.blockMean_le_eighthTarget
    {eta Gamma K d r mean : ℝ}
    (h : RawObservableCutoffSpec eta Gamma K d)
    (hmean : mean ≤ 32 * (4 * Gamma + 1) *
      Real.rpow d (r + 20 * rawRegularizationEps eta - eta)) :
    mean ≤ Real.rpow d (r - rawRegularizationEps eta / 4) / 8 := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) h.degreeAtLeastTwo
  let eps := rawRegularizationEps eta
  have hmean' : mean ≤ 32 * (4 * Gamma + 1) *
      (Real.rpow d r * Real.rpow d (20 * eps - eta)) := by
    calc
      mean ≤ 32 * (4 * Gamma + 1) *
          Real.rpow d (r + 20 * rawRegularizationEps eta - eta) := hmean
      _ = 32 * (4 * Gamma + 1) * Real.rpow d (r + (20 * eps - eta)) := by
        congr 3
        dsimp [eps]
        ring
      _ = 32 * (4 * Gamma + 1) *
          (Real.rpow d r * Real.rpow d (20 * eps - eta)) := by
        congr 2
        exact Real.rpow_add hd _ _
  have h8 : 8 * mean ≤ Real.rpow d r * Real.rpow d (-eps / 4) := by
    calc
      8 * mean ≤ 8 * (32 * (4 * Gamma + 1) *
          (Real.rpow d r * Real.rpow d (20 * eps - eta))) :=
        mul_le_mul_of_nonneg_left hmean' (by norm_num)
      _ = Real.rpow d r *
          (256 * (4 * Gamma + 1) * Real.rpow d (20 * eps - eta)) := by ring
      _ ≤ Real.rpow d r * Real.rpow d (-eps / 4) :=
        mul_le_mul_of_nonneg_left h.blockMean (Real.rpow_nonneg hd.le _)
  have htarget : Real.rpow d r * Real.rpow d (-eps / 4) =
      Real.rpow d (r - eps / 4) := by
    calc
      Real.rpow d r * Real.rpow d (-eps / 4) =
          Real.rpow d (r + (-eps / 4)) := (Real.rpow_add hd _ _).symm
      _ = Real.rpow d (r - eps / 4) := by congr 1 <;> ring
  rw [htarget] at h8
  linarith

theorem RawObservableCutoffSpec.oldPlusEighthThreshold_le
    {eta Gamma K d r old : ℝ}
    (h : RawObservableCutoffSpec eta Gamma K d)
    (hold : old ≤ Real.rpow d (r - rawRegularizationEps eta / 3)) :
    old + 2 * (Real.rpow d
      (r - rawRegularizationEps eta / 4) / 8) ≤
      Real.rpow d (r - rawRegularizationEps eta / 4) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) h.degreeAtLeastTwo
  let eps := rawRegularizationEps eta
  have hold' : old ≤ Real.rpow d r * Real.rpow d (-eps / 3) := by
    calc
      old ≤ Real.rpow d (r - rawRegularizationEps eta / 3) := hold
      _ = Real.rpow d (r + (-eps / 3)) := by
        congr 1
        dsimp [eps]
        ring
      _ = Real.rpow d r * Real.rpow d (-eps / 3) :=
        Real.rpow_add hd _ _
  have h4 : 4 * old ≤ Real.rpow d r * Real.rpow d (-eps / 4) := by
    calc
      4 * old ≤ 4 * (Real.rpow d r * Real.rpow d (-eps / 3)) :=
        mul_le_mul_of_nonneg_left hold' (by norm_num)
      _ = Real.rpow d r * (4 * Real.rpow d (-eps / 3)) := by ring
      _ ≤ Real.rpow d r * Real.rpow d (-eps / 4) :=
        mul_le_mul_of_nonneg_left h.oldRoom (Real.rpow_nonneg hd.le _)
  have htarget : Real.rpow d r * Real.rpow d (-eps / 4) =
      Real.rpow d (r - eps / 4) := by
    calc
      Real.rpow d r * Real.rpow d (-eps / 4) =
          Real.rpow d (r + (-eps / 4)) := (Real.rpow_add hd _ _).symm
      _ = Real.rpow d (r - eps / 4) := by congr 1 <;> ring
  rw [htarget] at h4
  have ht0 : 0 ≤ Real.rpow d (r - eps / 4) := Real.rpow_nonneg hd.le _
  let T := Real.rpow d (r - rawRegularizationEps eta / 4)
  have h4' : 4 * old ≤ T := by simpa [T, eps] using h4
  have hT0 : 0 ≤ T := by simpa [T, eps] using ht0
  have holdQuarter : old ≤ T / 4 := by nlinarith
  change old + 2 * (T / 8) ≤ T
  calc
    old + 2 * (T / 8) ≤ T / 4 + 2 * (T / 8) :=
      add_le_add holdQuarter le_rfl
    _ = T / 2 := by ring
    _ ≤ T := by linarith

theorem RawObservableCutoffSpec.rawLinearThreshold_failureScale
    {V : Type*} [Fintype V] [DecidableEq V]
    {eta Gamma K d : ℝ} (h : RawObservableCutoffSpec eta Gamma K d)
    (H : Hypergraph V) (stage : ℕ) :
    ∀ a : StageLinearUpperIndex H stage,
      Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
        rawLinearObservableThreshold H d eta stage a := by
  rintro (root | c4)
  · apply h.failureScale_le_eighthThreshold
    have hn : root.1.card + 1 ≤ stage := by omega
    have hn' : ((root.1.card + 1 : ℕ) : ℝ) ≤ (stage : ℝ) := by
      exact_mod_cast hn
    push_cast at hn'
    linarith
  · exact h.failureScale_le_eighthThreshold (r := 1) (by norm_num)

theorem RawObservableCutoffSpec.rawBlockThreshold_failureScale
    {V : Type*} [Fintype V] [DecidableEq V]
    {eta Gamma K d : ℝ} (h : RawObservableCutoffSpec eta Gamma K d)
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hstage : 2 ≤ stage) :
    ∀ a : StageBlockUpperIndex H current stage,
      Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
        rawBlockObservableThreshold H current d eta stage a := by
  intro a
  apply h.failureScale_le_eighthThreshold
  exact_mod_cast (by omega : 1 ≤ stage - 1)

theorem RawObservableCutoffSpec.rawLinearThreshold_dominates
    {V : Type*} [Fintype V] [DecidableEq V]
    {eta Gamma K d : ℝ} (h : RawObservableCutoffSpec eta Gamma K d)
    (H : Hypergraph V) (stage : ℕ)
    (mean : StageLinearUpperIndex H stage → ℝ)
    (hIImean : ∀ root : StageCodegreeIndex V stage,
      mean (Sum.inl root) ≤ 32 *
        Real.rpow d ((stage : ℝ) - (root.1.card : ℝ) +
          10 * rawRegularizationEps eta - eta))
    (hIIImean : ∀ a : StageC4Index H stage,
      mean (Sum.inr a) ≤ 32 *
        Real.rpow d (1 + 10 * rawRegularizationEps eta - eta)) :
    ∀ a, mean a ≤ rawLinearObservableThreshold H d eta stage a := by
  rintro (root | c4)
  · exact h.linearMean_le_eighthTarget (hIImean root)
  · exact h.linearMean_le_eighthTarget (hIIImean c4)

theorem RawObservableCutoffSpec.rawBlockThreshold_dominates
    {V : Type*} [Fintype V] [DecidableEq V]
    {eta Gamma K d : ℝ} (h : RawObservableCutoffSpec eta Gamma K d)
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (mean : StageBlockUpperIndex H current stage → ℝ)
    (hmean : ∀ a, mean a ≤ 32 * (4 * Gamma + 1) *
      Real.rpow d (((stage - 1 : ℕ) : ℝ) +
        20 * rawRegularizationEps eta - eta)) :
    ∀ a, mean a ≤ rawBlockObservableThreshold H current d eta stage a := by
  intro a
  exact h.blockMean_le_eighthTarget (hmean a)

theorem RawObservableCutoffSpec.rawPropertyIIRoom
    {V : Type*} [Fintype V] [DecidableEq V]
    {eta Gamma K d : ℝ} (h : RawObservableCutoffSpec eta Gamma K d)
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hold : ∀ root : StageCodegreeIndex V stage,
      (codegree (conflictLayer current stage) root.1 : ℝ) ≤
        Real.rpow d ((stage : ℝ) - (root.1.card : ℝ) -
          rawRegularizationEps eta / 3)) :
    PropertyIIRoom H current d (rawRegularizationEps eta) stage
      (rawLinearObservableThreshold H d eta stage) := by
  intro root
  exact h.oldPlusEighthThreshold_le (hold root)

theorem RawObservableCutoffSpec.rawPropertyIIIRoom
    {V : Type*} [Fintype V] [DecidableEq V]
    {eta Gamma K d : ℝ} (h : RawObservableCutoffSpec eta Gamma K d)
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hold : ∀ (hs : stage = 2) (e : Finset V) (he : e ∈ H) (v : V),
      (conditionC4Count H current e v : ℝ) ≤
        Real.rpow d (1 - rawRegularizationEps eta / 3)) :
    PropertyIIIRoom H current d (rawRegularizationEps eta) stage
      (rawLinearObservableThreshold H d eta stage) := by
  intro hs e he v
  exact h.oldPlusEighthThreshold_le (hold hs e he v)

theorem RawObservableCutoffSpec.rawPropertyIVRoom
    {V : Type*} [Fintype V] [DecidableEq V]
    {eta Gamma K d : ℝ} (h : RawObservableCutoffSpec eta Gamma K d)
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hold : ∀ (hs : stage = 2) (e : Finset V) (he : e ∈ H)
      (f : Finset V) (hf : f ∈ H) (hdisj : Disjoint e f),
      (conditionC5Count H current e f : ℝ) ≤
        Real.rpow d (1 - rawRegularizationEps eta / 3)) :
    PropertyIVRoom H current d (rawRegularizationEps eta) stage
      (rawBlockObservableThreshold H current d eta stage) := by
  intro hs e he f hf hdisj
  subst stage
  simpa only [rawBlockObservableThreshold, Nat.reduceSub, Nat.cast_one] using
    h.oldPlusEighthThreshold_le (hold rfl e he f hf hdisj)

theorem RawObservableCutoffSpec.rawPropertyVRoom
    {V : Type*} [Fintype V] [DecidableEq V]
    {eta Gamma K d : ℝ} (h : RawObservableCutoffSpec eta Gamma K d)
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ)
    (hold : ∀ (e : Finset V) (he : e ∈ H)
      (f : Finset V) (hf : f ∈ H) (hdisj : Disjoint e f)
      (hnot : {e, f} ∉ conflictLayer current 2),
      (((conflictLinkLayer current e (stage - 1) ∩
        conflictLinkLayer current f (stage - 1)).card : ℕ) : ℝ) ≤
        Real.rpow d (((stage - 1 : ℕ) : ℝ) -
          rawRegularizationEps eta / 3)) :
    PropertyVRoom H current d (rawRegularizationEps eta) stage
      (rawBlockObservableThreshold H current d eta stage) := by
  intro e he f hf hdisj hnot
  exact h.oldPlusEighthThreshold_le (hold e he f hf hdisj hnot)

/-! ### Entropy of the genuinely active observable families

The production indices currently range over all ambient finsets.  The
following active indices record the exact finite sets that can have a
nonzero sampled count.  Their polynomial cardinal bounds are the ones
needed to derive an `exp (K * d^(eta^3))` entropy estimate. -/

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev ActiveStageCodegreeIndex (H : Hypergraph V) (stage : ℕ) :=
  {root : Hypergraph V // root ⊆ H ∧ 2 ≤ root.card ∧ root.card < stage}

abbrev ActiveHostEdge (H : Hypergraph V) := {e : Finset V // e ∈ H}

abbrev ActiveHostVertex (H : Hypergraph V) :=
  {v : V // v ∈ vertexFinset H}

abbrev ActiveStageC4Index (H : Hypergraph V) (stage : ℕ) :=
  {p : ActiveHostEdge H × ActiveHostVertex H // stage = 2}

abbrev ActiveStageLinearUpperIndex (H : Hypergraph V) (stage : ℕ) :=
  Sum (ActiveStageCodegreeIndex H stage) (ActiveStageC4Index H stage)

abbrev ActiveStageC5BlockIndex (H : Hypergraph V) (stage : ℕ) :=
  {p : HostEdgePair H // stage = 2}

abbrev ActiveStageCommonBlockIndex (H : Hypergraph V)
    (current : ConflictSystem V) :=
  {p : HostEdgePair H // {p.left, p.right} ∉ conflictLayer current 2}

abbrev ActiveStageBlockUpperIndex (H : Hypergraph V)
    (current : ConflictSystem V) (stage : ℕ) :=
  Sum (ActiveStageC5BlockIndex H stage)
    (ActiveStageCommonBlockIndex H current)

theorem activeStageCodegreeIndex_card_le
    (H : Hypergraph V) (stage : ℕ) (hstage : stage ≤ 4) :
    Fintype.card (ActiveStageCodegreeIndex H stage) ≤
      H.card ^ 2 + H.card ^ 3 := by
  let roots := Finset.univ.filter fun root : Hypergraph V =>
    root ⊆ H ∧ 2 ≤ root.card ∧ root.card < stage
  let two := H.powersetCard 2
  let three := H.powersetCard 3
  have hcard : Fintype.card (ActiveStageCodegreeIndex H stage) = roots.card := by
    rw [Fintype.card_subtype]
  rw [hcard]
  calc
    roots.card ≤ (two ∪ three).card := by
      apply Finset.card_le_card
      intro root hroot
      have hr := Finset.mem_filter.mp hroot
      apply Finset.mem_union.mpr
      have hrootCard : root.card = 2 ∨ root.card = 3 := by omega
      rcases hrootCard with h2 | h3
      · exact Or.inl (Finset.mem_powersetCard.mpr ⟨hr.2.1, h2⟩)
      · exact Or.inr (Finset.mem_powersetCard.mpr ⟨hr.2.1, h3⟩)
    _ ≤ two.card + three.card := Finset.card_union_le _ _
    _ = H.card.choose 2 + H.card.choose 3 := by simp [two, three]
    _ ≤ H.card ^ 2 + H.card ^ 3 :=
      Nat.add_le_add (Nat.choose_le_pow _ _) (Nat.choose_le_pow _ _)

theorem activeStageC4Index_card_le (H : Hypergraph V) (stage : ℕ) :
    Fintype.card (ActiveStageC4Index H stage) ≤
      H.card * (vertexFinset H).card := by
  calc
    Fintype.card (ActiveStageC4Index H stage) ≤
        Fintype.card (ActiveHostEdge H × ActiveHostVertex H) :=
      Fintype.card_subtype_le _
    _ = H.card * (vertexFinset H).card := by
      simp [Fintype.card_prod]

theorem activeStageLinearUpperIndex_card_le
    (H : Hypergraph V) (stage : ℕ) (hstage : stage ≤ 4) :
    Fintype.card (ActiveStageLinearUpperIndex H stage) ≤
      H.card ^ 2 + H.card ^ 3 +
        H.card * (vertexFinset H).card := by
  rw [Fintype.card_sum]
  exact Nat.add_le_add
    (activeStageCodegreeIndex_card_le H stage hstage)
    (activeStageC4Index_card_le H stage)

theorem hostEdgePair_card_le_square (H : Hypergraph V) :
    Fintype.card (HostEdgePair H) ≤ H.card ^ 2 := by
  let edgeType := ActiveHostEdge H
  let f : HostEdgePair H → edgeType × edgeType := fun p =>
    (⟨p.left, p.left_mem⟩, ⟨p.right, p.right_mem⟩)
  have hf : Function.Injective f := by
    intro p q hpq
    rcases p with ⟨pl, plh, pr, prh, pd⟩
    rcases q with ⟨ql, qlh, qr, qrh, qd⟩
    simp only [f] at hpq
    cases hpq
    rfl
  calc
    Fintype.card (HostEdgePair H) ≤ Fintype.card (edgeType × edgeType) :=
      Fintype.card_le_of_injective f hf
    _ = H.card * H.card := by simp [edgeType, Fintype.card_prod]
    _ = H.card ^ 2 := by ring

theorem activeStageBlockUpperIndex_card_le
    (H : Hypergraph V) (current : ConflictSystem V) (stage : ℕ) :
    Fintype.card (ActiveStageBlockUpperIndex H current stage) ≤
      2 * H.card ^ 2 := by
  rw [Fintype.card_sum]
  calc
    Fintype.card (ActiveStageC5BlockIndex H stage) +
        Fintype.card (ActiveStageCommonBlockIndex H current) ≤
        Fintype.card (HostEdgePair H) + Fintype.card (HostEdgePair H) :=
      Nat.add_le_add (Fintype.card_subtype_le _)
        (Fintype.card_subtype_le _)
    _ ≤ H.card ^ 2 + H.card ^ 2 :=
      Nat.add_le_add (hostEdgePair_card_le_square H)
        (hostEdgePair_card_le_square H)
    _ = 2 * H.card ^ 2 := by ring

theorem activeHostEdge_card_eq (H : Hypergraph V) :
    Fintype.card (ActiveHostEdge H) = H.card := by simp

end
end CFMRegularization
end Erdos136

namespace Erdos136.CFMRegularization

open Finset Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- The uniform point-probability scale used for all three source stages. -/
def rawSourcePmax (d eta n : ℝ) (j : ℕ) : ℝ :=
  Real.rpow d ((j : ℝ) - 1 + 10 * rawRegularizationEps eta) /
    n ^ (j - 1)

/-- The `+3 eps` scale appearing in the paper's informal asymptotic
bookkeeping.  It cannot be derived for stage 4 from the present
`d^(j-1-2 eps)` deficit lower bound alone: the exact source expression has
power `d^(j-1+2 eps (j-1))`, hence `d^(3+6 eps)` at stage 4. -/
def paperSourcePmax (d eta n : ℝ) (j : ℕ) : ℝ :=
  Real.rpow d ((j : ℝ) - 1 + 3 * rawRegularizationEps eta) /
    n ^ (j - 1)

/-- The coefficient in the uniform `K*d*n^(j-2)` forbidden-set bound. -/
def rawForbiddenCoeff (A B : ℝ) (j : ℕ) : ℝ :=
  match j with
  | 2 => 8 * A + B
  | 3 => 16 * A + 3 * B
  | 4 => 16 * A + 5 * B
  | _ => 0

inductive RawSourceRequirement
  | degreeAtLeastOne
  | hostDominatesDegree
  | sourceCoeffTwo
  | sourceCoeffThree
  | sourceCoeffFour
  | pmaxOneTwo
  | pmaxOneThree
  | pmaxOneFour
  | symmetricRoom
  | forbiddenTwo
  | forbiddenThree
  | forbiddenFour
  | finalDegreeRoom
  deriving DecidableEq

/-- All purely numerical requirements needed for source probabilities and
Property-I centering at stages 2, 3, and 4. -/
def rawSourceRegistry (eta Gamma A B : ℝ) (heta : 0 < eta) :
    LargeDRegistry RawSourceRequirement where
  active := { .degreeAtLeastOne, .hostDominatesDegree,
    .sourceCoeffTwo, .sourceCoeffThree, .sourceCoeffFour,
    .pmaxOneTwo, .pmaxOneThree, .pmaxOneFour, .symmetricRoom,
    .forbiddenTwo, .forbiddenThree, .forbiddenFour, .finalDegreeRoom }
  condition r d := match r with
    | .degreeAtLeastOne => 1 ≤ d
    | .hostDominatesDegree => 32 ≤ Real.rpow d eta
    | .sourceCoeffTwo =>
        16 * Gamma ^ 2 ≤ Real.rpow d (8 * rawRegularizationEps eta)
    | .sourceCoeffThree =>
        128 * Gamma ^ 3 ≤ Real.rpow d (6 * rawRegularizationEps eta)
    | .sourceCoeffFour =>
        1536 * Gamma ^ 4 ≤ Real.rpow d (4 * rawRegularizationEps eta)
    | .pmaxOneTwo => 32 ≤ Real.rpow d (eta - 10 * rawRegularizationEps eta)
    | .pmaxOneThree =>
        32 ^ 2 ≤ Real.rpow d (2 * eta - 10 * rawRegularizationEps eta)
    | .pmaxOneFour =>
        32 ^ 3 ≤ Real.rpow d (3 * eta - 10 * rawRegularizationEps eta)
    | .symmetricRoom =>
        6144 * Gamma ^ 2 ≤
          Real.rpow d (1 + eta - 4 * rawRegularizationEps eta)
    | .forbiddenTwo => 32 * rawForbiddenCoeff A B 2 ≤
        Real.rpow d (eta - 12 * rawRegularizationEps eta)
    | .forbiddenThree => 32 * rawForbiddenCoeff A B 3 ≤
        Real.rpow d (eta - 12 * rawRegularizationEps eta)
    | .forbiddenFour => 32 * rawForbiddenCoeff A B 4 ≤
        Real.rpow d (eta - 12 * rawRegularizationEps eta)
    | .finalDegreeRoom =>
        64 ≤ Real.rpow d (599 * rawRegularizationEps eta / 600)
  eventually_condition := by
    intro r _hr
    cases r with
    | degreeAtLeastOne => exact eventually_ge_atTop 1
    | hostDominatesDegree => exact eventually_const_le_rpow_real 32 eta heta
    | sourceCoeffTwo =>
        exact eventually_const_le_rpow_real (16 * Gamma ^ 2)
          (8 * rawRegularizationEps eta) (by simp [rawRegularizationEps]; linarith)
    | sourceCoeffThree =>
        exact eventually_const_le_rpow_real (128 * Gamma ^ 3)
          (6 * rawRegularizationEps eta) (by simp [rawRegularizationEps]; linarith)
    | sourceCoeffFour =>
        exact eventually_const_le_rpow_real (1536 * Gamma ^ 4)
          (4 * rawRegularizationEps eta) (by simp [rawRegularizationEps]; linarith)
    | pmaxOneTwo =>
        exact eventually_const_le_rpow_real 32
          (eta - 10 * rawRegularizationEps eta)
          (by simp [rawRegularizationEps]; linarith)
    | pmaxOneThree =>
        exact eventually_const_le_rpow_real (32 ^ 2)
          (2 * eta - 10 * rawRegularizationEps eta)
          (by simp [rawRegularizationEps]; linarith)
    | pmaxOneFour =>
        exact eventually_const_le_rpow_real (32 ^ 3)
          (3 * eta - 10 * rawRegularizationEps eta)
          (by simp [rawRegularizationEps]; linarith)
    | symmetricRoom =>
        exact eventually_const_le_rpow_real (6144 * Gamma ^ 2)
          (1 + eta - 4 * rawRegularizationEps eta)
          (by simp [rawRegularizationEps]; linarith)
    | forbiddenTwo =>
        exact eventually_const_le_rpow_real (32 * rawForbiddenCoeff A B 2)
          (eta - 12 * rawRegularizationEps eta)
          (by simp [rawRegularizationEps]; linarith)
    | forbiddenThree =>
        exact eventually_const_le_rpow_real (32 * rawForbiddenCoeff A B 3)
          (eta - 12 * rawRegularizationEps eta)
          (by simp [rawRegularizationEps]; linarith)
    | forbiddenFour =>
        exact eventually_const_le_rpow_real (32 * rawForbiddenCoeff A B 4)
          (eta - 12 * rawRegularizationEps eta)
          (by simp [rawRegularizationEps]; linarith)
    | finalDegreeRoom =>
        exact eventually_const_le_rpow_real 64
          (599 * rawRegularizationEps eta / 600)
          (by simp [rawRegularizationEps]; positivity)

structure RawSourceCutoffSpec (eta Gamma A B d : ℝ) : Prop where
  degreeAtLeastOne : 1 ≤ d
  hostDominatesDegree : 32 ≤ Real.rpow d eta
  sourceCoeffTwo :
    16 * Gamma ^ 2 ≤ Real.rpow d (8 * rawRegularizationEps eta)
  sourceCoeffThree :
    128 * Gamma ^ 3 ≤ Real.rpow d (6 * rawRegularizationEps eta)
  sourceCoeffFour :
    1536 * Gamma ^ 4 ≤ Real.rpow d (4 * rawRegularizationEps eta)
  pmaxOneTwo : 32 ≤ Real.rpow d (eta - 10 * rawRegularizationEps eta)
  pmaxOneThree :
    32 ^ 2 ≤ Real.rpow d (2 * eta - 10 * rawRegularizationEps eta)
  pmaxOneFour :
    32 ^ 3 ≤ Real.rpow d (3 * eta - 10 * rawRegularizationEps eta)
  symmetricRoom :
    6144 * Gamma ^ 2 ≤
      Real.rpow d (1 + eta - 4 * rawRegularizationEps eta)
  forbiddenTwo : 32 * rawForbiddenCoeff A B 2 ≤
    Real.rpow d (eta - 12 * rawRegularizationEps eta)
  forbiddenThree : 32 * rawForbiddenCoeff A B 3 ≤
    Real.rpow d (eta - 12 * rawRegularizationEps eta)
  forbiddenFour : 32 * rawForbiddenCoeff A B 4 ≤
    Real.rpow d (eta - 12 * rawRegularizationEps eta)
  finalDegreeRoom :
    64 ≤ Real.rpow d (599 * rawRegularizationEps eta / 600)

theorem exists_rawSourceCutoff (eta Gamma A B : ℝ) (heta : 0 < eta) :
    ∃ d0 : ℝ, ∀ d, d0 ≤ d → RawSourceCutoffSpec eta Gamma A B d := by
  let R := rawSourceRegistry eta Gamma A B heta
  obtain ⟨d0, hd0⟩ := R.exists_cutoff
  refine ⟨d0, fun d hd => ?_⟩
  have hreq (r : RawSourceRequirement) : R.condition r d := by
    apply hd0 d hd r
    cases r <;> simp [R, rawSourceRegistry]
  constructor
  · simpa [R, rawSourceRegistry] using hreq .degreeAtLeastOne
  · simpa [R, rawSourceRegistry] using hreq .hostDominatesDegree
  · simpa [R, rawSourceRegistry] using hreq .sourceCoeffTwo
  · simpa [R, rawSourceRegistry] using hreq .sourceCoeffThree
  · simpa [R, rawSourceRegistry] using hreq .sourceCoeffFour
  · simpa [R, rawSourceRegistry] using hreq .pmaxOneTwo
  · simpa [R, rawSourceRegistry] using hreq .pmaxOneThree
  · simpa [R, rawSourceRegistry] using hreq .pmaxOneFour
  · simpa [R, rawSourceRegistry] using hreq .symmetricRoom
  · simpa [R, rawSourceRegistry] using hreq .forbiddenTwo
  · simpa [R, rawSourceRegistry] using hreq .forbiddenThree
  · simpa [R, rawSourceRegistry] using hreq .forbiddenFour
  · simpa [R, rawSourceRegistry] using hreq .finalDegreeRoom

theorem sourceExpression_two_le_rawSourcePmax
    {d eta n Gamma : ℝ} (hd : 0 < d) (hn : 0 < n)
    (hcoeff :
      16 * Gamma ^ 2 ≤ Real.rpow d (8 * rawRegularizationEps eta)) :
    (Nat.factorial (2 - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((2 : ℝ) - 1)) ^ 2 /
        ((n * Real.rpow d ((2 : ℝ) - 1 -
          2 * rawRegularizationEps eta)) ^ (2 - 1)) ≤
      rawSourcePmax d eta n 2 := by
  have hd0 : 0 ≤ d := hd.le
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hpow :
      Real.rpow d (8 * rawRegularizationEps eta) *
          Real.rpow d (1 + 2 * rawRegularizationEps eta) =
        Real.rpow d (1 + 10 * rawRegularizationEps eta) := by
    calc
      _ = Real.rpow d
          (8 * rawRegularizationEps eta +
            (1 + 2 * rawRegularizationEps eta)) :=
        (Real.rpow_add hd _ _).symm
      _ = _ := by congr 1; ring
  have hratio :
      d ^ 2 / Real.rpow d (1 - 2 * rawRegularizationEps eta) =
        Real.rpow d (1 + 2 * rawRegularizationEps eta) := by
    calc
      d ^ 2 / Real.rpow d (1 - 2 * rawRegularizationEps eta) =
          Real.rpow d (2 : ℝ) /
            Real.rpow d (1 - 2 * rawRegularizationEps eta) := by
        congr 1
        exact (Real.rpow_natCast d 2).symm
      _ = Real.rpow d ((2 : ℝ) - (1 - 2 * rawRegularizationEps eta)) :=
        (Real.rpow_sub hd _ _).symm
      _ = _ := by congr 1; ring
  calc
    (Nat.factorial (2 - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((2 : ℝ) - 1)) ^ 2 /
        ((n * Real.rpow d ((2 : ℝ) - 1 -
          2 * rawRegularizationEps eta)) ^ (2 - 1)) =
        (16 * Gamma ^ 2) *
          Real.rpow d (1 + 2 * rawRegularizationEps eta) / n := by
      norm_num
      calc
        (4 * Gamma * d) ^ 2 /
            (n * Real.rpow d (1 - 2 * rawRegularizationEps eta)) =
          (16 * Gamma ^ 2) *
            (d ^ 2 / Real.rpow d (1 - 2 * rawRegularizationEps eta)) / n := by
              ring
        _ = _ := by
          rw [hratio]
          rfl
    _ ≤ Real.rpow d (8 * rawRegularizationEps eta) *
          Real.rpow d (1 + 2 * rawRegularizationEps eta) / n := by
      apply div_le_div_of_nonneg_right
      exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hd0 _)
      exact hn.le
    _ = rawSourcePmax d eta n 2 := by
      rw [hpow]
      norm_num [rawSourcePmax]

theorem sourceExpression_three_le_rawSourcePmax
    {d eta n Gamma : ℝ} (hd : 0 < d) (hn : 0 < n)
    (hcoeff :
      128 * Gamma ^ 3 ≤ Real.rpow d (6 * rawRegularizationEps eta)) :
    (Nat.factorial (3 - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((3 : ℝ) - 1)) ^ 3 /
        ((n * Real.rpow d ((3 : ℝ) - 1 -
          2 * rawRegularizationEps eta)) ^ (3 - 1)) ≤
      rawSourcePmax d eta n 3 := by
  have hd0 : 0 ≤ d := hd.le
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hnum : (Real.rpow d 2) ^ 3 = Real.rpow d 6 := by
    calc
      _ = Real.rpow (Real.rpow d 2) 3 :=
        (Real.rpow_natCast (Real.rpow d 2) 3).symm
      _ = Real.rpow d ((2 : ℝ) * 3) := (Real.rpow_mul hd0 2 3).symm
      _ = _ := by norm_num
  have hden :
      (Real.rpow d (2 - 2 * rawRegularizationEps eta)) ^ 2 =
        Real.rpow d (2 * (2 - 2 * rawRegularizationEps eta)) := by
    calc
      _ = Real.rpow (Real.rpow d (2 - 2 * rawRegularizationEps eta)) 2 :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow d ((2 - 2 * rawRegularizationEps eta) * 2) :=
        (Real.rpow_mul hd0 _ 2).symm
      _ = _ := by congr 1; ring
  have hratio :
      (Real.rpow d 2) ^ 3 /
          (Real.rpow d (2 - 2 * rawRegularizationEps eta)) ^ 2 =
        Real.rpow d (2 + 4 * rawRegularizationEps eta) := by
    rw [hnum, hden]
    calc
      Real.rpow d 6 /
          Real.rpow d (2 * (2 - 2 * rawRegularizationEps eta)) =
        Real.rpow d (6 - 2 * (2 - 2 * rawRegularizationEps eta)) :=
          (Real.rpow_sub hd _ _).symm
      _ = _ := by congr 1; ring
  have hpow :
      Real.rpow d (6 * rawRegularizationEps eta) *
          Real.rpow d (2 + 4 * rawRegularizationEps eta) =
        Real.rpow d (2 + 10 * rawRegularizationEps eta) := by
    calc
      _ = Real.rpow d
          (6 * rawRegularizationEps eta +
            (2 + 4 * rawRegularizationEps eta)) :=
        (Real.rpow_add hd _ _).symm
      _ = _ := by congr 1; ring
  calc
    (Nat.factorial (3 - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((3 : ℝ) - 1)) ^ 3 /
        ((n * Real.rpow d ((3 : ℝ) - 1 -
          2 * rawRegularizationEps eta)) ^ (3 - 1)) =
        (128 * Gamma ^ 3) *
          Real.rpow d (2 + 4 * rawRegularizationEps eta) / n ^ 2 := by
      norm_num
      have hbase : (d ^ 2 : ℝ) = Real.rpow d 2 :=
        (Real.rpow_natCast d 2).symm
      calc
        2 * (4 * Gamma * d ^ 2) ^ 3 /
            (n * Real.rpow d (2 - 2 * rawRegularizationEps eta)) ^ 2 =
          2 * (4 * Gamma * Real.rpow d 2) ^ 3 /
            (n * Real.rpow d (2 - 2 * rawRegularizationEps eta)) ^ 2 := by
              rw [hbase]
        _ =
          (128 * Gamma ^ 3) *
            ((Real.rpow d 2) ^ 3 /
              (Real.rpow d (2 - 2 * rawRegularizationEps eta)) ^ 2) /
                n ^ 2 := by ring
        _ = _ := by rw [hratio]; rfl
    _ ≤ Real.rpow d (6 * rawRegularizationEps eta) *
          Real.rpow d (2 + 4 * rawRegularizationEps eta) / n ^ 2 := by
      apply div_le_div_of_nonneg_right
      exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hd0 _)
      positivity
    _ = rawSourcePmax d eta n 3 := by
      rw [hpow]
      norm_num [rawSourcePmax]

theorem sourceExpression_four_le_rawSourcePmax
    {d eta n Gamma : ℝ} (hd : 0 < d) (hn : 0 < n)
    (hcoeff :
      1536 * Gamma ^ 4 ≤ Real.rpow d (4 * rawRegularizationEps eta)) :
    (Nat.factorial (4 - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((4 : ℝ) - 1)) ^ 4 /
        ((n * Real.rpow d ((4 : ℝ) - 1 -
          2 * rawRegularizationEps eta)) ^ (4 - 1)) ≤
      rawSourcePmax d eta n 4 := by
  have hd0 : 0 ≤ d := hd.le
  have hnum : (Real.rpow d 3) ^ 4 = Real.rpow d 12 := by
    calc
      _ = Real.rpow (Real.rpow d 3) 4 :=
        (Real.rpow_natCast (Real.rpow d 3) 4).symm
      _ = Real.rpow d ((3 : ℝ) * 4) := (Real.rpow_mul hd0 3 4).symm
      _ = _ := by norm_num
  have hden :
      (Real.rpow d (3 - 2 * rawRegularizationEps eta)) ^ 3 =
        Real.rpow d (3 * (3 - 2 * rawRegularizationEps eta)) := by
    calc
      _ = Real.rpow (Real.rpow d (3 - 2 * rawRegularizationEps eta)) 3 :=
        (Real.rpow_natCast _ 3).symm
      _ = Real.rpow d ((3 - 2 * rawRegularizationEps eta) * 3) :=
        (Real.rpow_mul hd0 _ 3).symm
      _ = _ := by congr 1; ring
  have hratio :
      (Real.rpow d 3) ^ 4 /
          (Real.rpow d (3 - 2 * rawRegularizationEps eta)) ^ 3 =
        Real.rpow d (3 + 6 * rawRegularizationEps eta) := by
    rw [hnum, hden]
    calc
      Real.rpow d 12 /
          Real.rpow d (3 * (3 - 2 * rawRegularizationEps eta)) =
        Real.rpow d (12 - 3 * (3 - 2 * rawRegularizationEps eta)) :=
          (Real.rpow_sub hd _ _).symm
      _ = _ := by congr 1; ring
  have hpow :
      Real.rpow d (4 * rawRegularizationEps eta) *
          Real.rpow d (3 + 6 * rawRegularizationEps eta) =
        Real.rpow d (3 + 10 * rawRegularizationEps eta) := by
    calc
      _ = Real.rpow d
          (4 * rawRegularizationEps eta +
            (3 + 6 * rawRegularizationEps eta)) :=
        (Real.rpow_add hd _ _).symm
      _ = _ := by congr 1; ring
  calc
    (Nat.factorial (4 - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((4 : ℝ) - 1)) ^ 4 /
        ((n * Real.rpow d ((4 : ℝ) - 1 -
          2 * rawRegularizationEps eta)) ^ (4 - 1)) =
        (1536 * Gamma ^ 4) *
          Real.rpow d (3 + 6 * rawRegularizationEps eta) / n ^ 3 := by
      norm_num
      have hbase : (d ^ 3 : ℝ) = Real.rpow d 3 :=
        (Real.rpow_natCast d 3).symm
      calc
        6 * (4 * Gamma * d ^ 3) ^ 4 /
            (n * Real.rpow d (3 - 2 * rawRegularizationEps eta)) ^ 3 =
          6 * (4 * Gamma * Real.rpow d 3) ^ 4 /
            (n * Real.rpow d (3 - 2 * rawRegularizationEps eta)) ^ 3 := by
              rw [hbase]
        _ =
          (1536 * Gamma ^ 4) *
            ((Real.rpow d 3) ^ 4 /
              (Real.rpow d (3 - 2 * rawRegularizationEps eta)) ^ 3) /
                n ^ 3 := by ring
        _ = _ := by rw [hratio]; rfl
    _ ≤ Real.rpow d (4 * rawRegularizationEps eta) *
          Real.rpow d (3 + 6 * rawRegularizationEps eta) / n ^ 3 := by
      apply div_le_div_of_nonneg_right
      exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hd0 _)
      positivity
    _ = rawSourcePmax d eta n 4 := by
      rw [hpow]
      norm_num [rawSourcePmax]

theorem sourceExpression_le_rawSourcePmax_of_stage
    {d eta n Gamma A B : ℝ} {j : ℕ} (hj : j ∈ ({2, 3, 4} : Finset ℕ))
    (hd : 0 < d) (hn : 0 < n)
    (hcut : RawSourceCutoffSpec eta Gamma A B d) :
    (Nat.factorial (j - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ j /
        ((n * Real.rpow d ((j : ℝ) - 1 -
          2 * rawRegularizationEps eta)) ^ (j - 1)) ≤
      rawSourcePmax d eta n j := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · exact sourceExpression_two_le_rawSourcePmax hd hn hcut.sourceCoeffTwo
  · exact sourceExpression_three_le_rawSourcePmax hd hn hcut.sourceCoeffThree
  · exact sourceExpression_four_le_rawSourcePmax hd hn hcut.sourceCoeffFour

theorem rawSourcePmax_two_le_one
    {d eta n Gamma A B : ℝ}
    (hd : 0 < d) (hn : 0 < n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (hcut : RawSourceCutoffSpec eta Gamma A B d) :
    rawSourcePmax d eta n 2 ≤ 1 := by
  let eps := rawRegularizationEps eta
  have hpow :
      Real.rpow d (eta - 10 * eps) *
          Real.rpow d (1 + 10 * eps) = Real.rpow d (1 + eta) := by
    calc
      _ = Real.rpow d ((eta - 10 * eps) + (1 + 10 * eps)) :=
        (Real.rpow_add hd _ _).symm
      _ = _ := by congr 1; ring
  have hscaled :
      32 * Real.rpow d (1 + 10 * eps) ≤ Real.rpow d (1 + eta) := by
    calc
      _ ≤ Real.rpow d (eta - 10 * eps) *
          Real.rpow d (1 + 10 * eps) :=
        mul_le_mul_of_nonneg_right hcut.pmaxOneTwo (Real.rpow_nonneg hd.le _)
      _ = _ := hpow
  have hnum : Real.rpow d (1 + 10 * eps) ≤ n := by
    calc
      _ ≤ Real.rpow d (1 + eta) / 32 := by nlinarith
      _ ≤ n := hhost
  rw [rawSourcePmax]
  norm_num
  exact (div_le_one hn).2 hnum

theorem rawSourcePmax_three_le_one
    {d eta n Gamma A B : ℝ}
    (hd : 0 < d) (hn : 0 < n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (hcut : RawSourceCutoffSpec eta Gamma A B d) :
    rawSourcePmax d eta n 3 ≤ 1 := by
  let eps := rawRegularizationEps eta
  have hpow :
      Real.rpow d (2 * eta - 10 * eps) *
          Real.rpow d (2 + 10 * eps) = Real.rpow d (2 * (1 + eta)) := by
    calc
      _ = Real.rpow d ((2 * eta - 10 * eps) + (2 + 10 * eps)) :=
        (Real.rpow_add hd _ _).symm
      _ = _ := by congr 1; ring
  have hscaled :
      32 ^ 2 * Real.rpow d (2 + 10 * eps) ≤
        Real.rpow d (2 * (1 + eta)) := by
    calc
      _ ≤ Real.rpow d (2 * eta - 10 * eps) *
          Real.rpow d (2 + 10 * eps) :=
        mul_le_mul_of_nonneg_right hcut.pmaxOneThree
          (Real.rpow_nonneg hd.le _)
      _ = _ := hpow
  have hhostpow : (Real.rpow d (1 + eta) / 32) ^ 2 ≤ n ^ 2 := by
    exact pow_le_pow_left₀
      (div_nonneg (Real.rpow_nonneg hd.le _) (by norm_num)) hhost 2
  have hbasepow : (Real.rpow d (1 + eta)) ^ 2 =
      Real.rpow d (2 * (1 + eta)) := by
    calc
      _ = Real.rpow (Real.rpow d (1 + eta)) 2 :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow d ((1 + eta) * 2) := (Real.rpow_mul hd.le _ 2).symm
      _ = _ := by congr 1; ring
  have hnum : Real.rpow d (2 + 10 * eps) ≤ n ^ 2 := by
    have hdiv : Real.rpow d (2 + 10 * eps) ≤
        Real.rpow d (2 * (1 + eta)) / 32 ^ 2 := by
      nlinarith
    calc
      _ ≤ Real.rpow d (2 * (1 + eta)) / 32 ^ 2 := hdiv
      _ = (Real.rpow d (1 + eta) / 32) ^ 2 := by
        rw [← hbasepow]
        ring
      _ ≤ n ^ 2 := hhostpow
  rw [rawSourcePmax]
  norm_num
  exact (div_le_one (sq_pos_of_pos hn)).2 hnum

theorem rawSourcePmax_four_le_one
    {d eta n Gamma A B : ℝ}
    (hd : 0 < d) (hn : 0 < n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (hcut : RawSourceCutoffSpec eta Gamma A B d) :
    rawSourcePmax d eta n 4 ≤ 1 := by
  let eps := rawRegularizationEps eta
  have hpow :
      Real.rpow d (3 * eta - 10 * eps) *
          Real.rpow d (3 + 10 * eps) = Real.rpow d (3 * (1 + eta)) := by
    calc
      _ = Real.rpow d ((3 * eta - 10 * eps) + (3 + 10 * eps)) :=
        (Real.rpow_add hd _ _).symm
      _ = _ := by congr 1; ring
  have hscaled :
      32 ^ 3 * Real.rpow d (3 + 10 * eps) ≤
        Real.rpow d (3 * (1 + eta)) := by
    calc
      _ ≤ Real.rpow d (3 * eta - 10 * eps) *
          Real.rpow d (3 + 10 * eps) :=
        mul_le_mul_of_nonneg_right hcut.pmaxOneFour
          (Real.rpow_nonneg hd.le _)
      _ = _ := hpow
  have hhostpow : (Real.rpow d (1 + eta) / 32) ^ 3 ≤ n ^ 3 := by
    exact pow_le_pow_left₀
      (div_nonneg (Real.rpow_nonneg hd.le _) (by norm_num)) hhost 3
  have hbasepow : (Real.rpow d (1 + eta)) ^ 3 =
      Real.rpow d (3 * (1 + eta)) := by
    calc
      _ = Real.rpow (Real.rpow d (1 + eta)) 3 :=
        (Real.rpow_natCast _ 3).symm
      _ = Real.rpow d ((1 + eta) * 3) := (Real.rpow_mul hd.le _ 3).symm
      _ = _ := by congr 1; ring
  have hnum : Real.rpow d (3 + 10 * eps) ≤ n ^ 3 := by
    have hdiv : Real.rpow d (3 + 10 * eps) ≤
        Real.rpow d (3 * (1 + eta)) / 32 ^ 3 := by
      nlinarith
    calc
      _ ≤ Real.rpow d (3 * (1 + eta)) / 32 ^ 3 := hdiv
      _ = (Real.rpow d (1 + eta) / 32) ^ 3 := by
        rw [← hbasepow]
        ring
      _ ≤ n ^ 3 := hhostpow
  rw [rawSourcePmax]
  norm_num
  exact (div_le_one (pow_pos hn 3)).2 hnum

theorem rawSource_degree_le_host
    {d eta n Gamma A B : ℝ} (hd : 0 < d)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (hcut : RawSourceCutoffSpec eta Gamma A B d) : d ≤ n := by
  have hmul : 32 * d ≤ Real.rpow d eta * d :=
    mul_le_mul_of_nonneg_right hcut.hostDominatesDegree hd.le
  have hpow : Real.rpow d eta * d = Real.rpow d (1 + eta) := by
    calc
      _ = Real.rpow d eta * Real.rpow d 1 :=
        congrArg (fun z => Real.rpow d eta * z) (Real.rpow_one d).symm
      _ = Real.rpow d (eta + 1) := (Real.rpow_add hd _ _).symm
      _ = _ := by congr 1; ring
  have : d ≤ Real.rpow d (1 + eta) / 32 := by
    rw [← hpow]
    nlinarith
  exact this.trans hhost

theorem rawSourcePmax_le_one_of_stage
    {d eta n Gamma A B : ℝ} {j : ℕ}
    (hj : j ∈ ({2, 3, 4} : Finset ℕ))
    (hd : 0 < d) (hn : 0 < n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (hcut : RawSourceCutoffSpec eta Gamma A B d) :
    rawSourcePmax d eta n j ≤ 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · exact rawSourcePmax_two_le_one hd hn hhost hcut
  · exact rawSourcePmax_three_le_one hd hn hhost hcut
  · exact rawSourcePmax_four_le_one hd hn hhost hcut

theorem rawSourcePmax_nonneg (d eta n : ℝ) (j : ℕ)
    (hd : 0 ≤ d) (hn : 0 ≤ n) : 0 ≤ rawSourcePmax d eta n j := by
  exact div_nonneg (Real.rpow_nonneg hd _) (pow_nonneg hn _)

theorem paperSourcePmax_le_rawSourcePmax
    {d eta n : ℝ} (j : ℕ) (hd : 1 ≤ d) (heta : 0 ≤ eta) (hn : 0 ≤ n) :
    paperSourcePmax d eta n j ≤ rawSourcePmax d eta n j := by
  apply div_le_div_of_nonneg_right
  · apply Real.rpow_le_rpow_of_exponent_le hd
    simp only [rawRegularizationEps]
    linarith
  · exact pow_nonneg hn _

structure PaperSourceProbabilitySpec (d eta n Gamma : ℝ) (j : ℕ) : Prop where
  sourceExpressionBound :
    (Nat.factorial (j - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ j /
        ((n * Real.rpow d ((j : ℝ) - 1 -
          2 * rawRegularizationEps eta)) ^ (j - 1)) ≤
      paperSourcePmax d eta n j
  pmaxNonneg : 0 ≤ paperSourcePmax d eta n j
  pmaxAtMostOne : paperSourcePmax d eta n j ≤ 1

structure RawSourceProbabilitySpec (d eta n Gamma : ℝ) (j : ℕ) : Prop where
  sourceExpressionBound :
    (Nat.factorial (j - 1) : ℝ) *
          (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ j /
        ((n * Real.rpow d ((j : ℝ) - 1 -
          2 * rawRegularizationEps eta)) ^ (j - 1)) ≤
      rawSourcePmax d eta n j
  pmaxNonneg : 0 ≤ rawSourcePmax d eta n j
  pmaxAtMostOne : rawSourcePmax d eta n j ≤ 1

theorem rawSourceProbabilitySpec_of_cutoff
    {d eta n Gamma A B : ℝ} {j : ℕ}
    (hj : j ∈ ({2, 3, 4} : Finset ℕ))
    (hd : 0 < d) (hn : 0 < n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (hcut : RawSourceCutoffSpec eta Gamma A B d) :
    RawSourceProbabilitySpec d eta n Gamma j := by
  refine ⟨?_, rawSourcePmax_nonneg d eta n j hd.le hn.le, ?_⟩
  · exact sourceExpression_le_rawSourcePmax_of_stage hj hd hn hcut
  · exact rawSourcePmax_le_one_of_stage hj hd hn hhost hcut

/-- Conditional paper-scale route: the only extra premise is the exact
`+3 eps` source-expression estimate which is unavailable from the current
deficit bounds at stage 4. -/
theorem paperSourceProbabilitySpec_of_exact_bound
    {d eta n Gamma A B : ℝ} {j : ℕ}
    (hj : j ∈ ({2, 3, 4} : Finset ℕ))
    (hd : 0 < d) (heta : 0 ≤ eta) (hn : 0 < n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (hcut : RawSourceCutoffSpec eta Gamma A B d)
    (hexact :
      (Nat.factorial (j - 1) : ℝ) *
            (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ j /
          ((n * Real.rpow d ((j : ℝ) - 1 -
            2 * rawRegularizationEps eta)) ^ (j - 1)) ≤
        paperSourcePmax d eta n j) :
    PaperSourceProbabilitySpec d eta n Gamma j := by
  have hpaperRaw := paperSourcePmax_le_rawSourcePmax j hcut.degreeAtLeastOne
    heta hn.le
  refine ⟨hexact, ?_, hpaperRaw.trans
    (rawSourcePmax_le_one_of_stage hj hd hn hhost hcut)⟩
  exact div_nonneg (Real.rpow_nonneg hd.le _) (pow_nonneg hn.le _)

/- These three wrappers compile once the current production source is re-emitted;
the shared canonical olean predates the card-forbidden API. -/
/-
theorem forbiddenCard_two_le_rawCoeff
    {H : Hypergraph V} {C : ConflictSystem V} {D : ℕ}
    {d A B : ℝ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    (hD : (D : ℝ) ≤ A * d)
    (hlayer2 : (layerMaxDegree H C 2 : ℝ) ≤ B * d)
    {e : Finset V} (heH : e ∈ H) :
    ((forbiddenIncidentCompletions H C 2 e).card : ℝ) ≤
      rawForbiddenCoeff A B 2 * d * (H.card : ℝ) ^ (2 - 2) := by
  have hraw := card_forbiddenIncidentCompletions_two_le
    huniform hmax hC hcard heH
  have hrawR : ((forbiddenIncidentCompletions H C 2 e).card : ℝ) ≤
      8 * (D : ℝ) + (layerMaxDegree H C 2 : ℝ) := by exact_mod_cast hraw
  simp [rawForbiddenCoeff]
  linarith

theorem forbiddenCard_three_le_rawCoeff
    {H : Hypergraph V} {C : ConflictSystem V} {D : ℕ}
    {d n A B : ℝ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    (hd : 0 ≤ d) (hn : 0 ≤ n) (hHcard : (H.card : ℝ) ≤ n)
    (hdn : d ≤ n) (hB : 0 ≤ B)
    (hD : (D : ℝ) ≤ A * d)
    (hlayer2 : (layerMaxDegree H C 2 : ℝ) ≤ B * d)
    (hlayer3 : (layerMaxDegree H C 3 : ℝ) ≤ B * d ^ 2)
    {e : Finset V} (heH : e ∈ H) :
    ((forbiddenIncidentCompletions H C 3 e).card : ℝ) ≤
      rawForbiddenCoeff A B 3 * d * n ^ (3 - 2) := by
  have hraw := card_forbiddenIncidentCompletions_three_le
    huniform hmax hC hcard heH
  have hrawR : ((forbiddenIncidentCompletions H C 3 e).card : ℝ) ≤
      (8 * (D : ℝ)) * (H.card : ℝ) +
        (H.card : ℝ) * (8 * (D : ℝ)) +
        ((layerMaxDegree H C 2 : ℝ) * (H.card : ℝ) +
          (H.card : ℝ) * (layerMaxDegree H C 2 : ℝ) +
          (layerMaxDegree H C 3 : ℝ)) := by exact_mod_cast hraw
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hl20 : 0 ≤ (layerMaxDegree H C 2 : ℝ) := Nat.cast_nonneg _
  have hDcard : (D : ℝ) * (H.card : ℝ) ≤ (A * d) * n :=
    calc
      _ ≤ (D : ℝ) * n := mul_le_mul_of_nonneg_left hHcard hD0
      _ ≤ (A * d) * n := mul_le_mul_of_nonneg_right hD hn
  have hl2card : (layerMaxDegree H C 2 : ℝ) * (H.card : ℝ) ≤
      (B * d) * n :=
    calc
      _ ≤ (layerMaxDegree H C 2 : ℝ) * n :=
        mul_le_mul_of_nonneg_left hHcard hl20
      _ ≤ (B * d) * n := mul_le_mul_of_nonneg_right hlayer2 hn
  have hl3dn : (layerMaxDegree H C 3 : ℝ) ≤ B * d * n := by
    calc
      _ ≤ B * d ^ 2 := hlayer3
      _ ≤ B * d * n := by
        have := mul_le_mul_of_nonneg_left hdn (mul_nonneg hB hd)
        nlinarith
  simp [rawForbiddenCoeff]
  nlinarith

theorem forbiddenCard_four_le_rawCoeff
    {H : Hypergraph V} {C : ConflictSystem V} {D : ℕ}
    {d n A B : ℝ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    (hd : 0 ≤ d) (hn : 0 ≤ n) (hHcard : (H.card : ℝ) ≤ n)
    (hdn : d ≤ n) (hB : 0 ≤ B)
    (hD : (D : ℝ) ≤ A * d)
    (hlayer2 : (layerMaxDegree H C 2 : ℝ) ≤ B * d)
    (hlayer3 : (layerMaxDegree H C 3 : ℝ) ≤ B * d ^ 2)
    (hlayer4 : (layerMaxDegree H C 4 : ℝ) ≤ B * d ^ 3)
    {e : Finset V} (heH : e ∈ H) :
    ((forbiddenIncidentCompletions H C 4 e).card : ℝ) ≤
      rawForbiddenCoeff A B 4 * d * n ^ (4 - 2) := by
  have hraw := card_forbiddenIncidentCompletions_four_le
    huniform hmax hC hcard heH
  have hrawR : ((forbiddenIncidentCompletions H C 4 e).card : ℝ) ≤
      (8 * (D : ℝ)) * (H.card : ℝ) ^ 2 +
        ((H.card : ℝ) * (8 * (D : ℝ))) * (H.card : ℝ) +
        ((layerMaxDegree H C 2 : ℝ) * (H.card : ℝ) ^ 2 +
          ((H.card : ℝ) * (layerMaxDegree H C 2 : ℝ)) * (H.card : ℝ) +
          (layerMaxDegree H C 3 : ℝ) * (H.card : ℝ) +
          (H.card : ℝ) * (layerMaxDegree H C 3 : ℝ) +
          (layerMaxDegree H C 4 : ℝ)) := by exact_mod_cast hraw
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hl20 : 0 ≤ (layerMaxDegree H C 2 : ℝ) := Nat.cast_nonneg _
  have hl30 : 0 ≤ (layerMaxDegree H C 3 : ℝ) := Nat.cast_nonneg _
  have hH0 : 0 ≤ (H.card : ℝ) := Nat.cast_nonneg _
  have hHsq : (H.card : ℝ) ^ 2 ≤ n ^ 2 :=
    pow_le_pow_left₀ hH0 hHcard 2
  have hDcard2 : (D : ℝ) * (H.card : ℝ) ^ 2 ≤ (A * d) * n ^ 2 :=
    calc
      _ ≤ (D : ℝ) * n ^ 2 := mul_le_mul_of_nonneg_left hHsq hD0
      _ ≤ (A * d) * n ^ 2 := mul_le_mul_of_nonneg_right hD (sq_nonneg n)
  have hl2card2 : (layerMaxDegree H C 2 : ℝ) * (H.card : ℝ) ^ 2 ≤
      (B * d) * n ^ 2 :=
    calc
      _ ≤ (layerMaxDegree H C 2 : ℝ) * n ^ 2 :=
        mul_le_mul_of_nonneg_left hHsq hl20
      _ ≤ (B * d) * n ^ 2 :=
        mul_le_mul_of_nonneg_right hlayer2 (sq_nonneg n)
  have hl3card : (layerMaxDegree H C 3 : ℝ) * (H.card : ℝ) ≤
      (B * d) * n ^ 2 := by
    calc
      _ ≤ (B * d ^ 2) * (H.card : ℝ) :=
        mul_le_mul_of_nonneg_right hlayer3 hH0
      _ ≤ (B * d ^ 2) * n := by
        apply mul_le_mul_of_nonneg_left hHcard
        positivity
      _ ≤ (B * d) * n ^ 2 := by
        have := mul_le_mul_of_nonneg_left hdn (mul_nonneg hB hd)
        have hdn' := mul_le_mul_of_nonneg_left hdn hn
        nlinarith
  have hl4dn2 : (layerMaxDegree H C 4 : ℝ) ≤ (B * d) * n ^ 2 := by
    calc
      _ ≤ B * d ^ 3 := hlayer4
      _ ≤ (B * d) * n ^ 2 := by
        have hsqdn : d ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hd hdn 2
        have := mul_le_mul_of_nonneg_left hsqdn (mul_nonneg hB hd)
        nlinarith
  simp [rawForbiddenCoeff]
  nlinarith
-/

/-- Corrected forbidden-mass absorption for the uniform `+10 eps` source
probability scale and the `/32` host-size lower bound. -/
theorem forbiddenMass_absorbed_rawSource
    {j : ℕ} (hj2 : 2 ≤ j)
    {d n eta K pmax : ℝ} {m : ℕ}
    (hd : 0 < d) (hK : 0 ≤ K) (hpmax0 : 0 ≤ pmax)
    (hcard : (m : ℝ) ≤ K * d * n ^ (j - 2))
    (hpmax : pmax ≤ rawSourcePmax d eta n j)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (habsorb : 32 * K ≤
      Real.rpow d (eta - 12 * rawRegularizationEps eta)) :
    (m : ℝ) * pmax ≤
      Real.rpow d ((j : ℝ) - 1 - 2 * rawRegularizationEps eta) := by
  let eps := rawRegularizationEps eta
  have hnpos : 0 < n :=
    (div_pos (Real.rpow_pos_of_pos hd _) (by norm_num)).trans_le hhost
  have hpowpos : 0 < n ^ (j - 1) := pow_pos hnpos _
  have hnum0 : 0 ≤ K * d * n ^ (j - 2) := by positivity
  have hjpred : j - 1 = (j - 2) + 1 := by omega
  have hhostpos : 0 < Real.rpow d (1 + eta) / 32 :=
    div_pos (Real.rpow_pos_of_pos hd _) (by norm_num)
  calc
    (m : ℝ) * pmax ≤ (K * d * n ^ (j - 2)) * pmax :=
      mul_le_mul_of_nonneg_right hcard hpmax0
    _ ≤ (K * d * n ^ (j - 2)) * rawSourcePmax d eta n j :=
      mul_le_mul_of_nonneg_left hpmax hnum0
    _ = K * d * Real.rpow d ((j : ℝ) - 1 + 10 * eps) / n := by
      rw [rawSourcePmax, hjpred, pow_succ]
      field_simp
      simp only [eps]
    _ ≤ K * d * Real.rpow d ((j : ℝ) - 1 + 10 * eps) /
        (Real.rpow d (1 + eta) / 32) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (mul_nonneg hK hd.le) (Real.rpow_nonneg hd.le _)
      · exact hhostpos
      · exact hhost
    _ = (32 * K) * d * Real.rpow d ((j : ℝ) - 1 + 10 * eps) /
        Real.rpow d (1 + eta) := by
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hd (1 + eta))]
    _ ≤ Real.rpow d (eta - 12 * eps) * d *
        Real.rpow d ((j : ℝ) - 1 + 10 * eps) /
          Real.rpow d (1 + eta) := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hd.le _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right habsorb hd.le)
        (Real.rpow_nonneg hd.le _)
    _ = Real.rpow d ((j : ℝ) - 1 - 2 * eps) := by
      have hd1 : d = Real.rpow d 1 := (Real.rpow_one d).symm
      nth_rewrite 2 [hd1]
      have hexp :
          eta - 12 * eps + 1 + ((j : ℝ) - 1 + 10 * eps) - (1 + eta) =
            (j : ℝ) - 1 - 2 * eps := by ring
      calc
        Real.rpow d (eta - 12 * eps) * Real.rpow d 1 *
              Real.rpow d ((j : ℝ) - 1 + 10 * eps) /
            Real.rpow d (1 + eta) =
          Real.rpow d (eta - 12 * eps + 1) *
              Real.rpow d ((j : ℝ) - 1 + 10 * eps) /
            Real.rpow d (1 + eta) := by
              apply congrArg (fun x => x *
                Real.rpow d ((j : ℝ) - 1 + 10 * eps) /
                  Real.rpow d (1 + eta))
              exact (Real.rpow_add hd _ _).symm
        _ = Real.rpow d
              (eta - 12 * eps + 1 + ((j : ℝ) - 1 + 10 * eps)) /
            Real.rpow d (1 + eta) := by
              apply congrArg (fun x => x / Real.rpow d (1 + eta))
              exact (Real.rpow_add hd _ _).symm
        _ = Real.rpow d
            (eta - 12 * eps + 1 + ((j : ℝ) - 1 + 10 * eps) -
              (1 + eta)) := (Real.rpow_sub hd _ _).symm
        _ = _ := by rw [hexp]
    _ = _ := rfl

/-- The symmetric-sum error is below the same `d^(j-1-2 eps)` room once
the host has at least `d^(1+eta)/32` edges. -/
theorem symmetricMass_absorbed_rawSource
    {j : ℕ} {d n eta Gamma total : ℝ}
    (hd : 0 < d) (hn : 0 < n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (htotal : n * Real.rpow d
      ((j : ℝ) - 1 - 2 * rawRegularizationEps eta) ≤ total)
    (hcoeff : 6144 * Gamma ^ 2 ≤
      Real.rpow d (1 + eta - 4 * rawRegularizationEps eta)) :
    12 * (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ 2 / total ≤
      Real.rpow d ((j : ℝ) - 1 - 2 * rawRegularizationEps eta) := by
  let eps := rawRegularizationEps eta
  have hLpos : 0 < Real.rpow d ((j : ℝ) - 1 - 2 * eps) :=
    Real.rpow_pos_of_pos hd _
  have htotalpos : 0 < total :=
    (mul_pos hn hLpos).trans_le htotal
  have hhost' : Real.rpow d (1 + eta) ≤ 32 * n := by nlinarith
  have hnum0 : 0 ≤ 12 * (4 * Gamma *
      Real.rpow d ((j : ℝ) - 1)) ^ 2 := by positivity
  calc
    12 * (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ 2 / total ≤
        12 * (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ 2 /
          (n * Real.rpow d ((j : ℝ) - 1 - 2 * eps)) := by
      exact div_le_div_of_nonneg_left hnum0 (mul_pos hn hLpos) htotal
    _ = 192 * Gamma ^ 2 *
        Real.rpow d ((j : ℝ) - 1 + 2 * eps) / n := by
      have hratio :
          Real.rpow d ((j : ℝ) - 1) ^ 2 /
              Real.rpow d ((j : ℝ) - 1 - 2 * eps) =
            Real.rpow d ((j : ℝ) - 1 + 2 * eps) := by
        have hsquare : Real.rpow d ((j : ℝ) - 1) ^ 2 =
            Real.rpow d (2 * ((j : ℝ) - 1)) := by
          calc
            _ = Real.rpow (Real.rpow d ((j : ℝ) - 1)) 2 :=
              (Real.rpow_natCast _ 2).symm
            _ = Real.rpow d (((j : ℝ) - 1) * 2) :=
              (Real.rpow_mul hd.le _ 2).symm
            _ = _ := by congr 1; ring
        rw [hsquare]
        calc
          _ = Real.rpow d
              (2 * ((j : ℝ) - 1) - ((j : ℝ) - 1 - 2 * eps)) :=
            (Real.rpow_sub hd _ _).symm
          _ = _ := by congr 1; ring
      calc
        12 * (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ 2 /
            (n * Real.rpow d ((j : ℝ) - 1 - 2 * eps)) =
          192 * Gamma ^ 2 *
            (Real.rpow d ((j : ℝ) - 1) ^ 2 /
              Real.rpow d ((j : ℝ) - 1 - 2 * eps)) / n := by ring
        _ = _ := by rw [hratio]
    _ ≤ 6144 * Gamma ^ 2 *
        Real.rpow d ((j : ℝ) - 1 + 2 * eps) /
          Real.rpow d (1 + eta) := by
      have hninv : 0 < n := hn
      have hdiv : 1 / n ≤ 32 / Real.rpow d (1 + eta) := by
        apply (div_le_div_iff₀ hn (Real.rpow_pos_of_pos hd _)).2
        simpa using hhost'
      have hnonneg : 0 ≤ 192 * Gamma ^ 2 *
          Real.rpow d ((j : ℝ) - 1 + 2 * eps) :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Gamma))
          (Real.rpow_nonneg hd.le _)
      calc
        _ = (192 * Gamma ^ 2 *
            Real.rpow d ((j : ℝ) - 1 + 2 * eps)) * (1 / n) := by ring
        _ ≤ (192 * Gamma ^ 2 *
            Real.rpow d ((j : ℝ) - 1 + 2 * eps)) *
              (32 / Real.rpow d (1 + eta)) :=
          mul_le_mul_of_nonneg_left hdiv hnonneg
        _ = _ := by ring
    _ ≤ Real.rpow d (1 + eta - 4 * eps) *
        Real.rpow d ((j : ℝ) - 1 + 2 * eps) /
          Real.rpow d (1 + eta) := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hd.le _)
      exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hd.le _)
    _ = Real.rpow d ((j : ℝ) - 1 - 2 * eps) := by
      calc
        _ = Real.rpow d
              ((1 + eta - 4 * eps) + ((j : ℝ) - 1 + 2 * eps)) /
            Real.rpow d (1 + eta) := by
              apply congrArg (fun x => x / Real.rpow d (1 + eta))
              exact (Real.rpow_add hd _ _).symm
        _ = Real.rpow d
            ((1 + eta - 4 * eps) + ((j : ℝ) - 1 + 2 * eps) -
              (1 + eta)) := (Real.rpow_sub hd _ _).symm
        _ = _ := by congr 1; ring
    _ = _ := rfl

theorem two_rawSourceMasses_fit_degreeRoom
    {j : ℕ} {d eta layerDelta : ℝ}
    (hd : 0 < d) (hcut :
      64 ≤ Real.rpow d (599 * rawRegularizationEps eta / 600)) :
    2 * Real.rpow d ((j : ℝ) - 1 - 2 * rawRegularizationEps eta) ≤
      Real.rpow d (-rawRegularizationEps eta) *
        completionTarget d (rawRegularizationEps eta) layerDelta j / 32 := by
  let eps := rawRegularizationEps eta
  let base := Real.rpow d ((j : ℝ) - 1 - eps / 600)
  have hbasepos : 0 < base := Real.rpow_pos_of_pos hd _
  have hfactor : 1 ≤ 1 + Real.rpow d (-eps / 4) :=
    le_add_of_nonneg_right (Real.rpow_nonneg hd.le _)
  have htarget : base ≤ completionTarget d eps layerDelta j := by
    rw [completionTarget]
    calc
      base ≤ max base layerDelta := le_max_left _ _
      _ ≤ (1 + Real.rpow d (-eps / 4)) * max base layerDelta := by
        have hmax0 : 0 ≤ max base layerDelta := hbasepos.le.trans (le_max_left _ _)
        nlinarith
  have hscale :
      64 * Real.rpow d ((j : ℝ) - 1 - 2 * eps) ≤
        Real.rpow d (-eps) * base := by
    calc
      _ ≤ Real.rpow d (599 * eps / 600) *
          Real.rpow d ((j : ℝ) - 1 - 2 * eps) :=
        mul_le_mul_of_nonneg_right hcut (Real.rpow_nonneg hd.le _)
      _ = Real.rpow d
          (599 * eps / 600 + ((j : ℝ) - 1 - 2 * eps)) :=
        (Real.rpow_add hd _ _).symm
      _ = Real.rpow d (-eps) * base := by
        change Real.rpow d
            (599 * eps / 600 + ((j : ℝ) - 1 - 2 * eps)) =
          Real.rpow d (-eps) *
            Real.rpow d ((j : ℝ) - 1 - eps / 600)
        calc
          _ = Real.rpow d (-eps + ((j : ℝ) - 1 - eps / 600)) := by
            congr 1
            ring
          _ = _ := Real.rpow_add hd _ _
  have htargetScaled : Real.rpow d (-eps) * base ≤
      Real.rpow d (-eps) * completionTarget d eps layerDelta j :=
    mul_le_mul_of_nonneg_left htarget (Real.rpow_nonneg hd.le _)
  change 2 * Real.rpow d ((j : ℝ) - 1 - 2 * eps) ≤
    Real.rpow d (-eps) * completionTarget d eps layerDelta j / 32
  nlinarith [hscale.trans htargetScaled]

/-- The source symmetric error plus all forbidden completions fit one
quarter of the relative Property-I corridor. -/
theorem rawSource_propertyI_degreeRoom
    {j : ℕ} (hj2 : 2 ≤ j)
    {d n eta Gamma A B total layerDelta K pmax : ℝ} {m : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hK : 0 ≤ K) (hpmax0 : 0 ≤ pmax)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (htotal : n * Real.rpow d
      ((j : ℝ) - 1 - 2 * rawRegularizationEps eta) ≤ total)
    (hcard : (m : ℝ) ≤ K * d * n ^ (j - 2))
    (hpmax : pmax ≤ rawSourcePmax d eta n j)
    (hcut : RawSourceCutoffSpec eta Gamma A B d)
    (hKabsorb : 32 * K ≤
      Real.rpow d (eta - 12 * rawRegularizationEps eta)) :
    12 * (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ 2 / total +
        (m : ℝ) * pmax ≤
      Real.rpow d (-rawRegularizationEps eta) *
        completionTarget d (rawRegularizationEps eta) layerDelta j / 32 := by
  have hsym := symmetricMass_absorbed_rawSource
    (j := j) hd hn hhost htotal hcut.symmetricRoom
  have hforbidden := forbiddenMass_absorbed_rawSource hj2 hd hK hpmax0
    hcard hpmax hhost hKabsorb
  have hfit := two_rawSourceMasses_fit_degreeRoom
    (j := j) (layerDelta := layerDelta) hd hcut.finalDegreeRoom
  linarith

theorem rawSource_propertyI_degreeRoom_of_stageCoeff
    {j : ℕ} (hj : j ∈ ({2, 3, 4} : Finset ℕ))
    {d n eta Gamma A B total layerDelta pmax : ℝ} {m : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpmax0 : 0 ≤ pmax)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (htotal : n * Real.rpow d
      ((j : ℝ) - 1 - 2 * rawRegularizationEps eta) ≤ total)
    (hcard : (m : ℝ) ≤ rawForbiddenCoeff A B j * d * n ^ (j - 2))
    (hpmax : pmax ≤ rawSourcePmax d eta n j)
    (hcut : RawSourceCutoffSpec eta Gamma A B d) :
    12 * (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ 2 / total +
        (m : ℝ) * pmax ≤
      Real.rpow d (-rawRegularizationEps eta) *
        completionTarget d (rawRegularizationEps eta) layerDelta j / 32 := by
  have hj2 : 2 ≤ j := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> norm_num
  have hK : 0 ≤ rawForbiddenCoeff A B j := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;>
      simp [rawForbiddenCoeff] <;> positivity
  have hKabsorb : 32 * rawForbiddenCoeff A B j ≤
      Real.rpow d (eta - 12 * rawRegularizationEps eta) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact hcut.forbiddenTwo
    · exact hcut.forbiddenThree
    · exact hcut.forbiddenFour
  exact rawSource_propertyI_degreeRoom hj2 hd hn hK hpmax0 hhost htotal
    hcard hpmax hcut hKabsorb


end
end Erdos136.CFMRegularization

namespace Erdos136.CFMRegularization

open scoped BigOperators

variable {V : Type*} [DecidableEq V] [Fintype V]

attribute [local instance] Classical.propDecidable

noncomputable section

theorem scratch_layerMaxDegree_le_of_normalizedDegreeSum
    (H : Hypergraph V) (C : ConflictSystem V)
    {d Gamma : ℝ} {r : ℕ}
    (hd : 0 < d) (hr2 : 2 ≤ r) (hr4 : r ≤ 4)
    (hsum : (∑ q ∈ Finset.Icc 2 4,
      (layerMaxDegree H C q : ℝ) / Real.rpow d ((q : ℝ) - 1)) ≤ Gamma) :
    (layerMaxDegree H C r : ℝ) ≤
      Gamma * Real.rpow d ((r : ℝ) - 1) := by
  have hr : r ∈ Finset.Icc 2 4 := Finset.mem_Icc.mpr ⟨hr2, hr4⟩
  have hterm :
      (layerMaxDegree H C r : ℝ) / Real.rpow d ((r : ℝ) - 1) ≤
        ∑ q ∈ Finset.Icc 2 4,
          (layerMaxDegree H C q : ℝ) / Real.rpow d ((q : ℝ) - 1) := by
    apply Finset.single_le_sum (fun q _ => ?_) hr
    exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hd.le _)
  have hden : 0 < Real.rpow d ((r : ℝ) - 1) :=
    Real.rpow_pos_of_pos hd _
  rw [div_le_iff₀ hden] at hterm
  exact hterm.trans (by
    have := mul_le_mul_of_nonneg_right hsum hden.le
    simpa [mul_comm] using this)

theorem scratch_commonLink_upper_of_not_mem_minimalBadCore
    (H : Hypergraph V) (C : ConflictSystem V)
    {d etaBad : ℝ}
    (hHuniform : IsUniform H 8)
    (hCcard : ∀ c ∈ C, c.card = 4)
    (hd : 0 ≤ d)
    (e f : Finset V) (he : e ∈ H) (hf : f ∈ H)
    (hdisj : Disjoint e f)
    (hnot : {e, f} ∉ conflictLayer
      (minimalMatchingCore H
        (C ∪ badPairConflicts H C (trackableCutoff d etaBad))) 2)
    (s : Fin 3) :
    (((conflictLinkLayer C e (s.1 + 1)) ∩
      conflictLinkLayer C f (s.1 + 1)).card : ℝ) ≤
        Real.rpow d ((s.1 + 1 : ℕ) - etaBad) := by
  have hef : e ≠ f := by
    intro hef
    subst f
    have he0 : e = ∅ := disjoint_self.mp hdisj
    have hecard := hHuniform e he
    rw [he0] at hecard
    simp at hecard
  by_contra hn
  have hlarge : Real.rpow d ((s.1 + 1 : ℕ) - etaBad) <
      (((conflictLinkLayer C e (s.1 + 1)) ∩
        conflictLinkLayer C f (s.1 + 1)).card : ℕ) := lt_of_not_ge hn
  have hfloor : trackableCutoff d etaBad s <
      ((conflictLinkLayer C e (s.1 + 1)) ∩
        conflictLinkLayer C f (s.1 + 1)).card := by
    rw [trackableCutoff]
    exact (Nat.floor_lt (Real.rpow_nonneg hd _)).2 hlarge
  let B := badPairConflicts H C (trackableCutoff d etaBad)
  have hpairB : {e, f} ∈ B := by
    rw [mem_badPairConflicts]
    refine ⟨?_, Finset.card_pair hef, e, by simp,
      f, by simp, he, hf, hef, hdisj, s, hfloor⟩
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact he
    · exact hf
  have hpairMatch : IsMatching H {e, f} := by
    rw [isMatching_insert_iff]
    refine ⟨he, isMatching_singleton_iff.mpr hf, ?_⟩
    intro g hg _hge
    have : g = f := by simpa using hg
    subst g
    exact hdisj
  have hpairCore : {e, f} ∈ minimalMatchingCore H (C ∪ B) := by
    rw [mem_minimalMatchingCore]
    refine ⟨Finset.mem_union_right _ hpairB, hpairMatch, ?_⟩
    rintro ⟨c, hc, _hcmatch, hcstrict⟩
    have hcardlt := Finset.card_lt_card hcstrict
    have hpaircard : (({e, f} : Finset (Finset V))).card = 2 :=
      Finset.card_pair hef
    rw [hpaircard] at hcardlt
    rcases Finset.mem_union.mp hc with hcC | hcB
    · have hc4 := hCcard c hcC
      omega
    · have hc2 := badPairConflicts_uniform_two H C _ c hcB
      omega
  apply hnot
  exact Finset.mem_filter.mpr ⟨hpairCore, Finset.card_pair hef⟩

end
end Erdos136.CFMRegularization


namespace Erdos136.CFMRegularization

open Finset Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V : Type*} [DecidableEq V]

/-! A small finite registry for the numerical estimates not present in the
raw regularization cutoff.  `K` is a uniform constant in the source-bias
bound `pmax <= K d^(-eta+6 eps)`. -/

inductive RawTransferRequirement
  | regularizationTiny
  | testInfluence
  | sourceCoefficient
  deriving DecidableEq

def rawTransferRegistry (eta K : ℝ) (heta : 0 < eta) :
    LargeDRegistry RawTransferRequirement where
  active := { .regularizationTiny, .testInfluence, .sourceCoefficient }
  condition r d := match r with
    | .regularizationTiny =>
        Real.rpow d (-rawRegularizationEps eta / 600) ≤ 1 / 4
    | .testInfluence =>
        64 * d ≤ Real.rpow d (2 + rawRegularizationEps eta / 5)
    | .sourceCoefficient =>
        2 * K ≤ Real.rpow d (eta - 12 * rawRegularizationEps eta)
  eventually_condition := by
    intro r _hr
    cases r with
    | regularizationTiny =>
        have h := eventually_const_mul_rpow_le_rpow_real 4
          (-rawRegularizationEps eta / 600) 0 (by
            simp only [rawRegularizationEps]
            linarith)
        filter_upwards [h] with d hd
        have hd' : 4 * Real.rpow d (-rawRegularizationEps eta / 600) ≤ 1 := by
          rw [show Real.rpow d 0 = 1 from Real.rpow_zero d] at hd
          exact hd
        nlinarith
    | testInfluence =>
        have h := eventually_const_mul_rpow_le_rpow_real 64 1
            (2 + rawRegularizationEps eta / 5) (by
              simp only [rawRegularizationEps]
              linarith)
        filter_upwards [h] with d hd
        rw [show Real.rpow d 1 = d from Real.rpow_one d] at hd
        exact hd
    | sourceCoefficient =>
        exact eventually_const_le_rpow_real (2 * K)
          (eta - 12 * rawRegularizationEps eta) (by
            simp only [rawRegularizationEps]
            linarith)

structure RawTransferCutoffSpec (eta K d : ℝ) : Prop where
  regularizationTiny :
    Real.rpow d (-rawRegularizationEps eta / 600) ≤ 1 / 4
  testInfluence :
    64 * d ≤ Real.rpow d (2 + rawRegularizationEps eta / 5)
  sourceCoefficient :
    2 * K ≤ Real.rpow d (eta - 12 * rawRegularizationEps eta)

theorem exists_rawTransferCutoff (eta K : ℝ) (heta : 0 < eta) :
    ∃ d0 : ℝ, ∀ d, d0 ≤ d → RawTransferCutoffSpec eta K d := by
  let R := rawTransferRegistry eta K heta
  obtain ⟨d0, hd0⟩ := R.exists_cutoff
  refine ⟨d0, fun d hd => ?_⟩
  have hreq (r : RawTransferRequirement) : R.condition r d := by
    exact hd0 d hd r (by cases r <;> simp [R, rawTransferRegistry])
  exact ⟨by simpa [R, rawTransferRegistry] using hreq .regularizationTiny,
    by simpa [R, rawTransferRegistry] using hreq .testInfluence,
    by simpa [R, rawTransferRegistry] using hreq .sourceCoefficient⟩

theorem RawTransferCutoffSpec.testInfluence_stage
    {eta K d : ℝ} (h : RawTransferCutoffSpec eta K d)
    (hd : 1 ≤ d) {stage : ℕ} (hstage : 2 ≤ stage) :
    64 * d ≤ Real.rpow d ((stage : ℝ) + rawRegularizationEps eta / 5) := by
  exact h.testInfluence.trans
    (Real.rpow_le_rpow_of_exponent_le hd (by
      have : (2 : ℝ) ≤ (stage : ℝ) := by exact_mod_cast hstage
      linarith))

theorem RawTransferCutoffSpec.sourceKilledCoefficient
    {eta K d pmax : ℝ} {stage : ℕ}
    (h : RawTransferCutoffSpec eta K d) (hd : 0 < d)
    (hstage : 2 ≤ stage) (hpmax0 : 0 ≤ pmax)
    (hpmax : pmax ≤ K * Real.rpow d (-eta + 10 * rawRegularizationEps eta)) :
    16 * pmax ≤ (4 : ℝ) ^ stage /
      (2 * Real.rpow d (2 * rawRegularizationEps eta)) := by
  have hpowpos : 0 < Real.rpow d (2 * rawRegularizationEps eta) :=
    Real.rpow_pos_of_pos hd _
  have hKpow :
      2 * (K * Real.rpow d (-eta + 10 * rawRegularizationEps eta)) ≤
        1 / Real.rpow d (2 * rawRegularizationEps eta) := by
    apply (le_div_iff₀ hpowpos).2
    calc
      2 * (K * Real.rpow d (-eta + 10 * rawRegularizationEps eta)) *
          Real.rpow d (2 * rawRegularizationEps eta) =
          (2 * K) * (Real.rpow d (-eta + 10 * rawRegularizationEps eta) *
            Real.rpow d (2 * rawRegularizationEps eta)) := by ring
      _ = (2 * K) * Real.rpow d
            ((-eta + 10 * rawRegularizationEps eta) +
              2 * rawRegularizationEps eta) := by
            congr 1
            exact (Real.rpow_add hd _ _).symm
      _ = (2 * K) * Real.rpow d
            (-eta + 12 * rawRegularizationEps eta) := by ring
      _ ≤ Real.rpow d (eta - 12 * rawRegularizationEps eta) *
          Real.rpow d (-eta + 12 * rawRegularizationEps eta) := by
            apply mul_le_mul_of_nonneg_right h.sourceCoefficient
            exact Real.rpow_nonneg hd.le _
      _ = 1 := by
            calc
              Real.rpow d (eta - 12 * rawRegularizationEps eta) *
                  Real.rpow d (-eta + 12 * rawRegularizationEps eta) =
                  Real.rpow d ((eta - 12 * rawRegularizationEps eta) +
                    (-eta + 12 * rawRegularizationEps eta)) :=
                    (Real.rpow_add hd _ _).symm
              _ = Real.rpow d 0 := by congr 1 <;> ring
              _ = 1 := Real.rpow_zero d
  have hp : 2 * pmax ≤ 1 / Real.rpow d (2 * rawRegularizationEps eta) :=
    (mul_le_mul_of_nonneg_left hpmax (by norm_num)).trans hKpow
  have hfour : (16 : ℝ) ≤ (4 : ℝ) ^ stage := by
    calc
      (16 : ℝ) = (4 : ℝ) ^ 2 := by norm_num
      _ ≤ (4 : ℝ) ^ stage := pow_le_pow_right₀ (by norm_num) hstage
  calc
    16 * pmax = 8 * (2 * pmax) := by ring
    _ ≤ 8 * (1 / Real.rpow d (2 * rawRegularizationEps eta)) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 16 / (2 * Real.rpow d (2 * rawRegularizationEps eta)) := by ring
    _ ≤ (4 : ℝ) ^ stage /
        (2 * Real.rpow d (2 * rawRegularizationEps eta)) := by
      exact div_le_div_of_nonneg_right hfour (by positivity)

theorem RawTransferCutoffSpec.regularizationScales
    {eta K d : ℝ} (h : RawTransferCutoffSpec eta K d)
    (heta : 0 < eta) (hd : 1 ≤ d) :
    Real.rpow d (-rawRegularizationEps eta) ≤ 1 / 4 ∧
      Real.rpow d (-rawRegularizationEps eta / 4) ≤ 1 / 4 ∧
      Real.rpow d (rawRegularizationEps eta / 5 - eta) ≤ 1 / 4 := by
  have hmono (a : ℝ)
      (ha : a ≤ -rawRegularizationEps eta / 600) :
      Real.rpow d a ≤ 1 / 4 :=
    (Real.rpow_le_rpow_of_exponent_le hd ha).trans h.regularizationTiny
  refine ⟨hmono _ ?_, hmono _ ?_, hmono _ ?_⟩ <;>
    simp only [rawRegularizationEps] <;> linarith

theorem RawTransferCutoffSpec.transferScalar
    {eta K d : ℝ} (h : RawTransferCutoffSpec eta K d)
    (heta : 0 < eta) (hd : 1 ≤ d) :
    Real.rpow d (rawRegularizationEps eta / 5 - eta) +
        Real.rpow d (-rawRegularizationEps eta) ≤ 1 := by
  obtain ⟨hq, _ht, hg⟩ := h.regularizationScales heta hd
  linarith

theorem RawTransferCutoffSpec.finalDegreeSumGap
    {eta K d Gamma : ℝ} (h : RawTransferCutoffSpec eta K d)
    (heta : 0 < eta) (hd : 1 ≤ d) (hGamma : 1 ≤ Gamma) :
    (1 + Real.rpow d (-rawRegularizationEps eta)) *
        (1 + Real.rpow d (-rawRegularizationEps eta / 4)) *
        (Gamma + 3 * Real.rpow d (-rawRegularizationEps eta / 600)) ≤
      3 * Gamma := by
  obtain ⟨hq, ht, _hg⟩ := h.regularizationScales heta hd
  have hs := h.regularizationTiny
  have hq0 : 0 ≤ Real.rpow d (-rawRegularizationEps eta) :=
    Real.rpow_nonneg (by linarith) _
  have ht0 : 0 ≤ Real.rpow d (-rawRegularizationEps eta / 4) :=
    Real.rpow_nonneg (by linarith) _
  have hs0 : 0 ≤ Real.rpow d (-rawRegularizationEps eta / 600) :=
    Real.rpow_nonneg (by linarith) _
  calc
    (1 + Real.rpow d (-rawRegularizationEps eta)) *
        (1 + Real.rpow d (-rawRegularizationEps eta / 4)) *
        (Gamma + 3 * Real.rpow d (-rawRegularizationEps eta / 600)) ≤
      (5 / 4 : ℝ) * (5 / 4 : ℝ) * (Gamma + 3 / 4) := by
        apply mul_le_mul
        · apply mul_le_mul <;> nlinarith
        · nlinarith
        · positivity
        · positivity
    _ ≤ 3 * Gamma := by nlinarith

theorem transfer_W1_scale
    {d eta eps T T' : ℝ} {j : ℕ}
    (hd : 0 < d) (hT0 : 0 ≤ T)
    (hT : Real.rpow d ((j : ℝ) + eta) ≤ T)
    (hT' : (1 - Real.rpow d (-eps)) * T ≤ T')
    (hscalar : Real.rpow d (eps / 5 - eta) +
      Real.rpow d (-eps) ≤ 1) :
    Real.rpow d ((j : ℝ) + eps / 5) ≤ T' := by
  have hfactor : Real.rpow d (eps / 5 - eta) ≤
      1 - Real.rpow d (-eps) := by linarith
  have hone : 0 ≤ 1 - Real.rpow d (-eps) :=
    (Real.rpow_nonneg hd.le _).trans hfactor
  calc
    Real.rpow d ((j : ℝ) + eps / 5) =
        Real.rpow d ((j : ℝ) + eta) *
          Real.rpow d (eps / 5 - eta) := by
      calc
        Real.rpow d ((j : ℝ) + eps / 5) =
            Real.rpow d (((j : ℝ) + eta) + (eps / 5 - eta)) := by
              congr 1 <;> ring
        _ = _ := Real.rpow_add hd _ _
    _ ≤ Real.rpow d ((j : ℝ) + eta) *
        (1 - Real.rpow d (-eps)) :=
      mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hd.le _)
    _ ≤ T * (1 - Real.rpow d (-eps)) :=
      mul_le_mul_of_nonneg_right hT hone
    _ ≤ T' := by simpa [mul_comm] using hT'

theorem transfer_W2_scale
    {d eta eps T T' : ℝ} {j' : ℕ}
    (hd : 0 < d) (hT0 : 0 ≤ T)
    (hT' : (1 - Real.rpow d (-eps)) * T ≤ T')
    (hscalar : Real.rpow d (eps / 5 - eta) +
      Real.rpow d (-eps) ≤ 1) :
    T / Real.rpow d ((j' : ℝ) + eta) ≤
      T' / Real.rpow d ((j' : ℝ) + eps / 5) := by
  have hfactor : Real.rpow d (eps / 5 - eta) ≤
      1 - Real.rpow d (-eps) := by linarith
  have hone : 0 ≤ 1 - Real.rpow d (-eps) :=
    (Real.rpow_nonneg hd.le _).trans hfactor
  have ha : 0 < Real.rpow d ((j' : ℝ) + eta) :=
    Real.rpow_pos_of_pos hd _
  have hb : 0 < Real.rpow d ((j' : ℝ) + eps / 5) :=
    Real.rpow_pos_of_pos hd _
  rw [div_le_div_iff₀ ha hb]
  have hden : Real.rpow d ((j' : ℝ) + eps / 5) =
      Real.rpow d ((j' : ℝ) + eta) *
        Real.rpow d (eps / 5 - eta) := by
    calc
      Real.rpow d ((j' : ℝ) + eps / 5) =
          Real.rpow d (((j' : ℝ) + eta) + (eps / 5 - eta)) := by
            congr 1 <;> ring
      _ = _ := Real.rpow_add hd _ _
  rw [hden]
  calc
    T * (Real.rpow d ((j' : ℝ) + eta) *
        Real.rpow d (eps / 5 - eta)) =
      (T * Real.rpow d (eps / 5 - eta)) *
        Real.rpow d ((j' : ℝ) + eta) := by ring
    _ ≤ (T * (1 - Real.rpow d (-eps))) *
        Real.rpow d ((j' : ℝ) + eta) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hfactor hT0
      · exact Real.rpow_nonneg hd.le _
    _ ≤ T' * Real.rpow d ((j' : ℝ) + eta) := by
      apply mul_le_mul_of_nonneg_right
      · simpa [mul_comm] using hT'
      · exact Real.rpow_nonneg hd.le _

theorem restrictWeight_W1_W2_of_killedWeight
    {H : Hypergraph V} {C D : ConflictSystem V} {j ell : ℕ}
    {d eta eps : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C j ell d eta w) (hd : 0 < d)
    (hscalar : Real.rpow d (eps / 5 - eta) +
      Real.rpow d (-eps) ≤ 1)
    (hkill : killedWeight H D j w ≤
      testTotal w H j / Real.rpow d eps) :
    Real.rpow d ((j : ℝ) + eps / 5) ≤
        testTotal (restrictWeight D w) H j ∧
      ∀ j', 1 ≤ j' → j' < j →
        testTotal w H j / Real.rpow d ((j' : ℝ) + eta) ≤
          testTotal (restrictWeight D w) H j /
            Real.rpow d ((j' : ℝ) + eps / 5) := by
  let T := testTotal w H j
  let T' := testTotal (restrictWeight D w) H j
  have hT0 : 0 ≤ T := testTotal_nonneg hw.1.1 H j
  have heq : T' + killedWeight H D j w = T := by
    exact testTotal_restrictWeight_add_killedWeight H D j w hw.1.1
  have hdiv : T / Real.rpow d eps = T * Real.rpow d (-eps) := by
    rw [div_eq_mul_inv]
    congr 1
    exact (Real.rpow_neg hd.le eps).symm
  have hT' : (1 - Real.rpow d (-eps)) * T ≤ T' := by
    rw [hdiv] at hkill
    dsimp [T, T'] at heq hkill ⊢
    nlinarith
  refine ⟨transfer_W1_scale hd hT0 hw.2.1 hT' hscalar, ?_⟩
  intro j' _hj' _hj'j
  exact transfer_W2_scale hd hT0 hT' hscalar

theorem RawTransferCutoffSpec.restrictWeight_W1_W2
    {H : Hypergraph V} {C D : ConflictSystem V} {j ell : ℕ}
    {eta K d : ℝ} {w : TestWeight V}
    (h : RawTransferCutoffSpec eta K d) (heta : 0 < eta) (hd : 1 ≤ d)
    (hw : IsTrackable H C j ell d eta w)
    (hkill : killedWeight H D j w ≤
      testTotal w H j / Real.rpow d (rawRegularizationEps eta)) :
    Real.rpow d ((j : ℝ) + rawRegularizationEps eta / 5) ≤
        testTotal (restrictWeight D w) H j ∧
      ∀ j', 1 ≤ j' → j' < j →
        testTotal w H j / Real.rpow d ((j' : ℝ) + eta) ≤
          testTotal (restrictWeight D w) H j /
            Real.rpow d ((j' : ℝ) + rawRegularizationEps eta / 5) := by
  exact restrictWeight_W1_W2_of_killedWeight hw (zero_lt_one.trans_le hd)
    (h.transferScalar heta hd) hkill

theorem minimalBadCore_normalizedDegreeSum_le
    (H : Hypergraph V) (C B : ConflictSystem V)
    {d etaRaw etaBad : ℝ} {ell : ℕ}
    (hC : IsBounded C d ell etaRaw)
    (hB : IsUniform B 2) (hell : 4 ≤ ell) (hd : 0 < d)
    (hBdegree : ∀ e ∈ H,
      (degree B e : ℝ) ≤ Real.rpow d (1 - etaBad)) :
    (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H (minimalMatchingCore H (C ∪ B)) r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤
      2 * (ell : ℝ) + Real.rpow d (-etaBad) := by
  let C0 := minimalMatchingCore H (C ∪ B)
  have h2 : (layerMaxDegree H C0 2 : ℝ) ≤
      Real.rpow d (1 - etaBad) := by
    have hfloor : layerMaxDegree H C0 2 ≤
        Nat.floor (Real.rpow d (1 - etaBad)) := by
      unfold layerMaxDegree
      apply Finset.sup_le
      intro e he
      apply Nat.le_floor
      calc
        (degree (conflictLayer C0 2) e : ℝ) ≤
            degree (conflictLayer B 2) e := by
          exact_mod_cast degree_mono
            (minimalCore_union_layer_two_subset_right H hC) e
        _ = degree B e := by rw [conflictLayer_eq_self_of_uniform hB]
        _ ≤ Real.rpow d (1 - etaBad) := hBdegree e he
    exact (by exact_mod_cast hfloor :
        (layerMaxDegree H C0 2 : ℝ) ≤
          (Nat.floor (Real.rpow d (1 - etaBad)) : ℕ)) |>.trans
      (Nat.floor_le (Real.rpow_nonneg hd.le _))
  have hge : ∀ r, 3 ≤ r → r ≤ ell →
      (layerMaxDegree H C0 r : ℝ) ≤
        (ell : ℝ) * Real.rpow d ((r : ℝ) - 1) := by
    intro r hr3 hrell
    let D := (ell : ℝ) * Real.rpow d ((r : ℝ) - 1)
    have hD0 : 0 ≤ D :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hd.le _)
    have hlayer : conflictLayer C0 r ⊆ conflictLayer C r := by
      intro c hc
      have hc' := Finset.mem_filter.mp hc
      have hcU := (mem_minimalMatchingCore.mp hc'.1).1
      apply Finset.mem_filter.mpr
      refine ⟨?_, hc'.2⟩
      rcases Finset.mem_union.mp hcU with hcC | hcB'
      · exact hcC
      · have hcard2 := hB c hcB'
        have hcardr := hc'.2
        omega
    have hfloor : layerMaxDegree H C0 r ≤ Nat.floor D := by
      unfold layerMaxDegree
      apply Finset.sup_le
      intro e he
      apply Nat.le_floor
      calc
        (degree (conflictLayer C0 r) e : ℝ) ≤
            degree (conflictLayer C r) e := by
          exact_mod_cast degree_mono hlayer e
        _ ≤ D := by
          dsimp [D]
          exact hC.2.1 r hr3 hrell e
    exact (by exact_mod_cast hfloor :
        (layerMaxDegree H C0 r : ℝ) ≤ (Nat.floor D : ℕ)) |>.trans
      (Nat.floor_le hD0)
  have hn2 : (layerMaxDegree H C0 2 : ℝ) / Real.rpow d 1 ≤
      Real.rpow d (-etaBad) := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hd 1)).2
    calc
      (layerMaxDegree H C0 2 : ℝ) ≤ Real.rpow d (1 - etaBad) := h2
      _ = Real.rpow d (-etaBad) * Real.rpow d 1 := by
        calc
          Real.rpow d (1 - etaBad) = Real.rpow d (-etaBad + 1) := by
            congr 1 <;> ring
          _ = _ := Real.rpow_add hd _ _
  have hn3 : (layerMaxDegree H C0 3 : ℝ) / Real.rpow d 2 ≤
      (ell : ℝ) := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hd 2)).2
    have hg := hge 3 (by norm_num) (by omega)
    have hexp : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
    rw [hexp] at hg
    exact hg
  have hn4 : (layerMaxDegree H C0 4 : ℝ) / Real.rpow d 3 ≤
      (ell : ℝ) := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hd 3)).2
    have hg := hge 4 (by norm_num) hell
    have hexp : ((4 : ℕ) : ℝ) - 1 = 3 := by norm_num
    rw [hexp] at hg
    exact hg
  norm_num [Finset.sum_Icc_succ_top, C0] at hn2 hn3 hn4 ⊢
  linarith

theorem minimalBadCore_normalizedDegreeSum_le_Gamma
    (H : Hypergraph V) (C B : ConflictSystem V)
    {d etaRaw etaBad Gamma : ℝ} {ell : ℕ}
    (hC : IsBounded C d ell etaRaw) (hB : IsUniform B 2)
    (hell : 4 ≤ ell) (hd : 1 ≤ d) (hetaBad : 0 ≤ etaBad)
    (hBdegree : ∀ e ∈ H,
      (degree B e : ℝ) ≤ Real.rpow d (1 - etaBad))
    (hGamma : 2 * (ell : ℝ) + 1 ≤ Gamma) :
    (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H (minimalMatchingCore H (C ∪ B)) r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤ Gamma := by
  have hraw := minimalBadCore_normalizedDegreeSum_le H C B hC hB hell
    (zero_lt_one.trans_le hd) hBdegree
  have hpow : Real.rpow d (-etaBad) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hd (by linarith)
  linarith

theorem threeStageKilledWeightLimits_eq
    (d eps X : ℝ) (hd : 0 < d) :
    (4 : ℝ) ^ 2 * X / Real.rpow d (2 * eps) +
        (4 : ℝ) ^ 3 * X / Real.rpow d (2 * eps) +
        (4 : ℝ) ^ 4 * X / Real.rpow d (2 * eps) =
      336 * (X * Real.rpow d (-2 * eps)) := by
  norm_num
  have hneg : Real.rpow d (-(2 * eps)) =
      (Real.rpow d (2 * eps))⁻¹ := Real.rpow_neg hd.le (2 * eps)
  calc
    16 * X / Real.rpow d (2 * eps) +
        64 * X / Real.rpow d (2 * eps) +
        256 * X / Real.rpow d (2 * eps) =
      336 * (X * (Real.rpow d (2 * eps))⁻¹) := by
        simp only [div_eq_mul_inv]
        ring
    _ = 336 * (X * Real.rpow d (-(2 * eps))) :=
      congrArg (fun z : ℝ => 336 * (X * z)) hneg.symm

theorem RawRegularizationCutoffSpec.threeStageKilledWeightLimits
    {ell : ℕ} {eta d X : ℝ}
    (h : RawRegularizationCutoffSpec ell eta d) (hX : 0 ≤ X) :
    (4 : ℝ) ^ 2 * X /
          Real.rpow d (2 * rawRegularizationEps eta) +
        (4 : ℝ) ^ 3 * X /
          Real.rpow d (2 * rawRegularizationEps eta) +
        (4 : ℝ) ^ 4 * X /
          Real.rpow d (2 * rawRegularizationEps eta) ≤
      X / Real.rpow d (rawRegularizationEps eta) := by
  have hd : 0 < d := zero_lt_two.trans_le h.degreeAtLeastTwo
  rw [threeStageKilledWeightLimits_eq d (rawRegularizationEps eta) X hd]
  have hloss := h.threeStageLoss hX
  have hneg : Real.rpow d (-rawRegularizationEps eta) =
      (Real.rpow d (rawRegularizationEps eta))⁻¹ :=
    Real.rpow_neg hd.le (rawRegularizationEps eta)
  rw [hneg] at hloss
  simpa only [div_eq_mul_inv] using hloss

theorem threeStage_normalizedDegreeSum_le
    {H : Hypergraph V} {base final : ConflictSystem V}
    {d eps Gamma : ℝ}
    (h : ThreeStageProperties H base final d eps)
    (hd : 0 < d) (hGamma : 0 ≤ Gamma)
    (hbase :
      (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H base r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤ Gamma)
    (hgap :
      (1 + Real.rpow d (-eps)) *
          (1 + Real.rpow d (-eps / 4)) *
          (Gamma + 3 * Real.rpow d (-eps / 600)) ≤ 3 * Gamma) :
    (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H final r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤ 3 * Gamma := by
  let F := (1 + Real.rpow d (-eps)) *
    (1 + Real.rpow d (-eps / 4))
  let s := Real.rpow d (-eps / 600)
  have hF0 : 0 ≤ F := by
    dsimp [F]
    positivity
  have hrow : ∀ r ∈ Finset.Icc 2 4,
      (layerMaxDegree H final r : ℝ) /
          Real.rpow d ((r : ℝ) - 1) ≤
        F * (s + (layerMaxDegree H base r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) := by
    intro r hri
    have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hri).1
    have hr4 : r ≤ 4 := (Finset.mem_Icc.mp hri).2
    let A := Real.rpow d ((r : ℝ) - 1 - eps / 600)
    let B := (layerMaxDegree H base r : ℝ)
    let target := completionTarget d eps B r
    let D := (1 + Real.rpow d (-eps)) * target
    have hA0 : 0 ≤ A := Real.rpow_nonneg hd.le _
    have hB0 : 0 ≤ B := Nat.cast_nonneg _
    have ht0 : 0 ≤ Real.rpow d (-eps / 4) := Real.rpow_nonneg hd.le _
    have htarget0 : 0 ≤ target := by
      dsimp [target, completionTarget]
      exact mul_nonneg (by positivity) (hA0.trans (le_max_left A B))
    have hD0 : 0 ≤ D := by
      dsimp [D]
      positivity
    have hdegree : ∀ e ∈ H,
        (degree (conflictLayer final r) e : ℝ) ≤ D := by
      intro e he
      exact (h.layerDegree r hr2 hr4 e he).2
    have hfloor : layerMaxDegree H final r ≤ Nat.floor D := by
      unfold layerMaxDegree
      apply Finset.sup_le
      intro e he
      exact Nat.le_floor (hdegree e he)
    have hlayer : (layerMaxDegree H final r : ℝ) ≤ D :=
      (by exact_mod_cast hfloor :
          (layerMaxDegree H final r : ℝ) ≤ (Nat.floor D : ℕ)) |>.trans
        (Nat.floor_le hD0)
    have hden : 0 < Real.rpow d ((r : ℝ) - 1) :=
      Real.rpow_pos_of_pos hd _
    have hmax : max A B ≤ A + B :=
      max_le (le_add_of_nonneg_right hB0) (le_add_of_nonneg_left hA0)
    have hquotA : A / Real.rpow d ((r : ℝ) - 1) = s := by
      dsimp [A, s]
      calc
        Real.rpow d ((r : ℝ) - 1 - eps / 600) /
            Real.rpow d ((r : ℝ) - 1) =
          Real.rpow d (((r : ℝ) - 1 - eps / 600) - ((r : ℝ) - 1)) :=
            (Real.rpow_sub hd _ _).symm
        _ = Real.rpow d (-eps / 600) := by congr 1 <;> ring
    calc
      (layerMaxDegree H final r : ℝ) /
          Real.rpow d ((r : ℝ) - 1) ≤ D /
          Real.rpow d ((r : ℝ) - 1) :=
        div_le_div_of_nonneg_right hlayer hden.le
      _ = F * (max A B / Real.rpow d ((r : ℝ) - 1)) := by
        dsimp [D, target, F, completionTarget, A, B]
        ring
      _ ≤ F * ((A + B) / Real.rpow d ((r : ℝ) - 1)) := by
        apply mul_le_mul_of_nonneg_left _ hF0
        exact div_le_div_of_nonneg_right hmax hden.le
      _ = F * (s + B / Real.rpow d ((r : ℝ) - 1)) := by
        rw [add_div, hquotA]
  calc
    (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H final r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤
      ∑ r ∈ Finset.Icc 2 4,
        F * (s + (layerMaxDegree H base r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) :=
        Finset.sum_le_sum fun r hri => hrow r hri
    _ = F * (3 * s +
        ∑ r ∈ Finset.Icc 2 4,
          (layerMaxDegree H base r : ℝ) /
            Real.rpow d ((r : ℝ) - 1)) := by
      norm_num [Finset.sum_Icc_succ_top]
      ring
    _ ≤ F * (Gamma + 3 * s) := by
      apply mul_le_mul_of_nonneg_left _ hF0
      linarith
    _ ≤ 3 * Gamma := by simpa [F, s, add_comm] using hgap

theorem RawTransferCutoffSpec.threeStage_normalizedDegreeSum
    {H : Hypergraph V} {base final : ConflictSystem V}
    {eta K d Gamma : ℝ}
    (hc : RawTransferCutoffSpec eta K d)
    (heta : 0 < eta) (hd : 1 ≤ d) (hGamma : 1 ≤ Gamma)
    (h : ThreeStageProperties H base final d (rawRegularizationEps eta))
    (hbase :
      (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H base r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤ Gamma) :
    (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H final r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤ 3 * Gamma := by
  exact threeStage_normalizedDegreeSum_le h (zero_lt_one.trans_le hd)
    (zero_le_one.trans hGamma) hbase (hc.finalDegreeSumGap heta hd hGamma)

end
end Erdos136.CFMRegularization

namespace Erdos136.CFMRegularization

open Finset

noncomputable section

variable {V : Type*} [DecidableEq V]

theorem forbiddenCard_two_le_rawCoeff
    {H : Hypergraph V} {C : ConflictSystem V} {D : ℕ}
    {d A B : ℝ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    (hD : (D : ℝ) ≤ A * d)
    (hlayer2 : (layerMaxDegree H C 2 : ℝ) ≤ B * d)
    {e : Finset V} (heH : e ∈ H) :
    ((forbiddenIncidentCompletions H C 2 e).card : ℝ) ≤
      rawForbiddenCoeff A B 2 * d * (H.card : ℝ) ^ (2 - 2) := by
  have hi : (inferInstance : DecidableEq V) = @Classical.decEq V :=
    Subsingleton.elim _ _
  cases hi
  letI : DecidableEq V := @Classical.decEq V
  have hraw := card_forbiddenIncidentCompletions_two_le
    huniform hmax hC hcard heH
  have hrawR : ((forbiddenIncidentCompletions H C 2 e).card : ℝ) ≤
      8 * (D : ℝ) + (layerMaxDegree H C 2 : ℝ) := by exact_mod_cast hraw
  simp [rawForbiddenCoeff]
  linarith

theorem forbiddenCard_three_le_rawCoeff
    {H : Hypergraph V} {C : ConflictSystem V} {D : ℕ}
    {d n A B : ℝ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    (hd : 0 ≤ d) (hn : 0 ≤ n) (hHcard : (H.card : ℝ) ≤ n)
    (hdn : d ≤ n) (hB : 0 ≤ B)
    (hD : (D : ℝ) ≤ A * d)
    (hlayer2 : (layerMaxDegree H C 2 : ℝ) ≤ B * d)
    (hlayer3 : (layerMaxDegree H C 3 : ℝ) ≤ B * d ^ 2)
    {e : Finset V} (heH : e ∈ H) :
    ((forbiddenIncidentCompletions H C 3 e).card : ℝ) ≤
      rawForbiddenCoeff A B 3 * d * n ^ (3 - 2) := by
  have hi : (inferInstance : DecidableEq V) = @Classical.decEq V :=
    Subsingleton.elim _ _
  cases hi
  letI : DecidableEq V := @Classical.decEq V
  have hraw := card_forbiddenIncidentCompletions_three_le
    huniform hmax hC hcard heH
  have hrawR : ((forbiddenIncidentCompletions H C 3 e).card : ℝ) ≤
      (8 * (D : ℝ)) * (H.card : ℝ) +
        (H.card : ℝ) * (8 * (D : ℝ)) +
        ((layerMaxDegree H C 2 : ℝ) * (H.card : ℝ) +
          (H.card : ℝ) * (layerMaxDegree H C 2 : ℝ) +
          (layerMaxDegree H C 3 : ℝ)) := by exact_mod_cast hraw
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hl20 : 0 ≤ (layerMaxDegree H C 2 : ℝ) := Nat.cast_nonneg _
  have hDcard : (D : ℝ) * (H.card : ℝ) ≤ (A * d) * n :=
    calc
      _ ≤ (D : ℝ) * n := mul_le_mul_of_nonneg_left hHcard hD0
      _ ≤ (A * d) * n := mul_le_mul_of_nonneg_right hD hn
  have hl2card : (layerMaxDegree H C 2 : ℝ) * (H.card : ℝ) ≤
      (B * d) * n :=
    calc
      _ ≤ (layerMaxDegree H C 2 : ℝ) * n :=
        mul_le_mul_of_nonneg_left hHcard hl20
      _ ≤ (B * d) * n := mul_le_mul_of_nonneg_right hlayer2 hn
  have hl3dn : (layerMaxDegree H C 3 : ℝ) ≤ B * d * n := by
    calc
      _ ≤ B * d ^ 2 := hlayer3
      _ ≤ B * d * n := by
        have := mul_le_mul_of_nonneg_left hdn (mul_nonneg hB hd)
        nlinarith
  simp [rawForbiddenCoeff]
  nlinarith

theorem forbiddenCard_four_le_rawCoeff
    {H : Hypergraph V} {C : ConflictSystem V} {D : ℕ}
    {d n A B : ℝ}
    (huniform : IsUniform H 8) (hmax : MaxDegreeLE H D)
    (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, 2 ≤ c.card ∧ c.card ≤ 4)
    (hd : 0 ≤ d) (hn : 0 ≤ n) (hHcard : (H.card : ℝ) ≤ n)
    (hdn : d ≤ n) (hB : 0 ≤ B)
    (hD : (D : ℝ) ≤ A * d)
    (hlayer2 : (layerMaxDegree H C 2 : ℝ) ≤ B * d)
    (hlayer3 : (layerMaxDegree H C 3 : ℝ) ≤ B * d ^ 2)
    (hlayer4 : (layerMaxDegree H C 4 : ℝ) ≤ B * d ^ 3)
    {e : Finset V} (heH : e ∈ H) :
    ((forbiddenIncidentCompletions H C 4 e).card : ℝ) ≤
      rawForbiddenCoeff A B 4 * d * n ^ (4 - 2) := by
  have hi : (inferInstance : DecidableEq V) = @Classical.decEq V :=
    Subsingleton.elim _ _
  cases hi
  letI : DecidableEq V := @Classical.decEq V
  have hraw := card_forbiddenIncidentCompletions_four_le
    huniform hmax hC hcard heH
  have hrawR : ((forbiddenIncidentCompletions H C 4 e).card : ℝ) ≤
      (8 * (D : ℝ)) * (H.card : ℝ) ^ 2 +
        ((H.card : ℝ) * (8 * (D : ℝ))) * (H.card : ℝ) +
        ((layerMaxDegree H C 2 : ℝ) * (H.card : ℝ) ^ 2 +
          ((H.card : ℝ) * (layerMaxDegree H C 2 : ℝ)) * (H.card : ℝ) +
          (layerMaxDegree H C 3 : ℝ) * (H.card : ℝ) +
          (H.card : ℝ) * (layerMaxDegree H C 3 : ℝ) +
          (layerMaxDegree H C 4 : ℝ)) := by exact_mod_cast hraw
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hl20 : 0 ≤ (layerMaxDegree H C 2 : ℝ) := Nat.cast_nonneg _
  have hl30 : 0 ≤ (layerMaxDegree H C 3 : ℝ) := Nat.cast_nonneg _
  have hH0 : 0 ≤ (H.card : ℝ) := Nat.cast_nonneg _
  have hHsq : (H.card : ℝ) ^ 2 ≤ n ^ 2 :=
    pow_le_pow_left₀ hH0 hHcard 2
  have hDcard2 : (D : ℝ) * (H.card : ℝ) ^ 2 ≤ (A * d) * n ^ 2 :=
    calc
      _ ≤ (D : ℝ) * n ^ 2 := mul_le_mul_of_nonneg_left hHsq hD0
      _ ≤ (A * d) * n ^ 2 := mul_le_mul_of_nonneg_right hD (sq_nonneg n)
  have hl2card2 : (layerMaxDegree H C 2 : ℝ) * (H.card : ℝ) ^ 2 ≤
      (B * d) * n ^ 2 :=
    calc
      _ ≤ (layerMaxDegree H C 2 : ℝ) * n ^ 2 :=
        mul_le_mul_of_nonneg_left hHsq hl20
      _ ≤ (B * d) * n ^ 2 :=
        mul_le_mul_of_nonneg_right hlayer2 (sq_nonneg n)
  have hl3card : (layerMaxDegree H C 3 : ℝ) * (H.card : ℝ) ≤
      (B * d) * n ^ 2 := by
    calc
      _ ≤ (B * d ^ 2) * (H.card : ℝ) :=
        mul_le_mul_of_nonneg_right hlayer3 hH0
      _ ≤ (B * d ^ 2) * n := by
        apply mul_le_mul_of_nonneg_left hHcard
        positivity
      _ ≤ (B * d) * n ^ 2 := by
        have := mul_le_mul_of_nonneg_left hdn (mul_nonneg hB hd)
        have hdn' := mul_le_mul_of_nonneg_left hdn hn
        nlinarith
  have hl4dn2 : (layerMaxDegree H C 4 : ℝ) ≤ (B * d) * n ^ 2 := by
    calc
      _ ≤ B * d ^ 3 := hlayer4
      _ ≤ (B * d) * n ^ 2 := by
        have hsqdn : d ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hd hdn 2
        have := mul_le_mul_of_nonneg_left hsqdn (mul_nonneg hB hd)
        nlinarith
  simp [rawForbiddenCoeff]
  nlinarith

end
end Erdos136.CFMRegularization

open scoped BigOperators

namespace Erdos136
namespace CFMRegularization

variable {V : Type*} [DecidableEq V]

/-- A conflict-layer inclusion induces the corresponding link-layer inclusion. -/
theorem scratch_conflictLinkLayer_mono_of_layer_succ
    {C D : ConflictSystem V} {s : ℕ}
    (h : conflictLayer C (s + 1) ⊆ conflictLayer D (s + 1))
    (e : Finset V) :
    conflictLinkLayer C e s ⊆ conflictLinkLayer D e s := by
  intro t ht
  obtain ⟨htlink, hts⟩ := Finset.mem_filter.mp ht
  obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp htlink
  obtain ⟨huC, heu⟩ := Finset.mem_filter.mp hu
  have hecard : (u.erase e).card + 1 = u.card := by
    exact Finset.card_erase_add_one heu
  have hucard : u.card = s + 1 := by
    rw [hut, hts] at hecard
    omega
  have huDlayer : u ∈ conflictLayer D (s + 1) :=
    h (Finset.mem_filter.mpr ⟨huC, hucard⟩)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr
      ⟨u, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp huDlayer).1, heu⟩, hut⟩,
      hts⟩

/-- Link intersections can only shrink when the relevant conflict layer shrinks. -/
theorem scratch_card_link_inter_le_of_layer_succ
    {C D : ConflictSystem V} {s : ℕ}
    (h : conflictLayer C (s + 1) ⊆ conflictLayer D (s + 1))
    (e f : Finset V) :
    ((conflictLinkLayer C e s ∩ conflictLinkLayer C f s).card : ℝ) ≤
      ((conflictLinkLayer D e s ∩ conflictLinkLayer D f s).card : ℝ) := by
  exact_mod_cast Finset.card_le_card
    (Finset.inter_subset_inter
      (scratch_conflictLinkLayer_mono_of_layer_succ h e)
      (scratch_conflictLinkLayer_mono_of_layer_succ h f))

/-- At every rank other than the completed rank, one completion step only
shrinks the corresponding link layer. -/
theorem scratch_conflictLinkLayer_addCompletionLayer_subset_of_ne
    {C A : ConflictSystem V} {s stage : ℕ}
    (hA : IsUniform A stage) (hne : s + 1 ≠ stage) (e : Finset V) :
    conflictLinkLayer (addCompletionLayer C A) e s ⊆
      conflictLinkLayer C e s := by
  exact scratch_conflictLinkLayer_mono_of_layer_succ
    (conflictLayer_addCompletionLayer_subset_of_ne hA hne) e

/-- Literal trackability transfers from the raw conflict system to the
minimal matching core augmented by its bad-pair conflicts. -/
theorem scratch_isTrackable_minimalCore_with_badPairs_of_eta_le
    {H : Hypergraph V} {C : ConflictSystem V} {j ell : ℕ}
    {d etaRaw etaBad : ℝ} {w : TestWeight V}
    (hell : 4 ≤ ell) (hd : 1 ≤ d) (heta : etaBad ≤ etaRaw)
    (hC : IsBounded C d ell etaRaw)
    (hBdegree : ∀ e ∈ H,
      (degree (badPairConflicts H C (trackableCutoff d etaBad)) e : ℝ) ≤
        Real.rpow d (1 - etaBad))
    (hw : IsTrackable H C j ell d etaRaw w) :
    IsTrackable H
      (minimalMatchingCore H
        (C ∪ badPairConflicts H C (trackableCutoff d etaBad)))
      j ell d etaBad w := by
  let B := badPairConflicts H C (trackableCutoff d etaBad)
  let C0 := minimalMatchingCore H (C ∪ B)
  have hBuniform : IsUniform B 2 := badPairConflicts_uniform_two H C _
  have hlayer2 : conflictLayer C0 2 ⊆ conflictLayer B 2 :=
    minimalCore_union_layer_two_subset_right H hC
  have hlayerB : conflictLayer B 2 = B :=
    conflictLayer_eq_self_of_uniform hBuniform
  refine ⟨hw.1, ?_, ?_, ?_, ?_⟩
  · exact hw.2.1.trans' (Real.rpow_le_rpow_of_exponent_le hd (by linarith))
  · intro j' hj' hj'j root hrootH hrootcard
    calc
      testExtension w H j root ≤
          testTotal w H j / Real.rpow d ((j' : ℝ) + etaRaw) :=
        hw.2.2.1 j' hj' hj'j root hrootH hrootcard
      _ ≤ testTotal w H j / Real.rpow d ((j' : ℝ) + etaBad) := by
        apply div_le_div_of_nonneg_left
        · exact testTotal_nonneg hw.1.1 H j
        · exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hd) _
        · exact Real.rpow_le_rpow_of_exponent_le hd (by linarith)
  · intro S hSH hwS e he f hf hef j' hj' hj'ell
    by_cases hjone : j' = 1
    · subst j'
      calc
        (((conflictLinkLayer C0 e 1 ∩
            conflictLinkLayer C0 f 1).card : ℕ) : ℝ) ≤
            (conflictLinkLayer C0 e 1).card := by
          exact_mod_cast Finset.card_le_card Finset.inter_subset_left
        _ = (degree (conflictLayer C0 2) e : ℕ) := by
          exact_mod_cast card_conflictLinkLayer_eq_degree_layer C0 e 1
        _ ≤ (degree (conflictLayer B 2) e : ℕ) := by
          exact_mod_cast degree_mono hlayer2 e
        _ = (degree B e : ℕ) := by rw [hlayerB]
        _ ≤ Real.rpow d (1 - etaBad) := by
          apply hBdegree e
          exact (Finset.mem_powersetCard.mp hSH).1 he
        _ = Real.rpow d ((1 : ℕ) - etaBad) := by norm_num
    · have hjtwo : 2 ≤ j' := by omega
      have hlayer : conflictLayer C0 (j' + 1) ⊆ conflictLayer C (j' + 1) :=
        minimalCore_union_layer_ge_three_subset_left H hBuniform (j' + 1) (by omega)
      calc
        (((conflictLinkLayer C0 e j' ∩
            conflictLinkLayer C0 f j').card : ℕ) : ℝ) ≤
            ((conflictLinkLayer C e j' ∩
              conflictLinkLayer C f j').card : ℕ) :=
          scratch_card_link_inter_le_of_layer_succ hlayer e f
        _ ≤ Real.rpow d ((j' : ℝ) - etaRaw) :=
          hw.2.2.2.1 S hSH hwS e he f hf hef j' hj' hj'ell
        _ ≤ Real.rpow d ((j' : ℝ) - etaBad) :=
          Real.rpow_le_rpow_of_exponent_le hd (by linarith)
  · intro S hSH hcontains
    by_contra hne
    have hwS : 0 < w S := lt_of_le_of_ne (hw.1.1 S) (Ne.symm hne)
    have hfree : ConflictFree C0 S := by
      exact trackable_conflictFree_minimalCore_with_badPairs_of_eta_le
        hell hd heta hw hSH hwS
    exact (not_conflictFree_iff.mpr hcontains) hfree

/-- The exact raw endpoint specialization: the auxiliary cutoff and the
minimal-core trackability exponent are both `rawRegularizationEps eta / 3`. -/
theorem scratch_isTrackable_raw_minimalCore
    {H : Hypergraph V} {C : ConflictSystem V} {j ell : ℕ}
    {d eta : ℝ} {w : TestWeight V}
    (hell : 4 ≤ ell) (heta : 0 < eta) (hd : 1 ≤ d)
    (hC : IsBounded C d ell eta)
    (hBdegree : ∀ e ∈ H,
      (degree (badPairConflicts H C
        (trackableCutoff d (rawRegularizationEps eta / 3))) e : ℝ) ≤
          Real.rpow d (1 - rawRegularizationEps eta / 3))
    (hw : IsTrackable H C j ell d eta w) :
    IsTrackable H
      (minimalMatchingCore H
        (C ∪ badPairConflicts H C
          (trackableCutoff d (rawRegularizationEps eta / 3))))
      j ell d (rawRegularizationEps eta / 3) w := by
  have hle : rawRegularizationEps eta / 3 ≤ eta := by
    simp only [rawRegularizationEps]
    linarith
  exact scratch_isTrackable_minimalCore_with_badPairs_of_eta_le
    (etaRaw := eta) (etaBad := rawRegularizationEps eta / 3)
    hell hd hle hC hBdegree hw

/-- Property (V) controls the newly completed link rank, while every other
link rank inherits its old bound through conflict-layer monotonicity. -/
theorem scratch_completion_link_intersection_upper
    {H : Hypergraph V} {base current A : ConflictSystem V}
    {stage j ell : ℕ} {d eps etaOld : ℝ} {w : TestWeight V}
    (hd : 1 ≤ d) (heps : 0 ≤ eps) (heta : eps / 5 ≤ etaOld)
    (hA : IsUniform A stage)
    (hIV : HasStagePropertiesIV H base (addCompletionLayer current A)
      d eps stage)
    (hw : IsTrackable H current j ell d etaOld w)
    {S : Hypergraph V} (hSH : S ∈ H.powersetCard j) (hwS : 0 < w S)
    (hfree : ConflictFree (addCompletionLayer current A) S)
    {e f : Finset V} (he : e ∈ S) (hf : f ∈ S) (hef : e ≠ f)
    {j' : ℕ} (hj' : 1 ≤ j') (hj'ell : j' < ell) :
    (((conflictLinkLayer (addCompletionLayer current A) e j' ∩
      conflictLinkLayer (addCompletionLayer current A) f j').card : ℕ) : ℝ) ≤
      Real.rpow d ((j' : ℝ) - eps / 5) := by
  have heH : e ∈ H := (Finset.mem_powersetCard.mp hSH).1 he
  have hfH : f ∈ H := (Finset.mem_powersetCard.mp hSH).1 hf
  have hmatch : IsMatching H S := by
    by_contra hnmatch
    have hz := hw.1.2.2.2 S hnmatch
    linarith
  have hdisj : Disjoint e f := hmatch.2 he hf hef
  have hnotPair : {e, f} ∉ conflictLayer (addCompletionLayer current A) 2 := by
    intro hpair
    apply hfree {e, f} (Finset.mem_filter.mp hpair).1
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact he
    · exact hf
  by_cases hnew : j' = stage - 1
  · have hbound := hIV.2.2.2.2.2.2 e heH f hfH hdisj hnotPair
    calc
      (((conflictLinkLayer (addCompletionLayer current A) e j' ∩
        conflictLinkLayer (addCompletionLayer current A) f j').card : ℕ) : ℝ) ≤
          Real.rpow d ((stage - 1 : ℕ) - eps / 4) := by
        simpa [hnew] using hbound
      _ ≤ Real.rpow d ((j' : ℝ) - eps / 5) := by
        apply Real.rpow_le_rpow_of_exponent_le hd
        rw [hnew]
        nlinarith
  · have hne : j' + 1 ≠ stage := by
      have hs2 := hIV.1
      omega
    have hsub : conflictLayer (addCompletionLayer current A) (j' + 1) ⊆
        conflictLayer current (j' + 1) :=
      conflictLayer_addCompletionLayer_subset_of_ne hA hne
    calc
      (((conflictLinkLayer (addCompletionLayer current A) e j' ∩
        conflictLinkLayer (addCompletionLayer current A) f j').card : ℕ) : ℝ) ≤
          ((conflictLinkLayer current e j' ∩
            conflictLinkLayer current f j').card : ℕ) :=
        scratch_card_link_inter_le_of_layer_succ hsub e f
      _ ≤ Real.rpow d ((j' : ℝ) - etaOld) :=
        hw.2.2.2.1 S hSH hwS e he f hf hef j' hj' hj'ell
      _ ≤ Real.rpow d ((j' : ℝ) - eps / 5) :=
        Real.rpow_le_rpow_of_exponent_le hd (by linarith)

/-- Target-parameter version of `restrictWeight_isTrackable`; unlike the
specialized library wrapper, the source and target exponents are independent. -/
theorem scratch_restrictWeight_isTrackable_target
    {H : Hypergraph V} {C D : ConflictSystem V} {j ell : ℕ}
    {d etaOld etaNew : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C j ell d etaOld w)
    (hlarge : Real.rpow d ((j : ℝ) + etaNew) ≤
      testTotal (restrictWeight D w) H j)
    (hext : ∀ j', 1 ≤ j' → j' < j →
      testTotal w H j / Real.rpow d ((j' : ℝ) + etaOld) ≤
        testTotal (restrictWeight D w) H j /
          Real.rpow d ((j' : ℝ) + etaNew))
    (hlinks : ∀ S ∈ H.powersetCard j, 0 < w S → ConflictFree D S →
      ∀ e ∈ S, ∀ f ∈ S, e ≠ f → ∀ j', 1 ≤ j' → j' < ell →
        (((conflictLinkLayer D e j' ∩
          conflictLinkLayer D f j').card : ℕ) : ℝ) ≤
            Real.rpow d ((j' : ℝ) - etaNew)) :
    IsTrackable H D j ell d etaNew (restrictWeight D w) := by
  refine ⟨?_, hlarge, ?_, ?_, ?_⟩
  · refine ⟨restrictWeight_nonneg hw.1.1, ?_, ?_, ?_⟩
    · intro S
      exact (restrictWeight_le hw.1.1 S).trans (hw.1.2.1 S)
    · intro S hcard
      simp only [restrictWeight]
      split_ifs
      · exact hw.1.2.2.1 S hcard
      · rfl
    · intro S hmatch
      simp only [restrictWeight]
      split_ifs
      · exact hw.1.2.2.2 S hmatch
      · rfl
  · intro j' hj' hj'j root hrootH hrootcard
    exact (testExtension_restrictWeight_le H D j root w hw.1.1).trans
      ((hw.2.2.1 j' hj' hj'j root hrootH hrootcard).trans
        (hext j' hj' hj'j))
  · intro S hSH hpos e he f hf hef j' hj' hj'ell
    have hle := restrictWeight_le (D := D) hw.1.1 S
    have hwpos : 0 < w S := hpos.trans_le hle
    have hfree : ConflictFree D S := by
      by_contra hnfree
      rw [restrictWeight_apply_not_free hnfree] at hpos
      exact (lt_irrefl 0) hpos
    exact hlinks S hSH hwpos hfree e he f hf hef j' hj' hj'ell
  · intro S _hSH hcontains
    exact restrictWeight_apply_not_free (not_conflictFree_iff.mpr hcontains)

/-- One completion step preserves trackability after a cumulative
killed-weight estimate, with the paper's `eps / 5` output exponent. -/
theorem scratch_restrictWeight_isTrackable_addCompletionLayer_of_killedWeight
    {H : Hypergraph V} {base current A : ConflictSystem V}
    {stage j ell : ℕ} {d eps etaOld : ℝ} {w : TestWeight V}
    (hd : 1 ≤ d) (heps : 0 ≤ eps) (heta : eps / 5 ≤ etaOld)
    (hscalar : Real.rpow d (eps / 5 - etaOld) +
      Real.rpow d (-eps) ≤ 1)
    (hA : IsUniform A stage)
    (hIV : HasStagePropertiesIV H base (addCompletionLayer current A)
      d eps stage)
    (hw : IsTrackable H current j ell d etaOld w)
    (hkill : killedWeight H (addCompletionLayer current A) j w ≤
      testTotal w H j / Real.rpow d eps) :
    IsTrackable H (addCompletionLayer current A) j ell d (eps / 5)
      (restrictWeight (addCompletionLayer current A) w) := by
  have h12 := restrictWeight_W1_W2_of_killedWeight hw
    (zero_lt_one.trans_le hd) hscalar hkill
  apply scratch_restrictWeight_isTrackable_target hw h12.1 h12.2
  intro S hSH hwS hfree e he f hf hef j' hj' hj'ell
  exact scratch_completion_link_intersection_upper hd heps heta hA hIV hw
    hSH hwS hfree he hf hef hj' hj'ell

/-- The transfer cutoff supplies the scalar absorption needed for the first
completion step, whose input exponent is `eps / 3`. -/
theorem scratch_raw_firstStage_transferScalar
    {eta K d : ℝ} (hcut : RawTransferCutoffSpec eta K d)
    (heta : 0 < eta) (hd : 1 ≤ d) :
    Real.rpow d
          (rawRegularizationEps eta / 5 - rawRegularizationEps eta / 3) +
        Real.rpow d (-rawRegularizationEps eta) ≤ 1 := by
  have hsmall :
      Real.rpow d
          (rawRegularizationEps eta / 5 - rawRegularizationEps eta / 3) ≤
        1 / 4 := by
    calc
      Real.rpow d
          (rawRegularizationEps eta / 5 - rawRegularizationEps eta / 3) ≤
          Real.rpow d (-rawRegularizationEps eta / 600) := by
        apply Real.rpow_le_rpow_of_exponent_le hd
        simp only [rawRegularizationEps]
        linarith
      _ ≤ 1 / 4 := hcut.regularizationTiny
  have hreg := (hcut.regularizationScales heta hd).1
  linarith

/-- First-stage raw specialization of the killed-weight transfer theorem. -/
theorem scratch_restrictWeight_isTrackable_raw_firstCompletion
    {H : Hypergraph V} {base current A : ConflictSystem V}
    {stage j ell : ℕ} {eta K d : ℝ} {w : TestWeight V}
    (hcut : RawTransferCutoffSpec eta K d)
    (heta : 0 < eta) (hd : 1 ≤ d)
    (hA : IsUniform A stage)
    (hIV : HasStagePropertiesIV H base (addCompletionLayer current A)
      d (rawRegularizationEps eta) stage)
    (hw : IsTrackable H current j ell d
      (rawRegularizationEps eta / 3) w)
    (hkill : killedWeight H (addCompletionLayer current A) j w ≤
      testTotal w H j / Real.rpow d (rawRegularizationEps eta)) :
    IsTrackable H (addCompletionLayer current A) j ell d
      (rawRegularizationEps eta / 5)
      (restrictWeight (addCompletionLayer current A) w) := by
  have heps0 : 0 ≤ rawRegularizationEps eta := by
    simp only [rawRegularizationEps]
    linarith
  have hfrac : rawRegularizationEps eta / 5 ≤
      rawRegularizationEps eta / 3 := by
    simp only [rawRegularizationEps]
    linarith
  exact scratch_restrictWeight_isTrackable_addCompletionLayer_of_killedWeight
    (eps := rawRegularizationEps eta)
    (etaOld := rawRegularizationEps eta / 3)
    hd heps0 hfrac (scratch_raw_firstStage_transferScalar hcut heta hd)
    hA hIV hw hkill

end CFMRegularization
end Erdos136

namespace Erdos136.CFMRegularization

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem regularizationCertificate_of_not_nonempty_raw
    {V ι : Type*} [DecidableEq V] [Fintype V] [Fintype ι]
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eta : ℝ) (ell : ℕ) (j : ι → ℕ) (w : ι → TestWeight V)
    (hC : IsConflictSystem H C)
    (hcard : ∀ c ∈ C, c.card = 4)
    (hd : 1 ≤ d)
    (htrack : ∀ i, 1 ≤ j i ∧ j i ≤ 3 ∧
      IsTrackable H C (j i) ell d eta (w i))
    (hne : ¬ H.Nonempty) :
    Nonempty
      (RegularizationCertificate H C d (rawRegularizationEps eta)
        (2 * (ell : ℝ) + 1) ell j w) := by
  have hH : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hCempty : C = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hcsub : c ⊆ H := hC c hc
    rw [hH] at hcsub
    have hc0 : c = ∅ := Finset.subset_empty.mp hcsub
    have hc4 : c.card = 4 := hcard c hc
    rw [hc0] at hc4
    norm_num at hc4
  have hnoIndex : ∀ i : ι, False := by
    intro i
    have hji : 0 < j i := lt_of_lt_of_le Nat.zero_lt_one (htrack i).1
    have hmass := (htrack i).2.2.2.1
    have htotal : testTotal (w i) H (j i) = 0 := by
      rw [hH]
      exact testTotal_empty_of_pos (w i) hji
    rw [htotal] at hmass
    have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
    have hp := Real.rpow_pos_of_pos hdpos ((j i : ℝ) + eta)
    exact (not_lt_of_ge hmass hp)
  rw [hH, hCempty]
  refine ⟨{
    badPairs := ∅
    completion2 := ∅
    completion3 := ∅
    completion4 := ∅
    regularized := ∅
    badPairs_definition := ?_
    construction := ?_
    badPairs_uniform := ?_
    badPairs_degree := ?_
    completion2_uniform := ?_
    completion3_uniform := ?_
    completion4_uniform := ?_
    isConflictSystem := ?_
    bounded := ?_
    conflictMatching := ?_
    antichain := ?_
    layerDegree := ?_
    layerCodegree := ?_
    conditionC4 := ?_
    conditionC5 := ?_
    commonLinks := ?_
    restrictedWeight := fun i => restrictWeight ∅ (w i)
    restrictedWeight_definition := ?_
    killedWeight_small := ?_
    survivingTrackable := ?_
  }⟩
  · rw [badPairConflicts, Finset.powersetCard_eq_empty.mpr (by norm_num)]
    simp
  · simp [minimalMatchingCore, addCompletionLayer]
  · simp [IsUniform]
  · intro e he
    simp at he
  · simp [IsUniform]
  · simp [IsUniform]
  · simp [IsUniform]
  · simp [IsConflictSystem]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · have hzero : ∀ r, layerMaxDegree (∅ : Hypergraph V) ∅ r = 0 := by
        intro r
        rfl
      simp_rw [hzero]
      simp
      positivity
    · simp only [conflictLayer, Finset.filter_empty, ne_eq,
        not_true_eq_false, Finset.filter_false, Finset.card_empty,
        Nat.cast_zero]
      positivity
    · intro r _hr2 _hr4 q _hq2 _hqr root _hroot
      simp [conflictLayer]
      exact Real.rpow_nonneg (le_trans zero_le_one hd) _
    · intro e he
      simp at he
    · intro e he
      simp at he
  · simp
  · simp
  · intro r _hr2 _hr4 e he
    simp at he
  · intro r q _hr2 _hr4 _hq2 _hqr root _hroot
    simp [conflictLayer]
    exact Real.rpow_nonneg (le_trans zero_le_one hd) _
  · intro e he
    simp at he
  · intro e he
    simp at he
  · intro e he
    simp at he
  · intro i
    rfl
  · intro i
    exact (hnoIndex i).elim
  · intro i
    exact (hnoIndex i).elim

end Erdos136.CFMRegularization

namespace Erdos136.CFMRegularization

open Finset
open scoped BigOperators
open UpperObservables

attribute [local instance] Classical.propDecidable

noncomputable section

theorem rawSourcePmax_le_basic
    {d eta n : ℝ} {j : ℕ}
    (hj : j ∈ ({2, 3, 4} : Finset ℕ))
    (hd : 1 ≤ d) (hn : 0 < n) (hdn : d ≤ n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n) :
    rawSourcePmax d eta n j ≤
      32 * Real.rpow d (10 * rawRegularizationEps eta - eta) := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hhost0 : 0 < Real.rpow d (1 + eta) / 32 :=
    div_pos (Real.rpow_pos_of_pos hd0 _) (by norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · rw [rawSourcePmax]
    norm_num
    apply (div_le_iff₀ hn).2
    calc
      Real.rpow d (1 + 10 * rawRegularizationEps eta) =
          (32 * Real.rpow d (10 * rawRegularizationEps eta - eta)) *
            (Real.rpow d (1 + eta) / 32) := by
        field_simp
        calc
          Real.rpow d (1 + 10 * rawRegularizationEps eta) =
              Real.rpow d ((10 * rawRegularizationEps eta - eta) +
                (1 + eta)) := by congr 1 <;> ring
          _ = _ := Real.rpow_add hd0 _ _
      _ ≤ (32 * Real.rpow d (10 * rawRegularizationEps eta - eta)) * n := by
        exact mul_le_mul_of_nonneg_left hhost
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hd0.le _))
  · rw [rawSourcePmax]
    norm_num
    apply (div_le_iff₀ (sq_pos_of_pos hn)).2
    have hprod : d * (Real.rpow d (1 + eta) / 32) ≤ n ^ 2 := by
      calc
        _ ≤ n * n := mul_le_mul hdn hhost hhost0.le hn.le
        _ = n ^ 2 := by ring
    calc
      Real.rpow d (2 + 10 * rawRegularizationEps eta) =
          (32 * Real.rpow d (10 * rawRegularizationEps eta - eta)) *
            (d * (Real.rpow d (1 + eta) / 32)) := by
        field_simp
        calc
          Real.rpow d (2 + 10 * rawRegularizationEps eta) =
              Real.rpow d ((10 * rawRegularizationEps eta - eta) +
                1 + (1 + eta)) := by congr 1 <;> ring
          _ = Real.rpow d ((10 * rawRegularizationEps eta - eta) + 1) *
              Real.rpow d (1 + eta) := Real.rpow_add hd0 _ _
          _ = (Real.rpow d (10 * rawRegularizationEps eta - eta) *
                Real.rpow d 1) * Real.rpow d (1 + eta) := by
              exact congrArg (fun z => z * Real.rpow d (1 + eta))
                (Real.rpow_add hd0 _ _)
          _ = _ := by
              exact congrArg (fun z =>
                Real.rpow d (10 * rawRegularizationEps eta - eta) * z *
                  Real.rpow d (1 + eta)) (Real.rpow_one d)
      _ ≤ (32 * Real.rpow d (10 * rawRegularizationEps eta - eta)) *
          n ^ 2 := mul_le_mul_of_nonneg_left hprod
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hd0.le _))
  · rw [rawSourcePmax]
    norm_num
    apply (div_le_iff₀ (pow_pos hn 3)).2
    have hprod : d ^ 2 * (Real.rpow d (1 + eta) / 32) ≤ n ^ 3 := by
      have hdsq : d ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hd0.le hdn 2
      calc
        _ ≤ n ^ 2 * n := mul_le_mul hdsq hhost hhost0.le (sq_nonneg n)
        _ = n ^ 3 := by ring
    calc
      Real.rpow d (3 + 10 * rawRegularizationEps eta) =
          (32 * Real.rpow d (10 * rawRegularizationEps eta - eta)) *
            (d ^ 2 * (Real.rpow d (1 + eta) / 32)) := by
        rw [show d ^ 2 = Real.rpow d 2 by
          rw [← Real.rpow_natCast]; norm_num]
        field_simp
        calc
          Real.rpow d (3 + 10 * rawRegularizationEps eta) =
              Real.rpow d ((10 * rawRegularizationEps eta - eta) +
                2 + (1 + eta)) := by congr 1 <;> ring
          _ = Real.rpow d ((10 * rawRegularizationEps eta - eta) + 2) *
              Real.rpow d (1 + eta) := Real.rpow_add hd0 _ _
          _ = (Real.rpow d (10 * rawRegularizationEps eta - eta) *
                Real.rpow d 2) * Real.rpow d (1 + eta) := by
              exact congrArg (fun z => z * Real.rpow d (1 + eta))
                (Real.rpow_add hd0 _ _)
          _ = _ := by ring
      _ ≤ (32 * Real.rpow d (10 * rawRegularizationEps eta - eta)) *
          n ^ 3 := mul_le_mul_of_nonneg_left hprod
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hd0.le _))

theorem rawSourcePmax_sq_hostPower_le
    {d eta n : ℝ} {j : ℕ}
    (hj : j ∈ ({2, 3, 4} : Finset ℕ))
    (hd : 1 ≤ d) (hn : 0 < n) (hdn : d ≤ n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n) :
    n ^ (j - 1) * (rawSourcePmax d eta n j) ^ 2 ≤
      32 * Real.rpow d
        ((j : ℝ) - 1 + 20 * rawRegularizationEps eta - eta) := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hp := rawSourcePmax_le_basic hj hd hn hdn hhost
  have hp0 : 0 ≤ rawSourcePmax d eta n j :=
    rawSourcePmax_nonneg d eta n j hd0.le hn.le
  have hpow0 : 0 ≤ Real.rpow d
      ((j : ℝ) - 1 + 10 * rawRegularizationEps eta) :=
    Real.rpow_nonneg hd0.le _
  have hid : n ^ (j - 1) * (rawSourcePmax d eta n j) ^ 2 =
      rawSourcePmax d eta n j *
        Real.rpow d ((j : ℝ) - 1 + 10 * rawRegularizationEps eta) := by
    rw [rawSourcePmax]
    have hnzero : n ^ (j - 1) ≠ 0 := ne_of_gt (pow_pos hn _)
    field_simp
  rw [hid]
  calc
    rawSourcePmax d eta n j *
        Real.rpow d ((j : ℝ) - 1 + 10 * rawRegularizationEps eta) ≤
      (32 * Real.rpow d (10 * rawRegularizationEps eta - eta)) *
        Real.rpow d ((j : ℝ) - 1 + 10 * rawRegularizationEps eta) :=
      mul_le_mul_of_nonneg_right hp hpow0
    _ = 32 * Real.rpow d
        ((j : ℝ) - 1 + 20 * rawRegularizationEps eta - eta) := by
      rw [mul_assoc]
      exact congrArg (fun z => 32 * z) <| by
        change d ^ (10 * rawRegularizationEps eta - eta) *
            d ^ ((j : ℝ) - 1 + 10 * rawRegularizationEps eta) =
          d ^ ((j : ℝ) - 1 + 20 * rawRegularizationEps eta - eta)
        rw [← Real.rpow_add hd0]
        congr 1
        ring

theorem rawSourcePmax_codegreeMean_le
    {d eta n : ℝ} {j q : ℕ}
    (hj2 : 2 ≤ j) (hj4 : j ≤ 4) (hq2 : 2 ≤ q) (hqj : q < j)
    (hd : 1 ≤ d) (hn : 0 < n) (hdn : d ≤ n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n) :
    n ^ (j - q) * rawSourcePmax d eta n j ≤
      32 * Real.rpow d
        ((j : ℝ) - (q : ℝ) + 10 * rawRegularizationEps eta - eta) := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hhost0 : 0 < Real.rpow d (1 + eta) / 32 :=
    div_pos (Real.rpow_pos_of_pos hd0 _) (by norm_num)
  interval_cases j <;> interval_cases q
  all_goals simp [rawSourcePmax]
  · have hid : n * (Real.rpow d (2 + 10 * rawRegularizationEps eta) / n ^ 2) =
        Real.rpow d (2 + 10 * rawRegularizationEps eta) / n := by
      field_simp
    norm_num at ⊢
    change n * (Real.rpow d (2 + 10 * rawRegularizationEps eta) / n ^ 2) ≤
      32 * Real.rpow d (1 + 10 * rawRegularizationEps eta - eta)
    rw [hid]
    apply (div_le_iff₀ hn).2
    calc
      Real.rpow d (2 + 10 * rawRegularizationEps eta) =
          32 * Real.rpow d (1 + 10 * rawRegularizationEps eta - eta) *
            (Real.rpow d (1 + eta) / 32) := by
        field_simp
        change d ^ (2 + 10 * rawRegularizationEps eta) =
          d ^ (1 + 10 * rawRegularizationEps eta - eta) * d ^ (1 + eta)
        calc
          d ^ (2 + 10 * rawRegularizationEps eta) =
              d ^ ((1 + 10 * rawRegularizationEps eta - eta) + (1 + eta)) := by
                congr 1 <;> ring
          _ = _ := Real.rpow_add hd0 _ _
      _ ≤ 32 * Real.rpow d (1 + 10 * rawRegularizationEps eta - eta) * n := by
        exact mul_le_mul_of_nonneg_left hhost
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hd0.le _))
  · have hid : n ^ 2 * (Real.rpow d (3 + 10 * rawRegularizationEps eta) / n ^ 3) =
        Real.rpow d (3 + 10 * rawRegularizationEps eta) / n := by
      field_simp
    norm_num at ⊢
    change n ^ 2 * (Real.rpow d (3 + 10 * rawRegularizationEps eta) / n ^ 3) ≤
      32 * Real.rpow d (2 + 10 * rawRegularizationEps eta - eta)
    rw [hid]
    apply (div_le_iff₀ hn).2
    calc
      Real.rpow d (3 + 10 * rawRegularizationEps eta) =
          32 * Real.rpow d (2 + 10 * rawRegularizationEps eta - eta) *
            (Real.rpow d (1 + eta) / 32) := by
        field_simp
        change d ^ (3 + 10 * rawRegularizationEps eta) =
          d ^ (2 + 10 * rawRegularizationEps eta - eta) * d ^ (1 + eta)
        calc
          d ^ (3 + 10 * rawRegularizationEps eta) =
              d ^ ((2 + 10 * rawRegularizationEps eta - eta) + (1 + eta)) := by
                congr 1 <;> ring
          _ = _ := Real.rpow_add hd0 _ _
      _ ≤ 32 * Real.rpow d (2 + 10 * rawRegularizationEps eta - eta) * n := by
        exact mul_le_mul_of_nonneg_left hhost
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hd0.le _))
  · have hid : n * (Real.rpow d (3 + 10 * rawRegularizationEps eta) / n ^ 3) =
        Real.rpow d (3 + 10 * rawRegularizationEps eta) / n ^ 2 := by
      field_simp
    norm_num at ⊢
    change n * (Real.rpow d (3 + 10 * rawRegularizationEps eta) / n ^ 3) ≤
      32 * Real.rpow d (1 + 10 * rawRegularizationEps eta - eta)
    rw [hid]
    apply (div_le_iff₀ (sq_pos_of_pos hn)).2
    have hprod : d * (Real.rpow d (1 + eta) / 32) ≤ n ^ 2 := by
      calc
        _ ≤ n * n := mul_le_mul hdn hhost hhost0.le hn.le
        _ = n ^ 2 := by ring
    calc
      Real.rpow d (3 + 10 * rawRegularizationEps eta) =
          32 * Real.rpow d (1 + 10 * rawRegularizationEps eta - eta) *
            (d * (Real.rpow d (1 + eta) / 32)) := by
        field_simp
        calc
          Real.rpow d (3 + 10 * rawRegularizationEps eta) =
              Real.rpow d ((1 + 10 * rawRegularizationEps eta - eta) +
                1 + (1 + eta)) := by congr 1 <;> ring
          _ = Real.rpow d ((1 + 10 * rawRegularizationEps eta - eta) + 1) *
              Real.rpow d (1 + eta) := Real.rpow_add hd0 _ _
          _ = (Real.rpow d (1 + 10 * rawRegularizationEps eta - eta) *
                Real.rpow d 1) * Real.rpow d (1 + eta) := by
              exact congrArg (fun z => z * Real.rpow d (1 + eta))
                (Real.rpow_add hd0 _ _)
          _ = _ := by
            exact congrArg (fun z =>
              Real.rpow d (1 + 10 * rawRegularizationEps eta - eta) * z *
                Real.rpow d (1 + eta)) (Real.rpow_one d)
      _ ≤ 32 * Real.rpow d (1 + 10 * rawRegularizationEps eta - eta) *
          n ^ 2 := mul_le_mul_of_nonneg_left hprod
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hd0.le _))

inductive RawEndpointRequirement
  | degreeError
  | degreeFailure
  | degreeEntropy
  | entropyConstant
  deriving DecidableEq

def rawEndpointRegistry (eta : ℝ) (heta : 0 < eta) :
    LargeDRegistry RawEndpointRequirement where
  active := { .degreeError, .degreeFailure, .degreeEntropy, .entropyConstant }
  condition r d := match r with
    | .degreeError =>
        4 * Real.rpow d (-2 * rawRegularizationEps eta) ≤
          Real.rpow d (-rawRegularizationEps eta / 4 -
            rawRegularizationEps eta / 600)
    | .degreeFailure =>
        32 * Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
          Real.rpow d (1 - 1351 * rawRegularizationEps eta / 600)
    | .degreeEntropy =>
        (2 / eta ^ 3) * Real.rpow d (eta ^ 3 / 2) ≤
          Real.rpow d (eta ^ 3)
    | .entropyConstant => Real.log 4 ≤ Real.rpow d (eta ^ 3)
  eventually_condition := by
    intro r _hr
    cases r with
    | degreeError =>
        exact eventually_const_mul_rpow_le_rpow_real 4
          (-2 * rawRegularizationEps eta)
          (-rawRegularizationEps eta / 4 - rawRegularizationEps eta / 600)
          (by simp [rawRegularizationEps]; linarith)
    | degreeFailure =>
        exact eventually_const_mul_rpow_le_rpow_real 32
          (1 - 10 * rawRegularizationEps eta)
          (1 - 1351 * rawRegularizationEps eta / 600)
          (by simp [rawRegularizationEps]; linarith)
    | degreeEntropy =>
        exact eventually_const_mul_rpow_le_rpow_real (2 / eta ^ 3)
          (eta ^ 3 / 2) (eta ^ 3) (by
            have : 0 < eta ^ 3 := by positivity
            linarith)
    | entropyConstant =>
        exact eventually_const_le_rpow_real (Real.log 4) (eta ^ 3) (by positivity)

structure RawEndpointCutoffSpec (eta d : ℝ) : Prop where
  degreeError :
    4 * Real.rpow d (-2 * rawRegularizationEps eta) ≤
      Real.rpow d (-rawRegularizationEps eta / 4 -
        rawRegularizationEps eta / 600)
  degreeFailure :
    32 * Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
      Real.rpow d (1 - 1351 * rawRegularizationEps eta / 600)
  degreeEntropy :
    (2 / eta ^ 3) * Real.rpow d (eta ^ 3 / 2) ≤ Real.rpow d (eta ^ 3)
  entropyConstant : Real.log 4 ≤ Real.rpow d (eta ^ 3)

theorem exists_rawEndpointCutoff (eta : ℝ) (heta : 0 < eta) :
    ∃ d0 : ℝ, ∀ d, d0 ≤ d → RawEndpointCutoffSpec eta d := by
  let R := rawEndpointRegistry eta heta
  obtain ⟨d0, hd0⟩ := R.exists_cutoff
  refine ⟨d0, fun d hd => ?_⟩
  have hreq (r : RawEndpointRequirement) : R.condition r d := by
    exact hd0 d hd r (by cases r <;> simp [R, rawEndpointRegistry])
  exact ⟨by simpa [R, rawEndpointRegistry] using hreq .degreeError,
    by simpa [R, rawEndpointRegistry] using hreq .degreeFailure,
    by simpa [R, rawEndpointRegistry] using hreq .degreeEntropy,
    by simpa [R, rawEndpointRegistry] using hreq .entropyConstant⟩

theorem RawEndpointCutoffSpec.degree_le_exp_entropy
    {eta d : ℝ} (h : RawEndpointCutoffSpec eta d)
    (heta : 0 < eta) (hd : 1 ≤ d) :
    d ≤ Real.exp (Real.rpow d (eta ^ 3)) := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have ha : 0 < eta ^ 3 / 2 := by positivity
  have hlog0 := Real.log_le_rpow_div hd0.le ha
  have hscale : Real.rpow d (eta ^ 3 / 2) / (eta ^ 3 / 2) =
      (2 / eta ^ 3) * Real.rpow d (eta ^ 3 / 2) := by
    field_simp
  change Real.log d ≤ Real.rpow d (eta ^ 3 / 2) / (eta ^ 3 / 2) at hlog0
  rw [hscale] at hlog0
  calc
    d = Real.exp (Real.log d) := (Real.exp_log hd0).symm
    _ ≤ Real.exp (Real.rpow d (eta ^ 3)) :=
      Real.exp_le_exp.mpr (hlog0.trans h.degreeEntropy)

theorem RawEndpointCutoffSpec.four_le_exp_entropy
    {eta d : ℝ} (h : RawEndpointCutoffSpec eta d) :
    4 ≤ Real.exp (Real.rpow d (eta ^ 3)) := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  exact Real.exp_le_exp.mpr h.entropyConstant

theorem host_card_le_exp_two_entropy
    {H : Hypergraph V} {d eta : ℝ}
    (hH : IsUniform H 8)
    (hupper : ∀ v ∈ vertexFinset H, (degree H v : ℝ) ≤ d)
    (hvertex : ((vertexFinset H).card : ℝ) ≤
      Real.exp (Real.rpow d (eta ^ 3)))
    (hdexp : d ≤ Real.exp (Real.rpow d (eta ^ 3)))
    (hd : 0 ≤ d) :
    (H.card : ℝ) ≤ Real.exp (2 * Real.rpow d (eta ^ 3)) := by
  let E := Real.exp (Real.rpow d (eta ^ 3))
  have hsum : (∑ v ∈ vertexFinset H, (degree H v : ℝ)) ≤
      ((vertexFinset H).card : ℝ) * d := by
    calc
      (∑ v ∈ vertexFinset H, (degree H v : ℝ)) ≤
          ∑ _v ∈ vertexFinset H, d :=
        Finset.sum_le_sum fun v hv => hupper v hv
      _ = ((vertexFinset H).card : ℝ) * d := by simp
  have hhand : (∑ v ∈ vertexFinset H, (degree H v : ℝ)) =
      8 * (H.card : ℝ) := by
    norm_cast
    simpa using sum_degree_vertexFinset_of_uniform hH
  have hHE : (H.card : ℝ) ≤ E * E := by
    have hprod : ((vertexFinset H).card : ℝ) * d ≤ E * E :=
      mul_le_mul hvertex hdexp hd (Real.exp_pos _).le
    rw [hhand] at hsum
    have hcard0 : (0 : ℝ) ≤ (H.card : ℝ) := by positivity
    nlinarith [hsum.trans hprod]
  calc
    (H.card : ℝ) ≤ E * E := hHE
    _ = Real.exp (2 * Real.rpow d (eta ^ 3)) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem restricted_observable_card_bounds
    [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {current : ConflictSystem V}
    {d eta : ℝ} {stage : ℕ}
    (hstage4 : stage ≤ 4)
    (hhost : (H.card : ℝ) ≤ Real.exp (2 * Real.rpow d (eta ^ 3)))
    (hvertex : ((vertexFinset H).card : ℝ) ≤
      Real.exp (Real.rpow d (eta ^ 3)))
    (hfour : 4 ≤ Real.exp (Real.rpow d (eta ^ 3))) :
    (Fintype.card (ConcreteStageDegreeIndex H) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
      (Fintype.card (RestrictedStageLinearUpperIndex H stage) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
      (Fintype.card (StageBlockUpperIndex H current stage) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3)) := by
  let X := Real.rpow d (eta ^ 3)
  let E := Real.exp X
  have hE0 : 0 ≤ E := (Real.exp_pos X).le
  have hE1 : 1 ≤ E := le_trans (by norm_num) hfour
  have hH2 : (H.card : ℝ) ≤ E ^ 2 := by
    simpa [E, X, ← Real.exp_nat_mul] using hhost
  have hV : ((vertexFinset H).card : ℝ) ≤ E := by simpa [E, X] using hvertex
  have hdeg : (Fintype.card (ConcreteStageDegreeIndex H) : ℝ) =
      (H.card : ℝ) := by simp
  have hlinearNat := restrictedStageLinearUpperIndex_card_le H stage hstage4
  have hlinear : (Fintype.card (RestrictedStageLinearUpperIndex H stage) : ℝ) ≤
      (H.card : ℝ) ^ 2 + (H.card : ℝ) ^ 3 +
        (H.card : ℝ) * ((vertexFinset H).card : ℝ) := by exact_mod_cast hlinearNat
  have hpair : (Fintype.card (HostEdgePair H) : ℝ) ≤ (H.card : ℝ) ^ 2 := by
    exact_mod_cast hostEdgePair_card_le_square H
  have hblock : (Fintype.card (StageBlockUpperIndex H current stage) : ℝ) ≤
      2 * (H.card : ℝ) ^ 2 := by
    rw [Fintype.card_sum]
    have hl : Fintype.card (StageC5BlockIndex H stage) ≤
        Fintype.card (HostEdgePair H) := by
      apply Fintype.card_le_of_injective (fun a => a.pair)
      intro a b hab
      cases a
      cases b
      simp_all
    have hr : Fintype.card (StageCommonBlockIndex H current) ≤
        Fintype.card (HostEdgePair H) := by
      apply Fintype.card_le_of_injective (fun a => a.pair)
      intro a b hab
      cases a
      cases b
      simp_all
    have hbNat : Fintype.card (StageC5BlockIndex H stage) +
        Fintype.card (StageCommonBlockIndex H current) ≤ 2 * H.card ^ 2 := by
      calc
        _ ≤ Fintype.card (HostEdgePair H) + Fintype.card (HostEdgePair H) :=
          Nat.add_le_add hl hr
        _ ≤ H.card ^ 2 + H.card ^ 2 :=
          Nat.add_le_add (hostEdgePair_card_le_square H)
            (hostEdgePair_card_le_square H)
        _ = 2 * H.card ^ 2 := by ring
    exact_mod_cast hbNat
  have hE2 : 3 ≤ E ^ 2 := by nlinarith [sq_nonneg (E - 4)]
  have hto8 : E ^ 6 * 3 ≤ E ^ 8 := by
    calc
      E ^ 6 * 3 ≤ E ^ 6 * E ^ 2 :=
        mul_le_mul_of_nonneg_left hE2 (pow_nonneg hE0 6)
      _ = E ^ 8 := by ring
  have hlinE : (H.card : ℝ) ^ 2 + (H.card : ℝ) ^ 3 +
      (H.card : ℝ) * ((vertexFinset H).card : ℝ) ≤ E ^ 6 * 3 := by
    have hH0 : 0 ≤ (H.card : ℝ) := Nat.cast_nonneg _
    have hV0 : 0 ≤ ((vertexFinset H).card : ℝ) := Nat.cast_nonneg _
    have h2 : (H.card : ℝ) ^ 2 ≤ E ^ 4 := by nlinarith [sq_nonneg (E ^ 2 - H.card)]
    have h3 : (H.card : ℝ) ^ 3 ≤ E ^ 6 := by
      have hh := pow_le_pow_left₀ hH0 hH2 3
      calc
        _ ≤ (E ^ 2) ^ 3 := hh
        _ = E ^ 6 := by ring
    have hv : (H.card : ℝ) * ((vertexFinset H).card : ℝ) ≤ E ^ 3 := by
      calc
        _ ≤ E ^ 2 * E := mul_le_mul hH2 hV hV0 (pow_nonneg hE0 2)
        _ = E ^ 3 := by ring
    have h46 : E ^ 4 ≤ E ^ 6 := by
      exact pow_le_pow_right₀ hE1 (by norm_num)
    have h36 : E ^ 3 ≤ E ^ 6 := by
      exact pow_le_pow_right₀ hE1 (by norm_num)
    nlinarith
  have hexp8 : E ^ 8 = Real.exp (8 * X) := by
    dsimp [E]
    exact (Real.exp_nat_mul X 8).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hdeg, ← hexp8]
    exact hH2.trans (pow_le_pow_right₀ hE1 (by norm_num))
  · rw [← hexp8]
    exact hlinear.trans (hlinE.trans hto8)
  · rw [← hexp8]
    have h4to8 : 2 * E ^ 4 ≤ E ^ 8 := by
      have h2E4 : 2 ≤ E ^ 4 := by
        have hE4 : E ≤ E ^ 4 := by
          calc
            E = E ^ 1 := by ring
            _ ≤ E ^ 4 := pow_le_pow_right₀ hE1 (by norm_num)
        exact (by norm_num : (2 : ℝ) ≤ 4).trans (hfour.trans hE4)
      calc
        2 * E ^ 4 ≤ E ^ 4 * E ^ 4 :=
          mul_le_mul_of_nonneg_right h2E4 (pow_nonneg hE0 4)
        _ = E ^ 8 := by ring
    have hHsq : (H.card : ℝ) ^ 2 ≤ E ^ 4 := by
      have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) hH2 2
      calc
        _ ≤ (E ^ 2) ^ 2 := hh
        _ = E ^ 4 := by ring
    exact hblock.trans ((mul_le_mul_of_nonneg_left hHsq (by norm_num)).trans h4to8)

theorem rawSourcePmax_times_power_le
    {d eta n : ℝ} {j : ℕ} (r : ℝ)
    (hj : j ∈ ({2, 3, 4} : Finset ℕ))
    (hd : 1 ≤ d) (hn : 0 < n) (hdn : d ≤ n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n) :
    Real.rpow d r * rawSourcePmax d eta n j ≤
      32 * Real.rpow d (r + 10 * rawRegularizationEps eta - eta) := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hp := rawSourcePmax_le_basic hj hd hn hdn hhost
  calc
    Real.rpow d r * rawSourcePmax d eta n j ≤
        Real.rpow d r *
          (32 * Real.rpow d (10 * rawRegularizationEps eta - eta)) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hd0.le _)
    _ = 32 * (Real.rpow d r *
        Real.rpow d (10 * rawRegularizationEps eta - eta)) := by ring
    _ = 32 * Real.rpow d (r + 10 * rawRegularizationEps eta - eta) := by
      exact congrArg (fun z => 32 * z) <| by
        change d ^ r * d ^ (10 * rawRegularizationEps eta - eta) =
          d ^ (r + 10 * rawRegularizationEps eta - eta)
        rw [← Real.rpow_add hd0]
        congr 1
        ring

theorem rawSourcePmax_blockMean_le
    {d eta n Gamma : ℝ} {j : ℕ}
    (hj : j ∈ ({2, 3, 4} : Finset ℕ))
    (hd : 1 ≤ d) (hn : 0 < n) (hdn : d ≤ n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (heta : 0 ≤ eta) (hGamma : 0 ≤ Gamma) :
    2 * (Gamma * Real.rpow d ((j : ℝ) - 1)) *
          rawSourcePmax d eta n j +
        n ^ (j - 1) * rawSourcePmax d eta n j ^ 2 ≤
      32 * (4 * Gamma + 1) * Real.rpow d
        ((j : ℝ) - 1 + 20 * rawRegularizationEps eta - eta) := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  let a := Real.rpow d
    ((j : ℝ) - 1 + 10 * rawRegularizationEps eta - eta)
  let b := Real.rpow d
    ((j : ℝ) - 1 + 20 * rawRegularizationEps eta - eta)
  have hab : a ≤ b := by
    dsimp [a, b]
    apply Real.rpow_le_rpow_of_exponent_le hd
    have heps : 0 ≤ rawRegularizationEps eta := by
      simp [rawRegularizationEps]
      linarith
    linarith
  have hfirst0 := rawSourcePmax_times_power_le
    ((j : ℝ) - 1) hj hd hn hdn hhost
  have hfirst :
      2 * (Gamma * Real.rpow d ((j : ℝ) - 1)) *
          rawSourcePmax d eta n j ≤ 64 * Gamma * b := by
    calc
      _ = 2 * Gamma * (Real.rpow d ((j : ℝ) - 1) *
          rawSourcePmax d eta n j) := by ring
      _ ≤ 2 * Gamma * (32 * a) := by
        exact mul_le_mul_of_nonneg_left hfirst0 (mul_nonneg (by norm_num) hGamma)
      _ ≤ 2 * Gamma * (32 * b) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hab (by norm_num))
          (mul_nonneg (by norm_num) hGamma)
      _ = 64 * Gamma * b := by ring
  have hsquare := rawSourcePmax_sq_hostPower_le hj hd hn hdn hhost
  have hsquare' : n ^ (j - 1) * rawSourcePmax d eta n j ^ 2 ≤ 32 * b := by
    simpa [b] using hsquare
  calc
    _ ≤ 64 * Gamma * b + 32 * b := add_le_add hfirst hsquare'
    _ ≤ 32 * (4 * Gamma + 1) * b := by
      have hb0 : 0 ≤ b := Real.rpow_nonneg hd0.le _
      nlinarith

theorem rawSourcePmax_c4Mean_le
    {d eta n : ℝ}
    (hd : 1 ≤ d) (hn : 0 < n) (hdn : d ≤ n)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n) :
    d * rawSourcePmax d eta n 2 ≤
      32 * Real.rpow d (1 + 10 * rawRegularizationEps eta - eta) := by
  simpa [Real.rpow_one] using
    (rawSourcePmax_times_power_le (d := d) (eta := eta) (n := n)
      (j := 2) 1 (by simp) hd hn hdn hhost)

theorem rawSource_propertyI_degreeRoom_coarse
    {j : ℕ} (hj : j ∈ ({2, 3, 4} : Finset ℕ))
    {d n eta Gamma A B total pmax : ℝ} {m : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpmax0 : 0 ≤ pmax)
    (hhost : Real.rpow d (1 + eta) / 32 ≤ n)
    (htotal : n * Real.rpow d
      ((j : ℝ) - 1 - 2 * rawRegularizationEps eta) ≤ total)
    (hcard : (m : ℝ) ≤ rawForbiddenCoeff A B j * d * n ^ (j - 2))
    (hpmax : pmax ≤ rawSourcePmax d eta n j)
    (hcut : RawSourceCutoffSpec eta Gamma A B d) :
    12 * (4 * Gamma * Real.rpow d ((j : ℝ) - 1)) ^ 2 / total +
        (m : ℝ) * pmax ≤
      2 * Real.rpow d
        ((j : ℝ) - 1 - 2 * rawRegularizationEps eta) := by
  have hj2 : 2 ≤ j := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> norm_num
  have hK : 0 ≤ rawForbiddenCoeff A B j := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;>
      simp [rawForbiddenCoeff] <;> positivity
  have hKabsorb : 32 * rawForbiddenCoeff A B j ≤
      Real.rpow d (eta - 12 * rawRegularizationEps eta) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact hcut.forbiddenTwo
    · exact hcut.forbiddenThree
    · exact hcut.forbiddenFour
  have hsym := symmetricMass_absorbed_rawSource
    (j := j) hd hn hhost htotal hcut.symmetricRoom
  have hforbidden := forbiddenMass_absorbed_rawSource hj2 hd hK hpmax0
    hcard hpmax hhost hKabsorb
  linarith

theorem degreeDeficit_strong_lower_of_layer_subset
    {H : Hypergraph V} {base current : ConflictSystem V}
    {d eps : ℝ} {stage : ℕ}
    (hd : 1 ≤ d)
    (hcurrent : conflictLayer current stage ⊆ conflictLayer base stage)
    (e : ConcreteStageDegreeIndex H) :
    Real.rpow d ((stage : ℝ) - 1 - eps / 4 - eps / 600) ≤
      degreeDeficit current stage
        (completionTarget d eps (layerMaxDegree H base stage : ℝ) stage) e.1 := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  let baseline := Real.rpow d ((stage : ℝ) - 1 - eps / 600)
  let delta : ℝ := layerMaxDegree H base stage
  let t := Real.rpow d (-eps / 4)
  let m := max baseline delta
  have ht0 : 0 ≤ t := Real.rpow_nonneg hd0.le _
  have hdeg : (degree (conflictLayer current stage) e.1 : ℝ) ≤ m := by
    calc
      _ ≤ (degree (conflictLayer base stage) e.1 : ℝ) := by
        exact_mod_cast degree_mono hcurrent e.1
      _ ≤ delta := by
        dsimp [delta]
        exact_mod_cast degree_layer_le_layerMaxDegree e.2
      _ ≤ m := le_max_right _ _
  have htb : t * baseline =
      Real.rpow d ((stage : ℝ) - 1 - eps / 4 - eps / 600) := by
    dsimp [t, baseline]
    change d ^ (-eps / 4) * d ^ ((stage : ℝ) - 1 - eps / 600) = _
    rw [← Real.rpow_add hd0]
    congr 1
    ring
  rw [← htb]
  calc
    t * baseline ≤ t * m := mul_le_mul_of_nonneg_left (le_max_left _ _) ht0
    _ = (1 + t) * m - m := by ring
    _ ≤ (1 + t) * m - (degree (conflictLayer current stage) e.1 : ℝ) :=
      sub_le_sub_left hdeg _
    _ = degreeDeficit current stage
        (completionTarget d eps (layerMaxDegree H base stage : ℝ) stage) e.1 := rfl

theorem RawEndpointCutoffSpec.degreeErrorRoom_le_halfStrong
    {eta d : ℝ} (h : RawEndpointCutoffSpec eta d)
    (hd : 1 ≤ d) (stage : ℕ) :
    2 * Real.rpow d ((stage : ℝ) - 1 - 2 * rawRegularizationEps eta) ≤
      Real.rpow d ((stage : ℝ) - 1 - rawRegularizationEps eta / 4 -
        rawRegularizationEps eta / 600) / 2 := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  let p := Real.rpow d ((stage : ℝ) - 1)
  have hp0 : 0 ≤ p := Real.rpow_nonneg hd0.le _
  have hm := mul_le_mul_of_nonneg_left h.degreeError hp0
  have hleft : p * (4 * Real.rpow d (-2 * rawRegularizationEps eta)) =
      4 * Real.rpow d ((stage : ℝ) - 1 - 2 * rawRegularizationEps eta) := by
    dsimp [p]
    calc
      Real.rpow d ((stage : ℝ) - 1) *
          (4 * Real.rpow d (-2 * rawRegularizationEps eta)) =
          4 * (Real.rpow d ((stage : ℝ) - 1) *
            Real.rpow d (-2 * rawRegularizationEps eta)) := by ring
      _ = 4 * Real.rpow d
          ((stage : ℝ) - 1 - 2 * rawRegularizationEps eta) := by
        exact congrArg (fun z => 4 * z) <| by
          change d ^ ((stage : ℝ) - 1) * d ^ (-2 * rawRegularizationEps eta) = _
          rw [← Real.rpow_add hd0]
          congr 1
          ring
  have hright : p * Real.rpow d
      (-rawRegularizationEps eta / 4 - rawRegularizationEps eta / 600) =
      Real.rpow d ((stage : ℝ) - 1 - rawRegularizationEps eta / 4 -
        rawRegularizationEps eta / 600) := by
    dsimp [p]
    change d ^ ((stage : ℝ) - 1) *
      d ^ (-rawRegularizationEps eta / 4 - rawRegularizationEps eta / 600) = _
    rw [← Real.rpow_add hd0]
    congr 1
    ring
  rw [hleft, hright] at hm
  linarith

theorem RawEndpointCutoffSpec.degreeFailureScale
    {eta d : ℝ} (h : RawEndpointCutoffSpec eta d)
    (hd : 1 ≤ d) {stage : ℕ} (hstage : 2 ≤ stage) :
    Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
      Real.rpow d (-rawRegularizationEps eta) ^ 2 *
        Real.rpow d ((stage : ℝ) - 1 - rawRegularizationEps eta / 4 -
          rawRegularizationEps eta / 600) / 8 := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hstageCast : (2 : ℝ) ≤ (stage : ℝ) := by exact_mod_cast hstage
  have hstageR : (1 : ℝ) ≤ (stage : ℝ) - 1 := by linarith
  have hmono : Real.rpow d
      (1 - 1351 * rawRegularizationEps eta / 600) ≤
      Real.rpow d ((stage : ℝ) - 1 -
        1351 * rawRegularizationEps eta / 600) :=
    Real.rpow_le_rpow_of_exponent_le hd (by linarith)
  have h8 := h.degreeFailure.trans hmono
  have hid : Real.rpow d (-rawRegularizationEps eta) ^ 2 *
        Real.rpow d ((stage : ℝ) - 1 - rawRegularizationEps eta / 4 -
          rawRegularizationEps eta / 600) / 8 =
      Real.rpow d ((stage : ℝ) - 1 -
        1351 * rawRegularizationEps eta / 600) / 8 := by
    have hsquare : (Real.rpow d (-rawRegularizationEps eta)) ^ 2 =
        Real.rpow d (-2 * rawRegularizationEps eta) := by
      calc
        _ = Real.rpow (Real.rpow d (-rawRegularizationEps eta)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Real.rpow d ((-rawRegularizationEps eta) * 2) :=
          (Real.rpow_mul hd0.le _ 2).symm
        _ = _ := by congr 1 <;> ring
    have hmul : Real.rpow d (-2 * rawRegularizationEps eta) *
        Real.rpow d ((stage : ℝ) - 1 - rawRegularizationEps eta / 4 -
          rawRegularizationEps eta / 600) =
        Real.rpow d ((stage : ℝ) - 1 -
          1351 * rawRegularizationEps eta / 600) := by
      change d ^ (-2 * rawRegularizationEps eta) *
          d ^ ((stage : ℝ) - 1 - rawRegularizationEps eta / 4 -
            rawRegularizationEps eta / 600) = _
      rw [← Real.rpow_add hd0]
      congr 1
      ring
    calc
      Real.rpow d (-rawRegularizationEps eta) ^ 2 *
            Real.rpow d ((stage : ℝ) - 1 - rawRegularizationEps eta / 4 -
              rawRegularizationEps eta / 600) / 8 =
          (Real.rpow d (-rawRegularizationEps eta) ^ 2 *
            Real.rpow d ((stage : ℝ) - 1 - rawRegularizationEps eta / 4 -
              rawRegularizationEps eta / 600)) / 8 := by ring
      _ = _ := by rw [hsquare, hmul]
  rw [hid]
  have hx : Real.rpow d (1 - 10 * rawRegularizationEps eta) ≤
      Real.rpow d ((stage : ℝ) - 1 -
        1351 * rawRegularizationEps eta / 600) / 32 := by
    exact (le_div_iff₀' (by norm_num : (0 : ℝ) < 32)).2 h8
  have hpow0 : 0 ≤ Real.rpow d ((stage : ℝ) - 1 -
      1351 * rawRegularizationEps eta / 600) := Real.rpow_nonneg hd0.le _
  nlinarith

theorem exists_rawRegularizationStage_nonempty
    {ι : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    {ellTrack : ℕ}
    (H : Hypergraph V) (base current : ConflictSystem V)
    (hcurrentSys : IsConflictSystem H current)
    (hHuniform : IsUniform H 8)
    (d eta etaTrack Gamma : ℝ) (stage : ℕ)
    (hdegreeUpper : ∀ v ∈ vertexFinset H, (degree H v : ℝ) ≤ d)
    (testJ : ι → ℕ) (w : ι → TestWeight V)
    (hH : H.Nonempty) (heta : 0 < eta)
    (hstage : stage ∈ ({2, 3, 4} : Finset ℕ))
    (hGamma : 1 ≤ Gamma)
    (hcurrentLayer : conflictLayer current stage ⊆ conflictLayer base stage)
    (hbaseLayer : (layerMaxDegree H base stage : ℝ) ≤
      Gamma * Real.rpow d ((stage : ℝ) - 1))
    (hforbidden : ∀ e : ConcreteStageDegreeIndex H,
      ((forbiddenIncidentCompletions H current stage e.1).card : ℝ) ≤
        rawForbiddenCoeff 1 (4 * Gamma) stage * d *
          (H.card : ℝ) ^ (stage - 2))
    (hdef : HasSourceDeficitBoundsAtTarget H current d
      (rawRegularizationEps eta) Gamma
      (completionTarget d (rawRegularizationEps eta)
        (layerMaxDegree H base stage : ℝ) stage) stage)
    (hstrong : ∀ e : ConcreteStageDegreeIndex H,
      Real.rpow d ((stage : ℝ) - 1 - rawRegularizationEps eta / 4 -
        rawRegularizationEps eta / 600) ≤
      degreeDeficit current stage
        (completionTarget d (rawRegularizationEps eta)
          (layerMaxDegree H base stage : ℝ) stage) e.1)
    (holdII : ∀ root : StageCodegreeIndex V stage,
      (codegree (conflictLayer current stage) root.1 : ℝ) ≤
        Real.rpow d ((stage : ℝ) - (root.1.card : ℝ) -
          rawRegularizationEps eta / 3))
    (holdIII : ∀ (hs : stage = 2) (e : Finset V) (he : e ∈ H) (v : V),
      (conditionC4Count H current e v : ℝ) ≤
        Real.rpow d (1 - rawRegularizationEps eta / 3))
    (holdIV : ∀ (hs : stage = 2) (e : Finset V) (he : e ∈ H)
      (f : Finset V) (hf : f ∈ H) (hdisj : Disjoint e f),
      (conditionC5Count H current e f : ℝ) ≤
        Real.rpow d (1 - rawRegularizationEps eta / 3))
    (holdV : ∀ (e : Finset V) (he : e ∈ H)
      (f : Finset V) (hf : f ∈ H) (hdisj : Disjoint e f)
      (hnot : {e, f} ∉ conflictLayer current 2),
      (((conflictLinkLayer current e (stage - 1) ∩
        conflictLinkLayer current f (stage - 1)).card : ℕ) : ℝ) ≤
          Real.rpow d (((stage - 1 : ℕ) : ℝ) -
            rawRegularizationEps eta / 3))
    (htrack : ∀ a, IsTrackable H current (testJ a) ellTrack d etaTrack (w a))
    (hj : ∀ a, 1 ≤ testJ a ∧ testJ a ≤ 3)
    (hetaTrack : rawRegularizationEps eta / 5 ≤ etaTrack)
    (hreg : RawRegularizationCutoffSpec ellTrack eta d)
    (hsource : RawSourceCutoffSpec eta Gamma 1 (4 * Gamma) d)
    (hobs : RawObservableCutoffSpec eta Gamma 8 d)
    (htransfer : RawTransferCutoffSpec eta 32 d)
    (hendpoint : RawEndpointCutoffSpec eta d)
    (hhostLower : Real.rpow d (1 + eta) / 32 ≤ (H.card : ℝ))
    (hcards :
      (Fintype.card (ConcreteStageDegreeIndex H) : ℝ) ≤
          Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
        (Fintype.card (RestrictedStageLinearUpperIndex H stage) : ℝ) ≤
          Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
        (Fintype.card (StageBlockUpperIndex H current stage) : ℝ) ≤
          Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
        (Fintype.card (ActiveStageTest H current stage testJ w) : ℝ) ≤
          Real.exp (8 * Real.rpow d (eta ^ 3))) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H current stage ∧
      HasStagePropertiesIV H base (addCompletionLayer current A) d
        (rawRegularizationEps eta) stage ∧
      ∀ a, killedWeight H (addCompletionLayer current A) (testJ a) (w a) <
        stageKilledWeightLimit stage d (rawRegularizationEps eta)
          (testTotal (w a) H (testJ a)) := by
  have hi : (inferInstance : DecidableEq V) = @Classical.decEq V :=
    Subsingleton.elim _ _
  cases hi
  letI : DecidableEq V := @Classical.decEq V
  let eps := rawRegularizationEps eta
  let n : ℝ := H.card
  let target := completionTarget d eps (layerMaxDegree H base stage : ℝ) stage
  let pmax := rawSourcePmax d eta n stage
  let err := Real.rpow d (-eps)
  let room := 2 * Real.rpow d ((stage : ℝ) - 1 - 2 * eps)
  let delta : ConcreteStageDegreeIndex H → ℝ := fun _ => err / 2
  let linearThreshold : RestrictedStageLinearUpperIndex H stage → ℝ :=
    fun a => rawLinearObservableThreshold H d eta stage
      (restrictedStageLinearToFull H stage a)
  let blockThreshold : StageBlockUpperIndex H current stage → ℝ :=
    rawBlockObservableThreshold H current d eta stage
  let gap : ι → ℝ := fun a =>
    stageKilledWeightGap stage d eps (testTotal (w a) H (testJ a))
  let limit : ι → ℝ := fun a =>
    stageKilledWeightLimit stage d eps (testTotal (w a) H (testJ a))
  have hd : 1 ≤ d := hsource.degreeAtLeastOne
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Finset.card_pos.mpr hH
  have hdn : d ≤ n := rawSource_degree_le_host hd0 hhostLower hsource
  have heta0 : 0 ≤ eta := heta.le
  have heps : 0 < eps := by simp [eps, rawRegularizationEps, heta]
  have hstage2 : 2 ≤ stage := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hstage
    rcases hstage with rfl | rfl | rfl <;> norm_num
  have hstage4 : stage ≤ 4 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hstage
    rcases hstage with rfl | rfl | rfl <;> norm_num
  have hprobSpec : RawSourceProbabilitySpec d eta n Gamma stage :=
    rawSourceProbabilitySpec_of_cutoff hstage hd0 hn hhostLower hsource
  have hpmax0 : 0 ≤ pmax := by
    exact rawSourcePmax_nonneg d eta n stage hd0.le hn.le
  have hpmaxOne : pmax ≤ 1 := hprobSpec.pmaxAtMostOne
  have hpmaxBasic : pmax ≤ 32 * Real.rpow d (-eta + 10 * eps) := by
    have hp := rawSourcePmax_le_basic hstage hd hn hdn hhostLower
    calc
      pmax ≤ 32 * Real.rpow d (10 * eps - eta) := by
        simpa [pmax, n, eps] using hp
      _ = 32 * Real.rpow d (-eta + 10 * eps) := by congr 2 <;> ring
  have hweightMax : ∀ A ∈ H.powersetCard stage,
      completionWeight H stage (degreeDeficit current stage target) A ≤ pmax := by
    intro A hA
    exact (completionWeight_le_sourcePmax H current d eps Gamma target stage
      hH hd0 (zero_le_one.trans hGamma) hdef A hA).trans hprobSpec.sourceExpressionBound
  have hp : ∀ i, sourceCompletionBiasAtTarget H current stage target i ∈
      Set.Icc (0 : ℝ) 1 := by
    apply sourceCompletionBiasAtTarget_mem_Icc_of_sourcePmax_le_one
      H current d eps Gamma target stage hH hd0 (zero_le_one.trans hGamma) hdef
    exact hprobSpec.sourceExpressionBound.trans hpmaxOne
  have hpmax : ∀ i, sourceCompletionBiasAtTarget H current stage target i ≤ pmax := by
    intro i
    exact (sourceCompletionBiasAtTarget_le_sourcePmax H current d eps Gamma
      target stage hH hd0 (zero_le_one.trans hGamma) hdef i).trans
        hprobSpec.sourceExpressionBound
  have htotal := totalDeficit_lower_of_sourceBounds H current d eps Gamma
    target stage hdef
  have hroom : ∀ e : ConcreteStageDegreeIndex H,
      12 * (4 * Gamma * Real.rpow d ((stage : ℝ) - 1)) ^ 2 /
          totalDeficit H (degreeDeficit current stage target) +
        ((forbiddenIncidentCompletions H current stage e.1).card : ℝ) * pmax ≤
          room := by
    intro e
    apply rawSource_propertyI_degreeRoom_coarse hstage hd0 hn (by norm_num)
      (mul_nonneg (by norm_num) (zero_le_one.trans hGamma)) hpmax0 hhostLower
      htotal (hforbidden e) le_rfl hsource
  have hmeanRoom : ∀ e : ConcreteStageDegreeIndex H,
      |(degree (conflictLayer current stage) e.1 : ℝ) +
          ChernoffFinite.bitMean
            (sourceCompletionBiasAtTarget H current stage target)
            (concreteStageDegreeActive H current stage e) - target| ≤ room := by
    intro e
    exact sourceIncidentMean_room H current d eps Gamma target pmax room stage
      hH hd0 (zero_le_one.trans hGamma) hdef hprobSpec.sourceExpressionBound
      e.1 e.2 (hroom e)
  have hstrong' : ∀ e : ConcreteStageDegreeIndex H,
      Real.rpow d ((stage : ℝ) - 1 - eps / 4 - eps / 600) ≤
        degreeDeficit current stage target e.1 := by
    intro e
    simpa [eps, target] using hstrong e
  have hroomStrong : room ≤
      Real.rpow d ((stage : ℝ) - 1 - eps / 4 - eps / 600) / 2 := by
    simpa [room, eps] using hendpoint.degreeErrorRoom_le_halfStrong hd stage
  have hroomTarget : room ≤ err * target / 32 := by
    simpa [room, err, target, eps] using
      (two_rawSourceMasses_fit_degreeRoom (j := stage)
        (layerDelta := (layerMaxDegree H base stage : ℝ)) hd0 hsource.finalDegreeRoom)
  have hmargin : ∀ e : ConcreteStageDegreeIndex H,
      delta e * ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (concreteStageDegreeActive H current stage e) ≤
        err * target - room := by
    intro e
    apply halfRelativeDeviation_fits_margin
    · exact Real.rpow_nonneg hd0.le _
    · exact Real.rpow_le_one_of_one_le_of_nonpos hd (by linarith)
    · dsimp [room]
      positivity
    · exact hroomTarget.trans (by
        have hnonneg : 0 ≤ err * target := by
          dsimp [err, target, completionTarget]
          positivity
        nlinarith)
    · exact hmeanRoom e
  have hdelta0 : ∀ e, 0 ≤ delta e := by
    intro e
    dsimp [delta, err]
    positivity
  have hdelta1 : ∀ e, delta e ≤ 1 := by
    intro e
    dsimp [delta, err]
    have herr1 := Real.rpow_le_one_of_one_le_of_nonpos hd
      (show -eps ≤ 0 by linarith)
    have herr0 := Real.rpow_nonneg hd0.le (-eps)
    nlinarith
  have hdegreeFailure : ∀ e : ConcreteStageDegreeIndex H,
      Real.rpow d (1 - 10 * eps) ≤
        delta e ^ 2 * ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (concreteStageDegreeActive H current stage e) := by
    intro e
    have hchern := sourceIncident_chernoffExponent_lower
      (err := err) (room := room)
      (L := Real.rpow d ((stage : ℝ) - 1 - eps / 4 - eps / 600))
      (e := e.1) (Real.rpow_nonneg hd0.le _) (hstrong' e) hroomStrong
      (hmeanRoom e)
    have hscale := hendpoint.degreeFailureScale hd hstage2
    simpa [delta, err, eps, concreteStageDegreeActive] using hscale.trans hchern
  have hlinearMeanFull : ∀ a : StageLinearUpperIndex H stage,
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (stageLinearUpperActive H current stage a) ≤
        hostBoundLinearUpperThreshold H stage n d pmax a := by
    apply stageLinearUpperMean_le_hostBoundThreshold H current stage target pmax n d
      hpmax0
    · rfl
    · intro v
      by_cases hv : v ∈ vertexFinset H
      · exact hdegreeUpper v hv
      · rw [degree_eq_zero_of_not_mem_vertexFinset hv]
        simpa using hd0.le
    · exact hpmax
  have hlinearMean : ∀ a,
      ChernoffFinite.bitMean
          (sourceCompletionBiasAtTarget H current stage target)
          (restrictedStageLinearUpperActive H current stage a) ≤
        linearThreshold a := by
    intro a
    apply (hlinearMeanFull (restrictedStageLinearToFull H stage a)).trans
    apply hobs.rawLinearThreshold_dominates H stage
      (hostBoundLinearUpperThreshold H stage n d pmax)
    · intro root
      simp only [hostBoundLinearUpperThreshold]
      exact rawSourcePmax_codegreeMean_le (by omega) (by omega) (by omega)
        (by omega) hd hn hdn hhostLower
    · intro c4
      rcases c4 with ⟨edge, hedge, vertex, rfl⟩
      simp only [hostBoundLinearUpperThreshold]
      exact rawSourcePmax_c4Mean_le hd hn hdn hhostLower
  have hlinear0 : ∀ a, 0 ≤ linearThreshold a := by
    intro a
    dsimp [linearThreshold, rawLinearObservableThreshold]
    rcases restrictedStageLinearToFull H stage a with root | c4 <;> positivity
  have hcurrentDegree : ∀ e ∈ H,
      (degree (conflictLayer current stage) e : ℝ) ≤
        Gamma * Real.rpow d ((stage : ℝ) - 1) := by
    intro e he
    calc
      _ ≤ (degree (conflictLayer base stage) e : ℝ) := by
        exact_mod_cast degree_mono hcurrentLayer e
      _ ≤ (layerMaxDegree H base stage : ℝ) := by
        exact_mod_cast degree_layer_le_layerMaxDegree he
      _ ≤ _ := hbaseLayer
  have hhostNonempty : ∀ e ∈ H, e.Nonempty := by
    intro e he
    have hcard := hHuniform e he
    rw [Finset.nonempty_iff_ne_empty]
    intro hz
    simp [hz] at hcard
  have hblockMeanFull : ∀ a,
      BlockChernoff.blockMean
          (sourceCompletionBiasAtTarget H current stage target)
          (stageBlockFamily H current stage a) ≤
        hostBoundBlockUpperThreshold H current stage n
          (Gamma * Real.rpow d ((stage : ℝ) - 1)) pmax a := by
    apply stageBlockUpperMean_le_hostBoundThreshold H current hcurrentSys
      hhostNonempty stage (by omega) target pmax n
      (Gamma * Real.rpow d ((stage : ℝ) - 1)) hp hpmax hpmax0 le_rfl
      hcurrentDegree
  have hblockMean : ∀ a,
      BlockChernoff.blockMean
          (sourceCompletionBiasAtTarget H current stage target)
          (concreteStageBlockFamily H current stage a) ≤ blockThreshold a := by
    intro a
    rw [show concreteStageBlockFamily H current stage a =
      stageBlockFamily H current stage a from rfl]
    apply (hblockMeanFull a).trans
    apply hobs.rawBlockThreshold_dominates H current stage
      (hostBoundBlockUpperThreshold H current stage n
        (Gamma * Real.rpow d ((stage : ℝ) - 1)) pmax)
    intro b
    simp only [hostBoundBlockUpperThreshold]
    have hcast : (((stage - 1 : ℕ) : ℝ)) = (stage : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ stage by omega)]
      norm_num
    simpa [hcast] using
      (rawSourcePmax_blockMean_le hstage hd hn hdn hhostLower heta.le
        (zero_le_one.trans hGamma))
  have hblock0 : ∀ a, 0 ≤ blockThreshold a := by
    intro a
    dsimp [blockThreshold, rawBlockObservableThreshold]
    positivity
  have hII : RestrictedPropertyIIRoom H current d eps stage linearThreshold := by
    intro root
    let full : StageCodegreeIndex V stage := ⟨root.1, root.2.2⟩
    simpa [linearThreshold, restrictedStageLinearToFull, full] using
      (hobs.rawPropertyIIRoom H current stage holdII full)
  have hIII : RestrictedPropertyIIIRoom H current d eps stage linearThreshold := by
    intro c4
    exact hobs.rawPropertyIIIRoom H current stage holdIII
      c4.stage_eq c4.edge c4.edge_mem c4.vertex
  have hIV : PropertyIVRoom H current d eps stage blockThreshold := by
    exact hobs.rawPropertyIVRoom H current stage holdIV
  have hV : PropertyVRoom H current d eps stage blockThreshold := by
    exact hobs.rawPropertyVRoom H current stage holdV
  have hw0 : ∀ a S, 0 ≤ w a S := fun a => (htrack a).1.1
  have hfreeZero : ∀ a S, S ∈ H.powersetCard (testJ a) →
      (∃ c ∈ current, c ⊆ S) → w a S = 0 := by
    intro a S hS hcontains
    exact (htrack a).eq_zero_of_contains_conflict hS hcontains
  have hgap0 : ∀ a : ActiveStageTest H current stage testJ w, 0 ≤ gap a.1 := by
    intro a
    apply stageKilledWeightGap_nonneg
    · exact hd0
    · exact testTotal_nonneg (hw0 a.1) H (testJ a.1)
  have hlimitPos : ∀ a, 0 < limit a := by
    intro a
    dsimp [limit, stageKilledWeightLimit]
    have ht : 0 < testTotal (w a) H (testJ a) :=
      (Real.rpow_pos_of_pos hd0 ((testJ a : ℝ) + etaTrack)).trans_le
        (htrack a).2.1
    positivity
  have hcoefficient : 16 * pmax ≤ (4 : ℝ) ^ stage /
      (2 * Real.rpow d (2 * eps)) := by
    exact htransfer.sourceKilledCoefficient hd0 hstage2 hpmax0
      (by simpa [pmax, eps] using hpmaxBasic)
  have hkillRoom : ∀ a : ActiveStageTest H current stage testJ w,
      (∑ i, pmax * testExtension (w a.1) H (testJ a.1)
          (completionCandidate H current stage i)) + gap a.1 ≤ limit a.1 := by
    intro a
    have hsumExt := sum_testExtension_le_two_pow_mul_total H (testJ a.1) (w a.1)
      (completionCandidate H current stage)
      (completionCandidate_injective H current stage) (hw0 a.1)
    have hpow : (2 : ℝ) ^ testJ a.1 ≤ 16 :=
      two_pow_le_sixteen_of_le_four (testJ a.1)
        ((hj a.1).2.trans (by norm_num))
    have htotal0 : 0 ≤ testTotal (w a.1) H (testJ a.1) :=
      testTotal_nonneg (hw0 a.1) H (testJ a.1)
    have hsum : (∑ i, pmax * testExtension (w a.1) H (testJ a.1)
          (completionCandidate H current stage i)) ≤
        16 * pmax * testTotal (w a.1) H (testJ a.1) := by
      rw [← Finset.mul_sum]
      calc
        pmax * ∑ i, testExtension (w a.1) H (testJ a.1)
              (completionCandidate H current stage i) ≤
            pmax * ((2 : ℝ) ^ testJ a.1 *
              testTotal (w a.1) H (testJ a.1)) :=
          mul_le_mul_of_nonneg_left hsumExt hpmax0
        _ ≤ pmax * (16 * testTotal (w a.1) H (testJ a.1)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow htotal0) hpmax0
        _ = _ := by ring_nf
    have hmean : 16 * pmax * testTotal (w a.1) H (testJ a.1) ≤ gap a.1 := by
      have hc := mul_le_mul_of_nonneg_right hcoefficient htotal0
      dsimp [gap, stageKilledWeightGap, stageKilledWeightLimit]
      simp only [Real.rpow_eq_pow] at hc ⊢
      calc
        _ ≤ (4 : ℝ) ^ stage / (2 * d ^ (2 * eps)) *
            testTotal (w a.1) H (testJ a.1) := hc
        _ = _ := by ring
    calc
      _ ≤ gap a.1 + gap a.1 := add_le_add (hsum.trans hmean) le_rfl
      _ = limit a.1 := by unfold gap limit stageKilledWeightGap; ring
  have hlinearFailure : ∀ a,
      Real.rpow d (1 - 10 * eps) ≤ linearThreshold a := by
    intro a
    exact hobs.rawLinearThreshold_failureScale H stage
      (restrictedStageLinearToFull H stage a)
  have hblockFailure : ∀ a,
      Real.rpow d (1 - 10 * eps) ≤ blockThreshold a := by
    exact hobs.rawBlockThreshold_failureScale H current stage hstage2
  have htestFailure : ∀ a : ActiveStageTest H current stage testJ w,
      Real.rpow d (1 - 10 * eps) / 3 ≤
        2 * gap a.1 ^ 2 /
          ∑ i, testExtension (w a.1) H (testJ a.1)
            (completionCandidate H current stage i) ^ 2 := by
    intro a
    obtain ⟨hstageJ, hinflPos⟩ := activeStageTest_property
      H current stage testJ w a
    have habsorb : 8 * (ellTrack : ℝ) * d ≤
        Real.rpow d ((stage : ℝ) + etaTrack) :=
      hreg.testInfluence.trans
        (Real.rpow_le_rpow_of_exponent_le hd (by
          have hsreal : (2 : ℝ) ≤ (stage : ℝ) := by exact_mod_cast hstage2
          linarith))
    have hinfl := trackable_sum_sq_completionCandidate_le_total_sq_div_d_of_ell
      H current current (testJ a.1) ellTrack stage d etaTrack (w a.1)
      (htrack a.1) ((by norm_num : 1 ≤ 4).trans hreg.rankAtLeastFour) hd0
      ((by norm_num : 1 ≤ 2).trans hstage2) (hj a.1).2 habsorb
    have htpos : 0 < testTotal (w a.1) H (testJ a.1) :=
      (Real.rpow_pos_of_pos hd0 ((testJ a.1 : ℝ) + etaTrack)).trans_le
        (htrack a.1).2.1
    have hscale := stageKilledWeightGap_mcdiarmid_scale_relaxed (eps := eps) stage hd0
      htpos hinflPos hinfl
    have hpowmono : Real.rpow d (1 - 10 * eps) ≤
        Real.rpow d (1 - 4 * eps) :=
      Real.rpow_le_rpow_of_exponent_le hd (by linarith)
    have hcoef : (1 / 3 : ℝ) ≤ (4 : ℝ) ^ stage / 2 := by
      have hp4 : (16 : ℝ) ≤ (4 : ℝ) ^ stage := by
        calc
          16 = (4 : ℝ) ^ 2 := by norm_num
          _ ≤ _ := pow_le_pow_right₀ (by norm_num) hstage2
      nlinarith
    calc
      Real.rpow d (1 - 10 * eps) / 3 =
          Real.rpow d (1 - 10 * eps) * (1 / 3) := by ring
      _ ≤ Real.rpow d (1 - 4 * eps) * (1 / 3) :=
        mul_le_mul_of_nonneg_right hpowmono (by norm_num)
      _ ≤ Real.rpow d (1 - 4 * eps) * ((4 : ℝ) ^ stage / 2) :=
        mul_le_mul_of_nonneg_left hcoef (Real.rpow_nonneg hd0.le _)
      _ = ((4 : ℝ) ^ stage / 2) * Real.rpow d (1 - 4 * eps) := mul_comm _ _
      _ ≤ _ := by simpa [gap] using hscale
  have hfail := hobs.fourFamilyFailure delta
    (fun e => ChernoffFinite.bitMean
      (sourceCompletionBiasAtTarget H current stage target)
      (concreteStageDegreeActive H current stage e))
    linearThreshold blockThreshold
    (fun a : ActiveStageTest H current stage testJ w => gap a.1)
    (fun a : ActiveStageTest H current stage testJ w =>
      ∑ i, testExtension (w a.1) H (testJ a.1)
        (completionCandidate H current stage i) ^ 2)
    hcards.1 hcards.2.1 hcards.2.2.1 hcards.2.2.2
    hdegreeFailure hlinearFailure hblockFailure htestFailure
  exact exists_concreteRegularizationStageRestrictedActive_nonempty
    H base current hcurrentSys d eps Gamma stage target pmax delta
    (fun _ => room) linearThreshold blockThreshold testJ w gap limit hH hd0
    (zero_le_one.trans hGamma) rfl hdef hweightMax hpmaxOne hroom hmargin
    hdelta0 hdelta1 hlinear0 hlinearMean hblock0 hblockMean hII hIII hIV hV
    hw0 hfreeZero hgap0 hlimitPos hkillRoom hfail

end
end Erdos136.CFMRegularization

namespace Erdos136.CFMRegularization

variable {V : Type*} [DecidableEq V] [Fintype V]

attribute [local instance] Classical.propDecidable

noncomputable section

theorem scratch_completion_link_intersection_upper_target
    {H : Hypergraph V} {base current A : ConflictSystem V}
    {stage j ell : ℕ} {d eps etaOld etaNew : ℝ} {w : TestWeight V}
    (hd : 1 ≤ d) (hetaOld : etaNew ≤ etaOld) (hetaNew : etaNew ≤ eps / 4)
    (hA : IsUniform A stage)
    (hIV : HasStagePropertiesIV H base (addCompletionLayer current A)
      d eps stage)
    (hw : IsTrackable H current j ell d etaOld w)
    {S : Hypergraph V} (hSH : S ∈ H.powersetCard j) (hwS : 0 < w S)
    (hfree : ConflictFree (addCompletionLayer current A) S)
    {e f : Finset V} (he : e ∈ S) (hf : f ∈ S) (hef : e ≠ f)
    {j' : ℕ} (hj' : 1 ≤ j') (hj'ell : j' < ell) :
    (((conflictLinkLayer (addCompletionLayer current A) e j' ∩
      conflictLinkLayer (addCompletionLayer current A) f j').card : ℕ) : ℝ) ≤
      Real.rpow d ((j' : ℝ) - etaNew) := by
  have heH : e ∈ H := (Finset.mem_powersetCard.mp hSH).1 he
  have hfH : f ∈ H := (Finset.mem_powersetCard.mp hSH).1 hf
  have hmatch : IsMatching H S := by
    by_contra hnmatch
    have hz := hw.1.2.2.2 S hnmatch
    linarith
  have hdisj : Disjoint e f := hmatch.2 he hf hef
  have hnotPair : {e, f} ∉ conflictLayer (addCompletionLayer current A) 2 := by
    intro hpair
    apply hfree {e, f} (Finset.mem_filter.mp hpair).1
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact he
    · exact hf
  by_cases hnew : j' = stage - 1
  · have hbound := hIV.2.2.2.2.2.2 e heH f hfH hdisj hnotPair
    calc
      (((conflictLinkLayer (addCompletionLayer current A) e j' ∩
        conflictLinkLayer (addCompletionLayer current A) f j').card : ℕ) : ℝ) ≤
          Real.rpow d ((stage - 1 : ℕ) - eps / 4) := by
        simpa [hnew] using hbound
      _ ≤ Real.rpow d ((j' : ℝ) - etaNew) := by
        apply Real.rpow_le_rpow_of_exponent_le hd
        rw [hnew]
        linarith
  · have hne : j' + 1 ≠ stage := by
      have hs2 := hIV.1
      omega
    have hsub : conflictLayer (addCompletionLayer current A) (j' + 1) ⊆
        conflictLayer current (j' + 1) :=
      conflictLayer_addCompletionLayer_subset_of_ne hA hne
    calc
      (((conflictLinkLayer (addCompletionLayer current A) e j' ∩
        conflictLinkLayer (addCompletionLayer current A) f j').card : ℕ) : ℝ) ≤
          ((conflictLinkLayer current e j' ∩
            conflictLinkLayer current f j').card : ℕ) :=
        scratch_card_link_inter_le_of_layer_succ hsub e f
      _ ≤ Real.rpow d ((j' : ℝ) - etaOld) :=
        hw.2.2.2.1 S hSH hwS e he f hf hef j' hj' hj'ell
      _ ≤ Real.rpow d ((j' : ℝ) - etaNew) :=
        Real.rpow_le_rpow_of_exponent_le hd (by linarith)

theorem scratch_restrictWeight_W1_W2_target
    {H : Hypergraph V} {C D : ConflictSystem V} {j ell : ℕ}
    {d etaOld etaNew epsLoss : ℝ} {w : TestWeight V}
    (hw : IsTrackable H C j ell d etaOld w) (hd : 0 < d)
    (hscalar : Real.rpow d (etaNew - etaOld) +
      Real.rpow d (-epsLoss) ≤ 1)
    (hkill : killedWeight H D j w ≤
      testTotal w H j / Real.rpow d epsLoss) :
    Real.rpow d ((j : ℝ) + etaNew) ≤
        testTotal (restrictWeight D w) H j ∧
      ∀ j', 1 ≤ j' → j' < j →
        testTotal w H j / Real.rpow d ((j' : ℝ) + etaOld) ≤
          testTotal (restrictWeight D w) H j /
            Real.rpow d ((j' : ℝ) + etaNew) := by
  let T := testTotal w H j
  let T' := testTotal (restrictWeight D w) H j
  have hT0 : 0 ≤ T := testTotal_nonneg hw.1.1 H j
  have heq : T' + killedWeight H D j w = T :=
    testTotal_restrictWeight_add_killedWeight H D j w hw.1.1
  have hdiv : T / Real.rpow d epsLoss = T * Real.rpow d (-epsLoss) := by
    rw [div_eq_mul_inv]
    congr 1
    exact (Real.rpow_neg hd.le epsLoss).symm
  have hT' : (1 - Real.rpow d (-epsLoss)) * T ≤ T' := by
    rw [hdiv] at hkill
    dsimp [T, T'] at heq hkill ⊢
    nlinarith
  have hfactor : Real.rpow d (etaNew - etaOld) ≤
      1 - Real.rpow d (-epsLoss) := by linarith
  have hone : 0 ≤ 1 - Real.rpow d (-epsLoss) :=
    (Real.rpow_nonneg hd.le _).trans hfactor
  constructor
  · calc
      Real.rpow d ((j : ℝ) + etaNew) =
          Real.rpow d (((j : ℝ) + etaOld) + (etaNew - etaOld)) := by
        congr 1
        ring
      _ =
          Real.rpow d ((j : ℝ) + etaOld) *
            Real.rpow d (etaNew - etaOld) := by
        exact Real.rpow_add hd _ _
      _ ≤ Real.rpow d ((j : ℝ) + etaOld) *
          (1 - Real.rpow d (-epsLoss)) :=
        mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hd.le _)
      _ ≤ T * (1 - Real.rpow d (-epsLoss)) :=
        mul_le_mul_of_nonneg_right hw.2.1 hone
      _ ≤ T' := by simpa [mul_comm] using hT'
  · intro j' _hj' _hj'j
    have ha : 0 < Real.rpow d ((j' : ℝ) + etaOld) :=
      Real.rpow_pos_of_pos hd _
    have hb : 0 < Real.rpow d ((j' : ℝ) + etaNew) :=
      Real.rpow_pos_of_pos hd _
    rw [div_le_div_iff₀ ha hb]
    have hden : Real.rpow d ((j' : ℝ) + etaNew) =
        Real.rpow d ((j' : ℝ) + etaOld) *
          Real.rpow d (etaNew - etaOld) := by
      calc
        Real.rpow d ((j' : ℝ) + etaNew) =
            Real.rpow d (((j' : ℝ) + etaOld) + (etaNew - etaOld)) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hd _ _
    rw [hden]
    calc
      T * (Real.rpow d ((j' : ℝ) + etaOld) *
          Real.rpow d (etaNew - etaOld)) =
        (T * Real.rpow d (etaNew - etaOld)) *
          Real.rpow d ((j' : ℝ) + etaOld) := by ring
      _ ≤ (T * (1 - Real.rpow d (-epsLoss))) *
          Real.rpow d ((j' : ℝ) + etaOld) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hfactor hT0
        · exact Real.rpow_nonneg hd.le _
      _ ≤ T' * Real.rpow d ((j' : ℝ) + etaOld) := by
        apply mul_le_mul_of_nonneg_right
        · simpa [mul_comm] using hT'
        · exact Real.rpow_nonneg hd.le _

theorem scratch_restrictWeight_isTrackable_addCompletionLayer_target
    {H : Hypergraph V} {base current A : ConflictSystem V}
    {stage j ell : ℕ} {d eps etaOld etaNew : ℝ} {w : TestWeight V}
    (hd : 1 ≤ d) (hetaOld : etaNew ≤ etaOld) (hetaNew : etaNew ≤ eps / 4)
    (hscalar : Real.rpow d (etaNew - etaOld) + Real.rpow d (-eps) ≤ 1)
    (hA : IsUniform A stage)
    (hIV : HasStagePropertiesIV H base (addCompletionLayer current A)
      d eps stage)
    (hw : IsTrackable H current j ell d etaOld w)
    (hkill : killedWeight H (addCompletionLayer current A) j w ≤
      testTotal w H j / Real.rpow d eps) :
    IsTrackable H (addCompletionLayer current A) j ell d etaNew
      (restrictWeight (addCompletionLayer current A) w) := by
  have h12 := scratch_restrictWeight_W1_W2_target hw
    (zero_lt_one.trans_le hd) hscalar hkill
  apply scratch_restrictWeight_isTrackable_target hw h12.1 h12.2
  intro S hSH hwS hfree e he f hf hef j' hj' hj'ell
  exact scratch_completion_link_intersection_upper_target hd hetaOld hetaNew
    hA hIV hw hSH hwS hfree he hf hef hj' hj'ell

theorem RawTransferCutoffSpec.transferScalar_between
    {eta K d etaOld etaNew : ℝ} (h : RawTransferCutoffSpec eta K d)
    (heta : 0 < eta) (hd : 1 ≤ d)
    (hgap : etaNew - etaOld ≤ -rawRegularizationEps eta / 600) :
    Real.rpow d (etaNew - etaOld) +
        Real.rpow d (-rawRegularizationEps eta) ≤ 1 := by
  have hfirst : Real.rpow d (etaNew - etaOld) ≤ 1 / 4 :=
    (Real.rpow_le_rpow_of_exponent_le hd hgap).trans h.regularizationTiny
  have hsecond : Real.rpow d (-rawRegularizationEps eta) ≤ 1 / 4 := by
    calc
      Real.rpow d (-rawRegularizationEps eta) ≤
          Real.rpow d (-rawRegularizationEps eta / 600) := by
        apply Real.rpow_le_rpow_of_exponent_le hd
        simp only [rawRegularizationEps]
        linarith
      _ ≤ 1 / 4 := h.regularizationTiny
  linarith

end
end Erdos136.CFMRegularization

namespace Erdos136.CFMRegularization

variable {V : Type*} [DecidableEq V] [Fintype V]

open UpperObservables

noncomputable section

attribute [local instance] Classical.propDecidable

theorem scratch_stage_layerMaxDegree_le_fourGamma
    (H : Hypergraph V) (base next : ConflictSystem V)
    {d eta Gamma : ℝ} {stage : ℕ}
    (hIV : HasStagePropertiesIV H base next d (rawRegularizationEps eta) stage)
    (hbase : (layerMaxDegree H base stage : ℝ) ≤
      Gamma * Real.rpow d ((stage : ℝ) - 1))
    (heta : 0 < eta) (hGamma : 1 ≤ Gamma) (hd : 1 ≤ d)
    (htransfer : RawTransferCutoffSpec eta 32 d) :
    (layerMaxDegree H next stage : ℝ) ≤
      4 * Gamma * Real.rpow d ((stage : ℝ) - 1) := by
  have hi : (inferInstance : DecidableEq V) = @Classical.decEq V :=
    Subsingleton.elim _ _
  cases hi
  letI : DecidableEq V := @Classical.decEq V
  let eps := rawRegularizationEps eta
  let p := Real.rpow d ((stage : ℝ) - 1)
  let tiny := Real.rpow d (-eps / 4)
  let err := Real.rpow d (-eps)
  let baseline := Real.rpow d ((stage : ℝ) - 1 - eps / 600)
  let target := completionTarget d eps (layerMaxDegree H base stage : ℝ) stage
  have hd0 : 0 ≤ d := zero_le_one.trans hd
  have hp0 : 0 ≤ p := Real.rpow_nonneg hd0 _
  have hbase0 : 0 ≤ (layerMaxDegree H base stage : ℝ) := by positivity
  have hbaseline0 : 0 ≤ baseline := Real.rpow_nonneg hd0 _
  have hbaselineP : baseline ≤ p := by
    dsimp [baseline, p, eps]
    apply Real.rpow_le_rpow_of_exponent_le hd
    have heps0 : 0 ≤ rawRegularizationEps eta := by
      simp only [rawRegularizationEps]
      linarith
    linarith
  have hpGp : p ≤ Gamma * p := by nlinarith
  have hmax : max baseline (layerMaxDegree H base stage : ℝ) ≤ Gamma * p :=
    max_le (hbaselineP.trans hpGp) (by simpa [p] using hbase)
  have htiny : tiny ≤ 1 / 4 := by
    dsimp [tiny, eps]
    exact (htransfer.regularizationScales heta hd).2.1
  have herr : err ≤ 1 / 4 := by
    dsimp [err, eps]
    exact (htransfer.regularizationScales heta hd).1
  have htiny0 : 0 ≤ tiny := Real.rpow_nonneg hd0 _
  have herr0 : 0 ≤ err := Real.rpow_nonneg hd0 _
  have htarget0 : 0 ≤ target := by
    dsimp [target, completionTarget, eps]
    positivity
  have htarget : target ≤ (5 / 4 : ℝ) * (Gamma * p) := by
    change (1 + tiny) *
      max baseline (layerMaxDegree H base stage : ℝ) ≤
        (5 / 4 : ℝ) * (Gamma * p)
    have hmax0 : 0 ≤ max baseline (layerMaxDegree H base stage : ℝ) :=
      hbaseline0.trans (le_max_left _ _)
    have hm := mul_le_mul
      (by linarith : 1 + tiny ≤ 5 / 4)
      hmax hmax0 (by norm_num : (0 : ℝ) ≤ 5 / 4)
    exact hm
  have hdegree : ∀ e ∈ H,
      (degree (conflictLayer next stage) e : ℝ) ≤
        (5 / 4 : ℝ) * ((5 / 4 : ℝ) * (Gamma * p)) := by
    intro e he
    have hupp := (hIV.2.2.1 e he).2
    change (degree (conflictLayer next stage) e : ℝ) ≤ (1 + err) * target at hupp
    exact hupp.trans (by
      have hm := mul_le_mul (by linarith : 1 + err ≤ 5 / 4) htarget
        htarget0 (by norm_num : (0 : ℝ) ≤ 5 / 4)
      nlinarith)
  have hD0 : 0 ≤ 4 * Gamma * p := by positivity
  have hrow : ∀ e ∈ H,
      (degree (conflictLayer next stage) e : ℝ) ≤ 4 * Gamma * p := by
    intro e he
    calc
      (degree (conflictLayer next stage) e : ℝ) ≤
          (5 / 4 : ℝ) * ((5 / 4 : ℝ) * (Gamma * p)) := hdegree e he
      _ ≤ 4 * Gamma * p := by nlinarith
  have hLM := layerMaxDegree_le_of_degree_bound H next stage
    (4 * Gamma * p) hD0 hrow
  simpa [p] using hLM

theorem scratch_stageKilledWeightLimit_le_final
    {ell stage : ℕ} {eta d X : ℝ}
    (hreg : RawRegularizationCutoffSpec ell eta d)
    (hstage : stage ∈ ({2, 3, 4} : Finset ℕ)) (hX : 0 ≤ X) :
    stageKilledWeightLimit stage d (rawRegularizationEps eta) X ≤
      X / Real.rpow d (rawRegularizationEps eta) := by
  have hsum := hreg.threeStageKilledWeightLimits hX
  have hd : 0 < d := zero_lt_two.trans_le hreg.degreeAtLeastTwo
  have h2 : 0 ≤ stageKilledWeightLimit 2 d (rawRegularizationEps eta) X := by
    unfold stageKilledWeightLimit
    exact div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hX)
      (Real.rpow_nonneg hd.le _)
  have h3 : 0 ≤ stageKilledWeightLimit 3 d (rawRegularizationEps eta) X := by
    unfold stageKilledWeightLimit
    exact div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hX)
      (Real.rpow_nonneg hd.le _)
  have h4 : 0 ≤ stageKilledWeightLimit 4 d (rawRegularizationEps eta) X := by
    unfold stageKilledWeightLimit
    exact div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hX)
      (Real.rpow_nonneg hd.le _)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hstage
  rcases hstage with rfl | rfl | rfl
  · simpa [stageKilledWeightLimit] using (show
      stageKilledWeightLimit 2 d (rawRegularizationEps eta) X ≤
        stageKilledWeightLimit 2 d (rawRegularizationEps eta) X +
          stageKilledWeightLimit 3 d (rawRegularizationEps eta) X +
          stageKilledWeightLimit 4 d (rawRegularizationEps eta) X from by linarith).trans hsum
  · simpa [stageKilledWeightLimit] using (show
      stageKilledWeightLimit 3 d (rawRegularizationEps eta) X ≤
        stageKilledWeightLimit 2 d (rawRegularizationEps eta) X +
          stageKilledWeightLimit 3 d (rawRegularizationEps eta) X +
          stageKilledWeightLimit 4 d (rawRegularizationEps eta) X from by linarith).trans hsum
  · simpa [stageKilledWeightLimit] using (show
      stageKilledWeightLimit 4 d (rawRegularizationEps eta) X ≤
        stageKilledWeightLimit 2 d (rawRegularizationEps eta) X +
          stageKilledWeightLimit 3 d (rawRegularizationEps eta) X +
          stageKilledWeightLimit 4 d (rawRegularizationEps eta) X from by linarith).trans hsum

/-- Exact current-dependent package consumed by one raw rank-selection step. -/
structure RawStagePremises
    {ι : Type*} [Fintype ι] [Fintype V]
    (H : Hypergraph V) (base current : ConflictSystem V)
    (d eta etaTrack Gamma : ℝ) (ell stage : ℕ)
    (testJ : ι → ℕ) (w : ι → TestWeight V) : Prop where
  currentSystem : IsConflictSystem H current
  currentLayer : conflictLayer current stage ⊆ conflictLayer base stage
  baseLayer : (layerMaxDegree H base stage : ℝ) ≤
    Gamma * Real.rpow d ((stage : ℝ) - 1)
  forbidden : ∀ e : ConcreteStageDegreeIndex H,
    ((forbiddenIncidentCompletions H current stage e.1).card : ℝ) ≤
      rawForbiddenCoeff 1 (4 * Gamma) stage * d *
        (H.card : ℝ) ^ (stage - 2)
  deficit : HasSourceDeficitBoundsAtTarget H current d
    (rawRegularizationEps eta) Gamma
    (completionTarget d (rawRegularizationEps eta)
      (layerMaxDegree H base stage : ℝ) stage) stage
  strong : ∀ e : ConcreteStageDegreeIndex H,
    Real.rpow d ((stage : ℝ) - 1 - rawRegularizationEps eta / 4 -
      rawRegularizationEps eta / 600) ≤
    degreeDeficit current stage
      (completionTarget d (rawRegularizationEps eta)
        (layerMaxDegree H base stage : ℝ) stage) e.1
  oldII : ∀ root : StageCodegreeIndex V stage,
    (codegree (conflictLayer current stage) root.1 : ℝ) ≤
      Real.rpow d ((stage : ℝ) - (root.1.card : ℝ) -
        rawRegularizationEps eta / 3)
  oldIII : ∀ (_hs : stage = 2) (e : Finset V) (_he : e ∈ H) (v : V),
    (conditionC4Count H current e v : ℝ) ≤
      Real.rpow d (1 - rawRegularizationEps eta / 3)
  oldIV : ∀ (_hs : stage = 2) (e : Finset V) (_he : e ∈ H)
    (f : Finset V) (_hf : f ∈ H) (_hdisj : Disjoint e f),
    (conditionC5Count H current e f : ℝ) ≤
      Real.rpow d (1 - rawRegularizationEps eta / 3)
  oldV : ∀ (e : Finset V) (_he : e ∈ H)
    (f : Finset V) (_hf : f ∈ H) (_hdisj : Disjoint e f)
    (_hnot : {e, f} ∉ conflictLayer current 2),
    (((conflictLinkLayer current e (stage - 1) ∩
      conflictLinkLayer current f (stage - 1)).card : ℕ) : ℝ) ≤
        Real.rpow d (((stage - 1 : ℕ) : ℝ) -
          rawRegularizationEps eta / 3)
  trackable : ∀ a, IsTrackable H current (testJ a) ell d etaTrack (w a)
  trackExponent : rawRegularizationEps eta / 5 ≤ etaTrack
  cards :
    (Fintype.card (ConcreteStageDegreeIndex H) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
      (Fintype.card (RestrictedStageLinearUpperIndex H stage) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
      (Fintype.card (StageBlockUpperIndex H current stage) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
      (Fintype.card (ActiveStageTest H current stage testJ w) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3))

theorem RawStagePremises.exists_completion
    {ι : Type*} [Fintype ι] [Fintype V]
    {H : Hypergraph V} {base current : ConflictSystem V}
    {d eta etaTrack Gamma : ℝ} {ell stage : ℕ}
    {testJ : ι → ℕ} {w : ι → TestWeight V}
    (p : RawStagePremises H base current d eta etaTrack Gamma
      ell stage testJ w)
    (hHuniform : IsUniform H 8)
    (hdegreeUpper : ∀ v ∈ vertexFinset H, (degree H v : ℝ) ≤ d)
    (hH : H.Nonempty) (heta : 0 < eta) (hGamma : 1 ≤ Gamma)
    (hstage : stage ∈ ({2, 3, 4} : Finset ℕ))
    (hj : ∀ a, 1 ≤ testJ a ∧ testJ a ≤ 3)
    (hreg : RawRegularizationCutoffSpec ell eta d)
    (hsource : RawSourceCutoffSpec eta Gamma 1 (4 * Gamma) d)
    (hobs : RawObservableCutoffSpec eta Gamma 8 d)
    (htransfer : RawTransferCutoffSpec eta 32 d)
    (hendpoint : RawEndpointCutoffSpec eta d)
    (hhostLower : Real.rpow d (1 + eta) / 32 ≤ (H.card : ℝ)) :
    ∃ A : ConflictSystem V,
      A ⊆ completionCandidates H current stage ∧
      HasStagePropertiesIV H base (addCompletionLayer current A) d
        (rawRegularizationEps eta) stage ∧
      ∀ a, killedWeight H (addCompletionLayer current A) (testJ a) (w a) <
        stageKilledWeightLimit stage d (rawRegularizationEps eta)
          (testTotal (w a) H (testJ a)) := by
  exact exists_rawRegularizationStage_nonempty H base current p.currentSystem
    hHuniform d eta etaTrack Gamma stage hdegreeUpper testJ w hH heta hstage
    hGamma p.currentLayer p.baseLayer p.forbidden p.deficit p.strong p.oldII
    p.oldIII p.oldIV p.oldV p.trackable hj p.trackExponent hreg hsource hobs
    htransfer hendpoint hhostLower p.cards

theorem rawStage_card_bounds
    {ι : Type*} [Fintype ι] [Fintype V]
    {H : Hypergraph V} {current : ConflictSystem V}
    {d eta : ℝ} {stage : ℕ} {testJ : ι → ℕ} {w : ι → TestWeight V}
    (hstage4 : stage ≤ 4)
    (hhost : (H.card : ℝ) ≤ Real.exp (2 * Real.rpow d (eta ^ 3)))
    (hvertex : ((vertexFinset H).card : ℝ) ≤
      Real.exp (Real.rpow d (eta ^ 3)))
    (hfour : 4 ≤ Real.exp (Real.rpow d (eta ^ 3)))
    (htest : (Fintype.card ι : ℝ) ≤
      Real.exp (8 * Real.rpow d (eta ^ 3))) :
    (Fintype.card (ConcreteStageDegreeIndex H) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
      (Fintype.card (RestrictedStageLinearUpperIndex H stage) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
      (Fintype.card (StageBlockUpperIndex H current stage) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
      (Fintype.card (ActiveStageTest H current stage testJ w) : ℝ) ≤
        Real.exp (8 * Real.rpow d (eta ^ 3)) := by
  obtain ⟨hdegree, hlinear, hblock⟩ :=
    restricted_observable_card_bounds hstage4 hhost hvertex hfour
  refine ⟨hdegree, hlinear, hblock, ?_⟩
  have hactive : (Fintype.card (ActiveStageTest H current stage testJ w) : ℝ) ≤
      (Fintype.card ι : ℝ) := by
    exact_mod_cast card_activeStageTest_le H current stage testJ w
  exact hactive.trans htest

theorem exists_rawRegularization_nonempty
    {ι : Type*} [Fintype ι]
    (H : Hypergraph V) (C : ConflictSystem V)
    (d eta : ℝ) (ell : ℕ) (j : ι → ℕ) (w : ι → TestWeight V)
    (hHuniform : IsUniform H 8)
    (hC : IsConflictSystem H C)
    (hCcard : ∀ c ∈ C, c.card = 4)
    (heta : 0 < eta) (heta1 : eta < 1) (hd : 1 ≤ d)
    (hvertex : ((vertexFinset H).card : ℝ) ≤
      Real.exp (Real.rpow d (eta ^ 3)))
    (hdegree : ∀ v ∈ vertexFinset H,
      (1 - Real.rpow d (-eta)) * d ≤ (degree H v : ℝ) ∧
      (degree H v : ℝ) ≤ d)
    (hcodeg : ∀ s, s.card = 2 →
      (codegree H s : ℝ) ≤ Real.rpow d (1 - eta))
    (hbounded : IsBounded C d ell eta)
    (htestCard : (Fintype.card ι : ℝ) ≤
      Real.exp (Real.rpow d (eta ^ 3)))
    (htrack : ∀ a, 1 ≤ j a ∧ j a ≤ 3 ∧
      IsTrackable H C (j a) ell d eta (w a))
    (hH : H.Nonempty)
    (hreg : RawRegularizationCutoffSpec ell eta d)
    (hsource : RawSourceCutoffSpec eta (2 * (ell : ℝ) + 1) 1
      (4 * (2 * (ell : ℝ) + 1)) d)
    (hobs : RawObservableCutoffSpec eta (2 * (ell : ℝ) + 1) 8 d)
    (htransfer : RawTransferCutoffSpec eta 32 d)
    (hendpoint : RawEndpointCutoffSpec eta d) :
    Nonempty (RegularizationCertificate H C d (rawRegularizationEps eta)
      (2 * (ell : ℝ) + 1) ell j w) := by
  have hi : (inferInstance : DecidableEq V) = @Classical.decEq V :=
    Subsingleton.elim _ _
  cases hi
  letI : DecidableEq V := @Classical.decEq V
  let eps := rawRegularizationEps eta
  let Gamma : ℝ := 2 * (ell : ℝ) + 1
  let B := badPairConflicts H C (trackableCutoff d (eps / 3))
  let C0 := minimalMatchingCore H (C ∪ B)
  have heps : eps = rawRegularizationEps eta := rfl
  have heps0 : 0 < eps := by simp [eps, rawRegularizationEps, heta]
  have hGamma : 1 ≤ Gamma := by
    dsimp [Gamma]
    have : 0 ≤ (ell : ℝ) := by positivity
    linarith
  have hGamma3 : 3 ≤ Gamma := by
    dsimp [Gamma]
    have hell : 4 ≤ ell := hreg.rankAtLeastFour
    exact_mod_cast (by omega : 3 ≤ 2 * ell + 1)
  have hdpos : 0 < d := zero_lt_one.trans_le hd
  have hdegreeUpper : ∀ v ∈ vertexFinset H, (degree H v : ℝ) ≤ d :=
    fun v hv => (hdegree v hv).2
  have hdegreeLower : ∀ v ∈ vertexFinset H,
      (1 - Real.rpow d (-eta)) * d ≤ (degree H v : ℝ) :=
    fun v hv => (hdegree v hv).1
  have hBuniform : IsUniform B 2 := badPairConflicts_uniform_two H C _
  have hBsystem : IsConflictSystem H B := badPairConflicts_isConflictSystem H C _
  have habsorb : (ell : ℝ) * Real.rpow d (1 - eta + eps / 3) ≤
      Real.rpow d (1 - eps / 3) := by
    calc
      (ell : ℝ) * Real.rpow d (1 - eta + eps / 3) ≤
          (ell : ℝ) * Real.rpow d (1 - 2 * eta / 3) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hd
        simp [eps, rawRegularizationEps]
        linarith
      _ ≤ Real.rpow d (1 - eps / 3) := by
        simpa [eps] using hreg.badPairAbsorption
  have hBdegree : ∀ e ∈ H, (degree B e : ℝ) ≤
      Real.rpow d (1 - eps / 3) := by
    intro e he
    exact degree_badPairConflicts_trackableCutoff_target_card_four
      H C hbounded hCcard hreg.rankAtLeastFour hdpos habsorb e
  have hC0system : IsConflictSystem H C0 := by
    apply minimalMatchingCore_isConflictSystem
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact hC c hc
    · exact hBsystem c hc
  have hbaseSum :
      (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H C0 r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤ Gamma := by
    exact minimalBadCore_normalizedDegreeSum_le_Gamma H C B hbounded hBuniform
      hreg.rankAtLeastFour hd (by positivity : 0 ≤ eps / 3) hBdegree (by rfl)
  have hbaseLayer : ∀ r, 2 ≤ r → r ≤ 4 →
      (layerMaxDegree H C0 r : ℝ) ≤
        Gamma * Real.rpow d ((r : ℝ) - 1) := by
    intro r hr2 hr4
    exact scratch_layerMaxDegree_le_of_normalizedDegreeSum H C0 hdpos hr2 hr4 hbaseSum
  have hbaseReg : IsRegularizedBounded H C0 d Gamma (eps / 3) := by
    have hdegreeSum2 :
        (∑ r ∈ Finset.Icc 2 4,
          (layerMaxDegree H C0 r : ℝ) /
            Real.rpow d ((r : ℝ) - 1)) ≤ 2 * (Gamma / 2) := by
      convert hbaseSum using 1 <;> ring
    have hraw := minimalCore_with_badPairs_isRegularizedBounded_of_degreeSum
      H C hbounded hCcard hreg.rankAtLeastFour hd
      (by simp [eps, rawRegularizationEps]; linarith) hBdegree
      (Gamma := Gamma / 2) (by linarith) (by simpa [C0, B] using hdegreeSum2)
    have hGammaEq : 2 * (Gamma / 2) = Gamma := by ring
    rw [hGammaEq] at hraw
    simpa [C0, B] using hraw
  have hhostLower : Real.rpow d (1 + eta) / 32 ≤ (H.card : ℝ) :=
    thirtysecond_rpow_le_host_card hHuniform hH hdpos hreg.inverseInputSmall
      hdegreeLower hcodeg
  have hdn : d ≤ (H.card : ℝ) := rawSource_degree_le_host hdpos hhostLower hsource
  have hhostUpper : (H.card : ℝ) ≤
      Real.exp (2 * Real.rpow d (eta ^ 3)) :=
    host_card_le_exp_two_entropy hHuniform hdegreeUpper hvertex
      (hendpoint.degree_le_exp_entropy heta hd) hdpos.le
  have htest8 : (Fintype.card ι : ℝ) ≤
      Real.exp (8 * Real.rpow d (eta ^ 3)) := by
    refine htestCard.trans (Real.exp_le_exp.mpr ?_)
    have hx : 0 ≤ Real.rpow d (eta ^ 3) := Real.rpow_nonneg hdpos.le _
    linarith
  have hcards (current : ConflictSystem V) (stage : ℕ) (hs4 : stage ≤ 4)
      (ww : ι → TestWeight V) :
      (Fintype.card (ConcreteStageDegreeIndex H) : ℝ) ≤
          Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
        (Fintype.card (RestrictedStageLinearUpperIndex H stage) : ℝ) ≤
          Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
        (Fintype.card (StageBlockUpperIndex H current stage) : ℝ) ≤
          Real.exp (8 * Real.rpow d (eta ^ 3)) ∧
        (Fintype.card (ActiveStageTest H current stage j ww) : ℝ) ≤
          Real.exp (8 * Real.rpow d (eta ^ 3)) :=
    rawStage_card_bounds hs4 hhostUpper hvertex
      hendpoint.four_le_exp_entropy htest8
  have hmax : MaxDegreeLE H (Nat.floor d) :=
    maxDegreeLE_floor_of_vertex_degree_upper hdegreeUpper
  have hC0layer2B : conflictLayer C0 2 ⊆ conflictLayer B 2 :=
    minimalCore_union_layer_two_subset_right H hbounded
  have hBlayer : conflictLayer B 2 = B := conflictLayer_eq_self_of_uniform hBuniform
  have p2 : RawStagePremises H C0 C0 d eta (eps / 3) Gamma ell 2 j w := by
    refine {
      currentSystem := hC0system
      currentLayer := Finset.Subset.rfl
      baseLayer := hbaseLayer 2 (by norm_num) (by norm_num)
      forbidden := ?_
      deficit := ?_
      strong := ?_
      oldII := ?_
      oldIII := ?_
      oldIV := ?_
      oldV := ?_
      trackable := ?_
      trackExponent := ?_
      cards := hcards C0 2 (by norm_num) w }
    · intro e
      apply forbiddenCard_two_le_rawCoeff (A := 1) (B := 4 * Gamma)
        hHuniform hmax hC0system hbaseReg.1
      · simpa using (Nat.floor_le hdpos.le)
      · have hb := hbaseLayer 2 (by norm_num) (by norm_num)
        norm_num [Real.rpow_one] at hb ⊢
        nlinarith
      · exact e.2
    · exact hasSourceDeficitBoundsAtTarget_stageTwo H C0 hreg.degreeAtLeastTwo
        heps0 hGamma (hbaseLayer 2 (by norm_num) (by norm_num))
    · exact degreeDeficit_strong_lower_of_layer_subset hd Finset.Subset.rfl
    · intro root
      exact hbaseReg.layer_codegree (by norm_num) (by norm_num)
        root.2.1 root.2.2 root.1 rfl
    · intro _ e he v
      exact hbaseReg.2.2.2.2.1 e he v
    · intro _ e he f hf hdisj
      exact hbaseReg.2.2.2.2.2 e he f hf hdisj
    · intro e he f hf hdisj hnot
      calc
        (((conflictLinkLayer C0 e 1 ∩ conflictLinkLayer C0 f 1).card : ℕ) : ℝ) ≤
            (conflictLinkLayer C0 e 1).card := by
          exact_mod_cast Finset.card_le_card Finset.inter_subset_left
        _ = (degree (conflictLayer C0 2) e : ℕ) := by
          exact_mod_cast card_conflictLinkLayer_eq_degree_layer C0 e 1
        _ ≤ (degree (conflictLayer B 2) e : ℕ) := by
          exact_mod_cast degree_mono hC0layer2B e
        _ = (degree B e : ℕ) := by rw [hBlayer]
        _ ≤ Real.rpow d (1 - eps / 3) := hBdegree e he
        _ = Real.rpow d (((2 - 1 : ℕ) : ℝ) -
            rawRegularizationEps eta / 3) := by simp [eps]
    · intro a
      exact scratch_isTrackable_raw_minimalCore hreg.rankAtLeastFour heta hd
        hbounded hBdegree (htrack a).2.2
    · have := heps0
      linarith
  obtain ⟨A2, hA2, hIV2, hkill2⟩ := p2.exists_completion hHuniform
    hdegreeUpper hH heta hGamma (by simp) (fun a => ⟨(htrack a).1, (htrack a).2.1⟩)
    hreg hsource hobs htransfer hendpoint hhostLower
  let C2 := addCompletionLayer C0 A2
  let w2 : ι → TestWeight V := fun a => restrictWeight C2 (w a)
  have hA2uniform : IsUniform A2 2 :=
    (completionCandidates_uniform H C0 2).mono hA2
  have hA2system : IsConflictSystem H A2 := by
    intro c hc
    exact completionCandidates_isConflictSystem H C0 2 c (hA2 hc)
  have hC2system : IsConflictSystem H C2 :=
    addCompletionLayer_isConflictSystem hC0system hA2system
  have hC2card : ∀ c ∈ C2, 2 ≤ c.card ∧ c.card ≤ 4 :=
    addCompletionLayer_conflict_card hbaseReg.1 hA2uniform (by norm_num) (by norm_num)
  have hC2layer3 : conflictLayer C2 3 ⊆ conflictLayer C0 3 :=
    conflictLayer_stageThree_subset_base C0 A2 hA2uniform
  have hC2layer2 : (layerMaxDegree H C2 2 : ℝ) ≤
      4 * Gamma * Real.rpow d ((2 : ℝ) - 1) :=
    scratch_stage_layerMaxDegree_le_fourGamma H C0 C2 hIV2
      (hbaseLayer 2 (by norm_num) (by norm_num)) heta hGamma hd htransfer
  have hC2layer3max : (layerMaxDegree H C2 3 : ℝ) ≤
      4 * Gamma * Real.rpow d ((3 : ℝ) - 1) := by
    apply layerMaxDegree_le_of_degree_bound H C2 3
      (4 * Gamma * Real.rpow d ((3 : ℝ) - 1))
      (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hGamma))
        (Real.rpow_nonneg hdpos.le _))
    intro e he
    calc
      (degree (conflictLayer C2 3) e : ℝ) ≤
          degree (conflictLayer C0 3) e := by
        exact_mod_cast degree_mono hC2layer3 e
      _ ≤ (layerMaxDegree H C0 3 : ℕ) := by
        exact_mod_cast degree_layer_le_layerMaxDegree he
      _ ≤ Gamma * Real.rpow d ((3 : ℝ) - 1) :=
        hbaseLayer 3 (by norm_num) (by norm_num)
      _ ≤ 4 * Gamma * Real.rpow d ((3 : ℝ) - 1) := by
        have hp : 0 ≤ Real.rpow d ((3 : ℝ) - 1) := Real.rpow_nonneg hdpos.le _
        nlinarith
  have hkill2le : ∀ a, killedWeight H C2 (j a) (w a) ≤
      testTotal (w a) H (j a) / Real.rpow d eps := by
    intro a
    have hlim := scratch_stageKilledWeightLimit_le_final
      (ell := ell) (stage := 2) (eta := eta) (d := d)
      (X := testTotal (w a) H (j a)) hreg (by simp)
      (testTotal_nonneg (htrack a).2.2.1.1 H (j a))
    exact (hkill2 a).le.trans (by simpa [eps, C2] using hlim)
  have htrack2 : ∀ a, IsTrackable H C2 (j a) ell d (eps / 4) (w2 a) := by
    intro a
    have hscalar := htransfer.transferScalar_between heta hd
      (etaOld := eps / 3) (etaNew := eps / 4) (by
        have := heps0
        linarith)
    exact scratch_restrictWeight_isTrackable_addCompletionLayer_target
      hd (by linarith [heps0]) (by linarith [heps0]) hscalar hA2uniform hIV2
      (p2.trackable a) (hkill2le a)
  have hCraw3 : conflictLayer C 3 = ∅ :=
    conflictLayer_eq_empty_of_card_four C hCcard 3 (by omega)
  have hC2linkEmpty : ∀ e, conflictLinkLayer C2 e 2 = ∅ := by
    intro e
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hlink0 := scratch_conflictLinkLayer_mono_of_layer_succ
      (hC2layer3.trans
        (conflictLayer_minimalMatchingCore_union_two_subset hBuniform (by omega))) e ht
    rw [conflictLinkLayer_eq_empty_of_card_four_of_lt_three
      hCcard e 2 (by omega)] at hlink0
    simpa using hlink0
  have p3 : RawStagePremises H C0 C2 d eta (eps / 4) Gamma ell 3 j w2 := by
    refine {
      currentSystem := hC2system
      currentLayer := hC2layer3
      baseLayer := hbaseLayer 3 (by norm_num) (by norm_num)
      forbidden := ?_
      deficit := ?_
      strong := ?_
      oldII := ?_
      oldIII := ?_
      oldIV := ?_
      oldV := ?_
      trackable := htrack2
      trackExponent := ?_
      cards := hcards C2 3 (by norm_num) w2 }
    · intro e
      apply forbiddenCard_three_le_rawCoeff hHuniform hmax hC2system hC2card
        (d := d) (n := (H.card : ℝ)) (A := 1) (B := 4 * Gamma)
      · exact hdpos.le
      · positivity
      · exact le_rfl
      · exact hdn
      · positivity
      · simpa using (Nat.floor_le hdpos.le)
      · calc
          (layerMaxDegree H C2 2 : ℝ) ≤
              4 * Gamma * Real.rpow d ((2 : ℝ) - 1) := hC2layer2
          _ = 4 * Gamma * d := by norm_num [Real.rpow_one]
      · calc
          (layerMaxDegree H C2 3 : ℝ) ≤
              4 * Gamma * Real.rpow d ((3 : ℝ) - 1) := hC2layer3max
          _ = 4 * Gamma * d ^ 2 := by
            norm_num
      · exact e.2
    · exact hasSourceDeficitBoundsAtTarget_stageThree H C0 A2
        hreg.degreeAtLeastTwo heps0 hGamma hA2uniform
        (hbaseLayer 3 (by norm_num) (by norm_num))
    · exact degreeDeficit_strong_lower_of_layer_subset hd hC2layer3
    · intro root
      calc
        (codegree (conflictLayer C2 3) root.1 : ℝ) ≤
            codegree (conflictLayer C0 3) root.1 := by
          exact_mod_cast codegree_mono_hypergraph hC2layer3 root.1
        _ ≤ Real.rpow d ((3 : ℝ) - (root.1.card : ℝ) - eps / 3) :=
          hbaseReg.layer_codegree (by norm_num) (by norm_num)
            root.2.1 root.2.2 root.1 rfl
    · intro hs
      omega
    · intro hs
      omega
    · intro e he f hf hdisj hnot
      rw [hC2linkEmpty e]
      simp only [Finset.empty_inter, Finset.card_empty, Nat.cast_zero]
      exact Real.rpow_nonneg hdpos.le _
    · have := heps0
      linarith
  obtain ⟨A3, hA3, hIV3, hkill3⟩ := p3.exists_completion hHuniform
    hdegreeUpper hH heta hGamma (by simp) (fun a => ⟨(htrack a).1, (htrack a).2.1⟩)
    hreg hsource hobs htransfer hendpoint hhostLower
  let C3 := addCompletionLayer C2 A3
  let w3 : ι → TestWeight V := fun a => restrictWeight C3 (w a)
  have hA3uniform : IsUniform A3 3 :=
    (completionCandidates_uniform H C2 3).mono hA3
  have hA3system : IsConflictSystem H A3 := by
    intro c hc
    exact completionCandidates_isConflictSystem H C2 3 c (hA3 hc)
  have hC3system : IsConflictSystem H C3 :=
    addCompletionLayer_isConflictSystem hC2system hA3system
  have hC3card : ∀ c ∈ C3, 2 ≤ c.card ∧ c.card ≤ 4 :=
    addCompletionLayer_conflict_card hC2card hA3uniform (by norm_num) (by norm_num)
  have hC3layer4 : conflictLayer C3 4 ⊆ conflictLayer C0 4 :=
    conflictLayer_stageFour_subset_base C0 A2 A3 hA2uniform hA3uniform
  have hC3layer2sub : conflictLayer C3 2 ⊆ conflictLayer C2 2 :=
    conflictLayer_addCompletionLayer_subset_of_ne hA3uniform (by omega)
  have hC3layer2 : (layerMaxDegree H C3 2 : ℝ) ≤
      4 * Gamma * Real.rpow d ((2 : ℝ) - 1) := by
    apply layerMaxDegree_le_of_degree_bound H C3 2
      (4 * Gamma * Real.rpow d ((2 : ℝ) - 1))
      (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hGamma))
        (Real.rpow_nonneg hdpos.le _))
    intro e he
    calc
      (degree (conflictLayer C3 2) e : ℝ) ≤
          degree (conflictLayer C2 2) e := by
        exact_mod_cast degree_mono hC3layer2sub e
      _ ≤ (layerMaxDegree H C2 2 : ℕ) := by
        exact_mod_cast degree_layer_le_layerMaxDegree he
      _ ≤ 4 * Gamma * Real.rpow d ((2 : ℝ) - 1) := hC2layer2
  have hC3layer3 : (layerMaxDegree H C3 3 : ℝ) ≤
      4 * Gamma * Real.rpow d ((3 : ℝ) - 1) :=
    scratch_stage_layerMaxDegree_le_fourGamma H C0 C3 hIV3
      (hbaseLayer 3 (by norm_num) (by norm_num)) heta hGamma hd htransfer
  have hC3layer4max : (layerMaxDegree H C3 4 : ℝ) ≤
      4 * Gamma * Real.rpow d ((4 : ℝ) - 1) := by
    apply layerMaxDegree_le_of_degree_bound H C3 4
      (4 * Gamma * Real.rpow d ((4 : ℝ) - 1))
      (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hGamma))
        (Real.rpow_nonneg hdpos.le _))
    intro e he
    calc
      (degree (conflictLayer C3 4) e : ℝ) ≤
          degree (conflictLayer C0 4) e := by
        exact_mod_cast degree_mono hC3layer4 e
      _ ≤ (layerMaxDegree H C0 4 : ℕ) := by
        exact_mod_cast degree_layer_le_layerMaxDegree he
      _ ≤ Gamma * Real.rpow d ((4 : ℝ) - 1) :=
        hbaseLayer 4 (by norm_num) (by norm_num)
      _ ≤ 4 * Gamma * Real.rpow d ((4 : ℝ) - 1) := by
        have hp : 0 ≤ Real.rpow d ((4 : ℝ) - 1) := Real.rpow_nonneg hdpos.le _
        nlinarith
  have hkill3le : ∀ a, killedWeight H C3 (j a) (w2 a) ≤
      testTotal (w2 a) H (j a) / Real.rpow d eps := by
    intro a
    have hlim := scratch_stageKilledWeightLimit_le_final
      (ell := ell) (stage := 3) (eta := eta) (d := d)
      (X := testTotal (w2 a) H (j a)) hreg (by simp)
      (testTotal_nonneg (htrack2 a).1.1 H (j a))
    exact (hkill3 a).le.trans (by simpa [eps, C3] using hlim)
  have htrack3 : ∀ a, IsTrackable H C3 (j a) ell d (9 * eps / 40) (w3 a) := by
    intro a
    have hscalar := htransfer.transferScalar_between heta hd
      (etaOld := eps / 4) (etaNew := 9 * eps / 40) (by
        have := heps0
        linarith)
    have hraw := scratch_restrictWeight_isTrackable_addCompletionLayer_target
      hd (by linarith [heps0]) (by linarith [heps0]) hscalar hA3uniform hIV3
      (htrack2 a) (hkill3le a)
    rw [restrictWeight_addCompletionLayer_comp C2 A3 (w a)] at hraw
    simpa [C3, w3] using hraw
  have hC0layer2subC2 : conflictLayer C0 2 ⊆ conflictLayer C2 2 := by
    rw [show C2 = addCompletionLayer C0 A2 by rfl,
      conflictLayer_addCompletionLayer_eq hA2uniform]
    exact Finset.subset_union_left
  have hC0layer2subC3 : conflictLayer C0 2 ⊆ conflictLayer C3 2 := by
    rw [show C3 = addCompletionLayer C2 A3 by rfl,
      conflictLayer_addCompletionLayer_of_lt hA3uniform (by omega)]
    exact hC0layer2subC2
  have hC0layer4subC : conflictLayer C0 4 ⊆ conflictLayer C 4 :=
    conflictLayer_minimalMatchingCore_union_two_subset hBuniform (by omega)
  have p4 : RawStagePremises H C0 C3 d eta (9 * eps / 40) Gamma ell 4 j w3 := by
    refine {
      currentSystem := hC3system
      currentLayer := hC3layer4
      baseLayer := hbaseLayer 4 (by norm_num) (by norm_num)
      forbidden := ?_
      deficit := ?_
      strong := ?_
      oldII := ?_
      oldIII := ?_
      oldIV := ?_
      oldV := ?_
      trackable := htrack3
      trackExponent := ?_
      cards := hcards C3 4 (by norm_num) w3 }
    · intro e
      apply forbiddenCard_four_le_rawCoeff hHuniform hmax hC3system hC3card
        (d := d) (n := (H.card : ℝ)) (A := 1) (B := 4 * Gamma)
      · exact hdpos.le
      · positivity
      · exact le_rfl
      · exact hdn
      · positivity
      · simpa using (Nat.floor_le hdpos.le)
      · calc
          (layerMaxDegree H C3 2 : ℝ) ≤
              4 * Gamma * Real.rpow d ((2 : ℝ) - 1) := hC3layer2
          _ = 4 * Gamma * d := by norm_num [Real.rpow_one]
      · calc
          (layerMaxDegree H C3 3 : ℝ) ≤
              4 * Gamma * Real.rpow d ((3 : ℝ) - 1) := hC3layer3
          _ = 4 * Gamma * d ^ 2 := by norm_num
      · calc
          (layerMaxDegree H C3 4 : ℝ) ≤
              4 * Gamma * Real.rpow d ((4 : ℝ) - 1) := hC3layer4max
          _ = 4 * Gamma * d ^ 3 := by norm_num
      · exact e.2
    · exact hasSourceDeficitBoundsAtTarget_stageFour H C0 A2 A3
        hreg.degreeAtLeastTwo heps0 hGamma hA2uniform hA3uniform
        (hbaseLayer 4 (by norm_num) (by norm_num))
    · exact degreeDeficit_strong_lower_of_layer_subset hd hC3layer4
    · intro root
      calc
        (codegree (conflictLayer C3 4) root.1 : ℝ) ≤
            codegree (conflictLayer C0 4) root.1 := by
          exact_mod_cast codegree_mono_hypergraph hC3layer4 root.1
        _ ≤ Real.rpow d ((4 : ℝ) - (root.1.card : ℝ) - eps / 3) :=
          hbaseReg.layer_codegree (by norm_num) (by norm_num)
            root.2.1 root.2.2 root.1 rfl
    · intro hs
      omega
    · intro hs
      omega
    · intro e he f hf hdisj hnot
      have hnot0 : {e, f} ∉ conflictLayer C0 2 := fun hp =>
        hnot (hC0layer2subC3 hp)
      calc
        (((conflictLinkLayer C3 e 3 ∩ conflictLinkLayer C3 f 3).card : ℕ) : ℝ) ≤
            ((conflictLinkLayer C e 3 ∩ conflictLinkLayer C f 3).card : ℕ) :=
          scratch_card_link_inter_le_of_layer_succ
            (hC3layer4.trans hC0layer4subC) e f
        _ ≤ Real.rpow d ((3 : ℕ) - eps / 3) := by
          simpa [eps] using scratch_commonLink_upper_of_not_mem_minimalBadCore
            H C hHuniform hCcard hdpos.le e f he hf hdisj hnot0
              (⟨2, by omega⟩ : Fin 3)
    · have := heps0
      linarith
  obtain ⟨A4, hA4, hIV4, hkill4⟩ := p4.exists_completion hHuniform
    hdegreeUpper hH heta hGamma (by simp) (fun a => ⟨(htrack a).1, (htrack a).2.1⟩)
    hreg hsource hobs htransfer hendpoint hhostLower
  let R := addCompletionLayer C3 A4
  have hA4uniform : IsUniform A4 4 :=
    (completionCandidates_uniform H C3 4).mono hA4
  have hkill4le : ∀ a, killedWeight H R (j a) (w3 a) ≤
      testTotal (w3 a) H (j a) / Real.rpow d eps := by
    intro a
    have hlim := scratch_stageKilledWeightLimit_le_final
      (ell := ell) (stage := 4) (eta := eta) (d := d)
      (X := testTotal (w3 a) H (j a)) hreg (by simp)
      (testTotal_nonneg (htrack3 a).1.1 H (j a))
    exact (hkill4 a).le.trans (by simpa [eps, R] using hlim)
  have hsurvive : ∀ a, IsTrackable H R (j a) ell d (eps / 5)
      (restrictWeight R (w a)) := by
    intro a
    have hscalar := htransfer.transferScalar_between heta hd
      (etaOld := 9 * eps / 40) (etaNew := eps / 5) (by
        have := heps0
        linarith)
    have hraw := scratch_restrictWeight_isTrackable_addCompletionLayer_target
      hd (by linarith [heps0]) (by linarith [heps0]) hscalar hA4uniform hIV4
      (htrack3 a) (hkill4le a)
    rw [restrictWeight_addCompletionLayer_comp C3 A4 (w a)] at hraw
    simpa [R, w3] using hraw
  let L2 : ι → ℝ := fun a =>
    stageKilledWeightLimit 2 d eps (testTotal (w a) H (j a))
  let L3 : ι → ℝ := fun a =>
    stageKilledWeightLimit 3 d eps (testTotal (w2 a) H (j a))
  let L4 : ι → ℝ := fun a =>
    stageKilledWeightLimit 4 d eps (testTotal (w3 a) H (j a))
  have hassembled := assemble_threeConcreteStagesWeighted H C0 C0 A2 A3 A4
    d eps j w L2 L3 L4 (fun a => (htrack a).2.2.1.1) hA2 hA3 hA4
    hIV2 hIV3 hIV4 (by simpa [L2, eps] using hkill2)
    (by simpa [L3, eps, C2, w2, C3] using hkill3)
    (by simpa [L4, eps, C2, C3, w3, R] using hkill4)
  have hdegreeSum :
      (∑ r ∈ Finset.Icc 2 4,
        (layerMaxDegree H R r : ℝ) /
          Real.rpow d ((r : ℝ) - 1)) ≤ 3 * Gamma := by
    exact htransfer.threeStage_normalizedDegreeSum heta hd hGamma
      (by simpa [R, C3, C2, eps] using hassembled.1) hbaseSum
  have hkillFinal : ∀ a, killedWeight H R (j a) (w a) ≤
      testTotal (w a) H (j a) / Real.rpow d eps := by
    intro a
    have hT2 : testTotal (w2 a) H (j a) ≤ testTotal (w a) H (j a) := by
      simpa [w2] using testTotal_restrictWeight_le H C2 (j a) (w a)
        (htrack a).2.2.1.1
    have hT3 : testTotal (w3 a) H (j a) ≤ testTotal (w a) H (j a) := by
      simpa [w3] using testTotal_restrictWeight_le H C3 (j a) (w a)
        (htrack a).2.2.1.1
    have hden : 0 < Real.rpow d (2 * eps) := Real.rpow_pos_of_pos hdpos _
    have hL3 : L3 a ≤
        stageKilledWeightLimit 3 d eps (testTotal (w a) H (j a)) := by
      dsimp [L3, stageKilledWeightLimit]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hT2 (by positivity)) hden.le
    have hL4 : L4 a ≤
        stageKilledWeightLimit 4 d eps (testTotal (w a) H (j a)) := by
      dsimp [L4, stageKilledWeightLimit]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hT3 (by positivity)) hden.le
    have hsum := hreg.threeStageKilledWeightLimits
      (testTotal_nonneg (htrack a).2.2.1.1 H (j a))
    exact (show killedWeight H R (j a) (w a) <
        testTotal (w a) H (j a) / Real.rpow d eps from by
      calc
        killedWeight H R (j a) (w a) < L2 a + L3 a + L4 a := by
          simpa [R, C3, C2] using hassembled.2 a
        _ ≤ stageKilledWeightLimit 2 d eps (testTotal (w a) H (j a)) +
            stageKilledWeightLimit 3 d eps (testTotal (w a) H (j a)) +
            stageKilledWeightLimit 4 d eps (testTotal (w a) H (j a)) := by
          dsimp [L2]
          linarith
        _ ≤ testTotal (w a) H (j a) / Real.rpow d eps := by
          simpa [stageKilledWeightLimit, eps] using hsum).le
  exact ⟨by
    exact regularizationCertificate_of_threeStages H C B A2 A3 A4 d eps Gamma ell j w
      hC (fun c hc => by rw [hCcard c hc]; omega) hGamma rfl hBdegree hA2
      hA3 hA4 hIV2 hIV3 hIV4 (by simpa [R, C3, C2] using hdegreeSum)
      (by simpa [R, C3, C2] using hkillFinal)
      (by simpa [R, C3, C2] using hsurvive)⟩

theorem exists_regularizationCertificate_of_raw
    (ell : ℕ) (hell : 4 ≤ ell) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta < eta0 →
        ∃ d0 : ℝ, ∀ d : ℝ, d0 ≤ d →
          ∀ (V ι : Type*) [DecidableEq V] [Fintype V] [Fintype ι],
            ∀ (H : Hypergraph V) (C : ConflictSystem V)
              (j : ι → ℕ) (w : ι → TestWeight V),
              IsUniform H 8 → IsConflictSystem H C →
              (∀ c ∈ C, c.card = 4) → eta < 1 → 1 ≤ d →
              ((vertexFinset H).card : ℝ) ≤
                Real.exp (Real.rpow d (eta ^ 3)) →
              (∀ v ∈ vertexFinset H,
                (1 - Real.rpow d (-eta)) * d ≤ (degree H v : ℝ) ∧
                (degree H v : ℝ) ≤ d) →
              (∀ s, s.card = 2 →
                (codegree H s : ℝ) ≤ Real.rpow d (1 - eta)) →
              IsBounded C d ell eta →
              ((Fintype.card ι : ℕ) : ℝ) ≤
                Real.exp (Real.rpow d (eta ^ 3)) →
              (∀ i, 1 ≤ j i ∧ j i ≤ 3 ∧
                IsTrackable H C (j i) ell d eta (w i)) →
              Nonempty (RegularizationCertificate H C d
                (rawRegularizationEps eta)
                (2 * (ell : ℝ) + 1) ell j w) := by
  refine ⟨rawRegularizationEta0, ?_, ?_⟩
  · norm_num [rawRegularizationEta0]
  · intro eta heta hetaSmall
    have hetaTenth : eta < 1 / 10 := by
      simpa [rawRegularizationEta0] using hetaSmall
    obtain ⟨dreg, hdreg⟩ :=
      exists_rawRegularizationCutoff ell eta hell heta hetaSmall
    obtain ⟨dsource, hdsource⟩ :=
      exists_rawSourceCutoff eta (2 * (ell : ℝ) + 1) 1
        (4 * (2 * (ell : ℝ) + 1)) heta
    obtain ⟨dobs, hdobs⟩ :=
      exists_rawObservableCutoff eta (2 * (ell : ℝ) + 1) 8 heta hetaTenth
    obtain ⟨dtransfer, hdtransfer⟩ := exists_rawTransferCutoff eta 32 heta
    obtain ⟨dendpoint, hdendpoint⟩ := exists_rawEndpointCutoff eta heta
    let d0 := max dreg (max dsource (max dobs (max dtransfer dendpoint)))
    refine ⟨d0, ?_⟩
    intro d hd0 V ι _ _ _ H C j w hHuniform hC hCcard heta1 hd
      hvertex hdegree hcodeg hbounded htestCard htrack
    have hreg : RawRegularizationCutoffSpec ell eta d :=
      hdreg d ((le_max_left _ _).trans hd0)
    have hsource : RawSourceCutoffSpec eta (2 * (ell : ℝ) + 1) 1
        (4 * (2 * (ell : ℝ) + 1)) d :=
      hdsource d (((le_max_left _ _).trans (le_max_right _ _)).trans hd0)
    have hobs : RawObservableCutoffSpec eta (2 * (ell : ℝ) + 1) 8 d :=
      hdobs d (((le_max_left _ _).trans (le_max_right _ _)
        |>.trans (le_max_right _ _)).trans hd0)
    have htransfer : RawTransferCutoffSpec eta 32 d :=
      hdtransfer d (((le_max_left _ _).trans (le_max_right _ _)
        |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans hd0)
    have hendpoint : RawEndpointCutoffSpec eta d :=
      hdendpoint d (((le_max_right _ _).trans (le_max_right _ _)
        |>.trans (le_max_right _ _) |>.trans (le_max_right _ _)).trans hd0)
    by_cases hH : H.Nonempty
    · exact exists_rawRegularization_nonempty H C d eta ell j w hHuniform hC
        hCcard heta heta1 hd hvertex hdegree hcodeg hbounded htestCard htrack
        hH hreg hsource hobs htransfer hendpoint
    · exact regularizationCertificate_of_not_nonempty_raw H C d eta ell j w
        hC hCcard hd htrack hH



end
end Erdos136.CFMRegularization

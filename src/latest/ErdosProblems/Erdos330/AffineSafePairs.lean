/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.CRTBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Affine safe-pair lemmas for Erdős Problem 330

The nonselected CRT coordinates use allowed residues of the form `x_i ≠ β_i`.
The safe-pair theorem is proved after subtracting `β`, where the allowed set
is the nonzero box.  This file packages that affine normalization.
-/

namespace Erdos330

open scoped Pointwise

def affineNormalize {ι : Type*} (p : ι → ℕ)
    (β x : ∀ i : ι, ZMod (p i)) : ∀ i : ι, ZMod (p i) :=
  fun i => x i - β i

def affineDoubleNormalize {ι : Type*} (p : ι → ℕ)
    (β x : ∀ i : ι, ZMod (p i)) : ∀ i : ι, ZMod (p i) :=
  fun i => x i - (β i + β i)

lemma affineNormalize_add {ι : Type*} (p : ι → ℕ)
    (β x y : ∀ i : ι, ZMod (p i)) :
    affineDoubleNormalize p β (x + y) = affineNormalize p β x + affineNormalize p β y := by
  funext i
  simp [affineNormalize, affineDoubleNormalize]
  ring

lemma affineNormalize_add_left {ι : Type*} (p : ι → ℕ)
    (β x : ∀ i : ι, ZMod (p i)) :
    affineNormalize p β (fun i => β i + x i) = x := by
  funext i
  simp [affineNormalize]

def shiftedNonzeroBox {ι : Type*} (p : ι → ℕ)
    (β : ∀ i : ι, ZMod (p i)) : Set (∀ i : ι, ZMod (p i)) :=
  {x | ∀ i, x i ≠ β i}

def affineLeftSafeSet {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    Set (∀ i : ι, ZMod (p i)) :=
  {x | affineNormalize p β x ∈ leftSafeSet p e data ν threshold}

def affineRightSafeSet {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    Set (∀ i : ι, ZMod (p i)) :=
  {x | affineNormalize p β x ∈ rightSafeSet p e data ν threshold}

theorem affineLeftSafeSet_subset_shiftedNonzeroBox {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    affineLeftSafeSet p β e data ν threshold ⊆ shiftedNonzeroBox p β := by
  intro x hx i hxi
  have hnonzero : affineNormalize p β x i ≠ 0 :=
    (leftSafeSet_subset_nonzeroBox p e data ν threshold hx) i
  exact hnonzero (by simp [affineNormalize, hxi])

theorem affineRightSafeSet_subset_shiftedNonzeroBox {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) (threshold : ℕ) :
    affineRightSafeSet p β e data ν threshold ⊆ shiftedNonzeroBox p β := by
  intro x hx i hxi
  have hnonzero : affineNormalize p β x i ≠ 0 :=
    (rightSafeSet_subset_nonzeroBox p e data ν threshold hx) i
  exact hnonzero (by simp [affineNormalize, hxi])

theorem affineSafePair_sum_union_eq_coordinateTarget_preimage {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i)
    (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) :
    ((affineLeftSafeSet p β e data true (safeLeftThreshold ι) +
        affineRightSafeSet p β e data true (safeRightThreshold ι)) ∪
      (affineLeftSafeSet p β e data false (safeLeftThreshold ι) +
        affineRightSafeSet p β e data false (safeRightThreshold ι))) =
      {z | affineDoubleNormalize p β z ∈ coordinateTarget p e} := by
  classical
  ext z
  constructor
  · intro hz
    change affineDoubleNormalize p β z ∈ coordinateTarget p e
    rcases hz with hz | hz
    · rcases hz with ⟨x, hx, y, hy, hxy⟩
      have hnorm : affineDoubleNormalize p β z =
          affineNormalize p β x + affineNormalize p β y := by
        rw [← hxy]
        exact affineNormalize_add p β x y
      rw [hnorm]
      exact safePair_sum_subset_coordinateTarget_thresholds p e data true ⟨_, hx, _, hy, rfl⟩
    · rcases hz with ⟨x, hx, y, hy, hxy⟩
      have hnorm : affineDoubleNormalize p β z =
          affineNormalize p β x + affineNormalize p β y := by
        rw [← hxy]
        exact affineNormalize_add p β x y
      rw [hnorm]
      exact safePair_sum_subset_coordinateTarget_thresholds p e data false ⟨_, hx, _, hy, rfl⟩
  · intro hz
    change affineDoubleNormalize p β z ∈ coordinateTarget p e at hz
    have hnorm_mem : affineDoubleNormalize p β z ∈
        ((leftSafeSet p e data true (safeLeftThreshold ι) +
            rightSafeSet p e data true (safeRightThreshold ι)) ∪
          (leftSafeSet p e data false (safeLeftThreshold ι) +
            rightSafeSet p e data false (safeRightThreshold ι))) := by
      rw [safePair_sum_union_eq_coordinateTarget p hp7 e data]
      exact hz
    rcases hnorm_mem with htrue | hfalse
    · rcases htrue with ⟨x, hx, y, hy, hxy⟩
      refine Or.inl ⟨fun i => β i + x i, ?_, fun i => β i + y i, ?_, ?_⟩
      · change affineNormalize p β (fun i => β i + x i) ∈
          leftSafeSet p e data true (safeLeftThreshold ι)
        rw [affineNormalize_add_left]
        exact hx
      · change affineNormalize p β (fun i => β i + y i) ∈
          rightSafeSet p e data true (safeRightThreshold ι)
        rw [affineNormalize_add_left]
        exact hy
      · funext i
        have hcoord := congrFun hxy i
        dsimp [affineDoubleNormalize] at hcoord
        simp at hcoord ⊢
        linear_combination hcoord
    · rcases hfalse with ⟨x, hx, y, hy, hxy⟩
      refine Or.inr ⟨fun i => β i + x i, ?_, fun i => β i + y i, ?_, ?_⟩
      · change affineNormalize p β (fun i => β i + x i) ∈
          leftSafeSet p e data false (safeLeftThreshold ι)
        rw [affineNormalize_add_left]
        exact hx
      · change affineNormalize p β (fun i => β i + y i) ∈
          rightSafeSet p e data false (safeRightThreshold ι)
        rw [affineNormalize_add_left]
        exact hy
      · funext i
        have hcoord := congrFun hxy i
        dsimp [affineDoubleNormalize] at hcoord
        simp at hcoord ⊢
        linear_combination hcoord

theorem affineLeftRight_sum_subset_coordinateTarget {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) :
    (affineLeftSafeSet p β e data ν (safeLeftThreshold ι) +
        affineRightSafeSet p β e data ν (safeRightThreshold ι)) ⊆
      {z | affineDoubleNormalize p β z ∈ coordinateTarget p e} := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, hxy⟩
  change affineDoubleNormalize p β z ∈ coordinateTarget p e
  have hnorm : affineDoubleNormalize p β z =
      affineNormalize p β x + affineNormalize p β y := by
    rw [← hxy]
    exact affineNormalize_add p β x y
  rw [hnorm]
  exact safePair_sum_subset_coordinateTarget_thresholds p e data ν ⟨_, hx, _, hy, rfl⟩

theorem affineRightLeft_sum_subset_coordinateTarget {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (β e : ∀ i : ι, ZMod (p i))
    (data : ∀ i, SafePairData (ZMod (p i)) (e i)) (ν : Bool) :
    (affineRightSafeSet p β e data ν (safeRightThreshold ι) +
        affineLeftSafeSet p β e data ν (safeLeftThreshold ι)) ⊆
      {z | affineDoubleNormalize p β z ∈ coordinateTarget p e} := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, hxy⟩
  change affineDoubleNormalize p β z ∈ coordinateTarget p e
  have hnorm : affineDoubleNormalize p β z =
      affineNormalize p β y + affineNormalize p β x := by
    rw [← hxy]
    funext i
    simp [affineDoubleNormalize, affineNormalize]
    ring
  rw [hnorm]
  exact safePair_sum_subset_coordinateTarget_thresholds p e data ν ⟨_, hy, _, hx, rfl⟩

theorem shiftedNonzeroBox_add_self_eq_univ {ι : Type*}
    (p : ι → ℕ) [∀ i, Fact (Nat.Prime (p i))]
    (hp7 : ∀ i, 7 ≤ p i) (β : ∀ i : ι, ZMod (p i)) :
    ((shiftedNonzeroBox p β : Set (∀ i, ZMod (p i))) +
      (shiftedNonzeroBox p β : Set (∀ i, ZMod (p i)))) = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro z
  let target : ∀ i : ι, ZMod (p i) := fun i => z i - (β i + β i)
  let left : ∀ i : ι, ZMod (p i) := fun i =>
    β i + (nonzeroAddPairZMod (p i) (hp7 i) (target i)).left
  let right : ∀ i : ι, ZMod (p i) := fun i =>
    β i + (nonzeroAddPairZMod (p i) (hp7 i) (target i)).right
  refine ⟨left, ?_, right, ?_, ?_⟩
  · intro i hleft
    have hnonzero := (nonzeroAddPairZMod (p i) (hp7 i) (target i)).left_ne_zero
    apply hnonzero
    linear_combination hleft
  · intro i hright
    have hnonzero := (nonzeroAddPairZMod (p i) (hp7 i) (target i)).right_ne_zero
    apply hnonzero
    linear_combination hright
  · funext i
    have hsum := (nonzeroAddPairZMod (p i) (hp7 i) (target i)).sum_eq
    dsimp [left, right, target] at hsum ⊢
    linear_combination hsum

end Erdos330

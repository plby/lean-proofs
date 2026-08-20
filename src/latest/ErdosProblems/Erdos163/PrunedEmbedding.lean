/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.PrunedHost
import ErdosProblems.Erdos163.ConcentratedEmbedding

/-!
# From an all-direction moment through pruning to concentrated embedding

This file packages the deterministic part of Lee's Lemmas 6.2 and 5.3.
The only hypotheses left to the final numerical assembly are explicit
cardinality, moment, cutoff, and finite union-bound inequalities.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace PrunedEmbedding

noncomputable section

universe u v

variable {X : Type u} {P : Type v}
  [Fintype X] [DecidableEq X] [LinearOrder X]
  [Fintype P] [DecidableEq P] [LinearOrder P]

def failureSum
    {N r : ℕ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    (part : X → P) (color : P → Fin r)
    (B : Fin r → Finset (Fin N)) (q sizeTail : P → ℝ)
    (Λ : ℕ → ℝ) (tail : X → ℝ) : ℝ :=
  let coord : X → Type u := fun x : X =>
    ↑(RandomGreedy.forwardNeighbors H x)
  let base := fun x : X =>
    fun y : RandomGreedy.forwardNeighbors H x => B (color (part y))
  let activeCard : HostPartition.SamplingTest (P := P) X coord base → ℕ
    | Sum.inl p => (B (color p)).card
    | Sum.inr z =>
        (FiniteDefect.commonNeighbors G z.2.1
          (B (color (part z.1)))).card
  let which : HostPartition.SamplingTest (P := P) X coord base → P
    | Sum.inl p => p
    | Sum.inr z => part z.1
  (∑ k, Real.exp
    (-2 * (q (which k) * (activeCard k : ℝ) / 2) ^ 2 /
      (activeCard k : ℝ))) +
  (∑ p : P, Real.exp (-2 * (sizeTail p) ^ 2 / (N : ℝ))) +
  ∑ x : X, Real.exp
    (-2 * (tail x) ^ 2 /
      ∑ _i : Fin N,
        (Λ (Fintype.card (RandomGreedy.forwardNeighbors H x))) ^ 2)

theorem hasCopy_of_pruned_all_direction_parameters
    {N r oldθ τ D R M : ℕ} {ε γ μ : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    (part : X → P) (color : P → Fin r) (threshold : P → ℕ)
    (A : Fin r → Finset (Fin N)) (q : P → ℝ) (Λ : ℕ → ℝ)
    (tail meanBound : X → ℝ) (sizeTail : P → ℝ)
    (defaultTarget : X) (defaultHost : Fin N)
    (hr : 2 ≤ r) (hD : 0 < D) (holdθ : 0 < oldθ)
    (hτ : 0 < τ) (hτold : (τ : ℝ) ≤ (oldθ : ℝ) / 2)
    (hAcard : ∀ j, oldθ ≤ (A j).card)
    (hbad : (PrunedHost.allBadLevels (D := D) (θ := oldθ)
      (s := 4 * D) G A Λ).card ≤ R)
    (hτR : τ + R ≤ oldθ)
    (hAmoment : ∀ j,
      FiniteDefect.moment G oldθ (4 * D)
        (fun _ : Fin D => HostDirections.unionExcept A j) (A j) ≤ ε)
    (hε : 0 ≤ ε)
    (hN : 1 ≤ N) (hM : 0 < M) (hMold : M < oldθ) (hRM : 2 * R < M)
    (hcommonNumeric : (N : ℝ) ^ D * ε <
      ((oldθ : ℝ) / M) ^ (4 * D))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (horder : ∀ ⦃a b⦄, H.Adj a b → (a < b ↔ part a < part b))
    (hcolor : ∀ ⦃a b⦄, H.Adj a b → color (part a) ≠ color (part b))
    (hforward : ∀ x, (RandomGreedy.forwardNeighbors H x).card ≤ D)
    (hthreshold : ∀ p, 0 < threshold p)
    (hpartSize : ∀ x, 2 * (RandomGreedy.partVertices part x).card ≤
      threshold (part x))
    (hqpos : ∀ p, 0 < q p) (hqsum : ∑ p, q p ≤ 1)
    (hthresholdSample : ∀ p,
      (threshold p : ℝ) ≤ q p * τ / 2)
    (hΛ : ∀ k, k ≤ D → 0 < Λ k)
    (hmeanNumeric : ∀ x,
      (∏ y : RandomGreedy.forwardNeighbors H x, q (part y)) *
          ((N : ℝ) ^ Fintype.card (RandomGreedy.forwardNeighbors H x) * ε) +
        (Fintype.card (RandomGreedy.forwardNeighbors H x) : ℝ) ^ 2 *
          ((N : ℝ) ^
            (Fintype.card (RandomGreedy.forwardNeighbors H x) - 1) * ε) ≤
        meanBound x)
    (htail : ∀ x, 0 ≤ tail x)
    (hμ : 0 ≤ μ)
    (hnormalized : ∀ x,
      meanBound x + tail x ≤ μ *
        ∏ y : RandomGreedy.forwardNeighbors H x,
          (q (part y) *
            ((PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
              G A Λ (color (part y))).card : ℝ) / 2))
    (hγ : 1 ≤ γ)
    (hsizeTail : ∀ p, 0 ≤ sizeTail p)
    (hsize : ∀ p,
      q p * ((PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
          G A Λ (color p)).card : ℝ) + sizeTail p ≤
        γ * threshold p)
    (htotal :
      ∑ x : X, (2 / (threshold (part x) : ℝ)) *
        (2 * RandomGreedy.branchCoefficient (2 * γ) D * μ) < 1)
    (hfail : failureSum G H part color
      (fun j => PrunedHost.prunedLevels
        (D := D) (θ := oldθ) (s := 4 * D) G A Λ j)
      q sizeTail Λ tail < 1) :
    HasCopy H G := by
  let B : Fin r → Finset (Fin N) := fun j =>
    PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D) G A Λ j
  have hBcard : ∀ j, τ ≤ (B j).card := by
    intro j
    have hsum := PrunedHost.prunedLevels_card_add_bad_ge
      (D := D) (θ := oldθ) (s := 4 * D) G A Λ j
    have hAj := hAcard j
    dsimp [B]
    omega
  have hU : ∀ j, (HostDirections.unionExcept A j).Nonempty := by
    intro j
    classical
    by_cases hj0 : j.1 = 0
    · let k : Fin r := ⟨1, hr⟩
      have hkj : k ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        simp [k, hj0] at hv
      have hk : (A k).Nonempty :=
        Finset.card_pos.mp (holdθ.trans_le (hAcard k))
      exact hk.mono (HostDirections.subset_unionExcept A hkj)
    · let k : Fin r := ⟨0, by omega⟩
      have hkj : k ≠ j := by
        intro h
        apply hj0
        exact (congrArg Fin.val h).symm
      have hk : (A k).Nonempty :=
        Finset.card_pos.mp (holdθ.trans_le (hAcard k))
      exact hk.mono (HostDirections.subset_unionExcept A hkj)
  have hbaseSubset : ∀ x (y : RandomGreedy.forwardNeighbors H x),
      B (color (part y)) ⊆ HostDirections.unionExcept A (color (part x)) := by
    intro x y
    have hyAdj : H.Adj x y := (Finset.mem_filter.mp y.property).2.1
    exact (PrunedHost.prunedLevels_subset
      (D := D) (θ := oldθ) (s := 4 * D) G A Λ (color (part y))).trans
      (HostDirections.subset_unionExcept A (hcolor hyAdj).symm)
  have hlarge : ∀ x (g : RandomGreedy.forwardNeighbors H x → Fin N),
      g ∈ FiniteDefect.familyTuples
        (fun y : RandomGreedy.forwardNeighbors H x => B (color (part y))) →
      2 * R < (FiniteDefect.commonNeighbors G g
        (A (color (part x)))).card := by
    intro x g hg
    apply hRM.trans
    have hdim : Fintype.card (RandomGreedy.forwardNeighbors H x) ≤ D := by
      simpa only [Fintype.card_coe] using hforward x
    exact PreparedHost.commonNeighbors_card_gt_of_all_direction G
      (fun y : RandomGreedy.forwardNeighbors H x => B (color (part y)))
      (HostDirections.unionExcept A (color (part x))) (A (color (part x)))
      hN (hU (color (part x))) hdim (fun y => hbaseSubset x y)
      hM hMold hε (hAmoment (color (part x))) hcommonNumeric g hg
  have hdom : ∀ x (g : RandomGreedy.forwardNeighbors H x → Fin N),
      g ∈ FiniteDefect.familyTuples
        (fun y : RandomGreedy.forwardNeighbors H x => B (color (part y))) →
      FiniteDefect.defectPower G τ g (B (color (part x))) (4 * D) ≤
        FiniteDefect.defectPower G oldθ g (A (color (part x))) (4 * D) := by
    intro x g hg
    exact PrunedHost.defectPower_prunedLevels_le G A Λ (color (part x)) g
      hτold hbad (hlarge x g hg)
  have hcommonPos : ∀ x (g : RandomGreedy.forwardNeighbors H x → Fin N),
      g ∈ FiniteDefect.familyTuples
        (fun y : RandomGreedy.forwardNeighbors H x => B (color (part y))) →
        0 < (FiniteDefect.commonNeighbors G g (B (color (part x)))).card := by
    intro x g hg
    exact PrunedHost.commonNeighbors_prunedLevels_pos G A Λ (color (part x)) g
      hbad (hlarge x g hg)
  let cutoff : X → Fin N → ℝ := fun x _ =>
    Λ (Fintype.card (RandomGreedy.forwardNeighbors H x))
  have hcutoff : ∀ x i, 0 ≤ cutoff x i := by
    intro x i
    apply (hΛ _ ?_).le
    simpa only [Fintype.card_coe] using hforward x
  have hincident : ∀ x i,
      PartitionConcentration.incident
        (FiniteDefect.familyTuples
          (fun y : RandomGreedy.forwardNeighbors H x => B (color (part y))))
        (fun g => FiniteDefect.defectPower G τ g
          (B (color (part x))) (4 * D)) i ≤ cutoff x i := by
    intro x i
    let I := RandomGreedy.forwardNeighbors H x
    let base : I → Finset (Fin N) := fun y => B (color (part y))
    let weight : (I → Fin N) → ℝ := fun g =>
      FiniteDefect.defectPower G τ g (B (color (part x))) (4 * D)
    have hdim : Fintype.card I ≤ D := by
      simpa only [I, Fintype.card_coe] using hforward x
    by_cases hi : ∃ y : I, i ∈ base y
    · obtain ⟨y, hiy⟩ := hi
      have hle := PreparedHost.incident_le_of_domination G base
        (HostDirections.unionExcept A (color (part x))) (A (color (part x)))
        weight (fun z => hbaseSubset x z)
        (fun g hg => ⟨FiniteDefect.defectPower_nonneg G τ g
          (B (color (part x))) (4 * D), hdom x g hg⟩) i
      have hlt := PrunedHost.incidentWeight_lt_of_mem_prunedLevels
        (D := D) (θ := oldθ) (s := 4 * D) G A Λ
        hdim (color (part x)) (color (part y)) hiy
      exact hle.trans hlt.le
    · have hz := PartitionConcentration.incident_familyTuples_eq_zero_of_not_mem
        base weight i (by simpa only [not_exists] using hi)
      change PartitionConcentration.incident
        (FiniteDefect.familyTuples base) weight i ≤ cutoff x i
      rw [hz]
      exact hcutoff x i
  have hmean : ∀ x,
      Erdos136.McDiarmid.weightedMean
        (fun _ : Fin N => HostPartition.labelWeight q)
        (PartitionConcentration.rawStatistic
          (FiniteDefect.familyTuples
            (fun y : RandomGreedy.forwardNeighbors H x => B (color (part y))))
          (fun y => part y)
          (fun g => FiniteDefect.defectPower G τ g
            (B (color (part x))) (4 * D))) ≤ meanBound x := by
    intro x
    let I := RandomGreedy.forwardNeighbors H x
    let base : I → Finset (Fin N) := fun y => B (color (part y))
    let weight : (I → Fin N) → ℝ := fun g =>
      FiniteDefect.defectPower G τ g (B (color (part x))) (4 * D)
    have hdim : Fintype.card I ≤ D := by
      simpa only [I, Fintype.card_coe] using hforward x
    have hraw := PreparedHost.weightedMean_raw_le_of_all_direction
      (P := P) G q (fun y : I => part y) base
      (HostDirections.unionExcept A (color (part x))) (A (color (part x)))
      weight (hU (color (part x))) hdim (fun p => (hqpos p).le)
      hqsum hε (fun y => hbaseSubset x y)
      (fun g hg => ⟨FiniteDefect.defectPower_nonneg G τ g
        (B (color (part x))) (4 * D), hdom x g hg⟩)
      (hAmoment (color (part x)))
    exact hraw.trans (by simpa [I] using hmeanNumeric x)
  apply ConcentratedEmbedding.hasCopy_of_concentrated_parameters
    G H part color threshold B q cutoff tail meanBound sizeTail
    defaultTarget defaultHost hD hτ hBcard hcommonPos hpart horder hthreshold
    hpartSize hforward hqpos hqsum hthresholdSample hcutoff hincident htail
    hmean hμ hnormalized hγ hsizeTail hsize htotal
  simpa [failureSum, B, cutoff] using hfail

end
end PrunedEmbedding
end Erdos163

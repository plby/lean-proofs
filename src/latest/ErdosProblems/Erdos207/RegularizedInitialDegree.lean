/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizedForbiddenUnion
import ErdosProblems.Erdos207.FiniteHypergraphEmbedding
import ErdosProblems.Erdos207.KSSSInitialMargins

/-! # Actual regularized degrees provide the initial configuration trajectories -/

namespace Erdos207

open Finset

noncomputable section

theorem regularizedForbiddenUnion_order_family
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (q j : ℕ) (Lstar : ℕ → Finset (Finset I))
    (huniform : ∀ r ∈ Icc 4 q, ∀ E ∈ Lstar r, E.card = r - 2) (hj : j ∈ Icc 4 q) :
    forbiddenFamilyOfOrder (regularizedForbiddenUnion e q Lstar) j = (Lstar j).image (Finset.map e) := by
  ext E
  constructor
  · intro hE
    obtain ⟨hE, hcard⟩ := mem_forbiddenFamilyOfOrder.mp hE
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hE
    obtain ⟨r, hr, hCr⟩ := mem_biUnion.mp hC
    rw [card_map, huniform r hr C hCr] at hcard
    have hrj : r = j := by have hr4 := (mem_Icc.mp hr).1; have hj4 := (mem_Icc.mp hj).1; omega
    exact mem_image.mpr ⟨C, hrj ▸ hCr, rfl⟩
  · intro hE
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hE
    apply mem_forbiddenFamilyOfOrder.mpr
    exact ⟨mem_image.mpr ⟨C, mem_biUnion.mpr ⟨j, hj, hC⟩, rfl⟩, by
      rw [card_map, huniform j hj C hC]⟩

theorem regularizedForbiddenUnion_root_degree
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (q j : ℕ) (Lstar : ℕ → Finset (Finset I))
    (huniform : ∀ r ∈ Icc 4 q, ∀ E ∈ Lstar r, E.card = r - 2) (hj : j ∈ Icc 4 q) (i : I) :
    ((forbiddenFamilyOfOrder (regularizedForbiddenUnion e q Lstar) j).filter fun C ↦ e i ∈ C).card =
      finiteHypergraphDegree (Lstar j) i := by
  rw [regularizedForbiddenUnion_order_family e q j Lstar huniform hj]
  exact finiteHypergraphDegree_image_map e (Lstar j) i

theorem finiteHypergraph_degree_max_error_le_gap
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] (F : Finset (Finset I)) (i : I) :
    |(finiteHypergraphDegree F i : ℝ) - finiteHypergraphMaxDegree F| ≤ finiteHypergraphDegreeGap F := by
  have hmin := finiteHypergraphMinDegree_le F i
  have hmax := finiteHypergraphDegree_le_max F i
  have hminmax := finiteHypergraphMinDegree_le_max F
  have hmax' : (finiteHypergraphDegree F i : ℝ) ≤ finiteHypergraphMaxDegree F := by exact_mod_cast hmax
  have hmin' : (finiteHypergraphMinDegree F : ℝ) ≤ finiteHypergraphDegree F i := by exact_mod_cast hmin
  rw [abs_of_nonpos (sub_nonpos.mpr hmax'), finiteHypergraphDegreeGap, Nat.cast_sub hminmax]
  linarith

def regularizedTrajectoryCoefficient
    {I : Type*} [Fintype I] [DecidableEq I] (Lstar : ℕ → Finset (Finset I)) (A : ℝ) (d : ℕ) : ℝ :=
  (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ) / A ^ d

theorem regularizedTrajectoryCoefficient_nonneg
    {I : Type*} [Fintype I] [DecidableEq I] (Lstar : ℕ → Finset (Finset I)) (A : ℝ) (hA : 0 ≤ A) (d : ℕ) :
    0 ≤ regularizedTrajectoryCoefficient Lstar A d := div_nonneg (Nat.cast_nonneg _) (pow_nonneg hA _)

theorem regularizedTrajectoryCoefficient_target
    {I : Type*} [Fintype I] [DecidableEq I] (Lstar : ℕ → Finset (Finset I)) (A : ℝ) (hA : A ≠ 0) (d : ℕ) :
    regularizedTrajectoryCoefficient Lstar A d * A ^ d = finiteHypergraphMaxDegree (Lstar (d + 3)) :=
  div_mul_cancel₀ _ (pow_ne_zero _ hA)

theorem regularizedTrajectoryCoefficient_scaled_le
    {I : Type*} [Fintype I] [DecidableEq I] (Lstar : ℕ → Finset (Finset I))
    (A E coeff : ℝ) (d : ℕ) (hA : 0 < A) (hE : 0 < E)
    (hdegree : (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ) ≤ coeff * (A / E) ^ d) :
    regularizedTrajectoryCoefficient Lstar A d * E ^ d ≤ coeff := by
  calc
    _ = (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ) / (A / E) ^ d := by
      unfold regularizedTrajectoryCoefficient
      rw [div_pow]
      field_simp
    _ ≤ coeff := (div_le_iff₀ (pow_pos (div_pos hA hE) d)).2 hdegree

theorem regularized_initial_regularity
    {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] [Nonempty I]
    (e : I ↪ TripleOn V) (q : ℕ) (Lstar : ℕ → Finset (Finset I))
    (huniform : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, E.card = j - 2)
    (S₀ : GreedyStateOn V) (Q₀ : Finset (Finset V)) (A E eta : ℝ) (hA : 0 < A)
    (hsupport : S₀.available ⊆ univ.map e)
    (hpair : ∀ P ∈ Q₀, |((availableTrianglesContainingPair S₀ P).card : ℝ) - 3 * A / E| ≤ eta * (3 * A / E))
    (hgap : ∀ j ∈ Icc 4 q, (finiteHypergraphDegreeGap (Lstar j) : ℝ) ≤ eta * (A / E) ^ (j - 3)) :
    KSSSInitialRegularity (regularizedForbiddenUnion e q Lstar) S₀ q Q₀
      (regularizedTrajectoryCoefficient Lstar A) E A eta := by
  refine ⟨hpair, ?_⟩
  intro T hT j hj
  obtain ⟨i, _, rfl⟩ := mem_map.mp (hsupport hT)
  rw [regularizedForbiddenUnion_root_degree e q j Lstar huniform hj i,
    regularizedTrajectoryCoefficient_target Lstar A hA.ne']
  have hj' : j - 3 + 3 = j := by have h := (mem_Icc.mp hj).1; omega
  rw [hj']
  exact (finiteHypergraph_degree_max_error_le_gap (Lstar j) i).trans (hgap j hj)

end

end Erdos207

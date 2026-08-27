/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBatchConcentration

/-! # Deterministic simultaneous batch partitions of the original edge labels -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {I K J α : Type*} [Fintype I] [Fintype K] [Fintype J] [DecidableEq J]

omit [Fintype J] in
theorem categoricalDegree_reindex (e : K ≃ I) (w : I → ℝ) (a : K → Option J) (j : J) :
    categoricalDegree (fun k => w (e k)) a j =
      categoricalDegree w (fun i => a (e.symm i)) j := by
  simpa only [categoricalDegree, e.symm_apply_apply] using
    e.sum_comp (fun i => if a (e.symm i) = some j then w i else 0)

variable [DecidableEq α]

omit [DecidableEq α] in
theorem exists_categorical_partition (V : Finset α) (p : J → ℝ) (w : I → α → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1)
    (hw : ∀ i, ∀ v ∈ V, 0 ≤ w i v) {b t : ℝ} (hb : 0 ≤ b)
    (hwb : ∀ i, ∀ v ∈ V, w i v ≤ b) (ht : 0 ≤ t)
    (hsmall : 2 * (V.card : ℝ) * Fintype.card J *
      Real.exp (-2 * t ^ 2 / ((Fintype.card I : ℝ) * b ^ 2)) < 1) :
    ∃ a : I → Option J, ∀ v ∈ V, ∀ j,
      |categoricalDegree (fun i => w i v) a j - p j * ∑ i, w i v| < t := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  obtain ⟨a, ha⟩ := exists_numbered_categorical_partition V p (fun k => w (e k))
    hp hpsum (fun k => hw (e k)) hb (fun k => hwb (e k)) ht hsmall
  refine ⟨fun i => a (e.symm i), fun v hv j => ?_⟩
  have h := ha v hv j
  rw [categoricalDegree_reindex e (fun i => w i v) a j, e.sum_comp (fun i => w i v)] at h
  exact h

theorem batch_degree_target_error {d C p z t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcenter : |z - p * d| < t) (hdegree : |d - C| ≤ t) : |z - p * C| < 2 * t := by
  have ht : 0 ≤ t := (abs_nonneg _).trans hdegree
  calc
    |z - p * C| = |(z - p * d) + p * (d - C)| := congrArg abs (by ring)
    _ ≤ |z - p * d| + |p * (d - C)| := abs_add_le _ _
    _ = |z - p * d| + p * |d - C| := by rw [abs_mul, abs_of_nonneg hp0]
    _ < t + t := add_lt_add_of_lt_of_le hcenter
      ((mul_le_mul_of_nonneg_left hdegree hp0).trans (by nlinarith))
    _ = 2 * t := by ring

namespace FiniteEdgeFamily

variable {Ω : Type*} [Fintype Ω]

theorem exists_label_partition (F : FiniteEdgeFamily I Ω α) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1) {b t : ℝ} (hb : 0 ≤ b)
    (hcap : ∀ i, ∀ v ∈ F.vertices, F.vertexMass i v ≤ b) (ht : 0 ≤ t)
    (hsmall : 2 * (F.vertices.card : ℝ) * Fintype.card J *
      Real.exp (-2 * t ^ 2 / ((Fintype.card I : ℝ) * b ^ 2)) < 1) :
    ∃ a : I → Option J, ∀ v ∈ F.vertices, ∀ j,
      |(F.restrictLabels (batchLabels a j)).degree v - p j * F.degree v| < t := by
  obtain ⟨a, ha⟩ := exists_categorical_partition F.vertices p F.vertexMass hp hpsum
    (fun i v _ => F.vertexMass_nonneg i v) hb hcap ht hsmall
  refine ⟨a, fun v hv j => ?_⟩
  rw [batchLabels_degree]
  exact ha v hv j

theorem exists_label_partition_target (F : FiniteEdgeFamily I Ω α) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1) {b t C : ℝ} (hb : 0 ≤ b)
    (hcap : ∀ i, ∀ v ∈ F.vertices, F.vertexMass i v ≤ b) (ht : 0 ≤ t)
    (hdegree : ∀ v ∈ F.vertices, |F.degree v - C| ≤ t)
    (hsmall : 2 * (F.vertices.card : ℝ) * Fintype.card J *
      Real.exp (-2 * t ^ 2 / ((Fintype.card I : ℝ) * b ^ 2)) < 1) :
    ∃ a : I → Option J, ∀ v ∈ F.vertices, ∀ j,
      |(F.restrictLabels (batchLabels a j)).degree v - p j * C| < 2 * t := by
  obtain ⟨a, ha⟩ := F.exists_label_partition p hp hpsum hb hcap ht hsmall
  refine ⟨a, fun v hv j => ?_⟩
  exact batch_degree_target_error (hp j) (categorical_probability_le_one p hp hpsum j)
    (ha v hv j) (hdegree v hv)

omit [Fintype J] in
theorem batchLabels_nonempty_of_target (F : FiniteEdgeFamily I Ω α)
    (a : I → Option J) (j : J) {v : α} {T t : ℝ}
    (hdegree : |(F.restrictLabels (batchLabels a j)).degree v - T| < 2 * t)
    (htarget : 2 * t ≤ T) : (batchLabels a j).Nonempty := by
  apply F.restrictLabels_nonempty_of_degree_pos _ v
  linarith [(abs_lt.mp hdegree).1]

end FiniteEdgeFamily

end

end Erdos4b.FGKMT

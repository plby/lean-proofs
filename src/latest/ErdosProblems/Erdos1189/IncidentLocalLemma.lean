/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A coordinate-weight form of the box local lemma.
Informal argument: group dependency factors by shared coordinates and use
the product lower bound 1 - sum(w) <= product(1-w).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GridLocalLemma
import ErdosProblems.Erdos1189.AvoidanceProducts

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]

lemma boxNeighbours_eq_biUnion [DecidableEq α] (H : α → Box q) (A : Finset α) (a : α) :
    boxNeighbours H A a = (fixed (H a)).biUnion (fun i => A.filter (fun b => i ∈ fixed (H b))) := by
  classical
  ext b
  simp only [boxNeighbours, mem_filter, mem_biUnion, Finset.not_disjoint_iff]
  aesop

theorem coordinate_local_lemma (H : α → Box q) (A : Finset α) (w : α → ℝ) {c : ℝ}
    (hq : ∀ i, 0 < q i) (hc : c < 1)
    (hfixed : ∀ a ∈ A, (fixed (H a)).Nonempty) (hw : ∀ a ∈ A, 0 ≤ w a)
    (hlocal : ∀ i, (∑ a ∈ A with i ∈ fixed (H a), w a) ≤ c)
    (hprob : ∀ a ∈ A, finiteProbability (boxEvent (H a)) ≤
      w a * (1 - c) ^ (fixed (H a)).card) : ¬ CoversOn H A Set.univ := by
  classical
  have hwc : ∀ a ∈ A, w a ≤ c := by
    intro a ha
    obtain ⟨i, hi⟩ := hfixed a ha
    have hs := single_le_sum (s := A.filter (fun b => i ∈ fixed (H b)))
      (fun b hb => hw b (mem_filter.mp hb).1)
      (mem_filter.mpr ⟨ha, hi⟩)
    exact hs.trans (hlocal i)
  have hw1 : ∀ a ∈ A, 0 ≤ w a ∧ w a < 1 := fun a ha => ⟨hw a ha, (hwc a ha).trans_lt hc⟩
  apply box_local_lemma H A w hq hw1
  intro a ha
  have hprod : (1 - c) ^ (fixed (H a)).card ≤ ∏ b ∈ boxNeighbours H A a, (1 - w b) := by
    rw [boxNeighbours_eq_biUnion]
    calc
      _ = ∏ i ∈ fixed (H a), (1 - c) := (prod_const _).symm
      _ ≤ ∏ i ∈ fixed (H a), ∏ b ∈ A with i ∈ fixed (H b), (1 - w b) := by
        apply prod_le_prod
        · intro i _
          exact sub_nonneg.mpr hc.le
        · intro i _
          exact (sub_le_sub_left (hlocal i) 1).trans (one_sub_sum_le_product _ w
            (fun b hb => ⟨hw b (mem_filter.mp hb).1, (hw1 b (mem_filter.mp hb).1).2.le⟩))
      _ ≤ _ := product_biUnion_ge _ _ _ (fun i _ b hb =>
        ⟨sub_nonneg.mpr (hw1 b (mem_filter.mp hb).1).2.le,
          sub_le_self _ (hw b (mem_filter.mp hb).1)⟩)
  exact (hprob a ha).trans (mul_le_mul_of_nonneg_left hprod (hw a ha))

noncomputable def localBoxWeight (H : Box q) : ℝ :=
  (8 / 7 : ℝ) ^ (fixed H).card * finiteProbability (boxEvent H)

/-- Every nontrivial box cover has a coordinate with large incident weight. -/
theorem exists_large_incident_weight (H : α → Box q) (A : Finset α)
    (hq : ∀ i, 0 < q i) (hfixed : ∀ a ∈ A, (fixed (H a)).Nonempty)
    (hcover : CoversOn H A Set.univ) :
    ∃ i, (1 / 8 : ℝ) < ∑ a ∈ A with i ∈ fixed (H a), localBoxWeight (H a) := by
  classical
  by_contra hnot
  push Not at hnot
  apply coordinate_local_lemma H A (fun a => localBoxWeight (H a)) hq
    (by norm_num : (1 / 8 : ℝ) < 1) hfixed
    (fun a _ => mul_nonneg (by positivity) (finiteProbability_nonneg _)) hnot ?_ hcover
  intro a _
  apply le_of_eq
  unfold localBoxWeight
  calc
    _ = ((8 / 7 : ℝ) * (1 - 1 / 8)) ^ (fixed (H a)).card *
        finiteProbability (boxEvent (H a)) := by norm_num
    _ = _ := by rw [mul_pow]; ring

end Erdos1189.Grid

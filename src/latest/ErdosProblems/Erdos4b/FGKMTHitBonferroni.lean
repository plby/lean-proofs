/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTIndependentEdgeIntersection

/-! # Two-term finite inclusion--exclusion for edge hit probabilities -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

theorem hitMass_nonneg (F : FiniteEdgeFamily I Ω α) (i : I) (e : Finset α) :
    0 ≤ F.hitMass i e :=
  Finset.sum_nonneg fun w _hw => ite_nonneg (F.mass_nonneg i w) le_rfl

theorem hitMass_le_one (F : FiniteEdgeFamily I Ω α) (i : I) (e : Finset α) :
    F.hitMass i e ≤ 1 := by
  calc
    _ ≤ ∑ w, F.mass i w := Finset.sum_le_sum fun w _hw => by
      split_ifs
      · exact le_rfl
      · exact F.mass_nonneg i w
    _ = _ := F.mass_sum_one i

theorem sum_vertex_indicator_le_hit_add_pairs (e A : Finset α) {m : ℝ} (hm : 0 ≤ m) :
    (∑ v ∈ e, if v ∈ A then m else 0) ≤
      (if (e ∩ A).Nonempty then m else 0) +
        ∑ v ∈ e, ∑ u ∈ e.erase v, if v ∈ A ∧ u ∈ A then m else 0 := by
  have hpairs (v : α) :
      0 ≤ ∑ u ∈ e.erase v, if v ∈ A ∧ u ∈ A then m else 0 :=
    Finset.sum_nonneg fun u _hu => ite_nonneg hm le_rfl
  by_cases hh : (e ∩ A).Nonempty
  · obtain ⟨v, hv⟩ := hh
    obtain ⟨hve, hvA⟩ := Finset.mem_inter.mp hv
    rw [if_pos ⟨v, Finset.mem_inter.mpr ⟨hve, hvA⟩⟩]
    have hsum := Finset.sum_erase_add e (fun u => if u ∈ A then m else 0) hve
    have hpair := Finset.single_le_sum (s := e)
      (f := fun v => ∑ u ∈ e.erase v, if v ∈ A ∧ u ∈ A then m else 0)
      (fun v _hv => hpairs v) hve
    simp only [hvA, true_and, if_true] at hsum hpair
    linarith
  · have hzero : (∑ v ∈ e, if v ∈ A then m else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      have hvA : v ∉ A := fun h => hh ⟨v, Finset.mem_inter.mpr ⟨hv, h⟩⟩
      simp only [if_neg hvA]
    rw [hzero, if_neg hh, zero_add]
    exact Finset.sum_nonneg fun v _hv => hpairs v

theorem sum_vertexMass_le_hitMass_add_pairs (F : FiniteEdgeFamily I Ω α)
    (i : I) (e : Finset α) :
    (∑ v ∈ e, F.vertexMass i v) ≤ F.hitMass i e +
      ∑ v ∈ e, ∑ u ∈ e.erase v, F.pairMass i v u := by
  calc
    _ = ∑ w, ∑ v ∈ e, if v ∈ F.edge i w then F.mass i w else 0 := Finset.sum_comm
    _ ≤ ∑ w, ((if (e ∩ F.edge i w).Nonempty then F.mass i w else 0) +
        ∑ v ∈ e, ∑ u ∈ e.erase v,
          if v ∈ F.edge i w ∧ u ∈ F.edge i w then F.mass i w else 0) :=
      Finset.sum_le_sum fun w _hw =>
        sum_vertex_indicator_le_hit_add_pairs e (F.edge i w) (F.mass_nonneg i w)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      exact Finset.sum_comm

theorem hitMass_bonferroni (F : FiniteEdgeFamily I Ω α) (i : I) (e : Finset α) :
    0 ≤ (∑ v ∈ e, F.vertexMass i v) - F.hitMass i e ∧
      (∑ v ∈ e, F.vertexMass i v) - F.hitMass i e ≤
        ∑ v ∈ e, ∑ u ∈ e.erase v, F.pairMass i v u := by
  constructor
  · exact sub_nonneg.mpr (F.hitMass_le_sum_vertexMass i e)
  · linarith [F.sum_vertexMass_le_hitMass_add_pairs i e]

theorem sum_hitMass_bonferroni (F : FiniteEdgeFamily I Ω α) (e : Finset α) :
    0 ≤ (∑ v ∈ e, F.degree v) - ∑ i, F.hitMass i e ∧
      (∑ v ∈ e, F.degree v) - ∑ i, F.hitMass i e ≤
        ∑ v ∈ e, ∑ u ∈ e.erase v, F.codegree v u := by
  have hid : (∑ v ∈ e, F.degree v) - ∑ i, F.hitMass i e =
      ∑ i, ((∑ v ∈ e, F.vertexMass i v) - F.hitMass i e) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_comm
  rw [hid]
  constructor
  · exact Finset.sum_nonneg fun i _hi => (F.hitMass_bonferroni i e).1
  · calc
      _ ≤ ∑ i, ∑ v ∈ e, ∑ u ∈ e.erase v, F.pairMass i v u :=
        Finset.sum_le_sum fun i _hi => (F.hitMass_bonferroni i e).2
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _hv
        exact Finset.sum_comm

theorem sum_hitMass_error_le (F : FiniteEdgeFamily I Ω α) (e : Finset α)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcodeg : ∀ v ∈ e, ∀ u ∈ e, u ≠ v → F.codegree v u ≤ δ) :
    |(∑ i, F.hitMass i e) - ∑ v ∈ e, F.degree v| ≤ (e.card : ℝ) ^ 2 * δ := by
  have hb := F.sum_hitMass_bonferroni e
  rw [abs_sub_comm, abs_of_nonneg hb.1]
  refine hb.2.trans ?_
  calc
    _ ≤ ∑ _v ∈ e, (e.card : ℝ) * δ := by
      apply Finset.sum_le_sum
      intro v hv
      calc
        _ ≤ ∑ _u ∈ e.erase v, δ := Finset.sum_le_sum fun u hu =>
          hcodeg v hv u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu)
        _ = ((e.erase v).card : ℝ) * δ := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by exact_mod_cast Finset.card_le_card (Finset.erase_subset v e)) hδ
    _ = _ := by simp; ring

end

end Erdos4b.FGKMT.FiniteEdgeFamily

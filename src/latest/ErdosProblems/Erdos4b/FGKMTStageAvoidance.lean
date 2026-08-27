/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTReweightedTransition

/-! # Exact one-stage avoidance under the genuine coupled transition -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def stageRemaining (F : FiniteEdgeFamily I Ω α) (W : Finset α) (ξ : I → Ω) : Finset α :=
  W \ Finset.univ.biUnion (fun i => F.edge i (ξ i))

def reweightedRemaining (F : FiniteEdgeFamily I Ω α)
    (W : Finset α) (ξ : I → Option Ω) : Finset α :=
  W \ Finset.univ.biUnion (fun i => F.optionalEdge i (ξ i))

theorem subset_stageRemaining_iff (F : FiniteEdgeFamily I Ω α)
    (W e : Finset α) (ξ : I → Ω) :
    e ⊆ F.stageRemaining W ξ ↔ e ⊆ W ∧ ∀ i, ¬(e ∩ F.edge i (ξ i)).Nonempty := by
  constructor
  · intro h
    refine ⟨fun v hv => (Finset.mem_sdiff.mp (h hv)).1, ?_⟩
    intro i hh
    obtain ⟨v, hv⟩ := hh
    have hnot := (Finset.mem_sdiff.mp (h (Finset.mem_inter.mp hv).1)).2
    exact hnot (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, (Finset.mem_inter.mp hv).2⟩)
  · rintro ⟨he, hmiss⟩ v hv
    apply Finset.mem_sdiff.mpr
    refine ⟨he hv, ?_⟩
    intro hh
    obtain ⟨i, _hi, hvi⟩ := Finset.mem_biUnion.mp hh
    exact hmiss i ⟨v, Finset.mem_inter.mpr ⟨hv, hvi⟩⟩

theorem edge_miss_mass (F : FiniteEdgeFamily I Ω α) (i : I) (e : Finset α) :
    (∑ w, if ¬(e ∩ F.edge i w).Nonempty then F.mass i w else 0) = 1 - F.hitMass i e := by
  calc
    _ = ∑ w, (F.mass i w - (if (e ∩ F.edge i w).Nonempty then F.mass i w else 0)) := by
      apply Finset.sum_congr rfl
      intro w _hw
      by_cases h : (e ∩ F.edge i w).Nonempty <;> simp [h]
    _ = _ := by rw [Finset.sum_sub_distrib, F.mass_sum_one]; rfl

variable [DecidableEq I]

theorem stage_containment_eq_product (F : FiniteEdgeFamily I Ω α) (W e : Finset α) :
    (∑ ξ : I → Ω, if e ⊆ F.stageRemaining W ξ then F.choiceMass ξ else 0) =
      if e ⊆ W then ∏ i, (1 - F.hitMass i e) else 0 := by
  by_cases he : e ⊆ W
  · simp_rw [F.subset_stageRemaining_iff, he, true_and, if_true]
    rw [F.independent_events (fun i w => ¬(e ∩ F.edge i w).Nonempty)]
    simp only [F.edge_miss_mass]
  · simp only [F.subset_stageRemaining_iff, he, false_and, if_false, Finset.sum_const_zero]

variable {Ξ : Type*} [Fintype Ξ]

theorem transition_containment_eq_product (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (ρ : Ξ → ℝ) (W : Ξ → Finset α) (τ : ℝ)
    (hP : ∀ v ∈ F.vertices, 0 < P v) (hτ : τ < 1) (e : Finset α) :
    (∑ s, ∑ ξ : I → Option Ω,
      if e ⊆ F.reweightedRemaining (W s) ξ then F.transitionMass P W τ ρ s ξ else 0) =
      ∑ s, if e ⊆ W s then ρ s *
        ∏ i, (1 - (F.reweightedFamily P (W s) τ hP hτ).hitMass i e) else 0 := by
  apply Finset.sum_congr rfl
  intro s _hs
  let G := F.reweightedFamily P (W s) τ hP hτ
  have hprod := G.stage_containment_eq_product (W s) e
  calc
    _ = ρ s * ∑ ξ : I → Option Ω,
        if e ⊆ G.stageRemaining (W s) ξ then G.choiceMass ξ else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _hξ
      by_cases h : e ⊆ F.reweightedRemaining (W s) ξ
      · change (if e ⊆ F.reweightedRemaining (W s) ξ then _ else _) =
          ρ s * (if e ⊆ F.reweightedRemaining (W s) ξ then _ else _)
        rw [if_pos h, if_pos h]
        rfl
      · change (if e ⊆ F.reweightedRemaining (W s) ξ then _ else _) =
          ρ s * (if e ⊆ F.reweightedRemaining (W s) ξ then _ else _)
        rw [if_neg h, if_neg h, mul_zero]
    _ = _ := by
      rw [hprod]
      split_ifs
      · rfl
      · exact mul_zero _

end

end Erdos4b.FGKMT.FiniteEdgeFamily

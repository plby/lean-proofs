import ErdosProblems.Erdos547.SkewFractionalExtraction

/-!
# Loads of skew allocations directed out of one side of a cut
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

namespace SkewMatching

theorem IsSuballocation.weight_eq_zero {τ : SkewMatching G δ} {σ : SkewMatching G γ}
    (h : τ.IsSuballocation σ) {u v : V} (hz : σ.weight u v = 0) : τ.weight u v = 0 := by
  apply le_antisymm _ (τ.nonnegative u v)
  apply le_of_not_gt
  intro hp
  have hh := (h u v).1
  rw [hz, zero_div] at hh
  exact not_lt_of_ge hh (div_pos hp τ.denominator_pos)

def RunsFrom (σ : SkewMatching G γ) (U : Finset V) : Prop :=
  ∀ u v, 0 < σ.weight u v → u ∈ U ∧ v ∉ U

theorem RunsFrom.weight_eq_zero {σ : SkewMatching G γ} {U : Finset V}
    (h : σ.RunsFrom U) {u v : V} (hn : ¬ (u ∈ U ∧ v ∉ U)) : σ.weight u v = 0 :=
  le_antisymm (le_of_not_gt (fun hp ↦ hn (h u v hp))) (σ.nonnegative u v)

theorem RunsFrom.of_suballocation {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {U : Finset V} (h : σ.RunsFrom U) (hτ : τ.IsSuballocation σ) : τ.RunsFrom U := by
  intro u v hp
  by_contra hn
  rw [hτ.weight_eq_zero (h.weight_eq_zero hn)] at hp
  exact lt_irrefl 0 hp

theorem RunsFrom.incoming_zero {σ : SkewMatching G γ} {U : Finset V}
    (h : σ.RunsFrom U) {u : V} (hu : u ∈ U) (v : V) : σ.weight v u = 0 :=
  h.weight_eq_zero (fun hh ↦ hh.2 hu)

theorem RunsFrom.outLoad_zero {σ : SkewMatching G γ} {U : Finset V}
    (h : σ.RunsFrom U) {u : V} (hu : u ∉ U) : σ.outLoad u = 0 := by
  have hz (v : V) : σ.weight u v = 0 := h.weight_eq_zero (fun hh ↦ hu hh.1)
  simp only [outLoad, hz, Finset.sum_const_zero, zero_div]

theorem RunsFrom.load_eq_outLoad {σ : SkewMatching G γ} {U : Finset V}
    (h : σ.RunsFrom U) {u : V} (hu : u ∈ U) : σ.load u = σ.outLoad u := by
  simp only [load, inLoad, h.incoming_zero hu, Finset.sum_const_zero, mul_zero, zero_div,
    add_zero]

theorem RunsFrom.sum_load_side {σ : SkewMatching G γ} {U : Finset V}
    (h : σ.RunsFrom U) : (∑ u ∈ U, σ.load u) = σ.total / (1 + γ) := by
  classical
  calc
    _ = ∑ u ∈ U, σ.outLoad u := Finset.sum_congr rfl fun _ hu ↦ h.load_eq_outLoad hu
    _ = ∑ u, σ.outLoad u := Finset.sum_subset (Finset.subset_univ _)
      (fun _ _ hu ↦ h.outLoad_zero hu)
    _ = _ := σ.sum_outLoad

theorem RunsFrom.extractFractional_load {σ : SkewMatching G γ} {U : Finset V}
    (h : σ.RunsFrom U) (hγ : 1 ≤ γ) {u : V} (hu : u ∈ U) :
    (σ.extractFractional hγ).load u = σ.load u := by
  rw [σ.extractFractional_load_eq_outLoad hγ u (h.incoming_zero hu), h.load_eq_outLoad hu]

end SkewMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SkewMatching.RunsFrom.sum_load_side

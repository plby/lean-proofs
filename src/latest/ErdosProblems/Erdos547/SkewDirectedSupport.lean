import ErdosProblems.Erdos547.SkewBipartiteSupport
import ErdosProblems.Erdos547.AllocationRestriction

/-!
# Loads of a skew matching with prescribed source and target sets
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

namespace SkewMatching

def RunsBetween (σ : SkewMatching G γ) (A B : Finset V) : Prop :=
  ∀ u v, 0 < σ.weight u v → u ∈ A ∧ v ∈ B

theorem RunsBetween.weight_eq_zero {σ : SkewMatching G γ} {A B : Finset V}
    (h : σ.RunsBetween A B) {u v : V} (hn : ¬ (u ∈ A ∧ v ∈ B)) :
    σ.weight u v = 0 :=
  le_antisymm (le_of_not_gt (fun hp ↦ hn (h u v hp))) (σ.nonnegative u v)

theorem runsBetween_of_zero {σ : SkewMatching G γ} {A B : Finset V}
    (h : ∀ u v, ¬ (u ∈ A ∧ v ∈ B) → σ.weight u v = 0) :
    σ.RunsBetween A B := by
  intro u v hp
  by_contra hn
  rw [h u v hn] at hp
  exact lt_irrefl 0 hp

theorem RunsBetween.runsFrom {σ : SkewMatching G γ} {A B : Finset V}
    (h : σ.RunsBetween A B) (hd : Disjoint A B) : σ.RunsFrom A := by
  intro u v hp
  exact ⟨(h u v hp).1, fun hv ↦ Finset.disjoint_left.mp hd hv (h u v hp).2⟩

theorem RunsBetween.outLoad_zero {σ : SkewMatching G γ} {A B : Finset V}
    (h : σ.RunsBetween A B) {u : V} (hu : u ∉ A) : σ.outLoad u = 0 := by
  have hz (v : V) : σ.weight u v = 0 := h.weight_eq_zero (fun hh ↦ hu hh.1)
  simp only [outLoad, hz, Finset.sum_const_zero, zero_div]

theorem RunsBetween.inLoad_zero {σ : SkewMatching G γ} {A B : Finset V}
    (h : σ.RunsBetween A B) {u : V} (hu : u ∉ B) : σ.inLoad u = 0 := by
  have hz (v : V) : σ.weight v u = 0 := h.weight_eq_zero (fun hh ↦ hu hh.2)
  simp only [inLoad, hz, Finset.sum_const_zero, mul_zero, zero_div]

theorem RunsBetween.load_zero {σ : SkewMatching G γ} {A B : Finset V}
    (h : σ.RunsBetween A B) {u : V} (huA : u ∉ A) (huB : u ∉ B) : σ.load u = 0 := by
  rw [load, h.outLoad_zero huA, h.inLoad_zero huB, add_zero]

theorem RunsBetween.sum_load_source {σ : SkewMatching G γ} {A B : Finset V}
    (h : σ.RunsBetween A B) (hd : Disjoint A B) :
    (∑ u ∈ A, σ.load u) = σ.total / (1 + γ) := (h.runsFrom hd).sum_load_side

theorem RunsBetween.sum_load_target {σ : SkewMatching G γ} {A B : Finset V}
    (h : σ.RunsBetween A B) (hd : Disjoint A B) :
    (∑ u ∈ B, σ.load u) = γ * σ.total / (1 + γ) := by
  classical
  calc
    _ = ∑ u ∈ B, σ.inLoad u := Finset.sum_congr rfl fun u hu ↦ by
      rw [load, h.outLoad_zero (fun hh ↦ Finset.disjoint_left.mp hd hh hu), zero_add]
    _ = ∑ u, σ.inLoad u := Finset.sum_subset (Finset.subset_univ _)
      (fun u _ hu ↦ h.inLoad_zero hu)
    _ = _ := σ.sum_inLoad

theorem RunsBetween.mono {σ : SkewMatching G γ} {A B C D : Finset V}
    (h : σ.RunsBetween A B) (hAC : A ⊆ C) (hBD : B ⊆ D) : σ.RunsBetween C D :=
  fun u v hp ↦ ⟨hAC (h u v hp).1, hBD (h u v hp).2⟩

open scoped Classical in
theorem RunsBetween.add {σ τ : SkewMatching G γ} {A B C : Finset V}
    (hσ : σ.RunsBetween A B) (hτ : τ.RunsBetween A C)
    (hc : ∀ u, σ.load u + τ.load u ≤ 1) : (σ.add τ hc).RunsBetween A (B ∪ C) := by
  classical
  intro u v hp
  change 0 < σ.weight u v + τ.weight u v at hp
  rcases lt_or_ge 0 (σ.weight u v) with h | h
  · exact ⟨(hσ u v h).1, Finset.mem_union_left _ (hσ u v h).2⟩
  · have ht : 0 < τ.weight u v := by linarith
    exact ⟨(hτ u v ht).1, Finset.mem_union_right _ (hτ u v ht).2⟩

end SkewMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SkewMatching.RunsBetween.sum_load_target

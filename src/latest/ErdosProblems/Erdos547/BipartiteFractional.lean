import ErdosProblems.Erdos547.SeparatedRows

/-!
# Fractional allocations across a fixed bipartition
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace FractionalMatching

def RunsBetween (μ : FractionalMatching G) (U W : Finset V) : Prop :=
  ∀ u v, 0 < μ.weight u v → (u ∈ U ∧ v ∈ W) ∨ (u ∈ W ∧ v ∈ U)

def Crosses (μ : FractionalMatching G) (U : Finset V) : Prop :=
  ∀ u v, 0 < μ.weight u v → (u ∈ U ↔ v ∉ U)

omit [DecidableEq V] in
theorem RunsBetween.crosses {μ : FractionalMatching G} {U W : Finset V}
    (h : μ.RunsBetween U W) (hdis : Disjoint U W) : μ.Crosses U := by
  intro u v huv
  rcases h u v huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hvn : v ∉ U := fun hvU ↦ Finset.disjoint_left.mp hdis hvU hv
    exact ⟨fun _ ↦ hvn, fun _ ↦ hu⟩
  · have hun : u ∉ U := fun huU ↦ Finset.disjoint_left.mp hdis huU hu
    exact ⟨fun huU ↦ (hun huU).elim, fun hvn ↦ (hvn hv).elim⟩

theorem RunsBetween.load_zero_outside {μ : FractionalMatching G} {U W : Finset V}
    (h : μ.RunsBetween U W) {u : V} (hu : u ∉ U ∪ W) : μ.load u = 0 := by
  apply Finset.sum_eq_zero
  intro v _
  apply le_antisymm _ (μ.nonnegative u v)
  apply le_of_not_gt
  intro hp
  rcases h u v hp with ⟨hU, _⟩ | ⟨hW, _⟩
  · exact hu (Finset.mem_union_left _ hU)
  · exact hu (Finset.mem_union_right _ hW)

theorem Crosses.swap {μ : FractionalMatching G} {U : Finset V} (h : μ.Crosses U) :
    μ.Crosses Uᶜ := by
  intro u v hp
  simp only [Finset.mem_compl]
  exact (not_congr (h u v hp))

theorem Crosses.row_sum {μ : FractionalMatching G} {U : Finset V} (h : μ.Crosses U)
    {u : V} (hu : u ∈ U) : μ.load u = ∑ v ∈ Uᶜ, μ.weight u v := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  apply le_antisymm _ (μ.nonnegative u v)
  exact le_of_not_gt fun hp ↦ hv (Finset.mem_compl.mpr ((h u v hp).mp hu))

theorem Crosses.sum_load_eq {μ : FractionalMatching G} {U : Finset V} (h : μ.Crosses U) :
    (∑ u ∈ U, μ.load u) = ∑ u ∈ Uᶜ, μ.load u := by
  calc
    _ = ∑ u ∈ U, ∑ v ∈ Uᶜ, μ.weight u v := Finset.sum_congr rfl (fun _ hu ↦ h.row_sum hu)
    _ = ∑ v ∈ Uᶜ, ∑ u ∈ U, μ.weight u v := Finset.sum_comm
    _ = ∑ v ∈ Uᶜ, μ.load v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [h.swap.row_sum hv, compl_compl]
      exact Finset.sum_congr rfl fun u _ ↦ μ.symmetric u v

omit [DecidableEq V] in
theorem Crosses.sum_load_side {μ : FractionalMatching G} {U : Finset V} (h : μ.Crosses U) :
    (∑ u ∈ U, μ.load u) = μ.total := by
  classical
  have hh := Finset.sum_add_sum_compl U μ.load
  rw [h.sum_load_eq, μ.sum_load] at hh
  linarith [h.sum_load_eq]

def rowWeight (μ : FractionalMatching G) (U : Finset V) (p q : ℝ) (u v : V) : ℝ :=
  (if u ∈ U then p else q) * μ.weight u v

theorem rowWeight_sum (μ : FractionalMatching G) (U : Finset V) (p q : ℝ) (u : V) :
    (∑ v, μ.rowWeight U p q u v) = (if u ∈ U then p else q) * μ.load u := by
  simp only [rowWeight, ← Finset.mul_sum, load]

theorem Crosses.rowWeight_total {μ : FractionalMatching G} {U : Finset V}
    (h : μ.Crosses U) (p q : ℝ) : (∑ u, ∑ v, μ.rowWeight U p q u v) =
      (p + q) * μ.total := by
  simp only [μ.rowWeight_sum]
  calc
    _ = (∑ u ∈ U, p * μ.load u) + ∑ u ∈ Uᶜ, q * μ.load u := by
      rw [← Finset.sum_add_sum_compl U (fun u ↦ (if u ∈ U then p else q) * μ.load u)]
      congr 1
      · exact Finset.sum_congr rfl fun u hu ↦ by rw [if_pos hu]
      · exact Finset.sum_congr rfl fun u hu ↦ by rw [if_neg (Finset.mem_compl.mp hu)]
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum, h.sum_load_side,
      h.swap.sum_load_side]; ring

theorem rowWeight_nonneg (μ : FractionalMatching G) (U : Finset V) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (u v : V) : 0 ≤ μ.rowWeight U p q u v := by
  apply mul_nonneg _ (μ.nonnegative u v)
  split_ifs <;> assumption

theorem Crosses.rowWeight_endpoint {μ : FractionalMatching G} {U : Finset V}
    (h : μ.Crosses U) (p q γ : ℝ) (u v : V) :
    (μ.rowWeight U p q u v + γ * μ.rowWeight U p q v u) / (1 + γ) =
      (if u ∈ U then (p + γ * q) / (1 + γ) else (q + γ * p) / (1 + γ)) * μ.weight u v := by
  rw [rowWeight, rowWeight, μ.symmetric v u]
  by_cases hp : 0 < μ.weight u v
  · by_cases hu : u ∈ U
    · rw [if_pos hu, if_neg ((h u v hp).mp hu), if_pos hu]
      ring
    · have hv : v ∈ U := by
        by_contra hv
        exact hu ((h u v hp).mpr hv)
      rw [if_neg hu, if_pos hv, if_neg hu]
      ring
  · have hz : μ.weight u v = 0 := le_antisymm (le_of_not_gt hp) (μ.nonnegative u v)
    simp only [hz, mul_zero, add_zero, zero_div]

def bipartiteRows (μ : FractionalMatching G) (U : Finset V) (h : μ.Crosses U)
    (γ p q : ℝ) (hγ : 0 ≤ γ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hleft : p + γ * q ≤ 1 + γ) (hright : q + γ * p ≤ 1 + γ) : SkewMatching G γ :=
  SkewMatching.ofDominatedWeight μ γ hγ (μ.rowWeight U p q) (μ.rowWeight_nonneg U hp hq)
    (fun u v ↦ by
      rw [h.rowWeight_endpoint]
      have hden : 0 < 1 + γ := by linarith
      have hc : (if u ∈ U then (p + γ * q) / (1 + γ) else
          (q + γ * p) / (1 + γ)) ≤ 1 := by
        split_ifs
        · exact (div_le_one hden).mpr hleft
        · exact (div_le_one hden).mpr hright
      exact (mul_le_mul_of_nonneg_right hc (μ.nonnegative u v)).trans_eq (one_mul _))

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.Crosses.rowWeight_total

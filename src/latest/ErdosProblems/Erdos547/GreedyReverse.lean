import ErdosProblems.Erdos547.GreedyCapacity

/-!
# Greedy allocation with a capacity condition seen from the head side
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

open scoped Classical in
theorem exists_greedy_reverse (A B : Finset V) (hdis : Disjoint A B) (a b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ b u) (hb : ∀ u, b u ≤ 1)
    (hsupp : ∀ u ∉ A, a u = 0) (κ : ℝ) (hκ : 0 ≤ κ) (γ : ℝ) (hγ : 0 < γ)
    (hB : γ * κ ≤ ∑ u ∈ B, b u)
    (hN : ∀ y ∈ B, κ ≤ ∑ x ∈ A.filter (G.Adj y), a x) :
    ∃ σ : SkewMatching G γ, (∀ u, σ.outLoad u ≤ a u) ∧ (∀ u, σ.load u ≤ b u) ∧
      (∀ u v, ¬ (u ∈ A ∧ v ∈ B) → σ.weight u v = 0) ∧ σ.total = (1 + γ) * κ := by
  classical
  let supply := fun u ↦ if u ∈ B then b u / γ else 0
  have hs0 (u : V) : 0 ≤ supply u := by
    dsimp [supply]
    split_ifs
    · exact div_nonneg ((ha u).trans (hab u)) hγ.le
    · exact le_rfl
  have hsum : κ ≤ ∑ u, supply u := by
    change κ ≤ ∑ u, if u ∈ B then b u / γ else 0
    rw [Finset.sum_ite_mem_eq, ← Finset.sum_div]
    apply (le_div_iff₀ hγ).mpr
    simpa only [mul_comm] using hB
  obtain ⟨r, hr, hrs, hrsum⟩ := exists_capped_reservation supply hs0 κ hκ hsum
  have hrzero (u : V) (hu : u ∉ B) : r u = 0 := by
    apply le_antisymm _ (hr u)
    simpa only [supply, if_neg hu] using hrs u
  have hrbound (u : V) : γ * r u ≤ b u := by
    by_cases hu : u ∈ B
    · have hh : r u ≤ b u / γ := by simpa only [supply, if_pos hu] using hrs u
      have := (le_div_iff₀ hγ).mp hh
      linarith
    · rw [hrzero u hu, mul_zero]
      exact (ha u).trans (hab u)
  let P := fun v u ↦ v ∈ B ∧ u ∈ A ∧ G.Adj v u
  have hneigh (v : V) (hv : 0 < r v) : (∑ u, r u) ≤
      ∑ u ∈ Finset.univ.filter (P v), a u := by
    have hvB : v ∈ B := by
      by_contra hn
      rw [hrzero v hn] at hv
      exact (lt_irrefl 0) hv
    have hset : Finset.univ.filter (P v) = A.filter (G.Adj v) := by
      ext u
      simp [P, hvB]
    rw [hrsum, hset]
    exact hN v hvB
  obtain ⟨f, hrow⟩ := Transport.exists_full_rows P r a hr ha
    (by
      intro v hv
      convert hneigh v hv using 1
      apply Finset.sum_congr
      · ext u
        simp only [Finset.mem_filter]
      · intro u _
        rfl)
  let raw := fun u v ↦ (1 + γ) * f.weight v u
  have hden : 1 + γ ≠ 0 := by linarith
  have hload (u : V) : SkewMatching.vertexLoadOf γ raw u = f.col u + γ * r u := by
    simp only [SkewMatching.vertexLoadOf, raw, ← Finset.mul_sum]
    change (1 + γ) * f.col u / (1 + γ) + γ * ((1 + γ) * f.row u) / (1 + γ) = _
    rw [hrow]
    field_simp [hden]
  have hcapacity (u : V) : SkewMatching.vertexLoadOf γ raw u ≤ b u := by
    rw [hload]
    by_cases hu : u ∈ A
    · have huB : u ∉ B := fun huB ↦ Finset.disjoint_left.mp hdis hu huB
      rw [hrzero u huB, mul_zero, add_zero]
      exact (f.col_bound u).trans (hab u)
    · have hz : f.col u = 0 := le_antisymm
        ((f.col_bound u).trans_eq (hsupp u hu)) (f.col_nonneg u)
      rw [hz, zero_add]
      exact hrbound u
  let σ := SkewMatching.ofVertexLoad hγ.le raw
    (fun u v ↦ mul_nonneg (by linarith) (f.nonnegative v u))
    (fun u v huv ↦ by
      have hn : ¬ P v u := fun hp ↦ huv hp.2.2.symm
      dsimp [raw]
      rw [f.supported v u hn, mul_zero])
    (fun u ↦ (hcapacity u).trans (hb u))
  have hout (u : V) : σ.outLoad u = f.col u := by
    change (∑ v, (1 + γ) * f.weight v u) / (1 + γ) = _
    rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hden]
    rfl
  refine ⟨σ, fun u ↦ (hout u).trans_le (f.col_bound u), hcapacity, ?_, ?_⟩
  · intro u v huv
    have hn : ¬ P v u := fun hp ↦ huv ⟨hp.2.1, hp.1⟩
    change (1 + γ) * f.weight v u = 0
    rw [f.supported v u hn, mul_zero]
  · have hh := σ.sum_outLoad
    simp_rw [hout] at hh
    rw [f.sum_col] at hh
    have ht : f.total = κ := by change (∑ u, f.row u) = κ; simp_rw [hrow]; exact hrsum
    rw [ht] at hh
    have he := (eq_div_iff hden).mp hh
    linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_greedy_reverse

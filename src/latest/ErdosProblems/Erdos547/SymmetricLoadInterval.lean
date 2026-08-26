import ErdosProblems.Erdos547.MandatoryTransport

/-!
# Symmetric fractional weights with prescribed lower and upper loads
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V]

theorem exists_symmetric_load_interval (G : SimpleGraph V) (a b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ b u)
    (hI : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∑ u ∈ I, a u) ≤ ∑ v ∈ graphNeighbours G I, b v) :
    ∃ f : V → V → ℝ, (∀ u v, 0 ≤ f u v) ∧ (∀ u v, f u v = f v u) ∧
      (∀ u v, ¬ G.Adj u v → f u v = 0) ∧
      ∀ u, a u ≤ ∑ v, f u v ∧ (∑ v, f u v) ≤ b u := by
  classical
  obtain ⟨g, hg, hrow, hcol, hsupp, hdiag⟩ :=
    exists_transport_with_diagonal_bound G a b ha hab hI
  let h := fun u v ↦ (g u v + g v u) / 2
  let f := fun u v ↦ if u = v then 0 else h u v
  have hrowh (u : V) : (∑ v, h u v) = b u := by
    simp only [h, ← Finset.sum_div, Finset.sum_add_distrib, hrow, hcol]
    ring
  have hrowf (u : V) : (∑ v, f u v) + g u u = b u := by
    calc
      _ = ∑ v, (f u v + if v = u then g u u else 0) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      _ = ∑ v, h u v := Finset.sum_congr rfl fun v _ ↦ by
        by_cases hv : v = u
        · subst v
          simp only [f, if_pos rfl, if_true, h, zero_add]
          ring
        · simp only [f, if_neg hv, if_neg (Ne.symm hv), add_zero]
      _ = _ := hrowh u
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro u v
    dsimp [f, h]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (add_nonneg (hg u v) (hg v u)) (by norm_num)
  · intro u v
    by_cases huv : u = v
    · subst v
      rfl
    · simp only [f, if_neg huv, if_neg (Ne.symm huv), h, add_comm]
  · intro u v huv
    by_cases he : u = v
    · exact if_pos he
    · have hz₁ := hsupp u v (fun hh ↦ hh.elim huv he)
      have hz₂ := hsupp v u (fun hh ↦ hh.elim (fun hvu ↦ huv hvu.symm) (Ne.symm he))
      simp only [f, if_neg he, h, hz₁, hz₂, add_zero, zero_div]
  · intro u
    constructor
    · linarith [hrowf u, hdiag u]
    · linarith [hrowf u, hg u u]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_symmetric_load_interval

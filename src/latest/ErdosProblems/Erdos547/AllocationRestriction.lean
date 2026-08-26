import ErdosProblems.Erdos547.FractionalReplacement
import ErdosProblems.Erdos547.LoadTransfer

/-!
# Restricting allocations to selected arcs and incident edges
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

namespace SkewMatching

def ofBoundedWeight (σ : SkewMatching G γ) (f : V → V → ℝ)
    (hz : ∀ u v, 0 ≤ f u v) (hf : ∀ u v, f u v ≤ σ.weight u v) : SkewMatching G γ :=
  ofVertexLoad σ.skew_nonneg f hz
    (fun u v huv ↦ le_antisymm (by rw [← σ.supported u v huv]; exact hf u v) (hz u v))
    (fun u ↦ by
      apply le_trans _ (σ.load_le_one u)
      change (∑ v, f u v) / (1 + γ) + γ * (∑ v, f v u) / (1 + γ) ≤ _
      exact add_le_add
        (div_le_div_of_nonneg_right (Finset.sum_le_sum fun v _ ↦ hf u v) σ.denominator_pos.le)
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ ↦ hf v u) σ.skew_nonneg)
          σ.denominator_pos.le))

theorem ofBoundedWeight_isSuballocation (σ : SkewMatching G γ) (f : V → V → ℝ)
    (hz : ∀ u v, 0 ≤ f u v) (hf : ∀ u v, f u v ≤ σ.weight u v) :
    (σ.ofBoundedWeight f hz hf).IsSuballocation σ := by
  intro u v
  exact ⟨div_le_div_of_nonneg_right (hf u v) σ.denominator_pos.le,
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hf u v) σ.skew_nonneg)
      σ.denominator_pos.le⟩

open scoped Classical in
def retain (σ : SkewMatching G γ) (P : V → V → Prop) : SkewMatching G γ :=
  σ.ofBoundedWeight (fun u v ↦ if P u v then σ.weight u v else 0)
    (fun u v ↦ by split_ifs <;> first | exact σ.nonnegative u v | exact le_rfl)
    (fun u v ↦ by split_ifs <;> first | exact le_rfl | exact σ.nonnegative u v)

theorem retain_isSuballocation (σ : SkewMatching G γ) (P : V → V → Prop) :
    (σ.retain P).IsSuballocation σ := σ.ofBoundedWeight_isSuballocation _ _ _

def touching (σ : SkewMatching G γ) (C : Set V) : SkewMatching G γ :=
  σ.retain (fun u v ↦ u ∈ C ∨ v ∈ C)

theorem touching_weight_of_mem (σ : SkewMatching G γ) {C : Set V} {u v : V}
    (h : u ∈ C ∨ v ∈ C) : (σ.touching C).weight u v = σ.weight u v := by
  classical
  exact if_pos h

theorem touching_weight_of_notMem (σ : SkewMatching G γ) {C : Set V} {u v : V}
    (hu : u ∉ C) (hv : v ∉ C) : (σ.touching C).weight u v = 0 := by
  classical
  exact if_neg (not_or.mpr ⟨hu, hv⟩)

theorem load_eq_zero_of_weights (σ : SkewMatching G γ) (u : V)
    (hout : ∀ v, σ.weight u v = 0) (hin : ∀ v, σ.weight v u = 0) : σ.load u = 0 := by
  simp only [load, outLoad, inLoad, hout, hin, Finset.sum_const_zero, mul_zero, zero_div,
    add_zero]

end SkewMatching

namespace FractionalMatching

def touching (μ : FractionalMatching G) (C : Set V) : FractionalMatching G :=
  μ.retain (fun u v ↦ u ∈ C ∨ v ∈ C) (fun _ _ ↦ or_comm)

theorem touching_weight_of_mem (μ : FractionalMatching G) {C : Set V} {u v : V}
    (h : u ∈ C ∨ v ∈ C) : (μ.touching C).weight u v = μ.weight u v := by
  classical
  exact if_pos h

theorem touching_weight_of_notMem (μ : FractionalMatching G) {C : Set V} {u v : V}
    (hu : u ∉ C) (hv : v ∉ C) : (μ.touching C).weight u v = 0 := by
  classical
  exact if_neg (not_or.mpr ⟨hu, hv⟩)

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SkewMatching.retain_isSuballocation

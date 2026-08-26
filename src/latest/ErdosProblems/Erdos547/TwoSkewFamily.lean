import ErdosProblems.Erdos547.AllocationOperations
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Indexing an anchored pair by the two seed colours
-/

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {I : Type*} [Fintype I] {G : SimpleGraph I} {γ : Fin 2 → ℝ}

def twoSkewFamily (σ : SkewMatching G (γ 0)) (τ : SkewMatching G (γ 1)) :
    ∀ c, SkewMatching G (γ c) := Fin.cons σ (Fin.cons τ (fun i ↦ Fin.elim0 i))

@[simp] theorem twoSkewFamily_zero (σ : SkewMatching G (γ 0)) (τ : SkewMatching G (γ 1)) :
    twoSkewFamily σ τ 0 = σ := rfl

@[simp] theorem twoSkewFamily_one (σ : SkewMatching G (γ 0)) (τ : SkewMatching G (γ 1)) :
    twoSkewFamily σ τ 1 = τ := rfl

theorem AnchoredPair.two_family_capacity {σ : SkewMatching G (γ 0)} {τ : SkewMatching G (γ 1)}
    {w : EdgeWeights G} {c d : I} (h : AnchoredPair σ τ w c d) (i : I) :
    (∑ a : Fin 2, (twoSkewFamily σ τ a).load i) ≤ 1 := by
  simpa only [Fin.sum_univ_two, twoSkewFamily_zero, twoSkewFamily_one] using h.capacity i

theorem AnchoredPair.two_family_fits {σ : SkewMatching G (γ 0)} {τ : SkewMatching G (γ 1)}
    {w : EdgeWeights G} {c d : I} (h : AnchoredPair σ τ w c d) (a : Fin 2) (i : I) :
    (twoSkewFamily σ τ a).outLoad i ≤ w.weight (![c, d] a) i := by
  fin_cases a
  · exact h.fits_left i
  · exact h.fits_right i

namespace SkewMatching

theorem sum_outLoad_of_part_total {a b : ℝ} (σ : SkewMatching G (b / a))
    (ha : 0 < a) (r : ℝ) (htotal : σ.total = r * (a + b)) :
    (∑ i, σ.outLoad i) = r * a := by
  rw [σ.sum_outLoad]
  apply (div_eq_iff (ne_of_gt σ.denominator_pos)).mpr
  rw [htotal]
  field_simp

theorem outLoad_le_one {a : ℝ} (σ : SkewMatching G a) (i : I) : σ.outLoad i ≤ 1 :=
  (σ.outLoad_le_load i).trans (σ.load_le_one i)

end SkewMatching
end Erdos547.DPRS

#print axioms Erdos547.DPRS.AnchoredPair.two_family_capacity
#print axioms Erdos547.DPRS.SkewMatching.sum_outLoad_of_part_total

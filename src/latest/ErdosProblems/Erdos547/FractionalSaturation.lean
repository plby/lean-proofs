import ErdosProblems.Erdos547.AllocationOperations

/-!
# Exact fractional subweights and saturation identities
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace FractionalMatching

theorem total_nonneg (μ : FractionalMatching G) : 0 ≤ μ.total :=
  div_nonneg (Finset.sum_nonneg fun u _ ↦ Finset.sum_nonneg fun v _ ↦ μ.nonnegative u v)
    (by norm_num)

def scale (μ : FractionalMatching G) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : FractionalMatching G where
  weight u v := t * μ.weight u v
  symmetric u v := by rw [μ.symmetric u v]
  nonnegative u v := mul_nonneg ht (μ.nonnegative u v)
  supported u v huv := by rw [μ.supported u v huv, mul_zero]
  capacity u := by
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (μ.capacity u) ht).trans (by simpa only [mul_one] using ht1)

@[simp] theorem scale_load (μ : FractionalMatching G) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (u : V) :
    (μ.scale t ht ht1).load u = t * μ.load u := by
  simp only [load, scale, ← Finset.mul_sum]

@[simp] theorem scale_total (μ : FractionalMatching G) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (μ.scale t ht ht1).total = t * μ.total := by
  simp only [total, scale, ← Finset.mul_sum]
  ring

theorem scale_weight_le (μ : FractionalMatching G) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (u v : V) :
    (μ.scale t ht ht1).weight u v ≤ μ.weight u v :=
  (mul_le_mul_of_nonneg_right ht1 (μ.nonnegative u v)).trans_eq (one_mul _)

theorem exists_submatching_total (μ : FractionalMatching G) (r : ℝ) (hr : 0 ≤ r)
    (hrμ : r ≤ μ.total) :
    ∃ ν : FractionalMatching G, (∀ u v, ν.weight u v ≤ μ.weight u v) ∧ ν.total = r := by
  by_cases hz : μ.total = 0
  · have hr0 : r = 0 := by linarith
    exact ⟨μ, fun _ _ ↦ le_rfl, hz.trans hr0.symm⟩
  have hp : 0 < μ.total := lt_of_le_of_ne μ.total_nonneg (Ne.symm hz)
  have ht : 0 ≤ r / μ.total := div_nonneg hr hp.le
  have ht1 : r / μ.total ≤ 1 := (div_le_one hp).mpr hrμ
  refine ⟨μ.scale (r / μ.total) ht ht1, μ.scale_weight_le _ ht ht1, ?_⟩
  rw [scale_total, div_mul_cancel₀ _ hz]

theorem saturation_le_twice_total (μ : FractionalMatching G) (w : EdgeWeights G) (c : V) :
    w.saturation μ.load c ≤ 2 * μ.total :=
  (w.saturation_le_sum_load μ.load c).trans_eq μ.sum_load

theorem saturation_eq_twice_total (μ : FractionalMatching G) (w : EdgeWeights G) (c : V)
    (h : ∀ u, μ.load u ≤ w.weight c u) : w.saturation μ.load c = 2 * μ.total := by
  calc
    _ = ∑ u, μ.load u := Finset.sum_congr rfl fun u _ ↦ min_eq_right (h u)
    _ = _ := μ.sum_load

theorem saturation_add (μ ν : FractionalMatching G) (h : ∀ u, μ.load u + ν.load u ≤ 1)
    (w : EdgeWeights G) (c : V) :
    w.saturation μ.load c + (w.truncate μ.load μ.load_nonneg).saturation ν.load c =
      w.saturation (μ.add ν h).load c := by
  have hh := w.saturation_truncate_add μ.load (μ.add ν h).load μ.load_nonneg
    (fun u ↦ by rw [add_load]; exact le_add_of_nonneg_right (ν.load_nonneg u)) c
  simpa only [add_load, add_sub_cancel_left] using hh

theorem saturation_sub (μ ν : FractionalMatching G)
    (h : ∀ u v, ν.weight u v ≤ μ.weight u v) (w : EdgeWeights G) (c : V) :
    w.saturation ν.load c + (w.truncate ν.load ν.load_nonneg).saturation (μ.sub ν h).load c =
      w.saturation μ.load c := by
  have hh := w.saturation_truncate_add ν.load μ.load ν.load_nonneg
    (ν.load_le_of_weight_le μ h) c
  have he : (μ.sub ν h).load = fun u ↦ μ.load u - ν.load u := funext (μ.sub_load ν h)
  rw [he]
  exact hh

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.exists_submatching_total
#print axioms Erdos547.DPRS.FractionalMatching.saturation_sub

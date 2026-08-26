import ErdosProblems.Erdos547.BoundedFractional

/-!
# Replacing an internal fractional allocation

A convex replacement can repair one vertex load while leaving every other
load unchanged. This is used when moving weight away from a nontrivial
factor-critical block.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace FractionalMatching

def convex (μ ν : FractionalMatching G) (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) :
    FractionalMatching G where
  weight u v := (1 - t) * μ.weight u v + t * ν.weight u v
  symmetric u v := by rw [μ.symmetric u v, ν.symmetric u v]
  nonnegative u v := add_nonneg (mul_nonneg (sub_nonneg.mpr htone) (μ.nonnegative u v))
    (mul_nonneg ht (ν.nonnegative u v))
  supported u v huv := by rw [μ.supported u v huv, ν.supported u v huv]; ring
  capacity u := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hμ := mul_le_mul_of_nonneg_left (μ.capacity u) (sub_nonneg.mpr htone)
    have hν := mul_le_mul_of_nonneg_left (ν.capacity u) ht
    linarith

theorem convex_load (μ ν : FractionalMatching G) (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) (u : V) :
    (μ.convex ν t ht htone).load u = (1 - t) * μ.load u + t * ν.load u := by
  simp only [load, convex, Finset.sum_add_distrib, ← Finset.mul_sum]

open scoped Classical in
def retain (μ : FractionalMatching G) (P : V → V → Prop)
    (hP : ∀ u v, P u v ↔ P v u) : FractionalMatching G :=
  μ.ofBoundedWeight (fun u v ↦ if P u v then μ.weight u v else 0)
    (fun u v ↦ by rw [hP u v, μ.symmetric u v])
    (fun u v ↦ by split_ifs <;> first | exact μ.nonnegative u v | exact le_rfl)
    (fun u v ↦ by split_ifs <;> first | exact le_rfl | exact μ.nonnegative u v)

def inside (μ : FractionalMatching G) (C : Set V) : FractionalMatching G :=
  μ.retain (fun u v ↦ u ∈ C ∧ v ∈ C) (fun _ _ ↦ and_comm)

theorem inside_weight_le (μ : FractionalMatching G) (C : Set V) (u v : V) :
    (μ.inside C).weight u v ≤ μ.weight u v := by
  classical
  dsimp [inside, retain, ofBoundedWeight]
  split_ifs <;> first | exact le_rfl | exact μ.nonnegative u v

theorem inside_weight_of_mem (μ : FractionalMatching G) {C : Set V} {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) : (μ.inside C).weight u v = μ.weight u v := by
  classical
  simp [inside, retain, ofBoundedWeight, hu, hv]

theorem inside_weight_of_notMem (μ : FractionalMatching G) {C : Set V} {u v : V}
    (h : u ∉ C ∨ v ∉ C) : (μ.inside C).weight u v = 0 := by
  classical
  rcases h with hu | hv
  · simp [inside, retain, ofBoundedWeight, hu]
  · simp [inside, retain, ofBoundedWeight, hv]

theorem inside_load_of_notMem (μ : FractionalMatching G) {C : Set V} {u : V} (hu : u ∉ C) :
    (μ.inside C).load u = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ μ.inside_weight_of_notMem (Or.inl hu)

theorem inside_load_add_unique_outside (μ : FractionalMatching G) {C : Set V} {u y : V}
    (hu : u ∈ C) (hy : y ∉ C) (hzero : ∀ v ∉ C, v ≠ y → μ.weight u v = 0) :
    (μ.inside C).load u + μ.weight u y = μ.load u := by
  classical
  have hout : (∑ v, if v ∈ C then (0 : ℝ) else μ.weight u v) = μ.weight u y := by
    rw [Finset.sum_eq_single y]
    · exact if_neg hy
    · intro v _ hvy
      by_cases hv : v ∈ C
      · exact if_pos hv
      · rw [if_neg hv, hzero v hv hvy]
    · intro h
      exact (h (Finset.mem_univ y)).elim
  rw [← hout]
  change (∑ v, (μ.inside C).weight u v) + _ = _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ C
  · rw [μ.inside_weight_of_mem hu hv, if_pos hv, add_zero]
  · rw [μ.inside_weight_of_notMem (Or.inr hv), if_neg hv, zero_add]

open scoped Classical in
theorem exists_single_load_repair [DecidableEq V] (μ I P : FractionalMatching G)
    (hI : ∀ u v, I.weight u v ≤ μ.weight u v) (z : V) (l t : ℝ)
    (ht : 0 ≤ t) (htone : t ≤ 1)
    (hgap : ∀ u, P.load u - I.load u = if u = z then l else 0)
    (hcap : μ.load z + t * l ≤ 1) :
    ∃ ξ : FractionalMatching G,
      (∀ u, ξ.load u = μ.load u + if u = z then t * l else 0) ∧
      (∀ u v, ξ.weight u v = μ.weight u v - I.weight u v +
        ((1 - t) * I.weight u v + t * P.weight u v)) := by
  classical
  let Q := μ.sub I hI
  let J := I.convex P t ht htone
  have hrow (u : V) : Q.load u + J.load u = μ.load u + if u = z then t * l else 0 := by
    change (μ.sub I hI).load u + (I.convex P t ht htone).load u = _
    rw [sub_load, convex_load]
    calc
      _ = μ.load u + t * (P.load u - I.load u) := by ring
      _ = _ := by rw [hgap]; split_ifs <;> ring
  have hsum : ∀ u, Q.load u + J.load u ≤ 1 := by
    intro u
    rw [hrow]
    by_cases huz : u = z
    · simpa only [huz, if_true] using hcap
    · simpa only [if_neg huz, add_zero] using μ.load_le_one u
  refine ⟨Q.add J hsum, ?_, fun _ _ ↦ rfl⟩
  intro u
  rw [add_load, hrow]

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.exists_single_load_repair

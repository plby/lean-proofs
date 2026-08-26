import ErdosProblems.Erdos547.AllocationOperations
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Maximal fractional submatchings with vertex bounds

An optimum exists by finite-dimensional compactness. Its residual support
cannot join two vertices whose specified load bounds are both unsaturated.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

namespace FractionalMatching

def ofBoundedWeight (μ : FractionalMatching G) (f : V → V → ℝ)
    (hsym : ∀ u v, f u v = f v u) (hzero : ∀ u v, 0 ≤ f u v)
    (hbound : ∀ u v, f u v ≤ μ.weight u v) : FractionalMatching G where
  weight := f
  symmetric := hsym
  nonnegative := hzero
  supported u v huv := le_antisymm (by simpa only [μ.supported u v huv] using hbound u v)
    (hzero u v)
  capacity u := (Finset.sum_le_sum fun v _ ↦ hbound u v).trans (μ.capacity u)

def boundedWeights (μ : FractionalMatching G) (a : V → ℝ) : Set (V → V → ℝ) :=
  {f | (∀ u v, 0 ≤ f u v) ∧ (∀ u v, f u v ≤ μ.weight u v) ∧
    (∀ u v, f u v = f v u) ∧ ∀ u, ∑ v, f u v ≤ a u}

theorem isClosed_boundedWeights (μ : FractionalMatching G) (a : V → ℝ) :
    IsClosed (μ.boundedWeights a) := by
  have hz : IsClosed {f : V → V → ℝ | ∀ u v, 0 ≤ f u v} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦
      isClosed_le continuous_const (by fun_prop)
  have hb : IsClosed {f : V → V → ℝ | ∀ u v, f u v ≤ μ.weight u v} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦
      isClosed_le (by fun_prop) continuous_const
  have hs : IsClosed {f : V → V → ℝ | ∀ u v, f u v = f v u} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦
      isClosed_eq (by fun_prop) (by fun_prop)
  have ha : IsClosed {f : V → V → ℝ | ∀ u, ∑ v, f u v ≤ a u} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_le (by fun_prop) continuous_const
  exact hz.inter (hb.inter (hs.inter ha))

theorem isCompact_boundedWeights (μ : FractionalMatching G) (a : V → ℝ) :
    IsCompact (μ.boundedWeights a) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ _ : V ↦ (0 : ℝ)) μ.weight)).of_isClosed_subset
    (μ.isClosed_boundedWeights a)
  exact fun f hf ↦ ⟨hf.1, hf.2.1⟩

theorem exists_maximal_bounded (μ : FractionalMatching G) (a : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) :
    ∃ ν : FractionalMatching G,
      (∀ u v, ν.weight u v ≤ μ.weight u v) ∧ (∀ u, ν.load u ≤ a u) ∧
      ∀ ξ : FractionalMatching G, (∀ u v, ξ.weight u v ≤ μ.weight u v) →
        (∀ u, ξ.load u ≤ a u) → ξ.total ≤ ν.total := by
  have hne : (μ.boundedWeights a).Nonempty := by
    refine ⟨fun _ _ ↦ 0, fun _ _ ↦ le_rfl, μ.nonnegative, fun _ _ ↦ rfl, ?_⟩
    simpa only [Finset.sum_const_zero] using ha
  obtain ⟨f, hf, hmax⟩ := (μ.isCompact_boundedWeights a).exists_isMaxOn hne
    (show Continuous (fun f : V → V → ℝ ↦ (∑ u, ∑ v, f u v) / 2) from by
      fun_prop).continuousOn
  let ν := μ.ofBoundedWeight f hf.2.2.1 hf.1 hf.2.1
  refine ⟨ν, hf.2.1, hf.2.2.2, ?_⟩
  intro ξ hξ hξa
  exact hmax ⟨ξ.nonnegative, hξ, ξ.symmetric, hξa⟩

end FractionalMatching

open scoped Classical in
def edgeIncrement (a b : V) (t : ℝ) (u v : V) : ℝ :=
  if (u = a ∧ v = b) ∨ (u = b ∧ v = a) then t else 0

omit [Fintype V] in
theorem edgeIncrement_symmetric (a b : V) (t : ℝ) (u v : V) :
    edgeIncrement a b t u v = edgeIncrement a b t v u := by
  classical
  simp only [edgeIncrement, and_comm, or_comm]

omit [Fintype V] in
theorem edgeIncrement_nonneg (a b : V) {t : ℝ} (ht : 0 ≤ t) (u v : V) :
    0 ≤ edgeIncrement a b t u v := by
  classical
  simp only [edgeIncrement]
  split_ifs <;> positivity

open scoped Classical in
theorem sum_edgeIncrement {a b : V} (hab : a ≠ b) (t : ℝ) (u : V) :
    (∑ v, edgeIncrement a b t u v) = if u = a ∨ u = b then t else 0 := by
  classical
  by_cases hua : u = a
  · subst u
    simp [edgeIncrement, hab]
  · by_cases hub : u = b
    · subst u
      simp [edgeIncrement, hab.symm]
    · simp [edgeIncrement, hua, hub]

theorem sum_sum_edgeIncrement {a b : V} (hab : a ≠ b) (t : ℝ) :
    (∑ u, ∑ v, edgeIncrement a b t u v) = 2 * t := by
  classical
  simp only [sum_edgeIncrement hab]
  have hsplit (u : V) : (if u = a ∨ u = b then t else 0) =
      (if u = a then t else 0) + (if u = b then t else 0) := by
    by_cases hua : u = a
    · subst u; simp [hab]
    · by_cases hub : u = b <;> simp [hua, hub, hab.symm]
  simp only [hsplit, Finset.sum_add_distrib]
  simp [two_mul]

namespace FractionalMatching

theorem exists_maximal_bounded_with_residual (μ : FractionalMatching G) (a : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) :
    ∃ ν : FractionalMatching G,
      (∀ u v, ν.weight u v ≤ μ.weight u v) ∧ (∀ u, ν.load u ≤ a u) ∧
      ∀ u v, ν.load u < a u → ν.load v < a v → ν.weight u v = μ.weight u v := by
  classical
  obtain ⟨ν, hν, hνa, hmax⟩ := μ.exists_maximal_bounded a ha
  refine ⟨ν, hν, hνa, ?_⟩
  intro u v hu hv
  by_contra hne
  have he : ν.weight u v < μ.weight u v := lt_of_le_of_ne (hν u v) hne
  have huv : G.Adj u v := by
    by_contra h
    rw [μ.supported u v h, ν.supported u v h] at he
    exact (lt_irrefl 0) he
  let t := min (μ.weight u v - ν.weight u v) (min (a u - ν.load u) (a v - ν.load v))
  have ht : 0 < t := lt_min (sub_pos.mpr he) (lt_min (sub_pos.mpr hu) (sub_pos.mpr hv))
  have hte : t ≤ μ.weight u v - ν.weight u v := min_le_left _ _
  have htu : t ≤ a u - ν.load u := (min_le_right _ _).trans (min_le_left _ _)
  have htv : t ≤ a v - ν.load v := (min_le_right _ _).trans (min_le_right _ _)
  let f := fun x y ↦ ν.weight x y + edgeIncrement u v t x y
  have hf : ∀ x y, f x y ≤ μ.weight x y := by
    intro x y
    dsimp [f, edgeIncrement]
    split_ifs with hxy
    · rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx, hy]
        linarith
      · rw [hx, hy, ν.symmetric v u, μ.symmetric v u]
        linarith
    · simpa only [add_zero] using hν x y
  let ξ := μ.ofBoundedWeight f
    (fun x y ↦ by dsimp [f]; rw [ν.symmetric x y, edgeIncrement_symmetric u v t x y])
    (fun x y ↦ add_nonneg (ν.nonnegative x y) (edgeIncrement_nonneg u v ht.le x y)) hf
  have hload (x : V) : ξ.load x = ν.load x + if x = u ∨ x = v then t else 0 := by
    change (∑ y, (ν.weight x y + edgeIncrement u v t x y)) = _
    rw [Finset.sum_add_distrib, sum_edgeIncrement huv.ne]
    rfl
  have hξa : ∀ x, ξ.load x ≤ a x := by
    intro x
    rw [hload]
    split_ifs with hx
    · rcases hx with rfl | rfl <;> linarith
    · simpa only [add_zero] using hνa x
  have htotal : ξ.total = ν.total + t := by
    change (∑ x, ∑ y, (ν.weight x y + edgeIncrement u v t x y)) / 2 = _
    simp only [Finset.sum_add_distrib, sum_sum_edgeIncrement huv.ne, add_div, total]
    ring
  have hcontr := hmax ξ hf hξa
  rw [htotal] at hcontr
  linarith

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.exists_maximal_bounded_with_residual

import ErdosProblems.Erdos547.CappedIndependentRows

/-!
# Saturation loss when a bipartite matching is capped on one side
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace FractionalMatching

omit [DecidableEq V] in
theorem RunsBetween.swap {μ : FractionalMatching G} {U W : Finset V}
    (h : μ.RunsBetween U W) : μ.RunsBetween W U := by
  intro u v huv
  exact (h u v huv).symm

omit [DecidableEq V] in
theorem RunsBetween.mono {μ ν : FractionalMatching G} {U W : Finset V}
    (h : μ.RunsBetween U W) (hν : ∀ u v, ν.weight u v ≤ μ.weight u v) : ν.RunsBetween U W :=
  fun u v hp ↦ h u v (hp.trans_le (hν u v))

omit [DecidableEq V] in
theorem Crosses.mono {μ ν : FractionalMatching G} {U : Finset V}
    (h : μ.Crosses U) (hν : ∀ u v, ν.weight u v ≤ μ.weight u v) : ν.Crosses U :=
  fun u v hp ↦ h u v (hp.trans_le (hν u v))

theorem Crosses.runsBetween {μ : FractionalMatching G} {U : Finset V}
    (h : μ.Crosses U) : μ.RunsBetween U Uᶜ := by
  intro u v hp
  by_cases hu : u ∈ U
  · exact Or.inl ⟨hu, Finset.mem_compl.mpr ((h u v hp).mp hu)⟩
  · refine Or.inr ⟨Finset.mem_compl.mpr hu, ?_⟩
    by_contra hv
    exact hu ((h u v hp).mpr hv)

omit [DecidableEq V] in
theorem saturation_loss_le_other_side (μ ν : FractionalMatching G)
    (hν : ∀ u v, ν.weight u v ≤ μ.weight u v) (U : Finset V) (hU : μ.Crosses U)
    (w : EdgeWeights G) (c : V)
    (hselected : ∀ u ∈ U, min (w.weight c u) (ν.load u) = min (w.weight c u) (μ.load u)) :
    w.saturation μ.load c ≤ w.saturation ν.load c + (μ.sub ν hν).total := by
  classical
  let R := μ.sub ν hν
  have hR : R.Crosses U := hU.mono (fun u v ↦ sub_le_self _ (ν.nonnegative u v))
  have hp (u : V) : min (w.weight c u) (μ.load u) ≤
      min (w.weight c u) (ν.load u) + if u ∈ U then 0 else R.load u := by
    by_cases hu : u ∈ U
    · rw [if_pos hu, add_zero, hselected u hu]
    · rw [if_neg hu]
      have hlo := ν.load_le_of_weight_le μ hν u
      have he := EdgeWeights.min_add_min_truncated (w.weight c u) (ν.load u) (μ.load u) hlo
      have hh := min_le_right (max 0 (w.weight c u - ν.load u)) (μ.load u - ν.load u)
      change _ ≤ min (w.weight c u) (ν.load u) + (μ.sub ν hν).load u
      rw [sub_load]
      linarith
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ (Finset.univ : Finset V)) ↦ hp u
  have hside : (∑ u, if u ∈ U then (0 : ℝ) else R.load u) = R.total := by
    calc
      _ = ∑ u ∈ Uᶜ, R.load u := by
        simpa only [Finset.mem_compl, ite_not] using Finset.sum_ite_mem_eq Uᶜ R.load
      _ = _ := hR.swap.sum_load_side
  simpa only [Finset.sum_add_distrib, hside, EdgeWeights.saturation] using hsum

theorem capIndependent_saturation_loss (μ : FractionalMatching G) (U : Finset V)
    (hU : μ.Crosses U) (w : EdgeWeights G) (c : V) :
    let hzero := fun u (hu : u ∈ U) v (hv : v ∈ U) ↦ hU.weight_zero_same hu hv
    let ν := μ.capIndependent U hzero (w.weight c) (w.nonnegative c)
    w.saturation μ.load c ≤ w.saturation ν.load c +
      (μ.sub ν (μ.capIndependent_weight_le U hzero (w.weight c) (w.nonnegative c))).total := by
  dsimp only
  apply μ.saturation_loss_le_other_side _ _ U hU w c
  intro u hu
  rw [μ.capIndependent_load _ _ _ _ hu, ← min_assoc, min_self]

theorem capIndependent_residual_saturated (μ : FractionalMatching G) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ v ∈ U, μ.weight u v = 0) (a : V → ℝ) (ha : ∀ u, 0 ≤ a u)
    {u v : V} (hu : u ∈ U)
    (hp : 0 < μ.weight u v - (μ.capIndependent U hU a ha).weight u v) :
    (μ.capIndependent U hU a ha).load u = a u := by
  let ν := μ.capIndependent U hU a ha
  let R := μ.sub ν (μ.capIndependent_weight_le U hU a ha)
  have hpos : 0 < R.load u := hp.trans_le
    (Finset.single_le_sum (fun v _ ↦ R.nonnegative u v) (Finset.mem_univ v))
  have hload : R.load u = μ.load u - min (a u) (μ.load u) := by
    rw [show R.load u = μ.load u - ν.load u from μ.sub_load _ _ u,
      μ.capIndependent_load _ _ _ _ hu]
  rw [μ.capIndependent_load _ _ _ _ hu]
  by_cases h : a u ≤ μ.load u
  · exact min_eq_left h
  · rw [hload, min_eq_right (le_of_not_ge h), sub_self] at hpos
    exact (lt_irrefl 0 hpos).elim

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.capIndependent_saturation_loss
#print axioms Erdos547.DPRS.FractionalMatching.capIndependent_residual_saturated

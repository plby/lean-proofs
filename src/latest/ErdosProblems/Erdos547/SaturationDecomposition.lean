import ErdosProblems.Erdos547.CappedIndependentRows

/-!
# Decomposing a fractional matching at one anchor

The first part is accessible from both endpoints. The second runs from
still-unsaturated vertices to saturated vertices and captures all remaining
anchor saturation. Any leftover fractional weight is private to other uses.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

structure SaturationDecomposition (μ : FractionalMatching G) (w : EdgeWeights G) (c : V) where
  full : FractionalMatching G
  cross : FractionalMatching G
  active : Finset V
  full_le : ∀ u v, full.weight u v ≤ μ.weight u v
  combined_le : ∀ u v, full.weight u v + cross.weight u v ≤ μ.weight u v
  full_fits : ∀ u, full.load u ≤ w.weight c u
  active_iff : ∀ u, u ∈ active ↔ full.load u < w.weight c u
  cross_between : cross.RunsBetween active activeᶜ
  cross_load : ∀ u ∈ active,
    cross.load u = min (w.weight c u - full.load u) (μ.load u - full.load u)
  saturation_eq : w.saturation μ.load c = 2 * full.total + cross.total

theorem exists_saturation_decomposition (μ : FractionalMatching G) (w : EdgeWeights G) (c : V) :
    Nonempty (SaturationDecomposition μ w c) := by
  classical
  obtain ⟨ν, hν, hνa, hres⟩ := μ.exists_maximal_bounded_with_residual
    (w.weight c) (w.nonnegative c)
  let R := μ.sub ν hν
  let U := Finset.univ.filter (fun u ↦ ν.load u < w.weight c u)
  let a := fun u ↦ w.weight c u - ν.load u
  have ha (u : V) : 0 ≤ a u := sub_nonneg.mpr (hνa u)
  have hU : ∀ u ∈ U, ∀ v ∈ U, R.weight u v = 0 := by
    intro u hu v hv
    have he := hres u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2
    change μ.weight u v - ν.weight u v = 0
    rw [he, sub_self]
  let J := R.capIndependent U hU a ha
  have hJ (u v : V) : J.weight u v ≤ R.weight u v := R.capIndependent_weight_le U hU a ha u v
  have hbound (u v : V) : ν.weight u v + J.weight u v ≤ μ.weight u v := by
    have hh := hJ u v
    change J.weight u v ≤ μ.weight u v - ν.weight u v at hh
    linarith
  have htotal : J.total = ∑ u ∈ U, min (a u) (R.load u) := R.capIndependent_total U hU a ha
  have hidentity : (∑ u, ν.load u) + (∑ u, min (a u) (R.load u)) =
      w.saturation μ.load c := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    change ν.load u + min (w.weight c u - ν.load u) ((μ.sub ν hν).load u) = _
    rw [FractionalMatching.sub_load, min_sub_sub_right]
    ring
  have hselected : (∑ u, min (a u) (R.load u)) = ∑ u ∈ U, min (a u) (R.load u) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu
    have hnu : ¬ ν.load u < w.weight c u := fun hh ↦
      hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    have he : a u = 0 := by dsimp [a]; linarith [hνa u]
    rw [he, min_eq_left (R.load_nonneg u)]
  refine ⟨⟨ν, J, U, hν, hbound, hνa, ?_, R.capIndependent_runsBetween U hU a ha, ?_, ?_⟩⟩
  · intro u
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ u))
  · intro u hu
    rw [show J.load u = min (a u) (R.load u) from R.capIndependent_load U hU a ha hu]
    exact congrArg (min (a u)) (μ.sub_load ν hν u)
  · rw [ν.sum_load, hselected, ← htotal] at hidentity
    exact hidentity.symm

namespace SaturationDecomposition

variable {μ : FractionalMatching G} {w : EdgeWeights G} {c : V}

theorem combined_load_le (D : SaturationDecomposition μ w c) (u : V) :
    D.full.load u + D.cross.load u ≤ μ.load u := by
  rw [FractionalMatching.load, FractionalMatching.load, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun v _ ↦ D.combined_le u v

theorem outside_full_load (D : SaturationDecomposition μ w c) {u : V} (hu : u ∉ D.active) :
    D.full.load u = w.weight c u := by
  apply le_antisymm (D.full_fits u)
  exact le_of_not_gt fun hh ↦ hu ((D.active_iff u).mpr hh)

theorem active_cross_fits (D : SaturationDecomposition μ w c) {u : V} (hu : u ∈ D.active) :
    D.cross.load u ≤ w.weight c u - D.full.load u := by
  rw [D.cross_load u hu]
  exact min_le_left _ _

theorem active_combined_load (D : SaturationDecomposition μ w c) {u : V} (hu : u ∈ D.active) :
    D.full.load u + D.cross.load u = min (w.weight c u) (μ.load u) := by
  rw [D.cross_load u hu, min_sub_sub_right]
  ring

theorem captures_saturation (D : SaturationDecomposition μ w c) (u : V) :
    min (w.weight c u) (D.full.load u + D.cross.load u) = min (w.weight c u) (μ.load u) := by
  by_cases hu : u ∈ D.active
  · rw [D.active_combined_load hu, ← min_assoc, min_self]
  · have hfull := D.outside_full_load hu
    have hμ : w.weight c u ≤ μ.load u := by
      have hh := (D.full.load_le_of_weight_le μ D.full_le u)
      rwa [hfull] at hh
    rw [min_eq_left hμ, min_eq_left ?_]
    linarith [D.cross.load_nonneg u]

end SaturationDecomposition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_saturation_decomposition
#print axioms Erdos547.DPRS.SaturationDecomposition.captures_saturation

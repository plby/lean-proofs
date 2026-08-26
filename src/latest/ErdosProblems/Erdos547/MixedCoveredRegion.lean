import ErdosProblems.Erdos547.SkewDirectedSupport
import ErdosProblems.Erdos547.BipartiteFractional

/-!
# A mixed allocation covering one side has a sufficiently large opposite support
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

theorem mixed_covered_region_card_bound (σ : SkewMatching G γ) (ν : FractionalMatching G)
    (C R : Finset V) (hdis : Disjoint C R) (hσ : σ.RunsBetween C R)
    (hν : ν.RunsBetween C R) (hγ : 1 ≤ γ)
    (hcap : ∀ u, σ.load u + ν.load u ≤ 1)
    (hcover : ∀ u ∈ C, σ.load u + ν.load u = 1) :
    (C.card : ℝ) ≤ ((R.filter (fun u ↦ 0 < σ.load u + ν.load u)).card : ℝ) := by
  classical
  have htotal : 0 ≤ σ.total := Finset.sum_nonneg fun u _ ↦
    Finset.sum_nonneg fun v _ ↦ σ.nonnegative u v
  have hswap : ν.RunsBetween R C := by
    intro u v hp
    exact (hν u v hp).symm
  have hs : (∑ u ∈ C, σ.load u) ≤ ∑ u ∈ R, σ.load u := by
    rw [hσ.sum_load_source hdis, hσ.sum_load_target hdis]
    exact div_le_div_of_nonneg_right
      (by nlinarith : σ.total ≤ γ * σ.total) σ.denominator_pos.le
  have hn : (∑ u ∈ C, ν.load u) = ∑ u ∈ R, ν.load u := by
    rw [(hν.crosses hdis).sum_load_side, (hswap.crosses hdis.symm).sum_load_side]
  have hcov : (∑ u ∈ C, (σ.load u + ν.load u)) = (C.card : ℝ) := by
    calc
      _ = ∑ _u ∈ C, (1 : ℝ) := Finset.sum_congr rfl fun u hu ↦ hcover u hu
      _ = _ := by simp
  let Q := R.filter (fun u ↦ 0 < σ.load u + ν.load u)
  have he : (∑ u ∈ Q, (σ.load u + ν.load u)) = ∑ u ∈ R, (σ.load u + ν.load u) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro u hu hnQ
    apply le_antisymm _ (add_nonneg (σ.load_nonneg u) (ν.load_nonneg u))
    exact le_of_not_gt fun hp ↦ hnQ (Finset.mem_filter.mpr ⟨hu, hp⟩)
  calc
    _ = ∑ u ∈ C, (σ.load u + ν.load u) := hcov.symm
    _ ≤ ∑ u ∈ R, (σ.load u + ν.load u) := by
      simp only [Finset.sum_add_distrib]
      exact add_le_add hs hn.le
    _ = ∑ u ∈ Q, (σ.load u + ν.load u) := he.symm
    _ ≤ ∑ _u ∈ Q, (1 : ℝ) := Finset.sum_le_sum fun u _ ↦ hcap u
    _ = _ := by simp [Q]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.mixed_covered_region_card_bound

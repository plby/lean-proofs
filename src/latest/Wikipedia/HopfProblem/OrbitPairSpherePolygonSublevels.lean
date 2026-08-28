import Wikipedia.HopfProblem.OrbitPairSpherePolygonEnergy

/-!
# Compact energy sublevels avoid antipodal edges on a fine partition

For each edge, squared length is at most the total polygon energy times
that edge's time increment. Thus the explicit mesh condition
`c * (tau[i+1] - tau[i]) < pi^2` puts the entire closed energy sublevel
inside the canonical smooth nonantipodal domain. In particular, the open
domain does not cause a compactness gap on these controlled sublevels.
-/

noncomputable section

open scoped ContDiff Manifold
open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace SpherePairedGeodesic

variable {n m : ℕ}

theorem edgeCost_le_energy_mul (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m) (i : Fin (m + 1)) :
    sphereCost n (edge a b v i) ≤ energy a b τ v * (τ i.succ - τ i.castSucc) := by
  have hpos : 0 < τ i.succ - τ i.castSucc :=
    sub_pos.mpr (hτ (show i.castSucc < i.succ by simp))
  apply (div_le_iff₀ hpos).mp
  exact Finset.single_le_sum
    (fun j _ => div_nonneg (sphereCost_nonneg _)
      (sub_nonneg.mpr (hτ (show j.castSucc < j.succ by simp)).le))
    (Finset.mem_univ i)

theorem sublevel_subset_admissible (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (c : ℝ)
    (hmesh : ∀ i : Fin (m + 1), c * (τ i.succ - τ i.castSucc) < Real.pi ^ 2) :
    {v : Space n m | energy a b τ v ≤ c} ⊆ admissible (costDomain n) a b m := by
  intro v hv i
  apply mem_nonantipodal_of_cost_lt_pi_sq
  have hlen : 0 ≤ τ i.succ - τ i.castSucc :=
    sub_nonneg.mpr (hτ (show i.castSucc < i.succ by simp)).le
  exact ((edgeCost_le_energy_mul a b τ hτ v i).trans
    (mul_le_mul_of_nonneg_right hv hlen)).trans_lt (hmesh i)

theorem admissible_inter_sublevel (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (c : ℝ)
    (hmesh : ∀ i : Fin (m + 1), c * (τ i.succ - τ i.castSucc) < Real.pi ^ 2) :
    admissible (costDomain n) a b m ∩ {v : Space n m | energy a b τ v ≤ c} =
      {v : Space n m | energy a b τ v ≤ c} :=
  inter_eq_right.mpr (sublevel_subset_admissible a b τ hτ c hmesh)

theorem isCompact_admissible_sublevel (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (c : ℝ)
    (hmesh : ∀ i : Fin (m + 1), c * (τ i.succ - τ i.castSucc) < Real.pi ^ 2) :
    IsCompact (admissible (costDomain n) a b m ∩
      {v : Space n m | energy a b τ v ≤ c}) := by
  rw [admissible_inter_sublevel a b τ hτ c hmesh]
  exact isCompact_sublevel a b τ c

theorem contMDiffAt_energy_of_le (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (c : ℝ)
    (hmesh : ∀ i : Fin (m + 1), c * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (v : Space n m) (hv : energy a b τ v ≤ c) :
    ContMDiffAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) ∞ (energy a b τ) v :=
  (contMDiffOn_energy (costDomain n) a b τ).contMDiffAt
    ((isOpen_admissible (costDomain n) a b m).mem_nhds
      (sublevel_subset_admissible a b τ hτ c hmesh hv))

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

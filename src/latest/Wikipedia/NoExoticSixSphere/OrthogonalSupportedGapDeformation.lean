import Wikipedia.NoExoticSixSphere.OrthogonalSupportedBandDeformation
import Wikipedia.NoExoticSixSphere.OrthogonalCriticalEnergySpectrum

/-!
# Supported descent inside an antipodal critical-energy gap

The containing lattice for critical energies proves noncriticality of the
active band. A sufficiently fine common partition proves compactness. Thus
the global, band-supported deformation exists with neither of those facts
left as an unproved premise.
-/

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

theorem exists_supported_gap_deformation_partition (n q N : ℕ) (l k u v E : ℝ)
    (hlk : l < k) (huv : u < v) (hvE : v < E)
    (hlow : ((n : ℝ) + 8 * (q : ℝ)) * Real.pi ^ 2 < l)
    (hhigh : E < ((n : ℝ) + 8 * ((q : ℝ) + 1)) * Real.pi ^ 2) :
    ∃ m : ℕ, N ≤ m ∧ ∀ a b : OrthogonalOperators n,
      (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n) →
        ∃ F : C(admissible a b m, admissible a b m),
          ∃ H : ContinuousMap.HomotopyRel (ContinuousMap.id _) F
            {z : admissible a b m |
              energy a b (UniformTimePartition.time m) z.1 ≤ l ∨
              v ≤ energy a b (UniformTimePartition.time m) z.1},
            (∀ t z, energy a b (UniformTimePartition.time m) (H (t, z)).1 ≤
              energy a b (UniformTimePartition.time m) z.1) ∧
            ∀ z, energy a b (UniformTimePartition.time m) z.1 ≤ u →
              energy a b (UniformTimePartition.time m) (F z).1 ≤ k := by
  obtain ⟨m, hNm, hm⟩ := exists_compact_sublevels_partition n E N
  refine ⟨m, hNm, fun a b hanti ↦ ?_⟩
  apply exists_supported_band_deformation a b (UniformTimePartition.time m)
    l k u v E hlk huv hvE (hm a b E le_rfl).1
  intro z hz
  exact noncritical_of_energy_mem_gap a b (UniformTimePartition.time m)
    (UniformTimePartition.strictMono_time m) (UniformTimePartition.time_zero m)
    (UniformTimePartition.time_last m) hanti z hz.1.1 q
    (hlow.trans_le hz.2) (hz.1.2.trans_lt hhigh)

end NoExoticSixSphere.OrthogonalPolygon

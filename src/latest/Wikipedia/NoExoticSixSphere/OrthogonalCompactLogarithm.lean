import Wikipedia.NoExoticSixSphere.OrthogonalLogarithm
import Wikipedia.NoExoticSixSphere.OrthogonalCompactness

/-!
# Compact logarithmic neighborhoods

A closed ball sufficiently near zero lies in the actual logarithm target.
Its exponential image is a compact subset of the logarithm source, and
membership is equivalent to the corresponding logarithm norm bound.
-/

open Set Metric

namespace NoExoticSixSphere.OrthogonalExponential

open GLOrthonormalization CayleyTransform

variable {n : ℕ}

theorem exp_mem_logarithmChart_source (K : SkewOperators n)
    (hK : K ∈ (logarithmChart n).target) : exp K ∈ (logarithmChart n).source := by
  have hs := (logarithmChart n).map_target' hK
  have he : exp K = (logarithmChart n).symm K := by
    calc
      exp K = exp (logarithmChart n ((logarithmChart n).symm K)) := by
        exact congrArg exp ((logarithmChart n).right_inv' hK).symm
      _ = (logarithmChart n).symm K := exp_logarithmChart _ hs
  rwa [he]

theorem exists_compactLogarithm_radius (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ r < Real.pi ∧
      closedBall (0 : SkewOperators n) r ⊆ (logarithmChart n).target := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((logarithmChart n).open_target.mem_nhds (zero_mem_logarithmChart_target n))
  let r := min (ε / 2) (Real.pi / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrπ : r < Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  exact ⟨r, hr, hrπ, fun _ hK ↦ hball (lt_of_le_of_lt hK hrε)⟩

def compactIncrements (n : ℕ) (r : ℝ) : Set (OrthogonalOperators n) :=
  exp '' closedBall (0 : SkewOperators n) r

theorem isCompact_compactIncrements (n : ℕ) (r : ℝ) : IsCompact (compactIncrements n r) :=
  (isCompact_closedBall (0 : SkewOperators n) r).image contMDiff_exp.continuous

theorem mem_compactIncrements_iff {r : ℝ}
    (hr : closedBall (0 : SkewOperators n) r ⊆ (logarithmChart n).target)
    (a : OrthogonalOperators n) :
    a ∈ compactIncrements n r ↔ a ∈ (logarithmChart n).source ∧ ‖logarithmChart n a‖ ≤ r := by
  constructor
  · rintro ⟨K, hK, rfl⟩
    refine ⟨exp_mem_logarithmChart_source K (hr hK), ?_⟩
    rw [logarithmChart_exp K (hr hK)]
    simpa only [mem_closedBall, dist_zero_right] using hK
  · intro ha
    refine ⟨logarithmChart n a, ?_, exp_logarithmChart a ha.1⟩
    simpa only [mem_closedBall, dist_zero_right] using ha.2

end NoExoticSixSphere.OrthogonalExponential

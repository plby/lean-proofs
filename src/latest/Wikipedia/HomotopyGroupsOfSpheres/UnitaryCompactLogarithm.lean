import Wikipedia.HomotopyGroupsOfSpheres.UnitaryCompatibleLogarithm

/-! # Compact complex unitary increments strictly inside the common logarithm domain -/

noncomputable section

open scoped Matrix.Norms.Frobenius
open Set Metric

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexSkewMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem logarithm_exponential (K : Space N)
    (hK : K.val ∈ (ComplexMatrixLocalLogarithm.exponentialChart N).source) :
    logarithm (exponential K) = K := by
  change projection (ComplexMatrixLocalLogarithm.logarithm (NormedSpace.exp K.val)) = K
  rw [ComplexMatrixLocalLogarithm.logarithm_exp K.val hK]
  exact projection_coe K

namespace CompatibleLog

theorem exponential_mem_domain (K : Space N) (hK : ‖K‖ < radius N) :
    exponential K ∈ domain N := by
  have hsmall : ‖K.val‖ < ComplexMatrixLocalLogarithm.radius N := hK.trans radius_lt
  refine ⟨ComplexMatrixLocalLogarithm.exp_mem_domain K.val hsmall, ?_⟩
  rw [logarithm_exponential K (ComplexMatrixLocalLogarithm.mem_safeSource_of_norm_lt _ hsmall).1]
  exact hK

def compactIncrements (N : Type*) [Fintype N] [DecidableEq N] (r : ℝ) :
    Set (unitary (Matrix N N ℂ)) := exponential '' closedBall (0 : Space N) r

theorem isCompact_compactIncrements (r : ℝ) : IsCompact (compactIncrements N r) :=
  (isCompact_closedBall (0 : Space N) r).image continuous_exponential

theorem mem_compactIncrements_iff {r : ℝ} (hr : r < radius N)
    (U : unitary (Matrix N N ℂ)) :
    U ∈ compactIncrements N r ↔ U ∈ domain N ∧ ‖logarithm U‖ ≤ r := by
  constructor
  · rintro ⟨K, hK, rfl⟩
    have hn : ‖K‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hK
    have hs := exponential_mem_domain K (hn.trans_lt hr)
    refine ⟨hs, ?_⟩
    have ht : K.val ∈ (ComplexMatrixLocalLogarithm.exponentialChart N).source :=
      (ComplexMatrixLocalLogarithm.mem_safeSource_of_norm_lt K.val
        ((hn.trans_lt hr).trans radius_lt)).1
    rwa [logarithm_exponential K ht]
  · intro hU
    refine ⟨logarithm U, ?_, exponential_logarithm U hU.1.1⟩
    simpa only [mem_closedBall, dist_zero_right] using hU.2

end CompatibleLog

end Wikipedia.HomotopyGroupsOfSpheres.ComplexSkewMatrices

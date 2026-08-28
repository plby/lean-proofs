import Wikipedia.HopfProblem.CuspNormalizationGermsChartMap

/-!
# Literal representatives of the cusp normalization on active branches

The actual inverse quotient chart, composed with the centered actual
normalization branch map, agrees locally with the original component
projection. Consequently this equality remains true after composition
with any function on the quotient, without an analytic assumption.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricFan ToricSpace ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle) (b : E₃)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- On the actual chart domain, undoing the centered branch coordinate
map gives exactly the original component projection. -/
theorem centeredChartInverse_branch_eq_of_mem_target (j : Fin 3) (hj : b j = 0)
    (y : E₂) (hy : b + insertZero j y ∈ (e).target) :
    (e).symm (b + Germs.centeredBranchMap C ε hε hε1 hC hR a s b j y) =
      componentProjection C ε hε (branchAffine C s j (removeCoordinate j b + y)) := by
  have hcoord : insertZero j (removeCoordinate j b + y) = b + insertZero j y := by
    rw [Germs.insertZero_add, insertZero_removeCoordinate j b hj]
  have hz : removeCoordinate j b + y ∈
      normalizationBranchDomain C ε hε hε1 hC hR a s j := by
    change insertZero j (removeCoordinate j b + y) ∈ (e).target
    rwa [hcoord]
  have hsource : componentProjection C ε hε
      (branchAffine C s j (removeCoordinate j b + y)) ∈ (e).source :=
    normalizationBranch_mem_preimage C ε hε hε1 hC hR a s j _ hz
  simpa only [Germs.centeredBranchMap, ← add_sub_assoc, add_sub_cancel_left] using
    (e).left_inv hsource

/-- Near zero on each active branch, the inverse quotient chart is the
actual component projection in the translated affine branch chart. -/
theorem centeredChartInverse_branch_eventuallyEq (hb : b ∈ (e).target) (j : Fin 3)
    (hj : j ∈ Germs.activeBranches b) :
    (fun y : E₂ => (e).symm
        (b + Germs.centeredBranchMap C ε hε hε1 hC hR a s b j y))
      =ᶠ[𝓝 (0 : E₂)]
        (fun y => componentProjection C ε hε
          (branchAffine C s j (removeCoordinate j b + y))) := by
  have htarget : (fun y : E₂ => b + insertZero j y) ⁻¹' (e).target ∈ 𝓝 (0 : E₂) :=
    ((e).open_target.preimage
      (continuous_const.add (insertZero_holomorphic j).continuous)).mem_nhds
        (by simpa only [mem_preimage, Pi.add_apply, Germs.insertZero_zero, add_zero] using hb)
  filter_upwards [htarget] with y hy
  exact centeredChartInverse_branch_eq_of_mem_target C ε hε hε1 hC hR a s b j
    ((Germs.mem_activeBranches b j).mp hj) y hy

/-- Composition of any actual quotient function with the centered
branch coordinate expression is its literal normalization pullback. -/
theorem centeredAmbient_comp_branch_eventuallyEq (hb : b ∈ (e).target) (j : Fin 3)
    (hj : j ∈ Germs.activeBranches b) (F : QuotientSpace C ε → ℂ) :
    (fun y : E₂ => F ((e).symm
        (b + Germs.centeredBranchMap C ε hε hε1 hC hR a s b j y)))
      =ᶠ[𝓝 (0 : E₂)]
        (fun y => F (componentProjection C ε hε
          (branchAffine C s j (removeCoordinate j b + y)))) := by
  filter_upwards [centeredChartInverse_branch_eventuallyEq C ε hε hε1 hC hR a s b
    hb j hj] with y hy
  exact congrArg F hy

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution

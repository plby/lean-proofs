import Wikipedia.HopfProblem.CuspNormalizationLocal
import Wikipedia.HopfProblem.CuspNormalizationGermsRestriction

/-!
# The actual normalization pullback on centered branch germs

At a point of an adapted quotient chart, each active coordinate plane
comes from the actual affine branch of the component map. Centering that
branch at the point obtained by removing its zero coordinate makes the
actual component map equal to the coordinate-plane inclusion on a
neighbourhood of zero. Analytic pullback along this actual expression is
therefore the previously constructed branch restriction of analytic germs.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open CuspQuotient ToricCharts ToricFan ToricSpace ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle) (b : E₃)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- The actual component projection in the centered source and target
charts; no substitute for the normalization map is introduced. -/
def centeredBranchMap (j : Fin 3) (y : E₂) : E₃ :=
  e (componentProjection C ε hε (branchAffine C s j (removeCoordinate j b + y))) - b

/-- The centered coordinate identity wherever the actual quotient chart
is defined on the corresponding coordinate-plane point. -/
theorem centeredBranchMap_eq_of_mem_target (j : Fin 3) (hj : b j = 0)
    (y : E₂) (hy : b + insertZero j y ∈ (e).target) :
    centeredBranchMap C ε hε hε1 hC hR a s b j y = insertZero j y := by
  have he : insertZero j (removeCoordinate j b + y) = b + insertZero j y := by
    rw [insertZero_add, insertZero_removeCoordinate j b hj]
  have hz : removeCoordinate j b + y ∈
      normalizationBranchDomain C ε hε hε1 hC hR a s j := by
    change insertZero j (removeCoordinate j b + y) ∈ (e).target
    rwa [he]
  rw [centeredBranchMap,
    normalizationBranch_coordinates C ε hε hε1 hC hR a s j _ hz, he]
  exact add_sub_cancel_left b (insertZero j y)

/-- Every active branch has the actual coordinate-plane expression on a
genuine neighbourhood of the centered source point. -/
theorem centeredBranchMap_eventuallyEq (hb : b ∈ (e).target) (j : Fin 3)
    (hj : j ∈ activeBranches b) :
    centeredBranchMap C ε hε hε1 hC hR a s b j =ᶠ[𝓝 (0 : E₂)] insertZero j := by
  have htarget : (fun y : E₂ => b + insertZero j y) ⁻¹' (e).target ∈ 𝓝 (0 : E₂) :=
    ((e).open_target.preimage
      (continuous_const.add (insertZero_holomorphic j).continuous)).mem_nhds
        (by simpa only [mem_preimage, Pi.add_apply, insertZero_zero, add_zero] using hb)
  filter_upwards [htarget] with y hy
  exact centeredBranchMap_eq_of_mem_target C ε hε hε1 hC hR a s b j
    ((mem_activeBranches b j).mp hj) y hy

theorem centeredBranchMap_zero (hb : b ∈ (e).target) (j : Fin 3)
    (hj : j ∈ activeBranches b) :
    centeredBranchMap C ε hε hε1 hC hR a s b j 0 = 0 := by
  simpa only [insertZero_zero] using
    centeredBranchMap_eq_of_mem_target C ε hε hε1 hC hR a s b j
      ((mem_activeBranches b j).mp hj) 0
      (by simpa only [insertZero_zero, add_zero] using hb)

/-- Analyticity follows from the proved equality of the actual expression
with the analytic plane inclusion on a neighbourhood. -/
theorem centeredBranchMap_analyticAt (hb : b ∈ (e).target) (j : Fin 3)
    (hj : j ∈ activeBranches b) :
    AnalyticAt ℂ (centeredBranchMap C ε hε hε1 hC hR a s b j) 0 :=
  (insertZero_holomorphic j).contDiffAt.analyticAt.congr
    (centeredBranchMap_eventuallyEq C ε hε hε1 hC hR a s b hb j hj).symm

/-- Actual analytic-germ pullback along the centered expression of `ν`
in the selected branch chart. -/
def normalizationBranchPullback (hb : b ∈ (e).target) (j : Fin 3)
    (hj : j ∈ activeBranches b) : AmbientGerm →+* BranchGerm :=
  pullbackAt (centeredBranchMap C ε hε hε1 hC hR a s b j)
    (centeredBranchMap_analyticAt C ε hε hε1 hC hR a s b hb j hj)
    (centeredBranchMap_zero C ε hε hε1 hC hR a s b hb j hj)

/-- The actual normalization pullback is the coordinate restriction map
on analytic germs, proved from equality of representatives near zero. -/
theorem normalizationBranchPullback_eq_toBranch (hb : b ∈ (e).target) (j : Fin 3)
    (hj : j ∈ activeBranches b) :
    normalizationBranchPullback C ε hε hε1 hC hR a s b hb j hj = toBranch j :=
  pullbackAt_congr
    (centeredBranchMap_analyticAt C ε hε hε1 hC hR a s b hb j hj)
    (insertZero_holomorphic j).contDiffAt.analyticAt
    (centeredBranchMap_zero C ε hε hε1 hC hR a s b hb j hj) (insertZero_zero j)
    (centeredBranchMap_eventuallyEq C ε hε hε1 hC hR a s b hb j hj)

/-- On representatives this is the actual composition with the component
projection and both centered charts. -/
theorem normalizationBranchPullback_ofAnalytic (hb : b ∈ (e).target) (j : Fin 3)
    (hj : j ∈ activeBranches b) (f : E₃ → ℂ) (hf : AnalyticAt ℂ f 0) :
    normalizationBranchPullback C ε hε hε1 hC hR a s b hb j hj (ofAnalytic f hf) =
      ofAnalytic (f ∘ centeredBranchMap C ε hε hε1 hC hR a s b j)
        (hf.comp_of_eq
          (centeredBranchMap_analyticAt C ε hε hε1 hC hR a s b hb j hj)
          (centeredBranchMap_zero C ε hε hε1 hC hR a s b hb j hj)) :=
  pullbackAt_ofAnalytic ..

/-- Simultaneous actual pullback to every active branch over the point. -/
def normalizationBranchesPullback (hb : b ∈ (e).target) :
    AmbientGerm →+* (activeBranches b → BranchGerm) :=
  RingHom.pi fun j => normalizationBranchPullback C ε hε hε1 hC hR a s b hb j j.property

theorem normalizationBranchesPullback_eq_toBranches (hb : b ∈ (e).target) :
    normalizationBranchesPullback C ε hε hε1 hC hR a s b hb = toBranches (activeBranches b) := by
  apply RingHom.ext
  intro φ
  funext j
  change normalizationBranchPullback C ε hε hε1 hC hR a s b hb j j.property φ = toBranch j φ
  rw [normalizationBranchPullback_eq_toBranch]

/-- The kernel of actual pullback along `ν` is the actual ideal of
ambient-analytic germs vanishing on the active plane union. -/
theorem kernel_normalizationBranchesPullback (hb : b ∈ (e).target) :
    RingHom.ker (normalizationBranchesPullback C ε hε hε1 hC hR a s b hb) =
      RingHom.ker (toPlaneUnion (activeBranches b)) := by
  rw [normalizationBranchesPullback_eq_toBranches, kernel_toPlaneUnion]

end Wikipedia.HopfProblem.CuspNormalization.Germs

import Wikipedia.HopfProblem.CuspNormalizationLocal
import Wikipedia.HopfProblem.CuspNormalizationGermsPlanes

/-!
# Active coordinate branches and the actual normalization fibre

The full local normalization homeomorphism identifies the fibre over a
point in a quotient chart with exactly its vanishing coordinate indices.
The corresponding points are the actual translated affine branch centres
in the ray divisor.  No central-fibre assumption is needed: away from the
central equation, both sets are empty.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open CuspQuotient ToricCharts ToricComponent ToricFan ToricSpace

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- An active coordinate branch has its actual centre in the local branch
domain. -/
theorem activeBranch_mem_domain (b : E₃) (hb : b ∈ (e).target)
    (j : activeBranches b) :
    removeCoordinate j b ∈ normalizationBranchDomain C ε hε hε1 hC hR a s j := by
  change insertZero j (removeCoordinate j b) ∈ (e).target
  rw [insertZero_removeCoordinate j b ((mem_activeBranches b j).mp j.property)]
  exact hb

/-- The point of the actual normalization fibre belonging to an active
coordinate branch. -/
def activeFibrePoint (b : E₃) (hb : b ∈ (e).target) (j : activeBranches b) :
    componentProjection C ε hε ⁻¹' {(e).symm b} :=
  ⟨branchAffine C s j (removeCoordinate j b), by
    change componentProjection C ε hε (branchAffine C s j (removeCoordinate j b)) =
      (e).symm b
    rw [normalizationBranch_project C ε hε hε1 hC hR a s j (removeCoordinate j b)
      (activeBranch_mem_domain C ε hε hε1 hC hR a s b hb j)]
    rw [insertZero_removeCoordinate j b ((mem_activeBranches b j).mp j.property)]⟩

@[simp] theorem activeFibrePoint_val (b : E₃) (hb : b ∈ (e).target)
    (j : activeBranches b) :
    (activeFibrePoint C ε hε hε1 hC hR a s b hb j : rayDivisor 0) =
      branchAffine C s j (removeCoordinate j b) := rfl

@[simp] theorem activeFibrePoint_projection (b : E₃) (hb : b ∈ (e).target)
    (j : activeBranches b) :
    componentProjection C ε hε (activeFibrePoint C ε hε hε1 hC hR a s b hb j) =
      (e).symm b :=
  (activeFibrePoint C ε hε hε1 hC hR a s b hb j).property

theorem activeFibrePoint_coordinates (b : E₃) (hb : b ∈ (e).target)
    (j : activeBranches b) :
    (branchParametrization C s j).symm
      (activeFibrePoint C ε hε hε1 hC hR a s b hb j) = removeCoordinate j b :=
  (branchParametrization C s j).left_inv (by simp)

theorem activeFibrePoint_injective (b : E₃) (hb : b ∈ (e).target) :
    Function.Injective (activeFibrePoint C ε hε hε1 hC hR a s b hb) := by
  intro j k hjk
  let p : NormalizationLocalSource C ε hε hε1 hC hR a s :=
    ⟨j, ⟨removeCoordinate j b, activeBranch_mem_domain C ε hε hε1 hC hR a s b hb j⟩⟩
  let q : NormalizationLocalSource C ε hε hε1 hC hR a s :=
    ⟨k, ⟨removeCoordinate k b, activeBranch_mem_domain C ε hε hε1 hC hR a s b hb k⟩⟩
  have hbranch : branchAffine C s j (removeCoordinate j b) =
      branchAffine C s k (removeCoordinate k b) := congrArg Subtype.val hjk
  have hpq : normalizationLocalMap C ε hε hε1 hC hR a s p =
      normalizationLocalMap C ε hε hε1 hC hR a s q :=
    Subtype.ext hbranch
  have h := normalizationLocalMap_injective C ε hε hε1 hC hR a s hpq
  exact Subtype.ext (congrArg Sigma.fst h)

theorem activeFibrePoint_surjective (b : E₃) (hb : b ∈ (e).target) :
    Function.Surjective (activeFibrePoint C ε hε hε1 hC hR a s b hb) := by
  intro x
  let xU : normalizationPreimage C ε hε hε1 hC hR a s :=
    ⟨x.val, by
      change componentProjection C ε hε x.val ∈ (e).source
      rw [show componentProjection C ε hε x.val = (e).symm b from x.property]
      exact (e).map_target hb⟩
  obtain ⟨⟨j, z⟩, hz⟩ := normalizationLocalMap_surjective C ε hε hε1 hC hR a s xU
  have hbranch : branchAffine C s j z = x.val := congrArg Subtype.val hz
  have hcoord : insertZero j (z : E₂) = b := by
    rw [← normalizationBranch_coordinates C ε hε hε1 hC hR a s j z z.property,
      hbranch, show componentProjection C ε hε x.val = (e).symm b from x.property]
    exact (e).right_inv hb
  have hj : j ∈ activeBranches b := by
    apply (mem_activeBranches b j).mpr
    rw [← hcoord]
    exact insertZero_at j z
  have hzcoord : (z : E₂) = removeCoordinate j b := by
    simpa only [removeCoordinate_insertZero] using congrArg (removeCoordinate j) hcoord
  refine ⟨⟨j, hj⟩, Subtype.ext ?_⟩
  change branchAffine C s j (removeCoordinate j b) = x.val
  rw [← hzcoord]
  exact hbranch

/-- The active coordinate indices enumerate the actual fibre of the
normalization map, without replacing its points by a formal branch set. -/
def activeFibreEquiv (b : E₃) (hb : b ∈ (e).target) :
    (activeBranches b) ≃ (componentProjection C ε hε ⁻¹' {(e).symm b}) :=
  Equiv.ofBijective (activeFibrePoint C ε hε hε1 hC hR a s b hb)
    ⟨activeFibrePoint_injective C ε hε hε1 hC hR a s b hb,
      activeFibrePoint_surjective C ε hε hε1 hC hR a s b hb⟩

@[simp] theorem activeFibreEquiv_apply (b : E₃) (hb : b ∈ (e).target)
    (j : activeBranches b) :
    activeFibreEquiv C ε hε hε1 hC hR a s b hb j =
      activeFibrePoint C ε hε hε1 hC hR a s b hb j := rfl

/-- Recovering the active index also recovers the actual point by its
translated affine branch chart. -/
theorem activeFibreEquiv_symm_branch (b : E₃) (hb : b ∈ (e).target)
    (x : componentProjection C ε hε ⁻¹' {(e).symm b}) :
    branchAffine C s ((activeFibreEquiv C ε hε hε1 hC hR a s b hb).symm x)
      (removeCoordinate ((activeFibreEquiv C ε hε hε1 hC hR a s b hb).symm x) b) =
        (x : rayDivisor 0) :=
  congrArg Subtype.val ((activeFibreEquiv C ε hε hε1 hC hR a s b hb).apply_symm_apply x)

theorem activeFibreEquiv_symm_coordinates (b : E₃) (hb : b ∈ (e).target)
    (x : componentProjection C ε hε ⁻¹' {(e).symm b}) :
    (branchParametrization C s ((activeFibreEquiv C ε hε hε1 hC hR a s b hb).symm x)).symm
      (x : rayDivisor 0) =
        removeCoordinate ((activeFibreEquiv C ε hε hε1 hC hR a s b hb).symm x) b := by
  rw [← activeFibreEquiv_symm_branch C ε hε hε1 hC hR a s b hb x]
  exact (branchParametrization C s _).left_inv (by simp)

end Wikipedia.HopfProblem.CuspNormalization.Germs

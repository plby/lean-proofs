import Wikipedia.HopfProblem.CuspNormalizationChart
import Wikipedia.HopfProblem.CuspNormalizationBranches

/-!
# The full inverse image of a normal-crossing neighbourhood

Over a covering neighbourhood in one toric chart, the component projection
is the disjoint union of the three coordinate-plane maps.  The comparison
below is a homeomorphism onto the *entire* inverse image of the neighbourhood,
not just an enumeration of the fibre at its centre.  Each summand is an open
subset of complex two-space and its map is a genuine analytic branch chart.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricSpace ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- The open domain of the `j`-th coordinate plane in the chosen quotient chart. -/
def normalizationBranchDomain (j : Fin 3) : TopologicalSpace.Opens E₂ :=
  ⟨insertZero j ⁻¹' (e).target, (e).open_target.preimage (insertZero_holomorphic j).continuous⟩

/-- The whole inverse image of the chosen quotient neighbourhood. -/
def normalizationPreimage : TopologicalSpace.Opens (rayDivisor 0) :=
  ⟨componentProjection C ε hε ⁻¹' (e).source,
    (e).open_source.preimage (componentProjection_continuous C ε hε)⟩

/-- The disjoint union of the smooth coordinate branches, including empty
summands when the neighbourhood does not meet a particular plane. -/
def NormalizationLocalSource :=
  (j : Fin 3) × normalizationBranchDomain C ε hε hε1 hC hR a s j

instance normalizationLocalSource_topologicalSpace :
    TopologicalSpace (NormalizationLocalSource C ε hε hε1 hC hR a s) :=
  inferInstanceAs (TopologicalSpace ((j : Fin 3) ×
    normalizationBranchDomain C ε hε hε1 hC hR a s j))

theorem normalizationBranch_project (j : Fin 3) (z : E₂)
    (hz : z ∈ normalizationBranchDomain C ε hε hε1 hC hR a s j) :
    componentProjection C ε hε (branchAffine C s j z) = (e).symm (insertZero j z) := by
  rw [componentProjection_branchAffine]
  exact (normalizationChart_symm_central C ε hε hε1 hC hR a s (centralPlane j z) hz).symm

theorem normalizationBranch_coordinates (j : Fin 3) (z : E₂)
    (hz : z ∈ normalizationBranchDomain C ε hε hε1 hC hR a s j) :
    e (componentProjection C ε hε (branchAffine C s j z)) = insertZero j z := by
  rw [normalizationBranch_project C ε hε hε1 hC hR a s j z hz]
  exact (e).right_inv hz

theorem normalizationBranch_mem_preimage (j : Fin 3) (z : E₂)
    (hz : z ∈ normalizationBranchDomain C ε hε hε1 hC hR a s j) :
    branchAffine C s j z ∈ normalizationPreimage C ε hε hε1 hC hR a s := by
  change componentProjection C ε hε (branchAffine C s j z) ∈ (e).source
  rw [normalizationBranch_project C ε hε hε1 hC hR a s j z hz]
  exact (e).map_target hz

/-- Glue the translated affine branches, as a map into the actual `ν`-preimage. -/
def normalizationLocalMap (p : NormalizationLocalSource C ε hε hε1 hC hR a s) :
    normalizationPreimage C ε hε hε1 hC hR a s :=
  ⟨branchAffine C s p.1 p.2,
    normalizationBranch_mem_preimage C ε hε hε1 hC hR a s p.1 p.2 p.2.2⟩

theorem normalizationLocalMap_continuous :
    Continuous (normalizationLocalMap C ε hε hε1 hC hR a s) := by
  apply continuous_sigma
  intro j
  exact ((branchAffine_continuous C s j).comp continuous_subtype_val).subtype_mk _

theorem normalizationLocalMap_isOpenMap :
    IsOpenMap (normalizationLocalMap C ε hε hε1 hC hR a s) := by
  apply isOpenMap_sigma.mpr
  intro j
  have ho : IsOpenMap (fun z : normalizationBranchDomain C ε hε hε1 hC hR a s j =>
      branchAffine C s j z) :=
    (branchAffine_openEmbedding C s j).isOpenMap.comp
      (normalizationBranchDomain C ε hε hε1 hC hR a s j).isOpen.isOpenMap_subtype_val
  exact ho.codRestrict (fun z => normalizationBranch_mem_preimage C ε hε hε1 hC hR a s j z z.2)

theorem normalizationLocalMap_injective :
    Function.Injective (normalizationLocalMap C ε hε hε1 hC hR a s) := by
  let := tubeAction C (disc ε)
  let := free_action C ε hε hε1 hC hR
  rintro ⟨j, z⟩ ⟨k, w⟩ h
  have hbranch : branchAffine C s j z = branchAffine C s k w := congrArg Subtype.val h
  have hquot := congrArg (componentProjection C ε hε) hbranch
  rw [normalizationBranch_project C ε hε hε1 hC hR a s j z z.2,
    normalizationBranch_project C ε hε hε1 hC hR a s k w w.2] at hquot
  have hcoord : insertZero j (z : E₂) = insertZero k (w : E₂) :=
    (e).symm.injOn z.2 w.2 hquot
  have hcentral : centralPlane j (z : E₂) = centralPlane k (w : E₂) := Subtype.ext hcoord
  have hsmul := congrArg (componentLift ε hε) hbranch
  rw [componentLift_branchAffine, componentLift_branchAffine, ← hcentral] at hsmul
  change (Multiplicative.ofAdd (cuspVector (s.vertex j)) : LatticeGroup) •
      centralLift ε hε s (centralPlane j z) =
    (Multiplicative.ofAdd (cuspVector (s.vertex k)) : LatticeGroup) •
      centralLift ε hε s (centralPlane j z) at hsmul
  have hgroup := IsCancelSMul.right_cancel _ _ _ hsmul
  have hjk : j = k := s.vertex_injective
    (cuspVector_injective (congrArg Multiplicative.toAdd hgroup))
  subst k
  have hzw : (z : E₂) = (w : E₂) := by
    simpa only [removeCoordinate_insertZero] using congrArg (removeCoordinate j) hcoord
  have hzw' : z = w := Subtype.ext hzw
  cases hzw'
  rfl

theorem normalizationLocalMap_surjective :
    Function.Surjective (normalizationLocalMap C ε hε hε1 hC hR a s) := by
  let := tubeAction C (disc ε)
  let hq := quotientMap_covering C ε hε hε1 hC hR
  intro x
  let y := componentProjection C ε hε x.1
  have hy : y ∈ (e).source := x.2
  let b := CoveringQuotient.localInverse hq a y
  have hb : quotientMap C ε b = y := CoveringQuotient.project_localInverse hq a hy.1
  let xf : componentProjection C ε hε ⁻¹' {quotientMap C ε b} := ⟨x.1, hb.symm⟩
  obtain ⟨v, hv⟩ := componentFibreMap_surjective C ε hε b xf
  have hvx : branchRepresentative C ε b v = x.1 := congrArg Subtype.val hv
  have hcoordinates : (b : Space) = inclusion s (e y) :=
    normalizationChart_lift_coordinates C ε hε hε1 hC hR a s hy
  have hvbranch : inclusion s (e y) ∈ rayDivisor (v : Fin 2 → ℤ) := by
    rw [← hcoordinates]
    exact v.2
  obtain ⟨j, hj, hjv⟩ := (mem_rayDivisor_inclusion (v : Fin 2 → ℤ) s (e y)).mp hvbranch
  let z := removeCoordinate j (e y)
  have hz : insertZero j z = e y := insertZero_removeCoordinate j (e y) hj
  have hzmem : z ∈ normalizationBranchDomain C ε hε hε1 hC hR a s j := by
    change insertZero j z ∈ (e).target
    rw [hz]
    exact (e).map_source hy
  refine ⟨⟨j, ⟨z, hzmem⟩⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (branchAffine C s j z : Space) = (x.1 : Space)
  rw [branchAffine_coe, hz, hjv, ← hcoordinates]
  exact congrArg Subtype.val hvx

/-- The local normalization source is homeomorphic to the whole inverse
image of the quotient-chart neighbourhood. -/
def normalizationLocalHomeomorph :
    NormalizationLocalSource C ε hε hε1 hC hR a s ≃ₜ
      normalizationPreimage C ε hε hε1 hC hR a s :=
  (Equiv.ofBijective (normalizationLocalMap C ε hε hε1 hC hR a s)
    ⟨normalizationLocalMap_injective C ε hε hε1 hC hR a s,
      normalizationLocalMap_surjective C ε hε hε1 hC hR a s⟩).toHomeomorphOfContinuousOpen
        (normalizationLocalMap_continuous C ε hε hε1 hC hR a s)
        (normalizationLocalMap_isOpenMap C ε hε hε1 hC hR a s)

@[simp] theorem normalizationLocalHomeomorph_apply
    (p : NormalizationLocalSource C ε hε hε1 hC hR a s) :
    (normalizationLocalHomeomorph C ε hε hε1 hC hR a s p : rayDivisor 0) =
      branchAffine C s p.1 p.2 := rfl

/-- In the target chart the actual map is exactly the coordinate-plane inclusion. -/
theorem normalizationLocalHomeomorph_coordinates
    (p : NormalizationLocalSource C ε hε hε1 hC hR a s) :
    e (componentProjection C ε hε
      (normalizationLocalHomeomorph C ε hε hε1 hC hR a s p)) = insertZero p.1 p.2 :=
  normalizationBranch_coordinates C ε hε hε1 hC hR a s p.1 p.2 p.2.2

theorem normalizationLocalHomeomorph_symm_branch
    (x : normalizationPreimage C ε hε hε1 hC hR a s) :
    branchAffine C s ((normalizationLocalHomeomorph C ε hε hε1 hC hR a s).symm x).1
      ((normalizationLocalHomeomorph C ε hε hε1 hC hR a s).symm x).2 = (x : rayDivisor 0) := by
  exact congrArg Subtype.val
    ((normalizationLocalHomeomorph C ε hε hε1 hC hR a s).apply_symm_apply x)

theorem normalizationLocalHomeomorph_symm_coordinates
    (x : normalizationPreimage C ε hε hε1 hC hR a s) (j : Fin 3)
    (hj : ((normalizationLocalHomeomorph C ε hε hε1 hC hR a s).symm x).1 = j) :
    (((normalizationLocalHomeomorph C ε hε hε1 hC hR a s).symm x).2 : E₂) =
      (branchParametrization C s j).symm (x : rayDivisor 0) := by
  subst j
  rw [← normalizationLocalHomeomorph_symm_branch C ε hε hε1 hC hR a s x]
  exact ((branchParametrization C s _).left_inv (by simp)).symm

theorem normalizationLocalHomeomorph_symm_mem_branch
    (x : normalizationPreimage C ε hε hε1 hC hR a s) (j : Fin 3)
    (hj : ((normalizationLocalHomeomorph C ε hε hε1 hC hR a s).symm x).1 = j) :
    (x : rayDivisor 0) ∈ range (branchAffine C s j) := by
  subst j
  exact ⟨((normalizationLocalHomeomorph C ε hε hε1 hC hR a s).symm x).2,
    normalizationLocalHomeomorph_symm_branch C ε hε hε1 hC hR a s x⟩

end Wikipedia.HopfProblem.CuspQuotient

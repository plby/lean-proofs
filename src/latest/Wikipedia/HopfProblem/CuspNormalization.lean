import Wikipedia.HopfProblem.CuspNormalizationLocal
import Wikipedia.HopfProblem.CuspNormalizationSigma
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The analytic coordinate-branch model of the cusp normalization

The whole inverse image of each adapted quotient neighbourhood is
biholomorphic to the disjoint union of its coordinate-plane domains.  In
these independently constructed complex atlases the actual component map
is precisely the map inserting the missing zero coordinate.

This is the geometric local normalization model for a reduced
normal-crossing surface.  The declarations construct the maps, their
holomorphic inverses and the commuting diagram.  They do not assume a
normalization theorem or identify the integral closure of holomorphic-germ
stalks; no sheaf structure on the singular central fibre is introduced here.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricSpace ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3
local notation "I₂" => modelWithCornersSelf ℂ E₂
local notation "I₃" => modelWithCornersSelf ℂ E₃

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle)

local notation "U" => normalizationBranchDomain C ε hε hε1 hC hR a s
local notation "H" => normalizationLocalHomeomorph C ε hε hε1 hC hR a s

/-- The source uses the disjoint-union atlas of its open coordinate domains,
not an atlas transported from the component surface. -/
instance normalizationLocalSource_chartedSpace :
    ChartedSpace E₂ (NormalizationLocalSource C ε hε hε1 hC hR a s) :=
  CuspNormalizationSigma.chartedSpace U

instance normalizationLocalSource_isManifold :
    IsManifold I₂ ω (NormalizationLocalSource C ε hε hε1 hC hR a s) :=
  CuspNormalizationSigma.isManifold U ω

theorem normalizationLocalHomeomorph_holomorphic :
    ContMDiff I₂ I₂ ω H := by
  apply (CuspNormalizationSigma.contMDiff_iff U I₂ ω _).mpr
  intro j z
  have he : ContMDiffAt I₂ I₂ ω
      (fun w : U j => (normalizationLocalMap C ε hε hε1 hC hR a s ⟨j, w⟩ : rayDivisor 0)) z ↔
      ContMDiffAt I₂ I₂ ω
        (fun w : U j => normalizationLocalMap C ε hε hε1 hC hR a s ⟨j, w⟩) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (((branchAffine_holomorphic C s j).comp contMDiff_subtype_val) z)

theorem normalizationLocalHomeomorph_symm_coordinates_holomorphic :
    ContMDiff I₂ I₂ ω (CuspNormalizationSigma.coordinates U ∘ (H).symm) := by
  intro x
  let j : Fin 3 := ((H).symm x).1
  have hbranch : (x : rayDivisor 0) ∈ range (branchAffine C s j) :=
    normalizationLocalHomeomorph_symm_mem_branch C ε hε hε1 hC hR a s x j rfl
  have hlocal : ContMDiffAt I₂ I₂ ω (branchParametrization C s j).symm (x : rayDivisor 0) :=
    (branchParametrization_symm_holomorphic C s j).contMDiffAt
      ((branchAffine_openEmbedding C s j).isOpen_range.mem_nhds hbranch)
  have hindex : ∀ᶠ y in 𝓝 x, ((H).symm y).1 = j := by
    have ho : IsOpen {p : NormalizationLocalSource C ε hε hε1 hC hR a s | p.1 = j} :=
      isOpen_sigma_fst_preimage {j}
    exact (ho.preimage (H).symm.continuous).mem_nhds rfl
  have heq : (CuspNormalizationSigma.coordinates U ∘ (H).symm) =ᶠ[𝓝 x]
      (fun y => (branchParametrization C s j).symm (y : rayDivisor 0)) :=
    hindex.mono fun y hy =>
      normalizationLocalHomeomorph_symm_coordinates C ε hε hε1 hC hR a s y j hy
  exact (hlocal.comp x contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq heq

theorem normalizationLocalHomeomorph_symm_holomorphic :
    ContMDiff I₂ I₂ ω (H).symm := by
  apply (ContMDiff.iff_comp_isImmersion (CuspNormalizationSigma.coordinates_isImmersion U)).mpr
  exact ⟨(H).symm.continuous,
    normalizationLocalHomeomorph_symm_coordinates_holomorphic C ε hε hε1 hC hR a s⟩

/-- The full local comparison is analytic in both directions. -/
def normalizationLocalBiholomorph :
    Diffeomorph I₂ I₂ (NormalizationLocalSource C ε hε hε1 hC hR a s)
      (normalizationPreimage C ε hε hε1 hC hR a s) ω where
  toEquiv := (H).toEquiv
  contMDiff_toFun := normalizationLocalHomeomorph_holomorphic C ε hε hε1 hC hR a s
  contMDiff_invFun := normalizationLocalHomeomorph_symm_holomorphic C ε hε hε1 hC hR a s

@[simp] theorem normalizationLocalBiholomorph_apply
    (p : NormalizationLocalSource C ε hε hε1 hC hR a s) :
    (normalizationLocalBiholomorph C ε hε hε1 hC hR a s p : rayDivisor 0) =
      branchAffine C s p.1 p.2 := rfl

theorem normalizationLocalBiholomorph_coordinates
    (p : NormalizationLocalSource C ε hε hε1 hC hR a s) :
    normalizationChart C ε hε hε1 hC hR a s
      (componentProjection C ε hε
        (normalizationLocalBiholomorph C ε hε hε1 hC hR a s p)) = insertZero p.1 p.2 :=
  normalizationLocalHomeomorph_coordinates C ε hε hε1 hC hR a s p

omit a s in
/-- Every cusp point has an actual analytic quotient chart in which the
whole component preimage is the disjoint union of the coordinate planes.
The equivalence is biholomorphic for the original complex structure on
`E₀` and the standard complex structures on the branch domains. -/
theorem componentProjection_local_coordinate_normalization (x : QuotientSpace C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ∃ a : Tube (disc ε), ∃ s : Triangle,
      quotientMap C ε a = x ∧
      x ∈ (normalizationChart C ε hε hε1 hC hR a s).source ∧
      normalizationChart C ε hε hε1 hC hR a s ∈
        IsManifold.maximalAtlas I₃ ω (QuotientSpace C ε) ∧
      (∀ z ∈ (normalizationChart C ε hε hε1 hC hR a s).target,
        projection C ε ((normalizationChart C ε hε hε1 hC hR a s).symm z) = Triangle.time z) ∧
      ∃ Φ : Diffeomorph I₂ I₂ (NormalizationLocalSource C ε hε hε1 hC hR a s)
          (normalizationPreimage C ε hε hε1 hC hR a s) ω,
        ∀ p, normalizationChart C ε hε hε1 hC hR a s
          (componentProjection C ε hε (Φ p)) = insertZero p.1 p.2 := by
  let := tubeAction C (disc ε)
  let := chartedSpace C ε hε hε1 hC hR
  obtain ⟨a, rfl⟩ := (quotientMap_covering C ε hε hε1 hC hR).surjective x
  let s := preferredTriangle (a : Space)
  refine ⟨a, s, rfl, normalizationChart_mem_source C ε hε hε1 hC hR a s (preferred_mem _),
    normalizationChart_mem_maximalAtlas C ε hε hε1 hC hR a s,
    fun z hz => normalizationChart_projection C ε hε hε1 hC hR a s hz,
    normalizationLocalBiholomorph C ε hε hε1 hC hR a s, ?_⟩
  exact normalizationLocalBiholomorph_coordinates C ε hε hε1 hC hR a s

end Wikipedia.HopfProblem.CuspQuotient

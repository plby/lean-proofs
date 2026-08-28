import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreIdentificationBasic
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertQuotientAnalytic
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Analytic identification of the Appell--Humbert line bundle and quotient

The cocycle bundle and the diagonal orbit quotient keep their independently
constructed topologies. Their explicit inverse maps are holomorphic in the
existing bundle and quotient atlases, and preserve the original period-torus
base. Fibre linearity is checked in the actual scalar quotient coordinates.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

local notation "I₀" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

/-- The explicit bundle-to-quotient map is holomorphic in the original atlases. -/
theorem toAssociated_holomorphic :
    letI := associatedChartedSpace F
    ContMDiff ((I₀).prod I₁) I₂ ω (toAssociated F) := by
  let := associatedChartedSpace F
  intro u
  let e := trivializationAt ℂ (data F).core.Fiber u.proj
  have hu : u ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
  have he : ContMDiffAt ((I₀).prod I₁) ((I₀).prod I₁) ω e u :=
    e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hu)
  have hl : ContMDiffAt I₀ I₀ ω (lift p u.proj) u.proj :=
    (lift_holomorphic p u.proj).contMDiffAt
      ((isOpen_baseSet p u.proj).mem_nhds (mem_baseSet p u.proj))
  have hm : ContMDiffAt ((I₀).prod I₁) I₂ ω
      (fun r : p.Torus × ℂ => associatedMap F (lift p u.proj r.1, r.2)) (e u) := by
    have hf : ContMDiffAt ((I₀).prod I₁) I₂ ω
        (fun r : p.Torus × ℂ => (lift p u.proj r.1, r.2)) (e u) :=
      (hl.comp (e u) contMDiffAt_fst).prodMk_space contMDiffAt_snd
    exact (associatedMap_holomorphic F).contMDiffAt.comp (e u) hf
  apply (hm.comp u he).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hu] with r hr
  exact toAssociated_localTriv F u.proj r hr

/-- On the covering vector space, the inverse has locally the genuine
holomorphic scalar multiplier `F(l,z)` for a fixed lattice vector `l`. -/
theorem fromAssociated_comp_holomorphic :
    ContMDiff I₂ ((I₀).prod I₁) ω (fromAssociated F ∘ associatedMap F) := by
  intro u
  apply Bundle.contMDiffAt_totalSpace.mpr
  constructor
  · have hproj : ContMDiff I₂ I₀ ω
        (fun r : ComplexPlane₂ × ℂ => p.lattice.mkQ r.1) :=
      p.torus_projection_holomorphic.comp contDiff_fst.contMDiff
    exact hproj.contMDiffAt
  · change ContMDiffAt I₂ I₁ ω (fun r : ComplexPlane₂ × ℂ =>
      ((data F).core.localTriv (p.lattice.mkQ u.1)
        (fromAssociated F (associatedMap F r))).2) u
    obtain ⟨l, hl⟩ := lift_comp_mkQ_locally_add p (p.lattice.mkQ u.1) u.1
      (mem_baseSet p (p.lattice.mkQ u.1))
    have hnear : ∀ᶠ r : ComplexPlane₂ × ℂ in 𝓝 u,
        p.lattice.mkQ r.1 ∈ baseSet p (p.lattice.mkQ u.1) :=
      (p.lattice.continuous_mkQ.comp continuous_fst).continuousAt
        ((isOpen_baseSet p (p.lattice.mkQ u.1)).mem_nhds
          (mem_baseSet p (p.lattice.mkQ u.1)))
    have hs : ContMDiffAt I₂ I₁ ω
        (fun r : ComplexPlane₂ × ℂ => (F.factor l r.1 : ℂ) * r.2) u :=
      (((F.holomorphic_factor l).comp contDiff_fst).mul contDiff_snd).contMDiff.contMDiffAt
    apply hs.congr_of_eventuallyEq
    filter_upwards [hnear, hl.comp_tendsto continuousAt_fst] with r hr hlr
    exact congrArg Prod.snd
      (localTriv_fromAssociated_map F (p.lattice.mkQ u.1) r.1 r.2 l hr hlr)

/-- Holomorphicity of the inverse descends through the actual covering quotient. -/
theorem fromAssociated_holomorphic :
    letI := associatedChartedSpace F
    ContMDiff I₂ ((I₀).prod I₁) ω (fromAssociated F) := by
  let := associatedChartedSpace F
  let := diagonalAction F
  exact CoveringQuotient.contMDiff_of_comp
    (associatedMap_isQuotientCoveringMap F) ((I₀).prod I₁) ω
    (fromAssociated_comp_holomorphic F)

/-- A base-preserving analytic diffeomorphism with the independently topologized
orbit quotient, using no replacement of the base torus's atlas. -/
def identification :
    letI := associatedChartedSpace F
    Diffeomorph ((I₀).prod I₁) I₂ (data F).core.TotalSpace (AssociatedSpace F) ω := by
  letI := associatedChartedSpace F
  exact
    { toFun := toAssociated F
      invFun := fromAssociated F
      left_inv := fromAssociated_toAssociated F
      right_inv := toAssociated_fromAssociated F
      contMDiff_toFun := toAssociated_holomorphic F
      contMDiff_invFun := fromAssociated_holomorphic F }

@[simp] theorem identification_apply (u : (data F).core.TotalSpace) :
    identification F u = toAssociated F u := rfl

@[simp] theorem identification_symm_apply (u : AssociatedSpace F) :
    letI := associatedChartedSpace F
    (identification F).symm u = fromAssociated F u := rfl

@[simp] theorem identification_preserves_base (u : (data F).core.TotalSpace) :
    projection F (identification F u) = u.proj := projection_toAssociated F u

@[simp] theorem identification_symm_preserves_base (u : AssociatedSpace F) :
    letI := associatedChartedSpace F
    ((identification F).symm u).proj = projection F u := rfl

/-- In every original torus chart, the identification is the explicitly
proved complex-linear scalar quotient coordinate on each fibre. -/
theorem identification_fibreLinearEquiv (i b : p.Torus) (z : (data F).core.Fiber b)
    (hb : b ∈ baseSet p i) :
    fibreCoordinate F (lift p i b) (identification F ⟨b, z⟩)
      ((identification_preserves_base F _).trans (lift_project p i hb).symm) =
        fibreLinearEquiv F i b z :=
  fibreCoordinate_toAssociated_linear F i b z hb

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core

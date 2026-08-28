import Wikipedia.HopfProblem.EllipticLocalModel
import Wikipedia.HopfProblem.EllipticDiscLocalInverse
import Mathlib.Geometry.Manifold.Submersion

/-!
# Submersivity of the actual elliptic filling away from its multiple fibre

The local projection is a power of the first complex coordinate.  A
genuine inverse-function chart for that power turns it into the first
coordinate itself.  These charts lie in the filling's constructed
maximal analytic atlas.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

local notation "I₃" => modelWithCornersSelf ℂ FamilyModel
local notation "I₁" => modelWithCornersSelf ℂ ℂ

def complexPowerProductChart (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    OpenPartialHomeomorph FamilyModel FamilyModel :=
  (complexPowerChart m hm z hz).prod (OpenPartialHomeomorph.refl ComplexPlane₂)

theorem complexPowerProductChart_holomorphic (m : ℕ) (hm : 0 < m)
    (z : ℂ) (hz : z ≠ 0) :
    ContDiffOn ℂ ω (complexPowerProductChart m hm z hz)
      (complexPowerProductChart m hm z hz).source := by
  exact (complexPowerChart_holomorphic m hm z hz).prodMap contDiffOn_id

theorem complexPowerProductChart_symm_holomorphic (m : ℕ) (hm : 0 < m)
    (z : ℂ) (hz : z ≠ 0) :
    ContDiffOn ℂ ω (complexPowerProductChart m hm z hz).symm
      (complexPowerProductChart m hm z hz).target := by
  exact (complexPowerChart_symm_holomorphic m hm z hz).prodMap contDiffOn_id

theorem fillingChart_first_ne_zero (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv)
    (hy : fillingProjection j v hv y ≠ Elliptic.discZero) :
    (chartAt FamilyModel y y).1 ≠ 0 :=
  mt (fillingCentral_chart_iff j v hv y y (mem_chart_source FamilyModel y)).mpr hy

/-- A filling chart in which the actual base coordinate is the first
coordinate, obtained by an analytic power-coordinate change. -/
def fillingSubmersionChart (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv)
    (hy : fillingProjection j v hv y ≠ Elliptic.discZero) :
    OpenPartialHomeomorph (Filling j v hv) FamilyModel :=
  (chartAt FamilyModel y).trans
    (complexPowerProductChart j.order j.order_pos (chartAt FamilyModel y y).1
      (fillingChart_first_ne_zero j v hv y hy))

theorem mem_fillingSubmersionChart_source (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv)
    (hy : fillingProjection j v hv y ≠ Elliptic.discZero) :
    y ∈ (fillingSubmersionChart j v hv y hy).source := by
  refine ⟨mem_chart_source FamilyModel y, ?_⟩
  exact ⟨mem_complexPowerChart_source j.order j.order_pos
    (chartAt FamilyModel y y).1 (fillingChart_first_ne_zero j v hv y hy), mem_univ _⟩

theorem fillingSubmersionChart_holomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv)
    (hy : fillingProjection j v hv y ≠ Elliptic.discZero) :
    ContMDiffOn I₃ I₃ ω (fillingSubmersionChart j v hv y hy)
      (fillingSubmersionChart j v hv y hy).source := by
  exact (complexPowerProductChart_holomorphic j.order j.order_pos
    (chartAt FamilyModel y y).1 (fillingChart_first_ne_zero j v hv y hy)).contMDiffOn.comp
      (contMDiffOn_chart.mono inter_subset_left) (fun _ hx => hx.2)

theorem fillingSubmersionChart_symm_holomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv)
    (hy : fillingProjection j v hv y ≠ Elliptic.discZero) :
    ContMDiffOn I₃ I₃ ω (fillingSubmersionChart j v hv y hy).symm
      (fillingSubmersionChart j v hv y hy).target := by
  have hc : ContMDiffOn I₃ I₃ ω (chartAt FamilyModel y).symm
      (chartAt FamilyModel y).target := contMDiffOn_chart_symm
  have hp : ContMDiffOn I₃ I₃ ω
      (complexPowerProductChart j.order j.order_pos (chartAt FamilyModel y y).1
        (fillingChart_first_ne_zero j v hv y hy)).symm
      (complexPowerProductChart j.order j.order_pos (chartAt FamilyModel y y).1
        (fillingChart_first_ne_zero j v hv y hy)).target :=
    (complexPowerProductChart_symm_holomorphic j.order j.order_pos
      (chartAt FamilyModel y y).1 (fillingChart_first_ne_zero j v hv y hy)).contMDiffOn
  exact hc.comp (hp.mono inter_subset_left) (fun _ hx => hx.2)

theorem fillingSubmersionChart_mem_maximalAtlas (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv)
    (hy : fillingProjection j v hv y ≠ Elliptic.discZero) :
    fillingSubmersionChart j v hv y hy ∈ IsManifold.maximalAtlas I₃ ω (Filling j v hv) :=
  (fillingSubmersionChart j v hv y hy).mem_maximalAtlas_of_contMDiffOn
    (fillingSubmersionChart_holomorphic j v hv y hy)
    (fillingSubmersionChart_symm_holomorphic j v hv y hy)

theorem fillingSubmersionChart_symm_projection (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv)
    (hy : fillingProjection j v hv y ≠ Elliptic.discZero) {w : FamilyModel}
    (hw : w ∈ (fillingSubmersionChart j v hv y hy).target) :
    (fillingProjection j v hv ((fillingSubmersionChart j v hv y hy).symm w) : ℂ) =
      w.1 := by
  let e := complexPowerChart j.order j.order_pos (chartAt FamilyModel y y).1
    (fillingChart_first_ne_zero j v hv y hy)
  have hc : (e.symm w.1, w.2) ∈ (chartAt FamilyModel y).target := hw.2
  change (fillingProjection j v hv ((chartAt FamilyModel y).symm (e.symm w.1, w.2)) : ℂ) = _
  rw [fillingProjection_chart_symm j v hv y _ hc]
  exact e.right_inv hw.1.1

/-- The disc projection is a holomorphic submersion at every point outside
the central fibre, with complex two-dimensional complement. -/
theorem fillingProjection_submersionAt (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv)
    (hy : fillingProjection j v hv y ≠ Elliptic.discZero) :
    Manifold.IsSubmersionAtOfComplement ComplexPlane₂ I₃ I₁ ω
      (fillingProjection j v hv) y := by
  refine Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt
    (fillingProjection_holomorphic j v hv).continuous.continuousAt
    (ContinuousLinearEquiv.refl ℂ FamilyModel)
    (fillingSubmersionChart j v hv y hy) (chartAt ℂ (fillingProjection j v hv y))
    (mem_fillingSubmersionChart_source j v hv y hy) (mem_chart_source ℂ _)
    (fillingSubmersionChart_mem_maximalAtlas j v hv y hy)
    (IsManifold.chart_mem_maximalAtlas _) ?_
  intro w hw
  have hw' : w ∈ (fillingSubmersionChart j v hv y hy).target := by
    simpa [OpenPartialHomeomorph.extend] using hw
  change (chartAt ℂ (fillingProjection j v hv y))
    (fillingProjection j v hv ((fillingSubmersionChart j v hv y hy).symm w)) = w.1
  rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  exact fillingSubmersionChart_symm_projection j v hv y hy hw'

end Wikipedia.HopfProblem.Elliptic

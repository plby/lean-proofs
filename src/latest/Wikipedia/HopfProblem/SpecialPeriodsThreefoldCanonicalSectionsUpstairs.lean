import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalBundle
import Wikipedia.HopfProblem.EllipticEquivariantData

/-!
# Genuine weighted canonical forms on the elliptic period families

The upstairs canonical bundle is the native tangent-canonical bundle of
the actual varying lattice quotient.  A holomorphic coefficient on the
base disc multiplies its genuine global volume form.  Its zero set is
exactly that of the coefficient, and every valid native chart represents
the section by that coefficient times the actual product volume.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsUpstairs

open SpecialPeriods

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

/-- All preferred charts of the disc have their literal complex coordinate. -/
theorem disc_chart_apply (a s : Disc) : chartAt ℂ a s = (s : ℂ) := rfl

variable (P : HolomorphicPeriodMap ℂ Disc)

/-- The original canonical bundle of the actual varying-period family. -/
abbrev bundle := familyCanonicalBundle P

/-- A genuine ambient three-form, weighted by a function on the actual base. -/
def weightedSection (F : Disc → ℂ) (x : P.TotalSpace) : (bundle P).Fiber x :=
  F x.1 • familyCanonicalVolume P x

def sectionMap (F : Disc → ℂ) (x : P.TotalSpace) : (bundle P).TotalSpace :=
  ⟨x, weightedSection P F x⟩

@[simp] theorem sectionMap_proj (F : Disc → ℂ) (x : P.TotalSpace) :
    (sectionMap P F x).proj = x := rfl

/-- Scalar equality here is a consequence of the actual native volume
frame, rather than a replacement of the canonical bundle by a formal line. -/
theorem section_coefficient (F : Disc → ℂ) (x : P.TotalSpace) :
    id (α := ℂ) (weightedSection P F x) = F x.1 := by
  change F x.1 * 1 = F x.1
  exact mul_one _

theorem section_eq_zero_iff (F : Disc → ℂ) (x : P.TotalSpace) :
    weightedSection P F x = 0 ↔ F x.1 = 0 := by
  change F x.1 * 1 = 0 ↔ F x.1 = 0
  rw [mul_one]

theorem section_ne_zero_iff (F : Disc → ℂ) (x : P.TotalSpace) :
    weightedSection P F x ≠ 0 ↔ F x.1 ≠ 0 := (section_eq_zero_iff P F x).not

/-- Holomorphicity is measured in the existing canonical bundle atlas. -/
theorem sectionMap_holomorphic (F : Disc → ℂ) (hF : ContMDiff I₁ I₁ ω F) :
    letI := P.totalChartedSpace
    ContMDiff I₃ ((I₃).prod I₁) ω (sectionMap P F) := by
  let := P.totalChartedSpace
  let := P.totalSpace_isManifold
  have hc : ContMDiff I₃ I₁ ω (fun x : P.TotalSpace => F x.1) :=
    hF.comp P.projection_holomorphic
  have h := (familyCanonicalTrivialization (fun s : Disc => (s : ℂ))
    disc_chart_apply P).symm.contMDiff.comp (contMDiff_id.prodMk hc)
  convert h using 1
  funext x
  change (⟨x, F x.1 * 1⟩ : (bundle P).TotalSpace) = ⟨x, F x.1⟩
  exact congrArg (fun v : ℂ => (⟨x, v⟩ : (bundle P).TotalSpace)) (mul_one (F x.1))

/-- The corresponding bundled holomorphic section of the genuine line bundle. -/
def holomorphicSection (F : Disc → ℂ) (hF : ContMDiff I₁ I₁ ω F) :
    letI := P.totalChartedSpace
    ContMDiffSection I₃ ℂ ω (bundle P).Fiber := by
  let := P.totalChartedSpace
  exact ⟨weightedSection P F, sectionMap_holomorphic P F hF⟩

@[simp] theorem holomorphicSection_apply (F : Disc → ℂ) (hF : ContMDiff I₁ I₁ ω F)
    (x : P.TotalSpace) : holomorphicSection P F hF x = weightedSection P F x := rfl

/-- Intrinsic interpretation as an alternating three-covector on the actual tangent. -/
theorem section_intrinsic (F : Disc → ℂ) (x : P.TotalSpace) :
    familyCanonicalIntrinsicEquiv P x (weightedSection P F x) = F x.1 • volume := by
  rw [weightedSection, map_smul, familyCanonicalIntrinsicEquiv_volume]
  rfl

/-- The exact coefficient in every valid original family chart. -/
theorem section_inCoordinates (F : Disc → ℂ) (i x : P.TotalSpace)
    (hx : x ∈ (familyChart P i).source) :
    familyCanonicalInCoordinates P i x (weightedSection P F x) = F x.1 • volume := by
  let := P.totalChartedSpace
  let := P.totalSpace_isManifold
  change Atlas.coordinateEquiv P.TotalSpace (familyChartIndex P i) hx
      (F x.1 • familyCanonicalVolume P x) = _
  rw [map_smul]
  change F x.1 • familyCanonicalInCoordinates P i x (familyCanonicalVolume P x) = _
  rw [familyCanonicalVolume_inCoordinates (fun s : Disc => (s : ℂ)) disc_chart_apply P i x hx]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsUpstairs

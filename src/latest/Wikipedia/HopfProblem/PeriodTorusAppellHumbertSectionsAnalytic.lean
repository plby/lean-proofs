import Wikipedia.HopfProblem.PeriodTorusAppellHumbertSections
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertQuotientAnalytic

/-!
# Holomorphic sections and genuine entire automorphic functions

Holomorphicity of a section is tested in the actual quotient atlas and
the unchanged period-torus atlas. Its pulled-back scalar function is
proved analytic using a local inverse of the actual total-space covering.
Conversely, an entire analytic automorphic function descends to an actual
holomorphic section. Thus the correspondence is not a definition of
holomorphicity or a substitute for a quotient bundle construction.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

/-- Holomorphicity of an actual section in the two independently constructed atlases. -/
def Section.IsHolomorphic (s : Section F) : Prop :=
  letI := associatedChartedSpace F
  ContMDiff IC IP ω (s : p.Torus → AssociatedSpace F)

/-- Analytic automorphic functions descend analytically through the actual lattice quotient. -/
theorem sectionOfAutomorphic_holomorphic (f : ComplexPlane₂ → ℂ)
    (hf : IsAutomorphic F f) (hfhol : ContDiff ℂ ω f) :
    (sectionOfAutomorphic F f hf).IsHolomorphic F := by
  let := associatedChartedSpace F
  apply DiscreteQuotient.contMDiff_of_comp_mkQ p.lattice IP ω
  have he : ((sectionOfAutomorphic F f hf : p.Torus → AssociatedSpace F) ∘ p.lattice.mkQ) =
      fun z => associatedMap F (z, f z) := by
    funext z
    exact sectionOfAutomorphic_apply_project F f hf z
  rw [he]
  apply (associatedMap_holomorphic F).comp
  exact (contDiff_id.prodMk hfhol).contMDiff

theorem zeroSection_holomorphic : (zeroSection F).IsHolomorphic F :=
  sectionOfAutomorphic_holomorphic F _ _ contDiff_const

/-- The actual scalar pullback of a holomorphic section is holomorphic. -/
theorem Section.pullback_contMDiff (s : Section F) (hs : s.IsHolomorphic F) :
    ContMDiff IC I₁ ω (s.pullback F) := by
  let := associatedChartedSpace F
  let := diagonalAction F
  have hs' : ContMDiff IC IP ω (fun z => s (p.lattice.mkQ z)) :=
    hs.comp p.torus_projection_holomorphic
  intro z
  let u : ComplexPlane₂ × ℂ := (z, s.pullback F z)
  let hP := associatedMap_isQuotientCoveringMap F
  let e := CoveringQuotient.localInverse hP u
  let l : ComplexPlane₂ → ComplexPlane₂ × ℂ := fun y => e (s (p.lattice.mkQ y))
  have huz : associatedMap F u = s (p.lattice.mkQ z) := s.associatedMap_pullback F z
  have hsrc : s (p.lattice.mkQ z) ∈ e.source := by
    rw [← huz]
    exact hP.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
  have hl : ContMDiffAt IC IP ω l z :=
    ((associatedLocalInverse_holomorphic F u).contMDiffAt
      (e.open_source.mem_nhds hsrc)).comp z hs'.contMDiffAt
  have hlz : l z = u := by
    change e (s (p.lattice.mkQ z)) = u
    rw [← huz]
    exact hP.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self
  have hsource : ∀ᶠ y in 𝓝 z, s (p.lattice.mkQ y) ∈ e.source :=
    hs'.continuous.continuousAt (e.open_source.mem_nhds hsrc)
  have hfirst : (fun y => (l y).1) =ᶠ[𝓝 z] (fun y => y) := by
    apply eventuallyEq_of_localHomeomorph_comp_eq
      p.quotientCovering.isCoveringMap.isLocalHomeomorph
      (continuous_fst.continuousAt.comp hl.continuousAt) continuousAt_id
      (congrArg Prod.fst hlz)
    filter_upwards [hsource] with y hy
    calc
      p.lattice.mkQ (l y).1 = projection F (associatedMap F (l y)) := rfl
      _ = projection F (s (p.lattice.mkQ y)) := congrArg (projection F)
        (CoveringQuotient.project_localInverse hP u hy)
      _ = p.lattice.mkQ y := s.projection_apply F (p.lattice.mkQ y)
  have heq : s.pullback F =ᶠ[𝓝 z] (fun y => (l y).2) := by
    filter_upwards [hsource, hfirst] with y hy hfy
    apply associatedMap_fibre_injective F y
    calc
      associatedMap F (y, s.pullback F y) = s (p.lattice.mkQ y) :=
        s.associatedMap_pullback F y
      _ = associatedMap F (l y) := (CoveringQuotient.project_localInverse hP u hy).symm
      _ = associatedMap F (y, (l y).2) :=
        congrArg (associatedMap F) (Prod.ext hfy rfl)
  have hsnd : ContMDiff IP I₁ ω (Prod.snd : ComplexPlane₂ × ℂ → ℂ) :=
    (contDiff_snd : ContDiff ℂ ω (Prod.snd : ComplexPlane₂ × ℂ → ℂ)).contMDiff
  exact (hsnd.contMDiffAt.comp z hl).congr_of_eventuallyEq heq

theorem Section.pullback_contDiff (s : Section F) (hs : s.IsHolomorphic F) :
    ContDiff ℂ ω (s.pullback F) := (s.pullback_contMDiff F hs).contDiff

theorem Section.isHolomorphic_iff_pullback (s : Section F) :
    s.IsHolomorphic F ↔ ContDiff ℂ ω (s.pullback F) := by
  constructor
  · exact s.pullback_contDiff F
  · intro hs
    have h := sectionOfAutomorphic_holomorphic F
      (s.pullback F) (s.pullback_automorphic F) hs
    simpa only [sectionOfAutomorphic_section_pullback] using h

/-- Actual entire analytic functions satisfying the specified transformation law. -/
def EntireThetaFunction :=
  {f : ComplexPlane₂ → ℂ // ContDiff ℂ ω f ∧ IsAutomorphic F f}

/-- The proved correspondence between genuine holomorphic sections and entire theta functions. -/
def holomorphicSectionEquivTheta :
    {s : Section F // s.IsHolomorphic F} ≃ EntireThetaFunction F where
  toFun s := ⟨s.val.pullback F, s.val.pullback_contDiff F s.property,
    s.val.pullback_automorphic F⟩
  invFun f := ⟨sectionOfAutomorphic F f.val f.property.2,
    sectionOfAutomorphic_holomorphic F f.val f.property.2 f.property.1⟩
  left_inv s := Subtype.ext (sectionOfAutomorphic_section_pullback F s.val)
  right_inv f := Subtype.ext (sectionOfAutomorphic_pullback F f.val f.property.2)

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert

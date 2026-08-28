import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedSections
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Analytic trivializations of the actual associated quotient

A trivialization is a genuine biholomorphism from `(A × ℂ)/G` to `B × ℂ`,
over the identity of `B`, linear in each fibre.  The trivial character gives
such a biholomorphism explicitly by `[a,z] ↦ (q a,z)`.  Its inverse is analytic
because locally it is obtained using an analytic inverse of the base covering.

Any analytic fibrewise-linear trivialization gives a genuine nowhere-zero
holomorphic section by pulling back the constant section `(b,1)`.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle

variable {G A B : Type*} [Group G] [MulAction G A]
  [TopologicalSpace A] [TopologicalSpace B]
  {q : A → B} (hq : IsQuotientCoveringMap q G)

/-- The explicit underlying equivalence for the trivial character. -/
def trivialCharacterEquiv : AssociatedSpace (A := A) (1 : G →* ℂˣ) ≃ B × ℂ where
  toFun := Quotient.lift (fun p : A × ℂ => (q p.1, p.2)) fun p r h => by
    obtain ⟨g, hg⟩ := h
    apply Prod.ext
    · exact (congrArg q (congrArg Prod.fst hg)).symm.trans (hq.map_smul g)
    · have hz := (congrArg Prod.snd hg).symm
      change p.2 = ((1 : G →* ℂˣ) g : ℂ) * r.2 at hz
      simpa using hz
  invFun p := associatedMap (1 : G →* ℂˣ)
    (CoveringQuotient.representative hq p.1, p.2)
  left_inv p := by
    obtain ⟨⟨a, z⟩, rfl⟩ := associatedMap_surjective (1 : G →* ℂˣ) p
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp
      (CoveringQuotient.project_representative hq (q a))
    apply (associatedMap_eq_iff (1 : G →* ℂˣ) _ _).mpr
    refine ⟨g, hg, ?_⟩
    change ((1 : G →* ℂˣ) g : ℂ) * z = z
    simp
  right_inv p := by
    change (q (CoveringQuotient.representative hq p.1), p.2) = p
    exact Prod.ext (CoveringQuotient.project_representative hq p.1) rfl

@[simp] theorem trivialCharacterEquiv_apply_associatedMap (a : A) (z : ℂ) :
    trivialCharacterEquiv hq (associatedMap (1 : G →* ℂˣ) (a, z)) = (q a, z) := rfl

@[simp] theorem trivialCharacterEquiv_symm_apply (p : B × ℂ) :
    (trivialCharacterEquiv hq).symm p = associatedMap (1 : G →* ℂˣ)
      (CoveringQuotient.representative hq p.1, p.2) := rfl

theorem trivialCharacterEquiv_fst (p : AssociatedSpace (A := A) (1 : G →* ℂˣ)) :
    (trivialCharacterEquiv hq p).1 = projection hq (1 : G →* ℂˣ) p := by
  obtain ⟨⟨a, z⟩, rfl⟩ := associatedMap_surjective (1 : G →* ℂˣ) p
  rfl

/-- The inverse can be computed using any lift, not only the selected one. -/
theorem trivialCharacterEquiv_symm_apply_of_project_eq (a : A) (b : B)
    (hab : q a = b) (z : ℂ) :
    (trivialCharacterEquiv hq).symm (b, z) = associatedMap (1 : G →* ℂˣ) (a, z) := by
  apply (trivialCharacterEquiv hq).injective
  rw [Equiv.apply_symm_apply, trivialCharacterEquiv_apply_associatedMap]
  exact Prod.ext hab.symm rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E A]

local notation "IA" => modelWithCornersSelf ℂ E
local notation "IL" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (E × ℂ)

/-- An actual biholomorphism in the independently constructed quotient atlases.
This abbreviation only installs those specified charts. -/
abbrev AssociatedDiffeomorph (χ : G →* ℂˣ) :=
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := associatedChartedSpace (E := E) hq χ
  letI : ChartedSpace (E × ℂ) (B × ℂ) :=
    inferInstanceAs (ChartedSpace (ModelProd E ℂ) (B × ℂ))
  Diffeomorph IP IP (AssociatedSpace (A := A) χ) (B × ℂ) ω

/-- A base-preserving, complex-fibrewise-linear analytic trivialization of
the actual associated quotient, rather than a criterion defining triviality. -/
structure AnalyticAssociatedTrivialization (χ : G →* ℂˣ) where
  toDiffeomorph : AssociatedDiffeomorph (E := E) hq χ
  map_fst : ∀ p, (toDiffeomorph p).1 = projection hq χ p
  map_add : ∀ a : A, ∀ z w : ℂ,
    (toDiffeomorph (associatedMap χ (a, z + w))).2 =
      (toDiffeomorph (associatedMap χ (a, z))).2 +
        (toDiffeomorph (associatedMap χ (a, w))).2
  map_smul : ∀ a : A, ∀ c z : ℂ,
    (toDiffeomorph (associatedMap χ (a, c • z))).2 =
      c • (toDiffeomorph (associatedMap χ (a, z))).2

namespace AnalyticAssociatedTrivialization

variable (χ : G →* ℂˣ) (e : AnalyticAssociatedTrivialization (E := E) hq χ)

theorem map_zero (a : A) :
    (e.toDiffeomorph (associatedMap χ (a, 0))).2 = 0 := by
  simpa only [zero_smul] using e.map_smul a 0 0

/-- Fibrewise linearity forces the actual zero section to be sent to zero. -/
theorem map_zeroSection (b : B) :
    e.toDiffeomorph (zeroSection hq χ b) = (b, 0) := by
  obtain ⟨a, rfl⟩ := hq.surjective b
  apply Prod.ext
  · rw [e.map_fst, Section.projection_apply]
  · rw [zeroSection_apply_project]
    exact e.map_zero hq χ a

/-- Pull back the constant unit section by the actual inverse biholomorphism. -/
def unitSection : Section hq χ := by
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := associatedChartedSpace (E := E) hq χ
  letI : ChartedSpace (E × ℂ) (B × ℂ) :=
    inferInstanceAs (ChartedSpace (ModelProd E ℂ) (B × ℂ))
  refine ⟨fun b => e.toDiffeomorph.symm (b, 1), fun b => ?_⟩
  have h := e.map_fst (e.toDiffeomorph.symm (b, 1))
  rw [e.toDiffeomorph.apply_symm_apply] at h
  exact h.symm

@[simp] theorem map_unitSection (b : B) :
    e.toDiffeomorph (e.unitSection hq χ b) = (b, 1) := by
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := associatedChartedSpace (E := E) hq χ
  letI : ChartedSpace (E × ℂ) (B × ℂ) :=
    inferInstanceAs (ChartedSpace (ModelProd E ℂ) (B × ℂ))
  exact e.toDiffeomorph.apply_symm_apply (b, 1)

theorem unitSection_nowhereZero : (e.unitSection hq χ).NowhereZero hq χ := by
  intro b hb
  have h := congrArg e.toDiffeomorph hb
  rw [e.map_unitSection, e.map_zeroSection] at h
  exact one_ne_zero (congrArg Prod.snd h)

theorem unitSection_isHolomorphic :
    (e.unitSection hq χ).IsHolomorphic (E := E) hq χ := by
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := associatedChartedSpace (E := E) hq χ
  letI : ChartedSpace (E × ℂ) (B × ℂ) :=
    inferInstanceAs (ChartedSpace (ModelProd E ℂ) (B × ℂ))
  change ContMDiff IA IP ω (fun b : B => e.toDiffeomorph.symm (b, 1))
  apply e.toDiffeomorph.contMDiff_invFun.comp
  rw [modelWithCornersSelf_prod]
  exact contMDiff_id.prodMk contMDiff_const

end AnalyticAssociatedTrivialization

section TrivialCharacter

local instance trivialSourceProductChartedSpace : ChartedSpace (E × ℂ) (A × ℂ) :=
  inferInstanceAs (ChartedSpace (ModelProd E ℂ) (A × ℂ))

variable [IsManifold (modelWithCornersSelf ℂ E) ω A]
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (fun a : A => g • a))

local instance trivialSourceProductManifold : IsManifold IP ω (A × ℂ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := IA) (I' := IL) A ℂ

include hG

theorem trivialCharacterEquiv_holomorphic :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    letI := associatedChartedSpace (E := E) hq (1 : G →* ℂˣ)
    letI : ChartedSpace (E × ℂ) (B × ℂ) :=
      inferInstanceAs (ChartedSpace (ModelProd E ℂ) (B × ℂ))
    ContMDiff IP IP ω (trivialCharacterEquiv hq) := by
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := associatedChartedSpace (E := E) hq (1 : G →* ℂˣ)
  letI : ChartedSpace (E × ℂ) (B × ℂ) :=
    inferInstanceAs (ChartedSpace (ModelProd E ℂ) (B × ℂ))
  letI := diagonalAction (A := A) (1 : G →* ℂˣ)
  apply CoveringQuotient.contMDiff_of_comp
    (associatedMap_isQuotientCoveringMap hq (1 : G →* ℂˣ)) IP ω
  change ContMDiff IP IP ω (fun p : A × ℂ => (q p.1, p.2))
  rw [modelWithCornersSelf_prod]
  exact ((CoveringQuotient.contMDiff_project hq ω hG).comp contMDiff_fst).prodMk
    contMDiff_snd

/-- The selected representative need not depend continuously on the base:
locally the inverse equals the quotient of an analytic covering lift. -/
theorem trivialCharacterEquiv_symm_holomorphic :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    letI := associatedChartedSpace (E := E) hq (1 : G →* ℂˣ)
    letI : ChartedSpace (E × ℂ) (B × ℂ) :=
      inferInstanceAs (ChartedSpace (ModelProd E ℂ) (B × ℂ))
    ContMDiff IP IP ω (trivialCharacterEquiv hq).symm := by
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := associatedChartedSpace (E := E) hq (1 : G →* ℂˣ)
  letI : ChartedSpace (E × ℂ) (B × ℂ) :=
    inferInstanceAs (ChartedSpace (ModelProd E ℂ) (B × ℂ))
  intro p
  let a := CoveringQuotient.representative hq p.1
  let L := CoveringQuotient.localInverse hq a
  have hp : p.1 ∈ L.source := by
    have h := hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
      (x := a)
    change q a ∈ L.source at h
    simpa only [a, CoveringQuotient.project_representative] using h
  have hL : ContMDiffAt IA IA ω L p.1 :=
    (CoveringQuotient.localInverse_holomorphic hq ω hG a).contMDiffAt
      (L.open_source.mem_nhds hp)
  have hlocal : ContMDiffAt IP IP ω
      (fun r : B × ℂ => associatedMap (1 : G →* ℂˣ) (L r.1, r.2)) p := by
    apply (associatedMap_holomorphic hq (1 : G →* ℂˣ) hG).contMDiffAt.comp
    rw [modelWithCornersSelf_prod]
    exact (hL.comp p contMDiffAt_fst).prodMk contMDiffAt_snd
  apply hlocal.congr_of_eventuallyEq
  have hsource : ∀ᶠ r : B × ℂ in 𝓝 p, r.1 ∈ L.source :=
    continuous_fst.continuousAt (L.open_source.mem_nhds hp)
  filter_upwards [hsource] with r hr
  exact trivialCharacterEquiv_symm_apply_of_project_eq hq (L r.1) r.1
    (CoveringQuotient.project_localInverse hq a hr) r.2

/-- The explicit genuine biholomorphism trivializing the associated quotient
of the trivial character. -/
def trivialCharacterDiffeomorph : AssociatedDiffeomorph (E := E) hq (1 : G →* ℂˣ) := by
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := associatedChartedSpace (E := E) hq (1 : G →* ℂˣ)
  letI : ChartedSpace (E × ℂ) (B × ℂ) :=
    inferInstanceAs (ChartedSpace (ModelProd E ℂ) (B × ℂ))
  exact
    { toEquiv := trivialCharacterEquiv hq
      contMDiff_toFun := trivialCharacterEquiv_holomorphic hq hG
      contMDiff_invFun := trivialCharacterEquiv_symm_holomorphic hq hG }

@[simp] theorem trivialCharacterDiffeomorph_apply_associatedMap (a : A) (z : ℂ) :
    trivialCharacterDiffeomorph hq hG (associatedMap (1 : G →* ℂˣ) (a, z)) = (q a, z) := rfl

/-- The trivial character has an actual analytic linear bundle trivialization. -/
def trivialCharacterTrivialization :
    AnalyticAssociatedTrivialization (E := E) hq (1 : G →* ℂˣ) where
  toDiffeomorph := trivialCharacterDiffeomorph hq hG
  map_fst := trivialCharacterEquiv_fst hq
  map_add _ _ _ := rfl
  map_smul _ _ _ := rfl

end TrivialCharacter

end Wikipedia.HopfProblem.HolomorphicCharacterBundle

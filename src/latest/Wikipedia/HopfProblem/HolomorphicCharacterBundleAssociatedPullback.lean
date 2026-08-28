import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedSections

/-!
# Holomorphic pullback and the character obstruction for actual sections

The scalar coordinate of a holomorphic section is holomorphic: locally lift
the section through the diagonal covering and use uniqueness of local lifts
for its first coordinate. Compact complex-manifold constancy can therefore
be applied to genuine sections of the associated quotient.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle

variable {G A B E : Type*} [Group G] [MulAction G A]
  [TopologicalSpace A] [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E A]
  {q : A → B} (hq : IsQuotientCoveringMap q G) (χ : G →* ℂˣ)
  [IsManifold (modelWithCornersSelf ℂ E) ω A]
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (fun a : A => g • a))

local notation "IA" => modelWithCornersSelf ℂ E
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ (E × ℂ)

local instance associatedPullbackProductChartedSpace : ChartedSpace (E × ℂ) (A × ℂ) :=
  inferInstanceAs (ChartedSpace (ModelProd E ℂ) (A × ℂ))

include hG

theorem Section.pullback_holomorphic (s : Section hq χ)
    (hs : s.IsHolomorphic (E := E) hq χ) :
    ContMDiff IA I₁ ω (s.pullback hq χ) := by
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := associatedChartedSpace (E := E) hq χ
  letI := diagonalAction (A := A) χ
  have hs' : ContMDiff IA I₂ ω (fun a => s (q a)) :=
    hs.comp (CoveringQuotient.contMDiff_project hq ω hG)
  intro a
  let p : A × ℂ := (a, s.pullback hq χ a)
  let hP := associatedMap_isQuotientCoveringMap hq χ
  let e := CoveringQuotient.localInverse hP p
  let l : A → A × ℂ := fun y => e (s (q y))
  have hpa : associatedMap χ p = s (q a) := s.associatedMap_pullback hq χ a
  have hsrc : s (q a) ∈ e.source := by
    rw [← hpa]
    exact hP.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
  have hl : ContMDiffAt IA I₂ ω l a :=
    ((associatedLocalInverse_holomorphic hq χ hG p).contMDiffAt
      (e.open_source.mem_nhds hsrc)).comp a hs'.contMDiffAt
  have hla : l a = p := by
    change e (s (q a)) = p
    rw [← hpa]
    exact hP.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self
  have hsource : ∀ᶠ y in 𝓝 a, s (q y) ∈ e.source :=
    hs'.continuous.continuousAt (e.open_source.mem_nhds hsrc)
  have hfirst : (fun y => (l y).1) =ᶠ[𝓝 a] (fun y => y) := by
    apply eventuallyEq_of_localHomeomorph_comp_eq hq.isCoveringMap.isLocalHomeomorph
      (continuous_fst.continuousAt.comp hl.continuousAt) continuousAt_id
      (congrArg Prod.fst hla)
    filter_upwards [hsource] with y hy
    calc
      q (l y).1 = projection hq χ (associatedMap χ (l y)) := rfl
      _ = projection hq χ (s (q y)) := congrArg (projection hq χ)
        (CoveringQuotient.project_localInverse hP p hy)
      _ = q y := s.projection_apply hq χ (q y)
  have heq : s.pullback hq χ =ᶠ[𝓝 a] (fun y => (l y).2) := by
    filter_upwards [hsource, hfirst] with y hy hfy
    apply associatedMap_fibre_injective hq χ y
    calc
      associatedMap χ (y, s.pullback hq χ y) = s (q y) :=
        s.associatedMap_pullback hq χ y
      _ = associatedMap χ (l y) :=
        (CoveringQuotient.project_localInverse hP p hy).symm
      _ = associatedMap χ (y, (l y).2) :=
        congrArg (associatedMap χ) (Prod.ext hfy rfl)
  have hl' : ContMDiffAt IA ((IA).prod I₁) ω l a := by
    rwa [← modelWithCornersSelf_prod]
  exact (contMDiffAt_snd.comp a hl').congr_of_eventuallyEq heq

theorem Section.isHolomorphic_iff_pullback (s : Section hq χ) :
    s.IsHolomorphic (E := E) hq χ ↔ ContMDiff IA I₁ ω (s.pullback hq χ) := by
  constructor
  · exact s.pullback_holomorphic hq χ hG
  · intro hs
    have h := sectionOfEquivariant_holomorphic hq χ hG
      (s.pullback hq χ) (s.pullback_equivariant hq χ) hs
    simpa only [sectionOfEquivariant_section_pullback] using h

variable [CompactSpace A] [ConnectedSpace A]

/-- The obstruction applies to actual nowhere-zero holomorphic sections of
the quotient line bundle, not just to an abstract equivariance condition. -/
theorem exists_holomorphic_nowhereZero_section_iff_character_eq_one :
    (∃ s : Section hq χ, s.IsHolomorphic (E := E) hq χ ∧ s.NowhereZero hq χ) ↔ χ = 1 := by
  constructor
  · rintro ⟨s, hs, hn⟩
    apply character_eq_one_of_equivariant_holomorphic_nonzero
      (s.pullback_holomorphic hq χ hG hs) (s.pullback_equivariant hq χ)
    exact ⟨Classical.arbitrary A, (s.nowhereZero_iff_pullback hq χ).mp hn _⟩
  · rintro rfl
    have he : IsCharacterEquivariant (1 : G →* ℂˣ) (fun _ : A => (1 : ℂ)) := by
      intro g a
      simp
    refine ⟨sectionOfEquivariant hq 1 (fun _ => 1) he,
      sectionOfEquivariant_holomorphic hq 1 hG _ _ contMDiff_const, ?_⟩
    apply (Section.nowhereZero_iff_pullback hq 1 _).mpr
    intro a
    simpa only [sectionOfEquivariant_pullback] using (one_ne_zero : (1 : ℂ) ≠ 0)

/-- For a nontrivial character there is not even a nonzero holomorphic section. -/
theorem Section.eq_zero_of_holomorphic_of_character_ne_one (s : Section hq χ)
    (hs : s.IsHolomorphic (E := E) hq χ) (hχ : χ ≠ 1) : s = zeroSection hq χ := by
  have hz := equivariant_holomorphic_eq_zero_of_character_ne_one hχ
    (s.pullback_holomorphic hq χ hG hs) (s.pullback_equivariant hq χ)
  apply Section.ext
  intro b
  obtain ⟨a, rfl⟩ := hq.surjective b
  rw [← s.associatedMap_pullback hq χ a, zeroSection_apply_project]
  exact congrArg (fun z => associatedMap χ (a, z)) (congrFun hz a)

end Wikipedia.HopfProblem.HolomorphicCharacterBundle

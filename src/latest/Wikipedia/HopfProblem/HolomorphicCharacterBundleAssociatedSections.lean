import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedAnalytic
import Wikipedia.HopfProblem.HolomorphicCharacterBundleObstruction

/-!
# Sections of the associated quotient

A section here is a genuine right inverse to the projection of the associated
quotient. Its pullback has a unique scalar coordinate on `A`, and this coordinate
transforms by the character. The correspondence is proved, not taken as the
definition of a section or of bundle triviality.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle

variable {G A B : Type*} [Group G] [MulAction G A]
  [TopologicalSpace A] [TopologicalSpace B]
  {q : A → B} (hq : IsQuotientCoveringMap q G) (χ : G →* ℂˣ)

/-- An actual section of the associated quotient projection. -/
structure Section where
  toFun : B → AssociatedSpace (A := A) χ
  projection_toFun : ∀ b, projection hq χ (toFun b) = b

instance : CoeFun (Section hq χ) (fun _ => B → AssociatedSpace (A := A) χ) := ⟨Section.toFun⟩

@[simp] theorem Section.projection_apply (s : Section hq χ) (b : B) :
    projection hq χ (s b) = b := s.projection_toFun b

@[ext] theorem Section.ext {s t : Section hq χ} (h : ∀ b, s b = t b) : s = t := by
  cases s with
  | mk f hf =>
    cases t with
    | mk g hg =>
      have he : f = g := funext h
      subst g
      rfl

/-- The unique scalar function obtained by pulling a section back to `A`. -/
def Section.pullback (s : Section hq χ) (a : A) : ℂ :=
  fibreCoordinate hq χ a (s (q a)) (s.projection_apply hq χ (q a))

@[simp] theorem Section.associatedMap_pullback (s : Section hq χ) (a : A) :
    associatedMap χ (a, s.pullback hq χ a) = s (q a) :=
  associatedMap_fibreCoordinate hq χ a (s (q a)) _

theorem Section.pullback_equivariant (s : Section hq χ) :
    IsCharacterEquivariant χ (s.pullback hq χ) := by
  intro g a
  apply associatedMap_fibre_injective hq χ (g • a)
  dsimp only
  rw [s.associatedMap_pullback, hq.map_smul g,
    associatedMap_diagonal χ g (a, s.pullback hq χ a),
    s.associatedMap_pullback]

/-- An equivariant scalar function descends to a genuine section. -/
def sectionOfEquivariant (f : A → ℂ) (_hf : IsCharacterEquivariant χ f) : Section hq χ where
  toFun b := associatedMap χ
    (CoveringQuotient.representative hq b, f (CoveringQuotient.representative hq b))
  projection_toFun b := CoveringQuotient.project_representative hq b

theorem sectionOfEquivariant_apply_project (f : A → ℂ) (hf : IsCharacterEquivariant χ f)
    (a : A) : sectionOfEquivariant hq χ f hf (q a) = associatedMap χ (a, f a) := by
  obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp
    (CoveringQuotient.project_representative hq (q a))
  apply (associatedMap_eq_iff χ _ _).mpr
  exact ⟨g, hg, (hf g a).symm.trans (congrArg f hg)⟩

@[simp] theorem sectionOfEquivariant_pullback (f : A → ℂ)
    (hf : IsCharacterEquivariant χ f) :
    (sectionOfEquivariant hq χ f hf).pullback hq χ = f := by
  funext a
  apply associatedMap_fibre_injective hq χ a
  dsimp only
  rw [Section.associatedMap_pullback, sectionOfEquivariant_apply_project]

@[simp] theorem sectionOfEquivariant_section_pullback (s : Section hq χ) :
    sectionOfEquivariant hq χ (s.pullback hq χ) (s.pullback_equivariant hq χ) = s := by
  apply Section.ext
  intro b
  obtain ⟨a, rfl⟩ := hq.surjective b
  rw [sectionOfEquivariant_apply_project, Section.associatedMap_pullback]

def zeroSection : Section hq χ :=
  sectionOfEquivariant hq χ (fun _ => 0) (fun _ _ => by simp)

@[simp] theorem zeroSection_apply_project (a : A) :
    zeroSection hq χ (q a) = associatedMap χ (a, 0) :=
  sectionOfEquivariant_apply_project hq χ _ _ a

@[simp] theorem zeroSection_pullback : (zeroSection hq χ).pullback hq χ = 0 :=
  sectionOfEquivariant_pullback hq χ _ _

/-- Nonvanishing is a property of the actual section in each quotient fibre. -/
def Section.NowhereZero (s : Section hq χ) : Prop :=
  ∀ b, s b ≠ zeroSection hq χ b

theorem Section.nowhereZero_iff_pullback (s : Section hq χ) :
    s.NowhereZero hq χ ↔ ∀ a, s.pullback hq χ a ≠ 0 := by
  constructor
  · intro hs a ha
    apply hs (q a)
    rw [← s.associatedMap_pullback hq χ a, zeroSection_apply_project, ha]
  · intro hs b hb
    obtain ⟨a, rfl⟩ := hq.surjective b
    apply hs a
    apply associatedMap_fibre_injective hq χ a
    dsimp only
    rw [s.associatedMap_pullback, hb, zeroSection_apply_project]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E A]

local notation "IA" => modelWithCornersSelf ℂ E
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ (E × ℂ)

local instance associatedSectionProductChartedSpace : ChartedSpace (E × ℂ) (A × ℂ) :=
  inferInstanceAs (ChartedSpace (ModelProd E ℂ) (A × ℂ))

/-- Analyticity in the actual quotient atlases. -/
def Section.IsHolomorphic (s : Section hq χ) : Prop :=
  letI := CoveringQuotient.chartedSpace (E := E) hq
  letI := associatedChartedSpace (E := E) hq χ
  ContMDiff IA I₂ ω (s : B → AssociatedSpace (A := A) χ)

variable [IsManifold (modelWithCornersSelf ℂ E) ω A]
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (fun a : A => g • a))

include hG

theorem sectionOfEquivariant_holomorphic (f : A → ℂ) (hf : IsCharacterEquivariant χ f)
    (hfhol : ContMDiff IA I₁ ω f) :
    (sectionOfEquivariant hq χ f hf).IsHolomorphic (E := E) hq χ := by
  letI := associatedChartedSpace (E := E) hq χ
  apply CoveringQuotient.contMDiff_of_comp hq I₂ ω
  have he : ((sectionOfEquivariant hq χ f hf : B → AssociatedSpace (A := A) χ) ∘ q) =
      fun a => associatedMap χ (a, f a) := by
    funext a
    exact sectionOfEquivariant_apply_project hq χ f hf a
  rw [he]
  apply (associatedMap_holomorphic hq χ hG).comp
  rw [modelWithCornersSelf_prod]
  exact contMDiff_id.prodMk hfhol

theorem zeroSection_holomorphic :
    (zeroSection hq χ).IsHolomorphic (E := E) hq χ :=
  sectionOfEquivariant_holomorphic hq χ hG _ _ contMDiff_const

end Wikipedia.HopfProblem.HolomorphicCharacterBundle

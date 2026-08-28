import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionMap
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardGlobal

/-!
# Literal restriction of Čech cocycles and extension data

For an actual continuous map and an actual coefficient map into its
pushforward, pull back the original cover and apply the coefficient map
to every cocycle value. The same coordinatewise operation preserves
the original lifted integer in the concrete extension presheaf.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechFibre

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open CuspNormalization.SheafCohomologyFinitePushforward

variable {T X : TopCat.{0}} (f : T ⟶ X)
  {F : AbelianSheaf X} {G : AbelianSheaf T}
  (κ : F ⟶ (pushforward f).obj G) {ι : Type} {U : ι → Opens X}

/-- The literal inverse images of the original covering opens. -/
abbrev pullbackCover (U : ι → Opens X) : ι → Opens T :=
  fun j => (Opens.map f).obj (U j)

/-- A covering of the target pulls back to a covering of the source. -/
theorem pullbackCover_covers (hU : ∀ x : X, ∃ j : ι, x ∈ U j) :
    ∀ t : T, ∃ j : ι, t ∈ pullbackCover f U j :=
  fun t => hU (f t)

/-- The original coefficient morphism on the literal pullback cover. -/
def pullbackCocycle (c : CechOneCocycle F U) :
    CechOneCocycle G (pullbackCover f U) where
  value j k := κ.hom.app (op (U j ⊓ U k)) (c.value j k)
  condition j k l := (HolomorphicPicard.Cech.mapCocycle κ c).condition j k l

@[simp] theorem pullbackCocycle_value (c : CechOneCocycle F U) (j k : ι) :
    (pullbackCocycle f κ c).value j k =
      κ.hom.app (op (U j ⊓ U k)) (c.value j k) := rfl

/-- Apply the actual coefficient maps to the compatible local data,
without changing their original lifted integer coordinate. -/
def pullbackSectionHom (c : CechOneCocycle F U) (V : Opens X) :
    ExtensionSection c V →+
      ExtensionSection (pullbackCocycle f κ c) ((Opens.map f).obj V) :=
  mapSectionHom κ c V

@[simp] theorem pullbackSectionHom_degree (c : CechOneCocycle F U)
    (V : Opens X) (s : ExtensionSection c V) :
    degreeHom (pullbackCocycle f κ c) ((Opens.map f).obj V)
        (pullbackSectionHom f κ c V s) = degreeHom c V s := rfl

@[simp] theorem pullbackSectionHom_coordinate (c : CechOneCocycle F U)
    (V : Opens X) (j : ι) (s : ExtensionSection c V) :
    coordinateHom (pullbackCocycle f κ c) ((Opens.map f).obj V) j
        (pullbackSectionHom f κ c V s) =
      κ.hom.app (op (V ⊓ U j)) (coordinateHom c V j s) := rfl

/-- The original extension restrictions commute with coordinatewise
restriction to the source space. -/
theorem restrict_pullbackSectionHom (c : CechOneCocycle F U)
    {V W : Opens X} (hWV : W ≤ V) (s : ExtensionSection c V) :
    restrict (pullbackCocycle f κ c) (fun _ hx => hWV hx)
        (pullbackSectionHom f κ c V s) =
      pullbackSectionHom f κ c W (restrict c hWV s) := by
  apply extensionSection_ext
  · rfl
  · intro j
    exact res_map κ (inf_le_inf_right (U j) hWV) (s.1.2 j)

/-- Degree-zero data are carried by the actual coefficient map. -/
@[simp] theorem pullbackSectionHom_includeHom (c : CechOneCocycle F U)
    (V : Opens X) (a : Section F V) :
    pullbackSectionHom f κ c V (includeHom c V a) =
      includeHom (pullbackCocycle f κ c) ((Opens.map f).obj V)
        (κ.hom.app (op V) a) := by
  apply extensionSection_ext
  · rfl
  · intro j
    exact (res_map κ inf_le_left a).symm

/-- The genuine presheaf map into the pushed-forward extension data. -/
def pullbackPre (c : CechOneCocycle F U) :
    presheaf c ⟶ (Opens.map f).op ⋙ presheaf (pullbackCocycle f κ c) where
  app V := AddCommGrpCat.ofHom (pullbackSectionHom f κ c V.unop)
  naturality V W h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (restrict_pullbackSectionHom f κ c (leOfHom h.unop) s).symm

@[simp] theorem pullbackPre_app (c : CechOneCocycle F U)
    (V : Opens X) (s : ExtensionSection c V) :
    (pullbackPre f κ c).app (op V) s = pullbackSectionHom f κ c V s := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechFibre

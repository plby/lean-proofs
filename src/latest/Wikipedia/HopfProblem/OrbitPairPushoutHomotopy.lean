import Wikipedia.HopfProblem.OrbitPairInitialFaceRetraction
import Mathlib.Topology.Homotopy.Basic

/-!
# Gluing continuous homotopies through an actual topological pushout

Currying into the compact-open path space makes the gluing a direct use
of the pushout universal property. Evaluation is continuous because the
unit interval is locally compact. Thus no unjustified assertion that an
arbitrary product of quotient maps is a quotient map is needed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.PushoutHomotopy

def paths {A Z : TopCat.{u}} {F₀ F₁ : A ⟶ Z} (H : F₀.hom.Homotopy F₁.hom) :
    A ⟶ TopCat.of C(I, Z) :=
  TopCat.ofHom (H.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry

variable {S A B P Z : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B} {i : A ⟶ P} {j : B ⟶ P}
    (hP : IsPushout f g i j) {F₀ F₁ : P ⟶ Z}
    (H₁ : (i ≫ F₀).hom.Homotopy (i ≫ F₁).hom)
    (H₂ : (j ≫ F₀).hom.Homotopy (j ≫ F₁).hom)
    (hc : ∀ (t : I) (s : S), H₁ (t, f s) = H₂ (t, g s))

include hc in
theorem paths_compatible : f ≫ paths H₁ = g ≫ paths H₂ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro s
  apply ContinuousMap.ext
  intro t
  exact hc t s

def gluedPaths : P ⟶ TopCat.of C(I, Z) :=
  hP.desc (paths H₁) (paths H₂) (paths_compatible H₁ H₂ hc)

theorem gluedPaths_inl (t : I) (a : A) : gluedPaths hP H₁ H₂ hc (i a) t = H₁ (t, a) :=
  congrArg (fun F ↦ F a t) (hP.inl_desc (paths H₁) (paths H₂) (paths_compatible H₁ H₂ hc))

theorem gluedPaths_inr (t : I) (b : B) : gluedPaths hP H₁ H₂ hc (j b) t = H₂ (t, b) :=
  congrArg (fun F ↦ F b t) (hP.inr_desc (paths H₁) (paths H₂) (paths_compatible H₁ H₂ hc))

def glue : F₀.hom.Homotopy F₁.hom where
  toContinuousMap := (gluedPaths hP H₁ H₂ hc).hom.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  map_zero_left p := by
    obtain (⟨a, rfl⟩ | ⟨b, rfl⟩) :=
      Types.eq_or_eq_of_isPushout (hP.map (forget TopCat)) p
    · exact (gluedPaths_inl hP H₁ H₂ hc 0 a).trans (H₁.map_zero_left a)
    · exact (gluedPaths_inr hP H₁ H₂ hc 0 b).trans (H₂.map_zero_left b)
  map_one_left p := by
    obtain (⟨a, rfl⟩ | ⟨b, rfl⟩) :=
      Types.eq_or_eq_of_isPushout (hP.map (forget TopCat)) p
    · exact (gluedPaths_inl hP H₁ H₂ hc 1 a).trans (H₁.map_one_left a)
    · exact (gluedPaths_inr hP H₁ H₂ hc 1 b).trans (H₂.map_one_left b)

theorem glue_inl (t : I) (a : A) : glue hP H₁ H₂ hc (t, i a) = H₁ (t, a) :=
  gluedPaths_inl hP H₁ H₂ hc t a

theorem glue_inr (t : I) (b : B) : glue hP H₁ H₂ hc (t, j b) = H₂ (t, b) :=
  gluedPaths_inr hP H₁ H₂ hc t b

end Wikipedia.HopfProblem.OrbitPair.PushoutHomotopy

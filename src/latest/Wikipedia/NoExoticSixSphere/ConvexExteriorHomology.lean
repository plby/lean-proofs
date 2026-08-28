import Wikipedia.NoExoticSixSphere.ConvexExteriorHomotopy
import Wikipedia.NoExoticSixSphere.EnclosingSphereShift
import Mathlib.Algebra.Homology.QuasiIso

/-!
# The original convex-complement inclusion is a homology equivalence

The enclosing-sphere deformation and the actual point-shift homotopy
identify the original map from the complement of the convex support to
the complement of any of its points. This retains the actual inclusion
and works in every degree.
-/

noncomputable section

open CategoryTheory Metric
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare

namespace NoExoticSixSphere.ConvexExterior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem exterior_ne_point (K : Set E) (x : E) (hx : x ∈ K) (y : Space K) : (y : E) ≠ x := by
  intro h
  exact y.property (h.symm ▸ hx)

def toPointPuncture (K : Set E) (x : E) (hx : x ∈ K) : C(Space K, ({x}ᶜ : Set E)) :=
  ⟨fun y => ⟨y.1, exterior_ne_point K x hx y⟩, continuous_subtype_val.subtype_mk _⟩

theorem enclosingSphere_puncture_translate (K : Set E) (r : ℝ) (hr : 0 < r)
    (hB : ∀ y ∈ K, ‖y‖ < r) (x : E) (hx : x ∈ K) :
    (BallExterior.puncturedTranslate x : C(({x}ᶜ : Set E), PuncturedRadial.Space E)).comp
        ((toPointPuncture K x hx).comp (fromSphere K r hr hB)) =
      BallExterior.shiftedSphereMap r hr x (hB x hx) := rfl

end NoExoticSixSphere.ConvexExterior

namespace NoExoticSixSphere.ConvexExterior

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bijectivity concerns the actual complement-to-point inclusion on native integral homology. -/
theorem toPointPuncture_homology_bijective (K : Set E) (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (r : ℝ) (hr : 0 < r) (hB : ∀ y ∈ K, ‖y‖ < r) (x : E) (hx : x ∈ K) (n : ℕ) :
    Function.Bijective (singularHomologyMap (toPointPuncture K x hx) n) := by
  let s := singularHomologyMap (fromSphere K r hr hB) n
  let f := singularHomologyMap (toPointPuncture K x hx) n
  let g := singularHomologyMap
    (BallExterior.puncturedTranslate x : C(({x}ᶜ : Set E), PuncturedRadial.Space E)) n
  have hs : Function.Bijective s :=
    (homotopyEquivHomologyEquiv (sphereHomotopyEquiv K hK h0 r hr hB) n).bijective
  have hg : Function.Bijective g :=
    (homeomorphHomologyEquiv (BallExterior.puncturedTranslate x) n).bijective
  have he := congrArg (fun k => singularHomologyMap k n)
    (enclosingSphere_puncture_translate K r hr hB x hx)
  simp only [singularHomologyMap_comp] at he
  have hc : Function.Bijective (g.comp (f.comp s)) := by
    rw [show g.comp (f.comp s) = _ from he]
    exact BallExterior.shiftedSphereMap_homology_bijective r hr x (hB x hx) n
  constructor
  · intro a b hab
    obtain ⟨u, rfl⟩ := hs.surjective a
    obtain ⟨v, rfl⟩ := hs.surjective b
    exact congrArg s (hc.injective (congrArg g hab))
  · intro y
    obtain ⟨u, hu⟩ := hc.surjective (g y)
    exact ⟨s u, hg.injective hu⟩

theorem toPointPuncture_quasiIso (K : Set E) (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (r : ℝ) (hr : 0 < r) (hB : ∀ y ∈ K, ‖y‖ < r) (x : E) (hx : x ∈ K) :
    QuasiIso (singularChainMap (toPointPuncture K x hx)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (toPointPuncture_homology_bijective K hK h0 r hr hB x hx n)

end NoExoticSixSphere.ConvexExterior

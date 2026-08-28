import Wikipedia.NoExoticSixSphere.EnclosingSphereShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The exterior-to-puncture inclusion is an actual homology equivalence

The enclosing-sphere deformation and the point-shift homotopy prove this
for the original inclusion at every point of the closed ball, including
its boundary. The result holds in every degree and does not assume an
excision or duality statement for the closed support.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare

namespace NoExoticSixSphere.BallExterior

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The literal exterior inclusion induces a bijection on each actual integral homology group. -/
theorem toPointPuncture_homology_bijective (R : ℝ) (hR : 0 ≤ R)
    (x : E) (hx : ‖x‖ ≤ R) (n : ℕ) :
    Function.Bijective (singularHomologyMap (toPointPuncture R x hx) n) := by
  let r := R + 1
  have hr : R < r := lt_add_one R
  let s := singularHomologyMap (fromSphere (E := E) R hR r hr) n
  let f := singularHomologyMap (toPointPuncture R x hx) n
  let g := singularHomologyMap
    (puncturedTranslate x : C(({x}ᶜ : Set E), PuncturedRadial.Space E)) n
  have hs : Function.Bijective s :=
    (homotopyEquivHomologyEquiv (sphereHomotopyEquiv (E := E) R hR r hr) n).bijective
  have hg : Function.Bijective g := (homeomorphHomologyEquiv (puncturedTranslate x) n).bijective
  have he := congrArg (fun k => singularHomologyMap k n)
    (enclosingSphere_puncture_translate R hR r hr x hx)
  simp only [singularHomologyMap_comp] at he
  have hcomp : Function.Bijective (g.comp (f.comp s)) := by
    rw [show g.comp (f.comp s) = _ from he]
    exact shiftedSphereMap_homology_bijective r (radius_pos R hR r hr) x (hx.trans_lt hr) n
  constructor
  · intro a b hab
    obtain ⟨u, rfl⟩ := hs.surjective a
    obtain ⟨v, rfl⟩ := hs.surjective b
    exact congrArg s (hcomp.injective (congrArg g hab))
  · intro y
    obtain ⟨u, hu⟩ := hcomp.surjective (g y)
    exact ⟨s u, hg.injective hu⟩

/-- The actual singular-chain map of this inclusion is a quasi-isomorphism. -/
theorem toPointPuncture_quasiIso (R : ℝ) (hR : 0 ≤ R) (x : E) (hx : ‖x‖ ≤ R) :
    QuasiIso (singularChainMap (toPointPuncture R x hx)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (toPointPuncture_homology_bijective R hR x hx n)

end NoExoticSixSphere.BallExterior

import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Constancy through a compact connected holomorphic parametrization

A holomorphic function on an ambient open set is constant on the image
of any compact connected complex manifold mapped holomorphically into
that open set. This also applies to singular images: the image need not
itself be a manifold.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem

variable {E F H K X T : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace K]
  {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ F K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace T] [ChartedSpace K T] [IsManifold J ω T]
  [CompactSpace T] [ConnectedSpace T]

theorem holomorphic_apply_eq_of_compact_parametrization (U : Opens X) (f : U → ℂ)
    (hf : ContMDiff I 𝓘(ℂ) ω f) (g : T → X) (hg : ContMDiff J I ω g)
    (hU : ∀ t : T, g t ∈ U) (x y : U)
    (hx : (x : X) ∈ range g) (hy : (y : X) ∈ range g) : f x = f y := by
  let G : T → U := fun t => ⟨g t, hU t⟩
  have hG : ContMDiff J I ∞ G :=
    (ContMDiff.subtypeVal_comp_iff U G).mp (hg.of_le le_top)
  have hFG : ContMDiff J 𝓘(ℂ) ∞ (f ∘ G) := (hf.of_le le_top).comp hG
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have ha' : G a = x := Subtype.ext ha
  have hb' : G b = y := Subtype.ext hb
  have hconst : f (G a) = f (G b) :=
    (hFG.mdifferentiable (by simp)).apply_eq_of_compactSpace a b
  simpa only [ha', hb'] using hconst

end Wikipedia.HopfProblem

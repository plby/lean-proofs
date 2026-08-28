import Wikipedia.SmoothSixDPoincare.SmoothHomotopyCollars
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# A globally smooth real curve joining the endpoints of a continuous path

Smooth the path as a homotopy between maps from a point, then compose with
a globally smooth time map into the interval. This constructs an actual
smooth map on the whole real line with the original two endpoint values.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.CurveImmersion

def smoothTime (t : ℝ) : unitInterval :=
  projIcc 0 1 zero_le_one (Real.smoothTransition t)

theorem contMDiff_smoothTime : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ smoothTime := by
  let : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (projIcc (0 : ℝ) 1 zero_le_one) (Icc 0 1) :=
    contMDiffOn_projIcc
  have ht : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  apply contMDiffOn_univ.mp
  exact hp.comp ht.contMDiff.contMDiffOn
    (fun t _ => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩)

theorem smoothTime_zero : smoothTime 0 = 0 := by
  apply Subtype.ext
  simp [smoothTime]

theorem smoothTime_one : smoothTime 1 = 1 := by
  apply Subtype.ext
  simp [smoothTime]

end Wikipedia.SmoothSixDPoincare.CurveImmersion

namespace Wikipedia.SmoothSixDPoincare

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- Any continuous path gives an actual globally smooth real curve with the same endpoints. -/
theorem exists_smooth_connecting_curve {x y : N} (γ : Path x y) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧ f 0 = x ∧ f 1 = y := by
  let Z := EuclideanSpace ℝ (Fin 0)
  let f₀ : C(Z, N) := ContinuousMap.const Z x
  let f₁ : C(Z, N) := ContinuousMap.const Z y
  let H : f₀.Homotopy f₁ := {
    toFun := fun q => γ q.1
    continuous_toFun := γ.continuous.comp continuous_fst
    map_zero_left := fun _ => γ.source
    map_one_left := fun _ => γ.target }
  obtain ⟨H', hH', -, -⟩ := ManifoldSmoothing.exists_smooth_homotopy_with_collars
    (I := 𝓘(ℝ, Z)) (J := J) contMDiff_const contMDiff_const H
  let f : ℝ → N := fun t => H' (CurveImmersion.smoothTime t, (0 : Z))
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f :=
    hH'.comp (CurveImmersion.contMDiff_smoothTime.prodMk contMDiff_const)
  refine ⟨⟨f, hf.continuous⟩, hf, ?_, ?_⟩
  · change H' (CurveImmersion.smoothTime 0, (0 : Z)) = x
    rw [CurveImmersion.smoothTime_zero, H'.apply_zero]
    rfl
  · change H' (CurveImmersion.smoothTime 1, (0 : Z)) = y
    rw [CurveImmersion.smoothTime_one, H'.apply_one]
    rfl

end Wikipedia.SmoothSixDPoincare

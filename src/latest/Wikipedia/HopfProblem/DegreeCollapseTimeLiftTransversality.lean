import Wikipedia.HopfProblem.DegreeCollapseNativeTransversePostcomposition

/-!
# Lifting native level transversality by the flow-time direction

The free time parameter supplies the missing vertical tangent direction.
Arbitrary smooth phase functions do not affect surjectivity of the sum
of the two lifted tangent maps.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B Z : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def timeLiftLinear (L : A →L[ℝ] Z) (α : A →L[ℝ] ℝ) : (A × ℝ) →L[ℝ] (Z × ℝ) :=
  (L.comp (ContinuousLinearMap.fst ℝ A ℝ)).prod
    (ContinuousLinearMap.snd ℝ A ℝ + α.comp (ContinuousLinearMap.fst ℝ A ℝ))

theorem surjective_time_lift_coprod
    (L : A →L[ℝ] Z) (R : B →L[ℝ] Z) (α : A →L[ℝ] ℝ) (β : B →L[ℝ] ℝ)
    (h : Surjective (L.coprod R)) :
    Surjective ((timeLiftLinear L α).coprod (timeLiftLinear R β)) := by
  rintro ⟨z, t⟩
  obtain ⟨⟨a, b⟩, hab⟩ := h z
  refine ⟨((a, t - α a - β b), (b, 0)), ?_⟩
  apply Prod.ext
  · exact hab
  · change (t - α a - β b + α a) + (0 + β b) = t
    ring

variable {HA HB HZ X Y N : Type*}
  [TopologicalSpace HA] [TopologicalSpace HB] [TopologicalSpace HZ]
  {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB}
  {J : ModelWithCorners ℝ Z HZ}
  [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]
  [TopologicalSpace N] [ChartedSpace HZ N]

theorem native_time_lift_derivative
    {f : X → N} {v : X → ℝ} {x : X} (s : ℝ)
    (hf : MDifferentiableAt I J f x) (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x) :
    (mfderiv (I.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ))
      (fun p : X × ℝ => (f p.1, p.2 + v p.1)) (x, s) : (A × ℝ) →L[ℝ] (Z × ℝ)) =
      timeLiftLinear (A := A) (Z := Z) (mfderiv I J f x) (mvfderiv I v x) := by
  have hn := hf.hasMFDerivAt.comp (x, s)
    (hasMFDerivAt_fst (I := I) (I' := 𝓘(ℝ, ℝ)) (x, s))
  have hp := hv.hasMFDerivAt.comp (x, s)
    (hasMFDerivAt_fst (I := I) (I' := 𝓘(ℝ, ℝ)) (x, s))
  have ht := (hasMFDerivAt_snd (I := I) (I' := 𝓘(ℝ, ℝ)) (x, s)).add hp
  exact (hn.prodMk ht).mfderiv

theorem native_transversality_time_lifts
    {f : X → N} {g : Y → N} {v : X → ℝ} {w : Y → ℝ} {x : X} {y : Y}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt I' J g y)
    (hv : MDifferentiableAt I 𝓘(ℝ, ℝ) v x)
    (hw : MDifferentiableAt I' 𝓘(ℝ, ℝ) w y)
    (hxy : g y = f x) (htrans : NativeTransversality.At I I' J f g x y)
    (s t : ℝ) :
    NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ))
      (fun p : X × ℝ => (f p.1, p.2 + v p.1))
      (fun p : Y × ℝ => (g p.1, p.2 + w p.1)) (x, s) (y, t) := by
  intro _
  rw [native_time_lift_derivative s hf hv, native_time_lift_derivative t hg hw]
  exact surjective_time_lift_coprod _ _ _ _ (htrans hxy)

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

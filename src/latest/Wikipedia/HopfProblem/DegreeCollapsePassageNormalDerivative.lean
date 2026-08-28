import Wikipedia.HopfProblem.DegreeCollapsePassageClock
import Wikipedia.HopfProblem.DegreeCollapsePassageNormalDeterminant

/-!
# Differentiate the actual passage in its retained sheet charts

The normal derivative factors through the chosen terminal normal change,
the positive longitudinal rate, and the original source-sheet derivative.
The auxiliary terminal belt-tangent correction is absent from the formula.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {U H X N : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
  {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

theorem mfderiv_normal_trace_model
    {α : X → U} {x : X} (hα : MDifferentiableAt I 𝓘(ℝ, U) α x) (hα0 : α x = 0)
    {η : ℝ → ℝ} {τ κ : ℝ} (hη : HasDerivAt η κ τ) (hη1 : η τ = 1)
    (C : U ≃L[ℝ] U) {G : (ℝ × U) → N} {B : (ℝ × U) →L[ℝ] N}
    (hG : HasFDerivAt G B 0) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N)
      (fun p : ℝ × X => G (η p.1 - 1, C (α p.2))) (τ, x) : (ℝ × U) →L[ℝ] N) =
      B.comp ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).prodMap
        (C.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, U) α x))) := by
  have ht := (hη.sub_const 1).hasFDerivAt.hasMFDerivAt.comp (τ, x)
    (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hu := C.hasFDerivAt.hasMFDerivAt.comp x hα.hasMFDerivAt
  have hu' := hu.comp (τ, x) (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hpair : HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × U)
      (fun p : ℝ × X => (η p.1 - 1, C (α p.2))) (τ, x)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).prodMap
        (C.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, U) α x))) := by
    convert! ht.prodMk hu' using 1
  have hcenter : (η τ - 1, C (α x)) = (0 : ℝ × U) := by
    rw [hη1, hα0, map_zero, sub_self]
    rfl
  have hG' : HasFDerivAt G B (η τ - 1, C (α x)) := by rw [hcenter]; exact hG
  exact (hG'.hasMFDerivAt.comp (τ, x) hpair).mfderiv

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem LongitudinalTubeMotion.normal_trace_mfderiv
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞}
    (A : LongitudinalTubeMotion Φ)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞)
    (C : U ≃L[ℝ] U) (R : V ≃L[ℝ] V)
    {f : X → M} {x : X} (hf : MDifferentiableAt I 𝓘(ℝ, E) f x)
    (h0 : (0 : ℝ × (U × V)) ∈ Φ.source)
    (hΦ₀ : (0 : ℝ × (U × V)) ∈ Φ₀.source) (hx : Φ₀ 0 = f x)
    (hrec : ∀ z ∈ Φ₀.source, Φ₀ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hleft : (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 (0 : ℝ × (U × V))] Φ₀)
    (hright : (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 ((1 : ℝ), (0 : U × V))]
      linearTransverseChart (C.prodCongr R) Φ₁)
    (n : M → N) (B : (ℝ × U) →L[ℝ] N)
    (hB : HasFDerivAt (fun z : ℝ × U => n (Φ₁ (1 + z.1, (z.2, 0)))) B 0) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N)
      (fun p : ℝ × X => n (A.family (p.1, f p.2))) (A.time, x) : (ℝ × U) →L[ℝ] N) =
      B.comp ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (deriv Real.smoothTransition A.time * A.destination)).prodMap
          (C.toContinuousLinearMap.comp
            (mfderiv I 𝓘(ℝ, U) (fun q : X => (Φ₀.symm (f q)).2.1) x))) := by
  let W := ℝ × (U × V)
  let a : X → W := Φ₀.symm ∘ f
  let P : W →L[ℝ] U := (ContinuousLinearMap.fst ℝ U V).comp
    (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let α : X → U := P ∘ a
  have hfx : f x ∈ Φ₀.target := hx ▸ Φ₀.map_source hΦ₀
  have ha : MDifferentiableAt I 𝓘(ℝ, W) a x :=
    (Φ₀.symm.mdifferentiableAt (by simp) hfx).comp x hf
  have hα : MDifferentiableAt I 𝓘(ℝ, U) α x :=
    P.differentiableAt.mdifferentiableAt.comp x ha
  have ha0 : a x = 0 := (congrArg Φ₀.symm hx).symm.trans (Φ₀.left_inv hΦ₀)
  have hα0 : α x = 0 := by change P (a x) = 0; rw [ha0, map_zero]
  let η : ℝ → ℝ := fun t => Real.smoothTransition t * A.destination
  have hη : HasDerivAt η (deriv Real.smoothTransition A.time * A.destination) A.time :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable
      (by simp) A.time).hasDerivAt.mul_const _
  let G : (ℝ × U) → N := fun z => n (Φ₁ (1 + z.1, (z.2, 0)))
  have htrace := A.sheet_trace_germ_of_endpoint_germs Φ₀ Φ₁ C R hf.continuousAt
    h0 hΦ₀ hx hrec hleft hright
  have heq : (fun p : ℝ × X => n (A.family (p.1, f p.2))) =ᶠ[𝓝 (A.time, x)]
      fun p => G (η p.1 - 1, C (α p.2)) := by
    filter_upwards [htrace] with p hp
    rw [hp]
    change n (Φ₁ (η p.1, (C (α p.2), 0))) =
      n (Φ₁ (1 + (η p.1 - 1), (C (α p.2), 0)))
    rw [show 1 + (η p.1 - 1) = η p.1 by ring]
  rw [heq.mfderiv_eq]
  exact mfderiv_normal_trace_model hα hα0 hη A.time_value C hB

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

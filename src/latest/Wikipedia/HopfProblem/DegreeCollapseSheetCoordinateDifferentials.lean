import Wikipedia.HopfProblem.DegreeCollapseWholeSheetCrossing
import Wikipedia.HopfProblem.DegreeCollapseNativeTransversePostcomposition

/-!
# Original immersive sheets have invertible plane coordinates

An original native sheet locally contained in an affine coordinate plane
has a surjective coordinate differential. This follows from immersion and
equal finite dimensions, with no independent coordinate parametrization
or inverse-function hypothesis supplied.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {U W H X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] {I : ModelWithCorners ℝ U H}
  [TopologicalSpace X] [ChartedSpace H X]

theorem surjective_sheet_coordinate_mfderiv
    (P : W →L[ℝ] U) (Q : U →L[ℝ] W) (b : W) {a : X → W} {x : X}
    (ha : MDifferentiableAt I 𝓘(ℝ, W) a x)
    (hi : Injective (mfderiv I 𝓘(ℝ, W) a x))
    (hgerm : a =ᶠ[𝓝 x] fun y => Q (P (a y)) + b) :
    Surjective (mfderiv I 𝓘(ℝ, U) (P ∘ a) x) := by
  have hP : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, U) P (a x) :=
    P.differentiableAt.mdifferentiableAt
  have hα := hP.comp x ha
  have hQ : HasMFDerivAt 𝓘(ℝ, U) 𝓘(ℝ, W)
      (fun u => Q u + b) (P (a x)) Q :=
    (Q.hasFDerivAt.add_const b).hasMFDerivAt
  have heq : (mfderiv I 𝓘(ℝ, W) a x : U →L[ℝ] W) =
      Q.comp (mfderiv I 𝓘(ℝ, U) (P ∘ a) x) :=
    hgerm.mfderiv_eq.trans (hQ.comp x hα.hasMFDerivAt).mfderiv
  let D : U →L[ℝ] U := mfderiv I 𝓘(ℝ, U) (P ∘ a) x
  change Surjective D
  apply (LinearMap.injective_iff_surjective (f := D.toLinearMap)).mp
  intro u v huv
  apply hi
  rw [heq]
  exact congrArg Q huv

variable {V H' Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'}
  [TopologicalSpace Y] [ChartedSpace H' Y]

theorem native_coordinate_plane_trace_transverse
    {α : X → U} {β : Y → V} {x : X} {y : Y} {η : ℝ → ℝ} {τ κ : ℝ}
    (hα : MDifferentiableAt I 𝓘(ℝ, U) α x)
    (hβ : MDifferentiableAt I' 𝓘(ℝ, V) β y)
    (hαs : Surjective (mfderiv I 𝓘(ℝ, U) α x))
    (hβs : Surjective (mfderiv I' 𝓘(ℝ, V) β y))
    (hη : HasDerivAt η κ τ) (hκ : κ ≠ 0) :
    Wikipedia.SmoothSixDPoincare.NativeTransversality.At
      (𝓘(ℝ, ℝ).prod I) I' 𝓘(ℝ, ℝ × (U × V))
      (fun p : ℝ × X => (η p.1, (α p.2, 0)))
      (fun q : Y => (1, (0, β q))) (τ, x) y := by
  let D : U →L[ℝ] U := mfderiv I 𝓘(ℝ, U) α x
  let E : V →L[ℝ] V := mfderiv I' 𝓘(ℝ, V) β y
  let C : (ℝ × U) →L[ℝ] ℝ :=
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).comp
      (ContinuousLinearMap.fst ℝ ℝ U)
  let L : (ℝ × U) →L[ℝ] ℝ × (U × V) :=
    C.prod ((D.comp (ContinuousLinearMap.snd ℝ ℝ U)).prod 0)
  let R : V →L[ℝ] ℝ × (U × V) := (0 : V →L[ℝ] ℝ).prod ((0 : V →L[ℝ] U).prod E)
  have htime := hη.hasFDerivAt.hasMFDerivAt.comp (τ, x)
    (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hcoord := hα.hasMFDerivAt.comp (τ, x)
    (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hzero : HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V)
      (fun _ : ℝ × X => (0 : V)) (τ, x) 0 := hasMFDerivAt_const _ _
  have hT : HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × (U × V))
      (fun p : ℝ × X => (η p.1, (α p.2, (0 : V)))) (τ, x) L := by
    convert! htime.prodMk (hcoord.prodMk hzero) using 1
  have hone : HasMFDerivAt I' 𝓘(ℝ, ℝ) (fun _ : Y => (1 : ℝ)) y 0 :=
    hasMFDerivAt_const _ _
  have hz : HasMFDerivAt I' 𝓘(ℝ, U) (fun _ : Y => (0 : U)) y 0 :=
    hasMFDerivAt_const _ _
  have hB : HasMFDerivAt I' 𝓘(ℝ, ℝ × (U × V))
      (fun q : Y => ((1 : ℝ), ((0 : U), β q))) y R := by
    convert! hone.prodMk (hz.prodMk hβ.hasMFDerivAt) using 1
  intro _
  rw [hT.mfderiv, hB.mfderiv]
  change Surjective (L.coprod R)
  rintro ⟨s, u, v⟩
  obtain ⟨a, ha⟩ := hαs u
  obtain ⟨b, hb⟩ := hβs v
  refine ⟨((s / κ, a), b), ?_⟩
  apply Prod.ext
  · change s / κ * κ + 0 = s
    rw [add_zero, div_mul_cancel₀ s hκ]
  · change (D a + 0, 0 + E b) = (u, v)
    rw [add_zero, zero_add]
    exact Prod.ext ha hb

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

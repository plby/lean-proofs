import Wikipedia.NoExoticSixSphere.SmoothKernelFrame
import Mathlib.Analysis.Complex.Tietze

/-!
# Right inverses extending prescribed boundary values

A continuous family of surjective finite-dimensional operators has a
continuous right inverse. A prescribed right inverse on a closed embedded
subspace extends exactly: first extend its columns by Tietze, then correct
the extension by the canonical right inverse. This correction fixes all
already calibrated columns. No extension of an arbitrary frame is assumed.
-/

noncomputable section

open Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

theorem continuousAt_orthogonalRightInverse {X : Type*} [TopologicalSpace X]
    {D : X → H →L[ℝ] K} {x : X} (hD : ContinuousAt D x) (hs : Surjective (D x)) :
    ContinuousAt (fun y ↦ orthogonalRightInverse (D y)) x := by
  have h : ContMDiffAt 𝓘(ℝ, H →L[ℝ] K) 𝓘(ℝ, K →L[ℝ] H) ∞
      (fun A : H →L[ℝ] K ↦ orthogonalRightInverse A) (D x) :=
    contMDiffAt_orthogonalRightInverse contMDiffAt_id hs
  exact h.continuousAt.comp hD

theorem continuous_orthogonalRightInverse {X : Type*} [TopologicalSpace X]
    {D : X → H →L[ℝ] K} (hD : Continuous D) (hs : ∀ x, Surjective (D x)) :
    Continuous (fun x ↦ orthogonalRightInverse (D x)) :=
  continuous_iff_continuousAt.mpr fun x ↦
    continuousAt_orthogonalRightInverse hD.continuousAt (hs x)

namespace RelativeRightInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def inCoordinates (L : H ≃L[ℝ] E) (D : E →L[ℝ] K) : K →L[ℝ] E :=
  L.toContinuousLinearMap.comp (orthogonalRightInverse (D.comp L.toContinuousLinearMap))

theorem apply_inCoordinates (L : H ≃L[ℝ] E) (D : E →L[ℝ] K)
    (hs : Surjective D) (u : K) : D (inCoordinates L D u) = u :=
  apply_orthogonalRightInverse (D.comp L.toContinuousLinearMap) (hs.comp L.surjective) u

theorem continuous_inCoordinates (L : H ≃L[ℝ] E)
    {X : Type*} [TopologicalSpace X] {D : X → E →L[ℝ] K}
    (hD : Continuous D) (hs : ∀ x, Surjective (D x)) :
    Continuous (fun x ↦ inCoordinates L (D x)) :=
  continuous_const.clm_comp (continuous_orthogonalRightInverse
    (hD.clm_comp continuous_const) (fun x ↦ (hs x).comp L.surjective))

def correct (D : E →L[ℝ] K) (R A : K →L[ℝ] E) : K →L[ℝ] E :=
  R + A - R.comp (D.comp A)

omit [FiniteDimensional ℝ K] in
theorem apply_correct (D : E →L[ℝ] K) (R A : K →L[ℝ] E)
    (hR : ∀ u, D (R u) = u) (u : K) : D (correct D R A u) = u := by
  simp only [correct, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_add, hR, add_sub_cancel_right]

omit [FiniteDimensional ℝ K] in
theorem correct_eq (D : E →L[ℝ] K) (R A : K →L[ℝ] E)
    (hA : ∀ u, D (A u) = u) : correct D R A = A := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [correct, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, hA, add_sub_cancel_left]

omit [FiniteDimensional ℝ K] in
theorem continuous_correct {X : Type*} [TopologicalSpace X]
    {D : X → E →L[ℝ] K} {R A : X → K →L[ℝ] E}
    (hD : Continuous D) (hR : Continuous R) (hA : Continuous A) :
    Continuous (fun x ↦ correct (D x) (R x) (A x)) :=
  (hR.add hA).sub (hR.clm_comp (hD.clm_comp hA))

variable [FiniteDimensional ℝ E]

theorem exists_extension (L : H ≃L[ℝ] E)
    {X Y : Type*} [TopologicalSpace X] [NormalSpace X] [TopologicalSpace Y]
    (i : Y → X) (hi : IsClosedEmbedding i)
    (D : C(X, E →L[ℝ] K)) (hs : ∀ x, Surjective (D x))
    (a : C(Y, K →L[ℝ] E)) (ha : ∀ y u, D (i y) (a y u) = u) :
    ∃ A : C(X, K →L[ℝ] E), (∀ x u, D x (A x u) = u) ∧ ∀ y, A (i y) = a y := by
  obtain ⟨B, hB⟩ := a.exists_extension hi
  let R : C(X, K →L[ℝ] E) :=
    ⟨fun x ↦ inCoordinates L (D x), continuous_inCoordinates L D.continuous hs⟩
  refine ⟨⟨fun x ↦ correct (D x) (R x) (B x),
    continuous_correct D.continuous R.continuous B.continuous⟩, ?_, ?_⟩
  · intro x u
    exact apply_correct (D x) (R x) (B x) (apply_inCoordinates L (D x) (hs x)) u
  · intro y
    have hb : B (i y) = a y := ContinuousMap.congr_fun hB y
    change correct (D (i y)) (R (i y)) (B (i y)) = a y
    rw [hb]
    exact correct_eq (D (i y)) (R (i y)) (a y) (ha y)

end RelativeRightInverse

end NoExoticSixSphere

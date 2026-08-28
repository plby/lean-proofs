import Wikipedia.NoExoticSixSphere.ContinuousProjectionHomotopy
import Wikipedia.NoExoticSixSphere.SmoothFrame
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smoothing a continuous frame of smooth projection ranges

Approximate the ambient frame by a smooth operator family and project it into
the prescribed fibers. Compactness and openness of injectivity give a uniform
approximation tolerance. Equality of fiber dimensions then proves surjectivity.
-/

open scoped Manifold ContDiff Topology
open Function Set

namespace NoExoticSixSphere

variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
  {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

/-- A continuous frame of finite-dimensional smooth projection ranges can be made smooth. -/
theorem nonempty_smoothRangeFrame_of_continuous (P : M → F →L[ℝ] F)
    (hP : ∀ x, IsIdempotentElem (P x))
    (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (a : ContinuousRangeFrame P K) :
    Nonempty (SmoothRangeFrame I P K) := by
  let A : M → K →L[ℝ] F := fun x ↦ (P x).range.subtypeL.comp (a.equiv x).toContinuousLinearMap
  have hA : Continuous A := a.continuous
  have hAi (x : M) : Injective (A x) :=
    Subtype.val_injective.comp (a.equiv x).injective
  have hPA (x : M) : (P x).comp (A x) = A x := by
    apply ContinuousLinearMap.ext
    intro v
    exact projection_apply_range (P x) (hP x) (a.equiv x v)
  let U : Set (K →L[ℝ] F) := {L | ∀ x, Injective ((P x).comp (A x + L))}
  have hU : IsOpen U := by
    have hj : Continuous (fun p : (K →L[ℝ] F) × M ↦ (P p.2).comp (A p.2 + p.1)) :=
      (hs.continuous.comp continuous_snd).clm_comp
        ((hA.comp continuous_snd).add continuous_fst)
    exact isOpen_forall_compact (ContinuousLinearMap.isOpen_injective.preimage hj)
  have hzero : (0 : K →L[ℝ] F) ∈ U := by
    intro x
    simpa only [add_zero, hPA] using hAi x
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU 0 hzero
  obtain ⟨g, hg, _⟩ := hA.exists_contMDiff_approx I (⊤ : ℕ∞) continuous_const (fun _ ↦ hε)
  let S : M → K →L[ℝ] F := fun x ↦ (P x).comp (g x)
  have hSs : ContMDiff I 𝓘(ℝ, K →L[ℝ] F) ∞ S := hs.clm_comp g.contMDiff
  have hSi (x : M) : Injective (S x) := by
    have hb : g x - A x ∈ Metric.ball 0 ε := by
      simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hg x
    have hi := hball hb x
    simpa only [← add_sub_assoc, add_sub_cancel_left] using hi
  have hrange (x : M) : (S x).range = (P x).range := by
    let : FiniteDimensional ℝ (P x).range :=
      FiniteDimensional.of_injective (a.equiv x).symm.toLinearMap (a.equiv x).symm.injective
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro v ⟨w, rfl⟩
      exact ⟨g x w, rfl⟩
    · exact (LinearMap.finrank_range_of_inj (hSi x)).trans (a.equiv x).toLinearEquiv.finrank_eq
  let e (x : M) : K ≃L[ℝ] (P x).range :=
    (LinearEquiv.ofInjective (S x).toLinearMap (hSi x)).toContinuousLinearEquiv.trans
      (ContinuousLinearEquiv.ofEq _ _ (hrange x))
  refine ⟨⟨e, ?_⟩⟩
  have heq : (fun x ↦ (P x).range.subtypeL.comp (e x).toContinuousLinearMap) = S := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [heq]
  exact hSs

/-- Only the endpoint of a continuous projection nullhomotopy must be smooth to obtain a frame. -/
theorem nonempty_smoothRangeFrame_of_continuousHomotopy [CompleteSpace F]
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (P : T → M → F →L[ℝ] F) (hP : ∀ t x, IsIdempotentElem (P t x))
    (hc : Continuous (fun p : T × M ↦ P p.1 p.2)) (s t : T)
    (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ (P t))
    (P₀ : F →L[ℝ] F) (hstart : P s = fun _ ↦ P₀) (q : K ≃L[ℝ] P₀.range) :
    Nonempty (SmoothRangeFrame I (P t) K) := by
  obtain ⟨a⟩ := nonempty_continuousRangeFrame_of_homotopy P hP hc s t P₀ hstart q
  exact nonempty_smoothRangeFrame_of_continuous (P t) (hP t) hs a

end NoExoticSixSphere

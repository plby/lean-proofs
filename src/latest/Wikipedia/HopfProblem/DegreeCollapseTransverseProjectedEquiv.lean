import Wikipedia.HopfProblem.DegreeCollapseSupportedTransverseBlocks
import Wikipedia.SmoothSixDPoincare.NativeTransversalityStability
import Wikipedia.SmoothSixDPoincare.TransverseNormalLinearMap

/-!
# The projected block equivalence from actual native transversality

At the actual crossing of the first coordinate sheet with the second
coordinate plane, native transversality makes their tangent sum surjective.
Projection along the second plane gives a bijective first-block derivative
in equal finite dimensions. The required continuous linear equivalence is
constructed from this actual derivative, rather than supplied separately.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

/-- Construct the actual first-block equivalence required by the supported
correction theorem from native transversality at the crossing. -/
theorem exists_projected_equiv_of_native_transverse
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0)
    (htrans : NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B)
      (fun x : A => Φ (x, 0)) (fun y : B => (0, y)) 0 0) :
    ∃ P : A ≃L[ℝ] A, ∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x := by
  let D : A →L[ℝ] (A × B) := (fderiv ℝ Φ 0).comp (ContinuousLinearMap.inl ℝ A B)
  let N : (A × B) →L[ℝ] A := ContinuousLinearMap.fst ℝ A B
  let J : B →L[ℝ] (A × B) := ContinuousLinearMap.inr ℝ A B
  have hdiff := (Φ.contMDiffOn_toFun.contDiffOn.contDiffAt
    (Φ.open_source.mem_nhds hzero)).differentiableAt (by simp)
  have hι : HasFDerivAt (fun x : A => (x, (0 : B))) (ContinuousLinearMap.inl ℝ A B) (0 : A) :=
    (ContinuousLinearMap.inl ℝ A B).hasFDerivAt
  have hd : HasFDerivAt (fun x : A => Φ (x, 0)) D 0 :=
    hdiff.hasFDerivAt.comp (f := fun x : A => (x, (0 : B))) (0 : A) hι
  have hj : HasFDerivAt (fun y : B => (0, y)) J 0 :=
    (ContinuousLinearMap.inr ℝ A B).hasFDerivAt
  have hcross : (0, (0 : B)) = Φ ((0 : A), 0) := hΦzero.symm
  have ht := htrans hcross
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv, hd.fderiv, hj.fderiv] at ht
  have hNJ : N.comp J = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    rfl
  have hN : Surjective N := fun x => ⟨(x, 0), rfl⟩
  have hJD : Surjective (J.coprod D) := TransverseCoordinates.surjective_coprod_swap D J ht
  have hbij : Bijective (N.comp D) :=
    TransverseCoordinates.bijective_normal_comp N J D hN hJD hNJ rfl
  let P := (LinearEquiv.ofBijective (N.comp D).toLinearMap hbij).toContinuousLinearEquiv
  exact ⟨P, fun _ => rfl⟩

/-- Native transversality and the actual unique intersection construct the
supported block correction, including its projected derivative equivalence. -/
theorem exists_block_reduction_of_native_transverse
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0)
    (htrans : NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, A × B)
      (fun x : A => Φ (x, 0)) (fun y : B => (0, y)) 0 0)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Φ (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ P : A ≃L[ℝ] A, (∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x) ∧
      ∃ (S : B ≃L[ℝ] B)
        (Dₛ Dₜ : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
        (Kₛ Kₜ : Set (A × B)),
        IsCompact Kₛ ∧ Kₛ ⊆ Φ.source ∧ IsCompact Kₜ ∧ Kₜ ⊆ Φ.target ∧
        Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy Dₛ Kₛ {p : A × B | p.2 = 0}) ∧
        Nonempty (SupportedDiffeomorph.SupportedRelativeIsotopy Dₜ Kₜ {(0 : A × B)}) ∧
        MapsTo Dₛ Φ.source Φ.source ∧ MapsTo Dₜ Φ.target Φ.target ∧
        (∀ x : A, (x, (0 : B)) ∈ Φ.source →
          ((Dₜ (Φ (Dₛ (x, 0)))).1 = 0 ↔ x = 0)) ∧
        (fun p => Dₜ (Φ (Dₛ p))) =ᶠ[𝓝 (0 : A × B)] (fun p => (P p.1, S p.2)) := by
  obtain ⟨P, hP⟩ := exists_projected_equiv_of_native_transverse Φ hzero hΦzero htrans
  exact ⟨P, hP, exists_supported_transverse_block_reduction Φ hzero hΦzero P hP hunique⟩

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

import Wikipedia.HopfProblem.DegreeCollapseMutualSheetCancellation
import Wikipedia.SmoothSixDPoincare.FiniteSignedCancellation

/-!
# A repeatable cancellation step for the actual mutual crossing set

The compactly supported native move retains the full first-map germ at
every remaining crossing. Its endpoint is still an embedded transverse
immersion, and the intrinsic signs at all surviving source points agree.
The fixed second sheet is never changed.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MutualSheets

open Wikipedia.SmoothSixDPoincare
open OrbitPair.DeterminantSignCover

variable {D E M N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [T2Space N] [CompactSpace N] [PathConnectedSpace N]
  [TopologicalSpace P] [ChartedSpace D P] [IsManifold 𝓘(ℝ, D) ∞ P]
  [T2Space P] [CompactSpace P] [PathConnectedSpace P]
  (oN : Orientation (tangentBundleCore 𝓘(ℝ, D) N))
  (oP : Orientation (tangentBundleCore 𝓘(ℝ, D) P))
  (oM : Orientation (tangentBundleCore 𝓘(ℝ, E) M))
  (K : (D × D) ≃L[ℝ] E)

def crossingPoints (F : N → M) (G : P → M) : Set N := F ⁻¹' range G

def pointSign (F : N → M) (G : P → M) (x : N) : SignType :=
  if intersectionSign oN oP oM K F G x (Function.invFun G (F x)) then -1 else 1

def Good (G : P → M) (F : N → M) : Prop :=
  ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F ∧ Injective F ∧
    (∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x)) ∧
    ∀ x y, G y = F x → Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
        (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y))

theorem pointSign_unit (F : N → M) (G : P → M) (x : N) :
    pointSign oN oP oM K F G x = 1 ∨ pointSign oN oP oM K F G x = -1 := by
  unfold pointSign
  split_ifs <;> simp

theorem pointSign_opposite_iff (F : N → M) (G : P → M) (x y : N) :
    pointSign oN oP oM K F G x * pointSign oN oP oM K F G y = -1 ↔
      intersectionSign oN oP oM K F G x (Function.invFun G (F x)) ≠
        intersectionSign oN oP oM K F G y (Function.invFun G (F y)) := by
  unfold pointSign
  cases intersectionSign oN oP oM K F G x (Function.invFun G (F x)) <;>
    cases intersectionSign oN oP oM K F G y (Function.invFun G (F y)) <;> decide

theorem pointSign_eq_of_eventuallyEq {F F' : N → M} (G : P → M) {x : N}
    (he : F' =ᶠ[𝓝 x] F) : pointSign oN oP oM K F' G x = pointSign oN oP oM K F G x := by
  have hp : F' x = F x := he.eq_of_nhds
  have hd : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F' x : D →L[ℝ] E) =
      mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x := he.mfderiv_eq
  have hj (y : P) : jointFrame K F' G x y = jointFrame K F G x y := by
    unfold jointFrame
    rw [hd]
  unfold pointSign intersectionSign intersectionBit
  rw [hp, hj]

theorem exists_signed_cancellation_step
    (hdim : Module.finrank ℝ E = 6) (hsheet : Module.finrank ℝ D = 3)
    (F : C(N, M)) (G : C(P, M))
    (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G) (hinjG : Injective G)
    (hiG : ∀ y, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y))
    (hgood : Good (D := D) (E := E) G F)
    (x₀ x₁ : N) (hx₀ : x₀ ∈ crossingPoints F G) (hx₁ : x₁ ∈ crossingPoints F G)
    (hsign : pointSign oN oP oM K F G x₀ * pointSign oN oP oM K F G x₁ = -1) :
    ∃ ψ : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∃ F' : C(N, M),
      SupportedDiffeomorph.IsotopicToIdentity ψ ∧ (∀ x, F' x = ψ (F x)) ∧
      Good (D := D) (E := E) G F' ∧
      crossingPoints F' G = crossingPoints F G \ {x₀, x₁} ∧
      (∀ x ∈ crossingPoints F' G, (F' : N → M) =ᶠ[𝓝 x] F) ∧
      ∀ x ∈ crossingPoints F' G, pointSign oN oP oM K F' G x = pointSign oN oP oM K F G x := by
  obtain ⟨hF, hinjF, hiF, ht⟩ := hgood
  have hc₀ : G (Function.invFun G (F x₀)) = F x₀ := Function.invFun_eq hx₀
  have hc₁ : G (Function.invFun G (F x₁)) = F x₁ := Function.invFun_eq hx₁
  have hs := (pointSign_opposite_iff oN oP oM K F G x₀ x₁).mp hsign
  obtain ⟨C, hC, hdis, ψ, hiso, hfix, hcancel⟩ :=
    exists_opposite_pair_cancellation oN oP oM K hdim hsheet hF hG hinjF hinjG hiF hiG ht
      hc₀ hc₁ hs
  let F' : C(N, M) := ⟨ψ ∘ F, ψ.continuous.comp F.continuous⟩
  have hF' : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F' := ψ.contMDiff.comp hF
  have hinj' : Injective F' := ψ.injective.comp hinjF
  have hi' : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F' x) := by
    intro x
    change Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) (ψ ∘ F) x)
    rw [mfderiv_comp x (ψ.mdifferentiable (by simp) _) (hF.mdifferentiableAt (by simp))]
    exact ((ψ.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (by trivial)).comp (hiF x)
  have hfixR : ∀ z ∈ (range F ∩ range G) \ {F x₀, F x₁}, ψ z = z := by
    intro z hz
    exact hfix z (fun hzC => Set.disjoint_left.mp hdis hzC hz)
  have hpre := SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal
    ψ.toEquiv (F : N → M) hfixR hcancel
  have hp : (F : N → M) ⁻¹' {F x₀, F x₁} = {x₀, x₁} := by
    ext x
    change (F x = F x₀ ∨ F x = F x₁) ↔ (x = x₀ ∨ x = x₁)
    exact or_congr hinjF.eq_iff hinjF.eq_iff
  have hpoints : crossingPoints F' G = crossingPoints F G \ {x₀, x₁} :=
    hpre.trans (congrArg (fun s : Set N => crossingPoints F G \ s) hp)
  have hgerm : ∀ x ∈ crossingPoints F' G, (F' : N → M) =ᶠ[𝓝 x] F := by
    intro x hx
    have hxold : x ∈ crossingPoints F G \ {x₀, x₁} := hpoints ▸ hx
    have hz : F x ∈ (range F ∩ range G) \ {F x₀, F x₁} := by
      refine ⟨⟨⟨x, rfl⟩, hxold.1⟩, ?_⟩
      change x ∉ (F : N → M) ⁻¹' {F x₀, F x₁}
      rw [hp]
      exact hxold.2
    exact SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed hC.isClosed hfix
      F.continuous (fun hzC => Set.disjoint_left.mp hdis hzC hz)
  have ht' : ∀ x y, G y = F' x → Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F' x).coprod
        (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y)) := by
    intro x y hxy
    have hn := hgerm x ⟨y, hxy⟩
    have hd : (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F' x : D →L[ℝ] E) =
        mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x := hn.mfderiv_eq
    change Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F' x : D →L[ℝ] E).coprod
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y : D →L[ℝ] E))
    rw [hd]
    exact ht x y (hxy.trans hn.eq_of_nhds)
  refine ⟨ψ, F', hiso, fun _ => rfl, ⟨hF', hinj', hi', ht'⟩, hpoints, hgerm, ?_⟩
  intro x hx
  exact pointSign_eq_of_eventuallyEq oN oP oM K G (hgerm x hx)

end Wikipedia.HopfProblem.DegreeCollapse.MutualSheets

import Wikipedia.HopfProblem.DegreeCollapseCanonicalMiddleMatrix

/-!
# An unconditional geometric middle matrix for the original threefold

The matrix columns are exactly the canonical sphere classes in the actual
common sublevel's free basis. Its surjectivity follows from the finite
literal-inclusion sequence. The smooth family, original native parameters,
critical labels, intrinsic counts, and minimality are retained together.
Geometric matrix operations and smooth sphere recognition remain open.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.Threefold

open SpecialPeriods MorseCancellation SingularMayerVietoris

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
  SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
  SpecialPeriods.Threefold.space_isSmoothRealManifold SpecialPeriods.Threefold.space_pathConnected

local notation "E₆" => ℂ × ComplexPlane₂
local notation "M₆" => SpecialPeriods.Threefold.Space
local notation "S₂" => Hemisphere.Sphere 2

theorem exists_geometric_middle_matrix :
    ∃ f : M₆ → ℝ, ∃ hf : ContMDiff 𝓘(ℝ, E₆) 𝓘(ℝ, ℝ) ∞ f,
      IsMorse E₆ f ∧ ∃ S : AdaptedSurgeryWindows E₆ f,
        (∀ p q : criticalPoints E₆ f, f p < f q →
          nativeMorseIndex E₆ f p ≤ nativeMorseIndex E₆ f q) ∧
        nativeMorseCount E₆ f 0 = 1 ∧ nativeMorseCount E₆ f 6 = 1 ∧
        nativeMorseCount E₆ f 1 = 0 ∧ nativeMorseCount E₆ f 5 = 0 ∧
        (∀ g : M₆ → ℝ, ContMDiff 𝓘(ℝ, E₆) 𝓘(ℝ, ℝ) ∞ g → IsMorse E₆ g →
          InjOn g (criticalPoints E₆ g) → (criticalPoints E₆ f).ncard ≤
            (criticalPoints E₆ g).ncard) ∧
        ∃ r n : ℕ, nativeMorseCount E₆ f 2 = r ∧ nativeMorseCount E₆ f 3 = n ∧
          ∃ hn : r + n < S.toSurgeryWindows.count,
            let q := S.toSurgeryWindows.point ⟨r, by omega⟩
            let a := nativeMiddleBaseCut S r n hn
            let p := nativeMiddleBlockPoint S r n hn
            ∃ T : AdaptedSurgeryWindows E₆ f,
              (∀ z, (T.data z).chart = (S.data z).chart) ∧
              (∀ z, (T.data z).radius < (S.data z).radius) ∧
              (∀ z ∈ criticalPoints E₆ f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
              ∃ B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M₆ // f y ≤ a} 2,
              ∃ hp : ∀ j, nativeMorseIndex E₆ f (p j) = 3,
              ∃ hlower : ∀ j, a < T.toSurgeryWindows.lower (p j),
              ∃ γ : Fin n → C(S₂, {y : M₆ // f y = a}),
                IsNativeMiddleBasinFamily T hf (S.data q).upper_regular p (fun j => γ j) ∧
                (∀ j x, ∃ t : ℝ,
                  T.flow t (nativeIndexThreeAttachingSphere T (p j) (hp j) x).val = (γ j x).val) ∧
                (∀ j, singularHomologyMap (sublevelMap f (hlower j).le) 2 (middleSectionClass (γ j)) =
                  (T.data (p j)).indexThreeAttachingClass
                    ((nativeMorseIndex_eq_chart (T.data (p j)).chart).symm.trans (hp j))) ∧
                Surjective (canonicalMiddleMatrix B γ).mulVec := by
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal,
      r, n, hr, hcount, hn, T, hcharts, hradii, hgerms, ⟨B⟩, hp, hlower, γ, hγ, horbit, hclass⟩ :=
    exists_canonical_middle_family_with_classes
  refine ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal, r, n, hr, hcount,
    hn, T, hcharts, hradii, hgerms, B, hp, hlower, γ, hγ, horbit, hclass, ?_⟩
  exact canonical_middle_matrix_surjective S T hf SpecialPeriods.Threefold.real_dimension
    threefoldHomotopyEquiv horder hzero hone r n hr hcount hn hp hlower B γ horbit

end Wikipedia.HopfProblem.DegreeCollapse.Threefold

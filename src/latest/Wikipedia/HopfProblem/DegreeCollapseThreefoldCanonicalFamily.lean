import Wikipedia.HopfProblem.DegreeCollapseMiddleInclusionStep

/-!
# Canonical middle sections and their actual attaching classes on the original threefold

All geometric hypotheses are discharged. The common sublevel retains its
constructed free integral second-homology basis. Every canonical sphere
comes from the original signed critical chart along the actual new flow,
and its class maps by literal inclusion to that native attaching class.
The finite spanning argument and geometric cancellation are not asserted.
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

theorem exists_canonical_middle_family_with_classes :
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
            let a := S.toSurgeryWindows.upper q
            let p := nativeMiddleBlockPoint S r n hn
            ∃ T : AdaptedSurgeryWindows E₆ f,
              (∀ z, (T.data z).chart = (S.data z).chart) ∧
              (∀ z, (T.data z).radius < (S.data z).radius) ∧
              (∀ z ∈ criticalPoints E₆ f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
              Nonempty ((Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M₆ // f y ≤ a} 2) ∧
              ∃ hp : ∀ j, nativeMorseIndex E₆ f (p j) = 3,
              ∃ hlower : ∀ j, a < T.toSurgeryWindows.lower (p j),
              ∃ γ : Fin n → C(S₂, {y : M₆ // f y = a}),
                IsNativeMiddleBasinFamily T hf (S.data q).upper_regular p (fun j => γ j) ∧
                (∀ j x, ∃ t : ℝ,
                  T.flow t (nativeIndexThreeAttachingSphere T (p j) (hp j) x).val = (γ j x).val) ∧
                ∀ j, singularHomologyMap (sublevelMap f (hlower j).le) 2 (middleSectionClass (γ j)) =
                  (T.data (p j)).indexThreeAttachingClass
                    ((nativeMorseIndex_eq_chart (T.data (p j)).chart).symm.trans (hp j)) := by
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal,
      r, n, hr, hcount, htwo, hn, hthree, -, T, hcharts, hradii, hgerms, α, hα⟩ :=
    exists_native_middle_family
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  let a := S.toSurgeryWindows.upper q
  let p := nativeMiddleBlockPoint S r n hn
  have hp (j : Fin n) : nativeMorseIndex E₆ f (p j) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hthree ⟨r + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  have hlower (j : Fin n) : a < T.toSurgeryWindows.lower (p j) := by
    have hqj : f q < f (p j) :=
      S.toSurgeryWindows.point_strictMono (by change r < r + j.val + 1; omega)
    have hsep := S.separated q (p j) hqj
    have hh := mul_pos (sub_pos.mpr (hradii (p j)))
      (add_pos (S.data (p j)).radius_pos (T.data (p j)).radius_pos)
    change a < f (p j) - (T.data (p j)).radius ^ 2
    change a < f (p j) - (S.data (p j)).radius ^ 2 at hsep
    nlinarith
  obtain ⟨β, hβ, -, hβflow⟩ :=
    T.exists_canonical_middle_family hf (S.data q).upper_regular p hp α hα
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let γ : Fin n → C(S₂, {y : M₆ // f y = a}) := fun j => ⟨β j, (hβ.1 j).continuous⟩
  refine ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal, r, n, hr, hcount,
    hn, T, hcharts, hradii, hgerms, ?_, hp, hlower, γ, hβ, hβflow, ?_⟩
  · exact ⟨S.toSurgeryWindows.indexTwoBasis hf r (by omega) htwo⟩
  · intro j
    exact T.native_attaching_class_of_flow_section hf (p j) (hp j)
      (S.data q).upper_regular (hlower j) (γ j) (hβflow j)

end Wikipedia.HopfProblem.DegreeCollapse.Threefold

import Wikipedia.HopfProblem.DegreeCollapseOrderedMiddleFamily
import Wikipedia.HopfProblem.DegreeCollapseThreefoldOuterElimination
import Wikipedia.HopfProblem.DegreeCollapseMiddleBlockCounts

/-!
# An unconditional common-level middle family on the original threefold

The unchanged threefold supplies every hypothesis of the finite block
construction. The ordered minimal Morse function, original critical labels,
intrinsic block sizes, and surjective retained matrix remain available.
The new flow realizes full disjoint middle basin spheres on the original
common cut. Compatibility of their classes with the retained matrix is
not asserted here and remains a separate geometric obligation.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.Threefold

open SpecialPeriods MorseCancellation

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
  SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
  SpecialPeriods.Threefold.space_isSmoothRealManifold SpecialPeriods.Threefold.space_pathConnected

local notation "E₆" => ℂ × ComplexPlane₂
local notation "M₆" => SpecialPeriods.Threefold.Space
local notation "S₂" => Hemisphere.Sphere 2

theorem exists_native_middle_family :
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
          ∃ htwo : S.toSurgeryWindows.HasIndexTwoPrefix r,
          ∃ hn : r + n < S.toSurgeryWindows.count,
          ∃ hthree : S.toSurgeryWindows.HasIndexThreeBlock r n,
            Surjective (S.toSurgeryWindows.middleMatrix hf r n htwo hn hthree).mulVec ∧
            let q := S.toSurgeryWindows.point ⟨r, by omega⟩
            ∃ T : AdaptedSurgeryWindows E₆ f,
              (∀ p, (T.data p).chart = (S.data p).chart) ∧
              (∀ p, (T.data p).radius < (S.data p).radius) ∧
              (∀ p ∈ criticalPoints E₆ f, ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
              ∃ α : Fin n → S₂ → (S.data q).UpperLevel,
                IsNativeMiddleBasinFamily T hf (S.data q).upper_regular
                  (nativeMiddleBlockPoint S r n hn) α := by
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩ :=
    exists_minimal_ordered_morse_without_outer_indices
  obtain ⟨r, n, htwo, hn, hthree, -, hafter, hsurj, -⟩ :=
    exists_surjective_middle_matrix_of_ordered_indices S.toSurgeryWindows hf
      SpecialPeriods.Threefold.real_dimension threefoldHomotopyEquiv horder hzero hone
  obtain ⟨hr, hcount⟩ := native_middle_block_counts S.toSurgeryWindows hf r n htwo hn hthree hafter
  obtain ⟨T, hcharts, hradii, hgerms, α, hα⟩ := S.exists_ordered_middle_family hf hm
    SpecialPeriods.Threefold.real_dimension r n hn hthree (fun p => (S.data p).radius)
      (fun p => (S.data p).radius_pos)
  exact ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal, r, n, hr, hcount,
    htwo, hn, hthree, hsurj, T, hcharts, hradii, hgerms, α, hα⟩

end Wikipedia.HopfProblem.DegreeCollapse.Threefold

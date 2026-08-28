import Wikipedia.HopfProblem.DegreeCollapseIndexFourBlockRealization
import Wikipedia.HopfProblem.DegreeCollapseOrderedMiddleFamily
import Wikipedia.HopfProblem.DegreeCollapseThreeFourPresentation

/-!
# Realize the actual ordered index-four block on its original lower cut

The labels are exactly the consecutive original critical points. Their
constructed four-block property supplies the finite realization hypotheses.
The resulting disjoint embedded three-spheres have the full original
backward-basin labels in the native level before the block.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_ordered_index_four_family
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hfour : ThreeFourPresentation.HasIndexFourBlock S.toSurgeryWindows r n)
    (ε : criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ p, (T.data p).chart = (S.data p).chart) ∧
      (∀ p, (T.data p).radius < ε p) ∧
      (∀ p ∈ criticalPoints E f, ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
      ∃ α : Fin n → S₃ → (S.data q).UpperLevel,
        IsNativeFourBasinFamily T hf (S.data q).upper_regular
          (nativeMiddleBlockPoint S r n hn) α := by
  let W := S.toSurgeryWindows
  have hnW : r + n < W.count := hn
  let q := W.point ⟨r, by omega⟩
  let p := nativeMiddleBlockPoint S r n hn
  have hp (j : Fin n) : nativeMorseIndex E f (p j) = 4 :=
    (nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hfour ⟨r + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  have horder : StrictMono (fun j => f (p j)) := by
    intro i j hij
    apply W.point_strictMono
    change r + i.val + 1 < r + j.val + 1
    omega
  have habove (j : Fin n) : W.upper q < f (p j) := by
    have hqj : f q < f (p j) := W.point_strictMono (by change r < r + j.val + 1; omega)
    exact (W.separated q (p j) hqj).trans (W.lower_lt_value (p j))
  have hblock (j : Fin n) (z : criticalPoints E f)
      (hz : W.upper q < f z) (hzj : f z ≤ f (p j)) : z ∈ range p := by
    obtain ⟨k, rfl⟩ := W.point.surjective z
    have hrk : r < k.val := W.point_strictMono.lt_iff_lt.mp ((W.value_lt_upper q).trans hz)
    have hkj : k.val ≤ r + j.val + 1 := W.point_strictMono.le_iff_le.mp hzj
    let i : Fin n := ⟨k.val - (r + 1), by omega⟩
    refine ⟨i, ?_⟩
    apply congrArg W.point
    apply Fin.ext
    change r + (k.val - (r + 1)) + 1 = k.val
    omega
  exact S.exists_index_four_block_realization hf hm hdim n (S.data q).upper_regular
    p hp horder habove hblock ε hε

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

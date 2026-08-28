import Wikipedia.HopfProblem.DegreeCollapseCompleteFourCancellation
import Wikipedia.HopfProblem.DegreeCollapseNativeThreeBeltCutMatrix

/-!
# Cancel a pair in the actual three/four prefix below the original outer cut

The original ordered blocks and vanishing sublevel H3 construct the complete
native attaching family, its surjective integral matrix, the primitive
last-three-handle coordinate, and the lower loop contractions. These actual
data supply the bounded cancellation theorem. Every hypothesis concerns
the original prefix; the untouched upper region has no index restriction.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.cancel_three_four_block_below_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    {b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    [Subsingleton (SingularHomology {y : M // f y ≤ b} 3)]
    (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) (hrpos : 0 < r)
    (hthree : S.toSurgeryWindows.HasIndexThreeBlock 0 r)
    (hfour : ThreeFourPresentation.HasIndexFourBlock S.toSurgeryWindows r n)
    (hcut : S.toSurgeryWindows.upper (S.toSurgeryWindows.point ⟨r + n, hn⟩) < b)
    (hwhich : ∀ i : Fin S.toSurgeryWindows.count,
      f (S.toSurgeryWindows.point i) < b ↔ i.val ≤ r + n) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    let labels := nativeMiddleBlockPoint S r n hn
    ∃ i : Fin n, ∃ v : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧ IsMorse E v ∧
      InjOn v (criticalPoints E v) ∧
      (criticalPoints E v).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ z, z ∈ criticalPoints E v ↔
        z ∈ criticalPoints E f ∧ z ≠ q.val ∧ z ≠ (labels i).val) ∧
      (∀ z ∈ criticalPoints E v, nativeMorseIndex E v z = nativeMorseIndex E f z) ∧
      (∀ z, b ≤ f z → v =ᶠ[𝓝 z] f) ∧ ∀ z, v z < b ↔ f z < b := by
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  let labels := nativeMiddleBlockPoint S r n hn
  let m := S.toSurgeryWindows.point ⟨0, by omega⟩
  obtain ⟨T, _, _, _, _, _, hsep, hindex, hprimitive, hnull, hp, B, γ, hγ, _, hsurj⟩ :=
    S.exists_native_three_belt_cut_matrix hf hm hdim hb r n hn hrpos hthree hfour hcut hwhich
  have hprefix (z : criticalPoints E f) (hzb : f z < b) : z = m ∨
      nativeMorseIndex E f z = 3 ∨ nativeMorseIndex E f z = 4 := by
    obtain ⟨j, rfl⟩ := S.toSurgeryWindows.point.surjective z
    have hjbound := (hwhich j).mp hzb
    by_cases hj0 : j.val = 0
    · exact Or.inl (congrArg S.toSurgeryWindows.point (Fin.ext hj0))
    by_cases hjr : j.val ≤ r
    · exact Or.inr (Or.inl ((nativeMorseIndex_eq_chart
        (S.data (S.toSurgeryWindows.point j)).chart).trans (hthree j (by omega) (by omega))))
    · exact Or.inr (Or.inr ((nativeMorseIndex_eq_chart
        (S.data (S.toSurgeryWindows.point j)).chart).trans
          (hfour j (lt_of_not_ge hjr) hjbound)))
  have hvalues (j : Fin n) :
      f q + (T.data q).radius ^ 2 < f (labels j) ∧ f (labels j) < b := by
    refine ⟨(hsep j).trans (T.toSurgeryWindows.lower_lt_value (labels j)), ?_⟩
    exact (hwhich ⟨r + j.val + 1, by omega⟩).mpr (by dsimp; omega)
  have hcomplete (z : criticalPoints E f)
      (haz : f q + (T.data q).radius ^ 2 < f z) (hzb : f z < b) :
      ∃ j, labels j = z := by
    obtain ⟨j, rfl⟩ := S.toSurgeryWindows.point.surjective z
    have hjbound := (hwhich j).mp hzb
    have hrj : r < j.val := S.toSurgeryWindows.point_strictMono.lt_iff_lt.mp
      ((T.toSurgeryWindows.value_lt_upper q).trans haz)
    refine ⟨⟨j.val - (r + 1), by omega⟩, ?_⟩
    apply congrArg S.toSurgeryWindows.point
    apply Fin.ext
    change r + (j.val - (r + 1)) + 1 = j.val
    omega
  exact cancel_from_complete_four_family T hf hm hdim q hindex hnull hprimitive hb
    m hprefix labels hp hvalues hcomplete B γ hγ hsurj

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

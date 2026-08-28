import Wikipedia.HopfProblem.DegreeCollapseOrderedFourFamily
import Wikipedia.HopfProblem.DegreeCollapseCanonicalFourFamily
import Wikipedia.HopfProblem.DegreeCollapseFourSectionSpanning

/-!
# Construct the actual surjective matrix of embedded index-four attaching spheres

The original three/four blocks supply the native H3 basis and the exact
critical labels. Construct a complete adapted flow and the whole disjoint
embedded immersive three-sphere family at the original cut. Restore every
original attaching parameter by exact flow transport. The resulting
geometric coordinate matrix is surjective from the actual terminal H3
vanishing, with no geometric family or matrix supplied as extra data.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_geometric_index_four_matrix_below_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    {b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    [Subsingleton (SingularHomology {y : M // f y ≤ b} 3)]
    (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hthree : S.toSurgeryWindows.HasIndexThreeBlock 0 r)
    (hfour : ThreeFourPresentation.HasIndexFourBlock S.toSurgeryWindows r n)
    (hcut : S.toSurgeryWindows.upper (S.toSurgeryWindows.point ⟨r + n, hn⟩) < b)
    (hwhich : ∀ i : Fin S.toSurgeryWindows.count,
      f (S.toSurgeryWindows.point i) < b ↔ i.val ≤ r + n) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    let p := nativeMiddleBlockPoint S r n hn
    let B := MiddleBasis.middleBasis S.toSurgeryWindows hf r (by omega) hthree
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius < (S.data z).radius) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
      (∀ z : criticalPoints E f, f z < b → T.toSurgeryWindows.upper z < b) ∧
      (∀ j, S.toSurgeryWindows.upper q < T.toSurgeryWindows.lower (p j)) ∧
      ∃ hp : ∀ j, nativeMorseIndex E f (p j) = 4,
      ∃ γ : Fin n → C(Hemisphere.Sphere 3, (S.data q).UpperLevel),
        IsNativeFourBasinFamily T hf (S.data q).upper_regular p (fun j => γ j) ∧
        (∀ j x, ∃ t : ℝ, T.flow t (nativeIndexFourAttachingSphere T (p j) (hp j) x).val =
          (γ j x).val) ∧ Surjective (canonicalFourMatrix B γ).mulVec := by
  let W := S.toSurgeryWindows
  have hnW : r + n < W.count := hn
  let q := W.point ⟨r, by omega⟩
  let p := nativeMiddleBlockPoint S r n hn
  let B := MiddleBasis.middleBasis W hf r (by omega) hthree
  have hupperS (z : criticalPoints E f) (hz : f z < b) : W.upper z < b := by
    obtain ⟨i, rfl⟩ := W.point.surjective z
    have hi : i ≤ (⟨r + n, hn⟩ : Fin W.count) := (hwhich i).mp hz
    rcases lt_or_eq_of_le hi with hlt | rfl
    · exact (W.separated _ _ (W.point_strictMono hlt)).trans
        ((W.lower_lt_value _).trans ((W.value_lt_upper _).trans hcut))
    · exact hcut
  have hp (j : Fin n) : nativeMorseIndex E f (p j) = 4 :=
    (nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hfour ⟨r + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  obtain ⟨T, hcharts, hradii, hgerms, α, hα⟩ := S.exists_ordered_index_four_family
    hf hm hdim r n hn hfour (fun z => (S.data z).radius) (fun z => (S.data z).radius_pos)
  have hupperT (z : criticalPoints E f) (hz : f z < b) :
      T.toSurgeryWindows.upper z < b := by
    have hh := mul_pos (sub_pos.mpr (hradii z))
      (add_pos (S.data z).radius_pos (T.data z).radius_pos)
    have hu : T.toSurgeryWindows.upper z < W.upper z := by
      change f z + (T.data z).radius ^ 2 < f z + (S.data z).radius ^ 2
      nlinarith
    exact hu.trans (hupperS z hz)
  have hbefore (j : Fin n) : W.upper q < T.toSurgeryWindows.lower (p j) := by
    have hqj : f q < f (p j) := W.point_strictMono (by change r < r + j.val + 1; omega)
    have hsep := W.separated q (p j) hqj
    have hh := mul_pos (sub_pos.mpr (hradii (p j)))
      (add_pos (S.data (p j)).radius_pos (T.data (p j)).radius_pos)
    change W.upper q < f (p j) - (T.data (p j)).radius ^ 2
    change W.upper q < f (p j) - (S.data (p j)).radius ^ 2 at hsep
    nlinarith
  obtain ⟨β, hβ, _, horbit⟩ := T.exists_canonical_four_family hf
    (S.data q).upper_regular p hp α hα
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let γ : Fin n → C(Hemisphere.Sphere 3, (S.data q).UpperLevel) :=
    fun j => ⟨β j, (hβ.1 j).continuous⟩
  exact ⟨T, hcharts, hradii, hgerms, hupperT, hbefore, hp, γ, hβ, horbit,
    canonical_four_matrix_surjective_below_cut S T hf hb r n hn hwhich
      hupperS hupperT hp hbefore B γ horbit⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

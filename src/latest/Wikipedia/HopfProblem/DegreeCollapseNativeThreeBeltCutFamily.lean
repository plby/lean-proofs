import Wikipedia.HopfProblem.DegreeCollapseRegularCutFourMatrixTransport
import Wikipedia.HopfProblem.DegreeCollapseLastThreePrimitiveCoordinate

/-!
# The actual whole four-handle family at its own flow's last three-belt level

The constructed family initially lies on the older upper cut. Smaller windows
leave a genuinely regular band to the new upper cut. Use the family's own
complete flow to transport it, retaining the exact matrix through literal
inclusion. The collapse coordinate and lower-level contractions now belong
to this very same adapted surgery system. No global ordering outside the
three/four prefix is required.
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

theorem exists_native_three_belt_cut_family
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) (r n : ℕ) (hrc : r + n < S.toSurgeryWindows.count)
    (hrpos : 0 < r) (hthree : S.toSurgeryWindows.HasIndexThreeBlock 0 r)
    (hcharts : ∀ z, (T.data z).chart = (S.data z).chart)
    (hradii : ∀ z, (T.data z).radius < (S.data z).radius) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    let a := nativeMiddleBaseCut S r n hrc
    let p := nativeMiddleBlockPoint S r n hrc
    ∀ (_hlower : ∀ j, a < T.toSurgeryWindows.lower (p j))
      (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ a} 3)
      (γ : Fin n → C(Hemisphere.Sphere 3, {y : M // f y = a})),
      IsNativeFourBasinFamily T hf (S.data q).upper_regular p (fun j => γ j) →
      Surjective (canonicalFourMatrix B γ).mulVec →
      ∃ hindex : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 3,
        Surjective (MiddleBasis.collapseCoordinate (T.data q) 1 hf.continuous hindex) ∧
        (∀ δ : C(Hemisphere.Sphere 1, (T.data q).LowerLevel),
          ∃ z, δ.Homotopic (ContinuousMap.const _ z)) ∧
        (∀ j, T.toSurgeryWindows.upper q < T.toSurgeryWindows.lower (p j)) ∧
        ∃ β : Fin n → C(Hemisphere.Sphere 3, (T.data q).UpperLevel),
          IsNativeFourBasinFamily T hf (T.data q).upper_regular p (fun j => β j) ∧
          (∀ j x, ∃ t : ℝ, T.flow t (γ j x).val = (β j x).val) ∧
          ∃ B' : (Fin r → ℤ) ≃ₗ[ℤ]
              SingularHomology {y : M // f y ≤ T.toSurgeryWindows.upper q} 3,
            canonicalFourMatrix B' β = canonicalFourMatrix B γ ∧
            Surjective (canonicalFourMatrix B' β).mulVec := by
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  let a := nativeMiddleBaseCut S r n hrc
  let p := nativeMiddleBlockPoint S r n hrc
  dsimp only
  intro hlower B γ hγ hsurj
  have hrT : r < T.toSurgeryWindows.count := by
    change r < S.toSurgeryWindows.count
    omega
  have hthreeT : T.toSurgeryWindows.HasIndexThreeBlock 0 r := by
    intro i hi hir
    rw [hcharts]
    exact hthree i hi hir
  obtain ⟨hindex, hprimitive, hnull⟩ :=
    last_index_three_collapse_is_primitive T.toSurgeryWindows hf hdim r hrT hrpos hthreeT
  have hba : T.toSurgeryWindows.upper q < a := by
    change f q + (T.data q).radius ^ 2 < f q + (S.data q).radius ^ 2
    have hh := hradii q
    nlinarith [(T.data q).radius_pos, (S.data q).radius_pos]
  have hband : ∀ y, f y ∈ Icc (T.toSurgeryWindows.upper q) a → y ∉ criticalPoints E f := by
    intro y hy hcrit
    have hqy : f q < f y := (T.toSurgeryWindows.value_lt_upper q).trans_le hy.1
    have heq : y = q.val := S.isolated q y hcrit
      ⟨((S.toSurgeryWindows.lower_lt_value q).trans hqy).le, hy.2⟩
    exact hqy.ne (congrArg f heq).symm
  have hnpos : 0 < n := by
    by_contra hnot
    obtain ⟨x, hx⟩ := hsurj 1
    have hh := congrFun hx ⟨0, hrpos⟩
    let _ : IsEmpty (Fin n) := ⟨fun j => by have hj := j.isLt; omega⟩
    simp only [Matrix.mulVec, dotProduct, Finset.univ_eq_empty,
      Finset.sum_empty, Pi.one_apply] at hh
    exact zero_ne_one hh
  let za := γ ⟨0, hnpos⟩ (Hemisphere.point true ⟨0, by simp⟩)
  obtain ⟨β, hβ, horbit, _, hmatrix, hsurj'⟩ := T.exists_lower_cut_geometric_four_matrix
    hf hba (S.data q).upper_regular (T.data q).upper_regular hband za p
      (fun j => (hlower j).trans (T.toSurgeryWindows.lower_lt_value (p j))) B γ hγ hsurj
  exact ⟨hindex, hprimitive, hnull, fun j => hba.trans (hlower j), β, hβ, horbit,
    B.trans (regularCutThreeHomologyEquiv hf hba.le hband).symm, hmatrix, hsurj'⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

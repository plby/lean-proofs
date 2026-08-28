import Wikipedia.HopfProblem.DegreeCollapseNativeThreeBeltCutFamily

/-!
# Construct the surjective geometric matrix at the actual three-belt cut

Assemble the full family construction, exact original parameter transport,
literal-inclusion basis transport, primitive native collapse coordinate, and
actual lower-level loop contractions. The matrix and the last three-belt
now belong to the same complete flow and surgery system. All hypotheses
concern the original below-cut three/four prefix.
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

theorem AdaptedSurgeryWindows.exists_native_three_belt_cut_matrix
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
    let p := nativeMiddleBlockPoint S r n hn
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius < (S.data z).radius) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
      (∀ z : criticalPoints E f, f z < b → T.toSurgeryWindows.upper z < b) ∧
      T.toSurgeryWindows.upper q < b ∧
      (∀ j, T.toSurgeryWindows.upper q < T.toSurgeryWindows.lower (p j)) ∧
      ∃ hindex : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 3,
        Surjective (MiddleBasis.collapseCoordinate (T.data q) 1 hf.continuous hindex) ∧
        (∀ δ : C(Hemisphere.Sphere 1, (T.data q).LowerLevel),
          ∃ z, δ.Homotopic (ContinuousMap.const _ z)) ∧
        ∃ hp : ∀ j, nativeMorseIndex E f (p j) = 4,
        ∃ B : (Fin r → ℤ) ≃ₗ[ℤ]
            SingularHomology {y : M // f y ≤ T.toSurgeryWindows.upper q} 3,
        ∃ γ : Fin n → C(Hemisphere.Sphere 3, (T.data q).UpperLevel),
          IsNativeFourBasinFamily T hf (T.data q).upper_regular p (fun j => γ j) ∧
          (∀ j x, ∃ t : ℝ, T.flow t
            (nativeIndexFourAttachingSphere T (p j) (hp j) x).val = (γ j x).val) ∧
          Surjective (canonicalFourMatrix B γ).mulVec := by
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  let p := nativeMiddleBlockPoint S r n hn
  let B₀ := MiddleBasis.middleBasis S.toSurgeryWindows hf r (by omega) hthree
  obtain ⟨T, hcharts, hradii, hgerms, hupper, hbefore, hp, γ₀, hγ₀, hcanon, hsurj⟩ :=
    S.exists_geometric_index_four_matrix_below_cut hf hm hdim hb r n hn
      hthree hfour hcut hwhich
  obtain ⟨hindex, hprimitive, hnull, hsep, γ, hγ, horbit, B, _, hsurj'⟩ :=
    exists_native_three_belt_cut_family S T hf hdim r n hn hrpos hthree
      hcharts hradii hbefore B₀ γ₀ hγ₀ hsurj
  have hqb : f q < b := (hwhich ⟨r, by omega⟩).mpr (by dsimp; omega)
  refine ⟨T, hcharts, hradii, hgerms, hupper, hupper q hqb, hsep,
    hindex, hprimitive, hnull, hp, B, γ, hγ, ?_, hsurj'⟩
  intro j x
  obtain ⟨s, hs⟩ := hcanon j x
  obtain ⟨t, ht⟩ := horbit j x
  refine ⟨t + s, ?_⟩
  rw [T.flow.map_add, hs]
  exact ht

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

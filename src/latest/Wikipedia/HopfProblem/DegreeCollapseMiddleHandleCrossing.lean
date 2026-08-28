import Wikipedia.HopfProblem.DegreeCollapseFullBeltCrossing

/-!
# A supported transverse crossing of the actual index-three Morse belt

The original signed Morse chart constructs the full belt chart, cutoff,
sheet position, and global native level isotopy. Its complete local-sheet
trace meets the whole original belt once and transversely. All support is
inside the prescribed open neighborhood of the chosen actual belt point.
Placing an existing attaching-sphere disk into this sheet is still separate.
-/

noncomputable section

open Set Function Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

theorem exists_supported_middle_belt_crossing (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by have h := (S.data q).chart.finrank_negative_add_positive
          have hi := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
          omega⟩
    ∀ U : Set (S.data q).UpperLevel, IsOpen U → (S.data q).surgery.beltSphere v ∈ U →
      ∃ Φ : PartialDiffeomorph
          𝓘(ℝ, (ℝ × EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2))
          𝓘(ℝ, RegularLevel.Model E)
          ((ℝ × EuclideanSpace ℝ (Fin 2)) × EuclideanSpace ℝ (Fin 2)) (S.data q).UpperLevel ∞,
        Φ 0 = (S.data q).surgery.beltSphere v ∧ Φ.target ⊆ U ∧
        ∃ a : ℝ, 0 < a ∧ beltCrossingSheet a (0 : EuclideanSpace ℝ (Fin 2)) ∈ Φ.source ∧
          ∃ (F : ℝ × (S.data q).UpperLevel → (S.data q).UpperLevel)
            (K : Set (S.data q).UpperLevel),
            IsCompact K ∧ K ⊆ U ∧
            ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, RegularLevel.Model E))
              𝓘(ℝ, RegularLevel.Model E) ∞ F ∧
            (∀ y, F (0, y) = y) ∧
            (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
              (S.data q).UpperLevel (S.data q).UpperLevel ∞, ∀ y, d y = F (t, y)) ∧
            (∀ t y, y ∉ K → F (t, y) = y) ∧
            (∀ t ∈ Icc (0 : ℝ) 1, ∀ w : EuclideanSpace ℝ (Fin 2),
              beltCrossingSheet a w ∈ Φ.source →
              ∀ y : sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
                (F (t, Φ (beltCrossingSheet a w)) = (S.data q).surgery.beltSphere y ↔
                  t = 1 / 2 ∧ w = 0 ∧ y = v)) ∧
            ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, RegularLevel.Model E) ∞
              (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
                F (p.1, Φ (beltCrossingSheet a p.2))) (1 / 2, 0) ∧
            NativeTransversality.At 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) (𝓡 2)
              𝓘(ℝ, RegularLevel.Model E)
              (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
                F (p.1, Φ (beltCrossingSheet a p.2))) (S.data q).surgery.beltSphere (1 / 2, 0) v := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  have hneg : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 3 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
  have hsplit := (S.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) := ⟨by omega⟩
  change ∀ U : Set (S.data q).UpperLevel, IsOpen U → (S.data q).surgery.beltSphere v ∈ U → _
  intro U hU hvU
  obtain ⟨Φ, h0, hcenter, hΦU, hrecognition, χ, hχ0, hχv, haxis⟩ :=
    exists_middle_belt_chart S hf hdim q hq v U hU hvU
  obtain ⟨a, ha, hs, F, K, hK, hKΦ, hF, hF0, hFd, hFfix, hcount, htrace, htrans⟩ :=
    exists_supported_full_belt_crossing Φ h0 (S.data q).surgery.beltSphere
      (S.data q).belt_isClosedEmbedding.injective hrecognition χ v hχv haxis
      ((S.data q).belt_smooth hf 2).contMDiffAt
      (χ.contMDiffOn_toFun.contMDiffAt (χ.open_source.mem_nhds hχ0))
  exact ⟨Φ, hcenter, hΦU, a, ha, hs, F, K, hK, hKΦ.trans hΦU,
    hF, hF0, hFd, hFfix, hcount, htrace, htrans⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

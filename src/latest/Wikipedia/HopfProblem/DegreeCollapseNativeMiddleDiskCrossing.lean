import Wikipedia.HopfProblem.DegreeCollapseGlobalCrossingDisk

/-!
# Constructed embedded disk crossing the whole original middle belt

In every prescribed open neighborhood of an actual index-three belt point,
construct an entire smooth embedded immersive disk and a compactly supported
native isotopy. The full disk trace meets the full belt exactly once and
transversely. No model disk, chart, cutoff, or motion is supplied as input.
-/

noncomputable section

open Set Function Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

theorem exists_native_middle_disk_crossing (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by have h := (S.data q).chart.finrank_negative_add_positive
          have hi := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
          omega⟩
    ∀ U : Set (S.data q).UpperLevel, IsOpen U → (S.data q).surgery.beltSphere v ∈ U →
      ∃ g : EuclideanSpace ℝ (Fin 2) → (S.data q).UpperLevel,
        ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g ∧ Injective g ∧
        (∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x)) ∧
        IsClosedEmbedding (fun x : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 => g x.val) ∧
        (∀ x, g x ∈ U) ∧
        ∃ (F : ℝ × (S.data q).UpperLevel → (S.data q).UpperLevel)
          (K : Set (S.data q).UpperLevel), IsCompact K ∧ K ⊆ U ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, RegularLevel.Model E))
            𝓘(ℝ, RegularLevel.Model E) ∞ F ∧
          (∀ y, F (0, y) = y) ∧
          (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
            (S.data q).UpperLevel (S.data q).UpperLevel ∞, ∀ y, d y = F (t, y)) ∧
          (∀ t y, y ∉ K → F (t, y) = y) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : EuclideanSpace ℝ (Fin 2),
            ∀ y : sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
              (F (t, g x) = (S.data q).surgery.beltSphere y ↔
                t = 1 / 2 ∧ x = 0 ∧ y = v)) ∧
          ContMDiff 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, RegularLevel.Model E) ∞
            (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => F (p.1, g p.2)) ∧
          NativeTransversality.At 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) (𝓡 2)
            𝓘(ℝ, RegularLevel.Model E)
            (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => F (p.1, g p.2))
            (S.data q).surgery.beltSphere (1 / 2, 0) v := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  have hneg : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 3 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
  have hsplit := (S.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) := ⟨by omega⟩
  change ∀ U : Set (S.data q).UpperLevel, IsOpen U → (S.data q).surgery.beltSphere v ∈ U → _
  intro U hU hvU
  obtain ⟨Φ, -, hΦU, a, -, hs, F, K, hK, hKU, hF, hF0, hFd, hFfix,
      hcount, htrace, htrans⟩ := exists_supported_middle_belt_crossing S hf hdim q hq v U hU hvU
  obtain ⟨g, hg, hgi, hgd, hclosed, -, hgt, hgc, hgs, htr⟩ :=
    exists_global_crossing_disk Φ a hs F hF (S.data q).surgery.beltSphere v hcount htrace htrans
  exact ⟨g, hg, hgi, hgd, hclosed, fun x => hΦU (hgt x),
    F, K, hK, hKU, hF, hF0, hFd, hFfix, hgc, hgs, htr⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

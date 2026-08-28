import Wikipedia.HopfProblem.DegreeCollapseOrderedMiddleLevelConnected
import Wikipedia.HopfProblem.DegreeCollapseAmbientDimensionalAvoidance
import Wikipedia.HopfProblem.DegreeCollapseSurgeryFlowBandBridge

/-!
# A constructed transverse passage of the actual next middle attaching sphere

For consecutive index-three critical points in the ordered native system,
construct the regular-band bridge along the original common flow. Ambient
avoidance prepares its actual transported attaching sphere. Connectedness
of the actual upper level supplies a path, and the full-sheet construction
gives one transverse passage through the actual preceding belt.

The preparatory isotopy and the passage are retained separately. This
theorem does not assert preservation of other handles during preparation,
or an attaching-class addition formula.
-/

noncomputable section

open Set Function Filter Metric Manifold Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_middle_attaching_passage
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    (hq : nativeMorseIndex E f q = 3) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
    let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
      ⟨(nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
    let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by have hsplit := (S.data p).chart.finrank_negative_add_positive
          have hn := (nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
          omega⟩
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ B : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data p).UpperLevel (S.data q).LowerLevel ∞,
        D '' {z : M | f z ≤ f p + (S.data p).radius ^ 2} =
          {z : M | f z ≤ f q - (S.data q).radius ^ 2} ∧
        (∀ z, (B z : M) = D z) ∧ (∀ z, ∃ t, S.flow t z = D z) ∧
        ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data p).UpperLevel (S.data p).UpperLevel ∞,
          IsotopicToIdentity e ∧
          let α := (S.data p).transportedAttachingSphere (S.data q) 2 B.toHomeomorph
          let a : Hemisphere.Sphere 2 → (S.data p).UpperLevel := e ∘ α
          ∃ (x : Hemisphere.Sphere 2)
            (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1),
            ∃ τ ∈ Ioo (0 : ℝ) 1,
              ∃ (F : ℝ × (S.data p).UpperLevel → (S.data p).UpperLevel)
                (K : Set (S.data p).UpperLevel),
                IsCompact K ∧
                ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, RegularLevel.Model E))
                  𝓘(ℝ, RegularLevel.Model E) ∞ F ∧
                (∀ z, F (0, z) = z) ∧
                (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, RegularLevel.Model E)
                    𝓘(ℝ, RegularLevel.Model E) (S.data p).UpperLevel (S.data p).UpperLevel ∞,
                  ∀ z, d z = F (t, z)) ∧
                (∀ t z, z ∉ K → F (t, z) = z) ∧
                (∀ t ∈ Icc (0 : ℝ) 1, ∀ u : Hemisphere.Sphere 2,
                  ∀ w : sphere (0 : (S.data p).chart.PositiveCoordinates) 1,
                    F (t, a u) = (S.data p).surgery.beltSphere w ↔
                      t = τ ∧ u = x ∧ w = v) ∧
                NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2)
                  𝓘(ℝ, RegularLevel.Model E)
                  (fun z : ℝ × Hemisphere.Sphere 2 => F (z.1, a z.2))
                  (S.data p).surgery.beltSphere (τ, x) v := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by have hsplit := (S.data p).chart.finrank_negative_add_positive
        have hn := (nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
        omega⟩
  obtain ⟨D, B, hsub, hB, horbit⟩ := S.exists_orbit_bandBridge hf p q hpq hconsecutive
  let α := (S.data p).transportedAttachingSphere (S.data q) 2 B.toHomeomorph
  have hα : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ α :=
    (S.data p).transportedAttachingSphere_smooth (S.data q) hf 2 B
  have hαi := (S.data p).transportedAttachingSphere_derivative_injective (S.data q) hf 2 B
  have hαe := (S.data p).transportedAttachingSphere_isClosedEmbedding (S.data q) 2 B.toHomeomorph
  have hbelt := (S.data p).belt_smooth hf 2
  have hleveldim : Module.finrank ℝ (RegularLevel.Model E) = 5 := by
    simp [RegularLevel.Model, hdim]
  obtain ⟨e, he, hdisj⟩ := MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension
    hα hbelt (by simp only [finrank_euclideanSpace_fin, hleveldim]; norm_num)
  let a : Hemisphere.Sphere 2 → (S.data p).UpperLevel := e ∘ α
  have ha : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ a := e.contMDiff.comp hα
  have hae : IsClosedEmbedding a := ha.continuous.isClosedEmbedding (e.injective.comp hαe.injective)
  have hai : ∀ u, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) a u) := by
    intro u
    rw [mfderiv_comp u (e.mdifferentiable (by simp) _) (hα.mdifferentiable (by simp) u)]
    exact ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (by trivial)).comp (hαi u)
  let x : Hemisphere.Sphere 2 := Hemisphere.point true ⟨0, by simp [DiskDouble.Disk]⟩
  let v := SphereCoordinates.standardParametrization (S.data p).chart.PositiveCoordinates 2 x
  let _ : PathConnectedSpace (S.data p).UpperLevel :=
    S.pathConnectedSpace_index_three_upper_level hf hdim horder p hp (a x)
  obtain ⟨τ, hτ, F, K, hK, hF, hF0, hFd, hFfix, hcount, htrans⟩ :=
    exists_supported_single_sheet_passage ha hbelt hae.isEmbedding
      (S.data p).belt_isClosedEmbedding.isEmbedding hai
      ((S.data p).belt_derivative_injective hf 2) hdisj hleveldim x v
      (PathConnectedSpace.somePath (a x) ((S.data p).surgery.beltSphere v))
  exact ⟨D, B, hsub, hB, horbit, e, he, x, v, τ, hτ, F, K,
    hK, hF, hF0, hFd, hFfix, hcount, htrans⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

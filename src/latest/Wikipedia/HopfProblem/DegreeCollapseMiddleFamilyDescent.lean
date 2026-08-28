import Wikipedia.HopfProblem.DegreeCollapseWholeFamilyAvoidance

/-!
# Move the original finite sheet family through one actual middle window

Prepare the entire family by one supported native level isotopy, realize
it by a complete descending flow with the original critical charts, and
transport the original parametrized sheets through the old window. The
new lower-level family is smooth, embedded, immersive and pairwise disjoint.
Its backward critical labels are exactly the original upper-level labels.
-/

noncomputable section

open Set Function Filter Metric Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open MorseRearrangement

local notation "S₂" => Hemisphere.Sphere 2
local notation "D₂" => EuclideanSpace ℝ (Fin 2)

variable {ι E M : Type} [Finite ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_middle_family_descent
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    (α : ι → S₂ → (S.data p).UpperLevel)
    {P : Set (S.data p).UpperLevel} (hP : IsClosed P)
    (hαP : ∀ j, Disjoint (range (α j)) P)
    (ε : criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
    (∀ j, Injective (α j)) →
    (∀ j x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
    Pairwise (fun i j => Disjoint (range (α i)) (range (α j))) →
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ q, (T.data q).chart = (S.data q).chart) ∧
      (∀ q, (T.data q).radius < ε q) ∧
      (∀ q ∈ criticalPoints E f, ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
      (∀ x : (S.data p).UpperLevel, ∀ q : M,
        Tendsto (fun t => T.flow t x.val) atBot (𝓝 q) ↔
          Tendsto (fun t => S.flow t x.val) atBot (𝓝 q)) ∧
      (∀ x ∈ P, range (fun t => T.flow t x.val) = range (fun t => S.flow t x.val)) ∧
      ∃ β : ι → S₂ → (S.data p).LowerLevel,
        (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (β j)) ∧
        (∀ j, IsClosedEmbedding (β j)) ∧
        (∀ j x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (β j) x)) ∧
        Pairwise (fun i j => Disjoint (range (β i)) (range (β j))) ∧
        (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (β j x).val) ∧
        ∀ j x q, Tendsto (fun t => T.flow t (β j x).val) atBot (𝓝 q) ↔
          Tendsto (fun t => S.flow t (α j x).val) atBot (𝓝 q) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by have hs := (S.data p).chart.finrank_negative_add_positive
        have hn := (nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
        omega⟩
  dsimp only
  intro hα hαinj hαimm hpair
  have hdim' : Module.finrank ℝ D₂ + Module.finrank ℝ D₂ <
      Module.finrank ℝ (RegularLevel.Model E) := by
    simp [RegularLevel.Model, hdim]
  obtain ⟨D, K, hK, -, ⟨A⟩, havoid⟩ :=
    exists_whole_family_avoidance α hα ((S.data p).belt_smooth hf 2) hdim' hP hαP
  let x₀ : S₂ := Hemisphere.point true ⟨0, by simp [DiskDouble.Disk]⟩
  let u := SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2 x₀
  let v := SphereCoordinates.standardParametrization (S.data p).chart.PositiveCoordinates 2 x₀
  obtain ⟨T, hcharts, hradii, hgerms, hback, hforward, hprotected⟩ :=
    S.exists_relative_level_surgery_system hf hm (S.data p).upper_regular
      ((S.data p).surgery.beltSphere v) ε hε D K P hK A
  have hreach (j : ι) (x : S₂) : (α j x).val ∈
      FlowCancellation.levelBasin T.flow f (S.toSurgeryWindows.lower p) := by
    apply S.reaches_old_lower_of_belt_avoidance T hf p D hforward (α j x)
    intro hx
    exact Set.disjoint_left.mp (havoid j) ⟨x, rfl⟩ hx
  obtain ⟨β, hβ, hβe, hβi, hβpair, horbit⟩ := T.exists_native_family_level_transport hf
    (S.data p).upper_regular (S.data p).lower_regular
    ((S.data p).surgery.beltSphere v) ((S.data p).surgery.attachingSphere u)
    α hα hαinj hαimm hpair hreach
  refine ⟨T, hcharts, hradii, hgerms, hback, hprotected, β, hβ, hβe, hβi, hβpair, horbit, ?_⟩
  intro j x q
  obtain ⟨t, ht⟩ := horbit j x
  rw [← ht]
  exact (flow_time_atBot_limit_iff T.flow t (α j x).val q).trans (hback (α j x) q)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

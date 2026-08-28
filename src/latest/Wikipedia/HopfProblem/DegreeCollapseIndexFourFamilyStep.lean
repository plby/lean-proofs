import Wikipedia.HopfProblem.DegreeCollapseTransportedBasinImage
import Wikipedia.HopfProblem.DegreeCollapseIndexFourFamilyDescent
import Wikipedia.HopfProblem.DegreeCollapseIndexFourSectionClass

/-!
# Add the original index-four attaching sphere to the descending family

The whole higher family crosses the native four-handle window. Transport
its original attaching three-sphere to the same lower cut and retain its
entire actual backward-basin image. Distinct original critical endpoints
make the enlarged family disjoint. All original sphere parameters, old
labels, critical germs, and the protected complete orbits are preserved.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_index_four_family_step
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 4)
    (n : ℕ) (α : Fin n → S₃ → (S.data p).UpperLevel)
    {P : Set (S.data p).UpperLevel} (hP : IsClosed P)
    (hαP : ∀ j, Disjoint (range (α j)) P)
    (ε : criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
    let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
    (∀ j, ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) →
    (∀ j, Injective (α j)) →
    (∀ j x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) (α j) x)) →
    Pairwise (fun i j => Disjoint (range (α i)) (range (α j))) →
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ q, (T.data q).chart = (S.data q).chart) ∧
      (∀ q, (T.data q).radius < ε q) ∧
      (∀ q ∈ criticalPoints E f, ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
      (∀ x : (S.data p).UpperLevel, ∀ q : M,
        Tendsto (fun t => T.flow t x.val) atBot (𝓝 q) ↔
          Tendsto (fun t => S.flow t x.val) atBot (𝓝 q)) ∧
      (∀ x ∈ P, range (fun t => T.flow t x.val) = range (fun t => S.flow t x.val)) ∧
      ∃ Γ : Fin (n + 1) → S₃ → (S.data p).LowerLevel,
        (∀ j, ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ (Γ j)) ∧
        (∀ j, IsClosedEmbedding (Γ j)) ∧
        (∀ j x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) (Γ j) x)) ∧
        Pairwise (fun i j => Disjoint (range (Γ i)) (range (Γ j))) ∧
        (∀ x, ∃ t : ℝ, T.flow t (nativeIndexFourAttachingSphere T p hp x).val = (Γ 0 x).val) ∧
        (∀ y : (S.data p).LowerLevel, y ∈ range (Γ 0) ↔
          Tendsto (fun t => T.flow t y.val) atBot (𝓝 p.val)) ∧
        (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (Γ j.succ x).val) ∧
        (∀ j x q, Tendsto (fun t => T.flow t (Γ j.succ x).val) atBot (𝓝 q) ↔
          Tendsto (fun t => S.flow t (α j x).val) atBot (𝓝 q)) ∧
        ∀ j q, S.toSurgeryWindows.upper p < f q →
          (∀ x : (S.data p).UpperLevel, x ∈ range (α j) ↔
            Tendsto (fun t => S.flow t x.val) atBot (𝓝 q)) →
          ∀ y : (S.data p).LowerLevel, y ∈ range (Γ j.succ) ↔
            Tendsto (fun t => T.flow t y.val) atBot (𝓝 q) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  dsimp only
  intro hα hαinj hαimm hpair
  obtain ⟨T, hcharts, hradii, hgerms, hback, hprotected, β, hβ, hβe, hβi, hβpair,
      horbit, hlabels⟩ :=
    S.exists_index_four_family_descent hf hm hdim p hp α hP hαP ε hε hα hαinj hαimm hpair
  let _ : Fact (Module.finrank ℝ (T.data p).chart.NegativeCoordinates = 3 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (T.data p).chart).symm.trans hp⟩
  have hgap (q : criticalPoints E f) (hqp : f q < f p) : f q < S.toSurgeryWindows.lower p :=
    (S.toSurgeryWindows.value_lt_upper q).trans (S.separated q p hqp)
  obtain ⟨γ, hγ, hγe, hγi, hγflow, hγrange⟩ := T.exists_native_attaching_lower_cut hf p 3
    (S.data p).lower_regular (S.toSurgeryWindows.lower_lt_value p) hgap
  have hdisj (j : Fin n) : Disjoint (range γ) (range (β j)) := by
    apply Set.disjoint_left.mpr
    intro z hzγ hzβ
    obtain ⟨x, hx⟩ := hzβ
    have hb := (hγrange z).mp hzγ
    rw [← hx] at hb
    exact S.not_backward_basin_on_upper_level hf p (α j x) ((hlabels j x p.val).mp hb)
  let Γ : Fin (n + 1) → S₃ → (S.data p).LowerLevel := Fin.cases γ β
  have hΓpair : Pairwise (fun i j => Disjoint (range (Γ i)) (range (Γ j))) := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hdisj j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (hdisj i).symm
      | succ j => exact hβpair (fun h => hij (congrArg Fin.succ h))
  refine ⟨T, hcharts, hradii, hgerms, hback, hprotected, Γ, ?_, ?_, ?_, hΓpair, hγflow,
    hγrange, horbit, hlabels, ?_⟩
  · intro j
    cases j using Fin.cases with
    | zero => exact hγ
    | succ j => exact hβ j
  · intro j
    cases j using Fin.cases with
    | zero => exact hγe
    | succ j => exact hβe j
  · intro j
    cases j using Fin.cases with
    | zero => exact hγi
    | succ j => exact hβi j
  · intro j q hq hfull
    apply T.transported_backward_basin_image hf
      ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p))
      (S.data p).lower_regular q hq (α j) (β j)
    · intro x
      exact (hfull x).trans (hback x q).symm
    · exact horbit j

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

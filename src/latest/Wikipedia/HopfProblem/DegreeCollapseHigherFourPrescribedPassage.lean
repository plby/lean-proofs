import Wikipedia.HopfProblem.DegreeCollapseHigherFourFamily
import Wikipedia.HopfProblem.DegreeCollapseHigherFamilyPassage
import Wikipedia.HopfProblem.DegreeCollapseThreeFourLevelPaths
import Wikipedia.HopfProblem.DegreeCollapseFiniteFourPrescribedPassage

/-!
# A prescribed-sign passage of the actual higher four-handle family

Lift the original common-cut sphere parameters to the selected upper level.
Their old orbit formulas already imply belt avoidance. A centered passage
with the requested coefficient fixes the entire remaining lifted family.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology MorseRearrangement

local notation "P₄" => EuclideanSpace ℝ (Fin 4)
local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_higher_four_family_prescribed_passage
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 4)
    (hprefix : ∀ j : Fin S.toSurgeryWindows.count, 0 < j.val →
      f (S.toSurgeryWindows.point j) ≤ f q →
      Module.finrank ℝ (S.data (S.toSurgeryWindows.point j)).chart.NegativeCoordinates = 3 ∨
      Module.finrank ℝ (S.data (S.toSurgeryWindows.point j)).chart.NegativeCoordinates = 4)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f) (haq : a < f q)
    {n : ℕ} (p : Fin n → criticalPoints E f) (i : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C(S₃, {y : M // f y = a}))
    (hα : IsNativeFourBasinFamily S hf ha p (fun j => α j))
    (k : ℤ) (hk : k = 1 ∨ k = -1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by have hsplit := (S.data q).chart.finrank_negative_add_positive
          have hn := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
          omega⟩
    let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 3 + 1) :=
      ⟨(nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
    ∃ β : Fin n → C(S₃, (S.data q).UpperLevel),
      IsNativeFourBasinFamily S hf (S.data q).upper_regular p (fun j => β j) ∧
      (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
      (∀ j, Disjoint (range (β j)) (range (S.data q).surgery.beltSphere)) ∧
      ∃ (x : S₃) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1),
        ∃ A : CenteredSheetPassage (RegularLevel.Model E) (β i)
            (S.data q).surgery.beltSphere x v (otherSheetImages (fun j => β j) i),
          ∃ L : P₄ ≃L[ℝ] (S.data q).chart.NegativeCoordinates,
            HasFDerivAt (fun z : P₄ => (S.data q).beltNormal (A.family
              ((sphereRadialParameterChart 3 (1 / 2) x z).1,
                β i (sphereRadialParameterChart 3 (1 / 2) x z).2)))
              L.toContinuousLinearMap 0 ∧
            singularHomologyMap
              (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 3 =
              k • singularHomologyMap ((SphereCoordinates.standardParametrization
                (S.data q).chart.NegativeCoordinates 3).toHomeomorph :
                  C(S₃, sphere (0 : (S.data q).chart.NegativeCoordinates) 1)) 3 := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let _ : CompactSpace (S.data q).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by have hsplit := (S.data q).chart.finrank_negative_add_positive
        have hn := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
        omega⟩
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 3 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  obtain ⟨β₀, hβ₀, horbit₀⟩ := S.exists_higher_four_family hf
    (haq.trans (S.toSurgeryWindows.value_lt_upper q)) ha (S.data q).upper_regular p i hp hhigh α hα
  let β : Fin n → C(S₃, (S.data q).UpperLevel) := β₀
  have hβ : IsNativeFourBasinFamily S hf (S.data q).upper_regular p (fun j => β j) := hβ₀
  have horbit : ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := horbit₀
  have hdisj (j : Fin n) : Disjoint (range (β j)) (range (S.data q).surgery.beltSphere) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ hy
    exact S.upper_point_not_on_belt_of_lower_orbit hf q haq (α j x) (β j x) (horbit j x) hy
  let x : S₃ := Hemisphere.point true ⟨0, by simp⟩
  let v := SphereCoordinates.standardParametrization (S.data q).chart.PositiveCoordinates 2
    (Hemisphere.point true ⟨0, by simp⟩)
  have hv : (S.data q).surgery.beltSphere v ∉ otherSheetImages (fun j => β j) i := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact Set.disjoint_left.mp (hdisj j.val) hj (mem_range_self v)
  let _ : PathConnectedSpace (S.data q).UpperLevel :=
    { nonempty := ⟨β i x⟩
      joined := S.toSurgeryWindows.upper_joined_of_three_four_before hf hdim q hprefix }
  obtain ⟨A, L, hL, hunit⟩ := exists_native_four_prescribed_finite_family_passage (S.data q) hf hdim
    β hβ.2.2.2.1 i (hβ.2.1 i).isEmbedding (hdisj i) x v hv
    (PathConnectedSpace.somePath (β i x) ((S.data q).surgery.beltSphere v)) k hk hβ.1 (hβ.2.2.1 i)
  exact ⟨β, hβ, horbit, hdisj, x, v, A, L, hL, hunit⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

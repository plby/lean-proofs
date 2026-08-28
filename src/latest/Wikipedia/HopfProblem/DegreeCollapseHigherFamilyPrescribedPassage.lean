import Wikipedia.HopfProblem.DegreeCollapseHigherFamilyPassage
import Wikipedia.HopfProblem.DegreeCollapseFiniteFamilyPrescribedPassage

/-!
# A prescribed-sign passage of the actual higher middle family

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

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_higher_family_prescribed_passage
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f) (haq : a < f q)
    {n : ℕ} (p : Fin n → criticalPoints E f) (i : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C(S₂, {y : M // f y = a}))
    (hα : IsNativeMiddleBasinFamily S hf ha p (fun j => α j))
    (k : ℤ) (hk : k = 1 ∨ k = -1) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by have hsplit := (S.data q).chart.finrank_negative_add_positive
          have hn := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
          omega⟩
    let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
      ⟨(nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
    ∃ β : Fin n → C(S₂, (S.data q).UpperLevel),
      IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => β j) ∧
      (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
      (∀ j, Disjoint (range (β j)) (range (S.data q).surgery.beltSphere)) ∧
      ∃ (x : S₂) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1),
        ∃ A : CenteredSheetPassage (RegularLevel.Model E) (β i)
            (S.data q).surgery.beltSphere x v (otherSheetImages (fun j => β j) i),
          ∃ L : P₃ ≃L[ℝ] (S.data q).chart.NegativeCoordinates,
            HasFDerivAt (fun z : P₃ => (S.data q).beltNormal (A.family
              ((radialParameterChart (1 / 2) x z).1, β i (radialParameterChart (1 / 2) x z).2)))
              L.toContinuousLinearMap 0 ∧
            singularHomologyMap (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
              k • singularHomologyMap ((SphereCoordinates.standardParametrization
                (S.data q).chart.NegativeCoordinates 2).toHomeomorph :
                  C(S₂, sphere (0 : (S.data q).chart.NegativeCoordinates) 1)) 2 := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let _ : CompactSpace (S.data q).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by have hsplit := (S.data q).chart.finrank_negative_add_positive
        have hn := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
        omega⟩
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  obtain ⟨β₀, hβ₀, horbit₀⟩ := S.exists_higher_middle_family hf
    (haq.trans (S.toSurgeryWindows.value_lt_upper q)) ha (S.data q).upper_regular p i hp hhigh α hα
  let β : Fin n → C(S₂, (S.data q).UpperLevel) := β₀
  have hβ : IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => β j) := hβ₀
  have horbit : ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := horbit₀
  have hdisj (j : Fin n) : Disjoint (range (β j)) (range (S.data q).surgery.beltSphere) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ hy
    exact S.upper_point_not_on_belt_of_lower_orbit hf q haq (α j x) (β j x) (horbit j x) hy
  let x : S₂ := Hemisphere.point true ⟨0, by simp⟩
  let v := SphereCoordinates.standardParametrization (S.data q).chart.PositiveCoordinates 2 x
  have hv : (S.data q).surgery.beltSphere v ∉ otherSheetImages (fun j => β j) i := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact Set.disjoint_left.mp (hdisj j.val) hj (mem_range_self v)
  let _ : PathConnectedSpace (S.data q).UpperLevel :=
    S.pathConnectedSpace_index_three_upper_level hf hdim horder q hq (β i x)
  obtain ⟨A, L, hL, hunit⟩ := exists_native_prescribed_finite_family_passage (S.data q) hf hdim
    β hβ.2.2.2.1 i (hβ.2.1 i).isEmbedding (hdisj i) x v hv
    (PathConnectedSpace.somePath (β i x) ((S.data q).surgery.beltSphere v)) k hk hβ.1 (hβ.2.2.1 i)
  exact ⟨β, hβ, horbit, hdisj, x, v, A, L, hL, hunit⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

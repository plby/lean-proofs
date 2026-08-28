import Wikipedia.HopfProblem.DegreeCollapseCoreInclusionEquivalence

/-!
# The index-three relation for literal inclusions of native sublevels

Transport the actual core-cell exact sequence through the inclusion
homotopy equivalence, not through a chosen attachment homeomorphism.
The resulting ordinary inclusion is surjective on second homology and
its kernel is exactly the span of the original native attaching class.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_core_inclusion_homology_comparison
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (k : ℕ) :
    ∃ A : SingularHomology
        ↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ range (S.data p).coreMap) k ≃ₗ[ℤ]
        SingularHomology {y : M // f y ≤ S.toSurgeryWindows.upper p} k,
      ∀ a, A (((S.data p).coreCellPresentation hf.continuous).oldHomologyMap k
        ((S.data p).cellOldHomologyEquiv hf.continuous k a)) =
        singularHomologyMap (sublevelMap f
          ((S.toSurgeryWindows.lower_lt_value p).trans
            (S.toSurgeryWindows.value_lt_upper p)).le) k a := by
  obtain ⟨B, hB⟩ := S.exists_native_core_inclusion_equiv hf p
  let d := S.data p
  let A := homotopyEquivHomologyEquiv B k
  let old := (⟨Subtype.val, continuous_subtype_val⟩ : C((d.coreCellPresentation hf.continuous).old,
    ↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ range d.coreMap)))
  have hmaps : (B.toFun.comp old).comp
      (d.cellOldHomeomorph hf.continuous).toHomotopyEquiv.toFun =
      sublevelMap f ((S.toSurgeryWindows.lower_lt_value p).trans
        (S.toSurgeryWindows.value_lt_upper p)).le := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hB _)
  refine ⟨A, ?_⟩
  intro a
  change singularHomologyMap B.toFun k
    (singularHomologyMap old k (singularHomologyMap
      (d.cellOldHomeomorph hf.continuous).toHomotopyEquiv.toFun k a)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp, hmaps]
  rfl

theorem AdaptedSurgeryWindows.native_sublevel_inclusion_exact
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range ((S.data p).coreBoundaryHomologyMap k) =
      LinearMap.ker (singularHomologyMap (sublevelMap f
        ((S.toSurgeryWindows.lower_lt_value p).trans
          (S.toSurgeryWindows.value_lt_upper p)).le) k) := by
  obtain ⟨A, hA⟩ := S.exists_core_inclusion_homology_comparison hf p k
  let d := S.data p
  refine HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
    (d.cellOldHomologyEquiv hf.continuous k).symm A
    ((d.coreCellPresentation hf.continuous).attachingHomologyMap k)
    ((d.coreCellPresentation hf.continuous).oldHomologyMap k)
    (d.coreBoundaryHomologyMap k) _ ?_ ?_
    ((d.coreCellPresentation hf.continuous).cell_exact_at_old k hk)
  · intro a
    change d.coreBoundaryHomologyMap k a =
      (d.cellOldHomologyEquiv hf.continuous k).symm
        ((d.coreCellPresentation hf.continuous).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]
  · intro a
    have hh := hA ((d.cellOldHomologyEquiv hf.continuous k).symm a)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh.symm

theorem AdaptedSurgeryWindows.native_index_three_inclusion_relation
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3) :
    let I := singularHomologyMap (sublevelMap f
      ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le) 2
    Surjective I ∧ LinearMap.ker I = Submodule.span ℤ
      {(S.data p).indexThreeAttachingClass
        ((nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp)} := by
  let d := S.data p
  have hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3 :=
    (nativeMorseIndex_eq_chart d.chart).symm.trans hp
  let _ : Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 1) :=
    d.attachingHomology_subsingleton_of_index 1 one_ne_zero (by omega) (by omega)
  have hsurj : Surjective ((d.coreCellPresentation hf.continuous).oldHomologyMap 2) := by
    intro a
    have ha : a ∈ LinearMap.ker ((d.coreCellPresentation hf.continuous).cellConnectingMap 1) :=
      Subsingleton.elim _ _
    rw [← (d.coreCellPresentation hf.continuous).cell_exact_at_ambient 1] at ha
    exact ha
  obtain ⟨A, hA⟩ := S.exists_core_inclusion_homology_comparison hf p 2
  constructor
  · intro a
    obtain ⟨x, hx⟩ := hsurj (A.symm a)
    refine ⟨(d.cellOldHomologyEquiv hf.continuous 2).symm x, ?_⟩
    have hh := hA ((d.cellOldHomologyEquiv hf.continuous 2).symm x)
    rw [LinearEquiv.apply_symm_apply, hx, LinearEquiv.apply_symm_apply] at hh
    exact hh.symm
  · rw [← S.native_sublevel_inclusion_exact hf p 2 (by decide), d.coreBoundary_two_range hindex]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

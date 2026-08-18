/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section91CoordinateBodyGeometry
import ErdosProblems.Erdos186.CFP.Bilu.Section91GenericSharpProduct

/-!
# The sharp normalized section gauge

The full intersection lattice of `coordinateC0` is used as coordinates.
In those coordinates the gauge of `2 • coordinateB0` contains all source
differences, has a full independent integral family, and its volume is the
section volume divided by the lattice covolume.
-/

namespace Erdos186.CFP.Bilu.Section91GenericSharpSection

open scoped ENNReal Pointwise RealInnerProductSpace Topology
open MeasureTheory Set Module Submodule Filter
open CFP.BiluFreiman Mahler MinkowskiSecond
open Proposition75Data Proposition75Case2 Proposition75Case2Construction
open Proposition75Case2Branch SubspaceLattice
open Section8PresentationNormalization Section9NormalizedReplacement
open Section91InitialPresentation.InitialPresentation
open Section91InitialCoordinates.InitialPresentation
open Section91CoveringEnlargement
open Section91CoordinateBodyGeometry Section91GenericSharpProduct
open Section92PresentationDescent

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ} (X : RankedBodyPresentation A)
  {r : ℕ} {a : Fin r → EuclideanSpace ℝ (Fin X.1)}
  {D : GeometricData (normalizedEuclideanBody X) a}
  {coverConstant sigma : ℕ} {constant scale : ENNReal}

variable
  (N : CoveredNormalizedReplacement (D := D)
    (K := normalizedLiftSet X) (coverConstant := coverConstant)
    constant scale sigma)

/-- Discreteness of the full coordinate intersection lattice, obtained
from a saturated presentation. -/
noncomputable def coordinateIntegralPointsDiscreteTopology :
    DiscreteTopology (integralPoints (coordinateC0 D)) := by
  classical
  obtain ⟨presentationRank, P, hSat⟩ :=
    exists_saturatedPresentation_coordinateC0 D
  letI hdiscRow : DiscreteTopology P.rowLattice := by
    change DiscreteTopology
      (Submodule.span ℤ (Set.range P.rowBasis))
    infer_instance
  exact hSat ▸ hdiscRow

/-- The chosen integral section basis promoted to a real basis. -/
noncomputable def coordinateSectionRealBasis :
    Basis (Fin (finrank ℝ D.C0)) ℝ (coordinateC0 D) := by
  classical
  letI : DiscreteTopology (integralPoints (coordinateC0 D)) :=
    coordinateIntegralPointsDiscreteTopology (D := D)
  letI : IsZLattice ℝ (integralPoints (coordinateC0 D)) :=
    ⟨span_coordinateIntegralPoints_eq_top D⟩
  exact (coordinateIntegralBasis (D := D)).ofZLatticeBasis ℝ
    (integralPoints (coordinateC0 D))

/-- Real coordinates of a lattice point are the real embeddings of its
integral coordinates. -/
theorem coordinateSectionRealBasis_equivFun_latticePoint
    (q : integralPoints (coordinateC0 D)) :
    (coordinateSectionRealBasis (D := D)).equivFun
        (q : coordinateC0 D) =
      integralEmbed ((coordinateIntegralBasis (D := D)).equivFun q) := by
  classical
  letI : DiscreteTopology (integralPoints (coordinateC0 D)) :=
    coordinateIntegralPointsDiscreteTopology (D := D)
  letI : IsZLattice ℝ (integralPoints (coordinateC0 D)) :=
    ⟨span_coordinateIntegralPoints_eq_top D⟩
  ext i
  change ((coordinateSectionRealBasis (D := D)).repr
      (q : coordinateC0 D)) i =
    (((coordinateIntegralBasis (D := D)).equivFun q) i : ℝ)
  unfold coordinateSectionRealBasis
  exact (coordinateIntegralBasis (D := D)).ofZLatticeBasis_repr_apply
    ℝ (integralPoints (coordinateC0 D)) q i

theorem coordinateSectionRealBasis_equivFun_sourceLatticePoint
    (q : D.latticePoints) :
    (coordinateSectionRealBasis (D := D)).equivFun
        (coordinateC0Equiv D (q : D.C0)) =
      integralEmbed
        ((coordinateIntegralBasis (D := D)).equivFun
          (coordinateLatticeEquiv D q)) := by
  rw [← coordinateLatticeEquiv_coe D q]
  exact coordinateSectionRealBasis_equivFun_latticePoint
    (X := X) (coordinateLatticeEquiv D q)

/-- The doubled section in literal standard lattice coordinates. -/
def sharpCoordinateBody :
    Set (Fin (finrank ℝ D.C0) → ℝ) :=
  (coordinateSectionRealBasis (D := D)).equivFun ''
    ((2 : ℝ) • coordinateB0 D)

theorem balanced_sharpCoordinateBody :
    Balanced ℝ (sharpCoordinateBody (D := D)) := by
  apply balanced_iff_smul_mem.mpr
  intro c hc y hy
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨c • z, ?_, map_smul _ _ _⟩
  exact ((balanced_normalized_coordinateB0 X D).smul (2 : ℝ)).smul_mem hc hz

theorem convex_sharpCoordinateBody :
    Convex ℝ (sharpCoordinateBody (D := D)) := by
  exact ((convex_normalized_coordinateB0 X D).smul (2 : ℝ)).linear_image
    (coordinateSectionRealBasis (D := D)).equivFun.toLinearMap

theorem isCompact_sharpCoordinateBody :
    IsCompact (sharpCoordinateBody (D := D)) := by
  exact ((isCompact_normalized_coordinateB0 X D).smul (2 : ℝ)).image
    (coordinateSectionRealBasis (D := D)).equivFun.toLinearMap.continuous_of_finiteDimensional

theorem sharpCoordinateBody_mem_nhds_zero :
    sharpCoordinateBody (D := D) ∈ 𝓝 0 := by
  let e := (coordinateSectionRealBasis (D := D)).equivFun
  have hsource : coordinateB0 D ∈ 𝓝 (0 : coordinateC0 D) :=
    mem_interior_iff_mem_nhds.mp
      (zero_mem_interior_normalized_coordinateB0 X D)
  have hopen : IsOpenMap e :=
    e.toLinearMap.isOpenMap_of_finiteDimensional e.surjective
  have himage : e '' coordinateB0 D ∈ 𝓝 (0 : Fin (finrank ℝ D.C0) → ℝ) := by
    simpa only [map_zero] using hopen.image_mem_nhds hsource
  apply Filter.mem_of_superset himage
  exact Set.image_mono
    ((balanced_normalized_coordinateB0 X D).subset_smul (by norm_num))

/-- The Minkowski functional of the doubled normalized section. -/
def genericSharpSectionSeminorm :
    Seminorm ℝ (Fin (finrank ℝ D.C0) → ℝ) :=
  gaugeSeminorm (balanced_sharpCoordinateBody (D := D) X)
    (convex_sharpCoordinateBody (D := D) X)
    (absorbent_nhds_zero
      (sharpCoordinateBody_mem_nhds_zero (D := D) X))

theorem unitBall_genericSharpSectionSeminorm :
    {x | genericSharpSectionSeminorm (D := D) X x ≤ 1} =
      sharpCoordinateBody (D := D) := by
  ext x
  change gauge (sharpCoordinateBody (D := D)) x ≤ 1 ↔
    x ∈ sharpCoordinateBody (D := D)
  rw [gauge_le_one_iff_mem_closure
    (convex_sharpCoordinateBody (D := D) X)
    (sharpCoordinateBody_mem_nhds_zero (D := D) X)]
  rw [(isCompact_sharpCoordinateBody (D := D) X).isClosed.closure_eq]

theorem genericSharpSectionSeminorm_definite :
    IsDefinite (genericSharpSectionSeminorm (D := D) X) := by
  apply isDefinite_gaugeSeminorm
    (balanced_sharpCoordinateBody (D := D) X)
    (convex_sharpCoordinateBody (D := D) X)
    (absorbent_nhds_zero
      (sharpCoordinateBody_mem_nhds_zero (D := D) X))
  exact NormedSpace.isVonNBounded_of_isBounded ℝ
    (isCompact_sharpCoordinateBody (D := D) X).isBounded

/-- Every difference used in the Ruzsa cover lies in the doubled section
gauge ball. -/
theorem genericSharpSectionSeminorm_difference_mem
    (x : {x // x ∈ N.normalized.seed.sourceSlice})
    (y : {y // y ∈ N.normalized.seed.sourceSlice}) :
    genericSharpSectionSeminorm (D := D) X
        (integralEmbed
          ((coordinateIntegralBasis (D := D)).equivFun
            (coordinateLatticeEquiv D
              (Lemma45SectionSeed.differenceLift
                N.normalized.seed x y)))) ≤ 1 := by
  let q : D.latticePoints :=
    Lemma45SectionSeed.differenceLift N.normalized.seed x y
  have hsource : (N.normalized.seed.embed x -
      N.normalized.seed.embed y : D.C0) ∈ (2 : ℝ) • D.B0 :=
    Section7PlaneSeed.sub_mem_two_smul_of_balanced_convex
      (balanced_B0 (balanced_normalizedEuclideanBody X) D)
      (convex_B0 (convex_normalizedEuclideanBody X) D)
      (N.normalized.seed.embed_body x)
      (N.normalized.seed.embed_body y)
  have hcoord : coordinateC0Equiv D (q : D.C0) ∈
      (2 : ℝ) • coordinateB0 D := by
    obtain ⟨w, hw, hwEq⟩ := hsource
    refine ⟨coordinateC0Equiv D w, ⟨w, hw, rfl⟩, ?_⟩
    calc
      2 • coordinateC0Equiv D w =
          coordinateC0Equiv D (2 • w) :=
        (map_smul (coordinateC0Equiv D) 2 w).symm
      _ = coordinateC0Equiv D
          (N.normalized.seed.embed x - N.normalized.seed.embed y) :=
        congrArg (coordinateC0Equiv D) hwEq
      _ = coordinateC0Equiv D (q : D.C0) := rfl
  have hbody :
      (coordinateSectionRealBasis (D := D)).equivFun
          (coordinateC0Equiv D (q : D.C0)) ∈
        sharpCoordinateBody (D := D) :=
    ⟨coordinateC0Equiv D (q : D.C0), hcoord, rfl⟩
  rw [coordinateSectionRealBasis_equivFun_sourceLatticePoint] at hbody
  change gauge (sharpCoordinateBody (D := D))
    (integralEmbed
      ((coordinateIntegralBasis (D := D)).equivFun
        (coordinateLatticeEquiv D q))) ≤ 1
  exact gauge_le_one_of_mem hbody

/-- The lattice points already lying in `B0` span `C0` by
`GeometricData.spans`; choosing a maximal independent subfamily gives a
full integral family in the sharp coordinates. -/
theorem genericSharpSectionSeminorm_admitsIndependent :
    AdmitsIndependent (genericSharpSectionSeminorm (D := D) X)
      (finrank ℝ D.C0) 1 := by
  classical
  let T : Set D.C0 := D.B0 ∩ (D.latticePoints : Set D.C0)
  obtain ⟨f, hfRange, _hfSpan, hfLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ T
  have hTspan : Submodule.span ℝ T = ⊤ := D.spans
  have hdim : finrank ℝ (Submodule.span ℝ T) = finrank ℝ D.C0 := by
    rw [hTspan, finrank_top]
  let e : Fin (finrank ℝ D.C0) ≃
      Fin (finrank ℝ (Submodule.span ℝ T)) :=
    finCongr hdim.symm
  let q : Fin (finrank ℝ D.C0) → D.latticePoints := fun i ↦
    ⟨f (e i), (hfRange (e i)).2⟩
  let v : Fin (finrank ℝ D.C0) → IntegralPoint (finrank ℝ D.C0) :=
    fun i ↦ (coordinateIntegralBasis (D := D)).equivFun
      (coordinateLatticeEquiv D (q i))
  refine ⟨v, ?_, ?_⟩
  · let F : (Fin (finrank ℝ D.C0) → ℝ) →ₗ[ℝ] D.C0 :=
      (coordinateC0Equiv D).symm.toLinearMap.comp
        (coordinateSectionRealBasis (D := D)).equivFun.symm.toLinearMap
    apply LinearIndependent.of_comp F
    have hfLI' : LinearIndependent ℝ (fun i ↦ f (e i)) :=
      hfLI.comp e e.injective
    convert hfLI' using 1
    funext i
    change F (integralEmbed (v i)) = f (e i)
    have hreal := coordinateSectionRealBasis_equivFun_sourceLatticePoint
      (X := X) (q i)
    change (coordinateSectionRealBasis (D := D)).equivFun
        (coordinateC0Equiv D ((q i : D.latticePoints) : D.C0)) =
      integralEmbed (v i) at hreal
    have hreal' := congrArg
      (coordinateSectionRealBasis (D := D)).equivFun.symm hreal
    rw [(coordinateSectionRealBasis (D := D)).equivFun.symm_apply_apply]
      at hreal'
    simp only [F, LinearMap.comp_apply]
    change (coordinateC0Equiv D).symm
      ((coordinateSectionRealBasis (D := D)).equivFun.symm
        (integralEmbed (v i))) = f (e i)
    rw [← hreal', (coordinateC0Equiv D).symm_apply_apply]
  · intro i
    have hcoord : coordinateC0Equiv D ((q i : D.latticePoints) : D.C0) ∈
        coordinateB0 D :=
      ⟨f (e i), (hfRange (e i)).1, rfl⟩
    have hdouble : coordinateC0Equiv D
        ((q i : D.latticePoints) : D.C0) ∈
        (2 : ℝ) • coordinateB0 D :=
      (balanced_normalized_coordinateB0 X D).subset_smul (by norm_num) hcoord
    have hbody :
        (coordinateSectionRealBasis (D := D)).equivFun
            (coordinateC0Equiv D ((q i : D.latticePoints) : D.C0)) ∈
          sharpCoordinateBody (D := D) :=
      ⟨coordinateC0Equiv D ((q i : D.latticePoints) : D.C0),
        hdouble, rfl⟩
    rw [coordinateSectionRealBasis_equivFun_sourceLatticePoint] at hbody
    change gauge (sharpCoordinateBody (D := D)) (integralEmbed (v i)) ≤ 1
    exact gauge_le_one_of_mem hbody

/-- The standard-coordinate body has exactly the expected normalized
section volume. -/
theorem volume_sharpCoordinateBody :
    volume (sharpCoordinateBody (D := D)) =
      (2 : ENNReal) ^ finrank ℝ D.C0 *
        (volume (coordinateB0 D) /
          ENNReal.ofReal
            (ZLattice.covolume (integralPoints (coordinateC0 D)))) := by
  classical
  letI : DiscreteTopology (integralPoints (coordinateC0 D)) :=
    coordinateIntegralPointsDiscreteTopology (D := D)
  letI : IsZLattice ℝ (integralPoints (coordinateC0 D)) :=
    ⟨span_coordinateIntegralPoints_eq_top D⟩
  have h := ZLattice.volume_image_eq_volume_div_covolume'
    (integralPoints (coordinateC0 D))
    (coordinateIntegralBasis (D := D))
    ((isCompact_normalized_coordinateB0 X D).smul (2 : ℝ)
      |>.measurableSet.nullMeasurableSet)
  change volume (sharpCoordinateBody (D := D)) = _
  rw [sharpCoordinateBody]
  rw [show (coordinateIntegralBasis (D := D)).ofZLatticeBasis ℝ
      (integralPoints (coordinateC0 D)) =
        coordinateSectionRealBasis (D := D) by
    rfl] at h
  rw [h, volume.addHaar_smul]
  simp only [finrank_coordinateC0]
  rw [abs_of_nonneg (by positivity),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  rw [mul_div_assoc]

/-- The normalized section itself supplies all of the sharp analytic data
needed by the generic product construction. -/
theorem exists_genericSharpSectionData :
    Nonempty (GenericSharpSectionData X N) := by
  refine ⟨{
    seminorm := genericSharpSectionSeminorm (D := D) X
    definite := genericSharpSectionSeminorm_definite (D := D) X
    full := genericSharpSectionSeminorm_admitsIndependent (D := D) X
    difference_mem := genericSharpSectionSeminorm_difference_mem X N
    volume_le := ?_
  }⟩
  rw [unitBall_genericSharpSectionSeminorm (D := D) X,
    volume_sharpCoordinateBody (D := D) X]

#print axioms genericSharpSectionSeminorm_admitsIndependent
#print axioms volume_sharpCoordinateBody
#print axioms exists_genericSharpSectionData

end

end Erdos186.CFP.Bilu.Section91GenericSharpSection

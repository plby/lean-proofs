import Wikipedia.HopfProblem.DegreeCollapseDualPrimitive
import Wikipedia.HopfProblem.DegreeCollapsePrimitiveClassSplit
import Wikipedia.HopfProblem.DegreeCollapseSurgeryMiddleSplit
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A single framed geometric dual splits off two integral middle summands

The original attaching sphere and an actual second framed face meet in
exactly one transverse pair. Viewed in one direction, the intersection
constructs a primitive functional on the original attaching class. Viewed
in the other, it kills the native surgery belt. The two proved splittings
therefore identify original H3 with new H3 plus two copies of the integers.
The exact numerical formula records its finiteness and freeness hypotheses.
For the strict decrease needed in an induction, finite generation of the
original H3 alone suffices; no freeness of the new H3 is assumed. Existence
of the geometric dual is still required.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (q u : Sphere 3)
  (hcross : ∀ x y, f x = FramedSurgery.coreMap (E := Vector 4) B y ↔ x = q ∧ y = u)
  (htrans : Surjective ((mfderiv (𝓡 3) (𝓡 6) f q).coprod
    (mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B) u)))

include hcross htrans in
theorem geometric_dual_primitive_and_belt_zero :
    ∃ l : SingularHomology M 3 →ₗ[ℤ] ℤ,
      l (TraceCoreAttachment.originalSphereClass f) = 1 ∧ nativeBeltClass f A hR = 0 := by
  have hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f := by
    rw [← unitFace_coreMap_eq f A hR]
    exact FramedSurgery.contMDiff_coreMap _
  have hp : f q = FramedSurgery.coreMap (E := Vector 4) B u :=
    (hcross q u).mpr ⟨rfl, rfl⟩
  have hu : ∀ x, f x ∈ range (FramedSurgery.coreMap (E := Vector 4) B) → x = q := by
    rintro x ⟨y, hy⟩
    exact ((hcross x y).mp hy.symm).1
  obtain ⟨l, hl⟩ := DualCover.exists_primitive_functional_of_single_transverse_dual
    (E := Vector 4) B f hf q u hp hu htrans
  refine ⟨l, hl, ?_⟩
  have hg : ContMDiff (𝓡 3) (𝓡 6) ∞ (FramedSurgery.coreMap (E := Vector 4) B) :=
    FramedSurgery.contMDiff_coreMap (E := Vector 4) B
  have hguni : ∀ y, FramedSurgery.coreMap (E := Vector 4) B y ∈ range f → y = u := by
    rintro y ⟨x, hx⟩
    exact ((hcross x y).mp hx).2
  let Df : Vector 3 →L[ℝ] Vector 6 := mfderiv (𝓡 3) (𝓡 6) f q
  let Dg : Vector 3 →L[ℝ] Vector 6 :=
    mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B) u
  have hfg : Surjective (Df.coprod Dg) := htrans
  have ht := TransverseCoordinates.surjective_coprod_swap Df Dg hfg
  have hz := nativeBelt_homology_zero_of_single_dual f A hR
    (FramedSurgery.coreMap (E := Vector 4) B) hg u q hp.symm hguni ht
  exact (nativeBelt_homology_zero_iff_class_zero f A hR).mp hz

def middleHomologyEquivOfDual : SingularHomology M 3 ≃ₗ[ℤ]
    (SingularHomology (UnitSurgery.Target A hR) 3 × ℤ) × ℤ := by
  let h := geometric_dual_primitive_and_belt_zero f A hR B q u hcross htrans
  let l := Classical.choose h
  have hl : l (TraceCoreAttachment.originalSphereClass f) = 1 := (Classical.choose_spec h).1
  have hz : nativeBeltClass f A hR = 0 := (Classical.choose_spec h).2
  let E := PrimitiveSplitting.splitEquiv l (TraceCoreAttachment.originalSphereClass f) hl
  let P := (reducedMiddleHomologyEquiv f A hR hz).toAddEquiv.prodCongr (AddEquiv.refl ℤ)
  let ea := E.toAddEquiv.trans P
  exact ea.toIntLinearEquiv

include hcross htrans in
theorem middle_finrank_of_dual
    [Module.Free ℤ (SingularHomology (UnitSurgery.Target A hR) 3)]
    [Module.Finite ℤ (SingularHomology (UnitSurgery.Target A hR) 3)] :
    Module.finrank ℤ (SingularHomology M 3) =
      Module.finrank ℤ (SingularHomology (UnitSurgery.Target A hR) 3) + 2 := by
  let K := SingularHomology (UnitSurgery.Target A hR) 3
  -- Use the standard product actions only for this numerical algebra calculation.
  -- The already constructed equivalence is transported through its additive map.
  letI : Module ℤ (K × ℤ) := Prod.instModule
  letI : Module ℤ ((K × ℤ) × ℤ) := Prod.instModule
  let E := middleHomologyEquivOfDual f A hR B q u hcross htrans
  let ea : SingularHomology M 3 ≃+ (K × ℤ) × ℤ := {
    toEquiv := E.toEquiv
    map_add' := fun x y => E.map_add' x y }
  let L : SingularHomology M 3 ≃ₗ[ℤ] (K × ℤ) × ℤ := ea.toIntLinearEquiv
  have h := L.finrank_eq
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_assoc] using h

include hcross htrans in
theorem middle_finrank_drop_of_dual [Module.Finite ℤ (SingularHomology M 3)] :
    Module.finrank ℤ (SingularHomology (UnitSurgery.Target A hR) 3) + 2 ≤
      Module.finrank ℤ (SingularHomology M 3) := by
  let K := SingularHomology (UnitSurgery.Target A hR) 3
  letI : Module ℤ (K × ℤ) := Prod.instModule
  letI : Module ℤ ((K × ℤ) × ℤ) := Prod.instModule
  let E := middleHomologyEquivOfDual f A hR B q u hcross htrans
  let ea : SingularHomology M 3 ≃+ (K × ℤ) × ℤ := {
    toEquiv := E.toEquiv
    map_add' := fun x y => E.map_add' x y }
  let L : SingularHomology M 3 ≃ₗ[ℤ] (K × ℤ) × ℤ := ea.toIntLinearEquiv
  have h₁ := rank_add_rank_le_rank_prod (M₁ := ℤ) ℤ K
  have h₂ := rank_add_rank_le_rank_prod (M₁ := ℤ) ℤ (K × ℤ)
  have hb : (Module.rank ℤ K + 1) + 1 ≤ Module.rank ℤ (SingularHomology M 3) := by
    have h := (add_le_add h₁ (le_refl (Module.rank ℤ ℤ))).trans h₂
    have h' : (Module.rank ℤ K + 1) + 1 ≤ Module.rank ℤ ((K × ℤ) × ℤ) := by
      simpa only [Module.rank_self] using h
    exact h'.trans_eq L.rank_eq.symm
  have hfin := Module.rank_lt_aleph0 ℤ (SingularHomology M 3)
  have hk₁ := (Cardinal.add_lt_aleph0_iff.mp (hb.trans_lt hfin)).1
  have hk := (Cardinal.add_lt_aleph0_iff.mp hk₁).1
  have hnat := Cardinal.toNat_le_toNat hb hfin
  rw [Cardinal.toNat_add hk₁ (by simp), Cardinal.toNat_add hk (by simp)] at hnat
  simpa only [Module.finrank, K, map_one, Nat.add_assoc, Nat.reduceAdd] using hnat

include hcross htrans in
theorem middle_finrank_strict_decrease_of_dual [Module.Finite ℤ (SingularHomology M 3)] :
    Module.finrank ℤ (SingularHomology (UnitSurgery.Target A hR) 3) <
      Module.finrank ℤ (SingularHomology M 3) := by
  have h := middle_finrank_drop_of_dual f A hR B q u hcross htrans
  omega

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody

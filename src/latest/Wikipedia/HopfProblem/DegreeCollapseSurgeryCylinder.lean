import Wikipedia.HopfProblem.DegreeCollapseSurgeryTraceHomology

/-!
# The original end and sphere inside the actual surgery cylinder

Contract the actual compact height interval to its top endpoint. Its
composition with the original cylinder embedding gives a homotopy
equivalence whose forward map is precisely the original top inclusion.
The height homotopy also compares the original sphere with the core
attaching boundary, inside the cylinder itself.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceCoreAttachment

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def cylinderTopSection : C(M, UnroundedTrace.Cylinder A) :=
  ⟨fun m ↦ (m, ⟨UnroundedTrace.height A, (UnroundedTrace.height_pos A).le, le_rfl⟩),
    continuous_id.prodMk continuous_const⟩

def cylinderProjection : C(UnroundedTrace.Cylinder A, M) := ⟨Prod.fst, continuous_fst⟩

def cylinderContraction : ((cylinderTopSection A).comp (cylinderProjection A)).Homotopy
    (ContinuousMap.id (UnroundedTrace.Cylinder A)) := by
  have htime (z : I × UnroundedTrace.Cylinder A) :
      (1 - (z.1 : ℝ)) * UnroundedTrace.height A + (z.1 : ℝ) * z.2.2.val ∈
        Icc 0 (UnroundedTrace.height A) := by
    have hT := (UnroundedTrace.height_pos A).le
    have ht := z.1.property
    have hs := z.2.2.property
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hT) (mul_nonneg ht.1 hs.1)
    · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hs.2)]
  refine {
    toFun := fun z ↦ (z.2.1, ⟨(1 - (z.1 : ℝ)) * UnroundedTrace.height A +
      (z.1 : ℝ) * z.2.2.val, htime z⟩)
    continuous_toFun := by fun_prop
    map_zero_left := ?_
    map_one_left := ?_ }
  · intro p
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (1 - (0 : ℝ)) * UnroundedTrace.height A + (0 : ℝ) * p.2.val =
        UnroundedTrace.height A
      simp
  · intro p
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (1 - (1 : ℝ)) * UnroundedTrace.height A + (1 : ℝ) * p.2.val = p.2.val
      simp

def topCylinderProductHomotopyEquiv : M ≃ₕ UnroundedTrace.Cylinder A where
  toFun := cylinderTopSection A
  invFun := cylinderProjection A
  left_inv := by
    have h : (cylinderProjection A).comp (cylinderTopSection A) = ContinuousMap.id M := rfl
    rw [h]
  right_inv := ⟨cylinderContraction A⟩

def cylinderHomeomorph : UnroundedTrace.Cylinder A ≃ₜ range (UnroundedTrace.cylinderMap A) :=
  (UnroundedTrace.closedEmbedding_cylinder A).isEmbedding.toHomeomorph

def topCylinderHomotopyEquiv : M ≃ₕ range (UnroundedTrace.cylinderMap A) :=
  (topCylinderProductHomotopyEquiv A).trans (cylinderHomeomorph A).toHomotopyEquiv

theorem topCylinderHomotopyEquiv_ambient (m : M) :
    (topCylinderHomotopyEquiv A m).val = e.heightCylinder (m, UnroundedTrace.height A) := rfl

theorem cylinderInclusion_comp_top :
    (cylinderInclusion A).comp (topCylinderHomotopyEquiv A).toFun = topMap A := rfl

theorem top_sphere_homotopic_boundary (g : C(Sphere 3, M))
    (A : FramedAttachingProduct e a g) (hR : A.radius = 2) :
    ((topCylinderHomotopyEquiv A).toFun.comp g).Homotopic (coreBoundary A hR) := by
  have htime (t : I) : (1 - (t : ℝ)) * UnroundedTrace.height A ∈
      Icc 0 (UnroundedTrace.height A) := by
    have hT := (UnroundedTrace.height_pos A).le
    constructor
    · exact mul_nonneg (sub_nonneg.mpr t.property.2) hT
    · nlinarith [t.property.1]
  let K : C(I × Sphere 3, UnroundedTrace.Cylinder A) :=
    ⟨fun z ↦ (g z.2, ⟨(1 - (z.1 : ℝ)) * UnroundedTrace.height A, htime z.1⟩), by fun_prop⟩
  refine ⟨{
    toContinuousMap := (cylinderHomeomorph A).toHomotopyEquiv.toFun.comp K
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro s
    apply Subtype.ext
    change e.heightCylinder (g s, (1 - (0 : ℝ)) * UnroundedTrace.height A) =
      e.heightCylinder (g s, UnroundedTrace.height A)
    rw [sub_zero, one_mul]
  · intro s
    apply Subtype.ext
    change e.heightCylinder (g s, (1 - (1 : ℝ)) * UnroundedTrace.height A) =
      (coreBoundary A hR s).val
    rw [sub_self, zero_mul]
    exact (coreBoundary_ambient A hR s).symm

end Wikipedia.HopfProblem.DegreeCollapse.TraceCoreAttachment

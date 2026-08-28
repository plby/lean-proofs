import Wikipedia.NoExoticSixSphere.SuspensionProjectionKernel
import Wikipedia.NoExoticSixSphere.CircleProjectionKernel
import Wikipedia.HopfProblem.SphereHomologySuspension
import Wikipedia.HopfProblem.SphereHomologyCircleNative
import Wikipedia.HopfProblem.SphereHomologyCircleGeometry

/-!
# Lower-degree detection of maps on sphere-product projection kernels

The literal sphere is the actual suspension of the preceding sphere.
Transporting the natural suspension kernel equivalence reduces sphere
dimension and homology degree together. The circle case reduces to
ordinary homology of the second factor. Degree-zero kernels vanish for
path-connected factors. Thus lower-degree homology isomorphisms suffice
for an isomorphism on the projection kernel of a positive sphere product.
-/

noncomputable section

open Wikipedia.HopfProblem CuspCentralHomology SphereHomology
open SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.SphereProjectionKernel

def circleHomeomorph : UnitSphere 1 ≃ₜ CircleTopology.Circle :=
  sphereCircleHomeomorph.trans unitCircleAddCircleHomeomorph

variable (X : Type) [TopologicalSpace X]

def circleEquiv (d : ℕ) : ProductProjectionHomology.Kernel (UnitSphere 1) X (d + 1) ≃ₗ[ℤ]
    SingularHomology X d :=
  (ProductProjectionHomology.firstEquiv X circleHomeomorph.toHomotopyEquiv (d + 1)).trans
    (CircleProjectionKernel.equiv X d)

def stepEquiv (n d : ℕ) :
    ProductProjectionHomology.Kernel (UnitSphere (n + 1)) X (d + 1) ≃ₗ[ℤ]
      ProductProjectionHomology.Kernel (UnitSphere n) X d :=
  (ProductProjectionHomology.firstEquiv X
    (suspensionSphereHomeomorph n).symm.toHomotopyEquiv (d + 1)).trans
      (SuspensionProjectionKernel.equiv (UnitSphere n) X d)

variable {X} {Z : Type} [TopologicalSpace Z]

theorem circleEquiv_naturality (f : C(X, Z)) (d : ℕ)
    (a : ProductProjectionHomology.Kernel (UnitSphere 1) X (d + 1)) :
    circleEquiv Z d (ProductProjectionHomology.map (UnitSphere 1) f (d + 1) a) =
      singularHomologyMap f d (circleEquiv X d a) := by
  change CircleProjectionKernel.equiv Z d
    (ProductProjectionHomology.firstEquiv Z circleHomeomorph.toHomotopyEquiv (d + 1)
      (ProductProjectionHomology.map (UnitSphere 1) f (d + 1) a)) = _
  rw [ProductProjectionHomology.firstEquiv_naturality, CircleProjectionKernel.equiv_naturality]
  rfl

theorem stepEquiv_naturality (f : C(X, Z)) (n d : ℕ)
    (a : ProductProjectionHomology.Kernel (UnitSphere (n + 1)) X (d + 1)) :
    stepEquiv Z n d (ProductProjectionHomology.map (UnitSphere (n + 1)) f (d + 1) a) =
      ProductProjectionHomology.map (UnitSphere n) f d (stepEquiv X n d a) := by
  change SuspensionProjectionKernel.equiv (UnitSphere n) Z d
    (ProductProjectionHomology.firstEquiv Z
      (suspensionSphereHomeomorph n).symm.toHomotopyEquiv (d + 1)
      (ProductProjectionHomology.map (UnitSphere (n + 1)) f (d + 1) a)) = _
  rw [ProductProjectionHomology.firstEquiv_naturality,
    SuspensionProjectionKernel.equiv_naturality]
  rfl

theorem circle_map_bijective_iff (f : C(X, Z)) (d : ℕ) :
    Function.Bijective (ProductProjectionHomology.map (UnitSphere 1) f (d + 1)) ↔
      Function.Bijective (singularHomologyMap f d) := by
  have h : circleEquiv Z d ∘ ProductProjectionHomology.map (UnitSphere 1) f (d + 1) =
      singularHomologyMap f d ∘ circleEquiv X d := funext (circleEquiv_naturality f d)
  have h₁ := Function.Bijective.of_comp_iff' (circleEquiv Z d).bijective
    (ProductProjectionHomology.map (UnitSphere 1) f (d + 1))
  have h₂ := Function.Bijective.of_comp_iff (singularHomologyMap f d) (circleEquiv X d).bijective
  rw [← h₁, h, h₂]

theorem step_map_bijective_iff (f : C(X, Z)) (n d : ℕ) :
    Function.Bijective (ProductProjectionHomology.map (UnitSphere (n + 1)) f (d + 1)) ↔
      Function.Bijective (ProductProjectionHomology.map (UnitSphere n) f d) := by
  have h : stepEquiv Z n d ∘ ProductProjectionHomology.map (UnitSphere (n + 1)) f (d + 1) =
      ProductProjectionHomology.map (UnitSphere n) f d ∘ stepEquiv X n d :=
    funext (stepEquiv_naturality f n d)
  have h₁ := Function.Bijective.of_comp_iff' (stepEquiv Z n d).bijective
    (ProductProjectionHomology.map (UnitSphere (n + 1)) f (d + 1))
  have h₂ := Function.Bijective.of_comp_iff (ProductProjectionHomology.map (UnitSphere n) f d)
    (stepEquiv X n d).bijective
  rw [← h₁, h, h₂]

variable [PathConnectedSpace X] [PathConnectedSpace Z]

theorem map_zero_bijective (f : C(X, Z)) (n : ℕ) :
    Function.Bijective (ProductProjectionHomology.map (UnitSphere (n + 1)) f 0) := by
  let := ProductProjectionHomology.kernel_zero_subsingleton (UnitSphere (n + 1)) X
  let := ProductProjectionHomology.kernel_zero_subsingleton (UnitSphere (n + 1)) Z
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun a ↦ ⟨0, Subsingleton.elim _ a⟩⟩

theorem map_bijective_of_lower (f : C(X, Z)) (n d : ℕ)
    (h : ∀ k < d, Function.Bijective (singularHomologyMap f k)) :
    Function.Bijective (ProductProjectionHomology.map (UnitSphere (n + 1)) f d) := by
  induction n generalizing d with
  | zero =>
      cases d with
      | zero => exact map_zero_bijective f 0
      | succ d => exact (circle_map_bijective_iff f d).mpr (h d (Nat.lt_succ_self d))
  | succ n ih =>
      cases d with
      | zero => exact map_zero_bijective f (n + 1)
      | succ d =>
          apply (step_map_bijective_iff f (n + 1) d).mpr
          exact ih d (fun k hk ↦ h k (hk.trans (Nat.lt_succ_self d)))

end NoExoticSixSphere.SphereProjectionKernel

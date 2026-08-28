import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Wikipedia.HopfProblem.SphereHomologySuspensionOneZero

/-!
# The kernel of projection on actual product homology

This is the actual kernel of the homology map of second projection,
not a replacement definition of reduced homology. Maps in either factor
induce maps on these kernels. A homotopy equivalence in the first factor
gives a kernel equivalence, with its literal product map retained.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.ProductProjectionHomology

variable (P X : Type) [TopologicalSpace P] [TopologicalSpace X]

def projection (d : ℕ) : SingularHomology (P × X) d →ₗ[ℤ] SingularHomology X d :=
  singularHomologyMap ContinuousMap.snd d

abbrev Kernel (d : ℕ) := LinearMap.ker (projection P X d)

instance kernelModule (d : ℕ) : Module ℤ (Kernel P X d) := (Kernel P X d).module

def sectionMap (p : P) : C(X, P × X) :=
  (ContinuousMap.const X p).prodMk (ContinuousMap.id X)

theorem projection_section (p : P) (d : ℕ) (a : SingularHomology X d) :
    projection P X d (singularHomologyMap (sectionMap P X p) d a) = a := by
  have h := LinearMap.congr_fun
    (singularHomologyMap_comp (sectionMap P X p) (ContinuousMap.snd : C(P × X, X)) d) a
  change singularHomologyMap (ContinuousMap.id X) d a =
    projection P X d (singularHomologyMap (sectionMap P X p) d a) at h
  rw [singularHomologyMap_id] at h
  exact h.symm

variable {X} {Y : Type} [TopologicalSpace Y]

def secondMap (f : C(X, Y)) : C(P × X, P × Y) := (ContinuousMap.id P).prodMap f

theorem projection_secondMap (f : C(X, Y)) (d : ℕ) (a : SingularHomology (P × X) d) :
    projection P Y d (singularHomologyMap (secondMap P f) d a) =
      singularHomologyMap f d (projection P X d a) := by
  have h : (ContinuousMap.snd : C(P × Y, Y)).comp (secondMap P f) =
      f.comp (ContinuousMap.snd : C(P × X, X)) := rfl
  have hh := congrArg (fun q ↦ singularHomologyMap q d) h
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at hh
  exact LinearMap.congr_fun hh a

def map (f : C(X, Y)) (d : ℕ) : Kernel P X d →ₗ[ℤ] Kernel P Y d :=
  ((singularHomologyMap (secondMap P f) d).comp (Kernel P X d).subtype).codRestrict _ (by
    intro a
    change projection P Y d (singularHomologyMap (secondMap P f) d a.val) = 0
    rw [projection_secondMap, a.property, map_zero])

theorem map_val (f : C(X, Y)) (d : ℕ) (a : Kernel P X d) :
    (map P f d a).val = singularHomologyMap (secondMap P f) d a.val := rfl

variable {P} (X) {Q : Type} [TopologicalSpace Q]

def firstMap (f : C(P, Q)) : C(P × X, Q × X) := f.prodMap (ContinuousMap.id X)

theorem projection_firstMap (f : C(P, Q)) (d : ℕ) (a : SingularHomology (P × X) d) :
    projection Q X d (singularHomologyMap (firstMap X f) d a) = projection P X d a :=
  (LinearMap.congr_fun
    (singularHomologyMap_comp (firstMap X f) (ContinuousMap.snd : C(Q × X, X)) d) a).symm

def firstKernelMap (f : C(P, Q)) (d : ℕ) : Kernel P X d →ₗ[ℤ] Kernel Q X d :=
  ((singularHomologyMap (firstMap X f) d).comp (Kernel P X d).subtype).codRestrict _ (by
    intro a
    change projection Q X d (singularHomologyMap (firstMap X f) d a.val) = 0
    rw [projection_firstMap]
    exact a.property)

theorem firstKernelMap_val (f : C(P, Q)) (d : ℕ) (a : Kernel P X d) :
    (firstKernelMap X f d a).val = singularHomologyMap (firstMap X f) d a.val := rfl

def firstEquiv (e : ContinuousMap.HomotopyEquiv P Q) (d : ℕ) :
    Kernel P X d ≃ₗ[ℤ] Kernel Q X d where
  toLinearMap := firstKernelMap X e.toFun d
  invFun := firstKernelMap X e.invFun d
  left_inv a := by
    apply Subtype.ext
    let E := homotopyEquivHomologyEquiv (e.prodCongr (ContinuousMap.HomotopyEquiv.refl X)) d
    exact E.symm_apply_apply a.val
  right_inv a := by
    apply Subtype.ext
    let E := homotopyEquivHomologyEquiv (e.prodCongr (ContinuousMap.HomotopyEquiv.refl X)) d
    exact E.apply_symm_apply a.val

theorem firstEquiv_apply (e : ContinuousMap.HomotopyEquiv P Q) (d : ℕ) (a : Kernel P X d) :
    (firstEquiv X e d a).val = singularHomologyMap (firstMap X e.toFun) d a.val := rfl

variable {X}

theorem firstKernelMap_naturality (g : C(P, Q)) (f : C(X, Y)) (d : ℕ) (a : Kernel P X d) :
    firstKernelMap Y g d (map P f d a) = map Q f d (firstKernelMap X g d a) := by
  apply Subtype.ext
  have h : (firstMap Y g).comp (secondMap P f) = (secondMap Q f).comp (firstMap X g) := rfl
  have hh := congrArg (fun q ↦ singularHomologyMap q d) h
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at hh
  exact LinearMap.congr_fun hh a.val

theorem firstEquiv_naturality (e : ContinuousMap.HomotopyEquiv P Q) (f : C(X, Y)) (d : ℕ)
    (a : Kernel P X d) : firstEquiv Y e d (map P f d a) = map Q f d (firstEquiv X e d a) :=
  firstKernelMap_naturality e.toFun f d a

variable (P X)

theorem kernel_zero_subsingleton [PathConnectedSpace P] [PathConnectedSpace X] :
    Subsingleton (Kernel P X 0) := by
  apply Subsingleton.intro
  intro a b
  apply Subtype.ext
  apply SphereHomology.singularHomologyMap_zero_injective (ContinuousMap.snd : C(P × X, X))
  exact a.property.trans b.property.symm

end NoExoticSixSphere.ProductProjectionHomology

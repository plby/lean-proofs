import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardTensorLocalHolomorphic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsLinear

/-!
# Native section comparison for one pulled-back local line frame

Contraction and tensoring with the original base unit frame act on
holomorphic sections of the original native bundle cores. They are
inverse linear maps over the actual holomorphic functions on the open
set, and commute with literal restriction of the original sections.
-/

noncomputable section

open Set Topology TopologicalSpace Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.TensorLocal

open HolomorphicCharacterBundle

variable {M N : Type} {ι κ : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (A : TransitionData M ι) (B : TransitionData N κ)
  {E H F K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace K] [ChartedSpace K N]
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)
  (f : M → N) (hf : ContMDiff I J ω f)
  [A.IsHolomorphic I] [B.IsHolomorphic J]

/-- Contraction of an actual native holomorphic tensor-bundle section. -/
def unTensorSection (j : κ) (V : Opens M) (hV : MapsTo f V (B.baseSet j))
    (s : NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I V) :
    NativeBundleSections.Section A.core I V where
  toFun x := unTensorFiberEquiv A B f hf.continuous j x.val (s x)
  contMDiff_toFun := by
    intro x
    exact (unTensorMap_holomorphicAt A B I J f hf j ⟨x.val, s x⟩
      (hV x.property)).comp x (s.contMDiff_toFun x)

/-- Tensoring with the original pulled-back local unit frame, in the original total-space atlas. -/
def tensorSection (j : κ) (V : Opens M) (hV : MapsTo f V (B.baseSet j))
    (s : NativeBundleSections.Section A.core I V) :
    NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I V where
  toFun x := (unTensorFiberEquiv A B f hf.continuous j x.val).symm (s x)
  contMDiff_toFun := by
    intro x
    exact (tensorMap_holomorphicAt A B I J f hf j ⟨x.val, s x⟩
      (hV x.property)).comp x (s.contMDiff_toFun x)

@[simp] theorem unTensorSection_apply (j : κ) (V : Opens M)
    (hV : MapsTo f V (B.baseSet j))
    (s : NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I V)
    (x : V) :
    unTensorSection A B I J f hf j V hV s x =
      unTensorFiberEquiv A B f hf.continuous j x.val (s x) := rfl

@[simp] theorem tensorSection_apply (j : κ) (V : Opens M)
    (hV : MapsTo f V (B.baseSet j)) (s : NativeBundleSections.Section A.core I V) (x : V) :
    tensorSection A B I J f hf j V hV s x =
      (unTensorFiberEquiv A B f hf.continuous j x.val).symm (s x) := rfl

/-- The inverse section map has the genuine elementary-tensor expression in every fibre. -/
theorem tensorSection_fibreTensor (j : κ) (V : Opens M)
    (hV : MapsTo f V (B.baseSet j)) (s : NativeBundleSections.Section A.core I V) (x : V) :
    tensorSection A B I J f hf j V hV s x =
      fibreTensorEquiv A (pullback B f hf.continuous) x.val
        (s x ⊗ₜ[ℂ] pulledFrame B f hf.continuous j x.val) :=
  unTensorFiberEquiv_symm A B f hf.continuous j x.val (hV x.property) (s x)

@[simp] theorem unTensorSection_tensorSection (j : κ) (V : Opens M)
    (hV : MapsTo f V (B.baseSet j)) (s : NativeBundleSections.Section A.core I V) :
    unTensorSection A B I J f hf j V hV (tensorSection A B I J f hf j V hV s) = s := by
  apply NativeBundleSections.Section.ext A.core I
  intro x
  exact (unTensorFiberEquiv A B f hf.continuous j x.val).apply_symm_apply (s x)

@[simp] theorem tensorSection_unTensorSection (j : κ) (V : Opens M)
    (hV : MapsTo f V (B.baseSet j))
    (s : NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I V) :
    tensorSection A B I J f hf j V hV (unTensorSection A B I J f hf j V hV s) = s := by
  apply NativeBundleSections.Section.ext (tensor A (pullback B f hf.continuous)).core I
  intro x
  exact (unTensorFiberEquiv A B f hf.continuous j x.val).symm_apply_apply (s x)

/-- The native section comparison is linear over all actual holomorphic functions upstairs. -/
def sectionEquivOn (j : κ) (V : Opens M) (hV : MapsTo f V (B.baseSet j)) :
    letI : (pullback B f hf.continuous).IsHolomorphic I :=
      pullback_isHolomorphic B f hf.continuous I J hf
    NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I V
      ≃ₗ[HolomorphicFunctionSheaf.Section I M V] NativeBundleSections.Section A.core I V := by
  let : (pullback B f hf.continuous).IsHolomorphic I :=
    pullback_isHolomorphic B f hf.continuous I J hf
  exact
    { toFun := unTensorSection A B I J f hf j V hV
      invFun := tensorSection A B I J f hf j V hV
      left_inv := tensorSection_unTensorSection A B I J f hf j V hV
      right_inv := unTensorSection_tensorSection A B I J f hf j V hV
      map_add' s t := by
        apply NativeBundleSections.Section.ext A.core I
        intro x
        exact (unTensorFiberEquiv A B f hf.continuous j x.val).map_add (s x) (t x)
      map_smul' g s := by
        apply NativeBundleSections.Section.ext A.core I
        intro x
        exact (unTensorFiberEquiv A B f hf.continuous j x.val).map_smul (g x) (s x) }

@[simp] theorem sectionEquivOn_apply (j : κ) (V : Opens M)
    (hV : MapsTo f V (B.baseSet j))
    (s : NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I V) :
    sectionEquivOn A B I J f hf j V hV s = unTensorSection A B I J f hf j V hV s := rfl

@[simp] theorem sectionEquivOn_symm_apply (j : κ) (V : Opens M)
    (hV : MapsTo f V (B.baseSet j)) (s : NativeBundleSections.Section A.core I V) :
    letI : (pullback B f hf.continuous).IsHolomorphic I :=
      pullback_isHolomorphic B f hf.continuous I J hf
    (sectionEquivOn A B I J f hf j V hV).symm s = tensorSection A B I J f hf j V hV s := rfl

/-- The exact forward transition factor for contraction in a different original base chart. -/
theorem unTensorSection_change (j k : κ) (V : Opens M)
    (hj : MapsTo f V (B.baseSet j)) (hk : MapsTo f V (B.baseSet k))
    (s : NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I V)
    (x : V) :
    unTensorSection A B I J f hf k V hk s x =
      (B.transition j k (f x.val) : ℂ) • unTensorSection A B I J f hf j V hj s x :=
  unTensorFiberEquiv_change A B f hf.continuous j k x.val
    (hj x.property) (hk x.property) (s x)

/-- Contraction commutes with literal restriction in the original section modules. -/
theorem unTensorSection_restrict (j : κ) {V W : Opens M} (hVW : V ≤ W)
    (hV : MapsTo f V (B.baseSet j)) (hW : MapsTo f W (B.baseSet j))
    (s : NativeBundleSections.Section (tensor A (pullback B f hf.continuous)).core I W) :
    NativeBundleSections.Section.restrict A.core I hVW (unTensorSection A B I J f hf j W hW s) =
      unTensorSection A B I J f hf j V hV
        (NativeBundleSections.Section.restrict (tensor A (pullback B f hf.continuous)).core I
          hVW s) := by
  apply NativeBundleSections.Section.ext A.core I
  intro x
  rfl

theorem tensorSection_restrict (j : κ) {V W : Opens M} (hVW : V ≤ W)
    (hV : MapsTo f V (B.baseSet j)) (hW : MapsTo f W (B.baseSet j))
    (s : NativeBundleSections.Section A.core I W) :
    NativeBundleSections.Section.restrict (tensor A (pullback B f hf.continuous)).core I hVW
        (tensorSection A B I J f hf j W hW s) =
      tensorSection A B I J f hf j V hV (NativeBundleSections.Section.restrict A.core I hVW s) := by
  apply NativeBundleSections.Section.ext (tensor A (pullback B f hf.continuous)).core I
  intro x
  rfl

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.TensorLocal

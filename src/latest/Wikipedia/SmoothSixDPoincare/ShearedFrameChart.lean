import Wikipedia.SmoothSixDPoincare.FiberwiseFrameChart
import Wikipedia.SmoothSixDPoincare.CompactLocalDiffeomorph
import Wikipedia.SmoothSixDPoincare.LocalInverseIntoManifold

/-!
# Tubular frame changes retaining disk-tangent components

The shear `(x,z) ↦ (x + A(x) z, T(x) z)` fixes the zero section. Its
derivative there is the actual upper-triangular block map `[I A; 0 T]`.
Invertibility of `T` gives local smooth inverses, and compactness assembles
one genuine coordinate chart around the entire compact zero section.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {X Z F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def shearedBlock (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) : (X × Z) →L[ℝ] (X × F) :=
  (ContinuousLinearMap.inl ℝ X F).coprod (A.prod T)

theorem shearedBlock_apply (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (p : X × Z) :
    shearedBlock A T p = (p.1 + A p.2, T p.2) := by
  simp [shearedBlock, ContinuousLinearMap.coprod_apply]

theorem shearedBlock_horizontal (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (x : X) :
    shearedBlock A T (x, 0) = (x, 0) := by
  simp only [shearedBlock_apply, map_zero, add_zero]

theorem bijective_shearedBlock (A : Z →L[ℝ] X) (T : Z →L[ℝ] F) (hi : Bijective T) :
    Bijective (shearedBlock A T) := by
  constructor
  · intro p q hpq
    have hz : p.2 = q.2 := hi.1 (by simpa only [shearedBlock_apply] using congrArg Prod.snd hpq)
    have hx : p.1 + A p.2 = q.1 + A q.2 := by
      simpa only [shearedBlock_apply] using congrArg Prod.fst hpq
    rw [hz] at hx
    exact Prod.ext (add_right_cancel hx) hz
  · intro q
    obtain ⟨z, hz⟩ := hi.2 q.2
    refine ⟨(q.1 - A z, z), ?_⟩
    rw [shearedBlock_apply]
    simp only [sub_add_cancel, hz]

def shearedMap (A : X → (Z →L[ℝ] X)) (T : X → (Z →L[ℝ] F)) (p : X × Z) : X × F :=
  (p.1 + A p.1 p.2, T p.1 p.2)

theorem shearedMap_zero (A : X → (Z →L[ℝ] X)) (T : X → (Z →L[ℝ] F)) (x : X) :
    shearedMap A T (x, 0) = (x, 0) := by simp only [shearedMap, map_zero, add_zero]

theorem contDiffOn_shearedMap {A : X → (Z →L[ℝ] X)} {T : X → (Z →L[ℝ] F)} {U : Set X}
    (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U) :
    ContDiffOn ℝ ∞ (shearedMap A T) (Prod.fst ⁻¹' U) :=
  (contDiffOn_fst.add
    ((hA.comp contDiffOn_fst (fun _ hp => hp)).clm_apply contDiffOn_snd)).prodMk
      ((hT.comp contDiffOn_fst (fun _ hp => hp)).clm_apply contDiffOn_snd)

theorem hasFDerivAt_shearedMap_zero {A : X → (Z →L[ℝ] X)} {T : X → (Z →L[ℝ] F)} {x : X}
    (hA : DifferentiableAt ℝ A x) (hT : DifferentiableAt ℝ T x) :
    HasFDerivAt (shearedMap A T) (shearedBlock (A x) (T x)) (x, 0) := by
  have hAa : HasFDerivAt (fun p : X × Z => A p.1)
      ((fderiv ℝ A x).comp (ContinuousLinearMap.fst ℝ X Z)) (x, 0) :=
    hA.hasFDerivAt.comp (x, 0) hasFDerivAt_fst
  have hTt : HasFDerivAt (fun p : X × Z => T p.1)
      ((fderiv ℝ T x).comp (ContinuousLinearMap.fst ℝ X Z)) (x, 0) :=
    hT.hasFDerivAt.comp (x, 0) hasFDerivAt_fst
  have hs : HasFDerivAt (fun p : X × Z => p.2) (ContinuousLinearMap.snd ℝ X Z) (x, 0) :=
    hasFDerivAt_snd
  have hf : HasFDerivAt (fun p : X × Z => p.1) (ContinuousLinearMap.fst ℝ X Z) (x, 0) :=
    hasFDerivAt_fst
  have hd := (hf.add (hAa.clm_apply hs)).prodMk (hTt.clm_apply hs)
  convert hd using 1 <;> first
    | rfl
    | (apply ContinuousLinearMap.ext; intro p; simp [shearedBlock_apply])

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z]

theorem isInvertible_shearedBlock (A : Z →L[ℝ] X) (T : Z →L[ℝ] F)
    (hi : T.IsInvertible) : (shearedBlock A T).IsInvertible := by
  let e := (LinearEquiv.ofBijective (shearedBlock A T).toLinearMap
    (bijective_shearedBlock A T hi.bijective)).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

/-- The full compact zero section lies in one constructed smooth shear chart. -/
theorem exists_sheared_frame_chart {A : X → (Z →L[ℝ] X)} {T : X → (Z →L[ℝ] F)}
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U)
    (hi : ∀ x ∈ K, (T x).IsInvertible) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, X × F) (X × Z) (X × F) ∞,
      K ×ˢ {(0 : Z)} ⊆ Φ.source ∧ Φ.source ⊆ Prod.fst ⁻¹' U ∧
      (Φ : X × Z → X × F) = shearedMap A T := by
  have hzeroInj : InjOn (shearedMap A T) (K ×ˢ {(0 : Z)}) := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩ ⟨y, w⟩ ⟨hy, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [shearedMap_zero, shearedMap_zero] at heq
    exact Prod.ext (congrArg (fun q : X × F => q.1) heq) rfl
  have hlocal : ∀ p ∈ K ×ˢ {(0 : Z)},
      IsLocalDiffeomorphAt 𝓘(ℝ, X × Z) 𝓘(ℝ, X × F) ∞ (shearedMap A T) p := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply isLocalDiffeomorphAt_of_contMDiffOn (D := X × Z) (E := X × F) (M := X × F)
      (hU.preimage continuous_fst) (show (x, (0 : Z)) ∈ Prod.fst ⁻¹' U from hKU hx)
      (contDiffOn_shearedMap hA hT).contMDiffOn
    rw [mfderiv_eq_fderiv, (hasFDerivAt_shearedMap_zero
      ((hA.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
      ((hT.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))).fderiv]
    exact isInvertible_shearedBlock (A x) (T x) (hi x hx)
  exact exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton) hzeroInj hlocal
    (hU.preimage continuous_fst) (fun _ hp => hKU hp.1)

end Wikipedia.SmoothSixDPoincare.FrameField

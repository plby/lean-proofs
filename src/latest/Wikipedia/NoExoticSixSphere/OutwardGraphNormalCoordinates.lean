import Wikipedia.NoExoticSixSphere.OutwardGraphExtension
import Wikipedia.NoExoticSixSphere.NormalFrameSourceCoordinates

/-!
# The outward extension criterion in the actual boundary normal model

The native boundary codimension need not have the same expression as
the original normal dimension plus one. A fixed normal-model equivalence
is carried through all five graph axes and four derivative axes. It may
include a last-column reflection. Exact extendability is unchanged.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.OutwardGraphFrame

open GLOrthonormalization Stiefel CollaredDiskFrame DiskBoundary

variable {N k l : ℕ}

theorem combined_comp_normalCoordinates
    (A : Vector k →L[ℝ] (Vector N × ℝ)) (D : Vector 4 →L[ℝ] (Vector N × ℝ))
    (Q : Vector l ≃L[ℝ] Vector k) :
    combined (A.comp Q.toContinuousLinearMap) D =
      (combined A D).comp (NormalFrameSourceCoordinates.twistedBlock Q).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  change combined (A.comp Q.toContinuousLinearMap) D v =
    combined A D (NormalFrameSourceCoordinates.twistedBlock Q v)
  simp only [combined_apply, sourceCoordinates_apply,
    NormalFrameSourceCoordinates.twistedBlock, NormalFrameSourceCoordinates.block_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]

def outwardMap
    (A : C(Sphere 3, Vector k →L[ℝ] Vector N))
    (D : C(Sphere 3, Vector 4 →L[ℝ] Vector N))
    (ν : C(Sphere 3, Vector N)) (ξ : C(Sphere 3, Vector N →L[ℝ] ℝ))
    (Q : Vector l ≃L[ℝ] Vector (k + 1))
    (hAD : ∀ s, Injective ((A s).coprod (D s)))
    (hA : ∀ s u, ξ s (A s u) = 0) (hν : ∀ s, ξ s (ν s) < 0) :
    C(Sphere 3, Monomorphism.Space (N + 6) ((l + 5) + 4)) :=
  (Monomorphism.recoordinateHomeomorph
    (ContinuousLinearEquiv.refl ℝ (Vector (N + 6)))
    (NormalFrameSourceCoordinates.twistedBlock Q) :
      C(Monomorphism.Space (N + 6) (((k + 1) + 5) + 4),
        Monomorphism.Space (N + 6) ((l + 5) + 4))).comp
      { toFun := fun s ↦ ⟨outwardFamily A D ν ξ (1, s),
          outwardFamily_injective A D ν ξ hAD hA hν (1, s)⟩
        continuous_toFun := ((continuous_outwardFamily A D ν ξ).comp
          (continuous_const.prodMk continuous_id)).subtype_mk _ }

theorem outwardMap_value
    (A : C(Sphere 3, Vector k →L[ℝ] Vector N))
    (D : C(Sphere 3, Vector 4 →L[ℝ] Vector N))
    (ν : C(Sphere 3, Vector N)) (ξ : C(Sphere 3, Vector N →L[ℝ] ℝ))
    (Q : Vector l ≃L[ℝ] Vector (k + 1))
    (hAD : ∀ s, Injective ((A s).coprod (D s)))
    (hA : ∀ s u, ξ s (A s u) = 0) (hν : ∀ s, ξ s (ν s) < 0) (s : Sphere 3) :
    (outwardMap A D ν ξ Q hAD hA hν s).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp
        ((OrthogonalFrameAppend.operator (A s) (ν s)).comp Q.toContinuousLinearMap))
        (graph (D s) (ξ s)) := by
  change (combined (normal 1 (A s) (ν s)) (graph (D s) (ξ s))).comp
    (NormalFrameSourceCoordinates.twistedBlock Q).toContinuousLinearMap = _
  rw [normal_one, ← combined_comp_normalCoordinates]
  simp only [ContinuousLinearMap.comp_assoc]

theorem extends_outward_normalCoordinates_iff (hN : N = 3 + (k + 4))
    (A : C(Sphere 3, Vector k →L[ℝ] Vector N))
    (D : C(Sphere 3, Vector 4 →L[ℝ] Vector N))
    (ν : C(Sphere 3, Vector N)) (ξ : C(Sphere 3, Vector N →L[ℝ] ℝ))
    (Q : Vector l ≃L[ℝ] Vector (k + 1))
    (P : C(Sphere 3, Monomorphism.Space N (k + 4)))
    (G : C(Sphere 3, Monomorphism.Space (N + 6) ((l + 5) + 4)))
    (hP : ∀ s, (P s).val = OperatorSum.operator (A s) (D s))
    (hG : ∀ s, (G s).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp
        ((OrthogonalFrameAppend.operator (A s) (ν s)).comp Q.toContinuousLinearMap))
        (graph (D s) (ξ s)))
    (hA : ∀ s u, ξ s (A s u) = 0) (hν : ∀ s, ξ s (ν s) < 0) :
    Extends G ↔ Extends P := by
  have hAD : ∀ s, Injective ((A s).coprod (D s)) :=
    fun s ↦ coprod_injective_of_operator (P s) (A s) (D s) (hP s)
  let B : C(Sphere 3, Monomorphism.Space (N + 6) (((k + 1) + 5) + 4)) := {
    toFun s := ⟨outwardFamily A D ν ξ (1, s),
      outwardFamily_injective A D ν ξ hAD hA hν (1, s)⟩
    continuous_toFun := ((continuous_outwardFamily A D ν ξ).comp
      (continuous_const.prodMk continuous_id)).subtype_mk _ }
  have hB (s : Sphere 3) : (B s).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp
        (OrthogonalFrameAppend.operator (A s) (ν s))) (graph (D s) (ξ s)) := by
    change combined (normal 1 (A s) (ν s)) (graph (D s) (ξ s)) = _
    rw [normal_one]
  have hGB : Extends G ↔ Extends B := by
    apply Monomorphism.extends_recoordinate_iff
      (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector (N + 6)))
      (fun _ ↦ NormalFrameSourceCoordinates.twistedBlock Q)
      continuous_const continuous_const continuous_const continuous_const B G
    intro s
    apply Subtype.ext
    change (G s).val = (B s).val.comp
      (NormalFrameSourceCoordinates.twistedBlock Q).toContinuousLinearMap
    rw [hG, hB, ← combined_comp_normalCoordinates]
    simp only [ContinuousLinearMap.comp_assoc]
  exact hGB.trans (extends_outward_iff hN A D ν ξ P B hP hB hA hν)

end NoExoticSixSphere.OutwardGraphFrame

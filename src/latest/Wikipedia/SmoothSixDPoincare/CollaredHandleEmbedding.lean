import Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar
import Wikipedia.SmoothSixDPoincare.CollaredDiskAttachment
import Wikipedia.SmoothSixDPoincare.FramedSurgeryBodyAttachment

/-!
# Embed the whole collar-plus-handle model in the actual attachment

The original collar over the attaching face and the original whole handle
have exactly the model's identifications, and no others. The resulting
product-disk parametrization is a closed embedding in the actual quotient.
It retains both old collar coordinates and every whole-handle parameter.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CollaredHandleEmbedding

open CollaredDiskAttachment (Disk Sphere OldPiece Handle)

variable {E F X Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace X] [TopologicalSpace Y]
  (j : C(Sphere E × Disk F, X)) (i : C(X, Y)) (C : InwardBoundaryCollar i)

def faceMap : C(FramedSurgery.wholeAttachingFace E F, Y) :=
  i.comp (j.comp ⟨FramedSurgery.wholeFaceCoordinates E F,
    (FramedSurgery.wholeFaceCoordinates E F).continuous⟩)

theorem faceMap_injective (hi : Injective i) (hj : Injective j) : Injective (faceMap j i) :=
  hi.comp (hj.comp (FramedSurgery.wholeFaceCoordinates E F).injective)

def oldMap : C(OldPiece E F, FaceAttachment.Space (faceMap j i)) :=
  (FaceAttachment.oldMap (faceMap j i)).comp
    (C.map.comp ⟨fun a => (j (a.1, a.2.2), a.2.1),
      (j.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).prodMk
        (continuous_fst.comp continuous_snd)⟩)

def newMap : C(Handle E F, FaceAttachment.Space (faceMap j i)) :=
  FaceAttachment.handleMap (faceMap j i)

theorem oldMap_injective (hi : Injective i) (hj : Injective j) : Injective (oldMap j i C) := by
  intro a b hab
  have hbody := (FaceAttachment.oldMap_eq_oldMap (faceMap j i)
    (faceMap_injective j i hi hj) _ _).mp hab
  have hc := C.closedEmbedding.injective hbody
  have hf := hj (congrArg (fun p : X × unitInterval => p.1) hc)
  exact Prod.ext (congrArg (fun p : Sphere E × Disk F => p.1) hf)
    (Prod.ext (congrArg (fun p : X × unitInterval => p.2) hc)
      (congrArg (fun p : Sphere E × Disk F => p.2) hf))

theorem newMap_injective (hi : Injective i) (hj : Injective j) : Injective (newMap j i) :=
  fun a b hab => (FaceAttachment.handleMap_eq_handleMap (faceMap j i)
    (faceMap_injective j i hi hj) a b).mp hab

theorem oldMap_eq_newMap_iff (hi : Injective i) (hj : Injective j)
    (a : OldPiece E F) (k : Handle E F) :
    oldMap j i C a = newMap j i k ↔ CollaredDiskAttachment.Rel (.inl a) (.inr k) := by
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := (FaceAttachment.oldMap_eq_handleMap (faceMap j i)
      (faceMap_injective j i hi hj) _ _).mp h
    have hc : C.map (j (FramedSurgery.wholeFaceCoordinates E F u), 0) =
        C.map (j (a.1, a.2.2), a.2.1) :=
      (C.zero (j (FramedSurgery.wholeFaceCoordinates E F u))).trans hu
    have hp := C.closedEmbedding.injective hc
    have hf := hj (congrArg (fun p : X × unitInterval => p.1) hp)
    exact ⟨(congrArg (fun p : X × unitInterval => p.2) hp).symm,
      congrArg (fun p : Sphere E × Disk F => p.1.val) hf, congrArg Prod.snd hf⟩
  · rintro ⟨ht, he, hv⟩
    let u := (FramedSurgery.wholeFaceCoordinates E F).symm (a.1, a.2.2)
    have hk : u.val = k := Prod.ext (Subtype.ext he.symm) hv.symm
    change FaceAttachment.oldMap (faceMap j i) (C.map (j (a.1, a.2.2), a.2.1)) = _
    rw [ht, C.zero]
    exact (FaceAttachment.face_identification (faceMap j i) u).trans
      (congrArg (FaceAttachment.handleMap (faceMap j i)) hk)

def sumMap : OldPiece E F ⊕ Handle E F → FaceAttachment.Space (faceMap j i) :=
  Sum.elim (oldMap j i C) (newMap j i)

theorem continuous_sumMap : Continuous (sumMap j i C) :=
  continuous_sum_dom.mpr ⟨(oldMap j i C).continuous, (newMap j i).continuous⟩

theorem sumMap_respects (hi : Injective i) (hj : Injective j)
    (a b : OldPiece E F ⊕ Handle E F) (hab : CollaredDiskAttachment.Rel a b) :
    sumMap j i C a = sumMap j i C b := by
  cases a with
  | inl a =>
      cases b with
      | inl b => exact hab.elim
      | inr k => exact (oldMap_eq_newMap_iff j i C hi hj a k).mpr hab
  | inr k => cases b <;> exact hab.elim

def quotientMap (hi : Injective i) (hj : Injective j) :
    CollaredDiskAttachment.Space E F → FaceAttachment.Space (faceMap j i) :=
  Quot.lift (sumMap j i C) (sumMap_respects j i C hi hj)

theorem continuous_quotientMap (hi : Injective i) (hj : Injective j) :
    Continuous (quotientMap j i C hi hj) :=
  continuous_quot_lift (sumMap_respects j i C hi hj) (continuous_sumMap j i C)

theorem quotientMap_injective (hi : Injective i) (hj : Injective j) :
    Injective (quotientMap j i C hi hj) := by
  intro a b
  induction a using Quot.inductionOn with
  | _ a =>
      induction b using Quot.inductionOn with
      | _ b =>
          intro heq
          cases a with
          | inl a =>
              cases b with
              | inl b =>
                  exact congrArg (fun z => Quot.mk _ (Sum.inl z))
                    (oldMap_injective j i C hi hj heq)
              | inr k => exact Quot.sound ((oldMap_eq_newMap_iff j i C hi hj a k).mp heq)
          | inr k =>
              cases b with
              | inl a =>
                  exact (Quot.sound
                    ((oldMap_eq_newMap_iff j i C hi hj a k).mp heq.symm)).symm
              | inr l =>
                  exact congrArg (fun z => Quot.mk _ (Sum.inr z))
                    (newMap_injective j i hi hj heq)

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def parametrization (hi : Injective i) (hj : Injective j) :
    C(Handle E F, FaceAttachment.Space (faceMap j i)) :=
  ⟨quotientMap j i C hi hj ∘ CollaredDiskAttachment.homeomorph.symm,
    (continuous_quotientMap j i C hi hj).comp CollaredDiskAttachment.homeomorph.symm.continuous⟩

theorem parametrization_isClosedEmbedding [T2Space Y] [CompactSpace Y]
    (hi : Injective i) (hj : Injective j) :
    IsClosedEmbedding (parametrization j i C hi hj) := by
  let _ : T2Space (FaceAttachment.Space (faceMap j i)) :=
    FaceAttachment.t2Space (faceMap j i) (FramedSurgery.isClosed_wholeAttachingFace E F)
      (faceMap_injective j i hi hj)
  exact (parametrization j i C hi hj).continuous.isClosedEmbedding
    ((quotientMap_injective j i C hi hj).comp CollaredDiskAttachment.homeomorph.symm.injective)

theorem parametrization_old (hi : Injective i) (hj : Injective j) (a : OldPiece E F) :
    parametrization j i C hi hj (CollaredDiskAttachment.oldMap a) = oldMap j i C a :=
  congrArg (quotientMap j i C hi hj)
    (CollaredDiskAttachment.homeomorph.symm_apply_apply (Quot.mk _ (Sum.inl a)))

theorem parametrization_new (hi : Injective i) (hj : Injective j) (k : Handle E F) :
    parametrization j i C hi hj (CollaredDiskAttachment.newMap k) = newMap j i k :=
  congrArg (quotientMap j i C hi hj)
    (CollaredDiskAttachment.homeomorph.symm_apply_apply (Quot.mk _ (Sum.inr k)))

end Wikipedia.SmoothSixDPoincare.CollaredHandleEmbedding

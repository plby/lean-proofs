import Wikipedia.SmoothSixDPoincare.CollaredHandleEmbedding

/-!
# Original collar time is detected by the embedded product's negative radius

Any model point that lies in the original collar has exactly its specified
old radial coordinate. This includes the attaching-face seam, where both
presentations give original collar time zero.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CollaredHandleEmbedding

open CollaredDiskAttachment (Disk Sphere Handle)

variable {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [TopologicalSpace Y]
  (j : C(Sphere E × Disk F, X)) (i : C(X, Y)) (C : InwardBoundaryCollar i)
  (hi : Injective i) (hj : Injective j)

theorem parametrization_old_collar_norm (z : Handle E F) (x : X) (t : unitInterval)
    (h : parametrization j i C hi hj z =
      FaceAttachment.oldMap (faceMap j i) (C.map (x, t))) :
    2 * ‖z.1.val‖ = 1 + (t : ℝ) := by
  obtain ⟨q, rfl⟩ := (CollaredDiskAttachment.homeomorph (E := E) (F := F)).surjective z
  induction q using Quot.inductionOn with
  | _ q =>
      cases q with
      | inl a =>
          rw [CollaredDiskAttachment.homeomorph_inl, parametrization_old] at h
          have hbody := (FaceAttachment.oldMap_eq_oldMap (faceMap j i)
            (faceMap_injective j i hi hj) _ _).mp h
          have hc := C.closedEmbedding.injective hbody
          have ht : a.2.1 = t := congrArg (fun p : X × unitInterval => p.2) hc
          change 2 * ‖(CollaredDiskAttachment.collarPoint a.1 a.2.1).val‖ = _
          rw [CollaredDiskAttachment.norm_collarPoint, ht]
          unfold CollaredDiskAttachment.collarRadius
          ring
      | inr k =>
          rw [CollaredDiskAttachment.homeomorph_inr, parametrization_new] at h
          obtain ⟨u, hu, huk⟩ := (FaceAttachment.oldMap_eq_handleMap (faceMap j i)
            (faceMap_injective j i hi hj) _ _).mp h.symm
          have hc : C.map (j (FramedSurgery.wholeFaceCoordinates E F u), 0) = C.map (x, t) :=
            (C.zero (j (FramedSurgery.wholeFaceCoordinates E F u))).trans hu
          have ht : t = 0 :=
            (congrArg (fun p : X × unitInterval => p.2) (C.closedEmbedding.injective hc)).symm
          have hk : ‖k.1.val‖ = 1 :=
            (congrArg (fun p : Handle E F => ‖p.1.val‖) huk).symm.trans u.property
          change 2 * ‖(CollaredDiskAttachment.halfPoint k.1).val‖ = _
          rw [CollaredDiskAttachment.norm_halfPoint, hk, ht]
          norm_num

end Wikipedia.SmoothSixDPoincare.CollaredHandleEmbedding

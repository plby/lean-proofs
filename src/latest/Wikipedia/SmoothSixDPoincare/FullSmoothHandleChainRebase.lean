import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyCapEquiv

/-!
# Exact initial coordinate changes for full smooth handle chains

Only the first step changes. Births keep their whole disk, caps keep their
whole cap disk, and interior steps keep all framed handle parameters.
The entire original tail and terminal body stay unchanged.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  {dimension : ℕ} {U V W : SmoothBoundaryBody J} {k : ℕ}

def rebase (c : FullSmoothHandleChain J dimension U W k)
    (e : SmoothBoundaryBody.Equiv U V) : FullSmoothHandleChain J dimension V W k := by
  cases c with
  | nil r => exact .nil (e.symm.trans r)
  | birth D hdim r tail =>
      let D' := SmoothBoundaryBody.sumEquiv e (SmoothBoundaryBodyEquiv.refl D.space.inclusion)
      exact .birth D hdim (D'.symm.trans r) tail
  | @interior U Y W k E F _ _ _ _ _ _ m n _ _ A P hdim r tail =>
      let A' := A.postcompose e.boundary
      let Q := Classical.choice (FramedSurgery.nonempty_smoothBoundaryData A' n)
      let D := SmoothBoundaryBody.attachEquiv e A A' (fun _ => rfl) n P Q
      exact .interior A' Q hdim (D.symm.trans r) tail
  | cap j hj hopen hdim r tail =>
      let j' := SmoothBoundaryBody.capPostcompose e j
      have hj' := SmoothBoundaryBody.capPostcompose_isClosedEmbedding e j hj
      have hopen' := SmoothBoundaryBody.capPostcompose_isOpen e j hopen
      let D := SmoothBoundaryBody.capEquiv e j hj hopen j' hj' hopen' (fun _ => rfl)
      exact .cap j' hj' hopen' hdim (D.symm.trans r) tail

def rebasePieces (c : FullSmoothHandleChain J dimension U W k)
    (e : SmoothBoundaryBody.Equiv U V) : c.pieces ≃ₜ (c.rebase e).pieces := by
  cases c <;> exact Homeomorph.refl _

theorem rebase_sourceMap (c : FullSmoothHandleChain J dimension U W k)
    (e : SmoothBoundaryBody.Equiv U V) (y : V.body) :
    (c.rebase e).sourceMap y = c.sourceMap (e.body.symm y) := by
  cases c with
  | nil r => rfl
  | birth D hdim r tail => rfl
  | @interior U Y W k E F _ _ _ _ _ _ m n _ _ A P hdim r tail =>
      let A' := A.postcompose e.boundary
      let Q := Classical.choice (FramedSurgery.nonempty_smoothBoundaryData A' n)
      exact congrArg (fun z => tail.sourceMap (r.body z))
        (SmoothBoundaryBody.attachEquiv_symm_old e A A' (fun _ => rfl) n P Q y)
  | cap j hj hopen hdim r tail =>
      exact congrArg (fun z => tail.sourceMap (r.body z))
        (SmoothBoundaryBody.capEquiv_symm_old e j hj hopen _
          (SmoothBoundaryBody.capPostcompose_isClosedEmbedding e j hj)
          (SmoothBoundaryBody.capPostcompose_isOpen e j hopen) (fun _ => rfl) y)

theorem rebase_piecesMap (c : FullSmoothHandleChain J dimension U W k)
    (e : SmoothBoundaryBody.Equiv U V) (z : c.pieces) :
    (c.rebase e).piecesMap (c.rebasePieces e z) = c.piecesMap z := by
  cases c with
  | nil r => exact PEmpty.elim z
  | birth D hdim r tail => cases z <;> rfl
  | @interior U Y W k E F _ _ _ _ _ _ m n _ _ A P hdim r tail =>
      let A' := A.postcompose e.boundary
      let Q := Classical.choice (FramedSurgery.nonempty_smoothBoundaryData A' n)
      cases z with
      | inl z =>
          exact congrArg (fun x => tail.sourceMap (r.body x))
            (SmoothBoundaryBody.attachEquiv_symm_handle e A A' (fun _ => rfl) n P Q z)
      | inr z => rfl
  | cap j hj hopen hdim r tail =>
      cases z with
      | inl z =>
          exact congrArg (fun x => tail.sourceMap (r.body x))
            (SmoothBoundaryBody.capEquiv_symm_disk e j hj hopen _
              (SmoothBoundaryBody.capPostcompose_isClosedEmbedding e j hj)
              (SmoothBoundaryBody.capPostcompose_isOpen e j hopen) (fun _ => rfl) z)
      | inr z => rfl

theorem rebase_indices (c : FullSmoothHandleChain J dimension U W k)
    (e : SmoothBoundaryBody.Equiv U V) : (c.rebase e).indices = c.indices := by
  cases c <;> rfl

end Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

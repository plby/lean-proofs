import Wikipedia.SmoothSixDPoincare.ClosedCoverHomeomorph
import Mathlib.Topology.ContinuousMap.Basic

/-! # Continuous maps defined on two closed embedded pieces -/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.ClosedCover

variable {R P X Y : Type*} [TopologicalSpace R] [TopologicalSpace P]
  [TopologicalSpace X] [TopologicalSpace Y]
  (r : R → X) (p : P → X) (hr : IsClosedEmbedding r) (hp : IsClosedEmbedding p)
  (hcover : range r ∪ range p = univ)
  (f : C(R, Y)) (g : C(P, Y)) (hagree : ∀ a b, r a = p b → f a = g b)

/-- Glue continuous maps on actual closed embedded pieces with their original incidences. -/
def mapOfClosedPieces : C(X, Y) := by
  let a := hr.isEmbedding.toHomeomorph
  let b := hp.isEmbedding.toHomeomorph
  refine ⟨glue hcover (fun x => f (a.symm x)) (fun x => g (b.symm x)), ?_⟩
  apply continuous_glue hcover hr.isClosed_range hp.isClosed_range _ _
    (f.continuous.comp a.symm.continuous) (g.continuous.comp b.symm.continuous)
  intro x y hxy
  apply hagree
  exact (congrArg Subtype.val (a.apply_symm_apply x)).trans
    (hxy.trans (congrArg Subtype.val (b.apply_symm_apply y)).symm)

theorem mapOfClosedPieces_left (x : R) :
    mapOfClosedPieces r p hr hp hcover f g hagree (r x) = f x := by
  let a := hr.isEmbedding.toHomeomorph
  let b := hp.isEmbedding.toHomeomorph
  change glue hcover (fun z => f (a.symm z)) (fun z => g (b.symm z)) (r x) = f x
  exact (glue_left hcover _ _ ⟨r x, mem_range_self x⟩).trans
    (congrArg f (a.symm_apply_apply x))

theorem mapOfClosedPieces_right (x : P) :
    mapOfClosedPieces r p hr hp hcover f g hagree (p x) = g x := by
  let a := hr.isEmbedding.toHomeomorph
  let b := hp.isEmbedding.toHomeomorph
  have hagree' : ∀ u : range r, ∀ v : range p, (u : X) = v →
      f (a.symm u) = g (b.symm v) := by
    intro u v huv
    apply hagree
    exact (congrArg Subtype.val (a.apply_symm_apply u)).trans
      (huv.trans (congrArg Subtype.val (b.apply_symm_apply v)).symm)
  change glue hcover (fun z => f (a.symm z)) (fun z => g (b.symm z)) (p x) = g x
  exact (glue_right hcover _ _ hagree' ⟨p x, mem_range_self x⟩).trans
    (congrArg g (b.symm_apply_apply x))

end Wikipedia.SmoothSixDPoincare.ClosedCover

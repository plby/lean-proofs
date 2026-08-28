import Wikipedia.NoExoticSixSphere.OpenPreimageDiffeomorph
import Wikipedia.NoExoticSixSphere.StabilizedFramedDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapseClopenEmbedding

/-!
# Restrict an actual stabilized framed comparison to a native clopen component

The target component is the image under the given diffeomorphism,
expressed as an inverse image under its inverse. Restriction retains
the original ambient and normal isometries and every original frame
column. Both open-submanifold atlases are inherited, not transported.
The complementary subspaces have the actual inverse homeomorphism.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedFramedDiffeomorph

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {n : ℕ} {M M' : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [TopologicalSpace M'] [ChartedSpace (Vector n) M']
  {e : EuclideanEmbedding n M} {e' : EuclideanEmbedding n M'}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  {a' : SmoothRangeFrame (𝓡 n) e'.normalProjection e'.NormalModel}
  (F : StabilizedFramedDiffeomorph e a e' a') (U : Opens M)

def clopenImage : Opens M' := openDiffeomorphPreimage F.diffeomorph.symm U

theorem mem_clopenImage (y : M') : y ∈ F.clopenImage U ↔ F.diffeomorph.symm y ∈ U := Iff.rfl

theorem clopenImage_closed (hU : IsClosed (U : Set M)) :
    IsClosed (F.clopenImage U : Set M') := hU.preimage F.diffeomorph.symm.continuous

def restrictClopen (hU : IsClosed (U : Set M)) :
    StabilizedFramedDiffeomorph (ClopenEmbedding.restrict e U hU)
      (ClopenEmbedding.restrictNormalFrame e U hU a)
      (ClopenEmbedding.restrict e' (F.clopenImage U) (F.clopenImage_closed U hU))
      (ClopenEmbedding.restrictNormalFrame e' (F.clopenImage U)
        (F.clopenImage_closed U hU) a') where
  extra := F.extra
  ambient := F.ambient
  normal := F.normal
  diffeomorph := (openPreimageDiffeomorph F.diffeomorph.symm U).symm
  embedding_eq x := F.embedding_eq x.val
  frame_eq x v := F.frame_eq x.val v

theorem restrictClopen_extra (hU : IsClosed (U : Set M)) :
    (F.restrictClopen U hU).extra = F.extra := rfl

theorem restrictClopen_diffeomorph_val (hU : IsClosed (U : Set M)) (x : U) :
    ((F.restrictClopen U hU).diffeomorph x).val = F.diffeomorph x.val := rfl

def clopenComplementHomeomorph : ↥((F.clopenImage U : Set M')ᶜ) ≃ₜ ↥((U : Set M)ᶜ) :=
  F.diffeomorph.symm.toHomeomorph.subtype (fun _ ↦ Iff.rfl)

theorem clopenComplementHomeomorph_val (y : ↥((F.clopenImage U : Set M')ᶜ)) :
    (F.clopenComplementHomeomorph U y).val = F.diffeomorph.symm y.val := rfl

end NoExoticSixSphere.StabilizedFramedDiffeomorph

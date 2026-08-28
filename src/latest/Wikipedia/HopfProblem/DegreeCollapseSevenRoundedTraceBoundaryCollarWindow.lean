import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedTraceBoundaryCollar
import Wikipedia.NoExoticSixSphere.RoundedCornerGraphWindow

/-!
# The actual rounded boundary collar has an exact interval parameter

The previously constructed height and radius margins are wider than the
rounding support. Consequently the sphere-product parameter window is
exactly the interval from negative collar height to the squared-radius gap.
-/

noncomputable section

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner SmoothCornerRounding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem graphRadius_lt_iff (u : ℝ) :
    graphRadius (bump A) (UnroundedTrace.handleRadius A) u < A.radius ↔
      -radialGap A < graphRadial (bump A) u := by
  have hs := graphRadius_sq (bump A) (UnroundedTrace.handleRadius A) u
  have hp := graphRadius_pos (bump A) (UnroundedTrace.handleRadius_pos A) u
  dsimp only [radialGap]
  constructor
  · intro h
    nlinarith [A.radius_pos]
  · intro h
    by_contra hn
    have hle := le_of_not_gt hn
    nlinarith [A.radius_pos]

theorem mem_boundaryCollarParameters_iff_interval (p : BoundaryParameters) :
    p ∈ boundaryCollarParameters A ↔
      p.2.2 ∈ Ioo (-collarHeight A) (radialGap A) := by
  rw [mem_boundaryCollarParameters_iff, graphRadius_lt_iff]
  have ht := graphHeight_nonpos (bump A) p.2.2
  have hδ := collarHeight_pos A
  constructor
  · rintro ⟨hq, hlow, _⟩
    exact (graph_window_iff (bump A) (twice_outer_lt_height A)
      (twice_outer_lt_radialGap A)).mp ⟨hlow, hq⟩
  · intro hp
    obtain ⟨hlow, hq⟩ := (graph_window_iff (bump A) (twice_outer_lt_height A)
      (twice_outer_lt_radialGap A)).mpr hp
    exact ⟨hq, hlow, ht.trans_lt hδ⟩

def boundaryCollarInterval : Opens ℝ :=
  ⟨Ioo (-collarHeight A) (radialGap A), isOpen_Ioo⟩

def boundaryCollarProductEquiv : boundaryCollarParameters A ≃
    Sphere 3 × (Sphere 3 × boundaryCollarInterval A) where
  toFun p := (p.val.1, p.val.2.1, ⟨p.val.2.2,
    (mem_boundaryCollarParameters_iff_interval A p.val).mp p.property⟩)
  invFun p := ⟨(p.1, p.2.1, p.2.2.val),
    (mem_boundaryCollarParameters_iff_interval A _).mpr p.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def boundaryCollarProductDiffeomorph : boundaryCollarParameters A ≃ₘ⟮boundaryParameterModel,
    boundaryParameterModel⟯ Sphere 3 × (Sphere 3 × boundaryCollarInterval A) := by
  refine
    { toEquiv := boundaryCollarProductEquiv A
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have hv : ContMDiff boundaryParameterModel boundaryParameterModel ∞
        (Subtype.val : boundaryCollarParameters A → BoundaryParameters) := contMDiff_subtype_val
    have ht : ContMDiff boundaryParameterModel 𝓘(ℝ, ℝ) ∞
        (fun p : boundaryCollarParameters A ↦ (boundaryCollarProductEquiv A p).2.2) := by
      apply (ContMDiff.subtypeVal_comp_iff (boundaryCollarInterval A) _).mp
      exact contMDiff_snd.comp (contMDiff_snd.comp hv)
    exact (contMDiff_fst.comp hv).prodMk ((contMDiff_fst.comp (contMDiff_snd.comp hv)).prodMk ht)
  · apply (ContMDiff.subtypeVal_comp_iff (boundaryCollarParameters A) _).mp
    exact contMDiff_fst.prodMk ((contMDiff_fst.comp contMDiff_snd).prodMk
      (contMDiff_subtype_val.comp (contMDiff_snd.comp contMDiff_snd)))

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

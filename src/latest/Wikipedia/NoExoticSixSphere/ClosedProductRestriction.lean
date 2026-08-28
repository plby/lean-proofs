import Wikipedia.NoExoticSixSphere.PartialFrames
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Restricting an embedded compact product to a smaller closed transverse ball
-/

noncomputable section

open Function Metric Topology

namespace NoExoticSixSphere

open GLOrthonormalization

theorem restrict_closedProduct_embedding {q : ℕ} {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TopologicalSpace Y] (H : X × Vector q → Y) {r ε : ℝ} (hεr : ε ≤ r)
    (hH : IsClosedEmbedding (fun p : X × closedBall (0 : Vector q) r ↦ H (p.1, p.2.val))) :
    IsClosedEmbedding (fun p : X × closedBall (0 : Vector q) ε ↦ H (p.1, p.2.val)) := by
  let j : X × closedBall (0 : Vector q) ε → X × closedBall (0 : Vector q) r :=
    fun p ↦ (p.1, ⟨p.2.val, (closedBall_subset_closedBall hεr) p.2.property⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hji : Injective j := by
    intro p z hpz
    exact Prod.ext (congrArg (Prod.fst : X × closedBall (0 : Vector q) r → X) hpz)
      (Subtype.ext (congrArg (fun z : X × closedBall (0 : Vector q) r ↦ z.2.val) hpz))
  exact hH.comp (hj.isClosedEmbedding hji)

end NoExoticSixSphere

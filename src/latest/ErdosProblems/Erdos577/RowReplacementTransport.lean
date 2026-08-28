import ErdosProblems.Erdos577.RowReplacementModel
import ErdosProblems.Erdos577.ReplacementFactors

/-! Transport the single-row insertion certificate without edges between distinct arms. -/

namespace Erdos577.JointFirstRows

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem GoodPath.transport (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (row : Fin 16) (hrow : ∀ i : Fin 4, row.val.testBit i.val = true → G.Adj z (q i))
    (u : Fin 4) (t : Fin 3) (h : GoodPath (Unattached.diagonal q) row u t) :
    QuadOn G (insert z (q.support.erase (q u))) := by
  obtain ⟨hcover, hne, h01, h12, h0, h2⟩ := h
  let p := pathVertices u t
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  have himage : ({p 0, p 1, p 2} : Finset (Fin 4)).image q = q.support.erase (q u) := by
    rw [hcover, image_erase hinj]
    rfl
  have hset : ({q (p 0), q (p 1), q (p 2)} : Finset V) = q.support.erase (q u) := by
    simpa only [image_insert, image_singleton] using himage
  have hzm : z ≠ q (p 1) := fun he ↦ hz ((q.mem_support z).mpr ⟨p 1, he.symm⟩)
  have hquad : QuadOn G {z, q (p 0), q (p 1), q (p 2)} :=
    QuadOn.of_vertices hzm (hinj.ne hne) (hrow _ h0)
      ((q.model_adj_iff _ _).mp h01) ((q.model_adj_iff _ _).mp h12) (hrow _ h2).symm
  have he : ({z, q (p 0), q (p 1), q (p 2)} : Finset V) =
      insert z (q.support.erase (q u)) := by rw [← hset]
  exact he ▸ hquad

theorem replacement_mask_transport (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (row : Fin 16) (hrow : ∀ i : Fin 4, row.val.testBit i.val = true → G.Adj z (q i))
    (u : Fin 4) (h : (replacementMask (Unattached.diagonal q) row).testBit u.val = true) :
    QuadOn G (insert z (q.support.erase (q u))) :=
  GoodPath.transport q z hz row hrow u _ (replacement_mask_sound _ row u h)

end Erdos577.JointFirstRows

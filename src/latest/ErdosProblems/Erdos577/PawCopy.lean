import ErdosProblems.Erdos577.Paws
import ErdosProblems.Erdos577.CopyCounts

/-! Injective graph copies transport ordered paws and preserve their exact supports. -/

namespace Erdos577

open Finset

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def Paw.image (p : Paw G) (f : G.Copy H) : Paw H where
  vertices := p.vertices.trans f.toEmbedding
  pendant := f.toHom.map_rel' p.pendant
  edge12 := f.toHom.map_rel' p.edge12
  edge13 := f.toHom.map_rel' p.edge13
  edge23 := f.toHom.map_rel' p.edge23

variable [DecidableEq V] [DecidableEq W]

lemma Paw.image_support (p : Paw G) (f : G.Copy H) :
    (p.image f).support = p.support.image f := by
  rw [Paw.support, Paw.support, tupleSupport, tupleSupport, image_image]
  rfl

lemma Paw.image_triangle (p : Paw G) (f : G.Copy H) :
    (p.image f).triangle = p.triangle.image f := by
  simp only [Paw.triangle, image_insert, image_singleton]
  rfl

lemma Quadrilateral.support_copy_comp (q : Quadrilateral G) (f : G.Copy H) :
    Quadrilateral.support (f.comp q) = q.support.image f := by
  rw [Quadrilateral.support, Quadrilateral.support, image_image]
  rfl

end Erdos577

import ErdosProblems.Erdos577.PawLabels

/-! Label the old triangle, an outside singleton, and the old quadrilateral. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

namespace Paw

def outsideTuple (p : Paw G) (z : V) (_hz : z ∉ p.support) : Fin 4 ↪ V :=
  p.vertices.setValue 0 z

@[simp] lemma outsideTuple_zero (p : Paw G) (z : V) (hz : z ∉ p.support) :
    p.outsideTuple z hz 0 = z := Function.Embedding.setValue_eq _ _ _

lemma outsideTuple_nonzero (p : Paw G) (z : V) (hz : z ∉ p.support)
    {i : Fin 4} (hi : i ≠ 0) : p.outsideTuple z hz i = p.vertices i :=
  Function.Embedding.setValue_eq_of_ne hi
    (fun he ↦ hz ((mem_tupleSupport _ _).mpr ⟨i, he⟩))

lemma outsideTuple_support (p : Paw G) (z : V) (hz : z ∉ p.support) :
    tupleSupport (p.outsideTuple z hz) = insert z p.triangle := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide +kernel
  have h0 := p.outsideTuple_zero z hz
  have h1 := p.outsideTuple_nonzero z hz (i := 1) (by decide)
  have h2 := p.outsideTuple_nonzero z hz (i := 2) (by decide)
  have h3 := p.outsideTuple_nonzero z hz (i := 3) (by decide)
  simp only [tupleSupport, hu, image_insert, image_singleton, h0, h1, h2, h3, triangle]

end Paw

namespace OutsideLabeling

lemma outside_not_paw (p : Paw G) (q : Quadrilateral G) {z : V}
    (hz : z ∉ p.support ∪ q.support) : z ∉ p.support :=
  fun h ↦ hz (mem_union_left _ h)

lemma outside_not_quad (p : Paw G) (q : Quadrilateral G) {z : V}
    (hz : z ∉ p.support ∪ q.support) : z ∉ q.support :=
  fun h ↦ hz (mem_union_right _ h)

def labeling (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) : Fin 8 ↪ V :=
  joinTuples (p.outsideTuple z (outside_not_paw p q hz)) q.toEmbedding (by
    rw [p.outsideTuple_support]
    apply disjoint_left.mpr
    intro v hv hvq
    rcases mem_insert.mp hv with rfl | hv
    · exact outside_not_quad p q hz hvq
    · have hvp : v ∈ p.support := by rw [p.support_eq]; exact mem_insert_of_mem hv
      exact disjoint_left.mp hd hvp hvq)

lemma labeling_zero (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) : labeling p q hd z hz 0 = z := by
  change joinTuples _ _ _ (Fin.castAdd 4 (0 : Fin 4)) = z
  rw [joinTuples_left, p.outsideTuple_zero]

lemma labeling_nonzero (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) {i : Fin 4} (hi : i ≠ 0) :
    labeling p q hd z hz (Fin.castAdd 4 i) = p.vertices i := by
  change joinTuples _ _ _ (Fin.castAdd 4 i) = p.vertices i
  rw [joinTuples_left, p.outsideTuple_nonzero z _ hi]

lemma labeling_right (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) (i : Fin 4) :
    labeling p q hd z hz (Fin.natAdd 4 i) = q i := joinTuples_right _ _ _ i

lemma labeling_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (z : V) (hz : z ∉ p.support ∪ q.support) :
    univ.image (labeling p q hd z hz) = insert z (p.triangle ∪ q.support) := by
  change tupleSupport (labeling p q hd z hz) = _
  rw [labeling, tupleSupport_joinTuples, p.outsideTuple_support]
  change insert z p.triangle ∪ q.support = insert z (p.triangle ∪ q.support)
  rw [insert_union]

end OutsideLabeling

end Erdos577

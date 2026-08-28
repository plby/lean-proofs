import ErdosProblems.Erdos577.OutsideLabeling
import ErdosProblems.Erdos577.JointCoreModel

/-! Core labels require the new vertex to avoid only the seven-vertex core.
In particular, the new vertex is allowed to equal the original paw leaf. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def outsideTuple (p : Paw G) (u : V) : Fin 4 ↪ V := p.vertices.setValue 0 u

lemma outsideTuple_zero (p : Paw G) (u : V) : outsideTuple p u 0 = u :=
  Function.Embedding.setValue_eq _ _ _

lemma outsideTuple_nonzero (p : Paw G) (u : V) (hu : u ∉ p.triangle)
    (i : Fin 4) (hi : i ≠ 0) : outsideTuple p u i = p.vertices i := by
  apply Function.Embedding.setValue_eq_of_ne hi
  intro he
  apply hu
  rw [← he]
  fin_cases i
  · exact False.elim (hi rfl)
  all_goals simp [Paw.triangle]

lemma outsideTuple_support (p : Paw G) (u : V) (hu : u ∉ p.triangle) :
    tupleSupport (outsideTuple p u) = insert u p.triangle := by
  have he : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide +kernel
  simp only [tupleSupport, he, image_insert, image_singleton, outsideTuple_zero,
    outsideTuple_nonzero p u hu 1 (by decide), outsideTuple_nonzero p u hu 2 (by decide),
    outsideTuple_nonzero p u hu 3 (by decide), Paw.triangle]

def labeling (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.triangle q.support)
    (u : V) (hu : u ∉ p.triangle ∪ q.support) : Fin 8 ↪ V :=
  joinTuples (outsideTuple p u) q.toEmbedding (by
    rw [outsideTuple_support p u (fun hv ↦ hu (mem_union_left _ hv))]
    apply disjoint_left.mpr
    intro v hv hvq
    rcases mem_insert.mp hv with rfl | hv
    · exact hu (mem_union_right _ hvq)
    · exact disjoint_left.mp hd hv hvq)

lemma labeling_zero (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.triangle q.support)
    (u : V) (hu : u ∉ p.triangle ∪ q.support) : labeling p q hd u hu 0 = u := by
  change joinTuples _ _ _ (Fin.castAdd 4 (0 : Fin 4)) = u
  rw [joinTuples_left, outsideTuple_zero]

lemma labeling_nonzero (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.triangle q.support)
    (u : V) (hu : u ∉ p.triangle ∪ q.support) (i : Fin 4) (hi : i ≠ 0) :
    labeling p q hd u hu (Fin.castAdd 4 i) = p.vertices i := by
  change joinTuples _ _ _ (Fin.castAdd 4 i) = _
  rw [joinTuples_left, outsideTuple_nonzero p u (fun hv ↦ hu (mem_union_left _ hv)) i hi]

lemma labeling_right (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.triangle q.support)
    (u : V) (hu : u ∉ p.triangle ∪ q.support) (i : Fin 4) :
    labeling p q hd u hu (Fin.natAdd 4 i) = q i := joinTuples_right _ _ _ i

lemma labeling_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.triangle q.support)
    (u : V) (hu : u ∉ p.triangle ∪ q.support) :
    univ.image (labeling p q hd u hu) = insert u (p.triangle ∪ q.support) := by
  change tupleSupport (labeling p q hd u hu) = _
  rw [labeling, tupleSupport_joinTuples,
    outsideTuple_support p u (fun hv ↦ hu (mem_union_left _ hv)), insert_union]
  rfl

lemma labeling_core (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.triangle q.support)
    (u : V) (hu : u ∉ p.triangle ∪ q.support) :
    core.image (labeling p q hd u hu) = p.triangle ∪ q.support := by
  have he : core = (univ : Finset (Fin 8)).erase 0 := by decide +kernel
  rw [he, image_erase (labeling p q hd u hu).injective, labeling_image, labeling_zero,
    erase_insert hu]

lemma labeling_block (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.triangle q.support)
    (u : V) (hu : u ∉ p.triangle ∪ q.support) :
    block.image (labeling p q hd u hu) = q.support := by
  have he : block = (univ : Finset (Fin 4)).image (Fin.natAdd 4) := by decide +kernel
  rw [he, image_image]
  simp only [Function.comp_def, labeling_right]
  rfl

lemma exists_core_index (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.triangle q.support)
    (u : V) (hu : u ∉ p.triangle ∪ q.support) {v : V} (hv : v ∈ p.triangle ∪ q.support) :
    ∃ i : Fin 7, labeling p q hd u hu i.succ = v := by
  rw [← labeling_core p q hd u hu] at hv
  obtain ⟨a, ha, hav⟩ := mem_image.mp hv
  have hn : a ≠ 0 := by
    have he : core = (univ : Finset (Fin 8)).erase 0 := by decide +kernel
    rw [he] at ha
    exact (mem_erase.mp ha).1
  let i : Fin 7 := ⟨a.val - 1, by omega⟩
  have hi : i.succ = a := Fin.ext (by dsimp [i]; omega)
  exact ⟨i, hi ▸ hav⟩

end Erdos577.JointCore

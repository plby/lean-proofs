import ErdosProblems.Erdos577.FullRowInsertions
import ErdosProblems.Erdos577.CommonPathFactor
import ErdosProblems.Erdos577.PartitionReplacement

/-! The common insertion closes the paw's three-vertex path and joins an actual complement. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def pathTriple (p : Paw G) : Finset V := {p.leaf, p.center, p.vertices 2}

lemma pathTriple_subset (p : Paw G) : pathTriple p ⊆ p.support := by
  intro u hu
  simp only [pathTriple, mem_insert, mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact (mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩
  · exact (mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩
  · exact (mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩

lemma third_not_mem_pathTriple (p : Paw G) : p.vertices 3 ∉ pathTriple p := by
  simp only [pathTriple, Paw.leaf, Paw.center, mem_insert, mem_singleton,
    p.vertices.injective.eq_iff]
  decide

lemma insert_third_pathTriple (p : Paw G) : insert (p.vertices 3) (pathTriple p) = p.support := by
  rw [p.support_eq]
  ext u
  simp only [pathTriple, Paw.triangle, Paw.center, mem_insert, mem_singleton]
  tauto

lemma common_path_factor (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (u : V) (hu : u ∉ p.support ∪ q.support)
    (h : CommonReplacement G p.leaf (p.vertices 2) u q.support) :
    LocalFactor G (insert u (pathTriple p ∪ q.support)) := by
  apply LocalFactor.of_common_path p.leaf p.center (p.vertices 2) u
    (p.vertices.injective.ne (by decide : (0 : Fin 4) ≠ 2)) p.pendant p.edge12
    (hd.mono_left (pathTriple_subset p)) ?_ h
  exact fun hh ↦ hu ((union_subset_union (pathTriple_subset p) subset_rfl) hh)

lemma partition_of_common_insertion (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (t : Finset V)
    (hdis : Disjoint (p.support ∪ q.support) t) {u : V} (hu : u ∈ t)
    (h : CommonReplacement G p.leaf (p.vertices 2) u q.support)
    (hrep : Nonempty (BlockPartition G (insert (p.vertices 3) (t.erase u)))) :
    Nonempty (BlockPartition G (p.support ∪ (q.support ∪ t))) := by
  have hout : u ∉ p.support ∪ q.support := fun hh ↦ disjoint_left.mp hdis hh hu
  obtain ⟨f⟩ := (common_path_factor p q hd u hout h).partition
  obtain ⟨r⟩ := hrep
  have hdis' : Disjoint (pathTriple p ∪ q.support) t :=
    hdis.mono_left (union_subset_union (pathTriple_subset p) subset_rfl)
  have hthird : p.vertices 3 ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
  have hx : p.vertices 3 ∉ (pathTriple p ∪ q.support) ∪ t := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · exact third_not_mem_pathTriple p hh
      · exact disjoint_left.mp hd hthird hh
    · exact disjoint_left.mp hdis (mem_union_left _ hthird) hh
  let parts := BlockPartition.replacementUnion hdis' hx hu f r
  have he : insert (p.vertices 3) ((pathTriple p ∪ q.support) ∪ t) =
      p.support ∪ (q.support ∪ t) := by
    rw [← insert_union, ← insert_union, insert_third_pathTriple, union_assoc]
  exact ⟨he ▸ parts⟩

variable [Fintype V]

theorem hasPacking_of_common_insertion {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hd : Disjoint p.support q.support)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (hsn : s ∉ bs)
    {u : V} (hu : u ∈ bs.biUnion id)
    (h : CommonReplacement G p.leaf (p.vertices 2) u q.support)
    (hrep : Nonempty (BlockPartition G (insert (p.vertices 3) ((bs.biUnion id).erase u)))) :
    HasPacking G k := by
  have hpdis : Disjoint p.support (bs.biUnion id) := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right
      (biUnion_subset_biUnion_of_subset_left id hbs)
  have hqdis : Disjoint q.support (bs.biUnion id) := by
    rw [hq, disjoint_biUnion_right]
    intro a ha
    exact c.property.blocks_disjoint hs (hbs ha) (fun he ↦ hsn (he.symm ▸ ha))
  obtain ⟨parts⟩ := partition_of_common_insertion p q hd (bs.biUnion id)
    (disjoint_union_left.mpr ⟨hpdis, hqdis⟩) hu h hrep
  have hsel : insert s bs ⊆ c.blocks := insert_subset hs hbs
  have he : p.support ∪ (q.support ∪ bs.biUnion id) =
      c.remainder ∪ (insert s bs).biUnion id := by
    rw [hp, hq]
    simp only [biUnion_insert, id_eq]
  exact c.complementPartition.hasPacking_of_selected_factor hcard (insert s bs) hsel (he ▸ parts)

end Erdos577.FullRow

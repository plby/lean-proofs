import ErdosProblems.Erdos577.WeightedTwelveInsideCore

/-! Exact complements for either mixed pair, and the final old-center quadrilateral. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma DensePair.mixed_complement {p : Paw G} {d : Quadrilateral G} (h : DensePair p d)
    (i : Fin 4) (hi : i = 2 ∨ i = 3) :
    QuadOn G ((p.triangle ∪ d.support) \ {d i, p.center, p.vertices 2}) := by
  have hm (j : Fin 4) : d j ∈ d.support := (d.mem_support _).mpr ⟨j, rfl⟩
  have hpout (j : Fin 4) : p.vertices j ∉ d.support := fun hh ↦
    disjoint_left.mp h.disjoint ((mem_tupleSupport p.vertices _).mpr ⟨j, rfl⟩) hh
  have hiT : d i ∉ p.triangle := fun hh ↦ disjoint_left.mp h.disjoint
    ((p.support_eq ▸ subset_insert _ _) hh) (hm i)
  have hT : p.triangle \ {d i, p.center, p.vertices 2} = {p.vertices 3} := by
    rw [sdiff_insert_of_notMem hiT]
    ext v
    simp only [Paw.triangle, Paw.center, mem_sdiff, mem_insert, mem_singleton, not_or]
    constructor
    · rintro ⟨hmem, h1, h2⟩
      rcases hmem with hmem | hmem | hmem
      · exact False.elim (h1 hmem)
      · exact False.elim (h2 hmem)
      · exact hmem
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), p.vertices.injective.ne (by decide),
        p.vertices.injective.ne (by decide)⟩
  have hset : ({d i, p.center, p.vertices 2} : Finset V) =
      {p.center, p.vertices 2, d i} := by
    rw [insert_comm (d i) p.center, pair_comm (d i) (p.vertices 2)]
  have hA : d.support \ {d i, p.center, p.vertices 2} = d.support.erase (d i) := by
    rw [hset]
    change d.support \ {p.vertices 1, p.vertices 2, d i} = _
    rw [sdiff_insert_of_notMem (hpout 1), sdiff_insert_of_notMem (hpout 2),
      sdiff_singleton_eq_erase]
  have hdall : d.support = {d 0, d 1, d 2, d 3} := by
    rw [Quadrilateral.support, show (univ : Finset (Fin 4)) = {0, 1, 2, 3} from by decide]
    simp
  have hne (a b : Fin 4) (hab : a ≠ b) : d a ≠ d b := d.injective.ne hab
  rw [union_sdiff_distrib, hT, hA, singleton_union]
  rcases hi with rfl | rfl
  · have he : d.support.erase (d 2) = {d 3, d 0, d 1} := by
      ext v
      simp only [hdall, mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hv, hh | hh | hh | hh⟩
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr hh)
        · exact False.elim (hv hh)
        · exact Or.inl hh
      · rintro (rfl | rfl | rfl) <;> simp [hne]
    rw [he]
    exact h.other_complement 3 (Or.inr rfl)
  · have he : d.support.erase (d 3) = {d 2, d 0, d 1} := by
      ext v
      simp only [hdall, mem_erase, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hv, hh | hh | hh | hh⟩
        · exact Or.inr (Or.inl hh)
        · exact Or.inr (Or.inr hh)
        · exact Or.inl hh
        · exact False.elim (hv hh)
      · rintro (rfl | rfl | rfl) <;> simp [hne]
    rw [he]
    exact h.other_complement 2 (Or.inl rfl)

end Erdos577.WeightedTwelve

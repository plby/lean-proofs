import ErdosProblems.Erdos547.BoundedPiece
import ErdosProblems.Erdos547.TreeCore
import ErdosProblems.Erdos547.DegreeExtraction

/-!
# Independent low-degree vertices in a pendant piece
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph BigOperators

variable {U : Type*} [Fintype U] (T : SimpleGraph U) [DecidableRel T.Adj]

open scoped Classical in
/-- At least half the vertices of a nontrivial tree have degree at most two
and are different from any prescribed root. -/
theorem card_le_twice_nonroot_low_degree (hT : T.IsTree) [Nontrivial U] (r : U) :
    Fintype.card U ≤ 2 * ((Finset.univ : Finset U).filter
      fun v ↦ v ≠ r ∧ T.degree v ≤ 2).card := by
  classical
  let H := (Finset.univ : Finset U).filter fun v ↦ v ≠ r ∧ 2 < T.degree v
  let L := (Finset.univ : Finset U).filter fun v ↦ v ≠ r ∧ T.degree v ≤ 2
  have hsum : Fintype.card U + 2 * H.card ≤ ∑ v, T.degree v := by
    calc
      _ = ∑ v : U, (1 + 2 * if v ≠ r ∧ 2 < T.degree v then 1 else 0) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, smul_eq_mul, mul_one, Finset.sum_boole]
        rfl
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v _
        have hpos := hT.connected.preconnected.degree_pos_of_nontrivial v
        split_ifs <;> omega
  have hsplit : L.card + H.card + 1 = Fintype.card U := by
    have hpartition : L ∪ H = (Finset.univ : Finset U).erase r := by
      ext v
      simp only [L, H, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_erase, and_true]
      by_cases hv : v = r <;> simp [hv, le_or_gt]
    have hdis : Disjoint L H := by
      apply Finset.disjoint_left.mpr
      intro v hvL hvH
      have hL := (Finset.mem_filter.mp hvL).2.2
      have hH := (Finset.mem_filter.mp hvH).2.2
      omega
    rw [← Finset.card_union_of_disjoint hdis, hpartition]
    simpa using Finset.card_erase_add_one (Finset.mem_univ r)
  rw [T.sum_degrees_eq_twice_card_edges] at hsum
  have hedges := hT.card_edgeFinset
  change Fintype.card U ≤ 2 * L.card
  omega

omit [Fintype U] [DecidableRel T.Adj] in
open scoped Classical in
/-- Any set of at least `2*d` vertices in a bipartite graph contains `d`
pairwise nonadjacent vertices. -/
theorem exists_independent_subset_of_bipartite (hT : T.IsBipartite)
    (L : Finset U) (d : ℕ) (hsize : 2 * d ≤ L.card) :
    ∃ I ⊆ L, I.card = d ∧ ∀ u ∈ I, ∀ v ∈ I, ¬ T.Adj u v := by
  classical
  obtain ⟨c, hc⟩ := hT
  have hclass : ∃ i : Fin 2, d ≤ (L.filter fun v ↦ c v = i).card := by
    by_cases hzero : d ≤ (L.filter fun v ↦ c v = 0).card
    · exact ⟨0, hzero⟩
    have hone : (L.filter fun v ↦ c v ≠ 0) = (L.filter fun v ↦ c v = 1) := by
      ext v
      simp only [Finset.mem_filter]
      generalize c v = i
      fin_cases i <;> simp
    have hsplit := Finset.card_filter_add_card_filter_not (s := L) (fun v ↦ c v = 0)
    rw [hone] at hsplit
    exact ⟨1, by omega⟩
  obtain ⟨i, hi⟩ := hclass
  obtain ⟨I, hI, hcard⟩ := Finset.exists_subset_card_eq hi
  refine ⟨I, hI.trans (Finset.filter_subset _ _), hcard, ?_⟩
  intro u hu v hv huv
  have hcu := (Finset.mem_filter.mp (hI hu)).2
  have hcv := (Finset.mem_filter.mp (hI hv)).2
  exact hc huv (hcu.trans hcv.symm)

open scoped Classical in
theorem exists_independent_nonroot_low_degree (hT : T.IsTree)
    (r : U) (d : ℕ) (hd : 0 < d) (hsize : 4 * d ≤ Fintype.card U) :
    ∃ I : Finset U, I.card = d ∧
      (∀ v ∈ I, v ≠ r ∧ T.degree v ≤ 2) ∧
      (∀ u ∈ I, ∀ v ∈ I, ¬ T.Adj u v) := by
  classical
  let : Nontrivial U := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let L := (Finset.univ : Finset U).filter fun v ↦ v ≠ r ∧ T.degree v ≤ 2
  have hcount := card_le_twice_nonroot_low_degree T hT r
  have hL : 2 * d ≤ L.card := by change Fintype.card U ≤ 2 * L.card at hcount; omega
  obtain ⟨I, hIL, hI, hind⟩ := exists_independent_subset_of_bipartite T hT.isBipartite L d hL
  exact ⟨I, hI, fun v hv ↦ (Finset.mem_filter.mp (hIL hv)).2, hind⟩

open scoped Classical in
/-- A tree with at least `4*d` vertices has a pendant piece of fewer than
`8*d` vertices containing `d` independent nonroot vertices of global degree
at most two. Every neighbour of a selected vertex remains in the piece. -/
theorem exists_pendant_package (hT : T.IsTree) (d : ℕ)
    (hd : 0 < d) (hsize : 4 * d ≤ Fintype.card U) :
    ∃ S : Finset U, ∃ r, ∃ I : Finset U,
      4 * d ≤ S.card ∧ S.card ≤ 8 * d - 1 ∧ IsRootedPiece T (S : Set U) r ∧
      I ⊆ S ∧ I.card = d ∧
      (∀ v ∈ I, v ≠ r ∧ T.degree v ≤ 2) ∧
      (∀ u ∈ I, ∀ v ∈ I, ¬ T.Adj u v) ∧
      (∀ u ∈ I, ∀ v, T.Adj u v → v ∈ S) := by
  classical
  obtain ⟨S, r, hSlo, hShi, hpiece⟩ := exists_bounded_rooted_piece T hT (4 * d)
    (by omega) hsize
  have hST : (T.induce (S : Set U)).IsTree := ⟨hpiece.connected, hT.isAcyclic.induce _⟩
  have hScard : Fintype.card (S : Set U) = S.card := Fintype.card_coe S
  obtain ⟨J, hJcard, hJdeg, hJind⟩ := exists_independent_nonroot_low_degree
    (T.induce (S : Set U)) hST ⟨r, hpiece.root_mem⟩ d hd (by omega)
  let I := J.image (fun v : (S : Set U) ↦ v.val)
  have hIsub : I ⊆ S := by
    rintro v hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    exact u.property
  have hIcard : I.card = d := by
    change (J.image (fun v : (S : Set U) ↦ v.val)).card = d
    rw [Finset.card_image_of_injective _ Subtype.coe_injective, hJcard]
  have hIdeg : ∀ v ∈ I, v ≠ r ∧ T.degree v ≤ 2 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hne, hdegree⟩ := hJdeg u hu
    have hne' : u.val ≠ r := fun h ↦ hne (Subtype.ext h)
    have hclosed : T.neighborSet u.val ⊆ (S : Set U) :=
      fun w hw ↦ hpiece.closed_off_root u.val u.property hne' w hw
    have hfilter : S.filter (T.Adj u.val) = T.neighborFinset u.val := by
      ext w
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hclosed h, h⟩⟩
    have hlocal := degreeIn_eq_induce_degree T S u
    have hglobal : degreeIn T S u.val = T.degree u.val := by
      unfold degreeIn
      rw [hfilter, T.card_neighborFinset_eq_degree]
    exact ⟨hne', hglobal ▸ hlocal.symm ▸ hdegree⟩
  refine ⟨S, r, I, hSlo, by omega, hpiece, hIsub, hIcard, hIdeg, ?_, ?_⟩
  · intro u hu v hv huv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    exact hJind u' hu' v' hv' huv
  · intro u hu v huv
    exact hpiece.closed_off_root u (hIsub hu) (hIdeg u hu).1 v huv

end Erdos547

#print axioms Erdos547.exists_pendant_package

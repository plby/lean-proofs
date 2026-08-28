import ErdosProblems.Erdos577.JointClaimFourHeavy

/-! Two independent replacements give the exact three-cycle part of Claim2.4's final factor. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma parallel_replacement_partition {s a b : Finset V} {u v x y : V}
    (hsa : Disjoint s a) (hsab : Disjoint (s ∪ a) b)
    (hu : u ∈ a) (hv : v ∈ b) (hx : x ∉ (s ∪ a) ∪ b) (hy : y ∉ (s ∪ a) ∪ b)
    (hxy : x ≠ y) (hquad : QuadOn G (insert u (insert v s)))
    (hfirst : QuadOn G (insert x (a.erase u)))
    (hsecond : QuadOn G (insert y (b.erase v))) :
    Nonempty (BlockPartition G (insert y (insert x ((s ∪ a) ∪ b)))) := by
  have hva : v ∉ a := fun hh ↦ disjoint_left.mp hsab (mem_union_right _ hh) hv
  have hdis : Disjoint (insert v s) a := disjoint_insert_left.mpr ⟨hva, hsa⟩
  have hx' : x ∉ insert v s ∪ a := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_insert.mp hh with he | hh
      · exact hx (mem_union_right _ (he.symm ▸ hv))
      · exact hx (mem_union_left _ (mem_union_left _ hh))
    · exact hx (mem_union_left _ (mem_union_right _ hh))
  let part := (BlockPartition.single hquad).replacementUnion hdis hx' hu
    (BlockPartition.single hfirst)
  have he : insert x (insert v s ∪ a) = insert v (insert x (s ∪ a)) := by
    rw [insert_union, insert_comm x v]
  have part' : BlockPartition G (insert v (insert x (s ∪ a))) := he ▸ part
  have hdis' : Disjoint (insert x (s ∪ a)) b := disjoint_insert_left.mpr
    ⟨fun hh ↦ hx (mem_union_right _ hh), hsab⟩
  have hy' : y ∉ insert x (s ∪ a) ∪ b := by
    simp only [mem_union, mem_insert, not_or] at hy ⊢
    exact ⟨⟨hxy.symm, hy.1⟩, hy.2⟩
  let all := part'.replacementUnion hdis' hy' hv (BlockPartition.single hsecond)
  exact ⟨(insert_union x (s ∪ a) b) ▸ all⟩

lemma two_classified_partition (d v w : Quadrilateral G) (y : V)
    (hdv : Disjoint d.support v.support) (hdw : Disjoint d.support w.support)
    (hvw : Disjoint v.support w.support)
    (hyd : y ∉ d.support) (hyv : y ∉ v.support) (hyw : y ∉ w.support)
    (hfirst : ∀ i : Fin 4, i ≠ 0 → G.Adj (d 2) (v i) ∧ G.Adj (d 3) (v i))
    (hsecond : ∀ i : Fin 4, i ≠ 0 → G.Adj (d 2) (w i) ∧ G.Adj (d 1) (w i))
    (hyfirst : G.Adj y (v 2)) (hysecond : G.Adj y (w 2)) :
    Nonempty (BlockPartition G (insert y (({d 1, d 2, d 3} ∪ v.support) ∪ w.support))) := by
  have hm (i : Fin 4) : d i ∈ d.support := (d.mem_support _).mpr ⟨i, rfl⟩
  have hdvo (i : Fin 4) : d i ∉ v.support := fun hh ↦ disjoint_left.mp hdv (hm i) hh
  have hdwo (i : Fin 4) : d i ∉ w.support := fun hh ↦ disjoint_left.mp hdw (hm i) hh
  have hdy (i : Fin 4) : d i ≠ y := fun he ↦ hyd (he ▸ hm i)
  have hquad : QuadOn G {d 2, v 2, y, w 2} := QuadOn.of_vertices (hdy 2)
    (fun he ↦ disjoint_left.mp hvw ((v.mem_support _).mpr ⟨2, rfl⟩)
      (he.symm ▸ (w.mem_support _).mpr ⟨2, rfl⟩))
    (hfirst 2 (by decide)).1 hyfirst.symm hysecond (hsecond 2 (by decide)).1.symm
  have hequad : ({d 2, v 2, y, w 2} : Finset V) = insert (v 2) (insert (w 2) {y, d 2}) := by
    rw [insert_comm (d 2) (v 2), insert_comm (d 2) y, pair_comm (d 2) (w 2),
      insert_comm y (w 2)]
  have hbase : Disjoint {y, d 2} v.support := disjoint_insert_left.mpr
    ⟨hyv, disjoint_singleton_left.mpr (hdvo 2)⟩
  have hsecondDis : Disjoint (({y, d 2} : Finset V) ∪ v.support) w.support :=
    disjoint_union_left.mpr ⟨disjoint_insert_left.mpr
      ⟨hyw, disjoint_singleton_left.mpr (hdwo 2)⟩, hvw⟩
  have hout (i : Fin 4) (hi : i ≠ 2) : d i ∉ (({y, d 2} : Finset V) ∪ v.support) ∪ w.support := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨⟨hdy i, d.injective.ne hi⟩, hdvo i⟩, hdwo i⟩
  have hrep1 := low_pair_replace v (d 3) (hdvo 3)
    (hfirst 1 (by decide)).2 (hfirst 3 (by decide)).2 2 (Or.inr rfl)
  have hrep2 := low_pair_replace w (d 1) (hdwo 1)
    (hsecond 1 (by decide)).2 (hsecond 3 (by decide)).2 2 (Or.inr rfl)
  obtain ⟨parts⟩ := parallel_replacement_partition hbase hsecondDis
    ((v.mem_support _).mpr ⟨2, rfl⟩) ((w.mem_support _).mpr ⟨2, rfl⟩)
    (hout 3 (by decide)) (hout 1 (by decide))
    (d.injective.ne (by decide : (3 : Fin 4) ≠ 1)) (hequad ▸ hquad) hrep1 hrep2
  have he : insert (d 1) (insert (d 3) ((({y, d 2} : Finset V) ∪ v.support) ∪ w.support)) =
      insert y (({d 1, d 2, d 3} ∪ v.support) ∪ w.support) := by
    simp only [insert_union, singleton_union]
    rw [insert_comm (d 3) y, insert_comm (d 1) y, insert_comm (d 3) (d 2)]
  exact ⟨he ▸ parts⟩

end Erdos577.JointFinal

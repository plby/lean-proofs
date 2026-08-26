import ErdosProblems.Erdos547.SeparatingPartitions

/-!
# Extremal separating partitions

Maximize odd-block deficiency, breaking ties by separator size. Any local
refinement deleting a nonempty set must strictly decrease its deficiency.
In particular every remaining block has odd order.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}

structure IsBarrier (G : SimpleGraph V) (A S : Finset V) (F : Finset (Finset V)) : Prop where
  separates : SeparatesOn G A S F
  maximal : ∀ U H, SeparatesOn G A U H →
    (oddParts H).card + S.card ≤ (oddParts F).card + U.card
  tiebreak : ∀ U H, SeparatesOn G A U H →
    (oddParts H).card + S.card = (oddParts F).card + U.card → U.card ≤ S.card

theorem exists_barrier (G : SimpleGraph V) (A : Finset V) : ∃ S F, IsBarrier G A S F := by
  classical
  let := Fintype.ofFinite V
  let candidates := (Finset.univ : Finset (Finset V × Finset (Finset V))).filter
    fun p ↦ SeparatesOn G A p.1 p.2
  let score := fun p : Finset V × Finset (Finset V) ↦
    ((oddParts p.2).card : ℤ) - p.1.card
  have hne : candidates.Nonempty := by
    refine ⟨(A, ∅), Finset.mem_filter.mpr ⟨Finset.mem_univ _, separatesOn_empty A⟩⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image candidates score hne
  let best := candidates.filter fun q ↦ score q = score p
  have hbest : best.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
  obtain ⟨q, hq, hsize⟩ := Finset.exists_max_image best (fun q ↦ q.1.card) hbest
  have hqc := (Finset.mem_filter.mp hq).1
  have hqp := (Finset.mem_filter.mp hq).2
  refine ⟨q.1, q.2, (Finset.mem_filter.mp hqc).2, ?_, ?_⟩
  · intro U H hUH
    have hu : (U, H) ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUH⟩
    have hle := hmax (U, H) hu
    have hqq : score (U, H) ≤ score q := hqp ▸ hle
    dsimp [score] at hqq
    omega
  · intro U H hUH heq
    have hu : (U, H) ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUH⟩
    apply hsize (U, H)
    refine Finset.mem_filter.mpr ⟨hu, ?_⟩
    calc
      score (U, H) = score q := by dsimp [score]; omega
      _ = score p := hqp

namespace IsBarrier

variable {A S C U : Finset V} {F H : Finset (Finset V)}

omit [Finite V] in
theorem local_deficiency_lt (h : IsBarrier G A S F) (hC : C ∈ F)
    (h' : SeparatesOn G C U H) (hU : U.Nonempty) :
    (oddParts H).card < U.card + (if Odd C.card then 1 else 0) := by
  classical
  have href := h.separates.refine_part hC h'
  have hsep := h.separates.refined_separator_card hC h'
  have hodd := h.separates.refined_odd_card hC h'
  have hmax := h.maximal _ _ href
  have hpos := hU.card_pos
  by_contra hnot
  have heq : (oddParts (F.erase C ∪ H)).card + S.card =
      (oddParts F).card + (S ∪ U).card := by omega
  have hsize := h.tiebreak _ _ href heq
  omega

theorem odd_part (h : IsBarrier G A S F) (hC : C ∈ F) : Odd C.card := by
  classical
  by_contra hnot
  obtain ⟨u, hu⟩ := h.separates.nonempty C hC
  obtain ⟨H, hH⟩ := exists_separating_partition G C {u} (Finset.singleton_subset_iff.mpr hu)
  have hlt := h.local_deficiency_lt hC hH (Finset.singleton_nonempty u)
  simp only [Finset.card_singleton, if_neg hnot, add_zero] at hlt
  have heven : Even C.card := Nat.not_odd_iff_even.mp hnot
  have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hodd : Odd (C.card - ({u} : Finset V).card) := by
    rw [Finset.card_singleton, Nat.odd_iff, Nat.even_iff] at *
    omega
  have hp := hH.odd_parts_iff.mpr hodd
  have hzero : (oddParts H).card = 0 := by omega
  rw [hzero] at hp
  exact Nat.not_odd_zero hp

theorem local_odd_bound (h : IsBarrier G A S F) (hC : C ∈ F)
    (h' : SeparatesOn G C U H) (hU : U.Nonempty) : (oddParts H).card ≤ U.card := by
  have hlt := h.local_deficiency_lt hC h' hU
  rw [if_pos (h.odd_part hC)] at hlt
  omega

end IsBarrier

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_barrier
#print axioms Erdos547.DPRS.IsBarrier.odd_part

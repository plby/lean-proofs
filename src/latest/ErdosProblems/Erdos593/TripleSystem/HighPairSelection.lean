import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fin.Tuple.Embedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos593

universe u v

namespace TripleSystem

/-- Select one point from each finite reservoir, avoiding a fixed finite core,
while keeping all selected points globally distinct.

The capacity hypothesis is deliberately uniform: each reservoir has `T`
distinct points, and deleting the core still leaves enough choices for all
`m` cells. This is the finite selection step used when high-codegree pairs
are assembled into a witnessed bipartite matrix. -/
theorem exists_injective_choice_of_card_add_le
    {W : Type u} [DecidableEq W] {m T : Nat}
    (C : Finset W) (reservoir : Fin m → Fin T ↪ W)
    (hcap : C.card + m ≤ T) :
    ∃ choose : Fin m → Fin T,
      Function.Injective (fun i => reservoir i (choose i)) ∧
      ∀ i, reservoir i (choose i) ∉ C := by
  classical
  let A : Fin m → Finset W := fun i => Finset.univ.map (reservoir i) \ C
  have hlarge : ∀ i : Fin m, m ≤ (A i).card := by
    intro i
    have hsub : T - C.card ≤ (A i).card := by
      simpa [A, Finset.card_map] using!
        (Finset.le_card_sdiff C (Finset.univ.map (reservoir i)))
    exact (Nat.le_sub_of_add_le' hcap).trans hsub
  have hhall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion A).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · obtain ⟨i, hi⟩ := hs
      calc
        s.card ≤ m := by simpa using! (Finset.card_le_univ s)
        _ ≤ (A i).card := hlarge i
        _ ≤ (s.biUnion A).card := Finset.card_le_card (by
          intro x hx
          exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩)
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective A).mp hhall
  choose choose hchoose using fun i =>
    (Finset.mem_map.mp (Finset.mem_sdiff.mp (hf_mem i)).1)
  refine ⟨choose, ?_, ?_⟩
  · intro i j hij
    apply hf_inj
    calc
      f i = reservoir i (choose i) := (hchoose i).2.symm
      _ = reservoir j (choose j) := hij
      _ = f j := (hchoose j).2
  · intro i
    rw [(hchoose i).2]
    exact (Finset.mem_sdiff.mp (hf_mem i)).2

/-- The same finite Hall-selection principle indexed by an arbitrary finite
type. This form is convenient for the cells of a bipartite matrix, whose
natural index type is `Fin n × Fin n`. -/
theorem exists_injective_choice_of_fintype_card_add_le
    {ι : Type v} {W : Type u} [Fintype ι] [DecidableEq W] {T : Nat}
    (C : Finset W) (reservoir : ι → Fin T ↪ W)
    (hcap : C.card + Fintype.card ι ≤ T) :
    ∃ choose : ι → Fin T,
      Function.Injective (fun i => reservoir i (choose i)) ∧
      ∀ i, reservoir i (choose i) ∉ C := by
  classical
  let A : ι → Finset W := fun i => Finset.univ.map (reservoir i) \ C
  have hlarge : ∀ i : ι, Fintype.card ι ≤ (A i).card := by
    intro i
    have hsub : T - C.card ≤ (A i).card := by
      simpa [A, Finset.card_map] using!
        (Finset.le_card_sdiff C (Finset.univ.map (reservoir i)))
    exact (Nat.le_sub_of_add_le' hcap).trans hsub
  have hhall : ∀ s : Finset ι, s.card ≤ (s.biUnion A).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · obtain ⟨i, hi⟩ := hs
      calc
        s.card ≤ Fintype.card ι := Finset.card_le_univ s
        _ ≤ (A i).card := hlarge i
        _ ≤ (s.biUnion A).card := Finset.card_le_card (by
          intro x hx
          exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩)
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective A).mp hhall
  choose choose hchoose using fun i =>
    (Finset.mem_map.mp (Finset.mem_sdiff.mp (hf_mem i)).1)
  refine ⟨choose, ?_, ?_⟩
  · intro i j hij
    apply hf_inj
    calc
      f i = reservoir i (choose i) := (hchoose i).2.symm
      _ = reservoir j (choose j) := hij
      _ = f j := (hchoose j).2
  · intro i
    rw [(hchoose i).2]
    exact (Finset.mem_sdiff.mp (hf_mem i)).2

end TripleSystem

end Erdos593

import ErdosProblems.Erdos577.ReplacementFactors

/-! A common-neighbor insertion on three arms of a star gives a two-cycle factor. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem star_factor_of_common {r x y z : V} {j : Finset V}
    (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (hd : Disjoint ({x, r, y} : Finset V) j) (hz : z ∉ ({x, r, y} : Finset V) ∪ j)
    (hc : CommonReplacement G x y z j) :
    LocalFactor G (insert r ({x, y, z} ∪ j)) := by
  obtain ⟨u, hu, hxu, hyu, hrep⟩ := hc
  have hru : r ≠ u := fun he ↦ disjoint_left.mp hd (by simp) (he.symm ▸ hu)
  have hquad := QuadOn.of_vertices hxy hru hrx.symm hry hyu hxu.symm
  have heq : ({x, r, y, u} : Finset V) = insert u {x, r, y} := by
    symm
    rw [insert_comm u x, insert_comm u r, pair_comm u y]
  have hquad' : QuadOn G (insert u {x, r, y}) := heq ▸ hquad
  have hf := LocalFactor.of_replacement hd hz hu hquad' hrep
  have he : insert z (({x, r, y} : Finset V) ∪ j) = insert r ({x, y, z} ∪ j) := by
    simp only [insert_union, singleton_union]
    rw [insert_comm z x, insert_comm z r, insert_comm z y, insert_comm x r]
  exact he ▸ hf

theorem triple_no_factor_of_erase {r : V} {arms j : Finset V}
    (hfour : arms.card = 4)
    (hno : ∀ w ∈ arms, ¬LocalFactor G (insert r (arms.erase w) ∪ j))
    {s : Finset V} (hs : s ⊆ arms) (hthree : s.card = 3) :
    ¬LocalFactor G (insert r s ∪ j) := by
  have hstrict : s ⊂ arms := Finset.ssubset_iff_subset_ne.mpr ⟨hs, by
    intro he
    have hh := congrArg Finset.card he
    omega⟩
  obtain ⟨w, hw, hsub⟩ := ssubset_iff_exists_subset_erase.mp hstrict
  have he : s = arms.erase w := eq_of_subset_of_card_le hsub (by
    rw [card_erase_of_mem hw, hfour, hthree])
  rw [he]
  exact hno w hw

theorem no_common_of_star_triples {r : V} {arms j : Finset V}
    (hd : Disjoint arms j) (hrj : r ∉ j)
    (hcenter : ∀ w ∈ arms, G.Adj r w)
    (hno : ∀ s ⊆ arms, s.card = 3 → ¬LocalFactor G (insert r s ∪ j))
    {x y z : V} (hx : x ∈ arms) (hy : y ∈ arms) (hz : z ∈ arms)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : ¬CommonReplacement G x y z j := by
  intro hc
  have hxrj : Disjoint ({x, r, y} : Finset V) j :=
    disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hd hx hh,
      disjoint_insert_left.mpr ⟨hrj,
        disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hd hy hh)⟩⟩
  have hzout : z ∉ ({x, r, y} : Finset V) ∪ j := by
    simp only [mem_union, mem_insert, mem_singleton, not_or]
    exact ⟨⟨hxz.symm, (hcenter z hz).ne.symm, hyz.symm⟩,
      fun hh ↦ disjoint_left.mp hd hz hh⟩
  have hf := star_factor_of_common hxy (hcenter x hx) (hcenter y hy) hxrj hzout hc
  rw [← insert_union] at hf
  exact hno {x, y, z} (insert_subset hx (insert_subset hy (singleton_subset_iff.mpr hz)))
    (card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩) hf

end Erdos577

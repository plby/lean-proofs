import ErdosProblems.Erdos73.RobustConnectedSupport

/-! Glue a connected family of robust supports along two-vertex overlaps. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {I V : Type*} [DecidableEq I] [DecidableEq V]
variable {J : SimpleGraph I} {G : SimpleGraph V}

theorem deletionOneConnected_walkUnion (R : I → Finset V)
    (hR : ∀ i, DeletionOneConnected G (R i))
    (hJ : ∀ i j, J.Adj i j → 2 ≤ (R i ∩ R j).card)
    {i j : I} (p : J.Walk i j) :
    DeletionOneConnected G (p.support.toFinset.biUnion R) := by
  induction p with
  | @nil i => simpa using hR i
  | @cons i j k hij p ih =>
    have hsub : R j ⊆ p.support.toFinset.biUnion R := by
      intro x hx
      exact mem_biUnion.mpr ⟨j, List.mem_toFinset.mpr p.start_mem_support, hx⟩
    have hcard : 2 ≤ (R i ∩ p.support.toFinset.biUnion R).card :=
      (hJ i j hij).trans (card_le_card (Finset.inter_subset_inter subset_rfl hsub))
    have hh := (hR i).union ih hcard
    simpa only [Walk.support_cons, List.toFinset_cons, biUnion_insert] using hh

theorem deletionOneConnected_biUnion [Fintype I] (R : I → Finset V)
    (hR : ∀ i, DeletionOneConnected G (R i)) (hconn : J.Connected)
    (hJ : ∀ i j, J.Adj i j → 2 ≤ (R i ∩ R j).card) :
    DeletionOneConnected G (Finset.univ.biUnion R) := by
  intro X hX
  let U := (Finset.univ.biUnion R) \ X
  have hsub {i j : I} (p : J.Walk i j) :
      (p.support.toFinset.biUnion R) \ X ⊆ U := by
    intro x hx
    obtain ⟨hx, hxX⟩ := mem_sdiff.mp hx
    obtain ⟨a, _, hxa⟩ := mem_biUnion.mp hx
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨a, mem_univ _, hxa⟩, hxX⟩
  have hpre : (G.induce (U : Set V)).Preconnected := by
    intro x y
    obtain ⟨hx, hxX⟩ := mem_sdiff.mp x.property
    obtain ⟨hy, hyX⟩ := mem_sdiff.mp y.property
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
    obtain ⟨j, _, hyj⟩ := mem_biUnion.mp hy
    obtain ⟨p⟩ := hconn i j
    have hxT : x.val ∈ (p.support.toFinset.biUnion R) \ X := mem_sdiff.mpr
      ⟨mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr p.start_mem_support, hxi⟩, hxX⟩
    have hyT : y.val ∈ (p.support.toFinset.biUnion R) \ X := mem_sdiff.mpr
      ⟨mem_biUnion.mpr ⟨j, List.mem_toFinset.mpr p.end_mem_support, hyj⟩, hyX⟩
    have hT := deletionOneConnected_walkUnion R hR hJ p X hX
    exact (hT ⟨x.val, hxT⟩ ⟨y.val, hyT⟩).map
      (G.induceHomOfLE (show (((p.support.toFinset.biUnion R) \ X : Finset V) : Set V) ⊆
        (U : Set V) from hsub p)).toHom
  obtain ⟨i⟩ := hconn.nonempty
  obtain ⟨x⟩ := (hR i X hX).nonempty
  have hxU : x.val ∈ U := by
    obtain ⟨hx, hxX⟩ := mem_sdiff.mp x.property
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨i, mem_univ _, hx⟩, hxX⟩
  letI : Nonempty (U : Set V) := ⟨⟨x.val, hxU⟩⟩
  exact ⟨hpre⟩

end
end Erdos73

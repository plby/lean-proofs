import ErdosProblems.Erdos547.TreeConvexity
import ErdosProblems.Erdos547.DegreeExtraction

/-!
# Minimal connected hulls and their branch vertices
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {U : Type*} (T : SimpleGraph U)

theorem connected_induce_erase_of_degreeIn_eq_one [DecidableEq U] [DecidableRel T.Adj]
    (H : Finset U) (hH : (T.induce (H : Set U)).Connected) (v : U) (hv : v ∈ H)
    (hdeg : degreeIn T H v = 1) : (T.induce (↑(H.erase v) : Set U)).Connected := by
  classical
  let z : (H : Set U) := ⟨v, hv⟩
  have hz : (T.induce (H : Set U)).degree z = 1 := by
    rw [← degreeIn_eq_induce_degree]
    exact hdeg
  have hc := hH.induce_compl_singleton_of_degree_eq_one hz
  let f : ((T.induce (H : Set U)).induce ({z}ᶜ : Set ↥(H : Set U))) →g
      (T.induce (↑(H.erase v) : Set U)) := {
    toFun := fun u ↦ ⟨u.val.val, Finset.mem_erase.mpr
      ⟨fun he ↦ u.property (Subtype.ext he), u.val.property⟩⟩
    map_rel' := fun h ↦ h }
  have hsurj : Function.Surjective f := by
    rintro ⟨u, hu⟩
    obtain ⟨huv, huH⟩ := Finset.mem_erase.mp hu
    refine ⟨⟨⟨u, huH⟩, ?_⟩, rfl⟩
    intro he
    exact huv (congrArg Subtype.val he)
  exact hc.map f hsurj

open scoped Classical in
theorem exists_minimal_connected_hull [Fintype U] (hT : T.Connected) (W : Finset U) :
    ∃ H : Finset U, W ⊆ H ∧ (T.induce (H : Set U)).Connected ∧
      ∀ K : Finset U, W ⊆ K → (T.induce (K : Set U)).Connected → H.card ≤ K.card := by
  classical
  let candidates := (Finset.univ : Finset (Finset U)).filter
    fun H ↦ W ⊆ H ∧ (T.induce (H : Set U)).Connected
  have hfull : (T.induce (↑(Finset.univ : Finset U) : Set U)).Connected := by
    rw [Finset.coe_univ]
    exact hT.map T.induceUnivIso.symm.toHom T.induceUnivIso.symm.toEquiv.surjective
  have hc : Finset.univ ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_univ _, hfull⟩
  obtain ⟨H, hH, hmin⟩ := Finset.exists_min_image candidates Finset.card ⟨_, hc⟩
  refine ⟨H, (Finset.mem_filter.mp hH).2.1, (Finset.mem_filter.mp hH).2.2, ?_⟩
  intro K hWK hK
  exact hmin K (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hWK, hK⟩)

theorem minimal_connected_hull_degree [Fintype U] [DecidableRel T.Adj]
    {W H : Finset U} (hW : W.Nonempty) (hWH : W ⊆ H)
    (hH : (T.induce (H : Set U)).Connected)
    (hmin : ∀ K : Finset U, W ⊆ K → (T.induce (K : Set U)).Connected → H.card ≤ K.card)
    {v : U} (hv : v ∈ H) (hvW : v ∉ W) : 2 ≤ degreeIn T H v := by
  classical
  obtain ⟨w, hw⟩ := hW
  let z : (H : Set U) := ⟨v, hv⟩
  let y : (H : Set U) := ⟨w, hWH hw⟩
  have hzy : z ≠ y := by
    intro he
    have hh : v = w := congrArg Subtype.val he
    exact hvW (hh.symm ▸ hw)
  let : Nontrivial ↥(H : Set U) := nontrivial_of_ne z y hzy
  have hpos : 0 < degreeIn T H v := by
    rw [degreeIn_eq_induce_degree T H z]
    exact hH.preconnected.degree_pos_of_nontrivial z
  by_contra h
  have hdeg : degreeIn T H v = 1 := by omega
  have hconn := connected_induce_erase_of_degreeIn_eq_one T H hH v hv hdeg
  have hsub : W ⊆ H.erase v := by
    intro u hu
    exact Finset.mem_erase.mpr ⟨fun he ↦ hvW (he ▸ hu), hWH hu⟩
  have hbad := hmin (H.erase v) hsub hconn
  have hcard := Finset.card_erase_add_one hv
  omega

open scoped Classical in
theorem tree_branch_count [Fintype U] [Nontrivial U] [DecidableRel T.Adj]
    (hT : T.IsTree) (W : Finset U) (hW : ∀ v, v ∉ W → 2 ≤ T.degree v) :
    ((Finset.univ : Finset U).filter (fun v ↦ 3 ≤ T.degree v)).card + 2 ≤ W.card := by
  classical
  have hpoint (v : U) : 2 + (if 3 ≤ T.degree v then 1 else 0) ≤
      T.degree v + (if v ∈ W then 1 else 0) := by
    have hp := hT.connected.preconnected.degree_pos_of_nontrivial v
    by_cases hv : v ∈ W
    · simp only [if_pos hv]
      split_ifs <;> omega
    · have hh := hW v hv
      simp only [if_neg hv]
      split_ifs <;> omega
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset U)) (fun v _ ↦ hpoint v)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Nat.cast_id] at hs
  rw [T.sum_degrees_eq_twice_card_edges] at hs
  have he := hT.card_edgeFinset
  omega

end Erdos547

#print axioms Erdos547.minimal_connected_hull_degree
#print axioms Erdos547.tree_branch_count

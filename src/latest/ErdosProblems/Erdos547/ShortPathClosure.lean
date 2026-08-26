import ErdosProblems.Erdos547.ShortBridgeClosure
import ErdosProblems.Erdos547.PathSupportDegree

/-!
# Bounded cut sets with no short path between consecutive cut vertices
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem exists_short_path_closed_extension {U : Type*} [Fintype U] (T : SimpleGraph U)
    [DecidableRel T.Adj] (hT : T.IsAcyclic) (col : T.Coloring (Fin 2))
    (S H : Finset U) (hSH : S ⊆ H)
    (hdeg : ∀ u ∈ H, u ∉ S → degreeIn T H u = 2)
    (hclosed : ∀ u ∈ S, col u = 1 → ∀ v ∈ H, T.Adj u v → v ∈ S) :
    ∃ Z : Finset U, S ⊆ Z ∧ Z ⊆ H ∧ Z.card ≤ 5 * S.card ∧
      (∀ u ∈ H, u ∉ Z → degreeIn T H u = 2) ∧
      (∀ u ∈ Z, col u = 1 → ∀ v ∈ H, T.Adj u v → v ∈ Z) ∧
      ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → ∀ p : T.Walk a b, p.IsPath → 2 ≤ p.length →
        (∀ u ∈ p.support, u ∈ H) → (∀ u ∈ p.support, u ∈ Z → u = a ∨ u = b) →
        6 ≤ p.length := by
  classical
  obtain ⟨Z, hSZ, hZH, hcount, hZclosed, hnobridge⟩ :=
    exists_short_bridge_closed_extension T hT col S H hSH hclosed
  have hZdeg : ∀ u ∈ H, u ∉ Z → degreeIn T H u = 2 :=
    fun u hu hn ↦ hdeg u hu (fun hs ↦ hn (hSZ hs))
  refine ⟨Z, hSZ, hZH, hcount, hZdeg, hZclosed, ?_⟩
  intro a ha b hb hab p hp hl hsupport hcuts
  by_contra hlong
  let P := p.support.toFinset
  have hPH : P ⊆ H := fun u hu ↦ hsupport u (List.mem_toFinset.mp hu)
  have hPconn : (T.induce (P : Set U)).Connected := by
    have he : (P : Set U) = {u | u ∈ p.support} := by
      ext u
      exact List.mem_toFinset
    rw [he]
    exact p.connected_induce_support
  have hPcard : P.card = p.length + 1 := by
    change p.support.toFinset.card = p.length + 1
    rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  have hinter : Z ∩ P = {a, b} := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hu
      exact hcuts u (List.mem_toFinset.mp hu.2) hu.1
    · rintro (rfl | rfl)
      · exact ⟨ha, List.mem_toFinset.mpr p.start_mem_support⟩
      · exact ⟨hb, List.mem_toFinset.mpr p.end_mem_support⟩
  have htwo : (Z ∩ P).card = 2 := by rw [hinter, Finset.card_pair hab]
  have hnotadj := forest_path_endpoints_not_adjacent T hT p hp hl
  have hzero : degreeMass T (Z ∩ P) = 0 := by
    rw [hinter]
    have hnotadj' : ¬ T.Adj b a := fun hh ↦ hnotadj hh.symm
    simp [degreeMass, degreeIn, hnotadj, hnotadj']
  apply hnobridge P hPH hPconn (by omega) (by omega) htwo hzero
  intro u hu hc v hv huv
  by_cases huZ : u ∈ Z
  · exact Finset.mem_union_left _ (hZclosed u huZ hc v hv huv)
  · have hua : u ≠ a := fun he ↦ huZ (he.symm ▸ ha)
    have hub : u ≠ b := fun he ↦ huZ (he.symm ▸ hb)
    have hlo := path_internal_degree_lower T p hp (List.mem_toFinset.mp hu) hua hub
    have hhi := (hZdeg u (hPH hu) huZ).le
    exact Finset.mem_union_right _ (neighbour_closed_of_two_degrees T hPH hlo hhi v hv huv)

end Erdos547

#print axioms Erdos547.exists_short_path_closed_extension

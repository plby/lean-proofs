import ErdosProblems.Erdos547.ShortBridgePotential

/-!
# Bounded closure under short tree bridges

Only genuine small connected induced trees are absorbed.  The potential
bounds the resulting set by five times the original order.
-/

namespace Erdos547

open Finset SimpleGraph

variable {U : Type*} [Fintype U] (T : SimpleGraph U) [DecidableRel T.Adj]

open scoped Classical in
theorem exists_short_bridge_closed_extension (hT : T.IsAcyclic) (col : T.Coloring (Fin 2))
    (S H : Finset U) (hSH : S ⊆ H)
    (hclosed : ∀ u ∈ S, col u = 1 → ∀ v ∈ H, T.Adj u v → v ∈ S) :
    ∃ Z : Finset U, S ⊆ Z ∧ Z ⊆ H ∧ Z.card ≤ 5 * S.card ∧
      (∀ u ∈ Z, col u = 1 → ∀ v ∈ H, T.Adj u v → v ∈ Z) ∧
      ∀ P : Finset U, P ⊆ H → (T.induce (P : Set U)).Connected →
        3 ≤ P.card → P.card ≤ 6 → (Z ∩ P).card = 2 → degreeMass T (Z ∩ P) = 0 →
        (∀ u ∈ P, col u = 1 → ∀ v ∈ H, T.Adj u v → v ∈ Z ∪ P) → False := by
  classical
  let candidates := (Finset.univ : Finset (Finset U)).filter (fun Z ↦
    S ⊆ Z ∧ Z ⊆ H ∧ shortBridgePotential T Z ≤ 5 * S.card ∧
      ∀ u ∈ Z, col u = 1 → ∀ v ∈ H, T.Adj u v → v ∈ Z)
  have hstart : S ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    Finset.Subset.refl _, hSH, shortBridgePotential_upper T S, hclosed⟩
  obtain ⟨Z, hZ, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨S, hstart⟩
  obtain ⟨hSZ, hZH, hpot, hZclosed⟩ := (Finset.mem_filter.mp hZ).2
  have hZcard : Z.card ≤ 5 * S.card := by
    have hlo := shortBridgePotential_lower T hT Z
    exact_mod_cast hlo.trans hpot
  refine ⟨Z, hSZ, hZH, hZcard, hZclosed, ?_⟩
  intro P hPH hP hPlo hPhi hinter hzero hPclosed
  have hpot' : shortBridgePotential T (Z ∪ P) ≤ 5 * S.card :=
    (shortBridgePotential_union_le T hT Z P hP hPhi hinter hzero).trans hpot
  have hnew : Z ∪ P ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hSZ.trans Finset.subset_union_left,
      Finset.union_subset hZH hPH, hpot', ?_⟩
    intro u hu hc v hv huv
    rcases Finset.mem_union.mp hu with huZ | huP
    · exact Finset.mem_union_left _ (hZclosed u huZ hc v hv huv)
    · exact hPclosed u huP hc v hv huv
  have hm := hmax (Z ∪ P) hnew
  have hc := Finset.card_union_add_card_inter Z P
  rw [hinter] at hc
  omega

end Erdos547

#print axioms Erdos547.exists_short_bridge_closed_extension

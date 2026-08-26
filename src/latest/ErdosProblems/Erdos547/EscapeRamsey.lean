import ErdosProblems.Erdos547.NearBipartite
import ErdosProblems.Erdos547.InducedTransport
import ErdosProblems.Erdos547.Escape

/-!
# Escape in an induced near-core, unless the Ramsey conclusion already holds

The dense configurations supplied by escape failure are transported back to
the complete two-coloured host before applying the near-clique arguments.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

open scoped Classical in
theorem ramsey_or_induced_escape {m : ℕ} (T : SimpleGraph (Fin (m + 1)))
    (hT : T.IsTree) (R : SimpleGraph (Fin (2 * m)))
    (S : Set (Fin (2 * m))) [Fintype S] [DecidableEq S] (d k t : ℕ) (hk : 0 < k)
    (hm : 20000 * (3 * (d + k + t) + k) ≤ m)
    (hbudget : m * (d + k) ≤ t ^ 2)
    (hmin : ∀ z : S, m ≤ (R.induce S).degree z + d) :
    (T ⊑ R ∨ T ⊑ Rᶜ) ∨
      ∀ x : S, (R.induce S).degree x ≤ m → ∀ u : S,
        k ≤ (((R.induce S).neighborFinset u).filter fun z ↦
          k ≤ ((R.induce S).neighborFinset z \ (R.induce S).neighborFinset x).card).card := by
  classical
  by_cases hmono : T ⊑ R ∨ T ⊑ Rᶜ
  · exact Or.inl hmono
  right
  intro x hx u
  by_contra h
  have hfail : (((R.induce S).neighborFinset u).filter fun z ↦
      k ≤ ((R.induce S).neighborFinset z \ (R.induce S).neighborFinset x).card).card < k :=
    lt_of_not_ge h
  have hroom : d + k + t < m := by omega
  rcases escape_failure_dense_configuration (R.induce S) m d k t hroom hbudget
      hmin x u hx hfail with hclique | hbip
  · obtain ⟨C, hC, hCsize, hCdeg⟩ := hclique
    let C' := C.image (fun v : S ↦ v.val)
    have hC' : C'.Nonempty := hC.image _
    have hC'size : C'.card ≤ m := by
      change (C.image (fun v : S ↦ v.val)).card ≤ m
      rwa [Finset.card_image_of_injective _ Subtype.coe_injective]
    have hC'deg : ∀ z ∈ C', m ≤ degreeIn R C' z + (3 * (d + k + t) + k) := by
      intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      have heq := degreeIn_image_subtype R S C v
      have hdeg := hCdeg v hv
      change m ≤ degreeIn R (C.image (fun v : S ↦ v.val)) v.val + _
      rw [heq]
      omega
    exact hmono (ramsey_of_near_clique T hT R (3 * (d + k + t) + k)
      (by omega) hm C' hC' hC'size hC'deg)
  · obtain ⟨A, B, hA, _, _, _, hdis, hAB, hBA⟩ := hbip
    let A' := A.image (fun v : S ↦ v.val)
    let B' := B.image (fun v : S ↦ v.val)
    have hA' : A'.Nonempty := hA.image _
    have hdis' : Disjoint A' B' := (Finset.disjoint_image Subtype.coe_injective).mpr hdis
    have hAB' : ∀ a ∈ A', m ≤ degreeIn R B' a + (d + k + t) := by
      intro a ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
      change m ≤ degreeIn R (B.image (fun v : S ↦ v.val)) v.val + _
      rw [degreeIn_image_subtype R S B v]
      exact hAB v hv
    have hBA' : ∀ b ∈ B', m ≤ degreeIn R A' b + (d + k + t) := by
      intro b hb
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      change m ≤ degreeIn R (A.image (fun v : S ↦ v.val)) v.val + _
      rw [degreeIn_image_subtype R S A v]
      exact hBA v hv
    exact hmono (ramsey_of_dense_bipartite_pair (by omega) T hT R (d + k + t)
      (by omega) A' B' hA' hdis' hAB' hBA')

end Erdos547

#print axioms Erdos547.ramsey_or_induced_escape

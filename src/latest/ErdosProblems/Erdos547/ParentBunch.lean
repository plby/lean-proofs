import ErdosProblems.Erdos547.WeightedHall
import ErdosProblems.Erdos547.LeafBunch

/-!
# Deleting the leaves with one prescribed parent
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem exists_parent_bunch_complement {U : Type*} [Fintype U] (T : SimpleGraph U)
    (S : Set U) (parent : (Sᶜ : Set U) → S)
    (hp : ∀ x : (Sᶜ : Set U), ∀ y, T.Adj x.val y → y = (parent x).val) (p : S) :
    ∃ Q : Set U, ∃ r : Q, r.val = p.val ∧
      (∀ x : (Qᶜ : Set U), ∀ y, T.Adj x.val y → y = r.val) ∧
      Fintype.card (Qᶜ : Set U) = parentWeight parent p := by
  classical
  let L := (Finset.univ : Finset (Sᶜ : Set U)).filter fun x ↦ parent x = p
  let B := L.image (fun x : (Sᶜ : Set U) ↦ x.val)
  have hpB : p.val ∉ B := by
    intro h
    obtain ⟨x, _, hxp⟩ := Finset.mem_image.mp h
    exact x.property (hxp.symm ▸ p.property)
  let Q : Set U := (B : Set U)ᶜ
  let : DecidablePred (· ∈ Q) := fun u ↦ Classical.propDecidable (u ∈ Q)
  let r : Q := ⟨p.val, hpB⟩
  refine ⟨Q, r, rfl, ?_, ?_⟩
  · intro x y hxy
    have hxB : x.val ∈ B := by
      simpa only [Q, Set.mem_compl_iff, not_not, Finset.mem_coe] using x.property
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hxB
    have hzp : parent z = p := (Finset.mem_filter.mp hz).2
    have hzy : T.Adj z.val y := hzx.symm ▸ hxy
    have hy := hp z y hzy
    simpa only [hzp] using hy
  · trans B.card
    · exact @Fintype.card_of_subtype U (fun u ↦ u ∈ (Qᶜ : Set U)) B
        (fun u ↦ by simp [Q]) _
    · change (L.image (fun x : (Sᶜ : Set U) ↦ x.val)).card = parentWeight parent p
      rw [Finset.card_image_of_injective _ Subtype.coe_injective]
      unfold parentWeight
      congr 1
      ext x
      simp [L]

end Erdos547

#print axioms Erdos547.exists_parent_bunch_complement

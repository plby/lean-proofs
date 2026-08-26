/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Counting occupied prime-power residue classes on the sextic surface.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.RootCongruence

namespace Erdos477.Counting

noncomputable def sexticResidueImage (p r : ℕ) (S : Finset (Fin 3 → ℤ)) :
    Finset (Fin 3 → ZMod (p ^ r)) := by
  classical
  exact S.image (fun z k => (z k : ZMod (p ^ r)))

/-- A bound with a constant depending on the fixed prime is enough for the
nested residue-class construction. No Hensel existence theorem is needed. -/
theorem card_sexticResidueImage_le (p : ℕ) [Fact p.Prime] (h6 : p.Coprime 6)
    (r : ℕ) (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ z ∈ S, z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c) :
    (sexticResidueImage p r S).card ≤ 3 * p ^ 3 * (p ^ r) ^ 2 := by
  classical
  let T := sexticResidueImage p r S
  have hrep (a : ↥T) : ∃ z ∈ S, (fun k => (z k : ZMod (p ^ r))) = a.val :=
    Finset.mem_image.mp a.property
  choose z hz heq using hrep
  have hunit (a : ↥T) : ∃ k, ¬ (p : ℤ) ∣ z a k :=
    sextic_has_nondvd_coordinate p c hc (z a) (hS _ (hz a))
  choose k hk using hunit
  let f : ↥T → (Fin 3 → ZMod p) × Fin 3 × (Fin 2 → ZMod (p ^ r)) := fun a =>
    (fun j => (z a j : ZMod p), k a, fun j => (z a ((k a).succAbove j) : ZMod (p ^ r)))
  have hinj : Function.Injective f := by
    intro a b hab
    have hres := congrArg Prod.fst hab
    have hrest := congrArg Prod.snd hab
    have hkab : k a = k b := congrArg Prod.fst hrest
    have hfree : ∀ j, j ≠ k a →
        (z a j : ZMod (p ^ r)) = (z b j : ZMod (p ^ r)) := by
      intro j hj
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj
      have h := congrFun (congrArg Prod.snd hrest) i
      change (z a ((k a).succAbove i) : ZMod (p ^ r)) =
        (z b ((k b).succAbove i) : ZMod (p ^ r)) at h
      simpa only [← hkab, hi] using h
    have h := sextic_chart_congruence p h6 r c (z a) (z b)
      (hS _ (hz a)) (hS _ (hz b)) (k a) (hk a) (fun j => congrFun hres j) hfree
    apply Subtype.ext
    rw [← heq a, ← heq b]
    exact funext h
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, mul_comm, mul_left_comm, mul_assoc] using hcard

#print axioms card_sexticResidueImage_le
-- 'Erdos477.Counting.card_sexticResidueImage_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting

import ErdosProblems.Erdos1105.AlternatingEnds

namespace Erdos1105

open SimpleGraph Finset

def pathInitialBlock {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (a : ℕ) : Finset V := (range a).image p.getVert

def pathFinalBlock {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (a : ℕ) : Finset V := (range a).image (fun i ↦ p.getVert (p.length - i))

def pathAttachments {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (d a : ℕ) : Finset V :=
  (range (d + 2 - a)).image (fun i ↦ p.getVert (a + 2 * i))

lemma mem_pathInitialBlock {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) {a i : ℕ} (ha : a ≤ p.length + 1) (hi : i ≤ p.length) :
    p.getVert i ∈ pathInitialBlock p a ↔ i < a := by
  constructor
  · rintro h
    obtain ⟨j, hj, heq⟩ := mem_image.mp h
    have hja := mem_range.mp hj
    have := hp.getVert_injOn (show j ≤ p.length by omega) hi heq
    omega
  · intro h
    exact mem_image.mpr ⟨i, mem_range.mpr h, rfl⟩

lemma mem_pathFinalBlock {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) {a i : ℕ} (ha : a ≤ p.length + 1) (hi : i ≤ p.length) :
    p.getVert i ∈ pathFinalBlock p a ↔ p.length + 1 - a ≤ i := by
  constructor
  · rintro h
    obtain ⟨j, hj, heq⟩ := mem_image.mp h
    have hja := mem_range.mp hj
    have := hp.getVert_injOn (Nat.sub_le _ _) hi heq
    omega
  · intro h
    exact mem_image.mpr ⟨p.length - i, mem_range.mpr (by omega), by rw [Nat.sub_sub_self hi]⟩

lemma mem_pathAttachments {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a i : ℕ} (hp : AlternatingEnds p d a) (hi : i ≤ p.length) :
    p.getVert i ∈ pathAttachments p d a ↔ a ≤ i ∧ i ≤ p.length - a ∧ Even (i - a) := by
  have hlen := hp.length_eq
  have ha := hp.pos
  have had := hp.le_core
  constructor
  · intro h
    obtain ⟨j, hj, heq⟩ := mem_image.mp h
    have hjc := mem_range.mp hj
    have heq' := hp.isPath.getVert_injOn (show a + 2 * j ≤ p.length by omega) hi heq
    exact ⟨by omega, by omega, j, by omega⟩
  · rintro ⟨hai, hia, j, hj⟩
    exact mem_image.mpr ⟨j, mem_range.mpr (by omega), by
      have heq : a + 2 * j = i := by omega
      rw [heq]⟩

lemma pathInitialBlock_card {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) {a : ℕ} (ha : a ≤ p.length + 1) :
    (pathInitialBlock p a).card = a := by
  rw [pathInitialBlock, card_image_of_injOn, card_range]
  intro i hi j hj heq
  exact hp.getVert_injOn (show i ≤ p.length by have := mem_range.mp hi; omega)
    (show j ≤ p.length by have := mem_range.mp hj; omega) heq

lemma pathFinalBlock_card {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) {a : ℕ} (ha : a ≤ p.length + 1) :
    (pathFinalBlock p a).card = a := by
  rw [pathFinalBlock, card_image_of_injOn, card_range]
  intro i hi j hj heq
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  have := hp.getVert_injOn (Nat.sub_le _ _) (Nat.sub_le _ _) heq
  omega

lemma pathAttachments_card {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} {d a : ℕ} (hp : AlternatingEnds p d a) :
    (pathAttachments p d a).card = d + 2 - a := by
  have hlen := hp.length_eq
  have ha := hp.pos
  have had := hp.le_core
  rw [pathAttachments, card_image_of_injOn, card_range]
  intro i hi j hj heq
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  have := hp.isPath.getVert_injOn (show a + 2 * i ≤ p.length by omega)
    (show a + 2 * j ≤ p.length by omega) heq
  omega

end Erdos1105

#print axioms Erdos1105.pathAttachments_card

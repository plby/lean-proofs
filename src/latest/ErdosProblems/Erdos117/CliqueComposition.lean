import ErdosProblems.Erdos117.CentralForm

/-!
# Composing cliques across central layers

Commutators from different central layers cannot cancel when the earlier
one is nontrivial modulo the later layer. This gives the group-theoretic
part of the interaction-product and nested-anchor constructions.
-/

namespace Erdos117

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_mul_left_of_class_two (hG : commutator G ≤ Subgroup.center G)
    (x y z : G) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ :=
  congrArg Subtype.val (centralCommutator_mul_left (Subgroup.center G) hG le_rfl x y z)

theorem commutator_mul_right_of_class_two (hG : commutator G ≤ Subgroup.center G)
    (x y z : G) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ :=
  congrArg Subtype.val (centralCommutator_mul_right (Subgroup.center G) hG le_rfl x y z)

theorem commutator_mul_mul_of_cross_commute (hG : commutator G ≤ Subgroup.center G)
    {a b c d : G} (had : Commute a d) (hcb : Commute c b) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ * ⁅c, d⁆ := by
  rw [commutator_mul_left_of_class_two hG, commutator_mul_right_of_class_two hG,
    commutator_mul_right_of_class_two hG, had.commutator_eq, hcb.commutator_eq,
    mul_one, one_mul]

theorem commutator_same_anchor (hG : commutator G ≤ Subgroup.center G)
    {a x y : G} (hx : Commute a x) (hy : Commute a y) :
    ⁅a * x, a * y⁆ = ⁅x, y⁆ := by
  rw [commutator_mul_mul_of_cross_commute hG hy hx.symm,
    commutatorElement_self, one_mul]

theorem mul_not_one_of_notMem_of_mem (K : Subgroup G) {x y : G}
    (hx : x ∉ K) (hy : y ∈ K) : x * y ≠ 1 := by
  intro h
  apply hx
  rw [eq_inv_of_mul_eq_one_left h]
  exact K.inv_mem hy

/-- Exact cross-centralization lets the two commutators multiply. If the
first lies outside `K` and the second inside `K`, their product is nontrivial.
Injectivity of the product family follows from this clique property itself. -/
theorem layered_product_clique (hG : commutator G ≤ Subgroup.center G)
    (K : Subgroup G) {ι κ : Type*} (t : ι → G) (d : κ → G)
    (ht : ∀ i j, i ≠ j → ⁅t i, t j⁆ ∉ K)
    (hd : ∀ i j, i ≠ j → ¬Commute (d i) (d j))
    (hdK : ∀ i j, ⁅d i, d j⁆ ∈ K) (hcross : ∀ i j, Commute (t i) (d j)) :
    ∀ i j : ι × κ, i ≠ j → ¬Commute (t i.1 * d i.2) (t j.1 * d j.2) := by
  intro i j hij hc
  have h := hc.commutator_eq
  rw [commutator_mul_mul_of_cross_commute hG (hcross i.1 j.2) (hcross j.1 i.2).symm] at h
  by_cases hfirst : i.1 = j.1
  · have hsecond : i.2 ≠ j.2 := fun heq => hij (Prod.ext hfirst heq)
    rw [hfirst, commutatorElement_self, one_mul] at h
    exact hd i.2 j.2 hsecond (commutatorElement_eq_one_iff_commute.mp h)
  · exact mul_not_one_of_notMem_of_mem K (ht i.1 j.1 hfirst) (hdK i.2 j.2) h

theorem layered_product_card_le (hG : commutator G ≤ Subgroup.center G)
    {n : ℕ} (hn : NoncommutingBound G n) (K : Subgroup G)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (t : ι → G) (d : κ → G)
    (ht : ∀ i j, i ≠ j → ⁅t i, t j⁆ ∉ K)
    (hd : ∀ i j, i ≠ j → ¬Commute (d i) (d j))
    (hdK : ∀ i j, ⁅d i, d j⁆ ∈ K) (hcross : ∀ i j, Commute (t i) (d j)) :
    Fintype.card ι * Fintype.card κ ≤ n := by
  simpa only [Fintype.card_prod] using
    hn.card_le (layered_product_clique hG K t d ht hd hdK hcross)

end Erdos117

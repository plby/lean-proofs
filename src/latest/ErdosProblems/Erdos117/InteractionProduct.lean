import ErdosProblems.Erdos117.CliqueComposition
import ErdosProblems.Erdos117.InteractionIndex
import ErdosProblems.Erdos117.InteractionArithmetic
import ErdosProblems.Erdos117.TransversalClique

/-!
# The interaction-product inequality

A transversal clique at an earlier central layer is combined with a scalar
clique in the exact centralizer at a later layer. Every construction and
index loss is accounted for in an integer-valued inequality.
-/

namespace Erdos117

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Lemma 5.7 in terms of half-ranks and integer clique credits. The witness
`c+1` is an actual clique size, so no positivity proviso or truncated
subtraction is needed in the statement. -/
theorem interaction_product_inequality
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n)
    (A H K : Subgroup G) (hHK : ⁅H, H⁆ ≤ K)
    (β : AlternatingBicharacter A p) (γ : AlternatingBicharacter H p)
    (hβ : ∀ x y : A, β.toFun x y = 0 ↔ ⁅(x : G), (y : G)⁆ ∈ K)
    (hγ : ∀ x y : H, Commute x y → γ.toFun x y = 0)
    {d : ℕ} (hd : d ≤ Module.finrank (ZMod p)
      (subgroupImageSpace (p := p) β.rowMonoidHom (H.subgroupOf A))) :
    ∃ c : ℕ,
      scalarCreditRate p * (Module.finrank (ZMod p) γ.rowSpace / 2) ≤
        c + scalarDefect p + scalarCreditRate p * ((d + 1) * Nat.clog p ((2 * n) ^ 2)) ∧
      (d + 1) * (c + 1) ≤ n := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite H
  let U := subgroupImageSpace (p := p) β.rowMonoidHom (H.subgroupOf A)
  have hU : ∀ u ∈ U, ∀ v ∈ U, β.form u v = 0 := by
    intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := (mem_subgroupImageSpace_iff β.rowMonoidHom (H.subgroupOf A) u).mp hu
    obtain ⟨y, hy, rfl⟩ := (mem_subgroupImageSpace_iff β.rowMonoidHom (H.subgroupOf A) v).mp hv
    change β.form (β.row x) (β.row y) = 0
    rw [β.form_apply, β.pairing_row]
    exact (hβ x y).mpr (hHK (Subgroup.commutator_mem_commutator hx hy))
  obtain ⟨v, hv, htransversal⟩ := exists_transversal_clique β.form β.form_isAlt
    β.form_nondegenerate U hU hd
  choose t ht using fun i => β.row_surjective (v i)
  let T : Fin (d + 1) → G := fun i => t i
  have hT : ∀ i j, i ≠ j → ⁅T i, T j⁆ ∉ K := by
    intro i j hij hmem
    apply hv i j hij
    rw [← ht i, ← ht j, β.form_apply, β.pairing_row]
    exact (hβ (t i) (t j)).mpr hmem
  let C := simultaneousCentralizer H T
  have hC : C.index ≤ p ^ ((d + 1) * Nat.clog p ((2 * n) ^ 2)) := by
    simpa only [Fintype.card_fin] using
      simultaneousCentralizer_index_le_pow (p := p) H T (centralizerIndex_le hn)
  have hγcomm : ∀ x y : H, Commute x y →
      γ.form (γ.rowMonoidHom x).toAdd (γ.rowMonoidHom y).toAdd = 0 := by
    intro x y hxy
    change γ.form (γ.row x) (γ.row y) = 0
    rw [γ.form_apply, γ.pairing_row]
    exact hγ x y hxy
  obtain ⟨c, a, ha, hcredit⟩ := exists_restricted_scalar_clique γ.rowMonoidHom
    γ.row_surjective γ.form γ.form_nondegenerate γ.form_isAlt hγcomm C hC
  let D : Fin (c + 1) → G := fun i => ((a i : H) : G)
  have hD : ∀ i j, i ≠ j → ¬Commute (D i) (D j) := by
    intro i j hij hc
    exact ha i j hij (Subtype.ext (Subtype.ext hc.eq))
  have hDK : ∀ i j, ⁅D i, D j⁆ ∈ K := fun i j =>
    hHK (Subgroup.commutator_mem_commutator (a i).val.2 (a j).val.2)
  have hcross : ∀ i j, Commute (T i) (D j) := fun i j =>
    (mem_simultaneousCentralizer H T (a j).val).mp (a j).2 i
  refine ⟨c, hcredit, ?_⟩
  simpa only [Fintype.card_fin] using
    layered_product_card_le hG hn K T D hT hD hDK hcross

/-- Corollary 5.8 with explicit absolute constants, expressed using the
integer credit per hyperbolic plane. -/
theorem expensive_stage_interaction
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n)
    (A H K : Subgroup G) (hHK : ⁅H, H⁆ ≤ K)
    (β : AlternatingBicharacter A p) (γ : AlternatingBicharacter H p)
    (hβ : ∀ x y : A, β.toFun x y = 0 ↔ ⁅(x : G), (y : G)⁆ ∈ K)
    (hγ : ∀ x y : H, Commute x y → γ.toFun x y = 0)
    (hm : 0 < Module.finrank (ZMod p) γ.rowSpace / 2)
    (hexpensive : 128 * n * Nat.clog p ((2 * n) ^ 2) ≤
      scalarCreditRate p * (Module.finrank (ZMod p) γ.rowSpace / 2) *
        (Module.finrank (ZMod p) γ.rowSpace / 2)) :
    Module.finrank (ZMod p)
        (subgroupImageSpace (p := p) β.rowMonoidHom (H.subgroupOf A)) *
      (scalarCreditRate p * (Module.finrank (ZMod p) γ.rowSpace / 2)) ≤ 4 * n := by
  have hcredit := γ.scalar_credit_bound (hn.subgroup H) hγ
  apply interaction_small_of_expensive scalarCreditRate_pos hm
    (three_quarters_scalar_credit p hm hcredit) (scalarDefect_le_quarter_credit p hm) hexpensive
  intro d hd
  exact interaction_product_inequality hG hn A H K hHK β γ hβ hγ hd

end Erdos117

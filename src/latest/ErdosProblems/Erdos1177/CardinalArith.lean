-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Cardinal arithmetic for the exact linear calibration

This file formalizes the self-contained cardinal-arithmetic lemmas of

  Eric Li, *A Resolution of Erdős Problems 593 and 1177: Obligatory Triple
  Systems and Exact Spectra*, arXiv:2606.24882,

namely the "Small unions" lemma, the "Cardinal facts" lemma, the
"Cofinal fibres" lemma, and the "Successors cofinal" lemma from
Section~7 (Exact linear calibration).  These are theorems of ZFC and are
proved here in full.
-/

open Cardinal Ordinal

namespace Erdos1177

universe u

/-
**Small unions** (paper Lemma, `lem:small-union`).
Let `ρ` be an infinite cardinal, let `μ < cf(ρ)`, and let `(X i)` be a family
indexed by `ι` with `#ι ≤ μ` and `#(X i) < ρ` for every `i`.  Then
`#(⋃ i, X i) < ρ`.
-/
theorem small_union {ι : Type u} {V : Type u} (ρ μ : Cardinal.{u})
    (hρ : ℵ₀ ≤ ρ) (hμ : μ < ρ.ord.cof) (hI : #ι ≤ μ)
    (X : ι → Set V) (hX : ∀ i, #(X i) < ρ) :
    #(↥(⋃ i, X i)) < ρ := by
  convert! Cardinal.mk_iUnion_le ( fun i => X i ) |> lt_of_le_of_lt <| ?_;
  convert! Cardinal.mul_lt_of_lt hρ _ _;
  · exact lt_of_le_of_lt hI ( lt_of_lt_of_le hμ ( Ordinal.cof_ord_le _ ) );
  · convert! Ordinal.iSup_lt _ _;
    · exact lt_of_le_of_lt hI hμ;
    · assumption

/-- **Cardinal facts** (paper Lemma `lem:cardinal-facts`), part (i):
`cf(2^μ) > μ` for infinite `μ` (König's theorem). -/
theorem cf_two_pow (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    μ < ((2:Cardinal.{u}) ^ μ).ord.cof :=
  Cardinal.lt_cof_power hμ one_lt_two

/-- **Cardinal facts**, part (ii): `μ⁺ ≤ 2^μ`. -/
theorem succ_le_two_pow (μ : Cardinal.{u}) :
    Order.succ μ ≤ (2:Cardinal.{u}) ^ μ :=
  Order.succ_le_of_lt (Cardinal.cantor μ)

/-
**Cardinal facts**, part (iii): with `ρ` infinite and `Λ = 2^ρ`,
`Λ ^ ρ = Λ`.
-/
theorem pow_two_pow_self (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ) :
    ((2:Cardinal.{u}) ^ ρ) ^ ρ = (2:Cardinal.{u}) ^ ρ := by
  rw [ ← Cardinal.power_mul, Cardinal.mul_eq_self ] ; aesop

/-- **Cardinal facts**, part (iv): `ρ⁺ ≤ 2^ρ`. -/
theorem succ_le_two_pow' (ρ : Cardinal.{u}) :
    Order.succ ρ ≤ (2:Cardinal.{u}) ^ ρ :=
  Order.succ_le_of_lt (Cardinal.cantor ρ)

/-
**Successors cofinal** (paper Lemma `lem:successors-cofinal`).
If `κ` is an uncountable limit cardinal, then for every ordinal `α < κ.ord`
there is an uncountable successor cardinal `ν⁺` with `α < ν⁺.ord` and
`ν⁺ < κ`.  (This is the cofinality of the uncountable successor cardinals
below `κ`.)
-/
theorem successors_cofinal (κ : Cardinal.{u}) (hκ : ℵ₀ < κ)
    (hlim : ∀ ν : Cardinal.{u}, κ ≠ Order.succ ν) (α : Ordinal.{u}) (hα : α < κ.ord) :
    ∃ ν : Cardinal.{u}, ℵ₀ ≤ ν ∧ Order.succ ν < κ ∧ α < (Order.succ ν).ord := by
  obtain ⟨ν, hν⟩ : ∃ ν : Cardinal, Cardinal.aleph0 ≤ ν ∧ ν < κ ∧ α < (Order.succ ν).ord := by
    refine' ⟨ Max.max ℵ₀ α.card, _, _, _ ⟩ <;> simp_all +decide [ Cardinal.lt_ord ];
  refine' ⟨ ν, hν.1, lt_of_le_of_ne _ _, hν.2.2 ⟩;
  · exact Order.succ_le_of_lt hν.2.1;
  · exact Ne.symm ( hlim ν )

/-
**Cofinal fibres** (paper Lemma `lem:cofinal-fibres`).
If `κ ≤ ρ` are infinite cardinals and `R = ρ⁺`, then there is a map
`q` from the ordinals below `R.ord` to the ordinals below `κ.ord` (i.e. to
`κ` colours) every fibre of which is cofinal in `R.ord`.  Concretely, for
every colour `ξ < κ.ord` and every bound `β < R.ord` there is `α` in the
fibre with `β ≤ α < R.ord`.
-/
theorem cofinal_fibres (κ ρ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hρ : κ ≤ ρ) :
    ∃ q : Ordinal.{u} → Ordinal.{u},
      (∀ α, α < (Order.succ ρ).ord → q α < κ.ord) ∧
      (∀ ξ, ξ < κ.ord → ∀ β, β < (Order.succ ρ).ord →
        ∃ α, β ≤ α ∧ α < (Order.succ ρ).ord ∧ q α = ξ) := by
  refine' ⟨ fun α => α % κ.ord, _, _ ⟩;
  · intro α hα;
    by_cases h : κ.ord = 0;
    · simp_all +decide [ Cardinal.ord_eq_zero ];
      exact absurd hκ ( ne_of_gt ( Cardinal.aleph0_pos ) );
    · exact Ordinal.mod_lt _ h;
  · intro ξ hξ β hβ;
    refine' ⟨ κ.ord * β + ξ, _, _, _ ⟩;
    · refine' le_trans _ le_self_add;
      refine' le_mul_of_one_le_left' _;
      contrapose! hκ; aesop;
    · -- Since $β < (Order.succ ρ).ord$, we have $β.card ≤ ρ$.
      have hβ_card : β.card ≤ ρ := by
        grind +suggestions;
      -- Since $ξ < κ.ord$, we have $ξ.card < κ$.
      have hξ_card : ξ.card < κ := by
        grind +suggestions;
      -- Since $κ.ord * β + ξ$ is an ordinal, we have $(κ.ord * β + ξ).card ≤ κ * β.card + ξ.card$.
      have h_card : (κ.ord * β + ξ).card ≤ κ * β.card + ξ.card := by
        refine' le_trans ( Ordinal.card_add _ _ |> le_of_eq ) _;
        rw [ Ordinal.card_mul ];
        rw [ Cardinal.card_ord ];
      -- Since $κ * β.card + ξ.card ≤ ρ$, we have $(κ.ord * β + ξ).card ≤ ρ$.
      have h_card_le_ρ : (κ.ord * β + ξ).card ≤ ρ := by
        refine le_trans h_card ?_;
        refine' le_trans ( add_le_add ( mul_le_mul_left hρ _ ) hξ_card.le ) _;
        refine' le_trans ( add_le_add ( mul_le_mul_right hβ_card _ ) hρ ) _;
        rw [ Cardinal.mul_eq_self ];
        · rw [ Cardinal.add_eq_self ];
          exact le_trans hκ hρ;
        · exact le_trans hκ hρ;
      grind +suggestions;
    · simp +decide [ Ordinal.mod_eq_of_lt, hξ ]

end Erdos1177

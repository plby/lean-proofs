import ErdosProblems.Erdos788.CodeGeometry
import ErdosProblems.Erdos788.FiniteCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The regular-simplex list bound for `ZMod p` words

This is the deterministic half of the short-code lemma.  A code with the
stated near-Plotkin distance automatically has the list bound needed by the
extractor reconstruction.
-/

namespace Erdos788

open scoped BigOperators

/-- The binary strings used as code-coordinate labels. -/
abbrev BinaryCoord (ell : ℕ) := Fin ell → Bool

/-- An unnormalized regular-simplex coordinate for one `ZMod p` symbol. -/
noncomputable def simplexEntry (p : ℕ) (a c : ZMod p) : ℝ :=
  if a = c then (p : ℝ) - 1 else -1

theorem sum_simplexEntry_mul {p : ℕ} [NeZero p] (a b : ZMod p) :
    (∑ c : ZMod p, simplexEntry p a c * simplexEntry p b c) =
      if a = b then (p : ℝ) * (p - 1) else -(p : ℝ) := by
  classical
  by_cases hab : a = b
  · subst b
    have hpoint : ∀ c : ZMod p,
        simplexEntry p a c * simplexEntry p a c =
          if a = c then ((p : ℝ) - 1) ^ 2 else 1 := by
      intro c
      by_cases hac : a = c <;> simp [simplexEntry, hac, pow_two]
    have hsame :
        (Finset.univ.filter fun c : ZMod p ↦ a = c).card = 1 := by
      rw [show (Finset.univ.filter fun c : ZMod p ↦ a = c) = {a} by
        ext c
        simp [eq_comm]]
      simp
    have hsplitNat :
        (Finset.univ.filter fun c : ZMod p ↦ a = c).card +
            (Finset.univ.filter fun c : ZMod p ↦ ¬a = c).card = p := by
      simpa only [Finset.card_univ, ZMod.card] using!
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (ZMod p))) (fun c ↦ a = c))
    have hsplit :
        ((Finset.univ.filter fun c : ZMod p ↦ a = c).card : ℝ) +
            ((Finset.univ.filter fun c : ZMod p ↦ ¬a = c).card : ℝ) =
          (p : ℝ) := by
      exact_mod_cast hsplitNat
    rw [Finset.sum_congr rfl fun c _hc ↦ hpoint c]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsame] at hsplit ⊢
    norm_num at hsplit ⊢
    nlinarith
  · have hpoint : ∀ c : ZMod p,
        simplexEntry p a c * simplexEntry p b c =
          if a = c then 1 - (p : ℝ)
          else if b = c then 1 - (p : ℝ) else 1 := by
      intro c
      by_cases hac : a = c
      · have hbc : b ≠ c := by
          intro hbc
          exact hab (hac.trans hbc.symm)
        simp [simplexEntry, hac, hbc]
      · by_cases hbc : b = c <;> simp [simplexEntry, hac, hbc]
    let A : Finset (ZMod p) :=
      Finset.univ.filter fun c ↦ a = c
    let R : Finset (ZMod p) :=
      Finset.univ.filter fun c ↦ ¬a = c
    let B : Finset (ZMod p) := R.filter fun c ↦ b = c
    let C : Finset (ZMod p) := R.filter fun c ↦ ¬b = c
    have hA : A.card = 1 := by
      rw [show A = {a} by
        ext c
        simp [A, eq_comm]]
      simp
    have hB : B.card = 1 := by
      rw [show B = {b} by
        ext c
        simp only [B, R, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · rintro ⟨_hac, hbc⟩
          exact hbc.symm
        · intro hcb
          subst c
          exact ⟨hab, rfl⟩]
      simp
    have hAR : A.card + R.card = p := by
      simpa only [A, R, Finset.card_univ, ZMod.card] using!
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (ZMod p))) (fun c ↦ a = c))
    have hBC : B.card + C.card = R.card := by
      simpa only [B, C] using!
        (Finset.card_filter_add_card_filter_not
          (s := R) (fun c ↦ b = c))
    have htotalNat : A.card + B.card + C.card = p := by omega
    have htotal : (A.card : ℝ) + (B.card : ℝ) + (C.card : ℝ) = (p : ℝ) := by
      exact_mod_cast htotalNat
    rw [Finset.sum_congr rfl fun c _hc ↦ hpoint c]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    change (A.card : ℝ) * (1 - (p : ℝ)) +
        ((B.card : ℝ) * (1 - (p : ℝ)) + (C.card : ℝ)) =
          if a = b then (p : ℝ) * (p - 1) else -(p : ℝ)
    rw [if_neg hab]
    rw [hA, hB] at htotal ⊢
    norm_num at htotal ⊢
    nlinarith

/-- Number of coordinates at which two words agree. -/
noncomputable def agreementCount {p ell : ℕ}
    (u v : BinaryCoord ell → ZMod p) : ℕ := by
  classical
  exact (Finset.univ.filter fun z ↦ u z = v z).card

/-- Fraction of coordinates at which two words agree. -/
noncomputable def agreement {p ell : ℕ}
    (u v : BinaryCoord ell → ZMod p) : ℝ :=
  (agreementCount u v : ℝ) / Fintype.card (BinaryCoord ell)

@[simp]
theorem agreementCount_self {p ell : ℕ}
    (u : BinaryCoord ell → ZMod p) :
    agreementCount u u = Fintype.card (BinaryCoord ell) := by
  classical
  simp [agreementCount]

@[simp]
theorem agreement_self {p ell : ℕ}
    (u : BinaryCoord ell → ZMod p) : agreement u u = 1 := by
  rw [agreement, agreementCount_self]
  exact div_self (by
    exact_mod_cast
      (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card (BinaryCoord ell))))

/-- The common squared norm of the unnormalized simplex word vectors. -/
noncomputable def simplexWordScale (p ell : ℕ) : ℝ :=
  (Fintype.card (BinaryCoord ell) : ℝ) * p * (p - 1)

theorem simplexWordScale_pos {p ell : ℕ} (hp : 1 < p) :
    0 < simplexWordScale p ell := by
  have hcoord : (0 : ℝ) < Fintype.card (BinaryCoord ell) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BinaryCoord ell))
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  rw [simplexWordScale]
  exact mul_pos (mul_pos hcoord (by positivity)) (sub_pos.mpr hpR)

/-- The unnormalized concatenated simplex vector of a word. -/
noncomputable def wordSimplexRaw {p ell : ℕ}
    (u : BinaryCoord ell → ZMod p) :
    BinaryCoord ell × ZMod p → ℝ :=
  fun q ↦ simplexEntry p (u q.1) q.2

theorem finiteDot_wordSimplexRaw {p ell : ℕ} [NeZero p]
    (u v : BinaryCoord ell → ZMod p) :
    finiteDot (wordSimplexRaw u) (wordSimplexRaw v) =
      (p : ℝ) *
        ((p : ℝ) * agreementCount u v -
          Fintype.card (BinaryCoord ell)) := by
  classical
  rw [finiteDot]
  rw [Fintype.sum_prod_type]
  simp_rw [wordSimplexRaw, sum_simplexEntry_mul]
  let same : Finset (BinaryCoord ell) :=
    Finset.univ.filter fun z ↦ u z = v z
  let diff : Finset (BinaryCoord ell) :=
    Finset.univ.filter fun z ↦ ¬u z = v z
  have hsplit : same.card + diff.card = Fintype.card (BinaryCoord ell) := by
    simpa only [same, diff, Finset.card_univ] using!
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (BinaryCoord ell)))
        (fun z ↦ u z = v z))
  have hsame : same.card = agreementCount u v := rfl
  have hsplitR : (same.card : ℝ) + (diff.card : ℝ) =
      (Fintype.card (BinaryCoord ell) : ℝ) := by
    exact_mod_cast hsplit
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change (same.card : ℝ) * ((p : ℝ) * (p - 1)) +
    (diff.card : ℝ) * (-(p : ℝ)) = _
  rw [hsame] at hsplitR ⊢
  nlinarith

theorem finiteDot_wordSimplexRaw_eq_scale_mul {p ell : ℕ} [NeZero p]
    (hp : 1 < p) (u v : BinaryCoord ell → ZMod p) :
    finiteDot (wordSimplexRaw u) (wordSimplexRaw v) =
      simplexWordScale p ell *
        (((p : ℝ) * agreement u v - 1) / ((p : ℝ) - 1)) := by
  rw [finiteDot_wordSimplexRaw, agreement, simplexWordScale]
  have hcoord : (0 : ℝ) < Fintype.card (BinaryCoord ell) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BinaryCoord ell))
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  field_simp [ne_of_gt hcoord, ne_of_gt (sub_pos.mpr hpR)]

theorem finiteDot_wordSimplexRaw_le_of_agreement_le
    {p ell : ℕ} [NeZero p] (hp : 1 < p)
    (u v : BinaryCoord ell → ZMod p) (a : ℝ)
    (h : agreement u v ≤ a) :
    finiteDot (wordSimplexRaw u) (wordSimplexRaw v) ≤
      simplexWordScale p ell *
        (((p : ℝ) * a - 1) / ((p : ℝ) - 1)) := by
  rw [finiteDot_wordSimplexRaw_eq_scale_mul hp]
  apply mul_le_mul_of_nonneg_left _ (simplexWordScale_pos hp).le
  apply (div_le_div_iff_of_pos_right (by
    exact sub_pos.mpr (by exact_mod_cast hp))).2
  have hp0 : (0 : ℝ) ≤ p := by positivity
  nlinarith

theorem finiteDot_wordSimplexRaw_lt_of_agreement_lt
    {p ell : ℕ} [NeZero p] (hp : 1 < p)
    (u v : BinaryCoord ell → ZMod p) (a : ℝ)
    (h : agreement u v < a) :
    finiteDot (wordSimplexRaw u) (wordSimplexRaw v) <
      simplexWordScale p ell *
        (((p : ℝ) * a - 1) / ((p : ℝ) - 1)) := by
  rw [finiteDot_wordSimplexRaw_eq_scale_mul hp]
  apply mul_lt_mul_of_pos_left _ (simplexWordScale_pos hp)
  apply (div_lt_div_iff_of_pos_right (by
    exact sub_pos.mpr (by exact_mod_cast hp))).2
  have hp0 : (0 : ℝ) < p := by positivity
  nlinarith

theorem scale_mul_lt_finiteDot_wordSimplexRaw_of_lt_agreement
    {p ell : ℕ} [NeZero p] (hp : 1 < p)
    (u v : BinaryCoord ell → ZMod p) (a : ℝ)
    (h : a < agreement u v) :
    simplexWordScale p ell *
        (((p : ℝ) * a - 1) / ((p : ℝ) - 1)) <
      finiteDot (wordSimplexRaw u) (wordSimplexRaw v) := by
  rw [finiteDot_wordSimplexRaw_eq_scale_mul hp]
  apply mul_lt_mul_of_pos_left _ (simplexWordScale_pos hp)
  apply (div_lt_div_iff_of_pos_right (by
    exact sub_pos.mpr (by exact_mod_cast hp))).2
  have hp0 : (0 : ℝ) < p := by positivity
  nlinarith

theorem sum_sq_wordSimplexRaw {p ell : ℕ} [NeZero p]
    (u : BinaryCoord ell → ZMod p) :
    (∑ q, wordSimplexRaw u q ^ 2) = simplexWordScale p ell := by
  rw [show (∑ q, wordSimplexRaw u q ^ 2) =
      finiteDot (wordSimplexRaw u) (wordSimplexRaw u) by
    simp only [finiteDot, pow_two]]
  rw [finiteDot_wordSimplexRaw, agreementCount_self, simplexWordScale]
  ring

theorem finiteDot_wordSimplexRaw_self {p ell : ℕ} [NeZero p]
    (u : BinaryCoord ell → ZMod p) :
    finiteDot (wordSimplexRaw u) (wordSimplexRaw u) =
      simplexWordScale p ell := by
  rw [finiteDot_wordSimplexRaw, agreementCount_self, simplexWordScale]
  ring

/-- The deterministic list-decoding implication used by the short-code
construction.  A near-Plotkin pairwise agreement bound forces every strict
agreement list to have the paper's explicit size bound. -/
theorem card_lt_two_div_sq_add_one_of_pairwise_agreement
    {p ell : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fact p.Prime]
    (η τ : ℝ) (hη : 0 < η)
    (hτ : τ = (p : ℝ) * η ^ 2 / (2 * ((p : ℝ) - 1)))
    (L : Finset ι)
    (word : ι → BinaryCoord ell → ZMod p)
    (Q : BinaryCoord ell → ZMod p)
    (hpair : ∀ i ∈ L, ∀ j ∈ L, i ≠ j →
      agreement (word i) (word j) ≤ 1 / (p : ℝ) + τ)
    (hcorr : ∀ i ∈ L,
      1 / (p : ℝ) + η < agreement (word i) Q) :
    (L.card : ℝ) < 2 / η ^ 2 + 1 := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  letI : NeZero p := ⟨by omega⟩
  by_cases hL : L.Nonempty
  · let q : ℝ := simplexWordScale p ell
    let β : ℝ := (p : ℝ) * τ / ((p : ℝ) - 1)
    let γ : ℝ := (p : ℝ) * η / ((p : ℝ) - 1)
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp
    have hpR0 : (0 : ℝ) < p := by positivity
    have hden : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hpR
    have hq : 0 < q := simplexWordScale_pos hp
    have hγ : 0 < γ := by
      dsimp [γ]
      positivity
    have hβeq : β = γ ^ 2 / 2 := by
      dsimp [β, γ]
      rw [hτ]
      field_simp [ne_of_gt hpR0, ne_of_gt hden]
    have hgap : β < γ ^ 2 := by
      rw [hβeq]
      nlinarith [sq_pos_of_pos hγ]
    have hw : ∑ k, wordSimplexRaw Q k ^ 2 = q :=
      sum_sq_wordSimplexRaw Q
    have hdiag : ∀ i ∈ L,
        finiteDot (wordSimplexRaw (word i)) (wordSimplexRaw (word i)) ≤ q := by
      intro i _hi
      exact (finiteDot_wordSimplexRaw_self (word i)).le
    have hoff : ∀ i ∈ L, ∀ j ∈ L, i ≠ j →
        finiteDot (wordSimplexRaw (word i)) (wordSimplexRaw (word j)) ≤
          q * β := by
      intro i hi j hj hij
      calc
        finiteDot (wordSimplexRaw (word i)) (wordSimplexRaw (word j)) ≤
            q * (((p : ℝ) * (1 / (p : ℝ) + τ) - 1) /
              ((p : ℝ) - 1)) :=
          finiteDot_wordSimplexRaw_le_of_agreement_le hp _ _ _
            (hpair i hi j hj hij)
        _ = q * β := by
          dsimp [β]
          field_simp [ne_of_gt hpR0]
          ring
    have hcorrRaw : ∀ i ∈ L, q * γ <
        finiteDot (wordSimplexRaw (word i)) (wordSimplexRaw Q) := by
      intro i hi
      calc
        q * γ = q * (((p : ℝ) * (1 / (p : ℝ) + η) - 1) /
            ((p : ℝ) - 1)) := by
          dsimp [γ]
          field_simp [ne_of_gt hpR0]
          ring
        _ < finiteDot (wordSimplexRaw (word i)) (wordSimplexRaw Q) :=
          scale_mul_lt_finiteDot_wordSimplexRaw_of_lt_agreement hp _ _ _
            (hcorr i hi)
    have hgeom := card_lt_simplex_list_bound_scaled
      L (fun i ↦ wordSimplexRaw (word i)) (wordSimplexRaw Q)
      q β γ hL hq hw hdiag hoff hcorrRaw hγ.le hgap
    have hβnonneg : 0 ≤ β := by
      rw [hβeq]
      positivity
    have hgeomDen : 0 < γ ^ 2 - β := sub_pos.mpr hgap
    have hratioOne : (1 - β) / (γ ^ 2 - β) ≤
        1 / (γ ^ 2 - β) := by
      exact (div_le_div_iff_of_pos_right hgeomDen).2 (by nlinarith)
    have hdenEq : γ ^ 2 - β = γ ^ 2 / 2 := by
      rw [hβeq]
      ring
    have hηleγ : η ≤ γ := by
      dsimp [γ]
      apply (le_div_iff₀ hden).2
      nlinarith
    have hsq : η ^ 2 ≤ γ ^ 2 := by nlinarith
    have htwo : 2 / γ ^ 2 ≤ 2 / η ^ 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hη) hsq
    have hratio : (1 - β) / (γ ^ 2 - β) ≤ 2 / η ^ 2 := by
      calc
        (1 - β) / (γ ^ 2 - β) ≤ 1 / (γ ^ 2 - β) := hratioOne
        _ = 2 / γ ^ 2 := by rw [hdenEq]; field_simp
        _ ≤ 2 / η ^ 2 := htwo
    exact hgeom.trans_le (hratio.trans (by linarith))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hL]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hetaSq : 0 < η ^ 2 := sq_pos_of_pos hη
    positivity

end Erdos788

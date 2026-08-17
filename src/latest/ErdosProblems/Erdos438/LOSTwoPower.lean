/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import Mathlib

/-!
# The two-primary finite lemma of Lagarias--Odlyzko--Shearer

This file proves the part of the modular theorem which remains after the odd
part has been fractionally covered by triangles.  A function `F` assigns to
each element of `ZMod n` the colours of `K_3` which occur above it.  The
condition `SquareSumColoring n F` says exactly that the corresponding subset
of `Q_n × K_3` is independent.
-/

open scoped BigOperators

namespace Erdos438

/-- The fibre formulation of independence in `Q_n × K_3`. -/
def SquareSumColoring (n : ℕ) (F : ZMod n → Finset (Fin 3)) : Prop :=
  ∀ x y, IsSquare (x + y) → ∀ c ∈ F x, ∀ d ∈ F y, c = d

/-! ## Odd square roots modulo powers of two -/

/-- The elementary lifting calculation behind the fact that every integer
congruent to `1` modulo `8` is a square modulo every power of two.  Keeping an
explicit quotient makes the induction purely algebraic. -/
lemma odd_square_lift (a : ℤ) (k : ℕ)
    (ha : ∃ q : ℤ, a - 1 = 8 * q) :
    ∃ r q : ℤ, Odd r ∧ a - r * r = (2 : ℤ) ^ (k + 3) * q := by
  induction k with
  | zero =>
      obtain ⟨q, hq⟩ := ha
      refine ⟨1, q, odd_one, ?_⟩
      norm_num at hq ⊢
      simpa [hq] using hq
  | succ k ih =>
      obtain ⟨r, q, hr, hq⟩ := ih
      rcases Int.even_or_odd q with hqeven | hqodd
      · obtain ⟨s, rfl⟩ := hqeven
        refine ⟨r, s, hr, ?_⟩
        rw [hq, pow_succ]
        ring
      · obtain ⟨s, hs⟩ := hqodd
        obtain ⟨t, ht⟩ := hr
        let p : ℤ := (2 : ℤ) ^ (k + 2)
        refine ⟨r + p, s - t - (2 : ℤ) ^ k, ?_, ?_⟩
        · refine ⟨t + (2 : ℤ) ^ (k + 1), ?_⟩
          dsimp [p]
          rw [ht]
          ring
        · dsimp [p]
          calc
            a - (r + (2 : ℤ) ^ (k + 2)) * (r + (2 : ℤ) ^ (k + 2)) =
                (a - r * r) - 2 * r * 2 ^ (k + 2) - (2 ^ (k + 2)) ^ 2 := by ring
            _ = (2 : ℤ) ^ (k + 4) * (s - t - 2 ^ k) := by
              rw [hq, hs, ht]
              ring
            _ = (2 : ℤ) ^ (k + 1 + 3) * (s - t - 2 ^ k) := by ring

/-- Every natural number congruent to `1` modulo `8` is a square in
`ZMod (2^j)` for `j ≥ 3`. -/
lemma isSquare_zmod_two_pow_of_mod_eight_eq_one {j a : ℕ} (hj : 3 ≤ j)
    (ha : a % 8 = 1) : IsSquare (a : ZMod (2 ^ j)) := by
  have haMod : a ≡ 1 [MOD 8] := ha
  have hdvd : (8 : ℤ) ∣ (a : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd.mp haMod)
    simpa [sub_eq_add_neg, add_comm] using dvd_neg.mpr h
  obtain ⟨q, hq⟩ := hdvd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  obtain ⟨r, q', -, hr⟩ := odd_square_lift (a : ℤ) k ⟨q, by simpa [hq]⟩
  refine ⟨(r : ZMod (2 ^ (3 + k))), ?_⟩
  rw [show (a : ZMod (2 ^ (3 + k))) = ((a : ℤ) : ZMod (2 ^ (3 + k))) by simp]
  rw [show ((a : ℤ) : ZMod (2 ^ (3 + k))) = (r : ZMod (2 ^ (3 + k))) * r by
    apply sub_eq_zero.mp
    calc
      ((a : ℤ) : ZMod (2 ^ (3 + k))) - (r : ZMod (2 ^ (3 + k))) * r =
          ((a - r * r : ℤ) : ZMod (2 ^ (3 + k))) := by push_cast; rfl
      _ = ((2 : ℤ) ^ (k + 3) * q' : ℤ) := by rw [hr]
      _ = 0 := by
        rw [show k + 3 = 3 + k by omega, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact dvd_mul_right _ _]

/-! ## Three-colour fibre estimates -/

lemma fin3_card_le (S : Finset (Fin 3)) : S.card ≤ 3 := by
  simpa using S.card_le_univ

lemma card_le_one_of_cross_eq {S T : Finset (Fin 3)} (hS : S.Nonempty) (hT : T.Nonempty)
    (h : ∀ c ∈ S, ∀ d ∈ T, c = d) : S.card ≤ 1 ∧ T.card ≤ 1 := by
  obtain ⟨d, hd⟩ := hT
  obtain ⟨c, hc⟩ := hS
  constructor
  · rw [Finset.card_le_one]
    intro x hx y hy
    exact (h x hx d hd).trans (h y hy d hd).symm
  · rw [Finset.card_le_one]
    intro x hx y hy
    exact (h c hc x hx).symm.trans (h c hc y hy)

lemma card_add_card_le_three_of_cross_eq {S T : Finset (Fin 3)}
    (h : ∀ c ∈ S, ∀ d ∈ T, c = d) : S.card + T.card ≤ 3 := by
  by_cases hS : S.Nonempty
  · by_cases hT : T.Nonempty
    · obtain ⟨hS1, hT1⟩ := card_le_one_of_cross_eq hS hT h
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hT]
      simpa using fin3_card_le S
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simpa using fin3_card_le T

lemma card_three_le_three_of_pairwise_cross_eq {S T U : Finset (Fin 3)}
    (hST : ∀ c ∈ S, ∀ d ∈ T, c = d)
    (hSU : ∀ c ∈ S, ∀ d ∈ U, c = d)
    (hTU : ∀ c ∈ T, ∀ d ∈ U, c = d) :
    S.card + T.card + U.card ≤ 3 := by
  by_cases hS : S.Nonempty
  · by_cases hT : T.Nonempty
    · have hS1 := (card_le_one_of_cross_eq hS hT hST).1
      have hT1 := (card_le_one_of_cross_eq hS hT hST).2
      by_cases hU : U.Nonempty
      · have hU1 := (card_le_one_of_cross_eq hS hU hSU).2
        omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp hU]
        simpa using Nat.add_le_add_right (card_add_card_le_three_of_cross_eq hST) 0
    · rw [Finset.not_nonempty_iff_eq_empty.mp hT]
      simpa using card_add_card_le_three_of_cross_eq hSU
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simpa using card_add_card_le_three_of_cross_eq hTU

lemma four_fibers_card_le
    {S0 S1 S2 S3 : Finset (Fin 3)}
    (h0 : ∀ c ∈ S0, ∀ d ∈ S0, c = d)
    (h2 : ∀ c ∈ S2, ∀ d ∈ S2, c = d)
    (h01 : ∀ c ∈ S0, ∀ d ∈ S1, c = d)
    (h13 : ∀ c ∈ S1, ∀ d ∈ S3, c = d)
    (h23 : ∀ c ∈ S2, ∀ d ∈ S3, c = d) :
    S0.card + S1.card + S2.card + S3.card ≤ 4 := by
  have h0c : S0.card ≤ 1 := by
    rw [Finset.card_le_one]
    exact h0
  have h2c : S2.card ≤ 1 := by
    rw [Finset.card_le_one]
    exact h2
  by_cases h1 : S1.Nonempty
  · by_cases h3 : S3.Nonempty
    · have h1c := (card_le_one_of_cross_eq h1 h3 h13).1
      have h3c := (card_le_one_of_cross_eq h1 h3 h13).2
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp h3]
      have h01c := card_add_card_le_three_of_cross_eq h01
      simp only [Finset.card_empty, add_zero]
      omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp h1]
    have h23c := card_add_card_le_three_of_cross_eq h23
    simp only [Finset.card_empty]
    omega

lemma squareSumColoring_four_bound
    (F : ZMod 4 → Finset (Fin 3)) (hF : SquareSumColoring 4 F) :
    ∑ x, (F x).card ≤ 4 := by
  have h0 : ∀ c ∈ F (0 : ZMod 4), ∀ d ∈ F 0, c = d := by
    exact hF 0 0 ⟨0, by norm_num⟩
  have h2 : ∀ c ∈ F (2 : ZMod 4), ∀ d ∈ F 2, c = d := by
    exact hF 2 2 ⟨0, by decide⟩
  have h01 : ∀ c ∈ F (0 : ZMod 4), ∀ d ∈ F 1, c = d := by
    exact hF 0 1 ⟨1, by norm_num⟩
  have h13 : ∀ c ∈ F (1 : ZMod 4), ∀ d ∈ F 3, c = d := by
    exact hF 1 3 ⟨0, by decide⟩
  have h23 : ∀ c ∈ F (2 : ZMod 4), ∀ d ∈ F 3, c = d := by
    exact hF 2 3 ⟨1, by decide⟩
  have h := four_fibers_card_le h0 h2 h01 h13 h23
  calc
    ∑ x : ZMod 4, (F x).card =
        ∑ i : Fin 4, (F (ZMod.finEquiv 4 i)).card :=
      ((ZMod.finEquiv 4).toEquiv.sum_comp (fun x ↦ (F x).card)).symm
    _ = (F 0).card + (F 1).card + (F 2).card + (F 3).card := by
      rw [Fin.sum_univ_four]
      rfl
    _ ≤ 4 := h

lemma los_eight_weight_linear_bound
    (m w0 w1 w2 w3 w4 w5 w6 w7 : ℕ)
    (h01 : w0 = 0 ∨ w1 = 0 ∨ (w0 ≤ m ∧ w1 ≤ m))
    (h27 : w2 = 0 ∨ w7 = 0 ∨ (w2 ≤ m ∧ w7 ≤ m))
    (h36 : w3 = 0 ∨ w6 = 0 ∨ (w3 ≤ m ∧ w6 ≤ m))
    (h45 : w4 = 0 ∨ w5 = 0 ∨ (w4 ≤ m ∧ w5 ≤ m))
    (h04 : 16 * (w0 + w4) ≤ 33 * m)
    (h17 : w1 + w7 ≤ 3 * m)
    (h35 : w3 + w5 ≤ 3 * m)
    (h13 : w1 + w3 ≤ 3 * m)
    (h57 : w5 + w7 ≤ 3 * m)
    (h6 : 2 * w6 ≤ 3 * m)
    (h26 : 2 * w2 + w6 ≤ 3 * m) :
    4 * (w0 + w1 + w2 + w3 + w4 + w5 + w6 + w7) ≤ 33 * m := by
  rcases h01 with h01 | h01 | h01 <;>
    rcases h27 with h27 | h27 | h27 <;>
      rcases h36 with h36 | h36 | h36 <;>
        rcases h45 with h45 | h45 | h45 <;>
          omega

/-! ## The eight residue fibres -/

/-- Mixed-radix enumeration, with the residue modulo eight as the low digit. -/
noncomputable def blockEquiv (m : ℕ) [NeZero m] :
    ZMod m × Fin 8 ≃ ZMod (m * 8) :=
  ((ZMod.finEquiv m).symm.toEquiv.prodCongr (Equiv.refl (Fin 8))).trans <|
    finProdFinEquiv.trans (ZMod.finEquiv (m * 8)).toEquiv

noncomputable def blockPoint (m : ℕ) [NeZero m] (r : Fin 8) (t : ZMod m) :
    ZMod (m * 8) :=
  blockEquiv m (t, r)

lemma val_finEquiv (n : ℕ) [NeZero n] (i : Fin n) :
    (ZMod.finEquiv n i).val = i.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

lemma val_finEquiv_symm (n : ℕ) [NeZero n] (x : ZMod n) :
    ((ZMod.finEquiv n).symm x).val = x.val := by
  have h := val_finEquiv n ((ZMod.finEquiv n).symm x)
  simpa using h.symm

lemma blockPoint_val (m : ℕ) [NeZero m] (r : Fin 8) (t : ZMod m) :
    (blockPoint m r t).val = r.val + 8 * t.val := by
  simp [blockPoint, blockEquiv, finProdFinEquiv, val_finEquiv,
    val_finEquiv_symm]

lemma blockPoint_eq (m : ℕ) [NeZero m] (r : Fin 8) (t : ZMod m) :
    blockPoint m r t = (r.val + 8 * t.val : ℕ) := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
      have hval : (blockPoint (m + 1) r t).val = r.val + 8 * t.val := by
        exact blockPoint_val _ _ _
      calc
        blockPoint (m + 1) r t =
            ((blockPoint (m + 1) r t).val : ZMod ((m + 1) * 8)) :=
          (ZMod.natCast_zmod_val _).symm
        _ = (r.val + 8 * t.val : ℕ) := by rw [hval]

noncomputable def blockWeight (m : ℕ) [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3)) (r : Fin 8) : ℕ :=
  ∑ t : ZMod m, (F (blockPoint m r t)).card

lemma sum_blockWeight (m : ℕ) [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3)) :
    ∑ r : Fin 8, blockWeight m F r = ∑ x, (F x).card := by
  change ∑ r : Fin 8, ∑ t : ZMod m, (F (blockPoint m r t)).card = _
  rw [Finset.sum_comm]
  simpa only [Fintype.sum_prod_type, blockPoint] using
    (blockEquiv m).sum_comp (fun x ↦ (F x).card)

lemma blockWeight_le (m : ℕ) [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3)) (r : Fin 8) :
    blockWeight m F r ≤ 3 * m := by
  change (∑ t : ZMod m, (F (blockPoint m r t)).card) ≤ _
  calc
    ∑ t : ZMod m, (F (blockPoint m r t)).card ≤ ∑ _t : ZMod m, 3 := by
      gcongr with t
      exact fin3_card_le _
    _ = 3 * m := by simp [ZMod.card, mul_comm]

/-- The low base-eight digit gives an equivalence with each residue fibre. -/
noncomputable def residueEquiv (m : ℕ) [NeZero m] (r : Fin 8) :
    ZMod m ≃ {x : ZMod (m * 8) // x.val % 8 = r.val} where
  toFun t := ⟨blockPoint m r t, by simp [blockPoint_val]⟩
  invFun x := ((blockEquiv m).symm x.1).1
  left_inv t := by
    change ((blockEquiv m).symm (blockEquiv m (t, r))).1 = t
    simp
  right_inv x := by
    let p := (blockEquiv m).symm x.1
    have hpval : p.2.val = r.val := by
      have hval := blockPoint_val m p.2 p.1
      have happ : blockPoint m p.2 p.1 = x.1 := by
        exact (blockEquiv m).apply_symm_apply x.1
      rw [happ] at hval
      have hx := x.2
      rw [hval, Nat.add_mod, Nat.mul_mod] at hx
      simpa [Nat.mod_eq_of_lt p.2.isLt] using hx
    have hp : p.2 = r := Fin.ext hpval
    apply Subtype.ext
    change blockEquiv m (p.1, r) = x.1
    rw [show (p.1, r) = p by ext <;> simp [hp]]
    exact (blockEquiv m).apply_symm_apply x.1

def residueFinset (n : ℕ) [NeZero n] (r : Fin 8) : Finset (ZMod n) :=
  Finset.univ.filter fun x ↦ x.val % 8 = r.val

noncomputable def residueWeight (n : ℕ) [NeZero n] (F : ZMod n → Finset (Fin 3))
    (r : Fin 8) : ℕ :=
  ∑ x ∈ residueFinset n r, (F x).card

lemma residueFinset_card (m : ℕ) [NeZero m] (r : Fin 8) :
    (residueFinset (m * 8) r).card = m := by
  rw [residueFinset, ← Fintype.card_subtype]
  simpa [ZMod.card] using (Fintype.card_congr (residueEquiv m r)).symm

lemma residueWeight_eq_blockWeight (m : ℕ) [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3)) (r : Fin 8) :
    residueWeight (m * 8) F r = blockWeight m F r := by
  rw [residueWeight, residueFinset]
  rw [← Finset.sum_subtype_eq_sum_filter]
  rw [show Finset.subtype (fun x : ZMod (m * 8) ↦ x.val % 8 = r.val) Finset.univ =
      Finset.univ by ext; simp]
  simpa only [blockWeight, residueEquiv, Equiv.coe_fn_mk] using
    ((residueEquiv m r).sum_comp (fun x ↦ (F x.1).card)).symm

lemma sum_residueWeight (m : ℕ) [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3)) :
    ∑ r : Fin 8, residueWeight (m * 8) F r = ∑ x, (F x).card := by
  simp_rw [residueWeight_eq_blockWeight]
  exact sum_blockWeight m F

lemma mem_residueFinset_iff_cast {n : ℕ} [NeZero n] {r : Fin 8} {x : ZMod n} :
    x ∈ residueFinset n r ↔ (x.cast : ZMod 8) = (r.val : ℕ) := by
  rw [residueFinset, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, ZMod.cast_eq_val,
    ZMod.natCast_eq_natCast_iff']
  rw [Nat.mod_eq_of_lt r.isLt]

lemma isSquare_of_cast_eight_eq_one {j : ℕ} (hj : 3 ≤ j) (x : ZMod (2 ^ j))
    (hx : (x.cast : ZMod 8) = 1) : IsSquare x := by
  have hmod : x.val % 8 = 1 := by
    have := hx
    rw [ZMod.cast_eq_val, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at this
    simpa using this
  have hs := isSquare_zmod_two_pow_of_mod_eight_eq_one hj hmod
  simpa only [ZMod.natCast_zmod_val] using hs

lemma isSquare_of_cast_eight_eq_one_of_eq {n j : ℕ} [NeZero n]
    (hn : n = 2 ^ j) (hj : 3 ≤ j) (x : ZMod n)
    (hx : (x.cast : ZMod 8) = 1) : IsSquare x := by
  subst n
  exact isSquare_of_cast_eight_eq_one hj x hx

lemma isSquare_add_of_residues_one {j : ℕ} (hj : 3 ≤ j)
    {r s : Fin 8} (hrs : ((r.val : ZMod 8) + s.val) = 1)
    {x y : ZMod (2 ^ j)} (hx : x ∈ residueFinset (2 ^ j) r)
    (hy : y ∈ residueFinset (2 ^ j) s) : IsSquare (x + y) := by
  apply isSquare_of_cast_eight_eq_one hj
  rw [ZMod.cast_add (by exact pow_dvd_pow 2 hj) x y,
    (mem_residueFinset_iff_cast.mp hx), (mem_residueFinset_iff_cast.mp hy), hrs]

lemma residue_cross_alternative (k : ℕ) [NeZero k]
    (F : ZMod (k * 8) → Finset (Fin 3)) (hF : SquareSumColoring (k * 8) F)
    (r s : Fin 8)
    (hsq : ∀ {x y : ZMod (k * 8)}, x ∈ residueFinset (k * 8) r →
      y ∈ residueFinset (k * 8) s → IsSquare (x + y)) :
    residueWeight (k * 8) F r = 0 ∨ residueWeight (k * 8) F s = 0 ∨
      (residueWeight (k * 8) F r ≤ k ∧ residueWeight (k * 8) F s ≤ k) := by
  by_cases hr0 : residueWeight (k * 8) F r = 0
  · exact Or.inl hr0
  by_cases hs0 : residueWeight (k * 8) F s = 0
  · exact Or.inr (Or.inl hs0)
  right; right
  have getWitness (q : Fin 8) (hq0 : residueWeight (k * 8) F q ≠ 0) :
      ∃ x ∈ residueFinset (k * 8) q, (F x).Nonempty := by
    rw [residueWeight] at hq0
    obtain ⟨x, hx, hcard⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq0
    exact ⟨x, hx, Finset.card_ne_zero.mp hcard⟩
  obtain ⟨xr, hxr, cr, hcr⟩ := getWitness r hr0
  obtain ⟨xs, hxs, cs, hcs⟩ := getWitness s hs0
  constructor
  · rw [residueWeight]
    calc
      ∑ x ∈ residueFinset (k * 8) r, (F x).card ≤
          ∑ _x ∈ residueFinset (k * 8) r, 1 := by
        gcongr with x hx
        rw [Finset.card_le_one]
        intro c hc d hd
        exact (hF x xs (hsq hx hxs) c hc cs hcs).trans
          (hF x xs (hsq hx hxs) d hd cs hcs).symm
      _ = k := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact residueFinset_card k r
  · rw [residueWeight]
    calc
      ∑ x ∈ residueFinset (k * 8) s, (F x).card ≤
          ∑ _x ∈ residueFinset (k * 8) s, 1 := by
        gcongr with x hx
        rw [Finset.card_le_one]
        intro c hc d hd
        exact (hF xr x (hsq hxr hx) cr hcr c hc).symm.trans
          (hF xr x (hsq hxr hx) cr hcr d hd)
      _ = k := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact residueFinset_card k s

lemma residueWeight_pair_le (k : ℕ) [NeZero k]
    (F : ZMod (k * 8) → Finset (Fin 3)) (hF : SquareSumColoring (k * 8) F)
    (r s : Fin 8) (e : ZMod (k * 8) ≃ ZMod (k * 8))
    (he : ∀ {x}, x ∈ residueFinset (k * 8) r → e x ∈ residueFinset (k * 8) s)
    (he' : ∀ {y}, y ∈ residueFinset (k * 8) s → e.symm y ∈ residueFinset (k * 8) r)
    (hsq : ∀ {x}, x ∈ residueFinset (k * 8) r → IsSquare (x + e x)) :
    residueWeight (k * 8) F r + residueWeight (k * 8) F s ≤ 3 * k := by
  have hsum :
      (∑ x ∈ residueFinset (k * 8) r, (F (e x)).card) =
        ∑ y ∈ residueFinset (k * 8) s, (F y).card := by
    apply Finset.sum_bij (fun x _hx ↦ e x)
    · intro x hx
      exact he hx
    · intro x₁ _ x₂ _ h
      exact e.injective h
    · intro y hy
      refine ⟨e.symm y, he' hy, e.apply_symm_apply y⟩
    · intro x hx
      rfl
  rw [residueWeight, residueWeight, ← hsum, ← Finset.sum_add_distrib,
    ]
  calc
    ∑ x ∈ residueFinset (k * 8) r, ((F x).card + (F (e x)).card) ≤
        ∑ _x ∈ residueFinset (k * 8) r, 3 := by
      gcongr with x hx
      apply card_add_card_le_three_of_cross_eq
      exact hF x (e x) (hsq hx)
    _ = 3 * k := by
      simp [residueFinset_card k r, mul_comm]

lemma residueWeight_sub_pair_le (k : ℕ) [NeZero k]
    (F : ZMod (k * 8) → Finset (Fin 3)) (hF : SquareSumColoring (k * 8) F)
    (c : ℕ) (r s : Fin 8)
    (hrs : (c : ZMod 8) - r.val = s.val)
    (hsr : (c : ZMod 8) - s.val = r.val)
    (hc : IsSquare (c : ZMod (k * 8))) :
    residueWeight (k * 8) F r + residueWeight (k * 8) F s ≤ 3 * k := by
  let e : ZMod (k * 8) ≃ ZMod (k * 8) := Equiv.subLeft (c : ZMod (k * 8))
  apply residueWeight_pair_le k F hF r s e
  · intro x hx
    apply mem_residueFinset_iff_cast.mpr
    change (((c : ZMod (k * 8)) - x).cast : ZMod 8) = _
    rw [ZMod.cast_sub (by simp) (c : ZMod (k * 8)) x,
      mem_residueFinset_iff_cast.mp hx]
    simpa using hrs
  · intro y hy
    apply mem_residueFinset_iff_cast.mpr
    have heq : e.symm y = (c : ZMod (k * 8)) - y := by
      apply e.injective
      simp [e, Equiv.subLeft_apply]
    rw [heq]
    change (((c : ZMod (k * 8)) - y).cast : ZMod 8) = _
    rw [ZMod.cast_sub (by simp) (c : ZMod (k * 8)) y,
      mem_residueFinset_iff_cast.mp hy]
    simpa using hsr
  · intro x _hx
    change IsSquare (x + ((c : ZMod (k * 8)) - x))
    simpa [add_sub_cancel_left] using hc

lemma square_add_of_block_residues_one (k : ℕ) {r s : Fin 8}
    (hrs : (r.val : ZMod 8) + s.val = 1)
    {x y : ZMod ((2 ^ k) * 8)} (hx : x ∈ residueFinset ((2 ^ k) * 8) r)
    (hy : y ∈ residueFinset ((2 ^ k) * 8) s) : IsSquare (x + y) := by
  apply isSquare_of_cast_eight_eq_one_of_eq
      (show (2 ^ k) * 8 = 2 ^ (k + 3) by ring) (by omega)
  rw [ZMod.cast_add (by simp) x y, mem_residueFinset_iff_cast.mp hx,
    mem_residueFinset_iff_cast.mp hy, hrs]

lemma block_cross_alternative (k : ℕ)
    (F : ZMod ((2 ^ k) * 8) → Finset (Fin 3))
    (hF : SquareSumColoring ((2 ^ k) * 8) F) (r s : Fin 8)
    (hrs : (r.val : ZMod 8) + s.val = 1) :
    residueWeight ((2 ^ k) * 8) F r = 0 ∨ residueWeight ((2 ^ k) * 8) F s = 0 ∨
      (residueWeight ((2 ^ k) * 8) F r ≤ 2 ^ k ∧
        residueWeight ((2 ^ k) * 8) F s ≤ 2 ^ k) := by
  apply residue_cross_alternative (2 ^ k) F hF r s
  intro x y hx hy
  exact square_add_of_block_residues_one k hrs hx hy

lemma block_sub_pair_le (k : ℕ)
    (F : ZMod ((2 ^ k) * 8) → Finset (Fin 3))
    (hF : SquareSumColoring ((2 ^ k) * 8) F) (c : ℕ) (r s : Fin 8)
    (hrs : (c : ZMod 8) - r.val = s.val)
    (hsr : (c : ZMod 8) - s.val = r.val)
    (hc : IsSquare (c : ZMod ((2 ^ k) * 8))) :
    residueWeight ((2 ^ k) * 8) F r + residueWeight ((2 ^ k) * 8) F s ≤
      3 * 2 ^ k := by
  exact residueWeight_sub_pair_le (2 ^ k) F hF c r s hrs hsr hc

/-! ## The induction on multiples of four -/

noncomputable def quarterPull (m : ℕ) (F : ZMod (m * 8) → Finset (Fin 3))
    (x : ZMod (m * 2)) : Finset (Fin 3) :=
  F ((4 * x.val : ℕ) : ZMod (m * 8))

lemma four_mul_modEq_eight_mul_of_modEq_two_mul {m a b : ℕ}
    (h : a ≡ b [MOD m * 2]) : 4 * a ≡ 4 * b [MOD m * 8] := by
  rw [Nat.modEq_iff_dvd] at h ⊢
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  push_cast at ht ⊢
  calc
    4 * (b : ℤ) - 4 * (a : ℤ) = 4 * ((b : ℤ) - (a : ℤ)) := by ring
    _ = 4 * ((m : ℤ) * 2 * t) := by rw [ht]
    _ = (m : ℤ) * 8 * t := by ring

lemma isSquare_quarterLift {m : ℕ} [NeZero m] {x y : ZMod (m * 2)}
    (h : IsSquare (x + y)) :
    IsSquare (((4 * x.val : ℕ) : ZMod (m * 8)) +
      ((4 * y.val : ℕ) : ZMod (m * 8))) := by
  rcases h with ⟨z, hz⟩
  refine ⟨((2 * z.val : ℕ) : ZMod (m * 8)), ?_⟩
  have hz' : ((x.val + y.val : ℕ) : ZMod (m * 2)) =
      ((z.val * z.val : ℕ) : ZMod (m * 2)) := by
    rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y,
      ← ZMod.natCast_zmod_val z]
    simpa [pow_two] using hz
  have hmod : x.val + y.val ≡ z.val * z.val [MOD m * 2] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hz'
  have hmod4 := four_mul_modEq_eight_mul_of_modEq_two_mul hmod
  have hc : ((4 * (x.val + y.val) : ℕ) : ZMod (m * 8)) =
      ((4 * (z.val * z.val) : ℕ) : ZMod (m * 8)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod4
  calc
    ((4 * x.val : ℕ) : ZMod (m * 8)) + ((4 * y.val : ℕ) : ZMod (m * 8)) =
        ((4 * (x.val + y.val) : ℕ) : ZMod (m * 8)) := by push_cast; ring
    _ = ((4 * (z.val * z.val) : ℕ) : ZMod (m * 8)) := hc
    _ = ((2 * z.val : ℕ) : ZMod (m * 8)) *
        ((2 * z.val : ℕ) : ZMod (m * 8)) := by push_cast; ring

lemma squareSumColoring_quarterPull {m : ℕ} [NeZero m]
    {F : ZMod (m * 8) → Finset (Fin 3)}
    (hF : SquareSumColoring (m * 8) F) :
    SquareSumColoring (m * 2) (quarterPull m F) := by
  intro x y hxy c hc d hd
  exact hF _ _ (isSquare_quarterLift hxy) c hc d hd

noncomputable def halfBlockEquiv (m : ℕ) [NeZero m] :
    ZMod m × Fin 2 ≃ ZMod (m * 2) :=
  ((ZMod.finEquiv m).symm.toEquiv.prodCongr (Equiv.refl (Fin 2))).trans <|
    finProdFinEquiv.trans (ZMod.finEquiv (m * 2)).toEquiv

noncomputable def halfBlockPoint (m : ℕ) [NeZero m] (r : Fin 2) (t : ZMod m) :
    ZMod (m * 2) := halfBlockEquiv m (t, r)

lemma halfBlockPoint_val (m : ℕ) [NeZero m] (r : Fin 2) (t : ZMod m) :
    (halfBlockPoint m r t).val = r.val + 2 * t.val := by
  simp [halfBlockPoint, halfBlockEquiv, finProdFinEquiv, val_finEquiv,
    val_finEquiv_symm]

lemma quarterPull_halfBlockPoint_zero (m : ℕ) [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3)) (t : ZMod m) :
    quarterPull m F (halfBlockPoint m 0 t) = F (blockPoint m 0 t) := by
  unfold quarterPull
  apply congrArg F
  rw [halfBlockPoint_val, blockPoint_eq]
  norm_num
  ring

lemma quarterPull_halfBlockPoint_one (m : ℕ) [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3)) (t : ZMod m) :
    quarterPull m F (halfBlockPoint m 1 t) = F (blockPoint m 4 t) := by
  unfold quarterPull
  apply congrArg F
  rw [halfBlockPoint_val, blockPoint_eq]
  norm_num
  ring

lemma sum_quarterPull_eq_blockWeights (m : ℕ) [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3)) :
    (∑ x : ZMod (m * 2), (quarterPull m F x).card) =
      blockWeight m F 0 + blockWeight m F 4 := by
  rw [blockWeight, blockWeight]
  calc
    ∑ x : ZMod (m * 2), (quarterPull m F x).card =
        ∑ p : ZMod m × Fin 2,
          (quarterPull m F (halfBlockEquiv m p)).card := by
            exact ((halfBlockEquiv m).sum_comp
              (fun x ↦ (quarterPull m F x).card)).symm
    _ = ∑ t : ZMod m, ∑ r : Fin 2,
          (quarterPull m F (halfBlockPoint m r t)).card := by
            rw [Fintype.sum_prod_type]
            rfl
    _ = ∑ t : ZMod m,
          ((quarterPull m F (halfBlockPoint m 0 t)).card +
            (quarterPull m F (halfBlockPoint m 1 t)).card) := by
            simp_rw [Fin.sum_univ_two]
    _ = (∑ t : ZMod m, (F (blockPoint m 0 t)).card) +
          ∑ t : ZMod m, (F (blockPoint m 4 t)).card := by
            simp_rw [quarterPull_halfBlockPoint_zero,
              quarterPull_halfBlockPoint_one]
            exact Finset.sum_add_distrib

lemma sum_quarterPull_eq_residueWeights (m : ℕ) [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3)) :
    (∑ x : ZMod (m * 2), (quarterPull m F x).card) =
      residueWeight (m * 8) F 0 + residueWeight (m * 8) F 4 := by
  rw [residueWeight_eq_blockWeight m F 0,
    residueWeight_eq_blockWeight m F 4]
  exact sum_quarterPull_eq_blockWeights m F

lemma quarterPull_residue_bound {m : ℕ} [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3))
    (h : 32 * (∑ x : ZMod (m * 2), (quarterPull m F x).card) ≤
      33 * (m * 2)) :
    16 * (residueWeight (m * 8) F 0 + residueWeight (m * 8) F 4) ≤
      33 * m := by
  rw [sum_quarterPull_eq_residueWeights] at h
  omega

/-! ## The `R_2/R_6` triangle gadget -/

lemma isSquare_of_cast_thirtytwo_eq_four {j : ℕ} (hj : 3 ≤ j)
    (x : ZMod (2 ^ j)) (hx : (x.cast : ZMod 32) = 4) : IsSquare x := by
  have hmod : x.val % 32 = 4 := by
    have h := hx
    rw [ZMod.cast_eq_val] at h
    change (x.val : ZMod 32) = (4 : ZMod 32) at h
    have hm := (ZMod.natCast_eq_natCast_iff' x.val 4 32).mp h
    norm_num at hm
    exact hm
  let q := x.val / 32
  have hval : x.val = 4 * (1 + 8 * q) := by
    have hdecomp := Nat.mod_add_div x.val 32
    dsimp [q]
    omega
  obtain ⟨r, hr⟩ :=
    isSquare_zmod_two_pow_of_mod_eight_eq_one hj
      (a := 1 + 8 * q) (by simp)
  refine ⟨2 * r, ?_⟩
  rw [← ZMod.natCast_zmod_val x, hval]
  push_cast
  norm_num [Nat.cast_add, Nat.cast_mul] at hr
  rw [hr]
  ring

def zmodSixteen (n : ℕ) : ZMod n := (16 : ℕ)

noncomputable def triangleEquiv (n : ℕ) (h16 : 16 ∣ n) : Equiv.Perm (ZMod n) where
  toFun x := if (x.cast : ZMod 16) = 2 then x else x + zmodSixteen n
  invFun x := if (x.cast : ZMod 16) = 2 then x else x - zmodSixteen n
  left_inv x := by
    have hz : ((16 : ℕ) : ZMod 16) = 0 := CharP.cast_eq_zero (ZMod 16) 16
    have hadd : ((x + zmodSixteen n).cast : ZMod 16) = x.cast := by
      rw [ZMod.cast_add h16]
      change x.cast + (((16 : ℕ) : ZMod n).cast : ZMod 16) = x.cast
      rw [ZMod.cast_natCast h16, hz, add_zero]
    by_cases hx : (x.cast : ZMod 16) = 2
    · simp [hx]
    · have hx' : ((x + zmodSixteen n).cast : ZMod 16) ≠ 2 := by rw [hadd]; exact hx
      simp [hx, hx']
  right_inv x := by
    have hz : ((16 : ℕ) : ZMod 16) = 0 := CharP.cast_eq_zero (ZMod 16) 16
    have hsub : ((x - zmodSixteen n).cast : ZMod 16) = x.cast := by
      rw [ZMod.cast_sub h16]
      change x.cast - (((16 : ℕ) : ZMod n).cast : ZMod 16) = x.cast
      rw [ZMod.cast_natCast h16, hz, sub_zero]
    by_cases hx : (x.cast : ZMod 16) = 2
    · simp [hx]
    · have hx' : ((x - zmodSixteen n).cast : ZMod 16) ≠ 2 := by rw [hsub]; exact hx
      simp [hx, hx']

lemma isSquare_of_cast_thirtytwo_eq_four_of_eq {n j : ℕ} [NeZero n]
    (hn : n = 2 ^ j) (hj : 3 ≤ j) (x : ZMod n)
    (hx : (x.cast : ZMod 32) = 4) : IsSquare x := by
  subst n
  exact isSquare_of_cast_thirtytwo_eq_four hj x hx

lemma sixteen_dvd_two_pow_add_five (a : ℕ) : 16 ∣ 2 ^ (a + 5) := by
  refine ⟨2 ^ (a + 1), ?_⟩
  rw [show a + 5 = 4 + (a + 1) by omega, pow_add]
  norm_num

lemma thirtytwo_dvd_two_pow_add_five (a : ℕ) : 32 ∣ 2 ^ (a + 5) := by
  refine ⟨2 ^ a, ?_⟩
  rw [show a + 5 = 5 + a by omega, pow_add]
  norm_num

lemma isSquare_add_triangleEquiv (a : ℕ) (x : ZMod (2 ^ (a + 5)))
    (hx : x ∈ residueFinset (2 ^ (a + 5)) (2 : Fin 8)) :
    IsSquare (x + triangleEquiv (2 ^ (a + 5))
      (sixteen_dvd_two_pow_add_five a) x) := by
  have h32 : 32 ∣ 2 ^ (a + 5) := thirtytwo_dvd_two_pow_add_five a
  have hx8 : x.val % 8 = 2 := by simpa [residueFinset] using hx
  apply isSquare_of_cast_thirtytwo_eq_four (by omega)
  simp only [triangleEquiv, Equiv.coe_fn_mk]
  by_cases hx16 : (x.cast : ZMod 16) = 2
  · rw [if_pos hx16, ZMod.cast_add h32]
    simp only [ZMod.cast_eq_val]
    change (x.val : ZMod 32) + x.val = (4 : ZMod 32)
    rw [← Nat.cast_add]
    apply (ZMod.natCast_eq_natCast_iff' (x.val + x.val) 4 32).2
    have hx16mod : x.val % 16 = 2 := by
      rw [ZMod.cast_eq_val] at hx16
      change (x.val : ZMod 16) = ((2 : ℕ) : ZMod 16) at hx16
      exact (ZMod.natCast_eq_natCast_iff' x.val 2 16).mp hx16
    have hdecomp := Nat.mod_add_div x.val 16
    omega
  · rw [if_neg hx16, ZMod.cast_add h32, ZMod.cast_add h32]
    change (x.cast : ZMod 32) +
      (x.cast + (((16 : ℕ) : ZMod (2 ^ (a + 5))).cast : ZMod 32)) = 4
    rw [ZMod.cast_natCast h32]
    simp only [ZMod.cast_eq_val]
    rw [← add_assoc, ← Nat.cast_add, ← Nat.cast_add]
    apply (ZMod.natCast_eq_natCast_iff' (x.val + x.val + 16) 4 32).2
    have hx16mod : x.val % 16 ≠ 2 := by
      intro h
      apply hx16
      rw [ZMod.cast_eq_val]
      apply (ZMod.natCast_eq_natCast_iff' x.val 2 16).2
      simpa using h
    have hdecomp8 := Nat.mod_add_div x.val 8
    have hdecomp16 := Nat.mod_add_div x.val 16
    omega

lemma triangle_cross_relations (a : ℕ)
    (F : ZMod (2 ^ (a + 5)) → Finset (Fin 3))
    (hF : SquareSumColoring (2 ^ (a + 5)) F)
    (x : ZMod (2 ^ (a + 5)))
    (hx : x ∈ residueFinset (2 ^ (a + 5)) (2 : Fin 8)) :
    (∀ c ∈ F x, ∀ d ∈ F (triangleEquiv (2 ^ (a + 5))
      (sixteen_dvd_two_pow_add_five a) x), c = d) ∧
    (∀ c ∈ F x, ∀ d ∈ F (-x), c = d) ∧
    (∀ c ∈ F (triangleEquiv (2 ^ (a + 5))
      (sixteen_dvd_two_pow_add_five a) x), ∀ d ∈ F (-x), c = d) := by
  let h16 : 16 ∣ 2 ^ (a + 5) := sixteen_dvd_two_pow_add_five a
  let e := triangleEquiv (2 ^ (a + 5)) h16
  have heq : triangleEquiv (2 ^ (a + 5)) (sixteen_dvd_two_pow_add_five a) = e := by
    simp [e, h16]
  rw [heq]
  constructor
  · exact hF x (e x) (by simpa [e, h16] using isSquare_add_triangleEquiv a x hx)
  constructor
  · apply hF x (-x)
    simpa using (IsSquare.zero : IsSquare (0 : ZMod (2 ^ (a + 5))))
  · apply hF (e x) (-x)
    simp only [e, triangleEquiv, Equiv.coe_fn_mk]
    by_cases hx16 : (x.cast : ZMod 16) = 2
    · rw [if_pos hx16]
      simpa using (IsSquare.zero : IsSquare (0 : ZMod (2 ^ (a + 5))))
    · rw [if_neg hx16]
      refine ⟨4, ?_⟩
      simp [zmodSixteen]
      norm_num

lemma two_six_triangle_bound (a : ℕ)
    (F : ZMod (2 ^ (a + 5)) → Finset (Fin 3))
    (hF : SquareSumColoring (2 ^ (a + 5)) F) :
    2 * residueWeight (2 ^ (a + 5)) F (2 : Fin 8) +
        residueWeight (2 ^ (a + 5)) F (6 : Fin 8) ≤ 3 * (4 * 2 ^ a) := by
  let e := triangleEquiv (2 ^ (a + 5)) (sixteen_dvd_two_pow_add_five a)
  have h8 : 8 ∣ 2 ^ (a + 5) := dvd_trans (by norm_num : 8 ∣ 16)
    (sixteen_dvd_two_pow_add_five a)
  have he : ∀ x : ZMod (2 ^ (a + 5)),
      x ∈ residueFinset (2 ^ (a + 5)) (2 : Fin 8) ↔
        e x ∈ residueFinset (2 ^ (a + 5)) (2 : Fin 8) := by
    intro x
    rw [mem_residueFinset_iff_cast, mem_residueFinset_iff_cast]
    by_cases hx : (x.cast : ZMod 16) = 2
    · simp [e, triangleEquiv, hx]
    · simp only [e, triangleEquiv, Equiv.coe_fn_mk, if_neg hx]
      rw [ZMod.cast_add h8]
      change (x.cast : ZMod 8) = 2 ↔
        x.cast + (((16 : ℕ) : ZMod (2 ^ (a + 5))).cast : ZMod 8) = 2
      rw [ZMod.cast_natCast h8]
      have hz : ((16 : ℕ) : ZMod 8) = 0 := CharP.cast_eq_zero (ZMod 8) 8
      rw [hz, add_zero]
  have hneg : ∀ x : ZMod (2 ^ (a + 5)),
      x ∈ residueFinset (2 ^ (a + 5)) (2 : Fin 8) ↔
        -x ∈ residueFinset (2 ^ (a + 5)) (6 : Fin 8) := by
    intro x
    rw [mem_residueFinset_iff_cast, mem_residueFinset_iff_cast, ZMod.cast_neg h8]
    constructor <;> intro hx
    · rw [hx]; decide
    · calc
        (x.cast : ZMod 8) = -(-(x.cast : ZMod 8)) := by simp
        _ = -(6 : ZMod 8) := congrArg Neg.neg hx
        _ = 2 := by decide
  have hsumE := Finset.sum_equiv e he
      (f := fun x ↦ (F (e x)).card) (g := fun x ↦ (F x).card) (by simp)
  have hsumNeg := Finset.sum_equiv (Equiv.neg (ZMod (2 ^ (a + 5)))) hneg
      (f := fun x ↦ (F (-x)).card) (g := fun x ↦ (F x).card) (by simp)
  rw [residueWeight, residueWeight]
  calc
    2 * (∑ x ∈ residueFinset (2 ^ (a + 5)) (2 : Fin 8), (F x).card) +
        ∑ x ∈ residueFinset (2 ^ (a + 5)) (6 : Fin 8), (F x).card =
      ∑ x ∈ residueFinset (2 ^ (a + 5)) (2 : Fin 8),
        ((F x).card + (F (e x)).card + (F (-x)).card) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumE, hsumNeg]
          omega
    _ ≤ ∑ _x ∈ residueFinset (2 ^ (a + 5)) (2 : Fin 8), 3 := by
      gcongr with x hx
      exact card_three_le_three_of_pairwise_cross_eq
        (triangle_cross_relations a F hF x hx).1
        (triangle_cross_relations a F hF x hx).2.1
        (triangle_cross_relations a F hF x hx).2.2
    _ = 3 * (4 * 2 ^ a) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : (residueFinset (2 ^ (a + 5)) (2 : Fin 8)).card = 4 * 2 ^ a := by
        have hn : 2 ^ (a + 5) = 2 ^ (a + 2) * 8 := by
          rw [show a + 5 = (a + 2) + 3 by omega, pow_add]
          norm_num
        have hcard : ∀ {n m : ℕ} [NeZero n] [NeZero m], n = m * 8 →
            (residueFinset n (2 : Fin 8)).card = m := by
          intro n m hnI hmI hEq
          subst n
          exact residueFinset_card m (2 : Fin 8)
        calc
          (residueFinset (2 ^ (a + 5)) (2 : Fin 8)).card = 2 ^ (a + 2) :=
            hcard hn
          _ = 4 * 2 ^ a := by rw [pow_add]; norm_num [mul_comm]
      rw [hc]
      simp [mul_comm]

/-- For the two small eight-blocks, the identity supplies the middle vertex
of the `R₂/R₆` triangle gadget. -/
lemma two_six_bound_of_self_square (m : ℕ) [NeZero m]
    (F : ZMod (m * 8) → Finset (Fin 3))
    (hF : SquareSumColoring (m * 8) F)
    (hself : ∀ x ∈ residueFinset (m * 8) (2 : Fin 8), IsSquare (x + x)) :
    2 * residueWeight (m * 8) F (2 : Fin 8) +
        residueWeight (m * 8) F (6 : Fin 8) ≤ 3 * m := by
  let R2 := residueFinset (m * 8) (2 : Fin 8)
  let R6 := residueFinset (m * 8) (6 : Fin 8)
  have h8 : 8 ∣ m * 8 := dvd_mul_left 8 m
  have hneg : ∀ x, x ∈ R2 ↔ -x ∈ R6 := by
    intro x
    rw [mem_residueFinset_iff_cast, mem_residueFinset_iff_cast, ZMod.cast_neg h8]
    constructor
    · intro hx
      rw [hx]
      decide
    · intro hx
      calc
        (x.cast : ZMod 8) = -(-(x.cast : ZMod 8)) := by simp
        _ = -(6 : ZMod 8) := congrArg Neg.neg hx
        _ = 2 := by decide
  have hsumNeg : (∑ x ∈ R2, (F (-x)).card) = ∑ x ∈ R6, (F x).card := by
    simpa using Finset.sum_equiv (Equiv.neg (ZMod (m * 8))) hneg
      (f := fun x ↦ (F (-x)).card) (g := fun x ↦ (F x).card) (by simp)
  rw [residueWeight, residueWeight, two_mul]
  change (∑ x ∈ R2, (F x).card) + (∑ x ∈ R2, (F x).card) +
      (∑ x ∈ R6, (F x).card) ≤ _
  rw [← hsumNeg, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    ∑ x ∈ R2, ((F x).card + (F x).card + (F (-x)).card) ≤
        ∑ _x ∈ R2, 3 := by
      gcongr with x hx
      apply card_three_le_three_of_pairwise_cross_eq
      · exact hF x x (hself x (by simpa [R2] using hx))
      · apply hF x (-x)
        simpa using (IsSquare.zero : IsSquare (0 : ZMod (m * 8)))
      · apply hF x (-x)
        simpa using (IsSquare.zero : IsSquare (0 : ZMod (m * 8)))
    _ = 3 * m := by simp [R2, residueFinset_card, mul_comm]

lemma r2_self_square_eight (x : ZMod 8)
    (hx : x ∈ residueFinset 8 (2 : Fin 8)) : IsSquare (x + x) := by
  have hxmod : x.val % 8 = 2 := by simpa [residueFinset] using hx
  have hxlt := x.val_lt
  refine ⟨2, ?_⟩
  rw [← ZMod.natCast_zmod_val x]
  have hv : x.val = 2 := by omega
  rw [hv]
  norm_num

lemma r2_self_square_sixteen (x : ZMod 16)
    (hx : x ∈ residueFinset 16 (2 : Fin 8)) : IsSquare (x + x) := by
  have hxmod : x.val % 8 = 2 := by simpa [residueFinset] using hx
  have hxlt := x.val_lt
  refine ⟨2, ?_⟩
  rw [← ZMod.natCast_zmod_val x]
  have hv : x.val = 2 ∨ x.val = 10 := by omega
  rcases hv with hv | hv <;> rw [hv] <;> decide

lemma two_six_bound_eight (F : ZMod 8 → Finset (Fin 3))
    (hF : SquareSumColoring 8 F) :
    2 * residueWeight 8 F (2 : Fin 8) + residueWeight 8 F (6 : Fin 8) ≤ 3 := by
  simpa using two_six_bound_of_self_square 1 F hF r2_self_square_eight

lemma two_six_bound_sixteen (F : ZMod 16 → Finset (Fin 3))
    (hF : SquareSumColoring 16 F) :
    2 * residueWeight 16 F (2 : Fin 8) + residueWeight 16 F (6 : Fin 8) ≤ 6 := by
  simpa using two_six_bound_of_self_square 2 F hF r2_self_square_sixteen

/-! ## Assembly of the eight fibre inequalities -/

lemma eight_block_bound_of_special (k : ℕ)
    (F : ZMod ((2 ^ k) * 8) → Finset (Fin 3))
    (hF : SquareSumColoring ((2 ^ k) * 8) F)
    (h04 : 16 * (residueWeight ((2 ^ k) * 8) F (0 : Fin 8) +
        residueWeight ((2 ^ k) * 8) F (4 : Fin 8)) ≤ 33 * 2 ^ k)
    (h26 : 2 * residueWeight ((2 ^ k) * 8) F (2 : Fin 8) +
        residueWeight ((2 ^ k) * 8) F (6 : Fin 8) ≤ 3 * 2 ^ k) :
    32 * (∑ x, (F x).card) ≤ 33 * ((2 ^ k) * 8) := by
  let w : Fin 8 → ℕ := fun r ↦ residueWeight ((2 ^ k) * 8) F r
  have h01 : w 0 = 0 ∨ w 1 = 0 ∨ (w 0 ≤ 2 ^ k ∧ w 1 ≤ 2 ^ k) := by
    simpa [w] using block_cross_alternative k F hF 0 1 (by decide)
  have h27 : w 2 = 0 ∨ w 7 = 0 ∨ (w 2 ≤ 2 ^ k ∧ w 7 ≤ 2 ^ k) := by
    simpa [w] using block_cross_alternative k F hF 2 7 (by decide)
  have h36 : w 3 = 0 ∨ w 6 = 0 ∨ (w 3 ≤ 2 ^ k ∧ w 6 ≤ 2 ^ k) := by
    simpa [w] using block_cross_alternative k F hF 3 6 (by decide)
  have h45 : w 4 = 0 ∨ w 5 = 0 ∨ (w 4 ≤ 2 ^ k ∧ w 5 ≤ 2 ^ k) := by
    simpa [w] using block_cross_alternative k F hF 4 5 (by decide)
  have hsquare4 : IsSquare (4 : ZMod ((2 ^ k) * 8)) := ⟨2, by norm_num⟩
  have h17 : w 1 + w 7 ≤ 3 * 2 ^ k := by
    simpa [w] using block_sub_pair_le k F hF 0 1 7 (by decide) (by decide)
      (by exact ⟨0, by simp⟩)
  have h35 : w 3 + w 5 ≤ 3 * 2 ^ k := by
    simpa [w] using block_sub_pair_le k F hF 0 3 5 (by decide) (by decide)
      (by exact ⟨0, by simp⟩)
  have h13 : w 1 + w 3 ≤ 3 * 2 ^ k := by
    simpa [w] using block_sub_pair_le k F hF 4 1 3 (by decide) (by decide) hsquare4
  have h57 : w 5 + w 7 ≤ 3 * 2 ^ k := by
    simpa [w] using block_sub_pair_le k F hF 4 5 7 (by decide) (by decide) hsquare4
  have h6 : 2 * w 6 ≤ 3 * 2 ^ k := by
    have h66 := block_sub_pair_le k F hF 4 6 6 (by decide) (by decide) hsquare4
    simpa [w, two_mul] using h66
  have hlin := los_eight_weight_linear_bound (2 ^ k)
    (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)
    h01 h27 h36 h45 (by simpa [w] using h04) h17 h35 h13 h57 h6
    (by simpa [w] using h26)
  have hsum : w 0 + w 1 + w 2 + w 3 + w 4 + w 5 + w 6 + w 7 =
      ∑ x, (F x).card := by
    rw [← sum_residueWeight (2 ^ k) F, Fin.sum_univ_eight]
  calc
    32 * (∑ x, (F x).card) = 8 *
        (4 * (w 0 + w 1 + w 2 + w 3 + w 4 + w 5 + w 6 + w 7)) := by
      rw [hsum]
      ring
    _ ≤ 8 * (33 * 2 ^ k) := Nat.mul_le_mul_left 8 hlin
    _ = 33 * ((2 ^ k) * 8) := by ring

/-! ## Low powers and the complete two-primary bound -/

lemma coloring_sum_le_modulus_of_self_square {n : ℕ} [NeZero n]
    (F : ZMod n → Finset (Fin 3)) (hF : SquareSumColoring n F)
    (hself : ∀ x : ZMod n, IsSquare (x + x)) :
    (∑ x : ZMod n, (F x).card) ≤ n := by
  calc
    (∑ x : ZMod n, (F x).card) ≤ ∑ _x : ZMod n, 1 := by
      gcongr with x
      rw [Finset.card_le_one]
      intro c hc d hd
      exact hF x x (hself x) c hc d hd
    _ = n := by simp [ZMod.card]

lemma coloring_bound_pow_zero
    (F : ZMod (2 ^ 0) → Finset (Fin 3))
    (hF : SquareSumColoring (2 ^ 0) F) :
    32 * (∑ x, (F x).card) ≤ 33 * 2 ^ 0 := by
  have hself : ∀ x : ZMod (2 ^ 0), IsSquare (x + x) := by
    intro x
    refine ⟨0, ?_⟩
    have hx := x.val_lt
    norm_num at hx
    simpa [hx]
  have hsum := coloring_sum_le_modulus_of_self_square F hF hself
  norm_num at hsum ⊢
  omega

lemma coloring_bound_pow_one
    (F : ZMod (2 ^ 1) → Finset (Fin 3))
    (hF : SquareSumColoring (2 ^ 1) F) :
    32 * (∑ x, (F x).card) ≤ 33 * 2 ^ 1 := by
  have hself : ∀ x : ZMod (2 ^ 1), IsSquare (x + x) := by
    intro x
    refine ⟨0, ?_⟩
    have hx : x + x = 0 := by
      have htwo : (2 : ZMod (2 ^ 1)) = 0 := ZMod.natCast_self 2
      calc
        x + x = (2 : ZMod (2 ^ 1)) * x := by ring
        _ = 0 * x := by rw [htwo]
        _ = 0 := zero_mul x
    simpa [hx]
  have hsum := coloring_sum_le_modulus_of_self_square F hF hself
  norm_num at hsum ⊢
  omega

lemma coloring_bound_pow_two
    (F : ZMod (2 ^ 2) → Finset (Fin 3))
    (hF : SquareSumColoring (2 ^ 2) F) :
    32 * (∑ x, (F x).card) ≤ 33 * 2 ^ 2 := by
  have hsum : (∑ x, (F x).card) ≤ 4 := by
    simpa using squareSumColoring_four_bound F hF
  norm_num at hsum ⊢
  omega

/-- The bound at an arbitrary modulus, packaged as a proposition so that
equalities of the modulus transport the dependent fibre type at once. -/
def TwoPowerBound (n : ℕ) : Prop :=
  ∀ [NeZero n], ∀ F : ZMod n → Finset (Fin 3), SquareSumColoring n F →
    32 * (∑ x, (F x).card) ≤ 33 * n

theorem los_two_power_all (j : ℕ) : TwoPowerBound (2 ^ j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hj0 : j = 0
      · subst j
        exact coloring_bound_pow_zero
      by_cases hj1 : j = 1
      · subst j
        exact coloring_bound_pow_one
      by_cases hj2 : j = 2
      · subst j
        exact coloring_bound_pow_two
      have hj : 3 ≤ j := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
      have hblock : TwoPowerBound ((2 ^ k) * 8) := by
        unfold TwoPowerBound
        intro _inst
        intro G hG
        letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
        have hprevEq : 2 ^ (k + 1) = (2 ^ k) * 2 := by rw [pow_succ]
        have hprev : TwoPowerBound ((2 ^ k) * 2) :=
          (congrArg TwoPowerBound hprevEq).mp (ih (k + 1) (by omega))
        have hquarter := hprev (quarterPull (2 ^ k) G)
          (squareSumColoring_quarterPull hG)
        have h04 := quarterPull_residue_bound G hquarter
        have h26 : 2 * residueWeight ((2 ^ k) * 8) G (2 : Fin 8) +
            residueWeight ((2 ^ k) * 8) G (6 : Fin 8) ≤ 3 * 2 ^ k := by
          rcases k with _ | k
          · simpa using two_six_bound_eight G hG
          rcases k with _ | a
          · simpa using two_six_bound_sixteen G hG
          let Special (n : ℕ) : Prop := ∀ [NeZero n],
            ∀ G : ZMod n → Finset (Fin 3),
            SquareSumColoring n G →
            2 * residueWeight n G (2 : Fin 8) +
              residueWeight n G (6 : Fin 8) ≤ 3 * (4 * 2 ^ a)
          have htriEq : 2 ^ (a + 5) = (2 ^ (a + 1 + 1)) * 8 := by
            rw [show a + 5 = (a + 1 + 1) + 3 by omega, pow_add]
            norm_num
          have htri0 : Special (2 ^ (a + 5)) := by
            unfold Special
            intro _inst
            exact two_six_triangle_bound a
          have htri : Special ((2 ^ (a + 1 + 1)) * 8) :=
            (congrArg Special htriEq).mp htri0
          have ht := htri G hG
          have hp : 4 * 2 ^ a = 2 ^ (a + 1 + 1) := by
            rw [show a + 1 + 1 = a + 2 by omega, pow_add]
            norm_num
            ring
          simpa only [hp] using ht
        exact eight_block_bound_of_special k G hG h04 h26
      have hblockEq : 2 ^ (3 + k) = (2 ^ k) * 8 := by
        rw [pow_add]
        norm_num
        ring
      exact (congrArg TwoPowerBound hblockEq).mpr hblock

/-- The two-primary Lagarias--Odlyzko--Shearer bound, in the fibre form used
by the CRT assembly. -/
theorem los_two_power (j : ℕ) (F : ZMod (2 ^ j) → Finset (Fin 3))
    (hF : SquareSumColoring (2 ^ j) F) :
    32 * (∑ x, (F x).card) ≤ 33 * 2 ^ j :=
  (los_two_power_all j) F hF

end Erdos438

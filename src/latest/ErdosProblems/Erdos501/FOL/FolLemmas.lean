/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Two-valued lift and substitution lemmas for Flypitch's bounded formulas

Two-valued analogues of `Flypitch4/Bfol.lean`'s `boolean_realize_bounded_formula_insert_lift`,
`boolean_realize_formula_insert_lift2` and `boolean_realize_subst_formula0`, and of the private
`realize_lift2_at2` / `realize_lift3_at2` of `Flypitch4/Zfc.lean`.  They are needed to unfold the
two-valued semantics of Flypitch's strong collection scheme `axiom_of_collection`.
-/
import ErdosProblems.Erdos501.Flypitch4.Zfc

namespace Fol

variable {L : Language} {S : Structure L}

lemma realize_bounded_formula_eq' {n} {v₁ : DVec S n} (x : S) {l} (f : bounded_preformula L n l)
    (xs : DVec S l) :
    realize_bounded_formula v₁ f xs ↔
      realize_formula (fun k => if h : k < n then v₁.nth k h else x) f.fst xs :=
  realize_bounded_formula_iff (fun k hk => by simp [hk]) f xs

lemma realize_bounded_term_eq' {n} {v₁ : DVec S n} (x : S) {l} (t : bounded_preterm L n l)
    (xs : DVec S l) :
    realize_bounded_term v₁ t xs =
      realize_term (fun k => if h : k < n then v₁.nth k h else x) t.fst xs :=
  realize_bounded_term_eq (fun k hk => by simp [hk]) t xs

/-- Inserting a variable at position `m` of the context and lifting the formula accordingly does not
change its realization. -/
lemma realize_bounded_formula_insert_lift {n l} (v : DVec S n) (x : S) (m : ℕ) (hm : m ≤ n)
    (f : bounded_preformula L n l) (xs : DVec S l) :
    realize_bounded_formula (v.insert x m) (f ↑ᶠᵇ' 1 # m) xs ↔ realize_bounded_formula v f xs := by
  rw [realize_bounded_formula_eq' (v₁ := v.insert x m) x, realize_bounded_formula_eq' (v₁ := v) x]
  simp only [lift_bounded_formula_fst]
  rw [show (fun k => if h : k < n + 1 then (v.insert x m).nth k h else x) =
          subst_realize (fun k => if h : k < n then v.nth k h else x) x m from by
        funext k
        simp only [subst_realize]
        by_cases hkm : k < m
        · have hkn : k < n := Nat.lt_of_lt_of_le hkm hm
          have hkn1 : k < n + 1 := Nat.lt_succ_of_le (Nat.le_of_lt hkn)
          simp only [hkm, ite_true, hkn1, hkn, dite_true]
          simp [DVec.insert_nth_lt x v (by exact hkn) hkn1 (by exact hkm)]
        · by_cases hkm' : k = m
          · subst hkm'
            simp [DVec.insert_nth]
          · have hkm2 : m < k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hkm) (Ne.symm hkm')
            simp only [Nat.lt_asymm hkm2, hkm2, ite_false, ite_true]
            by_cases hkn1 : k < n + 1
            · have hk1 : k - 1 < n := by omega
              simp only [hkn1, hk1, dite_true]
              rw [DVec.insert_nth_gt_simp x v hkn1 hkm2]
            · have hk1 : ¬(k - 1 < n) := by omega
              simp only [hkn1, hk1, dite_false]]
  exact Iff.of_eq (realize_formula_subst_lift _ _ _ _ _)

@[simp] lemma realize_formula_insert_lift2 {n} (v : DVec S n) (x y z : S)
    (f : bounded_formula L (n + 2)) :
    realize_bounded_formula (DVec.cons x (DVec.cons y (DVec.cons z v))) (f ↑ᶠᵇ' 1 # 2) DVec.nil ↔
      realize_bounded_formula (DVec.cons x (DVec.cons y v)) f DVec.nil :=
  realize_bounded_formula_insert_lift (DVec.cons x (DVec.cons y v)) z 2 (by omega) f DVec.nil

lemma lift2_helper' {n l} (f : bounded_preformula L n l) {k} (m : ℕ) :
    (f ↑ᶠᵇ' (k + 2) # m).fst = ((f ↑ᶠᵇ' (k + 1) # m) ↑ᶠᵇ' 1 # m).fst := by
  simp only [lift_bounded_formula_fst]
  rw [lift_formula_at2_medium] <;> omega

lemma realize_lift2_at2 {n} (ϕ : bounded_formula L (n + 2)) (v : DVec S n) (x y z₁ z₂ : S) :
    realize_bounded_formula
        (DVec.cons x (DVec.cons y (DVec.cons z₁ (DVec.cons z₂ v)))) (ϕ ↑ᶠᵇ' 2 # 2) DVec.nil ↔
      realize_bounded_formula (DVec.cons x (DVec.cons y v)) ϕ DVec.nil := by
  rw [bounded_preformula.eq (lift2_helper' ϕ (k := 0) 2)]
  rw [realize_formula_insert_lift2 (DVec.cons z₂ v) x y z₁ (ϕ ↑ᶠᵇ' 1 # 2)]
  exact realize_formula_insert_lift2 v x y z₂ ϕ

lemma realize_lift3_at2 {n} (ϕ : bounded_formula L (n + 2)) (v : DVec S n) (x y z₁ z₂ z₃ : S) :
    realize_bounded_formula
        (DVec.cons x (DVec.cons y (DVec.cons z₁ (DVec.cons z₂ (DVec.cons z₃ v)))))
        (ϕ ↑ᶠᵇ' 3 # 2) DVec.nil ↔
      realize_bounded_formula (DVec.cons x (DVec.cons y v)) ϕ DVec.nil := by
  rw [bounded_preformula.eq (lift2_helper' ϕ (k := 1) 2)]
  rw [realize_formula_insert_lift2 (DVec.cons z₂ (DVec.cons z₃ v)) x y z₁ (ϕ ↑ᶠᵇ' 2 # 2)]
  exact realize_lift2_at2 ϕ v x y z₂ z₃

/-- Substituting a term for the innermost variable. -/
lemma realize_subst_formula0 [Nonempty S] {n} (f : bounded_formula L (n + 1))
    (t : bounded_term L n) (v : DVec S n) :
    realize_bounded_formula v (subst0_bounded_formula f t) DVec.nil ↔
      realize_bounded_formula (DVec.cons (realize_bounded_term v t DVec.nil) v) f DVec.nil := by
  obtain ⟨y⟩ := ‹Nonempty S›
  rw [realize_bounded_formula_eq' (v₁ := v) y, realize_bounded_formula_eq' (v₁ := DVec.cons _ v) y]
  simp only [subst0_bounded_formula_fst]
  rw [← realize_formula_subst0]
  apply realize_formula_congr
  intro k
  simp only [subst_realize]
  rw [← realize_bounded_term_eq' y]
  by_cases hk : k < n + 1
  · by_cases hk0 : k = 0
    · subst hk0
      simp [DVec.nth]
    · have hk' : k - 1 < n := by omega
      have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
      simp only [hk, hk0', hk', dite_true, ite_true, Nat.not_lt_zero, ite_false]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp [DVec.nth]
  · have hk' : ¬ (k - 1 < n) := by omega
    have hk0' : 0 < k := by omega
    simp only [hk, hk0', hk', dite_false, ite_true, Nat.not_lt_zero, ite_false]

end Fol

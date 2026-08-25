import Util.Bernays.IdealFactorizationUnique

/-!
# Products supported on two distinct maximal ideals
-/

open scoped Classical

namespace Bernays

theorem list_prod_two_values {M : Type*} [CommMonoid M] [DecidableEq M]
    (P Q : M) (hPQ : P ≠ Q) (l : List M) (hl : ∀ x ∈ l, x = P ∨ x = Q) :
    l.prod = P ^ l.count P * Q ^ l.count Q := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := hl x List.mem_cons_self
    have ht := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    rcases hx with rfl | rfl
    · simp only [List.prod_cons, List.count_cons_self, List.count_cons,
        beq_iff_eq, hPQ, if_false, Nat.add_zero, ht, pow_succ]
      ac_rfl
    · simp only [List.prod_cons, List.count_cons_self, List.count_cons,
        beq_iff_eq, Ne.symm hPQ, if_false, Nat.add_zero, ht, pow_succ]
      ac_rfl

theorem InvertibleIdeal.two_maximal_powers_injective {R : Type*} [CommRing R] [IsDomain R]
    (P Q : InvertibleIdeal R) (hP : (P : Ideal R).IsMaximal) (hQ : (Q : Ideal R).IsMaximal)
    (hPQ : P ≠ Q) {i j k l : ℕ} (heq : P ^ i * Q ^ j = P ^ k * Q ^ l) : i = k ∧ j = l := by
  classical
  have hprod : (List.replicate i P ++ List.replicate j Q).prod =
      (List.replicate k P ++ List.replicate l Q).prod := by
    simpa only [List.prod_append, List.prod_replicate] using heq
  have hmax (a b : ℕ) : ∀ T ∈ List.replicate a P ++ List.replicate b Q, (T : Ideal R).IsMaximal := by
    intro T hT
    rcases List.mem_append.mp hT with hT | hT
    · have ht : T = P := (List.mem_replicate.mp hT).2
      exact ht ▸ hP
    · have ht : T = Q := (List.mem_replicate.mp hT).2
      exact ht ▸ hQ
  have hperm := maximal_factors_perm hprod (hmax i j) (hmax k l)
  have hcountP := hperm.count_eq P
  have hcountQ := hperm.count_eq Q
  simpa [List.count_append, List.count_replicate, hPQ, Ne.symm hPQ] using And.intro hcountP hcountQ

end Bernays

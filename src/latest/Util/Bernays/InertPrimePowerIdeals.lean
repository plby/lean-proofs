import Util.Bernays.SplitPrimePowerIdeals

/-!
# Exact enumeration of ideals with a good inert-prime-power norm
-/

open scoped Classical

namespace Bernays

theorem list_prod_single_value {M : Type*} [Monoid M] (P : M) (l : List M)
    (hl : ∀ x ∈ l, x = P) : l.prod = P ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons, hl x List.mem_cons_self,
      ih (fun y hy => hl y (List.mem_cons_of_mem x hy)), List.length_cons, pow_succ']

theorem exists_inert_principal_power {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime)
    (hχ : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = p ^ e →
      ∃ k : ℕ, e = 2 * k ∧ I =
        InvertibleIdeal.principal (p : QuadraticAlgebra ℤ d b) (quadratic_natCast_ne_zero hp.pos) ^ k := by
  let := quadraticOrderIsDomain hD
  intro I hIF hnorm
  obtain ⟨l, hl, hmax⟩ := goodQuadraticIdeal_factorization hD I hIF
  let P := InvertibleIdeal.principal (p : QuadraticAlgebra ℤ d b) (quadratic_natCast_ne_zero hp.pos)
  have hsupport : ∀ Q ∈ l, Q = P := by
    intro Q hQl
    have hdiv : (Q : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∣ p ^ e := by
      rw [← hnorm, ← hl]
      exact InvertibleIdeal.cardQuot_dvd_listProd_of_mem hQl
    rcases goodMaximal_of_primePower_norm hD hp e Q (hmax Q hQl).1 (hmax Q hQl).2 hdiv with
      h | ⟨s, hs, _, _⟩
    · exact h.2
    · exact False.elim (s.character_ne_neg_one hD.ne (hs ▸ hχ))
  have hprod : I = P ^ l.length := hl.symm.trans (list_prod_single_value P l hsupport)
  refine ⟨l.length, ?_, hprod⟩
  apply Nat.pow_right_injective hp.two_le
  have h := congrArg InvertibleIdeal.normHom hprod
  change (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = _ at h
  rw [map_pow] at h
  change (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot =
    (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ^ l.length at h
  rw [hnorm, principal_nat_cardQuot hD hp.pos, ← pow_mul] at h
  exact h

theorem inert_normPower_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime) (hc : p.Coprime (discriminantLevel (b ^ 2 + 4 * d)))
    (hχ : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (p ^ e)) = if Even e then 1 else 0 := by
  let := quadraticOrderIsDomain hD
  let O := QuadraticAlgebra ℤ d b
  let X := GoodIdealNormFiber (quadraticBadIdeal d b) (p ^ e)
  by_cases he : Even e
  · obtain ⟨k, hk⟩ := he
    let P := InvertibleIdeal.principal (p : O) (quadratic_natCast_ne_zero hp.pos)
    have hnorm : ((P ^ k : InvertibleIdeal O) : Ideal O).cardQuot = p ^ e := by
      change InvertibleIdeal.normHom (P ^ k) = _
      rw [map_pow]
      change (P : Ideal O).cardQuot ^ k = p ^ e
      rw [principal_nat_cardQuot hD hp.pos, ← pow_mul, hk]
      congr 1
      omega
    let x : X := ⟨P ^ k, hnorm,
      InvertibleIdeal.coprime_scalar_of_cardQuot_coprime _ _ (by rw [hnorm]; exact hc.pow_left e)⟩
    let : Unique X :=
      { default := x
        uniq := by
          intro I
          obtain ⟨j, hj, hI⟩ := exists_inert_principal_power hD hp hχ e I.1 I.2.2 I.2.1
          have hjk : j = k := by omega
          apply Subtype.ext
          simpa only [hjk] using hI }
    rw [if_pos (show Even e from ⟨k, hk⟩)]
    exact Nat.card_unique
  · let : IsEmpty X := ⟨fun I => by
      obtain ⟨k, hk, _⟩ := exists_inert_principal_power hD hp hχ e I.1 I.2.2 I.2.1
      exact he ⟨k, by omega⟩⟩
    rw [if_neg he]
    change Nat.card X = 0
    simp

end Bernays

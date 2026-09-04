import Util.Bernays.SignedIdealProducts
import Util.Bernays.SquareClassExceptional

/-!
# From missing ideal classes to few rational prime factors
-/

open scoped Classical

namespace Bernays

theorem countOutsideSubgroup_ofFn {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) {k : ℕ} (x : Fin k → G) :
    countOutsideSubgroup H (List.ofFn x) = Nat.card {i : Fin k // x i ∉ H} := by
  classical
  have hlist (l : List G) : countOutsideSubgroup H l =
      (l.map fun a => if a ∉ H then 1 else 0).sum := by
    induction l with
    | nil => simp [countOutsideSubgroup]
    | cons a l ih =>
      by_cases ha : a ∈ H <;> simp [countOutsideSubgroup, ha] at * <;> omega
  rw [hlist, List.map_ofFn, Fin.sum_ofFn, Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert Finset.sum_boole (R := ℕ) (fun i => x i ∉ H) Finset.univ using 1 <;>
    simp only [Function.comp_def, Nat.cast_id] <;> congr

theorem goodMaximal_unique_prime_divisor {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∃ q : ℕ, q.Prime ∧ ∀ p : ℕ, p.Prime →
        p ∣ (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot → p = q := by
  let := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, hq, _, h | ⟨s, hs, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · refine ⟨q, hq, ?_⟩
    intro p hp hdvd
    rw [h.2.1] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)
  · refine ⟨q, hq, ?_⟩
    intro p hp hdvd
    rw [s.ideal_cardQuot hD ε, hs] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd

theorem SplitPrime.oriented_squareClass_mem_iff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      ∀ ε : Bool, classSquareElement (s.ideal hD ε).idealClass ∈ H ↔
        classSquareElement (s.idealClass hD) ∈ H := by
  let := quadraticOrderIsDomain hD
  intro H ε
  cases ε
  · rfl
  · have heq : classSquareElement (s.ideal hD true).idealClass =
        (classSquareElement (s.idealClass hD))⁻¹ := by
      apply Subtype.ext
      simp only [classSquareElement, s.idealClass_conjugate hD, inv_pow, Subgroup.coe_inv]
    rw [heq, H.inv_mem_iff]

theorem goodMaximal_squareClass_outside_of_bad_dvd {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      ∀ s : SplitPrime d b, classSquareElement (s.idealClass hD) ∉ H →
      s.1 ∣ (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot → classSquareElement P.idealClass ∉ H := by
  let := quadraticOrderIsDomain hD
  intro P hP hPF H s hs hdvd
  obtain ⟨q, hq, _, h | ⟨t, ht, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · rw [h.2.1] at hdvd
    have heq := (Nat.prime_dvd_prime_iff_eq s.2.1 hq).mp (s.2.1.dvd_of_dvd_pow hdvd)
    exact False.elim (s.character_ne_neg_one hD.ne (heq ▸ h.1))
  · rw [t.ideal_cardQuot hD ε] at hdvd
    have hst : s = t := Subtype.ext ((Nat.prime_dvd_prime_iff_eq s.2.1 t.2.1).mp hdvd)
    subst t
    exact fun h => hs ((s.oriented_squareClass_mem_iff hD H ε).mp h)

theorem badPrimeFactors_card_le_outside_coordinates {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ {k : ℕ} (P : Fin k → InvertibleIdeal (QuadraticAlgebra ℤ d b)),
      (∀ i, (P i : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal ∧
        IsCoprime (P i : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b)) →
      ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
        ((((∏ i, P i : InvertibleIdeal (QuadraticAlgebra ℤ d b)) :
          Ideal (QuadraticAlgebra ℤ d b)).cardQuot).primeFactors.filter (squareBadPrime hD H)).card ≤
          countOutsideSubgroup H (List.ofFn fun i => classSquareElement (P i).idealClass) := by
  classical
  let := quadraticOrderIsDomain hD
  let := quadraticOrderClassGroupFintype hD
  let : Fintype (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))) := Fintype.ofFinite _
  intro k P hP H
  let n := ((∏ i, P i : InvertibleIdeal (QuadraticAlgebra ℤ d b)) : Ideal (QuadraticAlgebra ℤ d b)).cardQuot
  let A := n.primeFactors.filter (squareBadPrime hD H)
  let X := {p // p ∈ A}
  let Y := {i : Fin k // classSquareElement (P i).idealClass ∉ H}
  have hex (p : X) : ∃ i : Y, p.1 ∣ (P i.1 : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
    obtain ⟨hpN, hpBad⟩ := Finset.mem_filter.mp p.2
    obtain ⟨hp, hpn, _⟩ := Nat.mem_primeFactors.mp hpN
    change p.1 ∣ ((∏ i, P i : InvertibleIdeal (QuadraticAlgebra ℤ d b)) : Ideal (QuadraticAlgebra ℤ d b)).cardQuot at hpn
    rw [InvertibleIdeal.cardQuot_prod] at hpn
    obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff
      (fun i => (P i : Ideal (QuadraticAlgebra ℤ d b)).cardQuot)).mp hpn
    obtain ⟨s, hs, hsb⟩ := hpBad
    refine ⟨⟨i, goodMaximal_squareClass_outside_of_bad_dvd hD (P i) (hP i).1 (hP i).2 H s hsb ?_⟩, hi⟩
    simpa only [hs] using hi
  let f : X → Y := fun p => (hex p).choose
  have hf : Function.Injective f := by
    intro p q hpq
    have hpdiv := (hex p).choose_spec
    have hqdiv := (hex q).choose_spec
    change p.1 ∣ (P (f p).1 : Ideal (QuadraticAlgebra ℤ d b)).cardQuot at hpdiv
    change q.1 ∣ (P (f q).1 : Ideal (QuadraticAlgebra ℤ d b)).cardQuot at hqdiv
    rw [← hpq] at hqdiv
    obtain ⟨r, _, hr⟩ := goodMaximal_unique_prime_divisor hD (P (f p).1) (hP _).1 (hP _).2
    have hpprime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp p.2).1).1
    have hqprime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp q.2).1).1
    exact Subtype.ext ((hr p.1 hpprime hpdiv).trans (hr q.1 hqprime hqdiv).symm)
  have hc := Nat.card_le_card_of_injective f hf
  rw [show Nat.card X = A.card from Nat.card_eq_fintype_card.trans (Fintype.card_coe A)] at hc
  rw [countOutsideSubgroup_ofFn]
  exact hc

end Bernays

import Util.Bernays.GoodNorms

/-!
# The genus of an ideal norm

For ideals coprime to the discriminant, the class modulo squares is determined
by the natural norm. This is a factorization statement and does not invoke the
principal genus theorem or a prime-distribution assumption.
-/

namespace Bernays

abbrev GenusGroup (R : Type*) [CommRing R] [IsDomain R] :=
  ClassGroup R ⧸ (classSquareSubgroup : Subgroup (ClassGroup R))

noncomputable def genusMap {R : Type*} [CommRing R] [IsDomain R] : ClassGroup R →* GenusGroup R :=
  QuotientGroup.mk' classSquareSubgroup

theorem genusMap_inv_eq {R : Type*} [CommRing R] [IsDomain R] (x : ClassGroup R) :
    genusMap x⁻¹ = genusMap x := by
  change QuotientGroup.mk x⁻¹ = QuotientGroup.mk x
  rw [QuotientGroup.eq_iff_div_mem]
  exact ⟨x⁻¹, by simp [div_eq_mul_inv, pow_two]⟩

theorem genusGroup_sq {R : Type*} [CommRing R] [IsDomain R] (x : GenusGroup R) : x ^ 2 = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective classSquareSubgroup x
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (classSquare_mem y)

noncomputable def primeGenus {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ℕ → GenusGroup (QuadraticAlgebra ℤ d b) := by
  classical
  letI := quadraticOrderIsDomain hD
  exact fun q => if h : ∃ s : SplitPrime d b, s.1 = q then genusMap (h.choose.idealClass hD) else 1

theorem primeGenus_split {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    primeGenus hD s.1 = genusMap (s.idealClass hD) := by
  classical
  letI := quadraticOrderIsDomain hD
  have hex : ∃ t : SplitPrime d b, t.1 = s.1 := ⟨s, rfl⟩
  have heq : hex.choose = s := Subtype.ext hex.choose_spec
  simp only [primeGenus, dif_pos hex, heq]

noncomputable def genusValue {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ℕ → GenusGroup (QuadraticAlgebra ℤ d b) :=
  letI := quadraticOrderIsDomain hD
  fun n => n.factorization.prod (fun q e => primeGenus hD q ^ e)

theorem genusValue_one {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    genusValue hD 1 = 1 := by
  simp [genusValue]

theorem genusValue_mul {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    letI := quadraticOrderIsDomain hD
    genusValue hD (m * n) = genusValue hD m * genusValue hD n := by
  letI := quadraticOrderIsDomain hD
  rw [genusValue, Nat.factorization_mul hm.ne' hn.ne']
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem genusValue_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    genusValue hD (p ^ e) = primeGenus hD p ^ e := by
  letI := quadraticOrderIsDomain hD
  rw [genusValue, hp.factorization_pow, Finsupp.prod_single_index]
  exact pow_zero _

theorem genusValue_goodMaximal_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      genusValue hD (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = genusMap P.idealClass := by
  letI := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, hq, _, h | ⟨s, hs, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · rw [h.2.1, h.2.2, map_one, genusValue_primePower hD hq, genusGroup_sq]
  · rw [s.ideal_cardQuot hD ε]
    have hprime : genusValue hD s.1 = genusMap (s.idealClass hD) := by
      have h := genusValue_primePower hD s.2.1 1
      simpa only [pow_one, primeGenus_split] using h
    rw [hprime]
    cases ε
    · rfl
    · rw [s.idealClass_conjugate hD, genusMap_inv_eq]

theorem genusValue_goodIdeal_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      genusValue hD (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = genusMap I.idealClass := by
  letI := quadraticOrderIsDomain hD
  intro I hIF
  obtain ⟨l, hl, hP⟩ := goodQuadraticIdeal_factorization hD I hIF
  rw [← hl]
  clear hl I hIF
  induction l with
  | nil => simp [Submodule.cardQuot_top, genusValue_one]
  | cons P l ih =>
    rw [List.prod_cons, InvertibleIdeal.cardQuot_mul, genusValue_mul hD P.cardQuot_pos l.prod.cardQuot_pos,
      InvertibleIdeal.idealClass_mul, map_mul]
    have hhead := hP P List.mem_cons_self
    rw [genusValue_goodMaximal_norm hD P hhead.1 hhead.2,
      ih (fun Q hQ => hP Q (List.mem_cons_of_mem P hQ))]

end Bernays

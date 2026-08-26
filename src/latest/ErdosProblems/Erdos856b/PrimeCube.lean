import ErdosProblems.Erdos856b.Capacity
import ErdosProblems.Erdos856b.Squarefree

/-! # Prime-divisor cubes for the upper arithmetic transference -/

namespace Erdos856b

open scoped BigOperators

noncomputable def cubeProduct (P : Finset ℕ) (T : Finset P) : ℕ := ∏ p ∈ T, p.val

theorem cubeProduct_eq_map_prod {P : Finset ℕ} (T : Finset P) :
    cubeProduct P T = ∏ p ∈ T.map (Function.Embedding.subtype _), p := by
  simp [cubeProduct]

theorem cubeProduct_primeFactors {P : Finset ℕ} (hp : ∀ p ∈ P, p.Prime) (T : Finset P) :
    (cubeProduct P T).primeFactors = T.map (Function.Embedding.subtype _) := by
  rw [cubeProduct_eq_map_prod]
  apply Nat.primeFactors_prod
  intro p hmem
  obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hmem
  exact hp q.val q.property

theorem cubeProduct_injective {P : Finset ℕ} (hp : ∀ p ∈ P, p.Prime) :
    Function.Injective (cubeProduct P) := by
  intro T U h
  have h' := congrArg Nat.primeFactors h
  rw [cubeProduct_primeFactors hp, cubeProduct_primeFactors hp] at h'
  exact Finset.map_injective _ h'

theorem cubeProduct_squarefree {P : Finset ℕ} (hp : ∀ p ∈ P, p.Prime) (T : Finset P) :
    Squarefree (cubeProduct P T) := by
  unfold cubeProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p _ q _ hpq
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes (hp _ p.property) (hp _ q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  · intro p _
    exact (hp _ p.property).squarefree

theorem cubeProduct_lcm {P : Finset ℕ} (hp : ∀ p ∈ P, p.Prime) (T U : Finset P) :
    Nat.lcm (cubeProduct P T) (cubeProduct P U) = cubeProduct P (T ∪ U) := by
  rw [lcm_eq_prod_union (cubeProduct_squarefree hp T) (cubeProduct_squarefree hp U),
    cubeProduct_primeFactors hp, cubeProduct_primeFactors hp, ← Finset.map_union,
    ← cubeProduct_eq_map_prod]

noncomputable def cubeFamily (P : Finset ℕ) (c : ℕ) (A : Finset ℕ) : Finset (Finset P) :=
  Finset.univ.filter (fun T => c * cubeProduct P T ∈ A)

theorem cubeFamily_unionFree {k c : ℕ} {P : Finset ℕ} {A : Finset ℕ}
    (hc : 0 < c) (hp : ∀ p ∈ P, p.Prime) (hA : LcmFree k A) :
    UnionFree k (cubeFamily P c A) := by
  intro T hT hmem hbad
  obtain ⟨U, hU⟩ := hbad
  have ha : Function.Injective (fun i => c * cubeProduct P (T i)) := by
    intro i j hij
    exact hT (cubeProduct_injective hp (Nat.eq_of_mul_eq_mul_left hc hij))
  apply hA (fun i => c * cubeProduct P (T i)) ha
    (fun i => (Finset.mem_filter.mp (hmem i)).2)
  exact ⟨c * cubeProduct P U, fun i j hij => by
    rw [Nat.lcm_mul_left, cubeProduct_lcm hp, hU i j hij]⟩

theorem partitionWeight_le_C_fintype {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} (hk : 3 ≤ k) {F : Finset (Finset α)} (hF : UnionFree k F) (z : ℝ) :
    partitionWeight F z ≤ C k (Fintype.card α) z := by
  classical
  let e := (Fintype.equivFin α).toEmbedding
  have h := partitionWeight_le_C (hF.map hk e) z
  have heq : partitionWeight (F.image (Finset.map e)) z = partitionWeight F z := by
    unfold partitionWeight
    rw [Finset.sum_image]
    · simp
    · intro s _ t _ h
      exact Finset.map_injective e h
  rwa [heq] at h

noncomputable def radicalProduct (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

noncomputable def cubeCore (m : ℕ) : ℕ := m / radicalProduct m

theorem radicalProduct_pos (m : ℕ) : 0 < radicalProduct m :=
  Finset.prod_pos (fun _p hp => (Nat.prime_of_mem_primeFactors hp).pos)

theorem cubeCore_pos {m : ℕ} (hm : 0 < m) : 0 < cubeCore m :=
  Nat.div_pos (Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)) (radicalProduct_pos m)

theorem cubeCore_mul_radical (m : ℕ) : cubeCore m * radicalProduct m = m :=
  Nat.div_mul_cancel (Nat.prod_primeFactors_dvd m)

theorem cubeProduct_univ (m : ℕ) :
    cubeProduct m.primeFactors Finset.univ = radicalProduct m :=
  Finset.prod_coe_sort m.primeFactors (fun p => p)

noncomputable def removedPrimes (m q : ℕ) : Finset m.primeFactors :=
  Finset.univ.filter (fun p => p.val ∈ q.primeFactors)

theorem removedPrimes_map {m q : ℕ} (hm : m ≠ 0) (hqm : q ∣ m) :
    (removedPrimes m q).map (Function.Embedding.subtype _) = q.primeFactors := by
  ext p
  simp only [Finset.mem_map, removedPrimes, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨p', hp', rfl⟩
    exact hp'
  · intro hp
    exact ⟨⟨p, Nat.primeFactors_mono hqm hm hp⟩, hp, rfl⟩

theorem removedPrimes_product {m q : ℕ} (hm : m ≠ 0) (hqm : q ∣ m)
    (hq : Squarefree q) : cubeProduct m.primeFactors (removedPrimes m q) = q := by
  rw [cubeProduct_eq_map_prod, removedPrimes_map hm hqm]
  exact Nat.prod_primeFactors_of_squarefree hq

theorem removedPrimes_card {m q : ℕ} (hm : m ≠ 0) (hqm : q ∣ m) :
    (removedPrimes m q).card = q.primeFactors.card := by
  rw [← removedPrimes_map hm hqm, Finset.card_map]

theorem cubeCore_mul_complement {a q : ℕ} (ha : 0 < a) (hq : Squarefree q) :
    cubeCore (a * q) * cubeProduct (a * q).primeFactors (removedPrimes (a * q) q)ᶜ = a := by
  have hm : a * q ≠ 0 := mul_ne_zero ha.ne' hq.ne_zero
  have hqprod := removedPrimes_product hm (dvd_mul_left q a) hq
  have hprod := Finset.prod_compl_mul_prod (removedPrimes (a * q) q) (fun p => p.val)
  change cubeProduct (a * q).primeFactors (removedPrimes (a * q) q)ᶜ *
    cubeProduct (a * q).primeFactors (removedPrimes (a * q) q) =
      cubeProduct (a * q).primeFactors Finset.univ at hprod
  rw [hqprod, cubeProduct_univ] at hprod
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq.ne_zero)
  calc
    q * (cubeCore (a * q) * cubeProduct (a * q).primeFactors (removedPrimes (a * q) q)ᶜ) =
        cubeCore (a * q) *
          (cubeProduct (a * q).primeFactors (removedPrimes (a * q) q)ᶜ * q) := by ring
    _ = a * q := by rw [hprod, cubeCore_mul_radical]
    _ = q * a := mul_comm _ _

theorem removed_complement_weight {m q : ℕ} (hm : m ≠ 0) (hqm : q ∣ m)
    {z : ℝ} (hz : 0 < z) :
    z ^ q.primeFactors.card = z ^ m.primeFactors.card *
      (1 / z) ^ (removedPrimes m q)ᶜ.card := by
  have hcard : q.primeFactors.card + (removedPrimes m q)ᶜ.card = m.primeFactors.card := by
    rw [← removedPrimes_card hm hqm]
    simp
  rw [← hcard, pow_add, one_div_pow]
  field_simp

end Erdos856b

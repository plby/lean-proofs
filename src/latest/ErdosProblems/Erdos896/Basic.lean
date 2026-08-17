/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 896

For `A, B ⊆ {1, ..., N}`, `F A B` counts the products having exactly one
ordered representation `a * b` with `a ∈ A` and `b ∈ B`.  The main result is
the Ford-scale estimate

`maxF N = Θ(N² / ((log N)^δ (log log N)^(3/2)))`.

The detailed mathematical proof and Leanization map are in `tex/896.tex`.
-/

namespace Erdos896

open Filter Asymptotics

/-- The integer interval `{1, ..., N}`. -/
def box (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- The number of ordered representations `m = a * b` with `a ∈ A`, `b ∈ B`. -/
def representationCount (A B : Finset ℕ) (m : ℕ) : ℕ :=
  ((A.product B).filter fun p ↦ p.1 * p.2 = m).card

/-- Products having exactly one ordered representation from `A × B`. -/
def uniqueProducts (A B : Finset ℕ) : Finset ℕ :=
  ((A.product B).image fun p ↦ p.1 * p.2).filter fun m ↦
    representationCount A B m = 1

/-- The quantity `F(A,B)` in Problem 896. -/
def F (A B : Finset ℕ) : ℕ := (uniqueProducts A B).card

/-- The maximum of `F(A,B)` over `A, B ⊆ {1, ..., N}`. -/
def maxF (N : ℕ) : ℕ :=
  ((box N).powerset.product (box N).powerset).sup fun p ↦ F p.1 p.2

/-- The set of all entries in the `N` by `N` multiplication table. -/
def multiplicationTable (N : ℕ) : Finset ℕ :=
  (((box N).product (box N)).image fun p ↦ p.1 * p.2)

@[simp]
lemma mem_box {N n : ℕ} : n ∈ box N ↔ 1 ≤ n ∧ n ≤ N := by
  simp [box]

@[simp]
lemma mem_uniqueProducts {A B : Finset ℕ} {m : ℕ} :
    m ∈ uniqueProducts A B ↔
      (∃ a ∈ A, ∃ b ∈ B, a * b = m) ∧ representationCount A B m = 1 := by
  simp [uniqueProducts]
  aesop

lemma representationCount_eq_one_iff {A B : Finset ℕ} {m : ℕ} :
    representationCount A B m = 1 ↔
      ∃! p : ℕ × ℕ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 * p.2 = m := by
  rw [representationCount, Finset.card_eq_one_iff_existsUnique]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨p, hp, hunique⟩
    have hp' := Finset.mem_product.mp hp.1
    refine ⟨p, ⟨hp'.1, hp'.2, hp.2⟩, ?_⟩
    intro q hq
    exact hunique q ⟨Finset.mem_product.mpr ⟨hq.1, hq.2.1⟩, hq.2.2⟩
  · rintro ⟨p, hp, hunique⟩
    refine ⟨p, ⟨Finset.mem_product.mpr ⟨hp.1, hp.2.1⟩, hp.2.2⟩, ?_⟩
    intro q hq
    have hq' := Finset.mem_product.mp hq.1
    exact hunique q ⟨hq'.1, hq'.2, hq.2⟩

lemma uniqueProducts_subset_productImage (A B : Finset ℕ) :
    uniqueProducts A B ⊆ (A.product B).image (fun p ↦ p.1 * p.2) := by
  exact Finset.filter_subset _ _

lemma F_le_productImage_card (A B : Finset ℕ) :
    F A B ≤ ((A.product B).image fun p ↦ p.1 * p.2).card := by
  exact Finset.card_le_card (uniqueProducts_subset_productImage A B)

lemma productImage_mono {A B A' B' : Finset ℕ}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    (A.product B).image (fun p ↦ p.1 * p.2) ⊆
      (A'.product B').image (fun p ↦ p.1 * p.2) := by
  intro m hm
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hm
  have hab' := Finset.mem_product.mp hab
  exact Finset.mem_image.mpr
    ⟨(a, b), Finset.mem_product.mpr ⟨hA hab'.1, hB hab'.2⟩, rfl⟩

/-- Every uniquely represented product is an entry of the full multiplication table. -/
lemma F_le_multiplicationTable_card {N : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ box N) (hB : B ⊆ box N) :
    F A B ≤ (multiplicationTable N).card := by
  exact (F_le_productImage_card A B).trans
    (Finset.card_le_card (productImage_mono hA hB))

/-- Any admissible pair contributes no more than the finite maximum `maxF N`. -/
lemma F_le_maxF {N : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ box N) (hB : B ⊆ box N) : F A B ≤ maxF N := by
  unfold maxF
  exact Finset.le_sup
    (s := (box N).powerset.product (box N).powerset)
    (f := fun p : Finset ℕ × Finset ℕ ↦ F p.1 p.2)
    (b := (A, B))
    (Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr hA, Finset.mem_powerset.mpr hB⟩)

/-- A pointwise upper bound for all admissible pairs bounds `maxF`. -/
lemma maxF_le {N K : ℕ}
    (h : ∀ A B : Finset ℕ, A ⊆ box N → B ⊆ box N → F A B ≤ K) :
    maxF N ≤ K := by
  unfold maxF
  apply Finset.sup_le
  rintro ⟨A, B⟩ hAB
  obtain ⟨hA, hB⟩ := Finset.mem_product.mp hAB
  exact h A B (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB)

/-- The maximum is bounded by the number of entries of the full multiplication table. -/
lemma maxF_le_multiplicationTable_card (N : ℕ) :
    maxF N ≤ (multiplicationTable N).card := by
  exact maxF_le fun _ _ hA hB ↦ F_le_multiplicationTable_card hA hB

/-- `maxF` is genuinely attained by a pair of subsets of `box N`. -/
lemma exists_maximizers (N : ℕ) :
    ∃ A B : Finset ℕ, A ⊆ box N ∧ B ⊆ box N ∧ maxF N = F A B := by
  let candidates := (box N).powerset.product (box N).powerset
  have hcandidates : candidates.Nonempty := by
    refine ⟨(∅, ∅), ?_⟩
    simp [candidates]
  obtain ⟨p, hp, hsup⟩ :=
    Finset.exists_mem_eq_sup candidates hcandidates (fun p ↦ F p.1 p.2)
  obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hp
  refine ⟨p.1, p.2, ?_, ?_, ?_⟩
  · exact Finset.mem_powerset.mp hpA
  · exact Finset.mem_powerset.mp hpB
  · simpa [maxF, candidates] using hsup

/-! ## The finite lower-bound bridge -/

/-- The left set produced by a selected finite set of primes. -/
def leftSet (N : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (box N).filter fun a ↦
    N < 2 * a ∧ ∃ p ∈ P, p ∣ a

/-- The right set consists of the positive integers avoiding every selected prime. -/
def rightSet (N : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (box N).filter fun b ↦
    ∀ p ∈ P, ¬p ∣ b

/-- The exact finite data needed from a good integer `n` for the selected prime `p`.

The inequalities `N < 2 * p * d` and `p * d ≤ N` say precisely that
`N / (2p) < d ≤ N / p`, without introducing rounded real endpoints. -/
def Good (N : ℕ) (P : Finset ℕ) (p n : ℕ) : Prop :=
  0 < n ∧
    (∀ q ∈ P, ¬q ∣ n) ∧
    ∃! d : ℕ,
      d ∣ n ∧ N < 2 * p * d ∧ p * d ≤ N ∧ n / d ≤ N

lemma half_lt_iff (N a : ℕ) : N / 2 < a ↔ N < 2 * a := by
  omega

lemma mem_uniqueProducts_of_existsUnique
    {A B : Finset ℕ} {m : ℕ}
    (h : ∃! ab : ℕ × ℕ, ab ∈ A.product B ∧ ab.1 * ab.2 = m) :
    m ∈ uniqueProducts A B := by
  rcases h with ⟨ab, hab, hab_unique⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_image.mpr ⟨ab, hab.1, hab.2⟩
  · apply representationCount_eq_one_iff.mpr
    have habmem := Finset.mem_product.mp hab.1
    refine ⟨ab, ⟨habmem.1, habmem.2, hab.2⟩, ?_⟩
    intro cd hcd
    exact hab_unique cd
      ⟨Finset.mem_product.mpr ⟨hcd.1, hcd.2.1⟩, hcd.2.2⟩

/-- A good pair `(p,n)` gives exactly one representation of `p*n` from the
constructed left and right sets. -/
theorem good_unique_representation
    (N : ℕ) (P : Finset ℕ)
    (hprime : ∀ q ∈ P, Nat.Prime q)
    {p n : ℕ} (hp : p ∈ P) (hn : Good N P p n) :
    ∃! ab : ℕ × ℕ,
      ab ∈ (leftSet N P).product (rightSet N P) ∧ ab.1 * ab.2 = p * n := by
  rcases hn with ⟨hnpos, hfree, d, hd, hd_unique⟩
  have hpprime : Nat.Prime p := hprime p hp
  have hppos : 0 < p := hpprime.pos
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
    subst d
    simp at hd
  have hdle : d ≤ n := Nat.le_of_dvd hnpos hd.1
  have hquotpos : 0 < n / d := Nat.div_pos hdle hdpos
  have hdn : d * (n / d) = n := Nat.mul_div_cancel' hd.1
  let witness : ℕ × ℕ := (p * d, n / d)
  have hwitness_mem : witness ∈ (leftSet N P).product (rightSet N P) := by
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact mem_box.mpr ⟨Nat.mul_pos hppos hdpos, hd.2.2.1⟩
      · constructor
        · simpa [mul_assoc] using hd.2.1
        · exact ⟨p, hp, dvd_mul_right p d⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact mem_box.mpr ⟨hquotpos, hd.2.2.2⟩
      · intro q hqP hqdiv
        apply hfree q hqP
        rcases hqdiv with ⟨k, hk⟩
        have hk' : n / d = q * k := by simpa [witness] using hk
        refine ⟨d * k, ?_⟩
        calc
          n = d * (n / d) := hdn.symm
          _ = d * (q * k) := by rw [hk']
          _ = q * (d * k) := by ac_rfl
  have hwitness_prod : witness.1 * witness.2 = p * n := by
    dsimp [witness]
    calc
      (p * d) * (n / d) = p * (d * (n / d)) := by simp [mul_assoc]
      _ = p * n := by rw [hdn]
  refine ⟨witness, ⟨hwitness_mem, hwitness_prod⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨habmem, habprod⟩
  rcases Finset.mem_product.mp habmem with ⟨ha, hb⟩
  rcases Finset.mem_filter.mp ha with ⟨haIcc, haLarge, q, hqP, hqa⟩
  rcases Finset.mem_filter.mp hb with ⟨hbIcc, hbfree⟩
  have hqprime : Nat.Prime q := hprime q hqP
  have hqprod : q ∣ p * n := by
    rw [← habprod]
    exact dvd_mul_of_dvd_left hqa b
  have hq_dvd_p : q ∣ p :=
    ((hqprime.dvd_mul.mp hqprod).resolve_right (hfree q hqP))
  have hqp : q = p := by
    rcases (Nat.dvd_prime hpprime).mp hq_dvd_p with hq1 | hqp
    · exact (hqprime.ne_one hq1).elim
    · exact hqp
  subst q
  rcases hqa with ⟨e, rfl⟩
  have heb : e * b = n := by
    apply Nat.mul_left_cancel hppos
    simpa [mul_assoc] using habprod
  have hepos : 0 < e := by
    by_contra h
    have he0 : e = 0 := Nat.eq_zero_of_not_pos h
    subst e
    simp at haLarge
  have hdiv : n / e = b := by
    rw [← heb]
    simpa [Nat.mul_comm] using Nat.mul_div_left b hepos
  have he_good :
      e ∣ n ∧ N < 2 * p * e ∧ p * e ≤ N ∧ n / e ≤ N := by
    refine ⟨⟨b, heb.symm⟩, ?_, (mem_box.mp haIcc).2, ?_⟩
    · simpa [mul_assoc] using haLarge
    · simpa [hdiv] using (mem_box.mp hbIcc).2
  have hed : e = d := hd_unique e he_good
  subst e
  simp only [witness, Prod.mk.injEq, true_and]
  exact hdiv.symm

/-- Products `p*n` are distinct when every `n` avoids all selected primes. -/
theorem products_injective
    (P : Finset ℕ) (G : ℕ → Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hfree : ∀ p ∈ P, ∀ n ∈ G p, ∀ q ∈ P, ¬q ∣ n) :
    Set.InjOn (fun pn : Σ _p : ℕ, ℕ ↦ pn.1 * pn.2)
      (P.sigma G : Set (Σ _p : ℕ, ℕ)) := by
  rintro ⟨p, n⟩ hpn ⟨q, m⟩ hqm heq
  change p * n = q * m at heq
  rcases Finset.mem_sigma.mp hpn with ⟨hp, hn⟩
  rcases Finset.mem_sigma.mp hqm with ⟨hq, hm⟩
  have hpprime := hprime p hp
  have hqprime := hprime q hq
  have hpqm : p ∣ q * m := by
    rw [← heq]
    exact dvd_mul_right p n
  have hpq : p ∣ q :=
    (hpprime.dvd_mul.mp hpqm).resolve_right (hfree q hq m hm p hp)
  have hp_eq_q : p = q := by
    rcases (Nat.dvd_prime hqprime).mp hpq with hp1 | hpq
    · exact (hpprime.ne_one hp1).elim
    · exact hpq
  subst q
  have hn_eq_m : n = m := Nat.mul_left_cancel hpprime.pos heq
  subst m
  rfl

/-- Products generated by the good sigma family. -/
def goodProducts (P : Finset ℕ) (G : ℕ → Finset ℕ) : Finset ℕ :=
  (P.sigma G).image fun pn ↦ pn.1 * pn.2

lemma goodProducts_subset_uniqueProducts
    (N : ℕ) (P : Finset ℕ) (G : ℕ → Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hgood : ∀ p ∈ P, ∀ n ∈ G p, Good N P p n) :
    goodProducts P G ⊆ uniqueProducts (leftSet N P) (rightSet N P) := by
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨pn, hpn, rfl⟩
  rcases Finset.mem_sigma.mp hpn with ⟨hp, hn⟩
  exact mem_uniqueProducts_of_existsUnique
    (good_unique_representation N P hprime hp (hgood pn.1 hp pn.2 hn))

/-- The cardinality form of the finite lower-bound bridge. -/
theorem card_sigma_le_F
    (N : ℕ) (P : Finset ℕ) (G : ℕ → Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hgood : ∀ p ∈ P, ∀ n ∈ G p, Good N P p n) :
    (P.sigma G).card ≤ F (leftSet N P) (rightSet N P) := by
  have hfree : ∀ p ∈ P, ∀ n ∈ G p, ∀ q ∈ P, ¬q ∣ n := by
    intro p hp n hn q hq
    exact (hgood p hp n hn).2.1 q hq
  have hinj := products_injective P G hprime hfree
  have hcard : (goodProducts P G).card = (P.sigma G).card :=
    Finset.card_image_iff.mpr hinj
  rw [← hcard]
  exact Finset.card_le_card
    (goodProducts_subset_uniqueProducts N P G hprime hgood)

end Erdos896

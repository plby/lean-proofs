/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 534: core definitions and reductions

Let `N > 1`.  Among subsets of `{1, ..., N}` which contain `N` and whose
distinct members have gcd greater than one, Ahlswede and Khachatrian proved
that a largest set is obtained as follows.  Order the distinct prime factors
of `N`, choose a nonempty initial segment, and take the integers divisible by
twice one of those primes or by their product.

The definitions below use `N.primeFactors` directly.  Thus the formal
statement neither trusts nor needs a separately supplied factorization.

Reference: R. Ahlswede and L. H. Khachatrian, *Sets of integers with
pairwise common divisor and a factor from a specified set of primes*.
-/

namespace Erdos534

open Finset
open UniqueFactorizationMonoid

/-- The interval `{1, ..., N}`. -/
def interval (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- The admissible sets in the literal Erdős problem. -/
def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ interval N ∧
    N ∈ A ∧
    Set.Pairwise (A : Set ℕ) (fun a b ↦ 1 < Nat.gcd a b)

/-- The auxiliary class used by Ahlswede--Khachatrian.  Its members need
not contain `N`; instead every member is required to have a prime factor in
common with `N`.  Adjoining `N` turns such a family into one from the literal
problem, without decreasing its cardinality. -/
def QAdmissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ interval N ∧
    (∀ a ∈ A, 1 < Nat.gcd a N) ∧
    Set.Pairwise (A : Set ℕ) (fun a b ↦ 1 < Nat.gcd a b)

/-- A maximum-cardinality member of the finite auxiliary class. -/
def QOptimal (N : ℕ) (A : Finset ℕ) : Prop :=
  QAdmissible N A ∧ ∀ B, QAdmissible N B → B.card ≤ A.card

/-- The distinct prime factors of `N` not exceeding `q`.  When `q` itself is
a prime factor, this is the nonempty initial segment ending at `q`. -/
def primePrefix (N q : ℕ) : Finset ℕ :=
  N.primeFactors.filter (· ≤ q)

/-- The product of the initial segment of prime factors ending at `q`. -/
def prefixProduct (N q : ℕ) : ℕ :=
  ∏ p ∈ primePrefix N q, p

/-- The Ahlswede--Khachatrian candidate associated to the prime factor `q`:
an integer is selected if it is divisible by the whole prefix product or by
twice one of the primes in the prefix. -/
def candidate (N q : ℕ) : Finset ℕ :=
  (interval N).filter fun m ↦
    prefixProduct N q ∣ m ∨ ∃ p ∈ primePrefix N q, 2 * p ∣ m

/-- The primitive generators displayed in the Ahlswede--Khachatrian
candidate. -/
def candidateGenerators (N q : ℕ) : Finset ℕ :=
  insert (prefixProduct N q) ((primePrefix N q).image (2 * ·))

@[simp] lemma mem_interval {N m : ℕ} : m ∈ interval N ↔ 1 ≤ m ∧ m ≤ N := by
  simp [interval]

@[simp] lemma mem_primePrefix {N q p : ℕ} :
    p ∈ primePrefix N q ↔ p ∈ N.primeFactors ∧ p ≤ q := by
  simp [primePrefix]

@[simp] lemma mem_candidate {N q m : ℕ} :
    m ∈ candidate N q ↔
      1 ≤ m ∧ m ≤ N ∧
        (prefixProduct N q ∣ m ∨ ∃ p ∈ primePrefix N q, 2 * p ∣ m) := by
  simp [candidate, interval, and_assoc]

@[simp] lemma mem_candidateGenerators {N q g : ℕ} :
    g ∈ candidateGenerators N q ↔
      g = prefixProduct N q ∨ ∃ p ∈ primePrefix N q, 2 * p = g := by
  simp [candidateGenerators]

lemma primePrefix_subset (N q : ℕ) : primePrefix N q ⊆ N.primeFactors := by
  intro p hp
  exact (mem_primePrefix.mp hp).1

lemma mem_primePrefix_self {N q : ℕ} (hq : q ∈ N.primeFactors) :
    q ∈ primePrefix N q := by
  exact mem_primePrefix.mpr ⟨hq, le_rfl⟩

lemma prime_of_mem_primePrefix {N q p : ℕ} (hp : p ∈ primePrefix N q) :
    p.Prime := by
  exact Nat.prime_of_mem_primeFactors (primePrefix_subset N q hp)

lemma dvd_prefixProduct_of_mem {N q p : ℕ} (hp : p ∈ primePrefix N q) :
    p ∣ prefixProduct N q := by
  exact Finset.dvd_prod_of_mem id hp

lemma prefixProduct_dvd (N q : ℕ) : prefixProduct N q ∣ N := by
  exact (Finset.prod_dvd_prod_of_subset (primePrefix N q) N.primeFactors id
    (primePrefix_subset N q)).trans (Nat.prod_primeFactors_dvd N)

lemma one_lt_gcd_of_prime_dvd {p a b : ℕ} (hp : p.Prime)
    (hpa : p ∣ a) (hpb : p ∣ b) (ha : 0 < a) :
    1 < Nat.gcd a b := by
  exact hp.one_lt.trans_le
    (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left b ha) (Nat.dvd_gcd hpa hpb))

/-- Enlarging one positive argument by divisibility cannot destroy a
nontrivial gcd. -/
lemma one_lt_gcd_of_dvd_left {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ∣ b) (h : 1 < Nat.gcd a c) :
    1 < Nat.gcd b c := by
  have hdvd : Nat.gcd a c ∣ Nat.gcd b c :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left a c).trans hab) (Nat.gcd_dvd_right a c)
  exact h.trans_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left c hb) hdvd)

/-- Replacing a positive integer by its squarefree kernel preserves every
nontrivial common divisor relation. -/
lemma one_lt_gcd_radical_left {a b : ℕ} (ha : 0 < a)
    (h : 1 < Nat.gcd a b) :
    1 < Nat.gcd (radical a) b := by
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (ne_of_gt h)
  have hpa : p ∣ a := hpg.trans (Nat.gcd_dvd_left a b)
  have hpb : p ∣ b := hpg.trans (Nat.gcd_dvd_right a b)
  have hpfa : p ∈ a.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpa, ne_of_gt ha⟩
  have hpfr : p ∈ (radical a).primeFactors := by
    simpa only [Nat.primeFactors_radical] using hpfa
  exact one_lt_gcd_of_prime_dvd hp (Nat.dvd_of_mem_primeFactors hpfr) hpb
    (Nat.radical_pos a)

lemma qAdmissible_empty (N : ℕ) : QAdmissible N ∅ := by
  simp [QAdmissible]

/-- The finite auxiliary class always has a maximum member. -/
lemma exists_qOptimal (N : ℕ) : ∃ A, QOptimal N A := by
  classical
  let F : Finset (Finset ℕ) :=
    (interval N).powerset.filter fun A ↦ QAdmissible N A
  have hF : F.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [F, qAdmissible_empty]
  have hCards : (F.image Finset.card).Nonempty := hF.image _
  let M := (F.image Finset.card).max' hCards
  have hMmem : M ∈ F.image Finset.card := Finset.max'_mem _ hCards
  obtain ⟨A, hAF, hcard⟩ := Finset.mem_image.mp hMmem
  have hAF' : A ⊆ interval N ∧ QAdmissible N A := by
    simpa only [F, Finset.mem_filter, Finset.mem_powerset] using hAF
  refine ⟨A, ?_, ?_⟩
  · exact hAF'.2
  · intro B hB
    have hBF : B ∈ F := by
      simpa only [F, Finset.mem_filter, Finset.mem_powerset] using And.intro hB.1 hB
    have hBcard : B.card ∈ F.image Finset.card :=
      Finset.mem_image.mpr ⟨B, hBF, rfl⟩
    have := Finset.le_max' (F.image Finset.card) B.card hBcard
    simpa [M, hcard] using this

/-- A maximum auxiliary family is an upset in the divisibility order. -/
lemma QOptimal.upward_closed {N : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    {a b : ℕ} (ha : a ∈ A) (hab : a ∣ b) (hb1 : 1 ≤ b) (hbN : b ≤ N) :
    b ∈ A := by
  by_contra hbA
  have ha1 : 1 ≤ a := (mem_interval.mp (hA.1.1 ha)).1
  have ha_gt : 1 < a :=
    (hA.1.2.1 a ha).trans_le
      (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a N))
  have hbpos : 0 < b := hb1
  have hIns : QAdmissible N (insert b A) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact mem_interval.mpr ⟨hb1, hbN⟩
      · exact hA.1.1 hx
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact one_lt_gcd_of_dvd_left (by omega) hbpos hab (hA.1.2.1 a ha)
      · exact hA.1.2.1 x hx
    · rw [Finset.coe_insert]
      intro x hx y hy hxy
      rcases hx with hxb | hx
      · subst x
        rcases hy with hyb | hy
        · exact (hxy hyb.symm).elim
        · by_cases hya : y = a
          · subst y
            exact one_lt_gcd_of_dvd_left (by omega) hbpos hab (by simpa using ha_gt)
          · exact one_lt_gcd_of_dvd_left (by omega) hbpos hab
              (hA.1.2.2 ha hy (fun h ↦ hya h.symm))
      · rcases hy with hyb | hy
        · subst y
          rw [Nat.gcd_comm]
          by_cases hxa : x = a
          · subst x
            exact one_lt_gcd_of_dvd_left (by omega) hbpos hab (by simpa using ha_gt)
          · exact one_lt_gcd_of_dvd_left (by omega) hbpos hab
              (by rw [Nat.gcd_comm]; exact hA.1.2.2 hx ha hxa)
        · exact hA.1.2.2 hx hy hxy
  have hle := hA.2 (insert b A) hIns
  rw [Finset.card_insert_of_notMem hbA] at hle
  omega

/-- A maximum auxiliary family contains the squarefree kernel of each of
its members. -/
lemma QOptimal.radical_mem {N : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    {a : ℕ} (ha : a ∈ A) :
    radical a ∈ A := by
  have haI := mem_interval.mp (hA.1.1 ha)
  have hapos : 0 < a := by omega
  by_contra hra
  have ha_gt : 1 < a :=
    (hA.1.2.1 a ha).trans_le
      (Nat.le_of_dvd hapos (Nat.gcd_dvd_left a N))
  have hrI : radical a ∈ interval N := by
    exact mem_interval.mpr ⟨Nat.radical_pos a, (Nat.radical_le_self_iff.mpr
      (ne_of_gt hapos)).trans haI.2⟩
  have hIns : QAdmissible N (insert (radical a) A) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hrI
      · exact hA.1.1 hx
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact one_lt_gcd_radical_left hapos (hA.1.2.1 a ha)
      · exact hA.1.2.1 x hx
    · rw [Finset.coe_insert]
      intro x hx y hy hxy
      rcases hx with hxr | hx
      · subst x
        rcases hy with hyr | hy
        · exact (hxy hyr.symm).elim
        · by_cases hya : y = a
          · subst y
            exact one_lt_gcd_radical_left hapos (by simpa using ha_gt)
          · exact one_lt_gcd_radical_left hapos
              (hA.1.2.2 ha hy (fun h ↦ hya h.symm))
      · rcases hy with hyr | hy
        · subst y
          rw [Nat.gcd_comm]
          by_cases hxa : x = a
          · subst x
            exact one_lt_gcd_radical_left hapos (by simpa using ha_gt)
          · exact one_lt_gcd_radical_left hapos
              (by rw [Nat.gcd_comm]; exact hA.1.2.2 hx ha hxa)
        · exact hA.1.2.2 hx hy hxy
  have hle := hA.2 (insert (radical a) A) hIns
  rw [Finset.card_insert_of_notMem hra] at hle
  omega

/-- The divisibility-minimal members of a finite family. -/
def primitive (A : Finset ℕ) : Finset ℕ :=
  A.filter fun a ↦ ∀ b ∈ A, b ∣ a → a ∣ b

@[simp] lemma mem_primitive {A : Finset ℕ} {a : ℕ} :
    a ∈ primitive A ↔ a ∈ A ∧ ∀ b ∈ A, b ∣ a → a ∣ b := by
  simp [primitive]

/-- The upset in `[1,N]` generated by a finite set of divisors. -/
def multiplesBelow (N : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (interval N).filter fun a ↦ ∃ p ∈ P, p ∣ a

@[simp] lemma mem_multiplesBelow {N : ℕ} {P : Finset ℕ} {a : ℕ} :
    a ∈ multiplesBelow N P ↔
      1 ≤ a ∧ a ≤ N ∧ ∃ p ∈ P, p ∣ a := by
  simp [multiplesBelow, and_assoc]

/-- Every member of a positive finite family has a primitive divisor in
that family. -/
lemma exists_primitive_dvd {N : ℕ} {A : Finset ℕ}
    (hsub : A ⊆ interval N) {a : ℕ} (ha : a ∈ A) :
    ∃ p ∈ primitive A, p ∣ a := by
  let D := A.filter fun p ↦ p ∣ a
  have hD : D.Nonempty := by
    refine ⟨a, ?_⟩
    simp [D, ha]
  let p := D.min' hD
  have hpD : p ∈ D := D.min'_mem hD
  have hpA : p ∈ A := (Finset.mem_filter.mp hpD).1
  have hpdiv : p ∣ a := (Finset.mem_filter.mp hpD).2
  have hppos : 0 < p := by
    have := (mem_interval.mp (hsub hpA)).1
    omega
  refine ⟨p, mem_primitive.mpr ⟨hpA, ?_⟩, hpdiv⟩
  intro b hbA hbp
  have hbD : b ∈ D := Finset.mem_filter.mpr ⟨hbA, hbp.trans hpdiv⟩
  have hpb : p ≤ b := D.min'_le b hbD
  have hbp_le : b ≤ p := Nat.le_of_dvd hppos hbp
  have : b = p := Nat.le_antisymm hbp_le hpb
  simpa [this]

/-- A maximum auxiliary family is exactly the bounded upset generated by
its primitive members. -/
lemma QOptimal.eq_multiplesBelow_primitive {N : ℕ} {A : Finset ℕ}
    (hA : QOptimal N A) :
    A = multiplesBelow N (primitive A) := by
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨p, hp, hpa⟩ := exists_primitive_dvd hA.1.1 ha
    exact mem_multiplesBelow.mpr
      ⟨(mem_interval.mp (hA.1.1 ha)).1, (mem_interval.mp (hA.1.1 ha)).2,
        p, hp, hpa⟩
  · intro a ha
    obtain ⟨ha1, haN, p, hp, hpa⟩ := mem_multiplesBelow.mp ha
    exact hA.upward_closed (mem_primitive.mp hp).1 hpa ha1 haN

/-- Primitive generators of an optimal family are squarefree. -/
lemma QOptimal.squarefree_of_mem_primitive {N : ℕ} {A : Finset ℕ}
    (hA : QOptimal N A) {a : ℕ} (ha : a ∈ primitive A) :
    Squarefree a := by
  have haA := (mem_primitive.mp ha).1
  have hradA := hA.radical_mem haA
  have hadiv : a ∣ radical a :=
    (mem_primitive.mp ha).2 (radical a) hradA radical_dvd_self
  have heq : radical a = a := Nat.dvd_antisymm radical_dvd_self hadiv
  simpa [heq] using (squarefree_radical (a := a))

/-! ### Cardinal algebra for the two pull/replacement stages -/

/-- The part generated by `R` which is not already generated by the common
lower family `L`. -/
def generatedRemainder (N : ℕ) (L R : Finset ℕ) : Finset ℕ :=
  multiplesBelow N (L ∪ R) \ multiplesBelow N L

@[simp] lemma mem_generatedRemainder {N a : ℕ} {L R : Finset ℕ} :
    a ∈ generatedRemainder N L R ↔
      1 ≤ a ∧ a ≤ N ∧ (∃ g ∈ R, g ∣ a) ∧
        a ∉ multiplesBelow N L := by
  simp only [generatedRemainder, Finset.mem_sdiff, mem_multiplesBelow,
    Finset.mem_union]
  aesop

/-- The bounded upset generated by `L ∪ R` is the disjoint union of its
common lower part and `generatedRemainder`. -/
lemma multiplesBelow_union_eq_lower_union_remainder (N : ℕ)
    (L R : Finset ℕ) :
    multiplesBelow N (L ∪ R) =
      multiplesBelow N L ∪ generatedRemainder N L R := by
  apply Finset.ext
  intro a
  simp only [generatedRemainder, Finset.mem_union, Finset.mem_sdiff]
  have hsub : multiplesBelow N L ⊆ multiplesBelow N (L ∪ R) := by
    intro m hm
    obtain ⟨hm1, hmN, g, hg, hgm⟩ := mem_multiplesBelow.mp hm
    exact mem_multiplesBelow.mpr
      ⟨hm1, hmN, g, Finset.mem_union_left R hg, hgm⟩
  constructor
  · intro ha
    by_cases hlow : a ∈ multiplesBelow N L
    · exact Or.inl hlow
    · exact Or.inr ⟨ha, hlow⟩
  · rintro (hlow | ⟨ha, _⟩)
    · exact hsub hlow
    · exact ha

lemma disjoint_lower_generatedRemainder (N : ℕ) (L R : Finset ℕ) :
    Disjoint (multiplesBelow N L) (generatedRemainder N L R) := by
  rw [Finset.disjoint_left]
  intro a ha hrem
  exact (Finset.mem_sdiff.mp hrem).2 ha

/-- Exact cardinal decomposition for a generated bounded upset. -/
lemma card_multiplesBelow_union (N : ℕ) (L R : Finset ℕ) :
    (multiplesBelow N (L ∪ R)).card =
      (multiplesBelow N L).card + (generatedRemainder N L R).card := by
  rw [multiplesBelow_union_eq_lower_union_remainder,
    Finset.card_union_of_disjoint (disjoint_lower_generatedRemainder N L R)]

lemma generatedRemainder_union (N : ℕ) (L R S : Finset ℕ) :
    generatedRemainder N L (R ∪ S) =
      generatedRemainder N L R ∪ generatedRemainder N L S := by
  ext a
  simp only [mem_generatedRemainder, Finset.mem_union]
  aesop

/-- Pure cardinal core of both Ahlswede--Khachatrian replacement stages.
The old remainder is partitioned into two colors `R₀,R₁`; pulling one
color to `Gᵢ` supplies at least twice its old contribution.  Pull the larger
old color. -/
lemma qOptimal_of_two_pulls {N : ℕ} {A L R₀ R₁ G₀ G₁ : Finset ℕ}
    (hA : QOptimal N A)
    (hgen : A = multiplesBelow N (L ∪ (R₀ ∪ R₁)))
    (hsplit : generatedRemainder N L (R₀ ∪ R₁) =
      generatedRemainder N L R₀ ∪ generatedRemainder N L R₁)
    (hdisj : Disjoint (generatedRemainder N L R₀)
      (generatedRemainder N L R₁))
    (hB₀ : QAdmissible N (multiplesBelow N (L ∪ G₀)))
    (hB₁ : QAdmissible N (multiplesBelow N (L ∪ G₁)))
    (hdouble₀ : 2 * (generatedRemainder N L R₀).card ≤
      (generatedRemainder N L G₀).card)
    (hdouble₁ : 2 * (generatedRemainder N L R₁).card ≤
      (generatedRemainder N L G₁).card) :
    QOptimal N (multiplesBelow N (L ∪ G₀)) ∨
      QOptimal N (multiplesBelow N (L ∪ G₁)) := by
  have hcardA : A.card = (multiplesBelow N L).card +
      (generatedRemainder N L R₀).card +
      (generatedRemainder N L R₁).card := by
    rw [hgen, card_multiplesBelow_union, hsplit,
      Finset.card_union_of_disjoint hdisj]
    omega
  by_cases hle : (generatedRemainder N L R₀).card ≤
      (generatedRemainder N L R₁).card
  · right
    refine ⟨hB₁, ?_⟩
    intro B hB
    have hBA := hA.2 B hB
    rw [card_multiplesBelow_union]
    omega
  · left
    have hle' : (generatedRemainder N L R₁).card ≤
        (generatedRemainder N L R₀).card := by omega
    refine ⟨hB₀, ?_⟩
    intro B hB
    have hBA := hA.2 B hB
    rw [card_multiplesBelow_union]
    omega

/-- A bounded upset is auxiliary-admissible as soon as its displayed
generators lie in the interval, meet the endpoint, and are pairwise
noncoprime. -/
lemma qAdmissible_multiplesBelow_of_generators {N : ℕ} {P : Finset ℕ}
    (hP : P ⊆ interval N)
    (hmeet : ∀ g ∈ P, 1 < Nat.gcd g N)
    (hpair : Set.Pairwise (P : Set ℕ) (fun a b ↦ 1 < Nat.gcd a b)) :
    QAdmissible N (multiplesBelow N P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact mem_interval.mpr ⟨(mem_multiplesBelow.mp ha).1,
      (mem_multiplesBelow.mp ha).2.1⟩
  · intro a ha
    obtain ⟨ha1, _haN, g, hgP, hga⟩ := mem_multiplesBelow.mp ha
    have hgpos : 0 < g := by
      have := (mem_interval.mp (hP hgP)).1
      omega
    exact one_lt_gcd_of_dvd_left hgpos (by omega) hga (hmeet g hgP)
  · intro a ha b hb hab
    obtain ⟨ha1, _haN, g, hgP, hga⟩ := mem_multiplesBelow.mp ha
    obtain ⟨hb1, _hbN, h, hhP, hhb⟩ := mem_multiplesBelow.mp hb
    by_cases hgh : g = h
    · subst h
      have hgpos : 0 < g := by
        have := (mem_interval.mp (hP hgP)).1
        omega
      have hgone : 1 < g := (hmeet g hgP).trans_le
        (Nat.le_of_dvd hgpos (Nat.gcd_dvd_left g N))
      exact hgone.trans_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left b (by omega))
        (Nat.dvd_gcd hga hhb))
    · have hgen := hpair hgP hhP hgh
      have hgpos : 0 < g := by
        have := (mem_interval.mp (hP hgP)).1
        omega
      have hhpos : 0 < h := by
        have := (mem_interval.mp (hP hhP)).1
        omega
      have hah : 1 < Nat.gcd a h :=
        one_lt_gcd_of_dvd_left hgpos (by omega) hga hgen
      have hba : 1 < Nat.gcd b a :=
        one_lt_gcd_of_dvd_left hhpos (by omega) hhb
          (by simpa [Nat.gcd_comm] using hah)
      simpa [Nat.gcd_comm] using hba

/-- Remove the full `r`-primary part from every displayed generator. -/
def pullGenerators (r : ℕ) (R : Finset ℕ) : Finset ℕ :=
  R.image (fun g ↦ ordCompl[r] g)

@[simp] lemma mem_pullGenerators {r g : ℕ} {R : Finset ℕ} :
    g ∈ pullGenerators r R ↔ ∃ b ∈ R, ordCompl[r] b = g := by
  simp [pullGenerators]

lemma ordCompl_mul_prime_eq_of_squarefree {r g : ℕ} (hr : r.Prime)
    (hg : Squarefree g) (hrg : r ∣ g) :
    ordCompl[r] g * r = g := by
  have hfac : g.factorization r = 1 :=
    Nat.factorization_eq_one_of_squarefree hg hr hrg
  calc
    ordCompl[r] g * r = r ^ 1 * ordCompl[r] g := by simp [mul_comm]
    _ = r ^ g.factorization r * ordCompl[r] g := by rw [hfac]
    _ = g := Nat.ordProj_mul_ordCompl_eq_self g r

lemma pullGenerators_mem_interval {N r : ℕ} {R : Finset ℕ}
    (hR : R ⊆ interval N) :
    pullGenerators r R ⊆ interval N := by
  intro g hg
  obtain ⟨b, hbR, rfl⟩ := mem_pullGenerators.mp hg
  have hb := mem_interval.mp (hR hbR)
  exact mem_interval.mpr ⟨Nat.ordCompl_pos r (by omega),
    (Nat.le_of_dvd (by omega) (Nat.ordCompl_dvd b r)).trans hb.2⟩

/-- Deleting a prime outside the endpoint preserves the required common
factor with the endpoint. -/
lemma pullGenerators_meets_endpoint {N r : ℕ} {R : Finset ℕ}
    (hr : r.Prime) (hN : N ≠ 0) (hrN : r ∉ N.primeFactors)
    (hR0 : ∀ g ∈ R, g ≠ 0)
    (hmeet : ∀ g ∈ R, 1 < Nat.gcd g N) :
    ∀ g ∈ pullGenerators r R, 1 < Nat.gcd g N := by
  intro g hg
  obtain ⟨b, hbR, rfl⟩ := mem_pullGenerators.mp hg
  obtain ⟨p, hp, hpg⟩ :=
    Nat.exists_prime_and_dvd (ne_of_gt (hmeet b hbR))
  have hpb : p ∣ b := hpg.trans (Nat.gcd_dvd_left b N)
  have hpN : p ∣ N := hpg.trans (Nat.gcd_dvd_right b N)
  have hpr : ¬r ∣ p := by
    intro hrp
    rcases (Nat.dvd_prime hp).mp hrp with hr1 | hrp
    · exact hr.ne_one hr1
    · subst p
      exact hrN (Nat.mem_primeFactors.mpr ⟨hr, hpN, hN⟩)
  have hpcompl : p ∣ ordCompl[r] b :=
    Nat.dvd_ordCompl_of_dvd_not_dvd hpb hpr
  exact one_lt_gcd_of_prime_dvd hp hpcompl hpN (Nat.ordCompl_pos r (hR0 b hbR))

/-- Internal deletion preserves the endpoint condition whenever every top
generator contains a second endpoint prime. -/
lemma pullGenerators_meets_endpoint_of_other_prime {N r : ℕ}
    {R : Finset ℕ} (hr : r.Prime) (hR0 : ∀ g ∈ R, g ≠ 0)
    (hother : ∀ g ∈ R, ∃ q ∈ N.primeFactors, q ≠ r ∧ q ∣ g) :
    ∀ g ∈ pullGenerators r R, 1 < Nat.gcd g N := by
  intro g hg
  obtain ⟨b, hbR, rfl⟩ := mem_pullGenerators.mp hg
  obtain ⟨q, hqN, hqr, hqb⟩ := hother b hbR
  have hq := Nat.prime_of_mem_primeFactors hqN
  have hrq : ¬r ∣ q := by
    intro h
    rcases (Nat.dvd_prime hq).mp h with hr1 | hrq'
    · exact hr.ne_one hr1
    · exact hqr hrq'.symm
  exact one_lt_gcd_of_prime_dvd hq
    (Nat.dvd_ordCompl_of_dvd_not_dvd hqb hrq)
    (Nat.dvd_of_mem_primeFactors hqN)
    (Nat.ordCompl_pos r (hR0 b hbR))

/-- If every generator in a color class contains a common prime `c ≠ r`,
then that class remains pairwise noncoprime after deleting `r`. -/
lemma pullGenerators_pairwise_of_common_prime {r c : ℕ} {R : Finset ℕ}
    (hr : r.Prime) (hc : c.Prime) (hrc : r ≠ c)
    (hR0 : ∀ g ∈ R, g ≠ 0) (hcR : ∀ g ∈ R, c ∣ g) :
    Set.Pairwise (pullGenerators r R : Set ℕ)
      (fun a b ↦ 1 < Nat.gcd a b) := by
  have hrcDvd : ¬r ∣ c := by
    intro h
    rcases (Nat.dvd_prime hc).mp h with hr1 | hrc'
    · exact hr.ne_one hr1
    · exact hrc hrc'
  intro a ha b hb _hab
  obtain ⟨g, hgR, rfl⟩ := mem_pullGenerators.mp ha
  obtain ⟨h, hhR, rfl⟩ := mem_pullGenerators.mp hb
  exact one_lt_gcd_of_prime_dvd hc
    (Nat.dvd_ordCompl_of_dvd_not_dvd (hcR g hgR) hrcDvd)
    (Nat.dvd_ordCompl_of_dvd_not_dvd (hcR h hhR) hrcDvd)
    (Nat.ordCompl_pos r (hR0 g hgR))

/-- Cross gcds between a lower generator and a top generator survive
deletion of the top prime, provided the lower generator does not contain it. -/
lemma one_lt_gcd_pullGenerator_of_cross {r l g : ℕ} (hr : r.Prime)
    (hl0 : l ≠ 0) (hg0 : g ≠ 0) (hrg : r ∣ g) (hrl : ¬r ∣ l)
    (hcross : 1 < Nat.gcd l g) :
    1 < Nat.gcd l (ordCompl[r] g) := by
  obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hcross)
  have hpl : p ∣ l := hpgcd.trans (Nat.gcd_dvd_left l g)
  have hpg : p ∣ g := hpgcd.trans (Nat.gcd_dvd_right l g)
  have hrp : ¬r ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with hr1 | hrp'
    · exact hr.ne_one hr1
    · exact hrl (hrp' ▸ hpl)
  have hpcompl : p ∣ ordCompl[r] g :=
    Nat.dvd_ordCompl_of_dvd_not_dvd hpg hrp
  exact one_lt_gcd_of_prime_dvd hp hpl hpcompl (Nat.pos_of_ne_zero hl0)

lemma QOptimal.primitive_pairwise {N : ℕ} {A : Finset ℕ}
    (hA : QOptimal N A) :
    Set.Pairwise (primitive A : Set ℕ) (fun a b ↦ 1 < Nat.gcd a b) := by
  intro a ha b hb hab
  exact hA.1.2.2 (mem_primitive.mp ha).1 (mem_primitive.mp hb).1 hab

lemma QOptimal.primitive_meets_N {N : ℕ} {A : Finset ℕ}
    (hA : QOptimal N A) {a : ℕ} (ha : a ∈ primitive A) :
    1 < Nat.gcd a N :=
  hA.1.2.1 a (mem_primitive.mp ha).1

/-- Literal admissibility implies auxiliary admissibility once `N > 1`. -/
lemma QAdmissible.of_admissible {N : ℕ} {A : Finset ℕ} (hN : 1 < N)
    (hA : Admissible N A) :
    QAdmissible N A := by
  refine ⟨hA.1, ?_, hA.2.2⟩
  intro a ha
  by_cases haN : a = N
  · subst a
    simpa using hN
  · exact hA.2.2 ha hA.2.1 haN

/-- Conversely, adjoining `N` to an auxiliary family gives a family from
the literal problem. -/
lemma QAdmissible.adjoin_N {N : ℕ} {A : Finset ℕ} (hA : QAdmissible N A)
    (hN : 1 ≤ N) :
    Admissible N (insert N A) := by
  refine ⟨?_, Finset.mem_insert_self N A, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact mem_interval.mpr ⟨hN, le_rfl⟩
    · exact hA.1 ha
  · rw [Finset.coe_insert]
    intro a ha b hb hab
    rcases ha with haN | ha
    · subst a
      rcases hb with hbN | hb
      · exact (hab hbN.symm).elim
      · rw [Nat.gcd_comm]
        exact hA.2.1 b hb
    · rcases hb with hbN | hb
      · subst b
        exact hA.2.1 a ha
      · exact hA.2.2 ha hb hab

/-! ### Prime-power left replacement -/

/-- Replace the full `q`-primary part of `n` by the same power of `p`.
The operation is used only when `p,q` are distinct primes, `q ∣ n`, and
`p ∤ n`. -/
def primePowerReplace (p q n : ℕ) : ℕ :=
  ordCompl[q] n * p ^ n.factorization q

lemma primePowerReplace_ne_zero {p q n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    primePowerReplace p q n ≠ 0 := by
  exact mul_ne_zero (Nat.ordCompl_pos q hn).ne' (pow_ne_zero _ hp.ne_zero)

lemma primePowerReplace_factorization {p q n : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) :
    (primePowerReplace p q n).factorization =
      n.factorization.erase q + Finsupp.single p (n.factorization q) := by
  rw [primePowerReplace, Nat.factorization_mul (Nat.ordCompl_pos q hn).ne'
    (pow_ne_zero _ hp.ne_zero), Nat.factorization_ordCompl,
    hp.factorization_pow]

lemma primePowerReplace_factorization_apply {p q n r : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) :
    (primePowerReplace p q n).factorization r =
      (n.factorization.erase q) r + if p = r then n.factorization q else 0 := by
  rw [primePowerReplace_factorization hp hn]
  simp [Finsupp.single_apply]

lemma primePowerReplace_lt {p q n : ℕ} (hpq : p < q) (hq : q.Prime)
    (hn : n ≠ 0) (hqn : q ∣ n) :
    primePowerReplace p q n < n := by
  have hk : 0 < n.factorization q := hq.factorization_pos_of_dvd hn hqn
  have hpow : p ^ n.factorization q < q ^ n.factorization q :=
    Nat.pow_lt_pow_left hpq (by omega)
  have hc : 0 < ordCompl[q] n := Nat.ordCompl_pos q hn
  calc
    primePowerReplace p q n
        < ordCompl[q] n * q ^ n.factorization q :=
          Nat.mul_lt_mul_of_pos_left hpow hc
    _ = n := by
      rw [mul_comm]
      exact Nat.ordProj_mul_ordCompl_eq_self n q

lemma prime_dvd_primePowerReplace_iff {p q n r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q) (hn : n ≠ 0)
    (hpn : ¬p ∣ n) (hqn : q ∣ n) :
    r ∣ primePowerReplace p q n ↔ r = p ∨ (r ≠ q ∧ r ∣ n) := by
  rw [hr.dvd_iff_one_le_factorization (primePowerReplace_ne_zero hp hn),
    primePowerReplace_factorization_apply hp hn]
  have hfp : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
  have hfq : 0 < n.factorization q := hq.factorization_pos_of_dvd hn hqn
  by_cases hrp : r = p
  · subst r
    simp [hfp, hpq]
    omega
  · have hpr : p ≠ r := fun h ↦ hrp h.symm
    simp only [hpr, if_false, add_zero]
    by_cases hrq : r = q
    · subst r
      have hqp : q ≠ p := fun h ↦ hpq h.symm
      simp [hqp]
    · rw [Finsupp.erase_ne hrq]
      rw [hr.dvd_iff_one_le_factorization hn]
      simp [hrp, hrq]

lemma primePowerReplace_inverse {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hn : n ≠ 0) (hpn : ¬p ∣ n) :
    primePowerReplace q p (primePowerReplace p q n) = n := by
  let c := ordCompl[q] n
  let k := n.factorization q
  have hpc : ¬p ∣ c := fun h ↦ hpn (h.trans (Nat.ordCompl_dvd n q))
  have hfac : (primePowerReplace p q n).factorization p = k := by
    rw [primePowerReplace_factorization_apply hp hn]
    simp [c, k, hpq, Nat.factorization_eq_zero_of_not_dvd hpn]
  have hcompl : ordCompl[p] (primePowerReplace p q n) = c := by
    rw [primePowerReplace, show ordCompl[q] n = c from rfl,
      show n.factorization q = k from rfl, mul_comm]
    exact Nat.ordCompl_pow_mul_of_not_dvd k hp hpc
  change ordCompl[p] (primePowerReplace p q n) *
    q ^ (primePowerReplace p q n).factorization p = n
  rw [hcompl, hfac]
  change ordCompl[q] n * q ^ n.factorization q = n
  rw [mul_comm]
  exact Nat.ordProj_mul_ordCompl_eq_self n q

/-- On the squarefree number `2*q`, left replacement simply changes the
prime `q` to `p`. -/
lemma primePowerReplace_two_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hq2 : q ≠ 2) :
    primePowerReplace p q (2 * q) = 2 * p := by
  have hqdvd2 : ¬q ∣ 2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
    · exact hq.ne_one h
    · exact hq2 h
  rw [primePowerReplace]
  have hcompl : ordCompl[q] (2 * q) = 2 := by
    rw [show 2 * q = q ^ 1 * 2 by simp [mul_comm],
      Nat.ordCompl_pow_mul_of_not_dvd 1 hq hqdvd2]
  have hfac : (2 * q).factorization q = 1 := by
    rw [Nat.factorization_mul (by norm_num) hq.ne_zero]
    simp [Nat.factorization_eq_zero_of_not_dvd hqdvd2, hq.factorization]
  rw [hcompl, hfac, pow_one]

/-- The members actually moved by a left-compression. -/
def movingPart (p q : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter fun n ↦ q ∣ n ∧ ¬p ∣ n ∧ primePowerReplace p q n ∉ A

@[simp] lemma mem_movingPart {p q n : ℕ} {A : Finset ℕ} :
    n ∈ movingPart p q A ↔
      n ∈ A ∧ q ∣ n ∧ ¬p ∣ n ∧ primePowerReplace p q n ∉ A := by
  simp [movingPart, and_assoc]

/-- Cardinality-preserving left compression of a finite integer family. -/
def leftCompress (p q : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A \ movingPart p q A) ∪
    (movingPart p q A).image (primePowerReplace p q)

lemma movingPart_subset (p q : ℕ) (A : Finset ℕ) :
    movingPart p q A ⊆ A := by
  exact Finset.filter_subset _ _

lemma leftCompress_card {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {A : Finset ℕ} (hpos : ∀ n ∈ A, n ≠ 0) :
    (leftCompress p q A).card = A.card := by
  classical
  let M := movingPart p q A
  have hMsub : M ⊆ A := movingPart_subset p q A
  have hinj : Set.InjOn (primePowerReplace p q) (M : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := mem_movingPart.mp hx
    have hy' := mem_movingPart.mp hy
    calc
      x = primePowerReplace q p (primePowerReplace p q x) :=
        (primePowerReplace_inverse hp hq hpq (hpos x hx'.1) hx'.2.2.1).symm
      _ = primePowerReplace q p (primePowerReplace p q y) := congrArg _ hxy
      _ = y := primePowerReplace_inverse hp hq hpq (hpos y hy'.1) hy'.2.2.1
  have hdisj : Disjoint (A \ M) (M.image (primePowerReplace p q)) := by
    rw [Finset.disjoint_left]
    intro x hxA hximg
    obtain ⟨m, hmM, rfl⟩ := Finset.mem_image.mp hximg
    have hm := mem_movingPart.mp hmM
    exact hm.2.2.2 (Finset.mem_sdiff.mp hxA).1
  calc
    (leftCompress p q A).card
        = (A \ M).card + (M.image (primePowerReplace p q)).card := by
          rw [leftCompress, show movingPart p q A = M from rfl,
            Finset.card_union_of_disjoint hdisj]
    _ = (A.card - M.card) + M.card := by
      rw [Finset.card_sdiff_of_subset hMsub, Finset.card_image_of_injOn hinj]
    _ = A.card := Nat.sub_add_cancel (Finset.card_le_card hMsub)

lemma mem_leftCompress_iff {p q n : ℕ} {A : Finset ℕ} :
    n ∈ leftCompress p q A ↔
      (n ∈ A ∧ n ∉ movingPart p q A) ∨
        ∃ m ∈ movingPart p q A, primePowerReplace p q m = n := by
  simp [leftCompress]

/-- Exactly the shifts allowed by the `Q`-condition: either both primes
divide `N`, or the removed prime does not divide `N`. -/
def AllowedShift (N p q : ℕ) : Prop :=
  (p ∈ N.primeFactors ∧ q ∈ N.primeFactors) ∨ q ∉ N.primeFactors

lemma allowedShift_preserves_common_factor {N p q n : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hN : N ≠ 0) (hn : n ≠ 0) (hpn : ¬p ∣ n)
    (hqn : q ∣ n) (hallow : AllowedShift N p q)
    (hcommon : 1 < Nat.gcd n N) :
    1 < Nat.gcd (primePowerReplace p q n) N := by
  rcases hallow with hboth | hqN
  · exact one_lt_gcd_of_prime_dvd hp
      ((prime_dvd_primePowerReplace_iff hp hq hp hpq hn hpn hqn).mpr (Or.inl rfl))
      (Nat.dvd_of_mem_primeFactors hboth.1)
      (Nat.pos_of_ne_zero (primePowerReplace_ne_zero hp hn))
  · obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd (ne_of_gt hcommon)
    have hrn : r ∣ n := hrg.trans (Nat.gcd_dvd_left n N)
    have hrN : r ∣ N := hrg.trans (Nat.gcd_dvd_right n N)
    have hrq : r ≠ q := by
      intro h
      subst r
      exact hqN (Nat.mem_primeFactors.mpr ⟨hq, hrN, hN⟩)
    exact one_lt_gcd_of_prime_dvd hr
      ((prime_dvd_primePowerReplace_iff hp hq hr hpq hn hpn hqn).mpr
      (Or.inr ⟨hrq, hrn⟩)) hrN
      (Nat.pos_of_ne_zero (primePowerReplace_ne_zero hp hn))

lemma exists_prime_dvd_both_of_one_lt_gcd {a b : ℕ}
    (h : 1 < Nat.gcd a b) :
    ∃ r, r.Prime ∧ r ∣ a ∧ r ∣ b := by
  obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd (ne_of_gt h)
  exact ⟨r, hr, hrg.trans (Nat.gcd_dvd_left a b),
    hrg.trans (Nat.gcd_dvd_right a b)⟩

lemma replacements_have_common_factor {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpa : ¬p ∣ a) (hpb : ¬p ∣ b) (hqa : q ∣ a) (hqb : q ∣ b)
    (hab : 1 < Nat.gcd a b) :
    1 < Nat.gcd (primePowerReplace p q a) (primePowerReplace p q b) := by
  obtain ⟨r, hr, hra, hrb⟩ := exists_prime_dvd_both_of_one_lt_gcd hab
  by_cases hrq : r = q
  · subst r
    have hpra : p ∣ primePowerReplace p q a :=
      (prime_dvd_primePowerReplace_iff hp hq hp hpq ha hpa hqa).mpr (Or.inl rfl)
    have hprb : p ∣ primePowerReplace p q b :=
      (prime_dvd_primePowerReplace_iff hp hq hp hpq hb hpb hqb).mpr (Or.inl rfl)
    exact one_lt_gcd_of_prime_dvd hp hpra hprb
      (Nat.pos_of_ne_zero (primePowerReplace_ne_zero hp ha))
  · exact one_lt_gcd_of_prime_dvd hr
      ((prime_dvd_primePowerReplace_iff hp hq hr hpq ha hpa hqa).mpr
        (Or.inr ⟨hrq, hra⟩))
      ((prime_dvd_primePowerReplace_iff hp hq hr hpq hb hpb hqb).mpr
        (Or.inr ⟨hrq, hrb⟩))
      (Nat.pos_of_ne_zero (primePowerReplace_ne_zero hp ha))

/-- The mixed case in the standard paired-collision proof for a left
compression. -/
lemma replacement_and_unmoved_have_common_factor {N p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {A : Finset ℕ}
    (hA : QAdmissible N A) (haM : a ∈ movingPart p q A)
    (hbA : b ∈ A) (hbM : b ∉ movingPart p q A) (hab : a ≠ b) :
    1 < Nat.gcd (primePowerReplace p q a) b := by
  have ha' := mem_movingPart.mp haM
  have ha0 : a ≠ 0 := by
    have := (mem_interval.mp (hA.1 ha'.1)).1
    omega
  have hb0 : b ≠ 0 := by
    have := (mem_interval.mp (hA.1 hbA)).1
    omega
  obtain ⟨r, hr, hra, hrb⟩ :=
    exists_prime_dvd_both_of_one_lt_gcd (hA.2.2 ha'.1 hbA hab)
  by_cases hrq : r = q
  · subst r
    by_cases hpb : p ∣ b
    · exact one_lt_gcd_of_prime_dvd hp
        ((prime_dvd_primePowerReplace_iff hp hq hp hpq ha0 ha'.2.2.1 ha'.2.1).mpr
          (Or.inl rfl)) hpb
        (Nat.pos_of_ne_zero (primePowerReplace_ne_zero hp ha0))
    · have hRbA : primePowerReplace p q b ∈ A := by
        by_contra hRb
        exact hbM (mem_movingPart.mpr ⟨hbA, hrb, hpb, hRb⟩)
      have hpRb : p ∣ primePowerReplace p q b :=
        (prime_dvd_primePowerReplace_iff hp hq hp hpq hb0 hpb hrb).mpr (Or.inl rfl)
      have haneRb : a ≠ primePowerReplace p q b := by
        intro h
        exact ha'.2.2.1 (h ▸ hpRb)
      obtain ⟨s, hs, hsa, hsRb⟩ := exists_prime_dvd_both_of_one_lt_gcd
        (hA.2.2 ha'.1 hRbA haneRb)
      have hsp : s ≠ p := fun h ↦ ha'.2.2.1 (h ▸ hsa)
      have hqRb : ¬q ∣ primePowerReplace p q b := by
        rw [prime_dvd_primePowerReplace_iff hp hq hq hpq hb0 hpb hrb]
        exact fun h ↦ h.elim (fun hqp ↦ hpq hqp.symm) (fun h ↦ h.1 rfl)
      have hsq : s ≠ q := fun h ↦ hqRb (h ▸ hsRb)
      have hsb : s ∣ b := by
        have := (prime_dvd_primePowerReplace_iff hp hq hs hpq hb0 hpb hrb).mp hsRb
        rcases this with h | h
        · exact (hsp h).elim
        · exact h.2
      exact one_lt_gcd_of_prime_dvd hs
        ((prime_dvd_primePowerReplace_iff hp hq hs hpq ha0 ha'.2.2.1 ha'.2.1).mpr
          (Or.inr ⟨hsq, hsa⟩)) hsb
        (Nat.pos_of_ne_zero (primePowerReplace_ne_zero hp ha0))
  · exact one_lt_gcd_of_prime_dvd hr
      ((prime_dvd_primePowerReplace_iff hp hq hr hpq ha0 ha'.2.2.1 ha'.2.1).mpr
        (Or.inr ⟨hrq, hra⟩)) hrb
      (Nat.pos_of_ne_zero (primePowerReplace_ne_zero hp ha0))

/-- Every allowed left compression preserves the auxiliary admissibility
conditions and cardinality. -/
theorem leftCompress_qAdmissible {N p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hallow : AllowedShift N p q) {A : Finset ℕ}
    (hA : QAdmissible N A) :
    QAdmissible N (leftCompress p q A) ∧
      (leftCompress p q A).card = A.card := by
  have hne : p ≠ q := ne_of_lt hpq
  have hpos : ∀ n ∈ A, n ≠ 0 := by
    intro n hn
    exact Nat.ne_of_gt (by have := (mem_interval.mp (hA.1 hn)).1; omega)
  refine ⟨⟨?_, ?_, ?_⟩, leftCompress_card hp hq hne hpos⟩
  · intro n hn
    rcases mem_leftCompress_iff.mp hn with hn | ⟨m, hm, rfl⟩
    · exact hA.1 hn.1
    · have hm' := mem_movingPart.mp hm
      have hmI := mem_interval.mp (hA.1 hm'.1)
      exact mem_interval.mpr ⟨Nat.one_le_iff_ne_zero.mpr
        (primePowerReplace_ne_zero hp (hpos m hm'.1)),
        (primePowerReplace_lt hpq hq (hpos m hm'.1) hm'.2.1).le.trans hmI.2⟩
  · intro n hn
    rcases mem_leftCompress_iff.mp hn with hn | ⟨m, hm, rfl⟩
    · exact hA.2.1 n hn.1
    · have hm' := mem_movingPart.mp hm
      have hN0 : N ≠ 0 := by
        have hmI := mem_interval.mp (hA.1 hm'.1)
        omega
      exact allowedShift_preserves_common_factor hp hq hne hN0 (hpos m hm'.1)
        hm'.2.2.1 hm'.2.1 hallow (hA.2.1 m hm'.1)
  · intro x hx y hy hxy
    rcases mem_leftCompress_iff.mp hx with hx | ⟨a, haM, hax⟩ <;>
      rcases mem_leftCompress_iff.mp hy with hy | ⟨b, hbM, hby⟩
    · exact hA.2.2 hx.1 hy.1 hxy
    · subst y
      rw [Nat.gcd_comm]
      exact replacement_and_unmoved_have_common_factor hp hq hne hA hbM hx.1 hx.2
        (fun h ↦ hx.2 (h ▸ hbM))
    · subst x
      exact replacement_and_unmoved_have_common_factor hp hq hne hA haM hy.1 hy.2
        (fun h ↦ hy.2 (h ▸ haM))
    · subst x
      subst y
      have hab : a ≠ b := fun h ↦ hxy (by subst b; rfl)
      have ha' := mem_movingPart.mp haM
      have hb' := mem_movingPart.mp hbM
      exact replacements_have_common_factor hp hq hne (hpos a ha'.1) (hpos b hb'.1)
        ha'.2.2.1 hb'.2.2.1 ha'.2.1 hb'.2.1 (hA.2.2 ha'.1 hb'.1 hab)

/-- A strictly decreasing integer weight used to choose a simultaneously
left-compressed optimum. -/
def familyWeight (A : Finset ℕ) : ℕ := ∑ a ∈ A, a

lemma leftCompress_weight_lt {N p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) {A : Finset ℕ} (hsub : A ⊆ interval N)
    (hne : leftCompress p q A ≠ A) :
    familyWeight (leftCompress p q A) < familyWeight A := by
  classical
  let M := movingPart p q A
  have hMsub : M ⊆ A := movingPart_subset p q A
  have hM : M.Nonempty := by
    by_contra hM
    have hMe : M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hM
    apply hne
    simp [leftCompress, M, hMe]
  have hpos : ∀ n ∈ A, n ≠ 0 := by
    intro n hn
    have := (mem_interval.mp (hsub hn)).1
    omega
  have hinj : Set.InjOn (primePowerReplace p q) (M : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := mem_movingPart.mp hx
    have hy' := mem_movingPart.mp hy
    have hpqne : p ≠ q := ne_of_lt hpq
    calc
      x = primePowerReplace q p (primePowerReplace p q x) :=
        (primePowerReplace_inverse hp hq hpqne (hpos x hx'.1) hx'.2.2.1).symm
      _ = primePowerReplace q p (primePowerReplace p q y) := congrArg _ hxy
      _ = y := primePowerReplace_inverse hp hq hpqne (hpos y hy'.1) hy'.2.2.1
  have hdisj : Disjoint (A \ M) (M.image (primePowerReplace p q)) := by
    rw [Finset.disjoint_left]
    intro x hxA hximg
    obtain ⟨m, hmM, rfl⟩ := Finset.mem_image.mp hximg
    exact (mem_movingPart.mp hmM).2.2.2 (Finset.mem_sdiff.mp hxA).1
  have hstrict : (∑ m ∈ M, primePowerReplace p q m) < ∑ m ∈ M, m := by
    exact Finset.sum_lt_sum_of_nonempty hM fun m hm ↦
      primePowerReplace_lt hpq hq (hpos m (hMsub hm)) (mem_movingPart.mp hm).2.1
  rw [familyWeight, familyWeight, leftCompress,
    show movingPart p q A = M from rfl, Finset.sum_union hdisj,
    Finset.sum_image hinj, ← Finset.sum_sdiff hMsub]
  exact Nat.add_lt_add_left hstrict _

/-- There is an optimum fixed by every allowed prime-power left
compression. -/
theorem exists_leftCompressed_qOptimal (N : ℕ) :
    ∃ A, QOptimal N A ∧
      ∀ p q, p.Prime → q.Prime → p < q → AllowedShift N p q →
        leftCompress p q A = A := by
  classical
  let F : Finset (Finset ℕ) :=
    (interval N).powerset.filter fun A ↦ QOptimal N A
  obtain ⟨A₀, hA₀⟩ := exists_qOptimal N
  have hF : F.Nonempty := by
    refine ⟨A₀, ?_⟩
    simpa only [F, Finset.mem_filter, Finset.mem_powerset] using And.intro hA₀.1.1 hA₀
  have hWeights : (F.image familyWeight).Nonempty := hF.image _
  let w := (F.image familyWeight).min' hWeights
  have hwmem : w ∈ F.image familyWeight := Finset.min'_mem _ hWeights
  obtain ⟨A, hAF, hAw⟩ := Finset.mem_image.mp hwmem
  have hA : QOptimal N A := by
    have := Finset.mem_filter.mp (show A ∈
      (interval N).powerset.filter (QOptimal N) by simpa only [F] using hAF)
    exact this.2
  refine ⟨A, hA, ?_⟩
  intro p q hp hq hpq hallow
  by_contra hne
  have hcomp := leftCompress_qAdmissible hp hq hpq hallow hA.1
  have hcompOpt : QOptimal N (leftCompress p q A) := by
    refine ⟨hcomp.1, ?_⟩
    intro B hB
    simpa [hcomp.2] using hA.2 B hB
  have hcompF : leftCompress p q A ∈ F := by
    simpa only [F, Finset.mem_filter, Finset.mem_powerset] using
      And.intro hcompOpt.1.1 hcompOpt
  have hcompWeightMem : familyWeight (leftCompress p q A) ∈ F.image familyWeight :=
    Finset.mem_image.mpr ⟨leftCompress p q A, hcompF, rfl⟩
  have hwle := Finset.min'_le (F.image familyWeight)
    (familyWeight (leftCompress p q A)) hcompWeightMem
  have hlt := leftCompress_weight_lt hp hq hpq hA.1.1 hne
  rw [hAw] at hlt
  have hwle' : w ≤ familyWeight (leftCompress p q A) := by
    simpa only [w] using hwle
  exact (not_lt_of_ge hwle') hlt

/-- In a family fixed by a left compression, every eligible element already
has its prime-power replacement in the family. -/
lemma primePowerReplace_mem_of_fixed {p q a : ℕ} {A : Finset ℕ}
    (hfix : leftCompress p q A = A) (ha : a ∈ A) (hqa : q ∣ a)
    (hpa : ¬p ∣ a) :
    primePowerReplace p q a ∈ A := by
  by_contra hnot
  have haM : a ∈ movingPart p q A :=
    mem_movingPart.mpr ⟨ha, hqa, hpa, hnot⟩
  have hmem : primePowerReplace p q a ∈ leftCompress p q A :=
    mem_leftCompress_iff.mpr (Or.inr ⟨a, haM, rfl⟩)
  rw [hfix] at hmem
  exact hnot hmem

/-- The chosen optimum is closed under every allowed prime-power replacement. -/
lemma QOptimal.primePowerReplace_mem {N p q a : ℕ} {A : Finset ℕ}
    (hA : QOptimal N A)
    (hfix : ∀ p q, p.Prime → q.Prime → p < q → AllowedShift N p q →
      leftCompress p q A = A)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hallow : AllowedShift N p q) (ha : a ∈ A) (hqa : q ∣ a)
    (hpa : ¬p ∣ a) :
    primePowerReplace p q a ∈ A := by
  exact primePowerReplace_mem_of_fixed
    (hfix p q hp hq hpq hallow) ha hqa hpa

lemma primePowerReplace_eq_ordCompl_mul_of_squarefree {p q n : ℕ}
    (hq : q.Prime) (hn : Squarefree n) (hqn : q ∣ n) :
    primePowerReplace p q n = ordCompl[q] n * p := by
  simp [primePowerReplace, Nat.factorization_eq_one_of_squarefree hn hq hqn]

/-- In the color class avoiding `c`, compressedness supplies the missing
pairwise gcd after the top prime `r` is deleted. -/
lemma QOptimal.pullGenerators_pairwise_of_compressed_avoids
    {N c r : ℕ} {A R : Finset ℕ} (hA : QOptimal N A)
    (hfix : ∀ p q, p.Prime → q.Prime → p < q → AllowedShift N p q →
      leftCompress p q A = A)
    (hc : c.Prime) (hr : r.Prime) (hcr : c < r)
    (hallow : AllowedShift N c r)
    (hR : R ⊆ primitive A) (hrR : ∀ g ∈ R, r ∣ g)
    (hcR : ∀ g ∈ R, ¬c ∣ g) :
    Set.Pairwise (pullGenerators r R : Set ℕ)
      (fun a b ↦ 1 < Nat.gcd a b) := by
  intro x hx y hy hxy
  obtain ⟨g, hgR, hgx⟩ := mem_pullGenerators.mp hx
  obtain ⟨h, hhR, hhy⟩ := mem_pullGenerators.mp hy
  have hgP := hR hgR
  have hhP := hR hhR
  have hgA := (mem_primitive.mp hgP).1
  have hhA := (mem_primitive.mp hhP).1
  have hg0 : g ≠ 0 := by
    have := (mem_interval.mp (hA.1.1 hgA)).1
    omega
  have hh0 : h ≠ 0 := by
    have := (mem_interval.mp (hA.1.1 hhA)).1
    omega
  have hgSq := hA.squarefree_of_mem_primitive hgP
  have hhSq := hA.squarefree_of_mem_primitive hhP
  have hgh : g ≠ h := by
    intro hEq
    apply hxy
    rw [← hgx, ← hhy, hEq]
  have hrep : primePowerReplace c r g ∈ A :=
    hA.primePowerReplace_mem hfix hc hr hcr hallow hgA (hrR g hgR) (hcR g hgR)
  have hrepEq : primePowerReplace c r g = ordCompl[r] g * c :=
    primePowerReplace_eq_ordCompl_mul_of_squarefree hr hgSq (hrR g hgR)
  obtain ⟨p, hp, hpRep, hpH⟩ := exists_prime_dvd_both_of_one_lt_gcd
    (hA.1.2.2 hrep hhA (by
      intro hEq
      have hrg : r ∣ g := hrR g hgR
      have hrRep : ¬r ∣ primePowerReplace c r g := by
        rw [prime_dvd_primePowerReplace_iff hc hr hr hcr.ne hg0 (hcR g hgR)
          hrg]
        exact fun hcase ↦ hcase.elim (fun hrc ↦ hcr.ne hrc.symm)
          (fun hrest ↦ hrest.1 rfl)
      exact hrRep (hEq ▸ hrR h hhR)))
  rw [hrepEq] at hpRep
  have hhEq : ordCompl[r] h * r = h :=
    ordCompl_mul_prime_eq_of_squarefree hr hhSq (hrR h hhR)
  rw [← hhEq] at hpH
  rcases hp.dvd_mul.mp hpRep with hpx | hpc <;>
    rcases hp.dvd_mul.mp hpH with hpy | hpr
  · rw [← hgx, ← hhy]
    exact one_lt_gcd_of_prime_dvd hp hpx hpy
      (Nat.ordCompl_pos r hg0)
  · have hprEq : p = r := by
      rcases (Nat.dvd_prime hr).mp hpr with hp1 | hpr'
      · exact (hp.ne_one hp1).elim
      · exact hpr'
    subst p
    exact ((Nat.not_dvd_ordCompl hr hg0) hpx).elim
  · have hpcEq : p = c := by
      rcases (Nat.dvd_prime hc).mp hpc with hp1 | hpc'
      · exact (hp.ne_one hp1).elim
      · exact hpc'
    subst p
    exact (hcR h hhR (hpy.trans (Nat.ordCompl_dvd h r))).elim
  · have hpcEq : p = c := by
      rcases (Nat.dvd_prime hc).mp hpc with hp1 | hpc'
      · exact (hp.ne_one hp1).elim
      · exact hpc'
    have hprEq : p = r := by
      rcases (Nat.dvd_prime hr).mp hpr with hp1 | hpr'
      · exact (hp.ne_one hp1).elim
      · exact hpr'
    exact (hcr.ne (hpcEq.symm.trans hprEq)).elim

/-- Generator-level admissibility of an external-prime pull.  Pairwise gcds
inside the pulled class are supplied separately by the two color lemmas. -/
lemma QOptimal.qAdmissible_pull_external {N r : ℕ} {A L R : Finset ℕ}
    (hA : QOptimal N A) (hN : N ≠ 0) (hr : r.Prime)
    (hrN : r ∉ N.primeFactors)
    (hL : L ⊆ primitive A) (hR : R ⊆ primitive A)
    (hrL : ∀ g ∈ L, ¬r ∣ g) (hrR : ∀ g ∈ R, r ∣ g)
    (hpairPull : Set.Pairwise (pullGenerators r R : Set ℕ)
      (fun a b ↦ 1 < Nat.gcd a b)) :
    QAdmissible N (multiplesBelow N (L ∪ pullGenerators r R)) := by
  have hLInterval : L ⊆ interval N := fun g hg ↦
    hA.1.1 (mem_primitive.mp (hL hg)).1
  have hRInterval : R ⊆ interval N := fun g hg ↦
    hA.1.1 (mem_primitive.mp (hR hg)).1
  have hR0 : ∀ g ∈ R, g ≠ 0 := by
    intro g hg
    have := (mem_interval.mp (hRInterval hg)).1
    omega
  apply qAdmissible_multiplesBelow_of_generators
  · intro g hg
    rcases Finset.mem_union.mp hg with hgL | hgPull
    · exact hLInterval hgL
    · exact pullGenerators_mem_interval hRInterval hgPull
  · intro g hg
    rcases Finset.mem_union.mp hg with hgL | hgPull
    · exact hA.primitive_meets_N (hL hgL)
    · exact pullGenerators_meets_endpoint hr hN hrN hR0
        (fun b hb ↦ hA.primitive_meets_N (hR hb)) g hgPull
  · intro g hg h hh hgh
    rcases Finset.mem_union.mp hg with hgL | hgPull <;>
      rcases Finset.mem_union.mp hh with hhL | hhPull
    · exact hA.primitive_pairwise (hL hgL) (hL hhL) hgh
    · obtain ⟨b, hbR, rfl⟩ := mem_pullGenerators.mp hhPull
      have hgb : g ≠ b := by
        intro hEq
        exact hrL g hgL (hEq ▸ hrR b hbR)
      exact one_lt_gcd_pullGenerator_of_cross hr
        (by have := (mem_interval.mp (hLInterval hgL)).1; omega)
        (hR0 b hbR) (hrR b hbR) (hrL g hgL)
        (hA.primitive_pairwise (hL hgL) (hR hbR) hgb)
    · obtain ⟨b, hbR, rfl⟩ := mem_pullGenerators.mp hgPull
      rw [Nat.gcd_comm]
      have hhb : h ≠ b := by
        intro hEq
        exact hrL h hhL (hEq ▸ hrR b hbR)
      exact one_lt_gcd_pullGenerator_of_cross hr
        (by have := (mem_interval.mp (hLInterval hhL)).1; omega)
        (hR0 b hbR) (hrR b hbR) (hrL h hhL)
        (hA.primitive_pairwise (hL hhL) (hR hbR) hhb)
    · exact hpairPull hgPull hhPull hgh

/-- Internal-prime version of the preceding admissibility lemma.  Here the
fact that deleting `r` leaves another endpoint prime is supplied explicitly
as `hmeetPull`. -/
lemma QOptimal.qAdmissible_pull_of_meet {N r : ℕ} {A L R : Finset ℕ}
    (hA : QOptimal N A) (hr : r.Prime)
    (hL : L ⊆ primitive A) (hR : R ⊆ primitive A)
    (hrL : ∀ g ∈ L, ¬r ∣ g) (hrR : ∀ g ∈ R, r ∣ g)
    (hmeetPull : ∀ g ∈ pullGenerators r R, 1 < Nat.gcd g N)
    (hpairPull : Set.Pairwise (pullGenerators r R : Set ℕ)
      (fun a b ↦ 1 < Nat.gcd a b)) :
    QAdmissible N (multiplesBelow N (L ∪ pullGenerators r R)) := by
  have hLInterval : L ⊆ interval N := fun g hg ↦
    hA.1.1 (mem_primitive.mp (hL hg)).1
  have hRInterval : R ⊆ interval N := fun g hg ↦
    hA.1.1 (mem_primitive.mp (hR hg)).1
  have hR0 : ∀ g ∈ R, g ≠ 0 := by
    intro g hg
    have := (mem_interval.mp (hRInterval hg)).1
    omega
  apply qAdmissible_multiplesBelow_of_generators
  · intro g hg
    rcases Finset.mem_union.mp hg with hgL | hgPull
    · exact hLInterval hgL
    · exact pullGenerators_mem_interval hRInterval hgPull
  · intro g hg
    rcases Finset.mem_union.mp hg with hgL | hgPull
    · exact hA.primitive_meets_N (hL hgL)
    · exact hmeetPull g hgPull
  · intro g hg h hh hgh
    rcases Finset.mem_union.mp hg with hgL | hgPull <;>
      rcases Finset.mem_union.mp hh with hhL | hhPull
    · exact hA.primitive_pairwise (hL hgL) (hL hhL) hgh
    · obtain ⟨b, hbR, rfl⟩ := mem_pullGenerators.mp hhPull
      have hgb : g ≠ b := by
        intro hEq
        exact hrL g hgL (hEq ▸ hrR b hbR)
      exact one_lt_gcd_pullGenerator_of_cross hr
        (by have := (mem_interval.mp (hLInterval hgL)).1; omega)
        (hR0 b hbR) (hrR b hbR) (hrL g hgL)
        (hA.primitive_pairwise (hL hgL) (hR hbR) hgb)
    · obtain ⟨b, hbR, rfl⟩ := mem_pullGenerators.mp hgPull
      rw [Nat.gcd_comm]
      have hhb : h ≠ b := by
        intro hEq
        exact hrL h hhL (hEq ▸ hrR b hbR)
      exact one_lt_gcd_pullGenerator_of_cross hr
        (by have := (mem_interval.mp (hLInterval hhL)).1; omega)
        (hR0 b hbR) (hrR b hbR) (hrL h hhL)
        (hA.primitive_pairwise (hL hhL) (hR hbR) hhb)
    · exact hpairPull hgPull hhPull hgh

/-- Primitive generators below the current top prime class. -/
def lowerGenerators (r : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (primitive A).filter fun g ↦ ¬r ∣ g

/-- Top generators in the color containing `c`. -/
def topGeneratorsWith (r c : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (primitive A).filter fun g ↦ r ∣ g ∧ c ∣ g

/-- Top generators in the color avoiding `c`. -/
def topGeneratorsWithout (r c : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (primitive A).filter fun g ↦ r ∣ g ∧ ¬c ∣ g

@[simp] lemma mem_lowerGenerators {r g : ℕ} {A : Finset ℕ} :
    g ∈ lowerGenerators r A ↔ g ∈ primitive A ∧ ¬r ∣ g := by
  simp [lowerGenerators]

@[simp] lemma mem_topGeneratorsWith {r c g : ℕ} {A : Finset ℕ} :
    g ∈ topGeneratorsWith r c A ↔
      g ∈ primitive A ∧ r ∣ g ∧ c ∣ g := by
  simp [topGeneratorsWith, and_assoc]

@[simp] lemma mem_topGeneratorsWithout {r c g : ℕ} {A : Finset ℕ} :
    g ∈ topGeneratorsWithout r c A ↔
      g ∈ primitive A ∧ r ∣ g ∧ ¬c ∣ g := by
  simp [topGeneratorsWithout, and_assoc]

lemma primitive_eq_lower_union_top_colors (r c : ℕ) (A : Finset ℕ) :
    primitive A = lowerGenerators r A ∪
      (topGeneratorsWith r c A ∪ topGeneratorsWithout r c A) := by
  ext g
  simp only [mem_lowerGenerators, mem_topGeneratorsWith,
    mem_topGeneratorsWithout, Finset.mem_union]
  tauto

/-- The two old top-color remainders are disjoint.  If a number were
generated by both colors, compressedness of the avoiding color would expose
a lower primitive divisor, contradicting that it lies outside the lower
upset. -/
lemma QOptimal.disjoint_top_color_remainders
    {N c r : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hfix : ∀ p q, p.Prime → q.Prime → p < q → AllowedShift N p q →
      leftCompress p q A = A)
    (hc : c.Prime) (hr : r.Prime) (hcr : c < r)
    (hallow : AllowedShift N c r) :
    Disjoint
      (generatedRemainder N (lowerGenerators r A)
        (topGeneratorsWith r c A))
      (generatedRemainder N (lowerGenerators r A)
        (topGeneratorsWithout r c A)) := by
  rw [Finset.disjoint_left]
  intro a haWith haWithout
  obtain ⟨_ha1, _haN, ⟨g, hgWith, hga⟩, haLower⟩ :=
    mem_generatedRemainder.mp haWith
  obtain ⟨_ha1', _haN', ⟨h, hhWithout, hha⟩, _haLower'⟩ :=
    mem_generatedRemainder.mp haWithout
  have hg := mem_topGeneratorsWith.mp hgWith
  have hh := mem_topGeneratorsWithout.mp hhWithout
  have hhA := (mem_primitive.mp hh.1).1
  have hh0 : h ≠ 0 := by
    have := (mem_interval.mp (hA.1.1 hhA)).1
    omega
  have hhSq := hA.squarefree_of_mem_primitive hh.1
  have hrep : primePowerReplace c r h ∈ A :=
    hA.primePowerReplace_mem hfix hc hr hcr hallow hhA hh.2.1 hh.2.2
  have hrepEq : primePowerReplace c r h = ordCompl[r] h * c :=
    primePowerReplace_eq_ordCompl_mul_of_squarefree hr hhSq hh.2.1
  have hcCompl : ¬c ∣ ordCompl[r] h := by
    intro hdiv
    exact hh.2.2 (hdiv.trans (Nat.ordCompl_dvd h r))
  have hcomplA : ordCompl[r] h ∣ a :=
    (Nat.ordCompl_dvd h r).trans hha
  have hcA : c ∣ a := hg.2.2.trans hga
  have hrepA : primePowerReplace c r h ∣ a := by
    rw [hrepEq]
    exact (hc.coprime_iff_not_dvd.mpr hcCompl).symm.mul_dvd_of_dvd_of_dvd
      hcomplA hcA
  obtain ⟨d, hdP, hdRep⟩ := exists_primitive_dvd hA.1.1 hrep
  have hrRep : ¬r ∣ primePowerReplace c r h := by
    rw [prime_dvd_primePowerReplace_iff hc hr hr hcr.ne hh0 hh.2.2 hh.2.1]
    exact fun hcase ↦ hcase.elim (fun hrc ↦ hcr.ne hrc.symm)
      (fun hrest ↦ hrest.1 rfl)
  have hrd : ¬r ∣ d := fun hrd ↦ hrRep (hrd.trans hdRep)
  have hdLower : d ∈ lowerGenerators r A :=
    mem_lowerGenerators.mpr ⟨hdP, hrd⟩
  apply haLower
  exact mem_multiplesBelow.mpr
    ⟨_ha1, _haN, d, hdLower, hdRep.trans hrepA⟩

/-- Complete external-prime replacement stage, with the two numerical fiber
doubling inequalities exposed as the only remaining inputs. -/
theorem QOptimal.optimal_external_pull_of_doubling
    {N c r : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hN : N ≠ 0)
    (hfix : ∀ p q, p.Prime → q.Prime → p < q → AllowedShift N p q →
      leftCompress p q A = A)
    (hc : c.Prime) (hr : r.Prime) (hcr : c < r)
    (hrN : r ∉ N.primeFactors)
    (hdoubleWith :
      2 * (generatedRemainder N (lowerGenerators r A)
        (topGeneratorsWith r c A)).card ≤
      (generatedRemainder N (lowerGenerators r A)
        (pullGenerators r (topGeneratorsWith r c A))).card)
    (hdoubleWithout :
      2 * (generatedRemainder N (lowerGenerators r A)
        (topGeneratorsWithout r c A)).card ≤
      (generatedRemainder N (lowerGenerators r A)
        (pullGenerators r (topGeneratorsWithout r c A))).card) :
    QOptimal N (multiplesBelow N
      (lowerGenerators r A ∪ pullGenerators r (topGeneratorsWith r c A))) ∨
    QOptimal N (multiplesBelow N
      (lowerGenerators r A ∪ pullGenerators r (topGeneratorsWithout r c A))) := by
  let L := lowerGenerators r A
  let R₀ := topGeneratorsWith r c A
  let R₁ := topGeneratorsWithout r c A
  let G₀ := pullGenerators r R₀
  let G₁ := pullGenerators r R₁
  have hL : L ⊆ primitive A := by
    intro g hg
    exact (mem_lowerGenerators.mp hg).1
  have hR₀ : R₀ ⊆ primitive A := by
    intro g hg
    exact (mem_topGeneratorsWith.mp hg).1
  have hR₁ : R₁ ⊆ primitive A := by
    intro g hg
    exact (mem_topGeneratorsWithout.mp hg).1
  have hrL : ∀ g ∈ L, ¬r ∣ g := by
    intro g hg
    exact (mem_lowerGenerators.mp hg).2
  have hrR₀ : ∀ g ∈ R₀, r ∣ g := by
    intro g hg
    exact (mem_topGeneratorsWith.mp hg).2.1
  have hrR₁ : ∀ g ∈ R₁, r ∣ g := by
    intro g hg
    exact (mem_topGeneratorsWithout.mp hg).2.1
  have hR₀0 : ∀ g ∈ R₀, g ≠ 0 := by
    intro g hg
    have hgA := (mem_primitive.mp (hR₀ hg)).1
    have := (mem_interval.mp (hA.1.1 hgA)).1
    omega
  have hpair₀ : Set.Pairwise (G₀ : Set ℕ)
      (fun a b ↦ 1 < Nat.gcd a b) := by
    apply pullGenerators_pairwise_of_common_prime hr hc hcr.ne.symm hR₀0
    intro g hg
    exact (mem_topGeneratorsWith.mp hg).2.2
  have hallow : AllowedShift N c r := Or.inr hrN
  have hpair₁ : Set.Pairwise (G₁ : Set ℕ)
      (fun a b ↦ 1 < Nat.gcd a b) := by
    exact hA.pullGenerators_pairwise_of_compressed_avoids hfix hc hr hcr
      hallow hR₁ hrR₁ (fun g hg ↦
        (mem_topGeneratorsWithout.mp hg).2.2)
  apply qOptimal_of_two_pulls hA
  · change A = multiplesBelow N (lowerGenerators r A ∪
      (topGeneratorsWith r c A ∪ topGeneratorsWithout r c A))
    exact hA.eq_multiplesBelow_primitive.trans
      (congrArg (multiplesBelow N)
        (primitive_eq_lower_union_top_colors r c A))
  · exact generatedRemainder_union N L R₀ R₁
  · exact hA.disjoint_top_color_remainders hfix hc hr hcr hallow
  · exact hA.qAdmissible_pull_external hN hr hrN hL hR₀ hrL hrR₀ hpair₀
  · exact hA.qAdmissible_pull_external hN hr hrN hL hR₁ hrL hrR₁ hpair₁
  · exact hdoubleWith
  · exact hdoubleWithout

/-- Complete internal-top-prime replacement stage.  In addition to the two
fiber inequalities, one supplies the fact that deleting `r` leaves a
nontrivial endpoint gcd in each color. -/
theorem QOptimal.optimal_internal_pull_of_doubling
    {N c r : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hfix : ∀ p q, p.Prime → q.Prime → p < q → AllowedShift N p q →
      leftCompress p q A = A)
    (hc : c.Prime) (hr : r.Prime) (hcr : c < r)
    (hcN : c ∈ N.primeFactors) (hrN : r ∈ N.primeFactors)
    (hmeetWith : ∀ g ∈ pullGenerators r (topGeneratorsWith r c A),
      1 < Nat.gcd g N)
    (hmeetWithout : ∀ g ∈ pullGenerators r (topGeneratorsWithout r c A),
      1 < Nat.gcd g N)
    (hdoubleWith :
      2 * (generatedRemainder N (lowerGenerators r A)
        (topGeneratorsWith r c A)).card ≤
      (generatedRemainder N (lowerGenerators r A)
        (pullGenerators r (topGeneratorsWith r c A))).card)
    (hdoubleWithout :
      2 * (generatedRemainder N (lowerGenerators r A)
        (topGeneratorsWithout r c A)).card ≤
      (generatedRemainder N (lowerGenerators r A)
        (pullGenerators r (topGeneratorsWithout r c A))).card) :
    QOptimal N (multiplesBelow N
      (lowerGenerators r A ∪ pullGenerators r (topGeneratorsWith r c A))) ∨
    QOptimal N (multiplesBelow N
      (lowerGenerators r A ∪ pullGenerators r (topGeneratorsWithout r c A))) := by
  let L := lowerGenerators r A
  let R₀ := topGeneratorsWith r c A
  let R₁ := topGeneratorsWithout r c A
  let G₀ := pullGenerators r R₀
  let G₁ := pullGenerators r R₁
  have hL : L ⊆ primitive A := by
    intro g hg
    exact (mem_lowerGenerators.mp hg).1
  have hR₀ : R₀ ⊆ primitive A := by
    intro g hg
    exact (mem_topGeneratorsWith.mp hg).1
  have hR₁ : R₁ ⊆ primitive A := by
    intro g hg
    exact (mem_topGeneratorsWithout.mp hg).1
  have hrL : ∀ g ∈ L, ¬r ∣ g := by
    intro g hg
    exact (mem_lowerGenerators.mp hg).2
  have hrR₀ : ∀ g ∈ R₀, r ∣ g := by
    intro g hg
    exact (mem_topGeneratorsWith.mp hg).2.1
  have hrR₁ : ∀ g ∈ R₁, r ∣ g := by
    intro g hg
    exact (mem_topGeneratorsWithout.mp hg).2.1
  have hR₀0 : ∀ g ∈ R₀, g ≠ 0 := by
    intro g hg
    have hgA := (mem_primitive.mp (hR₀ hg)).1
    have := (mem_interval.mp (hA.1.1 hgA)).1
    omega
  have hpair₀ : Set.Pairwise (G₀ : Set ℕ)
      (fun a b ↦ 1 < Nat.gcd a b) := by
    apply pullGenerators_pairwise_of_common_prime hr hc hcr.ne.symm hR₀0
    intro g hg
    exact (mem_topGeneratorsWith.mp hg).2.2
  have hallow : AllowedShift N c r := Or.inl ⟨hcN, hrN⟩
  have hpair₁ : Set.Pairwise (G₁ : Set ℕ)
      (fun a b ↦ 1 < Nat.gcd a b) := by
    exact hA.pullGenerators_pairwise_of_compressed_avoids hfix hc hr hcr
      hallow hR₁ hrR₁ (fun g hg ↦
        (mem_topGeneratorsWithout.mp hg).2.2)
  apply qOptimal_of_two_pulls hA
  · exact hA.eq_multiplesBelow_primitive.trans
      (congrArg (multiplesBelow N)
        (primitive_eq_lower_union_top_colors r c A))
  · exact generatedRemainder_union N L R₀ R₁
  · exact hA.disjoint_top_color_remainders hfix hc hr hcr hallow
  · exact hA.qAdmissible_pull_of_meet hr hL hR₀ hrL hrR₀ hmeetWith hpair₀
  · exact hA.qAdmissible_pull_of_meet hr hL hR₁ hrL hrR₁ hmeetWithout hpair₁
  · exact hdoubleWith
  · exact hdoubleWithout

/-- Once `2*q` is present, a fully left-compressed optimum contains `2*p`
for every prime factor `p ≤ q` of the endpoint. -/
lemma QOptimal.two_mul_mem_of_compressed_top
    {N q : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hfix : ∀ p q, p.Prime → q.Prime → p < q → AllowedShift N p q →
      leftCompress p q A = A)
    (hNodd : ¬2 ∣ N) (hq : q ∈ N.primeFactors) (htop : 2 * q ∈ A) :
    ∀ p ∈ primePrefix N q, 2 * p ∈ A := by
  intro p hpPrefix
  have hpN := primePrefix_subset N q hpPrefix
  have hp := Nat.prime_of_mem_primeFactors hpN
  have hqPrime := Nat.prime_of_mem_primeFactors hq
  have hpqle := (mem_primePrefix.mp hpPrefix).2
  rcases hpqle.eq_or_lt with rfl | hpq
  · exact htop
  · have hq2 : q ≠ 2 := by
      intro h
      exact hNodd (h ▸ Nat.dvd_of_mem_primeFactors hq)
    have hpnot : ¬p ∣ 2 * q := by
      intro h
      rcases hp.dvd_mul.mp h with hp2 | hpqDvd
      · rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
        · exact hp.ne_one h
        · exact hNodd (h ▸ Nat.dvd_of_mem_primeFactors hpN)
      · rcases (Nat.dvd_prime hqPrime).mp hpqDvd with h | h
        · exact hp.ne_one h
        · exact hpq.ne h
    have hmem := hA.primePowerReplace_mem hfix hp hqPrime hpq
      (Or.inl ⟨hpN, hq⟩) htop (dvd_mul_left q 2) hpnot
    rw [primePowerReplace_two_mul hp hqPrime hpq.ne hq2] at hmem
    exact hmem

/-! ### Finite sifted intervals -/

/-- Greatest prime factor, with the harmless default value `0` at `0` and
`1`.  The supremum formulation is convenient for finite-set decompositions. -/
def greatestPrimeFactor (n : ℕ) : ℕ := n.primeFactors.sup id

lemma greatestPrimeFactor_mem_primeFactors {n : ℕ} (hn : 1 < n) :
    greatestPrimeFactor n ∈ n.primeFactors := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  have hmem := Finset.sup_mem_of_nonempty (f := id) hne
  simpa [greatestPrimeFactor] using hmem

lemma greatestPrimeFactor_prime {n : ℕ} (hn : 1 < n) :
    (greatestPrimeFactor n).Prime :=
  Nat.prime_of_mem_primeFactors (greatestPrimeFactor_mem_primeFactors hn)

lemma greatestPrimeFactor_dvd {n : ℕ} (hn : 1 < n) :
    greatestPrimeFactor n ∣ n :=
  Nat.dvd_of_mem_primeFactors (greatestPrimeFactor_mem_primeFactors hn)

lemma prime_le_greatestPrimeFactor_of_dvd {n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hn : n ≠ 0) :
    p ≤ greatestPrimeFactor n := by
  have hpMem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩
  change p ≤ n.primeFactors.sup id
  exact Finset.le_sup (f := id) hpMem

lemma greatestPrimeFactor_le_of_dvd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ∣ b) :
    greatestPrimeFactor a ≤ greatestPrimeFactor b := by
  rw [greatestPrimeFactor, Finset.sup_le_iff]
  intro p hp
  exact prime_le_greatestPrimeFactor_of_dvd (Nat.prime_of_mem_primeFactors hp)
    ((Nat.dvd_of_mem_primeFactors hp).trans hab) hb

/-- If `r` is prime and no prime factor of `b` exceeds `r`, then `r` is the
greatest prime factor of `b*r`. -/
lemma greatestPrimeFactor_mul_eq_right {b r : ℕ} (hb : 0 < b) (hr : r.Prime)
    (hmax : greatestPrimeFactor b ≤ r) :
    greatestPrimeFactor (b * r) = r := by
  apply Nat.le_antisymm
  · rw [greatestPrimeFactor, Finset.sup_le_iff]
    intro p hpMem
    have hp := Nat.prime_of_mem_primeFactors hpMem
    have hpdiv := Nat.dvd_of_mem_primeFactors hpMem
    rcases hp.dvd_mul.mp hpdiv with hpb | hpr
    · exact (prime_le_greatestPrimeFactor_of_dvd hp hpb (ne_of_gt hb)).trans hmax
    · rcases (Nat.dvd_prime hr).mp hpr with h | h
      · exact (hp.ne_one h).elim
      · exact h.le
  · exact prime_le_greatestPrimeFactor_of_dvd hr (dvd_mul_left r b)
      (mul_ne_zero (ne_of_gt hb) hr.ne_zero)

lemma greatestPrimeFactor_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    greatestPrimeFactor (p ^ k) = p := by
  simp [greatestPrimeFactor, Nat.primeFactors_prime_pow hk hp]

/-! ### Kernel-clean elementary Chebyshev estimates

This is the elementary weighted Chebyshev argument used by the source.
Unlike the unfinished explicit-bound modules, it uses only Mathlib theorems
and proof-producing decimal logarithm bounds. -/

namespace ElementaryChebyshev

open Real Finsupp Finset
open ArithmeticFunction hiding log
open scoped Chebyshev

attribute [local fun_prop] DifferentiableAt.differentiableWithinAt

noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  rw [T, ← Ico_insert_right <| Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne',
    sum_insert right_notMem_Ico]
  have : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) :=
    fun a ha _ _ hab ↦ log_le_log (lt_of_lt_of_le one_pos (by grind)) hab
  have : ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 :=
    calc ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n
        ≤ ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t := this.sum_le_integral_Ico <|
          Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by simp_all
  have h3 : ∀ t ∈ interior (Set.Ici 1), DifferentiableWithinAt ℝ (_root_.id * log - _root_.id) (interior (Set.Ici 1)) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    fun_prop ( disch := positivity )
  have h4 : ∀ t ∈ interior (Set.Ici 1), 0 ≤ deriv (fun t ↦ t * log t - t) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have : DifferentiableAt ℝ (fun t ↦ t * log t) t := by fun_prop ( disch := positivity )
    have hderiv : deriv (fun t ↦ t * log t - t) t = log t := by
      simp [show (fun t ↦ t * log t - t) = (fun t ↦ t * log t) - _root_.id by rfl,
        deriv_sub this differentiableAt_id, deriv_mul_log (by linarith)]
    exact hderiv ▸ log_nonneg (le_of_lt ht)
  have h5 : ContinuousOn (fun t ↦ t * log t - t) (Set.Ici 1) := by fun_prop
  have h2 : MonotoneOn (fun t ↦ t * log t - t) (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1) h5 h3 h4
  have : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ ≤ x * log x - x := by
    exact h2 (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr hx) <| Nat.floor_le (by grind)
  linarith [log_le_log (by positivity) <| Nat.floor_le (by linarith)]

theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  have hone_le_floor : 1 ≤ ⌊x⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
  simp only [T, ← Ico_insert_right hone_le_floor, sum_insert right_notMem_Ico]
  have mono_log : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) := fun a ha _ _ hab ↦
    log_le_log (lt_of_lt_of_le one_pos (by simpa using ha.1)) hab
  have h1 : ∀ n ≥ 1, ∑ i ∈ Ico 1 n, log (i + 1 : ℕ) = log n + ∑ i ∈ Ico 1 n, log i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih => grind [Nat.Ico_succ_right_eq_insert_Ico]
  have sum_shift : ∑ i ∈ Ico 1 ⌊x⌋₊, log (i + 1 : ℕ) = log ⌊x⌋₊ + ∑ i ∈ Ico 1 ⌊x⌋₊, log i := by
    exact h1 ⌊x⌋₊ hone_le_floor
  have int_le_T : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t ≤ log ⌊x⌋₊ + ∑ n ∈ Ico 1 ⌊x⌋₊, log n := by
    linarith [mono_log.integral_le_sum_Ico hone_le_floor]
  have int_eq : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h2 : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ (x - ⌊x⌋₊) * log x := by
    calc ∫ t in (⌊x⌋₊ : ℝ)..x, log t
      ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x := (intervalIntegral.integral_mono_on (Nat.floor_le <| by linarith) intervalIntegral.intervalIntegrable_log'
            intervalIntegrable_const fun t ht ↦ log_le_log (lt_of_lt_of_le (by positivity) ht.1) ht.2)
      _ = (x - ⌊x⌋₊) * log x := by simp
  have target_le_int : x * log x - x + 1 - log x ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    calc x * log x - x + 1 - log x
        ≤ (x * log x - x + 1) - (x - ⌊x⌋₊) * log x := by nlinarith [log_nonneg hx, Nat.lt_floor_add_one x]
      _ ≤ (x * log x - x + 1) - ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by grind
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by grind [integral_log]
  linarith

theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← show Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ by ext n; simp; omega,
    sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)

theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) : ν.sum (fun m w ↦ w * T (x/m)) = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * E ν (x/n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by grind [Nat.one_le_cast]
  by_cases hx : x < 1
  · simp [hx, show x / y < 1 from div_lt_one (by linarith)|>.mpr (by linarith)]
  apply sum_subset_zero_on_sdiff
  · apply Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [mem_sdiff, mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith)|>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · grind

open Finsupp in
noncomputable def ν : ℕ →₀ ℝ := single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

/-- The support of `ν` is `{1, 2, 3, 5, 30}`. Used whenever we need to unfold `ν.sum`. -/
private lemma ν_support : ν.support = {1, 2, 3, 5, 30} := by
  norm_num [ν, Finset.ext_iff]; grind

/-- Unfold `ν.sum (fun m w ↦ w * f m)` into its five-term expansion.
This avoids repeating the `sum_add_index` / `sum_sub_index` chain every time
we need to compute a `ν`-weighted sum. -/
private lemma ν_sum_mul (f : ℕ → ℝ) :
    ν.sum (fun m w ↦ w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
  rw [ν, sum_add_index (by simp) (by intros; ring)]
  grind only [sum_single_index, sum_sub_index]

/-- Unfold `E ν y` into an explicit expression in terms of floors of `y / k`.
This is the key formula repeatedly used to analyse `E ν`. -/
private lemma E_nu_expand (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

/-- The classical sandwich `k * ⌊y/k⌋₊ ≤ ⌊y⌋₊ < k * ⌊y/k⌋₊ + k` for `k ≥ 1` and `y ≥ 0`. -/
private lemma floor_div_bounds {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    k * ⌊y / k⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < k * ⌊y / k⌋₊ + k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdivnn : 0 ≤ y / k := div_nonneg hy hk'.le
  refine ⟨Nat.le_floor ?_, ?_⟩
  · push_cast
    have := Nat.floor_le hdivnn
    calc ((k : ℝ) * ⌊y / k⌋₊) = k * (y / k) - k * (y / k - ⌊y / k⌋₊) := by ring
      _ ≤ k * (y / k) := by nlinarith [Nat.floor_le hdivnn]
      _ = y := mul_div_cancel₀ _ hk'.ne'
  · have hlt : y / k < ⌊y / k⌋₊ + 1 := Nat.lt_floor_add_one (y / k)
    have hy_lt : y < (k : ℝ) * (⌊y / k⌋₊ + 1) := by linarith [(div_lt_iff₀ hk').mp hlt]
    have : (⌊y⌋₊ : ℝ) < (k : ℝ) * (⌊y / k⌋₊ + 1) := (Nat.floor_le hy).trans_lt hy_lt
    exact_mod_cast this

theorem nu_sum_div_eq_zero : ν.sum (fun n w ↦ w / n) = 0 := by
  norm_num [ν, add_div, sum_add_index', sub_div, sum_sub_index]

theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  obtain ⟨h1, h6⟩ := hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : x / 30 < 1)]
  have hflb : 1 ≤ ⌊x⌋₊ := by rwa [Nat.one_le_floor_iff]
  have hfub : ⌊x⌋₊ ≤ 5 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by grind) |>.mpr h6)
  have h2 := floor_div_bounds hx0 (k := 2) (by norm_num)
  have h3 := floor_div_bounds hx0 (k := 3) (by norm_num)
  have h5 := floor_div_bounds hx0 (k := 5) (by norm_num)
  push_cast at h2 h3 h5
  rw [show ⌊x⌋₊ = ⌊x / 2⌋₊ + ⌊x / 3⌋₊ + ⌊x / 5⌋₊ + 1 by omega]
  grind

theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  have h (k : ℝ) : (x + 30) / k = x / k + (30 / k) := by ring
  simp_rw [E_nu_expand, h 2, h 3, h 5, h 30]
  norm_num
  repeat rw [Nat.floor_add_ofNat (by positivity)]
  rw [Nat.floor_add_one (by positivity)]
  grind

theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have : ∀ y, 0 ≤ y → y < 30 → 0 ≤ E ν y ∧ E ν y ≤ 1 := fun y hy0 hy30 ↦ by
    simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1), Nat.cast_zero, add_zero]
    have h2 := floor_div_bounds hy0 (k := 2) (by norm_num)
    have h3 := floor_div_bounds hy0 (k := 3) (by norm_num)
    have h5 := floor_div_bounds hy0 (k := 5) (by norm_num)
    push_cast at h2 h3 h5
    have hfy : ⌊y⌋₊ < 30 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hy30)
    have hlb : ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ ≤ ⌊y⌋₊ := by omega
    have hub : ⌊y⌋₊ ≤ ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 := by omega
    have hlb' : ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hlb
    have hub' : ((⌊y⌋₊ : ℕ) : ℝ) ≤ ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hub
    push_cast at hlb' hub'
    refine ⟨by linarith, by linarith⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x/30)], by
    linarith [Nat.lt_floor_add_one (x/30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x/30⌋₊ * 30 := by ring
    rw [this]; induction ⌊x/30⌋₊ with
    | zero => simp
    | succ n ih => simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ this y hy.1 hy.2

noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))

theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  unfold U Chebyshev.psi
  rw [T.weighted_eq_sum,
    ← show Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ by ext n; simp; omega]
  gcongr with i
  have := E_nu_bound (x / i) (div_nonneg hx.le (by simp))
  grw [this.2, mul_one]

theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U Chebyshev.psi
  rw [T.weighted_eq_sum,
    ← show Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊ by ext n; simp; omega]
  have subset : Ioc 0 ⌊x / 6⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← sum_sdiff_eq_sub subset, ← sum_sdiff subset]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_) (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind)|>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp))|>.1

noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7/15) * Real.log 2 + (3/10) * Real.log 3 + (1/6) * Real.log 5 := by
  norm_num [a, Finsupp.sum, single_apply, ν_support]
  norm_num [Finset.sum, ν]
  grind [show (30 : ℝ) = 2 * 3 * 5 by ring, log_mul, log_mul]

theorem a_bound : a ∈ Set.Icc 0.92129 0.92130 := by
  norm_num [ElementaryChebyshev.a_simpl]
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9, Real.log_five_lt_d9]

noncomputable def e (x : ℝ) : ℝ :=
  (T x - (x * log x - x + 1))

lemma U_bound.lemma_1 (x : ℝ) : T x = x * log x - x + 1 + (e x) := by
  unfold e
  ring

lemma U_bound.lemma_2 (x : ℝ) (hx : 1 ≤ x) : |e x| ≤ log x := by
  rw [abs_le]
  unfold e
  constructor <;> linarith [T.ge x hx, T.le x hx]

lemma U_bound.lemma_3 (x : ℝ) :
    U x = ν.sum (fun m w ↦ w * ((x / m) * (log (x / m))))
          - ν.sum (fun m w ↦ w * (x / m))
          + ν.sum (fun _m w ↦ w)
          + ν.sum (fun m w ↦ w * e (x / m)) := by
  simp [U, Finsupp.sum, U_bound.lemma_1, sub_eq_add_neg, add_mul, mul_comm, sum_add_distrib]

lemma U_bound.lemma_4 (x : ℝ) (hx : 0 < x) :
    ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) = a * x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : a = -(log 1 / 1 - log 2 / 2 - log 3 / 3 - log 5 / 5 + log 30 / 30) := by
    simp_rw [a, mul_div_assoc]; rw [ν_sum_mul (fun m ↦ log m / m)]; push_cast; rfl
  rw [ν_sum_mul (fun m ↦ (x / m) * log (x / m)), ha]
  simp [Real.log_div hx0]
  ring

lemma U_bound.lemma_5 (x : ℝ) : ν.sum (fun m w ↦ w * (x / m)) = 0 := by
  rw [ν_sum_mul (fun m ↦ x / m)]; push_cast; ring

lemma U_bound.lemma_6 : ν.sum (fun _ w ↦ w) = (-1 : ℝ) := by
  have := ν_sum_mul (fun _ ↦ (1 : ℝ)); simp at this; linarith

lemma Finsupp.abs_sum_le (A : Type*) (ν : A →₀ ℝ) (g : A → ℝ → ℝ) : |ν.sum g| ≤ ν.sum |g| := by
  simp_rw [Finsupp.sum.eq_1]
  exact abs_sum_le_sum_abs (fun i ↦ g i (ν i)) ν.support

theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [U_bound.lemma_3, U_bound.lemma_4 x hxpos]
  ring_nf
  have hlin : ν.sum (fun m w ↦ x * w * (↑m)⁻¹) = 0 :=
    by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using U_bound.lemma_5 x
  rw [hlin]; ring_nf; rw [U_bound.lemma_6]
  grw [abs_add_le, Finsupp.abs_sum_le]
  norm_num
  have hsupp_eq : ν.support = {1, 2, 3, 5, 30} := ν_support
  have hmem_of_supp : ∀ i ∈ ν.support, 0 < i ∧ i ≤ 30 := fun i hi ↦ by
    have : i ∈ ({1, 2, 3, 5, 30} : Finset ℕ) := hsupp_eq ▸ hi
    simp only [mem_insert, mem_singleton] at this
    constructor <;> omega
  have h : ν.sum |fun m w ↦ w * e (x * (↑m)⁻¹)| ≤ ν.sum (fun m w ↦ |w| * log (x * (↑m)⁻¹)) := by
    apply Finsupp.sum_le_sum
    intro i hi
    simp only [Pi.abs_apply, abs_mul]
    obtain ⟨hi_pos, hi_le⟩ := hmem_of_supp i hi
    have hxi : 1 ≤ x * (↑i)⁻¹ := by
      rw [le_mul_inv_iff₀ (by exact_mod_cast hi_pos)]
      linarith [show (i : ℝ) ≤ 30 from by exact_mod_cast hi_le]
    gcongr; exact U_bound.lemma_2 _ hxi
  grw [h]
  have hlog_split : ν.sum (fun m w ↦ |w| * log (x * (m : ℝ)⁻¹)) =
      log x * ν.sum (fun m w ↦ |w|) - ν.sum (fun m w ↦ |w| * log (↑m : ℝ)) := by
    simp only [Finsupp.sum]
    conv_rhs => rw [Finset.mul_sum, ← sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (hmem_of_supp m hm).1
    rw [← div_eq_mul_inv, Real.log_div (ne_of_gt hxpos) (ne_of_gt hm_pos)]; ring
  rw [hlog_split]
  -- Once the support of `ν` is known explicitly, both `habs` and `hsum_eq`
  -- reduce to concrete arithmetic over a five-element finset.
  have expand_sum : ∀ f : ℕ → ℝ → ℝ, (∀ n, f n 0 = 0) →
      ν.sum f = f 1 1 + f 2 (-1) + f 3 (-1) + f 5 (-1) + f 30 1 := by
    intro f hf
    rw [Finsupp.sum_of_support_subset _ hsupp_eq.le _ (by intros; simp [hf])]
    simp only [sum_insert (by decide : (1:ℕ) ∉ ({2,3,5,30} : Finset ℕ)),
               sum_insert (by decide : (2:ℕ) ∉ ({3,5,30} : Finset ℕ)),
               sum_insert (by decide : (3:ℕ) ∉ ({5,30} : Finset ℕ)),
               sum_insert (by decide : (5:ℕ) ∉ ({30} : Finset ℕ)),
               sum_singleton, ν, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    ring
  have habs : ν.sum (fun m w ↦ |w|) = 5 := by
    rw [expand_sum _ (by intros; simp)]; norm_num
  have hgeq6 : ν.sum (fun m w ↦ |w| * log m) ≥ 6 := by
    have hsum_eq : ν.sum (fun m w ↦ |w| * log (m : ℝ)) = log 2 + log 3 + log 5 + log 30 := by
      rw [expand_sum _ (by intros; simp)]
      simp [log_one]
    have hlog30 : log (30 : ℝ) = log 2 + log 3 + log 5 := by
      calc
        log (30 : ℝ) = log ((2 * 3 : ℝ) * 5) := by norm_num
        _ = log (2 * 3 : ℝ) + log 5 :=
          log_mul (by norm_num) (by norm_num)
        _ = log 2 + log 3 + log 5 := by
          rw [log_mul (by norm_num : (2 : ℝ) ≠ 0)
            (by norm_num : (3 : ℝ) ≠ 0)]
    rw [hlog30] at hsum_eq
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9]
  grw [hgeq6]; rw [habs]; linarith

theorem psi_lower (x : ℝ) (hx : 30 ≤ x) : ψ x ≥ a * x - 5 * log x + 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_ge_weighted x (by linarith), h2.1]

theorem psi_diff_upper (x : ℝ) (hx : 30 ≤ x) : ψ x - ψ (x / 6) ≤ a * x + 5 * log x - 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_diff_le_weighted x (by linarith), h2.2]


private lemma log_seven_lt : log (7 : ℝ) < 203 / 100 := by
  have h := log_lt_log (by norm_num : (0 : ℝ) < 7)
    (by norm_num : (7 : ℝ) < 15 / 2)
  rw [log_div (by norm_num : (15 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    show (15 : ℝ) = 3 * 5 by norm_num,
    log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)] at h
  nlinarith [Real.log_two_gt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

private lemma log_eleven_lt : log (11 : ℝ) < 253 / 100 := by
  have h := log_lt_log (by norm_num : (0 : ℝ) < 11)
    (by norm_num : (11 : ℝ) < 25 / 2)
  rw [log_div (by norm_num : (25 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    show (25 : ℝ) = 5 * 5 by norm_num,
    log_mul (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)] at h
  nlinarith [Real.log_two_gt_d9, Real.log_five_lt_d9]

private lemma log_thirteen_lt : log (13 : ℝ) < 261 / 100 := by
  have h := log_lt_log (by norm_num : (0 : ℝ) < 13)
    (by norm_num : (13 : ℝ) < 27 / 2)
  rw [log_div (by norm_num : (27 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    show (27 : ℝ) = 3 * (3 * 3) by norm_num,
    log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (3 * 3 : ℝ) ≠ 0),
    log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at h
  nlinarith [Real.log_two_gt_d9, Real.log_three_lt_d9]

private lemma log_seventeen_lt : log (17 : ℝ) < 29 / 10 := by
  have h := log_lt_log (by norm_num : (0 : ℝ) < 17)
    (by norm_num : (17 : ℝ) < 2 * (3 * 3))
  rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 * 3 : ℝ) ≠ 0),
    log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at h
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

private lemma log_nineteen_lt : log (19 : ℝ) < 3 := by
  have h := log_lt_log (by norm_num : (0 : ℝ) < 19)
    (by norm_num : (19 : ℝ) < (2 * 2) * 5)
  rw [log_mul (by norm_num : (2 * 2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0),
    log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at h
  nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

private lemma log_twentyThree_lt : log (23 : ℝ) < 16 / 5 := by
  have h := log_lt_log (by norm_num : (0 : ℝ) < 23)
    (by norm_num : (23 : ℝ) < (2 * (2 * 2)) * 3)
  rw [log_mul (by norm_num : (2 * (2 * 2) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
    log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 * 2 : ℝ) ≠ 0),
    log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at h
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9]

private lemma log_twentyNine_lt : log (29 : ℝ) < 341 / 100 := by
  have h := log_lt_log (by norm_num : (0 : ℝ) < 29)
    (by norm_num : (29 : ℝ) < (2 * 3) * 5)
  rw [log_mul (by norm_num : (2 * 3 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0),
    log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at h
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

-- Proof splits into many cases
theorem psi_num (x : ℝ) (hx : x > 0) (hx2 : x ≤ 30) : ψ x ≤ 1.1 * x := by
  suffices ∀ n ∈ Icc (0 : ℕ) 30, ψ n ≤ 1.1 * n by
    rw [Chebyshev.psi_eq_psi_coe_floor]
    grw [this]
    · gcongr
      exact Nat.floor_le hx.le
    · simp only [mem_Icc, zero_le, true_and]
      exact Nat.floor_le_of_le hx2
  unfold Chebyshev.psi
  have primes : Λ 2 = log 2 ∧ Λ 3 = log 3 ∧ Λ 5 = log 5 ∧ Λ 7 = log 7 ∧ Λ 11 = log 11 ∧ Λ 13 = log 13 ∧ Λ 17 = log 17 ∧ Λ 19 = log 19 ∧ Λ 23 = log 23 ∧ Λ 29 = log 29 := by
    split_ands <;> exact vonMangoldt_apply_prime (by decide)
  have lam_pow : (Λ (2 ^ 2) = log 2) ∧ Λ (2 ^ 3) = log 2 ∧ Λ (2 ^ 4) = log 2 ∧ Λ (3 ^ 2) = log 3 ∧ Λ (3 ^ 3) = log 3 ∧ Λ (5 ^ 2) = log 5:= by
    split_ands <;> rw [vonMangoldt_apply_pow (by norm_num)] <;> (try rw [primes.1]) <;> simp_all
  have comps : Λ 6 = 0 ∧ Λ 10 = 0 ∧ Λ 12 = 0 ∧ Λ 14 = 0 ∧ Λ 15 = 0 ∧ Λ 18 = 0 ∧ Λ 20 = 0 ∧ Λ 21 = 0 ∧ Λ 22 = 0 ∧ Λ 24 = 0 ∧ Λ 26 = 0 ∧ Λ 28 = 0 ∧ Λ 30 = 0 := by
    split_ands <;> rw [vonMangoldt_eq_zero_iff, isPrimePow_nat_iff_bounded_log] <;> decide
  intro n hn
  fin_cases hn
  · simp
  · simp; norm_num
  all_goals
    simp_all only [gt_iff_lt, Nat.reducePow, zero_add, Nat.reduceAdd, Nat.cast_ofNat,
      Nat.floor_ofNat, zero_le, sum_Ioc_succ_top, Nat.Ioc_succ_singleton, sum_singleton,
      vonMangoldt_apply_one, add_zero]
    try grw [Real.log_two_lt_d9]; try grw [Real.log_three_lt_d9]; try grw [Real.log_five_lt_d9]; try grw [log_seven_lt]
    try grw [log_eleven_lt]; try grw [log_thirteen_lt]; try grw [log_seventeen_lt]; try grw [log_nineteen_lt]
    try grw [log_twentyThree_lt]; try grw [log_twentyNine_lt]
    norm_num

theorem psi_upper (x : ℝ) (hx : 30 ≤ x) : ψ x ≤ 6 * a * x / 5 + (log (x/5) / log 6) * (5 * log x - 5) := by
  -- Compute `6 ^ (log (x/5) / log 6 - 1) = x / 30` (used twice below).
  have rpow_key : (30 : ℝ) * 6 ^ (log (x / 5) / log 6 - 1) = x := by
    rw [rpow_def_of_pos (by norm_num)]
    field_simp
    rw [exp_sub, exp_log, exp_log] <;> linarith
  have telescope (n : ℕ) : ψ x - ψ (x / 6 ^ n) = ∑ i ∈ Ico 0 n, (ψ (x / 6 ^ i) - ψ (x / 6 ^ (i + 1))) := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [sum_Ico_succ_top <| Nat.zero_le n, ← hn]
      ring
  have bound (n : ℕ) (h : ∀ i < n, 30 ≤ x / 6 ^ i) : ψ x - ψ (x / 6 ^ n) ≤ ∑ i ∈ Ico 0 n, (a * x / 6 ^i + 5 * log (x / 6 ^ i) - 5) := by
    rw [telescope]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    convert! psi_diff_upper (x / 6 ^ i) (by grind) using 3
    · field
    · ring
  replace bound (n : ℕ) (h : ∀ i < n, 30 ≤ x / 6 ^ i) : ψ x - ψ (x / 6 ^ n) ≤ ∑ i ∈ Ico 0 n, (a * x / 6 ^i + 5 * log x - 5) := by
    grw [bound n h]
    apply Finset.sum_le_sum fun i hi ↦ ?_
    gcongr
    bound
  let n := ⌊log (x / 5) / log 6⌋₊
  specialize bound n ?_
  · intro i hi
    apply le_div_iff₀ (by simp)|>.mpr
    trans (30 * 6 ^ (n-1))
    · gcongr <;> grind
    · trans (30 * 6 ^ (log (x / 5) / log 6 - 1))
      · rw [← rpow_natCast, Nat.cast_sub]
        · gcongr
          · norm_num
          · refine Nat.floor_le <| div_nonneg ?_ ?_ <;> apply log_nonneg <;> linarith
          · norm_cast
        · apply Nat.le_floor
          norm_cast
          apply le_div_iff₀ (log_pos (by norm_num))|>.mpr
          rw [one_mul]
          gcongr
          linarith
      · exact rpow_key.le
  simp_rw [← add_sub, sum_add_distrib, sum_const, Nat.Ico_zero_eq_range, Finset.card_range, nsmul_eq_mul, tsub_le_iff_right] at bound
  apply bound.trans
  conv => lhs; arg 1; arg 1; arg 2; ext i; rw [← mul_one_div, ←one_div_pow]
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num)]
  norm_num
  have : x / 6 ^ n ≤ 30 := by
    apply div_le_iff₀ (by simp)|>.mpr
    trans 30 * 6 ^ (log (x / 5) / log 6 - 1)
    · exact rpow_key.ge
    · rw [← rpow_natCast]
      gcongr
      · norm_num
      · exact Nat.sub_one_lt_floor _|>.le
  grw [psi_num _ (by simp; linarith) this]
  calc
  _ = 6 * a * x / 5 - x * (1 / 6) ^ n * (a * 1 / (5 / 6) - 1.1) + n * (5 * log x - 5) := by
    ring_nf
    congr
    norm_num
  _ ≤6 * a * x / 5 + n * (5 * log x - 5) := by
    gcongr
    simp only [one_div, inv_pow, mul_one, tsub_le_iff_right, le_add_iff_nonneg_right]
    refine mul_nonneg (mul_nonneg (by linarith) (by simp)) ?_
    grw [← a_bound.1]
    norm_num
  _ ≤ _ := by
    gcongr
    · simp only [sub_nonneg, Nat.ofNat_pos, le_mul_iff_one_le_right]
      exact le_log_iff_exp_le (by linarith)|>.mpr (by linarith [exp_one_lt_three])
    · exact Nat.floor_le (by bound)

/-- A convenient rational-coefficient consequence of `psi_upper`. -/
theorem psi_upper_simple (x : ℝ) (hx : 30 ≤ x) :
    ψ x ≤ (111 / 100 : ℝ) * x + 5 * (log x) ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hx5 : 0 < x / 5 := by positivity
  have hlogx : 1 ≤ log x := by
    have h3x : (3 : ℝ) < x := by linarith
    have hlog3 : 1 < log (3 : ℝ) := by
      nlinarith [Real.log_three_gt_d9]
    exact (hlog3.trans_le (log_le_log (by norm_num) h3x.le)).le
  have hlog6 : 1 ≤ log (6 : ℝ) := by
    have h3 : (3 : ℝ) ≤ 6 := by norm_num
    nlinarith [Real.log_three_gt_d9,
      log_le_log (by norm_num : (0 : ℝ) < 3) h3]
  have hlogDiv : log (x / 5) ≤ log x :=
    log_le_log hx5 (div_le_self hxpos.le (by norm_num))
  have hquot : log (x / 5) / log 6 ≤ log x := by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hlog6)).2
    nlinarith [log_nonneg (by linarith : (1 : ℝ) ≤ x / 5)]
  have hfactor0 : 0 ≤ 5 * log x - 5 := by nlinarith
  have hfactor : 5 * log x - 5 ≤ 5 * log x := by norm_num
  have herror : (log (x / 5) / log 6) * (5 * log x - 5) ≤
      5 * (log x) ^ 2 := by
    calc
      (log (x / 5) / log 6) * (5 * log x - 5)
          ≤ log x * (5 * log x - 5) :=
            mul_le_mul_of_nonneg_right hquot hfactor0
      _ ≤ log x * (5 * log x) :=
            mul_le_mul_of_nonneg_left hfactor (by linarith)
      _ = 5 * (log x) ^ 2 := by ring
  have ha := a_bound.2
  nlinarith [psi_upper x hx]

/-- The logarithmic error divided by its linear scale is decreasing once
`log x` exceeds two. -/
lemma log_sq_div_antitone_on :
    AntitoneOn (fun x : ℝ => (log x) ^ 2 / x) (Set.Ici (exp 2)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x : ℝ =>
    ((2 : ℝ) * log x ^ (2 - 1) * x⁻¹ * x - log x ^ 2 * 1) / x ^ 2)
    (convex_Ici (exp 2))
  · apply ContinuousOn.div
    · apply ContinuousOn.pow
      exact continuousOn_log.mono (by
        intro x hx
        simp only [Set.mem_Ici] at hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have := exp_pos (2 : ℝ)
        linarith)
    · exact continuousOn_id
    · intro x hx
      simp only [Set.mem_Ici] at hx
      have := exp_pos (2 : ℝ)
      linarith
  · intro x hx
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    have hxpos : 0 < x := lt_trans (exp_pos 2) hx
    exact (((hasDerivAt_log hxpos.ne').pow 2).div (hasDerivAt_id x)
      hxpos.ne').hasDerivWithinAt
  · intro x hx
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    have hxpos : 0 < x := lt_trans (exp_pos 2) hx
    have hlog : 2 < log x := by
      rw [← log_exp 2]
      exact strictMonoOn_log (Set.mem_Ioi.mpr (exp_pos 2))
        (Set.mem_Ioi.mpr hxpos) hx
    have hxone : 1 ≤ x :=
      (lt_trans (one_lt_exp_iff.mpr (by norm_num)) hx).le
    have hnum : log x * (2 - log x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (log_nonneg hxone) (by linarith)
    have hden : 0 < x ^ 2 := sq_pos_of_pos hxpos
    have heq :
        ((2 : ℝ) * log x ^ (2 - 1) * x⁻¹ * x - log x ^ 2 * 1) / x ^ 2 =
          log x * (2 - log x) / x ^ 2 := by
      field_simp [hxpos.ne']
      ring
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg hnum hden.le

lemma log_10000_eq : log (10000 : ℝ) = 4 * (log 2 + log 5) := by
  rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow,
    show (10 : ℝ) = 2 * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  norm_num

/-- At the numerical cutoff `10000`, the logarithmic-square error in
`psi_upper_simple` is at most five percent of the linear term. -/
lemma five_log_sq_le_twentieth_mul (x : ℝ) (hx : 10000 ≤ x) :
    5 * (log x) ^ 2 ≤ (1 / 20 : ℝ) * x := by
  have hlogUpper : log (10000 : ℝ) < 10 := by
    rw [log_10000_eq]
    nlinarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlogLower : 2 ≤ log (10000 : ℝ) := by
    rw [log_10000_eq]
    nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hbase : exp 2 ≤ (10000 : ℝ) :=
    (le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10000)).mp hlogLower
  have hxmem : x ∈ Set.Ici (exp 2) := hbase.trans hx
  have hratio := log_sq_div_antitone_on hbase hxmem hx
  have hlogNonneg : 0 ≤ log (10000 : ℝ) := by linarith
  have hbaseRatio :
      (log (10000 : ℝ)) ^ 2 / 10000 ≤ (1 / 100 : ℝ) := by
    have hsquare : (log (10000 : ℝ)) ^ 2 ≤ 100 := by nlinarith
    calc
      (log (10000 : ℝ)) ^ 2 / 10000 ≤ 100 / 10000 := by gcongr
      _ = (1 / 100 : ℝ) := by norm_num
  have hxpos : 0 < x := by linarith
  have hsquareX : (log x) ^ 2 ≤ (1 / 100 : ℝ) * x := by
    apply (div_le_iff₀ hxpos).mp
    exact hratio.trans hbaseRatio
  nlinarith

/-- A fully elementary linear upper bound for Chebyshev's second function
beyond the explicit cutoff. -/
theorem psi_upper_linear (x : ℝ) (hx : 10000 ≤ x) :
    ψ x ≤ (6 / 5 : ℝ) * x := by
  nlinarith [psi_upper_simple x (by linarith),
    five_log_sq_le_twentieth_mul x hx]




end ElementaryChebyshev


/-- Available primes between the base prime and `X`, inclusive. -/
def oldPrimeBand (T : Finset ℕ) (p X : ℕ) : Finset ℕ :=
  (Nat.primesLE X).filter fun r ↦ p ≤ r ∧ r ∉ T

/-- Available primes in the new interval `(X,pX]`. -/
def newPrimeBand (T : Finset ℕ) (p X : ℕ) : Finset ℕ :=
  (Nat.primesLE (p * X)).filter fun r ↦ X < r ∧ r ∉ T

@[simp] lemma mem_oldPrimeBand {T : Finset ℕ} {p X r : ℕ} :
    r ∈ oldPrimeBand T p X ↔ r.Prime ∧ p ≤ r ∧ r ≤ X ∧ r ∉ T := by
  simp [oldPrimeBand, Nat.mem_primesLE, and_assoc, and_left_comm]

@[simp] lemma mem_newPrimeBand {T : Finset ℕ} {p X r : ℕ} :
    r ∈ newPrimeBand T p X ↔ r.Prime ∧ X < r ∧ r ≤ p * X ∧ r ∉ T := by
  simp [newPrimeBand, Nat.mem_primesLE, and_assoc, and_left_comm]

/-- The exact local prime-interval hypothesis used by the fiber injection in
the conditional sieve lemma.  The source's prime-counting condition is used
only to establish this finite cardinal inequality. -/
def PrimeIntervalExpansion (T : Finset ℕ) (p : ℕ) : Prop :=
  ∀ X, p ≤ X → (oldPrimeBand T p X).card ≤ (newPrimeBand T p X).card

/-- The `k`-th prime in the paper's one-based indexing. -/
noncomputable def oneBasedPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

lemma oneBasedPrime_prime {k : ℕ} (hk : 1 ≤ k) :
    (oneBasedPrime k).Prime := by
  exact Nat.prime_nth_prime (k - 1)

@[simp] lemma primeCounting_oneBasedPrime {k : ℕ} (hk : 1 ≤ k) :
    Nat.primeCounting (oneBasedPrime k) = k := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  change Nat.count Nat.Prime (Nat.nth Nat.Prime (k - 1) + 1) = k
  rw [Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime]
  omega

/-- The product of the first `k` primes dominates `k!`, hence its logarithm
is a lower bound for the Chebyshev theta function at the `k`-th prime. -/
lemma log_factorial_le_theta_oneBasedPrime {k : ℕ} (hk : 1 ≤ k) :
    Real.log (Nat.factorial k) ≤ Chebyshev.theta (oneBasedPrime k) := by
  let f : ℕ → ℕ := fun i ↦ Nat.nth Nat.Prime i
  have hf : Function.Injective f :=
    Nat.nth_injective Nat.infinite_setOfPred_prime
  have hsub : (Finset.range k).image f ⊆
      Nat.primesLE (oneBasedPrime k) := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    rw [Nat.mem_primesLE]
    refine ⟨?_, Nat.prime_nth_prime i⟩
    dsimp only [oneBasedPrime, f]
    apply (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
    rw [Finset.mem_range] at hi
    omega
  calc
    Real.log (Nat.factorial k) =
        ∑ i ∈ Finset.range k, Real.log (i + 1 : ℕ) := by
      rw [← Finset.prod_range_add_one_eq_factorial]
      push_cast
      rw [Real.log_prod]
      intro i hi
      positivity
    _ ≤ ∑ i ∈ Finset.range k, Real.log (f i) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Real.log_le_log (by positivity)
      exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
    _ = ∑ p ∈ (Finset.range k).image f, Real.log p := by
      rw [Finset.sum_image (fun a _ha b _hb hab ↦ hf hab)]
    _ ≤ ∑ p ∈ Nat.primesLE (oneBasedPrime k), Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      exact Real.log_natCast_nonneg p
    _ = Chebyshev.theta (oneBasedPrime k) := by
      rw [Chebyshev.theta_eq_sum_primesLE_log]

lemma add_one_le_oneBasedPrime {k : ℕ} (hk : 1 ≤ k) :
    k + 1 ≤ oneBasedPrime k := by
  rw [oneBasedPrime]
  have h := Nat.add_two_le_nth_prime (k - 1)
  omega

/-- The two lower-order terms in Stirling's lower estimate are nonnegative,
so the familiar `k (log k - 1)` lower bound already holds. -/
lemma mul_log_sub_one_le_log_factorial {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * (Real.log k - 1) ≤ Real.log (Nat.factorial k) := by
  have hstirling := Stirling.le_log_factorial_stirling (n := k) (by omega)
  have hlogk : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  have hpi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  nlinarith

/-- A kernel-clean lower bound for the one-based `k`-th prime.  The
numerical cutoff is chosen only so that `psi_upper_linear` applies directly. -/
theorem oneBasedPrime_lower_large {k : ℕ} (hk : 9999 ≤ k) :
    (5 / 6 : ℝ) * k * (Real.log k - 1) ≤ oneBasedPrime k := by
  have hk1 : 1 ≤ k := by omega
  have hpNat : 10000 ≤ oneBasedPrime k :=
    (by omega : 10000 ≤ k + 1).trans (add_one_le_oneBasedPrime hk1)
  have hp : (10000 : ℝ) ≤ oneBasedPrime k := by exact_mod_cast hpNat
  have hfac := mul_log_sub_one_le_log_factorial hk1
  have hfacTheta := log_factorial_le_theta_oneBasedPrime hk1
  have hthetaPsi := Chebyshev.theta_le_psi (oneBasedPrime k : ℝ)
  have hpsi := ElementaryChebyshev.psi_upper_linear
    (oneBasedPrime k : ℝ) hp
  have hchain :
      (k : ℝ) * (Real.log k - 1) ≤
        (6 / 5 : ℝ) * oneBasedPrime k :=
    hfac.trans (hfacTheta.trans (hthetaPsi.trans hpsi))
  nlinarith

/-- If exactly `k` primes are at most `X`, the `k`-th one is at most `X`. -/
lemma oneBasedPrime_le_of_primeCounting_eq {X k : ℕ} (hk : 1 ≤ k)
    (hcount : Nat.primeCounting X = k) :
    oneBasedPrime k ≤ X := by
  have hltCount : k - 1 < Nat.count Nat.Prime (X + 1) := by
    change k - 1 < Nat.primeCounting X
    omega
  exact Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hltCount)

/-- A direct prime-counting criterion for `PrimeIntervalExpansion`.  The
left side counts every prime in `[p,X]`; the right side counts every prime
in `(X,pX]`, allowing `rho` losses for forbidden primes above `p`. -/
lemma primeIntervalExpansion_of_interval_counts {T : Finset ℕ} {p rho : ℕ}
    (hlarge : (T.filter fun r ↦ p < r).card ≤ rho)
    (hcount : ∀ X, p ≤ X →
      (Nat.primesLE X \ Nat.primesLE (p - 1)).card + rho ≤
        (Nat.primesLE (p * X) \ Nat.primesLE X).card) :
    PrimeIntervalExpansion T p := by
  classical
  intro X hpX
  let oldAll := Nat.primesLE X \ Nat.primesLE (p - 1)
  let newAll := Nat.primesLE (p * X) \ Nat.primesLE X
  let excluded := newAll.filter fun r ↦ r ∈ T
  have hOldSub : oldPrimeBand T p X ⊆ oldAll := by
    intro r hr
    rw [mem_oldPrimeBand] at hr
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
    exact ⟨⟨hr.2.2.1, hr.1⟩, fun h ↦ by
      have hrSmall := h.1
      have hrLarge := hr.2.1
      have hrTwo := hr.1.two_le
      omega⟩
  have hExcludedSub : excluded ⊆ T.filter fun r ↦ p < r := by
    intro r hr
    have hrData := Finset.mem_filter.mp hr
    have hrNew := Finset.mem_sdiff.mp hrData.1
    have hrPrimeLe := Nat.mem_primesLE.mp hrNew.1
    have hrNotLe : ¬r ≤ X := by
      intro hrX
      exact hrNew.2 (Nat.mem_primesLE.mpr ⟨hrX, hrPrimeLe.2⟩)
    exact Finset.mem_filter.mpr ⟨hrData.2, hpX.trans_lt (by omega)⟩
  have hNewSplit : newAll = newPrimeBand T p X ∪ excluded := by
    apply Finset.ext
    intro r
    simp only [Finset.mem_union]
    constructor
    · intro hr
      by_cases hrT : r ∈ T
      · exact Or.inr (Finset.mem_filter.mpr ⟨hr, hrT⟩)
      · have hrData := Finset.mem_sdiff.mp hr
        have hrUpper := Nat.mem_primesLE.mp hrData.1
        have hrLower : X < r := by
          by_contra h
          exact hrData.2 (Nat.mem_primesLE.mpr ⟨by omega, hrUpper.2⟩)
        exact Or.inl (mem_newPrimeBand.mpr
          ⟨hrUpper.2, hrLower, hrUpper.1, hrT⟩)
    · rintro (hr | hr)
      · have hrData := mem_newPrimeBand.mp hr
        exact Finset.mem_sdiff.mpr
          ⟨Nat.mem_primesLE.mpr ⟨hrData.2.2.1, hrData.1⟩,
            fun h ↦ by
              have hrLe := (Nat.mem_primesLE.mp h).1
              have hrGt := hrData.2.1
              omega⟩
      · exact (Finset.mem_filter.mp hr).1
  have hDisjoint : Disjoint (newPrimeBand T p X) excluded := by
    rw [Finset.disjoint_left]
    intro r hrNew hrExcluded
    exact (mem_newPrimeBand.mp hrNew).2.2.2 (Finset.mem_filter.mp hrExcluded).2
  have hOldCard := Finset.card_le_card hOldSub
  have hExcludedCard := (Finset.card_le_card hExcludedSub).trans hlarge
  have hSupply := hcount X hpX
  have hSplitCard : newAll.card =
      (newPrimeBand T p X).card + excluded.card := by
    rw [hNewSplit, Finset.card_union_of_disjoint hDisjoint]
  change oldAll.card + rho ≤ newAll.card at hSupply
  rw [hSplitCard] at hSupply
  omega

/-- Prime-counting form of the preceding criterion.  It is the exact
inequality isolated as (3.1) in the source proof, written without choosing
an index for the last prime below `X`. -/
lemma primeIntervalExpansion_of_primeCounting {T : Finset ℕ} {p rho : ℕ}
    (hp : p.Prime)
    (hlarge : (T.filter fun r ↦ p < r).card ≤ rho)
    (hcount : ∀ X, p ≤ X →
      2 * Nat.primeCounting X + rho ≤
        Nat.primeCounting (p * X) + Nat.primeCounting (p - 1)) :
    PrimeIntervalExpansion T p := by
  apply primeIntervalExpansion_of_interval_counts hlarge
  intro X hpX
  have hpPredX : p - 1 ≤ X := by omega
  have hXscale : X ≤ p * X := Nat.le_mul_of_pos_left X hp.pos
  have hsmallSub : Nat.primesLE (p - 1) ⊆ Nat.primesLE X :=
    Nat.primesLE_mono hpPredX
  have hlargeSub : Nat.primesLE X ⊆ Nat.primesLE (p * X) :=
    Nat.primesLE_mono hXscale
  rw [Finset.card_sdiff_of_subset hsmallSub,
    Finset.card_sdiff_of_subset hlargeSub]
  simp only [Nat.primesLE_card_eq_primeCounting]
  have hsmallCount := Nat.monotone_primeCounting hpPredX
  have hlargeCount := Nat.monotone_primeCounting hXscale
  have h := hcount X hpX
  omega

/-- Source form of the conditional hypothesis.  If `p` is the `s`-th
prime and every indexed endpoint has enough primes after multiplication by
`p`, then the value-level prime-counting criterion holds for every cutoff. -/
lemma primeIntervalExpansion_of_indexed_count {T : Finset ℕ}
    {p s rho : ℕ} (hp : p.Prime) (hs : 1 ≤ s)
    (hpIndex : Nat.primeCounting p = s)
    (hlarge : (T.filter fun r ↦ p < r).card ≤ rho)
    (hindexed : ∀ ell, 1 ≤ ell →
      rho + s + 2 * ell - 1 ≤
        Nat.primeCounting (p * oneBasedPrime (s + ell - 1))) :
    PrimeIntervalExpansion T p := by
  apply primeIntervalExpansion_of_primeCounting hp hlarge
  intro X hpX
  let k := Nat.primeCounting X
  have hsk : s ≤ k := by
    change s ≤ Nat.primeCounting X
    rw [← hpIndex]
    exact Nat.monotone_primeCounting hpX
  let ell := k - s + 1
  have hell : 1 ≤ ell := by simp [ell]
  have hindexEq : s + ell - 1 = k := by
    dsimp only [ell]
    omega
  have hkpos : 1 ≤ k := hs.trans hsk
  have hprimeLe : oneBasedPrime k ≤ X :=
    oneBasedPrime_le_of_primeCounting_eq hkpos rfl
  have hscale : p * oneBasedPrime k ≤ p * X :=
    Nat.mul_le_mul_left p hprimeLe
  have hmono := Nat.monotone_primeCounting hscale
  have hsupply := hindexed ell hell
  rw [hindexEq] at hsupply
  have hpPred : Nat.primeCounting (p - 1) + 1 =
      Nat.primeCounting p := by
    rw [Nat.primeCounting_sub_one, Nat.primeCounting_eq_primeCounting'_succ]
    simp only [Nat.primeCounting', Nat.count_succ, hp, if_true]
  change 2 * k + rho ≤
    Nat.primeCounting (p * X) + Nat.primeCounting (p - 1)
  omega

/-- A chosen injection between the two finite prime bands.  Taking
`max p X` makes it total in `X`; all later uses satisfy `p ≤ X`. -/
noncomputable def primeBandEmbedding {T : Finset ℕ} {p : ℕ}
    (h : PrimeIntervalExpansion T p) (X : ℕ) :
    oldPrimeBand T p (max p X) ↪ newPrimeBand T p (max p X) := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using h (max p X) (le_max_left _ _)

/-- Value-level wrapper around `primeBandEmbedding`.  It lets later
arguments rewrite the cutoff without transporting dependent Finset
membership proofs by hand. -/
noncomputable def primeBandMap {T : Finset ℕ} {p : ℕ}
    (h : PrimeIntervalExpansion T p) (X r : ℕ) : ℕ :=
  if hr : r ∈ oldPrimeBand T p (max p X)
  then (primeBandEmbedding h X ⟨r, hr⟩).1
  else 0

lemma primeBandMap_injective_of_mem {T : Finset ℕ} {p X r s : ℕ}
    (h : PrimeIntervalExpansion T p)
    (hr : r ∈ oldPrimeBand T p (max p X))
    (hs : s ∈ oldPrimeBand T p (max p X))
    (hrs : primeBandMap h X r = primeBandMap h X s) :
    r = s := by
  have hImage : primeBandEmbedding h X ⟨r, hr⟩ =
      primeBandEmbedding h X ⟨s, hs⟩ := by
    apply Subtype.ext
    simpa only [primeBandMap, dif_pos hr, dif_pos hs] using hrs
  exact congrArg Subtype.val ((primeBandEmbedding h X).injective hImage)

lemma div_greatestPrimeFactor_mul {m : ℕ} (hm : 1 < m) :
    m / greatestPrimeFactor m * greatestPrimeFactor m = m :=
  Nat.div_mul_cancel (greatestPrimeFactor_dvd hm)

lemma div_greatestPrimeFactor_pos {m : ℕ} (hm : 1 < m) :
    0 < m / greatestPrimeFactor m := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd (by omega) (greatestPrimeFactor_dvd hm)
  · exact (greatestPrimeFactor_prime hm).pos

lemma greatestPrimeFactor_div_le {m : ℕ} (hm : 1 < m) :
    greatestPrimeFactor (m / greatestPrimeFactor m) ≤ greatestPrimeFactor m := by
  apply greatestPrimeFactor_le_of_dvd
  · exact ne_of_gt (div_greatestPrimeFactor_pos hm)
  · exact ne_of_gt (by omega : 0 < m)
  · use greatestPrimeFactor m
    exact (div_greatestPrimeFactor_mul hm).symm

/-- Positive integers at most `U` which avoid every prime in `T`. -/
def sifted (T : Finset ℕ) (U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun m ↦ ∀ p ∈ T, ¬p ∣ m

@[simp] lemma mem_sifted {T : Finset ℕ} {U m : ℕ} :
    m ∈ sifted T U ↔ 1 ≤ m ∧ m ≤ U ∧ ∀ p ∈ T, ¬p ∣ m := by
  simp [sifted, and_assoc]

/-! ### Support-signature fibers for the pull argument -/

/-- The finite set of primes whose presence is recorded in a pull fiber:
all primes up to the deleted prime, together with the endpoint primes. -/
def coreScope (N r : ℕ) : Finset ℕ := Nat.primesLE r ∪ N.primeFactors

/-- The part of the squarefree support of `a` visible to a pull fiber. -/
def supportSignature (N r a : ℕ) : Finset ℕ :=
  a.primeFactors ∩ coreScope N r

/-- Primes in the visible scope which are absent from a signature. -/
def signatureForbidden (N r : ℕ) (S : Finset ℕ) : Finset ℕ :=
  coreScope N r \ S

@[simp] lemma mem_coreScope {N r p : ℕ} :
    p ∈ coreScope N r ↔ (p.Prime ∧ p ≤ r) ∨ p ∈ N.primeFactors := by
  simp [coreScope, Nat.mem_primesLE, and_comm]

lemma prime_of_mem_coreScope {N r p : ℕ} (hp : p ∈ coreScope N r) :
    p.Prime := by
  rcases mem_coreScope.mp hp with hp | hp
  · exact hp.1
  · exact Nat.prime_of_mem_primeFactors hp

lemma supportSignature_subset_scope (N r a : ℕ) :
    supportSignature N r a ⊆ coreScope N r := by
  exact Finset.inter_subset_right

lemma prime_of_mem_supportSignature {N r a p : ℕ}
    (hp : p ∈ supportSignature N r a) : p.Prime := by
  exact prime_of_mem_coreScope (supportSignature_subset_scope N r a hp)

@[simp] lemma mem_signatureForbidden {N r p : ℕ} {S : Finset ℕ} :
    p ∈ signatureForbidden N r S ↔ p ∈ coreScope N r ∧ p ∉ S := by
  simp [signatureForbidden]

lemma signature_prod_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    0 < ∏ p ∈ S, p := by
  exact Finset.prod_pos fun p hp ↦ (hS p hp).pos

/-- Multiplying a signature product by an integer avoiding precisely the
missing visible primes reconstructs that signature exactly. -/
lemma supportSignature_prod_mul {N r m : ℕ} {S : Finset ℕ}
    (hSscope : S ⊆ coreScope N r) (hSprime : ∀ p ∈ S, p.Prime)
    (hm : m ∈ sifted (signatureForbidden N r S) (m + 1)) :
    supportSignature N r ((∏ p ∈ S, p) * m) = S := by
  have hmData := mem_sifted.mp hm
  have hprodPos : 0 < ∏ p ∈ S, p := signature_prod_pos hSprime
  have hmul0 : (∏ p ∈ S, p) * m ≠ 0 :=
    mul_ne_zero (ne_of_gt hprodPos) (by omega)
  ext p
  simp only [supportSignature, Finset.mem_inter]
  constructor
  · rintro ⟨hpFactors, hpScope⟩
    have hp := Nat.prime_of_mem_primeFactors hpFactors
    have hpMul := Nat.dvd_of_mem_primeFactors hpFactors
    rcases hp.dvd_mul.mp hpMul with hpProd | hpM
    · obtain ⟨q, hqS, hpq⟩ :=
        (Prime.dvd_finsetProd_iff hp.prime id).mp hpProd
      have hq := hSprime q hqS
      rcases (Nat.dvd_prime hq).mp hpq with hp1 | hpqEq
      · exact (hp.ne_one hp1).elim
      · simpa [hpqEq] using hqS
    · by_contra hpS
      exact hmData.2.2 p (mem_signatureForbidden.mpr ⟨hpScope, hpS⟩) hpM
  · intro hpS
    refine ⟨Nat.mem_primeFactors.mpr ⟨hSprime p hpS, ?_, hmul0⟩,
      hSscope hpS⟩
    exact (Finset.dvd_prod_of_mem id hpS).trans (dvd_mul_right _ m)


def supportFiber (N r : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (interval N).filter fun a ↦ supportSignature N r a = S

@[simp] lemma mem_supportFiber {N r a : ℕ} {S : Finset ℕ} :
    a ∈ supportFiber N r S ↔
      1 ≤ a ∧ a ≤ N ∧ supportSignature N r a = S := by
  simp [supportFiber, and_assoc]

lemma supportFiber_eq_image_sifted {N r : ℕ} {S : Finset ℕ}
    (hSscope : S ⊆ coreScope N r) (hSprime : ∀ p ∈ S, p.Prime) :
    supportFiber N r S =
      (sifted (signatureForbidden N r S) (N / ∏ p ∈ S, p)).image
        (fun m ↦ (∏ p ∈ S, p) * m) := by
  classical
  let C := ∏ p ∈ S, p
  have hCpos : 0 < C := signature_prod_pos hSprime
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨ha1, haN, hsig⟩ := mem_supportFiber.mp ha
    have ha0 : a ≠ 0 := by omega
    have hCa : C ∣ a := by
      apply Finset.prod_primes_dvd a
      · intro p hp
        exact (hSprime p hp).prime
      · intro p hp
        apply Nat.dvd_of_mem_primeFactors
        have hpSig : p ∈ supportSignature N r a := by simpa [hsig] using hp
        exact (Finset.mem_inter.mp hpSig).1
    have hquot : a / C ∈ sifted (signatureForbidden N r S) (N / C) := by
      apply mem_sifted.mpr
      refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hCa) hCpos, Nat.div_le_div_right haN, ?_⟩
      intro p hpForbidden hpDiv
      have hp := prime_of_mem_coreScope (mem_signatureForbidden.mp hpForbidden).1
      have hpa : p ∣ a := hpDiv.trans (Nat.div_dvd_of_dvd hCa)
      have hpFactors : p ∈ a.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hpa, ha0⟩
      have hpSig : p ∈ supportSignature N r a :=
        Finset.mem_inter.mpr ⟨hpFactors, (mem_signatureForbidden.mp hpForbidden).1⟩
      exact (mem_signatureForbidden.mp hpForbidden).2 (by simpa [hsig] using hpSig)
    rw [Finset.mem_image]
    refine ⟨a / C, hquot, ?_⟩
    simpa [C] using Nat.mul_div_cancel' hCa
  · intro ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    have hmData := mem_sifted.mp hm
    apply mem_supportFiber.mpr
    refine ⟨Nat.mul_pos hCpos hmData.1, ?_, ?_⟩
    · calc
        C * m ≤ C * (N / C) := Nat.mul_le_mul_left C hmData.2.1
        _ ≤ N := Nat.mul_div_le N C
    · apply supportSignature_prod_mul hSscope hSprime
      exact mem_sifted.mpr ⟨hmData.1, by omega, hmData.2.2⟩

lemma card_supportFiber {N r : ℕ} {S : Finset ℕ}
    (hSscope : S ⊆ coreScope N r) (hSprime : ∀ p ∈ S, p.Prime) :
    (supportFiber N r S).card =
      (sifted (signatureForbidden N r S) (N / ∏ p ∈ S, p)).card := by
  rw [supportFiber_eq_image_sifted hSscope hSprime,
    Finset.card_image_of_injective]
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left (signature_prod_pos hSprime) hab

lemma squarefree_dvd_iff_dvd_signatureProd {N r g a : ℕ}
    (hg : Squarefree g) (ha0 : a ≠ 0)
    (hgscope : g.primeFactors ⊆ coreScope N r) :
    g ∣ a ↔ g ∣ ∏ p ∈ supportSignature N r a, p := by
  constructor
  · intro hga
    rw [← Nat.prod_primeFactors_of_squarefree hg]
    apply Finset.prod_dvd_prod_of_subset _ _ id
    intro p hp
    exact Finset.mem_inter.mpr ⟨Nat.primeFactors_mono hga ha0 hp, hgscope hp⟩
  · intro hprod
    rw [← Nat.prod_primeFactors_of_squarefree hg] at hprod ⊢
    apply hprod.trans
    apply Finset.prod_primes_dvd a
    · intro p hp
      exact (prime_of_mem_supportSignature hp).prime
    · intro p hp
      exact Nat.dvd_of_mem_primeFactors (Finset.mem_inter.mp hp).1

def relaxedSupportFiber (N r : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (interval N).filter fun a ↦ (supportSignature N r a).erase r = S.erase r

@[simp] lemma mem_relaxedSupportFiber {N r a : ℕ} {S : Finset ℕ} :
    a ∈ relaxedSupportFiber N r S ↔
      1 ≤ a ∧ a ≤ N ∧
        (supportSignature N r a).erase r = S.erase r := by
  simp [relaxedSupportFiber, and_assoc]

lemma erased_supportSignature_prod_erase_mul {N r m : ℕ} {S : Finset ℕ}
    (hrS : r ∈ S) (hSscope : S ⊆ coreScope N r)
    (hSprime : ∀ p ∈ S, p.Prime)
    (hm : m ∈ sifted (signatureForbidden N r S) (m + 1)) :
    (supportSignature N r ((∏ p ∈ S.erase r, p) * m)).erase r =
      S.erase r := by
  have hmData := mem_sifted.mp hm
  have hEraseScope : S.erase r ⊆ coreScope N r :=
    fun p hp ↦ hSscope (Finset.mem_of_mem_erase hp)
  have hErasePrime : ∀ p ∈ S.erase r, p.Prime :=
    fun p hp ↦ hSprime p (Finset.mem_of_mem_erase hp)
  have hprodPos : 0 < ∏ p ∈ S.erase r, p := signature_prod_pos hErasePrime
  have hmul0 : (∏ p ∈ S.erase r, p) * m ≠ 0 :=
    mul_ne_zero (ne_of_gt hprodPos) (by omega)
  ext p
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hpr, hpSig⟩
    refine ⟨hpr, ?_⟩
    have hpFactors := (Finset.mem_inter.mp hpSig).1
    have hpScope := (Finset.mem_inter.mp hpSig).2
    have hp := Nat.prime_of_mem_primeFactors hpFactors
    have hpMul := Nat.dvd_of_mem_primeFactors hpFactors
    rcases hp.dvd_mul.mp hpMul with hpProd | hpM
    · obtain ⟨q, hqS, hpq⟩ :=
        (Prime.dvd_finsetProd_iff hp.prime id).mp hpProd
      have hq := hErasePrime q hqS
      rcases (Nat.dvd_prime hq).mp hpq with hp1 | hpqEq
      · exact (hp.ne_one hp1).elim
      · simpa [hpqEq] using Finset.mem_of_mem_erase hqS
    · by_contra hpS
      exact hmData.2.2 p (mem_signatureForbidden.mpr ⟨hpScope, hpS⟩) hpM
  · rintro ⟨hpr, hpS⟩
    have hpErase : p ∈ S.erase r := Finset.mem_erase.mpr ⟨hpr, hpS⟩
    refine ⟨hpr, Finset.mem_inter.mpr ⟨?_, hSscope hpS⟩⟩
    refine Nat.mem_primeFactors.mpr ⟨hSprime p hpS, ?_, hmul0⟩
    exact (Finset.dvd_prod_of_mem id hpErase).trans (dvd_mul_right _ m)

lemma relaxedSupportFiber_eq_image_sifted {N r : ℕ} {S : Finset ℕ}
    (hrS : r ∈ S) (hSscope : S ⊆ coreScope N r)
    (hSprime : ∀ p ∈ S, p.Prime) :
    relaxedSupportFiber N r S =
      (sifted (signatureForbidden N r S)
        (N / ∏ p ∈ S.erase r, p)).image
        (fun m ↦ (∏ p ∈ S.erase r, p) * m) := by
  classical
  let B := ∏ p ∈ S.erase r, p
  have hErasePrime : ∀ p ∈ S.erase r, p.Prime :=
    fun p hp ↦ hSprime p (Finset.mem_of_mem_erase hp)
  have hBpos : 0 < B := signature_prod_pos hErasePrime
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨ha1, haN, hsig⟩ := mem_relaxedSupportFiber.mp ha
    have ha0 : a ≠ 0 := by omega
    have hBa : B ∣ a := by
      apply Finset.prod_primes_dvd a
      · intro p hp
        exact (hErasePrime p hp).prime
      · intro p hp
        apply Nat.dvd_of_mem_primeFactors
        have hpSig : p ∈ (supportSignature N r a).erase r := by
          simpa [hsig] using hp
        exact (Finset.mem_inter.mp (Finset.mem_of_mem_erase hpSig)).1
    have hquot : a / B ∈ sifted (signatureForbidden N r S) (N / B) := by
      apply mem_sifted.mpr
      refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hBa) hBpos,
        Nat.div_le_div_right haN, ?_⟩
      intro p hpForbidden hpDiv
      have hpScope := (mem_signatureForbidden.mp hpForbidden).1
      have hp := prime_of_mem_coreScope hpScope
      have hpa : p ∣ a := hpDiv.trans (Nat.div_dvd_of_dvd hBa)
      have hpFactors : p ∈ a.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hpa, ha0⟩
      have hpSig : p ∈ supportSignature N r a :=
        Finset.mem_inter.mpr ⟨hpFactors, hpScope⟩
      have hpr : p ≠ r := by
        intro h
        subst p
        exact (mem_signatureForbidden.mp hpForbidden).2 hrS
      have hpErase : p ∈ (supportSignature N r a).erase r :=
        Finset.mem_erase.mpr ⟨hpr, hpSig⟩
      exact (mem_signatureForbidden.mp hpForbidden).2
        (Finset.mem_of_mem_erase (by simpa [hsig] using hpErase))
    rw [Finset.mem_image]
    refine ⟨a / B, hquot, ?_⟩
    simpa [B] using Nat.mul_div_cancel' hBa
  · intro ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    have hmData := mem_sifted.mp hm
    apply mem_relaxedSupportFiber.mpr
    refine ⟨Nat.mul_pos hBpos hmData.1, ?_, ?_⟩
    · calc
        B * m ≤ B * (N / B) := Nat.mul_le_mul_left B hmData.2.1
        _ ≤ N := Nat.mul_div_le N B
    · apply erased_supportSignature_prod_erase_mul hrS hSscope hSprime
      exact mem_sifted.mpr ⟨hmData.1, by omega, hmData.2.2⟩

lemma card_relaxedSupportFiber {N r : ℕ} {S : Finset ℕ}
    (hrS : r ∈ S) (hSscope : S ⊆ coreScope N r)
    (hSprime : ∀ p ∈ S, p.Prime) :
    (relaxedSupportFiber N r S).card =
      (sifted (signatureForbidden N r S)
        (N / ∏ p ∈ S.erase r, p)).card := by
  rw [relaxedSupportFiber_eq_image_sifted hrS hSscope hSprime,
    Finset.card_image_of_injective]
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left
    (signature_prod_pos fun p hp ↦ hSprime p (Finset.mem_of_mem_erase hp)) hab

lemma ordCompl_signatureProd_eq_prod_erase {N r : ℕ} {S : Finset ℕ}
    (hrS : r ∈ S) (hSprime : ∀ p ∈ S, p.Prime) :
    ordCompl[r] (∏ p ∈ S, p) = ∏ p ∈ S.erase r, p := by
  have hr := hSprime r hrS
  have hprodSq : Squarefree (∏ p ∈ S, p) := by
    have hrad : radical (∏ p ∈ S, p) = ∏ p ∈ S, p := by
      rw [Nat.radical_eq_prod_primeFactors, Nat.primeFactors_prod hSprime]
    rw [← hrad]
    exact squarefree_radical
  apply Nat.eq_of_mul_eq_mul_right hr.pos
  calc
    ordCompl[r] (∏ p ∈ S, p) * r = ∏ p ∈ S, p :=
      ordCompl_mul_prime_eq_of_squarefree hr hprodSq
        (Finset.dvd_prod_of_mem id hrS)
    _ = (∏ p ∈ S.erase r, p) * r :=
      (Finset.prod_erase_mul S id hrS).symm

/-- Whether a visible support signature contributes to a generated
remainder: it contains a top generator but no lower generator. -/
def remainderSignatureGood (L R S : Finset ℕ) : Prop :=
  (∃ g ∈ R, g ∣ ∏ p ∈ S, p) ∧
    ∀ l ∈ L, ¬l ∣ ∏ p ∈ S, p

/-- All visible signatures which contribute to a generated remainder. -/
noncomputable def activeRemainderSignatures (N r : ℕ) (L R : Finset ℕ) :
    Finset (Finset ℕ) := by
  classical
  exact (coreScope N r).powerset.filter (remainderSignatureGood L R)

@[simp] lemma mem_activeRemainderSignatures {N r : ℕ}
    {L R S : Finset ℕ} :
    S ∈ activeRemainderSignatures N r L R ↔
      S ⊆ coreScope N r ∧ remainderSignatureGood L R S := by
  simp [activeRemainderSignatures]

lemma squarefree_dvd_prod_of_primeFactors_subset {g : ℕ} {S : Finset ℕ}
    (hg : Squarefree g) (hsub : g.primeFactors ⊆ S) :
    g ∣ ∏ p ∈ S, p := by
  rw [← Nat.prod_primeFactors_of_squarefree hg]
  exact Finset.prod_dvd_prod_of_subset _ _ id hsub

lemma mem_generatedRemainder_iff_signatureGood
    {N r a : ℕ} {L R : Finset ℕ}
    (hsq : ∀ g ∈ L ∪ R, Squarefree g)
    (hscope : ∀ g ∈ L ∪ R, g.primeFactors ⊆ coreScope N r) :
    a ∈ generatedRemainder N L R ↔
      a ∈ interval N ∧ remainderSignatureGood L R (supportSignature N r a) := by
  constructor
  · intro ha
    obtain ⟨ha1, haN, ⟨g, hgR, hga⟩, haLower⟩ :=
      mem_generatedRemainder.mp ha
    have ha0 : a ≠ 0 := by omega
    refine ⟨mem_interval.mpr ⟨ha1, haN⟩, ⟨?_, ?_⟩⟩
    · refine ⟨g, hgR, ?_⟩
      exact (squarefree_dvd_iff_dvd_signatureProd
        (hsq g (Finset.mem_union_right L hgR)) ha0
        (hscope g (Finset.mem_union_right L hgR))).mp hga
    · intro l hlL hlSig
      apply haLower
      exact mem_multiplesBelow.mpr ⟨ha1, haN, l, hlL,
        (squarefree_dvd_iff_dvd_signatureProd
          (hsq l (Finset.mem_union_left R hlL)) ha0
          (hscope l (Finset.mem_union_left R hlL))).mpr hlSig⟩
  · rintro ⟨haInterval, hgood⟩
    obtain ⟨ha1, haN⟩ := mem_interval.mp haInterval
    have ha0 : a ≠ 0 := by omega
    apply mem_generatedRemainder.mpr
    refine ⟨ha1, haN, ?_, ?_⟩
    · obtain ⟨g, hgR, hgSig⟩ := hgood.1
      exact ⟨g, hgR, (squarefree_dvd_iff_dvd_signatureProd
        (hsq g (Finset.mem_union_right L hgR)) ha0
        (hscope g (Finset.mem_union_right L hgR))).mpr hgSig⟩
    · intro haLower
      obtain ⟨_ha1, _haN, l, hlL, hla⟩ := mem_multiplesBelow.mp haLower
      exact hgood.2 l hlL
        ((squarefree_dvd_iff_dvd_signatureProd
          (hsq l (Finset.mem_union_left R hlL)) ha0
          (hscope l (Finset.mem_union_left R hlL))).mp hla)

lemma generatedRemainder_eq_biUnion_supportFibers
    {N r : ℕ} {L R : Finset ℕ}
    (hsq : ∀ g ∈ L ∪ R, Squarefree g)
    (hscope : ∀ g ∈ L ∪ R, g.primeFactors ⊆ coreScope N r) :
    generatedRemainder N L R =
      (activeRemainderSignatures N r L R).biUnion (supportFiber N r) := by
  apply Finset.ext
  intro a
  constructor
  · intro ha
    have haData := (mem_generatedRemainder_iff_signatureGood hsq hscope).mp ha
    apply Finset.mem_biUnion.mpr
    refine ⟨supportSignature N r a, ?_, ?_⟩
    · exact mem_activeRemainderSignatures.mpr
        ⟨supportSignature_subset_scope N r a, haData.2⟩
    · exact mem_supportFiber.mpr
        ⟨(mem_interval.mp haData.1).1, (mem_interval.mp haData.1).2, rfl⟩
  · intro ha
    obtain ⟨S, hSactive, haFiber⟩ := Finset.mem_biUnion.mp ha
    have hS := mem_activeRemainderSignatures.mp hSactive
    have haData := mem_supportFiber.mp haFiber
    apply (mem_generatedRemainder_iff_signatureGood hsq hscope).mpr
    exact ⟨mem_interval.mpr ⟨haData.1, haData.2.1⟩, haData.2.2 ▸ hS.2⟩

lemma supportFibers_pairwiseDisjoint (N r : ℕ) :
    (Set.univ : Set (Finset ℕ)).PairwiseDisjoint (supportFiber N r) := by
  intro S _ T _ hST
  change Disjoint (supportFiber N r S) (supportFiber N r T)
  rw [Finset.disjoint_left]
  intro a haS haT
  have hS := (mem_supportFiber.mp haS).2.2
  have hT := (mem_supportFiber.mp haT).2.2
  exact hST (hS.symm.trans hT)

lemma active_signature_contains_pull_prime
    {N r : ℕ} {L R S : Finset ℕ}
    (hr : r.Prime) (hrR : ∀ g ∈ R, r ∣ g)
    (hS : S ∈ activeRemainderSignatures N r L R) : r ∈ S := by
  obtain ⟨g, hgR, hgS⟩ := (mem_activeRemainderSignatures.mp hS).2.1
  have hrProd := (hrR g hgR).trans hgS
  obtain ⟨q, hqS, hrq⟩ := (Prime.dvd_finsetProd_iff hr.prime id).mp hrProd
  have hq := prime_of_mem_coreScope
    ((mem_activeRemainderSignatures.mp hS).1 hqS)
  rcases (Nat.dvd_prime hq).mp hrq with hr1 | hrqEq
  · exact (hr.ne_one hr1).elim
  · simpa [hrqEq] using hqS

lemma relaxedSupportFibers_pairwiseDisjoint_on_active
    {N r : ℕ} {L R : Finset ℕ} (hr : r.Prime)
    (hrR : ∀ g ∈ R, r ∣ g) :
    ((activeRemainderSignatures N r L R : Finset (Finset ℕ)) :
      Set (Finset ℕ)).PairwiseDisjoint (relaxedSupportFiber N r) := by
  intro S hS T hT hST
  change Disjoint (relaxedSupportFiber N r S) (relaxedSupportFiber N r T)
  rw [Finset.disjoint_left]
  intro a haS haT
  have hErase := (mem_relaxedSupportFiber.mp haS).2.2.symm.trans
    (mem_relaxedSupportFiber.mp haT).2.2
  have hrS := active_signature_contains_pull_prime hr hrR hS
  have hrT := active_signature_contains_pull_prime hr hrR hT
  apply hST
  ext p
  by_cases hpr : p = r
  · subst p
    simp [hrS, hrT]
  · simpa [Finset.mem_erase, hpr] using Finset.ext_iff.mp hErase p

lemma prod_erase_dvd_of_mem_relaxedSupportFiber
    {N r a : ℕ} {S : Finset ℕ} (ha : a ∈ relaxedSupportFiber N r S)
    (hSprime : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S.erase r, p) ∣ a := by
  have haData := mem_relaxedSupportFiber.mp ha
  apply Finset.prod_primes_dvd a
  · intro p hp
    exact (hSprime p (Finset.mem_of_mem_erase hp)).prime
  · intro p hp
    apply Nat.dvd_of_mem_primeFactors
    have hpCurrent : p ∈ (supportSignature N r a).erase r := by
      rw [haData.2.2]
      exact hp
    exact (Finset.mem_inter.mp (Finset.mem_of_mem_erase hpCurrent)).1

lemma biUnion_relaxedSupportFibers_subset_pull_remainder
    {N r : ℕ} {L R : Finset ℕ}
    (hr : r.Prime) (hrL : ∀ l ∈ L, ¬r ∣ l)
    (hrR : ∀ g ∈ R, r ∣ g)
    (hsq : ∀ g ∈ L ∪ R, Squarefree g)
    (hscope : ∀ g ∈ L ∪ R, g.primeFactors ⊆ coreScope N r) :
    (activeRemainderSignatures N r L R).biUnion
        (relaxedSupportFiber N r) ⊆
      generatedRemainder N L (pullGenerators r R) := by
  intro a ha
  obtain ⟨S, hSactive, haFiber⟩ := Finset.mem_biUnion.mp ha
  have hS := mem_activeRemainderSignatures.mp hSactive
  have hrS := active_signature_contains_pull_prime hr hrR hSactive
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp ↦
    prime_of_mem_coreScope (hS.1 hp)
  have haData := mem_relaxedSupportFiber.mp haFiber
  apply mem_generatedRemainder.mpr
  refine ⟨haData.1, haData.2.1, ?_, ?_⟩
  · obtain ⟨g, hgR, hgProd⟩ := hS.2.1
    refine ⟨ordCompl[r] g, mem_pullGenerators.mpr ⟨g, hgR, rfl⟩, ?_⟩
    have hcompl := Nat.ordCompl_dvd_ordCompl_of_dvd hgProd r
    rw [ordCompl_signatureProd_eq_prod_erase (N := N) hrS hSprime] at hcompl
    exact dvd_trans hcompl
      (prod_erase_dvd_of_mem_relaxedSupportFiber haFiber hSprime)
  · intro haLower
    obtain ⟨_ha1, _haN, l, hlL, hla⟩ := mem_multiplesBelow.mp haLower
    apply hS.2.2 l hlL
    apply squarefree_dvd_prod_of_primeFactors_subset
      (hsq l (Finset.mem_union_left R hlL))
    intro p hpL
    have hpA : p ∈ a.primeFactors :=
      Nat.primeFactors_mono hla (by omega) hpL
    have hpScope := hscope l (Finset.mem_union_left R hlL) hpL
    have hpSig : p ∈ supportSignature N r a :=
      Finset.mem_inter.mpr ⟨hpA, hpScope⟩
    have hpr : p ≠ r := by
      intro h
      subst p
      exact hrL l hlL (Nat.dvd_of_mem_primeFactors hpL)
    have hpErase : p ∈ (supportSignature N r a).erase r :=
      Finset.mem_erase.mpr ⟨hpr, hpSig⟩
    have : p ∈ S.erase r := by simpa [haData.2.2] using hpErase
    exact Finset.mem_of_mem_erase this

theorem generatedRemainder_pull_doubling_of_fibers
    {N r : ℕ} {L R : Finset ℕ}
    (hr : r.Prime) (hrL : ∀ l ∈ L, ¬r ∣ l)
    (hrR : ∀ g ∈ R, r ∣ g)
    (hsq : ∀ g ∈ L ∪ R, Squarefree g)
    (hscope : ∀ g ∈ L ∪ R, g.primeFactors ⊆ coreScope N r)
    (hdouble : ∀ S ∈ activeRemainderSignatures N r L R,
      2 * (sifted (signatureForbidden N r S)
        (N / ∏ p ∈ S, p)).card ≤
      (sifted (signatureForbidden N r S)
        (N / ∏ p ∈ S.erase r, p)).card) :
    2 * (generatedRemainder N L R).card ≤
      (generatedRemainder N L (pullGenerators r R)).card := by
  let I := activeRemainderSignatures N r L R
  have hOld := generatedRemainder_eq_biUnion_supportFibers hsq hscope
  have hNew := biUnion_relaxedSupportFibers_subset_pull_remainder
    hr hrL hrR hsq hscope
  have hOldCard : (generatedRemainder N L R).card =
      ∑ S ∈ I, (supportFiber N r S).card := by
    rw [hOld, Finset.card_biUnion]
    intro S _ T _ hST
    exact supportFibers_pairwiseDisjoint N r (Set.mem_univ S)
      (Set.mem_univ T) hST
  have hRelaxCard : (I.biUnion (relaxedSupportFiber N r)).card =
      ∑ S ∈ I, (relaxedSupportFiber N r S).card := by
    rw [Finset.card_biUnion]
    exact relaxedSupportFibers_pairwiseDisjoint_on_active hr hrR
  calc
    2 * (generatedRemainder N L R).card =
        ∑ S ∈ I, 2 * (supportFiber N r S).card := by
      rw [hOldCard, Finset.mul_sum]
    _ ≤ ∑ S ∈ I, (relaxedSupportFiber N r S).card := by
      apply Finset.sum_le_sum
      intro S hSI
      have hS := mem_activeRemainderSignatures.mp hSI
      have hSprime : ∀ p ∈ S, p.Prime := fun p hp ↦
        prime_of_mem_coreScope (hS.1 hp)
      rw [card_supportFiber hS.1 hSprime,
        card_relaxedSupportFiber
          (active_signature_contains_pull_prime hr hrR hSI) hS.1 hSprime]
      exact hdouble S hSI
    _ = (I.biUnion (relaxedSupportFiber N r)).card := hRelaxCard.symm
    _ ≤ (generatedRemainder N L (pullGenerators r R)).card :=
      Finset.card_le_card hNew

lemma base_le_greatestPrimeFactor_of_sifted {T : Finset ℕ} {p U m : ℕ}
    (hsmall : ∀ r, r.Prime → r < p → r ∈ T)
    (hm : m ∈ sifted T U) (hm1 : m ≠ 1) :
    p ≤ greatestPrimeFactor m := by
  have hmData := mem_sifted.mp hm
  have hmgt : 1 < m := by omega
  by_contra h
  have hlt : greatestPrimeFactor m < p := by omega
  exact hmData.2.2 _ (hsmall _ (greatestPrimeFactor_prime hmgt) hlt)
    (greatestPrimeFactor_dvd hmgt)

lemma greatestPrimeFactor_le_div_cutoff {T : Finset ℕ} {U m : ℕ}
    (hm : m ∈ sifted T U) (hm1 : m ≠ 1) :
    greatestPrimeFactor m ≤ U / (m / greatestPrimeFactor m) := by
  have hmgt : 1 < m := by
    have := (mem_sifted.mp hm).1
    omega
  apply (Nat.le_div_iff_mul_le (div_greatestPrimeFactor_pos hmgt)).2
  calc
    greatestPrimeFactor m * (m / greatestPrimeFactor m) = m := by
      rw [mul_comm, div_greatestPrimeFactor_mul hmgt]
    _ ≤ U := (mem_sifted.mp hm).2.1

/-- The new prime assigned to a nontrivial sifted integer in its
greatest-prime-factor fiber. -/
noncomputable def expandedPrime {T : Finset ℕ} {p U : ℕ}
    (hsmall : ∀ r, r.Prime → r < p → r ∈ T)
    (hexpand : PrimeIntervalExpansion T p)
    (m : ↥(sifted T U)) (hm1 : m.1 ≠ 1) : ℕ :=
  primeBandMap hexpand (U / (m.1 / greatestPrimeFactor m.1))
    (greatestPrimeFactor m.1)

lemma expandedPrime_spec {T : Finset ℕ} {p U : ℕ}
    (hsmall : ∀ r, r.Prime → r < p → r ∈ T)
    (hexpand : PrimeIntervalExpansion T p)
    (m : ↥(sifted T U)) (hm1 : m.1 ≠ 1) :
    let X := U / (m.1 / greatestPrimeFactor m.1)
    (expandedPrime hsmall hexpand m hm1).Prime ∧
      X < expandedPrime hsmall hexpand m hm1 ∧
      expandedPrime hsmall hexpand m hm1 ≤ p * X ∧
      expandedPrime hsmall hexpand m hm1 ∉ T := by
  dsimp only
  have hpX : p ≤ U / (m.1 / greatestPrimeFactor m.1) :=
    (base_le_greatestPrimeFactor_of_sifted hsmall m.2 hm1).trans
      (greatestPrimeFactor_le_div_cutoff m.2 hm1)
  have hOld : greatestPrimeFactor m.1 ∈ oldPrimeBand T p
      (max p (U / (m.1 / greatestPrimeFactor m.1))) :=
    mem_oldPrimeBand.mpr
      ⟨greatestPrimeFactor_prime (by
          have := (mem_sifted.mp m.2).1
          omega),
        base_le_greatestPrimeFactor_of_sifted hsmall m.2 hm1,
        (greatestPrimeFactor_le_div_cutoff m.2 hm1).trans
          (le_max_right _ _),
        fun hmem ↦ (mem_sifted.mp m.2).2.2 _ hmem
          (greatestPrimeFactor_dvd (by
            have := (mem_sifted.mp m.2).1
            omega))⟩
  have hmem := (primeBandEmbedding hexpand
    (U / (m.1 / greatestPrimeFactor m.1))
    ⟨greatestPrimeFactor m.1, hOld⟩).2
  rw [mem_newPrimeBand] at hmem
  have hExpanded : expandedPrime hsmall hexpand m hm1 =
      (primeBandEmbedding hexpand
        (U / (m.1 / greatestPrimeFactor m.1))
        ⟨greatestPrimeFactor m.1, hOld⟩).1 := by
    simp only [expandedPrime, primeBandMap, dif_pos hOld]
  rw [hExpanded]
  refine ⟨hmem.1, (le_max_right _ _).trans_lt hmem.2.1, ?_, hmem.2.2.2⟩
  simpa only [max_eq_right hpX] using hmem.2.2.1

/-- The second-copy injection used in conditional sieve doubling. -/
noncomputable def sieveLift {T : Finset ℕ} {p U : ℕ}
    (hsmall : ∀ r, r.Prime → r < p → r ∈ T)
    (hexpand : PrimeIntervalExpansion T p)
    (m : ↥(sifted T U)) : ℕ :=
  if hm1 : m.1 = 1 then p ^ (Nat.log p U + 1)
  else (m.1 / greatestPrimeFactor m.1) * expandedPrime hsmall hexpand m hm1

lemma sieveLift_mem_new_layer {T : Finset ℕ} {p U : ℕ}
    (hp : p.Prime) (hpT : p ∉ T) (hT : ∀ r ∈ T, r.Prime)
    (hU : p ≤ U)
    (hsmall : ∀ r, r.Prime → r < p → r ∈ T)
    (hexpand : PrimeIntervalExpansion T p)
    (m : ↥(sifted T U)) :
    sieveLift hsmall hexpand m ∈ sifted T (p * U) ∧
      U < sieveLift hsmall hexpand m := by
  by_cases hm1 : m.1 = 1
  · have hk : Nat.log p U + 1 ≠ 0 := by omega
    have hpowPos : 0 < p ^ (Nat.log p U + 1) := pow_pos hp.pos _
    have hpowGt : U < p ^ (Nat.log p U + 1) := by
      simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hp.one_lt U
    have hpowLe : p ^ (Nat.log p U + 1) ≤ p * U := by
      have hlog := Nat.pow_log_le_self p (ne_of_gt (hp.pos.trans_le hU))
      calc
        p ^ (Nat.log p U + 1) = p ^ Nat.log p U * p := by rw [pow_add, pow_one]
        _ ≤ U * p := Nat.mul_le_mul_right p hlog
        _ = p * U := Nat.mul_comm U p
    rw [sieveLift, dif_pos hm1]
    refine ⟨mem_sifted.mpr ⟨hpowPos, hpowLe, ?_⟩, hpowGt⟩
    intro r hrT hrdvd
    have hr := hT r hrT
    have hrp : r ∣ p := hr.dvd_of_dvd_pow hrdvd
    rcases (Nat.dvd_prime hp).mp hrp with h | h
    · exact hr.ne_one h
    · exact hpT (h ▸ hrT)
  · have hmData := mem_sifted.mp m.2
    have hmgt : 1 < m.1 := by omega
    let b := m.1 / greatestPrimeFactor m.1
    let r := expandedPrime hsmall hexpand m hm1
    have hb : 0 < b := div_greatestPrimeFactor_pos hmgt
    have hrspec := expandedPrime_spec hsmall hexpand m hm1
    have hrPrime : r.Prime := hrspec.1
    have hrLower : U / b < r := hrspec.2.1
    have hrUpper : r ≤ p * (U / b) := hrspec.2.2.1
    have hrT : r ∉ T := hrspec.2.2.2
    have hnewPos : 0 < b * r := Nat.mul_pos hb hrPrime.pos
    have hnewGt : U < b * r := by
      have := (Nat.div_lt_iff_lt_mul hb).mp hrLower
      simpa [mul_comm] using this
    have hnewLe : b * r ≤ p * U := by
      calc
        b * r ≤ b * (p * (U / b)) := Nat.mul_le_mul_left b hrUpper
        _ = p * (b * (U / b)) := by ring
        _ ≤ p * U := Nat.mul_le_mul_left p (Nat.mul_div_le U b)
    rw [sieveLift, dif_neg hm1]
    change b * r ∈ sifted T (p * U) ∧ U < b * r
    refine ⟨mem_sifted.mpr ⟨hnewPos, hnewLe, ?_⟩, hnewGt⟩
    intro t htT htdvd
    have ht := hT t htT
    rcases ht.dvd_mul.mp htdvd with htb | htr
    · have hbm : b ∣ m.1 := by
        use greatestPrimeFactor m.1
        exact (div_greatestPrimeFactor_mul hmgt).symm
      exact hmData.2.2 t htT (htb.trans hbm)
    · rcases (Nat.dvd_prime hrPrime).mp htr with h | h
      · exact ht.ne_one h
      · exact hrT (h ▸ htT)

/-- On every nontrivial greatest-prime-factor fiber, the newly assigned
prime is the greatest prime factor of the lifted integer. -/
lemma greatestPrimeFactor_sieveLift_of_ne_one {T : Finset ℕ} {p U : ℕ}
    (hsmall : ∀ r, r.Prime → r < p → r ∈ T)
    (hexpand : PrimeIntervalExpansion T p)
    (m : ↥(sifted T U)) (hm1 : m.1 ≠ 1) :
    greatestPrimeFactor (sieveLift hsmall hexpand m) =
      expandedPrime hsmall hexpand m hm1 := by
  have hmgt : 1 < m.1 := by
    have := (mem_sifted.mp m.2).1
    omega
  have hb : 0 < m.1 / greatestPrimeFactor m.1 :=
    div_greatestPrimeFactor_pos hmgt
  have hrspec := expandedPrime_spec hsmall hexpand m hm1
  rw [sieveLift, dif_neg hm1]
  apply greatestPrimeFactor_mul_eq_right hb hrspec.1
  exact (greatestPrimeFactor_div_le hmgt).trans
    ((greatestPrimeFactor_le_div_cutoff m.2 hm1).trans hrspec.2.1.le)

/-- If two nontrivial inputs have the same greatest-prime-factor-free core
and receive the same expanded prime, then their old greatest prime factors
are equal.  This is precisely injectivity of the chosen finite prime-band
embedding, with the dependent membership proofs hidden by proof
irrelevance. -/
lemma greatestPrimeFactor_eq_of_core_eq_of_expandedPrime_eq
    {T : Finset ℕ} {p U : ℕ}
    (hsmall : ∀ r, r.Prime → r < p → r ∈ T)
    (hexpand : PrimeIntervalExpansion T p)
    (a b : ↥(sifted T U)) (ha1 : a.1 ≠ 1) (hb1 : b.1 ≠ 1)
    (hcore : a.1 / greatestPrimeFactor a.1 =
      b.1 / greatestPrimeFactor b.1)
    (hexpanded : expandedPrime hsmall hexpand a ha1 =
      expandedPrime hsmall hexpand b hb1) :
    greatestPrimeFactor a.1 = greatestPrimeFactor b.1 := by
  let c := a.1 / greatestPrimeFactor a.1
  have haOld : greatestPrimeFactor a.1 ∈ oldPrimeBand T p (max p (U / c)) := by
    rw [mem_oldPrimeBand]
    refine ⟨greatestPrimeFactor_prime (by
        have := (mem_sifted.mp a.2).1
        omega),
      base_le_greatestPrimeFactor_of_sifted hsmall a.2 ha1, ?_, ?_⟩
    · exact (greatestPrimeFactor_le_div_cutoff a.2 ha1).trans
        (le_max_right _ _)
    · intro hmem
      exact (mem_sifted.mp a.2).2.2 _ hmem
        (greatestPrimeFactor_dvd (by
          have := (mem_sifted.mp a.2).1
          omega))
  have hbOld : greatestPrimeFactor b.1 ∈ oldPrimeBand T p (max p (U / c)) := by
    rw [mem_oldPrimeBand]
    refine ⟨greatestPrimeFactor_prime (by
        have := (mem_sifted.mp b.2).1
        omega),
      base_le_greatestPrimeFactor_of_sifted hsmall b.2 hb1, ?_, ?_⟩
    · have hle := greatestPrimeFactor_le_div_cutoff b.2 hb1
      rw [← hcore] at hle
      exact hle.trans (le_max_right _ _)
    · intro hmem
      exact (mem_sifted.mp b.2).2.2 _ hmem
        (greatestPrimeFactor_dvd (by
          have := (mem_sifted.mp b.2).1
          omega))
  have hImage :
      primeBandMap hexpand (U / c) (greatestPrimeFactor a.1) =
        primeBandMap hexpand (U / c) (greatestPrimeFactor b.1) := by
    simpa only [expandedPrime, c, hcore] using hexpanded
  exact primeBandMap_injective_of_mem hexpand haOld hbOld hImage

/-- The second-copy map is injective.  The exceptional input `1` is sent
to a pure power of `p`; every other input is reconstructed from the core
and the two greatest prime factors, using injectivity of the prime-band
embedding on a fixed core. -/
lemma sieveLift_injective {T : Finset ℕ} {p U : ℕ}
    (hp : p.Prime) (hU : p ≤ U)
    (hsmall : ∀ r, r.Prime → r < p → r ∈ T)
    (hexpand : PrimeIntervalExpansion T p) :
    Function.Injective (sieveLift hsmall hexpand : ↥(sifted T U) → ℕ) := by
  intro a b hab
  by_cases ha1 : a.1 = 1
  · by_cases hb1 : b.1 = 1
    · exact Subtype.ext (ha1.trans hb1.symm)
    · have hpow : greatestPrimeFactor (sieveLift hsmall hexpand a) = p := by
        rw [sieveLift, dif_pos ha1]
        exact greatestPrimeFactor_prime_pow hp (by omega)
      have hliftb := greatestPrimeFactor_sieveLift_of_ne_one
        hsmall hexpand b hb1
      have hpExpanded : p = expandedPrime hsmall hexpand b hb1 := by
        calc
          p = greatestPrimeFactor (sieveLift hsmall hexpand a) := hpow.symm
          _ = greatestPrimeFactor (sieveLift hsmall hexpand b) :=
            congrArg greatestPrimeFactor hab
          _ = expandedPrime hsmall hexpand b hb1 := hliftb
      have hX : p ≤ U / (b.1 / greatestPrimeFactor b.1) :=
        (base_le_greatestPrimeFactor_of_sifted hsmall b.2 hb1).trans
          (greatestPrimeFactor_le_div_cutoff b.2 hb1)
      have hrLower := (expandedPrime_spec hsmall hexpand b hb1).2.1
      rw [← hpExpanded] at hrLower
      omega
  · by_cases hb1 : b.1 = 1
    · have hpow : greatestPrimeFactor (sieveLift hsmall hexpand b) = p := by
        rw [sieveLift, dif_pos hb1]
        exact greatestPrimeFactor_prime_pow hp (by omega)
      have hlifta := greatestPrimeFactor_sieveLift_of_ne_one
        hsmall hexpand a ha1
      have hpExpanded : expandedPrime hsmall hexpand a ha1 = p := by
        calc
          expandedPrime hsmall hexpand a ha1 =
              greatestPrimeFactor (sieveLift hsmall hexpand a) := hlifta.symm
          _ = greatestPrimeFactor (sieveLift hsmall hexpand b) :=
            congrArg greatestPrimeFactor hab
          _ = p := hpow
      have hX : p ≤ U / (a.1 / greatestPrimeFactor a.1) :=
        (base_le_greatestPrimeFactor_of_sifted hsmall a.2 ha1).trans
          (greatestPrimeFactor_le_div_cutoff a.2 ha1)
      have hrLower := (expandedPrime_spec hsmall hexpand a ha1).2.1
      rw [hpExpanded] at hrLower
      omega
    · have hga := greatestPrimeFactor_sieveLift_of_ne_one
        hsmall hexpand a ha1
      have hgb := greatestPrimeFactor_sieveLift_of_ne_one
        hsmall hexpand b hb1
      have hrEq : expandedPrime hsmall hexpand a ha1 =
          expandedPrime hsmall hexpand b hb1 := by
        rw [← hga, hab, hgb]
      have hmul :
          (a.1 / greatestPrimeFactor a.1) *
              expandedPrime hsmall hexpand a ha1 =
            (b.1 / greatestPrimeFactor b.1) *
              expandedPrime hsmall hexpand b hb1 := by
        simpa only [sieveLift, dif_neg ha1, dif_neg hb1] using hab
      have hcore : a.1 / greatestPrimeFactor a.1 =
          b.1 / greatestPrimeFactor b.1 := by
        rw [hrEq] at hmul
        exact Nat.eq_of_mul_eq_mul_right
          (expandedPrime_spec hsmall hexpand b hb1).1.pos hmul
      have hgreatest := greatestPrimeFactor_eq_of_core_eq_of_expandedPrime_eq
        hsmall hexpand a b ha1 hb1 hcore hrEq
      apply Subtype.ext
      calc
        a.1 = (a.1 / greatestPrimeFactor a.1) * greatestPrimeFactor a.1 :=
          (div_greatestPrimeFactor_mul (by
            have := (mem_sifted.mp a.2).1
            omega)).symm
        _ = (b.1 / greatestPrimeFactor b.1) * greatestPrimeFactor b.1 := by
          rw [hcore, hgreatest]
        _ = b.1 := div_greatestPrimeFactor_mul (by
          have := (mem_sifted.mp b.2).1
          omega)

/-- Conditional sieve doubling above the base prime.  The original sifted
interval is the first copy.  `sieveLift` injects a second copy into the
disjoint layer `(U,pU]`. -/
theorem card_sifted_doubling_of_primeIntervalExpansion_of_le
    {T : Finset ℕ} {p U : ℕ}
    (hp : p.Prime) (hpT : p ∉ T) (hT : ∀ r ∈ T, r.Prime)
    (hU : p ≤ U)
    (hsmall : ∀ r, r.Prime → r < p → r ∈ T)
    (hexpand : PrimeIntervalExpansion T p) :
    2 * (sifted T U).card ≤ (sifted T (p * U)).card := by
  classical
  let newLayer := (sifted T (p * U)).filter fun m ↦ U < m
  let f : ↥(sifted T U) → ↥newLayer := fun m ↦
    ⟨sieveLift hsmall hexpand m, by
      apply Finset.mem_filter.mpr
      exact sieveLift_mem_new_layer hp hpT hT hU hsmall hexpand m⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply sieveLift_injective hp hU hsmall hexpand
    exact congrArg Subtype.val hab
  have hnew : (sifted T U).card ≤ newLayer.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  have hscale : U ≤ p * U := Nat.le_mul_of_pos_left U hp.pos
  have hsplit : sifted T (p * U) = sifted T U ∪ newLayer := by
    apply Finset.ext
    intro m
    simp only [Finset.mem_union]
    constructor
    · intro hm
      by_cases hmU : m ≤ U
      · exact Or.inl (mem_sifted.mpr
          ⟨(mem_sifted.mp hm).1, hmU, (mem_sifted.mp hm).2.2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hm, by omega⟩)
    · rintro (hm | hm)
      · exact mem_sifted.mpr
          ⟨(mem_sifted.mp hm).1, (mem_sifted.mp hm).2.1.trans hscale,
            (mem_sifted.mp hm).2.2⟩
      · exact (Finset.mem_filter.mp hm).1
  have hdisjoint : Disjoint (sifted T U) newLayer := by
    rw [Finset.disjoint_left]
    intro m hmOld hmNew
    have hmU := (mem_sifted.mp hmOld).2.1
    have hmGt := (Finset.mem_filter.mp hmNew).2
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisjoint]
  omega

/-- Full conditional sieve doubling, including cutoffs below the base
prime.  In that small range the old sifted set is just `{1}`, while the
new interval contains both `1` and `p`. -/
theorem card_sifted_doubling_of_primeIntervalExpansion
    {T : Finset ℕ} {p U : ℕ}
    (hp : p.Prime) (hpT : p ∉ T) (hT : ∀ r ∈ T, r.Prime)
    (hsmall : ∀ r, r.Prime → r < p → r ∈ T)
    (hexpand : PrimeIntervalExpansion T p) :
    2 * (sifted T U).card ≤ (sifted T (p * U)).card := by
  classical
  by_cases hbase : p ≤ U
  · exact card_sifted_doubling_of_primeIntervalExpansion_of_le
      hp hpT hT hbase hsmall hexpand
  have hUp : U < p := by omega
  by_cases hU0 : U = 0
  · subst U
    simp [sifted]
  have hUpos : 1 ≤ U := Nat.one_le_iff_ne_zero.mpr hU0
  have hOld : sifted T U = {1} := by
    apply Finset.ext
    intro m
    constructor
    · intro hm
      have hmData := mem_sifted.mp hm
      have hm1 : m = 1 := by
        by_contra hm1
        have hmgt : 1 < m := by omega
        have hpG := base_le_greatestPrimeFactor_of_sifted hsmall hm hm1
        have hGm : greatestPrimeFactor m ≤ m :=
          Nat.le_of_dvd (by omega) (greatestPrimeFactor_dvd hmgt)
        omega
      simp [hm1]
    · intro hm
      have hm1 : m = 1 := by simpa using hm
      subst m
      exact mem_sifted.mpr ⟨le_rfl, hUpos, fun r hrT hrOne ↦
        (hT r hrT).ne_one (Nat.dvd_one.mp hrOne)⟩
  have hPair : ({1, p} : Finset ℕ) ⊆ sifted T (p * U) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · subst m
      exact mem_sifted.mpr ⟨le_rfl, by
          exact Nat.one_le_iff_ne_zero.mpr
            (mul_ne_zero hp.ne_zero hU0),
        fun r hrT hrOne ↦ (hT r hrT).ne_one (Nat.dvd_one.mp hrOne)⟩
    · subst m
      exact mem_sifted.mpr ⟨hp.one_lt.le,
        (by simpa using Nat.mul_le_mul_left p hUpos),
        fun r hrT hrp ↦ by
          have hr := hT r hrT
          rcases (Nat.dvd_prime hp).mp hrp with hr1 | hrEq
          · exact hr.ne_one hr1
          · exact hpT (hrEq ▸ hrT)⟩
  have hPairCard := Finset.card_le_card hPair
  rw [hOld]
  simpa [hp.ne_one.symm] using hPairCard

lemma sifted_mono_cutoff (T : Finset ℕ) {U V : ℕ} (hUV : U ≤ V) :
    sifted T U ⊆ sifted T V := by
  intro m hm
  exact mem_sifted.mpr
    ⟨(mem_sifted.mp hm).1, (mem_sifted.mp hm).2.1.trans hUV,
      (mem_sifted.mp hm).2.2⟩

/-- Multiplication by a new prime bijects sifted integers below `U / q`
with the `q`-divisible sifted integers below `U`. -/
lemma card_sifted_filter_dvd {T : Finset ℕ} {U q : ℕ}
    (hq : q.Prime) (hqT : q ∉ T) (hT : ∀ p ∈ T, p.Prime) :
    ((sifted T U).filter (q ∣ ·)).card = (sifted T (U / q)).card := by
  classical
  let f : ℕ → ℕ := fun m ↦ q * m
  have hEq : (sifted T (U / q)).image f = (sifted T U).filter (q ∣ ·) := by
    ext n
    constructor
    · intro hn
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
      have hm' := mem_sifted.mp hm
      rw [Finset.mem_filter]
      refine ⟨mem_sifted.mpr ⟨Nat.mul_pos hq.pos hm'.1,
        (by simpa [f, mul_comm] using
          (Nat.le_div_iff_mul_le hq.pos).mp hm'.2.1), ?_⟩, dvd_mul_right q m⟩
      intro r hrT hrdiv
      rcases (hT r hrT).dvd_mul.mp hrdiv with hrq | hrm
      · have hrqeq : r = q :=
          ((Nat.dvd_prime hq).mp hrq).resolve_left (hT r hrT).ne_one
        exact hqT (hrqeq ▸ hrT)
      · exact hm'.2.2 r hrT hrm
    · intro hn
      have hn' := Finset.mem_filter.mp hn
      obtain ⟨m, rfl⟩ := hn'.2
      have hqm := mem_sifted.mp hn'.1
      have hmpos : 1 ≤ m := by
        by_contra hm
        have : m = 0 := by omega
        subst m
        simp at hqm
      rw [Finset.mem_image]
      refine ⟨m, mem_sifted.mpr ⟨hmpos,
        (Nat.le_div_iff_mul_le hq.pos).mpr (by simpa [mul_comm] using hqm.2.1), ?_⟩, rfl⟩
      intro r hrT hrm
      exact hqm.2.2 r hrT (dvd_mul_of_dvd_right hrm q)
  rw [← hEq, Finset.card_image_of_injective]
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left hq.pos hab

/-- Exact one-prime deletion recurrence for finite sifted intervals. -/
lemma card_sifted_insert {T : Finset ℕ} {U q : ℕ}
    (hq : q.Prime) (hqT : q ∉ T) (hT : ∀ p ∈ T, p.Prime) :
    (sifted (insert q T) U).card =
      (sifted T U).card - (sifted T (U / q)).card := by
  have hset : sifted (insert q T) U =
      sifted T U \ (sifted T U).filter (q ∣ ·) := by
    ext m
    simp only [mem_sifted, Finset.mem_insert, Finset.mem_sdiff,
      Finset.mem_filter]
    aesop
  rw [hset, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    card_sifted_filter_dvd hq hqT hT]

/-- The Euler-product density associated with a finite set of forbidden
primes.  Rational numbers are used here so that the finite error estimates
below involve no analytic approximation. -/
def sieveDensity (T : Finset ℕ) : ℚ :=
  ∏ p ∈ T, ((p - 1 : ℕ) : ℚ) / p

@[simp] lemma sieveDensity_empty : sieveDensity ∅ = 1 := by
  simp [sieveDensity]

lemma sieveDensity_nonneg {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    0 ≤ sieveDensity T := by
  apply Finset.prod_nonneg
  intro p hp
  exact div_nonneg (by positivity) (by positivity)

lemma sieveDensity_le_one {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    sieveDensity T ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    exact div_nonneg (by positivity) (by positivity)
  · intro p hp
    have hp1 : 1 ≤ p := (hT p hp).one_lt.le
    exact (div_le_one (by positivity)).2 (by exact_mod_cast Nat.sub_le p 1)

lemma sieveDensity_insert {T : Finset ℕ} {q : ℕ} (hqT : q ∉ T) :
    sieveDensity (insert q T) = ((q - 1 : ℕ) : ℚ) / q * sieveDensity T := by
  rw [sieveDensity, sieveDensity, Finset.prod_insert hqT]

lemma cast_div_eq_add_mod_div (U q : ℕ) (hq : 0 < q) :
    (U : ℚ) / q = (U / q : ℕ) + (U % q : ℕ) / (q : ℚ) := by
  apply (div_eq_iff (by exact_mod_cast hq.ne')).2
  rw [add_mul, div_mul_cancel₀ _ (by exact_mod_cast hq.ne')]
  push_cast
  exact_mod_cast (by simpa [mul_comm] using (Nat.div_add_mod U q).symm)

@[simp] lemma card_sifted_empty (U : ℕ) : (sifted ∅ U).card = U := by
  simp [sifted]

/-- One-sided finite-sieve error bounds.  If `k = T.card`, the upper
rounding error is at most `2^(k-1)` and the lower rounding error is at most
`2^(k-1)-1`.  The deliberately harmless upper error `1` when `T` is empty
keeps the statement uniform; the induction treats the first prime
separately and obtains the sharp singleton bounds. -/
theorem sifted_density_bounds {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (U : ℕ) :
    ((sifted T U).card : ℚ) ≤
        U * sieveDensity T + (2 ^ (T.card - 1) : ℕ) ∧
      U * sieveDensity T ≤
        ((sifted T U).card : ℚ) + ((2 ^ (T.card - 1) : ℕ) - 1) := by
  classical
  induction T using Finset.induction_on generalizing U with
  | empty =>
      simp [sifted, sieveDensity]
  | @insert q T hqT ih =>
      have hq : q.Prime := hT q (Finset.mem_insert_self q T)
      have hTp : ∀ p ∈ T, p.Prime := fun p hp ↦ hT p (Finset.mem_insert_of_mem hp)
      by_cases hTempty : T = ∅
      · subst T
        have hqpos : 0 < (q : ℚ) := by exact_mod_cast hq.pos
        have hqcast : (((q - 1 : ℕ) : ℚ)) = q - 1 := by
          rw [Nat.cast_sub hq.one_lt.le]
          norm_num
        have hmod0 : (0 : ℚ) ≤ (U % q : ℕ) / q := by positivity
        have hmod1 : (U % q : ℕ) / (q : ℚ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast (Nat.mod_lt U hq.pos).le
        have herr : ((sifted ∅ U).card : ℚ) - (sifted ∅ (U / q)).card =
            (U : ℚ) * (((q - 1 : ℕ) : ℚ) / q) + (U % q : ℕ) / q := by
          rw [card_sifted_empty, card_sifted_empty]
          rw [hqcast]
          have hdecomp : (U : ℚ) = q * (U / q : ℕ) + (U % q : ℕ) := by
            exact_mod_cast (Nat.div_add_mod U q).symm
          field_simp
          nlinarith
        rw [card_sifted_insert hq (by simp) (by simp)]
        rw [sieveDensity_insert (T := ∅) (by simp), sieveDensity_empty]
        norm_num at ⊢
        simp only [card_sifted_empty] at herr
        rw [Nat.cast_sub (Nat.div_le_self U q)]
        push_cast
        norm_num at ⊢
        rw [herr]
        constructor <;> nlinarith
      · have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTempty
        have hkpos : 0 < T.card := Finset.card_pos.mpr hTne
        have hqpos : 0 < (q : ℚ) := by exact_mod_cast hq.pos
        have hdivleNat : U / q ≤ U := Nat.div_le_self U q
        have hcardle : (sifted T (U / q)).card ≤ (sifted T U).card :=
          Finset.card_le_card (sifted_mono_cutoff T hdivleNat)
        have ihU := ih hTp U
        have ihV := ih hTp (U / q)
        have hd0 := sieveDensity_nonneg hTp
        have hd1 := sieveDensity_le_one hTp
        have hqcast : (((q - 1 : ℕ) : ℚ)) = q - 1 := by
          rw [Nat.cast_sub hq.one_lt.le]
          norm_num
        have hfloor : (U : ℚ) / q - (U / q : ℕ) = (U % q : ℕ) / q := by
          rw [cast_div_eq_add_mod_div U q hq.pos]
          ring
        have hfloor0 : (0 : ℚ) ≤ (U : ℚ) / q - (U / q : ℕ) := by
          rw [hfloor]
          positivity
        have hfloor1 : (U : ℚ) / q - (U / q : ℕ) ≤ 1 := by
          rw [hfloor, div_le_one (by positivity)]
          exact_mod_cast (Nat.mod_lt U hq.pos).le
        rw [card_sifted_insert hq hqT hTp,
          sieveDensity_insert hqT, Nat.cast_sub hcardle]
        rw [Finset.card_insert_of_notMem hqT]
        have hpow : (2 : ℚ) ^ T.card =
            2 * (2 : ℚ) ^ (T.card - 1) := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T.card ≠ 0)
          rw [hk]
          simp [pow_succ, mul_comm]
        have herr :
            ((sifted T U).card : ℚ) - (sifted T (U / q)).card -
                (U : ℚ) * (((q - 1 : ℕ) : ℚ) / q * sieveDensity T) =
              (((sifted T U).card : ℚ) - U * sieveDensity T) -
                (((sifted T (U / q)).card : ℚ) -
                  (U / q : ℕ) * sieveDensity T) +
                ((U : ℚ) / q - (U / q : ℕ)) * sieveDensity T := by
          rw [hqcast]
          field_simp
          ring
        push_cast at ihU ihV ⊢
        constructor
        · have hrnd : ((U : ℚ) / q - (U / q : ℕ)) * sieveDensity T ≤ 1 := by
            nlinarith
          have hdelta :
              ((sifted T U).card : ℚ) - (sifted T (U / q)).card -
                  U * (((q - 1 : ℕ) : ℚ) / q * sieveDensity T) ≤
                2 ^ T.card := by
            rw [herr, hpow]
            nlinarith [ihU.1, ihV.2]
          linarith

        · have hrnd : 0 ≤ ((U : ℚ) / q - (U / q : ℕ)) * sieveDensity T :=
            mul_nonneg hfloor0 hd0
          have hdelta :
              -(2 ^ T.card - 1) ≤
                ((sifted T U).card : ℚ) - (sifted T (U / q)).card -
                  U * (((q - 1 : ℕ) : ℚ) / q * sieveDensity T) := by
            rw [herr, hpow]
            nlinarith [ihU.2, ihV.1]
          linarith

/-- The numerical consequence of the density bounds used in the large-error
branch of the Ahlswede--Khachatrian sieve.  It is stated for arbitrary
cutoffs `U ≤ V`; later `U = ⌊x/d⌋` and `V = ⌊px/d⌋`. -/
theorem card_sifted_doubling_of_density {T : Finset ℕ} {U V : ℕ}
    (hT : ∀ p ∈ T, p.Prime)
    (hmain : (3 * (2 ^ (T.card - 1) : ℕ) : ℚ) ≤
      ((V : ℚ) - 2 * U) * sieveDensity T) :
    2 * (sifted T U).card ≤ (sifted T V).card := by
  have hU := sifted_density_bounds hT U
  have hV := sifted_density_bounds hT V
  have hrat : (2 : ℚ) * (sifted T U).card ≤ (sifted T V).card := by
    push_cast at hU hV hmain ⊢
    nlinarith
  exact_mod_cast hrat

/-- Symmetric density bounds when the cutoff is presented as a rational
quotient.  The fractional part consumes the one-unit gap between the two
one-sided integer-cutoff errors in `sifted_density_bounds`. -/
theorem sifted_quotient_density_bounds {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime)
    (x d : ℕ) (hd : 0 < d) :
    ((sifted T (x / d)).card : ℚ) ≤
        (x : ℚ) / d * sieveDensity T + (2 ^ (T.card - 1) : ℕ) ∧
      (x : ℚ) / d * sieveDensity T ≤
        ((sifted T (x / d)).card : ℚ) + (2 ^ (T.card - 1) : ℕ) := by
  have h := sifted_density_bounds hT (x / d)
  have hdensity0 := sieveDensity_nonneg hT
  have hdensity1 := sieveDensity_le_one hT
  have hfloor := cast_div_eq_add_mod_div x d hd
  have hfrac0 : (0 : ℚ) ≤ (x % d : ℕ) / d := by positivity
  have hfrac1 : (x % d : ℕ) / (d : ℚ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast (Nat.mod_lt x hd).le
  have hpow : 1 ≤ 2 ^ (T.card - 1) := one_le_pow₀ (by norm_num)
  have hround0 : 0 ≤ ((((x % d : ℕ) : ℚ) / d) * sieveDensity T) :=
    mul_nonneg hfrac0 hdensity0
  have hround1 : ((((x % d : ℕ) : ℚ) / d) * sieveDensity T) ≤ 1 :=
    mul_le_one₀ hfrac1 hdensity0 hdensity1
  have hpowQ : (1 : ℚ) ≤ ((2 ^ (T.card - 1) : ℕ) : ℚ) := by
    exact_mod_cast hpow
  constructor
  · rw [hfloor]
    nlinarith
  · rw [hfloor]
    nlinarith

/-- Large-error branch in exactly the quotient form used by the source:
once the Euler-product main term gained by multiplication by `p` dominates
the three rounding errors, the sifted interval at scale `p*x/d` is at least
twice the one at scale `x/d`. -/
theorem card_sifted_quotient_doubling_of_density {T : Finset ℕ}
    {x d p : ℕ} (hT : ∀ q ∈ T, q.Prime) (hd : 0 < d) (hp : 2 ≤ p)
    (hmain : (3 * (2 ^ (T.card - 1) : ℕ) : ℚ) ≤
      (p - 2 : ℕ) * ((x : ℚ) / d) * sieveDensity T) :
    2 * (sifted T (x / d)).card ≤ (sifted T (p * x / d)).card := by
  have hlo := sifted_quotient_density_bounds hT x d hd
  have hhi := sifted_quotient_density_bounds hT (p * x) d hd
  have hpcast : (((p - 2 : ℕ) : ℚ)) = p - 2 := by
    rw [Nat.cast_sub hp]
    norm_num
  have hgain : (((p - 2 : ℕ) : ℚ)) * ((x : ℚ) / d) * sieveDensity T =
      (p : ℚ) * x / d * sieveDensity T -
        2 * ((x : ℚ) / d * sieveDensity T) := by
    rw [hpcast]
    push_cast
    ring
  have hrat : (2 : ℚ) * (sifted T (x / d)).card ≤
      (sifted T (p * x / d)).card := by
    push_cast at hlo hhi hmain ⊢
    rw [hgain] at hmain
    nlinarith
  exact_mod_cast hrat

lemma candidate_contains_N {N q : ℕ} (hq : q ∈ N.primeFactors) :
    N ∈ candidate N q := by
  rw [mem_candidate]
  have hN0 : N ≠ 0 := (Nat.mem_primeFactors.mp hq).2.2
  exact ⟨Nat.one_le_iff_ne_zero.mpr hN0, le_rfl, Or.inl (prefixProduct_dvd N q)⟩

/-- Every displayed family in the resolution is genuinely admissible. -/
theorem candidate_admissible {N q : ℕ} (hq : q ∈ N.primeFactors) :
    Admissible N (candidate N q) := by
  refine ⟨?_, candidate_contains_N hq, ?_⟩
  · intro m hm
    exact mem_interval.mpr ⟨(mem_candidate.mp hm).1, (mem_candidate.mp hm).2.1⟩
  · intro a ha b hb _hab
    have ha' := mem_candidate.mp ha
    have hb' := mem_candidate.mp hb
    rcases ha'.2.2 with haProd | ⟨pa, hpaPrefix, hpa⟩
    · rcases hb'.2.2 with hbProd | ⟨pb, hpbPrefix, hpb⟩
      · have hqPrefix := mem_primePrefix_self hq
        have hqProd : q ∣ prefixProduct N q := dvd_prefixProduct_of_mem hqPrefix
        exact one_lt_gcd_of_prime_dvd (Nat.prime_of_mem_primeFactors hq)
          (hqProd.trans haProd) (hqProd.trans hbProd) ha'.1
      · have hpbProd : pb ∣ prefixProduct N q := dvd_prefixProduct_of_mem hpbPrefix
        exact one_lt_gcd_of_prime_dvd (prime_of_mem_primePrefix hpbPrefix)
          (hpbProd.trans haProd) ((Nat.dvd_mul_left pb 2).trans hpb) ha'.1
    · rcases hb'.2.2 with hbProd | ⟨pb, hpbPrefix, hpb⟩
      · have hpaProd : pa ∣ prefixProduct N q := dvd_prefixProduct_of_mem hpaPrefix
        exact one_lt_gcd_of_prime_dvd (prime_of_mem_primePrefix hpaPrefix)
          ((Nat.dvd_mul_left pa 2).trans hpa) (hpaProd.trans hbProd) ha'.1
      · exact one_lt_gcd_of_prime_dvd Nat.prime_two
          ((Nat.dvd_mul_right 2 pa).trans hpa)
          ((Nat.dvd_mul_right 2 pb).trans hpb) ha'.1

/-- The filter definition of a candidate is exactly the bounded upset
generated by its displayed primitive numbers. -/
lemma candidate_eq_multiplesBelow (N q : ℕ) :
    candidate N q = multiplesBelow N (candidateGenerators N q) := by
  ext m
  rw [mem_candidate, mem_multiplesBelow]
  constructor
  · rintro ⟨hm1, hmN, hm | ⟨p, hp, hpm⟩⟩
    · exact ⟨hm1, hmN, prefixProduct N q,
        Finset.mem_insert_self _ _, hm⟩
    · exact ⟨hm1, hmN, 2 * p, Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩), hpm⟩
  · rintro ⟨hm1, hmN, g, hg, hgm⟩
    rcases mem_candidateGenerators.mp hg with rfl | ⟨p, hp, rfl⟩
    · exact ⟨hm1, hmN, Or.inl hgm⟩
    · exact ⟨hm1, hmN, Or.inr ⟨p, hp, hgm⟩⟩

/-- Once the replacement argument identifies the primitive family, the
optimal integer family itself is the corresponding displayed candidate. -/
lemma QOptimal.eq_candidate_of_primitive_eq {N q : ℕ} {A : Finset ℕ}
    (hA : QOptimal N A) (hprimitive : primitive A = candidateGenerators N q) :
    A = candidate N q := by
  rw [hA.eq_multiplesBelow_primitive, hprimitive, ← candidate_eq_multiplesBelow]

/-! ### The elementary last step of the primitive-family classification -/

/-- A prime divisor of a prefix product is one of the primes in the prefix. -/
lemma mem_primePrefix_of_prime_dvd_prefixProduct {N q p : ℕ} (hp : p.Prime)
    (hpdvd : p ∣ prefixProduct N q) :
    p ∈ primePrefix N q := by
  classical
  have aux : ∀ S : Finset ℕ, p ∣ ∏ r ∈ S, r → ∃ r ∈ S, p ∣ r := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro h
        have hp1 : p = 1 := by simpa using h
        exact (hp.ne_one hp1).elim
    | @insert r S hrS ih =>
        rw [Finset.prod_insert hrS]
        intro h
        rcases hp.dvd_mul.mp h with hpr | hpS
        · exact ⟨r, Finset.mem_insert_self r S, hpr⟩
        · obtain ⟨t, ht, hpt⟩ := ih hpS
          exact ⟨t, Finset.mem_insert_of_mem ht, hpt⟩
  obtain ⟨r, hr, hpr⟩ := aux (primePrefix N q) (by
    simpa [prefixProduct] using hpdvd)
  rcases (Nat.dvd_prime (prime_of_mem_primePrefix hr)).mp hpr with h | h
  · exact (hp.ne_one h).elim
  · simpa [h] using hr

/-- If an odd number has a nontrivial gcd with `2*p`, where `p` is prime,
then it is divisible by `p`. -/
lemma prime_dvd_of_not_two_dvd_of_one_lt_gcd_two_mul {a p : ℕ}
    (hp : p.Prime) (ha2 : ¬2 ∣ a) (hgcd : 1 < Nat.gcd a (2 * p)) :
    p ∣ a := by
  obtain ⟨r, hr, hra, hr2p⟩ := exists_prime_dvd_both_of_one_lt_gcd hgcd
  rcases hr.dvd_mul.mp hr2p with hr2 | hrp
  · rcases (Nat.dvd_prime Nat.prime_two).mp hr2 with h | h
    · exact (hr.ne_one h).elim
    · exact (ha2 (h ▸ hra)).elim
  · rcases (Nat.dvd_prime hp).mp hrp with h | h
    · exact (hr.ne_one h).elim
    · simpa [h] using hra

/-- A squarefree integer supported on `2` and a prime prefix divides the
product of precisely those available primes. -/
lemma squarefree_dvd_two_mul_prefixProduct {N q g : ℕ}
    (hNodd : ¬2 ∣ N) (hsq : Squarefree g)
    (hsupport : ∀ p ∈ g.primeFactors, p = 2 ∨ p ∈ primePrefix N q) :
    g ∣ 2 * prefixProduct N q := by
  have hTwoNot : 2 ∉ primePrefix N q := by
    intro hTwo
    exact hNodd (Nat.dvd_of_mem_primeFactors (primePrefix_subset N q hTwo))
  have hsub : g.primeFactors ⊆ insert 2 (primePrefix N q) := by
    intro p hp
    rcases hsupport p hp with rfl | hp
    · exact Finset.mem_insert_self 2 _
    · exact Finset.mem_insert_of_mem hp
  calc
    g = ∏ p ∈ g.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
    _ ∣ ∏ p ∈ insert 2 (primePrefix N q), p :=
      Finset.prod_dvd_prod_of_subset _ _ id hsub
    _ = 2 * prefixProduct N q := by
      rw [Finset.prod_insert hTwoNot]
      rfl

/-- Under the structural conclusions supplied by the two replacement
arguments, every primitive generator is one of the displayed generators.
This is the arithmetic core of the last paragraph of the
Ahlswede--Khachatrian proof. -/
lemma QOptimal.mem_candidateGenerators_of_primitive_structure
    {N q : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hNodd : ¬2 ∣ N)
    (hsupport : ∀ g ∈ primitive A, g ∣ 2 * prefixProduct N q)
    (htwo : ∀ p ∈ primePrefix N q, 2 * p ∈ A)
    {g : ℕ} (hg : g ∈ primitive A) :
    g ∈ candidateGenerators N q := by
  have hgA : g ∈ A := (mem_primitive.mp hg).1
  have hgpos : 0 < g := by
    have := (mem_interval.mp (hA.1.1 hgA)).1
    omega
  obtain ⟨p, hp, hpg, hpN⟩ :=
    exists_prime_dvd_both_of_one_lt_gcd (hA.primitive_meets_N hg)
  have hpPrefix : p ∈ primePrefix N q := by
    have hp2prod : p ∣ 2 * prefixProduct N q := hpg.trans (hsupport g hg)
    rcases hp.dvd_mul.mp hp2prod with hp2 | hpProd
    · rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
      · exact (hp.ne_one h).elim
      · exact (hNodd (h ▸ hpN)).elim
    · exact mem_primePrefix_of_prime_dvd_prefixProduct hp hpProd
  by_cases hg2 : 2 ∣ g
  · have h2pCoprime : Nat.Coprime 2 p :=
      Nat.prime_two.coprime_iff_not_dvd.mpr fun h2p ↦ hNodd (h2p.trans hpN)
    have h2pg : 2 * p ∣ g :=
      h2pCoprime.mul_dvd_of_dvd_of_dvd hg2 hpg
    have hg2p : g ∣ 2 * p :=
      (mem_primitive.mp hg).2 (2 * p) (htwo p hpPrefix) h2pg
    have hgeq : g = 2 * p := Nat.dvd_antisymm hg2p h2pg
    exact mem_candidateGenerators.mpr (Or.inr ⟨p, hpPrefix, hgeq.symm⟩)
  · have hodd : Odd g := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using hg2)
    have hgCoprime : Nat.Coprime g 2 := Nat.coprime_two_right.mpr hodd
    have hgProd : g ∣ prefixProduct N q :=
      hgCoprime.dvd_of_dvd_mul_left (hsupport g hg)
    have hProdg : prefixProduct N q ∣ g := by
      rw [prefixProduct]
      refine (Finset.prod_dvd_prod_of_subset (primePrefix N q) g.primeFactors id ?_).trans
        (Nat.prod_primeFactors_dvd g)
      intro r hr
      have hrdiv : r ∣ g :=
        prime_dvd_of_not_two_dvd_of_one_lt_gcd_two_mul
          (prime_of_mem_primePrefix hr) hg2
          (hA.1.2.2 hgA (htwo r hr) (by
            intro hgr
            subst g
            exact hg2 (dvd_mul_right 2 r)))
      exact Nat.mem_primeFactors.mpr
        ⟨prime_of_mem_primePrefix hr, hrdiv, ne_of_gt hgpos⟩
    exact mem_candidateGenerators.mpr
      (Or.inl (Nat.dvd_antisymm hgProd hProdg))

/-- The full odd prefix product cannot be absent from an optimum once every
primitive generator is supported on that prefix together with `2`: it has
a prefix prime in common with every old member, so adjoining it would
otherwise enlarge the family. -/
lemma QOptimal.prefixProduct_mem_of_primitive_structure
    {N q : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hq : q ∈ N.primeFactors) (hNodd : ¬2 ∣ N)
    (hsupport : ∀ g ∈ primitive A, g ∣ 2 * prefixProduct N q) :
    prefixProduct N q ∈ A := by
  by_contra hnot
  have hNpos : 0 < N := (Nat.mem_primeFactors.mp hq).2.2.bot_lt
  have hprodPos : 0 < prefixProduct N q := by
    rw [prefixProduct]
    exact Finset.prod_pos fun p hp ↦ (prime_of_mem_primePrefix hp).pos
  have hprodI : prefixProduct N q ∈ interval N :=
    mem_interval.mpr
      ⟨hprodPos, Nat.le_of_dvd hNpos (prefixProduct_dvd N q)⟩
  have hqPrefix := mem_primePrefix_self hq
  have hqProd := dvd_prefixProduct_of_mem hqPrefix
  have hIns : QAdmissible N (insert (prefixProduct N q) A) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hprodI
      · exact hA.1.1 hx
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact one_lt_gcd_of_prime_dvd (Nat.prime_of_mem_primeFactors hq)
          hqProd (hqProd.trans (prefixProduct_dvd N q)) hprodPos
      · exact hA.1.2.1 x hx
    · rw [Finset.coe_insert]
      intro x hx y hy hxy
      rcases hx with hxProd | hxA
      · subst x
        rcases hy with hyProd | hyA
        · exact (hxy hyProd.symm).elim
        · obtain ⟨g, hg, hgy⟩ := exists_primitive_dvd hA.1.1 hyA
          obtain ⟨p, hp, hpg, hpN⟩ :=
            exists_prime_dvd_both_of_one_lt_gcd (hA.primitive_meets_N hg)
          have hpPrefix : p ∈ primePrefix N q := by
            have hp2prod : p ∣ 2 * prefixProduct N q :=
              hpg.trans (hsupport g hg)
            rcases hp.dvd_mul.mp hp2prod with hp2 | hpProd
            · rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
              · exact (hp.ne_one h).elim
              · exact (hNodd (h ▸ hpN)).elim
            · exact mem_primePrefix_of_prime_dvd_prefixProduct hp hpProd
          exact one_lt_gcd_of_prime_dvd hp
            (dvd_prefixProduct_of_mem hpPrefix) (hpg.trans hgy) hprodPos
      · rcases hy with hyProd | hyA
        · subst y
          rw [Nat.gcd_comm]
          obtain ⟨g, hg, hgx⟩ := exists_primitive_dvd hA.1.1 hxA
          obtain ⟨p, hp, hpg, hpN⟩ :=
            exists_prime_dvd_both_of_one_lt_gcd (hA.primitive_meets_N hg)
          have hpPrefix : p ∈ primePrefix N q := by
            have hp2prod : p ∣ 2 * prefixProduct N q :=
              hpg.trans (hsupport g hg)
            rcases hp.dvd_mul.mp hp2prod with hp2 | hpProd
            · rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with h | h
              · exact (hp.ne_one h).elim
              · exact (hNodd (h ▸ hpN)).elim
            · exact mem_primePrefix_of_prime_dvd_prefixProduct hp hpProd
          exact one_lt_gcd_of_prime_dvd hp
            (dvd_prefixProduct_of_mem hpPrefix) (hpg.trans hgx) hprodPos
        · exact hA.1.2.2 hxA hyA hxy
  have hle := hA.2 (insert (prefixProduct N q) A) hIns
  rw [Finset.card_insert_of_notMem hnot] at hle
  omega

/-- If the prefix has at least two primes, the structural conclusions of
the replacement proof determine the primitive family exactly. -/
theorem QOptimal.primitive_eq_candidateGenerators_of_structure
    {N q : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hq : q ∈ N.primeFactors) (hNodd : ¬2 ∣ N)
    (hprefix : 2 ≤ (primePrefix N q).card)
    (hsupport : ∀ g ∈ primitive A, g ∣ 2 * prefixProduct N q)
    (htwo : ∀ p ∈ primePrefix N q, 2 * p ∈ A) :
    primitive A = candidateGenerators N q := by
  have hprod := hA.prefixProduct_mem_of_primitive_structure hq hNodd hsupport
  apply Finset.Subset.antisymm
  · intro g hg
    exact hA.mem_candidateGenerators_of_primitive_structure hNodd hsupport htwo hg
  · intro g hg
    rcases mem_candidateGenerators.mp hg with rfl | ⟨p, hpPrefix, rfl⟩
    · obtain ⟨d, hd, hdProd⟩ := exists_primitive_dvd hA.1.1 hprod
      have hdGen := hA.mem_candidateGenerators_of_primitive_structure
        hNodd hsupport htwo hd
      rcases mem_candidateGenerators.mp hdGen with hdEq | ⟨p, hp, hpEq⟩
      · simpa [hdEq] using hd
      · exfalso
        have htwoProd : 2 ∣ prefixProduct N q :=
          (dvd_mul_right 2 p).trans (hpEq ▸ hdProd)
        exact hNodd (htwoProd.trans (prefixProduct_dvd N q))
    · obtain ⟨d, hd, hd2p⟩ := exists_primitive_dvd hA.1.1 (htwo p hpPrefix)
      have hdGen := hA.mem_candidateGenerators_of_primitive_structure
        hNodd hsupport htwo hd
      rcases mem_candidateGenerators.mp hdGen with hdEq | ⟨r, hrPrefix, hrEq⟩
      · exfalso
        have hProd2p : prefixProduct N q ∣ 2 * p := hdEq ▸ hd2p
        have hr : ∃ r ∈ primePrefix N q, r ≠ p := by
          by_contra h
          push_neg at h
          have hsub : primePrefix N q ⊆ {p} := by
            intro r hr
            simpa [h r hr]
          have hcard := Finset.card_le_card hsub
          simp at hcard
          omega
        obtain ⟨r, hrPrefix, hrp⟩ := hr
        have hr2p : r ∣ 2 * p :=
          (dvd_prefixProduct_of_mem hrPrefix).trans hProd2p
        rcases (prime_of_mem_primePrefix hrPrefix).dvd_mul.mp hr2p with hr2 | hrpdiv
        · rcases (Nat.dvd_prime Nat.prime_two).mp hr2 with h | h
          · exact ((prime_of_mem_primePrefix hrPrefix).ne_one h).elim
          · have h2N : 2 ∣ N := h ▸ Nat.dvd_of_mem_primeFactors
                (primePrefix_subset N q hrPrefix)
            exact hNodd h2N
        · rcases (Nat.dvd_prime (prime_of_mem_primePrefix hpPrefix)).mp hrpdiv with h | h
          · exact ((prime_of_mem_primePrefix hrPrefix).ne_one h).elim
          · exact hrp h
      · have hrp : r = p := by
          have hrdiv : r ∣ p := by
            have : 2 * r ∣ 2 * p := hrEq ▸ hd2p
            exact Nat.dvd_of_mul_dvd_mul_left (by omega) this
          rcases (Nat.dvd_prime (prime_of_mem_primePrefix hpPrefix)).mp hrdiv with h | h
          · exact ((prime_of_mem_primePrefix hrPrefix).ne_one h).elim
          · exact h
        have hdeq : d = 2 * p := by simpa [hrp] using hrEq.symm
        simpa [hdeq] using hd

/-- Packaged form of the final classification: it is enough that primitive
prime supports lie in `{2} ∪ primePrefix N q` and that compression supplies
the doubled prefix primes. -/
theorem QOptimal.eq_candidate_of_support
    {N q : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hq : q ∈ N.primeFactors) (hNodd : ¬2 ∣ N)
    (hprefix : 2 ≤ (primePrefix N q).card)
    (hsupport : ∀ g ∈ primitive A, ∀ p ∈ g.primeFactors,
      p = 2 ∨ p ∈ primePrefix N q)
    (htwo : ∀ p ∈ primePrefix N q, 2 * p ∈ A) :
    A = candidate N q := by
  apply hA.eq_candidate_of_primitive_eq
  apply hA.primitive_eq_candidateGenerators_of_structure hq hNodd hprefix
  · intro g hg
    exact squarefree_dvd_two_mul_prefixProduct hNodd
      (hA.squarefree_of_mem_primitive hg) (hsupport g hg)
  · exact htwo

/-- A cardinality-maximizing displayed candidate exists for every endpoint
greater than one. -/
lemma exists_candidate_maximizer {N : ℕ} (hN : 2 ≤ N) :
    ∃ q ∈ N.primeFactors,
      ∀ p ∈ N.primeFactors, (candidate N p).card ≤ (candidate N q).card := by
  classical
  have hQ : N.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  let cards := N.primeFactors.image fun q ↦ (candidate N q).card
  have hcards : cards.Nonempty := hQ.image _
  let M := cards.max' hcards
  have hMmem : M ∈ cards := cards.max'_mem hcards
  obtain ⟨q, hq, hqM⟩ := Finset.mem_image.mp hMmem
  refine ⟨q, hq, ?_⟩
  intro p hp
  have hpmem : (candidate N p).card ∈ cards :=
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hpM := Finset.le_max' cards (candidate N p).card hpmem
  simpa [M, hqM] using hpM

/-- The auxiliary Ahlswede--Khachatrian theorem immediately implies the
literal Erdős problem, because every literal family is auxiliary and every
displayed candidate contains `N`. -/
lemma erdos_534_of_qOptimal_candidate {N q : ℕ} (hN : 2 ≤ N)
    (hq : q ∈ N.primeFactors) (hopt : QOptimal N (candidate N q)) :
    Admissible N (candidate N q) ∧
      ∀ A, Admissible N A → A.card ≤ (candidate N q).card := by
  refine ⟨candidate_admissible hq, ?_⟩
  intro A hA
  exact hopt.2 A (QAdmissible.of_admissible (by omega) hA)

/-! ### Endpoints with a single distinct prime factor -/

/-- If `d ∣ N`, the positive multiples of `d` up to `N` are parametrized
exactly by `Fin (N / d)`. -/
lemma card_interval_filter_dvd {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) :
    ((interval N).filter (d ∣ ·)).card = N / d := by
  let f : Fin (N / d) → ℕ := fun k ↦ d * (k.1 + 1)
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.val_injective
    dsimp only [f] at hab
    nlinarith
  have hrange : (interval N).filter (d ∣ ·) = Finset.univ.image f := by
    apply Finset.ext
    intro m
    simp only [Finset.mem_filter, mem_interval, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨hm1, hmN⟩, ⟨k, rfl⟩⟩
      have hk : k ≤ N / d := (Nat.le_div_iff_mul_le hd).2 (by
        simpa [Nat.mul_comm] using hmN)
      have hk0 : 0 < k := by
        by_contra hk0
        simp only [not_lt, nonpos_iff_eq_zero] at hk0
        subst k
        simp at hm1
      refine ⟨⟨k - 1, by omega⟩, ?_⟩
      dsimp only [f]
      congr 1
      omega
    · rintro ⟨k, rfl⟩
      have hk := k.2
      dsimp only [f]
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega)), ?_⟩,
        dvd_mul_right d (k.1 + 1)⟩
      calc
        d * (k.1 + 1) ≤ d * (N / d) := Nat.mul_le_mul_left d (by omega)
        _ = N := Nat.mul_div_cancel' hdN
  rw [hrange, Finset.card_image_of_injective _ hf, Finset.card_univ,
    Fintype.card_fin]

lemma candidate_eq_filter_dvd_of_primeFactors_eq_single {N q : ℕ}
    (hQ : N.primeFactors = {q}) :
    candidate N q = (interval N).filter (q ∣ ·) := by
  have hprefix : primePrefix N q = {q} := by
    ext p
    simp only [primePrefix, hQ, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, _⟩
      rfl
    · rintro rfl
      exact ⟨rfl, le_rfl⟩
  have hprod : prefixProduct N q = q := by simp [prefixProduct, hprefix]
  ext m
  rw [mem_candidate]
  simp only [Finset.mem_filter, mem_interval, hprod, hprefix, Finset.mem_singleton,
    exists_eq_left]
  constructor
  · rintro ⟨hm1, hmN, hqm | h2qm⟩
    · exact ⟨⟨hm1, hmN⟩, hqm⟩
    · exact ⟨⟨hm1, hmN⟩, (dvd_mul_left q 2).trans h2qm⟩
  · rintro ⟨⟨hm1, hmN⟩, hqm⟩
    exact ⟨hm1, hmN, Or.inl hqm⟩

/-- Complete resolution when `N` has exactly one distinct prime factor. -/
theorem erdos_534_single_primeFactor {N q : ℕ} (hN : 2 ≤ N)
    (hQ : N.primeFactors = {q}) :
    Admissible N (candidate N q) ∧
      ∀ A, Admissible N A → A.card ≤ (candidate N q).card := by
  have hqmem : q ∈ N.primeFactors := by simp [hQ]
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqN : q ∣ N := Nat.dvd_of_mem_primeFactors hqmem
  have hcandCard : (candidate N q).card = N / q := by
    rw [candidate_eq_filter_dvd_of_primeFactors_eq_single hQ,
      card_interval_filter_dvd hq.pos hqN]
  refine ⟨candidate_admissible hqmem, ?_⟩
  intro A hA
  have hsub : A ⊆ (interval N).filter (q ∣ ·) := by
    intro a ha
    refine Finset.mem_filter.mpr ⟨hA.1 ha, ?_⟩
    by_cases haN : a = N
    · simpa [haN] using hqN
    · obtain ⟨p, hp, hpa, hpN⟩ :=
        exists_prime_dvd_both_of_one_lt_gcd (hA.2.2 ha hA.2.1 haN)
      have hpMem : p ∈ N.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hpN, by omega⟩
      have hpq : p = q := by simpa [hQ] using hpMem
      simpa [hpq] using hpa
  calc
    A.card ≤ ((interval N).filter (q ∣ ·)).card := Finset.card_le_card hsub
    _ = N / q := card_interval_filter_dvd hq.pos hqN
    _ = (candidate N q).card := hcandCard.symm

/-! ### The elementary even endpoint case -/

/-- Distinct positive integers with the same quotient on division by two
are consecutive, hence cannot have a nontrivial gcd. -/
lemma eq_of_div_two_eq_of_one_lt_gcd {a b : ℕ}
    (hcode : a / 2 = b / 2) (hgcd : 1 < Nat.gcd a b) :
    a = b := by
  by_contra hab
  have haMod : a % 2 < 2 := Nat.mod_lt _ (by omega)
  have hbMod : b % 2 < 2 := Nat.mod_lt _ (by omega)
  have haDiv := (Nat.mod_add_div a 2).symm
  have hbDiv := (Nat.mod_add_div b 2).symm
  have hsucc : a + 1 = b ∨ b + 1 = a := by omega
  rcases hsucc with hsucc | hsucc
  · subst b
    simpa using hgcd
  · subst a
    rw [Nat.gcd_comm] at hgcd
    simpa using hgcd

/-- Every literal admissible family has the universal half-interval bound.
Pair `{2k,2k+1}` and note separately that `1` cannot occur because the
family contains `N > 1`. -/
lemma admissible_card_le_half {N : ℕ} {A : Finset ℕ}
    (hN : 2 ≤ N) (hA : Admissible N A) :
    A.card ≤ N / 2 := by
  let pairCode : ℕ → ℕ := fun a ↦ a / 2
  have htwo : ∀ a ∈ A, 2 ≤ a := by
    intro a ha
    have ha1 := (mem_interval.mp (hA.1 ha)).1
    by_contra ha2
    have haeq : a = 1 := by omega
    subst a
    have hne : 1 ≠ N := by omega
    have := hA.2.2 ha hA.2.1 hne
    simp at this
  have hinj : Set.InjOn pairCode (A : Set ℕ) := by
    intro a ha b hb hcode
    by_contra hab
    exact hab (eq_of_div_two_eq_of_one_lt_gcd hcode (hA.2.2 ha hb hab))
  have hcodes : A.image pairCode ⊆ Finset.Icc 1 (N / 2) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le (by omega)).2 (by
        simpa using htwo a ha),
      Nat.div_le_div_right (mem_interval.mp (hA.1 ha)).2⟩
  calc
    A.card = (A.image pairCode).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (N / 2)).card := Finset.card_le_card hcodes
    _ = N / 2 := by simp

/-- Any displayed candidate which reaches the universal half-interval bound
is automatically a solution of the extremal problem. -/
lemma erdos_534_of_candidate_card_eq_half {N q : ℕ} (hN : 2 ≤ N)
    (hq : q ∈ N.primeFactors) (hcard : (candidate N q).card = N / 2) :
    Admissible N (candidate N q) ∧
      ∀ A, Admissible N A → A.card ≤ (candidate N q).card := by
  refine ⟨candidate_admissible hq, ?_⟩
  intro A hA
  rw [hcard]
  exact admissible_card_le_half hN hA

/-- Two positive integers which lie in the same adjacent pair
`{2k+1, 2k+2}` cannot both belong to a pairwise noncoprime family. -/
lemma eq_of_pairCode_eq_of_one_lt_gcd {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcode : (a - 1) / 2 = (b - 1) / 2)
    (hgcd : 1 < Nat.gcd a b) :
    a = b := by
  by_contra hab
  have haMod : (a - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hbMod : (b - 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  have haDiv := (Nat.mod_add_div (a - 1) 2).symm
  have hbDiv := (Nat.mod_add_div (b - 1) 2).symm
  have hsucc : a + 1 = b ∨ b + 1 = a := by omega
  rcases hsucc with hsucc | hsucc
  · subst b
    simpa using hgcd
  · subst a
    rw [Nat.gcd_comm] at hgcd
    simpa using hgcd

/-- If `N` is even, every admissible family has at most `N / 2` members:
map a member to the index of its adjacent pair. -/
lemma admissible_card_le_half_of_even {N : ℕ} {A : Finset ℕ}
    (hN : 2 ≤ N) (hEven : 2 ∣ N) (hA : Admissible N A) :
    A.card ≤ N / 2 := by
  let pairCode : ℕ → ℕ := fun a ↦ (a - 1) / 2
  have hinj : Set.InjOn pairCode (A : Set ℕ) := by
    intro a ha b hb hcode
    by_contra hab
    exact hab (eq_of_pairCode_eq_of_one_lt_gcd
      (mem_interval.mp (hA.1 ha)).1 (mem_interval.mp (hA.1 hb)).1 hcode
      (hA.2.2 ha hb hab))
  have hcodes : A.image pairCode ⊆ Finset.range (N / 2) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range]
    obtain ⟨M, rfl⟩ := hEven
    have haN := (mem_interval.mp (hA.1 ha)).2
    have hM : 1 ≤ M := by omega
    dsimp only [pairCode]
    omega
  calc
    A.card = (A.image pairCode).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (N / 2)).card := Finset.card_le_card hcodes
    _ = N / 2 := Finset.card_range _

/-- When `2 ∣ N`, the first displayed Ahlswede--Khachatrian candidate is
exactly the even part of `[1,N]`. -/
lemma candidate_two_eq_even {N : ℕ} (hTwo : 2 ∈ N.primeFactors) :
    candidate N 2 = (interval N).filter (2 ∣ ·) := by
  apply Finset.ext
  intro m
  rw [mem_candidate]
  simp only [Finset.mem_filter, mem_interval]
  have hprefix : primePrefix N 2 = {2} := by
    apply Finset.ext
    intro p
    simp only [mem_primePrefix, Finset.mem_singleton]
    constructor
    · rintro ⟨hpN, hp2⟩
      have hp := Nat.prime_of_mem_primeFactors hpN
      exact Nat.le_antisymm hp2 hp.two_le
    · rintro rfl
      exact ⟨hTwo, le_rfl⟩
  have hprod : prefixProduct N 2 = 2 := by simp [prefixProduct, hprefix]
  rw [hprod, hprefix]
  simp only [Finset.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨hm1, hmN, hm | hm⟩
    · exact ⟨⟨hm1, hmN⟩, hm⟩
    · exact ⟨⟨hm1, hmN⟩, (by norm_num : 2 ∣ 2 * 2).trans hm⟩
  · rintro ⟨⟨hm1, hmN⟩, hm⟩
    exact ⟨hm1, hmN, Or.inl hm⟩

/-- The first candidate has the expected exact size at an even endpoint. -/
lemma candidate_two_card {N : ℕ} (hN : 2 ≤ N) (hTwo : 2 ∈ N.primeFactors) :
    (candidate N 2).card = N / 2 := by
  rw [candidate_two_eq_even hTwo]
  let f : Fin (N / 2) → ℕ := fun k ↦ 2 * (k.1 + 1)
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.val_injective
    dsimp only [f] at hab
    omega
  have hrange : (interval N).filter (2 ∣ ·) = Finset.univ.image f := by
    apply Finset.ext
    intro m
    simp only [Finset.mem_filter, mem_interval, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨hm1, hmN⟩, ⟨k, rfl⟩⟩
      have hk : k ≤ N / 2 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      have hk0 : 0 < k := by omega
      refine ⟨⟨k - 1, ?_⟩, ?_⟩
      · omega
      · dsimp only [f]
        omega
    · rintro ⟨k, rfl⟩
      have hk := k.2
      dsimp only [f]
      refine ⟨⟨by omega, ?_⟩, dvd_mul_right 2 (k.1 + 1)⟩
      have hEven : 2 ∣ N := Nat.dvd_of_mem_primeFactors hTwo
      calc
        2 * (k.1 + 1) ≤ 2 * (N / 2) := Nat.mul_le_mul_left 2 (by omega)
        _ = N := Nat.mul_div_cancel' hEven
  rw [hrange, Finset.card_image_of_injective _ hf, Finset.card_univ,
    Fintype.card_fin]

/-- Complete resolution of Problem 534 when the endpoint is even. -/
theorem erdos_534_even {N : ℕ} (hN : 2 ≤ N) (hEven : 2 ∣ N) :
    Admissible N (candidate N 2) ∧
      ∀ A, Admissible N A → A.card ≤ (candidate N 2).card := by
  have hTwo : 2 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hEven, by omega⟩
  refine ⟨candidate_admissible hTwo, ?_⟩
  intro A hA
  rw [candidate_two_card hN hTwo]
  exact admissible_card_le_half_of_even hN hEven hA

end Erdos534

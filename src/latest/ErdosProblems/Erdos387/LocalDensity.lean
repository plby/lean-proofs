/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CoverAlgebra
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local sieve density for binomial coefficients

For a prime `p > k`, the denominator `k!` is invertible modulo `p`.
Consequently `p ∣ n.choose k` exactly when `n` lies in one of the `k`
classes `0, ..., k - 1` modulo `p`.  This is the exact local-density input in
BNPZ Proposition 6.1.
-/

namespace Erdos387

open scoped BigOperators

/-- A prime divides a finite product exactly when it divides one factor. -/
theorem prime_dvd_finset_prod_iff {p : ℕ} (hp : p.Prime)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    p ∣ ∏ i ∈ s, f i ↔ ∃ i ∈ s, p ∣ f i := by
  induction s using Finset.induction_on with
  | empty => simp [hp.not_dvd_one]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, hp.dvd_mul, ih]
      simp

/-- Exact forbidden-residue criterion for one prime greater than `k`. -/
theorem prime_dvd_choose_iff_exists_mod_eq
    {n k p : ℕ} (hp : p.Prime) (hkp : k < p) (hkn : k ≤ n) :
    p ∣ n.choose k ↔ ∃ i < k, n % p = i := by
  have hchooseDesc : p ∣ n.choose k ↔ p ∣ n.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    constructor
    · exact fun h => dvd_mul_of_dvd_right h k.factorial
    · intro h
      rcases hp.dvd_mul.mp h with hfac | hchoose
      · exact False.elim (Nat.not_le_of_lt hkp (hp.dvd_factorial.mp hfac))
      · exact hchoose
  rw [hchooseDesc, Nat.descFactorial_eq_prod_range,
    prime_dvd_finset_prod_iff hp (Finset.range k) (fun i => n - i)]
  constructor
  · rintro ⟨i, hi, hdiv⟩
    have hik : i < k := Finset.mem_range.mp hi
    have hin : i ≤ n := (Nat.le_of_lt hik).trans hkn
    have hmodEq : i ≡ n [MOD p] := (Nat.modEq_iff_dvd' hin).mpr hdiv
    exact ⟨i, hik, Nat.mod_eq_of_modEq hmodEq.symm (hik.trans hkp)⟩
  · rintro ⟨i, hik, hmod⟩
    refine ⟨i, Finset.mem_range.mpr hik, ?_⟩
    have hin : i ≤ n := (Nat.le_of_lt hik).trans hkn
    have hmodEq : i ≡ n [MOD p] := by
      simpa [hmod] using Nat.mod_modEq n p
    exact (Nat.modEq_iff_dvd' hin).mp hmodEq

/-- The finite set of forbidden residue representatives modulo `p`. -/
def localBadResidues (p k : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun a => a < k

theorem localBadResidues_eq_range {p k : ℕ} (hkp : k ≤ p) :
    localBadResidues p k = Finset.range k := by
  ext a
  simp [localBadResidues]
  omega

/-- There are exactly `k` forbidden residue classes. -/
theorem card_localBadResidues {p k : ℕ} (hkp : k ≤ p) :
    (localBadResidues p k).card = k := by
  rw [localBadResidues_eq_range hkp, Finset.card_range]

/-- Membership in the explicit local bad set is equivalent to prime
divisibility of the binomial coefficient. -/
theorem prime_dvd_choose_iff_mod_mem_localBadResidues
    {n k p : ℕ} (hp : p.Prime) (hkp : k < p) (hkn : k ≤ n) :
    p ∣ n.choose k ↔ n % p ∈ localBadResidues p k := by
  rw [prime_dvd_choose_iff_exists_mod_eq hp hkp hkn,
    localBadResidues_eq_range hkp.le]
  simp only [Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hmod⟩
    simpa [hmod] using hi
  · intro hmod
    exact ⟨n % p, hmod, rfl⟩

/-- Distinct members of `g.primeFactors` are coprime. -/
theorem primeFactors_pairwise_coprime (g : ℕ) :
    Set.Pairwise (↑g.primeFactors : Set ℕ) Nat.Coprime := by
  intro p hp q hq hpq
  have pp := (Nat.mem_primeFactors.mp hp).1
  have pq := (Nat.mem_primeFactors.mp hq).1
  rw [pp.coprime_iff_not_dvd]
  intro hpd
  exact hpq ((pq.dvd_iff_eq pp.ne_one).mp hpd).symm

/-- CRT residue attached to a choice of one shift in `Fin k` for every prime
factor of `g`. -/
noncomputable def localAssignmentResidue (g k : ℕ)
    (A : (p : ↑g.primeFactors) → Fin k) : ℕ :=
  Nat.chineseRemainderOfFinset
    (fun p : ↑g.primeFactors => (A p : ℕ))
    (fun p : ↑g.primeFactors => (p : ℕ)) Finset.univ
    (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
    (by
      intro p _ q _ hpq
      exact primeFactors_pairwise_coprime g p.property q.property
        (fun h => hpq (Subtype.ext h)))

theorem localAssignmentResidue_mod (g k : ℕ)
    (A : (p : ↑g.primeFactors) → Fin k) (p : ↑g.primeFactors) :
    localAssignmentResidue g k A ≡ (A p : ℕ) [MOD (p : ℕ)] := by
  exact (Nat.chineseRemainderOfFinset
    (fun p : ↑g.primeFactors => (A p : ℕ))
    (fun p : ↑g.primeFactors => (p : ℕ)) Finset.univ
    (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
    (by
      intro p _ q _ hpq
      exact primeFactors_pairwise_coprime g p.property q.property
        (fun h => hpq (Subtype.ext h)))).prop p (Finset.mem_univ p)

/-- When all prime factors of `g` exceed `k`, distinct local assignments
yield distinct CRT residues. -/
theorem localAssignmentResidue_injective {g k : ℕ}
    (hlarge : ∀ p ∈ g.primeFactors, k < p) :
    Function.Injective (localAssignmentResidue g k) := by
  intro A A' hres
  funext p
  apply Fin.ext
  have hA := localAssignmentResidue_mod g k A p
  have hA' := localAssignmentResidue_mod g k A' p
  have hAp : (A p : ℕ) < (p : ℕ) := (A p).isLt.trans (hlarge p p.property)
  have hA'p : (A' p : ℕ) < (p : ℕ) := (A' p).isLt.trans (hlarge p p.property)
  have hmA := Nat.mod_eq_of_modEq hA hAp
  have hmA' := Nat.mod_eq_of_modEq hA' hA'p
  rw [hres] at hmA
  omega

/-- The finite set of CRT residues arising from all local assignments. -/
noncomputable def localAssignmentResidues (g k : ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.image (localAssignmentResidue g k)

/-- Its cardinality is the exact sieve multiplicity `k ^ ω(g)`. -/
theorem card_localAssignmentResidues {g k : ℕ}
    (hlarge : ∀ p ∈ g.primeFactors, k < p) :
    (localAssignmentResidues g k).card = k ^ g.primeFactors.card := by
  classical
  rw [localAssignmentResidues, Finset.card_image_of_injective _
    (localAssignmentResidue_injective hlarge), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

/-- For squarefree `g`, each assignment residue is the canonical
representative below `g`. -/
theorem localAssignmentResidue_lt {g k : ℕ} (hg : Squarefree g)
    (A : (p : ↑g.primeFactors) → Fin k) :
    localAssignmentResidue g k A < g := by
  have hlt :=
    Nat.chineseRemainderOfFinset_lt_prod
      (fun p : ↑g.primeFactors => (A p : ℕ))
      (fun p : ↑g.primeFactors => (p : ℕ)) (t := Finset.univ)
      (by intro p _; exact (Nat.mem_primeFactors.mp p.property).1.ne_zero)
      (by
        intro p _ q _ hpq
        exact primeFactors_pairwise_coprime g p.property q.property
          (fun h => hpq (Subtype.ext h)))
  have hlt' : localAssignmentResidue g k A <
      ∏ p : ↑g.primeFactors, (p : ℕ) := by
    simpa [localAssignmentResidue] using hlt
  calc
    localAssignmentResidue g k A < ∏ p : ↑g.primeFactors, (p : ℕ) := hlt'
    _ = ∏ p ∈ g.primeFactors, p := by
      simpa using Finset.prod_attach g.primeFactors (fun p : ℕ => p)
    _ = g := Nat.prod_primeFactors_of_squarefree hg

/-- Congruence modulo the radical of `g` is equivalent to congruence modulo
every prime factor of `g`.  This is the finite CRT uniqueness statement used
to identify the residue classes counted by the sieve. -/
theorem modEq_prod_primeFactors_iff (g a b : ℕ) :
    a ≡ b [MOD ∏ p ∈ g.primeFactors, p] ↔
      ∀ p ∈ g.primeFactors, a ≡ b [MOD p] := by
  let l := g.primeFactors.toList
  have hl : l.Pairwise Nat.Coprime := by
    have hlnodup : l.Nodup := Finset.nodup_toList g.primeFactors
    apply hlnodup.pairwise_of_forall_ne
    intro p hp q hq hpq
    apply primeFactors_pairwise_coprime g
    · simpa [l] using hp
    · simpa [l] using hq
    · exact hpq
  simpa [l] using (Nat.modEq_list_map_prod_iff
    (s := fun p : ℕ => p) (l := l) hl)

/-- A squarefree natural divides `m` exactly when each of its prime factors
does. -/
theorem squarefree_dvd_iff_primeFactors_dvd {g m : ℕ} (hg : Squarefree g) :
    g ∣ m ↔ ∀ p ∈ g.primeFactors, p ∣ m := by
  constructor
  · intro h p hp
    exact (Nat.dvd_of_mem_primeFactors hp).trans h
  · intro h
    rw [← Nat.prod_primeFactors_of_squarefree hg]
    by_cases hm : m = 0
    · simp [hm]
    rw [Nat.prod_primeFactors_dvd_iff hm]
    intro p hp
    exact Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1, h p hp, hm⟩

/-- Exact simultaneous local-density statement.  For a squarefree modulus
whose prime factors all exceed `k`, divisibility by that modulus is equivalent
to membership in one of the CRT classes indexed by a choice in `Fin k` at
each prime. -/
theorem squarefree_dvd_choose_iff_exists_localAssignment
    {g n k : ℕ} (hg : Squarefree g)
    (hlarge : ∀ p ∈ g.primeFactors, k < p) (hkn : k ≤ n) :
    g ∣ n.choose k ↔
      ∃ A : (p : ↑g.primeFactors) → Fin k,
        n % g = localAssignmentResidue g k A := by
  classical
  constructor
  · intro hdiv
    have hloc : ∀ p : ↑g.primeFactors,
        ∃ i < k, n % (p : ℕ) = i := by
      intro p
      apply (prime_dvd_choose_iff_exists_mod_eq
        (Nat.mem_primeFactors.mp p.property).1
        (hlarge p p.property) hkn).mp
      exact (Nat.dvd_of_mem_primeFactors p.property).trans hdiv
    let A : (p : ↑g.primeFactors) → Fin k := fun p =>
      ⟨(hloc p).choose, (hloc p).choose_spec.1⟩
    refine ⟨A, Nat.mod_eq_of_modEq ?_ (localAssignmentResidue_lt hg A)⟩
    have hm : n ≡ localAssignmentResidue g k A
        [MOD ∏ p ∈ g.primeFactors, p] := by
      apply (modEq_prod_primeFactors_iff g n
        (localAssignmentResidue g k A)).mpr
      intro p hp
      let p' : ↑g.primeFactors := ⟨p, hp⟩
      have hnp : n ≡ (A p' : ℕ) [MOD p] := by
        change n % p = (A p' : ℕ) % p
        rw [Nat.mod_eq_of_lt ((A p').isLt.trans (hlarge p hp))]
        exact (hloc p').choose_spec.2
      exact hnp.trans (localAssignmentResidue_mod g k A p').symm
    simpa only [Nat.prod_primeFactors_of_squarefree hg] using hm
  · rintro ⟨A, hmod⟩
    apply (squarefree_dvd_iff_primeFactors_dvd hg).mpr
    intro p hp
    apply (prime_dvd_choose_iff_exists_mod_eq
      (Nat.mem_primeFactors.mp hp).1 (hlarge p hp) hkn).mpr
    let p' : ↑g.primeFactors := ⟨p, hp⟩
    refine ⟨A p', (A p').isLt, ?_⟩
    have hng : n ≡ localAssignmentResidue g k A [MOD g] := by
      change n % g = localAssignmentResidue g k A % g
      rw [Nat.mod_eq_of_lt (localAssignmentResidue_lt hg A)]
      exact hmod
    have hnp := hng.of_dvd (Nat.dvd_of_mem_primeFactors hp)
    have hlocal := localAssignmentResidue_mod g k A p'
    exact Nat.mod_eq_of_modEq (hnp.trans hlocal)
      ((A p').isLt.trans (hlarge p hp))

/-- The integers below `X` whose residues modulo `g` lie in `A`. -/
def modularPreimage (X g : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.range X).filter fun n => n % g ∈ A

/-- Exact count of a union of distinct residue classes in an initial
interval.  The second term is the incomplete final block, so this also gives
an error at most `A.card` without any analytic input. -/
theorem card_modularPreimage {X g : ℕ} (hg : 0 < g) (A : Finset ℕ)
    (hA : ∀ a ∈ A, a < g) :
    (modularPreimage X g A).card =
      A.card * (X / g) + (A.filter fun a => a < X % g).card := by
  classical
  unfold modularPreimage
  rw [← Finset.sum_card_fiberwise_eq_card_filter
    (Finset.range X) A (fun n => n % g)]
  calc
    ∑ a ∈ A, ((Finset.range X).filter fun n => n % g = a).card =
        ∑ a ∈ A, X.count (fun n => n ≡ a [MOD g]) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Nat.count_eq_card_filter_range]
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
      intro _
      simp [Nat.ModEq, Nat.mod_eq_of_lt (hA a ha)]
    _ = ∑ a ∈ A, (X / g + if a < X % g then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Nat.count_modEq_card X hg a, Nat.mod_eq_of_lt (hA a ha)]
    _ = A.card * (X / g) + (A.filter fun a => a < X % g).card := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact Finset.sum_const_nat (fun _ _ => rfl)
      · rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The count in an initial interval differs from its density main term by
at most the number of selected residue classes. -/
theorem abs_card_modularPreimage_sub_density {X g : ℕ} (hg : 0 < g)
    (A : Finset ℕ) (hA : ∀ a ∈ A, a < g) :
    |((modularPreimage X g A).card : ℝ) -
        (A.card : ℝ) * (X : ℝ) / g| ≤ A.card := by
  let r := (A.filter fun a => a < X % g).card
  have hrle : r ≤ A.card := Finset.card_filter_le _ _
  have hslt : X % g < g := Nat.mod_lt X hg
  have hgReal : (0 : ℝ) < g := by exact_mod_cast hg
  have hsNonneg : (0 : ℝ) ≤ (X % g : ℕ) := by positivity
  have hfracNonneg :
      (0 : ℝ) ≤ (A.card : ℝ) * (X % g : ℕ) / g := by positivity
  have hfracLe :
      (A.card : ℝ) * (X % g : ℕ) / g ≤ A.card := by
    have hsle : ((X % g : ℕ) : ℝ) / g ≤ 1 :=
      (div_le_one hgReal).mpr (by exact_mod_cast hslt.le)
    calc
      (A.card : ℝ) * (X % g : ℕ) / g =
          (A.card : ℝ) * (((X % g : ℕ) : ℝ) / g) := by ring
      _ ≤ (A.card : ℝ) * 1 := by gcongr
      _ = A.card := by ring
  have hxNat : g * (X / g) + X % g = X := by
    simpa [add_comm, mul_comm] using Nat.mod_add_div X g
  have hxReal : (X : ℝ) =
      (g : ℝ) * (X / g : ℕ) + (X % g : ℕ) := by
    exact_mod_cast hxNat.symm
  have hrewrite :
      ((modularPreimage X g A).card : ℝ) -
          (A.card : ℝ) * (X : ℝ) / g =
        (r : ℝ) - (A.card : ℝ) * (X % g : ℕ) / g := by
    rw [card_modularPreimage hg A hA]
    push_cast
    rw [hxReal]
    field_simp
    ring
  have hrleReal : (r : ℝ) ≤ A.card := by
    exact_mod_cast hrle
  have hrNonneg : (0 : ℝ) ≤ r := by positivity
  rw [hrewrite, abs_le]
  constructor <;> linarith

/-- The integers in `(L,U]` whose residues modulo `g` lie in `A`. -/
def modularPreimageIoc (L U g : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter fun n => n % g ∈ A

/-- An interval residue preimage is the difference of two initial residue
preimages. -/
theorem modularPreimageIoc_eq_sdiff {L U g : ℕ} (hLU : L ≤ U)
    (A : Finset ℕ) :
    modularPreimageIoc L U g A =
      modularPreimage (U + 1) g A \ modularPreimage (L + 1) g A := by
  classical
  ext n
  simp only [modularPreimageIoc, modularPreimage, Finset.mem_filter,
    Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_range]
  constructor
  · rintro ⟨⟨hLn, hnU⟩, hnA⟩
    exact ⟨⟨by omega, hnA⟩, fun hnLower => by omega⟩
  · rintro ⟨⟨hnU, hnA⟩, hnLower⟩
    refine ⟨⟨?_, by omega⟩, hnA⟩
    by_contra hLn
    apply hnLower
    exact ⟨by omega, hnA⟩

/-- The smaller initial residue preimage is contained in the larger one. -/
theorem modularPreimage_mono {X Y g : ℕ} (hXY : X ≤ Y)
    (A : Finset ℕ) :
    modularPreimage X g A ⊆ modularPreimage Y g A := by
  intro n hn
  simp only [modularPreimage, Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1.trans_le hXY, hn.2⟩

/-- Exact cardinal decomposition for an interval residue preimage. -/
theorem card_modularPreimageIoc_add_card {L U g : ℕ} (hLU : L ≤ U)
    (A : Finset ℕ) :
    (modularPreimageIoc L U g A).card +
        (modularPreimage (L + 1) g A).card =
      (modularPreimage (U + 1) g A).card := by
  rw [modularPreimageIoc_eq_sdiff hLU]
  exact Finset.card_sdiff_add_card_eq_card
    (modularPreimage_mono (Nat.add_le_add_right hLU 1) A)

/-- Uniform discrepancy estimate for a union of residue classes in an
arbitrary half-open interval.  Each endpoint contributes at most one copy of
the number of selected classes. -/
theorem abs_card_modularPreimageIoc_sub_density {L U g : ℕ}
    (hLU : L ≤ U) (hg : 0 < g) (A : Finset ℕ)
    (hA : ∀ a ∈ A, a < g) :
    |((modularPreimageIoc L U g A).card : ℝ) -
        (A.card : ℝ) * ((U - L : ℕ) : ℝ) / g| ≤ 2 * A.card := by
  have hU := abs_card_modularPreimage_sub_density
    (X := U + 1) hg A hA
  have hL := abs_card_modularPreimage_sub_density
    (X := L + 1) hg A hA
  have hcardNat := card_modularPreimageIoc_add_card (g := g) hLU A
  have hcardReal :
      ((modularPreimageIoc L U g A).card : ℝ) =
        ((modularPreimage (U + 1) g A).card : ℝ) -
          ((modularPreimage (L + 1) g A).card : ℝ) := by
    have hcardCast :
        ((modularPreimageIoc L U g A).card : ℝ) +
            ((modularPreimage (L + 1) g A).card : ℝ) =
          ((modularPreimage (U + 1) g A).card : ℝ) := by
      exact_mod_cast hcardNat
    linarith
  have hrewrite :
      ((modularPreimageIoc L U g A).card : ℝ) -
          (A.card : ℝ) * ((U - L : ℕ) : ℝ) / g =
        (((modularPreimage (U + 1) g A).card : ℝ) -
            (A.card : ℝ) * (U + 1 : ℕ) / g) -
          (((modularPreimage (L + 1) g A).card : ℝ) -
            (A.card : ℝ) * (L + 1 : ℕ) / g) := by
    rw [hcardReal, Nat.cast_sub hLU]
    push_cast
    ring
  rw [hrewrite]
  calc
    |_ - _| ≤
        |((modularPreimage (U + 1) g A).card : ℝ) -
          (A.card : ℝ) * (U + 1 : ℕ) / g| +
        |((modularPreimage (L + 1) g A).card : ℝ) -
          (A.card : ℝ) * (L + 1 : ℕ) / g| := abs_sub _ _
    _ ≤ A.card + A.card := add_le_add hU hL
    _ = 2 * A.card := by ring

/-- Membership formulation of the simultaneous local-density theorem. -/
theorem squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
    {g n k : ℕ} (hg : Squarefree g)
    (hlarge : ∀ p ∈ g.primeFactors, k < p) (hkn : k ≤ n) :
    g ∣ n.choose k ↔ n % g ∈ localAssignmentResidues g k := by
  rw [squarefree_dvd_choose_iff_exists_localAssignment hg hlarge hkn]
  simp only [localAssignmentResidues, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A, hA.symm⟩
  · rintro ⟨A, hA⟩
    exact ⟨A, hA.symm⟩

/-- Exact number of the forbidden simultaneous CRT classes below a
squarefree modulus. -/
theorem card_localAssignment_modularPreimage {X g k : ℕ}
    (hg : Squarefree g) (hlarge : ∀ p ∈ g.primeFactors, k < p) :
    (modularPreimage X g (localAssignmentResidues g k)).card =
      k ^ g.primeFactors.card * (X / g) +
        ((localAssignmentResidues g k).filter fun a => a < X % g).card := by
  rw [card_modularPreimage (Nat.pos_of_ne_zero hg.ne_zero)
    (localAssignmentResidues g k)
    (fun a ha => by
      rw [localAssignmentResidues, Finset.mem_image] at ha
      obtain ⟨A, _, rfl⟩ := ha
      exact localAssignmentResidue_lt hg A),
    card_localAssignmentResidues hlarge]

end Erdos387

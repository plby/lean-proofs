/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.External.Erdos380.AntiSieve
import ErdosProblems.Erdos387.CongruenceCounting
import ErdosProblems.Erdos980.External.Erdos387.FiniteBetaSieveBridge
import ErdosProblems.Erdos980.External.Erdos387.GeneralBetaMainTerm
import ErdosProblems.Erdos980.External.Erdos822.MertensUpper
import ErdosProblems.Erdos980.External.Erdos822.SieveErrorAverage
import ErdosProblems.Erdos980.External.Erdos822.SlowCutoffLog
import ErdosProblems.Erdos851.ConcreteBetaCardinality
import ErdosProblems.Erdos851.EndpointBridge
import ErdosProblems.Erdos851.SieveSpecialization
import ErdosProblems.Erdos980.ElliottTail.CumulativeMediumApplication
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# A quadratic medium-range sieve for Erdős problem 980

For a prime `p`, the assertion that several odd primes `q` are quadratic
residues modulo `p` becomes, after fixing `p % 4`, a restriction to one half
of the nonzero residue classes modulo each `q`.  This file feeds those exact
restrictions into the tensor larger sieve proved in `Erdos380.AntiSieve`.

The resulting bound is entirely finite and unconditional.  It is the raw
quadratic sieve estimate used in the medium range: if `m` auxiliary odd
primes are available and every product of two `k`-element subfamilies is at
most the interval length `N`, then the number of simultaneous quadratic
patterns in an interval of length `N` is at most

`2 * N / (((m - k) / (2 * k)) ^ k)`.
-/

namespace Erdos980.ElliottTail

open scoped BigOperators
open Finset
open Filter

/-! ## The two halves of an odd prime field -/

/-- Nonzero quadratic residues modulo a prime. -/
noncomputable def nonzeroQuadraticResidues (q : ℕ) [Fact q.Prime] :
    Finset (ZMod q) :=
  Finset.univ.filter fun a ↦ IsSquare a ∧ a ≠ 0

/-- Quadratic nonresidues modulo a prime. -/
noncomputable def quadraticNonresidues (q : ℕ) [Fact q.Prime] :
    Finset (ZMod q) :=
  Finset.univ.filter fun a ↦ ¬ IsSquare a

private lemma quadraticChar_eq_indicator (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) (a : ZMod q) :
    quadraticChar (ZMod q) a =
      if a ∈ nonzeroQuadraticResidues q then 1
      else if a ∈ quadraticNonresidues q then -1 else 0 := by
  by_cases ha0 : a = 0
  · subst a
    simp [nonzeroQuadraticResidues, quadraticNonresidues]
  · have hchar := quadraticChar_dichotomy ha0
    rcases hchar with hchar | hchar
    · have hsquare : IsSquare a :=
        (quadraticChar_one_iff_isSquare ha0).mp hchar
      simp [nonzeroQuadraticResidues, quadraticNonresidues, ha0, hsquare, hchar]
    · have hnsquare : ¬ IsSquare a :=
        quadraticChar_neg_one_iff_not_isSquare.mp hchar
      simp [nonzeroQuadraticResidues, quadraticNonresidues, ha0, hnsquare, hchar]

private lemma card_nonzeroQuadraticResidues_add_card_quadraticNonresidues
    (q : ℕ) [Fact q.Prime] :
    (nonzeroQuadraticResidues q).card + (quadraticNonresidues q).card = q - 1 := by
  classical
  have hdisj : Disjoint (nonzeroQuadraticResidues q) (quadraticNonresidues q) := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2.1
  have hunion : nonzeroQuadraticResidues q ∪ quadraticNonresidues q =
      (Finset.univ : Finset (ZMod q)).erase 0 := by
    ext a
    by_cases ha0 : a = 0
    · subst a
      simp [nonzeroQuadraticResidues, quadraticNonresidues]
    · by_cases hs : IsSquare a <;>
        simp [nonzeroQuadraticResidues, quadraticNonresidues, ha0, hs]
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  simp [(Fact.out : q.Prime).ne_zero]

private lemma card_nonzeroQuadraticResidues_eq_card_quadraticNonresidues
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    (nonzeroQuadraticResidues q).card = (quadraticNonresidues q).card := by
  classical
  have hsum := quadraticChar_sum_zero
    ((ZMod.ringChar_zmod_n q).substr hq2 : ringChar (ZMod q) ≠ 2)
  have hrewrite :
      (∑ a : ZMod q, quadraticChar (ZMod q) a) =
        ((nonzeroQuadraticResidues q).card : ℤ) -
          ((quadraticNonresidues q).card : ℤ) := by
    calc
      (∑ a : ZMod q, quadraticChar (ZMod q) a) =
          ∑ a : ZMod q,
            ((if a ∈ nonzeroQuadraticResidues q then 1 else 0) +
              (if a ∈ quadraticNonresidues q then -1 else 0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [quadraticChar_eq_indicator q hq2]
        have hdisj : ¬ (a ∈ nonzeroQuadraticResidues q ∧
            a ∈ quadraticNonresidues q) := by
          rintro ⟨ha, hb⟩
          exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2.1
        by_cases ha : a ∈ nonzeroQuadraticResidues q <;>
          by_cases hb : a ∈ quadraticNonresidues q <;> simp_all
      _ = ((nonzeroQuadraticResidues q).card : ℤ) -
          ((quadraticNonresidues q).card : ℤ) := by
        rw [Finset.sum_add_distrib]
        have hpos :
            (∑ a : ZMod q,
              (if a ∈ nonzeroQuadraticResidues q then 1 else 0 : ℤ)) =
                ((nonzeroQuadraticResidues q).card : ℤ) := by simp
        have hneg :
            (∑ a : ZMod q,
              (if a ∈ quadraticNonresidues q then -1 else 0 : ℤ)) =
                -((quadraticNonresidues q).card : ℤ) := by simp
        rw [hpos, hneg]
        ring
  rw [hrewrite] at hsum
  omega

theorem card_nonzeroQuadraticResidues (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    (nonzeroQuadraticResidues q).card = (q - 1) / 2 := by
  have heq := card_nonzeroQuadraticResidues_eq_card_quadraticNonresidues q hq2
  have hsum := card_nonzeroQuadraticResidues_add_card_quadraticNonresidues q
  omega

theorem card_quadraticNonresidues (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    (quadraticNonresidues q).card = (q - 1) / 2 := by
  rw [← card_nonzeroQuadraticResidues_eq_card_quadraticNonresidues q hq2,
    card_nonzeroQuadraticResidues q hq2]

/-- The classes forbidden by the request that the quadratic character have
the prescribed sign.  `wantSquare = true` means that nonzero squares survive;
`false` means that nonsquares survive. -/
noncomputable def quadraticVanishing (q : ℕ) [Fact q.Prime]
    (wantSquare : Bool) : Finset (ZMod q) :=
  if wantSquare then Finset.univ \ nonzeroQuadraticResidues q
  else Finset.univ \ quadraticNonresidues q

theorem card_quadraticVanishing (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) (wantSquare : Bool) :
    (quadraticVanishing q wantSquare).card = q - (q - 1) / 2 := by
  classical
  cases wantSquare <;>
    simp [quadraticVanishing, Finset.card_sdiff_of_subset,
      card_nonzeroQuadraticResidues q hq2,
      card_quadraticNonresidues q hq2]

theorem quadraticVanishing_nonempty (q : ℕ) [Fact q.Prime]
    (wantSquare : Bool) : (quadraticVanishing q wantSquare).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  cases wantSquare <;>
    simp [quadraticVanishing, nonzeroQuadraticResidues, quadraticNonresidues]

theorem card_quadraticVanishing_lt (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) (wantSquare : Bool) :
    (quadraticVanishing q wantSquare).card < q := by
  rw [card_quadraticVanishing q hq2 wantSquare]
  have hq : 3 ≤ q := by
    have := (Fact.out : q.Prime).two_le
    omega
  omega

theorem half_le_quadraticVanishing_fraction (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) (wantSquare : Bool) :
    (1 / 2 : ℝ) ≤
      ((quadraticVanishing q wantSquare).card : ℝ) / q := by
  rw [card_quadraticVanishing q hq2 wantSquare]
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast (Fact.out : q.Prime).pos
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hqpos]
  norm_num only [one_mul]
  have hn : q ≤ 2 * (q - (q - 1) / 2) := by omega
  simpa [mul_comm] using (show (q : ℝ) ≤ 2 * (q - (q - 1) / 2 : ℕ) by
    exact_mod_cast hn)

/-! ## Quadratic reciprocity puts prime patterns in the sieve -/

/-- The required sign modulo an auxiliary prime after the candidate primes
have been split according to their residue class modulo four. -/
def reciprocityWantsSquare (candidateOneModFour : Bool) (q : ℕ) : Bool :=
  if candidateOneModFour then true else decide (q % 4 = 1)

theorem square_mod_prime_avoids_quadraticVanishing
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (candidateOneModFour : Bool)
    (hpClass : if candidateOneModFour then p % 4 = 1 else p % 4 = 3)
    (hsquare : IsSquare (q : ZMod p)) :
    (p : ZMod q) ∉
      quadraticVanishing q (reciprocityWantsSquare candidateOneModFour q) := by
  classical
  have hpnonzero : (p : ZMod q) ≠ 0 := by
    exact ZMod.prime_ne_zero q p hpq.symm
  cases candidateOneModFour with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hpClass
      have hqOdd : q % 2 = 1 :=
        (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : q.Prime)).mpr hq2
      rcases Nat.odd_mod_four_iff.mp hqOdd with hq1 | hq3
      · have hsquare' : IsSquare (p : ZMod q) :=
          (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
            (p := q) (q := p) hq1 hp2).mpr hsquare
        simp [quadraticVanishing, reciprocityWantsSquare, hq1,
          nonzeroQuadraticResidues, hpnonzero, hsquare']
      · have hnsquare' : ¬ IsSquare (p : ZMod q) :=
          (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three
            (p := p) (q := q) hpClass hq3 hpq).mp hsquare
        simp [quadraticVanishing, reciprocityWantsSquare, hq3,
          quadraticNonresidues, hnsquare']
  | true =>
      simp only [if_true] at hpClass
      have hsquare' : IsSquare (p : ZMod q) :=
        (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
          (p := p) (q := q) hpClass hq2).mp hsquare
      simp [quadraticVanishing, reciprocityWantsSquare,
        nonzeroQuadraticResidues, hpnonzero, hsquare']

/-- Candidate primes in an interval for which all members of `Q` are
quadratic residues.  Splitting by `candidateOneModFour` makes the residue
restrictions modulo each auxiliary prime independent of the candidate `p`. -/
noncomputable def quadraticResiduePrimePattern
    (Q : Finset ℕ) (candidateOneModFour : Bool) (m0 N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc m0 (m0 + N)).filter fun p ↦
    p.Prime ∧
      (if candidateOneModFour then p % 4 = 1 else p % 4 = 3) ∧
      ∀ q ∈ Q, q < p ∧ IsSquare (q : ZMod p)

theorem quadraticResiduePrimePattern_subset_survivors
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hodd : ∀ q ∈ Q, q ≠ 2)
    (candidateOneModFour : Bool) (m0 N : ℕ) :
    letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
    letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
    quadraticResiduePrimePattern Q candidateOneModFour m0 N ⊆
      Erdos380.residueClassSurvivors
        (modulus := fun q : Q ↦ q.1)
        (fun q ↦ quadraticVanishing q.1
          (reciprocityWantsSquare candidateOneModFour q.1)) m0 N := by
  classical
  letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
  letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
  intro p hp
  rw [quadraticResiduePrimePattern] at hp
  obtain ⟨hpInterval, hpPrime, hpClass, hpResidues⟩ := Finset.mem_filter.mp hp
  rw [Erdos380.residueClassSurvivors, Finset.mem_filter]
  refine ⟨hpInterval, fun q ↦ ?_⟩
  obtain ⟨hqp, hsq⟩ := hpResidues q.1 q.2
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hp2 : p ≠ 2 := by
    intro hpEq
    subst p
    cases candidateOneModFour <;> simp at hpClass
  exact square_mod_prime_avoids_quadraticVanishing p q.1 hp2
    (hodd q.1 q.2) (Nat.ne_of_gt hqp) candidateOneModFour hpClass hsq

/-! ## The finite tensor-sieve specialization -/

/-- An explicit unconditional tensor larger-sieve bound for any prescribed
quadratic sign at each odd prime in `Q`.  The discarded set `L` consists of
`k` coordinates; since every remaining removal fraction is at least `1/2`,
the denominator is bounded below by `((Q.card-k)/(2*k))^k`.

The structural `k`-subset/product hypotheses are precisely the finite
square-root cutoff required by the large sieve, rather than an analytic
estimate hidden behind a predicate. -/
theorem quadraticPatternSurvivors_card_le
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hodd : ∀ q ∈ Q, q ≠ 2)
    (wantSquare : Q → Bool)
    (k m0 N : ℕ) (hk : 0 < k)
    (hsubsets : Nonempty (Erdos380.fixedCardSubsets Q k))
    (hproduct : ∀ T U : Erdos380.fixedCardSubsets Q k,
      (∏ q ∈ T.1, q.1) * (∏ q ∈ U.1, q.1) ≤ N)
    (L : Finset Q) (hLcard : L.card = k)
    (htrimNonempty : ((Finset.univ : Finset Q) \ L).Nonempty) :
    letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
    letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
    (∀ i ∈ (Finset.univ : Finset Q) \ L,
      ∀ l ∈ L,
        ((quadraticVanishing i.1 (wantSquare i)).card : ℝ) / i.1 ≤
          ((quadraticVanishing l.1 (wantSquare l)).card : ℝ) / l.1) →
      ((Erdos380.residueClassSurvivors
        (modulus := fun q : Q ↦ q.1)
        (fun q ↦ quadraticVanishing q.1 (wantSquare q)) m0 N).card : ℝ) ≤
        ((N : ℝ) + N) /
          ((((Q.card - k : ℕ) : ℝ) / (2 * k)) ^ k) := by
  classical
  letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
  letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
  intro hlargest
  let removed : Q → ℝ := fun q ↦
    Erdos380.residueRemovedFraction (fun q : Q ↦ q.1)
      (fun q ↦ quadraticVanishing q.1 (wantSquare q)) q
  have hcoprime : Pairwise (fun q r : Q ↦ Nat.Coprime q.1 r.1) := by
    intro q r hqr
    exact (Nat.coprime_primes (hprime q.1 q.2) (hprime r.1 r.2)).mpr
      (Subtype.coe_ne_coe.mpr hqr)
  have hhalf (q : Q) : (1 / 2 : ℝ) ≤ removed q := by
    simpa [removed, Erdos380.residueRemovedFraction] using
      half_le_quadraticVanishing_fraction q.1 (hodd q.1 q.2) (wantSquare q)
  have hsumLower :
      ((Q.card - k : ℕ) : ℝ) / 2 ≤
        ∑ q ∈ (Finset.univ : Finset Q) \ L, removed q := by
    have hcard : ((Finset.univ : Finset Q) \ L).card = Q.card - k := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hLcard]
      simp
    calc
      ((Q.card - k : ℕ) : ℝ) / 2 =
          ∑ _q ∈ (Finset.univ : Finset Q) \ L, (1 / 2 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard]
            push_cast
            ring
      _ ≤ ∑ q ∈ (Finset.univ : Finset Q) \ L, removed q := by
        exact Finset.sum_le_sum fun q _ ↦ hhalf q
  have hbaseNonneg :
      0 ≤ (((Q.card - k : ℕ) : ℝ) / (2 * k)) := by positivity
  have hdenom :
      ((((Q.card - k : ℕ) : ℝ) / (2 * k)) ^ k) ≤
        (((∑ q ∈ (Finset.univ : Finset Q) \ L, removed q) / k) ^ k) := by
    apply pow_le_pow_left₀ hbaseNonneg
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    calc
      ((Q.card - k : ℕ) : ℝ) / (2 * k) =
          (((Q.card - k : ℕ) : ℝ) / 2) / k := by ring
      _ ≤ (∑ q ∈ (Finset.univ : Finset Q) \ L, removed q) / k :=
        div_le_div_of_nonneg_right hsumLower hkR.le
  have hcore := Erdos380.residueClassSurvivors_card_le_trimmed_largerSieve
    (fun q : Q ↦ q.1) hcoprime
    (fun q ↦ quadraticVanishing q.1 (wantSquare q))
    k m0 N hk hsubsets hproduct
    (fun q ↦ quadraticVanishing_nonempty q.1 (wantSquare q))
    (fun q ↦ card_quadraticVanishing_lt q.1 (hodd q.1 q.2) (wantSquare q))
    L hLcard htrimNonempty
    (by
      intro i hi l hl
      simpa [removed, Erdos380.residueRemovedFraction] using hlargest i hi l hl)
  have hnum : (0 : ℝ) ≤ (N : ℝ) + N := by positivity
  have hsumPos : 0 < ∑ q ∈ (Finset.univ : Finset Q) \ L, removed q := by
    exact Finset.sum_pos
      (fun q _ ↦ (show (0 : ℝ) < 1 / 2 by norm_num).trans_le (hhalf q))
      htrimNonempty
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdiffPosNat : 0 < Q.card - k := by
    have hcardPos := Finset.card_pos.mpr htrimNonempty
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hLcard] at hcardPos
    simpa using hcardPos
  have htargetPos :
      0 < ((((Q.card - k : ℕ) : ℝ) / (2 * k)) ^ k) := by
    apply pow_pos
    apply div_pos
    · exact_mod_cast hdiffPosNat
    · positivity
  exact hcore.trans (div_le_div_of_nonneg_left hnum
    htargetPos
    hdenom)

/-- The prime-counting form of `quadraticPatternSurvivors_card_le`.  This is
the unconditional raw medium-range estimate: its left side counts actual
prime moduli with all auxiliary primes quadratic residues, while its right
side is exponentially small in the tensor order `k` once `Q.card / k` is
bounded away from `2`. -/
theorem quadraticResiduePrimePattern_card_le
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hodd : ∀ q ∈ Q, q ≠ 2)
    (candidateOneModFour : Bool)
    (k m0 N : ℕ) (hk : 0 < k)
    (hsubsets : Nonempty (Erdos380.fixedCardSubsets Q k))
    (hproduct : ∀ T U : Erdos380.fixedCardSubsets Q k,
      (∏ q ∈ T.1, q.1) * (∏ q ∈ U.1, q.1) ≤ N)
    (L : Finset Q) (hLcard : L.card = k)
    (htrimNonempty : ((Finset.univ : Finset Q) \ L).Nonempty) :
    letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
    letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
    (∀ i ∈ (Finset.univ : Finset Q) \ L,
      ∀ l ∈ L,
        ((quadraticVanishing i.1
          (reciprocityWantsSquare candidateOneModFour i.1)).card : ℝ) / i.1 ≤
        ((quadraticVanishing l.1
          (reciprocityWantsSquare candidateOneModFour l.1)).card : ℝ) / l.1) →
      ((quadraticResiduePrimePattern Q candidateOneModFour m0 N).card : ℝ) ≤
        ((N : ℝ) + N) /
          ((((Q.card - k : ℕ) : ℝ) / (2 * k)) ^ k) := by
  classical
  letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
  letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
  intro hlargest
  have hsubset := quadraticResiduePrimePattern_subset_survivors
    Q hprime hodd candidateOneModFour m0 N
  have hcard :
      ((quadraticResiduePrimePattern Q candidateOneModFour m0 N).card : ℝ) ≤
        ((Erdos380.residueClassSurvivors
          (modulus := fun q : Q ↦ q.1)
          (fun q ↦ quadraticVanishing q.1
            (reciprocityWantsSquare candidateOneModFour q.1)) m0 N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  exact hcard.trans (quadraticPatternSurvivors_card_le
    Q hprime hodd
    (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1)
    k m0 N hk hsubsets hproduct L hLcard htrimNonempty hlargest)

/-! ## Simultaneously sieving for primality

The quadratic restrictions alone give exponential decay in the number of
prescribed residues.  To retain the factor `1 / log x` uniformly when that
number is small, one inserts the ordinary divisibility sieve at the same
time.  The next result is the exact finite combined inequality. -/

/-- Moduli in the disjoint union of quadratic auxiliary primes and ordinary
divisibility-sieve primes. -/
def mixedQuadraticModulus (Q R : Finset ℕ) : Q ⊕ R → ℕ
  | Sum.inl q => q.1
  | Sum.inr r => r.1

/-- On the left summand we remove the wrong quadratic classes; on the right
summand we remove zero, thereby imposing ordinary roughness. -/
noncomputable def mixedQuadraticVanishing
    (Q R : Finset ℕ)
    [∀ q : Q, Fact q.1.Prime] [∀ q : Q, NeZero q.1]
    [∀ r : R, Fact r.1.Prime] [∀ r : R, NeZero r.1]
    (wantSquare : Q → Bool) :
    ∀ i : Q ⊕ R, Finset (ZMod (mixedQuadraticModulus Q R i))
  | Sum.inl q => quadraticVanishing q.1 (wantSquare q)
  | Sum.inr _r => {0}

@[simp] theorem mixedQuadratic_removedFraction_inl
    (Q R : Finset ℕ)
    [∀ q : Q, Fact q.1.Prime] [∀ q : Q, NeZero q.1]
    [∀ r : R, Fact r.1.Prime] [∀ r : R, NeZero r.1]
    [∀ i : Q ⊕ R, NeZero (mixedQuadraticModulus Q R i)]
    (wantSquare : Q → Bool) (q : Q) :
    Erdos380.residueRemovedFraction (mixedQuadraticModulus Q R)
      (mixedQuadraticVanishing Q R wantSquare) (Sum.inl q) =
        ((quadraticVanishing q.1 (wantSquare q)).card : ℝ) / q.1 := by
  rfl

@[simp] theorem mixedQuadratic_removedFraction_inr
    (Q R : Finset ℕ)
    [∀ q : Q, Fact q.1.Prime] [∀ q : Q, NeZero q.1]
    [∀ r : R, Fact r.1.Prime] [∀ r : R, NeZero r.1]
    [∀ i : Q ⊕ R, NeZero (mixedQuadraticModulus Q R i)]
    (wantSquare : Q → Bool) (r : R) :
    Erdos380.residueRemovedFraction (mixedQuadraticModulus Q R)
      (mixedQuadraticVanishing Q R wantSquare) (Sum.inr r) =
        (1 : ℝ) / r.1 := by
  change (({0} : Finset (ZMod r.1)).card : ℝ) / (r.1 : ℝ) =
    (1 : ℝ) / r.1
  rw [Finset.card_singleton, Nat.cast_one]

theorem half_le_mixedQuadratic_removedFraction_inl
    (Q R : Finset ℕ)
    [∀ q : Q, Fact q.1.Prime] [∀ q : Q, NeZero q.1]
    [∀ r : R, Fact r.1.Prime] [∀ r : R, NeZero r.1]
    [∀ i : Q ⊕ R, NeZero (mixedQuadraticModulus Q R i)]
    (hoddQ : ∀ q ∈ Q, q ≠ 2) (wantSquare : Q → Bool) (q : Q) :
    (1 / 2 : ℝ) ≤
      Erdos380.residueRemovedFraction (mixedQuadraticModulus Q R)
        (mixedQuadraticVanishing Q R wantSquare) (Sum.inl q) := by
  rw [mixedQuadratic_removedFraction_inl]
  exact half_le_quadraticVanishing_fraction q.1 (hoddQ q.1 q.2) (wantSquare q)

theorem mixedQuadraticModulus_pairwise
    (Q R : Finset ℕ)
    (hprimeQ : ∀ q ∈ Q, q.Prime) (hprimeR : ∀ r ∈ R, r.Prime)
    (hdisjoint : Disjoint Q R) :
    Pairwise (fun i j : Q ⊕ R ↦
      Nat.Coprime (mixedQuadraticModulus Q R i)
        (mixedQuadraticModulus Q R j)) := by
  intro i j hij
  cases i with
  | inl q =>
      cases j with
      | inl q' =>
          apply (Nat.coprime_primes (hprimeQ q.1 q.2)
            (hprimeQ q'.1 q'.2)).mpr
          intro hqq
          apply hij
          exact congrArg Sum.inl (Subtype.ext hqq)
      | inr r =>
          apply (Nat.coprime_primes (hprimeQ q.1 q.2)
            (hprimeR r.1 r.2)).mpr
          intro hqr
          have hqR : q.1 ∈ R := by simpa [hqr] using r.2
          exact (Finset.disjoint_left.mp hdisjoint) q.2 hqR
  | inr r =>
      cases j with
      | inl q =>
          apply (Nat.coprime_primes (hprimeR r.1 r.2)
            (hprimeQ q.1 q.2)).mpr
          intro hrq
          have hqR : q.1 ∈ R := by simpa [hrq] using r.2
          exact (Finset.disjoint_left.mp hdisjoint) q.2 hqR
      | inr r' =>
          apply (Nat.coprime_primes (hprimeR r.1 r.2)
            (hprimeR r'.1 r'.2)).mpr
          intro hrr
          apply hij
          exact congrArg Sum.inr (Subtype.ext hrr)

theorem quadraticResiduePrimePattern_subset_mixedSurvivors
    (Q R : Finset ℕ)
    (hprimeQ : ∀ q ∈ Q, q.Prime) (hoddQ : ∀ q ∈ Q, q ≠ 2)
    (hprimeR : ∀ r ∈ R, r.Prime)
    (candidateOneModFour : Bool) (m0 N : ℕ)
    (hRle : ∀ r ∈ R, r ≤ m0) :
    letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprimeQ q.1 q.2⟩
    letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprimeQ q.1 q.2).ne_zero⟩
    letI : ∀ r : R, Fact r.1.Prime := fun r ↦ ⟨hprimeR r.1 r.2⟩
    letI : ∀ r : R, NeZero r.1 := fun r ↦ ⟨(hprimeR r.1 r.2).ne_zero⟩
    letI : ∀ i : Q ⊕ R, NeZero (mixedQuadraticModulus Q R i) := fun i ↦
      match i with
      | Sum.inl q => ⟨(hprimeQ q.1 q.2).ne_zero⟩
      | Sum.inr r => ⟨(hprimeR r.1 r.2).ne_zero⟩
    quadraticResiduePrimePattern Q candidateOneModFour m0 N ⊆
      Erdos380.residueClassSurvivors
        (modulus := mixedQuadraticModulus Q R)
        (mixedQuadraticVanishing Q R
          (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1)) m0 N := by
  classical
  letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprimeQ q.1 q.2⟩
  letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprimeQ q.1 q.2).ne_zero⟩
  letI : ∀ r : R, Fact r.1.Prime := fun r ↦ ⟨hprimeR r.1 r.2⟩
  letI : ∀ r : R, NeZero r.1 := fun r ↦ ⟨(hprimeR r.1 r.2).ne_zero⟩
  letI : ∀ i : Q ⊕ R, NeZero (mixedQuadraticModulus Q R i) := fun i ↦
    match i with
    | Sum.inl q => ⟨(hprimeQ q.1 q.2).ne_zero⟩
    | Sum.inr r => ⟨(hprimeR r.1 r.2).ne_zero⟩
  intro p hp
  rw [quadraticResiduePrimePattern] at hp
  obtain ⟨hpInterval, hpPrime, hpClass, hpResidues⟩ := Finset.mem_filter.mp hp
  rw [Erdos380.residueClassSurvivors, Finset.mem_filter]
  refine ⟨hpInterval, ?_⟩
  intro i
  cases i with
  | inl q =>
      obtain ⟨hqp, hsq⟩ := hpResidues q.1 q.2
      letI : Fact p.Prime := ⟨hpPrime⟩
      have hp2 : p ≠ 2 := by
        intro hpEq
        subst p
        cases candidateOneModFour <;> simp at hpClass
      exact square_mod_prime_avoids_quadraticVanishing p q.1 hp2
        (hoddQ q.1 q.2) (Nat.ne_of_gt hqp) candidateOneModFour hpClass hsq
  | inr r =>
      simp only [mixedQuadraticVanishing, Finset.mem_singleton]
      letI : Fact p.Prime := ⟨hpPrime⟩
      have hrp : r.1 ≠ p := by
        have hpLower : m0 < p := (Finset.mem_Ioc.mp hpInterval).1
        exact Nat.ne_of_lt ((hRle r.1 r.2).trans_lt hpLower)
      exact ZMod.prime_ne_zero r.1 p hrp

/-- The combined quadratic/ordinary tensor sieve.  Its denominator contains
one removal ratio for every retained coordinate: at least `1/2` on the
quadratic side, and exactly `1/r` on the ordinary-prime side.  Thus the same
finite theorem simultaneously supplies geometric pattern decay and the
prime-density logarithm. -/
theorem quadraticResiduePrimePattern_card_le_mixed
    (Q R : Finset ℕ)
    (hprimeQ : ∀ q ∈ Q, q.Prime) (hoddQ : ∀ q ∈ Q, q ≠ 2)
    (hprimeR : ∀ r ∈ R, r.Prime)
    (hdisjoint : Disjoint Q R) (candidateOneModFour : Bool)
    (k m0 N : ℕ) (hk : 0 < k) (hRle : ∀ r ∈ R, r ≤ m0)
    (hsubsets : Nonempty (Erdos380.fixedCardSubsets (Q ⊕ R) k))
    (hproduct : ∀ T U : Erdos380.fixedCardSubsets (Q ⊕ R) k,
      (∏ i ∈ T.1, mixedQuadraticModulus Q R i) *
        (∏ i ∈ U.1, mixedQuadraticModulus Q R i) ≤ N)
    (L : Finset (Q ⊕ R)) (hLcard : L.card = k)
    (htrimNonempty : ((Finset.univ : Finset (Q ⊕ R)) \ L).Nonempty) :
    letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprimeQ q.1 q.2⟩
    letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprimeQ q.1 q.2).ne_zero⟩
    letI : ∀ r : R, Fact r.1.Prime := fun r ↦ ⟨hprimeR r.1 r.2⟩
    letI : ∀ r : R, NeZero r.1 := fun r ↦ ⟨(hprimeR r.1 r.2).ne_zero⟩
    letI : ∀ i : Q ⊕ R, NeZero (mixedQuadraticModulus Q R i) := fun i ↦
      match i with
      | Sum.inl q => ⟨(hprimeQ q.1 q.2).ne_zero⟩
      | Sum.inr r => ⟨(hprimeR r.1 r.2).ne_zero⟩
    let vanish := mixedQuadraticVanishing Q R
      (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1)
    (∀ i ∈ (Finset.univ : Finset (Q ⊕ R)) \ L,
      ∀ l ∈ L,
        Erdos380.residueRemovedFraction (mixedQuadraticModulus Q R) vanish i ≤
          Erdos380.residueRemovedFraction (mixedQuadraticModulus Q R) vanish l) →
      ((quadraticResiduePrimePattern Q candidateOneModFour m0 N).card : ℝ) ≤
        ((N : ℝ) + N) /
          (((∑ i ∈ (Finset.univ : Finset (Q ⊕ R)) \ L,
            Erdos380.residueRemovedFraction
              (mixedQuadraticModulus Q R) vanish i) / k) ^ k) := by
  classical
  letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprimeQ q.1 q.2⟩
  letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprimeQ q.1 q.2).ne_zero⟩
  letI : ∀ r : R, Fact r.1.Prime := fun r ↦ ⟨hprimeR r.1 r.2⟩
  letI : ∀ r : R, NeZero r.1 := fun r ↦ ⟨(hprimeR r.1 r.2).ne_zero⟩
  letI : ∀ i : Q ⊕ R, NeZero (mixedQuadraticModulus Q R i) := fun i ↦
    match i with
    | Sum.inl q => ⟨(hprimeQ q.1 q.2).ne_zero⟩
    | Sum.inr r => ⟨(hprimeR r.1 r.2).ne_zero⟩
  dsimp only
  intro hlargest
  let vanish := mixedQuadraticVanishing Q R
    (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1)
  have hsubset := quadraticResiduePrimePattern_subset_mixedSurvivors
    Q R hprimeQ hoddQ hprimeR candidateOneModFour m0 N hRle
  have hcard :
      ((quadraticResiduePrimePattern Q candidateOneModFour m0 N).card : ℝ) ≤
        ((Erdos380.residueClassSurvivors
          (modulus := mixedQuadraticModulus Q R) vanish m0 N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hnonempty : ∀ i : Q ⊕ R, (vanish i).Nonempty := by
    intro i
    cases i with
    | inl q => exact quadraticVanishing_nonempty q.1 _
    | inr r => simp [vanish, mixedQuadraticVanishing]
  have hproper : ∀ i : Q ⊕ R,
      (vanish i).card < mixedQuadraticModulus Q R i := by
    intro i
    cases i with
    | inl q => exact card_quadraticVanishing_lt q.1 (hoddQ q.1 q.2) _
    | inr r =>
        simp only [vanish, mixedQuadraticVanishing, Finset.card_singleton,
          mixedQuadraticModulus]
        exact (hprimeR r.1 r.2).one_lt
  exact hcard.trans (Erdos380.residueClassSurvivors_card_le_trimmed_largerSieve
    (mixedQuadraticModulus Q R)
    (mixedQuadraticModulus_pairwise Q R hprimeQ hprimeR hdisjoint)
    vanish k m0 N hk hsubsets hproduct hnonempty hproper
    L hLcard htrimNonempty hlargest)

/-! ## A Rosser-ready congruence-base endpoint estimate

The ordinary prime sieve is most efficiently applied after collecting the
quadratic conditions into a finite set of residue classes modulo their
product.  The following lemma is the exact endpoint input needed by the
generic Rosser sieve: imposing an additional coprime divisor costs the
expected factor `1 / d`, with an error of at most two points for each base
class. -/

/-- The part of a union of base residue classes which is divisible by `d`. -/
def divisibleBaseCongruenceSet
    (L U M d : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Erdos387.modularPreimageIoc L U M A).filter (d ∣ ·)

/-- A coprime divisibility condition on a finite union of residue classes
has the uniform CRT endpoint discrepancy `2 * #A`. -/
theorem abs_card_divisibleBaseCongruenceSet_sub_density
    {L U M d : ℕ} (hLU : L ≤ U) (hM : 0 < M) (hd : 0 < d)
    (hcop : M.Coprime d) (A : Finset ℕ) (hA : ∀ a ∈ A, a < M) :
    |((divisibleBaseCongruenceSet L U M d A).card : ℝ) -
        (A.card : ℝ) * (U - L : ℕ) / (M * d : ℕ)| ≤
      2 * A.card := by
  classical
  let C : ℕ → Finset ℕ := fun a ↦
    Erdos387.modularPreimageIoc L U (M * d)
      {Erdos387.simultaneousResidue hcop a 0}
  have hset : divisibleBaseCongruenceSet L U M d A = A.biUnion C := by
    ext n
    rw [divisibleBaseCongruenceSet, Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hnBase, hdn⟩
      have hnBase' := hnBase
      rw [Erdos387.modularPreimageIoc, Finset.mem_filter] at hnBase'
      obtain ⟨hnIoc, hnA⟩ := hnBase'
      let a := n % M
      have ha : a ∈ A := hnA
      have haM : n ≡ a [MOD M] := by simp [a, Nat.ModEq]
      have hnD : n ≡ 0 [MOD d] := by
        exact (Nat.modEq_zero_iff_dvd.mpr hdn)
      refine ⟨a, ha, ?_⟩
      apply (Erdos387.mem_simultaneousClassIoc_iff hcop hM hd).mpr
      exact ⟨hnIoc, haM, hnD⟩
    · rintro ⟨a, ha, hnClass⟩
      have hnData := (Erdos387.mem_simultaneousClassIoc_iff
        hcop hM hd).mp (by
          simpa [Erdos387.simultaneousClassIoc, C] using hnClass)
      refine ⟨?_, ?_⟩
      · rw [Erdos387.modularPreimageIoc, Finset.mem_filter]
        refine ⟨hnData.1, ?_⟩
        have hna : n % M = a := by
          simpa [Nat.ModEq, Nat.mod_eq_of_lt (hA a ha)] using
            show n % M = a % M from hnData.2.1
        simpa [hna] using ha
      · exact Nat.modEq_zero_iff_dvd.mp hnData.2.2
  have hpair : (A : Set ℕ).PairwiseDisjoint C := by
    intro a ha b hb hab
    change Disjoint (C a) (C b)
    rw [Finset.disjoint_left]
    intro n hna hnb
    have hna' : n ≡ a [MOD M] := by
      have hm := (Erdos387.mem_simultaneousClassIoc_iff
        hcop hM hd).mp (by simpa [Erdos387.simultaneousClassIoc, C] using hna)
      exact hm.2.1
    have hnb' : n ≡ b [MOD M] := by
      have hm := (Erdos387.mem_simultaneousClassIoc_iff
        hcop hM hd).mp (by simpa [Erdos387.simultaneousClassIoc, C] using hnb)
      exact hm.2.1
    apply hab
    have habmod : a ≡ b [MOD M] := hna'.symm.trans hnb'
    exact habmod.eq_of_lt_of_lt (hA a ha) (hA b hb)
  have hcard : (divisibleBaseCongruenceSet L U M d A).card =
      ∑ a ∈ A, (C a).card := by
    rw [hset, Finset.card_biUnion hpair]
  have hterm (a : ℕ) (ha : a ∈ A) :
      |↑(C a).card - ((U - L : ℕ) : ℝ) / (M * d : ℕ)| ≤ 2 := by
    have h := Erdos387.abs_card_modularPreimageIoc_sub_density hLU
      (Nat.mul_pos hM hd)
      ({Erdos387.simultaneousResidue hcop a 0} : Finset ℕ)
      (by
        intro r hr
        simp only [Finset.mem_singleton] at hr
        subst r
        exact Erdos387.simultaneousResidue_lt hcop hM hd a 0)
    simpa [C] using h
  rw [hcard, Nat.cast_sum]
  have hrewrite :
      (∑ a ∈ A, (↑(C a).card : ℝ)) -
          (A.card : ℝ) * (U - L : ℕ) / (M * d : ℕ) =
        ∑ a ∈ A, ((↑(C a).card : ℝ) -
          ((U - L : ℕ) : ℝ) / (M * d : ℕ)) := by
    rw [Finset.sum_sub_distrib]
    simp [nsmul_eq_mul]
    ring
  rw [hrewrite]
  calc
    |∑ a ∈ A, (↑(C a).card -
        ((U - L : ℕ) : ℝ) / (M * d : ℕ))| ≤
        ∑ a ∈ A, |↑(C a).card -
          ((U - L : ℕ) : ℝ) / (M * d : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ A, (2 : ℝ) := Finset.sum_le_sum hterm
    _ = 2 * A.card := by simp [nsmul_eq_mul, mul_comm]

/-! ## The arbitrary-base one-dimensional bounding sieve -/

open Erdos851
open Erdos851.ShiftSieve

/-- The ordinary prime sieve on a union of canonical residue classes modulo
`M`.  Coprimality of `M` with the sieve product is deliberately kept at the
use site: in the quadratic application all primes dividing `M` lie below
the lower sieve endpoint. -/
noncomputable def baseCongruenceBoundingSieve
    (L U M z Y : ℕ) (A : Finset ℕ) : BoundingSieve := by
  classical
  exact
    { support := Erdos387.modularPreimageIoc L U M A
      prodPrimes := Erdos387.sievePrimeProduct z Y
      prodPrimes_squarefree := Erdos387.sievePrimeProduct_squarefree z Y
      weights := fun _ ↦ 1
      weights_nonneg := fun _ ↦ by norm_num
      totalMass := (A.card : ℝ) * (U - L : ℕ) / M
      nu := shiftNu {0}
      nu_mult := shiftNu_mult {0}
      nu_pos_of_prime := by
        intro p hp _hpDiv
        rw [shiftNu_prime hp, localNu_singleton]
        exact div_pos (by norm_num) (by exact_mod_cast hp.pos)
      nu_lt_one_of_prime := by
        intro p hp _hpDiv
        rw [shiftNu_prime hp, localNu_singleton]
        exact (div_lt_one (by exact_mod_cast hp.pos)).mpr
          (by exact_mod_cast hp.one_lt) }

@[simp] theorem baseCongruenceBoundingSieve_totalMass
    (L U M z Y : ℕ) (A : Finset ℕ) :
    (baseCongruenceBoundingSieve L U M z Y A).totalMass =
      (A.card : ℝ) * (U - L : ℕ) / M := rfl

/-- The abstract multiple sum is the literal divisible subset of the base
congruence union. -/
theorem baseCongruenceBoundingSieve_multSum
    (L U M z Y d : ℕ) (A : Finset ℕ) :
    (baseCongruenceBoundingSieve L U M z Y A).multSum d =
      ((divisibleBaseCongruenceSet L U M d A).card : ℝ) := by
  classical
  rw [BoundingSieve.multSum]
  change (∑ n ∈ Erdos387.modularPreimageIoc L U M A,
    if d ∣ n then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp [divisibleBaseCongruenceSet]

/-- The abstract sifted sum is the cardinality of the base-class points
coprime to the full ordinary sieve product. -/
theorem baseCongruenceBoundingSieve_siftedSum
    (L U M z Y : ℕ) (A : Finset ℕ) :
    (baseCongruenceBoundingSieve L U M z Y A).siftedSum =
      (((Erdos387.modularPreimageIoc L U M A).filter fun n ↦
        Nat.Coprime (Erdos387.sievePrimeProduct z Y) n).card : ℝ) := by
  classical
  rw [BoundingSieve.siftedSum]
  change (∑ n ∈ Erdos387.modularPreimageIoc L U M A,
    if Nat.Coprime (Erdos387.sievePrimeProduct z Y) n then
      (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp

/-- Exact endpoint remainder for the arbitrary-base sieve. -/
theorem baseCongruenceBoundingSieve_abs_rem_le
    {L U M z Y d : ℕ} (hLU : L ≤ U) (hM : 0 < M)
    (hcop : M.Coprime (Erdos387.sievePrimeProduct z Y))
    (A : Finset ℕ) (hA : ∀ a ∈ A, a < M)
    (hd : d ∣ Erdos387.sievePrimeProduct z Y) :
    |(baseCongruenceBoundingSieve L U M z Y A).rem d| ≤ 2 * A.card := by
  have hdpos : 0 < d := Erdos387.pos_of_dvd_sievePrimeProduct hd
  have hdSquarefree : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (Erdos387.sievePrimeProduct_squarefree z Y)
  have hcopd : M.Coprime d := hcop.of_dvd_right hd
  rw [BoundingSieve.rem, baseCongruenceBoundingSieve_multSum,
    baseCongruenceBoundingSieve_totalMass]
  change |((divisibleBaseCongruenceSet L U M d A).card : ℝ) -
    shiftNu {0} d * ((A.card : ℝ) * (U - L : ℕ) / M)| ≤
      2 * A.card
  rw [shiftNu_squarefree hdSquarefree]
  have hnuClasses : nuClasses {0} d = 1 := by
    simp [nuClasses, localNu_singleton]
  rw [hnuClasses, Nat.cast_one]
  have hendpoint := abs_card_divisibleBaseCongruenceSet_sub_density
    hLU hM hdpos hcopd A hA
  rw [Nat.cast_mul] at hendpoint
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  convert hendpoint using 1
  congr 1
  field_simp [hMne, hdne]
  <;> ring

open Erdos851.FiniteCombinatorialSieve
open Erdos851.BetaSieveFundamental
open Erdos387.FiniteBetaSieveBridge

/-- A completely unconditional Rosser upper bound for an arbitrary union of
base congruence classes.  The first term is the expected base density times
the one-dimensional Euler product.  The second is the exact CRT endpoint
loss retained at level `y ^ S`.

This is the finite estimate used for the small and medium quadratic-pattern
indices; it contains no analytic hypothesis beyond explicit inequalities on
the displayed parameters. -/
theorem exists_baseCongruence_rosser_upper_bound :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {L U M z y S : ℕ} (A : Finset ℕ),
        L ≤ U → 0 < M → (∀ a ∈ A, a < M) →
        M.Coprime (Erdos387.sievePrimeProduct z (y + 1)) →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log C ≤ 2 * (S - 100 : ℕ) / 99 →
        let P := Erdos851.ascendingSievePrimes z y
        let V := Erdos851.localEulerProduct Erdos851.oneShiftDensity z y
        let eta := (4 * C / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (((Erdos387.modularPreimageIoc L U M A).filter fun n ↦
            Nat.Coprime (Erdos387.sievePrimeProduct z (y + 1)) n).card : ℝ) ≤
          ((A.card : ℝ) * (U - L : ℕ) / M) * ((1 + eta) * V) +
            (2 * A.card : ℝ) * (y ^ S : ℕ) *
              (P.map fun p ↦ 1 + (1 : ℝ) / p).prod := by
  classical
  obtain ⟨C, hC, hmain⟩ :=
    Erdos851.BetaSieveFundamental.exists_oneShift_concrete_finiteMainTerm_bounds
  refine ⟨C, hC, ?_⟩
  intro L U M z y S A hLU hM hA hcop hz hzy hy hS hlog
  dsimp only
  let P := Erdos851.ascendingSievePrimes z y
  let D := y ^ S
  let stop := rosserStoppingPredicate 100 D
  let sieve := baseCongruenceBoundingSieve L U M z (y + 1) A
  have hprod : P.prod = sieve.prodPrimes := by
    simpa [P, sieve, baseCongruenceBoundingSieve] using
      Erdos851.ascendingSievePrimes_prod z y
  have hsort : P.Pairwise (· ≤ ·) := by
    simpa [P] using Erdos851.ascendingSievePrimes_pairwise z y
  have hnodup : P.Nodup := by
    simpa [P] using Erdos851.ascendingSievePrimes_nodup z y
  have hprime : ∀ p ∈ P, p.Prime := by
    simpa [P] using (Erdos851.ascendingSievePrimes_prime (z := z) (y := y))
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by omega)
  have hrem : ∀ d : ℕ, d ∣ sieve.prodPrimes →
      |sieve.rem d| ≤ (2 * A.card : ℝ) *
        ((1 : ℕ) : ℝ) ^ d.primeFactors.card := by
    intro d hd
    simpa [sieve] using
      (baseCongruenceBoundingSieve_abs_rem_le hLU hM hcop A hA hd)
  have hsieve := boundingSieve_siftedSum_le_rosserUpperMain_add_levelEuler
    sieve P (2 * A.card : ℝ) 1 100 D hprod hsort hnodup hprime
      (by norm_num) hD hrem (by positivity)
  have hm := hmain z y S hz hzy hy hS hlog
  dsimp only at hm
  have hnu : ∀ p ∈ P, sieve.nu p = Erdos851.oneShiftDensity p := by
    intro p hp
    change shiftNu {0} p = Erdos851.oneShiftDensity p
    exact Erdos851.shiftNu_singleton_prime 0 (hprime p hp)
  rw [Erdos851.upperMainTerm_congr_on stop (fun p ↦ sieve.nu p)
    Erdos851.oneShiftDensity P hnu] at hsieve
  rw [baseCongruenceBoundingSieve_siftedSum,
    baseCongruenceBoundingSieve_totalMass] at hsieve
  have hmainle := mul_le_mul_of_nonneg_left hm.2
    (show 0 ≤ (A.card : ℝ) * (U - L : ℕ) / M by positivity)
  have htotal := add_le_add hmainle
    (le_refl ((2 * A.card : ℝ) * (D : ℕ) *
      (P.map fun p ↦ 1 + (((1 : ℕ) : ℝ) / p)).prod))
  exact hsieve.trans (by
    simpa [P, D, stop, Erdos851.ascendingSievePrimes] using htotal)

/-! ## Exact CRT packaging of the quadratic base classes -/

/-- Canonical natural representatives of a Cartesian product of allowed
local residue sets. -/
noncomputable def crtBaseResidues
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ)
    (hcoprime : Pairwise (Function.onFun Nat.Coprime modulus))
    (allowed : ∀ i, Finset (ZMod (modulus i))) : Finset ℕ := by
  classical
  let e := ZMod.prodEquivPi modulus hcoprime
  exact (Fintype.piFinset allowed).image fun a ↦ (e.symm a).val

/-- Every CRT representative is canonical modulo the product modulus. -/
theorem crtBaseResidues_lt
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime modulus))
    (allowed : ∀ i, Finset (ZMod (modulus i))) :
    ∀ a ∈ crtBaseResidues modulus hcoprime allowed,
      a < ∏ i, modulus i := by
  classical
  letI : NeZero (∏ i, modulus i) := ⟨Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ NeZero.ne (modulus i))⟩
  intro a ha
  rw [crtBaseResidues, Finset.mem_image] at ha
  obtain ⟨v, _hv, rfl⟩ := ha
  exact ZMod.val_lt _

/-- Exact cardinality factorization for canonical CRT representatives. -/
theorem card_crtBaseResidues
    {I : Type*} [Fintype I] [DecidableEq I]
    (modulus : I → ℕ) [∀ i, NeZero (modulus i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime modulus))
    (allowed : ∀ i, Finset (ZMod (modulus i))) :
    (crtBaseResidues modulus hcoprime allowed).card =
      ∏ i, (allowed i).card := by
  classical
  letI : NeZero (∏ i, modulus i) := ⟨Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ NeZero.ne (modulus i))⟩
  rw [crtBaseResidues, Finset.card_image_iff.mpr]
  · exact Fintype.card_piFinset allowed
  · intro a _ha b _hb hab
    apply (ZMod.prodEquivPi modulus hcoprime).symm.injective
    exact ZMod.val_injective _ hab

/-- The allowed local half-field after reciprocity has fixed the sign. -/
noncomputable def quadraticAllowed (q : ℕ) [Fact q.Prime]
    (wantSquare : Bool) : Finset (ZMod q) :=
  Finset.univ \ quadraticVanishing q wantSquare

theorem card_quadraticAllowed (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) (wantSquare : Bool) :
    (quadraticAllowed q wantSquare).card = (q - 1) / 2 := by
  rw [quadraticAllowed, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, ZMod.card, card_quadraticVanishing q hq2]
  omega

theorem mem_quadraticAllowed_iff (q : ℕ) [Fact q.Prime]
    (wantSquare : Bool) (a : ZMod q) :
    a ∈ quadraticAllowed q wantSquare ↔
      a ∉ quadraticVanishing q wantSquare := by
  simp [quadraticAllowed]

/-- Product of the auxiliary quadratic primes. -/
def quadraticBaseModulus (Q : Finset ℕ) : ℕ := ∏ q ∈ Q, q

/-- Exact CRT base classes for a prescribed quadratic sign at every member
of `Q`. -/
noncomputable def quadraticBaseResidues
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (wantSquare : Q → Bool) : Finset ℕ := by
  classical
  letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
  letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
  let hcoprime : Pairwise
      (Function.onFun Nat.Coprime fun q : Q ↦ q.1) := by
    intro q r hqr
    exact (Nat.coprime_primes (hprime q.1 q.2) (hprime r.1 r.2)).mpr
      (Subtype.coe_ne_coe.mpr hqr)
  exact crtBaseResidues (fun q : Q ↦ q.1) hcoprime
    (fun q ↦ quadraticAllowed q.1 (wantSquare q))

theorem quadraticBaseModulus_pos
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime) :
    0 < quadraticBaseModulus Q := by
  unfold quadraticBaseModulus
  exact Finset.prod_pos fun q hq ↦ (hprime q hq).pos

theorem quadraticBaseResidues_lt
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (wantSquare : Q → Bool) :
    ∀ a ∈ quadraticBaseResidues Q hprime wantSquare,
      a < quadraticBaseModulus Q := by
  classical
  letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
  letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
  let hcoprime : Pairwise
      (Function.onFun Nat.Coprime fun q : Q ↦ q.1) := by
    intro q r hqr
    exact (Nat.coprime_primes (hprime q.1 q.2) (hprime r.1 r.2)).mpr
      (Subtype.coe_ne_coe.mpr hqr)
  have hprod : (∏ q : Q, q.1) = ∏ q ∈ Q, q := by
    change (∏ q ∈ (Finset.univ : Finset Q), q.1) = _
    rw [show (Finset.univ : Finset Q) = Q.attach by ext; simp]
    simpa using (Finset.prod_attach Q id)
  rw [quadraticBaseModulus, ← hprod]
  simpa [quadraticBaseResidues] using
    (crtBaseResidues_lt (fun q : Q ↦ q.1) hcoprime
      (fun q ↦ quadraticAllowed q.1 (wantSquare q)))

theorem card_quadraticBaseResidues
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hodd : ∀ q ∈ Q, q ≠ 2) (wantSquare : Q → Bool) :
    (quadraticBaseResidues Q hprime wantSquare).card =
      ∏ q ∈ Q, (q - 1) / 2 := by
  classical
  letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
  letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
  let hcoprime : Pairwise
      (Function.onFun Nat.Coprime fun q : Q ↦ q.1) := by
    intro q r hqr
    exact (Nat.coprime_primes (hprime q.1 q.2) (hprime r.1 r.2)).mpr
      (Subtype.coe_ne_coe.mpr hqr)
  rw [quadraticBaseResidues,
    card_crtBaseResidues (fun q : Q ↦ q.1) hcoprime]
  change (∏ q ∈ (Finset.univ : Finset Q),
    (quadraticAllowed q.1 (wantSquare q)).card) = _
  rw [show (Finset.univ : Finset Q) = Q.attach by ext; simp]
  calc
    (∏ q ∈ Q.attach, (quadraticAllowed q.1 (wantSquare q)).card) =
        ∏ q ∈ Q.attach, (q.1 - 1) / 2 := by
      apply Finset.prod_congr rfl
      intro q hq
      exact card_quadraticAllowed q.1 (hodd q.1 q.2) _
    _ = ∏ q ∈ Q, (q - 1) / 2 := by
      simpa using (Finset.prod_attach Q (fun q ↦ (q - 1) / 2))

/-- A prime pattern satisfying the quadratic conditions lies in the exact
CRT base classes and, once the ordinary sieve endpoint is below the interval,
survives the ordinary prime sieve. -/
theorem quadraticResiduePrimePattern_subset_baseSifted
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hodd : ∀ q ∈ Q, q ≠ 2) (candidateOneModFour : Bool)
    (m0 N z y : ℕ) (hy : y ≤ m0) :
    quadraticResiduePrimePattern Q candidateOneModFour m0 N ⊆
      (Erdos387.modularPreimageIoc m0 (m0 + N)
        (quadraticBaseModulus Q)
        (quadraticBaseResidues Q hprime
          (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1))).filter
        (fun n ↦ Nat.Coprime (Erdos387.sievePrimeProduct z (y + 1)) n) := by
  classical
  letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
  letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
  let hcoprime : Pairwise
      (Function.onFun Nat.Coprime fun q : Q ↦ q.1) := by
    intro q r hqr
    exact (Nat.coprime_primes (hprime q.1 q.2) (hprime r.1 r.2)).mpr
      (Subtype.coe_ne_coe.mpr hqr)
  let M := ∏ q : Q, q.1
  have hMeq : M = quadraticBaseModulus Q := by
    dsimp [M, quadraticBaseModulus]
    change (∏ q ∈ (Finset.univ : Finset Q), q.1) = _
    rw [show (Finset.univ : Finset Q) = Q.attach by ext; simp]
    simpa using (Finset.prod_attach Q id)
  have hMpos : 0 < M := by
    rw [hMeq]
    exact quadraticBaseModulus_pos Q hprime
  letI : NeZero M := ⟨hMpos.ne'⟩
  intro p hp
  rw [quadraticResiduePrimePattern, Finset.mem_filter] at hp
  obtain ⟨hpIoc, hpPrime, hpClass, hpSquares⟩ := hp
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [Erdos387.modularPreimageIoc, Finset.mem_filter]
    refine ⟨hpIoc, ?_⟩
    rw [← hMeq]
    let e := ZMod.prodEquivPi (fun q : Q ↦ q.1) hcoprime
    let v : ∀ q : Q, ZMod q.1 := e (p : ZMod M)
    have hv : v ∈ Fintype.piFinset (fun q : Q ↦
        quadraticAllowed q.1
          (reciprocityWantsSquare candidateOneModFour q.1)) := by
      rw [Fintype.mem_piFinset]
      intro q
      apply (mem_quadraticAllowed_iff q.1 _ _).mpr
      letI : Fact p.Prime := ⟨hpPrime⟩
      have hp2 : p ≠ 2 := by
        intro hpEq
        subst p
        cases candidateOneModFour <;> simp at hpClass
      have havoid := square_mod_prime_avoids_quadraticVanishing
        p q.1 hp2 (hodd q.1 q.2)
          (Nat.ne_of_gt (hpSquares q.1 q.2).1)
          candidateOneModFour hpClass (hpSquares q.1 q.2).2
      have hvq : v q = (p : ZMod q.1) := by
        simpa [v, e] using
          congrFun (ZMod.prodEquivPi_apply
            (fun q : Q ↦ q.1) hcoprime (p : ZMod M)) q
      simpa [hvq] using havoid
    change p % M ∈ crtBaseResidues (fun q : Q ↦ q.1) hcoprime
      (fun q ↦ quadraticAllowed q.1
        (reciprocityWantsSquare candidateOneModFour q.1))
    rw [crtBaseResidues, Finset.mem_image]
    refine ⟨v, hv, ?_⟩
    have hev : e.symm v = (p : ZMod M) := by
      exact e.symm_apply_apply (p : ZMod M)
    change (e.symm v).val = p % M
    rw [hev]
    exact ZMod.val_natCast M p
  · apply (Nat.coprime_comm.mp)
    rw [hpPrime.coprime_iff_not_dvd]
    intro hpdiv
    have hpmem := Erdos387.prime_mem_sievePrimes_of_dvd_product hpPrime hpdiv
    have hpy : p < y + 1 := (Erdos387.mem_sievePrimes.mp hpmem).2.2
    have hpm0 : m0 < p := (Finset.mem_Ioc.mp hpIoc).1
    omega

/-- The exact CRT base density is at most `2 ^ (-#Q)`. -/
theorem quadraticBaseResidues_density_le_geometric
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hodd : ∀ q ∈ Q, q ≠ 2) (wantSquare : Q → Bool) :
    ((quadraticBaseResidues Q hprime wantSquare).card : ℝ) /
        quadraticBaseModulus Q ≤ (1 / 2 : ℝ) ^ Q.card := by
  rw [card_quadraticBaseResidues Q hprime hodd wantSquare,
    quadraticBaseModulus]
  push_cast
  rw [← Finset.prod_div_distrib]
  calc
    ∏ q ∈ Q, ((((q - 1) / 2 : ℕ) : ℝ) / q) ≤
        ∏ _q ∈ Q, (1 / 2 : ℝ) := by
      apply Finset.prod_le_prod
      · intro q hq
        positivity
      · intro q hq
        have hqpos : (0 : ℝ) < q := by exact_mod_cast (hprime q hq).pos
        rw [div_le_iff₀ hqpos]
        have hn : 2 * ((q - 1) / 2) ≤ q := by omega
        have hnR : (2 : ℝ) * (((q - 1) / 2 : ℕ) : ℝ) ≤ q := by
          exact_mod_cast hn
        nlinarith
    _ = (1 / 2 : ℝ) ^ Q.card := by simp

/-- If every quadratic auxiliary prime is at most the lower ordinary sieve
endpoint, the quadratic CRT modulus and ordinary sieve product are coprime. -/
theorem quadraticBaseModulus_coprime_sievePrimeProduct
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    {z Y : ℕ} (hQz : ∀ q ∈ Q, q ≤ z) :
    (quadraticBaseModulus Q).Coprime
      (Erdos387.sievePrimeProduct z Y) := by
  unfold quadraticBaseModulus Erdos387.sievePrimeProduct
  apply Nat.Coprime.prod_left
  intro q hq
  apply Nat.Coprime.prod_right
  intro r hr
  have hrData := Erdos387.mem_sievePrimes.mp hr
  have hqz := hQz q hq
  have hzr := hrData.2.1
  apply (Nat.coprime_primes (hprime q hq) hrData.1).mpr
  omega

/-! ## A finite Rosser estimate with all analytic factors exposed -/

private theorem ascendingSievePrimes_endpointEuler_le_inverseLocalEuler
    {z y : ℕ} (hz : 2 ≤ z) :
    ((Erdos851.ascendingSievePrimes z y).map
        (fun p : ℕ ↦ 1 + (1 : ℝ) / p)).prod ≤
      Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity z y := by
  classical
  rw [Erdos851.inverseLocalEulerProduct]
  change ((Erdos851.ascendingSievePrimes z y).map
      (fun p : ℕ ↦ 1 + (1 : ℝ) / p)).prod ≤ _
  rw [← List.prod_toFinset _ (Erdos851.ascendingSievePrimes_nodup z y)]
  have hset : (Erdos851.ascendingSievePrimes z y).toFinset =
      Erdos851.sievePrimes z y := by
    ext p
    simp only [List.mem_toFinset, Erdos851.mem_ascendingSievePrimes]
  rw [hset]
  apply Finset.prod_le_prod
  · intro p hp
    exact add_nonneg zero_le_one (div_nonneg zero_le_one (by positivity))
  · intro p hp
    have hp' : p ∈ Erdos851.ascendingSievePrimes z y :=
      Erdos851.mem_ascendingSievePrimes.mpr hp
    have hpPrime := Erdos851.ascendingSievePrimes_prime p hp'
    have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    have hden : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr
      (inv_lt_one_of_one_lt₀ hpR)
    change 1 + 1 / (p : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹
    rw [inv_eq_one_div, le_div_iff₀ hden]
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    field_simp [hp0]
    nlinarith

/-- The custom CRT Rosser sieve, the exact quadratic base density, and both
directions of weak Mertens combine to give a finite estimate in its final
analytic shape.  The first term is geometric in the number of prescribed
quadratic residues and has the prime-counting scale `N / log y`; the second
is the completely explicit finite-level endpoint loss. -/
theorem exists_quadraticResiduePrimePattern_rosser_upper_bound :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ {Q : Finset ℕ} (hprime : ∀ q ∈ Q, q.Prime)
        (hodd : ∀ q ∈ Q, q ≠ 2) (candidateOneModFour : Bool)
        {m0 N z y S : ℕ},
        y ≤ m0 → 2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        (∀ q ∈ Q, q ≤ z) →
        Real.log (Classical.choose exists_baseCongruence_rosser_upper_bound) ≤
          2 * (S - 100 : ℕ) / 99 →
        ((quadraticResiduePrimePattern Q candidateOneModFour m0 N).card : ℝ) ≤
          C₁ * (1 / 2 : ℝ) ^ Q.card * (N : ℝ) *
              (Real.log (z : ℝ) / Real.log (y : ℝ)) +
            C₂ * ((quadraticBaseResidues Q hprime
                (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1)).card : ℝ) *
              (y ^ S : ℕ) *
                (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
  classical
  let Cβ := Classical.choose exists_baseCongruence_rosser_upper_bound
  have hspec := Classical.choose_spec exists_baseCongruence_rosser_upper_bound
  rcases hspec with ⟨hCβ, hrosser⟩
  obtain ⟨Cd, hCd, hdirect⟩ := Erdos822.exists_oneShift_localEulerProduct_upper
  obtain ⟨Ci, hCi, hinverse⟩ := Erdos851.exists_oneShift_dimension_bound
  refine ⟨(1 + Cβ / 3) * Cd, 2 * Ci, ?_, ?_, ?_⟩
  · have hCβpos : 0 < Cβ := zero_lt_one.trans_le hCβ
    positivity
  · positivity
  intro Q hprime hodd candidateOneModFour m0 N z y S
    hym0 hz hzy hy hS hQz hlog
  let A := quadraticBaseResidues Q hprime
    (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1)
  let M := quadraticBaseModulus Q
  let P := Erdos851.ascendingSievePrimes z y
  let E := (P.map fun p : ℕ ↦ 1 + (1 : ℝ) / p).prod
  let V := Erdos851.localEulerProduct Erdos851.oneShiftDensity z y
  let eta := (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
  have hM : 0 < M := quadraticBaseModulus_pos Q hprime
  have hA : ∀ a ∈ A, a < M := by
    simpa [A, M] using quadraticBaseResidues_lt Q hprime
      (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1)
  have hPcast : (P : List ℝ) = P.map (fun p : ℕ ↦ (p : ℝ)) := by
    change List.flatMap (fun p : ℕ ↦ [(p : ℝ)]) P = _
    exact List.map_eq_flatMap.symm
  have hE : (P.map fun p ↦ 1 + (1 : ℝ) / p).prod = E := by
    rw [hPcast, List.map_map]
    rfl
  have hcop : M.Coprime (Erdos387.sievePrimeProduct z (y + 1)) := by
    simpa [M] using quadraticBaseModulus_coprime_sievePrimeProduct
      Q hprime hQz
  have hsieve := hrosser A (Nat.le_add_right m0 N) hM hA hcop hz hzy hy hS
    (by simpa using hlog)
  dsimp only at hsieve
  rw [hE] at hsieve
  have hsubset := quadraticResiduePrimePattern_subset_baseSifted
    Q hprime hodd candidateOneModFour m0 N z y hym0
  have hcard :
      ((quadraticResiduePrimePattern Q candidateOneModFour m0 N).card : ℝ) ≤
        (((Erdos387.modularPreimageIoc m0 (m0 + N) M A).filter fun n ↦
          Nat.Coprime (Erdos387.sievePrimeProduct z (y + 1)) n).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hgeo : (A.card : ℝ) / M ≤ (1 / 2 : ℝ) ^ Q.card := by
    simpa [A, M] using quadraticBaseResidues_density_le_geometric Q hprime hodd
      (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1)
  have hVpos : 0 ≤ V := (Erdos851.oneShift_localEulerProduct_pos (z := z) (y := y)).le
  have hetaNonneg : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have heta : eta ≤ Cβ / 3 := by
    have hexp : 1 ≤ S - 100 := by omega
    have hpow : (1 / 4 : ℝ) ^ (S - 100) ≤ 1 / 4 := by
      have hbase : (0 : ℝ) ≤ 1 / 4 := by norm_num
      simpa only [pow_one] using
        (pow_le_pow_of_le_one hbase (by norm_num : (1 / 4 : ℝ) ≤ 1) hexp)
    have hCβnonneg : 0 ≤ 4 * Cβ / 3 := by
      have : 0 ≤ Cβ := zero_le_one.trans hCβ
      positivity
    calc
      eta ≤ (4 * Cβ / 3) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow hCβnonneg
      _ = Cβ / 3 := by ring
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have hV : V ≤ Cd * (Real.log (z : ℝ) / Real.log (y : ℝ)) := by
    simpa [V] using hdirect z y hz hzy
  have hPinv : E ≤ Ci * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
    calc
      E ≤ Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity z y := by
        simpa [E, P] using ascendingSievePrimes_endpointEuler_le_inverseLocalEuler
          (z := z) (y := y) hz
      _ ≤ Ci * (Real.log (y : ℝ) / Real.log (z : ℝ)) :=
        hinverse z y hz hzy
  have hmainNonneg : 0 ≤ (1 + eta) * V := mul_nonneg (by linarith) hVpos
  have hmain :
      ((A.card : ℝ) * (N : ℕ) / M) * ((1 + eta) * V) ≤
        ((1 + Cβ / 3) * Cd) * (1 / 2 : ℝ) ^ Q.card * (N : ℝ) *
          (Real.log (z : ℝ) / Real.log (y : ℝ)) := by
    have hratioNonneg : 0 ≤ Real.log (z : ℝ) / Real.log (y : ℝ) := by positivity
    calc
      ((A.card : ℝ) * (N : ℕ) / M) * ((1 + eta) * V) =
          ((A.card : ℝ) / M) * (N : ℝ) * ((1 + eta) * V) := by ring
      _ ≤ (1 / 2 : ℝ) ^ Q.card * (N : ℝ) * ((1 + eta) * V) := by
        gcongr
      _ ≤ (1 / 2 : ℝ) ^ Q.card * (N : ℝ) *
          ((1 + Cβ / 3) * (Cd * (Real.log (z : ℝ) / Real.log (y : ℝ)))) := by
        gcongr
      _ = ((1 + Cβ / 3) * Cd) * (1 / 2 : ℝ) ^ Q.card * (N : ℝ) *
          (Real.log (z : ℝ) / Real.log (y : ℝ)) := by ring
  have hendpoint :
      (2 * A.card : ℝ) * (y ^ S : ℕ) * E ≤
        (2 * Ci) * (A.card : ℝ) * (y ^ S : ℕ) *
          (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
    have hratioNonneg : 0 ≤ Real.log (y : ℝ) / Real.log (z : ℝ) := by positivity
    calc
      (2 * A.card : ℝ) * (y ^ S : ℕ) * E ≤
          (2 * A.card : ℝ) * (y ^ S : ℕ) *
            (Ci * (Real.log (y : ℝ) / Real.log (z : ℝ))) := by
        gcongr
      _ = (2 * Ci) * (A.card : ℝ) * (y ^ S : ℕ) *
          (Real.log (y : ℝ) / Real.log (z : ℝ)) := by ring
  have hsieve' :
      (((Erdos387.modularPreimageIoc m0 (m0 + N) M A).filter fun n ↦
          Nat.Coprime (Erdos387.sievePrimeProduct z (y + 1)) n).card : ℝ) ≤
        ((A.card : ℝ) * (N : ℕ) / M) * ((1 + eta) * V) +
          (2 * A.card : ℝ) * (y ^ S : ℕ) * E := by
    simpa [A, M, P, E, V, eta, Cβ] using hsieve
  exact hcard.trans (hsieve'.trans (add_le_add hmain hendpoint))

/-! ## Cumulative quadratic exceptional sets -/

/-- The odd auxiliary primes up to a numerical least-nonresidue cutoff. -/
noncomputable def quadraticAuxiliaryPrimes (t : ℕ) : Finset ℕ :=
  (Nat.primesLE t).erase 2

lemma quadraticAuxiliaryPrimes_prime {t q : ℕ}
    (hq : q ∈ quadraticAuxiliaryPrimes t) : q.Prime := by
  exact Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase hq)

lemma quadraticAuxiliaryPrimes_ne_two {t q : ℕ}
    (hq : q ∈ quadraticAuxiliaryPrimes t) : q ≠ 2 := by
  exact Finset.ne_of_mem_erase hq

lemma quadraticAuxiliaryPrimes_le {t q : ℕ}
    (hq : q ∈ quadraticAuxiliaryPrimes t) : q ≤ t := by
  exact Nat.le_of_mem_primesLE (Finset.mem_of_mem_erase hq)

lemma quadraticAuxiliaryPrimes_mono {s t : ℕ} (hst : s ≤ t) :
    quadraticAuxiliaryPrimes s ⊆ quadraticAuxiliaryPrimes t := by
  intro q hq
  rw [quadraticAuxiliaryPrimes, Finset.mem_erase] at hq ⊢
  exact ⟨hq.1, Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE hq.2).trans hst,
      (Nat.prime_of_mem_primesLE hq.2)⟩⟩

lemma quadraticResiduePrimePattern_mono_auxiliary
    {Q R : Finset ℕ} (hQR : Q ⊆ R)
    (candidateOneModFour : Bool) (m0 N : ℕ) :
    quadraticResiduePrimePattern R candidateOneModFour m0 N ⊆
      quadraticResiduePrimePattern Q candidateOneModFour m0 N := by
  classical
  intro p hp
  rw [quadraticResiduePrimePattern, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hp.2.2.1,
    fun q hq ↦ hp.2.2.2 q (hQR hq)⟩

lemma quadraticAuxiliaryPrimes_card {t : ℕ} (ht : 2 ≤ t) :
    (quadraticAuxiliaryPrimes t).card = Nat.primeCounting t - 1 := by
  rw [quadraticAuxiliaryPrimes, Finset.card_erase_of_mem]
  · rw [Nat.primesLE_card_eq_primeCounting]
  · exact Nat.mem_primesLE.mpr ⟨ht, Nat.prime_two⟩

private lemma eventually_sqrt_add_one_le_primeCounting :
    ∀ᶠ t : ℕ in atTop, Nat.sqrt t + 1 ≤ Nat.primeCounting t := by
  obtain ⟨e, he, hpi⟩ := pi_alt
  have herr := tendsto_natCast_atTop_atTop.eventually
    (he.bound (by norm_num : (0 : ℝ) < 1 / 2))
  have hlogSmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).bound
      (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [herr, hlogSmall, eventually_ge_atTop 16] with t he' hsmall ht
  have htR : (0 : ℝ) < t := by positivity
  have ht1 : (1 : ℝ) < t := by exact_mod_cast (show 1 < t by omega)
  have hlog : 0 < Real.log (t : ℝ) := Real.log_pos ht1
  have heLower : (1 / 2 : ℝ) ≤ 1 + e (t : ℝ) := by
    have habs : |e (t : ℝ)| ≤ (1 / 2 : ℝ) := by simpa using he'
    linarith [neg_le_abs (e (t : ℝ))]
  have hpiLower : (t : ℝ) / (2 * Real.log t) ≤
      (Nat.primeCounting t : ℝ) := by
    have hformula := hpi (t : ℝ)
    norm_num at hformula
    rw [hformula]
    rw [show (t : ℝ) / (2 * Real.log t) =
        ((1 / 2 : ℝ) * t) / Real.log t by ring]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right heLower
        (by exact_mod_cast (show 0 ≤ t by omega) : (0 : ℝ) ≤ t)) hlog.le
  have hsqrtNonneg : 0 ≤ Real.sqrt (t : ℝ) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (t : ℝ) ^ 2 = t := Real.sq_sqrt htR.le
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (t : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ t by omega))
  have hlogBound : Real.log (t : ℝ) ≤ Real.sqrt (t : ℝ) / 8 := by
    have habs : |Real.log (t : ℝ)| ≤
        (1 / 8 : ℝ) * |(t : ℝ) ^ (1 / 2 : ℝ)| := by
      simpa only [Real.norm_eq_abs] using hsmall
    rw [abs_of_pos hlog, ← Real.sqrt_eq_rpow, abs_of_nonneg hsqrtNonneg] at habs
    linarith
  have hsqrtMain : 2 * Real.sqrt (t : ℝ) ≤
      (t : ℝ) / (2 * Real.log t) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hlog)]
    nlinarith
  have hnatSqrt : ((Nat.sqrt t + 1 : ℕ) : ℝ) ≤
      2 * Real.sqrt (t : ℝ) := by
    push_cast
    have := Real.nat_sqrt_le_real_sqrt (a := t)
    linarith
  exact_mod_cast hnatSqrt.trans (hsqrtMain.trans hpiLower)

private lemma square_mod_of_lt_least_quadratic
    {p q : ℕ} (hp : Eligible 2 p)
    (hqprime : q.Prime) (hq : q < leastKthPowerNonresidue 2 p) :
    IsSquare (q : ZMod p) := by
  have hleastp : leastKthPowerNonresidue 2 p < p :=
    leastKthPowerNonresidue_lt (by norm_num) hp
  have hqp : q < p := hq.trans hleastp
  have hunit : IsUnit (q : ZMod p) :=
    (ZMod.isUnit_iff_coprime q p).mpr
      ((Nat.coprime_primes hqprime hp.1).mpr (Nat.ne_of_lt hqp))
  have hnot := not_kthPowerNonresidue_of_lt_least
    (k := 2) (p := p) (a := q) (by norm_num) hp hq
  have hex : ∃ b : ZMod p, b ^ 2 = (q : ZMod p) := by
    by_contra hn
    exact hnot ⟨hunit, hn⟩
  obtain ⟨b, hb⟩ := hex
  exact ⟨b, by simpa [pow_two] using hb.symm⟩

/-- After discarding the initial interval, every quadratic exceptional prime
lies in one of the two reciprocity patterns associated with the odd primes
up to `t`.  This is the cumulative (rather than exact-level) bridge needed
for layer-cake summation. -/
theorem exceptionalPrimes_two_subset_quadraticPatterns
    (t m0 x : ℕ) (hm0 : 2 ≤ m0) :
    exceptionalPrimes 2 t x ⊆
      Finset.range (m0 + 1) ∪
        (quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t)
          false m0 x ∪
        quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t)
          true m0 x) := by
  classical
  intro p hp
  have hmem := mem_exceptionalPrimes.mp hp
  by_cases hpm0 : p ≤ m0
  · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
  have helig : Eligible 2 p := eligible_of_mem_exceptionalPrimes
    (k := 2) (y := t) (x := x) (by norm_num) hp
  have hpOdd : Odd p := (Nat.Prime.odd_of_ne_two hmem.2.1 (by omega))
  have hpClass := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpOdd)
  have hpInterval : p ∈ Finset.Ioc m0 (m0 + x) := by
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hpResidues : ∀ q ∈ quadraticAuxiliaryPrimes t,
      q < p ∧ IsSquare (q : ZMod p) := by
    intro q hq
    have hqt : q ≤ t := quadraticAuxiliaryPrimes_le hq
    have hqleast : q < leastKthPowerNonresidue 2 p :=
      hqt.trans_lt hmem.2.2
    exact ⟨hqleast.trans (leastKthPowerNonresidue_lt (by norm_num) helig),
      square_mod_of_lt_least_quadratic helig
        (quadraticAuxiliaryPrimes_prime hq) hqleast⟩
  rcases hpClass with hp1 | hp3
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    rw [quadraticResiduePrimePattern, Finset.mem_filter]
    exact ⟨hpInterval, hmem.2.1, by simpa using hp1, hpResidues⟩
  · apply Finset.mem_union_right
    apply Finset.mem_union_left
    rw [quadraticResiduePrimePattern, Finset.mem_filter]
    exact ⟨hpInterval, hmem.2.1, by simpa using hp3, hpResidues⟩

theorem exceptionalPrimes_two_card_le_quadraticPatterns
    (t m0 x : ℕ) (hm0 : 2 ≤ m0) :
    ((exceptionalPrimes 2 t x).card : ℝ) ≤
      (m0 + 1 : ℕ) +
        ((quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t)
          false m0 x).card : ℝ) +
        ((quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t)
          true m0 x).card : ℝ) := by
  have hcard := Finset.card_le_card
    (exceptionalPrimes_two_subset_quadraticPatterns t m0 x hm0)
  have houter := Finset.card_union_le (Finset.range (m0 + 1))
    (quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t) false m0 x ∪
      quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t) true m0 x)
  have hinner := Finset.card_union_le
    (quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t) false m0 x)
    (quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t) true m0 x)
  have hnat := hcard.trans (houter.trans (Nat.add_le_add_left hinner _))
  have hnat' : (exceptionalPrimes 2 t x).card ≤
      (m0 + 1) +
        (quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t)
          false m0 x).card +
        (quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t)
          true m0 x).card := by
    simpa [Finset.card_range, add_assoc] using hnat
  exact_mod_cast hnat'

/-- An order-free powerset form of the quadratic tensor sieve.  It is more
convenient for moving cutoffs than the trimmed formulation: every local
removal ratio is at least `1/2`, so the elementary-symmetric denominator is
at least `choose |Q| k * 2⁻ᵏ`. -/
theorem quadraticResiduePrimePattern_card_le_choose
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hodd : ∀ q ∈ Q, q ≠ 2) (candidateOneModFour : Bool)
    (k m0 N : ℕ) (hk : k ≤ Q.card)
    (hproduct : ∀ T U : Erdos380.fixedCardSubsets Q k,
      (∏ q ∈ T.1, q.1) * (∏ q ∈ U.1, q.1) ≤ N) :
    ((quadraticResiduePrimePattern Q candidateOneModFour m0 N).card : ℝ) ≤
      ((N : ℝ) + N) /
        ((Q.card.choose k : ℕ) * (1 / 2 : ℝ) ^ k) := by
  classical
  letI : ∀ q : Q, Fact q.1.Prime := fun q ↦ ⟨hprime q.1 q.2⟩
  letI : ∀ q : Q, NeZero q.1 := fun q ↦ ⟨(hprime q.1 q.2).ne_zero⟩
  let vanish := fun q : Q ↦
    quadraticVanishing q.1
      (reciprocityWantsSquare candidateOneModFour q.1)
  have hsubsets : Nonempty (Erdos380.fixedCardSubsets Q k) := by
    obtain ⟨T, _hTuniv, hTcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset Q))
        (by simpa using hk)
    exact ⟨⟨T, hTcard⟩⟩
  have hcoprime : Pairwise (fun q r : Q ↦ Nat.Coprime q.1 r.1) := by
    intro q r hqr
    exact (Nat.coprime_primes (hprime q.1 q.2) (hprime r.1 r.2)).mpr
      (Subtype.coe_ne_coe.mpr hqr)
  have hsubset := quadraticResiduePrimePattern_subset_survivors
    Q hprime hodd candidateOneModFour m0 N
  have hcore := Erdos380.residueClassSurvivors_card_le_powerset_ratio
    (fun q : Q ↦ q.1) hcoprime vanish k m0 N hsubsets hproduct
    (fun q ↦ quadraticVanishing_nonempty q.1 _)
    (fun q ↦ card_quadraticVanishing_lt q.1 (hodd q.1 q.2) _)
  let D : ℝ := ∑ T : Erdos380.fixedCardSubsets Q k,
    ∏ q ∈ T.1, Erdos380.residueRemovalRatio (fun q : Q ↦ q.1) vanish q
  let d : ℝ := (Q.card.choose k : ℕ) * (1 / 2 : ℝ) ^ k
  have hhalf (q : Q) : (1 / 2 : ℝ) ≤
      Erdos380.residueRemovalRatio (fun q : Q ↦ q.1) vanish q := by
    have hcard := half_le_quadraticVanishing_fraction q.1
      (hodd q.1 q.2) (reciprocityWantsSquare candidateOneModFour q.1)
    unfold Erdos380.residueRemovalRatio
    have hproper := card_quadraticVanishing_lt q.1 (hodd q.1 q.2)
      (reciprocityWantsSquare candidateOneModFour q.1)
    have hdenNat : 0 < q.1 - (vanish q).card := by
      dsimp [vanish]
      omega
    have hdenR : (0 : ℝ) < ((q.1 - (vanish q).card : ℕ) : ℝ) := by
      exact_mod_cast hdenNat
    rw [le_div_iff₀ hdenR]
    have hqR : (0 : ℝ) < q.1 := by
      exact_mod_cast (hprime q.1 q.2).pos
    have hhalfq : (q.1 : ℝ) / 2 ≤ (vanish q).card := by
      dsimp [vanish]
      have hm := (le_div_iff₀ hqR).mp hcard
      nlinarith
    rw [Nat.cast_sub (by dsimp [vanish]; omega)]
    push_cast
    nlinarith
  have hterm (T : Erdos380.fixedCardSubsets Q k) :
      (1 / 2 : ℝ) ^ k ≤
        ∏ q ∈ T.1,
          Erdos380.residueRemovalRatio (fun q : Q ↦ q.1) vanish q := by
    calc
      (1 / 2 : ℝ) ^ k = ∏ _q ∈ T.1, (1 / 2 : ℝ) := by simp [T.2]
      _ ≤ ∏ q ∈ T.1,
          Erdos380.residueRemovalRatio (fun q : Q ↦ q.1) vanish q :=
        Finset.prod_le_prod (fun _ _ ↦ by norm_num)
          (fun q _ ↦ hhalf q)
  have hD : d ≤ D := by
    calc
      d = ∑ _T : Erdos380.fixedCardSubsets Q k, (1 / 2 : ℝ) ^ k := by
        dsimp [d]
        simp [Fintype.card_finset_len, Fintype.card_coe,
          nsmul_eq_mul]
      _ ≤ D := by
        dsimp [D]
        exact Finset.sum_le_sum fun T _ ↦ hterm T
  have hdpos : 0 < d := by
    dsimp [d]
    exact mul_pos (by exact_mod_cast Nat.choose_pos hk) (by positivity)
  have hcard :
      ((quadraticResiduePrimePattern Q candidateOneModFour m0 N).card : ℝ) ≤
        ((Erdos380.residueClassSurvivors
          (modulus := fun q : Q ↦ q.1) vanish m0 N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  calc
    ((quadraticResiduePrimePattern Q candidateOneModFour m0 N).card : ℝ) ≤
        ((Erdos380.residueClassSurvivors
          (modulus := fun q : Q ↦ q.1) vanish m0 N).card : ℝ) := hcard
    _ ≤ ((N : ℝ) + N) / D := by simpa [D] using hcore
    _ ≤ ((N : ℝ) + N) / d := by
      exact div_le_div_of_nonneg_left (by positivity) hdpos hD
    _ = ((N : ℝ) + N) /
        ((Q.card.choose k : ℕ) * (1 / 2 : ℝ) ^ k) := rfl

/-- A coarse exponential corollary suited to a moving tensor depth. -/
theorem quadraticResiduePrimePattern_card_le_three_pow
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hodd : ∀ q ∈ Q, q ≠ 2) (candidateOneModFour : Bool)
    (k m0 N : ℕ) (hk : 0 < k) (h8 : 8 * k ≤ Q.card)
    (hproduct : ∀ T U : Erdos380.fixedCardSubsets Q k,
      (∏ q ∈ T.1, q.1) * (∏ q ∈ U.1, q.1) ≤ N) :
    ((quadraticResiduePrimePattern Q candidateOneModFour m0 N).card : ℝ) ≤
      ((N : ℝ) + N) / (3 : ℝ) ^ k := by
  have hkQ : k ≤ Q.card := by omega
  have hraw := quadraticResiduePrimePattern_card_le_choose
    Q hprime hodd candidateOneModFour k m0 N hkQ hproduct
  have hbaseNat : 7 * k ≤ Q.card + 1 - k := by omega
  have hfacNat : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
  have hchoose7 : (7 : ℝ) ^ k ≤ (Q.card.choose k : ℕ) := by
    calc
      (7 : ℝ) ^ k ≤
          ((Q.card + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < k.factorial)]
        calc
          (7 : ℝ) ^ k * (k.factorial : ℝ) ≤
              (7 : ℝ) ^ k * (k : ℝ) ^ k := by gcongr; exact_mod_cast hfacNat
          _ = ((7 * k : ℕ) : ℝ) ^ k := by
            push_cast
            rw [mul_pow]
          _ ≤ ((Q.card + 1 - k : ℕ) : ℝ) ^ k := by
            gcongr
      _ ≤ (Q.card.choose k : ℕ) := Nat.pow_le_choose k Q.card
  have hden : (3 : ℝ) ^ k ≤
      (Q.card.choose k : ℕ) * (1 / 2 : ℝ) ^ k := by
    calc
      (3 : ℝ) ^ k ≤ (7 / 2 : ℝ) ^ k := by gcongr <;> norm_num
      _ = (7 : ℝ) ^ k * (1 / 2 : ℝ) ^ k := by
        rw [show (7 / 2 : ℝ) = 7 * (1 / 2 : ℝ) by ring, mul_pow]
      _ ≤ (Q.card.choose k : ℕ) * (1 / 2 : ℝ) ^ k := by gcongr
  exact hraw.trans (div_le_div_of_nonneg_left (by positivity)
    (pow_pos (by norm_num) k) hden)

/-- The first `J` odd rational primes, used as the common high-cutoff tensor. -/
noncomputable def firstOddRationalPrimes (J : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (J + 1)).image rationalPrime

lemma firstOddRationalPrimes_card (J : ℕ) :
    (firstOddRationalPrimes J).card = J := by
  rw [firstOddRationalPrimes, Finset.card_image_iff.mpr]
  · simp
  · exact rationalPrime_strictMono.injective.injOn

lemma firstOddRationalPrimes_prime {J q : ℕ}
    (hq : q ∈ firstOddRationalPrimes J) : q.Prime := by
  rw [firstOddRationalPrimes, Finset.mem_image] at hq
  obtain ⟨i, _hi, rfl⟩ := hq
  exact rationalPrime_prime i

lemma firstOddRationalPrimes_ne_two {J q : ℕ}
    (hq : q ∈ firstOddRationalPrimes J) : q ≠ 2 := by
  rw [firstOddRationalPrimes, Finset.mem_image] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  have hthree : 3 ≤ rationalPrime i := by
    calc
      3 = rationalPrime 1 := by
        simpa [rationalPrime] using Nat.nth_prime_one_eq_three.symm
      _ ≤ rationalPrime i := rationalPrime_strictMono.monotone hi1
  omega

lemma firstOddRationalPrimes_le_last {J q : ℕ}
    (hq : q ∈ firstOddRationalPrimes J) : q ≤ rationalPrime J := by
  rw [firstOddRationalPrimes, Finset.mem_image] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  exact rationalPrime_strictMono.monotone (by
    have := (Finset.mem_Ico.mp hi).2
    omega)

/-! ## Moving quadratic split

The Rosser estimate is used below the sixth power of an eighth-root
logarithmic scale.  Above that split a fixed tensor of the auxiliary primes
already gives a super-polynomial logarithmic saving.  Writing the split in
terms of one integral scale makes all product constraints purely algebraic.
-/

private noncomputable def quadraticScale (x : ℕ) : ℕ :=
  ⌊(Real.log (x : ℝ)) ^ (1 / 8 : ℝ)⌋₊

private noncomputable def quadraticSplit (x : ℕ) : ℕ :=
  quadraticScale x ^ 6

private noncomputable def quadraticTensorDepth (x : ℕ) : ℕ :=
  quadraticScale x ^ 3 / 8

private lemma quadraticAuxiliaryPrimes_card_le (t : ℕ) :
    (quadraticAuxiliaryPrimes t).card ≤ t := by
  classical
  calc
    (quadraticAuxiliaryPrimes t).card ≤ (Finset.Icc 1 t).card := by
      apply Finset.card_le_card
      intro q hq
      rw [Finset.mem_Icc]
      exact ⟨(Nat.Prime.one_le (quadraticAuxiliaryPrimes_prime hq)),
        quadraticAuxiliaryPrimes_le hq⟩
    _ = t := by simp

private lemma quadraticBaseResidues_card_le_modulus
    (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hodd : ∀ q ∈ Q, q ≠ 2) (wantSquare : Q → Bool) :
    (quadraticBaseResidues Q hprime wantSquare).card ≤
      quadraticBaseModulus Q := by
  classical
  rw [card_quadraticBaseResidues Q hprime hodd wantSquare,
    quadraticBaseModulus]
  exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
    (fun q _ ↦ by omega)

private lemma quadraticBaseResidues_aux_card_le_split_pow
    {t T : ℕ} (ht : t ≤ T) (hT : 1 ≤ T) (candidateOneModFour : Bool) :
    (quadraticBaseResidues (quadraticAuxiliaryPrimes t)
      (fun _q hq ↦ quadraticAuxiliaryPrimes_prime hq)
      (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1)).card ≤ T ^ T := by
  classical
  let Q := quadraticAuxiliaryPrimes t
  let hprime : ∀ q ∈ Q, q.Prime := fun _q hq ↦
    quadraticAuxiliaryPrimes_prime hq
  let hodd : ∀ q ∈ Q, q ≠ 2 := fun _q hq ↦
    quadraticAuxiliaryPrimes_ne_two hq
  calc
    (quadraticBaseResidues Q hprime
        (fun q ↦ reciprocityWantsSquare candidateOneModFour q.1)).card ≤
        quadraticBaseModulus Q :=
      quadraticBaseResidues_card_le_modulus Q hprime hodd _
    _ = ∏ q ∈ Q, q := rfl
    _ ≤ T ^ Q.card := by
      exact Finset.prod_le_pow_card Q id T fun q hq ↦
        (quadraticAuxiliaryPrimes_le hq).trans ht
    _ ≤ T ^ T := Nat.pow_le_pow_right hT
      ((quadraticAuxiliaryPrimes_card_le t).trans ht)

private lemma eventually_quadraticScale_bounds :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ quadraticScale x ∧
      ((quadraticScale x : ℕ) : ℝ) ≤
        (Real.log (x : ℝ)) ^ (1 / 8 : ℝ) ∧
      (Real.log (x : ℝ)) ^ (1 / 8 : ℝ) / 2 ≤
        (quadraticScale x : ℝ) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowTop : Tendsto
      (fun u : ℝ ↦ u ^ (1 / 8 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hlarge := hlogTop.eventually
    (hpowTop.eventually (eventually_ge_atTop (4 : ℝ)))
  filter_upwards [hlarge, eventually_ge_atTop 3] with x hpow hx
  let u : ℝ := Real.log (x : ℝ)
  let L : ℕ := quadraticScale x
  have hu : 0 ≤ u := by
    dsimp [u]
    exact (Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega)))
  have hupow : 0 ≤ u ^ (1 / 8 : ℝ) := Real.rpow_nonneg hu _
  have hLle : (L : ℝ) ≤ u ^ (1 / 8 : ℝ) := by
    dsimp [L, quadraticScale]
    exact Nat.floor_le hupow
  have hLlt : u ^ (1 / 8 : ℝ) < (L : ℝ) + 1 := by
    simpa [L, quadraticScale, u] using
      Nat.lt_floor_add_one (u ^ (1 / 8 : ℝ))
  have hLlower : u ^ (1 / 8 : ℝ) / 2 ≤ (L : ℝ) := by linarith
  have hL2 : 2 ≤ L := by
    have : (2 : ℝ) < L := by linarith
    have hnat : 2 < L := by exact_mod_cast this
    omega
  exact ⟨hL2, by simpa [L, u] using hLle, by simpa [L, u] using hLlower⟩

/-- The complete CRT base at the moving split is a tiny fixed power of the
ambient interval.  The integral six/eight choice avoids any rounding loss
in the subsequent product estimates. -/
private lemma eventually_quadraticSplit_selfPow_sixteen_le :
    ∀ᶠ x : ℕ in atTop,
      (quadraticSplit x ^ quadraticSplit x) ^ 16 ≤ x := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 4)).bound
        (by norm_num : (0 : ℝ) < 1 / 16)
  have hsmall := hlogTop.eventually hsmallReal
  filter_upwards [hsmall, eventually_quadraticScale_bounds,
      eventually_ge_atTop 16] with x hsmall hxscale hx
  let u : ℝ := Real.log (x : ℝ)
  let L : ℕ := quadraticScale x
  let T : ℕ := quadraticSplit x
  have hxR : (0 : ℝ) < x := by positivity
  have hu1 : (1 : ℝ) < u := by
    dsimp [u]
    rw [Real.lt_log_iff_exp_lt hxR]
    calc
      Real.exp 1 < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
      _ ≤ (x : ℝ) := by exact_mod_cast (show 3 ≤ x by omega)
  have hu0 : 0 ≤ u := (zero_lt_one.trans hu1).le
  have hlogu : 0 < Real.log u := Real.log_pos hu1
  have hsmall' : Real.log u ≤ (1 / 16 : ℝ) * u ^ (1 / 4 : ℝ) := by
    have := hsmall
    simpa only [u, Real.norm_eq_abs, Real.rpow_one, abs_of_pos hlogu,
      abs_of_nonneg (Real.rpow_nonneg hu0 _)] using this
  have hLle : (L : ℝ) ≤ u ^ (1 / 8 : ℝ) := by
    simpa [L, u] using hxscale.2.1
  have hTpos : (0 : ℝ) < T := by
    have hLpos : 0 < L := by omega
    have hTnat : 0 < T := by
      dsimp [T, quadraticSplit, L]
      positivity
    exact_mod_cast hTnat
  have hTle : (T : ℝ) ≤ u ^ (3 / 4 : ℝ) := by
    dsimp [T, quadraticSplit]
    push_cast
    calc
      (L : ℝ) ^ 6 ≤ (u ^ (1 / 8 : ℝ)) ^ 6 := by gcongr
      _ = u ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0]
        norm_num
  have hTleu : (T : ℝ) ≤ u := by
    calc
      (T : ℝ) ≤ u ^ (3 / 4 : ℝ) := hTle
      _ ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1.le (by norm_num)
      _ = u := Real.rpow_one u
  have hlogT : Real.log (T : ℝ) ≤ Real.log u :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact hTpos)
      (by simp only [Set.mem_Ioi]; positivity)
      hTleu
  have hexponent : 16 * (T : ℝ) * Real.log (T : ℝ) ≤ u := by
    calc
      16 * (T : ℝ) * Real.log (T : ℝ) ≤
          16 * u ^ (3 / 4 : ℝ) * Real.log u := by gcongr
      _ ≤ 16 * u ^ (3 / 4 : ℝ) *
          ((1 / 16 : ℝ) * u ^ (1 / 4 : ℝ)) := by gcongr
      _ = u := by
        rw [show 16 * u ^ (3 / 4 : ℝ) *
            ((1 / 16 : ℝ) * u ^ (1 / 4 : ℝ)) =
            u ^ (3 / 4 : ℝ) * u ^ (1 / 4 : ℝ) by ring,
          ← Real.rpow_add (zero_lt_one.trans hu1)]
        norm_num
  have hcast : ((((T ^ T) ^ 16 : ℕ) : ℝ)) ≤ (x : ℝ) := by
    calc
      ((((T ^ T) ^ 16 : ℕ) : ℝ)) =
          Real.exp (16 * (T : ℝ) * Real.log (T : ℝ)) := by
        push_cast
        rw [← pow_mul, ← Real.rpow_natCast,
          Real.rpow_def_of_pos hTpos]
        congr 1
        push_cast
        ring
      _ ≤ Real.exp u := Real.exp_le_exp.mpr hexponent
      _ = (x : ℝ) := by simp [u, Real.exp_log hxR]
  exact_mod_cast hcast

private noncomputable def quadraticGeometricWeight (t : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (quadraticAuxiliaryPrimes t).card *
    Real.log (max 3 t : ℝ) * (t + 1 : ℕ) ^ 2

private lemma quadraticGeometricWeight_nonneg (t : ℕ) :
    0 ≤ quadraticGeometricWeight t := by
  unfold quadraticGeometricWeight
  have : (1 : ℝ) ≤ max (3 : ℝ) (t : ℝ) := by
    exact (by norm_num : (1 : ℝ) ≤ 3).trans (le_max_left _ _)
  have hlog : 0 ≤ Real.log (max 3 t : ℝ) := Real.log_nonneg this
  positivity

/-- The geometric main term, including the two powers required by the
cumulative layer-cake majorant, is bounded uniformly in the cutoff. -/
private theorem exists_quadraticGeometricWeight_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℕ, quadraticGeometricWeight t ≤ B := by
  let G : ℕ → ℝ := fun n ↦
    3 * ((n + 1 : ℕ) : ℝ) ^ 6 * (1 / 2 : ℝ) ^ n
  have hbase : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 6 * (1 / 2 : ℝ) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 6 (by norm_num) (by norm_num)
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hG : Tendsto G atTop (nhds 0) := by
    have h := hshift.const_mul 6
    simp only [mul_zero] at h
    convert h using 1
    ext n
    dsimp [G]
    rw [pow_succ]
    push_cast
    ring
  have hGone : ∀ᶠ n : ℕ in atTop, G n ≤ 1 := by
    filter_upwards [(tendsto_order.1 hG).2 1 (by norm_num)] with n hn
    exact hn.le
  have hsqrtTop : Tendsto Nat.sqrt atTop atTop := by
    rw [tendsto_atTop]
    intro n
    filter_upwards [eventually_ge_atTop (n ^ 2)] with t ht
    exact Nat.le_sqrt'.2 ht
  have hweightEventually : ∀ᶠ t : ℕ in atTop,
      quadraticGeometricWeight t ≤ 1 := by
    filter_upwards [eventually_sqrt_add_one_le_primeCounting,
      hsqrtTop.eventually hGone, eventually_ge_atTop 2] with t hpi hGsqrt ht
    have hcard : Nat.sqrt t ≤ (quadraticAuxiliaryPrimes t).card := by
      rw [quadraticAuxiliaryPrimes_card ht]
      omega
    have hhalf : (1 / 2 : ℝ) ^ (quadraticAuxiliaryPrimes t).card ≤
        (1 / 2 : ℝ) ^ Nat.sqrt t :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
    have hmax : max (3 : ℝ) (t : ℝ) ≤ 3 * (t + 1 : ℕ) := by
      apply max_le
      · push_cast
        nlinarith
      · push_cast
        linarith
    have hlog : Real.log (max 3 t : ℝ) ≤ 3 * (t + 1 : ℕ) :=
      (Real.log_le_self (by positivity)).trans hmax
    have hlognonneg : 0 ≤ Real.log (max 3 t : ℝ) :=
      Real.log_nonneg (by norm_num [le_max_left (3 : ℝ) t])
    have hsqrt : t + 1 ≤ (Nat.sqrt t + 1) ^ 2 :=
      Nat.succ_le_of_lt (Nat.lt_succ_sqrt' t)
    have hcubic : (((t + 1 : ℕ) : ℝ) ^ 3) ≤
        (((Nat.sqrt t + 1 : ℕ) : ℝ) ^ 6) := by
      have hpow : (t + 1) ^ 3 ≤ ((Nat.sqrt t + 1) ^ 2) ^ 3 :=
        Nat.pow_le_pow_left hsqrt 3
      exact_mod_cast (hpow.trans_eq (by ring))
    calc
      quadraticGeometricWeight t ≤
          (1 / 2 : ℝ) ^ Nat.sqrt t *
            (3 * (t + 1 : ℕ)) * (t + 1 : ℕ) ^ 2 := by
        unfold quadraticGeometricWeight
        gcongr
      _ = 3 * (1 / 2 : ℝ) ^ Nat.sqrt t *
          (((t + 1 : ℕ) : ℝ) ^ 3) := by
        push_cast
        ring
      _ ≤ 3 * (1 / 2 : ℝ) ^ Nat.sqrt t *
          (((Nat.sqrt t + 1 : ℕ) : ℝ) ^ 6) := by gcongr
      _ = G (Nat.sqrt t) := by simp [G]; ring
      _ ≤ 1 := hGsqrt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hweightEventually
  let B : ℝ := 1 + ∑ t ∈ Finset.range N, quadraticGeometricWeight t
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    have hsum : 0 ≤ ∑ t ∈ Finset.range N, quadraticGeometricWeight t :=
      Finset.sum_nonneg fun t _ ↦ quadraticGeometricWeight_nonneg t
    linarith
  intro t
  by_cases ht : t < N
  · have hterm : quadraticGeometricWeight t ≤
        ∑ s ∈ Finset.range N, quadraticGeometricWeight s := by
      exact Finset.single_le_sum
        (fun s _ ↦ quadraticGeometricWeight_nonneg s)
        (Finset.mem_range.mpr ht)
    dsimp [B]
    linarith
  · have hone := hN t (by omega)
    have hsum : 0 ≤ ∑ s ∈ Finset.range N, quadraticGeometricWeight s :=
      Finset.sum_nonneg fun s _ ↦ quadraticGeometricWeight_nonneg s
    dsimp [B]
    linarith

private lemma tendsto_quadraticScale_atTop :
    Tendsto quadraticScale atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

private lemma tendsto_quadraticSplit_atTop :
    Tendsto quadraticSplit atTop atTop := by
  exact (tendsto_pow_atTop (by norm_num : 6 ≠ 0)).comp
    tendsto_quadraticScale_atTop

/-- All moving tensor constraints, including the logarithmic saving required
at the top of the medium range, hold simultaneously. -/
private lemma eventually_quadratic_high_parameters :
    ∀ᶠ x : ℕ in atTop,
      0 < quadraticTensorDepth x ∧
      8 * quadraticTensorDepth x ≤
        (quadraticAuxiliaryPrimes (quadraticSplit x)).card ∧
      (∀ T U : Erdos380.fixedCardSubsets
          (quadraticAuxiliaryPrimes (quadraticSplit x))
          (quadraticTensorDepth x),
        (∏ q ∈ T.1, q.1) * (∏ q ∈ U.1, q.1) ≤ x) ∧
      8 * Real.log (x : ℝ) *
          ((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2 ≤
        (3 : ℝ) ^ quadraticTensorDepth x ∧
      6 * Real.log (x : ℝ) *
          ((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2 ≤ (x : ℝ) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hsmallTensorReal :=
    (isLittleO_log_rpow_atTop (r := (3 / 8 : ℝ)) (by norm_num)).bound
      (show 0 < Real.log (3 : ℝ) / (128 * 70) by positivity)
  have hsmallTensor := hlogTop.eventually hsmallTensorReal
  have hsmallExpReal :=
    (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).bound
      (by norm_num : (0 : ℝ) < 1 / 70)
  have hsmallExp := hlogTop.eventually hsmallExpReal
  have hpiSplit := tendsto_quadraticSplit_atTop.eventually
    eventually_sqrt_add_one_le_primeCounting
  have hscale16 := tendsto_quadraticScale_atTop.eventually
    (eventually_ge_atTop 16)
  have hu3Event := hlogTop.eventually (eventually_ge_atTop (3 : ℝ))
  have hpow128 := hlogTop.eventually
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 8)).eventually
      (eventually_ge_atTop (128 : ℝ)))
  filter_upwards [eventually_quadraticScale_bounds,
      eventually_quadraticSplit_selfPow_sixteen_le,
      hsmallTensor, hsmallExp, hpiSplit, hscale16, hu3Event, hpow128,
      eventually_ge_atTop 16] with
      x hxscale hsplitPower hsmallTensor hsmallExp hpi hscale16 hu3 hpowLarge hx
  let u : ℝ := Real.log (x : ℝ)
  let L : ℕ := quadraticScale x
  let T₀ : ℕ := quadraticSplit x
  let K : ℕ := quadraticTensorDepth x
  let Y : ℕ := smoothParameterY x
  have hxR : (0 : ℝ) < x := by positivity
  have hu1 : (1 : ℝ) < u := by
    dsimp [u]
    rw [Real.lt_log_iff_exp_lt hxR]
    calc
      Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ ≤ 3 := by norm_num
      _ ≤ (x : ℝ) := by exact_mod_cast (show 3 ≤ x by omega)
  have hu0 : 0 ≤ u := (zero_lt_one.trans hu1).le
  have hlogu : 0 < Real.log u := Real.log_pos hu1
  have hL2 : 2 ≤ L := by simpa [L] using hxscale.1
  have hLupper : (L : ℝ) ≤ u ^ (1 / 8 : ℝ) := by
    simpa [L, u] using hxscale.2.1
  have hLlower : u ^ (1 / 8 : ℝ) / 2 ≤ (L : ℝ) := by
    simpa [L, u] using hxscale.2.2
  have hKpos : 0 < K := by
    have hL : 2 ≤ L := hL2
    have hcube : 8 ≤ L ^ 3 := by
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ L ^ 3 := Nat.pow_le_pow_left hL 3
    change 0 < L ^ 3 / 8
    omega
  have hsqrtT₀ : Nat.sqrt T₀ = L ^ 3 := by
    dsimp [T₀, quadraticSplit]
    rw [show L ^ 6 = (L ^ 3) * (L ^ 3) by ring]
    exact Nat.sqrt_eq _
  have hT₀2 : 2 ≤ T₀ := by
    have hL : 2 ≤ L := hL2
    change 2 ≤ L ^ 6
    calc
      2 ≤ 2 ^ 6 := by norm_num
      _ ≤ L ^ 6 := Nat.pow_le_pow_left hL 6
  have hcard : 8 * K ≤ (quadraticAuxiliaryPrimes T₀).card := by
    have hcount : Nat.sqrt T₀ ≤ (quadraticAuxiliaryPrimes T₀).card := by
      rw [quadraticAuxiliaryPrimes_card hT₀2]
      have hpi' : Nat.sqrt T₀ + 1 ≤ Nat.primeCounting T₀ := by
        simpa [T₀] using hpi
      omega
    dsimp [K, quadraticTensorDepth]
    rw [hsqrtT₀] at hcount
    exact (Nat.mul_div_le (L ^ 3) 8).trans hcount
  have hproduct : ∀ V W : Erdos380.fixedCardSubsets
      (quadraticAuxiliaryPrimes T₀) K,
      (∏ q ∈ V.1, q.1) * (∏ q ∈ W.1, q.1) ≤ x := by
    intro V W
    have hV : ∏ q ∈ V.1, q.1 ≤ T₀ ^ K := by
      calc
        ∏ q ∈ V.1, q.1 ≤ ∏ _q ∈ V.1, T₀ := by
          exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
            (fun q hq ↦ quadraticAuxiliaryPrimes_le q.2)
        _ = T₀ ^ K := by simp [V.2]
    have hW : ∏ q ∈ W.1, q.1 ≤ T₀ ^ K := by
      calc
        ∏ q ∈ W.1, q.1 ≤ ∏ _q ∈ W.1, T₀ := by
          exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
            (fun q hq ↦ quadraticAuxiliaryPrimes_le q.2)
        _ = T₀ ^ K := by simp [W.2]
    have hKle : 2 * K ≤ 16 * T₀ := by
      have hKT : K ≤ T₀ := by
        have hdiv : L ^ 3 / 8 ≤ L ^ 3 := Nat.div_le_self _ _
        have hpow : L ^ 3 ≤ L ^ 6 :=
          Nat.pow_le_pow_right (by omega) (by omega)
        simpa [K, T₀, quadraticTensorDepth, quadraticSplit, L] using hdiv.trans hpow
      omega
    calc
      (∏ q ∈ V.1, q.1) * (∏ q ∈ W.1, q.1) ≤
          (T₀ ^ K) * (T₀ ^ K) := Nat.mul_le_mul hV hW
      _ = T₀ ^ (2 * K) := by rw [← pow_add]; congr 1 <;> omega
      _ ≤ T₀ ^ (16 * T₀) :=
        Nat.pow_le_pow_right (by positivity) hKle
      _ = (T₀ ^ T₀) ^ 16 := by ring
      _ ≤ x := by simpa [T₀] using hsplitPower
  have hLcube : u ^ (3 / 8 : ℝ) / 8 ≤ (L : ℝ) ^ 3 := by
    calc
      u ^ (3 / 8 : ℝ) / 8 =
          (u ^ (1 / 8 : ℝ) / 2) ^ 3 := by
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hu0]
        norm_num
      _ ≤ (L : ℝ) ^ 3 := by gcongr
  have hKrem : L ^ 3 ≤ 8 * K + 7 := by
    change L ^ 3 ≤ 8 * (L ^ 3 / 8) + 7
    omega
  have hpowLarge' : (128 : ℝ) ≤ u ^ (3 / 8 : ℝ) := by
    simpa [u] using hpowLarge
  have hKlower : u ^ (3 / 8 : ℝ) / 128 ≤ (K : ℝ) := by
    have hKremR : (L : ℝ) ^ 3 ≤ 8 * (K : ℝ) + 7 := by
      exact_mod_cast hKrem
    nlinarith
  have hsmallTensor' : Real.log u ≤
      (Real.log (3 : ℝ) / (128 * 70)) * u ^ (3 / 8 : ℝ) := by
    simpa only [u, Real.norm_eq_abs, abs_of_pos hlogu,
      abs_of_nonneg (Real.rpow_nonneg hu0 _)] using hsmallTensor
  have hsmallExp' : Real.log u ≤ (1 / 70 : ℝ) * u := by
    simpa only [u, Real.norm_eq_abs, Real.rpow_one, abs_of_pos hlogu,
      abs_of_pos (zero_lt_one.trans hu1)] using hsmallExp
  have hlog32 : Real.log (32 : ℝ) ≤ 5 * Real.log u := by
    have h32 : (32 : ℝ) ≤ u ^ 5 := by
      have : (2 : ℝ) ≤ u := by linarith [hu3]
      calc
        (32 : ℝ) = (2 : ℝ) ^ 5 := by norm_num
        _ ≤ u ^ 5 := by gcongr
    calc
      Real.log (32 : ℝ) ≤ Real.log (u ^ 5) :=
        Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; norm_num)
          (by simp only [Set.mem_Ioi]; positivity) h32
      _ = 5 * Real.log u := by rw [Real.log_pow]; norm_num
  have hexpTensor : Real.log (32 : ℝ) + 65 * Real.log u ≤
      (K : ℝ) * Real.log (3 : ℝ) := by
    have h70 : 70 * Real.log u ≤
        (Real.log (3 : ℝ) / 128) * u ^ (3 / 8 : ℝ) := by
      calc
        70 * Real.log u ≤ 70 *
            ((Real.log (3 : ℝ) / (128 * 70)) *
              u ^ (3 / 8 : ℝ)) := by gcongr
        _ = (Real.log (3 : ℝ) / 128) * u ^ (3 / 8 : ℝ) := by ring
    have hKmul := mul_le_mul_of_nonneg_right hKlower hlog3.le
    nlinarith
  have hYle : (Y : ℝ) ≤ u ^ (32 : ℕ) := by
    dsimp [Y, smoothParameterY, logarithmicCutoff]
    have hfloor := Nat.floor_le (Real.rpow_nonneg hu0 (32 : ℝ))
    simpa [u, Real.rpow_natCast] using hfloor
  have hYsucc : ((Y + 1 : ℕ) : ℝ) ≤ 2 * u ^ (32 : ℕ) := by
    push_cast
    have huPow : (1 : ℝ) ≤ u ^ (32 : ℕ) := one_le_pow₀ hu1.le
    linarith
  have htensorRaw : 32 * u ^ (65 : ℕ) ≤ (3 : ℝ) ^ K := by
    calc
      32 * u ^ (65 : ℕ) =
          Real.exp (Real.log (32 : ℝ) + 65 * Real.log u) := by
        rw [show Real.log (32 : ℝ) + 65 * Real.log u =
            Real.log (32 * u ^ (65 : ℕ)) by
          rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) (by positivity),
            Real.log_pow]
          ring]
        rw [Real.exp_log]
        positivity
      _ ≤ Real.exp ((K : ℝ) * Real.log (3 : ℝ)) :=
        Real.exp_le_exp.mpr hexpTensor
      _ = (3 : ℝ) ^ K := by
        rw [show (K : ℝ) * Real.log (3 : ℝ) =
            Real.log ((3 : ℝ) ^ K) by rw [Real.log_pow],
          Real.exp_log (by positivity)]
  have htensor : 8 * Real.log (x : ℝ) *
      (((Y + 1 : ℕ) : ℝ) ^ 2) ≤ (3 : ℝ) ^ K := by
    calc
      8 * Real.log (x : ℝ) * (((Y + 1 : ℕ) : ℝ) ^ 2) ≤
          8 * u * (2 * u ^ (32 : ℕ)) ^ 2 := by
        dsimp [u]
        gcongr
      _ = 32 * u ^ (65 : ℕ) := by ring
      _ ≤ (3 : ℝ) ^ K := htensorRaw
  have hlog24 : Real.log (24 : ℝ) ≤ 5 * Real.log u := by
    have h24 : (24 : ℝ) ≤ u ^ 5 := by
      calc
        (24 : ℝ) ≤ 3 ^ 5 := by norm_num
        _ ≤ u ^ 5 := by gcongr
    exact (Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; norm_num)
      (by simp only [Set.mem_Ioi]; positivity) h24).trans_eq
      (by rw [Real.log_pow]; norm_num)
  have hexpRaw : 24 * u ^ (65 : ℕ) ≤ (x : ℝ) := by
    have hexponent : Real.log (24 : ℝ) + 65 * Real.log u ≤ u := by
      nlinarith
    calc
      24 * u ^ (65 : ℕ) =
          Real.exp (Real.log (24 : ℝ) + 65 * Real.log u) := by
        rw [show Real.log (24 : ℝ) + 65 * Real.log u =
            Real.log (24 * u ^ (65 : ℕ)) by
          rw [Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) (by positivity),
            Real.log_pow]
          ring]
        rw [Real.exp_log]
        positivity
      _ ≤ Real.exp u := Real.exp_le_exp.mpr hexponent
      _ = (x : ℝ) := by simp [u, Real.exp_log hxR]
  have hinitial : 6 * Real.log (x : ℝ) *
      (((Y + 1 : ℕ) : ℝ) ^ 2) ≤ (x : ℝ) := by
    calc
      6 * Real.log (x : ℝ) * (((Y + 1 : ℕ) : ℝ) ^ 2) ≤
          6 * u * (2 * u ^ (32 : ℕ)) ^ 2 := by
        dsimp [u]
        gcongr
      _ = 24 * u ^ (65 : ℕ) := by ring
      _ ≤ (x : ℝ) := hexpRaw
  exact ⟨by simpa [K] using hKpos, by simpa [K, T₀] using hcard,
    by simpa [K, T₀] using hproduct, by simpa [K, Y] using htensor,
    by simpa [Y] using hinitial⟩

private lemma eventually_quadratic_low_parameters
    (S : ℕ) (hS : 0 < S) (D : ℝ) (hD : 0 < D) :
    ∀ᶠ x : ℕ in atTop,
      let y := Nat.nthRoot (4 * S) x
      let T := quadraticSplit x
      let Y := smoothParameterY x
      2 ≤ y ∧ T ≤ y ∧
      (y ^ S) ^ 2 ≤ x ∧
      (T ^ T) ^ 16 ≤ x ∧
      D * Real.log (x : ℝ) ^ (66 : ℕ) ≤
        (x : ℝ) ^ (7 / 16 : ℝ) ∧
      (((Y + 1 : ℕ) : ℝ) ≤
        2 * Real.log (x : ℝ) ^ (32 : ℕ)) := by
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (66 : ℝ)
      (by norm_num : (0 : ℝ) < 7 / 16)).bound (inv_pos.mpr hD)
  have hsmall := tendsto_natCast_atTop_atTop.eventually hsmallReal
  have hTgeS := tendsto_quadraticSplit_atTop.eventually (eventually_ge_atTop S)
  filter_upwards [eventually_quadraticSplit_selfPow_sixteen_le,
      hsmall, hTgeS, eventually_ge_atTop (2 ^ (4 * S)),
      eventually_ge_atTop 16] with x hsplit hsmall hTgeS hxroot hx
  let u : ℝ := Real.log (x : ℝ)
  let y : ℕ := Nat.nthRoot (4 * S) x
  let T : ℕ := quadraticSplit x
  let Y : ℕ := smoothParameterY x
  have hxR : (0 : ℝ) < x := by positivity
  have hu1 : (1 : ℝ) < u := by
    dsimp [u]
    rw [Real.lt_log_iff_exp_lt hxR]
    calc
      Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ ≤ 3 := by norm_num
      _ ≤ (x : ℝ) := by exact_mod_cast (show 3 ≤ x by omega)
  have hu0 : 0 ≤ u := (zero_lt_one.trans hu1).le
  have hlogpos : 0 < Real.log (x : ℝ) := by simpa [u] using zero_lt_one.trans hu1
  have hy2 : 2 ≤ y := by
    apply (Nat.le_nthRoot_iff (by omega : 4 * S ≠ 0)).2
    simpa [y] using hxroot
  have hTy : T ≤ y := by
    apply (Nat.le_nthRoot_iff (by omega : 4 * S ≠ 0)).2
    have hexp : 4 * S ≤ 16 * T := by omega
    calc
      T ^ (4 * S) ≤ T ^ (16 * T) :=
        Nat.pow_le_pow_right (by omega : 1 ≤ T) hexp
      _ = (T ^ T) ^ 16 := by ring
      _ ≤ x := by simpa [T] using hsplit
  have herr := Erdos822.slowSieveCutoff_error_sq_le x S hS
  have hsmall' : Real.log (x : ℝ) ^ (66 : ℕ) ≤
      D⁻¹ * (x : ℝ) ^ (7 / 16 : ℝ) := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlogpos.le _),
      Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hxR.le _)] at hsmall
    rw [show (66 : ℝ) = ((66 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at hsmall
    exact hsmall
  have hDsmall : D * Real.log (x : ℝ) ^ (66 : ℕ) ≤
      (x : ℝ) ^ (7 / 16 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hsmall' hD.le
    field_simp [hD.ne'] at this
    exact this
  have hYle : (Y : ℝ) ≤ u ^ (32 : ℕ) := by
    dsimp [Y, smoothParameterY, logarithmicCutoff]
    have hfloor := Nat.floor_le (Real.rpow_nonneg hu0 (32 : ℝ))
    simpa [u, Real.rpow_natCast] using hfloor
  have hYsucc : ((Y + 1 : ℕ) : ℝ) ≤ 2 * u ^ (32 : ℕ) := by
    push_cast
    have huPow : (1 : ℝ) ≤ u ^ (32 : ℕ) := one_le_pow₀ hu1.le
    linarith
  exact ⟨hy2, hTy, by simpa [y] using herr, by simpa [T] using hsplit,
    hDsmall, by simpa [u, Y] using hYsucc⟩

private lemma eventually_quadratic_high_exceptional_bound :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      quadraticSplit x ≤ t → t ≤ smoothParameterY x →
      ((exceptionalPrimes 2 t x).card : ℝ) ≤
        (x : ℝ) / Real.log (x : ℝ) /
          (((t + 1 : ℕ) : ℝ) ^ 2) := by
  filter_upwards [eventually_quadratic_high_parameters,
      eventually_ge_atTop 16] with x hp hx
  intro t hsplit htY
  let Q := quadraticAuxiliaryPrimes (quadraticSplit x)
  let K := quadraticTensorDepth x
  let Y := smoothParameterY x
  let A : ℝ := Real.log (x : ℝ)
  let Z : ℝ := (((Y + 1 : ℕ) : ℝ) ^ 2)
  let den : ℝ := (3 : ℝ) ^ K
  have hxR : (0 : ℝ) < x := by positivity
  have hA : 0 < A := by
    dsimp [A]
    exact Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hden : 0 < den := by dsimp [den]; positivity
  have hK : 0 < K := by simpa [K] using hp.1
  have h8 : 8 * K ≤ Q.card := by simpa [K, Q] using hp.2.1
  have hproduct : ∀ T U : Erdos380.fixedCardSubsets Q K,
      (∏ q ∈ T.1, q.1) * (∏ q ∈ U.1, q.1) ≤ x := by
    simpa [Q, K] using hp.2.2.1
  have hpat (b : Bool) :
      ((quadraticResiduePrimePattern Q b 2 x).card : ℝ) ≤
        2 * (x : ℝ) / den := by
    have h := quadraticResiduePrimePattern_card_le_three_pow Q
      (fun _q hq ↦ quadraticAuxiliaryPrimes_prime hq)
      (fun _q hq ↦ quadraticAuxiliaryPrimes_ne_two hq)
      b K 2 x hK h8 hproduct
    convert h using 1 <;> simp [den] <;> ring
  have hraw : ((exceptionalPrimes 2 t x).card : ℝ) ≤
      3 + 4 * (x : ℝ) / den := by
    have hcard := exceptionalPrimes_two_card_le_quadraticPatterns t 2 x (by norm_num)
    have hfalse := hpat false
    have htrue := hpat true
    dsimp [Q] at hfalse htrue
    calc
      ((exceptionalPrimes 2 t x).card : ℝ) ≤
          3 +
            ((quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t)
              false 2 x).card : ℝ) +
            ((quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t)
              true 2 x).card : ℝ) := by simpa using hcard
      _ ≤ 3 +
            ((quadraticResiduePrimePattern Q false 2 x).card : ℝ) +
            ((quadraticResiduePrimePattern Q true 2 x).card : ℝ) := by
        -- Requiring residues at the smaller split is weaker than requiring
        -- them at every auxiliary prime up to `t`.
        have hf :
            ((quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t)
              false 2 x).card : ℝ) ≤
            ((quadraticResiduePrimePattern Q false 2 x).card : ℝ) := by
          exact_mod_cast Finset.card_le_card
            (quadraticResiduePrimePattern_mono_auxiliary
              (candidateOneModFour := false) (m0 := 2) (N := x)
              (quadraticAuxiliaryPrimes_mono hsplit))
        have ht :
            ((quadraticResiduePrimePattern (quadraticAuxiliaryPrimes t)
              true 2 x).card : ℝ) ≤
            ((quadraticResiduePrimePattern Q true 2 x).card : ℝ) := by
          exact_mod_cast Finset.card_le_card
            (quadraticResiduePrimePattern_mono_auxiliary
              (candidateOneModFour := true) (m0 := 2) (N := x)
              (quadraticAuxiliaryPrimes_mono hsplit))
        linarith
      _ ≤ 3 + (2 * (x : ℝ) / den) + (2 * (x : ℝ) / den) := by
        gcongr
      _ = 3 + 4 * (x : ℝ) / den := by ring
  have hdenBound : 8 * A * Z ≤ den := by
    simpa [A, Z, den, K, Y] using hp.2.2.2.1
  have hxBound : 6 * A * Z ≤ (x : ℝ) := by
    simpa [A, Z, Y] using hp.2.2.2.2
  have hinit : (3 : ℝ) ≤ (x : ℝ) / (2 * A * Z) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hsieve : 4 * (x : ℝ) / den ≤
      (x : ℝ) / (2 * A * Z) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have hm := mul_le_mul_of_nonneg_right hdenBound hxR.le
    nlinarith
  have htop : ((exceptionalPrimes 2 t x).card : ℝ) ≤
      (x : ℝ) / A / Z := by
    calc
      ((exceptionalPrimes 2 t x).card : ℝ) ≤
          3 + 4 * (x : ℝ) / den := hraw
      _ ≤ (x : ℝ) / (2 * A * Z) +
          (x : ℝ) / (2 * A * Z) := add_le_add hinit hsieve
      _ = (x : ℝ) / A / Z := by field_simp; ring
  have htZ : ((((t + 1 : ℕ) : ℝ) ^ 2)) ≤ Z := by
    dsimp [Z, Y]
    exact pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast Nat.add_le_add_right htY 1) 2
  calc
    ((exceptionalPrimes 2 t x).card : ℝ) ≤ (x : ℝ) / A / Z := htop
    _ ≤ (x : ℝ) / A / (((t + 1 : ℕ) : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) htZ
    _ = (x : ℝ) / Real.log (x : ℝ) /
          (((t + 1 : ℕ) : ℝ) ^ 2) := by rfl

/-- The quadratic Rosser sieve and the moving tensor together give a
uniform inverse-square cumulative exceptional-prime bound. -/
theorem exists_quadratic_inverseSquare_cumulative_bound :
    ∃ C : ℝ, 0 < C ∧
      CumulativeExceptionalPrimeScaleBound 2 (inverseSquareMajorant C) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hsieve⟩ :=
    exists_quadraticResiduePrimePattern_rosser_upper_bound
  obtain ⟨B, hB, hBbound⟩ := exists_quadraticGeometricWeight_bound
  let Cβ := Classical.choose exists_baseCongruence_rosser_upper_bound
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (max 1 (Real.log Cβ))
  let S : ℕ := 100 + 99 * n
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
    exact_mod_cast this.le
  have hS101 : 101 ≤ S := by dsimp [S]; omega
  have hSpos : 0 < S := by omega
  have hRosserLog : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 := by
    have hlogn : Real.log Cβ ≤ (n : ℝ) :=
      (le_max_right (1 : ℝ) (Real.log Cβ)).trans hn.le
    dsimp [S]
    push_cast
    norm_num
    linarith
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  let D : ℝ := max 8 (8 * C₂ / Real.log 3)
  have hD : 0 < D := (by norm_num : (0 : ℝ) < 8).trans_le (le_max_left _ _)
  let C : ℝ := 16 * C₁ * (S : ℝ) * B + 3
  have hC : 0 < C := by dsimp [C]; positivity
  have hCone : 1 ≤ C := by
    have hnonneg : 0 ≤ 16 * C₁ * (S : ℝ) * B := by positivity
    dsimp [C]
    linarith
  have hlow := eventually_quadratic_low_parameters S hSpos D hD
  have hsplit3 := tendsto_quadraticSplit_atTop.eventually (eventually_ge_atTop 3)
  have hhigh := eventually_quadratic_high_exceptional_bound
  have hevent : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      t ≤ smoothParameterY x →
      ((exceptionalPrimes 2 t x).card : ℝ) ≤
        (x : ℝ) / Real.log (x : ℝ) * inverseSquareMajorant C t := by
    filter_upwards [hlow, hsplit3, hhigh, eventually_ge_atTop 16] with
        x hlow hsplit3 hhigh hx
    intro t htY
    by_cases ht : t ≤ quadraticSplit x
    · let y : ℕ := Nat.nthRoot (4 * S) x
      let T : ℕ := quadraticSplit x
      let Y : ℕ := smoothParameterY x
      let z : ℕ := max 3 t
      let Q := quadraticAuxiliaryPrimes t
      let A : ℝ := Real.log (x : ℝ)
      let P : ℕ := T ^ T
      let E : ℕ := y ^ S
      have hxR : (0 : ℝ) < x := by positivity
      have hA : 0 < A := by
        dsimp [A]
        exact Real.log_pos (by exact_mod_cast (show 1 < x by omega))
      have hy2 : 2 ≤ y := by simpa [y, T, Y] using hlow.1
      have hTy : T ≤ y := by simpa [y, T, Y] using hlow.2.1
      have herr : E ^ 2 ≤ x := by simpa [y, T, Y, E] using hlow.2.2.1
      have hPpow : P ^ 16 ≤ x := by simpa [y, T, Y, P] using hlow.2.2.2.1
      have hanalytic : D * A ^ (66 : ℕ) ≤
          (x : ℝ) ^ (7 / 16 : ℝ) := by
        simpa [y, T, Y, A] using hlow.2.2.2.2.1
      have hYsucc : (((Y + 1 : ℕ) : ℝ) ≤ 2 * A ^ (32 : ℕ)) := by
        simpa [y, T, Y, A] using hlow.2.2.2.2.2
      have hT3 : 3 ≤ T := by simpa [T] using hsplit3
      have hz2 : 2 ≤ z := by dsimp [z]; omega
      have hzy : z ≤ y := by
        have : z ≤ T := by dsimp [z]; omega
        exact this.trans hTy
      have hy1 : 1 < y := by omega
      have hQz : ∀ q ∈ Q, q ≤ z := by
        intro q hq
        exact (quadraticAuxiliaryPrimes_le hq).trans (le_max_right 3 t)
      have hpat (b : Bool) :
          ((quadraticResiduePrimePattern Q b y x).card : ℝ) ≤
            C₁ * (1 / 2 : ℝ) ^ Q.card * (x : ℝ) *
                (Real.log (z : ℝ) / Real.log (y : ℝ)) +
              C₂ * ((quadraticBaseResidues Q
                  (fun _q hq ↦ quadraticAuxiliaryPrimes_prime hq)
                  (fun q ↦ reciprocityWantsSquare b q.1)).card : ℝ) *
                (y ^ S : ℕ) *
                  (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
        exact hsieve
          (fun _q hq ↦ quadraticAuxiliaryPrimes_prime hq)
          (fun _q hq ↦ quadraticAuxiliaryPrimes_ne_two hq)
          b (le_refl y) hz2 hzy hy1 hS101 hQz
          (by simpa [Cβ] using hRosserLog)
      have hcard := exceptionalPrimes_two_card_le_quadraticPatterns t y x hy2
      have hbase (b : Bool) :
          (quadraticBaseResidues Q
            (fun _q hq ↦ quadraticAuxiliaryPrimes_prime hq)
            (fun q ↦ reciprocityWantsSquare b q.1)).card ≤ P :=
        quadraticBaseResidues_aux_card_le_split_pow
          ht (by omega : 1 ≤ T) b
      have hyx : y ≤ x := Erdos822.nthRoot_le_self_of_pos (by omega)
      have hlogy : 0 < Real.log (y : ℝ) :=
        Real.log_pos (by exact_mod_cast hy1)
      have hlogz : 0 < Real.log (z : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < z by omega))
      have hlogyA : Real.log (y : ℝ) ≤ A := by
        dsimp [A]
        exact Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; positivity)
          (by simp only [Set.mem_Ioi]; positivity)
          (by exact_mod_cast hyx)
      have hlog3z : Real.log (3 : ℝ) ≤ Real.log (z : ℝ) :=
        Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; norm_num)
          (by simp only [Set.mem_Ioi]; positivity)
          (by exact_mod_cast (le_max_left 3 t))
      have hratio : A / Real.log (y : ℝ) ≤ 8 * (S : ℝ) := by
        simpa [A, y] using Erdos822.log_div_log_slowSieveCutoff_le hSpos hy2
      have hreverseRatio : Real.log (y : ℝ) / Real.log (z : ℝ) ≤
          A / Real.log (3 : ℝ) := by
        calc
          Real.log (y : ℝ) / Real.log (z : ℝ) ≤
              A / Real.log (z : ℝ) :=
            div_le_div_of_nonneg_right hlogyA hlogz.le
          _ ≤ A / Real.log (3 : ℝ) :=
            div_le_div_of_nonneg_left hA.le hlog3 hlog3z
      have hP : (P : ℝ) ≤ (x : ℝ) ^ (1 / 16 : ℝ) := by
        rw [show (1 / 16 : ℝ) = (16 : ℝ)⁻¹ by norm_num]
        apply (Real.le_rpow_inv_iff_of_pos (by positivity) hxR.le (by norm_num)).2
        have hpowR : ((P : ℝ) ^ 16) ≤ (x : ℝ) := by exact_mod_cast hPpow
        simpa [Real.rpow_natCast] using hpowR
      have hE : (E : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
        apply (Real.le_rpow_inv_iff_of_pos (by positivity) hxR.le (by norm_num)).2
        have herrR : ((E : ℝ) ^ 2) ≤ (x : ℝ) := by exact_mod_cast herr
        simpa [Real.rpow_natCast] using herrR
      have hPE : (P : ℝ) * E ≤ (x : ℝ) ^ (9 / 16 : ℝ) := by
        calc
          (P : ℝ) * E ≤
              (x : ℝ) ^ (1 / 16 : ℝ) *
                (x : ℝ) ^ (1 / 2 : ℝ) := mul_le_mul hP hE (by positivity) (by positivity)
          _ = (x : ℝ) ^ (9 / 16 : ℝ) := by
            rw [← Real.rpow_add hxR]
            norm_num
      have hsq : (((t + 1 : ℕ) : ℝ) ^ 2) ≤ 4 * A ^ (64 : ℕ) := by
        calc
          (((t + 1 : ℕ) : ℝ) ^ 2) ≤
              (((Y + 1 : ℕ) : ℝ) ^ 2) := by
            gcongr
          _ ≤ (2 * A ^ (32 : ℕ)) ^ 2 := by gcongr
          _ = 4 * A ^ (64 : ℕ) := by ring
      have hDcoef : 8 * C₂ / Real.log 3 ≤ D := le_max_right _ _
      have htailAbsorb : D * (x : ℝ) ^ (9 / 16 : ℝ) * A ^ (65 : ℕ) ≤
          (x : ℝ) / A := by
        calc
          D * (x : ℝ) ^ (9 / 16 : ℝ) * A ^ (65 : ℕ) =
              ((x : ℝ) ^ (9 / 16 : ℝ) / A) *
                (D * A ^ (66 : ℕ)) := by field_simp
          _ ≤ ((x : ℝ) ^ (9 / 16 : ℝ) / A) *
                (x : ℝ) ^ (7 / 16 : ℝ) := by gcongr
          _ = (x : ℝ) / A := by
            rw [div_mul_eq_mul_div, ← Real.rpow_add hxR]
            norm_num
      have hendpoint (b : Bool) :
          (C₂ * ((quadraticBaseResidues Q
              (fun _q hq ↦ quadraticAuxiliaryPrimes_prime hq)
              (fun q ↦ reciprocityWantsSquare b q.1)).card : ℝ) *
            (y ^ S : ℕ) *
              (Real.log (y : ℝ) / Real.log (z : ℝ))) *
            (((t + 1 : ℕ) : ℝ) ^ 2) ≤ (x : ℝ) / A := by
        calc
          _ ≤ C₂ * (P : ℝ) * E *
              (A / Real.log 3) * (4 * A ^ (64 : ℕ)) := by
            gcongr
            exact_mod_cast hbase b
          _ ≤ D * (P : ℝ) * E * A ^ (65 : ℕ) := by
            have hlog3ne := hlog3.ne'
            have h4D : 4 * C₂ / Real.log 3 ≤ D := by
              calc
                4 * C₂ / Real.log 3 ≤ 8 * C₂ / Real.log 3 := by
                  exact div_le_div_of_nonneg_right (by nlinarith [hC₂.le]) hlog3.le
                _ ≤ D := hDcoef
            calc
              C₂ * (P : ℝ) * E * (A / Real.log 3) *
                  (4 * A ^ (64 : ℕ)) =
                  (4 * C₂ / Real.log 3) * (P : ℝ) * E * A ^ 65 := by
                field_simp
              _ ≤ D * (P : ℝ) * E * A ^ 65 := by
                gcongr
          _ = D * ((P : ℝ) * E) * A ^ (65 : ℕ) := by ring
          _ ≤ D * (x : ℝ) ^ (9 / 16 : ℝ) * A ^ (65 : ℕ) := by
            gcongr
          _ ≤ (x : ℝ) / A := htailAbsorb
      have hyS : y ≤ E := by
        dsimp [E]
        simpa using Nat.pow_le_pow_right (by omega : 1 ≤ y)
          (show 1 ≤ S by omega)
      have hE9 : (E : ℝ) ≤ (x : ℝ) ^ (9 / 16 : ℝ) :=
        hE.trans (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ x by omega)) (by norm_num))
      have hinit : ((y + 1 : ℕ) : ℝ) * (((t + 1 : ℕ) : ℝ) ^ 2) ≤
          (x : ℝ) / A := by
        have hx9one : (1 : ℝ) ≤ (x : ℝ) ^ (9 / 16 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast (show 1 ≤ x by omega)) (by norm_num)
        calc
          ((y + 1 : ℕ) : ℝ) * (((t + 1 : ℕ) : ℝ) ^ 2) ≤
              (2 * (x : ℝ) ^ (9 / 16 : ℝ)) *
                (4 * A ^ (64 : ℕ)) := by
            apply mul_le_mul _ hsq (by positivity) (by positivity)
            push_cast
            have hyR : (y : ℝ) ≤ (x : ℝ) ^ (9 / 16 : ℝ) :=
              (by exact_mod_cast hyS : (y : ℝ) ≤ E).trans hE9
            linarith
          _ = 8 * (x : ℝ) ^ (9 / 16 : ℝ) * A ^ 64 := by ring
          _ ≤ D * (x : ℝ) ^ (9 / 16 : ℝ) * A ^ 65 := by
            have hD8 : (8 : ℝ) ≤ D := le_max_left _ _
            have hA1 : (1 : ℝ) ≤ A := by
              dsimp [A]
              exact (show (1 : ℝ) < Real.log (x : ℝ) from by
                rw [Real.lt_log_iff_exp_lt hxR]
                calc
                  Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
                  _ ≤ 3 := by norm_num
                  _ ≤ (x : ℝ) := by exact_mod_cast (show 3 ≤ x by omega)).le
            gcongr
            simpa [pow_succ] using
              mul_le_mul_of_nonneg_left hA1 (pow_nonneg hA.le 64)
          _ ≤ (x : ℝ) / A := htailAbsorb
      have hmain :
          (2 * (C₁ * (1 / 2 : ℝ) ^ Q.card * (x : ℝ) *
            (Real.log (z : ℝ) / Real.log (y : ℝ)))) *
              (((t + 1 : ℕ) : ℝ) ^ 2) ≤
            (x : ℝ) / A * (16 * C₁ * (S : ℝ) * B) := by
        have hW : (1 / 2 : ℝ) ^ Q.card * Real.log (z : ℝ) *
            (((t + 1 : ℕ) : ℝ) ^ 2) ≤ B := by
          simpa [quadraticGeometricWeight, Q, z] using hBbound t
        have hscale : 0 ≤ (x : ℝ) / A := by positivity
        calc
          _ = (x : ℝ) / A *
              (2 * C₁ * ((1 / 2 : ℝ) ^ Q.card * Real.log (z : ℝ) *
                (((t + 1 : ℕ) : ℝ) ^ 2)) *
                (A / Real.log (y : ℝ))) := by field_simp
          _ ≤ (x : ℝ) / A *
              (2 * C₁ * B * (8 * (S : ℝ))) := by gcongr
          _ = (x : ℝ) / A * (16 * C₁ * (S : ℝ) * B) := by ring
      let M : ℝ := C₁ * (1 / 2 : ℝ) ^ Q.card * (x : ℝ) *
        (Real.log (z : ℝ) / Real.log (y : ℝ))
      let EF : ℝ := C₂ * ((quadraticBaseResidues Q
          (fun _q hq ↦ quadraticAuxiliaryPrimes_prime hq)
          (fun q ↦ reciprocityWantsSquare false q.1)).card : ℝ) * E *
        (Real.log (y : ℝ) / Real.log (z : ℝ))
      let ET : ℝ := C₂ * ((quadraticBaseResidues Q
          (fun _q hq ↦ quadraticAuxiliaryPrimes_prime hq)
          (fun q ↦ reciprocityWantsSquare true q.1)).card : ℝ) * E *
        (Real.log (y : ℝ) / Real.log (z : ℝ))
      have hfalse : ((quadraticResiduePrimePattern Q false y x).card : ℝ) ≤
          M + EF := by simpa [M, EF, E] using hpat false
      have htrue : ((quadraticResiduePrimePattern Q true y x).card : ℝ) ≤
          M + ET := by simpa [M, ET, E] using hpat true
      have hmain' : (2 * M) * (((t + 1 : ℕ) : ℝ) ^ 2) ≤
          (x : ℝ) / A * (16 * C₁ * (S : ℝ) * B) := by
        simpa [M] using hmain
      have hendpointF : EF * (((t + 1 : ℕ) : ℝ) ^ 2) ≤
          (x : ℝ) / A := by simpa [EF, E] using hendpoint false
      have hendpointT : ET * (((t + 1 : ℕ) : ℝ) ^ 2) ≤
          (x : ℝ) / A := by simpa [ET, E] using hendpoint true
      have htotalWeighted : ((exceptionalPrimes 2 t x).card : ℝ) *
          (((t + 1 : ℕ) : ℝ) ^ 2) ≤ (x : ℝ) / A * C := by
        have hraw : ((exceptionalPrimes 2 t x).card : ℝ) ≤
            (y + 1 : ℕ) + 2 * M + EF + ET := by
          calc
            ((exceptionalPrimes 2 t x).card : ℝ) ≤
                (y + 1 : ℕ) +
                  ((quadraticResiduePrimePattern Q false y x).card : ℝ) +
                  ((quadraticResiduePrimePattern Q true y x).card : ℝ) := by
              simpa [Q] using hcard
            _ ≤ (y + 1 : ℕ) + (M + EF) + (M + ET) := by gcongr
            _ = (y + 1 : ℕ) + 2 * M + EF + ET := by ring
        have hmul := mul_le_mul_of_nonneg_right hraw (by positivity :
          (0 : ℝ) ≤ (((t + 1 : ℕ) : ℝ) ^ 2))
        calc
          ((exceptionalPrimes 2 t x).card : ℝ) * (((t + 1 : ℕ) : ℝ) ^ 2) ≤
              _ := hmul
          _ = ((y + 1 : ℕ) : ℝ) * (((t + 1 : ℕ) : ℝ) ^ 2) +
              (2 * M) * (((t + 1 : ℕ) : ℝ) ^ 2) +
              EF * (((t + 1 : ℕ) : ℝ) ^ 2) +
              ET * (((t + 1 : ℕ) : ℝ) ^ 2) := by ring
          _ ≤ (x : ℝ) / A +
              ((x : ℝ) / A * (16 * C₁ * (S : ℝ) * B)) +
              (x : ℝ) / A + (x : ℝ) / A := by gcongr
          _ = (x : ℝ) / A * C := by simp [C]; ring
      unfold inverseSquareMajorant
      rw [show (x : ℝ) / Real.log (x : ℝ) *
          (C / (((t + 1 : ℕ) : ℝ) ^ 2)) =
          ((x : ℝ) / Real.log (x : ℝ) * C) /
            (((t + 1 : ℕ) : ℝ) ^ 2) by ring]
      apply (le_div_iff₀ (by positivity)).2
      simpa [A, mul_assoc] using htotalWeighted
    · have hh := hhigh t (by omega) htY
      unfold inverseSquareMajorant
      have hlogpos : 0 < Real.log (x : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < x by omega))
      have hscale : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
      calc
        ((exceptionalPrimes 2 t x).card : ℝ) ≤
            (x : ℝ) / Real.log (x : ℝ) /
              (((t + 1 : ℕ) : ℝ) ^ 2) := hh
        _ ≤ ((x : ℝ) / Real.log (x : ℝ) * C) /
              (((t + 1 : ℕ) : ℝ) ^ 2) := by
          exact div_le_div_of_nonneg_right
            (by simpa using mul_le_mul_of_nonneg_left hCone hscale) (by positivity)
        _ = (x : ℝ) / Real.log (x : ℝ) *
              (C / (((t + 1 : ℕ) : ℝ) ^ 2)) := by ring
  obtain ⟨X, hX⟩ := eventually_atTop.mp hevent
  refine ⟨C, hC, X, ?_⟩
  intro x hx t ht
  exact hX x hx t ht

/-- Unconditional quadratic medium-tail estimate used by the final Elliott
assembly. -/
theorem quadraticPrimeExponentMediumEstimate : PrimeExponentMediumEstimate 2 := by
  obtain ⟨C, hC, hcount⟩ := exists_quadratic_inverseSquare_cumulative_bound
  exact primeExponentMediumEstimate_of_inverseSquare_cumulative_bound
    2 (by norm_num) C hC.le hcount

#print axioms quadraticPrimeExponentMediumEstimate

end Erdos980.ElliottTail

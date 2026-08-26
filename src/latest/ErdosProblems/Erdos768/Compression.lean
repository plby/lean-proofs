import Mathlib
import ErdosProblems.Erdos768.Defs

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 768 — canonical compression scaffold (Sections 7–9)

This file develops the canonical-witness / deterministic homogeneous-sequence
construction underlying `Erdos768.canonical_compression_exists`.  Together with
`RequestProject/Canonical.lean` (which assembles the canonical fiber bound and is
imported by `RequestProject/UpperBound.lean`), it now fully discharges
`canonical_compression_exists`.
-/

open scoped Classical BigOperators
open Finset

namespace Erdos768Comp

open Erdos768

/-- Canonical Sylow witness: least divisor `d > 1` of `n` with `d ≡ 1 (mod p)`. -/
noncomputable def Dwit (n p : ℕ) : ℕ :=
  (n.divisors.filter (fun d => 1 < d ∧ d % p = 1)).min.getD 0

/-- One deterministic majority-halving step on a finset of primes of `n`. -/
noncomputable def step (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if h : S.Nonempty then
    let q := S.max' h
    let rest := S.erase q
    let Splus := rest.filter (fun r => r ∣ Dwit n q)
    let Szero := rest.filter (fun r => ¬ r ∣ Dwit n q)
    if Szero.card < Splus.card then Splus else Szero
  else S

/-- Iterated selection sets `S_i`. -/
noncomputable def Siter (n : ℕ) (S0 : Finset ℕ) : ℕ → Finset ℕ
  | 0 => S0
  | (i+1) => step n (Siter n S0 i)

/-- The `i`-th selected prime (0-indexed): the maximum of `S_i`. -/
noncomputable def qsel (n : ℕ) (S0 : Finset ℕ) (i : ℕ) : ℕ :=
  (Siter n S0 i).max.getD 0

/-
**Row-homogeneity (core of Lemma 7.1).**  Every element remaining after the
`(i+1)`-st selection stands in the same divisibility relation to the witness of
the `i`-th selected prime: they all divide `D_{q_i}`, or none of them does.
-/
theorem homog (n : ℕ) (S0 : Finset ℕ) (i : ℕ) (a b : ℕ)
    (ha : a ∈ Siter n S0 (i+1)) (hb : b ∈ Siter n S0 (i+1)) :
    (a ∣ Dwit n (qsel n S0 i)) ↔ (b ∣ Dwit n (qsel n S0 i)) := by
  by_cases h_nonempty : (Siter n S0 i).Nonempty;
  · unfold Siter at ha hb;
    unfold step at ha hb;
    unfold qsel;
    rw [ show ( Siter n S0 i ).max = some ( Siter n S0 i |> Finset.max' <| h_nonempty ) from ?_ ];
    · grind;
    · exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr <| Finset.le_max' _ _ hx ) ( Finset.le_sup ( f := WithBot.some ) <| Finset.max'_mem _ h_nonempty );
  · simp_all +decide [ Siter ];
    unfold step at ha hb; aesop;

/-
The defining set of the canonical witness is nonempty for `n ∈ Acal` and a
prime `p ∣ n`.
-/
theorem Dwit_spec (n p : ℕ) (hn : n ∈ Acal) (hp : p.Prime) (hpn : p ∣ n) (hn0 : n ≠ 0) :
    Dwit n p ∣ n ∧ 1 < Dwit n p ∧ Dwit n p % p = 1 := by
  unfold Dwit;
  unfold Acal at hn; simp_all +decide [ SylowDivisor ] ;
  obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := hn p hp hpn; have := Finset.min_of_mem ( show d ∈ { d ∈ n.divisors | 1 < d ∧ d % p = 1 } from by aesop ) ; simp_all +decide [ Finset.min ] ;
  rcases this with ⟨ b, hb ⟩ ; rw [ hb ] ; simp +decide [ Option.getD ] ;
  have := Finset.mem_of_min hb; aesop;

/-
`p` never divides its canonical witness.
-/
theorem Dwit_not_dvd (n p : ℕ) (hn : n ∈ Acal) (hp : p.Prime) (hpn : p ∣ n) (hn0 : n ≠ 0) :
    ¬ p ∣ Dwit n p := by
  convert! Nat.dvd_iff_mod_eq_zero.not.mpr _;
  rw [ Dwit_spec _ _ hn hp hpn hn0 |>.2.2 ] ; aesop

/-
**Lemma 8.1 (one-bit valuation completion).**  Let `Q` be squarefree, `n = m*Q`
and `D ∣ n`.  With `a = gcd(D,m)`, for each prime `q ∣ Q` the excess
`v_q(D) - v_q(a)` is `0` or `1`, and `D = a * ∏_{q ∣ Q} q^{v_q(D)-v_q(a)}`.
-/
theorem valuation_bit (Q m D : ℕ) (hQ : Squarefree Q) (hm : m ≠ 0)
    (hD : D ∣ m * Q) (hD0 : D ≠ 0) :
    (∀ q ∈ Q.primeFactors, (D.factorization q) - ((Nat.gcd D m).factorization q) ≤ 1) ∧
      D = Nat.gcd D m * ∏ q ∈ Q.primeFactors, q ^ ((D.factorization q) - ((Nat.gcd D m).factorization q)) := by
  refine' ⟨ fun q hq => _, _ ⟩;
  · have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 hD ; simp_all +decide [ Nat.factorization_mul ] ;
    replace := this q; simp_all +decide [ Nat.factorization_gcd ] ;
    have := hQ.natFactorization_le_one q; omega;
  · refine' Nat.factorization_inj _ _ _;
    · grind;
    · simp_all +decide [ Finset.prod_eq_zero_iff ];
    · ext p; by_cases hp : p.Prime <;> simp_all +decide [ Nat.factorization_prod, Finset.prod_eq_zero_iff ] ;
      by_cases hpQ : p ∈ Q.primeFactors <;> simp_all +decide [ Nat.factorization_gcd, Finset.sum_eq_single p ];
      rw [ Finset.sum_eq_zero ] <;> simp_all +decide;
      · have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 hD; simp_all +decide ;
        by_cases hQ0 : Q = 0 <;> simp_all +decide [ Nat.factorization_mul ];
        replace this := this p; simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd hpQ ] ;
      · intro x hx hxQ hQ0; rw [ Finsupp.single_apply ] ; aesop;

/-! ### The per-`r` selection structure -/

/-- Top-`r` distinct prime factors of `n` (the starting set `S_0`). -/
noncomputable def topR (n r : ℕ) : Finset ℕ :=
  ((n.primeFactors.sort (· ≥ ·)).take r).toFinset

/-- The `i`-th selected prime for the run started at `topR n r`. -/
noncomputable def qi (n r i : ℕ) : ℕ := qsel n (topR n r) i

/-- Whether row `i` is a positive row (majority divides the witness). -/
noncomputable def rowPos (n r i : ℕ) : Prop :=
  (((Siter n (topR n r) i).erase (qi n r i)).filter (fun z => ¬ z ∣ Dwit n (qi n r i))).card
    < (((Siter n (topR n r) i).erase (qi n r i)).filter (fun z => z ∣ Dwit n (qi n r i))).card

/-- Positive-row index set among the first `h_r` rows. -/
noncomputable def Iplus (n r : ℕ) : Finset ℕ := (Finset.range (hr r)).filter (fun i => rowPos n r i)

/-- Zero-row index set among the first `h_r` rows. -/
noncomputable def Izero (n r : ℕ) : Finset ℕ := (Finset.range (hr r)).filter (fun i => ¬ rowPos n r i)

/-- Number of positive rows. -/
noncomputable def hplus (n r : ℕ) : ℕ := (Iplus n r).card

/-- Deleted-slot index set `E = I₀ ∪ {h,…,h+h₊-1}`. -/
noncomputable def Esel (n r : ℕ) : Finset ℕ := Izero n r ∪ Finset.Ico (hr r) (hr r + hplus n r)

/-- The deleted squarefree divisor `Q_r(n) = ∏_{j∈E} q_j`. -/
noncomputable def Qr (n r : ℕ) : ℕ := ∏ j ∈ Esel n r, qi n r j

/-
Selection sets are contained in the starting set `topR n r`.
-/
theorem Siter_subset (n r i : ℕ) : Siter n (topR n r) i ⊆ topR n r := by
  induction' i with i ih;
  · rfl;
  · simp_all +decide [ Siter, step ];
    grind

/-
`topR n r ⊆ n.primeFactors`.
-/
theorem topR_subset (n r : ℕ) : topR n r ⊆ n.primeFactors := by
  intro z hz
  simp [topR] at hz;
  exact Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x2 ≤ x1 ) |>.1 ( List.mem_of_mem_take hz )

/-
When `r ≤ ω(n)`, `topR n r` has exactly `r` elements.
-/
theorem topR_card (n r : ℕ) (hrn : r ≤ omegaCount n) : (topR n r).card = r := by
  -- The list `L := n.primeFactors.sort (· ≥ ·)` is `Nodup` (`Finset.sort_nodup`) and has length `n.primeFactors.card = omegaCount n` (`Finset.length_sort`).
  set L := n.primeFactors.sort (· ≥ ·)
  have hL_nodup : L.Nodup := by
    exact Finset.sort_nodup _ _
  have hL_length : L.length = omegaCount n := by
    aesop;
  convert! List.toFinset_card_of_nodup _;
  · grind;
  · exact hL_nodup.sublist ( List.take_sublist _ _ )

/-
Halving bound: one step keeps at least `⌈(|S|-1)/2⌉` elements.
-/
theorem step_card_ge (n : ℕ) (S : Finset ℕ) :
    S.card / 2 ≤ (step n S).card := by
  by_cases hS : S.Nonempty;
  · unfold step;
    split_ifs;
    have h_card : (Finset.filter (fun r => r ∣ Dwit n (S.max' hS)) (S.erase (S.max' hS))).card + (Finset.filter (fun r => ¬r ∣ Dwit n (S.max' hS)) (S.erase (S.max' hS))).card = S.card - 1 := by
      rw [ Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem ( Finset.max'_mem _ hS ) ];
    grind;
  · aesop

/-
The selection sets stay large: for `i ≤ ⌊log₂ r⌋`, `2^(⌊log₂ r⌋ - i) ≤ |S_i|`
provided `r ≤ ω(n)`.
-/
theorem Siter_card_ge (n r i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hi : i ≤ Nat.log 2 r) :
    2 ^ (Nat.log 2 r - i) ≤ (Siter n (topR n r) i).card := by
  induction' i with i ih <;> norm_num at *;
  · rw [ show Siter n ( topR n r ) 0 = topR n r from rfl, topR_card n r hrn ] ; exact Nat.pow_log_le_self 2 ( by linarith );
  · rw [ show Nat.log 2 r - i = ( Nat.log 2 r - ( i + 1 ) ) + 1 by omega, pow_succ' ] at *;
    exact le_trans ( by omega ) ( step_card_ge _ _ )

/-
For `i < s_r` (and `r ≤ ω(n)`), `S_i` is nonempty, so `q_i` is a genuine prime
factor of `n`.
-/
theorem qi_mem_primeFactors (n r i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hi : i < sr r) :
    qi n r i ∈ n.primeFactors := by
  refine' Finset.mem_of_subset ( Siter_subset n r i ) _ |> Finset.mem_of_subset ( topR_subset n r );
  have hq_in_Siter : qi n r i = (Siter n (topR n r) i).max.getD 0 := by
    rfl;
  have h_nonempty : (Siter n (topR n r) i).Nonempty := by
    have h_card : 2 ^ (Nat.log 2 r - i) ≤ (Siter n (topR n r) i).card := by
      apply Siter_card_ge n r i hr1 hrn (by
      exact Nat.le_of_lt_succ ( by rw [ show sr r = 1 + Nat.log 2 r from rfl ] at hi; linarith ));
    exact Finset.card_pos.mp ( lt_of_lt_of_le ( by positivity ) h_card );
  have := Finset.max_of_nonempty h_nonempty;
  obtain ⟨ a, ha ⟩ := this; simp_all +decide [ Finset.max_eq_sup_coe ] ;
  have := Finset.mem_of_max ha; aesop;

/-
The selected primes strictly decrease: `q_{i+1} < q_i` while selections last.
-/
theorem qi_strictAnti (n r i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hi : i + 1 < sr r) :
    qi n r (i+1) < qi n r i := by
  -- By definition of `Siter`, we know that `Siter n (topR n r) (i + 1)` is a subset of `Siter n (topR n r) i` with at least one element removed.
  have h_subset : Siter n (topR n r) (i + 1) ⊆ (Siter n (topR n r) i).erase (qi n r i) := by
    unfold qi;
    unfold qsel;
    rw [ show Siter n ( topR n r ) ( i + 1 ) = step n ( Siter n ( topR n r ) i ) from rfl ] ; unfold step; split_ifs <;> simp_all +decide [ Finset.subset_iff ] ;
    split_ifs <;> simp_all +decide [ Option.getD ];
    · cases h : Finset.max ( Siter n ( topR n r ) i ) <;> simp_all +decide [ Finset.max' ];
      · simp_all +decide [ Finset.max ];
      · intro x hx₁ hx₂ hx₃; contrapose! hx₁; simp_all +decide [ Finset.max_eq_sup_coe ] ;
        exact le_antisymm ( Finset.le_sup' ( fun x => x ) hx₂ ) ( Finset.sup'_le _ _ fun x hx => WithBot.coe_le_coe.mp <| h ▸ Finset.le_sup ( f := WithBot.some ) hx );
    · cases h : ( Siter n ( topR n r ) i ).max <;> simp_all +decide [ Finset.max' ];
      · simp_all +decide [ Finset.max ];
      · intro x hx₁ hx₂ hx₃; contrapose! hx₁; simp_all +decide [ Finset.max_eq_sup_coe ] ;
        exact le_antisymm ( Finset.le_sup' ( fun x => x ) hx₂ ) ( Finset.sup'_le _ _ fun x hx => WithBot.coe_le_coe.mp <| h ▸ Finset.le_sup ( f := WithBot.some ) hx );
  -- Since `Siter n (topR n r) (i + 1)` is a subset of `Siter n (topR n r) i` with at least one element removed, its maximum element must be strictly less than the maximum element of `Siter n (topR n r) i`.
  have h_max_lt : ∀ {S T : Finset ℕ}, S ⊆ T.erase (T.max.getD 0) → S.Nonempty → S.max.getD 0 < T.max.getD 0 := by
    intro S T hST hS_nonempty
    have h_max_lt : ∀ x ∈ S, x < T.max.getD 0 := by
      intro x hx; have := hST hx; simp_all +decide [ Finset.subset_iff ] ;
      have := Finset.le_max ( hST hx |>.2 ) ; cases h : T.max <;> simp_all +decide ;
      exact lt_of_le_of_ne this ( hST hx |>.1 );
    obtain ⟨ x, hx ⟩ := Finset.max_of_nonempty hS_nonempty;
    exact hx.symm ▸ h_max_lt x ( Finset.mem_of_max hx );
  apply h_max_lt h_subset;
  have := Siter_card_ge n r ( i + 1 ) hr1 hrn ( by linarith [ show sr r = 1 + Nat.log 2 r from rfl ] ) ; contrapose! this; aesop;

/-! ### Basic arithmetic of the index bounds -/

/-
`2 * h_r ≤ s_r`.
-/
theorem two_hr_le_sr (r : ℕ) : 2 * hr r ≤ sr r := by
  exact Nat.mul_div_le _ _

/-
`h₊ ≤ h_r`.
-/
theorem hplus_le_hr (n r : ℕ) : hplus n r ≤ hr r := by
  exact Finset.card_filter_le _ _ |> le_trans <| by simp +decide [ hr ] ;

/-
Every deleted slot index is `< s_r`.
-/
theorem Esel_lt_sr (n r j : ℕ) (hj : j ∈ Esel n r) : j < sr r := by
  cases Finset.mem_union.mp hj;
  · exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp ‹_› |>.1 ) ) ( by linarith [ two_hr_le_sr r ] );
  · linarith [ Finset.mem_Ico.mp ‹_›, hplus_le_hr n r, two_hr_le_sr r ]

/-
The selected primes are strictly decreasing in the index, over `[0, s_r)`.
-/
theorem qi_lt_of_lt (n r j k : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hjk : j < k) (hk : k < sr r) : qi n r k < qi n r j := by
  induction' hjk with k hk ih;
  · exact qi_strictAnti n r j hr1 hrn hk;
  · exact lt_trans ( qi_strictAnti n r k hr1 hrn hk ) ( ih ( Nat.lt_of_succ_lt hk ) )

/-
Each selected prime `q_i` (`i < s_r`) is prime.
-/
theorem qi_prime (n r i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hi : i < sr r) :
    (qi n r i).Prime := by
  exact Nat.prime_of_mem_primeFactors ( qi_mem_primeFactors n r i hr1 hrn hi )

/-
Each selected prime `q_i` (`i < s_r`) divides `n`.
-/
theorem qi_dvd (n r i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hi : i < sr r) :
    qi n r i ∣ n := by
  exact Nat.dvd_of_mem_primeFactors ( qi_mem_primeFactors n r i hr1 hrn hi )

/-
The map `j ↦ q_j` is injective on the deleted-slot set `E`.
-/
theorem qi_injOn_Esel (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) :
    Set.InjOn (qi n r) (Esel n r) := by
  intros j hj k hk h_eq;
  by_contra h_neq;
  cases lt_or_gt_of_ne h_neq <;> have := Esel_lt_sr n r j hj <;> have := Esel_lt_sr n r k hk <;> simp_all +decide;
  · exact absurd h_eq ( ne_of_gt ( qi_lt_of_lt n r j k hr1 hrn ‹_› ‹_› ) );
  · exact absurd h_eq ( ne_of_lt ( qi_lt_of_lt n r k j hr1 hrn ‹_› ‹_› ) )

/-
`|E| = h_r`.
-/
theorem Esel_card (n r : ℕ) : (Esel n r).card = hr r := by
  -- The cardinality of the union of $I_{\text{zero}}$ and $[h_r, h_r+h_+)$ is $h_r - h_+ + h_+ = h_r$.
  have h_union_card : (Izero n r).card + (Finset.Ico (hr r) (hr r + hplus n r)).card = hr r := by
    simp +arith +decide [ Izero, Iplus, hplus ];
    rw [ add_comm, Finset.card_filter_add_card_filter_not ] ; aesop;
  rw [ ← h_union_card, show Esel n r = Izero n r ∪ Finset.Ico ( hr r ) ( hr r + hplus n r ) from rfl, Finset.card_union_of_disjoint ];
  exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Ico.mp hx₂, Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ) ] ;

/-
`Q_r(n)` is squarefree.
-/
theorem Qr_squarefree (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) :
    Squarefree (Qr n r) := by
  -- The product of a finset of distinct primes is squarefree.
  have h_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) : Squarefree (∏ p ∈ s, p) := by
    induction s using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ];
    exact ⟨ Nat.Coprime.prod_right fun p hp => hs.1.coprime_iff_not_dvd.mpr fun h => by have := Nat.prime_dvd_prime_iff_eq hs.1 ( hs.2 p hp ) ; aesop, hs.1.squarefree ⟩;
  convert! h_prod_squarefree ( ( Esel n r ).image ( qi n r ) ) _ using 1;
  · rw [ Finset.prod_image ];
    · rfl;
    · grind +suggestions;
  · rintro p hp; obtain ⟨ j, hj, rfl ⟩ := Finset.mem_image.mp hp; exact qi_prime n r j hr1 hrn ( Esel_lt_sr n r j hj ) ;

/-
`ω(Q_r(n)) = h_r`.
-/
theorem Qr_omega (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) :
    omegaCount (Qr n r) = hr r := by
  -- By definition of `qi`, we know that each `qi n r j` is a prime factor of `n`.
  have h_prime_factors : (Qr n r).primeFactors = (Esel n r).image (qi n r) := by
    convert! Nat.primeFactors_prod _;
    · rw [ Finset.prod_image ];
      · rfl;
      · exact qi_injOn_Esel n r hr1 hrn;
    · simp +zetaDelta at *;
      exact fun x hx => qi_prime n r x hr1 hrn ( Esel_lt_sr n r x hx );
  convert! congr_arg Finset.card h_prime_factors using 1;
  rw [ Finset.card_image_of_injOn ( qi_injOn_Esel n r hr1 hrn ), Esel_card ]

/-
`Q_r(n) ∣ n`.
-/
theorem Qr_dvd (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (_hn0 : n ≠ 0) :
    Qr n r ∣ n := by
  refine' Nat.dvd_trans _ ( Nat.prod_primeFactors_dvd n );
  have h_prod_dvd : ∏ p ∈ (Finset.image (fun j => qi n r j) (Esel n r)), p ∣ ∏ p ∈ n.primeFactors, p := by
    apply_rules [ Finset.prod_dvd_prod_of_subset ];
    exact Finset.image_subset_iff.mpr fun j hj => qi_mem_primeFactors n r j hr1 hrn ( Esel_lt_sr n r j hj );
  rwa [ Finset.prod_image ( by exact fun x hx y hy hxy => by have := qi_injOn_Esel n r hr1 hrn; aesop ) ] at h_prod_dvd

/-! ### Homogeneity consequences (row structure vs. witnesses) -/

/-
`step n S ⊆ S`.
-/
theorem step_subset (n : ℕ) (S : Finset ℕ) : step n S ⊆ S := by
  unfold step;
  grind

/-
The selection sets are antitone in the step index.
-/
theorem Siter_antitone (n r k l : ℕ) (hkl : k ≤ l) :
    Siter n (topR n r) l ⊆ Siter n (topR n r) k := by
  induction hkl <;> simp_all +decide [ Siter ];
  exact Finset.Subset.trans ( step_subset _ _ ) ‹_›

/-
`q_j ∈ S_j` for `j < s_r`.
-/
theorem qi_mem_Siter (n r j : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hj : j < sr r) :
    qi n r j ∈ Siter n (topR n r) j := by
  obtain ⟨q, hq⟩ : ∃ q, q ∈ Siter n (topR n r) j ∧ ∀ p ∈ Siter n (topR n r) j, p ≤ q := by
    refine' ⟨ Finset.max' _ _, Finset.max'_mem _ _, fun p hp => Finset.le_max' _ _ hp ⟩;
    have := Siter_card_ge n r j hr1 hrn ( by linarith [ show j ≤ Nat.log 2 r from Nat.le_of_lt_succ ( by linarith [ show sr r = 1 + Nat.log 2 r from rfl ] ) ] ) ; exact Finset.card_pos.mp ( lt_of_lt_of_le ( by positivity ) this ) ;
  unfold qi;
  unfold qsel;
  rw [ Finset.max_eq_sup_coe ];
  rw [ show ( Siter n ( topR n r ) j ).sup WithBot.some = ↑q from ?_ ];
  · exact hq.1;
  · exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr ( hq.2 x hx ) ) ( Finset.le_sup ( f := WithBot.some ) hq.1 )

/-
In a zero row `i`, no later selected prime divides the witness `D_{q_i}`.
-/
theorem zero_row_later_not_dvd (n r i j : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hij : i < j) (hj : j < sr r) (hzero : ¬ rowPos n r i) :
    ¬ qi n r j ∣ Dwit n (qi n r i) := by
  -- Since `i < sr r`, we have `i < sr r`, so `Siter n (topR n r) i` is nonempty.
  have hi_ne : (Siter n (topR n r) i).Nonempty := by
    exact Set.nonempty_of_mem ( qi_mem_Siter n r i hr1 hrn ( by linarith ) );
  unfold rowPos at hzero; simp_all +decide ;
  -- Since `Siter n (topR n r) j ⊆ Siter n (topR n r) (i+1)`, we have `qi n r j ∈ Siter n (topR n r) (i+1)`.
  have h_mem : qi n r j ∈ Siter n (topR n r) (i + 1) := by
    exact Siter_antitone _ _ _ _ ( by linarith ) ( qi_mem_Siter _ _ _ hr1 hrn hj );
  have h_mem : qi n r j ∈ step n (Siter n (topR n r) i) := by
    exact h_mem;
  unfold step at h_mem; simp_all +decide ;
  have h_mem : qi n r i = (Siter n (topR n r) i).max' hi_ne := by
    unfold qi qsel;
    rw [ Finset.max_eq_sup_coe ];
    rw [ show ( Siter n ( topR n r ) i ).sup WithBot.some = WithBot.some ( Finset.max' _ hi_ne ) from ?_ ];
    · rfl;
    · exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr <| Finset.le_max' _ _ hx ) ( Finset.le_sup ( f := WithBot.some ) <| Finset.max'_mem _ hi_ne );
  split_ifs at * <;> simp_all +decide [ Finset.mem_erase, Finset.mem_filter ];
  linarith

/-
In a positive row `i`, every later selected prime divides the witness `D_{q_i}`.
-/
theorem pos_row_later_dvd (n r i j : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hij : i < j) (hj : j < sr r) (hpos : rowPos n r i) :
    qi n r j ∣ Dwit n (qi n r i) := by
  unfold rowPos at hpos;
  have h_step : step n (Siter n (topR n r) i) = ((Siter n (topR n r) i).erase (qi n r i)).filter (fun z => z ∣ Dwit n (qi n r i)) := by
    unfold step;
    have h_max : (Siter n (topR n r) i).Nonempty := by
      contrapose! hpos; aesop;
    have h_max_eq : (Siter n (topR n r) i).max' h_max = qi n r i := by
      have h_max_eq : (Siter n (topR n r) i).max' h_max = (Siter n (topR n r) i).max.getD 0 := by
        rw [ Finset.max_eq_sup_coe ];
        rw [ show ( Siter n ( topR n r ) i ).sup WithBot.some = ↑ ( Finset.max' ( Siter n ( topR n r ) i ) h_max ) from ?_ ];
        · rfl;
        · exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr <| Finset.le_max' _ _ hx ) ( Finset.le_sup ( f := WithBot.some ) <| Finset.max'_mem _ h_max );
      exact h_max_eq;
    aesop;
  have h_mem_step : qi n r j ∈ step n (Siter n (topR n r) i) := by
    apply Siter_antitone n r (i + 1) j (by linarith) (qi_mem_Siter n r j hr1 hrn hj);
  aesop

/-! ### Record data and the zero-row recovery formula -/

/-- Visibility record: `b_j = q_j` if `q_j ∣ m`, else `0`. -/
noncomputable def bvec (n r m j : ℕ) : ℕ := if qi n r j ∣ m then qi n r j else 0

/-- The `m`-part of the witness: `a_i = gcd(D_{q_i}, m)`. -/
noncomputable def avec (n r m i : ℕ) : ℕ := Nat.gcd (Dwit n (qi n r i)) m

/-- Valuation-excess bits: `ε_{i,k} = v_{q_k}(D_{q_i}) - v_{q_k}(a_i)`. -/
noncomputable def epsv (n r m i k : ℕ) : ℕ :=
  (Dwit n (qi n r i)).factorization (qi n r k) - (avec n r m i).factorization (qi n r k)

/-
The prime factors of `Q_r(n)` are exactly `{q_j : j ∈ E}`.
-/
theorem Qr_primeFactors (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) :
    (Qr n r).primeFactors = (Esel n r).image (qi n r) := by
  have h_image : Qr n r = ∏ j ∈ Esel n r, qi n r j := by
    rfl;
  have h_prime_factors : ∀ {S : Finset ℕ}, (∀ j ∈ S, (qi n r j).Prime) → (∏ j ∈ S, qi n r j).primeFactors = S.image (fun j => qi n r j) := by
    intros S hS; induction S using Finset.induction <;> simp_all +decide ;
    rw [ Nat.primeFactors_mul, ‹ ( ∏ j ∈ _, qi n r j |> Nat.primeFactors ) = _ › ] <;> simp_all +decide [ Nat.Prime.ne_zero, Finset.prod_eq_zero_iff ];
  exact h_image.symm ▸ h_prime_factors fun j hj => qi_prime n r j hr1 hrn ( Esel_lt_sr n r j hj )

/-
`n = m * Q_r(n)` when `m = n / Q_r(n)`.
-/
theorem n_eq_m_mul_Qr (n r m : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hn0 : n ≠ 0)
    (hm : m = n / Qr n r) : n = m * Qr n r := by
  rw [ hm, Nat.div_mul_cancel ( Qr_dvd n r hr1 hrn hn0 ) ]

/-
For a zero row `i`, the valuation-excess bit vanishes at every deleted slot
`k ≥ i`.
-/
theorem epsv_zero_of_ge (n r m i k : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hi : i < hr r) (hzero : ¬ rowPos n r i)
    (hk : k ∈ Esel n r) (hik : i ≤ k) : epsv n r m i k = 0 := by
  refine' Nat.sub_eq_zero_of_le _;
  by_cases h : qi n r k ∣ Dwit n ( qi n r i ) <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
  by_cases hik' : i < k;
  · exact absurd h ( zero_row_later_not_dvd n r i k ( by linarith ) hrn hik' ( by linarith [ Esel_lt_sr n r k hk ] ) hzero );
  · cases eq_or_lt_of_le hik <;> simp_all +decide;
    exact absurd h ( Dwit_not_dvd n ( qi n r k ) hn ( qi_prime n r k ( by linarith ) hrn ( by linarith [ two_hr_le_sr r ] ) ) ( qi_dvd n r k ( by linarith ) hrn ( by linarith [ two_hr_le_sr r ] ) ) hn0 )

/-
**Zero-row recovery formula (Lemma 8.3).**  For a zero row `i` (`i < h_r`,
`¬ rowPos`), the witness of `q_i` is determined by its `m`-part and the
earlier deleted primes.
-/
theorem zero_row_recovery (n r m i : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i < hr r) (hzero : ¬ rowPos n r i) :
    Dwit n (qi n r i)
      = avec n r m i * ∏ k ∈ (Esel n r).filter (· < i), (qi n r k) ^ (epsv n r m i k) := by
  have h_val : Nat.gcd (Dwit n (qi n r i)) m * ∏ k ∈ Esel n r, qi n r k ^ epsv n r m i k = Dwit n (qi n r i) := by
    have := valuation_bit (Qr n r) m (Dwit n (qi n r i)) (Qr_squarefree n r (by linarith) (by linarith)) (by
    linarith [ Nat.div_pos ( show n ≥ Qr n r from Nat.le_of_dvd ( Nat.pos_of_ne_zero hn0 ) ( Qr_dvd n r ( by linarith ) ( by linarith ) ( by aesop ) ) ) ( Nat.pos_of_ne_zero ( show Qr n r ≠ 0 from Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by intros h; have := Qr_squarefree n r ( by linarith ) ( by linarith ) ; aesop ) ) ]) (by
    rw [ hm, Nat.div_mul_cancel ];
    · exact Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) hrn ( by linarith [ hr2, hrn, hi, hr r, sr r, two_hr_le_sr r ] ) ) ( qi_dvd n r i ( by linarith ) hrn ( by linarith [ hr2, hrn, hi, hr r, sr r, two_hr_le_sr r ] ) ) hn0 |>.1;
    · exact Qr_dvd n r ( by linarith ) ( by linarith ) hn0) (by
    exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) ( by linarith [ show hr r ≤ sr r from Nat.div_le_self _ _ ] ) ) ( qi_dvd n r i ( by linarith ) ( by linarith ) ( by linarith [ show hr r ≤ sr r from Nat.div_le_self _ _ ] ) ) hn0 |>.1 ) ( Nat.pos_of_ne_zero hn0 ) ));
    rw [ Qr_primeFactors n r ( by linarith ) ( by linarith ), Finset.prod_image ] at this;
    · exact this.2.symm;
    · exact qi_injOn_Esel n r ( by linarith ) ( by linarith );
  convert! h_val.symm using 2;
  refine' Finset.prod_subset _ _ <;> intro k hk <;> simp_all +decide;
  exact fun h => Or.inr <| epsv_zero_of_ge n r ( n / Qr n r ) i k hn hr2 hrn hn0 hi hzero hk h

/-! ### Positive rows and the common suffix product `P` -/

/-- Hidden exact suffix slots. -/
noncomputable def Fsel (n r m : ℕ) : Finset ℕ :=
  (Finset.Ico (hr r) (hr r + hplus n r)).filter (fun f => ¬ qi n r f ∣ m)

/-- The common suffix product `P = ∏_{f∈F} q_f`. -/
noncomputable def Pval (n r m : ℕ) : ℕ := ∏ f ∈ Fsel n r m, qi n r f

/-- The per-row cofactor `C_i = a_i · ∏_{k∈E\F} q_k^{ε_{i,k}}`. -/
noncomputable def Cval (n r m i : ℕ) : ℕ :=
  avec n r m i * ∏ k ∈ (Esel n r) \ (Fsel n r m), (qi n r k) ^ (epsv n r m i k)

/-- `R = ∏_{i∈I₊} q_i`. -/
noncomputable def Rval (n r : ℕ) : ℕ := ∏ i ∈ Iplus n r, qi n r i

/-
The factorization of `Q_r(n)` at a selected prime `q_k` (`k∈E`) is `1`.
-/
theorem vQr_eq_one (n r k : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hk : k ∈ Esel n r) :
    (Qr n r).factorization (qi n r k) = 1 := by
  convert! Nat.factorization_eq_one_of_squarefree _ _ _;
  · exact Qr_squarefree n r hr1 hrn;
  · exact qi_prime n r k hr1 hrn ( Esel_lt_sr n r k hk );
  · exact Finset.dvd_prod_of_mem _ hk

/-
Valuation transfer: `v_{q_k}(n) = v_{q_k}(m) + 1` for `k∈E`.
-/
theorem vn_eq (n r m k : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hn0 : n ≠ 0)
    (hm : m = n / Qr n r) (hk : k ∈ Esel n r) :
    n.factorization (qi n r k) = m.factorization (qi n r k) + 1 := by
  convert! congr_arg ( fun x : ℕ => x.factorization ( qi n r k ) ) ( n_eq_m_mul_Qr n r m hr1 hrn hn0 hm ) using 1;
  rw [ Nat.factorization_mul ] <;> norm_num [ hn0, hm, Qr_squarefree ];
  · rw [ vQr_eq_one n r k hr1 hrn hk ];
  · exact ⟨ Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( Qr_dvd n r hr1 hrn hn0 ) ( Nat.pos_of_ne_zero hn0 ) ), Nat.le_of_dvd ( Nat.pos_of_ne_zero hn0 ) ( Qr_dvd n r hr1 hrn hn0 ) ⟩;
  · exact Finset.prod_ne_zero_iff.mpr fun x hx => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors <| qi_mem_primeFactors n r x hr1 hrn <| Esel_lt_sr n r x hx

/-
The general witness factorization: `D_{q_i} = a_i · ∏_{k∈E} q_k^{ε_{i,k}}`.
-/
theorem Dwit_prod_eq (n r m i : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i < sr r) :
    Dwit n (qi n r i) = avec n r m i * ∏ k ∈ Esel n r, (qi n r k) ^ (epsv n r m i k) := by
  convert! valuation_bit _ _ _ _ _ _ _ |> And.right using 1;
  rotate_left;
  exact Qr n r;
  exact m;
  · exact Qr_squarefree n r ( by linarith ) ( by linarith );
  · exact hm.symm ▸ Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn0 ) ( Qr_dvd n r ( by linarith ) ( by linarith ) hn0 ) ) ( Nat.pos_of_ne_zero ( by
      exact Finset.prod_ne_zero_iff.mpr fun x hx => Nat.Prime.ne_zero ( qi_prime n r x ( by linarith ) ( by linarith ) ( by linarith [ Esel_lt_sr n r x hx ] ) ) ) ) );
  · convert! Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) hi ) ( qi_dvd n r i ( by linarith ) ( by linarith ) hi ) hn0 |> And.left using 1;
    rw [ hm, Nat.div_mul_cancel ( Qr_dvd n r ( by linarith ) ( by linarith ) hn0 ) ];
  · exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) hi ) ( qi_dvd n r i ( by linarith ) ( by linarith ) hi ) hn0 |>.1 ) ( Nat.pos_of_ne_zero hn0 ) );
  · rw [ Qr_primeFactors ];
    · rw [ Finset.prod_image ];
      · rfl;
      · exact qi_injOn_Esel n r ( by linarith ) ( by linarith );
    · linarith;
    · linarith

/-
For a positive row `i` and a hidden exact suffix slot `f`, the excess bit is `1`.
-/
theorem epsv_one_of_F (n r m i f : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i ∈ Iplus n r) (hf : f ∈ Fsel n r m) :
    epsv n r m i f = 1 := by
  refine' tsub_eq_of_eq_add _;
  have h_factorization_D : (Dwit n (qi n r i)).factorization (qi n r f) = 1 := by
    have h_factorization_Dwit : qi n r f ∣ Dwit n (qi n r i) := by
      apply pos_row_later_dvd n r i f (by linarith) (by linarith) (by
      simp_all +decide [ Fsel, Iplus ];
      linarith) (by
      exact Esel_lt_sr n r f ( Finset.mem_union_right _ ( Finset.mem_Ico.mpr ⟨ Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ) |>.1, Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ) |>.2 ⟩ ) )) (by
      exact Finset.mem_filter.mp hi |>.2);
    have h_factorization_Dwit_le : (Dwit n (qi n r i)).factorization (qi n r f) ≤ 1 := by
      have h_factorization_Dwit_le : (Dwit n (qi n r i)).factorization (qi n r f) ≤ (n.factorization (qi n r f)) := by
        have h_factorization_Dwit_le : Dwit n (qi n r i) ∣ n := by
          apply (Dwit_spec n (qi n r i) hn (qi_prime n r i (by linarith) (by linarith) (by
          exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ))) (qi_dvd n r i (by linarith) (by linarith) (by
          exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ))) hn0).left;
        exact Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 h_factorization_Dwit_le _;
      have h_factorization_m : m.factorization (qi n r f) = 0 := by
        exact Nat.factorization_eq_zero_of_not_dvd fun h => Finset.mem_filter.mp hf |>.2 h;
      linarith [ vn_eq n r m f ( by linarith ) ( by linarith ) hn0 hm ( by
        exact Finset.mem_union_right _ ( Finset.mem_Ico.mpr ⟨ by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ) ], by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ) ] ⟩ ) ) ];
    refine' le_antisymm h_factorization_Dwit_le ( Nat.pos_of_ne_zero _ );
    simp_all +decide [ Nat.factorization_eq_zero_iff ];
    exact ⟨ qi_prime n r f ( by linarith ) ( by linarith ) ( by
      exact Esel_lt_sr n r f ( Finset.mem_union_right _ ( Finset.mem_Ico.mpr ⟨ by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ) ], by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hf |>.1 ), hplus_le_hr n r ] ⟩ ) ) ), by
      exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) ( by
        exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) ) ) ( qi_dvd n r i ( by linarith ) ( by linarith ) ( by
        exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) ) ) hn0 |>.1 ) ( Nat.pos_of_ne_zero hn0 ) ) ⟩;
  simp_all +decide [ Fsel ];
  exact Nat.factorization_eq_zero_of_not_dvd ( fun h => hf.2 <| Nat.dvd_trans h <| Nat.gcd_dvd_right _ _ )

/-
**Positive-row common product (Lemma 8.4).**  For a positive row `i`,
`D_{q_i} = P · C_i`.
-/
theorem positive_common_product (n r m i : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r)
    (hrn : r ≤ omegaCount n) (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i ∈ Iplus n r) :
    Dwit n (qi n r i) = Pval n r m * Cval n r m i := by
  convert! Dwit_prod_eq n r m i hn hr2 hrn hn0 hm _ using 1;
  · rw [ ← Finset.prod_sdiff <| show Fsel n r m ⊆ Esel n r from ?_ ];
    · simp +decide [ Pval, Cval, mul_comm, mul_left_comm ];
      exact Or.inl <| Or.inl <| Finset.prod_congr rfl fun x hx => by rw [ epsv_one_of_F n r m i x hn hr2 hrn hn0 hm hi hx ] ; norm_num;
    · exact fun x hx => Finset.mem_union_right _ <| Finset.mem_Ico.mpr ⟨ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ⟩;
  · exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ )

/-
`q_i` is coprime to its cofactor `C_i` for positive rows.
-/
theorem Cval_coprime (n r m i : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i ∈ Iplus n r) :
    Nat.Coprime (Cval n r m i) (qi n r i) := by
  refine' Nat.Coprime.symm ( Nat.Prime.coprime_iff_not_dvd ( qi_prime n r i ( by linarith ) ( by linarith ) ( by
    exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) |> lt_of_lt_of_le <| Nat.le_refl _ ) ) |>.2 _ );
  refine' Nat.Prime.not_dvd_mul ( qi_prime n r i ( by linarith ) ( by linarith ) ( by
    exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) |> lt_of_lt_of_le <| Nat.le_refl _ ) ) _ _;
  · refine' fun h => _;
    exact Dwit_not_dvd n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) ( by
      exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) ) ) ( qi_dvd n r i ( by linarith ) ( by linarith ) ( by
      exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) ) ) hn0 ( Nat.dvd_trans h ( Nat.gcd_dvd_left _ _ ) );
  · rw [ Nat.Prime.dvd_iff_not_coprime ] <;> norm_num;
    · refine' Nat.Coprime.prod_right fun k hk => _;
      by_cases hik : i = k;
      · simp_all +decide [ Iplus, Izero, Esel ];
        linarith;
      · refine' Nat.Coprime.pow_right _ _;
        have h_distinct : ∀ j k, j < sr r → k < sr r → j ≠ k → qi n r j ≠ qi n r k := by
          intros j k hj hk hneq;
          cases lt_or_gt_of_ne hneq <;> [ exact ne_of_gt ( qi_lt_of_lt n r j k ( by linarith ) ( by linarith ) ‹_› ‹_› ) ; exact ne_of_lt ( qi_lt_of_lt n r k j ( by linarith ) ( by linarith ) ‹_› ‹_› ) ];
        exact Nat.coprime_iff_gcd_eq_one.mpr ( by have := h_distinct i k ( by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ), two_hr_le_sr r ] ) ( by linarith [ Esel_lt_sr n r k ( Finset.mem_sdiff.mp hk |>.1 ), two_hr_le_sr r ] ) hik; have := Nat.coprime_primes ( qi_prime n r i ( by linarith ) ( by linarith ) ( by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ), two_hr_le_sr r ] ) ) ( qi_prime n r k ( by linarith ) ( by linarith ) ( by linarith [ Esel_lt_sr n r k ( Finset.mem_sdiff.mp hk |>.1 ), two_hr_le_sr r ] ) ) ; tauto );
    · exact qi_prime n r i ( by linarith ) ( by linarith ) ( by
        exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) |> lt_of_lt_of_le <| Nat.le_refl _ )

/-! ### Branch index `κ` and size bounds -/

/-- Branch index: position of `q_i` among the sorted prime divisors of `D_{q_i}-1`. -/
noncomputable def kappav (n r i : ℕ) : ℕ :=
  ((Dwit n (qi n r i) - 1).primeFactors.sort (· ≤ ·)).idxOf (qi n r i)

/-
`q_i` divides `D_{q_i} - 1`.
-/
theorem qi_dvd_Dwit_sub_one (n r i : ℕ) (hn : n ∈ Acal) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hi : i < sr r) : qi n r i ∣ Dwit n (qi n r i) - 1 := by
  obtain ⟨d, hd⟩ := Dwit_spec n (qi n r i) hn (qi_prime n r i hr1 hrn hi) (qi_dvd n r i hr1 hrn hi) hn0;
  exact ⟨ Dwit n ( qi n r i ) / qi n r i, Nat.sub_eq_of_eq_add <| by linarith [ Nat.mod_add_div ( Dwit n ( qi n r i ) ) ( qi n r i ) ] ⟩

/-
`q_i` is recovered from `D_{q_i}` and the branch index.
-/
theorem kappa_recovery (n r i : ℕ) (hn : n ∈ Acal) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hi : i < sr r) :
    qi n r i = ((Dwit n (qi n r i) - 1).primeFactors.sort (· ≤ ·)).getD (kappav n r i) 0 := by
  by_cases h : ( ( Dwit n ( qi n r i ) - 1 ).primeFactors.sort fun x1 x2 => x1 ≤ x2 ).idxOf ( qi n r i ) < ( ( Dwit n ( qi n r i ) - 1 ).primeFactors.sort fun x1 x2 => x1 ≤ x2 ).length <;> simp_all +decide;
  · convert! List.getElem_idxOf _ |> Eq.symm using 1;
    convert! List.getD_eq_getElem _ _ _ using 1;
    · aesop;
    · infer_instance;
  · contrapose! h;
    convert! List.idxOf_lt_length_iff.mpr _ using 1;
    · norm_num;
    · infer_instance;
    · convert! Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 _ using 1;
      exact Nat.mem_primeFactors.mpr ⟨ qi_prime n r i hr1 hrn hi, Nat.dvd_of_mod_eq_zero ( by rw [ Nat.mod_eq_zero_of_dvd ] ; exact qi_dvd_Dwit_sub_one n r i hn hr1 hrn hn0 hi ), Nat.sub_ne_zero_of_lt ( by linarith [ Dwit_spec n ( qi n r i ) hn ( qi_prime n r i hr1 hrn hi ) ( qi_dvd n r i hr1 hrn hi ) hn0 ] ) ⟩

/-
`P ≥ 1`.
-/
theorem one_le_Pval (n r m : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) : 1 ≤ Pval n r m := by
  refine' Finset.one_le_prod' _;
  intro i hi; exact Nat.Prime.pos ( qi_prime n r i hr1 hrn ( by
    exact Esel_lt_sr n r i ( Finset.mem_union_right _ ( Finset.mem_filter.mp hi |>.1 ) ) ) ) ;

/-
`P < R` whenever there is at least one positive row.
-/
theorem Pval_lt_Rval (n r m : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hne : (Iplus n r).Nonempty) : Pval n r m < Rval n r := by
  -- Let `a = qi n r iM` where `iM = (Iplus n r).max' hne` (the smallest positive-row prime).
  obtain ⟨iM, hiM⟩ : ∃ iM, iM ∈ Iplus n r ∧ ∀ i ∈ Iplus n r, i ≤ iM := by
    exact ⟨ Finset.max' _ hne, Finset.max'_mem _ hne, fun i hi => Finset.le_max' _ _ hi ⟩
  set a := qi n r iM
  have ha_prime : Nat.Prime a := by
    apply qi_prime n r iM hr1 hrn (by
    exact Finset.mem_range.mp ( Finset.mem_filter.mp hiM.1 |>.1 ) |> lt_of_lt_of_le <| by linarith [ show hr r ≤ sr r from by linarith [ two_hr_le_sr r ] ] ;)
  have ha_ge_two : 2 ≤ a := by
    exact ha_prime.two_le;
  -- Now chain: `Pval n r m ≤ (a-1)^(Fsel).card ≤ (a-1)^(Iplus).card < a^(Iplus).card ≤ Rval n r`.
  have h_chain : Pval n r m ≤ (a - 1) ^ (Fsel n r m).card ∧ (a - 1) ^ (Fsel n r m).card ≤ (a - 1) ^ (Iplus n r).card ∧ (a - 1) ^ (Iplus n r).card < a ^ (Iplus n r).card ∧ a ^ (Iplus n r).card ≤ Rval n r := by
    refine' ⟨ _, _, _, _ ⟩;
    · have hP_le : ∀ f ∈ Fsel n r m, qi n r f ≤ a - 1 := by
        intros f hf
        have h_f_lt_a : qi n r f < a := by
          apply qi_lt_of_lt n r iM f hr1 hrn;
          · grind +locals;
          · exact Esel_lt_sr n r f ( Finset.mem_union_right _ ( Finset.mem_filter.mp hf |>.1 ) )
        exact Nat.le_sub_one_of_lt h_f_lt_a;
      exact le_trans ( Finset.prod_le_prod' hP_le ) ( by norm_num );
    · exact Nat.pow_le_pow_right ( Nat.sub_pos_of_lt ha_ge_two ) ( by simpa using! Finset.card_le_card ( show Fsel n r m ⊆ Finset.Ico ( hr r ) ( hr r + hplus n r ) from Finset.filter_subset _ _ ) |> le_trans <| by simp +decide [ hplus ] );
    · gcongr ; omega;
    · have h_prod_ge_a_pow : ∀ i ∈ Iplus n r, qi n r i ≥ a := by
        intros i hi
        have h_le : i ≤ iM := hiM.right i hi
        have h_lt : i < sr r := by
          exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ )
        have h_lt_iM : iM < sr r := by
          exact Finset.mem_range.mp ( Finset.mem_filter.mp hiM.1 |>.1 ) |> lt_of_lt_of_le <| by linarith [ show hr r ≤ sr r from by exact Nat.div_le_self _ _ ] ;
        exact (by
        exact if h : i = iM then h.symm ▸ le_rfl else le_of_lt ( qi_lt_of_lt n r i iM hr1 hrn ( lt_of_le_of_ne h_le h ) h_lt_iM ));
      exact le_trans ( by norm_num ) ( Finset.prod_le_prod' h_prod_ge_a_pow );
  linarith

/-! ### Injectivity of the record map -/

/-
`I₀ = range h \ I₊`.
-/
theorem Izero_eq_sdiff (n r : ℕ) : Izero n r = Finset.range (hr r) \ Iplus n r := by
  unfold Izero Iplus; ext; aesop;

/-
`E` depends only on `I₊`.
-/
theorem Esel_congr (n n' r : ℕ) (hIp : Iplus n r = Iplus n' r) : Esel n r = Esel n' r := by
  unfold Esel;
  simp_all +decide [ Izero, hplus ];
  unfold Iplus at hIp;
  simp_all +decide [ Finset.ext_iff ];
  grind

/-
`F` depends only on `I₊` and the visibility record `b`.
-/
theorem Fsel_congr (n n' r m : ℕ) (hr2 : 2 ≤ r) (_hrn : r ≤ omegaCount n) (hrn' : r ≤ omegaCount n')
    (hIp : Iplus n r = Iplus n' r) (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j) :
    Fsel n r m = Fsel n' r m := by
  unfold Fsel;
  simp_all +decide [ Finset.ext_iff ];
  intro a; specialize hb a; simp_all +decide [ bvec ] ;
  by_cases ha : a < sr r <;> simp_all +decide [ hplus ];
  · split_ifs at hb <;> simp_all +decide;
    · exact absurd hb.symm ( Nat.Prime.ne_zero ( qi_prime n' r a ( by linarith ) ( by linarith ) ( by linarith ) ) );
    · exact fun h => by rw [ show Iplus n r = Iplus n' r from Finset.ext hIp ] ;
  · have h_card : (Iplus n r).card ≤ hr r ∧ (Iplus n' r).card ≤ hr r := by
      exact ⟨ hplus_le_hr n r, hplus_le_hr n' r ⟩;
    have h_eq : a ≥ hr r + hr r := by
      exact le_trans ( by linarith [ two_hr_le_sr r ] ) ha;
    grind

/-
**Reconstruction of the non-suffix primes.**  Under equality of all record
coordinates, every deleted non-suffix prime is determined.
-/
theorem qi_recon_eq (n n' r m t : ℕ)
    (hn : n ∈ Acal) (hn' : n' ∈ Acal) (hr2 : 2 ≤ r) (ht : omegaCount n = t) (ht' : omegaCount n' = t)
    (hrt : r ≤ t) (hn0 : n ≠ 0) (hn0' : n' ≠ 0)
    (hmn : m = n / Qr n r) (hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r)
    (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (ha : ∀ i, i < hr r → avec n r m i = avec n' r m i)
    (he : ∀ i k, i < hr r → k ∈ Esel n r → epsv n r m i k = epsv n' r m i k)
    (hkap : ∀ i, i < hr r → kappav n r i = kappav n' r i) :
    ∀ k, k ∈ Esel n r → k ∉ Fsel n r m → qi n r k = qi n' r k := by
  intro k hk_mem hk_not_in_Fsel; induction' k using Nat.strong_induction_on with k ih; rcases lt_or_ge k ( hr r ) with hk_lt | hk_ge;
  · -- Apply the induction hypothesis to the product.
    have h_prod_eq : ∏ j ∈ (Esel n r).filter (· < k), (qi n r j) ^ (epsv n r m k j) = ∏ j ∈ (Esel n r).filter (· < k), (qi n' r j) ^ (epsv n' r m k j) := by
      refine' Finset.prod_congr rfl fun j hj => _;
      by_cases hj_in_Fsel : j ∈ Fsel n r m <;> simp_all +decide [ Fsel ];
      lia;
    -- Apply the induction hypothesis to the product and simplify.
    have h_simp : Dwit n (qi n r k) = Dwit n' (qi n' r k) := by
      convert! zero_row_recovery n r m k hn hr2 ( by linarith ) hn0 hmn hk_lt ( by
        grind +locals ) using 1;
      convert! zero_row_recovery n' r m k hn' hr2 ( by linarith ) hn0' hmn' hk_lt ( by
        unfold Esel at hk_mem; simp_all +decide [ Izero_eq_sdiff ] ;
        contrapose! hk_mem; simp_all +decide [ Iplus ] ; ) using 1;
      rw [ ha k hk_lt, h_prod_eq, Esel_congr n n' r hIp ];
    rw [ kappa_recovery n r k hn ( by linarith ) ( by linarith ) hn0 ( by linarith [ Esel_lt_sr n r k hk_mem ] ), kappa_recovery n' r k hn' ( by linarith ) ( by linarith ) hn0' ( by linarith [ Esel_lt_sr n r k hk_mem ] ) ] ; aesop ( simp_config := { singlePass := true } ) ;
  · -- Since $k \notin Fsel n r m$, we have $qi n r k \mid m$.
    have hk_div_m : qi n r k ∣ m := by
      grind +locals;
    specialize hb k ( Esel_lt_sr n r k hk_mem ) ; simp_all +decide [ bvec ] ;
    grind +suggestions

theorem qi_dvd_m_of_notMem (n r m i : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hn0 : n ≠ 0)
    (hm : m = n / Qr n r) (hi : i < sr r) (hni : i ∉ Esel n r) : qi n r i ∣ m := by
  have h_div_m : qi n r i ∣ n ∧ ¬ qi n r i ∣ Qr n r := by
    refine' ⟨ _, _ ⟩;
    · exact qi_dvd n r i hr1 hrn hi;
    · rw [ Nat.Prime.dvd_iff_not_coprime ];
      · rw [ Classical.not_not, Nat.coprime_comm ];
        refine' Nat.Coprime.prod_left _;
        intro j hj
        apply (Nat.coprime_primes (qi_prime n r j hr1 hrn (Esel_lt_sr n r j hj))
          (qi_prime n r i hr1 hrn hi)).mpr
        have hji : j ≠ i := fun h => hni (h ▸ hj)
        rcases lt_or_gt_of_ne hji with hlt | hlt
        · exact ne_of_gt (qi_lt_of_lt n r j i hr1 hrn hlt hi)
        · exact ne_of_lt (qi_lt_of_lt n r i j hr1 hrn hlt (Esel_lt_sr n r j hj))
      · exact qi_prime n r i hr1 hrn hi;
  rw [ hm, Nat.dvd_div_iff_mul_dvd ];
  · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( Nat.Coprime.symm <| Nat.Prime.coprime_iff_not_dvd ( qi_prime n r i hr1 hrn hi ) |>.2 h_div_m.2 ) ( Qr_dvd n r hr1 hrn hn0 ) h_div_m.1;
  · exact Qr_dvd n r hr1 hrn hn0

/-
On positive rows, the kept prime is determined by `b`.
-/
theorem qi_eq_Iplus (n n' r m : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hrn' : r ≤ omegaCount n')
    (hn0 : n ≠ 0) (hn0' : n' ≠ 0) (hmn : m = n / Qr n r) (hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r) (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (i : ℕ) (hi : i ∈ Iplus n r) : qi n r i = qi n' r i := by
  by_cases hi' : i < sr r <;> simp_all +decide [ bvec ];
  · have h_not_mem_Esel : i ∉ Esel n r ∧ i ∉ Esel n' r := by
      simp_all +decide [ Esel, Izero ];
      simp_all +decide [ Finset.ext_iff, Iplus ];
    grind +suggestions;
  · contrapose! hi';
    exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ )

theorem Cval_eq_Iplus (n n' r m : ℕ) (hr1 : 1 ≤ r) (_hrn : r ≤ omegaCount n) (hrn' : r ≤ omegaCount n')
    (hIp : Iplus n r = Iplus n' r) (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (ha : ∀ i, i < hr r → avec n r m i = avec n' r m i) (he : ∀ i k, i < hr r → k ∈ Esel n r → epsv n r m i k = epsv n' r m i k)
    (hqi : ∀ k, k ∈ Esel n r → k ∉ Fsel n r m → qi n r k = qi n' r k)
    (_hr2 : 2 ≤ r) (i : ℕ) (hi : i ∈ Iplus n r) : Cval n r m i = Cval n' r m i := by
  apply congr_arg₂ _ (ha i (by
  exact Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ))) (Finset.prod_bij (fun k hk => k) (by
  simp_all +decide;
  intro k hk hk'; rw [ Esel_congr n n' r hIp ] at *; simp_all +decide [ Fsel ] ;
  intro hk'' hk'''; specialize hqi k hk hk'; simp_all +decide [ bvec ] ;
  exact hk' ( by linarith [ show hplus n r = hplus n' r from by rw [ show hplus n r = ( Iplus n r ).card from rfl, show hplus n' r = ( Iplus n' r ).card from rfl, hIp ] ] )) (by
  grind) (by
  simp +zetaDelta at *;
  intro k hk hk'; rw [ Esel_congr n n' r hIp ] at *; simp_all +decide [ Fsel ] ;
  contrapose! hb;
  use k; simp_all +decide [ bvec ] ;
  exact ⟨ by linarith [ show hr r + hplus n r ≤ sr r from by linarith [ two_hr_le_sr r, hplus_le_hr n r ] ], hk' ( by linarith [ show hr r + hplus n r = hr r + hplus n' r from by rw [ show hplus n r = hplus n' r from by { unfold hplus; aesop } ] ] ), Ne.symm <| Nat.ne_of_gt <| Nat.Prime.pos <| qi_prime n' r k hr1 hrn' <| by linarith [ show hr r + hplus n r ≤ sr r from by linarith [ two_hr_le_sr r, hplus_le_hr n r ] ] ⟩) (by
  grind +locals))

theorem Pval_congr_mod (n n' r m : ℕ) (hn : n ∈ Acal) (hn' : n' ∈ Acal) (hr2 : 2 ≤ r)
    (hrn : r ≤ omegaCount n) (hrn' : r ≤ omegaCount n') (hn0 : n ≠ 0) (hn0' : n' ≠ 0)
    (hmn : m = n / Qr n r) (hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r) (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (ha : ∀ i, i < hr r → avec n r m i = avec n' r m i) (he : ∀ i k, i < hr r → k ∈ Esel n r → epsv n r m i k = epsv n' r m i k)
    (hqi : ∀ k, k ∈ Esel n r → k ∉ Fsel n r m → qi n r k = qi n' r k)
    (i : ℕ) (hi : i ∈ Iplus n r) :
    Nat.ModEq (qi n r i) (Pval n r m) (Pval n' r m) := by
  have hPcong_step : (Pval n r m * Cval n r m i) ≡ (Pval n' r m * Cval n' r m i) [MOD qi n r i] := by
    rw [ ← positive_common_product, ← positive_common_product ];
    any_goals assumption;
    · have hDwit_mod : Dwit n (qi n r i) ≡ 1 [MOD qi n r i] ∧ Dwit n' (qi n' r i) ≡ 1 [MOD qi n' r i] := by
        have hPcong_step : ∀ n r i, n ∈ Acal → 1 ≤ r → r ≤ omegaCount n → i < sr r → Dwit n (qi n r i) ≡ 1 [MOD qi n r i] := by
          intros n r i hn hr1 hrn hi
          have hDwit : Dwit n (qi n r i) ∣ n ∧ 1 < Dwit n (qi n r i) ∧ Dwit n (qi n r i) % (qi n r i) = 1 := by
            apply Dwit_spec n (qi n r i) hn (qi_prime n r i hr1 hrn hi) (qi_dvd n r i hr1 hrn hi) (by
            rintro rfl; simp_all +decide [ omegaCount ] ;)
          generalize_proofs at *; (
          rw [ ← hDwit.2.2, Nat.ModEq, Nat.mod_mod ])
        generalize_proofs at *; (
        apply And.intro (hPcong_step n r i hn (by linarith) hrn (by
        exact Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) |> lt_of_lt_of_le <| Nat.div_le_self _ _)) (hPcong_step n' r i hn' (by linarith) hrn' (by
        exact Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) |> lt_of_lt_of_le <| Nat.div_le_self _ _)));
      rw [ ← qi_eq_Iplus n n' r m ( by linarith ) hrn hrn' hn0 hn0' hmn hmn' hIp hb i hi ] at * ; simp_all +decide [ Nat.ModEq ];
    · exact hIp ▸ hi;
  have hCval_coprime : Nat.Coprime (Cval n r m i) (qi n r i) := by
    apply Cval_coprime n r m i hn hr2 hrn hn0 hmn hi;
  have hCval_eq : Cval n r m i = Cval n' r m i := by
    apply Cval_eq_Iplus n n' r m (by linarith) hrn hrn' hIp hb ha he hqi hr2 i hi;
  rw [ Nat.modEq_iff_dvd ] at *;
  simp_all +decide [ ← sub_mul ];
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hPcong_step hCval_coprime.symm

theorem Pval_eq (n n' r m t : ℕ)
    (hn : n ∈ Acal) (hn' : n' ∈ Acal) (hr2 : 2 ≤ r) (ht : omegaCount n = t) (ht' : omegaCount n' = t)
    (hrt : r ≤ t) (hn0 : n ≠ 0) (hn0' : n' ≠ 0)
    (hmn : m = n / Qr n r) (hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r)
    (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (ha : ∀ i, i < hr r → avec n r m i = avec n' r m i)
    (he : ∀ i k, i < hr r → k ∈ Esel n r → epsv n r m i k = epsv n' r m i k)
    (hqi : ∀ k, k ∈ Esel n r → k ∉ Fsel n r m → qi n r k = qi n' r k) :
    Pval n r m = Pval n' r m := by
  by_cases hIplus : (Iplus n r).Nonempty;
  · have hPval_congr : Pval n r m ≡ Pval n' r m [MOD Rval n r] := by
      have hPval_congr : ∀ i ∈ Iplus n r, Pval n r m ≡ Pval n' r m [MOD qi n r i] := by
        intros i hi;
        apply Pval_congr_mod n n' r m hn hn' hr2 (by
        grind) (by
        grind) hn0 hn0' hmn hmn' hIp hb ha he hqi i hi;
      have hPval_congr : ∀ i j, i ∈ Iplus n r → j ∈ Iplus n r → i ≠ j → Nat.Coprime (qi n r i) (qi n r j) := by
        intros i j hi hj hij
        have h_distinct : qi n r i ≠ qi n r j := by
          have h_distinct : StrictAntiOn (qi n r) (Iplus n r) := by
            intros i hi j hj hij;
            apply qi_lt_of_lt;
            · linarith;
            · grind;
            · exact hij;
            · exact Finset.mem_range.mp ( Finset.mem_filter.mp hj |>.1 ) |> lt_of_lt_of_le <| by unfold hr; unfold sr; omega;
          exact fun h => hij <| StrictAntiOn.injOn h_distinct hi hj h;
        have h_prime : Nat.Prime (qi n r i) ∧ Nat.Prime (qi n r j) := by
          exact ⟨ qi_prime n r i ( by linarith ) ( by linarith ) ( by
            exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hi |>.1 ) ) ( Nat.div_le_self _ _ ) ), qi_prime n r j ( by linarith ) ( by linarith ) ( by
            exact lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hj |>.1 ) ) ( by linarith [ show hr r ≤ sr r from by linarith [ two_hr_le_sr r ] ] ) ) ⟩;
        simpa [ h_distinct ] using! Nat.coprime_primes h_prime.1 h_prime.2;
      have hPval_congr : ∀ {S : Finset ℕ}, (∀ i ∈ S, Pval n r m ≡ Pval n' r m [MOD qi n r i]) → (∀ i j, i ∈ S → j ∈ S → i ≠ j → Nat.Coprime (qi n r i) (qi n r j)) → Pval n r m ≡ Pval n' r m [MOD ∏ i ∈ S, qi n r i] := by
        intros S hS hS_coprime; induction' S using Finset.induction with i S hiS ih; simp_all +decide [ Nat.modEq_iff_dvd ] ;
        rw [ Finset.prod_insert hiS ];
        rw [ ← Nat.modEq_and_modEq_iff_modEq_mul ];
        · exact ⟨ hS i ( Finset.mem_insert_self _ _ ), ih ( fun j hj => hS j ( Finset.mem_insert_of_mem hj ) ) ( fun j k hj hk hjk => hS_coprime j k ( Finset.mem_insert_of_mem hj ) ( Finset.mem_insert_of_mem hk ) hjk ) ⟩;
        · exact Nat.Coprime.prod_right fun j hj => hS_coprime i j ( Finset.mem_insert_self _ _ ) ( Finset.mem_insert_of_mem hj ) ( by rintro rfl; exact hiS hj );
      exact hPval_congr ‹_› ‹_›;
    have hPval_lt_Rval : Pval n r m < Rval n r ∧ Pval n' r m < Rval n r := by
      have hPval_lt_Rval : Pval n r m < Rval n r := by
        apply Pval_lt_Rval;
        · linarith;
        · linarith;
        · assumption
      have hPval_lt_Rval' : Pval n' r m < Rval n' r := by
        apply Pval_lt_Rval n' r m (by linarith) (by linarith) (by
        exact hIp ▸ hIplus)
      rw [show Rval n' r = Rval n r from by
            exact Finset.prod_congr hIp.symm fun i hi => by
              apply Eq.symm; exact (by
                have := qi_eq_Iplus n n' r m (by linarith) (by linarith) (by linarith) hn0 hn0' hmn hmn' hIp hb i hi;
                exact this)] at hPval_lt_Rval'
      exact ⟨hPval_lt_Rval, hPval_lt_Rval'⟩;
    exact Nat.mod_eq_of_lt hPval_lt_Rval.1 ▸ Nat.mod_eq_of_lt hPval_lt_Rval.2 ▸ hPval_congr;
  · unfold Pval; simp_all +decide [ Fsel ] ;
    unfold hplus at *; aesop;

/-
`F ⊆ E`.
-/
theorem Fsel_subset_Esel (n r m : ℕ) : Fsel n r m ⊆ Esel n r := by
  exact fun x hx => Finset.mem_union_right _ <| Finset.mem_filter.mp hx |>.1

/-- Under record equality, the deleted divisor `Q_r` is determined. -/
theorem Qr_eq_of_data (n n' r m t : ℕ)
    (_hn : n ∈ Acal) (_hn' : n' ∈ Acal) (hr2 : 2 ≤ r) (ht : omegaCount n = t) (ht' : omegaCount n' = t)
    (hrt : r ≤ t) (_hn0 : n ≠ 0) (_hn0' : n' ≠ 0)
    (_hmn : m = n / Qr n r) (_hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r)
    (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (_ha : ∀ i, i < hr r → avec n r m i = avec n' r m i)
    (hqi : ∀ k, k ∈ Esel n r → k ∉ Fsel n r m → qi n r k = qi n' r k)
    (hP : Pval n r m = Pval n' r m) : Qr n r = Qr n' r := by
  have hrn : r ≤ omegaCount n := ht ▸ hrt
  have hrn' : r ≤ omegaCount n' := ht' ▸ hrt
  have hEs : Esel n r = Esel n' r := Esel_congr n n' r hIp
  have hFs : Fsel n r m = Fsel n' r m := Fsel_congr n n' r m hr2 hrn hrn' hIp hb
  have e1 : (∏ k ∈ (Esel n r) \ (Fsel n r m), qi n r k) * (∏ k ∈ Fsel n r m, qi n r k) = Qr n r :=
    Finset.prod_sdiff (Fsel_subset_Esel n r m)
  have e2 : (∏ k ∈ (Esel n' r) \ (Fsel n' r m), qi n' r k) * (∏ k ∈ Fsel n' r m, qi n' r k)
      = Qr n' r := Finset.prod_sdiff (Fsel_subset_Esel n' r m)
  have hprodF : (∏ k ∈ Fsel n r m, qi n r k) = (∏ k ∈ Fsel n' r m, qi n' r k) := hP
  have hprodS : (∏ k ∈ (Esel n r) \ (Fsel n r m), qi n r k)
      = (∏ k ∈ (Esel n' r) \ (Fsel n' r m), qi n' r k) := by
    rw [← hEs, ← hFs]
    exact Finset.prod_congr rfl fun k hk =>
      hqi k (Finset.mem_sdiff.mp hk).1 (Finset.mem_sdiff.mp hk).2
  rw [← e1, ← e2, hprodS, hprodF]

/-
**Fiber injectivity.**  An element of the fixed-prefix fiber is determined by
its record `(I₊, b, a, ε, κ)`.
-/
theorem fiber_inj (n n' r m t : ℕ)
    (hn : n ∈ Acal) (hn' : n' ∈ Acal) (hr2 : 2 ≤ r) (ht : omegaCount n = t) (ht' : omegaCount n' = t)
    (hrt : r ≤ t) (hn0 : n ≠ 0) (hn0' : n' ≠ 0)
    (hmn : m = n / Qr n r) (hmn' : m = n' / Qr n' r)
    (hIp : Iplus n r = Iplus n' r)
    (hb : ∀ j, j < sr r → bvec n r m j = bvec n' r m j)
    (ha : ∀ i, i < hr r → avec n r m i = avec n' r m i)
    (he : ∀ i k, i < hr r → k ∈ Esel n r → epsv n r m i k = epsv n' r m i k)
    (hkap : ∀ i, i < hr r → kappav n r i = kappav n' r i) : n = n' := by
  have hqi := qi_recon_eq n n' r m t hn hn' hr2 ht ht' hrt hn0 hn0' hmn hmn' hIp hb ha he hkap
  have hP := Pval_eq n n' r m t hn hn' hr2 ht ht' hrt hn0 hn0' hmn hmn' hIp hb ha he hqi
  have hQr := Qr_eq_of_data n n' r m t hn hn' hr2 ht ht' hrt hn0 hn0' hmn hmn' hIp hb ha hqi hP
  rw [ n_eq_m_mul_Qr n r m ( by linarith ) ( ht ▸ hrt ) hn0 hmn,
    n_eq_m_mul_Qr n' r m ( by linarith ) ( ht' ▸ hrt ) hn0' hmn', hQr ]

/-! ### The fixed-prefix fiber bound (counting) -/

/-- The fixed-prefix fiber. -/
noncomputable def fixedFiber (x : ℝ) (t r m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ Acal ∧ omegaCount n = t ∧ n / Qr n r = m)

/-- The record-encoding map into a finite product type. -/
noncomputable def encRec (_x : ℝ) (r m : ℕ) (n : ℕ) :
    Finset ℕ × (Fin (sr r) → ℕ) × (Fin (hr r) → ℕ) × (Fin (hr r) → Fin (sr r) → ℕ) × (Fin (hr r) → ℕ) :=
  (Iplus n r,
   (fun j => bvec n r m j),
   (fun i => avec n r m i),
   (fun i k => if (k : ℕ) ∈ Esel n r then epsv n r m i k else 0),
   (fun i => kappav n r i))

/-- The finite target of the encoding. -/
noncomputable def encTarget (x : ℝ) (r m : ℕ) :
    Finset (Finset ℕ × (Fin (sr r) → ℕ) × (Fin (hr r) → ℕ) × (Fin (hr r) → Fin (sr r) → ℕ) × (Fin (hr r) → ℕ)) :=
  (Finset.range (hr r)).powerset ×ˢ
  (Fintype.piFinset fun _ => insert 0 m.primeFactors) ×ˢ
  (Fintype.piFinset fun _ => m.divisors) ×ˢ
  (Fintype.piFinset fun _ => Fintype.piFinset fun _ => ({0, 1} : Finset ℕ)) ×ˢ
  (Fintype.piFinset fun _ => Finset.range (Nat.log 2 ⌊x⌋₊ + 1))

/-
Cardinality of the encoding target.
-/
theorem encTarget_card (x : ℝ) (r m : ℕ) :
    (encTarget x r m).card
      = 2 ^ (hr r) * (1 + omegaCount m) ^ (sr r) * (tauCount m) ^ (hr r)
          * 2 ^ (hr r * sr r) * (1 + Nat.log 2 ⌊x⌋₊) ^ (hr r) := by
  unfold encTarget; simp +decide [ Fintype.card_fin ] ; ring;

/-
Each valuation-excess bit at a deleted slot is `≤ 1`.
-/
theorem epsv_le_one (n r m i k : ℕ) (hn : n ∈ Acal) (hr2 : 2 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hm : m = n / Qr n r) (hi : i < sr r) (hk : k ∈ Esel n r) :
    epsv n r m i k ≤ 1 := by
  apply (valuation_bit (Qr n r) m (Dwit n (qi n r i)) (Qr_squarefree n r (by linarith) hrn) (by
  rw [ hm, Ne.eq_def, Nat.div_eq_zero_iff ];
  exact not_or.mpr ⟨ Nat.ne_of_gt ( Finset.prod_pos fun x hx => Nat.Prime.pos ( qi_prime n r x ( by linarith ) ( by linarith ) ( by
    exact Esel_lt_sr n r x hx ) ) ), not_lt_of_ge ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn0 ) ( Qr_dvd n r ( by linarith ) ( by linarith ) hn0 ) ) ⟩) (by
  rw [ hm, Nat.div_mul_cancel ( Qr_dvd n r ( by linarith ) hrn hn0 ) ];
  exact Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) hrn hi ) ( qi_dvd n r i ( by linarith ) hrn hi ) hn0 |>.1) (by
  exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i ( by linarith ) ( by linarith ) hi ) ( qi_dvd n r i ( by linarith ) ( by linarith ) hi ) hn0 |>.1 ) ( Nat.pos_of_ne_zero hn0 ) ))).left (qi n r k) (by
  convert! Qr_primeFactors n r ( by linarith ) hrn |> fun h => h.symm ▸ Finset.mem_image_of_mem _ hk using 1)

/-
The branch index is at most `log₂ N` whenever `n ≤ N`.
-/
theorem kappav_le_logx (n r i N : ℕ) (hn : n ∈ Acal) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n)
    (hn0 : n ≠ 0) (hi : i < sr r) (hnN : n ≤ N) : kappav n r i ≤ Nat.log 2 N := by
  -- The index kappav n r i is the position of qi n r i in the sorted list of prime factors of Dwit n (qi n r i) - 1.
  have h_index : kappav n r i < (Dwit n (qi n r i) - 1).primeFactors.card := by
    have h_index : qi n r i ∈ ((Dwit n (qi n r i) - 1).primeFactors.sort (· ≤ ·)) := by
      convert! Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.2 _;
      have := qi_dvd_Dwit_sub_one n r i hn hr1 hrn hn0 hi;
      exact Nat.mem_primeFactors.mpr ⟨ qi_prime n r i hr1 hrn hi, this, Nat.sub_ne_zero_of_lt <| Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by linarith [ Dwit_spec n ( qi n r i ) hn ( qi_prime n r i hr1 hrn hi ) ( qi_dvd n r i hr1 hrn hi ) hn0 ], by linarith [ Dwit_spec n ( qi n r i ) hn ( qi_prime n r i hr1 hrn hi ) ( qi_dvd n r i hr1 hrn hi ) hn0 ] ⟩ ⟩;
    convert! List.idxOf_lt_length_iff.mpr h_index using 1;
    rw [ Finset.length_sort ];
  refine le_trans h_index.le ?_;
  refine' Nat.le_log_of_pow_le ( by decide ) _;
  refine' le_trans _ ( Nat.le_trans ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn0 ) ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i hr1 hrn hi ) ( qi_dvd n r i hr1 hrn hi ) hn0 |>.1 ) ) hnN );
  have h_prod_le : ∏ p ∈ (Dwit n (qi n r i) - 1).primeFactors, p ≤ Dwit n (qi n r i) - 1 := by
    exact Nat.le_of_dvd ( Nat.sub_pos_of_lt ( Dwit_spec n ( qi n r i ) hn ( qi_prime n r i hr1 hrn hi ) ( qi_dvd n r i hr1 hrn hi ) hn0 |>.2.1 ) ) ( Nat.prod_primeFactors_dvd _ );
  exact le_trans ( by simpa using! Finset.prod_le_prod' fun p hp => Nat.Prime.two_le <| Nat.prime_of_mem_primeFactors hp ) ( h_prod_le.trans <| Nat.pred_le _ )

/-
The `m`-quotient is positive on the fiber.
-/
theorem mval_pos (n r m : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hn1 : 1 ≤ n)
    (hm : m = n / Qr n r) : 1 ≤ m := by
  rw [ hm ];
  refine' Nat.div_pos ( Nat.le_of_dvd hn1 _ ) ( Nat.pos_of_dvd_of_pos _ hn1 ); all_goals exact Qr_dvd n r hr1 hrn ( by linarith )

/-
The encoding maps the fiber into the target.
-/
theorem encRec_mapsTo (x : ℝ) (t r m : ℕ) (_hx : 3 ≤ x) (hr2 : 2 ≤ r) (hrt : r ≤ t) :
    ∀ n ∈ fixedFiber x t r m, encRec x r m n ∈ encTarget x r m := by
  intro n hn; simp +decide [ encTarget ] ;
  refine' ⟨ _, _, _, _, _ ⟩;
  · exact fun i hi => Finset.mem_range.mpr ( Finset.mem_filter.mp hi |>.1 |> Finset.mem_range.mp );
  · unfold fixedFiber at hn; simp_all +decide [ encRec ] ;
    intro a; unfold bvec; split_ifs <;> simp_all +decide ;
    exact Or.inr ⟨ qi_prime n r a ( by linarith ) ( by linarith ) ( by exact a.2 ), by linarith [ Nat.div_pos ( show n ≥ Qr n r from Nat.le_of_dvd ( by linarith ) ( Qr_dvd n r ( by linarith ) ( by linarith ) ( by linarith ) ) ) ( show 0 < Qr n r from Nat.pos_of_ne_zero ( by
                                                                                                                                                                                                                                        exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero ( qi_prime n r i ( by linarith ) ( by linarith ) ( by exact Esel_lt_sr n r i hi ) ) ) ) ] ⟩;
  · unfold fixedFiber at hn; simp_all +decide [ encRec ] ;
    refine' fun a => ⟨ Nat.gcd_dvd_right _ _, _ ⟩;
    exact Nat.ne_of_gt ( mval_pos n r m ( by linarith ) ( by linarith ) ( by linarith ) ( by tauto ) );
  · intro i j; by_cases hij : j.val ∈ Esel n r <;> simp +decide [ *, encRec ] ;
    have := epsv_le_one n r m i j ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp_all +decide [ fixedFiber ];
    · interval_cases epsv n r m i j <;> trivial;
    · linarith;
    · exact lt_of_lt_of_le i.2 ( by linarith [ two_hr_le_sr r ] );
  · intro i; exact kappav_le_logx n r i ⌊x⌋₊ (by
    exact Finset.mem_filter.mp hn |>.2.1) (by
    linarith) (by
    unfold fixedFiber at hn; aesop;) (by
    exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 )) (by
    exact lt_of_lt_of_le i.2 ( Nat.le_of_lt_succ <| by linarith [ show sr r = 1 + Nat.log 2 r from rfl, show hr r = sr r / 2 from rfl, Nat.div_mul_le_self ( sr r ) 2 ] )) (by
    exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2) ;

/-
The encoding is injective on the fiber.
-/
theorem encRec_injOn (x : ℝ) (t r m : ℕ) (hr2 : 2 ≤ r) (hrt : r ≤ t) :
    Set.InjOn (encRec x r m) (fixedFiber x t r m) := by
  -- By definition of `fixedFiber`, if `encRec x r m n = encRec x r m n'`, then `n` and `n'` must satisfy the same conditions.
  intro n hn n' hn' h_eq
  have h_eq_conditions : n ∈ Acal ∧ n' ∈ Acal ∧ omegaCount n = t ∧ omegaCount n' = t ∧ n / Qr n r = m ∧ n' / Qr n' r = m := by
    unfold fixedFiber at hn hn'; aesop;
  apply fiber_inj n n' r m t;
  all_goals simp_all +decide [ encRec ];
  all_goals norm_num [ funext_iff ] at *;
  any_goals intro i hi; exact h_eq.2.2.1 ⟨ i, hi ⟩;
  · exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 );
  · exact Nat.ne_of_gt ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn' |>.1 ) |>.1 );
  · exact fun j hj => h_eq.2.1 ⟨ j, hj ⟩;
  · intro i k hi hk;
    have := h_eq.2.2.2.1 ⟨ i, hi ⟩ ⟨ k, by
      exact Esel_lt_sr n r k hk ⟩
    generalize_proofs at *;
    grind +suggestions;
  · exact fun i hi => h_eq.2.2.2.2 ⟨ i, hi ⟩

/-
**Fixed-prefix fiber bound, combinatorial form (Prop 8.5 pre-analysis).**
-/
theorem fixed_prefix_card_le (x : ℝ) (t r m : ℕ) (hx : 3 ≤ x) (hr2 : 2 ≤ r) (hrt : r ≤ t) :
    (fixedFiber x t r m).card
      ≤ 2 ^ (hr r) * (1 + omegaCount m) ^ (sr r) * (tauCount m) ^ (hr r)
          * 2 ^ (hr r * sr r) * (1 + Nat.log 2 ⌊x⌋₊) ^ (hr r) := by
  rw [ ← encTarget_card ];
  refine' le_trans _ ( Finset.card_le_card <| show encTarget x r m ≥ Finset.image ( encRec x r m ) ( fixedFiber x t r m ) from _ );
  · rw [ Finset.card_image_of_injOn ] ; exact fun a ha b hb hab => by have := encRec_injOn x t r m hr2 hrt ; exact this ha hb hab;
  · exact Finset.image_subset_iff.mpr fun n hn => encRec_mapsTo x t r m hx hr2 hrt n hn

/-! ### The canonical score-maximizing divisor -/

/-- The `r`-th largest prime factor of `n` (`1` if out of range). -/
noncomputable def pnth (n r : ℕ) : ℕ := (n.primeFactors.sort (· ≥ ·)).getD (r - 1) 1

/-- The canonical score `σ_1 = log p_1`, `σ_r = h_r log p_r` (`r ≥ 2`). -/
noncomputable def score (n r : ℕ) : ℝ :=
  if r = 1 then Real.log (pnth n 1) else (hr r : ℝ) * Real.log (pnth n r)

/-- The canonical maximizing index (a deterministic argmax over `[1, ω n]`). -/
noncomputable def rhoIdx (n : ℕ) : ℕ :=
  if h : (Finset.Icc 1 (omegaCount n)).Nonempty
  then (Finset.exists_max_image (Finset.Icc 1 (omegaCount n)) (score n) h).choose
  else 1

/-- The canonical compression divisor `Q(n)`. -/
noncomputable def Qcanon (n : ℕ) : ℕ :=
  if rhoIdx n = 1 then pnth n 1 else Qr n (rhoIdx n)

/-
Each selected prime is at least the `r`-th largest prime.
-/
theorem pnth_le_qi (n r j : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) (hj : j ∈ Esel n r) :
    pnth n r ≤ qi n r j := by
  -- Let `L = n.primeFactors.sort (· ≥ ·)`. `L` is sorted in `≥` order (`Finset.sort_sorted`) and has length `omegaCount n` (`Finset.length_sort`, `= n.primeFactors.card`).
  set L := n.primeFactors.sort (· ≥ ·) with hL_def
  -- `L` is sorted in `≥` order; `Finset.pairwise_sort` states this directly as
  -- a `List.Pairwise`, which is exactly the form consumed by
  -- `List.pairwise_iff_get` below.
  have hL_sorted : List.Pairwise (· ≥ ·) L := by
    exact Finset.pairwise_sort _ _
  have hL_length : L.length = omegaCount n := by
    aesop
  have hL_getD : pnth n r = L.getD (r - 1) 1 := by
    rfl
  have hL_getD' : pnth n r = L.get ⟨r - 1, by
    omega⟩ := by
    grind
  generalize_proofs at *;
  -- `j ∈ Esel n r` gives `j < sr r` (`Esel_lt_sr`), so `qi n r j ∈ Siter n (topR n r) j` (`qi_mem_Siter`) `subseteq topR n r` (`Siter_subset`).
  have hq_subset_topR : qi n r j ∈ topR n r := by
    exact Siter_subset n r j |> fun h => h <| qi_mem_Siter n r j hr1 hrn <| Esel_lt_sr n r j hj;
  -- `topR n r = (L.take r).toFinset`, so `qi n r j ∈ (L.take r).toFinset`, i.e. `qi n r j ∈ L.take r` (`List.mem_toFinset`).
  have hq_mem_take : qi n r j ∈ L.take r := by
    unfold topR at hq_subset_topR; aesop;
  obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hq_mem_take;
  have := List.pairwise_iff_get.mp hL_sorted; simp_all +decide ;
  by_cases hk_lt_r : k.val < r - 1;
  · specialize this ⟨ k, by
      grind +revert ⟩ ⟨ r - 1, by
      grind ⟩ hk_lt_r
    generalize_proofs at *;
    grind;
  · grind

/-
Lower bound `Q_r(n) ≥ p_r ^ h_r`.
-/
theorem Qr_ge (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ omegaCount n) :
    (pnth n r) ^ (hr r) ≤ Qr n r := by
  convert! Finset.prod_le_prod' fun j hj => pnth_le_qi n r j hr1 hrn hj;
  rw [ Finset.prod_const, Esel_card ]

/-
`ρ(n) ∈ [1, ω n]`.
-/
theorem rhoIdx_mem (n : ℕ) (h : 1 ≤ omegaCount n) : rhoIdx n ∈ Finset.Icc 1 (omegaCount n) := by
  unfold rhoIdx; split_ifs ;
  · grind +qlia;
  · exact Finset.mem_Icc.mpr ⟨ le_rfl, h ⟩

/-
`ρ(n)` maximizes the score.
-/
theorem rhoIdx_max (n r : ℕ) (h : 1 ≤ omegaCount n) (hr : r ∈ Finset.Icc 1 (omegaCount n)) :
    score n r ≤ score n (rhoIdx n) := by
  convert! ( Finset.exists_max_image ( Finset.Icc 1 ( omegaCount n ) ) ( score n ) ( by aesop ) ) |> Classical.choose_spec |> And.right |> fun h => h r hr using 1;
  unfold rhoIdx; aesop;

/-
`Q(n)` is squarefree.
-/
theorem Qcanon_squarefree (n : ℕ) : Squarefree (Qcanon n) := by
  unfold Qcanon;
  split_ifs;
  · -- If `rhoIdx n = 1`, then by definition `omegaCount n` is empty or `pnth n 1 = 1`. In either case, `pnth n 1` is squarefree.
    by_cases h_empty : omegaCount n = 0;
    · unfold pnth; aesop;
    · -- Since `omegaCount n ≠ 0`, `pnth n 1` is a prime factor of `n`.
      have h_prime : ∃ p, p ∈ n.primeFactors ∧ pnth n 1 = p := by
        unfold pnth;
        rcases x : n.primeFactors.sort ( · ≥ · ) with ( _ | ⟨ p, _ | ⟨ q, l ⟩ ⟩ ) <;> simp_all +decide;
        · replace x := congr_arg List.length x ; simp_all +decide;
        · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x p; aesop;
        · replace x := congr_arg List.toFinset x; rw [ Finset.ext_iff ] at x; specialize x p; aesop;
      rcases h_prime with ⟨ p, hp₁, hp₂ ⟩ ; rw [ hp₂ ] ; exact Nat.prime_iff.mp ( Nat.prime_of_mem_primeFactors hp₁ ) |> fun h => h.squarefree;
  · apply Qr_squarefree;
    · unfold rhoIdx at *;
      grind;
    · by_cases h : 1 ≤ omegaCount n <;> simp_all +decide [ rhoIdx ];
      grind +splitIndPred

/-
`Q(n) ∣ n`.
-/
theorem Qcanon_dvd (n : ℕ) (hn : n ∈ Acal) (h2 : 2 ≤ omegaCount n) : Qcanon n ∣ n := by
  by_cases h : rhoIdx n = 1 <;> simp_all +decide [ Qcanon ];
  · unfold pnth;
    rcases k : n.primeFactors.sort ( fun x1 x2 => x1 ≥ x2 ) <;> simp_all +decide;
    replace k := congr_arg List.toFinset k; rw [ Finset.ext_iff ] at k; specialize k ‹_›; aesop;
  · apply Qr_dvd;
    · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.1;
    · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.2;
    · unfold omegaCount at h2; aesop;

/-! ### The reciprocal staircase sum (Lemma 9.1) -/

/-
As reals, `hr r ≥ (log₂ r)/2`.
-/
theorem hr_ge_half_log (r : ℕ) : (Nat.log 2 r : ℝ) / 2 ≤ (hr r : ℝ) := by
  rw [ div_le_iff₀ ] <;> norm_cast;
  unfold hr;
  unfold sr; omega;

/-
`1 ≤ h_r` for `r ≥ 2`.
-/
theorem one_le_hr (r : ℕ) (hr2 : 2 ≤ r) : 1 ≤ hr r := by
  unfold hr;
  unfold sr;
  exact Nat.div_pos ( by linarith [ Nat.log_pos one_lt_two hr2 ] ) zero_lt_two

/-
If `h_r < K` then `r < 2 ^ (2 K)`.
-/
theorem hr_small_lt (r K : ℕ) (h : hr r < K) : r < 2 ^ (2 * K) := by
  rcases r with ( _ | _ | r ) <;> simp_all +arith +decide [ hr ];
  · grind;
  · unfold sr at h;
    have := Nat.lt_pow_of_log_lt ( by linarith ) ( show Nat.log 2 ( r + 2 ) < 2 * K from by omega ) ; linarith

/-
Asymptotic ratio: `h_t / (log t / (2 log 2)) → 1`.
-/
theorem hr_div_log_tendsto :
    Filter.Tendsto (fun t : ℕ => (hr t : ℝ) / (Real.log t / (2 * Real.log 2)))
      Filter.atTop (nhds 1) := by
  -- We'll use the fact that $hr t \sim \frac{\log t}{2 \log 2}$ as $t \to \infty$.
  have h_hr_log : Filter.Tendsto (fun t : ℕ => (hr t : ℝ) / (Nat.log 2 t / 2)) Filter.atTop (nhds 1) := by
    -- We'll use the fact that `hr t` is approximately `Nat.log 2 t / 2`.
    have hr_approx : ∀ t : ℕ, t ≥ 2 → (hr t : ℝ) ≥ (Nat.log 2 t / 2 : ℝ) ∧ (hr t : ℝ) ≤ (Nat.log 2 t / 2 : ℝ) + 1 := by
      intro t ht; rw [ div_add_one, ge_iff_le, div_le_iff₀ ] <;> norm_cast ; simp +arith +decide [ hr ] ;
      unfold sr; rw [ le_div_iff₀ ] <;> norm_cast ; omega;
    generalize_proofs at *;
    -- Using the approximation, we can bound the ratio.
    have hr_bound : ∀ t : ℕ, t ≥ 2 → |(hr t : ℝ) / (Nat.log 2 t / 2) - 1| ≤ 2 / (Nat.log 2 t) := by
      intro t ht; rw [ abs_le ] ; constructor <;> ring_nf at * <;> nlinarith [ hr_approx t ht, inv_mul_cancel₀ ( show ( Nat.log 2 t : ℝ ) ≠ 0 by exact ne_of_gt <| Nat.cast_pos.mpr <| Nat.log_pos one_lt_two ht ), show ( Nat.log 2 t : ℝ ) ≥ 1 by exact_mod_cast Nat.log_pos one_lt_two ht ] ;
    generalize_proofs at *; (
    exact tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 2, fun t ht => by simpa using! hr_bound t ht ⟩ ) <| tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ 2 ^ x, fun t ht => Nat.le_log_of_pow_le ( by norm_num ) ht ⟩ ;);
  -- We'll use the fact that $Nat.log 2 t \sim \frac{\log t}{\log 2}$ as $t \to \infty$.
  have h_log : Filter.Tendsto (fun t : ℕ => (Nat.log 2 t : ℝ) / (Real.log t / Real.log 2)) Filter.atTop (nhds 1) := by
    -- We'll use the fact that $Nat.log 2 t \leq \frac{\log t}{\log 2} < Nat.log 2 t + 1$ to bound the ratio.
    have h_log_bound : ∀ t : ℕ, t ≥ 2 → (Nat.log 2 t : ℝ) ≤ (Real.log t) / (Real.log 2) ∧ (Real.log t) / (Real.log 2) < (Nat.log 2 t + 1 : ℝ) := by
      intro t ht; rw [ le_div_iff₀ ( Real.log_pos one_lt_two ), div_lt_iff₀ ( Real.log_pos one_lt_two ) ] ; norm_cast;
      exact ⟨ by rw [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_le_log ( by positivity ) ( mod_cast Nat.pow_log_le_self 2 ( by positivity ) ), by rw [ ← Real.log_rpow zero_lt_two ] ; exact Real.log_lt_log ( by positivity ) ( mod_cast Nat.lt_pow_succ_log_self ( by decide ) _ ) ⟩;
    -- Using the bounds, we can show that the ratio is squeezed between two sequences that tend to 1.
    have h_squeeze : ∀ t : ℕ, t ≥ 2 → 1 - 1 / (Nat.log 2 t + 1 : ℝ) ≤ (Nat.log 2 t : ℝ) / (Real.log t / Real.log 2) ∧ (Nat.log 2 t : ℝ) / (Real.log t / Real.log 2) ≤ 1 := by
      intro t ht; specialize h_log_bound t ht; rw [ one_sub_div ( by positivity ) ] ; rw [ div_le_div_iff₀ ] <;> try linarith [ show 0 < Real.log t / Real.log 2 from div_pos ( Real.log_pos <| Nat.one_lt_cast.mpr ht ) ( Real.log_pos <| by norm_num ) ] ;
      exact ⟨ by nlinarith, div_le_one_of_le₀ h_log_bound.1 <| by positivity ⟩;
    -- The sequence $1 - 1 / (Nat.log 2 t + 1)$ tends to $1$ as $t$ tends to infinity.
    have h_seq_tendsto : Filter.Tendsto (fun t : ℕ => 1 - 1 / (Nat.log 2 t + 1 : ℝ)) Filter.atTop (nhds 1) := by
      exact le_trans ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ <| tendsto_natCast_atTop_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ 2 ^ x, fun t ht => Nat.le_log_of_pow_le ( by norm_num ) ht ⟩ ) <| by norm_num;
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_seq_tendsto tendsto_const_nhds ( Filter.eventually_atTop.mpr ⟨ 2, fun t ht => h_squeeze t ht |>.1 ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 2, fun t ht => h_squeeze t ht |>.2 ⟩ )
  generalize_proofs at *;
  convert! h_hr_log.mul ( h_log.const_mul ( 1 / 1 ) ) using 2 <;> ring_nf! ; norm_num at *;
  by_cases h : Nat.log 2 ‹_› = 0 <;> simp_all +decide [ mul_assoc ];
  interval_cases ( ‹_› : ℕ ) <;> norm_num at *

/-
**Reciprocal staircase upper bound.**  For every `ε > 0`, eventually
`∑_{r=2}^t 1/h_r ≤ (2 log 2 + ε) · t / log t`.
-/
theorem sum_inv_hr_le (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      (∑ r ∈ Finset.Icc 2 t, (1 : ℝ) / (hr r)) ≤ (2 * Real.log 2 + ε) * t / Real.log t := by
  -- Choose δ ∈ (0,1) with 2 * Real.log 2 / (1 - δ) < 2 * Real.log 2 + ε/2.
  obtain ⟨δ, hδ_pos, hδ_lt⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ 2 * Real.log 2 / (1 - δ) < 2 * Real.log 2 + ε / 2 := by
    have hδ : Filter.Tendsto (fun δ : ℝ => 2 * Real.log 2 / (1 - δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * Real.log 2)) := by
      exact le_trans ( tendsto_const_nhds.div ( tendsto_const_nhds.sub ( Filter.tendsto_id.mono_left inf_le_left ) ) ( by norm_num ) ) ( by norm_num );
    have := hδ.eventually ( gt_mem_nhds <| show 2 * Real.log 2 < 2 * Real.log 2 + ε / 2 by linarith ) ; have := this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ) ; obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this.exists; exact ⟨ δ, hδ₂.1, hδ₂.2, hδ₁ ⟩ ;
  -- Define the threshold `K t := ⌈(1-δ) * (hr t : ℝ)⌉₊`.
  set K := fun t : ℕ => Nat.ceil ((1 - δ) * (hr t : ℝ));
  -- Show that eventually `∑_{r∈L} 1/(hr r) ≤ (2 log 2 + ε/2) t/log t`.
  have h_sum_L : ∃ T : ℕ, ∀ t ≥ T, (∑ r ∈ Finset.filter (fun r => K t ≤ hr r) (Finset.Icc 2 t), (1 / (hr r : ℝ))) ≤ (2 * Real.log 2 + ε / 2) * t / Real.log t := by
    -- For `r ∈ L`, `1/(hr r) ≤ 1/(K t)` (since `hr r ≥ K t ≥ ...`, use `one_le_hr`, and `K t ≥ (1-δ) hr t`).
    have h_sum_L_bound : ∀ t : ℕ, t ≥ 2 → (∑ r ∈ Finset.filter (fun r => K t ≤ hr r) (Finset.Icc 2 t), (1 / (hr r : ℝ))) ≤ (t : ℝ) / (K t : ℝ) := by
      intros t ht
      have h_card_L : (Finset.filter (fun r => K t ≤ hr r) (Finset.Icc 2 t)).card ≤ t := by
        exact le_trans ( Finset.card_filter_le _ _ ) ( by simp );
      refine' le_trans ( Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le _ <| Nat.cast_le.mpr <| Finset.mem_filter.mp hx |>.2 ) _ <;> norm_num [ div_eq_mul_inv ];
      · exact Nat.ceil_pos.mpr ( mul_pos ( by linarith ) ( Nat.cast_pos.mpr ( one_le_hr t ht ) ) );
      · exact mul_le_mul_of_nonneg_right ( mod_cast h_card_L ) ( by positivity );
    -- Since `K t ≥ (1-δ) hr t`, we have `t / (K t) ≤ t / ((1-δ) hr t)`.
    have h_sum_L_bound' : ∀ t : ℕ, t ≥ 2 → (∑ r ∈ Finset.filter (fun r => K t ≤ hr r) (Finset.Icc 2 t), (1 / (hr r : ℝ))) ≤ (t : ℝ) / ((1 - δ) * (hr t : ℝ)) := by
      intro t ht; specialize h_sum_L_bound t ht; refine le_trans h_sum_L_bound ?_; gcongr;
      · exact mul_pos ( by linarith ) ( Nat.cast_pos.mpr ( one_le_hr t ht ) );
      · exact Nat.le_ceil _;
    -- Since `hr t / (log t / (2 log 2)) → 1`, we have `t / ((1-δ) hr t) / (t/log t) → 2 log 2/(1-δ)`.
    have h_lim : Filter.Tendsto (fun t : ℕ => (t : ℝ) / ((1 - δ) * (hr t : ℝ)) / (t / Real.log t)) Filter.atTop (nhds (2 * Real.log 2 / (1 - δ))) := by
      have h_lim : Filter.Tendsto (fun t : ℕ => (hr t : ℝ) / (Real.log t / (2 * Real.log 2))) Filter.atTop (nhds 1) := by
        convert! hr_div_log_tendsto using 1;
      have := h_lim.inv₀ ; norm_num at *;
      convert! this.const_mul ( 2 * Real.log 2 / ( 1 - δ ) ) |> Filter.Tendsto.congr' _ using 2;
      · ring;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with t ht ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le ( Nat.one_le_cast.mpr ht.le ) ) ];
        exact Or.inl <| Or.inl <| by ring;
    have := h_lim.eventually ( gt_mem_nhds <| show 2 * Real.log 2 / ( 1 - δ ) < 2 * Real.log 2 + ε / 2 from hδ_lt.2 );
    simp +zetaDelta at *;
    obtain ⟨ T, hT ⟩ := this; use T + 2; intros t ht; specialize hT t ( by linarith ) ; rw [ div_lt_iff₀ ] at hT;
    · exact le_trans ( h_sum_L_bound' t ( by linarith ) ) ( by simpa only [ mul_div_assoc ] using! hT.le );
    · exact div_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) );
  -- Show that eventually `∑_{r∈S} 1/(hr r) ≤ (ε/2) t/log t`.
  have h_sum_S : ∃ T : ℕ, ∀ t ≥ T, (∑ r ∈ Finset.filter (fun r => hr r < K t) (Finset.Icc 2 t), (1 / (hr r : ℝ))) ≤ (ε / 2) * t / Real.log t := by
    -- Since $hr r < K t$, we have $r < 2^{2K t}$.
    have h_bound_S : ∀ t : ℕ, t ≥ 2 → (∑ r ∈ Finset.filter (fun r => hr r < K t) (Finset.Icc 2 t), (1 / (hr r : ℝ))) ≤ (2 ^ (2 * K t) : ℝ) := by
      intros t ht
      have h_bound_S : ∀ r ∈ Finset.filter (fun r => hr r < K t) (Finset.Icc 2 t), r < 2 ^ (2 * K t) := by
        intros r hr;
        have := hr_small_lt r ( K t ) ?_ <;> aesop;
      refine' le_trans ( Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le _ <| show ( hr x : ℝ ) ≥ 1 from _ ) _ <;> norm_num;
      · exact one_le_hr x ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ] );
      · exact_mod_cast le_trans ( Finset.card_le_card <| show Finset.filter ( fun r => hr r < K t ) ( Finset.Icc 2 t ) ⊆ Finset.Ico 2 ( 2 ^ ( 2 * K t ) ) from fun x hx => Finset.mem_Ico.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, h_bound_S x hx ⟩ ) ( by norm_num );
    -- Since $K t \leq (1-δ) hr t + 1$, we have $2^{2K t} \leq 4 \cdot (2^{2 hr t})^{1-δ}$.
    have h_exp_bound : ∀ t : ℕ, t ≥ 2 → (2 ^ (2 * K t) : ℝ) ≤ 4 * (2 ^ (2 * hr t)) ^ (1 - δ) := by
      intros t ht
      have h_exp_bound : (2 : ℝ) ^ (2 * K t) ≤ (2 : ℝ) ^ (2 * ((1 - δ) * (hr t : ℝ) + 1)) := by
        exact_mod_cast Real.rpow_le_rpow_of_exponent_le one_le_two ( show ( 2 * K t : ℝ ) ≤ 2 * ( ( 1 - δ ) * hr t + 1 ) by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( 1 - δ ) * hr t by exact mul_nonneg ( sub_nonneg.mpr hδ_lt.1.le ) ( Nat.cast_nonneg _ ) ) ] );
      convert! h_exp_bound using 1 ; norm_num [ Real.rpow_add, Real.rpow_mul ] ; ring_nf;
      norm_num [ pow_mul', ← Real.mul_rpow ] ; ring_nf;
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_comm, Real.rpow_mul ( by positivity ), Real.rpow_natCast ];
    -- Since $hr t \leq \log t / (2 \log 2) + 1$, we have $(2^{2 hr t})^{1-δ} \leq (t \cdot 2^{2})^{1-δ}$.
    have h_log_bound : ∀ t : ℕ, t ≥ 2 → (2 ^ (2 * hr t) : ℝ) ≤ (t * 2 ^ 2) := by
      intros t ht
      have h_hr_bound : (hr t : ℝ) ≤ Real.log t / (2 * Real.log 2) + 1 := by
        have h_log_bound : (hr t : ℝ) ≤ (Nat.log 2 t : ℝ) / 2 + 1 := by
          rw [ div_add_one, le_div_iff₀ ] <;> norm_cast;
          exact Nat.div_mul_le_self _ _ |> le_trans <| by unfold sr; linarith;
        refine le_trans h_log_bound ?_;
        rw [ div_add_one, div_add_one, div_le_div_iff₀ ] <;> try positivity;
        have := Real.log_le_log ( by positivity ) ( show ( t : ℝ ) ≥ 2 ^ Nat.log 2 t by exact_mod_cast Nat.pow_log_le_self 2 <| by linarith ) ; norm_num at * ; linarith;
      rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_pow ];
      rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] ; norm_num ; nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( Real.log t ) ( by positivity : ( 2 * Real.log 2 ) ≠ 0 ) ];
    -- Since $t^{1-δ} \cdot \log t / t \to 0$, we have $4 \cdot (t \cdot 2^{2})^{1-δ} \leq (ε/2) t / \log t$ eventually.
    have h_lim_zero : Filter.Tendsto (fun t : ℕ => (4 * (t * 2 ^ 2 : ℝ) ^ (1 - δ)) / (t / Real.log t)) Filter.atTop (nhds 0) := by
      -- Simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun t : ℕ => (4 * (2 ^ 2) ^ (1 - δ) * (t : ℝ) ^ (1 - δ) * Real.log t) / t) Filter.atTop (nhds 0) by
        refine h_simplify.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; rw [ div_div_eq_mul_div ] ; ring;
      -- We can factor out $t^{1-δ}$ and use the fact that $\frac{\log t}{t^δ}$ tends to $0$ as $t$ tends to infinity.
      have h_factor : Filter.Tendsto (fun t : ℕ => (Real.log t : ℝ) / t ^ δ) Filter.atTop (nhds 0) := by
        -- Let $y = \log t$, therefore the expression becomes $\frac{y}{e^{y \delta}}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => y / Real.exp (y * δ)) Filter.atTop (nhds 0) by
          have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht using by simp +decide [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr ht ), mul_comm ] );
        -- Let $z = y \delta$, therefore the expression becomes $\frac{z}{e^z}$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => z / Real.exp z) Filter.atTop (nhds 0) by
          have := h_z.comp ( Filter.tendsto_id.atTop_mul_const hδ_pos );
          convert! this.div_const δ using 2 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm δ, hδ_pos.ne' ];
        simpa [ Real.exp_neg ] using! Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
      convert! h_factor.const_mul ( 4 * ( 2 ^ 2 ) ^ ( 1 - δ ) ) using 2 <;> ring_nf;
      by_cases h : ‹_› = 0 <;> simp +decide [ h, mul_assoc, mul_comm, mul_left_comm ];
      rw [ ← mul_assoc, ← Real.rpow_neg ( by positivity ), ← Real.rpow_neg_one, ← Real.rpow_add ( by positivity ) ] ; ring_nf;
    have := h_lim_zero.eventually ( gt_mem_nhds <| show 0 < ε / 2 by positivity );
    obtain ⟨ T, hT ⟩ := Filter.eventually_atTop.mp this;
    refine' ⟨ T + 2, fun t ht => le_trans ( h_bound_S t ( by linarith ) ) ( le_trans ( h_exp_bound t ( by linarith ) ) _ ) ⟩;
    have := hT t ( by linarith );
    rw [ div_lt_iff₀ ( div_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ) ] at this;
    rw [ mul_div_assoc ];
    exact le_trans ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( by positivity ) ( h_log_bound t ( by linarith ) ) ( by linarith ) ) ( by positivity ) ) this.le;
  obtain ⟨ T₁, hT₁ ⟩ := h_sum_L; obtain ⟨ T₂, hT₂ ⟩ := h_sum_S; use Max.max T₁ T₂; intro t ht; specialize hT₁ t ( le_trans ( le_max_left _ _ ) ht ) ; specialize hT₂ t ( le_trans ( le_max_right _ _ ) ht ) ; simp_all +decide [ Finset.sum_filter ] ;
  convert! add_le_add hT₁ hT₂ using 1 <;> ring_nf;
  simpa only [ ← Finset.sum_add_distrib ] using! Finset.sum_congr rfl fun x hx => by split_ifs <;> linarith;

/-! ### The weighted-prefix bound (Proposition 9.2) -/

/-- The sum of logs of the ordered prime factors equals `log (rad n)`. -/
theorem sum_log_pnth (n : ℕ) :
    ∑ r ∈ Finset.Icc 1 (omegaCount n), Real.log (pnth n r) = Real.log (rad n) := by
  set L := n.primeFactors.sort (· ≥ ·) with hL
  have hlen : L.length = omegaCount n := by rw [hL, Finset.length_sort]
  have hstep : ∑ r ∈ Finset.Icc 1 (omegaCount n), Real.log (pnth n r)
      = ∑ r ∈ Finset.Icc 1 L.length, Real.log ((L.getD (r-1) 1 : ℕ) : ℝ) := by
    rw [← hlen]
    apply Finset.sum_congr rfl
    intro r _
    simp only [pnth, ← hL]
  rw [hstep]
  have hreindex : ∑ r ∈ Finset.Icc 1 L.length, Real.log ((L.getD (r-1) 1 : ℕ):ℝ)
      = ∑ i ∈ Finset.range L.length, Real.log ((L.getD i 1 : ℕ):ℝ) := by
    apply Finset.sum_nbij' (fun r => r - 1) (fun i => i + 1) <;> simp_all;
    omega
  rw [hreindex]
  have hmap : ∑ i ∈ Finset.range L.length, Real.log ((L.getD i 1 : ℕ):ℝ)
      = (L.map (fun x : ℕ => Real.log (x:ℝ))).sum := by
    symm
    induction L with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ih, add_comm]
  rw [hmap]
  have hnodup : L.Nodup := by rw [hL]; exact Finset.sort_nodup _ _
  have htofin : (L.map (fun x : ℕ => Real.log (x:ℝ))).sum
      = ∑ x ∈ L.toFinset, Real.log (x:ℝ) := by
    rw [Finset.sum, List.toFinset_val, List.dedup_eq_self.mpr hnodup, Multiset.map_coe,
      Multiset.sum_coe]
  rw [htofin]
  have htoeq : L.toFinset = n.primeFactors := by rw [hL]; exact Finset.sort_toFinset _ _
  rw [htoeq, ← Real.log_prod]
  · congr 1
    rw [rad, Nat.cast_prod]; rfl
  · intro p hp
    have := Nat.prime_of_mem_primeFactors hp
    exact_mod_cast this.ne_zero

/-
`log Q(n)` dominates the maximal score.
-/
theorem log_Qcanon_ge_score (n : ℕ) (h2 : 2 ≤ omegaCount n) :
    score n (rhoIdx n) ≤ Real.log (Qcanon n) := by
  by_cases h : rhoIdx n = 1 <;> simp_all +decide [ score ];
  · unfold Qcanon; aesop;
  · rw [ Qcanon ];
    convert! Real.log_le_log ?_ ( Nat.cast_le.mpr ( Qr_ge n ( rhoIdx n ) ?_ ?_ ) ) using 1 <;> norm_num [ h ];
    · exact pow_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
        unfold pnth;
        have h_prime_factors : ∀ x ∈ n.primeFactors.sort (· ≥ ·), x ≠ 0 := by
          exact fun x hx => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors <| Finset.mem_sort ( α := ℕ ) ( · ≥ · ) |>.1 hx;
        grind ) _;
    · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.1;
    · exact Finset.mem_Icc.mp ( rhoIdx_mem n ( by linarith ) ) |>.2

/-
The averaging bound: `log (rad n) ≤ M · (1 + ∑ 1/h_r)`.
-/
theorem W_le_M_sum (n : ℕ) (h2 : 2 ≤ omegaCount n) :
    Real.log (rad n)
      ≤ score n (rhoIdx n) * (1 + ∑ r ∈ Finset.Icc 2 (omegaCount n), (1 : ℝ) / (hr r)) := by
  -- By definition of $score$, we know that for any $r \in \{1, 2, \ldots, \omega(n)\}$, $score n r \leq score n (rhoIdx n)$.
  have h_score_le : ∀ r ∈ Finset.Icc 1 (omegaCount n), (if r = 1 then Real.log (pnth n 1) else (hr r : ℝ) * Real.log (pnth n r)) ≤ score n (rhoIdx n) := by
    intros r hr; exact (by
    convert! rhoIdx_max n r ( by linarith ) hr using 1);
  -- Applying the bound from h_score_le to each term in the sum, we get:
  have h_sum_bound : ∑ r ∈ Finset.Icc 2 (omegaCount n), Real.log (pnth n r) ≤ ∑ r ∈ Finset.Icc 2 (omegaCount n), (score n (rhoIdx n)) / (hr r : ℝ) := by
    gcongr;
    rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| one_le_hr _ <| by linarith [ Finset.mem_Icc.mp ‹_› ] ) ];
    grind +qlia;
  convert! add_le_add ( show Real.log ( pnth n 1 ) ≤ score n ( rhoIdx n ) from by
                        simpa using! h_score_le 1 ( Finset.mem_Icc.mpr ⟨ by norm_num, by linarith ⟩ ) ) h_sum_bound using 1;
  · rw [ ← sum_log_pnth ];
    rw [ Finset.Icc_eq_cons_Ioc ( by linarith ), Finset.sum_cons ] ; aesop;
  · simp +decide [ div_eq_mul_inv, mul_add, Finset.mul_sum _ _ _ ]

/-
**Proposition 9.2 (weighted prefix).**
-/
theorem weighted_prefix (η : ℝ) (hη : 0 < η) :
    ∃ T : ℕ, ∀ n, n ∈ Acal → T ≤ omegaCount n →
      (1 - η) / (2 * Real.log 2) * Real.log (rad n) * Real.log (omegaCount n) / (omegaCount n)
        ≤ Real.log (Qcanon n) := by
  by_cases hη1 : η ≥ 1;
  · use 1; intros n hn hn'; exact le_trans ( div_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonpos_of_nonneg ( mul_nonpos_of_nonpos_of_nonneg ( div_nonpos_of_nonpos_of_nonneg ( by linarith ) ( by positivity ) ) ( Real.log_nonneg ( mod_cast Nat.pos_of_ne_zero ( by
      exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp ) ) ) ) ( Real.log_nonneg ( mod_cast Nat.one_le_iff_ne_zero.mpr ( by
      finiteness ) ) ) ) ( Nat.cast_nonneg _ ) ) ( Real.log_nonneg ( mod_cast Nat.pos_of_ne_zero ( by
      exact Nat.ne_of_gt ( Nat.pos_of_ne_zero ( by exact fun h => by have := Qcanon_squarefree n; simp_all +decide ) ) ) ) ) ;
  · -- Choose ε such that (1 - η) * (2 * Real.log 2 + ε) / (2 * Real.log 2) < 1.
    obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, (1 - η) * (2 * Real.log 2 + ε) / (2 * Real.log 2) < 1 := by
      exact ⟨ ( 2 * Real.log 2 * ( 1 - ( 1 - η ) ) / 2 ) / ( 1 - η ), div_pos ( div_pos ( mul_pos ( mul_pos two_pos ( Real.log_pos one_lt_two ) ) ( by linarith ) ) zero_lt_two ) ( by linarith ), by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( 2 * Real.log 2 * ( 1 - ( 1 - η ) ) / 2 ) ( by linarith : ( 1 - η ) ≠ 0 ) ] ⟩;
    -- Set `κ := (1 - η) * (2 * Real.log 2 + ε) / (2 * Real.log 2)`, so `κ < 1`.
    set κ : ℝ := (1 - η) * (2 * Real.log 2 + ε) / (2 * Real.log 2) with hκ_def
    have hκ_lt_1 : κ < 1 := by
      exact hε;
    obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℕ, ∀ t : ℕ, T₁ ≤ t → (1 - η) / (2 * Real.log 2) * (Real.log t / t) ≤ 1 - κ := by
      have h_log_div_t_zero : Filter.Tendsto (fun t : ℕ => Real.log t / t) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
        suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_log_recip.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using! Real.continuous_mul_log.neg.tendsto 0 );
      simpa using! h_log_div_t_zero.const_mul _ |> fun h => h.eventually ( ge_mem_nhds <| by linarith );
    obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t → (∑ r ∈ Finset.Icc 2 t, (1 : ℝ) / (hr r)) ≤ (2 * Real.log 2 + ε) * t / Real.log t := by
      convert! sum_inv_hr_le ε hε_pos using 1;
    refine' ⟨ Max.max ( Max.max T₀ T₁ ) 3, fun n hn hn' => _ ⟩ ; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    -- Using the bounds from `hT₀` and `hT₁`, we can simplify the expression.
    have h_simplify : (1 - η) / (2 * Real.log 2) * Real.log (rad n) * Real.log (omegaCount n) / (omegaCount n) ≤ Real.log (rad n) / (1 + ∑ r ∈ Finset.Icc 2 (omegaCount n), (1 : ℝ) / (hr r)) := by
      have h_simplify : (1 - η) / (2 * Real.log 2) * Real.log (omegaCount n) / (omegaCount n) * (1 + ∑ r ∈ Finset.Icc 2 (omegaCount n), (1 : ℝ) / (hr r)) ≤ 1 := by
        have := hT₁ ( omegaCount n ) hn'.2.1; have := hT₀ ( omegaCount n ) hn'.1; norm_num at *;
        field_simp at *;
        rw [ div_le_iff₀ ( by norm_cast; linarith ) ] at *;
        rw [ le_div_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ] at this;
        nlinarith [ show 0 ≤ ( 1 - η ) * Real.log ( omegaCount n ) by exact mul_nonneg ( sub_nonneg.2 hη1.le ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ];
      rw [ le_div_iff₀ ];
      · convert! mul_le_mul_of_nonneg_right h_simplify ( Real.log_nonneg <| show ( rad n : ℝ ) ≥ 1 from mod_cast Nat.one_le_iff_ne_zero.mpr <| by
                                                                            exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.ne_of_gt <| Nat.pos_of_mem_primeFactors hp ) using 1 ; ring;
        ring;
      · exact add_pos_of_pos_of_nonneg zero_lt_one <| Finset.sum_nonneg fun _ _ => by positivity;
    convert! h_simplify.trans _ using 1;
    · unfold rad; norm_num [ Finset.prod_natCast ] ; ring;
    · refine' le_trans _ ( log_Qcanon_ge_score n ( by linarith ) );
      have := W_le_M_sum n ( by linarith );
      rwa [ div_le_iff₀ ( add_pos_of_pos_of_nonneg zero_lt_one <| Finset.sum_nonneg fun _ _ => by positivity ) ]

end Erdos768Comp

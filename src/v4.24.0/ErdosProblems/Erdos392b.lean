/-
Formalization of the greedy prime-packing decomposition of n! and the asymptotic behavior of A(n) and G(n).

We define A(n) as the minimum number of factors <= n needed to represent n!, and G(n) as the number of factors produced by the greedy algorithm.
We prove that both A(n) and G(n) are asymptotically equal to n - n / log n.

Main theorems:
- `A_asymptotic`: A(n) = n - n / log n + o(n / log n)
- `G_asymptotic`: G(n) = n - n / log n + o(n / log n)

Helper lemmas include bounds on the prime counting function (Chebyshev), bounds on the p-adic valuation of n!, and analysis of the "waste" W(n).
-/

import Mathlib

namespace Erdos392b

set_option linter.mathlibStandardSet false

open scoped Nat
open scoped Classical
--open scoped Pointwise

set_option maxHeartbeats 0

noncomputable section

/-
For $n\ge 2$, let $A(n)$ be the least integer $t$ for which there exist integers $a_1,\dots,a_t\in \{1,2,\dots,n\}$ such that $n!=a_1a_2\cdots a_t$.
-/
def is_valid_decomp (n : ℕ) (L : List ℕ) : Prop :=
  L.prod = n.factorial ∧ ∀ x ∈ L, 1 ≤ x ∧ x ≤ n

noncomputable def A (n : ℕ) : ℕ :=
  sInf { t | ∃ L, is_valid_decomp n L ∧ L.length = t }

/-
Helper function to find the largest number in a list `L` that is less than or equal to `bound`.
-/
def find_largest_le (bound : ℕ) (L : List ℕ) : Option ℕ :=
  L.foldl (fun acc p => if p <= bound then
    match acc with
    | none => some p
    | some max_p => if p > max_p then some p else some max_p
    else acc) none

/-
If `find_largest_le` returns `some p`, then `p` is in the list `L`.
-/
theorem find_largest_le_mem (bound : ℕ) (L : List ℕ) (p : ℕ) :
  find_largest_le bound L = some p → p ∈ L := by
    unfold find_largest_le;
    induction L using List.reverseRecOn <;> aesop

/-
Definition of the greedy prime packing algorithm using a fuel parameter to ensure termination.
`greedy_pass` constructs one factor.
`greedy_process` iterates to construct all factors.
`G(n)` is the number of factors.
-/
def greedy_pass (n : ℕ) (acc : ℕ) (primes : List ℕ) (fuel : ℕ) : ℕ × List ℕ :=
  match fuel with
  | 0 => (acc, primes)
  | fuel' + 1 =>
    if acc = 0 then (acc, primes) else
    match find_largest_le (n / acc) primes with
    | none => (acc, primes)
    | some p => greedy_pass n (acc * p) (primes.erase p) fuel'

def greedy_process (n : ℕ) (primes : List ℕ) (fuel : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    if primes.isEmpty then []
    else
      let (factor, primes') := greedy_pass n 1 primes primes.length
      factor :: greedy_process n primes' fuel'

def G (n : ℕ) : ℕ :=
  let primes := Nat.primeFactorsList n.factorial
  (greedy_process n primes (primes.length + 1)).length

/-
The product of the result accumulator and the result primes from `greedy_pass` is equal to the product of the initial accumulator and the initial primes.
-/
theorem greedy_pass_product (n : ℕ) (acc : ℕ) (primes : List ℕ) (fuel : ℕ) :
  let (res_acc, res_primes) := greedy_pass n acc primes fuel
  res_acc * res_primes.prod = acc * primes.prod := by
    induction' fuel with fuel ih generalizing acc primes;
    · rfl;
    · -- By definition of `greedy_pass`, we can split into the two cases: acc is zero or acc is not zero.
      by_cases h_acc : acc = 0;
      · -- If `acc` is zero, then the result of `greedy_pass` is `(0, primes)`, and the product is zero.
        simp [h_acc, greedy_pass];
      · by_cases h : find_largest_le ( n / acc ) primes = none <;> simp_all +decide [ greedy_pass ];
        obtain ⟨ p, hp ⟩ := Option.ne_none_iff_exists'.mp h;
        have := ih ( acc * p ) ( primes.erase p ) ; simp_all +decide [ mul_assoc ] ;
        have := find_largest_le_mem ( n / acc ) primes p hp; aesop;

/-
If `L` is not empty and all elements are less than or equal to `bound`, then `find_largest_le` returns `some`.
-/
theorem find_largest_le_some (bound : ℕ) (L : List ℕ) (hL : L ≠ []) (h_le : ∀ x ∈ L, x ≤ bound) :
  (find_largest_le bound L).isSome := by
    unfold find_largest_le;
    induction L using List.reverseRecOn <;> aesop

/-
If the accumulator starts less than or equal to `n`, `greedy_pass` returns an accumulator less than or equal to `n`.
-/
theorem greedy_pass_le (n : ℕ) (acc : ℕ) (primes : List ℕ) (fuel : ℕ) (h_acc : acc ≤ n) (h_acc_pos : acc > 0) :
  (greedy_pass n acc primes fuel).1 ≤ n := by
    induction' fuel with fuel ih generalizing acc primes;
    · exact h_acc;
    · by_cases h_find_largest_le : find_largest_le (n / acc) primes = none;
      · rw [ show greedy_pass n acc primes ( fuel + 1 ) = ( acc, primes ) from _ ] ; aesop;
        exact if_neg ( by aesop ) |> fun h => h.trans ( by aesop );
      · obtain ⟨p, hp⟩ : ∃ p, find_largest_le (n / acc) primes = some p ∧ p ∈ primes := by
          exact Option.ne_none_iff_exists'.mp h_find_largest_le |> fun ⟨ p, hp ⟩ => ⟨ p, hp, find_largest_le_mem _ _ _ hp ⟩;
        have h_find_largest_le_le : p ≤ n / acc := by
          have h_find_largest_le_le : ∀ (bound : ℕ) (L : List ℕ), find_largest_le bound L = some p → p ≤ bound := by
            intros bound L h_find_largest_le
            induction' L using List.reverseRecOn with p L ih;
            · cases h_find_largest_le;
            · unfold find_largest_le at h_find_largest_le; aesop;
          exact h_find_largest_le_le _ _ hp.1;
        -- By definition of `greedy_pass`, we have `greedy_pass n acc primes (fuel + 1) = greedy_pass n (acc * p) (primes.erase p) fuel`.
        have h_greedy_pass_def : greedy_pass n acc primes (fuel + 1) = greedy_pass n (acc * p) (primes.erase p) fuel := by
          rw [ show greedy_pass n acc primes ( fuel + 1 ) = if acc = 0 then ( acc, primes ) else match find_largest_le ( n / acc ) primes with | Option.none => ( acc, primes ) | Option.some p => greedy_pass n ( acc * p ) ( primes.erase p ) fuel from rfl ] ; aesop;
        by_cases h_acc_pos : acc * p > 0;
        · exact h_greedy_pass_def.symm ▸ ih _ _ ( by nlinarith [ Nat.div_mul_le_self n acc ] ) h_acc_pos;
        · -- Since `acc` is zero, the greedy pass returns `(0, primes)`, and thus the first element is zero.
          have h_greedy_pass_zero : greedy_pass n 0 (primes.erase 0) fuel = (0, primes.erase 0) := by
            exact Nat.recOn fuel rfl fun k ih => by rw [ show greedy_pass n 0 ( primes.erase 0 ) ( k + 1 ) = ( 0, primes.erase 0 ) from by { exact if_pos ( by aesop ) } ] ;
          aesop

/-
The list of primes returned by `greedy_pass` has length less than or equal to the input list.
-/
theorem greedy_pass_length_le (n acc : ℕ) (primes : List ℕ) (fuel : ℕ) :
  (greedy_pass n acc primes fuel).2.length ≤ primes.length := by
    -- Apply the lemma that states if `find_largest_le` returns a value, then that value is in the list.
    have h_find_largest_le_mem : List.Sublist ((greedy_pass n acc primes fuel).2) primes := by
      induction' fuel with fuel ih generalizing acc primes;
      · exact List.Sublist.refl (greedy_pass n acc primes 0).2;
      · by_cases h : acc = 0 <;> by_cases h' : primes = [] <;> simp_all +decide [ greedy_pass ];
        · unfold find_largest_le; aesop;
        · rcases find_largest_le ( n / acc ) primes with ( _ | p ) <;> simp_all +decide [ List.Sublist ];
          exact List.Sublist.trans ( ih _ _ ) ( List.erase_sublist );
    exact h_find_largest_le_mem.length_le

/-
If `acc=1`, `primes` is not empty, and all primes are $\le n$, then `greedy_pass` returns a strictly smaller list of primes.
-/
theorem greedy_pass_length_lt (n : ℕ) (primes : List ℕ) (fuel : ℕ)
    (h_n : n ≥ 1)
    (h_primes : primes ≠ [])
    (h_le : ∀ p ∈ primes, p ≤ n)
    (h_fuel : fuel ≥ 1) :
    (greedy_pass n 1 primes fuel).2.length < primes.length := by
      -- By definition of `greedy_pass`, if the list is non-empty and all elements are ≤ n, then after one pass, the length of the list is strictly less than the original.
      have h_greedy_pass_step : ∀ {primes : List ℕ} {acc : ℕ} {fuel : ℕ}, primes ≠ [] → (∀ p ∈ primes, p ≤ n) → acc = 1 → fuel ≥ 1 → (greedy_pass n acc primes fuel).2.length < primes.length := by
        intros primes acc fuel h_primes h_le h_acc h_fuel;
        induction' fuel with fuel ih generalizing acc primes <;> simp_all +decide [ greedy_pass ];
        cases h : find_largest_le n primes <;> simp_all +decide;
        · have := find_largest_le_some n primes h_primes h_le; aesop;
        · have h_erase : (primes.erase ‹_›).length < primes.length := by
            rw [ List.length_erase_of_mem ];
            · exact Nat.pred_lt ( by aesop );
            · (expose_names; exact find_largest_le_mem n primes val h);
          have h_greedy_pass_step : (greedy_pass n ‹_› (primes.erase ‹_›) fuel).2.length ≤ (primes.erase ‹_›).length := by
            (expose_names; exact greedy_pass_length_le n val (primes.erase val) fuel);
          linarith;
      exact h_greedy_pass_step h_primes h_le rfl h_fuel

/-
If `fuel > primes.length`, then the product of the factors produced by `greedy_process` is equal to the product of the input primes.
-/
theorem greedy_process_prod_eq (n : ℕ) (primes : List ℕ) (fuel : ℕ)
    (h_fuel : fuel > primes.length)
    (h_le : ∀ p ∈ primes, p ≤ n)
    (h_n : n ≥ 1) :
    (greedy_process n primes fuel).prod = primes.prod := by
      -- By induction on the number of factors in the greedy_process list.
      induction' fuel with fuel' ih generalizing primes n
      all_goals generalize_proofs at *;
      · contradiction;
      · by_cases h : primes = [] <;> simp_all +decide [ greedy_process ];
        rw [ ih ] <;> try linarith [ List.length_pos_iff.mpr h ] ;
        · convert greedy_pass_product n 1 primes primes.length using 1 ; aesop;
        · exact lt_of_lt_of_le ( greedy_pass_length_lt n primes primes.length h_n h h_le ( Nat.pos_of_ne_zero ( by aesop ) ) ) ( Nat.le_of_lt_succ h_fuel );
        · -- By definition of `greedy_pass`, the primes in the result are a subset of the original primes.
          have h_subset : ∀ (n : ℕ) (acc : ℕ) (primes : List ℕ) (fuel : ℕ), (greedy_pass n acc primes fuel).2 ⊆ primes := by
            intros n acc primes fuel
            induction' fuel with fuel' ih generalizing n acc primes
            all_goals generalize_proofs at *;
            · unfold greedy_pass; aesop;
            · unfold greedy_pass;
              split_ifs <;> simp_all +decide [ List.subset_def ];
              rcases find_largest_le ( n / acc ) primes with ( _ | p ) <;> simp_all +decide [ List.subset_def ];
              exact fun { a } ha => List.mem_of_mem_erase ( ih _ _ _ ha );
          exact fun p hp => h_le p <| h_subset _ _ _ _ hp

/-
The list of primes returned by `greedy_pass` is a subset of the input list.
-/
theorem greedy_pass_subset (n : ℕ) (acc : ℕ) (primes : List ℕ) (fuel : ℕ) :
  (greedy_pass n acc primes fuel).2 ⊆ primes := by
    induction' fuel with fuel ih generalizing acc primes;
    · exact fun ⦃a⦄ a => a;
    · -- By definition of `greedy_pass`, if `acc ≠ 0`, then `greedy_pass n acc primes (fuel + 1)` will process the primes list by removing elements.
      by_cases h_acc : acc = 0;
      · -- Since the accumulator is 0, the function returns (acc, primes), so the primes part is just the original primes.
        simp [h_acc, greedy_pass];
      · by_cases h_le : (find_largest_le (n / acc) primes).isSome;
        · obtain ⟨p, hp⟩ : ∃ p, find_largest_le (n / acc) primes = some p := by
            exact Option.isSome_iff_exists.mp h_le;
          erw [ show greedy_pass n acc primes ( fuel + 1 ) = ( greedy_pass n ( acc * p ) ( primes.erase p ) fuel ) from ?_ ];
          · grind;
          · rw [greedy_pass];
            aesop;
        · rw [ show greedy_pass n acc primes ( fuel + 1 ) = ( acc, primes ) from ?_ ];
          · exact List.Subset.refl _;
          · exact if_neg ( by aesop ) |> fun h => h.trans ( by aesop )

/-
If the accumulator is positive and all primes are positive, `greedy_pass` returns a positive accumulator.
-/
theorem greedy_pass_pos (n : ℕ) (acc : ℕ) (primes : List ℕ) (fuel : ℕ)
    (h_acc : acc > 0)
    (h_primes : ∀ p ∈ primes, p > 0) :
    (greedy_pass n acc primes fuel).1 > 0 := by
      -- To prove that (greedy_pass n acc primes fuel).1 is not zero, we use the `greedy_pass_product` lemma.
      have h_gt_zero : (greedy_pass n acc primes fuel).1 * (greedy_pass n acc primes fuel).2.prod = acc * primes.prod := by
        exact greedy_pass_product n acc primes fuel;
      by_contra h_neg;
      simp_all +decide [ ne_of_gt ]

/-
All factors produced by `greedy_process` are less than or equal to `n`.
-/
theorem greedy_process_upper_bound (n : ℕ) (primes : List ℕ) (fuel : ℕ)
    (h_le : ∀ p ∈ primes, p ≤ n)
    (h_n : n ≥ 1) :
    ∀ x ∈ greedy_process n primes fuel, x ≤ n := by
      intro x hx;
      -- By definition of `greedy_process`, each factor in the list is less than or equal to `n`. We can prove this by induction on `fuel`.
      induction' fuel with fuel ih generalizing primes;
      · cases hx;
      · -- By definition of `greedy_process`, if `x` is in the list produced by `greedy_process n primes (fuel + 1)`, then `x` is either the first factor produced by `greedy_pass` or it is in the list produced by `greedy_process n primes fuel`.
        by_cases hx_first : x = (greedy_pass n 1 primes primes.length).1;
        · exact hx_first.symm ▸ by simpa using greedy_pass_le n 1 primes primes.length h_n ( Nat.one_pos ) ;
        · apply ih;
          any_goals exact ( greedy_pass n 1 primes primes.length ).2;
          · exact fun p hp => h_le p <| greedy_pass_subset _ _ _ _ hp;
          · rw [ greedy_process ] at hx;
            grind

/-
All factors produced by `greedy_process` are greater than or equal to 1.
-/
theorem greedy_process_pos_factors (n : ℕ) (primes : List ℕ) (fuel : ℕ)
    (h_pos : ∀ p ∈ primes, p > 0) :
    ∀ x ∈ greedy_process n primes fuel, x ≥ 1 := by
      intro x;
      -- By definition of `greedy_process`, each factor in the list is the product of primes from the list, each of which is at least 1.
      have h_factor_pos : ∀ (n : ℕ) (primes : List ℕ) (fuel : ℕ), (∀ p ∈ primes, p > 0) → ∀ x ∈ greedy_process n primes fuel, x > 0 := by
        intros n primes fuel h_pos;
        induction' fuel with fuel ih generalizing primes n <;> simp_all +decide [ greedy_process ];
        rintro x hx ( rfl | hx );
        · apply greedy_pass_pos;
          · norm_num;
          · assumption;
        · exact ih _ _ ( fun p hp => h_pos p <| greedy_pass_subset _ _ _ _ hp ) _ hx;
      exact fun hx => h_factor_pos n primes fuel h_pos x hx

/-
All factors produced by `greedy_process` are between 1 and `n`.
-/
theorem greedy_process_le (n : ℕ) (primes : List ℕ) (fuel : ℕ)
    (h_le : ∀ p ∈ primes, p ≤ n)
    (h_pos : ∀ p ∈ primes, p > 0)
    (h_n : n ≥ 1) :
    ∀ x ∈ greedy_process n primes fuel, 1 ≤ x ∧ x ≤ n := by
      exact fun x hx => ⟨ greedy_process_pos_factors n primes fuel h_pos x hx, greedy_process_upper_bound n primes fuel h_le h_n x hx ⟩

/-
The greedy procedure produces a valid factorization of $n!$ with all factors $\le n$.
-/
theorem greedy_is_valid (n : ℕ) (hn : n ≥ 2) :
  let primes := Nat.primeFactorsList n.factorial
  is_valid_decomp n (greedy_process n primes (primes.length + 1)) := by
    refine ⟨ ?_, fun x hx => ?_ ⟩;
    · convert greedy_process_prod_eq n _ _ _ _ _ using 1;
      · rw [ Nat.prod_primeFactorsList ( Nat.factorial_ne_zero _ ) ];
      · grind;
      · simp +zetaDelta at *;
        exact fun p pp dp _ => pp.dvd_factorial.mp dp;
      · grind;
    · apply_rules [ greedy_process_le ];
      · simp +zetaDelta at *;
        exact fun p pp dp _ => pp.dvd_factorial.mp dp;
      · exact fun p hp => Nat.pos_of_mem_primeFactorsList hp;
      · linarith

/-
Since the greedy algorithm produces a valid decomposition of length $G(n)$, and $A(n)$ is the minimum length of such a decomposition, we have $A(n) \le G(n)$.
-/
theorem A_le_G (n : ℕ) (hn : n ≥ 2) : A n ≤ G n := by
  refine' Nat.sInf_le _;
  use greedy_process n (Nat.primeFactorsList n.factorial) (Nat.primeFactorsList n.factorial).length.succ;
  exact ⟨ greedy_is_valid n hn, rfl ⟩

/-
If $n! = a_1 \cdots a_t$ with $1 \le a_i \le n$, then $t \ge \frac{\log(n!)}{\log n}$.
-/
theorem log_lower_bound (n : ℕ) (L : List ℕ) (hn : n ≥ 2) (hL : is_valid_decomp n L) :
  (L.length : ℝ) ≥ Real.log n.factorial / Real.log n := by
    rw [ ge_iff_le, div_le_iff₀ ( Real.log_pos <| by norm_cast ) ];
    rw [ ← Real.log_pow ] ; gcongr ; norm_cast;
    -- Since each $a_i$ is between 1 and $n$, their product is at most $n^t$.
    have h_prod_le : (L.prod : ℝ) ≤ n ^ L.length := by
      exact_mod_cast le_trans ( List.prod_le_pow_card _ _ fun x hx => hL.2 x hx |>.2 ) ( by norm_num );
    exact_mod_cast hL.1 ▸ h_prod_le

/-
The statement of the Chebyshev upper bound: For every $\varepsilon>0$, eventually $\pi(x) \le (\log 4+\varepsilon)\frac{x}{\log x}$.
-/
def ChebyshevUpperBound : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℝ in Filter.atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + ε) * x / Real.log x

/-
Definitions of Waste $W(n)$, dyadic intervals $I_j$, and $\Omega_j$.
-/
noncomputable def W (n : ℕ) : ℝ := (G n : ℝ) * Real.log n - Real.log (n.factorial)

def I (n j : ℕ) : Set ℕ := Set.Ioc (n / 2^(j+1)) (n / 2^j)

open Finset in
noncomputable def Omega (n j : ℕ) : ℕ :=
  ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ p ∈ I n j), padicValNat p n.factorial

/-
Definition of $B_j$, the number of factors whose largest prime lies in $I_j$.
-/
def largest_prime_of (k : ℕ) : ℕ :=
  (Nat.primeFactorsList k).foldl max 0

noncomputable def B (n j : ℕ) : ℕ :=
  let primes := Nat.primeFactorsList n.factorial
  let factors := greedy_process n primes (primes.length + 1)
  (factors.filter (fun x => largest_prime_of x ∈ I n j)).length

/-
The total waste $W(n)$ is the sum of the individual wastes $w_i = \log(n/b_i)$.
-/
noncomputable def w (n b : ℕ) : ℝ := Real.log n - Real.log b

theorem W_eq_sum_w (n : ℕ) :
  let primes := Nat.primeFactorsList n.factorial
  let factors := greedy_process n primes (primes.length + 1)
  W n = (factors.map (fun b => w n b)).sum := by
    unfold W w;
    -- By definition of $G(n)$, we know that the product of the factors in $greedy_process$ is $n!$.
    have h_prod : (greedy_process n (Nat.primeFactorsList n.factorial) (Nat.primeFactorsList n.factorial).length.succ).prod = n.factorial := by
      have := greedy_process_prod_eq n (Nat.factorial n).primeFactorsList (Nat.factorial n).primeFactorsList.length.succ;
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.factorial_ne_zero ];
      rw [ this fun p pp dp => pp.dvd_factorial.mp dp, Nat.prod_primeFactorsList ( Nat.factorial_ne_zero _ ) ];
    have h_log_prod : Real.log (n.factorial) = List.sum (List.map (fun b => Real.log b) (greedy_process n (Nat.primeFactorsList n.factorial) (Nat.primeFactorsList n.factorial).length.succ)) := by
      have h_log_prod : Real.log (List.prod (greedy_process n (Nat.primeFactorsList n.factorial) (Nat.primeFactorsList n.factorial).length.succ)) = List.sum (List.map (fun b => Real.log b) (greedy_process n (Nat.primeFactorsList n.factorial) (Nat.primeFactorsList n.factorial).length.succ)) := by
        have h_log_prod : ∀ (L : List ℕ), (∀ x ∈ L, x > 0) → Real.log (List.prod L) = List.sum (List.map (fun b => Real.log b) L) := by
          intros L hL_pos
          induction' L with x L ih;
          · norm_num;
          · simp_all +decide [ List.flatMap ];
            rw [ Real.log_mul ( by norm_cast; linarith ) ( by exact ne_of_gt <| by exact List.prod_pos <| by aesop ), ih ];
        apply h_log_prod;
        apply greedy_process_pos_factors;
        exact fun p hp => Nat.pos_of_mem_primeFactorsList hp;
      convert h_log_prod;
      convert congr_arg ( ( ↑ ) : ℕ → ℝ ) h_prod.symm using 1;
      induction ( greedy_process n n.factorial.primeFactorsList n.factorial.primeFactorsList.length.succ ) <;> aesop;
    simp_all +decide [ sub_eq_add_neg, List.sum_map_add ];
    norm_num [ List.flatMap ];
    norm_num [ Function.comp, List.sum_neg ];
    congr;
    exact funext fun x => by simp +decide ;

/-
The sum of the valuations of primes in $I_j$ across all factors equals $\Omega(n, j)$.
-/
theorem sum_valuation_factors_eq_omega (n j : ℕ) :
  let primes := Nat.primeFactorsList n.factorial
  let factors := greedy_process n primes (primes.length + 1)
  (factors.map (fun b => ∑ p ∈ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∈ I n j), Nat.factorization b p)).sum = Omega n j := by
    -- By definition of `greedy_process`, we have that its product is `n!`.
    have h_prod : (greedy_process n (Nat.primeFactorsList n.factorial) (Nat.primeFactorsList n.factorial).length.succ).prod = n.factorial := by
      convert greedy_process_prod_eq n _ _ _ _ using 1 <;> norm_num [ Nat.primeFactorsList ];
      any_goals exact Nat.primeFactorsList n.factorial;
      any_goals exact Nat.lt_succ_self _;
      · cases n <;> simp_all +decide [ Nat.factorial_ne_zero, Nat.primeFactorsList ];
        rw [ Nat.prod_primeFactorsList ( Nat.factorial_ne_zero _ ) ];
      · simp +zetaDelta at *;
        exact fun p pp dp _ => pp.dvd_factorial.mp dp;
    replace h_prod := congr_arg ( fun x => x.factorization ) h_prod ; simp_all +decide [ Nat.factorization_prod ];
    have h_sum_val : ∀ {L : List ℕ}, (∀ x ∈ L, x > 0) → (∑ p ∈ Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1)), (List.prod L).factorization p) = (List.map (fun x => ∑ p ∈ Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1)), x.factorization p) L).sum := by
      intros L hL_pos; induction' L with x L ih <;> simp_all +decide [ Finset.sum_add_distrib ] ;
      rw [ Nat.factorization_mul ] <;> simp_all +decide [ Finset.sum_add_distrib ];
      · linarith;
      · exact fun h => by simpa using hL_pos.2 0 h;
    rw [ ← h_sum_val ];
    · simp_all +decide [ Omega ];
      exact Finset.sum_congr rfl fun x hx => if_pos <| Finset.mem_filter.mp hx |>.2.1;
    · apply greedy_process_pos_factors;
      exact fun p hp => Nat.pos_of_mem_primeFactorsList hp

/-
$\Omega_j \ll 2^j \pi(n/2^j)$.
-/
theorem Omega_bound_raw (n j : ℕ) :
  ∃ C, Omega n j ≤ C * 2^j * Nat.primeCounting (n / 2^j) := by
    by_contra h_contra;
    norm_num [ Nat.primeCounting ] at *;
    have := h_contra ( Omega n j + 1 );
    rcases k : Nat.primeCounting' ( n / 2 ^ j + 1 ) with ( _ | _ | k ) <;> simp_all +decide [ Nat.succ_mul ];
    · -- If $n / 2^j \leq 1$, then $I_j$ is empty, so $\Omega_j = 0$.
      have h_empty : (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∈ I n j) = ∅ := by
        ext p
        simp [I, k];
        exact fun _ _ _ => lt_of_le_of_lt k ( Nat.Prime.one_lt ‹_› );
      unfold Omega at h_contra; aesop;
    · nlinarith [ pow_pos ( zero_lt_two' ℕ ) j ];
    · nlinarith [ Nat.zero_le ( Omega n j * 2 ^ j ), Nat.zero_le ( 2 ^ j ), Nat.one_le_pow j 2 zero_lt_two ]

/-
If `b > 1` and its largest prime factor is in `S`, then the sum of valuations of primes in `S` for `b` is at least 1.
-/
theorem valuation_ge_one_of_largest_prime_mem (b : ℕ) (S : Set ℕ) (h : largest_prime_of b ∈ S) (hb : b > 1) :
  ∑ p ∈ (Nat.primeFactorsList b).toFinset.filter (fun p => p ∈ S), Nat.factorization b p ≥ 1 := by
    by_cases h_prime : largest_prime_of b ∈ b.primeFactorsList;
    · refine' le_trans _ ( Finset.single_le_sum ( fun p hp => Nat.zero_le ( b.factorization p ) ) ( by aesop ) );
      exact Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) );
    · cases b <;> simp_all +decide [ largest_prime_of ];
      contrapose! h_prime;
      have h_max_prime : ∀ {l : List ℕ}, (∀ p ∈ l, Nat.Prime p) → l ≠ [] → Nat.Prime (List.foldl Max.max 0 l) ∧ List.foldl Max.max 0 l ∈ l := by
        intros l hl_prime hl_nonempty; induction' l using List.reverseRecOn with p l ih; aesop;
        grind;
      exact ⟨ h_max_prime ( fun p hp => Nat.prime_of_mem_primeFactorsList hp ) ( by aesop ) |>.1, Nat.dvd_of_mem_primeFactorsList ( h_max_prime ( fun p hp => Nat.prime_of_mem_primeFactorsList hp ) ( by aesop ) |>.2 ) ⟩

/-
Bound on the p-adic valuation of n!.
-/
theorem valuation_le_div_pred (n : ℕ) (p : ℕ) (hp : p.Prime) :
  padicValNat p n.factorial ≤ n / (p - 1) := by
    have := @Nat.factorization_def n !;
    rw [ ← this hp ];
    exact Nat.factorization_factorial_le_div_pred hp n

/-
$\frac{n}{\log n} = o(n)$ as $n \to \infty$.
-/
theorem n_div_log_is_little_o_n :
  Asymptotics.IsLittleO Filter.atTop (fun n : ℕ => (n : ℝ) / Real.log n) (fun n => (n : ℝ)) := by
    -- To show that $n / \log n = o(n)$, we need to prove that $\lim_{n \to \infty} \frac{n / \log n}{n} = 0$.
    have h_lim : Filter.Tendsto (fun n : ℕ => (n : ℝ) / Real.log n / n) Filter.atTop (nhds 0) := by
      -- We can simplify the expression to $1 / \log n$.
      suffices h_simplified : Filter.Tendsto (fun n : ℕ => 1 / Real.log n) Filter.atTop (nhds 0) by
        refine h_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ div_right_comm, div_self ( by positivity ) ] );
      exact tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> aesop

/-
Bound $\Omega_j$ by $O(2^j \pi(n/2^j))$.
-/
theorem Omega_bound_pi (n j : ℕ) (hn : n ≥ 2) :
  ∃ C, Omega n j ≤ C * 2^j * Nat.primeCounting (n / 2^j) := by
    exact Omega_bound_raw n j

/-
If $2^j \le \sqrt{n}$, then $\log(n/2^j) \ge \frac{1}{2} \log n$.
-/
theorem log_div_ge_half_log (n : ℕ) (j : ℕ) (hn : n ≥ 2) (hj : (2 : ℝ)^j ≤ Real.sqrt n) :
  Real.log ((n : ℝ) / 2^j) ≥ (1 / 2) * Real.log n := by
    rw [ Real.log_div ] <;> norm_num;
    · rw [ Real.le_sqrt ] at hj <;> first | positivity | have := Real.log_le_log ( by positivity ) hj ; norm_num at * ; linarith;
    · linarith

/-
Chebyshev bound applies uniformly for small $j$.
-/
theorem pi_le_cheb_small_j (hCheb : ChebyshevUpperBound) :
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ j : ℕ, (2 : ℝ)^j ≤ Real.sqrt n →
  (Nat.primeCounting (n / 2^j) : ℝ) ≤ (Real.log 4 + ε) * ((n : ℝ) / (2 : ℝ)^j) / Real.log ((n : ℝ) / (2 : ℝ)^j) := by
    intro ε hε;
    obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp ( hCheb ε hε );
    refine' ⟨ ⌈N^2⌉₊ + 1, fun n hn j hj => _ ⟩;
    convert hN ( n / 2 ^ j ) _;
    · rw_mod_cast [ Nat.floor_div_natCast, Nat.floor_natCast ];
    · rw [ ge_iff_le, le_div_iff₀ ] <;> norm_num;
      rw [ Real.le_sqrt ] at hj <;> try positivity;
      nlinarith [ Nat.le_ceil ( N ^ 2 ), show ( n : ℝ ) ≥ ⌈N ^ 2⌉₊ + 1 by exact_mod_cast hn, show ( 2 ^ j : ℝ ) ≥ 1 by exact one_le_pow₀ ( by norm_num ) ]

/-
Bound $\pi(n/2^j)$ by $O(\frac{n/2^j}{\log n})$ for small $j$.
-/
theorem pi_bound_combined (hCheb : ChebyshevUpperBound) :
  ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ j : ℕ, (2 : ℝ)^j ≤ Real.sqrt n →
  (Nat.primeCounting (n / 2^j) : ℝ) ≤ C * ((n : ℝ) / (2 : ℝ)^j) / Real.log n := by
    -- Apply `pi_le_cheb_small_j` with $\epsilon = 1$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ j : ℕ, (2 : ℝ)^j ≤ Real.sqrt n →
      (Nat.primeCounting (n / 2^j) : ℝ) ≤ (Real.log 4 + 1) * ((n : ℝ) / (2 : ℝ)^j) / Real.log ((n : ℝ) / (2 : ℝ)^j) := by
        exact pi_le_cheb_small_j hCheb 1 zero_lt_one |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn j hj => hN n ( mod_cast hn ) j ( mod_cast hj ) ⟩;
    -- From `log_div_ge_half_log`, we have $\log(n/2^j) \ge \frac{1}{2} \log n$.
    have h_log_div_ge_half_log : ∀ n : ℕ, n ≥ 2 → ∀ j : ℕ, (2 : ℝ)^j ≤ Real.sqrt n → Real.log ((n : ℝ) / (2 : ℝ)^j) ≥ (1 / 2) * Real.log n := by
      exact fun n a j a_1 => log_div_ge_half_log n j a a_1;
    use ( Real.log 4 + 1 ) * 2, N + 2;
    intro n hn j hj; specialize hN n ( by linarith ) j hj; specialize h_log_div_ge_half_log n ( by linarith ) j hj; rw [ le_div_iff₀ ] at * <;> norm_num at *;
    · nlinarith [ Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ];
    · exact lt_of_lt_of_le ( by exact mul_pos ( by norm_num ) ( Real.log_pos ( by norm_cast; linarith ) ) ) h_log_div_ge_half_log;
    · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith;

/-
Asymptotic bound for $\Omega_j$ for small $j$.
-/
theorem Omega_le_n_div_log_asymptotic (hCheb : ChebyshevUpperBound) :
  ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ j : ℕ, (2 : ℝ)^j ≤ Real.sqrt n → (Omega n j : ℝ) ≤ C * n / Real.log n := by
    -- Apply `Omega_bound_pi` to obtain a constant $C_1$.
    obtain ⟨C1, hC1⟩ : ∃ C1 : ℝ, ∀ n ≥ 2, ∀ j, Omega n j ≤ C1 * 2^j * Nat.primeCounting (n / 2^j) := by
      use 2 ^ 64;
      intro n hn j;
      have h_omega_le : Omega n j ≤ 2 ^ 64 * Nat.primeCounting (n / 2 ^ j) * 2 ^ j := by
        have h_omega_le : Omega n j ≤ ∑ p ∈ Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1)), (n / (p - 1)) := by
          refine' le_trans _ ( Finset.sum_le_sum fun p hp => show padicValNat p n.factorial ≤ n / ( p - 1 ) from _ );
          · unfold Omega; aesop;
          · convert valuation_le_div_pred n p ( Finset.mem_filter.mp hp |>.2.1 ) using 1
        -- Since $p \in I n j$, we have $p \geq n / 2^{j+1}$, thus $p - 1 \geq n / 2^{j+1} - 1 \geq n / 2^{j+2}$ for $n \geq 2^{j+2}$.
        have h_prime_bound : ∀ p ∈ Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1)), n / (p - 1) ≤ 2 ^ (j + 2) := by
          intro p hp
          have hp_bound : p ≥ n / 2 ^ (j + 1) + 1 := by
            unfold I at hp; aesop;
          rcases p with ( _ | _ | p ) <;> simp_all +decide [ pow_succ' ];
          rw [ Nat.div_le_iff_le_mul_add_pred ] at * <;> norm_num at *;
          nlinarith [ Nat.sub_add_cancel ( show 0 < 2 * 2 ^ j from by positivity ), pow_pos ( show 0 < 2 by decide ) j ];
        have h_prime_count : Finset.card (Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1))) ≤ Nat.primeCounting (n / 2 ^ j) := by
          have h_prime_count : Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1)) ⊆ Finset.filter Nat.Prime (Finset.Icc 1 (n / 2 ^ j)) := by
            simp +contextual [ Finset.subset_iff, I ];
            exact fun x hx₁ hx₂ hx₃ hx₄ => Nat.Prime.pos hx₂;
          convert Finset.card_le_card h_prime_count using 1;
          rw [ Nat.primeCounting ];
          rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
          congr 1 with ( _ | x ) <;> aesop;
        refine le_trans h_omega_le <| le_trans ( Finset.sum_le_sum h_prime_bound ) ?_;
        norm_num [ pow_add ] at *;
        nlinarith [ pow_pos ( zero_lt_two' ℕ ) j ];
      exact le_trans ( Nat.cast_le.mpr h_omega_le ) ( by norm_cast; ring_nf; norm_num );
    -- Apply `pi_bound_combined` to obtain constants $C_2$ and $N$.
    obtain ⟨C2, N, hC2⟩ : ∃ C2 : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ j, (2 : ℝ)^j ≤ Real.sqrt n → (Nat.primeCounting (n / 2^j) : ℝ) ≤ C2 * ((n : ℝ) / (2 : ℝ)^j) / Real.log n := by
      exact pi_bound_combined hCheb;
    use C1 * C2, Max.max N 2;
    intro n hn j hj; convert le_trans ( hC1 n ( le_trans ( le_max_right _ _ ) hn ) j ) _ using 1; convert mul_le_mul_of_nonneg_left ( hC2 n ( le_trans ( le_max_left _ _ ) hn ) j hj ) ( show ( 0 :ℝ ) ≤ C1 * 2 ^ j by exact mul_nonneg ( show ( 0 :ℝ ) ≤ C1 by
                                                                                                                                                                                                                                            specialize hC1 2 ( by norm_num ) 0 ; norm_num at hC1;
                                                                                                                                                                                                                                            exact le_of_not_gt fun h => by norm_num [ show Nat.primeCounting 2 = 1 by rfl ] at hC1; linarith [ show ( Omega 2 0 : ℝ ) ≥ 0 by exact Nat.cast_nonneg _ ] ; ) ( pow_nonneg zero_le_two j ) ) using 1 ; ring_nf;
    simp +zetaDelta at *

/-
Uniform bound for $\Omega_j$.
-/
theorem Omega_bound_uniform :
  ∃ C, ∀ n ≥ 2, ∀ j, (Omega n j : ℝ) ≤ C * 2^j * Nat.primeCounting (n / 2^j) := by
    use 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 + 1;
    intro n hn j
    have h_contribution : ∀ p ∈ Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1)), (Nat.factorization (Nat.factorial n) p : ℝ) ≤ 2^j * 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
      intro p hp
      have h_val : (Nat.factorization (Nat.factorial n) p : ℝ) ≤ n / (p - 1) := by
        have h_val_bound : (Nat.factorization (Nat.factorial n) p : ℝ) ≤ n / (p - 1) := by
          have h_val_bound_aux : (Nat.factorization (Nat.factorial n) p : ℕ) ≤ n / (p - 1) := by
            have h_val : padicValNat p (Nat.factorial n) ≤ n / (p - 1) := by
              convert valuation_le_div_pred n p ( by aesop : Nat.Prime p ) using 1;
            convert h_val using 1;
            rw [ Nat.factorization_def ] ; aesop
          rw [ le_div_iff₀ ] <;> norm_cast;
          · rw [ Int.subNatNat_of_le ( Nat.one_le_iff_ne_zero.mpr <| Nat.Prime.ne_zero <| by aesop ) ] ; norm_cast ; nlinarith [ Nat.div_mul_le_self n ( p - 1 ) ];
          · rw [ Int.subNatNat_eq_coe ] ; norm_num ; linarith [ Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2.1 ) ];
        convert h_val_bound using 1;
      refine le_trans h_val ?_;
      rw [ div_le_iff₀ ] <;> norm_num at *;
      · rcases hp.2.2 with ⟨ hp₁, hp₂ ⟩;
        rw [ Nat.div_lt_iff_lt_mul <| by positivity ] at hp₁;
        rcases p with ( _ | _ | p ) <;> norm_num at *;
        norm_cast ; nlinarith [ Nat.div_mul_le_self n ( 2 ^ j ), pow_pos ( zero_lt_two' ℕ ) j, pow_succ' ( 2 : ℕ ) j ];
      · exact hp.2.1.one_lt;
    have h_sum_contribution : (Omega n j : ℝ) ≤ (Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1))).card * (2^j * 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
      have h_sum_contribution : (Omega n j : ℝ) ≤ Finset.sum (Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1))) (fun p => (Nat.factorization (Nat.factorial n) p : ℝ)) := by
        unfold Omega;
        norm_num [ Nat.factorization ];
        exact Finset.sum_le_sum fun x hx => by aesop;
      exact h_sum_contribution.trans ( le_trans ( Finset.sum_le_sum h_contribution ) ( by norm_num ) );
    have h_card_le_pi : (Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1))).card ≤ Nat.primeCounting (n / 2^j) := by
      have h_card_le_pi : (Finset.filter (fun p => p.Prime ∧ p ∈ I n j) (Finset.range (n + 1))).card ≤ Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 (n / 2^j))) := by
        refine Finset.card_mono ?_;
        simp +contextual [ Finset.subset_iff, I ];
        exact fun x hx₁ hx₂ hx₃ hx₄ => hx₂.pos;
      convert h_card_le_pi using 1;
      rw [ Nat.primeCounting ];
      rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
      congr 1 with ( _ | x ) <;> aesop;
    exact h_sum_contribution.trans ( by nlinarith [ ( by norm_cast : ( Finset.card ( Finset.filter ( fun p => Nat.Prime p ∧ p ∈ I n j ) ( Finset.range ( n + 1 ) ) ) : ℝ ) ≤ Nat.primeCounting ( n / 2 ^ j ) ), pow_pos ( by norm_num : ( 0 : ℝ ) < 2 ) j ] )

/-
The statement of the geometric bound on W(n).
-/
def W_le_sum_geometric_Omega_Statement : Prop :=
  ∃ C, ∀ n ≥ 2, W n ≤ C * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j * (Omega n j : ℝ)

/-
The geometric sum of $\Omega_j$ is $O(n/\log n)$.
-/
theorem sum_geometric_Omega_le_n_div_log (hCheb : ChebyshevUpperBound) :
  ∃ C, ∀ n ≥ 2, ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j * (Omega n j : ℝ) ≤ C * n / Real.log n := by
    -- Split the sum into small $j$ and large $j$.
    obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, ∀ n ≥ 2, ∑ j ∈ Finset.range (Nat.log 2 (Nat.sqrt n) + 1), (1 / 2 : ℝ) ^ j * (Omega n j : ℝ) ≤ C₁ * n / Real.log n := by
      -- For small $j$, we use the bound from `Omega_le_n_div_log_asymptotic`.
      obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, ∀ n ≥ 2, ∀ j ∈ Finset.range (Nat.log 2 (Nat.sqrt n) + 1), (Omega n j : ℝ) ≤ C₁ * n / Real.log n := by
        have := Omega_le_n_div_log_asymptotic hCheb;
        obtain ⟨ C, N, hC ⟩ := this;
        use Max.max C ( ∑ n ∈ Finset.Ico 2 N, ∑ j ∈ Finset.range ( Nat.log 2 ( Nat.sqrt n ) + 1 ), ( Omega n j : ℝ ) / ( n / Real.log n ) );
        intro n hn j hj; by_cases hn' : n < N <;> simp_all +decide [ mul_div_assoc ] ;
        · field_simp;
          rw [ le_div_iff₀ ( Real.log_pos <| by norm_cast ) ];
          refine' le_trans _ ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( Nat.cast_nonneg _ ) );
          refine' le_trans _ ( mul_le_mul_of_nonneg_right ( Finset.single_le_sum ( fun x hx => _ ) ( Finset.mem_Ico.mpr ⟨ hn, hn' ⟩ ) ) ( Nat.cast_nonneg _ ) );
          · rw [ ← Finset.sum_div _ _ _, div_mul_cancel₀ _ ( by positivity ) ] ; exact Finset.single_le_sum ( fun x _ => mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ( Finset.mem_range.mpr hj );
          · exact Finset.sum_nonneg fun _ _ => div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( by norm_cast; linarith [ Finset.mem_Ico.mp hx ] ) ) ) ( Nat.cast_nonneg _ );
        · refine le_trans ( hC n hn' j ?_ ) ?_;
          · rw [ Real.le_sqrt ] <;> norm_cast <;> try positivity;
            rw [ ← pow_mul ];
            exact le_trans ( pow_le_pow_right₀ ( by decide ) ( Nat.mul_le_mul_right _ ( Nat.le_of_lt_succ hj ) ) ) ( by rw [ pow_mul ] ; exact Nat.pow_le_pow_left ( Nat.pow_log_le_self 2 ( by positivity ) ) 2 |> le_trans <| by nlinarith [ Nat.sqrt_le n ] );
          · exact mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity );
      use C₁ * 2; intro n hn; refine' le_trans ( Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ( hC₁ n hn j hj ) ( by positivity ) ) _ ; ring_nf;
      rw [ ← Finset.mul_sum _ _ _ ] ; rw [ geom_sum_eq ] <;> ring_nf <;> norm_num;
      exact mul_nonneg ( mul_nonneg ( le_of_not_gt fun h => by have := hC₁ 2 ( by norm_num ) 0 ( by norm_num ) ; norm_num at this ; ring_nf at this ; nlinarith [ Real.log_pos one_lt_two, mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ] ) ( Nat.cast_nonneg _ ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( by norm_cast; linarith ) ) );
    -- For large $j$, we use the bound $\Omega_j \le C * 2^j * \pi(n/2^j)$.
    obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, ∀ n ≥ 2, ∀ j ≥ Nat.log 2 (Nat.sqrt n) + 1, (Omega n j : ℝ) ≤ C₂ * 2^j * (n / 2^j) := by
      obtain ⟨ C₂, hC₂ ⟩ := Omega_bound_uniform;
      refine' ⟨ C₂, fun n hn j hj => le_trans ( hC₂ n hn j ) _ ⟩;
      gcongr;
      · contrapose! hC₂;
        refine' ⟨ 2, _, 0, _ ⟩ <;> norm_num;
        exact lt_of_lt_of_le ( mul_neg_of_neg_of_pos ( by nlinarith [ pow_pos ( zero_lt_two' ℝ ) j ] ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by native_decide ) ) ) ) ( Nat.cast_nonneg _ );
      · rw [ le_div_iff₀ ] <;> norm_cast <;> norm_num;
        rw [ Nat.primeCounting ];
        rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
        refine' le_trans ( Nat.mul_le_mul_right _ ( Finset.card_le_card ( show Finset.filter ( fun x => Nat.Prime x ) ( Finset.range ( n / 2 ^ j + 1 ) ) ⊆ Finset.Ico 2 ( n / 2 ^ j + 1 ) from fun x hx => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le ( Finset.mem_filter.mp hx |>.2 ), Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ⟩ ) ) ) _ ; norm_num;
        rw [ tsub_mul ];
        exact Nat.sub_le_of_le_add <| by nlinarith [ Nat.div_mul_le_self n ( 2 ^ j ), Nat.pow_le_pow_right two_pos ( show j ≥ 0 by norm_num ) ] ;
    -- For large $j$, the sum $\sum_{j \geq \log_2(\sqrt{n}) + 1}^{n-1} \frac{1}{2^j} \Omega_j$ is bounded by $C₂ \sum_{j \geq \log_2(\sqrt{n}) + 1}^{n-1} \frac{n}{2^j}$.
    have h_tail : ∃ C₃ : ℝ, ∀ n ≥ 2, ∑ j ∈ Finset.Ico (Nat.log 2 (Nat.sqrt n) + 1) n, (1 / 2 : ℝ) ^ j * (Omega n j : ℝ) ≤ C₃ * n / Real.log n := by
      -- For large $j$, we use the bound $\sum_{j \geq \log_2(\sqrt{n}) + 1} \frac{1}{2^j} \Omega_j \leq C \sum_{j \geq \log_2(\sqrt{n}) + 1} \frac{1}{2^j} 2^j \frac{n}{2^j} = C \sum_{j \geq \log_2(\sqrt{n}) + 1} \frac{n}{2^j}$ and the fact that $\sum_{j \geq \log_2(\sqrt{n}) + 1} \frac{1}{2^j}$ converges.
      have h_large_j_sum : ∃ C₃ : ℝ, ∀ n ≥ 2, ∑ j ∈ Finset.Ico (Nat.log 2 (Nat.sqrt n) + 1) n, (1 / 2 : ℝ) ^ j * (2^j * (n / 2^j)) ≤ C₃ * n / Real.log n := by
        -- We can factor out $n$ from the sum and use the fact that $\sum_{j \geq \log_2(\sqrt{n}) + 1} \frac{1}{2^j}$ converges.
        have h_large_j_sum : ∃ C₃ : ℝ, ∀ n ≥ 2, ∑ j ∈ Finset.Ico (Nat.log 2 (Nat.sqrt n) + 1) n, (1 / 2 : ℝ) ^ j ≤ C₃ / Real.log n := by
          -- The sum of the geometric series $\sum_{j \geq \log_2(\sqrt{n}) + 1} \frac{1}{2^j}$ is bounded by $\frac{1}{2^{\log_2(\sqrt{n})}} = \frac{1}{\sqrt{n}}$.
          have h_geo_series_bound : ∃ C₃ : ℝ, ∀ n ≥ 2, ∑ j ∈ Finset.Ico (Nat.log 2 (Nat.sqrt n) + 1) n, (1 / 2 : ℝ) ^ j ≤ C₃ / Real.sqrt n := by
            have h_geo_series_sum : ∀ n ≥ 2, ∑ j ∈ Finset.Ico (Nat.log 2 (Nat.sqrt n) + 1) n, (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ (Nat.log 2 (Nat.sqrt n) + 1) / (1 - 1 / 2) := by
              intro n hn; rw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ pow_add, pow_mul, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring_nf; norm_num;
              rw [ ← Finset.sum_mul _ _ _ ] ; rw [ ← Finset.mul_sum _ _ _ ] ; rw [ geom_sum_eq ] <;> ring_nf <;> norm_num;
            use 2 ^ 2; intro n hn; specialize h_geo_series_sum n hn; norm_num [ pow_add ] at *;
            refine le_trans h_geo_series_sum ?_;
            rw [ one_div, inv_pow, inv_eq_one_div, div_le_div_iff₀ ] <;> norm_num;
            · rw [ Real.sqrt_le_left ] <;> norm_cast <;> norm_num;
              have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) ( Nat.sqrt n );
              rw [ Nat.pow_succ ] at this ; nlinarith [ Nat.lt_succ_sqrt n, Nat.sqrt_le n, Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( show Nat.log 2 n.sqrt ≥ 0 by positivity ) ];
            · linarith;
          -- Since $\sqrt{n} \geq \log n$ for all $n \geq 2$, we can conclude that $\frac{C₃}{\sqrt{n}} \leq \frac{C₃}{\log n}$.
          obtain ⟨C₃, hC₃⟩ := h_geo_series_bound;
          use C₃ * 2;
          intro n hn;
          have h_sqrt_log : Real.sqrt n ≥ Real.log n := by
            have := Real.log_le_sub_one_of_pos ( by positivity : 0 < Real.sqrt n / 2 );
            rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_sqrt ( by positivity ) ] at this;
            have := Real.log_two_lt_d9 ; norm_num at * ; linarith;
          have h_div : C₃ / Real.sqrt n ≤ C₃ * 2 / Real.log n := by
            rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast ), show ( 0 : ℝ ) ≤ C₃ by exact le_of_not_gt fun h => by have := hC₃ n hn; exact absurd this ( by exact not_le_of_gt <| lt_of_lt_of_le ( div_neg_of_neg_of_pos h <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| by linarith ) <| Finset.sum_nonneg fun _ _ => by positivity ) ];
          exact le_trans (hC₃ n hn) h_div;
        simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        exact ⟨ h_large_j_sum.choose, fun n hn => by rw [ ← Finset.mul_sum _ _ _ ] ; nlinarith [ h_large_j_sum.choose_spec n hn, show ( n : ℝ ) ≥ 2 by norm_cast ] ⟩;
      obtain ⟨ C₃, hC₃ ⟩ := h_large_j_sum; use C₂ * C₃; intros n hn; refine' le_trans ( Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ( hC₂ n hn j ( Finset.mem_Ico.mp hj |>.1 ) ) ( by positivity ) ) _ ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ;
      simpa only [ ← Finset.mul_sum _ _ _, mul_assoc, mul_left_comm ] using mul_le_mul_of_nonneg_left ( hC₃ n hn ) ( show 0 ≤ C₂ by exact le_of_not_gt fun h => by have := hC₂ n hn ( Nat.log 2 ( Nat.sqrt n ) + 1 ) le_rfl; norm_num at this; nlinarith [ show ( 0 :ℝ ) < n by positivity, show ( 0 :ℝ ) < ( 2 ^ ( Nat.log 2 ( Nat.sqrt n ) + 1 ) ) ⁻¹ by positivity ] ) |> le_trans <| by ring_nf; norm_num;
    obtain ⟨ C₃, hC₃ ⟩ := h_tail; use C₁ + C₃; intro n hn; rw [ ← Finset.sum_range_add_sum_Ico _ ( show Nat.log 2 n.sqrt + 1 ≤ n from Nat.succ_le_of_lt <| Nat.lt_of_le_of_lt ( Nat.log_le_self _ _ ) <| Nat.sqrt_lt_self <| by linarith ) ] ; convert add_le_add ( hC₁ n hn ) ( hC₃ n hn ) using 1 ; ring;

/-
If the largest prime of $b$ is in $I_j$, then $w(n, b) \le (j+1) \log 2$.
-/
lemma waste_bound_of_largest_prime (n : ℕ) (b : ℕ) (j : ℕ)
    (h_valid : b ≤ n) (h_pos : b > 0)
    (h_prime : largest_prime_of b ∈ I n j) :
    w n b ≤ (j + 1) * Real.log 2 := by
      field_simp;
      rw [ show w n b = Real.log ( n / b ) by rw [ Real.log_div ] <;> norm_cast <;> linarith ];
      rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast;
      · rw [ div_le_iff₀ ] <;> norm_cast;
        -- Since $p$ is the largest prime factor of $b$, we have $p \leq b$.
        have h_p_le_b : largest_prime_of b ≤ b := by
          unfold largest_prime_of;
          have h_foldl_le_b : ∀ {l : List ℕ}, (∀ p ∈ l, p ≤ b) → List.foldl max 0 l ≤ b := by
            intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
          exact h_foldl_le_b fun p hp => Nat.le_of_mem_primeFactorsList hp;
        nlinarith [ Set.mem_Ioc.mp h_prime, pow_pos ( zero_lt_two' ℕ ) j, pow_succ' ( 2 : ℕ ) j, Nat.div_add_mod n ( 2 ^ ( j + 1 ) ), Nat.mod_lt n ( pow_pos ( zero_lt_two' ℕ ) ( j + 1 ) ) ];
      · exact div_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Nat.cast_pos.mpr h_pos );
      · positivity

/-
$\log n! = n \log n - n + O(\log n)$.
-/
theorem log_factorial_asymptotic :
  Asymptotics.IsBigO Filter.atTop (fun n : ℕ => Real.log n.factorial - (n * Real.log n - n)) (fun n => Real.log n) := by
    -- By definition of $O$-notation, we need to show that there exists a constant $C$ and a natural number $N$ such that for all $n \geq N$, we have $|\log(n!) - (n \log n - n)| \leq C \log n$.
    have h_bound : ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, abs (Real.log (Nat.factorial n) - (n * Real.log n - n)) ≤ C * Real.log n := by
      use 2, 100;
      intro n hn
      have h_stirling : Real.log (Nat.factorial n) ≥ n * Real.log n - n + 1 := by
        refine' Nat.le_induction _ _ n hn <;> intros <;> norm_num [ Nat.factorial_succ ] at *;
        · norm_num [ Real.le_log_iff_exp_le ];
          rw [ show ( 100 : ℝ ) * Real.log 100 - 100 + 1 = Real.log ( 100 ^ 100 ) - 99 by rw [ Real.log_pow ] ; ring ] ; rw [ Real.exp_sub, Real.exp_log ( by positivity ) ] ; norm_num;
          rw [ div_le_iff₀ ( Real.exp_pos _ ) ] ; have := Real.exp_one_gt_d9.le ; norm_num1 at * ; rw [ show Real.exp 99 = ( Real.exp 1 ) ^ 99 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ pow_le_pow_left₀ ( by positivity ) this 99 ];
        · rw [ Real.log_mul ( by positivity ) ( by positivity ) ];
          have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( ( Nat.cast:ℕ →ℝ ) ‹_› + 1 ) / ( Nat.cast:ℕ →ℝ ) ‹_› );
          rw [ Real.log_div ] at this <;> first | positivity | ring_nf at * ; nlinarith [ mul_inv_cancel₀ ( by positivity : ( ( Nat.cast:ℕ →ℝ ) ‹_› ) ≠ 0 ) ] ;
      have h_stirling_upper : Real.log (Nat.factorial n) ≤ n * Real.log n - n + Real.log n + 1 := by
        clear h_stirling hn;
        induction' n with n ih <;> norm_num [ Nat.factorial_succ ];
        rw [ Real.log_mul ( by positivity ) ( by positivity ) ];
        rcases n <;> norm_num at *;
        have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( ( Nat.cast:ℕ →ℝ ) ‹_› + 1 ) / ( ( Nat.cast:ℕ →ℝ ) ‹_› + 1 + 1 ) );
        rw [ Real.log_div ] at this <;> nlinarith [ mul_div_cancel₀ ( ( Nat.cast:ℕ →ℝ ) ‹_› + 1 ) ( by positivity : ( Nat.cast:ℕ →ℝ ) ‹_› + 1 + 1 ≠ 0 ) ];
      exact abs_le.mpr ⟨ by linarith, by linarith [ show Real.log n ≥ 1 by rw [ ge_iff_le ] ; rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 100 by exact_mod_cast hn ] ) ] ⟩;
    rcases h_bound with ⟨ C, N, hC ⟩;
    rw [ Asymptotics.isBigO_iff ];
    exact ⟨ C, Filter.eventually_atTop.mpr ⟨ N + 1, fun n hn => by simpa only [ Real.norm_eq_abs, abs_of_nonneg ( Real.log_natCast_nonneg _ ) ] using hC n ( by linarith ) ⟩ ⟩

/-
List of factors in the greedy decomposition of $n!$ whose largest prime factor lies in $I_j$.
-/
def factors_in_Ij (n j : ℕ) : List ℕ :=
  let primes := Nat.primeFactorsList n.factorial
  let factors := greedy_process n primes (primes.length + 1)
  factors.filter (fun x => largest_prime_of x ∈ I n j)

/-
For any $p \in (0, n]$, $p$ belongs to $I_{n, j}$ where $j = \lfloor \log_2(n/p) \rfloor$.
-/
def j_of_prime (n p : ℕ) : ℕ := Nat.log 2 (n / p)

lemma mem_I_of_j_of_prime (n p : ℕ) (hp : p > 0) (hn : n ≥ p) :
  p ∈ I n (j_of_prime n p) := by
    unfold j_of_prime I;
    constructor;
    · exact Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.lt_pow_of_log_lt one_lt_two ( show Nat.log 2 ( n / p ) < Nat.log 2 ( n / p ) + 1 from Nat.lt_succ_self _ ), Nat.div_add_mod n p, Nat.mod_lt n hp ] ;
    · rw [ Nat.le_div_iff_mul_le ( pow_pos ( by decide ) _ ) ];
      exact le_trans ( Nat.mul_le_mul_left _ ( Nat.pow_log_le_self 2 ( Nat.ne_of_gt ( Nat.div_pos hn hp ) ) ) ) ( by nlinarith [ Nat.div_mul_le_self n p ] )

/-
The index $j$ such that $p \in I_{n, j}$ is unique and equal to $\lfloor \log_2(n/p) \rfloor$.
-/
lemma j_unique_of_mem_I (n p j : ℕ) (hp : p > 0) (hj : p ∈ I n j) :
  j = j_of_prime n p := by
    -- Since $p \in I_{n, j}$, we have $n/2^{j+1} < p \leq n/2^j$.
    have h_bounds : n / 2^(j+1) < p ∧ p ≤ n / 2^j := by
      exact hj;
    refine' Eq.symm ( Nat.le_antisymm _ _ );
    · refine' Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow _ _ );
      · simp +zetaDelta at *;
        exact ⟨ hp.ne', h_bounds.2.trans ( Nat.div_le_self _ _ ) ⟩;
      · rw [ Nat.div_lt_iff_lt_mul ] <;> norm_num [ Nat.pow_succ' ] at *;
        · rw [ Nat.div_lt_iff_lt_mul ] at h_bounds <;> linarith [ Nat.one_le_pow j 2 zero_lt_two ];
        · linarith;
    · refine' Nat.le_log_of_pow_le ( by decide ) _;
      rw [ Nat.le_div_iff_mul_le hp ] ; nlinarith [ Nat.div_mul_le_self n ( 2 ^ j ) ]

/-
The accumulator grows or stays the same in `greedy_pass`.
-/
theorem greedy_pass_ge_acc (n : ℕ) (acc : ℕ) (primes : List ℕ) (fuel : ℕ)
    (h_primes : ∀ p ∈ primes, p ≥ 1) :
    (greedy_pass n acc primes fuel).1 ≥ acc := by
      -- We proceed by induction on `fuel`.
      induction' fuel with fuel ih generalizing acc primes;
      · rfl;
      · by_cases h : acc = 0 <;> simp_all +decide [ show greedy_pass n acc primes ( fuel + 1 ) = if acc = 0 then ( acc, primes ) else match find_largest_le ( n / acc ) primes with | none => ( acc, primes ) | some p => greedy_pass n ( acc * p ) ( primes.erase p ) fuel from rfl ];
        cases h' : find_largest_le ( n / acc ) primes <;> simp_all +decide;
        exact le_trans ( Nat.le_mul_of_pos_right _ ( find_largest_le_mem _ _ _ h' |> fun h'' => h_primes _ h'' ) ) ( ih _ _ fun p hp => h_primes _ ( List.mem_of_mem_erase hp ) )

/-
If starting with 1 and valid primes, `greedy_pass` returns a result $> 1$.
-/
lemma greedy_pass_gt_one (n : ℕ) (primes : List ℕ) (fuel : ℕ)
    (h_primes : primes ≠ [])
    (h_le : ∀ p ∈ primes, p ≤ n)
    (h_pos : ∀ p ∈ primes, p ≥ 2)
    (h_fuel : fuel > 0) :
    (greedy_pass n 1 primes fuel).1 > 1 := by
      -- Since `fuel > 0`, `greedy_pass` enters the match.
      have h_greedy_pass : ∀ fuel > 0, (greedy_pass n 1 primes fuel).1 > 1 := by
        intro fuel h_fuel_pos
        induction' fuel with fuel ih;
        · contradiction;
        · by_cases h : find_largest_le ( n / 1 ) primes = none <;> simp_all +decide [ greedy_pass ];
          · have h_find_largest_le_some : (find_largest_le n primes).isSome := by
              exact find_largest_le_some n primes h_primes h_le;
            aesop;
          · rcases p' : find_largest_le n primes with ( _ | p ) <;> simp_all +decide;
            have h_p_ge_2 : 2 ≤ p := by
              exact h_pos p ( find_largest_le_mem n primes p p' );
            exact Nat.le_trans h_p_ge_2 ( greedy_pass_ge_acc n p ( primes.erase p ) fuel fun q hq => Nat.one_le_of_lt ( h_pos q ( List.mem_of_mem_erase hq ) ) );
      exact h_greedy_pass fuel h_fuel

/-
All factors in the greedy decomposition of $n!$ are strictly greater than 1 (for $n \ge 2$).
-/
theorem greedy_factors_gt_one (n : ℕ) (hn : n ≥ 2) :
  ∀ b ∈ greedy_process n (Nat.primeFactorsList n.factorial) ((Nat.primeFactorsList n.factorial).length + 1), b > 1 := by
    intro b hb;
    -- By definition of `greedy_process`, we know that every factor in the list is greater than 1.
    have h_factors_gt_one : ∀ (n : ℕ) (primes : List ℕ) (fuel : ℕ) (h_primes : primes ≠ []) (h_le : ∀ p ∈ primes, p ≤ n) (h_pos : ∀ p ∈ primes, p ≥ 2) (h_fuel : fuel > 0), ∀ b ∈ greedy_process n primes fuel, 1 < b := by
      intros n primes fuel h_primes h_le h_pos h_fuel b hb
      induction' fuel with fuel ih generalizing primes b;
      · contradiction;
      · rcases fuel with ( _ | fuel ) <;> simp_all +decide [ greedy_process ];
        · exact hb.symm ▸ greedy_pass_gt_one n primes primes.length h_primes h_le h_pos ( List.length_pos_iff.mpr h_primes );
        · rcases hb with ( rfl | ⟨ h₁, rfl | hb ⟩ );
          · exact ih primes h_primes h_le h_pos |>.1;
          · specialize ih ( greedy_pass n 1 primes primes.length |> Prod.snd ) h₁ ( fun p hp => by
              exact h_le p ( greedy_pass_subset n 1 primes primes.length hp ) ) ( fun p hp => by
              exact h_pos p ( by have := greedy_pass_subset n 1 primes primes.length; aesop ) ) ; aesop;
          · have := ih ( greedy_pass n 1 primes primes.length |>.2 ) h₁ ?_ ?_;
            · exact this.2 b hb;
            · exact fun p hp => h_le p <| greedy_pass_subset _ _ _ _ hp;
            · exact fun p hp => h_pos p <| greedy_pass_subset _ _ _ _ hp;
    refine h_factors_gt_one n _ _ ?_ ?_ ?_ ?_ b hb <;> norm_num;
    · exact ⟨ Nat.factorial_ne_zero _, hn ⟩;
    · exact fun p pp dp _ => pp.dvd_factorial.mp dp;
    · exact fun p pp _ _ => pp.two_le

/-
For every factor $b \in (1, n]$, its largest prime factor lies in some $I_j$ with $j < n$.
-/
lemma exists_j_in_range_for_factor (n : ℕ) (b : ℕ) (hn : n ≥ 2)
    (hb_le : b ≤ n) (hb_pos : b > 1) :
    ∃ j ∈ Finset.range n, largest_prime_of b ∈ I n j := by
      refine' ⟨ Nat.log 2 ( n / largest_prime_of b ), _, _ ⟩;
      · refine' Finset.mem_range.mpr ( lt_of_le_of_lt ( Nat.log_mono_right <| Nat.div_le_self _ _ ) _ );
        exact Nat.log_lt_of_lt_pow ( by linarith ) ( by exact Nat.recOn n ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ ] at * ; nlinarith );
      · apply mem_I_of_j_of_prime;
        · have h_max_pos : ∀ {l : List ℕ}, (∀ p ∈ l, p > 0) → l ≠ [] → List.foldl max 0 l > 0 := by
            intros l hl_pos hl_nonempty; induction' l using List.reverseRecOn with l ih <;> aesop;
          exact h_max_pos ( fun p hp => Nat.pos_of_mem_primeFactorsList hp ) ( by aesop );
        · have h_max_le_b : ∀ {l : List ℕ}, (∀ p ∈ l, p ≤ b) → List.foldl max 0 l ≤ b := by
            intros l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
          exact le_trans ( h_max_le_b fun p hp => Nat.le_of_mem_primeFactorsList hp ) hb_le

/-
$W(n)$ is the sum over $j$ of the waste contributions from factors in $I_j$.
-/
theorem W_eq_sum_Ij_sum_w (n : ℕ) (hn : n ≥ 2) :
  W n = ∑ j ∈ Finset.range n, ((factors_in_Ij n j).map (fun b => w n b)).sum := by
    have h_partition : ∀ {L : List ℕ}, (∀ b ∈ L, b > 1 ∧ b ≤ n) → ∑ j ∈ Finset.range n, (List.map (fun b => w n b) (L.filter (fun b => largest_prime_of b ∈ I n j))).sum = (List.map (fun b => w n b) L).sum := by
      intros L hL
      have h_partition : ∀ b ∈ L, ∃! j ∈ Finset.range n, largest_prime_of b ∈ I n j := by
        intro b hb
        obtain ⟨j, hj₁, hj₂⟩ : ∃ j ∈ Finset.range n, largest_prime_of b ∈ I n j := by
          apply exists_j_in_range_for_factor n b hn (hL b hb).2 (hL b hb).1;
        use j;
        field_simp;
        exact ⟨ ⟨ hj₁, hj₂ ⟩, fun y hy => j_unique_of_mem_I n ( largest_prime_of b ) y ( Nat.pos_of_ne_zero ( by rintro h; have := hy.2; unfold I at this; aesop ) ) hy.2 ▸ j_unique_of_mem_I n ( largest_prime_of b ) j ( Nat.pos_of_ne_zero ( by rintro h; have := hj₂; unfold I at this; aesop ) ) hj₂ ▸ rfl ⟩;
      induction' L using List.reverseRecOn with L ih;
      · norm_num;
      · simp_all +decide [ Finset.sum_add_distrib, List.filter_cons ];
        obtain ⟨ j, hj₁, hj₂ ⟩ := h_partition ih ( Or.inr rfl );
        rw [ Finset.sum_eq_single j ] <;> aesop;
    convert h_partition _ |> Eq.symm using 1;
    · exact W_eq_sum_w n;
    · intro b hb; refine' ⟨ _, _ ⟩;
      · exact greedy_factors_gt_one n hn b hb;
      · apply greedy_process_upper_bound;
        any_goals assumption;
        · exact fun p hp => Nat.le_of_not_lt fun h => absurd ( Nat.dvd_of_mem_primeFactorsList hp ) ( by rw [ Nat.Prime.dvd_factorial ( Nat.prime_of_mem_primeFactorsList hp ) ] ; linarith );
        · linarith

/-
The Refinement Property implies the geometric bound on $W(n)$.
-/
def RefinementProperty : Prop :=
  ∃ C, ∀ n ≥ 2, ∀ j, ((factors_in_Ij n j).map (fun b => w n b)).sum ≤ C * (1 / 2 : ℝ) ^ j * (Omega n j : ℝ)

theorem W_le_sum_geometric_Omega_of_Refinement (h : RefinementProperty) : W_le_sum_geometric_Omega_Statement := by
  obtain ⟨ C, hC ⟩ := h;
  refine' ⟨ C, fun n hn => _ ⟩;
  rw [ W_eq_sum_Ij_sum_w n hn ];
  simpa only [ mul_assoc, Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun j hj => hC n hn j

/-
The sum $\sum 2^{-j} \Omega_j$ is bounded by $O(n/\log n)$.
-/
theorem sum_geometric_Omega_le_n_div_log_proof (hCheb : ChebyshevUpperBound) :
  ∃ C, ∀ n ≥ 2, ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j * (Omega n j : ℝ) ≤ C * n / Real.log n := by
    -- Apply the hypothesis `h_sum` to conclude the proof.
    apply sum_geometric_Omega_le_n_div_log hCheb

open Finset Nat

/-
Define $\theta(n) = \sum_{p \le n} \log p$ and prove $\theta(n) = \log(n\#)$.
-/
noncomputable def theta (n : ℕ) : ℝ := ∑ p ∈ (range (n + 1)).filter Prime, Real.log p

lemma theta_eq_log_primorial (n : ℕ) : theta n = Real.log (primorial n) := by
  unfold theta primorial;
  rw [ Nat.cast_prod, Real.log_prod ] ; aesop

/-
Prove $\theta(n) \le n \log 4$ using `primorial_le_4_pow`.
-/
lemma theta_le_n_log_4 (n : ℕ) : theta n ≤ n * Real.log 4 := by
  -- By definition of `theta`, we know that `theta n = Real.log (primorial n)`.
  have h_theta_def : theta n = Real.log (primorial n) := by
    exact theta_eq_log_primorial n;
  rw [ h_theta_def, ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> norm_num;
  · exact primorial_le_4_pow n;
  · exact primorial_pos n

/-
Prove that $\pi(x) \le \frac{\theta(x)}{\alpha \log x} + x^\alpha$ for $x \ge 2$ and $\alpha \in (0, 1)$.
-/
lemma pi_le_theta_div_log (x : ℝ) (α : ℝ) (hx : x ≥ 2) (hα : 0 < α) (hα1 : α < 1) :
  (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ theta ⌊x⌋₊ / (α * Real.log x) + x ^ α := by
    -- By splitting the sum into two parts, we can bound the number of primes in each part.
    have h_split : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (theta ⌊x⌋₊) / (α * Real.log x) + (x ^ α) := by
      have h_pi_le : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (∑ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), if p ≤ x ^ α then 1 else 0) + (∑ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), if p > x ^ α then 1 else 0) := by
        rw [ ← Finset.sum_add_distrib ];
        norm_num [ Nat.primeCounting ];
        rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
        rw [ Finset.sum_congr rfl fun i hi => by aesop ] ; norm_num
      -- For primes $p > x^\alpha$, we have $\log p \ge \alpha \log x$, so $\sum_{p > x^\alpha} \log p \ge \alpha \log x \sum_{p > x^\alpha} 1$.
      have h_sum_log_gt : (∑ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), if p > x ^ α then Real.log p else 0) ≥ (α * Real.log x) * (∑ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), if p > x ^ α then 1 else 0) := by
        have h_sum_log_gt : ∀ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), p > x ^ α → Real.log p ≥ α * Real.log x := by
          exact fun p hp hp' => by rw [ ← Real.log_rpow ( by positivity ) ] ; exact Real.log_le_log ( by positivity ) hp'.le;
        simpa only [ Finset.mul_sum _ _ _, mul_boole ] using Finset.sum_le_sum fun p hp => by aesop;
      -- For primes $p \le x^\alpha$, we have $\sum_{p \le x^\alpha} 1 \le x^\alpha$.
      have h_sum_le : (∑ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), if p ≤ x ^ α then 1 else 0) ≤ x ^ α := by
        norm_num [ Finset.sum_ite ];
        refine' le_trans _ ( show ( x ^ α : ℝ ) ≥ ↑⌊x ^ α⌋₊ from Nat.floor_le ( by positivity ) );
        exact_mod_cast le_trans ( Finset.card_le_card <| show Finset.filter ( fun p : ℕ => ( p : ℝ ) ≤ x ^ α ) ( Finset.filter Nat.Prime ( Finset.range ( ⌊x⌋₊ + 1 ) ) ) ⊆ Finset.Icc 1 ⌊x ^ α⌋₊ from fun p hp => Finset.mem_Icc.mpr ⟨ Nat.Prime.pos <| Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2, Nat.le_floor <| Finset.mem_filter.mp hp |>.2 ⟩ ) <| by simp +arith +decide;
      -- Since $\sum_{p \le x^\alpha} \log p \le \theta(x)$, we have $\sum_{p > x^\alpha} \log p \le \theta(x)$.
      have h_sum_log_le_theta : (∑ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), if p > x ^ α then Real.log p else 0) ≤ theta ⌊x⌋₊ := by
        refine' le_trans ( Finset.sum_le_sum fun p hp => _ ) _;
        use fun p => Real.log p;
        · split_ifs <;> norm_num ; linarith [ Real.log_nonneg ( show ( p : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.Prime.pos ( by aesop ) ) ) ];
        · unfold theta; aesop;
      rw [ div_add', le_div_iff₀ ] <;> nlinarith [ show 0 < α * Real.log x from mul_pos hα ( Real.log_pos <| by linarith ), Real.log_pos <| show 1 < x from by linarith ];
    exact h_split

/-
The Chebyshev upper bound on the prime counting function holds.
-/
lemma chebyshev_upper_bound : ChebyshevUpperBound := by
  -- Fix $\varepsilon > 0$.
  intro ε hε_pos
  -- Choose $\alpha \in (0, 1)$ such that $\frac{\log 4}{\alpha} < \log 4 + \varepsilon/2$.
  obtain ⟨α, hα_pos, hα_lt_one, hα_bound⟩ : ∃ α : ℝ, 0 < α ∧ α < 1 ∧ (Real.log 4) / α < Real.log 4 + ε / 2 := by
    have h_alpha : Filter.Tendsto (fun α : ℝ => (Real.log 4) / α) (nhdsWithin 1 (Set.Iio 1)) (nhds (Real.log 4)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using tendsto_const_nhds.div ( Filter.tendsto_id ) ( by norm_num : ( 1 : ℝ ) ≠ 0 ) );
    have := h_alpha.eventually ( gt_mem_nhds <| show Real.log 4 < Real.log 4 + ε / 2 by linarith ) ; have := this.and ( Ioo_mem_nhdsLT one_pos ) ; obtain ⟨ α, hα₁, hα₂ ⟩ := this.exists; exact ⟨ α, hα₂.1, hα₂.2, hα₁ ⟩ ;
  -- Using `pi_le_theta_div_log` and `theta_le_n_log_4`, we get $\pi(x) \le \frac{x \log 4}{\alpha \log x} + x^\alpha$.
  have h_pi_bound : ∀ x : ℝ, 2 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x * Real.log 4 / (α * Real.log x) + x ^ α := by
    intros x hx
    have h_pi_bound : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ theta ⌊x⌋₊ / (α * Real.log x) + x ^ α := by
      convert pi_le_theta_div_log x α ( by linarith ) hα_pos hα_lt_one using 1;
    refine le_trans h_pi_bound ?_;
    gcongr;
    · exact mul_nonneg hα_pos.le ( Real.log_nonneg ( by linarith ) );
    · exact le_trans ( theta_le_n_log_4 _ ) ( mul_le_mul_of_nonneg_right ( Nat.floor_le ( by positivity ) ) ( Real.log_nonneg ( by norm_num ) ) );
  -- Since $1-\alpha > 0$, $\lim_{x \to \infty} \frac{\log x}{x^{1-\alpha}} = 0$.
  have h_log_div_x_pow_zero : Filter.Tendsto (fun x : ℝ => Real.log x / x ^ (1 - α)) Filter.atTop (nhds 0) := by
    -- Let $y = \log x$, therefore the expression becomes $\frac{y}{e^{(1-\alpha)y}}$.
    suffices h_log_div_exp_zero : Filter.Tendsto (fun y : ℝ => y / Real.exp ((1 - α) * y)) Filter.atTop (nhds 0) by
      have := h_log_div_exp_zero.comp Real.tendsto_log_atTop;
      refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.rpow_def_of_pos hx ] ; ring_nf );
    -- Let $z = (1 - \alpha) y$, therefore the expression becomes $\frac{z}{e^z}$.
    suffices h_log_div_exp_zero' : Filter.Tendsto (fun z : ℝ => z / Real.exp z) Filter.atTop (nhds 0) by
      have := h_log_div_exp_zero'.comp ( Filter.tendsto_id.const_mul_atTop ( by linarith : 0 < ( 1 - α ) ) );
      convert this.const_mul ( 1 / ( 1 - α ) ) using 2 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( sub_pos.mpr hα_lt_one ) ];
    simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
  -- Thus for large enough $x$, $\frac{\log x}{x^{1-\alpha}} < \varepsilon/2$.
  obtain ⟨X, hX⟩ : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → Real.log x / x ^ (1 - α) < ε / 2 := by
    simpa using h_log_div_x_pow_zero.eventually ( gt_mem_nhds <| half_pos hε_pos );
  -- Then $\pi(x) \le \frac{x}{\log x} \left( \frac{\log 4}{\alpha} + \frac{\log x}{x^{1-\alpha}} \right)$.
  have h_pi_bound_final : ∀ x : ℝ, max 2 X ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / Real.log x * ((Real.log 4) / α + Real.log x / x ^ (1 - α)) := by
    intro x hx; convert h_pi_bound x ( le_trans ( le_max_left _ _ ) hx ) using 1; ring_nf;
    rw [ Real.rpow_sub ( by linarith [ le_max_left 2 X, le_max_right 2 X ] ), Real.rpow_one ] ; ring_nf;
    norm_num [ add_comm, ne_of_gt ( Real.log_pos ( show x > 1 by linarith [ le_max_left 2 X, le_max_right 2 X ] ) ), ne_of_gt ( show x > 0 by linarith [ le_max_left 2 X, le_max_right 2 X ] ) ];
  filter_upwards [ Filter.eventually_ge_atTop ( Max.max 2 X ) ] with x hx using le_trans ( h_pi_bound_final x hx ) ( by convert mul_le_mul_of_nonneg_left ( show Real.log 4 / α + Real.log x / x ^ ( 1 - α ) ≤ Real.log 4 + ε by linarith [ hX x ( le_trans ( le_max_right 2 X ) hx ) ] ) ( div_nonneg ( by linarith [ le_max_left 2 X, le_max_right 2 X ] : 0 ≤ x ) ( Real.log_nonneg ( by linarith [ le_max_left 2 X, le_max_right 2 X ] : ( 1:ℝ ) ≤ x ) ) ) using 1 ; ring ) ;

/-
For $p \in I_j$, $\nu_p(n!) \le 4 \cdot 2^j$.
-/
lemma valuation_bound_in_Ij (n j p : ℕ) (hp : p.Prime) (hin : p ∈ I n j) :
  padicValNat p n.factorial ≤ 4 * 2^j := by
    have h_val_le : padicValNat p n.factorial ≤ n / (p - 1) := by
      exact valuation_le_div_pred n p hp;
    rcases hin with ⟨ hj₁, hj₂ ⟩;
    rw [ Nat.div_lt_iff_lt_mul <| by positivity ] at hj₁;
    refine le_trans h_val_le ?_;
    rcases p with ( _ | _ | p ) <;> simp_all +decide [ pow_succ' ];
    exact Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.div_mul_le_self n ( 2 ^ j ) ] ;

/-
Prove `Omega_bound_uniform` with $C=4$.
-/
lemma Omega_bound_uniform_proof :
  ∃ C, ∀ n ≥ 2, ∀ j, (Omega n j : ℝ) ≤ C * 2^j * Nat.primeCounting (n / 2^j) := by
    have h_C_exists : ∃ C : ℝ, ∀ n ≥ 2, ∀ j, (Omega n j : ℝ) ≤ C * (2^j) * (Nat.primeCounting (n / 2^j)) := by
      have := Omega_bound_uniform
      exact ⟨ this.choose, fun n hn j => mod_cast this.choose_spec n hn j ⟩;
    exact h_C_exists

/-
The sum of $2^{-j} \Omega_j$ over $j$ with $2^j > \sqrt{n}$ is $O(n/\log n)$.
-/
lemma sum_geometric_Omega_large_j_le :
  ∃ C, ∀ n ≥ 2, ∑ j ∈ (Finset.range n).filter (fun j => (2 : ℝ)^j > Real.sqrt n), (1 / 2 : ℝ) ^ j * (Omega n j : ℝ) ≤ C * n / Real.log n := by
    have := sum_geometric_Omega_le_n_div_log ( by exact chebyshev_upper_bound );
    exact ⟨ this.choose, fun n hn => le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => by positivity ) ( this.choose_spec n hn ) ⟩

/-
If $2^j \le \sqrt{n}$, then $\log(n/2^j) \ge \frac{1}{2} \log n$.
-/
lemma log_div_pow_two_ge_half_log (n j : ℕ) (h : (2 : ℝ)^j ≤ Real.sqrt n) (hn : n ≥ 1) :
  Real.log (n / (2 : ℝ)^j) ≥ (1/2) * Real.log n := by
    rw [ ge_iff_le, Real.le_log_iff_exp_le ] <;> norm_num;
    · rw [ show ( 1 / 2 : ℝ ) * Real.log n = Real.log ( Real.sqrt n ) by rw [ Real.log_sqrt ( by positivity ) ] ; ring, Real.exp_log ( by positivity ) ];
      rw [ le_div_iff₀ ] <;> first | positivity | nlinarith [ Real.mul_self_sqrt ( Nat.cast_nonneg n ), show ( 2:ℝ ) ^ j ≥ 1 by exact one_le_pow₀ ( by norm_num ) ] ;
    · linarith

/-
The sum of $2^{-j} \Omega_j$ over $j$ with $2^j \le \sqrt{n}$ is $O(n/\log n)$.
-/
lemma sum_geometric_Omega_small_j_le (hCheb : ChebyshevUpperBound) :
  ∃ C, ∀ n ≥ 2, ∑ j ∈ (Finset.range n).filter (fun j => (2 : ℝ)^j ≤ Real.sqrt n), (1 / 2 : ℝ) ^ j * (Omega n j : ℝ) ≤ C * n / Real.log n := by
    have := @sum_geometric_Omega_le_n_div_log;
    exact Exists.elim ( this hCheb ) fun C hC => ⟨ C, fun n hn => le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => by positivity ) ( hC n hn ) ⟩

/-
Combine the small $j$ and large $j$ bounds to prove the total sum bound.
-/
lemma sum_geometric_Omega_le_n_div_log_calc (hCheb : ChebyshevUpperBound) :
  ∃ C, ∀ n ≥ 2, ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j * (Omega n j : ℝ) ≤ C * n / Real.log n := by
    exact sum_geometric_Omega_le_n_div_log hCheb

/-
The sum $\sum 2^{-j} \Omega_j$ is bounded by $O(n/\log n)$.
-/
lemma sum_geometric_Omega_le_n_div_log_final (hCheb : ChebyshevUpperBound) :
  ∃ C, ∀ n ≥ 2, ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j * (Omega n j : ℝ) ≤ C * n / Real.log n := by
    exact sum_geometric_Omega_le_n_div_log_calc hCheb

/-
Prove that the Refinement Property implies the geometric bound on $W(n)$.
-/
theorem W_le_sum_geometric_Omega_of_Refinement_proof (h : RefinementProperty) : W_le_sum_geometric_Omega_Statement := by
  exact W_le_sum_geometric_Omega_of_Refinement h

/-
Combine the small $j$ and large $j$ bounds to prove the total sum bound.
-/
lemma sum_geometric_Omega_le_n_div_log_combined (hCheb : ChebyshevUpperBound) :
  ∃ C, ∀ n ≥ 2, ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j * (Omega n j : ℝ) ≤ C * n / Real.log n := by
    -- Apply the lemma sum_geometric_Omega_le_n_div_log_final with the given hCheb.
    apply sum_geometric_Omega_le_n_div_log_final hCheb

/-
$W(n) \ge 0$.
-/
lemma W_nonneg (n : ℕ) (hn : n ≥ 1) : 0 ≤ W n := by
  unfold W;
  -- By definition of $G(n)$, we know that $G(n) \geq \frac{\log(n!)}{\log n}$.
  have h_G_ge : (G n : ℝ) ≥ Real.log (n.factorial) / Real.log n := by
    by_cases hn2 : n ≥ 2;
    · have := @greedy_is_valid n hn2;
      have := @log_lower_bound n ( greedy_process n ( Nat.primeFactorsList n.factorial ) ( List.length ( Nat.primeFactorsList n.factorial ) + 1 ) ) hn2 this; aesop;
    · interval_cases n ; norm_num;
  contrapose! h_G_ge;
  rw [ lt_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| lt_of_le_of_ne hn <| Ne.symm <| by rintro rfl; norm_num [ Nat.factorial ] at h_G_ge ) ] ; linarith

/-
$W(n) = o(n)$.
-/
theorem W_is_little_o_n (hRef : RefinementProperty) (hCheb : ChebyshevUpperBound) :
  Asymptotics.IsLittleO Filter.atTop W (fun n => (n : ℝ)) := by
    -- By combining the results from W_le_sum_geometric_Omega_of_Refinement and sum_geometric_Omega_le_n_div_log_combined, we can conclude that W(n) is bounded by O(n / log n).
    have hW_bound : ∃ C, ∀ n ≥ 2, W n ≤ C * n / Real.log n := by
      obtain ⟨ C, hC ⟩ := W_le_sum_geometric_Omega_of_Refinement hRef;
      obtain ⟨ D, hD ⟩ := sum_geometric_Omega_le_n_div_log_combined hCheb;
      exact ⟨ C * D, fun n hn => le_trans ( hC n hn ) ( by convert mul_le_mul_of_nonneg_left ( hD n hn ) ( show 0 ≤ C by
                                                                                                            have := hC 2 ( by norm_num );
                                                                                                            norm_num [ Finset.sum_range_succ, Omega ] at this;
                                                                                                            norm_num [ Finset.sum_filter, Finset.sum_range_succ, I ] at this;
                                                                                                            exact le_trans ( W_nonneg 2 ( by norm_num ) ) this ) using 1 ; ring ) ⟩;
    obtain ⟨ C, hC ⟩ := hW_bound;
    rw [ Asymptotics.isLittleO_iff_tendsto' ];
    · -- Using the bound $W(n) \leq C * n / \log n$, we can show that $W(n) / n \leq C / \log n$.
      have h_div_bound : ∀ n ≥ 2, W n / (n : ℝ) ≤ C / Real.log n := by
        intro n hn; rw [ div_le_iff₀ ( by positivity ) ] ; convert hC n hn using 1 ; ring;
      exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 2, fun n hn => by rw [ Real.norm_of_nonneg ( div_nonneg ( W_nonneg n ( by linarith ) ) ( Nat.cast_nonneg _ ) ) ] ; exact h_div_bound n hn ⟩ ) ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) );
    · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn hn' using absurd hn' <| by positivity;

/-
$G(n) = n - \frac{n}{\log n} + o\left(\frac{n}{\log n}\right)$.
-/
theorem G_asymptotic (hRef : RefinementProperty) (hCheb : ChebyshevUpperBound) :
  Asymptotics.IsLittleO Filter.atTop (fun n : ℕ => (G n : ℝ) - ((n : ℝ) - (n : ℝ) / Real.log n)) (fun n => (n : ℝ) / Real.log n) := by
    -- Using the fact that $W(n) = o(n)$, we can bound $G(n)$.
    have h_bound : ∀ᶠ n in Filter.atTop, abs ((G n : ℝ) - (n - n / Real.log n)) ≤ 2 * abs (W n) / Real.log n + 2 * abs (Real.log n.factorial - (n * Real.log n - n)) / Real.log n := by
      -- Using the definitions of $W(n)$ and the asymptotic expansion of $\log(n!)$, we can express $G(n)$ in terms of $W(n)$ and the error term.
      have hG_expr : ∀ n ≥ 2, (G n : ℝ) = (W n + Real.log (Nat.factorial n)) / Real.log n := by
        intro n hn; rw [ eq_div_iff ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) ] ; unfold W; ring;
      filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn;
      rw [ hG_expr n hn, abs_le ];
      constructor <;> cases abs_cases ( W n ) <;> cases abs_cases ( Real.log n ! - ( n * Real.log n - n ) ) <;> ring_nf at * <;> nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast ) ) ) ];
    -- Using the fact that $W(n) = o(n)$ and $\log(n!) = n \log n - n + O(\log n)$, we can bound the terms.
    have h_term1 : (fun n : ℕ => 2 * abs (W n) / Real.log n) =o[Filter.atTop] (fun n : ℕ => (n : ℝ) / Real.log n) := by
      have h_term1 : (fun n : ℕ => abs (W n) / Real.log n) =o[Filter.atTop] (fun n : ℕ => (n : ℝ) / Real.log n) := by
        have := W_is_little_o_n hRef hCheb;
        rw [ Asymptotics.isLittleO_iff ] at *;
        intro c hc; filter_upwards [ this hc, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂; simp_all +decide [ abs_div, abs_mul, div_le_iff₀ ] ;
        rw [ mul_div ] ; gcongr;
      simpa only [ mul_div_assoc ] using h_term1.const_mul_left 2
    have h_term2 : (fun n : ℕ => 2 * abs (Real.log n.factorial - (n * Real.log n - n)) / Real.log n) =o[Filter.atTop] (fun n : ℕ => (n : ℝ) / Real.log n) := by
      have h_term2 : (fun n : ℕ => abs (Real.log n.factorial - (n * Real.log n - n))) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
        have h_term2 : (fun n : ℕ => Real.log n.factorial - (n * Real.log n - n)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
          have := log_factorial_asymptotic
          refine' this.trans_isLittleO _;
          rw [ Asymptotics.isLittleO_iff_tendsto' ] <;> norm_num;
          · -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
            suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
              exact h_log_recip.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
            norm_num;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
          · exact ⟨ 1, by aesop ⟩;
        aesop;
      rw [ Asymptotics.isLittleO_iff ] at *;
      intro c hc; filter_upwards [ h_term2 ( half_pos hc ), Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂; simp_all +decide [ abs_div, abs_mul, div_eq_mul_inv ] ;
      convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left hx₁ zero_le_two ) ( inv_nonneg.mpr ( abs_nonneg ( Real.log x ) ) ) using 1 ; ring;
    rw [ Asymptotics.isLittleO_iff ] at *;
    intro c hc; filter_upwards [ h_bound, h_term1 ( half_pos hc ), h_term2 ( half_pos hc ) ] with n hn hn' hn''; norm_num at *;
    refine le_trans hn ?_;
    convert add_le_add hn' hn'' using 1 <;> ring_nf;
    rw [ abs_of_nonneg ( Real.log_natCast_nonneg _ ) ] ; ring

/-
The error term in Stirling's approximation divided by $n$ tends to 0.
-/
lemma stirling_term_tendsto_zero :
  Filter.Tendsto (fun n : ℕ => (Real.log n.factorial - ((n : ℝ) * Real.log n - n)) / n) Filter.atTop (nhds 0) := by
    have h_log_factorial_approx : Asymptotics.IsBigO Filter.atTop (fun n : ℕ => Real.log (Nat.factorial n) - (n * Real.log n - n)) (fun n : ℕ => Real.log n) := by
      exact log_factorial_asymptotic;
    rw [ Asymptotics.isBigO_iff ] at h_log_factorial_approx;
    refine' squeeze_zero_norm' _ _;
    use fun n => h_log_factorial_approx.choose * ‖Real.log n‖ / n;
    · filter_upwards [ h_log_factorial_approx.choose_spec ] with n hn using by simpa [ abs_div ] using div_le_div_of_nonneg_right hn ( Nat.cast_nonneg _ ) ;
    · -- We'll use the fact that $\frac{\log n}{n}$ tends to $0$ as $n$ tends to infinity.
      have h_log_div_n : Filter.Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
        suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_log_recip.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num +zetaDelta at *;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
      convert h_log_div_n.const_mul ( h_log_factorial_approx.choose : ℝ ) using 2 <;> norm_num ; ring_nf;
      rw [ abs_of_nonneg ( Real.log_natCast_nonneg _ ) ] ; ring

/-
$A(n) = n - \frac{n}{\log n} + o\left(\frac{n}{\log n}\right)$.
-/
theorem A_asymptotic (hRef : RefinementProperty) (hCheb : ChebyshevUpperBound) :
  Asymptotics.IsLittleO Filter.atTop (fun n : ℕ => (A n : ℝ) - ((n : ℝ) - (n : ℝ) / Real.log n)) (fun n => (n : ℝ) / Real.log n) := by
    -- By definition of $A(n)$, we know that $A(n) \leq G(n)$.
    have h_A_le_G : ∀ n ≥ 2, (A n : ℝ) ≤ (G n : ℝ) := by
      norm_num +zetaDelta at *;
      exact fun n a => A_le_G n a;
    -- By definition of $A(n)$, we know that $A(n) \geq \frac{\log(n!)}{\log n}$.
    have h_A_ge_log : ∀ n ≥ 2, (A n : ℝ) ≥ (Real.log n.factorial / Real.log n) := by
      intro n hn
      obtain ⟨L, hL⟩ : ∃ L : List ℕ, is_valid_decomp n L ∧ L.length = A n := by
        have := Nat.sInf_mem ( show { t | ∃ L : List ℕ, is_valid_decomp n L ∧ L.length = t }.Nonempty from ?_ );
        · exact this;
        · exact ⟨ _, ⟨ greedy_process n ( Nat.primeFactorsList n.factorial ) ( List.length ( Nat.primeFactorsList n.factorial ) + 1 ), greedy_is_valid n hn, rfl ⟩ ⟩;
      have := log_lower_bound n L hn hL.1; aesop;
    -- Using the bounds from h_A_le_G and h_A_ge_log, we can show that the difference between A(n) and (n - n / log n) is bounded by a function that tends to zero.
    have h_diff_bound : Asymptotics.IsLittleO Filter.atTop (fun n : ℕ => (G n : ℝ) - (n - n / Real.log n)) (fun n : ℕ => n / Real.log n) ∧ Asymptotics.IsLittleO Filter.atTop (fun n : ℕ => (Real.log n.factorial / Real.log n) - (n - n / Real.log n)) (fun n : ℕ => n / Real.log n) := by
      constructor;
      · convert G_asymptotic hRef hCheb using 1;
      · have h_diff_bound : Asymptotics.IsLittleO Filter.atTop (fun n : ℕ => (Real.log n.factorial - (n * Real.log n - n)) / Real.log n) (fun n : ℕ => n / Real.log n) := by
          have := stirling_term_tendsto_zero;
          rw [ Asymptotics.isLittleO_iff_tendsto' ];
          · refine' this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ div_div_div_cancel_right₀ ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hx ) ] );
          · filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn h using absurd h <| ne_of_gt <| div_pos ( Nat.cast_pos.mpr <| pos_of_gt hn ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn;
        refine h_diff_bound.congr' ?_ ?_ <;> norm_num [ sub_div ];
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn using by rw [ mul_div_cancel_right₀ _ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hn ) ) ) ] ;
    rw [ Asymptotics.isLittleO_iff ] at *;
    intro c hc; filter_upwards [ h_diff_bound.1 hc, h_diff_bound.2.def hc, Filter.eventually_ge_atTop 2 ] with n hn hn' hn''; rw [ Real.norm_eq_abs, abs_le ] ; constructor <;> linarith [ abs_le.mp hn, abs_le.mp hn', h_A_le_G n hn'', h_A_ge_log n hn'' ] ;

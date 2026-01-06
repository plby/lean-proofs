/-
We formalize the positive answer to Erdos problem #728. We prove the main theorem of the paper 'Factorial Divisibility Beyond the Logarithmic Barrier'. We show that for any fixed $0<\varepsilon<1/2$ and $C>0$, there are infinitely many triples $(a,b,n)$ satisfying the divisibility $a!b! \mid n!(a+b-n)!$ with range constraints and $a+b > n + C \log n$. The proof follows the probabilistic method outlined in the paper, using Kummer's theorem and estimates on carry counts.
-/

import Mathlib


open Real

open scoped Classical Nat Topology

set_option maxHeartbeats 0

/-
Definitions of W and kappa. W_p(m) is the p-adic valuation of the product of m+1 to m+k. kappa_p(m) is the p-adic valuation of binom(2m, m).
-/
def W (p m k : ℕ) : ℕ := padicValNat p (Nat.descFactorial (m + k) k)

def kappa (p m : ℕ) : ℕ := padicValNat p (Nat.choose (2 * m) m)

/-
If p^j divides m+i and i is small enough, then kappa_p(m) >= j.
-/
lemma lemma_forced_carries_largep (p m i j : ℕ) (hp : p.Prime) (hi : 1 ≤ i) (hip : i < p)
    (hij : i ≤ (p - 1) / 2) (hdiv : p ^ j ∣ m + i) :
    kappa p m ≥ j := by
  unfold kappa;
  -- By Kummer's theorem, the p-adic valuation of the binomial coefficient (2m choose m) is equal to the number of carries when m and m are added in base p.
  have h_kummer : padicValNat p (Nat.choose (2 * m) m) = (∑ k ∈ Finset.Ico 1 (Nat.log p (2 * m) + 1), (Nat.floor ((2 * m) / p ^ k) - 2 * Nat.floor (m / p ^ k))) := by
    haveI := Fact.mk hp;
    rw [ padicValNat_choose ];
    any_goals exact Nat.lt_succ_self _;
    · norm_num [ two_mul, Nat.add_div ( pow_pos hp.pos _ ) ];
    · linarith;
  -- Since $p^j \mid m + i$, we have $\left\lfloor \frac{2m}{p^k} \right\rfloor - 2 \left\lfloor \frac{m}{p^k} \right\rfloor \geq 1$ for $k = 1, 2, \ldots, j$.
  have h_floor : ∀ k ∈ Finset.Ico 1 (j + 1), (Nat.floor ((2 * m) / p ^ k) - 2 * Nat.floor (m / p ^ k)) ≥ 1 := by
    -- Since $p^j \mid m + i$, we have $m \equiv -i \pmod{p^k}$ for $k \leq j$.
    have h_cong : ∀ k ∈ Finset.Ico 1 (j + 1), m % p ^ k = p ^ k - i % p ^ k := by
      intro k hk
      have h_cong : m ≡ -i [ZMOD p ^ k] := by
        exact Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using dvd_trans ( pow_dvd_pow _ <| Finset.mem_Ico.mp hk |>.2 |> Nat.lt_succ_iff.mp ) hdiv;
      -- Since $m \equiv -i \pmod{p^k}$, we have $m \mod p^k = (p^k - i \mod p^k) \mod p^k$.
      have h_mod : m % p ^ k = (p ^ k - i % p ^ k) % p ^ k := by
        zify;
        rw [ Int.ofNat_sub ( Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ) ] ; simp_all +decide [ Int.ModEq ];
        exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr ( by ring_nf; norm_num );
      rw [ h_mod, Nat.mod_eq_of_lt ( Nat.sub_lt ( pow_pos hp.pos _ ) ( Nat.pos_of_ne_zero ( by rw [ Nat.mod_eq_of_lt ] <;> linarith [ Nat.pow_le_pow_right hp.one_lt.le ( show k ≥ 1 by linarith [ Finset.mem_Ico.mp hk ] ) ] ) ) ) ];
    -- Since $m \equiv -i \pmod{p^k}$, we have $\left\lfloor \frac{2m}{p^k} \right\rfloor = \left\lfloor \frac{2(-i)}{p^k} \right\rfloor + 2 \left\lfloor \frac{m}{p^k} \right\rfloor$.
    intros k hk
    have h_floor_eq : Nat.floor ((2 * m) / p ^ k) = 2 * Nat.floor (m / p ^ k) + Nat.floor ((2 * (m % p ^ k)) / p ^ k) := by
      rw [ show 2 * m = 2 * ( m / p ^ k ) * p ^ k + 2 * ( m % p ^ k ) by linarith [ Nat.mod_add_div m ( p ^ k ) ] ] ; norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.mul_mod, Nat.mod_eq_of_lt ( show 1 < p ^ k from one_lt_pow₀ hp.one_lt ( by linarith [ Finset.mem_Ico.mp hk ] ) ) ] ; ring_nf;
      norm_num [ Nat.add_mul_div_left, Nat.mul_assoc, Nat.mul_div_assoc, Nat.mod_lt, hp.pos ];
      rw [ Nat.add_div ] <;> norm_num [ Nat.mul_div_assoc, Nat.mod_lt, hp.pos ];
    -- Since $m \equiv -i \pmod{p^k}$, we have $\left\lfloor \frac{2(-i)}{p^k} \right\rfloor \geq 1$.
    have h_floor_neg_i : Nat.floor ((2 * (p ^ k - i % p ^ k)) / p ^ k) ≥ 1 := by
      refine Nat.div_pos ?_ ( pow_pos hp.pos _ );
      rw [ Nat.mod_eq_of_lt ];
      · rw [ Nat.mul_sub_left_distrib ];
        exact le_tsub_of_add_le_left ( by nlinarith [ Nat.pow_le_pow_right hp.one_lt.le ( show k ≥ 1 by linarith [ Finset.mem_Ico.mp hk ] ), Nat.div_mul_le_self ( p - 1 ) 2, Nat.sub_add_cancel hp.pos ] );
      · exact lt_of_lt_of_le hip ( Nat.le_self_pow ( by linarith [ Finset.mem_Ico.mp hk ] ) _ );
    grind;
  -- Therefore, the sum $\sum_{k=1}^{j} \left( \left\lfloor \frac{2m}{p^k} \right\rfloor - 2 \left\lfloor \frac{m}{p^k} \right\rfloor \right)$ is at least $j$.
  have h_sum_ge_j : ∑ k ∈ Finset.Ico 1 (Nat.log p (2 * m) + 1), (Nat.floor ((2 * m) / p ^ k) - 2 * Nat.floor (m / p ^ k)) ≥ ∑ k ∈ Finset.Ico 1 (j + 1), (Nat.floor ((2 * m) / p ^ k) - 2 * Nat.floor (m / p ^ k)) := by
    by_cases hj : j ≤ Nat.log p (2 * m);
    · exact Finset.sum_le_sum_of_subset ( Finset.Ico_subset_Ico_right ( by linarith ) );
    · contrapose! h_floor;
      use Nat.log p (2 * m) + 1;
      norm_num [ Nat.div_eq_of_lt ( show 2 * m < p ^ ( Nat.log p ( 2 * m ) + 1 ) from Nat.lt_pow_succ_log_self hp.one_lt _ ) ];
      linarith;
  exact h_kummer ▸ h_sum_ge_j.trans' ( by simpa using Finset.sum_le_sum h_floor )

/-
For primes p > 2k, kappa_p(m) >= W_p(m).
-/
lemma lemma_p_gt_2k (m k p : ℕ) (hp : p.Prime) (hk : 2 * k < p) :
    kappa p m ≥ W p m k := by
  by_cases h_cases : ∃ i ∈ Finset.Icc 1 k, p ∣ (m + i);
  · -- Let $i_0$ be such that $p \mid (m + i_0)$ and $1 \leq i_0 \leq k$.
    obtain ⟨i₀, hi₀_range, hi₀_div⟩ : ∃ i₀ ∈ Finset.Icc 1 k, p ∣ (m + i₀) := h_cases
    have hi₀_unique : ∀ i ∈ Finset.Icc 1 k, i ≠ i₀ → ¬(p ∣ (m + i)) := by
      intros i hi_range hi_ne_i₀ hi_div
      have h_diff : p ∣ Int.natAbs (i - i₀) := by
        simpa [ ← Int.natCast_dvd_natCast ] using dvd_sub ( Int.natCast_dvd_natCast.mpr hi_div ) ( Int.natCast_dvd_natCast.mpr hi₀_div );
      cases abs_cases ( i - i₀ : ℤ ) <;> linarith [ Finset.mem_Icc.mp hi_range, Finset.mem_Icc.mp hi₀_range, Nat.le_of_dvd ( by omega ) h_diff ];
    -- Since $p \mid (m + i_0)$, we have $W_p(m) = v_p(m + i_0)$.
    have hW_eq_vp : W p m k = padicValNat p (m + i₀) := by
      unfold W;
      -- The product $\prod_{i=1}^k (m+i)$ can be factored as $(m+i₀) \prod_{i \neq i₀} (m+i)$.
      have h_prod_factor : Nat.descFactorial (m + k) k = (m + i₀) * (∏ i ∈ Finset.Icc 1 k \ {i₀}, (m + i)) := by
        have h_prod_factor : Nat.descFactorial (m + k) k = ∏ i ∈ Finset.Icc 1 k, (m + i) := by
          erw [ Finset.prod_Ico_eq_prod_range, Nat.descFactorial_eq_prod_range ];
          rw [ ← Finset.prod_range_reflect ];
          exact Finset.prod_congr rfl fun x hx => by cases k <;> norm_num at * ; omega;
        rw [ h_prod_factor, Finset.prod_eq_mul_prod_diff_singleton hi₀_range ];
      haveI := Fact.mk hp; rw [ h_prod_factor, padicValNat.mul ] <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
      · exact Or.inr <| Or.inr <| Nat.Coprime.prod_right fun i hi => hi₀_unique i ( Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hi |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hi |>.1 ) |>.2 ) <| by aesop;
      · aesop;
      · exact Finset.prod_ne_zero_iff.mpr fun x hx => by linarith [ Finset.mem_Icc.mp ( Finset.mem_sdiff.mp hx |>.1 ) ] ;
    -- Since $p \mid (m + i_0)$, we have $kappa_p(m) \geq v_p(m + i_0)$ by the lemma_forced_carries_largep.
    have hkappa_ge_vp : kappa p m ≥ padicValNat p (m + i₀) := by
      apply lemma_forced_carries_largep p m i₀ (padicValNat p (m + i₀)) hp (Finset.mem_Icc.mp hi₀_range).left (by
      linarith [ Finset.mem_Icc.mp hi₀_range ]) (by
      rw [ Nat.le_div_iff_mul_le ] <;> linarith [ Finset.mem_Icc.mp hi₀_range, Nat.sub_add_cancel hp.pos ]) (by
      exact pow_padicValNat_dvd);
    linarith;
  · unfold W kappa;
    simp_all +decide [ Nat.descFactorial_eq_prod_range ];
    rw [ padicValNat.eq_zero_of_not_dvd ];
    · exact Nat.zero_le _;
    · simp_all +decide [ Nat.Prime.dvd_iff_not_coprime hp, Nat.coprime_prod_right_iff ];
      exact fun x hx => h_cases ( k - x ) ( Nat.sub_pos_of_lt hx ) ( Nat.sub_le _ _ ) |> fun h => by simpa [ Nat.add_sub_assoc hx.le ] using h;

/-
Definitions of N_pj, J_p, and V_p. N_pj counts multiples of p^j in (m, m+k]. J_p is floor(log_p k). V_p is the max valuation in the interval.
-/
def N_pj (p m k j : ℕ) : ℕ := ((Finset.Icc 1 k).filter (fun i => p ^ j ∣ m + i)).card

def J_p (p k : ℕ) : ℕ := Nat.log p k

def V_p (p m k : ℕ) : ℕ := Finset.sup (Finset.Icc 1 k) (fun i => padicValNat p (m + i))

/-
The number of multiples of p^j in (m, m+k] is at most ceil(k/p^j).
-/
lemma lemma_N_pj_le_ceil (p m k j : ℕ) (hp : p.Prime) :
    N_pj p m k j ≤ Nat.ceil ((k : ℝ) / (p ^ j : ℝ)) := by
  -- Each multiple of $p^j$ in the interval $(m, m+k]$ corresponds to a unique integer $i$ in the range $1$ to $k$ such that $p^j \mid (m+i)$.
  have h_multiples : Finset.filter (fun i => p ^ j ∣ m + i) (Finset.Icc 1 k) ⊆ Finset.image (fun x => p ^ j * x - m) (Finset.Icc (m / p ^ j + 1) ((m + k) / p ^ j)) := by
    intro i hi;
    simp +zetaDelta at *;
    refine' ⟨ ( m + i ) / p ^ j, ⟨ _, _ ⟩, _ ⟩;
    · nlinarith [ Nat.div_mul_cancel hi.2, Nat.div_mul_le_self m ( p ^ j ), Nat.div_mul_le_self ( m + i ) ( p ^ j ), Nat.div_add_mod m ( p ^ j ), Nat.mod_lt m ( pow_pos hp.pos j ), Nat.div_add_mod ( m + i ) ( p ^ j ), Nat.mod_lt ( m + i ) ( pow_pos hp.pos j ) ];
    · exact Nat.div_le_div_right ( by linarith );
    · rw [ Nat.mul_div_cancel' hi.2, Nat.add_sub_cancel_left ];
  refine le_trans ( Finset.card_le_card h_multiples ) ?_;
  refine' le_trans ( Finset.card_image_le ) _;
  rcases eq_or_ne ( p ^ j ) 0 <;> simp_all +decide
  refine' Nat.le_of_lt_succ _;
  rw [ Nat.div_lt_iff_lt_mul <| pow_pos hp.pos _ ];
  have := Nat.le_ceil ( ( k : ℝ ) / p ^ j ) ; rw [ div_le_iff₀ ( pow_pos ( Nat.cast_pos.mpr hp.pos ) _ ) ] at this; norm_cast at *; nlinarith [ Nat.div_add_mod m ( p ^ j ), Nat.mod_lt m ( pow_pos hp.pos j ), pow_pos hp.pos j ] ;

/-
W_p(m) is the sum of N_pj over j from 1 to V_p.
-/
lemma lemma_W_eq_sum_N_pj (p m k : ℕ) (hp : p.Prime) :
    W p m k = ∑ j ∈ Finset.Icc 1 (V_p p m k), N_pj p m k j := by
  -- By definition of $W$, we know that
  have h_W_def : W p m k = ∑ i ∈ Finset.Icc 1 k, padicValNat p (m + i) := by
    unfold W; (
    rw [ Nat.descFactorial_eq_prod_range ];
    have h_prod : padicValNat p (∏ i ∈ Finset.range k, (m + k - i)) = ∑ i ∈ Finset.range k, padicValNat p (m + k - i) := by
      induction' k with k ih;
      · aesop;
      · rw [ Finset.prod_range_succ', Finset.sum_range_succ' ];
        haveI := Fact.mk hp; rw [ padicValNat.mul ] <;> simp_all +decide [ ← add_assoc ] ;
        exact Finset.prod_ne_zero_iff.mpr fun x hx => Nat.sub_ne_zero_of_lt <| by linarith [ Finset.mem_range.mp hx ] ;
    erw [ Finset.sum_Ico_eq_sum_range ];
    rw [ h_prod, ← Finset.sum_range_reflect ];
    exact Finset.sum_congr rfl fun x hx => congr_arg _ ( Nat.sub_eq_of_eq_add <| by norm_num at *; omega ));
  -- By definition of $V_p$, we can rewrite the inner sum as $\sum_{j=1}^{V_p} \mathbf{1}_{p^j \mid m+i}$.
  have h_inner : ∀ i ∈ Finset.Icc 1 k, padicValNat p (m + i) = ∑ j ∈ Finset.Icc 1 (V_p p m k), (if p ^ j ∣ m + i then 1 else 0) := by
    intro i hi
    have h_inner_sum : padicValNat p (m + i) = ∑ j ∈ Finset.Icc 1 (padicValNat p (m + i)), 1 := by
      norm_num;
    rw [ h_inner_sum, ← Finset.sum_filter ];
    refine' Finset.sum_subset _ _ <;> simp +contextual [ Finset.subset_iff ];
    · intro x hx₁ hx₂; refine' ⟨ _, _ ⟩;
      · exact le_trans hx₂ ( Finset.le_sup ( f := fun i => padicValNat p ( m + i ) ) hi );
      · rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
        · intro q; by_cases hq : p = q <;> simp +decide [ hq, hp.factorization ] ;
          simp +decide [ ← hq, hp.factorization ];
          convert hx₂ using 1;
          rw [ Nat.factorization_def ] ; aesop;
        · exact fun h => absurd h hp.ne_zero;
        · exact fun _ => by linarith [ Finset.mem_Icc.mp hi ] ;
    · intro x hx₁ hx₂ hx₃; have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 hx₃; simp +decide [ hp ] at this;
      rw [ Nat.factorization_def ] at this ; aesop;
      assumption;
  rw [ h_W_def, Finset.sum_congr rfl h_inner, Finset.sum_comm ] ; aesop;

/-
The number of integers in [M, 2M] with m = r mod Q is at most M/Q + 2.
-/
lemma lemma_residue_interval (M Q r : ℕ) (hQ : Q > 0) :
    ((Finset.Icc M (2 * M)).filter (fun m => m % Q = r)).card ≤ M / Q + 2 := by
  -- The number of integers in [M, 2M] congruent to r mod Q is at most the number of multiples of Q in [M, 2M] plus 1.
  have h_count : (Finset.filter (fun m => m % Q = r) (Finset.Icc M (2 * M))).card ≤ (Finset.image (fun m => m * Q + r) (Finset.Icc (M / Q) (2 * M / Q))).card := by
    refine Finset.card_le_card ?_;
    intro m hm; simp_all
    exact ⟨ m / Q, ⟨ Nat.div_le_div_right hm.1.1, Nat.div_le_div_right hm.1.2 ⟩, by linarith [ Nat.mod_add_div m Q ] ⟩;
  refine le_trans h_count <| Finset.card_image_le.trans ?_;
  norm_num;
  nlinarith [ Nat.div_mul_le_self ( 2 * M ) Q, Nat.div_add_mod ( 2 * M ) Q, Nat.mod_lt ( 2 * M ) hQ, Nat.div_mul_le_self M Q, Nat.div_add_mod M Q, Nat.mod_lt M hQ ]

/-
The number of m in [M, 2M] with V_p(m) >= J_p + t is at most k * (M/p^(J_p+t) + 2).
-/
lemma lemma_spike_count_bound (p M k t : ℕ) (hp : p.Prime) (hk : k > 0) :
    ((Finset.Icc M (2 * M)).filter (fun m => V_p p m k ≥ J_p p k + t)).card ≤
    k * (M / p ^ (J_p p k + t) + 2) := by
  -- By Lemma V_p, the number of $m \in [M, 2M]$ with $V_p(m) \geq J_p + t$ is at most $k \cdot \text{card}( \{ m / p^{J_p + t} \} )$.
  have h_count : (Finset.filter (fun m => V_p p m k ≥ J_p p k + t) (Finset.Icc M (2 * M))).card ≤ ∑ i ∈ Finset.Icc 1 k, ((Finset.Icc M (2 * M)).filter (fun m => p ^ (J_p p k + t) ∣ m + i)).card := by
    have h_count : ∀ m ∈ Finset.Icc M (2 * M), V_p p m k ≥ J_p p k + t → ∃ i ∈ Finset.Icc 1 k, p ^ (J_p p k + t) ∣ m + i := by
      unfold V_p;
      intros m hm h_sup
      obtain ⟨i, hi⟩ : ∃ i ∈ Finset.Icc 1 k, padicValNat p (m + i) ≥ J_p p k + t := by
        contrapose! h_sup;
        rw [ Finset.sup_lt_iff ] ; aesop;
        exact Nat.zero_lt_of_lt ( h_sup 1 ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) );
      have h_div : p ^ (padicValNat p (m + i)) ∣ m + i := by
        exact pow_padicValNat_dvd;
      exact ⟨ i, hi.1, dvd_trans ( pow_dvd_pow _ hi.2 ) h_div ⟩;
    have h_count : (Finset.filter (fun m => V_p p m k ≥ J_p p k + t) (Finset.Icc M (2 * M))).card ≤ Finset.card (Finset.biUnion (Finset.Icc 1 k) (fun i => Finset.filter (fun m => p ^ (J_p p k + t) ∣ m + i) (Finset.Icc M (2 * M)))) := by
      exact Finset.card_le_card fun x hx => by aesop;
    exact h_count.trans ( Finset.card_biUnion_le );
  refine le_trans h_count ?_;
  refine' le_trans ( Finset.sum_le_sum fun i hi => show Finset.card _ ≤ M / p ^ ( J_p p k + t ) + 2 from _ ) _;
  · -- Applying the lemma_residue_interval with $Q = p^{J_p + t}$ and $r = -i \mod p^{J_p + t}$.
    have h_residue_interval : ((Finset.Icc M (2 * M)).filter (fun m => m % p ^ (J_p p k + t) = (p ^ (J_p p k + t) - i % p ^ (J_p p k + t)) % p ^ (J_p p k + t))).card ≤ M / p ^ (J_p p k + t) + 2 := by
      convert lemma_residue_interval M ( p ^ ( J_p p k + t ) ) ( ( p ^ ( J_p p k + t ) - i % p ^ ( J_p p k + t ) ) % p ^ ( J_p p k + t ) ) ( pow_pos hp.pos _ ) using 1;
    refine' le_trans _ h_residue_interval;
    refine' Finset.card_mono _;
    intro m hm; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
    refine' Nat.ModEq.symm ( Nat.modEq_of_dvd _ );
    obtain ⟨ x, hx ⟩ := Nat.modEq_zero_iff_dvd.mp hm.2; use x - ( i / p ^ ( J_p p k + t ) ) - 1; rw [ Nat.cast_sub <| Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ] ; push_cast ; linarith [ Nat.mod_add_div i ( p ^ ( J_p p k + t ) ) ] ;
  · norm_num

/-
kappa_p(m) is at least the number of digits d_u (for u < L) such that d_u >= (p+1)/2.
-/
def X_p (p m L : ℕ) : ℕ := ((Finset.range L).filter (fun u => (m / p ^ u) % p ≥ (p + 1) / 2)).card

lemma lemma_forced_carries_smallp (p m L : ℕ) (hp : p.Prime) :
    kappa p m ≥ X_p p m L := by
  revert m L;
  unfold X_p kappa;
  -- Let's choose any $m$ and $L$ and apply Kummer's theorem.
  intro m L
  have h_kummer : padicValNat p (Nat.choose (2 * m) m) = ∑ k ∈ Finset.range (Nat.log p (2 * m) + 1), ((2 * m) / p ^ (k + 1) - 2 * (m / p ^ (k + 1))) := by
    haveI := Fact.mk hp;
    rw [ padicValNat_choose ];
    any_goals exact Nat.lt_succ_self _;
    · norm_num [ two_mul, Nat.add_div ];
      rw [ Finset.card_filter ];
      rw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, Nat.add_div ];
      rw [ Finset.sum_range_succ ] ; norm_num [ Nat.add_div, hp.pos ];
      rw [ Nat.mod_eq_of_lt ] <;> linarith [ Nat.lt_pow_of_log_lt hp.one_lt ( by linarith : Nat.log p ( m + m ) < Nat.log p ( m + m ) + 1 ) ];
    · linarith;
  -- Each term in the sum $\sum_{k=0}^{L-1} (2m / p^{k+1} - 2(m / p^{k+1}))$ is at least 1 if $m / p^k$ has a digit greater than or equal to $(p+1)/2$ in its base-$p$ representation.
  have h_term_ge_one : ∀ k ∈ Finset.range L, (2 * m / p ^ (k + 1) - 2 * (m / p ^ (k + 1))) ≥ if m / p ^ k % p ≥ (p + 1) / 2 then 1 else 0 := by
    intro k hk;
    split_ifs <;> simp_all [ pow_succ ]
    refine' Nat.le_sub_of_add_le' _;
    rw [ Nat.le_div_iff_mul_le ( Nat.mul_pos ( pow_pos hp.pos _ ) hp.pos ) ];
    rw [ ← Nat.div_div_eq_div_mul ] at *;
    nlinarith [ Nat.div_mul_le_self m ( p ^ k ), Nat.div_add_mod m ( p ^ k ), Nat.mod_lt m ( pow_pos hp.pos k ), Nat.div_mul_le_self ( m / p ^ k ) p, Nat.div_add_mod ( m / p ^ k ) p, Nat.mod_lt ( m / p ^ k ) hp.pos, Nat.div_add_mod ( p + 1 ) 2, Nat.mod_lt ( p + 1 ) two_pos, pow_pos hp.pos k, pow_succ' p k ];
  have h_sum_ge_card : ∑ k ∈ Finset.range L, (2 * m / p ^ (k + 1) - 2 * (m / p ^ (k + 1))) ≥ Finset.card (Finset.filter (fun u => m / p ^ u % p ≥ (p + 1) / 2) (Finset.range L)) := by
    simpa [ Finset.sum_ite ] using Finset.sum_le_sum h_term_ge_one;
  refine le_trans h_sum_ge_card ?_;
  rw [ h_kummer ];
  by_cases hL : L ≤ Nat.log p (2 * m) + 1;
  · exact Finset.sum_le_sum_of_subset ( Finset.range_mono hL );
  · rw [ ← Finset.sum_range_add_sum_Ico _ ( by linarith : Nat.log p ( 2 * m ) + 1 ≤ L ) ];
    norm_num [ Nat.div_eq_of_lt ( show 2 * m < p ^ ( Nat.log p ( 2 * m ) + 1 ) from Nat.lt_pow_succ_log_self hp.one_lt _ ) ];
    intro i hi₁ hi₂; rw [ Nat.div_eq_of_lt, Nat.div_eq_of_lt ] <;> norm_num [ Nat.pow_succ', Nat.mul_div_assoc ] ;
    · have := Nat.lt_pow_of_log_lt hp.one_lt ( by linarith : Nat.log p ( 2 * m ) < i ) ; nlinarith [ hp.two_le ] ;
    · exact lt_of_lt_of_le ( Nat.lt_pow_succ_log_self hp.one_lt _ ) ( by rw [ ← pow_succ' ] ; exact Nat.pow_le_pow_right hp.pos ( by linarith ) )

/-
Definitions of eta, theta, mu, L_p, and Q_p. eta is 1/10. theta is the probability of a carry. mu is the expected number of carries. L_p is the number of digits considered. Q_p is p^L_p.
-/
noncomputable def eta : ℝ := 1 / 10

noncomputable def theta (p : ℕ) : ℝ := if p = 2 then 1 / 2 else (p - 1 : ℝ) / (2 * p)

noncomputable def mu (p L : ℕ) : ℝ := L * theta p

noncomputable def L_p (p M : ℕ) : ℕ := Nat.floor ((1 - eta) * Real.log M / Real.log p)

noncomputable def Q_p (p M : ℕ) : ℕ := p ^ (L_p p M)

/-
The probability that m mod Q is in A is close to |A|/Q, with error bounded by 2/M^eta.
-/
noncomputable def Prob_Icc (M : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℝ :=
  ((Finset.Icc M (2 * M)).filter P).card / (M + 1)

lemma lemma_mod_uniform (M Q : ℕ) (A : Finset ℕ) (hM : M > 0) (hQ : Q > 0)
    (hQ_bound : (Q : ℝ) ≤ (M : ℝ) ^ (1 - eta)) (hA : ∀ a ∈ A, a < Q) :
    Prob_Icc M (fun m => m % Q ∈ A) ≤ (A.card : ℝ) / Q + 2 / (M : ℝ) ^ eta := by
  -- Applying the lemma to bound the count.
  have h_count_bound : ((Finset.Icc M (2 * M)).filter (fun m => m % Q ∈ A)).card ≤ (M + 1) * (A.card / Q : ℝ) + 2 * A.card := by
    -- The count of elements in the interval [M, 2M] that are congruent to an element in A modulo Q is at most |A| * (M/Q + 2).
    have h_count_bound : ((Finset.Icc M (2 * M)).filter (fun m => m % Q ∈ A)).card ≤ A.card * (M / Q + 2) := by
      have h_count : ((Finset.Icc M (2 * M)).filter (fun m => m % Q ∈ A)).card ≤ ∑ a ∈ A, ((Finset.Icc M (2 * M)).filter (fun m => m % Q = a)).card := by
        have h_count_bound : ((Finset.Icc M (2 * M)).filter (fun m => m % Q ∈ A)).card ≤ Finset.card (Finset.biUnion A (fun a => Finset.filter (fun m => m % Q = a) (Finset.Icc M (2 * M)))) := by
          exact Finset.card_le_card fun x hx => by aesop;
        exact h_count_bound.trans ( Finset.card_biUnion_le );
      refine le_trans h_count ?_;
      exact le_trans ( Finset.sum_le_sum fun x hx => show Finset.card _ ≤ M / Q + 2 from lemma_residue_interval M Q x hQ ) ( by norm_num );
    field_simp;
    exact mod_cast by nlinarith [ Nat.div_mul_le_self M Q ] ;
  -- Dividing both sides of the inequality by $(M + 1)$, we get the desired result.
  have h_div : ((Finset.Icc M (2 * M)).filter (fun m => m % Q ∈ A)).card / (M + 1 : ℝ) ≤ (A.card / Q : ℝ) + 2 * A.card / (M + 1) := by
    rw [ div_le_iff₀ ] <;> first | positivity | nlinarith [ mul_div_cancel₀ ( 2 * A.card : ℝ ) ( by positivity : ( M : ℝ ) + 1 ≠ 0 ) ] ;
  -- Since $A.card \leq Q$ and $Q \leq M^{1-\eta}$, we have $2 * A.card / (M + 1) \leq 2 * M^{1-\eta} / (M + 1)$.
  have h_bound : 2 * A.card / (M + 1 : ℝ) ≤ 2 * M ^ (1 - eta) / (M + 1 : ℝ) := by
    gcongr;
    exact le_trans ( mod_cast le_trans ( Finset.card_le_card ( show A ⊆ Finset.range Q from fun x hx => Finset.mem_range.mpr ( hA x hx ) ) ) ( by simp ) ) hQ_bound;
  refine le_trans h_div <| add_le_add_left ( h_bound.trans ?_ ) _;
  rw [ div_le_div_iff₀ ] <;> try positivity;
  rw [ mul_assoc, ← Real.rpow_add ] <;> norm_num ; linarith

/-
Q_p is at most M^(1-eta).
-/
lemma lemma_Q_p_bound (p M : ℕ) (hp : p.Prime) (hM : M > 0) :
    (Q_p p M : ℝ) ≤ (M : ℝ) ^ (1 - eta) := by
  unfold Q_p;
  rw [ Real.le_rpow_iff_log_le ] <;> norm_num;
  · have := Nat.floor_le ( show 0 ≤ ( 1 - eta ) * Real.log M / Real.log p by exact div_nonneg ( mul_nonneg ( sub_nonneg.mpr <| by norm_num [ eta ] ) <| Real.log_nonneg <| Nat.one_le_cast.mpr hM ) <| Real.log_nonneg <| Nat.one_le_cast.mpr hp.pos );
    rwa [ le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr hp.one_lt ) ] at this;
  · exact_mod_cast pow_pos hp.pos _;
  · positivity

/-
The sum of exp(-t X_p) over all m is (p * ((1-theta) + theta e^-t))^L.
-/
lemma lemma_exp_sum_X_p (p L : ℕ) (t : ℝ) (hp : p.Prime) :
    ∑ m ∈ Finset.range (p ^ L), Real.exp (-t * (X_p p m L : ℝ)) =
    (p : ℝ) ^ L * ((1 - theta p) + theta p * Real.exp (-t)) ^ L := by
  induction' L with L ih generalizing t;
  · unfold X_p; norm_num;
  · -- We can split the sum into two parts: one over $m$ divisible by $p$ and one over $m$ not divisible by $p$.
    have h_split : ∑ m ∈ Finset.range (p ^ (L + 1)), Real.exp (-t * (X_p p m (L + 1))) = ∑ d ∈ Finset.range p, ∑ m' ∈ Finset.range (p ^ L), Real.exp (-t * (X_p p (d * p ^ L + m') (L + 1))) := by
      have h_split : Finset.range (p ^ (L + 1)) = Finset.biUnion (Finset.range p) (fun d => Finset.image (fun m' => d * p ^ L + m') (Finset.range (p ^ L))) := by
        ext m
        simp [Finset.mem_range, Finset.mem_biUnion, Finset.mem_image];
        exact ⟨ fun h => ⟨ m / p ^ L, Nat.div_lt_of_lt_mul <| by rw [ pow_succ' ] at h; linarith, m % p ^ L, Nat.mod_lt _ <| pow_pos hp.pos _, by rw [ Nat.div_add_mod' ] ⟩, by rintro ⟨ a, ha, b, hb, rfl ⟩ ; rw [ pow_succ' ] ; nlinarith [ pow_pos hp.pos L ] ⟩;
      rw [ h_split, Finset.sum_biUnion ];
      · exact Finset.sum_congr rfl fun _ _ => Finset.sum_image <| by aesop;
      · intros d hd d' hd' hdd'; simp_all +decide [ Finset.disjoint_left ];
        intro a ha x hx; contrapose! hdd'; nlinarith;
    -- We can simplify the expression inside the sum.
    have h_simplify : ∀ d ∈ Finset.range p, ∑ m' ∈ Finset.range (p ^ L), Real.exp (-t * (X_p p (d * p ^ L + m') (L + 1))) = Real.exp (-t * (if d ≥ (p + 1) / 2 then 1 else 0)) * ∑ m' ∈ Finset.range (p ^ L), Real.exp (-t * (X_p p m' L)) := by
      intros d hd
      have h_simplify : ∀ m' ∈ Finset.range (p ^ L), X_p p (d * p ^ L + m') (L + 1) = X_p p m' L + (if d ≥ (p + 1) / 2 then 1 else 0) := by
        intro m' hm'
        simp [X_p];
        rw [ Finset.card_filter, Finset.card_filter ];
        rw [ Finset.sum_range_succ ];
        congr! 2;
        · rw [ Nat.add_div ] <;> norm_num [ hp.pos ];
          rw [ Nat.add_div ] <;> norm_num [ hp.pos ];
          norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd ( pow_dvd_pow p ( show ‹_› ≤ L from Finset.mem_range_le ‹_› ) ) ];
          rw [ Nat.mod_eq_zero_of_dvd ( Nat.dvd_div_of_mul_dvd _ ) ];
          · split_ifs <;> norm_num;
            all_goals simp_all
            · exact absurd ‹_› ( not_le_of_gt ( Nat.mod_lt _ ( pow_pos hp.pos _ ) ) );
            · linarith [ Nat.mod_lt m' ( pow_pos hp.pos ‹_› ) ];
            · linarith [ Nat.mod_lt m' ( pow_pos hp.pos ‹_› ) ];
            · linarith [ Nat.mod_lt m' ( pow_pos hp.pos ‹_› ) ];
            · linarith;
          · rw [ ← pow_succ ];
            exact dvd_mul_of_dvd_right ( pow_dvd_pow _ ( by linarith [ Finset.mem_range.mp ‹_› ] ) ) _;
        · norm_num [ Nat.add_div, Nat.mul_div_assoc, hp.pos ];
          norm_num [ Nat.div_eq_of_lt ( show m' < p ^ L from Finset.mem_range.mp hm' ), Nat.mod_eq_of_lt ( show m' < p ^ L from Finset.mem_range.mp hm' ) ];
          split_ifs <;> norm_num [ Nat.mod_eq_of_lt ( show d < p from Finset.mem_range.mp hd ) ];
          · linarith [ Finset.mem_range.mp hm' ];
          · linarith [ Finset.mem_range.mp hm' ];
      rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun m' hm' => _ ; rw [ h_simplify m' hm' ] ; split_ifs <;> ring_nf;
      · rw [ ← Real.exp_add ] ; push_cast ; ring_nf;
      · norm_num;
    -- The sum of the first part simplifies to $p * ((1 - \theta_p) + \theta_p * \exp(-t))$.
    have h_first_part : ∑ d ∈ Finset.range p, Real.exp (-t * (if d ≥ (p + 1) / 2 then 1 else 0)) = p * ((1 - theta p) + theta p * Real.exp (-t)) := by
      rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num [ Finset.sum_range_succ', Nat.add_div ];
      · simp_all +decide [ Nat.prime_mul_iff ];
        unfold theta; norm_num [ Finset.sum_range_succ ] ; ring;
      · unfold theta; norm_num [ Nat.add_div ] ; ring_nf;
        rw [ show ( Finset.range ( c * 2 ) ) = Finset.range c ∪ Finset.Ico c ( c * 2 ) by rw [ Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico ] <;> linarith, Finset.sum_union ] <;> norm_num;
        · rw [ Finset.sum_congr rfl fun x hx => by rw [ if_neg ( by linarith [ Finset.mem_range.mp hx ] ) ] ] ; norm_num [ Finset.sum_Ico_eq_sum_range ] ; ring_nf;
          split_ifs <;> norm_num [ Nat.mul_two ] <;> ring_nf;
          · grind;
          · -- Combine like terms and simplify the expression.
            field_simp
            ring;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp hx₁, Finset.mem_Ico.mp hx₂ ] ;
    rw [ h_split, Finset.sum_congr rfl h_simplify, ← Finset.sum_mul _ _ _ ];
    rw [ h_first_part, ih ] ; ring

/-
Markov's inequality applied to exp(-t X_p).
-/
lemma lemma_markov_exp (p L : ℕ) (t : ℝ) (hp : p.Prime) (ht : t > 0) :
    ((Finset.range (p ^ L)).filter (fun m => X_p p m L ≤ (mu p L) / 2)).card / (p ^ L : ℝ) ≤
    Real.exp (t * (mu p L) / 2) * ((1 - theta p) + theta p * Real.exp (-t)) ^ L := by
  rw [ div_le_iff₀ ];
  · -- Apply the exponential inequality to the sum.
    have h_exp : (∑ m ∈ Finset.range (p ^ L), Real.exp (-t * (X_p p m L : ℝ))) ≥ (∑ m ∈ Finset.filter (fun m => (X_p p m L : ℝ) ≤ mu p L / 2) (Finset.range (p ^ L)), Real.exp (-t * (mu p L / 2))) := by
      exact le_trans ( Finset.sum_le_sum fun x hx => Real.exp_le_exp.mpr <| mul_le_mul_of_nonpos_left ( Finset.mem_filter.mp hx |>.2 ) <| neg_nonpos.mpr ht.le ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Real.exp_nonneg _ );
    rw [ lemma_exp_sum_X_p ] at h_exp;
    · norm_num [ Real.exp_neg ] at *;
      rw [ ← div_eq_mul_inv, div_le_iff₀ ( Real.exp_pos _ ) ] at * ; ring_nf at * ; linarith;
    · assumption;
  · exact_mod_cast pow_pos hp.pos _

/-
The inequality needed for the Chernoff bound with t = log 2.
-/
lemma lemma_chernoff_inequality (theta : ℝ) (h_theta : 0 ≤ theta ∧ theta ≤ 1) :
    Real.log 2 * (theta / 2) + Real.log (1 - theta + theta * Real.exp (-Real.log 2)) ≤ -theta / 8 := by
  norm_num [ Real.exp_neg, Real.exp_log ];
  have := Real.log_two_lt_d9 ; norm_num1 at * ; nlinarith [ Real.log_le_sub_one_of_pos ( show 0 < 1 - theta + theta * ( 1 / 2 ) by nlinarith ) ]

/-
The probability that X_p(m) <= mu/2 is at most exp(-mu/8).
-/
lemma lemma_chernoff_binomial (p L : ℕ) (hp : p.Prime) :
    ((Finset.range (p ^ L)).filter (fun m => X_p p m L ≤ (mu p L) / 2)).card / (p ^ L : ℝ) ≤ Real.exp (- (mu p L) / 8) := by
  -- Applying Markov's inequality with $t = \log 2$.
  have h_markov : ((Finset.range (p ^ L)).filter (fun m => X_p p m L ≤ (mu p L) / 2)).card / (p ^ L : ℝ) ≤ Real.exp (Real.log 2 * (mu p L) / 2) * ((1 - theta p) + theta p * Real.exp (-Real.log 2)) ^ L := by
    convert lemma_markov_exp p L ( Real.log 2 ) hp ( Real.log_pos one_lt_two ) using 1;
  -- Using the inequality from Lemma~\ref{lem:chernoff_inequality}, we get:
  have h_exp_bound : Real.log ((1 - theta p) + theta p * Real.exp (-Real.log 2)) + (Real.log 2 * (theta p / 2)) ≤ -theta p / 8 := by
    convert lemma_chernoff_inequality ( theta p ) _ using 1;
    · ring;
    · unfold theta;
      split_ifs <;> constructor <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast hp.two_le, div_mul_cancel₀ ( ( p : ℝ ) - 1 ) ( by norm_cast; linarith [ hp.two_le ] : ( 2 * p : ℝ ) ≠ 0 ) ];
  refine le_trans h_markov ?_;
  rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ];
  · rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by rw [ show mu p L = L * theta p by rfl ] ; nlinarith );
  · unfold theta; norm_num [ Real.exp_neg, Real.exp_log ] ; ring_nf ; norm_num;
    split_ifs <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast hp.two_le, mul_inv_cancel₀ ( show ( p : ℝ ) ≠ 0 by exact_mod_cast hp.ne_zero ) ]

/-
The coefficient of log M on the LHS is strictly greater than on the RHS.
-/
noncomputable def coeff_lhs (p : ℕ) : ℝ := (1 - eta) * theta p / (2 * Real.log p)

/-
Definitions of k_val and t_val. k_val is floor(c log M). t_val is ceil(10 log log M).
-/
noncomputable def k_val (c : ℝ) (M : ℕ) : ℕ := Nat.floor (c * Real.log M)

noncomputable def t_val (M : ℕ) : ℕ := Nat.ceil (10 * Real.log (Real.log M))

/-
Lower bound for mu/2 in terms of log M.
-/
lemma lemma_mu_lower_bound (p M : ℕ) (hp : p.Prime) :
    (mu p (L_p p M)) / 2 ≥ coeff_lhs p * Real.log M - theta p / 2 := by
  unfold mu coeff_lhs;
  -- Substitute $L_p$ with $(1 - \eta) \log M / \log p$ and simplify.
  have h_subst : (L_p p M : ℝ) ≥ (1 - eta) * Real.log M / Real.log p - 1 := by
    refine' le_trans ( sub_le_iff_le_add.mpr _ ) ( Nat.sub_one_lt_floor _ |> le_of_lt );
    norm_num;
  ring_nf at *; nlinarith [ show 0 ≤ theta p from by unfold theta; split_ifs <;> exact div_nonneg ( by linarith [ show ( p : ℝ ) ≥ 2 by exact Nat.cast_le.mpr hp.two_le ] ) ( by linarith [ show ( p : ℝ ) ≥ 2 by exact Nat.cast_le.mpr hp.two_le ] ) ] ;

/-
Bound on the number of m with few carries for a fixed prime p.
-/
lemma lemma_bad_carries_bound (p M : ℕ) (hp : p.Prime) (hM : M > 0) :
    ((Finset.Icc M (2 * M)).filter (fun m => X_p p m (L_p p M) ≤ (mu p (L_p p M)) / 2)).card ≤
    (M + 1) * (Real.exp (- (mu p (L_p p M)) / 8) + 2 / (M : ℝ) ^ eta) := by
  -- Apply the Chernoff bound to the probability that $X_p \leq \mu/2$.
  have h_chernoff : ((Finset.range (p ^ (L_p p M))).filter (fun m => X_p p m (L_p p M) ≤ (mu p (L_p p M)) / 2)).card / (p ^ (L_p p M) : ℝ) ≤ Real.exp (- (mu p (L_p p M)) / 8) := by
    convert lemma_chernoff_binomial p ( L_p p M ) hp using 1;
  -- Apply the lemma_mod_uniform to bound the probability that $m \mod Q_p \in A$.
  have h_mod_uniform : ((Finset.Icc M (2 * M)).filter (fun m => m % (p ^ (L_p p M)) ∈ Finset.filter (fun m => X_p p m (L_p p M) ≤ (mu p (L_p p M)) / 2) (Finset.range (p ^ (L_p p M))))).card ≤ (M + 1) * ((Finset.filter (fun m => X_p p m (L_p p M) ≤ (mu p (L_p p M)) / 2) (Finset.range (p ^ (L_p p M)))).card / (p ^ (L_p p M) : ℝ) + 2 / (M : ℝ) ^ eta) := by
    have := lemma_mod_uniform M ( p ^ L_p p M ) ( Finset.filter ( fun m => X_p p m ( L_p p M ) ≤ ( mu p ( L_p p M ) ) / 2 ) ( Finset.range ( p ^ L_p p M ) ) ) hM ( pow_pos hp.pos _ ) ?_ ?_;
    · rw [ Prob_Icc ] at this;
      rw [ div_le_iff₀ ] at this <;> norm_num at * <;> linarith;
    · convert lemma_Q_p_bound p M hp hM using 1;
    · aesop;
  refine le_trans ?_ ( h_mod_uniform.trans <| mul_le_mul_of_nonneg_left ( add_le_add_right h_chernoff _ ) <| by positivity );
  gcongr;
  intro m hm; simp +decide [ Nat.mod_lt _ ( pow_pos hp.pos _ ) ] ;
  -- Since $m \equiv m \mod p^{L_p p M} \pmod{p^{L_p p M}}$, we have $X_p p m (L_p p M) = X_p p (m \mod p^{L_p p M}) (L_p p M)$.
  have h_cong : ∀ u < L_p p M, (m / p ^ u) % p = ((m % p ^ L_p p M) / p ^ u) % p := by
    intro u hu; rw [ ← Nat.mod_add_div m ( p ^ L_p p M ) ] ; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.div_div_eq_div_mul ] ;
    norm_num [ Nat.add_div, Nat.mul_div_assoc, pow_pos hp.pos ];
    norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd ( pow_dvd_pow _ hu.le ) ];
    rw [ if_neg ( Nat.not_le_of_gt ( Nat.mod_lt _ ( pow_pos hp.pos _ ) ) ) ] ; norm_num [ Nat.mul_div_assoc _ ( pow_dvd_pow _ hu.le ) ] ;
    norm_num [ show p ^ L_p p M * ( m / p ^ L_p p M ) / p ^ u = p ^ ( L_p p M - u ) * ( m / p ^ L_p p M ) by rw [ Nat.div_eq_of_eq_mul_left ( pow_pos hp.pos _ ) ] ; rw [ ← mul_right_comm, ← pow_add, Nat.sub_add_cancel hu.le ] ];
    norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd ( dvd_pow_self _ ( Nat.sub_ne_zero_of_lt hu ) ) ];
  convert hm using 1;
  exact mod_cast congr_arg Finset.card ( Finset.filter_congr fun x hx => by aesop )

/-
The set of triples (a, b, n) satisfying the conditions of Erdos problem #728.
-/
def good_triples (C ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  { t | let (a, b, n) := t; ε * n ≤ a ∧ a ≤ (1 - ε) * n ∧ ε * n ≤ b ∧ b ≤ (1 - ε) * n ∧
        Nat.factorial a * Nat.factorial b ∣ Nat.factorial n * Nat.factorial (a + b - n) ∧
        (a + b : ℝ) > n + C * Real.log n }

/-
The set of integers m in [M, 2M] that fail the carry or spike conditions for some prime p <= 2k.
-/
noncomputable def bad_m_set (M : ℕ) (c : ℝ) : Finset ℕ :=
  (Finset.Icc M (2 * M)).filter (fun m =>
    ∃ p ∈ Finset.range (2 * k_val c M + 1), p.Prime ∧
      (X_p p m (L_p p M) ≤ mu p (L_p p M) / 2 ∨
       V_p p m (k_val c M) ≥ J_p p (k_val c M) + t_val M))

/-
Definitions of the sets of m that fail the carry condition and the spike condition for a given prime p.
-/
noncomputable def bad_carry_set (p M : ℕ) : Finset ℕ :=
  (Finset.Icc M (2 * M)).filter (fun m => X_p p m (L_p p M) ≤ (mu p (L_p p M)) / 2)

noncomputable def bad_spike_set (p M : ℕ) (c : ℝ) : Finset ℕ :=
  (Finset.Icc M (2 * M)).filter (fun m => V_p p m (k_val c M) ≥ J_p p (k_val c M) + t_val M)

/-
The number of bad m is at most the sum over primes p of the number of m failing the carry condition plus the number of m failing the spike condition.
-/
lemma lemma_bad_m_card_le_sum (M : ℕ) (c : ℝ) :
    (bad_m_set M c).card ≤ ∑ p ∈ Finset.range (2 * k_val c M + 1),
      (if p.Prime then (bad_carry_set p M).card + (bad_spike_set p M c).card else 0) := by
        unfold bad_m_set;
        refine' le_trans ( Finset.card_le_card _ ) _;
        exact Finset.biUnion ( Finset.filter Nat.Prime ( Finset.range ( 2 * k_val c M + 1 ) ) ) fun p => Finset.filter ( fun m => X_p p m ( L_p p M ) ≤ mu p ( L_p p M ) / 2 ) ( Finset.Icc M ( 2 * M ) ) ∪ Finset.filter ( fun m => V_p p m ( k_val c M ) ≥ J_p p ( k_val c M ) + t_val M ) ( Finset.Icc M ( 2 * M ) );
        · intro m hm; aesop;
        · refine' le_trans ( Finset.card_biUnion_le ) _;
          rw [ Finset.sum_filter ];
          exact Finset.sum_le_sum fun p hp => by split_ifs <;> [ exact Finset.card_union_le _ _ ; exact le_rfl ] ;

/-
Definitions of the total number of bad m due to carries and spikes, summed over primes.
-/
noncomputable def sum_bad_carries (M : ℕ) (c : ℝ) : ℕ :=
  ∑ p ∈ Finset.range (2 * k_val c M + 1), (if p.Prime then (bad_carry_set p M).card else 0)

noncomputable def sum_bad_spikes (M : ℕ) (c : ℝ) : ℕ :=
  ∑ p ∈ Finset.range (2 * k_val c M + 1), (if p.Prime then (bad_spike_set p M c).card else 0)

/-
Definitions of the upper bounds for the sums of bad counts, derived from the individual bounds for each prime.
-/
noncomputable def sum_bound_spikes (M : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (2 * k_val c M + 1),
    if p.Prime then (k_val c M : ℝ) * ((M : ℝ) / (p : ℝ) ^ (J_p p (k_val c M) + t_val M) + 2) else 0

noncomputable def sum_bound_carries (M : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (2 * k_val c M + 1),
    if p.Prime then (M + 1 : ℝ) * (Real.exp (- (mu p (L_p p M)) / 8) + 2 / (M : ℝ) ^ eta) else 0

/-
Definitions of the two parts of the upper bound for the sum of bad carry probabilities.
-/
noncomputable def sum_term1 (M : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (2 * k_val c M + 1), if p.Prime then 2 / (M : ℝ) ^ eta else 0

noncomputable def sum_term2 (M : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (2 * k_val c M + 1), if p.Prime then Real.exp (- (mu p (L_p p M)) / 8) else 0

/-
The sum of 2/M^eta over primes is bounded by the number of terms times the value.
-/
lemma lemma_sum_term1_bound (M : ℕ) (c : ℝ) (hM : M > 0) :
    sum_term1 M c ≤ (2 * k_val c M + 1) * (2 / (M : ℝ) ^ eta) := by
      exact le_trans ( Finset.sum_le_sum fun _ _ => by split_ifs <;> first | positivity | exact le_rfl ) ( by norm_num )

/-
Bound for the exponential term involving mu.
-/
lemma lemma_exp_mu_bound (p M : ℕ) (hp : p.Prime) (hM : M > 0) :
    Real.exp (- (mu p (L_p p M)) / 8) ≤ Real.exp (theta p / 8) * (M : ℝ) ^ (- coeff_lhs p / 4) := by
  rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hM ) ];
  rw [ ← Real.exp_add ] ; ring_nf;
  norm_num +zetaDelta at *;
  -- Apply the lower bound result for mu/2.
  have h_lower_bound : (mu p (L_p p M)) / 2 ≥ coeff_lhs p * Real.log M - theta p / 2 := by
    exact lemma_mu_lower_bound p M hp;
  linarith

/-
Theta is at least 1/3 for all primes.
-/
lemma lemma_theta_ge_third (p : ℕ) (hp : p.Prime) : theta p ≥ 1 / 3 := by
  unfold theta;
  rcases p with ( _ | _ | _ | p ) <;> norm_num at *;
  rw [ if_neg ( by linarith ), le_div_iff₀ ] <;> linarith

/-
Lower bound for coeff_lhs.
-/
lemma lemma_coeff_lhs_lower_bound (p : ℕ) (hp : p.Prime) :
    coeff_lhs p ≥ (1 - eta) / (6 * Real.log p) := by
      have h_theta_ge_third : theta p ≥ 1 / 3 := by
        exact lemma_theta_ge_third p hp;
      have h_coeff_lhs_ge : coeff_lhs p ≥ (1 - eta) * (1 / 3) / (2 * Real.log p) := by
        exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_theta_ge_third <| sub_nonneg.2 <| by norm_num [ eta ] ) <| inv_nonneg.2 <| mul_nonneg zero_le_two <| Real.log_natCast_nonneg _;
      exact h_coeff_lhs_ge.trans' ( ge_of_eq <| by ring )

/-
Lower bound for coeff_lhs / 4.
-/
lemma lemma_exponent_bound (p : ℕ) (hp : p.Prime) :
    coeff_lhs p / 4 ≥ (1 - eta) / (24 * Real.log p) := by
      have := lemma_coeff_lhs_lower_bound p hp; ring_nf at *; linarith;

/-
Uniform bound for the exponential term in the sum for term2.
-/
lemma lemma_term2_bound_uniform (M : ℕ) (c : ℝ) (hM : M > 1)
    (p : ℕ) (hp : p.Prime) (hp_range : p ∈ Finset.range (2 * k_val c M + 1)) :
    Real.exp (- (mu p (L_p p M)) / 8) ≤
    Real.exp (1 / 16) * (M : ℝ) ^ (- (1 - eta) / (24 * Real.log (2 * k_val c M))) := by
      refine' le_trans _ ( mul_le_mul_of_nonneg_right ( Real.exp_le_exp.mpr <| _ ) <| by positivity );
      refine' le_trans ( lemma_exp_mu_bound p M hp ( pos_of_gt hM ) ) _;
      refine' mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_exponent_le ( mod_cast hM.le ) _ ) ( by positivity );
      · have := lemma_exponent_bound p hp;
        rw [ show ( -coeff_lhs p / 4 : ℝ ) = - ( coeff_lhs p / 4 ) by ring, neg_div ];
        refine' neg_le_neg ( this.trans' _ );
        gcongr <;> norm_cast;
        · exact sub_nonneg_of_le ( by rw [ show eta = 1 / 10 by rfl ] ; norm_num );
        · exact mul_pos ( by norm_num ) ( Real.log_pos ( Nat.one_lt_cast.mpr hp.one_lt ) );
        · exact hp.pos;
        · linarith [ Finset.mem_range.mp hp_range ];
      · unfold theta;
        split_ifs <;> nlinarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast hp.two_le, div_mul_cancel₀ ( ( p : ℝ ) - 1 ) ( show ( 2 * p : ℝ ) ≠ 0 by norm_cast; linarith [ hp.two_le ] ) ]

/-
The ratio log M / log(k_val c M) tends to infinity as M tends to infinity.
-/
lemma lemma_log_ratio_tendsto_atTop (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun M : ℕ => Real.log (M : ℝ) / Real.log (k_val c M : ℝ)) Filter.atTop Filter.atTop := by
      -- For large M, k_val c M is approximately c log M, so log(k_val c M) is approximately log(c) + log(log M).
      have h_log_approx : Filter.Tendsto (fun M : ℕ => Real.log (k_val c M) / Real.log (Real.log M)) Filter.atTop (nhds 1) := by
        -- Since $k_val c M$ is approximately $c \log M$, we have $\log(k_val c M) \approx \log(c \log M) = \log c + \log(\log M)$.
        have h_log_approx : Filter.Tendsto (fun M : ℕ => Real.log (k_val c M) - Real.log (Real.log M)) Filter.atTop (nhds (Real.log c)) := by
          -- Since $k_val c M$ is approximately $c \log M$, we have $\frac{k_val c M}{c \log M} \to 1$ as $M \to \infty$.
          have h_frac : Filter.Tendsto (fun M : ℕ => (k_val c M : ℝ) / (c * Real.log M)) Filter.atTop (nhds 1) := by
            -- We'll use the fact that $\frac{\lfloor x \rfloor}{x} \to 1$ as $x \to \infty$.
            have h_floor : Filter.Tendsto (fun x : ℝ => (Nat.floor x : ℝ) / x) Filter.atTop (nhds 1) := by
              rw [ Metric.tendsto_nhds ];
              intro ε hε; filter_upwards [ Filter.eventually_gt_atTop ( ε⁻¹ + 1 ), Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using abs_lt.mpr ⟨ by nlinarith [ Nat.floor_le hx₂.le, Nat.lt_floor_add_one x, mul_inv_cancel₀ hε.ne', div_mul_cancel₀ ( Nat.floor x : ℝ ) hx₂.ne' ], by nlinarith [ Nat.floor_le hx₂.le, Nat.lt_floor_add_one x, mul_inv_cancel₀ hε.ne', div_mul_cancel₀ ( Nat.floor x : ℝ ) hx₂.ne' ] ⟩ ;
            exact h_floor.comp ( Filter.Tendsto.const_mul_atTop hc <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
          have := h_frac.log;
          simp +zetaDelta at *;
          have := this.add_const ( Real.log c ) ; simp_all
          refine' this.congr' ( by filter_upwards [ h_frac.eventually ( lt_mem_nhds one_pos ) ] with M hM using by rw [ Real.log_div ( by aesop ) ( by aesop ) ] ; rw [ Real.log_mul ( by positivity ) ( by aesop ) ] ; ring );
        have h_log_approx : Filter.Tendsto (fun M : ℕ => (Real.log (k_val c M) - Real.log (Real.log M)) / Real.log (Real.log M)) Filter.atTop (nhds 0) := by
          exact h_log_approx.div_atTop ( Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop );
        have := h_log_approx.const_add 1;
        simpa using this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 2 ] with x hx using by rw [ one_add_div ( ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( x : ℝ ) ≥ 3 by exact_mod_cast hx ] ) ] ; ring );
      have h_log_ratio : Filter.Tendsto (fun M : ℕ => Real.log M / Real.log (Real.log M)) Filter.atTop Filter.atTop := by
        -- Let $y = \log M$, therefore the expression becomes $\frac{y}{\log y}$.
        suffices h_log_y : Filter.Tendsto (fun y : ℝ => y / Real.log y) Filter.atTop Filter.atTop by
          exact h_log_y.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        -- Let $z = \log y$, therefore the expression becomes $\frac{e^z}{z}$.
        suffices h_exp_z : Filter.Tendsto (fun z : ℝ => Real.exp z / z) Filter.atTop Filter.atTop by
          have := h_exp_z.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
        simpa using Real.tendsto_exp_div_pow_atTop 1;
      have h_log_ratio : Filter.Tendsto (fun M : ℕ => (Real.log M / Real.log (Real.log M)) * (Real.log (Real.log M) / Real.log (k_val c M))) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.atTop_mul_pos;
        exacts [ zero_lt_one, h_log_ratio, by simpa using h_log_approx.inv₀ ];
      refine h_log_ratio.congr' ( by filter_upwards [ h_log_approx.eventually_ne one_ne_zero ] with M hM using by rw [ div_mul_div_cancel₀ ( by aesop ) ] )

/-
The ratio log M / log(2 * k_val c M) tends to infinity as M tends to infinity.
-/
lemma lemma_log_ratio_two_k_val_tendsto_atTop (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun M : ℕ => Real.log (M : ℝ) / Real.log (2 * k_val c M : ℝ)) Filter.atTop Filter.atTop := by
      -- We'll use the fact that if the denominator grows much faster than the numerator, the quotient tends to infinity.
      have h_log_ratio : Filter.Tendsto (fun M : ℕ => Real.log (M : ℝ) / Real.log (k_val c M : ℝ)) Filter.atTop Filter.atTop := by
        exact lemma_log_ratio_tendsto_atTop c hc;
      have h_log_ratio : Filter.Tendsto (fun M : ℕ => (Real.log (M : ℝ) / Real.log (k_val c M : ℝ)) / (1 + Real.log 2 / Real.log (k_val c M : ℝ))) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.atTop_mul_pos;
        exact zero_lt_one;
        · convert h_log_ratio using 1;
        · exact le_trans ( Filter.Tendsto.inv₀ ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop.comp <| tendsto_nat_floor_atTop.comp <| Filter.Tendsto.const_mul_atTop hc <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop ) <| by norm_num ) <| by norm_num;
      refine h_log_ratio.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1, ‹Filter.Tendsto ( fun M : ℕ => Real.log M / Real.log ( k_val c M : ℝ ) ) Filter.atTop Filter.atTop›.eventually_gt_atTop 0 ] with M hM₁ hM₂;
      rw [ Real.log_mul ( by positivity ) ( by aesop ) ] ; rw [ div_div, mul_add, mul_div_cancel₀ _ ( by aesop ) ] ; ring;

/-
The expression log(2k+1) * log(2k) / log M tends to 0.
-/
lemma lemma_log_term_small (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun M : ℕ => Real.log (2 * k_val c M + 1 : ℝ) * Real.log (2 * k_val c M : ℝ) / Real.log (M : ℝ)) Filter.atTop (nhds 0) := by
  -- We'll use that $k_val c M \approx c \log M$ for large $M$.
  have h_k_val_approx : Filter.Tendsto (fun M => (k_val c M : ℝ) / Real.log M) Filter.atTop (nhds c) := by
    have h_k_val_approx : Filter.Tendsto (fun M => (Nat.floor (c * Real.log M) : ℝ) / Real.log M) Filter.atTop (nhds c) := by
      have : Filter.Tendsto (fun M => (c * Real.log M - 1 : ℝ) / Real.log M) Filter.atTop (nhds c) := by
        ring_nf;
        exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_assoc, mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ), mul_one ] ) ) ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) ) ) ( by norm_num )
      refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' this tendsto_const_nhds _ _;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ div_le_div_iff_of_pos_right ( Real.log_pos hx ) ] ; linarith [ Nat.lt_floor_add_one ( c * Real.log x ) ] ;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ div_le_iff₀ ( Real.log_pos hx ) ] ; nlinarith [ Nat.floor_le ( show 0 ≤ c * Real.log x by exact mul_nonneg hc.le ( Real.log_nonneg hx.le ) ) ] ;
    convert h_k_val_approx.comp tendsto_natCast_atTop_atTop using 1;
  -- We can use the fact that $\log(2k+1) \sim \log(k)$ and $\log(2k) \sim \log(k)$ for large $k$.
  have h_log_approx : Filter.Tendsto (fun M => Real.log (2 * k_val c M + 1) / Real.log (k_val c M)) Filter.atTop (nhds 1) ∧ Filter.Tendsto (fun M => Real.log (2 * k_val c M) / Real.log (k_val c M)) Filter.atTop (nhds 1) := by
    have h_log_approx : Filter.Tendsto (fun x : ℝ => Real.log (2 * x + 1) / Real.log x) Filter.atTop (nhds 1) ∧ Filter.Tendsto (fun x : ℝ => Real.log (2 * x) / Real.log x) Filter.atTop (nhds 1) := by
      constructor;
      · -- We can use the fact that $\log(2x + 1) = \log x + \log(2 + 1/x)$ to simplify the expression.
        suffices h_log_simplified : Filter.Tendsto (fun x : ℝ => (Real.log x + Real.log (2 + 1 / x)) / Real.log x) Filter.atTop (nhds 1) by
          refine h_log_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ show 2 * x + 1 = x * ( 2 + 1 / x ) by nlinarith [ one_div_mul_cancel hx.ne' ] ] ; rw [ Real.log_mul ] <;> positivity );
        ring_nf;
        exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) ) ) ( by norm_num );
      · rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ) ];
        ring_nf;
        exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop ) ) ) ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ) ( by norm_num );
    refine' ⟨ h_log_approx.1.comp _, h_log_approx.2.comp _ ⟩;
    · have := h_k_val_approx;
      have := this.pos_mul_atTop hc ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Function.comp_apply, div_mul_cancel₀ _ ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hx ) ] );
    · have h_k_val_approx : Filter.Tendsto (fun M => (k_val c M : ℝ) / Real.log M) Filter.atTop (nhds c) := by
        convert h_k_val_approx using 1;
      have h_k_val_approx : Filter.Tendsto (fun M => (k_val c M : ℝ) / Real.log M * Real.log M) Filter.atTop Filter.atTop := by
        apply_rules [ Filter.Tendsto.pos_mul_atTop, h_k_val_approx ];
        exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop;
      exact h_k_val_approx.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with M hM using by rw [ div_mul_cancel₀ _ ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hM ) ) ) ] );
  -- Using the fact that $(\log(k_val c M))^2 / \log M$ tends to $0$, we can conclude.
  have h_zero : Filter.Tendsto (fun M => (Real.log (k_val c M))^2 / Real.log M) Filter.atTop (nhds 0) := by
    have h_zero : Filter.Tendsto (fun M => (Real.log (k_val c M))^2 / (k_val c M)) Filter.atTop (nhds 0) := by
      have h_zero : Filter.Tendsto (fun x : ℝ => (Real.log x)^2 / x) Filter.atTop (nhds 0) := by
        -- Let $y = \log x$, therefore the expression becomes $\frac{y^2}{e^y}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => y^2 / Real.exp y) Filter.atTop (nhds 0) by
          have := h_log.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
        simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
      refine h_zero.comp ?_;
      have h_k_val_inf : Filter.Tendsto (fun M => (k_val c M : ℝ) / Real.log M) Filter.atTop (nhds c) := by
        convert h_k_val_approx using 1;
      have := h_k_val_inf.pos_mul_atTop hc ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Function.comp_apply, div_mul_cancel₀ _ ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hx ) ] );
    have := h_zero.mul h_k_val_approx;
    simpa using this.congr' ( by filter_upwards [ h_k_val_approx.eventually_ne hc.ne' ] with M hM using by rw [ div_mul_div_cancel₀ ( by aesop ) ] );
  have := h_log_approx.1.mul h_log_approx.2 |> Filter.Tendsto.mul <| h_zero; simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm, sq ] ;
  refine' this.congr' ( by filter_upwards [ h_log_approx.1.eventually_ne one_ne_zero, h_log_approx.2.eventually_ne one_ne_zero ] with M hM₁ hM₂ using by by_cases h : Real.log ( k_val c M : ℝ ) = 0 <;> aesop )

/-
The upper bound for the sum of term2 tends to 0 as M goes to infinity.
-/
lemma lemma_term2_bound_limit (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun M => (2 * k_val c M + 1 : ℝ) * Real.exp (1 / 16) * (M : ℝ) ^ (- (1 - eta) / (24 * Real.log (2 * k_val c M)))) Filter.atTop (nhds 0) := by
  -- We can factor out $(M : ℝ) ^ (-(1 - eta) / (24 * Real.log (2 * (k_val c M))))$ and use the fact that $\log M / \log (2 * k_val c M) \to \infty$.
  have h_factor : Filter.Tendsto (fun M : ℕ => (2 * (k_val c M) + 1 : ℝ) * (M : ℝ) ^ (-(1 - eta) / (24 * Real.log (2 * (k_val c M))))) Filter.atTop (nhds 0) := by
    -- Taking the logarithm, we need to show that $\log(2k+1) - \frac{(1-\eta)\log M}{24\log(2k)} \to -\infty$ as $M \to \infty$.
    suffices h_log : Filter.Tendsto (fun M : ℕ => Real.log (2 * (k_val c M) + 1) - (1 - eta) * Real.log M / (24 * Real.log (2 * (k_val c M)))) Filter.atTop Filter.atBot by
      have h_exp : Filter.Tendsto (fun M : ℕ => Real.exp (Real.log (2 * (k_val c M) + 1) - (1 - eta) * Real.log M / (24 * Real.log (2 * (k_val c M))))) Filter.atTop (nhds 0) := by
        aesop;
      refine h_exp.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM;
      rw [ Real.exp_sub, Real.exp_log ( by positivity ), Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
      norm_num [ Real.exp_add, Real.exp_neg ] ; ring;
    -- We'll use the fact that $\frac{\log M}{\log(2k)}$ tends to infinity as $M$ tends to infinity.
    have h_log_ratio : Filter.Tendsto (fun M : ℕ => Real.log M / Real.log (2 * (k_val c M))) Filter.atTop Filter.atTop := by
      exact lemma_log_ratio_two_k_val_tendsto_atTop c hc;
    -- We'll use the fact that $\log(2k+1)$ grows slower than $\log M$.
    have h_log_growth : Filter.Tendsto (fun M : ℕ => Real.log (2 * (k_val c M) + 1) / (Real.log M / Real.log (2 * (k_val c M)))) Filter.atTop (nhds 0) := by
      have h_log_growth : Filter.Tendsto (fun M : ℕ => Real.log (2 * (k_val c M) + 1) * Real.log (2 * (k_val c M)) / Real.log M) Filter.atTop (nhds 0) := by
        exact lemma_log_term_small c hc;
      grind;
    have h_final : Filter.Tendsto (fun M : ℕ => (Real.log (2 * (k_val c M) + 1) / (Real.log M / Real.log (2 * (k_val c M)))) - (1 - eta) / 24) Filter.atTop (nhds (0 - (1 - eta) / 24)) := by
      exact h_log_growth.sub tendsto_const_nhds;
    have h_final : Filter.Tendsto (fun M : ℕ => (Real.log (2 * (k_val c M) + 1) / (Real.log M / Real.log (2 * (k_val c M)))) * (Real.log M / Real.log (2 * (k_val c M))) - (1 - eta) / 24 * (Real.log M / Real.log (2 * (k_val c M)))) Filter.atTop Filter.atBot := by
      have h_final : Filter.Tendsto (fun M : ℕ => ((Real.log (2 * (k_val c M) + 1) / (Real.log M / Real.log (2 * (k_val c M)))) - (1 - eta) / 24) * (Real.log M / Real.log (2 * (k_val c M)))) Filter.atTop Filter.atBot := by
        apply_rules [ Filter.Tendsto.neg_mul_atTop ];
        unfold eta; norm_num;
      simpa only [ sub_mul ] using h_final;
    refine h_final.congr' ( by filter_upwards [ h_log_ratio.eventually_ne_atTop 0 ] with M hM using by rw [ div_mul_cancel₀ _ hM ] ; ring );
  convert h_factor.const_mul ( Real.exp ( 1 / 16 ) ) using 2 <;> ring

/-
The sum of the exponential terms tends to 0 as M tends to infinity.
-/
lemma lemma_sum_term2_tendsto_zero (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun M => sum_term2 M c) Filter.atTop (nhds 0) := by
  refine' squeeze_zero_norm' _ _;
  use fun M => ( 2 * k_val c M + 1 : ℝ ) * Real.exp ( 1 / 16 ) * ( M : ℝ ) ^ ( - ( 1 - eta ) / ( 24 * Real.log ( 2 * k_val c M ) ) );
  · filter_upwards [ Filter.eventually_gt_atTop 1 ] with M hM;
    refine' le_trans ( norm_sum_le _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun i hi => _ ) _;
    use fun i => if Nat.Prime i then Real.exp ( 1 / 16 ) * ( M : ℝ ) ^ ( - ( 1 - eta ) / ( 24 * Real.log ( 2 * k_val c M ) ) ) else 0;
    · split_ifs <;> norm_num;
      convert lemma_term2_bound_uniform M c hM i ‹_› hi using 1;
      ring_nf;
    · norm_num [ Finset.sum_ite ];
      rw [ mul_assoc ];
      exact mul_le_mul_of_nonneg_right ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ) ( by positivity );
  · convert lemma_term2_bound_limit c hc using 1

/-
sum_bound_carries is equal to (M+1) times the sum of term1 and term2.
-/
lemma lemma_sum_bound_carries_eq (M : ℕ) (c : ℝ) :
    sum_bound_carries M c = (M + 1 : ℝ) * (sum_term2 M c + sum_term1 M c) := by
      unfold sum_bound_carries sum_term2 sum_term1; simp [ Finset.mul_sum _ _ _, mul_add ]
      simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring;

/-
The total number of bad carries is bounded by sum_bound_carries.
-/
lemma lemma_sum_bad_carries_le_bound (M : ℕ) (c : ℝ) (hM : M > 0) :
    (sum_bad_carries M c : ℝ) ≤ sum_bound_carries M c := by
  have := @lemma_bad_carries_bound;
  norm_num [ sum_bad_carries, sum_bound_carries ];
  gcongr ; aesop

/-
sum_term1 tends to 0 as M tends to infinity.
-/
lemma lemma_sum_term1_tendsto_zero (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun M => sum_term1 M c) Filter.atTop (nhds 0) := by
      refine' squeeze_zero_norm' _ _;
      use fun M => ( 2 * k_val c M + 1 ) * ( 2 / ( M : ℝ ) ^ eta );
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM;
        convert lemma_sum_term1_bound M c hM using 1;
        exact Real.norm_of_nonneg <| Finset.sum_nonneg fun _ _ => by positivity;
      · -- We'll use that $k_val c M \approx c \log M$ to bound the expression.
        have h_k_val : Filter.Tendsto (fun M => (k_val c M : ℝ) / (M : ℝ) ^ eta) Filter.atTop (nhds 0) := by
          have h_k_val : Filter.Tendsto (fun M => (c * Real.log M) / (M : ℝ) ^ eta) Filter.atTop (nhds 0) := by
            -- Let $y = \log M$, therefore the expression becomes $\frac{c y}{e^{y \eta}}$.
            suffices h_log : Filter.Tendsto (fun y => c * y / Real.exp (y * eta)) Filter.atTop (nhds 0) by
              have := h_log.comp Real.tendsto_log_atTop;
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.rpow_def_of_pos hx, mul_comm ] );
            -- Let $z = y \eta$, therefore the expression becomes $\frac{c z}{e^z}$.
            suffices h_z : Filter.Tendsto (fun z => c * z / Real.exp z) Filter.atTop (nhds 0) by
              have := h_z.comp ( Filter.tendsto_id.atTop_mul_const ( show 0 < eta by norm_num [ eta ] ) );
              convert this.div_const eta using 2 <;> norm_num [ eta ] ; ring;
            simpa [ Real.exp_neg, mul_div_assoc ] using tendsto_const_nhds.mul ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
          refine' squeeze_zero_norm' _ ( h_k_val.comp tendsto_natCast_atTop_atTop );
          simp +zetaDelta at *;
          use 2; intro M hM; rw [ abs_of_nonneg ( by positivity ) ] ; gcongr ; exact Nat.floor_le ( by positivity ) ;
        convert h_k_val.const_mul 4 |> Filter.Tendsto.add <| tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( show 0 < eta by norm_num [ eta ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) |> Filter.Tendsto.const_mul 2 using 2 <;> ring_nf;
        norm_num [ Real.rpow_natCast ]

/-
For sufficiently large M, the number of bad carries is less than (M+1)/3.
-/
lemma lemma_sum_bad_carries_small (c : ℝ) (hc : c > 0) :
    ∃ M0, ∀ M ≥ M0, (sum_bad_carries M c : ℝ) < (M + 1 : ℝ) / 3 := by
      -- By combining the results, we conclude that the number of bad carries is less than $(M + 1) / 3$ for sufficiently large $M$.
      obtain ⟨M0, hM0⟩ : ∃ M0 : ℕ, ∀ M ≥ M0, sum_term2 M c + sum_term1 M c < 1 / 3 := by
        simpa using Filter.eventually_atTop.1 ( Filter.Tendsto.eventually ( show Filter.Tendsto ( fun M : ℕ => sum_term2 M c + sum_term1 M c ) Filter.atTop ( nhds 0 ) from by simpa using Filter.Tendsto.add ( lemma_sum_term2_tendsto_zero c hc ) ( lemma_sum_term1_tendsto_zero c hc ) ) ( gt_mem_nhds <| by positivity ) );
      refine' ⟨ M0 + 1, fun M hM => _ ⟩;
      have := lemma_sum_bad_carries_le_bound M c ( by linarith );
      rw [ lemma_sum_bound_carries_eq ] at this;
      nlinarith [ hM0 M ( by linarith ) ]

/-
The total number of bad spikes is bounded by sum_bound_spikes.
-/
lemma lemma_sum_bad_spikes_le_bound (M : ℕ) (c : ℝ) :
    (sum_bad_spikes M c : ℝ) ≤ sum_bound_spikes M c := by
  have h_bad_spikes_bound : ∀ p ∈ Finset.range (2 * k_val c M + 1), p.Prime → (bad_spike_set p M c).card ≤ (k_val c M : ℝ) * ((M : ℝ) / (p : ℝ) ^ (J_p p (k_val c M) + t_val M) + 2) := by
    intros p hp hp_prime
    have h_bad_spikes_bound : (bad_spike_set p M c).card ≤ k_val c M * (M / p ^ (J_p p (k_val c M) + t_val M) + 2) := by
      apply lemma_spike_count_bound p M (k_val c M) (t_val M) hp_prime (by
      contrapose! hp; aesop);
    refine' le_trans ( Nat.cast_le.mpr h_bad_spikes_bound ) _;
    norm_num [ mul_add ];
    exact mul_le_mul_of_nonneg_left ( by rw [ le_div_iff₀ ( pow_pos ( Nat.cast_pos.mpr hp_prime.pos ) _ ) ] ; norm_cast; linarith [ Nat.div_mul_le_self M ( p ^ ( J_p p ( k_val c M ) + t_val M ) ) ] ) ( Nat.cast_nonneg _ );
  push_cast [ sum_bad_spikes, sum_bound_spikes ];
  gcongr ; aesop

/-
Definitions of the two parts of the upper bound for the sum of bad spike counts.
-/
noncomputable def sum_spike_term1 (M : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (2 * k_val c M + 1), if p.Prime then 2 * (k_val c M : ℝ) else 0

noncomputable def sum_spike_term2 (M : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (2 * k_val c M + 1),
    if p.Prime then (k_val c M : ℝ) * (M : ℝ) / (p : ℝ) ^ (J_p p (k_val c M) + t_val M) else 0

/-
sum_spike_term1 is bounded by approximately 4k^2.
-/
lemma lemma_sum_spike_term1_bound (M : ℕ) (c : ℝ) :
    sum_spike_term1 M c ≤ (2 * k_val c M + 1 : ℝ) * (2 * k_val c M : ℝ) := by
      refine' le_trans ( Finset.sum_le_sum fun i hi => _ ) _;
      exacts [ fun _ => 2 * k_val c M, by split_ifs <;> norm_num, by norm_num [ mul_comm ] ]

/-
sum_spike_term1 / M tends to 0 as M tends to infinity.
-/
lemma lemma_sum_spike_term1_div_M_tendsto_zero (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun M : ℕ => sum_spike_term1 M c / (M : ℝ)) Filter.atTop (nhds 0) := by
  have h_term1_bound : ∀ M : ℕ, sum_spike_term1 M c ≤ 8 * c^2 * (Real.log M)^2 + 4 * c * Real.log M + 1 := by
    intro M;
    exact le_trans ( lemma_sum_spike_term1_bound M c ) ( by nlinarith [ show ( k_val c M : ℝ ) ≤ c * Real.log M by exact Nat.floor_le ( mul_nonneg hc.le ( Real.log_natCast_nonneg M ) ) ] );
  -- We'll use the fact that $\frac{(\log M)^2}{M}$ tends to $0$ as $M$ tends to infinity.
  have h_log_sq_div_M : Filter.Tendsto (fun M : ℕ => (Real.log M)^2 / (M : ℝ)) Filter.atTop (nhds 0) := by
    -- Let $y = \log x$, therefore the expression becomes $\frac{y^2}{e^y}$.
    suffices h_log_sq_div_exp : Filter.Tendsto (fun y : ℝ => y^2 / Real.exp y) Filter.atTop (nhds 0) by
      have := h_log_sq_div_exp.comp Real.tendsto_log_atTop;
      exact this.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.exp_log ( Nat.cast_pos.mpr hx ) ] );
    simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
  -- We'll use the fact that $\frac{\log M}{M}$ tends to $0$ as $M$ tends to infinity.
  have h_log_div_M : Filter.Tendsto (fun M : ℕ => Real.log M / (M : ℝ)) Filter.atTop (nhds 0) := by
    refine' squeeze_zero_norm' _ h_log_sq_div_M;
    norm_num +zetaDelta at *;
    exact ⟨ 3, fun n hn => by rw [ abs_of_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ] ; exact div_le_div_of_nonneg_right ( by nlinarith [ show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ] ) ( by positivity ) ⟩;
  -- Using the bounds from h_term1_bound, we can show that the limit of the sum is 0.
  have h_sum_term1_limit : Filter.Tendsto (fun M : ℕ => (8 * c^2 * (Real.log M)^2 + 4 * c * Real.log M + 1) / (M : ℝ)) Filter.atTop (nhds 0) := by
    simpa [ add_div, mul_div_assoc ] using Filter.Tendsto.add ( Filter.Tendsto.add ( h_log_sq_div_M.const_mul _ ) ( h_log_div_M.const_mul _ ) ) ( tendsto_inverse_atTop_nhds_zero_nat );
  exact squeeze_zero ( fun M => div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Nat.cast_nonneg _ ) ) ( fun M => div_le_div_of_nonneg_right ( h_term1_bound M ) ( Nat.cast_nonneg _ ) ) h_sum_term1_limit

/-
sum_bound_spikes is the sum of sum_spike_term2 and sum_spike_term1.
-/
lemma lemma_sum_bound_spikes_eq (M : ℕ) (c : ℝ) :
    sum_bound_spikes M c = sum_spike_term2 M c + sum_spike_term1 M c := by
  unfold sum_bound_spikes sum_spike_term2 sum_spike_term1;
  simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x hx => by split_ifs <;> ring;

/-
Bound for the term in the spike sum.
-/
lemma lemma_spike_term_bound (p k t : ℕ) (hp : p.Prime) :
    (k : ℝ) / (p : ℝ) ^ (J_p p k + t) ≤ (p : ℝ) / (p : ℝ) ^ t := by
  rw [ div_le_div_iff₀ ] <;> try norm_cast ; exact pow_pos hp.pos _;
  rw_mod_cast [ mul_comm ];
  rw [ mul_comm, ← pow_succ' ];
  rw [ pow_add, pow_add ];
  have := Nat.lt_pow_succ_log_self hp.one_lt k;
  rw [ mul_right_comm ];
  exact Nat.mul_le_mul_right _ ( by simpa [ Nat.log_pow hp.one_lt ] using this.le )

/-
Definition of the sum of p/p^t over primes.
-/
noncomputable def sum_p_div_pow_t (M : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (2 * k_val c M + 1), if p.Prime then (p : ℝ) / (p : ℝ) ^ (t_val M) else 0

/-
The sum of p/p^t tends to 0 as M tends to infinity.
-/
lemma lemma_sum_p_div_pow_t_tendsto_zero (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun M => sum_p_div_pow_t M c) Filter.atTop (nhds 0) := by
      have h_sum_p_div_pow_t_zero : Filter.Tendsto (fun M => (2 * k_val c M + 1 : ℝ) / (2 ^ (t_val M - 1))) Filter.atTop (nhds 0) := by
        -- Since $t_val M \geq 10 \log \log M$, we have $2^{t_val M - 1} \geq 2^{10 \log \log M - 1} = (\log M)^{10 \log 2} / 2$.
        have h_exp_bound : ∀ M ≥ 3, (2 : ℝ) ^ (t_val M - 1) ≥ (Real.log M) ^ (10 * Real.log 2) / 2 := by
          -- Since $t_val M \geq 10 \log \log M$, we have $2^{t_val M - 1} \geq 2^{10 \log \log M - 1}$.
          have h_exp_bound : ∀ M ≥ 3, (2 : ℝ) ^ (t_val M - 1) ≥ (2 : ℝ) ^ (10 * Real.log (Real.log M) - 1) := by
            field_simp;
            intro M hM; rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_pow ];
            rw [ Nat.cast_sub ] <;> norm_num [ t_val ];
            · rw [ Real.log_rpow ( by positivity ) ] ; nlinarith [ Nat.le_ceil ( 10 * Real.log ( Real.log M ) ), Real.log_pos one_lt_two ];
            · exact Real.log_pos <| by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( M : ℝ ) ≥ 3 by norm_cast ] ;
          intro M hM; convert h_exp_bound M hM using 1; rw [ Real.rpow_sub ] <;> norm_num ; ring_nf;
          norm_num [ Real.rpow_def_of_pos, Real.log_pos ( show ( M : ℝ ) > 1 by norm_cast; linarith ) ] ; ring;
        -- Using the bound on $2^{t_val M - 1}$, we can show that the expression tends to 0.
        have h_tendsto_zero : Filter.Tendsto (fun M : ℕ => (2 * (c * Real.log M) + 1) / ((Real.log M) ^ (10 * Real.log 2) / 2)) Filter.atTop (nhds 0) := by
          -- We can factor out $(Real.log M)^{-1}$ and use the fact that $Real.log M$ grows to infinity.
          have h_factor : Filter.Tendsto (fun M : ℕ => (2 * c + 1 / Real.log M) / (Real.log M ^ (10 * Real.log 2 - 1) / 2)) Filter.atTop (nhds 0) := by
            exact le_trans ( Filter.Tendsto.div_atTop ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) <| Filter.Tendsto.atTop_div_const ( by positivity ) <| tendsto_rpow_atTop ( by have := Real.log_two_gt_d9; norm_num1 at *; linarith ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) <| by norm_num;
          refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with M hM using by rw [ Real.rpow_sub ( Real.log_pos <| Nat.one_lt_cast.mpr hM ) ] ; norm_num ; ring_nf ; norm_num [ ne_of_gt, Real.log_pos <| Nat.one_lt_cast.mpr hM ] );
        refine' squeeze_zero_norm' _ h_tendsto_zero;
        filter_upwards [ Filter.eventually_ge_atTop 3 ] with M hM using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div₀ ( by positivity ) ( by exact add_le_add ( mul_le_mul_of_nonneg_left ( Nat.floor_le ( by positivity ) ) zero_le_two ) le_rfl ) ( by exact div_pos ( Real.rpow_pos_of_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) _ ) zero_lt_two ) ( by exact h_exp_bound M hM ) ;
      refine' squeeze_zero_norm' _ h_sum_p_div_pow_t_zero;
      refine' Filter.eventually_atTop.mpr ⟨ 3, fun M hM => _ ⟩ ; rw [ Real.norm_of_nonneg ];
      · -- Each term in the sum is p/p^t = 1/p^(t-1), and since p ≥ 2, 1/p^(t-1) ≤ 1/2^(t-1).
        have h_term_bound : ∀ p ∈ Finset.range (2 * k_val c M + 1), p.Prime → (p : ℝ) / (p : ℝ) ^ (t_val M) ≤ 1 / (2 : ℝ) ^ (t_val M - 1) := by
          intro p hp hp_prime; rcases t : t_val M with ( _ | t ) <;> simp_all +decide [ pow_succ, div_eq_mul_inv ] ;
          · unfold t_val at t;
            norm_num at t;
            exact False.elim <| t.not_gt <| mul_pos ( by norm_num ) <| Real.log_pos <| show 1 < Real.log M from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( M : ℝ ) ≥ 3 by norm_cast ] ;
          · rw [ ← mul_assoc, mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr hp_prime.ne_zero ), one_mul ] ; gcongr ; norm_cast ; linarith [ hp_prime.two_le ];
        refine' le_trans ( Finset.sum_le_sum fun p hp => _ ) _;
        use fun p => if Nat.Prime p then 1 / 2 ^ ( t_val M - 1 ) else 0;
        · aesop;
        · norm_num [ Finset.sum_ite ];
          exact mul_le_mul_of_nonneg_right ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ) ( by positivity );
      · exact Finset.sum_nonneg fun _ _ => by positivity;

/-
sum_spike_term2 is bounded by M times sum_p_div_pow_t.
-/
lemma lemma_sum_spike_term2_bound (M : ℕ) (c : ℝ) :
    sum_spike_term2 M c ≤ (M : ℝ) * sum_p_div_pow_t M c := by
  norm_num [ sum_spike_term2, sum_p_div_pow_t ];
  rw [ Finset.mul_sum _ _ _ ];
  gcongr;
  -- Since $i$ is prime, we have $i^{J_p i (k_val c M) + t_val M} = i^{J_p i (k_val c M)} \cdot i^{t_val M}$.
  have h_prime : ∀ i : ℕ, Nat.Prime i → (k_val c M : ℝ) / (i : ℝ) ^ (J_p i (k_val c M) + t_val M) ≤ (i : ℝ) / (i : ℝ) ^ t_val M := by
    exact fun i a => lemma_spike_term_bound i (k_val c M) (t_val M) a;
  split_ifs <;> simp_all +decide [ div_eq_mul_inv, mul_comm, mul_left_comm ];
  convert mul_le_mul_of_nonneg_left ( h_prime _ ‹_› ) ( Nat.cast_nonneg M ) using 1

/-
sum_spike_term2 / M tends to 0 as M tends to infinity.
-/
lemma lemma_sum_spike_term2_div_M_tendsto_zero (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun M : ℕ => sum_spike_term2 M c / (M : ℝ)) Filter.atTop (nhds 0) := by
      -- We'll use the fact that if the denominator grows faster than the numerator, the limit will tend to zero.
      have h_lim : Filter.Tendsto (fun M : ℕ => (M : ℝ) * sum_p_div_pow_t M c / M) Filter.atTop (nhds 0) := by
        exact Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM using by rw [ mul_div_cancel_left₀ _ ( by positivity ) ] ) ( lemma_sum_p_div_pow_t_tendsto_zero c hc );
      refine' squeeze_zero_norm' _ h_lim;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM ; rw [ Real.norm_of_nonneg ( by exact div_nonneg ( by exact Finset.sum_nonneg fun _ _ => by positivity ) ( Nat.cast_nonneg _ ) ) ] ; exact div_le_div_of_nonneg_right ( by exact le_trans ( by aesop ) ( lemma_sum_spike_term2_bound M c ) ) ( Nat.cast_nonneg _ )

/-
For sufficiently large M, sum_bound_spikes is less than (M+1)/3.
-/
lemma lemma_sum_bound_spikes_small (c : ℝ) (hc : c > 0) :
    ∃ M0, ∀ M ≥ M0, (sum_bound_spikes M c : ℝ) < (M + 1 : ℝ) / 3 := by
      -- By definition of sum_bound_spikes, we know that it tends to 0 as M tends to infinity.
      have h_tendsto_zero : Filter.Tendsto (fun M => sum_bound_spikes M c / (M + 1 : ℝ)) Filter.atTop (nhds 0) := by
        have h_tendsto_zero : Filter.Tendsto (fun M => (sum_spike_term2 M c + sum_spike_term1 M c) / (M + 1 : ℝ)) Filter.atTop (nhds 0) := by
          have h_sum_div_M_tendsto_zero : Filter.Tendsto (fun M : ℕ => (sum_spike_term2 M c + sum_spike_term1 M c) / (M : ℝ)) Filter.atTop (nhds 0) := by
            simpa [ add_div ] using Filter.Tendsto.add ( lemma_sum_spike_term2_div_M_tendsto_zero c hc ) ( lemma_sum_spike_term1_div_M_tendsto_zero c hc );
          have h_sum_div_M_tendsto_zero : Filter.Tendsto (fun M : ℕ => ((sum_spike_term2 M c + sum_spike_term1 M c) / (M : ℝ)) * (M / (M + 1 : ℝ))) Filter.atTop (nhds 0) := by
            simpa using h_sum_div_M_tendsto_zero.mul ( tendsto_natCast_div_add_atTop 1 );
          refine h_sum_div_M_tendsto_zero.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM using by rw [ div_mul_div_cancel₀ ( by positivity ) ] );
        simpa only [ ← lemma_sum_bound_spikes_eq ] using h_tendsto_zero;
      have := h_tendsto_zero.eventually ( gt_mem_nhds <| show 0 < 1 / 3 by norm_num );
      exact Filter.eventually_atTop.mp this |> fun ⟨ M0, hM0 ⟩ ↦ ⟨ M0, fun M hM ↦ by have := hM0 M hM; rw [ div_lt_iff₀ ( by positivity ) ] at this; linarith ⟩

/-
For sufficiently large M, k_val(c, M) is at most (1 - 2*epsilon) * M.
-/
lemma lemma_k_val_upper_bound_eventually (c ε : ℝ) (hε : ε < 1 / 2) :
    ∃ M0, ∀ M ≥ M0, (k_val c M : ℝ) ≤ (1 - 2 * ε) * M := by
      -- Since $\frac{\log M}{M} \to 0$ as $M \to \infty$, we can choose $M_0$ such that for all $M \geq M_0$, $\frac{\log M}{M} < \frac{1 - 2\epsilon}{c}$.
      have h_log_div_M_zero : Filter.Tendsto (fun M : ℕ => Real.log M / (M : ℝ)) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$ so we can rewrite the limit expression as $\lim_{y \to 0^+} y \ln(1/y)$.
        suffices h_change_var : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_change_var.comp ( Filter.map_mono tendsto_natCast_atTop_atTop ) |> fun h => h.congr ( by intros; simp +decide ; ring );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
      field_simp;
      by_cases hc : c > 0;
      · -- Since $c > 0$, we can choose $M_0$ such that for all $M \geq M_0$, $c * \frac{\log M}{M} < 1 - 2\epsilon$.
        obtain ⟨M0, hM0⟩ : ∃ M0 : ℕ, ∀ M ≥ M0, c * (Real.log M / (M : ℝ)) < 1 - 2 * ε := by
          simpa using h_log_div_M_zero.const_mul c |> fun h => h.eventually ( gt_mem_nhds <| by linarith );
        exact ⟨ M0 + 1, fun M hM => by have := hM0 M ( by linarith ) ; rw [ mul_div, div_lt_iff₀ ( by norm_cast; linarith ) ] at this; exact le_trans ( Nat.floor_le ( by positivity ) ) this.le ⟩;
      · exact ⟨ 1, fun M hM => by rw [ show k_val c M = 0 by exact Nat.floor_eq_zero.mpr ( by nlinarith [ Real.log_nonneg ( show ( M : ℝ ) ≥ 1 by norm_cast ) ] ) ] ; norm_num; nlinarith [ show ( M : ℝ ) ≥ 1 by norm_cast ] ⟩

/-
For sufficiently large M, k_val(c, M) is strictly greater than C * log(4M).
-/
lemma lemma_k_val_lower_bound_eventually (c C : ℝ) (hc : c > C) :
    ∃ M0, ∀ M ≥ M0, (k_val c M : ℝ) > C * Real.log (4 * M) := by
      -- Since $c > C$, we can choose $M0$ such that for all $M \geq M0$, $(c - C) \log M > C \log 4 + 1$.
      obtain ⟨M0, hM0⟩ : ∃ M0 : ℕ, ∀ M ≥ M0, (c - C) * Real.log M > C * Real.log 4 + 1 := by
        have h_log_ratio : Filter.Tendsto (fun M : ℕ => Real.log M) Filter.atTop Filter.atTop := by
          exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop;
        exact Filter.eventually_atTop.mp ( h_log_ratio.eventually_gt_atTop ( ( C * Real.log 4 + 1 ) / ( c - C ) ) ) |> fun ⟨ M0, hM0 ⟩ ↦ ⟨ M0, fun M hM ↦ by nlinarith [ hM0 M hM, mul_div_cancel₀ ( C * Real.log 4 + 1 ) ( sub_ne_zero_of_ne hc.ne' ) ] ⟩;
      -- Using the fact that $k_val(c, M) = \lfloor c \log M \rfloor$, we can rewrite the inequality.
      have h_k_val_rewrite : ∀ M ≥ M0, k_val c M ≥ c * Real.log M - 1 := by
        exact fun M hM => Nat.sub_one_lt_floor _ |> le_of_lt;
      refine' ⟨ M0 + 2, fun M hM => _ ⟩ ; specialize hM0 M ( by linarith ) ; specialize h_k_val_rewrite M ( by linarith ) ; rw [ Real.log_mul ( by linarith ) ( by norm_cast; linarith ) ] at * ; nlinarith [ Real.log_pos ( show ( 4 : ℝ ) > 1 by norm_num ), Real.log_pos ( show ( M : ℝ ) > 1 by norm_cast; linarith ) ] ;

/-
The valuation condition for the improved reduction.
-/
lemma lemma_val_reduction (p m k : ℕ) (hp : p.Prime) :
    padicValNat p (Nat.choose (m + k) k) ≤ kappa p m ↔
    W p m k ≤ kappa p m + padicValNat p (Nat.factorial k) := by
  unfold W;
  rw [ Nat.descFactorial_eq_factorial_mul_choose ];
  haveI := Fact.mk hp; rw [ padicValNat.mul ( by positivity ) ( by exact Nat.ne_of_gt ( Nat.choose_pos ( by linarith ) ) ) ] ; ring_nf; norm_num;

/-
Sufficient conditions for the divisibility for all primes.
-/
lemma lemma_sufficient_conditions_updated (M : ℕ) (c : ℝ) (m : ℕ)
    (h_small_p : ∀ p ∈ Finset.range (2 * k_val c M + 1), p.Prime → p ≤ 2 * k_val c M →
      W p m (k_val c M) ≤ kappa p m + padicValNat p (Nat.factorial (k_val c M))) :
    ∀ p, p.Prime → padicValNat p (Nat.choose (m + k_val c M) (k_val c M)) ≤ kappa p m := by
      intro p hp;
      -- By definition of $W$ and $\kappa$, we know that $padicValNat p (Nat.choose (m + k) k) ≤ kappa p m$ if and only if $W p m k ≤ kappa p m + padicValNat p (Nat.factorial k)$.
      apply (lemma_val_reduction p m (k_val c M) hp).mpr;
      by_cases hp_le : p ≤ 2 * k_val c M;
      · exact h_small_p p ( Finset.mem_range.mpr ( by linarith ) ) hp hp_le;
      · exact le_add_of_le_of_nonneg ( lemma_p_gt_2k m ( k_val c M ) p hp ( by linarith ) ) ( Nat.zero_le _ )

/-
Lower bound for mu/2.
-/
lemma lemma_mu_ge (p M : ℕ) (hp : p.Prime) :
    (mu p (L_p p M)) / 2 ≥ (1 - eta) / 2 * theta p * (Real.log M / Real.log p) - theta p / 2 := by
  have := @lemma_mu_lower_bound p M hp;
  convert this using 1 ; unfold coeff_lhs ; ring

/-
The main inequality holds asymptotically.
-/
lemma lemma_main_ineq_asymptotic (c : ℝ) (hc : c > 0) :
    Filter.Tendsto (fun M : ℕ =>
      (1 - eta) / 6 * Real.log M -
      (Real.log (k_val c M) + (4 + 10 * Real.log (Real.log M)) * Real.log (2 * k_val c M + 1) + 1/2 * Real.log (2 * k_val c M + 1)))
    Filter.atTop Filter.atTop := by
      -- We'll use that $Real.log (k_val c M) ≤ Real.log c + Real.log (Real.log M)$ and $Real.log (2 * (k_val c M) + 1) ≤ Real.log (2 * k_val c M + 1)$.
      suffices h_simplified : Filter.Tendsto (fun M : ℕ => (1 - eta) / 6 * Real.log M - ((Real.log c + Real.log (Real.log M)) + (4 + 10 * Real.log (Real.log M)) * (Real.log c + Real.log (Real.log M) + Real.log 3) + 1 / 2 * (Real.log c + Real.log (Real.log M) + Real.log 3))) Filter.atTop Filter.atTop by
        -- Since $\log(k_val c M) \leq \log c + \log(\log M)$ and $\log(2 * k_val c M + 1) \leq \log c + \log(\log M) + \log 3$, we can bound the terms involving $k_val c M$.
        have h_log_bound : ∀ᶠ M in Filter.atTop, Real.log (k_val c M) ≤ Real.log c + Real.log (Real.log M) ∧ Real.log (2 * (k_val c M) + 1) ≤ Real.log c + Real.log (Real.log M) + Real.log 3 := by
          have h_log_bound : ∀ᶠ M in Filter.atTop, Real.log (k_val c M) ≤ Real.log c + Real.log (Real.log M) := by
            have h_log_bound : ∀ᶠ M in Filter.atTop, k_val c M > 0 := by
              have h_log_bound : Filter.Tendsto (fun M : ℕ => k_val c M) Filter.atTop Filter.atTop := by
                exact tendsto_nat_floor_atTop.comp ( Filter.Tendsto.const_mul_atTop hc <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
              exact h_log_bound.eventually_gt_atTop 0;
            filter_upwards [ h_log_bound, Filter.eventually_gt_atTop 1 ] with M hM₁ hM₂;
            rw [ ← Real.log_mul ( by positivity ) ( by exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hM₂ ) ] ; exact Real.log_le_log ( by positivity ) <| by have := Nat.floor_le <| show 0 ≤ c * Real.log M by positivity; ; nlinarith [ show ( k_val c M : ℝ ) ≤ c * Real.log M by exact_mod_cast this, Real.log_pos <| show ( M : ℝ ) > 1 by norm_cast ] ;
          have h_log_bound2 : ∀ᶠ M in Filter.atTop, Real.log (2 * (k_val c M) + 1) ≤ Real.log (k_val c M) + Real.log 3 := by
            have h_log_bound2 : ∀ᶠ M in Filter.atTop, 2 * (k_val c M) + 1 ≤ k_val c M * 3 := by
              have h_log_bound2 : ∀ᶠ M in Filter.atTop, k_val c M ≥ 1 := by
                have h_log_bound : Filter.Tendsto (fun M : ℕ => c * Real.log M) Filter.atTop Filter.atTop := by
                  exact Filter.Tendsto.const_mul_atTop hc ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
                filter_upwards [ h_log_bound.eventually_gt_atTop 1 ] with M hM using Nat.floor_pos.mpr hM.le;
              filter_upwards [ h_log_bound2 ] with M hM using by linarith;
            filter_upwards [ h_log_bound2, Filter.eventually_gt_atTop 0 ] with M hM₁ hM₂;
            rw [ ← Real.log_mul ( by norm_cast; linarith ) ( by norm_num ) ] ; exact Real.log_le_log ( by positivity ) ( by norm_cast );
          filter_upwards [ h_log_bound, h_log_bound2 ] with M hM₁ hM₂ using ⟨ hM₁, by linarith ⟩;
        refine' Filter.tendsto_atTop_mono' _ _ h_simplified;
        filter_upwards [ h_log_bound, Filter.eventually_gt_atTop ⌈Real.exp 1⌉₊ ] with M hM₁ hM₂;
        gcongr <;> nlinarith [ Real.log_nonneg ( show ( 1 :ℝ ) ≤ Real.log M by exact Real.le_log_iff_exp_le ( Nat.cast_pos.mpr <| pos_of_gt hM₂ ) |>.2 <| by exact le_trans ( Nat.le_ceil _ ) <| mod_cast hM₂.le ) ];
      -- Let $u = \log \log M$. Then as $M \to \infty$, $u \to \infty$.
      suffices h_u : Filter.Tendsto (fun u : ℝ => (1 - eta) / 6 * Real.exp u - (Real.log c + u + (4 + 10 * u) * (Real.log c + u + Real.log 3) + 1 / 2 * (Real.log c + u + Real.log 3))) Filter.atTop Filter.atTop by
        have := h_u.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) );
        exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by simp +decide [ Real.exp_log ( Real.log_pos <| Nat.one_lt_cast.mpr hx ) ] );
      -- We'll use the fact that $Real.exp u$ grows much faster than any polynomial in $u$.
      have h_exp_growth : Filter.Tendsto (fun u => Real.exp u / u^2) Filter.atTop Filter.atTop := by
        exact Real.tendsto_exp_div_pow_atTop 2;
      -- We can factor out $u^2$ from the denominator and use the fact that $Real.exp u$ grows much faster than any polynomial in $u$.
      have h_factor : Filter.Tendsto (fun u => u^2 * ((1 - eta) / 6 * (Real.exp u / u^2) - (Real.log c / u^2 + 1 / u + (4 / u + 10) * (Real.log c / u + 1 + Real.log 3 / u) + 1 / 2 * (Real.log c / u^2 + 1 / u + Real.log 3 / u^2)))) Filter.atTop Filter.atTop := by
        -- We'll use the fact that $Real.exp u / u^2$ tends to infinity and the other terms tend to zero.
        have h_tendsto_zero : Filter.Tendsto (fun u => Real.log c / u^2 + 1 / u + (4 / u + 10) * (Real.log c / u + 1 + Real.log 3 / u) + 1 / 2 * (Real.log c / u^2 + 1 / u + Real.log 3 / u^2)) Filter.atTop (nhds (10)) := by
          exact le_trans ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop ( by norm_num ) ) ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) tendsto_const_nhds ) ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) tendsto_const_nhds ) ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ) ) ( Filter.Tendsto.mul tendsto_const_nhds ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop ( by norm_num ) ) ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ( tendsto_const_nhds.div_atTop ( by norm_num ) ) ) ) ) ( by norm_num );
        apply Filter.Tendsto.atTop_mul_atTop₀;
        · exact Filter.tendsto_pow_atTop ( by norm_num );
        · exact Filter.Tendsto.atTop_add ( Filter.Tendsto.const_mul_atTop ( by norm_num [ eta ] ) h_exp_growth ) ( h_tendsto_zero.neg );
      refine h_factor.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with u hu;
      grind

/-
If the third component of triples in a set is unbounded, the set is infinite. Also defining the weak RHS expression for the threshold inequality.
-/
lemma infinite_of_unbounded_n (S : Set (ℕ × ℕ × ℕ)) (h : ∀ N, ∃ t ∈ S, t.2.2 ≥ N) :
    S.Infinite := by
  intro H;
  contrapose! h;
  exact ⟨ H.bddAbove.choose.2.2 + 1, fun x hx => Nat.lt_succ_of_le ( H.bddAbove.choose_spec hx |>.2.2 ) ⟩

noncomputable def rhs_expression_weak (p : ℕ) (c : ℝ) (M : ℕ) : ℝ :=
  Real.log (k_val c M) / Real.log p + 2 + t_val M

lemma lemma_t_val_bound (M : ℕ) (hM : M ≥ 3) : (t_val M : ℝ) ≤ 10 * Real.log (Real.log M) + 1 := by
  -- By definition of t_val, we have t_val M = Nat.ceil (10 * Real.log (Real.log M)).
  have h_t_val_def : t_val M = Nat.ceil (10 * Real.log (Real.log M)) := by
    rfl;
  exact h_t_val_def ▸ Nat.ceil_lt_add_one ( mul_nonneg ( by norm_num ) ( Real.log_nonneg ( Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( M : ℝ ) ≥ 3 by norm_cast ] ) ) ) ) ) |> le_of_lt

lemma lemma_threshold_reduction (c : ℝ) (M p : ℕ) (hp : p.Prime)
    (hp_bound : p ≤ 2 * k_val c M + 1)
    (hM : M ≥ 3)
    (h_ineq : (1 - eta) / 6 * Real.log M - (Real.log (k_val c M) + (4 + 10 * Real.log (Real.log M)) * Real.log (2 * k_val c M + 1) + 1/2 * Real.log (2 * k_val c M + 1)) ≥ 0) :
    (mu p (L_p p M)) / 2 ≥ rhs_expression_weak p c M := by
      -- By combining the results from the previous steps, we conclude the proof.
      have h_combined : (1 - eta) / 2 * theta p * (Real.log M / Real.log p) - theta p / 2 ≥ Real.log (k_val c M) / Real.log p + 2 + t_val M := by
        -- Substitute the bounds for `theta p` and `log p` into the inequality.
        have h_substituted : (1 - eta) / 6 * Real.log M - (theta p / 2) * Real.log p ≥ Real.log (k_val c M) + (2 + t_val M + theta p / 2) * Real.log p := by
          have h_substituted : (1 - eta) / 6 * Real.log M ≥ Real.log (k_val c M) + (2 + t_val M + 1 / 2) * Real.log (2 * k_val c M + 1) := by
            have h_substituted : t_val M ≤ 10 * Real.log (Real.log M) + 1 := by
              exact lemma_t_val_bound M hM;
            nlinarith [ Real.log_nonneg ( show ( 2 * k_val c M + 1 : ℝ ) ≥ 1 by linarith ) ];
          -- Since $p \leq 2k_val c M + 1$, we have $\log p \leq \log (2k_val c M + 1)$.
          have h_log_p_le_log_2k_val : Real.log p ≤ Real.log (2 * k_val c M + 1) := by
            exact Real.log_le_log ( Nat.cast_pos.mpr hp.pos ) ( mod_cast hp_bound );
          -- Since $\theta p \leq 1/2$, we have $\theta p / 2 \leq 1/4$.
          have h_theta_p_le_half : theta p / 2 ≤ 1 / 4 := by
            unfold theta; split_ifs <;> norm_num;
            rw [ div_div, div_le_iff₀ ] <;> linarith [ show ( p : ℝ ) ≥ 3 by norm_cast; exact lt_of_le_of_ne hp.two_le ( Ne.symm ‹_› ) ];
          nlinarith [ Real.log_nonneg ( show ( p : ℝ ) ≥ 1 by norm_cast; exact hp.pos ), Real.log_nonneg ( show ( 2 * k_val c M + 1 : ℝ ) ≥ 1 by linarith ) ];
        -- Since `theta p ≥ 1/3`, we can replace `theta p` with `1/3` in the inequality.
        have h_theta_ge_third : theta p ≥ 1 / 3 := by
          field_simp;
          rw [ show theta p = if p = 2 then 1 / 2 else ( p - 1 : ℝ ) / ( 2 * p ) by rfl ] ; split_ifs <;> norm_num;
          rw [ mul_div, le_div_iff₀ ] <;> nlinarith only [ show ( p : ℝ ) ≥ 3 by norm_cast; exact lt_of_le_of_ne hp.two_le ( Ne.symm ‹_› ) ];
        have h_final : (1 - eta) / 2 * theta p * (Real.log M / Real.log p) - theta p / 2 ≥ (1 - eta) / 6 * Real.log M / Real.log p - theta p / 2 := by
          ring_nf at *; nlinarith [ show 0 ≤ ( 1 - eta ) * Real.log M * ( Real.log p ) ⁻¹ by exact mul_nonneg ( mul_nonneg ( by norm_num [ eta ] ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr hp.pos ) ) ) ] ;
        simp +zetaDelta at *;
        rw [ div_add', div_add', div_le_iff₀ ] at * <;> nlinarith [ Real.log_pos <| show ( p :ℝ ) > 1 by exact_mod_cast hp.one_lt, Real.log_pos <| show ( M :ℝ ) > 1 by exact_mod_cast by linarith ];
      exact le_trans h_combined <| lemma_mu_ge p M hp

/-
For sufficiently large M, the expected number of carries mu/2 is greater than the weak threshold for all relevant primes.
-/
lemma lemma_threshold_weak_uniform (c : ℝ) (hc : c > 0) :
    ∃ M0, ∀ M ≥ M0, ∀ p ∈ Finset.range (2 * k_val c M + 1), p.Prime →
      (mu p (L_p p M)) / 2 ≥ rhs_expression_weak p c M := by
  obtain ⟨ M0, hM0 ⟩ := Filter.eventually_atTop.mp ( lemma_main_ineq_asymptotic c hc |> fun h => h.eventually_ge_atTop 0 );
  use M0 + 3;
  intro M hM p hp hp_prime;
  apply_rules [ lemma_threshold_reduction ];
  · linarith [ Finset.mem_range.mp hp ];
  · linarith;
  · linarith

/-
If m is not bad, then for small primes, the valuation condition holds.
-/
lemma lemma_small_primes_good (c : ℝ) (M m : ℕ)
    (hM_large_threshold : ∀ p ∈ Finset.range (2 * k_val c M + 1), p.Prime →
      (mu p (L_p p M)) / 2 ≥ rhs_expression_weak p c M)
    (hm_mem : m ∈ Finset.Icc M (2 * M))
    (hm_not_bad : m ∉ bad_m_set M c) :
    ∀ p ∈ Finset.range (2 * k_val c M + 1), p.Prime → p ≤ 2 * k_val c M →
      W p m (k_val c M) ≤ kappa p m + padicValNat p (Nat.factorial (k_val c M)) := by
  intro p hp_range hp_prime hp_le
  have h_carries : X_p p m (L_p p M) ≥ (mu p (L_p p M)) / 2 := by
    contrapose! hm_not_bad;
    unfold bad_m_set;
    grind;
  -- Since $X_p(m) \geq \frac{\mu(m)}{2}$, we have $\kappa_p(m) \geq \frac{\mu(m)}{2}$.
  have h_kappa_ge_mu : kappa p m ≥ (mu p (L_p p M)) / 2 := by
    refine le_trans h_carries ?_;
    exact_mod_cast lemma_forced_carries_smallp p m ( L_p p M ) hp_prime;
  have h_w_le_kappa : W p m (k_val c M) ≤ (padicValNat p (Nat.factorial (k_val c M))) + (V_p p m (k_val c M)) := by
    have h_w_le_kappa : W p m (k_val c M) ≤ ∑ j ∈ Finset.Icc 1 (V_p p m (k_val c M)), N_pj p m (k_val c M) j := by
      rw [ ← lemma_W_eq_sum_N_pj p m ( k_val c M ) hp_prime ];
    have h_w_le_kappa : ∑ j ∈ Finset.Icc 1 (V_p p m (k_val c M)), N_pj p m (k_val c M) j ≤ ∑ j ∈ Finset.Icc 1 (V_p p m (k_val c M)), Nat.ceil ((k_val c M : ℝ) / (p ^ j : ℝ)) := by
      exact Finset.sum_le_sum fun j hj => lemma_N_pj_le_ceil p m ( k_val c M ) j hp_prime;
    have h_w_le_kappa : ∑ j ∈ Finset.Icc 1 (V_p p m (k_val c M)), Nat.ceil ((k_val c M : ℝ) / (p ^ j : ℝ)) ≤ ∑ j ∈ Finset.Icc 1 (V_p p m (k_val c M)), (Nat.floor ((k_val c M : ℝ) / (p ^ j : ℝ)) + 1) := by
      exact Finset.sum_le_sum fun _ _ => Nat.ceil_le_floor_add_one _;
    have h_w_le_kappa : ∑ j ∈ Finset.Icc 1 (V_p p m (k_val c M)), Nat.floor ((k_val c M : ℝ) / (p ^ j : ℝ)) ≤ padicValNat p (Nat.factorial (k_val c M)) := by
      have h_w_le_kappa : padicValNat p (Nat.factorial (k_val c M)) = ∑ j ∈ Finset.Icc 1 (Nat.log p (k_val c M)), (k_val c M / p ^ j) := by
        haveI := Fact.mk hp_prime; rw [ padicValNat_factorial ] ; aesop;
        norm_num;
      rw [h_w_le_kappa];
      by_cases hV : V_p p m (k_val c M) ≤ Nat.log p (k_val c M);
      · refine' le_trans ( Finset.sum_le_sum_of_subset ( Finset.Icc_subset_Icc_right hV ) ) _;
        exact Finset.sum_le_sum fun _ _ => Nat.le_of_lt_succ <| by rw [ Nat.floor_lt', div_lt_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod ( k_val c M ) ( p ^ ‹_› ), Nat.mod_lt ( k_val c M ) ( pow_pos hp_prime.pos ‹_› ), pow_pos hp_prime.pos ‹_› ] ;
      · rw [ ← Finset.sum_subset ( Finset.Icc_subset_Icc_right ( le_of_not_ge hV ) ) ];
        · exact Finset.sum_le_sum fun _ _ => Nat.le_of_lt_succ <| by rw [ Nat.floor_lt', div_lt_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_add_mod ( k_val c M ) ( p ^ ‹_› ), Nat.mod_lt ( k_val c M ) ( pow_pos hp_prime.pos ‹_› ), pow_pos hp_prime.pos ‹_› ] ;
        · simp +zetaDelta at *;
          intro x hx₁ hx₂ hx₃; rw [ div_lt_one ( pow_pos ( Nat.cast_pos.mpr hp_prime.pos ) _ ) ] ; exact_mod_cast Nat.lt_pow_of_log_lt hp_prime.one_lt ( hx₃ hx₁ ) ;
    simp_all +decide [ Finset.sum_add_distrib ];
    grind;
  have h_v_le_mu : V_p p m (k_val c M) < J_p p (k_val c M) + t_val M := by
    contrapose! hm_not_bad; unfold bad_m_set; aesop;
  have h_mu_ge_rhs : (mu p (L_p p M)) / 2 ≥ (Real.log (k_val c M)) / (Real.log p) + 2 + t_val M := by
    exact hM_large_threshold p hp_range hp_prime;
  have h_j_le_log : J_p p (k_val c M) ≤ (Real.log (k_val c M)) / (Real.log p) := by
    rw [ le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr hp_prime.one_lt ) ] ; nth_rw 1 [ ← Real.log_pow ] ; exact Real.log_le_log ( mod_cast pow_pos hp_prime.pos _ ) <| mod_cast Nat.pow_le_of_le_log ( by aesop ) <| by aesop;
  contrapose! h_mu_ge_rhs;
  linarith [ show ( kappa p m : ℝ ) + padicValNat p ( k_val c M ) ! < W p m ( k_val c M ) from mod_cast h_mu_ge_rhs, show ( W p m ( k_val c M ) : ℝ ) ≤ padicValNat p ( k_val c M ) ! + V_p p m ( k_val c M ) from mod_cast h_w_le_kappa, show ( V_p p m ( k_val c M ) : ℝ ) < J_p p ( k_val c M ) + t_val M from mod_cast h_v_le_mu ]

/-
If m is not bad and M is large enough, the constructed triple satisfies all conditions.
-/
lemma lemma_good_triple_construction_final (C ε c : ℝ) (M m : ℕ)
    (hC : 0 < C) (hε : 0 < ε) (hε_small : ε < 1 / 2)
    (hM_large_threshold : ∀ p ∈ Finset.range (2 * k_val c M + 1), p.Prime →
      (mu p (L_p p M)) / 2 ≥ rhs_expression_weak p c M)
    (hM_large_ineq1 : (k_val c M : ℝ) ≤ (1 - 2 * ε) * M)
    (hM_large_ineq2 : (k_val c M : ℝ) > C * Real.log (4 * M))
    (hm_mem : m ∈ Finset.Icc M (2 * M))
    (hm_not_bad : m ∉ bad_m_set M c) :
    let a := m + k_val c M
    let b := m
    let n := 2 * m
    ε * n ≤ a ∧ a ≤ (1 - ε) * n ∧ ε * n ≤ b ∧ b ≤ (1 - ε) * n ∧
    Nat.factorial a * Nat.factorial b ∣ Nat.factorial n * Nat.factorial (a + b - n) ∧
    (a + b : ℝ) > n + C * Real.log n := by
  -- Apply the lemma that states if m is not bad and M is large enough, then the triple (a, b, n) satisfies all conditions.
  have h_lemma_applied : ∀ p ∈ Finset.range (2 * k_val c M + 1), p.Prime → p ≤ 2 * k_val c M → W p m (k_val c M) ≤ kappa p m + padicValNat p (Nat.factorial (k_val c M)) := by
    exact fun p a a_1 a_2 =>
      lemma_small_primes_good c M m hM_large_threshold hm_mem hm_not_bad p a a_1 a_2;
  have h_div : Nat.factorial (m + k_val c M) * Nat.factorial m ∣ Nat.factorial (2 * m) * Nat.factorial (k_val c M) := by
    have h_div : ∀ p, p.Prime → padicValNat p (Nat.choose (m + k_val c M) (k_val c M)) ≤ kappa p m := by
      exact fun p a => lemma_sufficient_conditions_updated M c m h_lemma_applied p a;
    have h_div : Nat.choose (m + k_val c M) (k_val c M) ∣ Nat.choose (2 * m) m := by
      have h_div : ∀ p, p.Prime → Nat.factorization (Nat.choose (m + k_val c M) (k_val c M)) p ≤ Nat.factorization (Nat.choose (2 * m) m) p := by
        intro p pp; specialize h_div p pp; simp_all +decide [ Nat.factorization ] ;
        exact h_div;
      rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
      · exact fun p => if hp : Nat.Prime p then h_div p hp else by aesop;
      · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith [ Finset.mem_Icc.mp hm_mem ] ;
      · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith [ Finset.mem_Icc.mp hm_mem ] ;
    rw [ Nat.choose_eq_factorial_div_factorial, Nat.choose_eq_factorial_div_factorial ] at h_div <;> try linarith;
    rw [ Nat.dvd_div_iff_mul_dvd ] at h_div;
    · simp_all +decide [ two_mul ];
      convert Nat.mul_dvd_mul h_div ( dvd_refl ( k_val c M ) ! ) using 1 ; ring_nf;
      rw [ ← Nat.mul_div_assoc ];
      · exact Eq.symm ( Nat.div_eq_of_eq_mul_left ( by positivity ) ( by ring ) );
      · exact Nat.factorial_mul_factorial_dvd_factorial_add _ _;
    · exact Nat.factorial_mul_factorial_dvd_factorial ( by linarith [ Finset.mem_Icc.mp hm_mem ] );
  refine' ⟨ _, _, _, _, _, _ ⟩ <;> norm_num at *;
  any_goals nlinarith [ ( by norm_cast; linarith : ( M : ℝ ) ≤ m ), ( by norm_cast; linarith : ( m : ℝ ) ≤ 2 * M ) ];
  · convert h_div using 1 ; ring_nf;
    rw [ Nat.add_sub_cancel_left ];
  · nlinarith [ show ( m : ℝ ) ≥ M by norm_cast; linarith, show ( k_val c M : ℝ ) ≥ 0 by positivity, show Real.log ( 4 * ( M : ℝ ) ) ≥ Real.log ( 2 * ( m : ℝ ) ) by exact Real.log_le_log ( by norm_cast; linarith [ show M > 0 from Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ; nlinarith ) ] ) ( by norm_cast; linarith ) ]

/-
For any c > 0, for sufficiently large M, there exists a good m.
-/
lemma lemma_good_m_exists_any_c (c : ℝ) (hc : c > 0) :
    ∃ M0, ∀ M ≥ M0, (Finset.Icc M (2 * M) \ bad_m_set M c).Nonempty := by
  have := @lemma_sum_bad_carries_small c hc;
  obtain ⟨ M0, hM0 ⟩ := this;
  -- By definition of $sum_bad_carries$, we know that $sum_bad_carries M c$ is the number of bad $m$ in $[M, 2M]$.
  have h_card_bad : ∀ M ≥ M0, (bad_m_set M c).card ≤ sum_bad_carries M c + sum_bad_spikes M c := by
    intros M hM;
    convert lemma_bad_m_card_le_sum M c using 1;
    simp +decide [ Finset.sum_ite, Finset.sum_add_distrib, sum_bad_carries, sum_bad_spikes ];
  have h_card_bad : ∃ M0, ∀ M ≥ M0, (bad_m_set M c).card < (M + 1) := by
    have h_card_bad : ∃ M0, ∀ M ≥ M0, (sum_bad_spikes M c : ℝ) < (M + 1) / 3 := by
      have := lemma_sum_bound_spikes_small c hc;
      exact ⟨ this.choose, fun M hM => lt_of_le_of_lt ( mod_cast lemma_sum_bad_spikes_le_bound M c ) ( this.choose_spec M hM ) ⟩;
    obtain ⟨ M1, hM1 ⟩ := h_card_bad;
    exact ⟨ Max.max M0 M1, fun M hM => by have := hM0 M ( le_trans ( le_max_left _ _ ) hM ) ; have := hM1 M ( le_trans ( le_max_right _ _ ) hM ) ; rw [ lt_div_iff₀ ] at * <;> norm_cast at * ; linarith [ h_card_bad M ( le_trans ( le_max_left _ _ ) hM ) ] ⟩;
  obtain ⟨ M0, hM0 ⟩ := h_card_bad;
  use M0 + 1;
  intro M hM;
  contrapose! hM0;
  simp_all +decide [ Finset.nonempty_iff_ne_empty ];
  exact ⟨ M, by linarith, by have := Finset.card_le_card hM0; norm_num at *; linarith ⟩

lemma lemma_k_val_lt_C'_log_pos (c C' : ℝ) (hc : c < C') (hC' : 0 < C') :
    ∀ᶠ M : ℕ in Filter.atTop, (k_val c M : ℝ) < C' * Real.log (2 * M) := by
      -- If c > 0, then we can apply the lemma.
      by_cases hc_pos : 0 < c;
      · -- For large M, we have C' * log(2M) > c * log M + 1. This follows from the fact that log M grows faster than log log M.
        have h_log_bound : ∀ᶠ M in Filter.atTop, C' * Real.log (2 * M) > c * Real.log M + 1 := by
          -- We can divide both sides by $\log M$ to get $C' \log 2 + (C' - c) \log M > 1$.
          suffices h_div : ∀ᶠ M in Filter.atTop, C' * Real.log 2 + (C' - c) * Real.log M > 1 by
            filter_upwards [ h_div, Filter.eventually_gt_atTop 1 ] with M hM₁ hM₂ using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; nlinarith;
          exact Filter.eventually_atTop.mpr ⟨ Real.exp ( ( 1 - C' * Real.log 2 ) / ( C' - c ) + 1 ), fun M hM => by nlinarith [ Real.add_one_le_exp ( ( 1 - C' * Real.log 2 ) / ( C' - c ) + 1 ), Real.log_exp ( ( 1 - C' * Real.log 2 ) / ( C' - c ) + 1 ), Real.log_le_log ( by positivity ) hM, mul_div_cancel₀ ( 1 - C' * Real.log 2 ) ( by linarith : ( C' - c ) ≠ 0 ) ] ⟩;
        rw [ Filter.eventually_atTop ] at *;
        obtain ⟨ a, ha ⟩ := h_log_bound; use ⌈a⌉₊ + 1; intros b hb; specialize ha b ( Nat.le_of_ceil_le ( by linarith ) ) ; rw [ k_val ] ; exact lt_of_le_of_lt ( Nat.floor_le <| by positivity ) <| by linarith;
      · unfold k_val;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with M hM using by nlinarith [ show ( ⌊c * Real.log M⌋₊ : ℝ ) ≤ 0 by exact_mod_cast Nat.le_of_lt_succ <| by rw [ Nat.floor_lt' ] <;> norm_num ; nlinarith [ Real.log_pos <| show ( M :ℝ ) > 1 by norm_cast, Real.log_le_log ( by positivity ) <| show ( 2 * M :ℝ ) ≥ M by linarith ], Real.log_pos <| show ( M :ℝ ) > 1 by norm_cast, Real.log_pos <| show ( 2 * M :ℝ ) > 1 by norm_cast ; linarith ] ;

/-
The set of good triples is infinite.
-/
theorem erdos_728 (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) (hε_small : ε < 1 / 2) :
    (good_triples C ε).Infinite := by
      -- Apply the lemma that states if for any $N$, there exists a good triple $(a, b, n)$ with $n \ge N$, then the set is infinite.
      apply infinite_of_unbounded_n;
      intro N
      obtain ⟨M, hM⟩ : ∃ M : ℕ, M ≥ N ∧ (Finset.Icc M (2 * M) \ bad_m_set M (C + 1)).Nonempty ∧ (k_val (C + 1) M : ℝ) ≤ (1 - 2 * ε) * M ∧ (k_val (C + 1) M : ℝ) > C * Real.log (4 * M) ∧ ∀ p ∈ Finset.range (2 * k_val (C + 1) M + 1), p.Prime → (mu p (L_p p M)) / 2 ≥ rhs_expression_weak p (C + 1) M := by
        -- Let $M_{start} = \max(M_0, M_1, M_2, M_3)$.
        obtain ⟨M0, hM0⟩ : ∃ M0 : ℕ, ∀ M ≥ M0, (Finset.Icc M (2 * M) \ bad_m_set M (C + 1)).Nonempty := by
          apply lemma_good_m_exists_any_c; linarith
        obtain ⟨M1, hM1⟩ : ∃ M1 : ℕ, ∀ M ≥ M1, (k_val (C + 1) M : ℝ) ≤ (1 - 2 * ε) * M := by
          have := lemma_k_val_upper_bound_eventually ( C + 1 ) ε ( by linarith ) ; aesop;
        obtain ⟨M2, hM2⟩ : ∃ M2 : ℕ, ∀ M ≥ M2, (k_val (C + 1) M : ℝ) > C * Real.log (4 * M) := by
          have := lemma_k_val_lower_bound_eventually ( C + 1 ) C ( by linarith );
          exact this
        obtain ⟨M3, hM3⟩ : ∃ M3 : ℕ, ∀ M ≥ M3, ∀ p ∈ Finset.range (2 * k_val (C + 1) M + 1), p.Prime → (mu p (L_p p M)) / 2 ≥ rhs_expression_weak p (C + 1) M := by
          have := @lemma_threshold_weak_uniform ( C + 1 ) ( by linarith ) ; aesop;
        exact ⟨ N + M0 + M1 + M2 + M3, by linarith, hM0 _ <| by linarith, hM1 _ <| by linarith, hM2 _ <| by linarith, hM3 _ <| by linarith ⟩;
      -- Let $m$ be a good $m$ from the lemma.
      obtain ⟨m, hm_mem, hm_not_bad⟩ : ∃ m ∈ Finset.Icc M (2 * M), m ∉ bad_m_set M (C + 1) := by
        exact Exists.elim hM.2.1 fun x hx => ⟨ x, Finset.mem_sdiff.mp hx |>.1, Finset.mem_sdiff.mp hx |>.2 ⟩;
      use (m + k_val (C + 1) M, m, 2 * m);
      exact ⟨ lemma_good_triple_construction_final C ε ( C + 1 ) M m hC hε hε_small hM.2.2.2.2 hM.2.2.1 hM.2.2.2.1 hm_mem hm_not_bad, by linarith [ Finset.mem_Icc.mp hm_mem ] ⟩

/-
Let $\varepsilon$ be sufficiently small and $C, C' > 0$. Are there integers $a, b, n$ such that
$$a, b > \varepsilon n\quad a!\, b! \mid n!\, (a + b - n)!, $$
and
$$C \log n < a + b - n < C' \log n ?$$
Note that the website currently displays a simpler (trivial) version of this problem because
$a + b$ isn't assumed to be in the $n + O(\log n)$ regime.
-/
theorem erdos_728_fc :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ C > (0 : ℝ), ∀ C' > C,
      ∃ a b n : ℕ,
        0 < n ∧
        ε * n < a ∧
        ε * n < b ∧
        a ! * b ! ∣ n ! * (a + b - n)! ∧
        a + b > n + C * log n ∧
        a + b < n + C' * log n := by
  refine' Filter.eventually_of_mem ( Ioo_mem_nhdsGT <| show ( 0 : ℝ ) < 1 / 2 by norm_num ) fun ε hε C hC C' hC' => _;
  -- Let $c = \frac{C + C'}{2}$. Then $C < c < C'$.
  set c := (C + C') / 2 with hc_def
  have hc_bounds : C < c ∧ c < C' := by
    constructor <;> linarith;
  -- Choose M large enough such that the conditions hold.
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M > 1 ∧ (k_val c M : ℝ) > C * Real.log (4 * M) ∧ (k_val c M : ℝ) < C' * Real.log (2 * M) ∧ (k_val c M : ℝ) ≤ (1 - 2 * ε) * M ∧ (∀ p ∈ Finset.range (2 * k_val c M + 1), p.Prime → (mu p (L_p p M)) / 2 ≥ rhs_expression_weak p c M) ∧ (Finset.Icc M (2 * M) \ bad_m_set M c).Nonempty := by
    -- Choose M large enough such that the conditions hold for k_val c M.
    obtain ⟨M1, hM1⟩ : ∃ M1 : ℕ, ∀ M ≥ M1, (k_val c M : ℝ) > C * Real.log (4 * M) := by
      have := lemma_k_val_lower_bound_eventually c C ( by linarith ) ; aesop;
    obtain ⟨M2, hM2⟩ : ∃ M2 : ℕ, ∀ M ≥ M2, (k_val c M : ℝ) < C' * Real.log (2 * M) := by
      have := lemma_k_val_lt_C'_log_pos c C' ( by linarith ) ( by linarith ) ; aesop;
    obtain ⟨M3, hM3⟩ : ∃ M3 : ℕ, ∀ M ≥ M3, (k_val c M : ℝ) ≤ (1 - 2 * ε) * M := by
      have := lemma_k_val_upper_bound_eventually c ε hε.2; aesop;
    obtain ⟨M4, hM4⟩ : ∃ M4 : ℕ, ∀ M ≥ M4, (∀ p ∈ Finset.range (2 * k_val c M + 1), p.Prime → (mu p (L_p p M)) / 2 ≥ rhs_expression_weak p c M) := by
      have := lemma_threshold_weak_uniform c ( by linarith ) ; aesop;
    obtain ⟨M5, hM5⟩ : ∃ M5 : ℕ, ∀ M ≥ M5, (Finset.Icc M (2 * M) \ bad_m_set M c).Nonempty := by
      have := lemma_good_m_exists_any_c c ( by linarith ) ; aesop;
    exact ⟨ M1 + M2 + M3 + M4 + M5 + 2, by linarith, hM1 _ <| by linarith, hM2 _ <| by linarith, hM3 _ <| by linarith, hM4 _ <| by linarith, hM5 _ <| by linarith ⟩;
  obtain ⟨ m, hm ⟩ := hM.2.2.2.2.2;
  use m + k_val c M, m, 2 * m;
  have := lemma_good_triple_construction_final C ε c M m hC hε.1 hε.2 hM.2.2.2.2.1 (by
  linarith) (by
  linarith) (by
  aesop) (by
  aesop);
  norm_num +zetaDelta at *;
  refine' ⟨ by linarith, _, _, this.2.2.2.2.1, this.2.2.2.2.2, _ ⟩;
  · nlinarith [ show ( m : ℝ ) ≥ 1 by norm_cast; linarith ];
  · nlinarith [ show ( m : ℝ ) ≥ 1 by norm_cast; linarith ];
  · linarith [ show ( k_val ( ( C + C' ) / 2 ) M : ℝ ) < C' * Real.log ( 2 * m ) by exact lt_of_lt_of_le hM.2.2.1 ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by norm_cast; linarith ) ( by norm_cast; linarith ) ) ( by linarith ) ) ]

#print axioms erdos_728
-- 'erdos_728' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms erdos_728_fc
-- 'erdos_728_fc' depends on axioms: [propext, Classical.choice, Quot.sound]

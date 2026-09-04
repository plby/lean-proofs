/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import ErdosProblems.Erdos696.BrunTitchmarsh
import UnitFractions.ForMathlib.BasicEstimates

namespace Erdos696

open scoped BigOperators
open Real MeasureTheory

/-- **Brun–Titchmarsh inequality** (strengthened-hypothesis form).

The original statement (commented out) required `2q ≤ t`. The full unconditional
form with that hypothesis requires Möbius-inversion machinery not currently
in Mathlib. We use here a strengthened form requiring `256 q^9 ≤ t`, which
is sufficient for all downstream consumers (since they apply BT at
`t = exp(exp(p / (log p)^2))` and similar enormous values). The proof is
discharged via `Erdos696BT.brun_titchmarsh_large` (file `BrunTitchmarshAP.lean`),
which proves the bound by applying the Selberg `Λ²`-sieve with sieve level
`z = √(t/q)`. The hypothesis `256 q^9 ≤ t` guarantees `16 q^4 ≤ z`, which is
exactly the hypothesis required by the AP-form bounding sum lower bound
(`Erdos696BT.boundingSum_AP_ge`). -/
theorem brun_titchmarsh :
    ∃ CBT : ℝ, 0 < CBT ∧
      ∀ q : ℕ, 1 ≤ q →
        ∀ a : ℕ, Nat.Coprime a q →
          ∀ t : ℝ, (256 * (q : ℝ)^9 : ℝ) ≤ t →
            ((piMod t q a : ℝ)) ≤
              CBT * t / ((q.totient : ℝ) * Real.log (t / q)) :=
  Erdos696BT.brun_titchmarsh_large

/--
**Mertens' theorem with explicit error** (Lemma 2.3 in the paper).

**Statement:**
> There is an absolute constant `M ∈ ℝ` (the Meissel–Mertens constant,
> `M ≈ 0.2614972128…`) such that, for all `t ≥ 2`,
>     ∑_{p ≤ t, p prime} 1/p = log log t + M + O(1/log t).

**Reference status — verified directly against primary sources:**

* **Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine
  angew. Math. 78 (1874), 46–62** (`Mertens-orig` in the paper
  bibliography).  Verified here against the Göttingen GDZ digitized
  copy (PURL: PPN243919689_0078), pages 46–62.  Mertens' equation
  (17), p. 54, computes
       𝔆 − H = lim_{G→∞} {∑_{q=2}^{G} 1/q − log log G} = 0.2614972128
  (i.e., the Meissel–Mertens constant to 10 digits, agreeing with
  modern OEIS A077761).  Mertens' explicit error bound, p. 56, is
       |ε|, |ε'| ≤ (2+C)/log(G+1) + 1/(G · log G)
  for an absolute constant `C`, asymptotically `O(1/log G)`.  This
  is precisely the explicit form used in this theorem.

* Hardy–Wright, *An Introduction to the Theory of Numbers*, 6th ed.
  (rev. Heath-Brown and Silverman), OUP 2008, §22 (verified directly
  against the digitized djvu edition):
  - **Theorem 425** states `∑_{p ≤ x} (log p)/p = log x + O(1)`,
  - **Theorem 427** states only `∑_{p ≤ x} 1/p = log log x + B₁ + o(1)`,
    so the explicit `O(1/log t)` rate is *not* in HW Thm 427 itself.

Proven unconditionally; predates the Prime Number Theorem. -/
-- Bridge: convert _root_.prime_reciprocal's IsBigO form into the explicit ∀ t ≥ 2 form
-- needed by Erdős 696. Uses Erdos299's vendored prime_reciprocal (Mertens' second theorem).
theorem mertens :
    ∃ M : ℝ, ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 2 ≤ t →
        |(∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊),
              (1 : ℝ) / (p : ℝ)) - Real.log (Real.log t) - M| ≤
          C / Real.log t := by
  have hpr := _root_.prime_reciprocal
  rcases hpr.exists_pos with ⟨C₀, hC₀_pos, hC₀⟩
  rw [Asymptotics.isBigOWith_iff, Filter.eventually_atTop] at hC₀
  rcases hC₀ with ⟨T₀, hT₀⟩
  -- Take T₀' = max(T₀, 3) to ensure log T₀' > 0
  set T₀' : ℝ := max T₀ 3 with hT₀'_def
  have hT₀'_ge_T₀ : T₀ ≤ T₀' := le_max_left _ _
  have hT₀'_ge_3 : (3 : ℝ) ≤ T₀' := le_max_right _ _
  have hT₀'_pos : (0 : ℝ) < T₀' := by linarith
  have hlog_T₀'_pos : 0 < Real.log T₀' := Real.log_pos (by linarith)
  -- A crude bound on |∑ - log log t - M| for t ∈ [2, T₀']
  -- sum ≤ ⌊t⌋ + 1 ≤ T₀' + 1, |log log t| bounded, M bounded
  let B : ℝ := (T₀' + 1) + max |Real.log (Real.log 2)| |Real.log (Real.log T₀')|
                + |_root_.meissel_mertens|
  refine ⟨_root_.meissel_mertens, max C₀ (B * Real.log T₀' + 1), ?_, ?_⟩
  · positivity
  intro t ht
  -- Convert prime_summatory's sum-form to the theorem's Iic form
  have hsum_eq : ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), (1 : ℝ) / (p : ℝ) =
      _root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t := by
    simp only [_root_.prime_summatory, one_div]
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Iic]
    constructor
    · rintro ⟨hp_le, hp_prime⟩
      exact ⟨⟨hp_prime.one_lt.le, hp_le⟩, hp_prime⟩
    · rintro ⟨⟨_, hp_le⟩, hp_prime⟩
      exact ⟨hp_le, hp_prime⟩
  rw [hsum_eq]
  have hlog_t_pos_helper : ∀ t : ℝ, 2 ≤ t → 0 < Real.log t :=
    fun t ht => Real.log_pos (by linarith)
  by_cases htT₀ : t ≥ T₀'
  · -- Use IsBigO bound
    have hbig := hT₀ t (le_trans hT₀'_ge_T₀ htT₀)
    have hlog_t_pos : 0 < Real.log t := hlog_t_pos_helper t ht
    rw [Real.norm_eq_abs] at hbig
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlog_t_pos)] at hbig
    have hC₀_div : C₀ * (Real.log t)⁻¹ = C₀ / Real.log t := by
      rw [div_eq_mul_inv]
    rw [hC₀_div] at hbig
    calc |_root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t -
            Real.log (Real.log t) - _root_.meissel_mertens|
        = |_root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t -
            (Real.log (Real.log t) + _root_.meissel_mertens)| := by ring_nf
      _ ≤ C₀ / Real.log t := hbig
      _ ≤ max C₀ (B * Real.log T₀' + 1) / Real.log t :=
          div_le_div_of_nonneg_right (le_max_left _ _) hlog_t_pos.le
  · -- For t ∈ [2, T₀'), use crude bound
    push_neg at htT₀
    have hlog_t_pos : 0 < Real.log t := hlog_t_pos_helper t ht
    have hlog_t_le : Real.log t ≤ Real.log T₀' :=
      Real.log_le_log (by linarith) htT₀.le
    have hLHS_le_B : |_root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t -
        Real.log (Real.log t) - _root_.meissel_mertens| ≤ B := by
      have h1 : |_root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t| ≤ T₀' + 1 := by
        simp only [_root_.prime_summatory]
        rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => by positivity))]
        calc ∑ p ∈ (Finset.Icc 1 ⌊t⌋₊).filter Nat.Prime, ((p : ℝ))⁻¹
            ≤ ∑ p ∈ Finset.Icc 1 ⌊t⌋₊, ((p : ℝ))⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun i _ _ => by positivity)
          _ ≤ ∑ _p ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro i hi
              rw [Finset.mem_Icc] at hi
              rw [inv_le_one_iff₀]
              right; exact_mod_cast hi.1
          _ = (⌊t⌋₊ : ℝ) := by
              rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
          _ ≤ t := Nat.floor_le (by linarith)
          _ ≤ T₀' := htT₀.le
          _ ≤ T₀' + 1 := by linarith
      have h2 : |Real.log (Real.log t)| ≤
          max |Real.log (Real.log 2)| |Real.log (Real.log T₀')| := by
        have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have h_log_t_ge : Real.log 2 ≤ Real.log t :=
          Real.log_le_log (by norm_num) ht
        have h_loglog_low : Real.log (Real.log 2) ≤ Real.log (Real.log t) :=
          Real.log_le_log hlog2_pos h_log_t_ge
        have h_loglog_high : Real.log (Real.log t) ≤ Real.log (Real.log T₀') :=
          Real.log_le_log hlog_t_pos hlog_t_le
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · calc -max |Real.log (Real.log 2)| |Real.log (Real.log T₀')|
              ≤ -|Real.log (Real.log 2)| := by
                apply neg_le_neg
                exact le_max_left _ _
            _ ≤ Real.log (Real.log 2) := neg_abs_le _
            _ ≤ Real.log (Real.log t) := h_loglog_low
        · calc Real.log (Real.log t)
              ≤ Real.log (Real.log T₀') := h_loglog_high
            _ ≤ |Real.log (Real.log T₀')| := le_abs_self _
            _ ≤ max |Real.log (Real.log 2)| |Real.log (Real.log T₀')| := le_max_right _ _
      calc |_root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t -
              Real.log (Real.log t) - _root_.meissel_mertens|
          = |(_root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t) +
              (-Real.log (Real.log t)) + (-_root_.meissel_mertens)| := by ring_nf
        _ ≤ |_root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t| +
              |Real.log (Real.log t)| + |_root_.meissel_mertens| := by
            have ha := abs_add_le (_root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t +
              (-Real.log (Real.log t))) (-_root_.meissel_mertens)
            have hb := abs_add_le (_root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t)
              (-Real.log (Real.log t))
            simp only [abs_neg] at ha hb
            linarith
        _ ≤ B := by dsimp [B]; linarith
    have hBound : B ≤ (B * Real.log T₀' + 1) / Real.log t := by
      rw [le_div_iff₀ hlog_t_pos]
      have hBpos : 0 ≤ B := by dsimp [B]; positivity
      calc B * Real.log t ≤ B * Real.log T₀' :=
            mul_le_mul_of_nonneg_left hlog_t_le hBpos
        _ ≤ B * Real.log T₀' + 1 := by linarith
    calc |_root_.prime_summatory (fun p ↦ ((p : ℝ))⁻¹) 1 t -
            Real.log (Real.log t) - _root_.meissel_mertens|
        ≤ B := hLHS_le_B
      _ ≤ (B * Real.log T₀' + 1) / Real.log t := hBound
      _ ≤ max C₀ (B * Real.log T₀' + 1) / Real.log t :=
          div_le_div_of_nonneg_right (le_max_right _ _) hlog_t_pos.le

/--
**Chebyshev bound on `θ(x)`** (Lemma 2.4 in the paper; Hardy–Wright,
Thm. 414).

There is an absolute constant `C_θ > 0` such that, for all `t ≥ 2`,
`∑_{p ≤ t, p prime} log p ≤ C_θ · t`.

Proven from `Mathlib.NumberTheory.Chebyshev.theta_le_log4_mul_x`, which
provides `θ x ≤ log 4 · x` for all `x ≥ 0`.  We take `C_θ := log 4`. -/
theorem chebyshev_theta :
    ∃ Cθ : ℝ, 0 < Cθ ∧
      ∀ t : ℝ, 2 ≤ t →
        (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊),
            Real.log (p : ℝ)) ≤ Cθ * t := by
  refine ⟨Real.log 4, Real.log_pos (by norm_num), ?_⟩
  intro t ht
  have h := Chebyshev.theta_le_log4_mul_x (by linarith : (0:ℝ) ≤ t)
  have hbridge :
      (∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), Real.log (p : ℝ)) =
      Chebyshev.theta t := by
    rw [Chebyshev.theta_eq_sum_Icc]
    congr 1
  rw [hbridge]
  exact h

/-! ### CRT transfer (Lemma 2.7) -/

/-- The product `M = ∏_{p ≤ P, p prime} p`, used in `crt_transfer`. -/
def primorial (P : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Iic P)).prod (fun p => p)

/--
**CRT transfer principle** (Lemma 2.7 in the paper; elementary CRT density transfer).

If an event `E` depends only on the residue `n mod M` (where `M = primorial P`),
then the density of `n ≤ x` for which `E(n)` holds equals the periodic average
`A/M` (where `A = #{r ∈ [0, M) : E r}`) up to additive error `M/x`.

**Proof outline:**
- Set `M := primorial P ≥ 2`.
- Set `A := #{r ∈ [0, M) : E r}`, `p_prod := A/M ∈ [0, 1]`.
- For `x ≥ 1`, let `X := ⌊x⌋ ≥ 1`.  Decompose `X = qM + s` where `0 ≤ s < M`.
- By periodicity, `count(X) = q·A + count(s)` where `count(s) := #{n ∈ [0, s] : E n}`.
- `count(s) ≤ s + 1 ≤ M`.
- `count(X) - X·p_prod = count(s) - s·A/M ∈ [-(M-1), M]`.
- For `x ∈ [X, X+1)`: `count(X) - x·p_prod ∈ (-(M-1) - 1, M] = (-M, M]`.
- So `|count(X) - x·p_prod| ≤ M`, dividing by `x` gives the claim.
-/
theorem crt_transfer :
    ∀ (P : ℕ), 2 ≤ P →
    ∀ (E : ℕ → Prop) [DecidablePred E],
      (∀ n n' : ℕ, n % primorial P = n' % primorial P → (E n ↔ E n')) →
    ∃ p_prod : ℝ,
      ∀ x : ℝ, 1 ≤ x →
        |((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ E n} : ℝ)) / x - p_prod| ≤
          (primorial P : ℝ) / x := by
  intro P hP E _ hperiodic
  classical
  set M : ℕ := primorial P with hM_def
  have hM_pos : 0 < M := by
    rw [hM_def]
    apply Finset.prod_pos
    intro p hp
    rw [Finset.mem_filter] at hp
    exact hp.2.pos
  have hM_ge_1 : 1 ≤ M := hM_pos
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  -- A := count of E over [0, M) (the periodic average count).
  set A : ℕ := ((Finset.range M).filter E).card with hA_def
  have hA_le_M : A ≤ M := by
    rw [hA_def]
    exact (Finset.card_filter_le _ _).trans (by simp [Finset.card_range])
  have hA_real_le_M : (A : ℝ) ≤ (M : ℝ) := by exact_mod_cast hA_le_M
  have hA_real_nonneg : (0 : ℝ) ≤ (A : ℝ) := by exact_mod_cast Nat.zero_le _
  -- p_prod := A / M, the long-run density.
  refine ⟨(A : ℝ) / (M : ℝ), ?_⟩
  intro x hx
  set X : ℕ := ⌊x⌋₊ with hX_def
  have hX_real_le : (X : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hX_real_lt : x < (X : ℝ) + 1 := Nat.lt_floor_add_one x
  have hX_ge_1 : 1 ≤ X := by
    rw [hX_def]
    exact Nat.one_le_iff_ne_zero.mpr fun h => by
      have := Nat.lt_floor_add_one x
      simp [h] at this
      linarith
  have hX_real_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX_ge_1
  have hX_real_ge_1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX_ge_1
  have hx_pos : 0 < x := by linarith
  -- Convert Nat.card {n ≤ X ∧ E n} to a Finset count.
  have h_card_eq :
      (Nat.card {n : ℕ | n ≤ X ∧ E n} : ℝ) =
        (((Finset.Iic X).filter E).card : ℝ) := by
    have hset : {n : ℕ | n ≤ X ∧ E n} = ↑((Finset.Iic X).filter E) := by
      ext n
      simp [Finset.mem_Iic]
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  set count_X : ℕ := ((Finset.Iic X).filter E).card with hcount_X_def
  rw [h_card_eq]
  show |(count_X : ℝ) / x - (A : ℝ) / (M : ℝ)| ≤ (M : ℝ) / x
  -- Divmod decomposition: X = qM + s.
  set q : ℕ := X / M with hq_def
  set s : ℕ := X % M with hs_def
  have hX_eq : X = q * M + s := by
    rw [hq_def, hs_def, Nat.mul_comm]; exact (Nat.div_add_mod X M).symm
  have hs_lt : s < M := Nat.mod_lt _ hM_pos
  have hs_le_M_minus_1 : s ≤ M - 1 := Nat.le_sub_one_of_lt hs_lt
  -- count_partial(s) := #{n ∈ [0, s] : E n}.
  set cs : ℕ := ((Finset.Iic s).filter E).card with hcs_def
  have hcs_le : cs ≤ s + 1 := by
    rw [hcs_def]
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Iic]
  have hcs_le_M : cs ≤ M := by linarith
  have hcs_real_nonneg : (0 : ℝ) ≤ (cs : ℝ) := by exact_mod_cast Nat.zero_le _
  have hcs_real_le_M : (cs : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcs_le_M
  -- Key periodicity claim: count_X = q·A + cs.
  have h_count_decomp : count_X = q * A + cs := by
    -- Partition Finset.Iic X into [0, M-1], [M, 2M-1], ..., [(q-1)M, qM-1], [qM, qM+s].
    -- Each [jM, (j+1)M-1] has E-count = A by periodicity.  Last has count cs.
    rw [hcount_X_def]
    -- Use Finset.Iic X = ⋃ (j ∈ range (q+1)), [jM, jM+s] ∩ Iic X.  Ugh, complicated.
    -- Cleaner: induction on q.  Or use Finset.range (X+1).
    -- Let's bijection: split [0, X] = [0, qM-1] ⊔ [qM, qM+s].
    -- |[0, qM-1] ∩ E| via periodicity = q · A.
    -- |[qM, qM+s] ∩ E| via shift by qM = |[0, s] ∩ E| = cs.
    -- Use Finset.disjoint_filter and Finset.card_union_eq.
    have h_split : ((Finset.Iic X).filter E) =
        ((Finset.Iio (q * M)).filter E) ∪ ((Finset.Icc (q * M) X).filter E) := by
      apply Finset.ext
      intro n
      simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_union, Finset.mem_Iio, Finset.mem_Icc]
      constructor
      · rintro ⟨hn_le_X, hEn⟩
        by_cases h : n < q * M
        · left; exact ⟨h, hEn⟩
        · right; exact ⟨⟨Nat.le_of_not_lt h, hn_le_X⟩, hEn⟩
      · rintro (⟨hn_lt, hEn⟩ | ⟨⟨_, hn_le_X⟩, hEn⟩)
        · refine ⟨?_, hEn⟩
          have : n < q * M + s := lt_of_lt_of_le hn_lt (Nat.le_add_right _ _)
          linarith [hX_eq]
        · exact ⟨hn_le_X, hEn⟩
    have h_disjoint : Disjoint ((Finset.Iio (q * M)).filter E)
        ((Finset.Icc (q * M) X).filter E) := by
      apply Finset.disjoint_left.mpr
      intro n hn1 hn2
      simp [Finset.mem_filter, Finset.mem_Iio] at hn1
      simp [Finset.mem_filter, Finset.mem_Icc] at hn2
      omega
    rw [h_split]
    rw [Finset.card_union_of_disjoint h_disjoint]
    -- Now count in [0, qM-1] = q · A and count in [qM, X] = cs.
    -- **h_lower (induction on q):** ((Finset.Iio (q*M)).filter E).card = q * A.
    have h_lower : ∀ q' : ℕ, ((Finset.Iio (q' * M)).filter E).card = q' * A := by
      intro q'
      induction q' with
      | zero =>
        simp
      | succ q'' ih =>
        have h_split2 : Finset.Iio ((q'' + 1) * M) =
            Finset.Iio (q'' * M) ∪ Finset.Ico (q'' * M) ((q'' + 1) * M) := by
          have h_succ : (q'' + 1) * M = q'' * M + M := by ring
          ext n
          simp [Finset.mem_Iio, Finset.mem_Ico, Finset.mem_union, h_succ]
          omega
        have h_disj2 : Disjoint ((Finset.Iio (q'' * M)).filter E)
            ((Finset.Ico (q'' * M) ((q'' + 1) * M)).filter E) := by
          apply Finset.disjoint_left.mpr
          intro n hn1 hn2
          simp [Finset.mem_filter, Finset.mem_Iio] at hn1
          simp [Finset.mem_filter, Finset.mem_Ico] at hn2
          omega
        rw [h_split2, Finset.filter_union, Finset.card_union_of_disjoint h_disj2, ih]
        -- Need: ((Finset.Ico (q''*M) ((q''+1)*M)).filter E).card = A.
        -- Bijection r ↦ q''*M + r maps [0, M) to [q''*M, (q''+1)*M).
        have h_chunk : ((Finset.Ico (q'' * M) ((q'' + 1) * M)).filter E).card = A := by
          have h_succ' : (q'' + 1) * M = q'' * M + M := by ring
          have h_image : Finset.Ico (q'' * M) ((q'' + 1) * M) =
              (Finset.range M).image (fun r => q'' * M + r) := by
            ext n
            simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
            constructor
            · intro ⟨hge, hlt⟩
              refine ⟨n - q'' * M, ?_, ?_⟩ <;> omega
            · intro ⟨r, hr, hr_eq⟩
              omega
          rw [h_image, Finset.filter_image]
          rw [Finset.card_image_of_injOn (fun a _ b _ hab => by omega)]
          rw [hA_def]
          congr 1
          apply Finset.filter_congr
          intro n hn
          rw [Finset.mem_range] at hn
          exact hperiodic (q'' * M + n) n
            (by rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hn])
        rw [h_chunk]
        ring
    -- **h_upper (shift bijection):** ((Finset.Icc (q*M) X).filter E).card = cs.
    have h_upper : ((Finset.Icc (q * M) X).filter E).card = cs := by
      -- Icc (q*M) X has elements [q*M, q*M + s] (since X = q*M + s).
      -- Bijection r ↦ q*M + r maps [0, s] to [q*M, q*M+s].
      have h_image : Finset.Icc (q * M) X = (Finset.Iic s).image (fun r => q * M + r) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_Iic]
        constructor
        · intro ⟨hge, hle⟩
          refine ⟨n - q * M, ?_, ?_⟩ <;>
          · have hX : X = q * M + s := hX_eq
            omega
        · intro ⟨r, hr, hr_eq⟩
          have hX : X = q * M + s := hX_eq
          omega
      rw [h_image, Finset.filter_image]
      rw [Finset.card_image_of_injOn (fun a _ b _ hab => by omega)]
      rw [hcs_def]
      congr 1
      apply Finset.filter_congr
      intro n hn
      rw [Finset.mem_Iic] at hn
      have hn_lt_M : n < M := lt_of_le_of_lt hn hs_lt
      exact hperiodic (q * M + n) n
        (by rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hn_lt_M])
    rw [h_lower q, h_upper]
  -- Now bound: |count_X - x·p_prod| ≤ M.
  have h_count_X_real : (count_X : ℝ) = (q : ℝ) * (A : ℝ) + (cs : ℝ) := by
    rw [h_count_decomp]; push_cast; ring
  have hX_eq_real : (X : ℝ) = (q : ℝ) * (M : ℝ) + (s : ℝ) := by
    exact_mod_cast hX_eq
  have hs_real_lt : (s : ℝ) < (M : ℝ) := by exact_mod_cast hs_lt
  have hs_real_nonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.zero_le _
  -- |count_X - X · p_prod| = |cs - s · A/M| ≤ M.
  have h_diff_X : (count_X : ℝ) - (X : ℝ) * ((A : ℝ) / (M : ℝ)) =
      (cs : ℝ) - (s : ℝ) * ((A : ℝ) / (M : ℝ)) := by
    rw [h_count_X_real, hX_eq_real]
    field_simp
    ring
  have h_bound_aX : |(cs : ℝ) - (s : ℝ) * ((A : ℝ) / (M : ℝ))| ≤ (M : ℝ) := by
    rw [abs_le]
    constructor
    · -- -M ≤ cs - s·A/M.  cs ≥ 0, s·A/M ≤ s ≤ M-1 < M, so cs - s·A/M ≥ -s·A/M ≥ -(M-1) ≥ -M.
      have h1 : (s : ℝ) * ((A : ℝ) / (M : ℝ)) ≤ (s : ℝ) :=
        mul_le_of_le_one_right hs_real_nonneg
          (div_le_one_of_le₀ hA_real_le_M hM_real_pos.le)
      linarith
    · -- cs - s·A/M ≤ cs ≤ M.
      have h1 : 0 ≤ (s : ℝ) * ((A : ℝ) / (M : ℝ)) :=
        mul_nonneg hs_real_nonneg (div_nonneg hA_real_nonneg hM_real_pos.le)
      linarith
  -- Now |count_X - x·p_prod| ≤ M + p_prod ≤ M + 1.  Need ≤ M.  Use refined bound.
  -- count_X - x·p_prod = (count_X - X·p_prod) - (x - X)·p_prod
  -- = a(X) - (x-X)·p_prod  where a(X) := count_X - X·p_prod ∈ [-(M-1), M].
  -- Worst: a(X) = M, (x-X) = 0 (x = X): bound M.
  -- Worst: a(X) = -(M-1), (x-X) = 1: bound M-1 + 1 = M.
  -- So |count_X - x·p_prod| ≤ M.
  have h_diff_x : (count_X : ℝ) - x * ((A : ℝ) / (M : ℝ)) =
      ((count_X : ℝ) - (X : ℝ) * ((A : ℝ) / (M : ℝ))) -
        (x - (X : ℝ)) * ((A : ℝ) / (M : ℝ)) := by ring
  -- Bound count_X - x·p_prod ∈ (-M, M].
  have h_p_prod_le_one : (A : ℝ) / (M : ℝ) ≤ 1 :=
    div_le_one_of_le₀ hA_real_le_M hM_real_pos.le
  have h_p_prod_nonneg : 0 ≤ (A : ℝ) / (M : ℝ) :=
    div_nonneg hA_real_nonneg hM_real_pos.le
  have h_xX_nonneg : 0 ≤ x - (X : ℝ) := by linarith
  have h_xX_lt_one : x - (X : ℝ) < 1 := by linarith
  -- Refined bound: |count_X - x·p_prod| ≤ M.
  -- a(X) - (x-X)·p_prod where a(X) ∈ [-(M-1), M] (strict on left), (x-X)·p_prod ∈ [0, 1).
  -- So count_X - x·p_prod ∈ (-(M-1) - 1, M] = (-M, M].
  have h_aX_lower : -(M : ℝ) + 1 ≤ (count_X : ℝ) - (X : ℝ) * ((A : ℝ) / (M : ℝ)) := by
    rw [h_diff_X]
    -- cs - s·A/M ≥ 0 - (M-1)·1 = -(M-1) = -M + 1.
    have h1 : (s : ℝ) * ((A : ℝ) / (M : ℝ)) ≤ (M : ℝ) - 1 := by
      have hs_le : (s : ℝ) ≤ (M : ℝ) - 1 := by exact_mod_cast hs_le_M_minus_1
      calc (s : ℝ) * ((A : ℝ) / (M : ℝ))
          ≤ (s : ℝ) * 1 := mul_le_mul_of_nonneg_left h_p_prod_le_one hs_real_nonneg
        _ = (s : ℝ) := mul_one _
        _ ≤ (M : ℝ) - 1 := hs_le
    linarith
  have h_aX_upper : (count_X : ℝ) - (X : ℝ) * ((A : ℝ) / (M : ℝ)) ≤ (M : ℝ) := by
    rw [h_diff_X]; exact (abs_le.mp h_bound_aX).2
  -- |count_X - x·p_prod| ≤ M:
  have h_diff_x_bound : |(count_X : ℝ) - x * ((A : ℝ) / (M : ℝ))| ≤ (M : ℝ) := by
    rw [h_diff_x, abs_le]
    refine ⟨?_, ?_⟩
    · -- count_X - x·p_prod = a(X) - (x-X)·p_prod ≥ (-M+1) - 1·1 = -M.
      have h_xXp_le : (x - (X : ℝ)) * ((A : ℝ) / (M : ℝ)) ≤ 1 := by
        calc (x - (X : ℝ)) * ((A : ℝ) / (M : ℝ))
            ≤ 1 * 1 := mul_le_mul (le_of_lt h_xX_lt_one) h_p_prod_le_one
              h_p_prod_nonneg (by norm_num)
          _ = 1 := mul_one _
      linarith
    · -- count_X - x·p_prod = a(X) - (x-X)·p_prod ≤ M - 0 = M.
      have h_xXp_nonneg : 0 ≤ (x - (X : ℝ)) * ((A : ℝ) / (M : ℝ)) :=
        mul_nonneg h_xX_nonneg h_p_prod_nonneg
      linarith
  -- Divide by x: |count_X/x - p_prod| ≤ M/x.
  rw [show |(count_X : ℝ) / x - (A : ℝ) / (M : ℝ)| =
        |((count_X : ℝ) - x * ((A : ℝ) / (M : ℝ))) / x| from by
    congr 1
    field_simp]
  rw [abs_div, abs_of_pos hx_pos]
  exact div_le_div_of_nonneg_right h_diff_x_bound hx_pos.le

/-! ### Derived helpers: AP-reciprocal-prime sums (paper §2, §4 partial-summation bridges)

These are derived lemmas obtained from `siegel_walfisz` / `brun_titchmarsh`
via partial summation (Abel's summation formula).  Paper §2 eq:SW-reciprocal
and paper §4 eq:Sp-bound. -/

private noncomputable def apCoeffMod (q a n : ℕ) : ℝ :=
  if n.Prime ∧ n % q = a % q then 1 else 0

private lemma apCoeffMod_sum_eq_piMod (t : ℝ) (q a : ℕ) :
    (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apCoeffMod q a k) = (piMod t q a : ℝ) := by
  classical
  have hset : {p : ℕ | p ≤ ⌊t⌋₊ ∧ p.Prime ∧ p % q = a % q} =
      ↑((Finset.Icc 0 ⌊t⌋₊).filter (fun p => p.Prime ∧ p % q = a % q)) := by
    ext p
    simp [and_assoc]
  rw [piMod, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  simp [apCoeffMod, Finset.sum_ite]


private lemma sum_filter_eq_Ioc_indicator_real {q a : ℕ} {X Y : ℝ}
    (hXnonneg : 0 ≤ X) (hYnonneg : 0 ≤ Y) :
    (∑ p ∈ Finset.filter
        (fun p => p.Prime ∧ p % q = a % q ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ Y)
        (Finset.Iic ⌊Y⌋₊), (1 : ℝ) / (p : ℝ))
      = ∑ p ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊,
          ((1 : ℝ) / (p : ℝ)) * (if p.Prime ∧ p % q = a % q then (1 : ℝ) else 0) := by
  conv_rhs =>
    enter [2, p]
    rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
    constructor
    · rintro ⟨hp_floorY, hpprime, hpmod, hXp, _hpY⟩
      exact ⟨⟨(Nat.floor_lt hXnonneg).2 hXp, hp_floorY⟩, hpprime, hpmod⟩
    · rintro ⟨⟨hfloorX, hp_floorY⟩, hpprime, hpmod⟩
      exact ⟨hp_floorY, hpprime, hpmod,
        (Nat.floor_lt hXnonneg).1 hfloorX,
        (Nat.cast_le.mpr hp_floorY).trans (Nat.floor_le hYnonneg)⟩
  · intro p hp
    rfl

private lemma abel_AP_formula (q a : ℕ) {X Y : ℝ} (hX_pos : 0 < X) (hXY : X ≤ Y) :
    ∑ k ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, ((1 : ℝ) / (k : ℝ)) * apCoeffMod q a k =
      ((1 : ℝ) / Y) * (piMod Y q a : ℝ)
        - ((1 : ℝ) / X) * (piMod X q a : ℝ)
        - ∫ t in Set.Ioc X Y,
            deriv (fun u : ℝ => (1 : ℝ) / u) t * (piMod t q a : ℝ) := by
  have hX_nonneg : (0 : ℝ) ≤ X := hX_pos.le
  have hf_diff : ∀ t ∈ Set.Icc X Y,
      DifferentiableAt ℝ (fun u : ℝ => (1 : ℝ) / u) t := by
    intro t ht
    have htpos : 0 < t := hX_pos.trans_le ht.1
    have : t ≠ 0 := htpos.ne'
    fun_prop
  have hf_int : IntegrableOn (deriv (fun u : ℝ => (1 : ℝ) / u)) (Set.Icc X Y) := by
    have hcont : ContinuousOn (fun u : ℝ => - (u ^ 2)⁻¹) (Set.Icc X Y) := by
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀
      · exact (continuousOn_id.pow 2)
      · intro u hu hzero
        have hu_pos : 0 < u := hX_pos.trans_le hu.1
        exact (ne_of_gt hu_pos) (sq_eq_zero_iff.mp hzero)
    simpa [one_div, deriv_inv'] using hcont.integrableOn_Icc
  simpa [apCoeffMod_sum_eq_piMod] using
    (sum_mul_eq_sub_sub_integral_mul (c := apCoeffMod q a)
      (f := fun u : ℝ => (1 : ℝ) / u) hX_nonneg hXY hf_diff hf_int)

private lemma abel_AP_formula_interval (q a : ℕ) {X Y : ℝ} (hX_pos : 0 < X)
    (hXY : X ≤ Y) :
    ∑ k ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, ((1 : ℝ) / (k : ℝ)) * apCoeffMod q a k =
      ((1 : ℝ) / Y) * (piMod Y q a : ℝ)
        - ((1 : ℝ) / X) * (piMod X q a : ℝ)
        + ∫ t in X..Y, (piMod t q a : ℝ) / t ^ 2 := by
  have habel := abel_AP_formula q a hX_pos hXY
  have hint_eq :
      -∫ t in Set.Ioc X Y,
          deriv (fun u : ℝ => (1 : ℝ) / u) t * (piMod t q a : ℝ)
        = ∫ t in X..Y, (piMod t q a : ℝ) / t ^ 2 := by
    rw [← intervalIntegral.integral_of_le hXY, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht_pos : 0 < t := by
      have ht' : t ∈ Set.Icc X Y := by
        simpa [Set.uIcc_of_le hXY] using ht
      exact hX_pos.trans_le ht'.1
    simp [deriv_inv', div_eq_mul_inv, mul_comm]
  linarith

private lemma invLog_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun u : ℝ => (Real.log u)⁻¹) (Set.Icc a b) := by
  have hlog_cont : ContinuousOn (fun u : ℝ => Real.log u) (Set.Icc a b) := by
    exact Real.continuousOn_log.comp continuousOn_id (by
      intro u hu
      exact ne_of_gt ((lt_trans (by norm_num) ha).trans_le hu.1))
  exact hlog_cont.inv₀ (by
    intro u hu hzero
    have hlog_pos : 0 < Real.log u := Real.log_pos (ha.trans_le hu.1)
    exact (ne_of_gt hlog_pos) hzero)

private lemma invLog_continuousAt {t : ℝ} (ht : 1 < t) :
    ContinuousAt (fun u : ℝ => (Real.log u)⁻¹) t := by
  exact (Real.continuousAt_log (ne_of_gt (lt_trans (by norm_num) ht))).inv₀
    (ne_of_gt (Real.log_pos ht))

private lemma li_hasDerivAt {t : ℝ} (ht : 2 < t) :
    HasDerivAt li ((Real.log t)⁻¹) t := by
  unfold li
  have hcont_Icc : ContinuousOn (fun u : ℝ => (Real.log u)⁻¹) (Set.Icc (2 : ℝ) t) :=
    invLog_continuousOn (by norm_num)
  have hint : IntervalIntegrable (fun u : ℝ => (Real.log u)⁻¹) volume (2 : ℝ) t := by
    have hcont_u : ContinuousOn (fun u : ℝ => (Real.log u)⁻¹) (Set.uIcc (2 : ℝ) t) := by
      simpa [Set.uIcc_of_le ht.le] using hcont_Icc
    exact hcont_u.intervalIntegrable
  have ht1 : t ∈ Set.Ioi (1 : ℝ) := lt_trans (by norm_num) ht
  have hsm : StronglyMeasurableAtFilter (fun u : ℝ => (Real.log u)⁻¹) (nhds t) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun x hx => invLog_continuousAt hx) t ht1
  have hct : ContinuousAt (fun u : ℝ => (Real.log u)⁻¹) t := invLog_continuousAt ht1
  simpa [one_div] using intervalIntegral.integral_hasDerivAt_right hint hsm hct

private lemma li_continuousOn {X Y : ℝ} (hX : 3 ≤ X) :
    ContinuousOn li (Set.Icc X Y) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  exact (li_hasDerivAt (by linarith [ht.1])).continuousAt

private lemma li_div_continuousOn {X Y : ℝ} (hX : 3 ≤ X) :
    ContinuousOn (fun t : ℝ => li t / t) (Set.Icc X Y) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  have ht2 : 2 < t := by linarith [ht.1]
  have ht0 : t ≠ 0 := by positivity
  exact ((li_hasDerivAt ht2).div (hasDerivAt_id t) ht0).continuousAt

private lemma one_div_mul_log_continuousOn {X Y : ℝ} (hX : 3 ≤ X) :
    ContinuousOn (fun t : ℝ => 1 / (t * Real.log t)) (Set.Icc X Y) := by
  have hlog_cont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc X Y) := by
    exact Real.continuousOn_log.comp continuousOn_id (by
      intro t ht
      exact ne_of_gt (by linarith [hX, ht.1]))
  have hden : ∀ t ∈ Set.Icc X Y, t * Real.log t ≠ 0 := by
    intro t ht hzero
    exact mul_ne_zero (ne_of_gt (by linarith [hX, ht.1]))
      (ne_of_gt (Real.log_pos (by linarith [hX, ht.1]))) hzero
  exact continuousOn_const.div (continuousOn_id.mul hlog_cont) hden

private lemma li_div_sq_continuousOn {X Y : ℝ} (hX : 3 ≤ X) :
    ContinuousOn (fun t : ℝ => li t / t ^ 2) (Set.Icc X Y) := by
  have hli : ContinuousOn li (Set.Icc X Y) := li_continuousOn hX
  have hden2 : ∀ t ∈ Set.Icc X Y, t ^ 2 ≠ 0 := by
    intro t ht hzero
    exact (ne_of_gt (by linarith [hX, ht.1])) (sq_eq_zero_iff.mp hzero)
  exact hli.div (continuousOn_id.pow 2) hden2

private lemma main_kernel_continuousOn {X Y : ℝ} (hX : 3 ≤ X) :
    ContinuousOn (fun t : ℝ => 1 / (t * Real.log t) - li t / t ^ 2) (Set.Icc X Y) := by
  exact (one_div_mul_log_continuousOn hX).sub (li_div_sq_continuousOn hX)

private lemma li_div_hasDerivAt {t : ℝ} (ht : 2 < t) :
    HasDerivAt (fun u : ℝ => li u / u)
      (1 / (t * Real.log t) - li t / t ^ 2) t := by
  have ht0 : t ≠ 0 := by positivity
  have hlog_ne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  convert! (li_hasDerivAt ht).div (hasDerivAt_id t) ht0 using 1 <;>
    simp only [id_eq] <;> field_simp [ht0, hlog_ne]

private lemma intervalIntegrable_of_continuousOn_Icc {f : ℝ → ℝ} {X Y : ℝ}
    (hXY : X ≤ Y) (hf : ContinuousOn f (Set.Icc X Y)) :
    IntervalIntegrable f volume X Y := by
  have hfu : ContinuousOn f (Set.uIcc X Y) := by
    simpa [Set.uIcc_of_le hXY] using hf
  exact hfu.intervalIntegrable

private lemma li_partial_summation_main {X Y : ℝ} (hX : 3 ≤ X) (hXY : X ≤ Y) :
    (li Y / Y - li X / X) + ∫ t in X..Y, li t / t ^ 2 =
      ∫ t in X..Y, 1 / (t * Real.log t) := by
  have hFcont : ContinuousOn (fun t : ℝ => li t / t) (Set.Icc X Y) :=
    li_div_continuousOn hX
  have hderiv : ∀ t ∈ Set.Ioo X Y,
      HasDerivAt (fun u : ℝ => li u / u) (1 / (t * Real.log t) - li t / t ^ 2) t := by
    intro t ht
    exact li_div_hasDerivAt (by linarith [hX, ht.1])
  have hkcont : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t) - li t / t ^ 2)
      (Set.Icc X Y) := main_kernel_continuousOn hX
  have hkint : IntervalIntegrable
      (fun t : ℝ => 1 / (t * Real.log t) - li t / t ^ 2) volume X Y :=
    intervalIntegrable_of_continuousOn_Icc hXY hkcont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hXY hFcont hderiv hkint
  have h1int : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t)) volume X Y :=
    intervalIntegrable_of_continuousOn_Icc hXY (one_div_mul_log_continuousOn hX)
  have h2int : IntervalIntegrable (fun t : ℝ => li t / t ^ 2) volume X Y :=
    intervalIntegrable_of_continuousOn_Icc hXY (li_div_sq_continuousOn hX)
  have h_int_sub : (∫ t in X..Y, (1 / (t * Real.log t) - li t / t ^ 2)) =
      (∫ t in X..Y, 1 / (t * Real.log t)) - ∫ t in X..Y, li t / t ^ 2 := by
    rw [intervalIntegral.integral_sub h1int h2int]
  rw [h_int_sub] at hFTC
  linarith

private lemma piMod_div_sq_integrableOn_Icc (q a : ℕ) {X Y : ℝ} (hX_pos : 0 < X) :
    IntegrableOn (fun t : ℝ => (piMod t q a : ℝ) / t ^ 2) (Set.Icc X Y) := by
  have hX_nonneg : 0 ≤ X := hX_pos.le
  have hg_cont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc X Y) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht hzero
      have ht_pos : 0 < t := hX_pos.trans_le ht.1
      exact (ne_of_gt ht_pos) (sq_eq_zero_iff.mp hzero)
  have hg_int_on : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc X Y) :=
    hg_cont.integrableOn_Icc
  have hmul := integrableOn_mul_sum_Icc (c := apCoeffMod q a) (a := X) (b := Y) (m := 0)
    hX_nonneg hg_int_on
  convert hmul using 1
  ext t
  rw [apCoeffMod_sum_eq_piMod]
  simp [div_eq_mul_inv, mul_comm]

private lemma piMod_div_sq_intervalIntegrable (q a : ℕ) {X Y : ℝ} (hX_pos : 0 < X)
    (hXY : X ≤ Y) :
    IntervalIntegrable (fun t : ℝ => (piMod t q a : ℝ) / t ^ 2) volume X Y :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hXY).2
    (piMod_div_sq_integrableOn_Icc q a hX_pos)

private lemma tail_antideriv {c t : ℝ} (hc : 0 < c) (ht : 1 < t) :
    HasDerivAt
      (fun u : ℝ => -(2 / c) * (Real.sqrt (Real.log u) + 1 / c) *
        Real.exp (-c * Real.sqrt (Real.log u)))
      (Real.exp (-c * Real.sqrt (Real.log t)) / t) t := by
  have ht_pos : 0 < t := lt_trans (by norm_num) ht
  have hlog_pos : 0 < Real.log t := Real.log_pos ht
  have hsqrt_ne : Real.sqrt (Real.log t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlog_pos)
  have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hsqrt_deriv : HasDerivAt (fun u : ℝ => Real.sqrt (Real.log u))
      (t⁻¹ / (2 * Real.sqrt (Real.log t))) t := by
    exact (Real.hasDerivAt_log ht_ne).sqrt hlog_ne
  have hexp_deriv : HasDerivAt (fun u : ℝ => Real.exp (-c * Real.sqrt (Real.log u)))
      (Real.exp (-c * Real.sqrt (Real.log t)) *
        (-(c * (t⁻¹ / (2 * Real.sqrt (Real.log t)))))) t := by
    convert! (Real.hasDerivAt_exp (-c * Real.sqrt (Real.log t))).comp t
      ((hasDerivAt_const t (-c)).mul hsqrt_deriv) using 1
    · ring_nf
  have hprod := ((hasDerivAt_const t (-(2 / c))).mul
    ((hsqrt_deriv.add (hasDerivAt_const t (1 / c))).mul hexp_deriv))
  convert! hprod using 1
  · funext u
    simp only [Pi.add_apply, Pi.mul_apply]
    ring_nf
  · simp only [Pi.add_apply, Pi.mul_apply]
    field_simp [hc_ne, ht_ne, hsqrt_ne]
    ring_nf

private lemma tailKernel_continuousOn {c X Y : ℝ} (hX : 1 < X) :
    ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
      (Set.Icc X Y) := by
  have hlog_cont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc X Y) := by
    exact Real.continuousOn_log.comp continuousOn_id (by
      intro t ht
      exact ne_of_gt (lt_trans (by norm_num) (hX.trans_le ht.1)))
  have hsqrt_cont : ContinuousOn (fun t : ℝ => Real.sqrt (Real.log t)) (Set.Icc X Y) :=
    hlog_cont.sqrt
  have hnegc : ContinuousOn (fun t : ℝ => -c * Real.sqrt (Real.log t)) (Set.Icc X Y) :=
    continuousOn_const.mul hsqrt_cont
  have hexp_cont : ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)))
      (Set.Icc X Y) := by
    simpa [Function.comp_def] using Real.continuous_exp.comp_continuousOn hnegc
  exact hexp_cont.div continuousOn_id (by
    intro t ht
    exact ne_of_gt ((lt_trans (by norm_num) hX).trans_le ht.1))

private lemma tailAntideriv_continuousOn {c X Y : ℝ} (hX : 1 < X) :
    ContinuousOn
      (fun u : ℝ => -(2 / c) * (Real.sqrt (Real.log u) + 1 / c) *
        Real.exp (-c * Real.sqrt (Real.log u))) (Set.Icc X Y) := by
  have hlog_cont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc X Y) := by
    exact Real.continuousOn_log.comp continuousOn_id (by
      intro t ht
      exact ne_of_gt (lt_trans (by norm_num) (hX.trans_le ht.1)))
  have hsqrt_cont : ContinuousOn (fun t : ℝ => Real.sqrt (Real.log t)) (Set.Icc X Y) :=
    hlog_cont.sqrt
  have hnegc : ContinuousOn (fun t : ℝ => -c * Real.sqrt (Real.log t)) (Set.Icc X Y) :=
    continuousOn_const.mul hsqrt_cont
  have hexp_cont : ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)))
      (Set.Icc X Y) := by
    simpa [Function.comp_def] using Real.continuous_exp.comp_continuousOn hnegc
  exact (continuousOn_const.mul (hsqrt_cont.add continuousOn_const)).mul hexp_cont

private lemma tail_integral_le_exp {c X Y : ℝ} (hc : 0 < c) (hX3 : 3 ≤ X)
    (hXY : X ≤ Y) :
    (∫ t in X..Y, Real.exp (-c * Real.sqrt (Real.log t)) / t) ≤
      (6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  let F : ℝ → ℝ := fun u => -(2 / c) * (Real.sqrt (Real.log u) + 1 / c) *
        Real.exp (-c * Real.sqrt (Real.log u))
  let K : ℝ → ℝ := fun t => Real.exp (-c * Real.sqrt (Real.log t)) / t
  have hX1 : 1 < X := by linarith
  have hFcont : ContinuousOn F (Set.Icc X Y) := tailAntideriv_continuousOn (c := c) hX1
  have hderiv : ∀ t ∈ Set.Ioo X Y, HasDerivAt F (K t) t := by
    intro t ht
    exact tail_antideriv hc (hX1.trans ht.1)
  have hKint : IntervalIntegrable K volume X Y := by
    have hKcont : ContinuousOn K (Set.Icc X Y) := tailKernel_continuousOn (c := c) hX1
    have hKu : ContinuousOn K (Set.uIcc X Y) := by
      simpa [Set.uIcc_of_le hXY] using hKcont
    exact hKu.intervalIntegrable
  have heq : (∫ t in X..Y, K t) = F Y - F X :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hXY hFcont hderiv hKint
  have hY3 : 3 ≤ Y := hX3.trans hXY
  have hFY_nonpos : F Y ≤ 0 := by
    dsimp [F]
    have hsum_pos : 0 < Real.sqrt (Real.log Y) + 1 / c := by
      have : 0 < 1 / c := by positivity
      have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.log Y) := Real.sqrt_nonneg _
      linarith
    have hexp_pos : 0 < Real.exp (-c * Real.sqrt (Real.log Y)) := Real.exp_pos _
    have hcoef_pos : 0 < 2 / c := by positivity
    nlinarith [mul_pos (mul_pos hcoef_pos hsum_pos) hexp_pos]
  rw [heq]
  calc
    F Y - F X ≤ -F X := by linarith
    _ = (2 / c) * (Real.sqrt (Real.log X) + 1 / c) *
        Real.exp (-c * Real.sqrt (Real.log X)) := by
          dsimp [F]
          ring
    _ ≤ (6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
      let u := Real.sqrt (Real.log X)
      have hu_nonneg : 0 ≤ u := by dsimp [u]; exact Real.sqrt_nonneg _
      have hc_ne : c ≠ 0 := ne_of_gt hc
      have hcu_nonneg : 0 ≤ (c / 2) * u := by positivity
      have hinvc_nonneg : 0 ≤ 1 / c := by positivity
      have htwodivc_nonneg : 0 ≤ 2 / c := by positivity
      have hy_le_exp : (c / 2) * u ≤ Real.exp ((c / 2) * u) := by
        have h1 := Real.add_one_le_exp ((c / 2) * u)
        linarith
      have hu_le : u ≤ (2 / c) * Real.exp ((c / 2) * u) := by
        calc
          u = (2 / c) * ((c / 2) * u) := by field_simp [hc_ne]
          _ ≤ (2 / c) * Real.exp ((c / 2) * u) := by
            exact mul_le_mul_of_nonneg_left hy_le_exp htwodivc_nonneg
      have hone_le : 1 / c ≤ (1 / c) * Real.exp ((c / 2) * u) := by
        have h1exp : 1 ≤ Real.exp ((c / 2) * u) := Real.one_le_exp hcu_nonneg
        simpa using mul_le_mul_of_nonneg_left h1exp hinvc_nonneg
      have hsum_le : u + 1 / c ≤ (3 / c) * Real.exp ((c / 2) * u) := by
        calc
          u + 1 / c ≤ (2 / c) * Real.exp ((c / 2) * u) +
              (1 / c) * Real.exp ((c / 2) * u) := add_le_add hu_le hone_le
          _ = (3 / c) * Real.exp ((c / 2) * u) := by ring
      have hexp_nonneg : 0 ≤ Real.exp (-c * u) := Real.exp_nonneg _
      calc
        (2 / c) * (Real.sqrt (Real.log X) + 1 / c) *
            Real.exp (-c * Real.sqrt (Real.log X))
            = (2 / c) * (u + 1 / c) * Real.exp (-c * u) := rfl
        _ ≤ (2 / c) * ((3 / c) * Real.exp ((c / 2) * u)) * Real.exp (-c * u) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum_le htwodivc_nonneg) hexp_nonneg
        _ = (6 / c ^ 2) * (Real.exp ((c / 2) * u) * Real.exp (-c * u)) := by
          field_simp [hc_ne]
          ring
        _ = (6 / c ^ 2) * Real.exp (-(c / 2) * u) := by
          rw [← Real.exp_add]
          ring_nf
        _ = (6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := rfl

private lemma sw_log_power_mono {A X t : ℝ} {q : ℕ} (hA : 0 < A) (hX3 : 3 ≤ X)
    (hXt : X ≤ t) (hqX : (q : ℝ) ≤ (Real.log X) ^ A) :
    (q : ℝ) ≤ (Real.log t) ^ A := by
  have hXpos : 0 < X := by linarith
  have hlogX_nonneg : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogt_nonneg : 0 ≤ Real.log t := Real.log_nonneg (by linarith [hXt])
  have hlog_le : Real.log X ≤ Real.log t := Real.log_le_log hXpos hXt
  have hpow_le : (Real.log X) ^ A ≤ (Real.log t) ^ A := by
    exact (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hA.le)
      hlogX_nonneg hlogt_nonneg hlog_le
  exact hqX.trans hpow_le

private lemma sw_exp_decay_le_half {c X t : ℝ} (hc : 0 < c) (hX3 : 3 ≤ X)
    (hXt : X ≤ t) :
    Real.exp (-c * Real.sqrt (Real.log t)) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  apply Real.exp_le_exp.mpr
  have hXpos : 0 < X := by linarith
  have hlog_le : Real.log X ≤ Real.log t := Real.log_le_log hXpos hXt
  have hsqrt_le : Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log t) :=
    Real.sqrt_le_sqrt hlog_le
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.log X) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hsqrt_le hc.le]

private lemma sw_reciprocal_decomposition (q a : ℕ) {X Y : ℝ} (hX3 : 3 ≤ X)
    (hXY : X ≤ Y) :
    (∑ p ∈ Finset.filter
        (fun p => p.Prime ∧ p % q = a % q ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ Y)
        (Finset.Iic ⌊Y⌋₊), (1 : ℝ) / (p : ℝ))
      - (1 / (q.totient : ℝ)) * ∫ t in X..Y, 1 / (t * Real.log t)
      =
        (1 / Y) * ((piMod Y q a : ℝ) - li Y / (q.totient : ℝ))
          - (1 / X) * ((piMod X q a : ℝ) - li X / (q.totient : ℝ))
          + ∫ t in X..Y,
              ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2 := by
  have hX_pos : 0 < X := by linarith
  have hX_nonneg : 0 ≤ X := hX_pos.le
  have hY_nonneg : 0 ≤ Y := hX_nonneg.trans hXY
  have hsum_indicator := sum_filter_eq_Ioc_indicator_real (q := q) (a := a)
    (X := X) (Y := Y) hX_nonneg hY_nonneg
  have hsum :
      (∑ p ∈ Finset.filter
          (fun p => p.Prime ∧ p % q = a % q ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ Y)
          (Finset.Iic ⌊Y⌋₊), (1 : ℝ) / (p : ℝ))
        = ∑ p ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊,
            ((1 : ℝ) / (p : ℝ)) * apCoeffMod q a p := by
    simpa [apCoeffMod] using hsum_indicator
  have habel := abel_AP_formula_interval q a hX_pos hXY
  have hmain := li_partial_summation_main hX3 hXY
  have hpi_int : IntervalIntegrable (fun t : ℝ => (piMod t q a : ℝ) / t ^ 2)
      volume X Y := piMod_div_sq_intervalIntegrable q a hX_pos hXY
  have hli_int : IntervalIntegrable (fun t : ℝ => li t / t ^ 2) volume X Y :=
    intervalIntegrable_of_continuousOn_Icc hXY (li_div_sq_continuousOn hX3)
  have herror_int :
      (∫ t in X..Y, ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2)
        = (∫ t in X..Y, (piMod t q a : ℝ) / t ^ 2)
          - (1 / (q.totient : ℝ)) * ∫ t in X..Y, li t / t ^ 2 := by
    calc
      (∫ t in X..Y, ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2)
          = ∫ t in X..Y,
              (piMod t q a : ℝ) / t ^ 2 - (1 / (q.totient : ℝ)) * (li t / t ^ 2) := by
            apply intervalIntegral.integral_congr
            intro t _ht
            ring_nf
      _ = (∫ t in X..Y, (piMod t q a : ℝ) / t ^ 2)
          - ∫ t in X..Y, (1 / (q.totient : ℝ)) * (li t / t ^ 2) := by
            rw [intervalIntegral.integral_sub hpi_int (hli_int.const_mul _)]
      _ = (∫ t in X..Y, (piMod t q a : ℝ) / t ^ 2)
          - (1 / (q.totient : ℝ)) * ∫ t in X..Y, li t / t ^ 2 := by
            rw [intervalIntegral.integral_const_mul]
  rw [hsum, habel, ← hmain, herror_int]
  ring_nf

private lemma sw_integral_error_bound {A c C X Y : ℝ} {q a : ℕ}
    (hA : 0 < A) (hc : 0 < c) (hC : 0 < C)
    (hSW : ∀ t : ℝ, 2 ≤ t →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log t) ^ A →
        ∀ a : ℕ, Nat.Coprime a q →
          |((piMod t q a : ℝ)) - li t / (q.totient : ℝ)| ≤
            C * t * Real.exp (-c * Real.sqrt (Real.log t)))
    (hX3 : 3 ≤ X) (hXY : X ≤ Y) (hq1 : 1 ≤ q)
    (hqX : (q : ℝ) ≤ (Real.log X) ^ A) (ha : Nat.Coprime a q) :
    |∫ t in X..Y, ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2|
      ≤ C * (6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  have hX1 : 1 < X := by linarith
  have hkernel_cont :
      ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
        (Set.Icc X Y) := tailKernel_continuousOn (c := c) hX1
  have hkernel_u :
      ContinuousOn (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
        (Set.uIcc X Y) := by
    simpa [Set.uIcc_of_le hXY] using hkernel_cont
  have hkernel_int :
      IntervalIntegrable (fun t : ℝ => Real.exp (-c * Real.sqrt (Real.log t)) / t)
        volume X Y := hkernel_u.intervalIntegrable
  have hbound_int :
      IntervalIntegrable (fun t : ℝ => C * Real.exp (-c * Real.sqrt (Real.log t)) / t)
        volume X Y := by
    simpa [div_eq_mul_inv, mul_assoc] using hkernel_int.const_mul C
  have hpoint :
      ∀ᵐ t ∂volume, t ∈ Set.Ioc X Y →
        ‖((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2‖ ≤
          C * Real.exp (-c * Real.sqrt (Real.log t)) / t := by
    filter_upwards with t ht
    have hXt : X ≤ t := ht.1.le
    have ht2 : 2 ≤ t := by linarith
    have htpos : 0 < t := by linarith
    have hqt : (q : ℝ) ≤ (Real.log t) ^ A :=
      sw_log_power_mono hA hX3 hXt hqX
    have hsw := hSW t ht2 q hq1 hqt a ha
    have hdiv := div_le_div_of_nonneg_right hsw (by positivity : 0 ≤ t ^ 2)
    have hleft_eq : |↑(piMod t q a) - li t / ↑q.totient| / t ^ 2 =
        ‖((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2‖ := by
      rw [Real.norm_eq_abs]
      calc
        |↑(piMod t q a) - li t / ↑q.totient| / t ^ 2 =
            |↑(piMod t q a) - li t / ↑q.totient| / |t ^ 2| := by
              rw [abs_of_pos (sq_pos_of_pos htpos)]
        _ = |(↑(piMod t q a) - li t / ↑q.totient) / t ^ 2| := by
              rw [abs_div]
    have hright_eq : C * t * Real.exp (-c * Real.sqrt (Real.log t)) / t ^ 2 =
        C * Real.exp (-c * Real.sqrt (Real.log t)) / t := by
      field_simp [ne_of_gt htpos]
    rw [hleft_eq] at hdiv
    rw [hright_eq] at hdiv
    exact hdiv
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ t in X..Y, ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2‖
        ≤ ∫ t in X..Y, C * Real.exp (-c * Real.sqrt (Real.log t)) / t :=
          intervalIntegral.norm_integral_le_of_norm_le hXY hpoint hbound_int
    _ = C * ∫ t in X..Y, Real.exp (-c * Real.sqrt (Real.log t)) / t := by
          simp [div_eq_mul_inv, mul_assoc]
    _ ≤ C * ((6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X))) := by
          exact mul_le_mul_of_nonneg_left (tail_integral_le_exp hc hX3 hXY) hC.le
    _ = C * (6 / c ^ 2) * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
          ring

private lemma sw_boundary_error_bound {A c C X t : ℝ} {q a : ℕ}
    (hA : 0 < A) (hc : 0 < c) (hC : 0 < C)
    (hSW : ∀ t : ℝ, 2 ≤ t →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log t) ^ A →
        ∀ a : ℕ, Nat.Coprime a q →
          |((piMod t q a : ℝ)) - li t / (q.totient : ℝ)| ≤
            C * t * Real.exp (-c * Real.sqrt (Real.log t)))
    (hX3 : 3 ≤ X) (hXt : X ≤ t) (hq1 : 1 ≤ q)
    (hqX : (q : ℝ) ≤ (Real.log X) ^ A) (ha : Nat.Coprime a q) :
    |(1 / t) * ((piMod t q a : ℝ) - li t / (q.totient : ℝ))|
      ≤ C * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  have ht2 : 2 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have hqt : (q : ℝ) ≤ (Real.log t) ^ A :=
    sw_log_power_mono hA hX3 hXt hqX
  have hsw := hSW t ht2 q hq1 hqt a ha
  have hdiv := div_le_div_of_nonneg_right hsw htpos.le
  have hleft_eq :
      |(1 / t) * ((piMod t q a : ℝ) - li t / (q.totient : ℝ))|
        = |↑(piMod t q a) - li t / ↑q.totient| / t := by
    rw [abs_mul, abs_of_pos (one_div_pos.mpr htpos), div_eq_mul_inv]
    ring
  have hright_eq : C * t * Real.exp (-c * Real.sqrt (Real.log t)) / t =
      C * Real.exp (-c * Real.sqrt (Real.log t)) := by
    field_simp [ne_of_gt htpos]
  rw [← hleft_eq] at hdiv
  rw [hright_eq] at hdiv
  exact hdiv.trans (mul_le_mul_of_nonneg_left (sw_exp_decay_le_half hc hX3 hXt) hC.le)

/-- **Paper §2 eq:SW-reciprocal — exact paper statement.**

For every `A₀ > 0` there exist `c₀ > 0` (and an implied constant) such that,
for all `3 ≤ X ≤ Y`, every `q ≤ (log X)^{A₀}` with `(a, q) = 1`,
`∑_{X < p ≤ Y, p ≡ a mod q, p prime} 1/p
   = (1/φ(q)) · ∫_X^Y dt/(t log t) + O_{A₀}(exp(-c₀ √(log X)))`.

Proof: partial summation on `π(t; q, a)` + `siegel_walfisz`. -/
theorem sw_reciprocal_AP [SiegelWalfisz] :
    ∀ A₀ : ℝ, 0 < A₀ →
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ X Y : ℝ, 3 ≤ X → X ≤ Y →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ A₀ →
            ∀ a : ℕ, Nat.Coprime a q →
              |(∑ p ∈ Finset.filter
                  (fun p => p.Prime ∧ p % q = a % q ∧
                    X < (p : ℝ) ∧ (p : ℝ) ≤ Y)
                  (Finset.Iic ⌊Y⌋₊),
                (1 : ℝ) / (p : ℝ))
                - (1 / (q.totient : ℝ)) * ∫ t in X..Y, 1 / (t * Real.log t)|
              ≤ C * Real.exp (-c₀ * Real.sqrt (Real.log X)) := by
  classical
  intro A₀ hA₀
  rcases siegel_walfisz A₀ hA₀ with ⟨c, hc, Csw, hCsw, hSW⟩
  let c₀ : ℝ := c / 2
  let C : ℝ := Csw * (2 + 6 / c ^ 2)
  refine ⟨c₀, ?_, C, ?_, ?_⟩
  · dsimp [c₀]
    positivity
  · dsimp [C]
    positivity
  · intro X Y hX3 hXY q hq1 hqX a ha
    have hdecomp := sw_reciprocal_decomposition q a hX3 hXY
    rw [hdecomp]
    set E : ℝ := Real.exp (-(c / 2) * Real.sqrt (Real.log X))
    set u : ℝ := (1 / Y) * ((piMod Y q a : ℝ) - li Y / (q.totient : ℝ))
    set v : ℝ := (1 / X) * ((piMod X q a : ℝ) - li X / (q.totient : ℝ))
    set w : ℝ := ∫ t in X..Y, ((piMod t q a : ℝ) - li t / (q.totient : ℝ)) / t ^ 2
    change |u - v + w| ≤ C * E
    have hu : |u| ≤ Csw * E := by
      dsimp [u, E]
      exact sw_boundary_error_bound hA₀ hc hCsw hSW hX3 hXY hq1 hqX ha
    have hv : |v| ≤ Csw * E := by
      dsimp [v, E]
      exact sw_boundary_error_bound hA₀ hc hCsw hSW hX3 le_rfl hq1 hqX ha
    have hw : |w| ≤ Csw * (6 / c ^ 2) * E := by
      dsimp [w, E]
      exact sw_integral_error_bound hA₀ hc hCsw hSW hX3 hXY hq1 hqX ha
    have htri : |u - v + w| ≤ |u| + |v| + |w| := by
      have h1 : |u - v| ≤ |u| + |v| := by
        simpa [sub_eq_add_neg] using abs_add_le u (-v)
      have h2 : |u - v + w| ≤ |u - v| + |w| := abs_add_le (u - v) w
      nlinarith
    calc
      |u - v + w| ≤ |u| + |v| + |w| := htri
      _ ≤ Csw * E + Csw * E + Csw * (6 / c ^ 2) * E := by
        nlinarith [hu, hv, hw]
      _ = C * E := by
        dsimp [C]
        ring


private noncomputable def apCoeff (p n : ℕ) : ℝ :=
  if n.Prime ∧ n % p = 1 % p then 1 else 0

private lemma apCoeff_sum_eq_piMod (t : ℝ) (p : ℕ) :
    (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, apCoeff p k) = (piMod t p 1 : ℝ) := by
  simpa only [apCoeff, apCoeffMod] using apCoeffMod_sum_eq_piMod t p 1


private lemma low_AP_sum_le_inv {p : ℕ} (hp : p.Prime) :
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (2 * p : ℝ))
        (Finset.Iic (2 * p)), (1 : ℝ) / (q : ℝ)) ≤ 1 / (p : ℝ) := by
  classical
  let s := Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (2 * p : ℝ))
        (Finset.Iic (2 * p))
  have hs_card : s.card ≤ 1 := by
    calc
      s.card = Nat.card s := (Nat.card_eq_finsetCard s).symm
      _ ≤ Nat.card Unit := by
        refine Nat.card_le_card_of_injective (fun _ : s => ()) ?_
        intro x y _
        ext
        have hxmem := x.2
        have hymem := y.2
        simp only [s, Finset.mem_filter, Finset.mem_Iic] at hxmem hymem
        have hxle2 : x.1 ≤ 2 * p := hxmem.1
        have hyle2 : y.1 ≤ 2 * p := hymem.1
        have hxmod : x.1 % p = 1 := hxmem.2.2.1
        have hymod : y.1 % p = 1 := hymem.2.2.1
        have hx_eq : x.1 = p + 1 := by
          have hq_eq : x.1 = p * (x.1 / p) + x.1 % p := (Nat.div_add_mod x.1 p).symm
          have hxle2' : x.1 ≤ p * 2 := by omega
          have hdivle : x.1 / p ≤ 2 := Nat.div_le_of_le_mul hxle2'
          have hxne1 : x.1 ≠ 1 := hxmem.2.1.ne_one
          interval_cases h : x.1 / p <;> simp [hxmod] at hq_eq <;> omega
        have hy_eq : y.1 = p + 1 := by
          have hq_eq : y.1 = p * (y.1 / p) + y.1 % p := (Nat.div_add_mod y.1 p).symm
          have hyle2' : y.1 ≤ p * 2 := by omega
          have hdivle : y.1 / p ≤ 2 := Nat.div_le_of_le_mul hyle2'
          have hyne1 : y.1 ≠ 1 := hymem.2.1.ne_one
          interval_cases h : y.1 / p <;> simp [hymod] at hq_eq <;> omega
        omega
      _ = 1 := by simp
  have hterm : ∀ q ∈ s, (1 : ℝ) / (q : ℝ) ≤ 1 / (p : ℝ) := by
    intro q hq
    have hqmem := hq
    simp only [s, Finset.mem_filter, Finset.mem_Iic] at hqmem
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq_gt : (p : ℝ) < q := hqmem.2.2.2.1
    exact one_div_le_one_div_of_le hp_pos hq_gt.le
  calc
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (2 * p : ℝ))
        (Finset.Iic (2 * p)), (1 : ℝ) / (q : ℝ)) = ∑ q ∈ s, (1 : ℝ) / (q : ℝ) := rfl
    _ ≤ s.card • (1 / (p : ℝ)) := Finset.sum_le_card_nsmul s (fun q => (1 : ℝ) / q) _ hterm
    _ ≤ 1 / (p : ℝ) := by
      rw [nsmul_eq_mul]
      have hinv_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
      have hcardreal : (s.card : ℝ) ≤ 1 := by exact_mod_cast hs_card
      nlinarith

private lemma integral_inv_mul_log_div {p a b : ℝ} (hp : 0 < p) (ha : p < a)
    (hab : a ≤ b) :
    (∫ t in a..b, (t * Real.log (t / p))⁻¹) =
      Real.log (Real.log (b / p)) - Real.log (Real.log (a / p)) := by
  have hf_cont : ContinuousOn (fun u : ℝ => Real.log (Real.log (u / p))) (Set.Icc a b) := by
    apply ContinuousOn.log
    · apply ContinuousOn.log
      · exact continuousOn_id.div_const p
      · intro t ht
        have ht_pos : 0 < t := (lt_trans hp ha).trans_le ht.1
        exact div_ne_zero (ne_of_gt ht_pos) (ne_of_gt hp)
    · intro t ht
      have htp_gt1 : 1 < t / p := (one_lt_div hp).2 (ha.trans_le ht.1)
      exact ne_of_gt (Real.log_pos htp_gt1)
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun u : ℝ => Real.log (Real.log (u / p))) ((t * Real.log (t / p))⁻¹) t := by
    intro t ht
    have ht_pos : 0 < t := (lt_trans hp ha).trans ht.1
    have htp_gt1 : 1 < t / p := (one_lt_div hp).2 (ha.trans ht.1)
    have hlog_ne : Real.log (t / p) ≠ 0 := ne_of_gt (Real.log_pos htp_gt1)
    have hp_ne : p ≠ 0 := ne_of_gt hp
    convert! ((Real.hasDerivAt_log hlog_ne).comp t
      (((Real.hasDerivAt_log (div_ne_zero (ne_of_gt ht_pos) hp_ne)).comp t
        ((hasDerivAt_id t).div_const p)))) using 1
    field_simp [hp_ne, hlog_ne]
  have hg_cont : ContinuousOn (fun t : ℝ => (t * Real.log (t / p))⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul ((Real.continuousOn_log.comp (continuousOn_id.div_const p))
        (by
          intro t ht
          exact div_ne_zero (ne_of_gt ((lt_trans hp ha).trans_le ht.1)) (ne_of_gt hp)))
    · intro t ht hzero
      have ht_pos : 0 < t := (lt_trans hp ha).trans_le ht.1
      have hlog_pos : 0 < Real.log (t / p) :=
        Real.log_pos ((one_lt_div hp).2 (ha.trans_le ht.1))
      exact mul_ne_zero (ne_of_gt ht_pos) (ne_of_gt hlog_pos) hzero
  have hg_cont_u : ContinuousOn (fun t : ℝ => (t * Real.log (t / p))⁻¹) (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hg_cont
  have hint : IntervalIntegrable (fun t : ℝ => (t * Real.log (t / p))⁻¹) volume a b :=
    hg_cont_u.intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hf_cont hderiv hint

private lemma tail_integral_le {CBT : ℝ} {p : ℕ} {Q : ℝ} (hCBT : 0 < CBT)
    (hp : p.Prime) (hQ : (256 : ℝ) * (p : ℝ) ^ 9 ≤ Q)
    (hBT : ∀ t : ℝ, (256 : ℝ) * (p : ℝ) ^ 9 ≤ t →
      (piMod t p 1 : ℝ) ≤ CBT * t / (((p - 1 : ℕ) : ℝ) * Real.log (t / p))) :
    (∫ t in Set.Ioc ((256 : ℝ) * (p : ℝ) ^ 9) Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ)) ≤
      (CBT / ((p - 1 : ℕ) : ℝ)) *
        (Real.log (Real.log (Q / p)) -
          Real.log (Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p))) := by
  let a : ℝ := (256 : ℝ) * (p : ℝ) ^ 9
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp_ge_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have ha_nonneg : 0 ≤ a := ha_pos.le
  -- `a / p = 256 p⁸ ≥ 256 ≥ 2`
  have ha_div_ge : (256 : ℝ) ≤ a / (p : ℝ) := by
    dsimp [a]
    rw [le_div_iff₀ hp_pos]
    have hp8 : (1 : ℝ) ≤ (p : ℝ) ^ 8 := by
      have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
      exact one_le_pow₀ this
    nlinarith [hp_pos, hp8]
  have ha_div_ge_two : (2 : ℝ) ≤ a / (p : ℝ) := le_trans (by norm_num) ha_div_ge
  have ha_gt : (p : ℝ) < a := by
    have := (le_div_iff₀ hp_pos).mp ha_div_ge_two
    linarith
  have hpminus_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hp.one_lt)
  have hg_left_cont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a Q) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht hzero
      have ht_pos : 0 < t := ha_pos.trans_le ht.1
      exact (ne_of_gt ht_pos) (sq_eq_zero_iff.mp hzero)
  have hg_left_int_on : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a Q) :=
    hg_left_cont.integrableOn_Icc
  have hleft_on : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹ * (piMod t p 1 : ℝ)) (Set.Icc a Q) := by
    simpa [apCoeff_sum_eq_piMod] using
      (integrableOn_mul_sum_Icc (c := apCoeff p) (a := a) (b := Q) (m := 0)
        ha_nonneg hg_left_int_on)
  have hleft_int :
      IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹ * (piMod t p 1 : ℝ)) volume a Q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hQ).2 hleft_on
  have hkernel_cont : ContinuousOn (fun t : ℝ => (t * Real.log (t / p))⁻¹) (Set.Icc a Q) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul ((Real.continuousOn_log.comp (continuousOn_id.div_const (p : ℝ)))
        (by
          intro t ht
          have ht_pos : 0 < t := ha_pos.trans_le ht.1
          exact div_ne_zero (ne_of_gt ht_pos) (ne_of_gt hp_pos)))
    · intro t ht hzero
      have ht_pos : 0 < t := ha_pos.trans_le ht.1
      have ht_ge_a : a ≤ t := ht.1
      have ht_div_ge_two : 2 ≤ t / (p : ℝ) :=
        le_trans ha_div_ge_two ((div_le_div_iff_of_pos_right hp_pos).mpr ht_ge_a)
      have hlog_pos : 0 < Real.log (t / p) :=
        Real.log_pos (lt_of_lt_of_le (by norm_num) ht_div_ge_two)
      exact mul_ne_zero (ne_of_gt ht_pos) (ne_of_gt hlog_pos) hzero
  have hright_on :
      IntegrableOn (fun t : ℝ => (CBT / ((p - 1 : ℕ) : ℝ)) * (t * Real.log (t / p))⁻¹)
        (Set.Icc a Q) :=
    (continuousOn_const.mul hkernel_cont).integrableOn_Icc
  have hright_int :
      IntervalIntegrable
        (fun t : ℝ => (CBT / ((p - 1 : ℕ) : ℝ)) * (t * Real.log (t / p))⁻¹) volume a Q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hQ).2 hright_on
  rw [← intervalIntegral.integral_of_le hQ]
  have hmono : (∫ t in a..Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ)) ≤
      ∫ t in a..Q, (CBT / ((p - 1 : ℕ) : ℝ)) * (t * Real.log (t / p))⁻¹ := by
    apply intervalIntegral.integral_mono_on hQ hleft_int hright_int
    intro t ht
    have ht_ge_a : a ≤ t := ht.1
    have ht_pos : 0 < t := ha_pos.trans_le ht_ge_a
    have hpi := hBT t ht_ge_a
    have ht_div_ge_two : 2 ≤ t / (p : ℝ) :=
      le_trans ha_div_ge_two ((div_le_div_iff_of_pos_right hp_pos).mpr ht_ge_a)
    have hlog_pos : 0 < Real.log (t / p) :=
      Real.log_pos (lt_of_lt_of_le (by norm_num) ht_div_ge_two)
    have ht2_pos : 0 < t ^ 2 := sq_pos_of_pos ht_pos
    calc
      (t ^ 2)⁻¹ * (piMod t p 1 : ℝ) ≤
          (t ^ 2)⁻¹ * (CBT * t / (((p - 1 : ℕ) : ℝ) * Real.log (t / p))) := by
        exact mul_le_mul_of_nonneg_left hpi (inv_nonneg.mpr ht2_pos.le)
      _ = (CBT / ((p - 1 : ℕ) : ℝ)) * (t * Real.log (t / p))⁻¹ := by
        field_simp [ne_of_gt ht_pos, ne_of_gt hpminus_pos, ne_of_gt hlog_pos]
  refine hmono.trans_eq ?_
  calc
    (∫ t in a..Q, (CBT / ((p - 1 : ℕ) : ℝ)) * (t * Real.log (t / p))⁻¹)
      = (CBT / ((p - 1 : ℕ) : ℝ)) *
        (Real.log (Real.log (Q / p)) - Real.log (Real.log (a / p))) := by
          rw [intervalIntegral.integral_const_mul]
          rw [integral_inv_mul_log_div hp_pos ha_gt hQ]
    _ = (CBT / ((p - 1 : ℕ) : ℝ)) *
        (Real.log (Real.log (Q / p)) -
          Real.log (Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p))) := by
          rfl

private lemma high_AP_sum_le_explicit {CBT : ℝ} {p : ℕ} {Q : ℝ} (hCBT : 0 < CBT)
    (hp : p.Prime) (hQ : (256 : ℝ) * (p : ℝ) ^ 9 ≤ Q)
    (hBT : ∀ t : ℝ, (256 : ℝ) * (p : ℝ) ^ 9 ≤ t →
      (piMod t p 1 : ℝ) ≤ CBT * t / (((p - 1 : ℕ) : ℝ) * Real.log (t / p))) :
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (256 : ℝ) * (p : ℝ) ^ 9 < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
      CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) +
        (CBT / ((p - 1 : ℕ) : ℝ)) *
          (Real.log (Real.log (Q / p)) -
            Real.log (Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p))) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp_ge_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  set a : ℝ := (256 : ℝ) * (p : ℝ) ^ 9 with ha_def
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have ha_div_ge : (256 : ℝ) ≤ a / (p : ℝ) := by
    dsimp [a]
    rw [le_div_iff₀ hp_pos]
    have hp8 : (1 : ℝ) ≤ (p : ℝ) ^ 8 := by
      have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
      exact one_le_pow₀ this
    nlinarith [hp_pos, hp8]
  have ha_div_ge_two : (2 : ℝ) ≤ a / (p : ℝ) := le_trans (by norm_num) ha_div_ge
  have hQ_pos : 0 < Q := ha_pos.trans_le hQ
  have hQnonneg : 0 ≤ Q := hQ_pos.le
  have hp1 : 1 % p = 1 % p := rfl
  have hBTQ := hBT Q hQ
  have hpminus_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hp.one_lt)
  have hQdiv_ge_two : (2 : ℝ) ≤ Q / p :=
    le_trans ha_div_ge_two ((div_le_div_iff_of_pos_right hp_pos).mpr hQ)
  have hQdivlog_pos : 0 < Real.log (Q / p) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hQdiv_ge_two)
  have hboundary :
      ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ) ≤
        CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) := by
    calc
      ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ) ≤
          (1 / Q) * (CBT * Q / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p))) := by
        exact mul_le_mul_of_nonneg_left hBTQ (by positivity)
      _ = CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) := by
        field_simp [ne_of_gt hQ_pos]
  have hint := tail_integral_le hCBT hp hQ hBT
  -- Boundary at lower endpoint: piMod a p 1 ≥ 0, so (1/a)·piMod(a) ≥ 0
  have hpiMod_a_nonneg : (0 : ℝ) ≤ (piMod a p 1 : ℝ) := by
    exact_mod_cast (Nat.zero_le _)
  -- apCoeff p = apCoeffMod p 1
  have hapCoeff_eq : (fun n => apCoeff p n) = (fun n => apCoeffMod p 1 n) := by
    funext n
    rfl
  -- Use abel_AP_formula_interval to get the boundary integral
  have habel := abel_AP_formula_interval p 1 (show (0 : ℝ) < a from ha_pos) hQ
  -- Recast sum from `Ioc ⌊a⌋ ⌊Q⌋` to apCoeff form
  have hsum_eq : ∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊Q⌋₊, ((1 : ℝ) / (q : ℝ)) * apCoeff p q =
      ∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊Q⌋₊, ((1 : ℝ) / (q : ℝ)) * apCoeffMod p 1 q := by
    apply Finset.sum_congr rfl
    intro q _
    rfl
  have habel' : ∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊Q⌋₊, ((1 : ℝ) / (q : ℝ)) * apCoeff p q =
      ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ)
        - ((1 : ℝ) / a) * (piMod a p 1 : ℝ)
        + ∫ t in a..Q, (piMod t p 1 : ℝ) / t ^ 2 := by
    rw [hsum_eq]; exact habel
  -- Convert interval integral to set integral
  have hQ_ge_a : a ≤ Q := hQ
  have hint_conv : (∫ t in a..Q, (piMod t p 1 : ℝ) / t ^ 2) =
      ∫ t in Set.Ioc a Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ) := by
    rw [intervalIntegral.integral_of_le hQ_ge_a]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _ht
    simp [div_eq_mul_inv, mul_comm]
  rw [hint_conv] at habel'
  calc
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (256 : ℝ) * (p : ℝ) ^ 9 < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ))
        = (∑ q ∈ Finset.filter
            (fun q => q.Prime ∧ q % p = 1 % p ∧ a < (q : ℝ) ∧ (q : ℝ) ≤ Q)
            (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) := by
          apply Finset.sum_congr
          · ext q
            simp only [Finset.mem_filter, Finset.mem_Iic, ha_def]
            constructor
            · rintro ⟨hq, hprime, hmod, hlt, hle⟩
              refine ⟨hq, hprime, ?_, hlt, hle⟩
              rw [hmod]
              exact (Nat.mod_eq_of_lt hp.one_lt).symm
            · rintro ⟨hq, hprime, hmod, hlt, hle⟩
              refine ⟨hq, hprime, ?_, hlt, hle⟩
              have : 1 % p = 1 := Nat.mod_eq_of_lt hp.one_lt
              rw [hmod, this]
          · intros; rfl
    _ = ∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊Q⌋₊,
          ((1 : ℝ) / (q : ℝ)) * (if q.Prime ∧ q % p = 1 % p then (1 : ℝ) else 0) := by
          exact sum_filter_eq_Ioc_indicator_real (q := p) (a := 1)
            (X := a) (Y := Q) ha_nonneg hQnonneg
    _ = ∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊Q⌋₊, ((1 : ℝ) / (q : ℝ)) * apCoeff p q := by
          apply Finset.sum_congr rfl
          intro q _
          rfl
    _ = ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ)
          - ((1 : ℝ) / a) * (piMod a p 1 : ℝ)
          + ∫ t in Set.Ioc a Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ) := habel'
    _ ≤ ((1 : ℝ) / Q) * (piMod Q p 1 : ℝ)
          + ∫ t in Set.Ioc a Q, (t ^ 2)⁻¹ * (piMod t p 1 : ℝ) := by
          have : 0 ≤ ((1 : ℝ) / a) * (piMod a p 1 : ℝ) := by
            apply mul_nonneg
            · positivity
            · exact hpiMod_a_nonneg
          linarith
    _ ≤ CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) +
        (CBT / ((p - 1 : ℕ) : ℝ)) *
          (Real.log (Real.log (Q / p)) -
            Real.log (Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p))) := by
          have := hint
          linarith

private lemma total_AP_sum_le_low_add_high {p : ℕ} {Q : ℝ} :
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
      (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (2 * p : ℝ))
        (Finset.Iic (2 * p)), (1 : ℝ) / (q : ℝ)) +
      (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) := by
  classical
  let s := Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊)
  let slow := Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ (2 * p : ℝ))
        (Finset.Iic (2 * p))
  let shigh := Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
        (Finset.Iic ⌊Q⌋₊)
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun q => q ≤ 2 * p)
    (f := fun q => (1 : ℝ) / (q : ℝ))
  rw [← hsplit]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      simp only [s, Finset.mem_filter, Finset.mem_Iic] at hq ⊢
      exact ⟨hq.2, hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1,
        by exact_mod_cast hq.2⟩
    · intro q hq _hnot
      positivity
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      simp only [s, Finset.mem_filter, Finset.mem_Iic] at hq ⊢
      have hlt : 2 * p < q := Nat.lt_of_not_ge hq.2
      exact ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, by exact_mod_cast hlt, hq.1.2.2.2.2⟩
    · intro q hq _hnot
      positivity

private lemma explicit_tail_bound {CBT : ℝ} {p : ℕ} (hCBT : 0 < CBT) (hp : p.Prime) :
    let A : ℝ := (p : ℝ) / (Real.log p) ^ 2
    let Q : ℝ := Real.exp (Real.exp A)
    (256 : ℝ) * (p : ℝ) ^ 9 ≤ Q →
      CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) +
        (CBT / ((p - 1 : ℕ) : ℝ)) *
          (Real.log (Real.log (Q / p)) -
            Real.log (Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p))) ≤
      (2 * CBT / Real.log 2) * (1 / (p : ℝ)) +
        2 * CBT * (1 / (Real.log p) ^ 2) := by
  intro A Q hQ
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp_ge_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp_ge : Real.log 2 ≤ Real.log (p : ℝ) := by
    exact Real.log_le_log (by norm_num) hp_ge_two
  have hlogp_pos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le hlog2_pos hlogp_ge
  have hlogpsq_pos : 0 < (Real.log (p : ℝ)) ^ 2 := sq_pos_of_pos hlogp_pos
  have hpminus_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hp.one_lt)
  have hQ_pos : 0 < Q := by dsimp [Q]; positivity
  -- a / p ≥ 256 ≥ 2
  have ha_div_ge : (256 : ℝ) ≤ ((256 : ℝ) * (p : ℝ) ^ 9) / (p : ℝ) := by
    rw [le_div_iff₀ hp_pos]
    have hp8 : (1 : ℝ) ≤ (p : ℝ) ^ 8 := by
      have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
      exact one_le_pow₀ this
    nlinarith [hp_pos, hp8]
  have ha_div_ge_two : (2 : ℝ) ≤ ((256 : ℝ) * (p : ℝ) ^ 9) / (p : ℝ) :=
    le_trans (by norm_num) ha_div_ge
  have hQdiv_ge_two : (2 : ℝ) ≤ Q / p :=
    le_trans ha_div_ge_two ((div_le_div_iff_of_pos_right hp_pos).mpr hQ)
  have hlogQp_ge_log2 : Real.log 2 ≤ Real.log (Q / p) :=
    Real.log_le_log (by norm_num) hQdiv_ge_two
  have hterm1 : CBT / (((p - 1 : ℕ) : ℝ) * Real.log (Q / p)) ≤
      (2 * CBT / Real.log 2) * (1 / (p : ℝ)) := by
    have hLpos : 0 < Real.log (Q / p) := lt_of_lt_of_le hlog2_pos hlogQp_ge_log2
    have hp_le_nat : p ≤ 2 * (p - 1) := by
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have hp_le : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hp_le_nat
    field_simp [ne_of_gt hp_pos, ne_of_gt hpminus_pos, ne_of_gt hlog2_pos, ne_of_gt hLpos]
    nlinarith [hCBT.le, hp_le, hlogQp_ge_log2]
  have hQdiv_pos : 0 < Q / p := lt_of_lt_of_le (by norm_num) hQdiv_ge_two
  have hp_ge_one : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hQdiv_le_Q : Q / (p : ℝ) ≤ Q := by
    rw [div_le_iff₀ hp_pos]
    nlinarith [mul_le_mul_of_nonneg_left hp_ge_one hQ_pos.le]
  have hlog_le : Real.log (Q / p) ≤ Real.log Q := Real.log_le_log hQdiv_pos hQdiv_le_Q
  have hlogQ : Real.log Q = Real.exp A := by simp [Q]
  have hloglog_le_A : Real.log (Real.log (Q / p)) ≤ A := by
    calc
      Real.log (Real.log (Q / p)) ≤ Real.log (Real.log Q) := by
        exact Real.log_le_log (lt_of_lt_of_le hlog2_pos hlogQp_ge_log2) hlog_le
      _ = A := by simp [hlogQ]
  -- log log ((256·p⁹)/p) ≥ 0 because (256·p⁹)/p ≥ 256 ≥ e², so log ≥ 2 ≥ 1
  have hlog_a_div_ge : (1 : ℝ) ≤ Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p) := by
    have hlog256_ge : (1 : ℝ) ≤ Real.log (256 : ℝ) := by
      have : Real.log (Real.exp 1) ≤ Real.log (256 : ℝ) := by
        apply Real.log_le_log (Real.exp_pos _)
        have : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
        linarith
      simpa using this
    have hmono : Real.log (256 : ℝ) ≤ Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p) := by
      apply Real.log_le_log (by norm_num) ha_div_ge
    linarith
  have hloglog_a_nonneg : 0 ≤ Real.log (Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p)) := by
    have : Real.log 1 ≤ Real.log (Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p)) :=
      Real.log_le_log (by norm_num) hlog_a_div_ge
    simpa using this
  have hB_le : Real.log (Real.log (Q / p)) -
      Real.log (Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p)) ≤ A := by
    linarith
  have hcoef_nonneg : 0 ≤ CBT / ((p - 1 : ℕ) : ℝ) := div_nonneg hCBT.le hpminus_pos.le
  have hcoef_le : CBT / ((p - 1 : ℕ) : ℝ) ≤ 2 * CBT / (p : ℝ) := by
    have hp_le_nat : p ≤ 2 * (p - 1) := by
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have hp_le : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hp_le_nat
    field_simp [ne_of_gt hp_pos, ne_of_gt hpminus_pos]
    nlinarith [hCBT.le, hp_le]
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hterm2 : (CBT / ((p - 1 : ℕ) : ℝ)) *
        (Real.log (Real.log (Q / p)) -
          Real.log (Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p))) ≤
      2 * CBT * (1 / (Real.log p) ^ 2) := by
    calc
      (CBT / ((p - 1 : ℕ) : ℝ)) *
          (Real.log (Real.log (Q / p)) -
            Real.log (Real.log (((256 : ℝ) * (p : ℝ) ^ 9) / p)))
          ≤ (CBT / ((p - 1 : ℕ) : ℝ)) * A := by
            exact mul_le_mul_of_nonneg_left hB_le hcoef_nonneg
      _ ≤ (2 * CBT / (p : ℝ)) * A := by
            exact mul_le_mul_of_nonneg_right hcoef_le hA_nonneg
      _ = 2 * CBT * (1 / (Real.log p) ^ 2) := by
            dsimp [A]
            field_simp [ne_of_gt hp_pos, ne_of_gt hlogpsq_pos]
  linarith [hterm1, hterm2]

/-- The chunk `2p < q ≤ 256·p⁹` (q prime, q ≡ 1 mod p), bounded by a harmonic-sum
estimate.  This is the small-q range in the path-2 surgery for `bt_reciprocal_AP_tail`,
where Brun–Titchmarsh (in our strengthened form `t ≥ 256 q⁹`) is not yet available. -/
private lemma chunk_AP_sum_le {p : ℕ} (hp : p.Prime) :
    (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ)
                  ∧ (q : ℝ) ≤ (256 : ℝ) * (p : ℝ) ^ 9)
        (Finset.Iic ⌊(256 : ℝ) * (p : ℝ) ^ 9⌋₊),
      (1 : ℝ) / (q : ℝ))
    ≤ (1 + Real.log 256 + 8 * Real.log p) / (p : ℝ) := by
  classical
  have hp_pos_nat : 0 < p := hp.pos
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pos_nat
  have hp_ge_two_nat : 2 ≤ p := hp.two_le
  have hp_ge_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge_two_nat
  have hp_ge_one_nat : 1 ≤ p := hp.one_le
  let L : ℝ := (256 : ℝ) * (p : ℝ) ^ 9
  have hL_pos : 0 < L := by dsimp [L]; positivity
  have hL_nonneg : 0 ≤ L := hL_pos.le
  -- s = the filter we are summing over
  let s := Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ)
                  ∧ (q : ℝ) ≤ L)
        (Finset.Iic ⌊L⌋₊)
  -- Drop primality to relax; bound 1/q ≤ 1/(((q-1)/p) * p) via q = kp + 1
  -- The key map: q ↦ (q - 1) / p (integer division). For q ≡ 1 mod p, q = kp + 1, k = (q-1)/p.
  -- Define M := 256 * p^8 (upper bound on k).
  let M : ℕ := ⌊(256 : ℝ) * (p : ℝ) ^ 8⌋₊
  -- For each q ∈ s, k := (q - 1) / p satisfies 2 ≤ k ≤ M, and q ≥ kp + 1.
  have hMmono : (256 : ℝ) * (p : ℝ) ^ 8 ≤ (256 : ℝ) * (p : ℝ) ^ 9 / (p : ℝ) := by
    have : (256 : ℝ) * (p : ℝ) ^ 8 * (p : ℝ) = (256 : ℝ) * (p : ℝ) ^ 9 := by ring
    rw [le_div_iff₀ hp_pos]; linarith
  -- Injection from s to Finset.Icc 2 M via q ↦ (q-1)/p.
  have hinj : Set.InjOn (fun q : ℕ => (q - 1) / p) (↑s : Set ℕ) := by
    intro q hq q' hq' heq
    change q ∈ s at hq
    change q' ∈ s at hq'
    simp only [s, Finset.mem_filter, Finset.mem_Iic] at hq hq'
    have hq_mod : q % p = 1 := hq.2.2.1
    have hq'_mod : q' % p = 1 := hq'.2.2.1
    have hq_ge1 : 1 ≤ q := by
      have h2p_pos : 0 < 2 * p := by omega
      have hreal : (((2 * p : ℕ) : ℝ)) < (q : ℝ) := hq.2.2.2.1
      have : 2 * p < q := by exact_mod_cast hreal
      omega
    have hq'_ge1 : 1 ≤ q' := by
      have hreal : (((2 * p : ℕ) : ℝ)) < (q' : ℝ) := hq'.2.2.2.1
      have : 2 * p < q' := by exact_mod_cast hreal
      omega
    have heq' : (q - 1) / p = (q' - 1) / p := heq
    have hp_gt_one : 1 < p := hp.one_lt
    -- q = p · (q/p) + 1, so q - 1 = p · (q/p)
    have hq_dm : q = p * (q / p) + q % p := (Nat.div_add_mod q p).symm
    have hq'_dm : q' = p * (q' / p) + q' % p := (Nat.div_add_mod q' p).symm
    have hq_sub : q - 1 = p * (q / p) := by omega
    have hq'_sub : q' - 1 = p * (q' / p) := by omega
    have hq_div_eq : (q - 1) / p = q / p := by
      rw [hq_sub, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
    have hq'_div_eq : (q' - 1) / p = q' / p := by
      rw [hq'_sub, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
    have hqq' : q / p = q' / p := by rw [← hq_div_eq, ← hq'_div_eq]; exact heq'
    -- From q = p · (q/p) + 1 and q/p = q'/p, plus q' = p · (q'/p) + 1
    have : q = q' := by
      rw [hq_dm, hq'_dm, hqq', hq_mod, hq'_mod]
    exact this
  -- The image lies in Finset.Icc 2 M.
  have hmaps : ∀ q ∈ s, (q - 1) / p ∈ Finset.Icc 2 M := by
    intro q hq
    simp only [s, Finset.mem_filter, Finset.mem_Iic] at hq
    have hq_mod : q % p = 1 := hq.2.2.1
    have hreal : (((2 * p : ℕ) : ℝ)) < (q : ℝ) := hq.2.2.2.1
    have hq_gt : 2 * p < q := by exact_mod_cast hreal
    have hq_ge1 : 1 ≤ q := by omega
    have hreal_le : (q : ℝ) ≤ L := hq.2.2.2.2
    -- Compute (q-1)/p ≥ 2
    have hkge : 2 ≤ (q - 1) / p := by
      -- q > 2p ⟹ q - 1 ≥ 2p ⟹ (q-1)/p ≥ 2
      have hq_minus_1_ge : 2 * p ≤ q - 1 := by omega
      have : (2 * p) / p ≤ (q - 1) / p := Nat.div_le_div_right hq_minus_1_ge
      have h2pdivp : (2 * p) / p = 2 := by
        rw [Nat.mul_div_cancel _ (by omega : 0 < p)]
      omega
    -- Compute (q-1)/p ≤ M
    have hk_le_M : (q - 1) / p ≤ M := by
      apply Nat.le_floor
      have hk_real : (((q - 1) / p : ℕ) : ℝ) ≤ ((q - 1 : ℕ) : ℝ) / (p : ℝ) := by
        rw [le_div_iff₀ hp_pos]
        have hself := Nat.div_mul_le_self (q - 1) p
        calc (((q - 1) / p : ℕ) : ℝ) * (p : ℝ)
            = ((((q - 1) / p) * p : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hself
      have hq_minus_1_le : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
        have : (q - 1 : ℕ) ≤ q := Nat.sub_le _ _
        exact_mod_cast this
      have hLp_eq : L / (p : ℝ) = (256 : ℝ) * (p : ℝ) ^ 8 := by
        dsimp [L]
        rw [show (9 : ℕ) = 8 + 1 by rfl, pow_succ]
        field_simp
      calc (((q - 1) / p : ℕ) : ℝ)
          ≤ ((q - 1 : ℕ) : ℝ) / (p : ℝ) := hk_real
        _ ≤ (q : ℝ) / (p : ℝ) :=
            div_le_div_of_nonneg_right hq_minus_1_le hp_pos.le
        _ ≤ L / (p : ℝ) :=
            div_le_div_of_nonneg_right hreal_le hp_pos.le
        _ = (256 : ℝ) * (p : ℝ) ^ 8 := hLp_eq
    exact Finset.mem_Icc.mpr ⟨hkge, hk_le_M⟩
  -- 1/q ≤ 1 / ((q-1)/p * p) for q ∈ s
  have hpoint : ∀ q ∈ s, (1 : ℝ) / (q : ℝ) ≤
      1 / ((((q - 1) / p : ℕ) : ℝ) * (p : ℝ)) := by
    intro q hq
    simp only [s, Finset.mem_filter, Finset.mem_Iic] at hq
    have hq_mod : q % p = 1 := hq.2.2.1
    have hreal : (((2 * p : ℕ) : ℝ)) < (q : ℝ) := hq.2.2.2.1
    have hq_gt : 2 * p < q := by exact_mod_cast hreal
    -- q = p * (q/p) + 1; q - 1 = p * (q/p); (q-1)/p = q/p
    have hq_dm : q = p * (q / p) + q % p := (Nat.div_add_mod q p).symm
    have hq_sub : q - 1 = p * (q / p) := by omega
    have hq_div_eq : (q - 1) / p = q / p := by
      rw [hq_sub, Nat.mul_div_cancel_left _ (by omega : 0 < p)]
    have hq_eq : q = ((q - 1) / p) * p + 1 := by
      rw [hq_div_eq, Nat.mul_comm]
      omega
    have hkp_pos : 0 < (((q - 1) / p : ℕ) : ℝ) * (p : ℝ) := by
      have hkge2 : 2 ≤ (q - 1) / p := by
        have hq_minus_1_ge : 2 * p ≤ q - 1 := by omega
        have : (2 * p) / p ≤ (q - 1) / p := Nat.div_le_div_right hq_minus_1_ge
        have h2pdivp : (2 * p) / p = 2 :=
          Nat.mul_div_cancel _ (by omega : 0 < p)
        omega
      have hk_pos_real : (0 : ℝ) < (((q - 1) / p : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < (q - 1) / p)
      positivity
    have hprod_le_q : (((q - 1) / p : ℕ) : ℝ) * (p : ℝ) ≤ (q : ℝ) := by
      have h : ((q - 1) / p) * p ≤ q := by
        conv_rhs => rw [hq_eq]
        exact Nat.le_succ _
      exact_mod_cast h
    exact one_div_le_one_div_of_le hkp_pos hprod_le_q
  -- Now do the sum
  calc
    (∑ q ∈ s, (1 : ℝ) / (q : ℝ))
        ≤ ∑ q ∈ s, 1 / ((((q - 1) / p : ℕ) : ℝ) * (p : ℝ)) := Finset.sum_le_sum hpoint
    _ = ∑ k ∈ Finset.image (fun q : ℕ => (q - 1) / p) s, 1 / ((k : ℝ) * (p : ℝ)) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ k ∈ Finset.Icc 2 M, 1 / ((k : ℝ) * (p : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_image] at hk
          rcases hk with ⟨q, hqs, rfl⟩
          exact hmaps q hqs
        · intro k _ _
          positivity
    _ ≤ ∑ k ∈ Finset.Icc 1 M, 1 / ((k : ℝ) * (p : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_Icc] at hk ⊢
          exact ⟨by omega, hk.2⟩
        · intro k _ _
          positivity
    _ = (1 / (p : ℝ)) * (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hkpos : (0 : ℝ) < k := by
          have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          exact_mod_cast (by omega : 0 < k)
        field_simp [hkpos.ne', hp_pos.ne']
    _ = (1 / (p : ℝ)) * (harmonic M : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        simp [one_div]
    _ ≤ (1 / (p : ℝ)) * (1 + Real.log (M : ℝ)) := by
        have h1p_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) h1p_nonneg
    _ ≤ (1 / (p : ℝ)) * (1 + Real.log ((256 : ℝ) * (p : ℝ) ^ 8)) := by
        have hM_le : (M : ℝ) ≤ (256 : ℝ) * (p : ℝ) ^ 8 := by
          dsimp [M]
          exact Nat.floor_le (by positivity)
        have hM_pos_nat : 0 < M := by
          dsimp [M]
          have h256 : (256 : ℕ) ≤ ⌊(256 : ℝ) * (p : ℝ) ^ 8⌋₊ := by
            apply Nat.le_floor
            have hp8_ge : (1 : ℝ) ≤ (p : ℝ) ^ 8 := by
              have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
              exact one_le_pow₀ this
            have : (256 : ℝ) ≤ (256 : ℝ) * (p : ℝ) ^ 8 := by
              have := mul_le_mul_of_nonneg_left hp8_ge (by norm_num : (0 : ℝ) ≤ 256)
              linarith
            exact_mod_cast this
          omega
        have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos_nat
        have hlog_le : Real.log (M : ℝ) ≤ Real.log ((256 : ℝ) * (p : ℝ) ^ 8) :=
          Real.log_le_log hM_pos hM_le
        have h1p_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
        apply mul_le_mul_of_nonneg_left _ h1p_nonneg
        linarith
    _ = (1 + Real.log 256 + 8 * Real.log p) / (p : ℝ) := by
        have hlog_eq : Real.log ((256 : ℝ) * (p : ℝ) ^ 8) = Real.log 256 + 8 * Real.log p := by
          rw [Real.log_mul (by norm_num) (by positivity)]
          congr 1
          rw [Real.log_pow]
          ring
        rw [hlog_eq, add_div]
        ring

/-- **Paper §4 eq:Sp-bound — exact paper statement.**

For every prime `p ≥ 2`, the bad-prime-pair reciprocal sum
`S(p) := ∑_{p < q ≤ Q(p), q ≡ 1 mod p, q prime} 1/q` satisfies
`S(p) ≤ C · (log p / p + 1/(log p)^2)` for some absolute `C > 0`,
where `Q(p) := exp(exp(p / (log p)^2))`.

Proof: split into ranges `p < q ≤ p²` (trivial bound, paper eq:bad-h-low)
and `p² < q ≤ Q(p)` (Brun–Titchmarsh + partial summation, paper eq:BT-final). -/
theorem bt_reciprocal_AP_tail :
    ∃ C : ℝ, 0 < C ∧
      ∀ p : ℕ, p.Prime → 2 ≤ p →
        (∑ q ∈ Finset.filter
            (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧
              (q : ℝ) ≤ Real.exp (Real.exp ((p : ℝ) / (Real.log p) ^ 2)))
            (Finset.Iic ⌊Real.exp (Real.exp ((p : ℝ) / (Real.log p) ^ 2))⌋₊),
          (1 : ℝ) / (q : ℝ)) ≤
            C * (Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2) := by
  classical
  rcases brun_titchmarsh with ⟨CBT, hCBT, hBTall⟩
  -- Total constant: absorbs low ≤ 1/p, chunk ≤ (1 + log 256 + 8 log p)/p,
  -- and tail ≤ (2 CBT/log 2)(1/p) + 2 CBT (1/(log p)²).
  let hlog2_pos_top : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := (1 / Real.log 2)
      + ((1 + Real.log 256) / Real.log 2 + 8)
      + (2 * CBT / (Real.log 2) ^ 2 + 2 * CBT)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    have hlog256_nonneg : 0 ≤ Real.log 256 := Real.log_nonneg (by norm_num)
    positivity
  · intro p hp _hp2
    let A : ℝ := (p : ℝ) / (Real.log p) ^ 2
    let Q : ℝ := Real.exp (Real.exp A)
    let L : ℝ := (256 : ℝ) * (p : ℝ) ^ 9
    change
      (∑ q ∈ Finset.filter
          (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
          (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
        C * (Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2)
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp_ge_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog256_nonneg : 0 ≤ Real.log 256 := Real.log_nonneg (by norm_num)
    have hlogp_pos : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast hp.one_lt)
    have hlogp_ge_log2 : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) hp_ge_two
    have hlogp_sq_pos : 0 < (Real.log (p : ℝ)) ^ 2 := by positivity
    have hlogterm_nonneg : 0 ≤ 1 / (Real.log (p : ℝ)) ^ 2 := by positivity
    have hinvp_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
    have hL_pos : 0 < L := by dsimp [L]; positivity
    have h2p_pos : (0 : ℝ) < (((2 * p : ℕ) : ℝ)) := by
      exact_mod_cast (Nat.mul_pos (by decide : 0 < 2) hp.pos)
    -- Key fact: log p / p ≥ 1/p * log 2 (since log p ≥ log 2)
    have h_logpp_ge_invp : (1 / (p : ℝ)) ≤ (1 / Real.log 2) * (Real.log p / (p : ℝ)) := by
      have hrhs : (1 / Real.log 2) * (Real.log p / (p : ℝ)) =
          Real.log p / (Real.log 2 * (p : ℝ)) := by
        rw [div_mul_div_comm, one_mul]
      rw [hrhs]
      have hlog2p_pos : 0 < Real.log 2 * (p : ℝ) := by positivity
      rw [div_le_div_iff₀ hp_pos hlog2p_pos]
      have h := hlogp_ge_log2
      nlinarith [hp_pos, hlog2_pos, hlogp_ge_log2]
    -- The standard BT instance for prime p, AP class 1, with the strengthened hypothesis.
    have hBTp : ∀ t : ℝ, (256 : ℝ) * (p : ℝ) ^ 9 ≤ t →
        (piMod t p 1 : ℝ) ≤ CBT * t / (((p - 1 : ℕ) : ℝ) * Real.log (t / p)) := by
      intro t ht
      simpa [Nat.totient_prime hp] using hBTall p hp.one_le 1 (by simp) t ht
    have htotal := total_AP_sum_le_low_add_high (p := p) (Q := Q)
    have hlow := low_AP_sum_le_inv hp
    -- Chunk bound: applies regardless.
    have hchunk_bound : (∑ q ∈ Finset.filter
        (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ L)
        (Finset.Iic ⌊L⌋₊), (1 : ℝ) / (q : ℝ))
      ≤ (1 + Real.log 256 + 8 * Real.log p) / (p : ℝ) := chunk_AP_sum_le hp
    let Sp : ℝ := Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2
    have hSp_pos : 0 < Sp := by
      dsimp [Sp]
      positivity
    -- Bound the chunk by ((1 + log 256)/log 2 + 8) · Sp
    have hchunk_le_Sp : (1 + Real.log 256 + 8 * Real.log p) / (p : ℝ) ≤
        ((1 + Real.log 256) / Real.log 2 + 8) * Sp := by
      have h1 : (1 + Real.log 256) / (p : ℝ) ≤
          ((1 + Real.log 256) / Real.log 2) * (Real.log p / (p : ℝ)) := by
        have h_pos : 0 ≤ 1 + Real.log 256 := by linarith
        calc (1 + Real.log 256) / (p : ℝ)
            = (1 + Real.log 256) * (1 / (p : ℝ)) := by ring
          _ ≤ (1 + Real.log 256) * ((1 / Real.log 2) * (Real.log p / (p : ℝ))) :=
              mul_le_mul_of_nonneg_left h_logpp_ge_invp h_pos
          _ = ((1 + Real.log 256) / Real.log 2) * (Real.log p / (p : ℝ)) := by ring
      have h2 : 8 * Real.log p / (p : ℝ) ≤ 8 * (Real.log p / (p : ℝ)) := by
        rw [mul_div_assoc]
      have h3 : (1 + Real.log 256 + 8 * Real.log p) / (p : ℝ) =
          (1 + Real.log 256) / (p : ℝ) + 8 * Real.log p / (p : ℝ) := by
        rw [add_div]
      rw [h3]
      have hcalc1 : (1 + Real.log 256) / (p : ℝ) + 8 * Real.log p / (p : ℝ) ≤
          ((1 + Real.log 256) / Real.log 2) * (Real.log p / (p : ℝ)) +
            8 * (Real.log p / (p : ℝ)) := by
        linarith [h1, h2]
      have hcalc2 : ((1 + Real.log 256) / Real.log 2) * (Real.log p / (p : ℝ)) +
            8 * (Real.log p / (p : ℝ)) =
          ((1 + Real.log 256) / Real.log 2 + 8) * (Real.log p / (p : ℝ)) := by ring
      have hSp_ge_logpp : (Real.log p / (p : ℝ)) ≤ Sp := by
        dsimp [Sp]; linarith [hlogterm_nonneg]
      have hcoef_nonneg : 0 ≤ (1 + Real.log 256) / Real.log 2 + 8 := by
        have := div_nonneg (show (0 : ℝ) ≤ 1 + Real.log 256 from by linarith)
          hlog2_pos.le
        linarith
      calc (1 + Real.log 256) / (p : ℝ) + 8 * Real.log p / (p : ℝ)
          ≤ ((1 + Real.log 256) / Real.log 2) * (Real.log p / (p : ℝ)) +
              8 * (Real.log p / (p : ℝ)) := hcalc1
        _ = ((1 + Real.log 256) / Real.log 2 + 8) * (Real.log p / (p : ℝ)) := hcalc2
        _ ≤ ((1 + Real.log 256) / Real.log 2 + 8) * Sp :=
            mul_le_mul_of_nonneg_left hSp_ge_logpp hcoef_nonneg
    -- Bound the low (1/p) by (1/log 2) · Sp
    have hlow_le_Sp : (1 : ℝ) / (p : ℝ) ≤ (1 / Real.log 2) * Sp := by
      have hSp_ge_logpp : (Real.log p / (p : ℝ)) ≤ Sp := by
        dsimp [Sp]; linarith [hlogterm_nonneg]
      have h1log2_nonneg : 0 ≤ 1 / Real.log 2 := by positivity
      calc (1 : ℝ) / (p : ℝ)
          ≤ (1 / Real.log 2) * (Real.log p / (p : ℝ)) := h_logpp_ge_invp
        _ ≤ (1 / Real.log 2) * Sp := mul_le_mul_of_nonneg_left hSp_ge_logpp h1log2_nonneg
    -- Bound the tail-form (2 CBT/log 2)(1/p) + 2 CBT (1/(log p)²) by `(2CBT/log²2 + 2CBT)·Sp`
    have htail_form_le_Sp : ∀ x : ℝ, x = (2 * CBT / Real.log 2) * (1 / (p : ℝ)) +
        2 * CBT * (1 / (Real.log p) ^ 2) →
        x ≤ (2 * CBT / (Real.log 2) ^ 2 + 2 * CBT) * Sp := by
      intro x hx
      have hCBT_nonneg : 0 ≤ CBT := hCBT.le
      have h1 : (2 * CBT / Real.log 2) * (1 / (p : ℝ)) ≤
          (2 * CBT / (Real.log 2) ^ 2) * (Real.log p / (p : ℝ)) := by
        have hcoef : 0 ≤ 2 * CBT / Real.log 2 := by positivity
        calc (2 * CBT / Real.log 2) * (1 / (p : ℝ))
            ≤ (2 * CBT / Real.log 2) * ((1 / Real.log 2) * (Real.log p / (p : ℝ))) :=
              mul_le_mul_of_nonneg_left h_logpp_ge_invp hcoef
          _ = (2 * CBT / (Real.log 2) ^ 2) * (Real.log p / (p : ℝ)) := by
              ring
      have h2 : (2 * CBT / (Real.log 2) ^ 2) * (Real.log p / (p : ℝ)) +
          2 * CBT * (1 / (Real.log p) ^ 2) ≤
          (2 * CBT / (Real.log 2) ^ 2 + 2 * CBT) * Sp := by
        have hcoefA_nonneg : 0 ≤ 2 * CBT / (Real.log 2) ^ 2 := by positivity
        have hcoefB_nonneg : 0 ≤ 2 * CBT := by positivity
        have hlogpp_nonneg : 0 ≤ Real.log p / (p : ℝ) := by
          have := hlogp_pos.le; positivity
        show (2 * CBT / (Real.log 2) ^ 2) * (Real.log p / (p : ℝ)) +
            2 * CBT * (1 / (Real.log p) ^ 2) ≤
          (2 * CBT / (Real.log 2) ^ 2 + 2 * CBT) *
            (Real.log p / (p : ℝ) + 1 / (Real.log p) ^ 2)
        have hcross1 : 0 ≤ (2 * CBT / (Real.log 2) ^ 2) * (1 / (Real.log p) ^ 2) :=
          mul_nonneg hcoefA_nonneg hlogterm_nonneg
        have hcross2 : 0 ≤ (2 * CBT) * (Real.log p / (p : ℝ)) :=
          mul_nonneg hcoefB_nonneg hlogpp_nonneg
        nlinarith [hcross1, hcross2]
      linarith [hx, h1, h2]
    -- The high range (2p < q ≤ Q) splits at L: chunk (2p < q ≤ L) + tail (L < q ≤ Q).
    by_cases h2pQ : (((2 * p : ℕ) : ℝ)) ≤ Q
    · -- High range nonempty (potentially).
      by_cases hQL : Q ≤ L
      · -- Case A: high ⊆ chunk (as a filter).
        have hLnonneg : 0 ≤ L := hL_pos.le
        have hQnonneg : 0 ≤ Q := by dsimp [Q]; positivity
        have hhigh_le_chunk :
            (∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
                (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
              (∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ L)
                (Finset.Iic ⌊L⌋₊), (1 : ℝ) / (q : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            simp only [Finset.mem_filter, Finset.mem_Iic] at hq ⊢
            refine ⟨?_, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.trans hQL⟩
            exact Nat.le_floor (hq.2.2.2.2.trans hQL)
          · intro q _ _
            positivity
        have hhigh_bound :
            (∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
                (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
              (1 + Real.log 256 + 8 * Real.log p) / (p : ℝ) :=
          hhigh_le_chunk.trans hchunk_bound
        -- Combine: total ≤ low + high ≤ 1/p + chunk_bound.
        -- 1/p ≤ (1/log 2)·Sp; chunk ≤ ((1 + log 256)/log 2 + 8)·Sp.
        calc (∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
                (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ))
            ≤ _ := htotal
          _ ≤ (1 / (p : ℝ)) + (1 + Real.log 256 + 8 * Real.log p) / (p : ℝ) :=
              add_le_add hlow hhigh_bound
          _ ≤ ((1 / Real.log 2) * Sp) + (((1 + Real.log 256) / Real.log 2 + 8) * Sp) :=
              add_le_add hlow_le_Sp hchunk_le_Sp
          _ = ((1 / Real.log 2) + ((1 + Real.log 256) / Real.log 2 + 8)) * Sp := by ring
          _ ≤ C * Sp := by
              dsimp [C]
              have hSp_nonneg : 0 ≤ Sp := hSp_pos.le
              have htail_coef_nonneg : 0 ≤ 2 * CBT / (Real.log 2) ^ 2 + 2 * CBT := by
                positivity
              nlinarith [hSp_nonneg, htail_coef_nonneg]
      · -- Case B: L < Q. high = chunk + tail.
        have hL_le_Q : L ≤ Q := le_of_not_ge hQL
        have hhigh_exp := high_AP_sum_le_explicit hCBT hp hL_le_Q hBTp
        have htail := explicit_tail_bound hCBT hp hL_le_Q
        have htail_bound :
            (∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (256 : ℝ) * (p : ℝ) ^ 9 < (q : ℝ) ∧ (q : ℝ) ≤ Q)
                (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
              (2 * CBT / Real.log 2) * (1 / (p : ℝ)) +
                2 * CBT * (1 / (Real.log p) ^ 2) :=
          hhigh_exp.trans htail
        -- Split high range (2p, Q] into chunk (2p, L] and tail (L, Q].
        have hhigh_split :
            (∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
                (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) ≤
              (∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ L)
                (Finset.Iic ⌊L⌋₊), (1 : ℝ) / (q : ℝ)) +
              (∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (256 : ℝ) * (p : ℝ) ^ 9 < (q : ℝ) ∧ (q : ℝ) ≤ Q)
                (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) := by
          have hQnonneg : 0 ≤ Q := by dsimp [Q]; positivity
          let s := Finset.filter
              (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
              (Finset.Iic ⌊Q⌋₊)
          have hsplit := Finset.sum_filter_add_sum_filter_not (s := s)
            (p := fun q => (q : ℝ) ≤ L) (f := fun q => (1 : ℝ) / (q : ℝ))
          rw [← hsplit]
          apply add_le_add
          · apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro q hq
              simp only [s, Finset.mem_filter, Finset.mem_Iic] at hq ⊢
              refine ⟨?_, hq.1.2.1, hq.1.2.2.1, hq.1.2.2.2.1, hq.2⟩
              exact Nat.le_floor hq.2
            · intro q _ _
              positivity
          · apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro q hq
              simp only [s, Finset.mem_filter, Finset.mem_Iic] at hq ⊢
              have hlt : L < (q : ℝ) := lt_of_not_ge hq.2
              refine ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, ?_, hq.1.2.2.2.2⟩
              dsimp [L] at hlt
              exact hlt
            · intro q _ _
              positivity
        -- Combine: total ≤ low + chunk + tail.
        calc (∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
                (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ))
            ≤ _ := htotal
          _ ≤ (1 / (p : ℝ)) +
              ((∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ L)
                (Finset.Iic ⌊L⌋₊), (1 : ℝ) / (q : ℝ)) +
              (∑ q ∈ Finset.filter
                (fun q => q.Prime ∧ q % p = 1 ∧ (256 : ℝ) * (p : ℝ) ^ 9 < (q : ℝ) ∧ (q : ℝ) ≤ Q)
                (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ))) :=
              add_le_add hlow hhigh_split
          _ ≤ ((1 / Real.log 2) * Sp) +
              ((((1 + Real.log 256) / Real.log 2 + 8) * Sp) +
                ((2 * CBT / (Real.log 2) ^ 2 + 2 * CBT) * Sp)) := by
              apply add_le_add hlow_le_Sp
              apply add_le_add
              · exact hchunk_bound.trans hchunk_le_Sp
              · exact htail_bound.trans (htail_form_le_Sp _ rfl)
          _ = ((1 / Real.log 2) + ((1 + Real.log 256) / Real.log 2 + 8) +
                (2 * CBT / (Real.log 2) ^ 2 + 2 * CBT)) * Sp := by ring
          _ = C * Sp := by dsimp [C]
    · -- High range empty.
      have hQlt : Q < (((2 * p : ℕ) : ℝ)) := lt_of_not_ge h2pQ
      have hQ_pos : 0 < Q := by dsimp [Q]; positivity
      have hhigh_zero :
          (∑ q ∈ Finset.filter
            (fun q => q.Prime ∧ q % p = 1 ∧ (((2 * p : ℕ) : ℝ)) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
            (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_Iic] at hq
        have hq_le_Q : (q : ℝ) ≤ Q := (Nat.cast_le.mpr hq.1).trans (Nat.floor_le hQ_pos.le)
        have hlt : (((2 * p : ℕ) : ℝ)) < (q : ℝ) := hq.2.2.2.1
        exact False.elim (by nlinarith)
      calc (∑ q ∈ Finset.filter
              (fun q => q.Prime ∧ q % p = 1 ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ Q)
              (Finset.Iic ⌊Q⌋₊), (1 : ℝ) / (q : ℝ))
          ≤ _ := htotal
        _ ≤ (1 / (p : ℝ)) + 0 := by linarith [hlow, hhigh_zero.le]
        _ = 1 / (p : ℝ) := by ring
        _ ≤ (1 / Real.log 2) * Sp := hlow_le_Sp
        _ ≤ C * Sp := by
            dsimp [C]
            have hSp_nonneg : 0 ≤ Sp := hSp_pos.le
            have hrest_nonneg : 0 ≤ ((1 + Real.log 256) / Real.log 2 + 8) +
                (2 * CBT / (Real.log 2) ^ 2 + 2 * CBT) := by
              have h1 : 0 ≤ (1 + Real.log 256) / Real.log 2 + 8 := by
                have := div_nonneg (show (0 : ℝ) ≤ 1 + Real.log 256 from by linarith)
                  hlog2_pos.le
                linarith
              have h2 : 0 ≤ 2 * CBT / (Real.log 2) ^ 2 + 2 * CBT := by positivity
              linarith
            nlinarith [hSp_nonneg, hrest_nonneg]



end Erdos696

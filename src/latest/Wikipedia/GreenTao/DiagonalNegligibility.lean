import Wikipedia.GreenTao.Assembly
import Wikipedia.GreenTao.Majorization
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Negligibility of diagonal progressions

The relative-counting argument produces a positive lower bound for the
normalized count of cyclic progressions.  To extract a progression with
nonzero common difference, that lower bound must dominate the contribution
of the constant progressions.

For the W-tricked prime weight the pointwise height is at most a fixed
multiple of `log N`.  Since every fixed power of `log N` is `o(N)`, the
diagonal contribution is eventually smaller than any fixed positive
progression-count lower bound.  This file records that elementary bridge
without imposing any sieve or transference hypotheses.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter

/-- A W-tricked value in the standard residue system is bounded by the value
at the right endpoint of that system. -/
theorem wTrickedValue_le_affine_end
    {N : ℕ} [NeZero N] (W b : ℕ) (n : ZMod N) :
    wTrickedValue W b n ≤ W * N + b := by
  unfold wTrickedValue
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left W n.val_lt.le) b

/-- The real totient ratio is at most one for a positive modulus. -/
theorem totient_div_self_le_one
    {W : ℕ} (hW : 0 < W) :
    (W.totient : ℝ) / W ≤ 1 := by
  rw [div_le_one (by exact_mod_cast hW)]
  exact_mod_cast Nat.totient_le W

/-- Under the standard parameter bound `W + b ≤ N`, the W-tricked prime
weight has the crude but uniform height bound `2 α log N`.

The localization to `greenTaoInterval` is not needed for this estimate; only
the standard representative bound `n.val < N` is used. -/
theorem wTrickedPrimeWeight_le_two_mul_alpha_mul_log
    {N W b : ℕ} [NeZero N] {α : ℝ}
    (hα : 0 ≤ α) (hW : 0 < W)
    (hN : 1 ≤ N) (hWB : W + b ≤ N)
    (n : ZMod N) :
    wTrickedPrimeWeight α W b n ≤
      2 * α * Real.log (N : ℝ) := by
  unfold wTrickedPrimeWeight
  split_ifs with hprime
  · have hvaluePos :
        (0 : ℝ) < (wTrickedValue W b n : ℝ) := by
      exact_mod_cast hprime.2.pos
    have hvalueUpperNat :
        wTrickedValue W b n ≤ N ^ 2 :=
      (wTrickedValue_le_affine_end W b n).trans
        (affine_mul_add_le_sq hN hWB)
    have hvalueUpperReal :
        (wTrickedValue W b n : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast hvalueUpperNat
    have hlog :
        Real.log (wTrickedValue W b n) ≤
          2 * Real.log (N : ℝ) := by
      calc
        Real.log (wTrickedValue W b n) ≤
            Real.log ((N : ℝ) ^ 2) :=
          Real.log_le_log hvaluePos hvalueUpperReal
        _ = 2 * Real.log (N : ℝ) := by
          rw [Real.log_pow]
          norm_num
    have hratioNonneg :
        0 ≤ (W.totient : ℝ) / W :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hratio :
        (W.totient : ℝ) / W ≤ 1 :=
      totient_div_self_le_one hW
    have hlogNonneg : 0 ≤ 2 * Real.log (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      positivity
    calc
      α * ((W.totient : ℝ) / W) *
            Real.log (wTrickedValue W b n) ≤
          α * ((W.totient : ℝ) / W) *
            (2 * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog
          (mul_nonneg hα hratioNonneg)
      _ ≤ α * (2 * Real.log (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right hα hratio) hlogNonneg
      _ = 2 * α * Real.log (N : ℝ) := by ring
  · have hlogNonneg : 0 ≤ Real.log (N : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hN
    positivity

/-- The same height estimate after averaging over the cyclic group. -/
theorem mean_wTrickedPrimeWeight_le_two_mul_alpha_mul_log
    {N W b : ℕ} [NeZero N] {α : ℝ}
    (hα : 0 ≤ α) (hW : 0 < W)
    (hN : 1 ≤ N) (hWB : W + b ≤ N) :
    mean (wTrickedPrimeWeight α W b : ZMod N → ℝ) ≤
      2 * α * Real.log (N : ℝ) :=
  mean_le_of_le_const fun n =>
    wTrickedPrimeWeight_le_two_mul_alpha_mul_log
      hα hW hN hWB n

/-- A convenient strengthening of `cyclicAPOffDiagMass_pos_of_count`.
It is enough that the `k`th power of a uniform height bound be smaller than
`N` times a lower bound for the normalized progression count. -/
theorem cyclicAPOffDiagMass_pos_of_count_lower_height
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ}
    {B c : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B)
    (hB0 : 0 ≤ B)
    (hcountLower : c ≤ cyclicAPCount k N f)
    (hheight : B ^ k < (N : ℝ) * c) :
    0 < cyclicAPOffDiagMass k N f := by
  apply cyclicAPOffDiagMass_pos_of_count hk hf0 hfB
  have hmean : mean f ≤ B :=
    mean_le_of_le_const hfB
  have hdiagonal :
      B ^ (k - 1) * mean f ≤ B ^ k := by
    calc
      B ^ (k - 1) * mean f ≤ B ^ (k - 1) * B :=
        mul_le_mul_of_nonneg_left hmean (pow_nonneg hB0 _)
      _ = B ^ k := by
        rw [← pow_succ]
        congr
        omega
  have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  exact hdiagonal.trans_lt
    (hheight.trans_le
      (mul_le_mul_of_nonneg_left hcountLower hNnonneg))

/-- Specialization of the preceding extraction lemma to the W-tricked prime
weight and its logarithmic height bound. -/
theorem wTrickedPrimeWeight_offDiagMass_pos_of_count_lower
    {k N W b : ℕ} [NeZero N] {α c : ℝ}
    (hk : 1 ≤ k)
    (hα : 0 ≤ α) (hW : 0 < W)
    (hN : 1 ≤ N) (hWB : W + b ≤ N)
    (hcountLower :
      c ≤ cyclicAPCount k N
        (wTrickedPrimeWeight α W b))
    (hheight :
      (2 * α * Real.log (N : ℝ)) ^ k <
        (N : ℝ) * c) :
    0 < cyclicAPOffDiagMass k N
      (wTrickedPrimeWeight α W b) := by
  apply cyclicAPOffDiagMass_pos_of_count_lower_height
    hk
    (wTrickedPrimeWeight_nonneg hα W b)
    (wTrickedPrimeWeight_le_two_mul_alpha_mul_log
      hα hW hN hWB)
  · have hlogNonneg : 0 ≤ Real.log (N : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hN
    positivity
  · exact hcountLower
  · exact hheight

/-- Every fixed multiple of a fixed power of `log N` is eventually smaller
than `c N` for any `c > 0`.  The constant `C` is unrestricted: the absolute
value estimate supplied by little-o is stronger than the displayed
one-sided inequality. -/
theorem eventually_mul_log_pow_lt_linear
    (C c : ℝ) (k : ℕ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      (C * Real.log (N : ℝ)) ^ k < (N : ℝ) * c := by
  have hlittle :
      (fun N : ℕ => (C * Real.log (N : ℝ)) ^ k) =o[atTop]
        (fun N : ℕ => (N : ℝ)) := by
    have hlog :
        (fun N : ℕ => Real.log (N : ℝ) ^ k) =o[atTop]
          (fun N : ℕ => (N : ℝ)) :=
      (Real.isLittleO_pow_log_id_atTop (n := k)).comp_tendsto
        tendsto_natCast_atTop_atTop
    simpa [mul_pow] using hlog.const_mul_left (C ^ k)
  have hcHalf : 0 < c / 2 := by positivity
  filter_upwards
    [hlittle.bound hcHalf, eventually_gt_atTop (0 : ℕ)]
      with N hbound hN
  calc
    (C * Real.log (N : ℝ)) ^ k ≤
        ‖(C * Real.log (N : ℝ)) ^ k‖ :=
      (by simpa [Real.norm_eq_abs] using
        le_abs_self ((C * Real.log (N : ℝ)) ^ k))
    _ ≤ (c / 2) * ‖(N : ℝ)‖ := hbound
    _ = (c / 2) * (N : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
    _ < (N : ℝ) * c := by
      have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      nlinarith

/-- In particular, the crude W-tricked height raised to any fixed power is
eventually negligible compared with a fixed positive count lower bound. -/
theorem eventually_wTrickedPrimeWeight_height_pow_lt_linear
    (α c : ℝ) (k : ℕ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      (2 * α * Real.log (N : ℝ)) ^ k <
        (N : ℝ) * c := by
  simpa [mul_assoc] using
    eventually_mul_log_pow_lt_linear (2 * α) c k hc

/-! ## Asymptotic final interface -/

/-- The exact asymptotic output needed from the sieve and transference
layers.  For each progression length, all W-trick parameters and the
positive count lower bound are fixed before the cyclic modulus tends to
infinity.

Writing the modulus as `M + 1` keeps the proposition free of a dependent
`NeZero` argument. -/
def HasEventuallyWTrickedPrimeProgressionCountLower : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (α : ℝ) (W : ℕ) (c : ℝ),
      0 < α ∧ 0 < W ∧ 0 < c ∧
        ∀ᶠ M : ℕ in atTop,
          ∃ b : ℕ, b < W ∧
            c ≤
              cyclicAPCount k (M + 1)
                (wTrickedPrimeWeight α W b)

/-- An eventual positive lower bound for the full W-tricked cyclic count
implies the positive off-diagonal mass interface.  The only extra input is
the elementary fact that fixed logarithmic height is `o(N)`. -/
theorem HasEventuallyWTrickedPrimeProgressionCountLower.toMass
    (hcount : HasEventuallyWTrickedPrimeProgressionCountLower) :
    HasPrimeProgressionMass := by
  intro k hk
  obtain ⟨α, W, c, hα, hW, hc, heventualCount⟩ :=
    hcount k hk
  rw [eventually_atTop] at heventualCount
  obtain ⟨Mcount, hcountFrom⟩ := heventualCount
  have heventualHeight :=
    eventually_wTrickedPrimeWeight_height_pow_lt_linear
      α c k hc
  rw [eventually_atTop] at heventualHeight
  obtain ⟨Nheight, hheightFrom⟩ := heventualHeight
  let M : ℕ := max Mcount (max (2 * W) Nheight)
  have hMcount : Mcount ≤ M :=
    le_max_left _ _
  have hNheight : Nheight ≤ M + 1 := by
    exact (le_max_right (2 * W) Nheight).trans
      ((le_max_right Mcount _).trans (Nat.le_succ M))
  obtain ⟨b, hb, hcountLower⟩ :=
    hcountFrom M hMcount
  have htwoW : 2 * W ≤ M :=
    (le_max_left (2 * W) Nheight).trans
      (le_max_right Mcount _)
  have hWB : W + b ≤ M + 1 := by
    omega
  have hheight :
      (2 * α * Real.log ((M + 1 : ℕ) : ℝ)) ^ k <
        ((M + 1 : ℕ) : ℝ) * c :=
    hheightFrom (M + 1) hNheight
  refine ⟨M, α, W, b, hα, hW, ?_⟩
  exact
    wTrickedPrimeWeight_offDiagMass_pos_of_count_lower
      (by omega) hα.le hW (by omega) hWB
      hcountLower hheight

/-- Final Green--Tao assembly from the asymptotic count-lower-bound
interface. -/
theorem containsArbitraryAPs_primes_of_eventual_count_lower
    (hcount : HasEventuallyWTrickedPrimeProgressionCountLower) :
    SzemeredisTheorem.ContainsArbitraryAPs
      {p : ℕ | Nat.Prime p} :=
  containsArbitraryAPs_primes_of_mass hcount.toMass

end Wikipedia.SzemeredisTheorem

import ErdosProblems.Erdos321.KernelAlgebra
import ErdosProblems.Erdos321.AnalyticRecurrence

namespace Erdos321

/-- A natural quotient differs from the corresponding real quotient by less
than one, from below. -/
theorem natCast_div_sub_one_lt {N d : ℕ} (hd : 0 < d) :
    (N : ℝ) / d - 1 < (N / d : ℕ) := by
  have hnat : N < (N / d + 1) * d :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (N / d))
  have hreal : (N : ℝ) < ((N / d + 1) * d : ℕ) := by exact_mod_cast hnat
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdiv : (N : ℝ) / d < (N / d + 1 : ℕ) := by
    rw [div_lt_iff₀ hdR]
    exact_mod_cast hnat
  norm_num at hdiv ⊢
  linarith

/-- The width of a quotient interval differs by at most one from its real
main term. -/
theorem quotientInterval_width_bounds {N t : ℕ} (ht : 0 < t) :
    (N : ℝ) / (t * (t + 1)) - 1 ≤
        ((N / t : ℕ) : ℝ) - ((N / (t + 1) : ℕ) : ℝ) ∧
      ((N / t : ℕ) : ℝ) - ((N / (t + 1) : ℕ) : ℝ) ≤
        (N : ℝ) / (t * (t + 1)) + 1 := by
  have hlowT := natCast_div_sub_one_lt (N := N) ht
  have hlowS := natCast_div_sub_one_lt (N := N) (show 0 < t + 1 by omega)
  have hupT : ((N / t : ℕ) : ℝ) ≤ (N : ℝ) / t := Nat.cast_div_le
  have hupS : ((N / (t + 1) : ℕ) : ℝ) ≤ (N : ℝ) / (t + 1) := by
    simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := t + 1))
  norm_num at hlowS hupS
  have hid : (N : ℝ) / t - (N : ℝ) / (t + 1) =
      (N : ℝ) / (t * (t + 1)) := by
    field_simp
    ring
  constructor <;> rw [← hid] <;> linarith

/-- Main normalized quotient kernel. -/
noncomputable def quotientMainKernel (N t : ℕ) : ℝ :=
  (N : ℝ) / ((t : ℝ) * (t + 1) * Real.log N)

/-- Explicit relative error controlling floors, PNT endpoint errors, and the
variation of logarithms across one quotient interval. -/
noncomputable def quotientKernelError (C : ℝ) (N t : ℕ) : ℝ :=
  ((t : ℝ) * (t + 1)) / N +
    8 * C * (t + 1) / Real.log N ^ 2 +
    Real.log (2 * (t + 1)) / Real.log N

/-- Explicit kernel comparison.  All asymptotic work is isolated in checking
that `quotientKernelError≤1/4` on the chosen range. -/
theorem quotientCoefficient_kernel_sandwich
    {C : ℝ} (hC : 0 ≤ C) {N t : ℕ}
    (ht : 1 ≤ t) (hNt : 2 * (t + 1) ≤ N)
    (hN : 1 < N)
    (hη : quotientKernelError C N t ≤ 1 / 4) :
    (1 - 2 * quotientKernelError C N t) * quotientMainKernel N t ≤
        quotientLowerCoefficient C N t ∧
      quotientUpperCoefficient C N t ≤
        (1 + 4 * quotientKernelError C N t) * quotientMainKernel N t := by
  let x : ℝ := N
  let r : ℝ := t
  let L : ℝ := Real.log N
  let a : ℝ := (N / (t + 1) : ℕ)
  let b : ℝ := (N / t : ℕ)
  let m : ℝ := x / (r * (r + 1))
  let d : ℝ := b - a
  let e : ℝ := C * b / Real.log b ^ 2 + C * a / Real.log a ^ 2
  let η : ℝ := quotientKernelError C N t
  have hx : 0 < x := by dsimp [x]; positivity
  have hr : 0 < r := by dsimp [r]; exact_mod_cast ht
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos (by exact_mod_cast hN)
  have hm : 0 < m := by dsimp [m]; positivity
  have haNat : 2 ≤ N / (t + 1) := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < t + 1)]
    simpa [Nat.mul_comm] using hNt
  have habNat : N / (t + 1) ≤ N / t :=
    Nat.div_le_div_left (by omega) (by omega)
  have haPos : 0 < a := by dsimp [a]; exact_mod_cast (by omega : 0 < N / (t + 1))
  have hbPos : 0 < b := by dsimp [b]; exact_mod_cast (by omega : 0 < N / t)
  have hlaPos : 0 < Real.log a := Real.log_pos (by
    dsimp [a]
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two haNat))
  have hlbPos : 0 < Real.log b := Real.log_pos (by
    dsimp [b]
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two (haNat.trans habNat)))
  have haUpper : a ≤ x / (r + 1) := by
    dsimp [a, x, r]
    simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := t + 1))
  have hbUpper : b ≤ x / r := by
    dsimp [b, x, r]
    exact Nat.cast_div_le
  have haLower : x / (2 * (r + 1)) ≤ a := by
    have hfloor := natCast_div_sub_one_lt (N := N) (show 0 < t + 1 by omega)
    have hy : (2 : ℝ) ≤ x / (r + 1) := by
      dsimp [x, r]
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast hNt
    have hid : x / (2 * (r + 1)) = (x / (r + 1)) / 2 := by
      field_simp [ne_of_gt (show 0 < r + 1 by linarith)]
    rw [hid]
    dsimp [a, x, r] at hfloor hy ⊢
    norm_num at hfloor
    linarith
  have hlogArg : Real.log (2 * (r + 1)) ≤ L := by
    apply Real.strictMonoOn_log.monotoneOn
    · simp only [Set.mem_Ioi]
      positivity
    · simp only [Set.mem_Ioi]
      exact hx
    · dsimp [x, r]
      exact_mod_cast hNt
  have hla :
      (1 - Real.log (2 * (r + 1)) / L) * L ≤ Real.log a := by
    have hlogLower : Real.log (x / (2 * (r + 1))) ≤ Real.log a :=
      Real.log_le_log (by positivity) haLower
    rw [Real.log_div (ne_of_gt hx) (by positivity), Real.log_mul
      (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hlogLower
    calc
      (1 - Real.log (2 * (r + 1)) / L) * L =
          L - Real.log (2 * (r + 1)) := by field_simp
      _ = Real.log x - (Real.log 2 + Real.log (r + 1)) := by
        dsimp [L]
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
      _ ≤ Real.log a := hlogLower
  have hlb : Real.log b ≤ L := by
    have hrOne : (1 : ℝ) ≤ r := by dsimp [r]; exact_mod_cast ht
    have hbLeX : b ≤ x := hbUpper.trans (div_le_self hx.le hrOne)
    exact Real.log_le_log hbPos hbLeX
  have hwidth := quotientInterval_width_bounds (N := N) (t := t) (by omega)
  have hηform : η = (r * (r + 1)) / x +
      8 * C * (r + 1) / L ^ 2 +
      Real.log (2 * (r + 1)) / L := by
    simp [η, quotientKernelError, x, r, L]
  have hLogNonneg : 0 ≤ Real.log (2 * (r + 1)) := by
    apply Real.log_nonneg
    nlinarith
  have hη0 : 0 ≤ η := by
    rw [hηform]
    positivity
  have hFloorPart : ((r * (r + 1)) / x) * m = 1 := by
    dsimp [m]
    field_simp [ne_of_gt hx, ne_of_gt hr, ne_of_gt (show 0 < r + 1 by linarith)]
  have hExtra : 0 ≤ 8 * C * (r + 1) / L ^ 2 +
      Real.log (2 * (r + 1)) / L := by positivity
  have hTotal : 1 ≤ ((r * (r + 1)) / x +
      8 * C * (r + 1) / L ^ 2 +
      Real.log (2 * (r + 1)) / L) * m := by
    rw [add_mul, add_mul, hFloorPart]
    have := mul_nonneg hExtra hm.le
    linarith
  have hdlo : (1 - η) * m ≤ d := by
    have hw : m - 1 ≤ d := by simpa [m, d, x, r] using hwidth.1
    rw [hηform, sub_mul]
    nlinarith
  have hdhi : d ≤ (1 + η) * m := by
    have hw : d ≤ m + 1 := by simpa [m, d, x, r] using hwidth.2
    rw [hηform, add_mul]
    nlinarith
  have hLogTermLeEta : Real.log (2 * (r + 1)) / L ≤ η := by
    rw [hηform]
    have hfirst : 0 ≤ r * (r + 1) / x := by positivity
    have hsecond : 0 ≤ 8 * C * (r + 1) / L ^ 2 := by positivity
    linarith
  have hlogCommon : (1 - η) * L ≤ Real.log a := by
    have : (1 - η) * L ≤
        (1 - Real.log (2 * (r + 1)) / L) * L :=
      mul_le_mul_of_nonneg_right (by linarith) hL.le
    exact this.trans hla
  have haLeB : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast habNat
  have e0 : 0 ≤ e := by dsimp [e]; positivity
  have hhalf : L / 2 ≤ Real.log a := by
    have := hlogCommon
    nlinarith [mul_pos hL (show 0 < 1 / 4 by norm_num)]
  have hInvA : 1 / Real.log a ^ 2 ≤ 4 / L ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hlaPos) (sq_pos_of_pos hL)]
    nlinarith [sq_nonneg (Real.log a - L / 2)]
  have hLogAB : Real.log a ≤ Real.log b :=
    Real.log_le_log haPos haLeB
  have hInvB : 1 / Real.log b ^ 2 ≤ 4 / L ^ 2 := by
    have hsquares : (Real.log a) ^ 2 ≤ (Real.log b) ^ 2 :=
      (sq_le_sq₀ (Real.log_nonneg (by
        dsimp [a]
        exact_mod_cast (show 1 ≤ N / (t + 1) by omega))) (Real.log_nonneg (by
          dsimp [b]
          exact_mod_cast (show 1 ≤ N / t by omega)))).2 hLogAB
    exact (one_div_le_one_div_of_le (sq_pos_of_pos hlaPos) hsquares).trans hInvA
  have he : e ≤ η * m := by
    have habUpper : a ≤ x / r := haUpper.trans (by
      apply div_le_div_of_nonneg_left hx.le hr
      linarith)
    have hTermA : C * a / Real.log a ^ 2 ≤
        C * (x / r) * (4 / L ^ 2) := by
      calc
        C * a / Real.log a ^ 2 = C * a * (1 / Real.log a ^ 2) := by ring
        _ ≤ C * (x / r) * (4 / L ^ 2) := by gcongr
    have hTermB : C * b / Real.log b ^ 2 ≤
        C * (x / r) * (4 / L ^ 2) := by
      calc
        C * b / Real.log b ^ 2 = C * b * (1 / Real.log b ^ 2) := by ring
        _ ≤ C * (x / r) * (4 / L ^ 2) := by gcongr
    have heRaw : e ≤ 8 * C * (x / r) / L ^ 2 := by
      dsimp [e]
      calc
        _ ≤ C * (x / r) * (4 / L ^ 2) +
            C * (x / r) * (4 / L ^ 2) := add_le_add hTermB hTermA
        _ = _ := by ring
    calc
      e ≤ 8 * C * (x / r) / L ^ 2 := heRaw
      _ = (8 * C * (r + 1) / L ^ 2) * m := by
        dsimp [m]
        field_simp [ne_of_gt hr, ne_of_gt hL,
          ne_of_gt (show 0 < r + 1 by linarith)]
      _ ≤ η * m := by
        apply mul_le_mul_of_nonneg_right _ hm.le
        rw [hηform]
        have hfirst : 0 ≤ r * (r + 1) / x := by positivity
        have hthird : 0 ≤ Real.log (2 * (r + 1)) / L := by positivity
        linarith
  have hsand := quotient_kernel_sandwich hη0 hη hm hL hdlo hdhi he
    hlogCommon hlb hlbPos
  have hmain : m / L = quotientMainKernel N t := by
    dsimp [m, L, x, r, quotientMainKernel]
    field_simp
  rw [hmain] at hsand
  simpa [η, d, e, a, b, quotientLowerCoefficient,
    quotientUpperCoefficient, add_assoc] using hsand

end Erdos321

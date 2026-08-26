import ErdosProblems.Erdos1002.FixedAwayUnshiftedAbel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An unconditional elementary middle range for the unshifted carrier

The zero Fourier carrier does not require a Chan--Kumchev prefix estimate
on every denominator between `sqrt K` and the terminal cutoff.  On one
dyadic denominator shell the reciprocal-square Ramanujan vector already
has an absolute constant norm by incomplete orthogonality.  Combining that
fact with the proved bounded-variation estimate for the fixed-away
multiplier gives a constant bound for each shell.  Consequently `R`
successive denominator shells cost only `O(R)`, and the existing
divisor-square estimate handles the remaining tail.

This file contains only unconditional finite estimates.
-/

open Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- The elementary Ramanujan-vector constant on the rounded square-root
transition shell. -/
def fixedAwayUnshiftedElementaryRamanujanConstant : ℝ :=
  Real.sqrt 54

/-- A common fixed-away bound for every denominator shell beginning at a
point `Q` with `K ≤ 4Q²`.  The factor four is exactly what is needed when
`Q = ⌊sqrt K⌋`. -/
def fixedAwayUnshiftedElementaryShellConstant (t δ : ℝ) : ℝ :=
  fixedAwayUnshiftedElementaryRamanujanConstant *
    fixedAwayUnshiftedTransitionMultiplierConstant t δ

theorem fixedAwayUnshiftedElementaryRamanujanConstant_nonneg :
    0 ≤ fixedAwayUnshiftedElementaryRamanujanConstant := by
  exact Real.sqrt_nonneg 54

theorem fixedAwayUnshiftedElementaryShellConstant_nonneg
    (t δ : ℝ) :
    0 ≤ fixedAwayUnshiftedElementaryShellConstant t δ := by
  exact mul_nonneg
    fixedAwayUnshiftedElementaryRamanujanConstant_nonneg
    (fixedAwayUnshiftedTransitionMultiplierConstant_nonneg t δ)

/-- Every truncated reciprocal-square Ramanujan vector in a denominator
shell satisfying the rounded transition inequality `K ≤ 4Q²` has norm at
most `sqrt 54`. -/
theorem
    norm_euclideanIntervalPartialSum_nearRamanujan_dyadic_le_transitionRange
    (K Q R : ℕ) (hQ : 0 < Q) (hKQ : K ≤ 4 * Q ^ 2)
    (hR : R ∈ Finset.Icc (Q + 1) (2 * Q)) :
    ‖euclideanIntervalPartialSum
        (nearRamanujanVectorTerm K) (Q + 1) R‖ ≤
      fixedAwayUnshiftedElementaryRamanujanConstant := by
  have hsubset : Finset.Icc (Q + 1) R ⊆ Finset.Ioc Q (2 * Q) := by
    intro p hp
    have hpBounds := Finset.mem_Icc.mp hp
    have hRBounds := Finset.mem_Icc.mp hR
    exact Finset.mem_Ioc.mpr
      ⟨by omega, hpBounds.2.trans hRBounds.2⟩
  have hraw := norm_sum_nearRamanujanVectorTerm_dyadic_le
    (Finset.Icc (Q + 1) R) K Q hQ hsubset
  have hQleQsq : Q ≤ Q ^ 2 := by nlinarith
  have hOneleQsq : 1 ≤ Q ^ 2 := by nlinarith
  have hnumNat : 2 * K + 1 + 2 * Q ≤ 11 * Q ^ 2 := by omega
  have hden : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
  have hinside :
      2 * ((2 * K + 1 + 2 * Q : ℕ) : ℝ) / (Q : ℝ) ^ 2 + 32 ≤
        54 := by
    have hnumReal :
        ((2 * K + 1 + 2 * Q : ℕ) : ℝ) ≤ 11 * (Q : ℝ) ^ 2 := by
      exact_mod_cast hnumNat
    have hfrac :
        2 * ((2 * K + 1 + 2 * Q : ℕ) : ℝ) / (Q : ℝ) ^ 2 ≤
          22 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    linarith
  rw [euclideanIntervalPartialSum]
  exact hraw.trans <| by
    unfold fixedAwayUnshiftedElementaryRamanujanConstant
    exact Real.sqrt_le_sqrt hinside

/-- Unconditional `O(1)` estimate for one complete or truncated
fixed-away denominator shell at and above the rounded square-root
transition. -/
theorem norm_fixedAwayUnshiftedFiniteVector_le_elementaryShell
    {t δ : ℝ} {K Q U : ℕ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q) (hKQ : K ≤ 4 * Q ^ 2)
    (hQU : Q + 1 ≤ U) (hU2Q : U ≤ 2 * Q) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U‖ ≤
      fixedAwayUnshiftedElementaryShellConstant t δ := by
  let M : ℝ := fixedAwayUnshiftedElementaryRamanujanConstant
  have hpartial : ∀ R ∈ Finset.Icc (Q + 1) U,
      ‖euclideanIntervalPartialSum
          (nearRamanujanVectorTerm K) (Q + 1) R‖ ≤ M := by
    intro R hR
    apply
      norm_euclideanIntervalPartialSum_nearRamanujan_dyadic_le_transitionRange
        K Q R hQ hKQ
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hR).1,
        (Finset.mem_Icc.mp hR).2.trans hU2Q⟩
  have habel := norm_euclidean_vector_sum_coordinateMul_le
    (nearRamanujanVectorTerm K)
    (fun p ↦ fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))
    hQU M hpartial
  have hmult :=
    fixedAwayUnshiftedDyadicMultiplier_terminal_add_variation_le_transitionShell
      hδ hδt hK hQ hKQ hQU hU2Q
  have hM : 0 ≤ M := by
    exact fixedAwayUnshiftedElementaryRamanujanConstant_nonneg
  change ‖∑ p ∈ Finset.Icc (Q + 1) U,
      euclideanCoordinateMul (nearRamanujanVectorTerm K p)
        (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))‖ ≤ _
  calc
    ‖∑ p ∈ Finset.Icc (Q + 1) U,
        euclideanCoordinateMul (nearRamanujanVectorTerm K p)
          (fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ))‖ ≤
      M *
        (‖fixedAwayUnshiftedDyadicMultiplier t δ K (U : ℝ)‖ +
          ∑ p ∈ Finset.Ico (Q + 1) U,
            ‖fixedAwayUnshiftedDyadicMultiplier t δ K (p : ℝ) -
              fixedAwayUnshiftedDyadicMultiplier t δ K
                ((p + 1 : ℕ) : ℝ)‖) := habel
    _ ≤ M * fixedAwayUnshiftedTransitionMultiplierConstant t δ :=
      mul_le_mul_of_nonneg_left hmult hM
    _ = fixedAwayUnshiftedElementaryShellConstant t δ := rfl

/-- The exact denominator interval obtained after `R` doublings. -/
def fixedAwayUnshiftedElementaryMiddleEndpoint
    (Q R : ℕ) : ℕ :=
  2 ^ R * Q

/-- `R` consecutive denominator shells above a rounded square-root point
have norm at most `R` times one absolute shell constant. -/
theorem norm_fixedAwayUnshiftedFiniteVector_le_elementaryMiddle
    {t δ : ℝ} {K Q : ℕ} (R : ℕ)
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q) (hKQ : K ≤ 4 * Q ^ 2) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1)
        (fixedAwayUnshiftedElementaryMiddleEndpoint Q R)‖ ≤
      (R : ℝ) * fixedAwayUnshiftedElementaryShellConstant t δ := by
  induction R with
  | zero =>
      simp [fixedAwayUnshiftedElementaryMiddleEndpoint,
        fixedAwayUnshiftedFiniteVector]
  | succ R ih =>
      let P : ℕ := fixedAwayUnshiftedElementaryMiddleEndpoint Q R
      have hQP : Q ≤ P := by
        dsimp [P, fixedAwayUnshiftedElementaryMiddleEndpoint]
        nlinarith [Nat.one_le_two_pow (n := R)]
      have hP : 0 < P := hQ.trans_le hQP
      have hKQ' : K ≤ 4 * P ^ 2 := by
        exact hKQ.trans <| by
          gcongr
      have hPsucc :
          fixedAwayUnshiftedElementaryMiddleEndpoint Q (R + 1) =
            2 * P := by
        dsimp [P, fixedAwayUnshiftedElementaryMiddleEndpoint]
        rw [pow_succ]
        ring
      have hshell :
          ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) (2 * P)‖ ≤
            fixedAwayUnshiftedElementaryShellConstant t δ :=
        norm_fixedAwayUnshiftedFiniteVector_le_elementaryShell
          hδ hδt hK hP hKQ' (by omega) le_rfl
      have hdisjoint :
          Disjoint (Finset.Ioc Q P) (Finset.Ioc P (2 * P)) := by
        rw [Finset.disjoint_left]
        intro p hpLeft hpRight
        have hl := Finset.mem_Ioc.mp hpLeft
        have hr := Finset.mem_Ioc.mp hpRight
        omega
      have hsplit :
          fixedAwayUnshiftedFiniteVector t δ K (Q + 1) (2 * P) =
            fixedAwayUnshiftedFiniteVector t δ K (Q + 1) P +
              fixedAwayUnshiftedFiniteVector t δ K (P + 1) (2 * P) := by
        rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
          fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
          fixedAwayUnshiftedFiniteVector_eq_sum_Ioc]
        rw [← Finset.sum_union hdisjoint]
        rw [Finset.Ioc_union_Ioc_eq_Ioc hQP (by omega)]
      rw [hPsucc, hsplit]
      calc
        ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) P +
            fixedAwayUnshiftedFiniteVector t δ K (P + 1) (2 * P)‖ ≤
          ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) P‖ +
            ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) (2 * P)‖ :=
          norm_add_le _ _
        _ ≤ (R : ℝ) *
              fixedAwayUnshiftedElementaryShellConstant t δ +
            fixedAwayUnshiftedElementaryShellConstant t δ :=
          add_le_add ih hshell
        _ = ((R + 1 : ℕ) : ℝ) *
              fixedAwayUnshiftedElementaryShellConstant t δ := by
          push_cast
          ring

/-- Endpoint-flexible version of the elementary middle estimate.  Every
partial interval ending before the `R`-th doubled endpoint obeys the same
`R`-shell bound. -/
theorem norm_fixedAwayUnshiftedFiniteVector_le_elementaryMiddle_truncated
    {t δ : ℝ} {K Q R U : ℕ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q) (hKQ : K ≤ 4 * Q ^ 2)
    (hQU : Q ≤ U)
    (hUP : U ≤ fixedAwayUnshiftedElementaryMiddleEndpoint Q R) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U‖ ≤
      (R : ℝ) * fixedAwayUnshiftedElementaryShellConstant t δ := by
  induction R generalizing U with
  | zero =>
      have hUQ : U ≤ Q := by
        simpa [fixedAwayUnshiftedElementaryMiddleEndpoint] using! hUP
      have hUeq : U = Q := le_antisymm hUQ hQU
      subst U
      simp [fixedAwayUnshiftedFiniteVector]
  | succ R ih =>
      let P : ℕ := fixedAwayUnshiftedElementaryMiddleEndpoint Q R
      have hQP : Q ≤ P := by
        dsimp [P, fixedAwayUnshiftedElementaryMiddleEndpoint]
        nlinarith [Nat.one_le_two_pow (n := R)]
      have hP : 0 < P := hQ.trans_le hQP
      have hKQ' : K ≤ 4 * P ^ 2 := by
        exact hKQ.trans <| by
          gcongr
      have hPsucc :
          fixedAwayUnshiftedElementaryMiddleEndpoint Q (R + 1) =
            2 * P := by
        dsimp [P, fixedAwayUnshiftedElementaryMiddleEndpoint]
        rw [pow_succ]
        ring
      have hU2P : U ≤ 2 * P := by
        rw [← hPsucc]
        exact hUP
      have hC :
          0 ≤ fixedAwayUnshiftedElementaryShellConstant t δ :=
        fixedAwayUnshiftedElementaryShellConstant_nonneg t δ
      by_cases hUPrev : U ≤ P
      · have hprev := ih hQU hUPrev
        exact hprev.trans <| by
          have hRle : (R : ℝ) ≤ (R + 1 : ℕ) := by norm_num
          exact mul_le_mul_of_nonneg_right hRle hC
      · have hPU : P < U := lt_of_not_ge hUPrev
        have hmiddle :=
          norm_fixedAwayUnshiftedFiniteVector_le_elementaryMiddle
            R hδ hδt hK hQ hKQ
        have hshell :=
          norm_fixedAwayUnshiftedFiniteVector_le_elementaryShell
            hδ hδt hK hP hKQ' (by omega) hU2P
        have hdisjoint :
            Disjoint (Finset.Ioc Q P) (Finset.Ioc P U) := by
          rw [Finset.disjoint_left]
          intro p hpLeft hpRight
          have hl := Finset.mem_Ioc.mp hpLeft
          have hr := Finset.mem_Ioc.mp hpRight
          omega
        have hsplit :
            fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U =
              fixedAwayUnshiftedFiniteVector t δ K (Q + 1) P +
                fixedAwayUnshiftedFiniteVector t δ K (P + 1) U := by
          rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
            fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
            fixedAwayUnshiftedFiniteVector_eq_sum_Ioc]
          rw [← Finset.sum_union hdisjoint]
          rw [Finset.Ioc_union_Ioc_eq_Ioc hQP hPU.le]
        rw [hsplit]
        calc
          ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) P +
              fixedAwayUnshiftedFiniteVector t δ K (P + 1) U‖ ≤
            ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) P‖ +
              ‖fixedAwayUnshiftedFiniteVector t δ K (P + 1) U‖ :=
            norm_add_le _ _
          _ ≤ (R : ℝ) *
                fixedAwayUnshiftedElementaryShellConstant t δ +
              fixedAwayUnshiftedElementaryShellConstant t δ :=
            add_le_add hmiddle hshell
          _ = ((R + 1 : ℕ) : ℝ) *
                fixedAwayUnshiftedElementaryShellConstant t δ := by
            push_cast
            ring

/-- After at least one elementary middle shell, the endpoint lies in the
true high range `K ≤ P²`, so the existing divisor-square estimate may be
attached without a gap. -/
theorem norm_fixedAwayUnshiftedFiniteVector_le_elementaryMiddleThenDivisor
    {t δ : ℝ} {K Q R U : ℕ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hK : 0 < K) (hQ : 0 < Q) (hKQ : K ≤ 4 * Q ^ 2)
    (hR : 1 ≤ R)
    (hPU : fixedAwayUnshiftedElementaryMiddleEndpoint Q R < U) :
    ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U‖ ≤
      (R : ℝ) * fixedAwayUnshiftedElementaryShellConstant t δ +
        (12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
            Real.sqrt (K : ℝ) /
            (fixedAwayUnshiftedElementaryMiddleEndpoint Q R : ℝ)) *
          fixedAwayUnshiftedHighMultiplierConstant t δ := by
  let P : ℕ := fixedAwayUnshiftedElementaryMiddleEndpoint Q R
  have hQPtwo : 2 * Q ≤ P := by
    dsimp [P, fixedAwayUnshiftedElementaryMiddleEndpoint]
    have hpow : 2 ≤ 2 ^ R := by
      simpa only [pow_one] using!
        Nat.pow_le_pow_right (by omega : 0 < 2) hR
    nlinarith
  have hP : 0 < P := by
    have htwoQ : 0 < 2 * Q := by positivity
    exact htwoQ.trans_le hQPtwo
  have hKP : K ≤ P ^ 2 := by
    calc
      K ≤ 4 * Q ^ 2 := hKQ
      _ = (2 * Q) ^ 2 := by ring
      _ ≤ P ^ 2 := Nat.pow_le_pow_left hQPtwo 2
  have hmiddle :=
    norm_fixedAwayUnshiftedFiniteVector_le_elementaryMiddle
      R hδ hδt hK hQ hKQ
  have htail :=
    norm_fixedAwayUnshiftedFiniteVector_tail_le_highShell_divisorSquare
      K P U hδ hδt hK hP hKP hPU
  have hQP : Q ≤ P := le_trans (by omega) hQPtwo
  have hdisjoint :
      Disjoint (Finset.Ioc Q P) (Finset.Ioc P U) := by
    rw [Finset.disjoint_left]
    intro p hpLeft hpRight
    have hl := Finset.mem_Ioc.mp hpLeft
    have hr := Finset.mem_Ioc.mp hpRight
    omega
  have hsplit :
      fixedAwayUnshiftedFiniteVector t δ K (Q + 1) U =
        fixedAwayUnshiftedFiniteVector t δ K (Q + 1) P +
          fixedAwayUnshiftedFiniteVector t δ K (P + 1) U := by
    rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
      fixedAwayUnshiftedFiniteVector_eq_sum_Ioc,
      fixedAwayUnshiftedFiniteVector_eq_sum_Ioc]
    rw [← Finset.sum_union hdisjoint]
    rw [Finset.Ioc_union_Ioc_eq_Ioc hQP hPU.le]
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hmiddle htail)

/-! ## A concrete choice on the frequency shell `K = 2^s` -/

/-- The exact lower denominator endpoint used on the frequency shell
`K = 2^s`. -/
def fixedAwayUnshiftedPowerShellBase (s : ℕ) : ℕ :=
  2 ^ (s / 2)

/-- Four powers of `s + 2` are more than enough to absorb the cubic
harmonic loss in the divisor-square tail. -/
def fixedAwayUnshiftedPowerShellMiddleCount (s : ℕ) : ℕ :=
  Nat.clog 2 ((s + 2) ^ 4)

def fixedAwayUnshiftedPowerShellMiddleEndpoint (s : ℕ) : ℕ :=
  fixedAwayUnshiftedElementaryMiddleEndpoint
    (fixedAwayUnshiftedPowerShellBase s)
    (fixedAwayUnshiftedPowerShellMiddleCount s)

theorem fixedAwayUnshiftedPowerShellBase_pos (s : ℕ) :
    0 < fixedAwayUnshiftedPowerShellBase s := by
  unfold fixedAwayUnshiftedPowerShellBase
  positivity

theorem fixedAwayUnshiftedPowerShellBase_sq_le (s : ℕ) :
    fixedAwayUnshiftedPowerShellBase s ^ 2 ≤ 2 ^ s := by
  have hexp : (s / 2) * 2 ≤ s := Nat.div_mul_le_self s 2
  unfold fixedAwayUnshiftedPowerShellBase
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by omega : 0 < 2) hexp

theorem fixedAwayUnshiftedPowerShell_le_four_base_sq (s : ℕ) :
    2 ^ s ≤ 4 * fixedAwayUnshiftedPowerShellBase s ^ 2 := by
  have hmod : s % 2 < 2 := Nat.mod_lt s (by omega)
  have hdecomp : s % 2 + 2 * (s / 2) = s :=
    Nat.mod_add_div s 2
  have hexp : s ≤ 2 + 2 * (s / 2) := by omega
  have hpow :
      2 ^ s ≤ 2 ^ (2 + 2 * (s / 2)) :=
    Nat.pow_le_pow_right (by omega : 0 < 2) hexp
  calc
    2 ^ s ≤ 2 ^ (2 + 2 * (s / 2)) := hpow
    _ = 4 * fixedAwayUnshiftedPowerShellBase s ^ 2 := by
      unfold fixedAwayUnshiftedPowerShellBase
      rw [pow_add]
      norm_num only [pow_two]
      rw [show 2 * (s / 2) = (s / 2) * 2 by omega, pow_mul]
      rw [pow_two]

theorem fixedAwayUnshiftedPowerShellMiddleCount_pos (s : ℕ) :
    0 < fixedAwayUnshiftedPowerShellMiddleCount s := by
  apply Nat.clog_pos (by omega : 1 < 2)
  change 1 < (s + 2) ^ 4
  have htwo : 2 ≤ s + 2 := by omega
  have hpow : 2 ^ 4 ≤ (s + 2) ^ 4 :=
    Nat.pow_le_pow_left htwo 4
  exact (by norm_num : 1 < 2 ^ 4) |>.trans_le hpow

/-- Exact logarithmic control of the number of elementary denominator
shells. -/
theorem fixedAwayUnshiftedPowerShellMiddleCount_le (s : ℕ) :
    fixedAwayUnshiftedPowerShellMiddleCount s ≤
      4 * Nat.clog 2 (s + 2) := by
  let c : ℕ := Nat.clog 2 (s + 2)
  have hbase : s + 2 ≤ 2 ^ c := by
    dsimp [c]
    exact Nat.le_pow_clog (by omega) (s + 2)
  have hpow : (s + 2) ^ 4 ≤ 2 ^ (4 * c) := by
    calc
      (s + 2) ^ 4 ≤ (2 ^ c) ^ 4 :=
        Nat.pow_le_pow_left hbase 4
      _ = 2 ^ (4 * c) := by
        rw [← pow_mul]
        congr 1
        omega
  unfold fixedAwayUnshiftedPowerShellMiddleCount
  exact Nat.clog_le_of_le_pow hpow

theorem harmonic_two_mul_two_pow_le_powerShell (s : ℕ) :
    (harmonic (2 * 2 ^ s) : ℝ) ≤ (s + 2 : ℕ) := by
  have hraw := harmonic_le_one_add_log (2 * 2 ^ s)
  have harg :
      (((2 * 2 ^ s : ℕ) : ℝ)) = (2 : ℝ) ^ (s + 1) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_succ]
    ring
  have hlog :
      Real.log (((2 * 2 ^ s : ℕ) : ℝ)) =
        (s + 1 : ℕ) * Real.log 2 := by
    rw [harg, Real.log_pow]
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h :=
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  rw [hlog] at hraw
  have hs : 0 ≤ ((s + 1 : ℕ) : ℝ) := by positivity
  calc
    (harmonic (2 * 2 ^ s) : ℝ) ≤
        1 + ((s + 1 : ℕ) : ℝ) * Real.log 2 := hraw
    _ ≤ 1 + ((s + 1 : ℕ) : ℝ) * 1 := by gcongr
    _ = ((s + 2 : ℕ) : ℝ) := by push_cast; ring

/-- With the concrete middle endpoint, the complete divisor-square tail
factor is bounded by an absolute constant. -/
theorem fixedAwayUnshiftedPowerShell_divisorFactor_le
    (s : ℕ) :
    Real.sqrt (2 * (harmonic (2 * 2 ^ s) : ℝ) ^ 3) *
          Real.sqrt ((2 ^ s : ℕ) : ℝ) /
          (fixedAwayUnshiftedPowerShellMiddleEndpoint s : ℝ) ≤
      4 := by
  let q : ℕ := fixedAwayUnshiftedPowerShellBase s
  let r : ℕ := fixedAwayUnshiftedPowerShellMiddleCount s
  let x : ℝ := (s + 2 : ℕ)
  have hq : 0 < q := by
    dsimp [q]
    exact fixedAwayUnshiftedPowerShellBase_pos s
  have hr : 0 < r := by
    dsimp [r]
    exact fixedAwayUnshiftedPowerShellMiddleCount_pos s
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast (show 2 ≤ s + 2 by omega)
  have hx0 : 0 ≤ x := by linarith
  have hqFour : 2 ^ s ≤ 4 * q ^ 2 := by
    dsimp [q]
    exact fixedAwayUnshiftedPowerShell_le_four_base_sq s
  have hsqrt :
      Real.sqrt ((2 ^ s : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)]
    rw [Real.sq_sqrt (by positivity :
      0 ≤ ((2 ^ s : ℕ) : ℝ))]
    have hqFourReal :
        (((2 ^ s : ℕ) : ℝ)) ≤ 4 * (q : ℝ) ^ 2 := by
      exact_mod_cast hqFour
    nlinarith
  have hharm :
      (harmonic (2 * 2 ^ s) : ℝ) ≤ x := by
    dsimp [x]
    exact harmonic_two_mul_two_pow_le_powerShell s
  have hharm0 : 0 ≤ (harmonic (2 * 2 ^ s) : ℝ) := by
    exact_mod_cast
      (harmonic_pos (by positivity : 2 * 2 ^ s ≠ 0)).le
  have hcube :
      (harmonic (2 * 2 ^ s) : ℝ) ^ 3 ≤ x ^ 3 :=
    pow_le_pow_left₀ hharm0 hharm 3
  have hxCube : x ^ 3 ≤ x ^ 4 := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hroot :
      Real.sqrt (2 * (harmonic (2 * 2 ^ s) : ℝ) ^ 3) ≤
        2 * x ^ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · calc
        2 * (harmonic (2 * 2 ^ s) : ℝ) ^ 3 ≤
            2 * x ^ 3 := by gcongr
        _ ≤ 4 * x ^ 4 := by nlinarith
        _ = (2 * x ^ 2) ^ 2 := by ring
  have hrpowNat : (s + 2) ^ 4 ≤ 2 ^ r := by
    dsimp [r, fixedAwayUnshiftedPowerShellMiddleCount]
    exact Nat.le_pow_clog (by omega) ((s + 2) ^ 4)
  have hrpow : x ^ 4 ≤ (2 ^ r : ℕ) := by
    dsimp [x]
    exact_mod_cast hrpowNat
  have hpowPos : (0 : ℝ) < (2 ^ r : ℕ) := by positivity
  have hqPos : (0 : ℝ) < (q : ℕ) := by exact_mod_cast hq
  have hden :
      (0 : ℝ) <
        (fixedAwayUnshiftedPowerShellMiddleEndpoint s : ℕ) := by
    unfold fixedAwayUnshiftedPowerShellMiddleEndpoint
      fixedAwayUnshiftedElementaryMiddleEndpoint
    positivity
  have hreplace :
      Real.sqrt (2 * (harmonic (2 * 2 ^ s) : ℝ) ^ 3) *
          Real.sqrt ((2 ^ s : ℕ) : ℝ) ≤
        (2 * x ^ 2) * (2 * (q : ℝ)) := by
    exact mul_le_mul hroot hsqrt (Real.sqrt_nonneg _) (by positivity)
  calc
    Real.sqrt (2 * (harmonic (2 * 2 ^ s) : ℝ) ^ 3) *
          Real.sqrt ((2 ^ s : ℕ) : ℝ) /
          (fixedAwayUnshiftedPowerShellMiddleEndpoint s : ℝ) ≤
        ((2 * x ^ 2) * (2 * (q : ℝ))) /
          (fixedAwayUnshiftedPowerShellMiddleEndpoint s : ℝ) :=
      div_le_div_of_nonneg_right hreplace hden.le
    _ = 4 * x ^ 2 / (2 ^ r : ℕ) := by
      change
        (2 * x ^ 2 * (2 * (q : ℝ))) /
            (((2 ^ r) * q : ℕ) : ℝ) =
          4 * x ^ 2 / (((2 ^ r : ℕ) : ℝ))
      push_cast
      field_simp [hqPos.ne', hpowPos.ne']
      ring
    _ ≤ 4 * x ^ 2 / x ^ 4 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hrpow
    _ ≤ 4 := by
      have hxSq : 1 ≤ x ^ 2 := by nlinarith [sq_nonneg x]
      rw [show x ^ 4 = x ^ 2 * x ^ 2 by ring]
      field_simp
      nlinarith [sq_pos_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx)]

/-! ## Uniform one-frequency-shell estimate -/

def fixedAwayUnshiftedElementaryShellUniformConstant
    (T δ : ℝ) : ℝ :=
  fixedAwayUnshiftedElementaryRamanujanConstant *
    fixedAwayUnshiftedTransitionMultiplierUniformConstant T δ

def fixedAwayUnshiftedPowerShellUniformBound
    (T δ : ℝ) (s : ℕ) : ℝ :=
  2 * fixedAwayUnshiftedLowShellUniformConstant T δ +
    (fixedAwayUnshiftedPowerShellMiddleCount s : ℝ) *
      fixedAwayUnshiftedElementaryShellUniformConstant T δ +
    48 * fixedAwayUnshiftedHighMultiplierUniformConstant T δ

theorem fixedAwayUnshiftedLowShellUniformConstant_nonneg_of_nonneg
    {T δ : ℝ} (hT : 0 ≤ T) :
    0 ≤ fixedAwayUnshiftedLowShellUniformConstant T δ := by
  have hderiv0 := fixedAwayDerivativeUniformBound_nonneg hT δ 0
  have hderiv2 := fixedAwayDerivativeUniformBound_nonneg hT δ 2
  unfold fixedAwayUnshiftedLowShellUniformConstant
    fixedAwayPVInverseDecayUniformConstant
    fixedAwayDerivativeCauchyUniformConstant
  positivity

theorem fixedAwayUnshiftedHighMultiplierUniformConstant_nonneg_of_nonneg
    {T δ : ℝ} (hT : 0 ≤ T) :
    0 ≤ fixedAwayUnshiftedHighMultiplierUniformConstant T δ := by
  have hlocal := fixedAwayPVLocalUniformBound_nonneg hT
  have hderiv0 := fixedAwayDerivativeUniformBound_nonneg hT δ 0
  have hderiv2 := fixedAwayDerivativeUniformBound_nonneg hT δ 2
  unfold fixedAwayUnshiftedHighMultiplierUniformConstant
    fixedAwayPVGlobalDecayUniformConstant
  positivity

theorem
    fixedAwayUnshiftedTransitionMultiplierUniformConstant_nonneg_of_nonneg
    {T δ : ℝ} (hT : 0 ≤ T) :
    0 ≤ fixedAwayUnshiftedTransitionMultiplierUniformConstant T δ := by
  have hlocal := fixedAwayPVLocalUniformBound_nonneg hT
  have hderiv0 := fixedAwayDerivativeUniformBound_nonneg hT δ 0
  have hderiv2 := fixedAwayDerivativeUniformBound_nonneg hT δ 2
  unfold fixedAwayUnshiftedTransitionMultiplierUniformConstant
    fixedAwayPVGlobalDecayUniformConstant
  positivity

theorem fixedAwayUnshiftedElementaryShellUniformConstant_nonneg
    {T δ : ℝ} (hT : 0 ≤ T) :
    0 ≤ fixedAwayUnshiftedElementaryShellUniformConstant T δ := by
  exact mul_nonneg
    fixedAwayUnshiftedElementaryRamanujanConstant_nonneg
    (fixedAwayUnshiftedTransitionMultiplierUniformConstant_nonneg_of_nonneg
      hT)

theorem fixedAwayUnshiftedPowerShellUniformBound_nonneg
    {T δ : ℝ} (hT : 0 ≤ T) (s : ℕ) :
    0 ≤ fixedAwayUnshiftedPowerShellUniformBound T δ s := by
  unfold fixedAwayUnshiftedPowerShellUniformBound
  have hlow :=
    fixedAwayUnshiftedLowShellUniformConstant_nonneg_of_nonneg
      (T := T) (δ := δ) hT
  have hmiddle :=
    fixedAwayUnshiftedElementaryShellUniformConstant_nonneg
      (T := T) (δ := δ) hT
  have hhigh :=
    fixedAwayUnshiftedHighMultiplierUniformConstant_nonneg_of_nonneg
      (T := T) (δ := δ) hT
  positivity

theorem fixedAwayUnshiftedElementaryShellConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T) :
    fixedAwayUnshiftedElementaryShellConstant t δ ≤
      fixedAwayUnshiftedElementaryShellUniformConstant T δ := by
  unfold fixedAwayUnshiftedElementaryShellConstant
    fixedAwayUnshiftedElementaryShellUniformConstant
  exact mul_le_mul_of_nonneg_left
    (fixedAwayUnshiftedTransitionMultiplierConstant_le_uniform
      hδ hδt.le htT)
    fixedAwayUnshiftedElementaryRamanujanConstant_nonneg

/-- The complete low denominator range on `K = 2^s` is uniformly bounded
in the moving fixed-away threshold. -/
theorem norm_fixedAwayUnshiftedFiniteVector_powerShell_low_le_uniform
    {t δ T : ℝ} (s U : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T)
    (hU : 1 ≤ U)
    (hUQ : U ≤ fixedAwayUnshiftedPowerShellBase s) :
    ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 U‖ ≤
      2 * fixedAwayUnshiftedLowShellUniformConstant T δ := by
  let K : ℕ := 2 ^ s
  let Q : ℕ := fixedAwayUnshiftedPowerShellBase s
  have hK : 0 < K := by positivity
  have hQ : 0 < Q := by
    dsimp [Q]
    exact fixedAwayUnshiftedPowerShellBase_pos s
  have hQK : Q ^ 2 ≤ K := by
    dsimp [Q, K]
    exact fixedAwayUnshiftedPowerShellBase_sq_le s
  have hUK : U ^ 2 ≤ K :=
    (Nat.pow_le_pow_left hUQ 2).trans hQK
  have hraw :=
    norm_fixedAwayUnshiftedFiniteVector_two_le_lowRange
      K U hδ hδt hK hU hUK
  have hQroot : (Q : ℝ) ≤ Real.sqrt (K : ℝ) := by
    have hsq : (Q : ℝ) ^ 2 ≤ (K : ℝ) := by exact_mod_cast hQK
    have hsqrt := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq (Nat.cast_nonneg Q)] using! hsqrt
  have hUroot : (U : ℝ) ≤ Real.sqrt (K : ℝ) :=
    (by exact_mod_cast hUQ : (U : ℝ) ≤ (Q : ℝ)).trans hQroot
  have hsqrtPos : 0 < Real.sqrt (K : ℝ) := by positivity
  have hratio : (U : ℝ) / Real.sqrt (K : ℝ) ≤ 1 :=
    (div_le_one₀ hsqrtPos).2 hUroot
  have hlocal :
      0 ≤ 2 * fixedAwayUnshiftedLowShellConstant t δ :=
    mul_nonneg (by norm_num)
      (fixedAwayUnshiftedLowShellConstant_nonneg t δ)
  have hactual :
      ‖fixedAwayUnshiftedFiniteVector t δ K 2 U‖ ≤
        2 * fixedAwayUnshiftedLowShellConstant t δ := by
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ K 2 U‖ ≤
          2 * fixedAwayUnshiftedLowShellConstant t δ *
            (U : ℝ) / Real.sqrt (K : ℝ) := hraw
      _ = (2 * fixedAwayUnshiftedLowShellConstant t δ) *
            ((U : ℝ) / Real.sqrt (K : ℝ)) := by ring
      _ ≤ (2 * fixedAwayUnshiftedLowShellConstant t δ) * 1 :=
        mul_le_mul_of_nonneg_left hratio hlocal
      _ = 2 * fixedAwayUnshiftedLowShellConstant t δ := by ring
  exact hactual.trans <| by
    gcongr
    exact fixedAwayUnshiftedLowShellConstant_le_uniform
      hδ hδt.le htT

/-- Complete unconditional fixed-away estimate on one positive frequency
shell.  The denominator range is split into:

* the elementary low range `p ≤ 2^(s/2)`;
* `clog₂((s+2)^4)` constant-cost dyadic middle shells;
* the divisor-square tail, whose remaining factor is at most four.

All constants are uniform for the moving threshold `δ < t ≤ T`. -/
theorem norm_fixedAwayUnshiftedFiniteVector_powerShell_le_uniform
    {t δ T : ℝ} (s N : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T) :
    ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ≤
      fixedAwayUnshiftedPowerShellUniformBound T δ s := by
  let K : ℕ := 2 ^ s
  let Q : ℕ := fixedAwayUnshiftedPowerShellBase s
  let R : ℕ := fixedAwayUnshiftedPowerShellMiddleCount s
  let P : ℕ := fixedAwayUnshiftedPowerShellMiddleEndpoint s
  have hK : 0 < K := by positivity
  have hQ : 0 < Q := by
    dsimp [Q]
    exact fixedAwayUnshiftedPowerShellBase_pos s
  have hQone : 1 ≤ Q := hQ
  have hKQ : K ≤ 4 * Q ^ 2 := by
    dsimp [K, Q]
    exact fixedAwayUnshiftedPowerShell_le_four_base_sq s
  have hR : 1 ≤ R := by
    dsimp [R]
    exact fixedAwayUnshiftedPowerShellMiddleCount_pos s
  have hPdef :
      P = fixedAwayUnshiftedElementaryMiddleEndpoint Q R := by
    rfl
  have hT0 : 0 ≤ T := hδ.le.trans hδt.le |>.trans htT
  have hlowUniform :
      0 ≤ fixedAwayUnshiftedLowShellUniformConstant T δ :=
    fixedAwayUnshiftedLowShellUniformConstant_nonneg_of_nonneg hT0
  have hmiddleUniform :
      0 ≤ fixedAwayUnshiftedElementaryShellUniformConstant T δ :=
    fixedAwayUnshiftedElementaryShellUniformConstant_nonneg hT0
  have hhighUniform :
      0 ≤ fixedAwayUnshiftedHighMultiplierUniformConstant T δ :=
    fixedAwayUnshiftedHighMultiplierUniformConstant_nonneg_of_nonneg hT0
  have hboundNonneg :
      0 ≤ fixedAwayUnshiftedPowerShellUniformBound T δ s :=
    fixedAwayUnshiftedPowerShellUniformBound_nonneg hT0 s
  by_cases hNone : N ≤ 1
  · have hempty : Finset.Icc 2 N = ∅ :=
      Finset.Icc_eq_empty (by omega)
    simp only [fixedAwayUnshiftedFiniteVector, hempty, Finset.sum_empty,
      norm_zero]
    exact hboundNonneg
  have hNone' : 1 ≤ N := by omega
  by_cases hNQ : N ≤ Q
  · have hlow :=
      norm_fixedAwayUnshiftedFiniteVector_powerShell_low_le_uniform
        s N hδ hδt htT hNone' hNQ
    exact hlow.trans <| by
      unfold fixedAwayUnshiftedPowerShellUniformBound
      have hmiddleTerm :
          0 ≤ (fixedAwayUnshiftedPowerShellMiddleCount s : ℝ) *
            fixedAwayUnshiftedElementaryShellUniformConstant T δ := by
        positivity
      have hhighTerm :
          0 ≤ 48 *
            fixedAwayUnshiftedHighMultiplierUniformConstant T δ := by
        positivity
      linarith
  have hQN : Q < N := lt_of_not_ge hNQ
  have hlow :
      ‖fixedAwayUnshiftedFiniteVector t δ K 2 Q‖ ≤
        2 * fixedAwayUnshiftedLowShellUniformConstant T δ := by
    simpa only [K, Q] using!
      norm_fixedAwayUnshiftedFiniteVector_powerShell_low_le_uniform
        s Q hδ hδt htT hQone le_rfl
  have hdisjoint :
      Disjoint (Finset.Ioc 1 Q) (Finset.Ioc Q N) := by
    rw [Finset.disjoint_left]
    intro p hpLeft hpRight
    have hl := Finset.mem_Ioc.mp hpLeft
    have hr := Finset.mem_Ioc.mp hpRight
    omega
  have hsplit :
      fixedAwayUnshiftedFiniteVector t δ K 2 N =
        fixedAwayUnshiftedFiniteVector t δ K 2 Q +
          fixedAwayUnshiftedFiniteVector t δ K (Q + 1) N := by
    rw [fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K 1,
      fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K 1,
      fixedAwayUnshiftedFiniteVector_eq_sum_Ioc t δ K Q]
    rw [← Finset.sum_union hdisjoint]
    rw [Finset.Ioc_union_Ioc_eq_Ioc hQone hQN.le]
  have hshellLe :
      fixedAwayUnshiftedElementaryShellConstant t δ ≤
        fixedAwayUnshiftedElementaryShellUniformConstant T δ :=
    fixedAwayUnshiftedElementaryShellConstant_le_uniform hδ hδt htT
  have hRnonneg : 0 ≤ (R : ℝ) := by positivity
  by_cases hNP : N ≤ P
  · have hmiddleRaw :=
      norm_fixedAwayUnshiftedFiniteVector_le_elementaryMiddle_truncated
        (K := K) (Q := Q) (R := R) (U := N)
        hδ hδt hK hQ hKQ hQN.le (by simpa only [hPdef] using! hNP)
    have hmiddle :
        ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) N‖ ≤
          (R : ℝ) *
            fixedAwayUnshiftedElementaryShellUniformConstant T δ :=
      hmiddleRaw.trans
        (mul_le_mul_of_nonneg_left hshellLe hRnonneg)
    rw [hsplit]
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ K 2 Q +
          fixedAwayUnshiftedFiniteVector t δ K (Q + 1) N‖ ≤
        ‖fixedAwayUnshiftedFiniteVector t δ K 2 Q‖ +
          ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) N‖ :=
        norm_add_le _ _
      _ ≤ 2 * fixedAwayUnshiftedLowShellUniformConstant T δ +
          (R : ℝ) *
            fixedAwayUnshiftedElementaryShellUniformConstant T δ :=
        add_le_add hlow hmiddle
      _ ≤ fixedAwayUnshiftedPowerShellUniformBound T δ s := by
        unfold fixedAwayUnshiftedPowerShellUniformBound
        dsimp [R]
        linarith
  · have hPN : P < N := lt_of_not_ge hNP
    have htailRaw :=
      norm_fixedAwayUnshiftedFiniteVector_le_elementaryMiddleThenDivisor
        (K := K) (Q := Q) (R := R) (U := N)
        hδ hδt hK hQ hKQ hR (by simpa only [hPdef] using! hPN)
    let F : ℝ :=
      Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
        Real.sqrt (K : ℝ) / (P : ℝ)
    have hF : F ≤ 4 := by
      dsimp [F, K, P]
      exact fixedAwayUnshiftedPowerShell_divisorFactor_le s
    have hF0 : 0 ≤ F := by
      dsimp [F]
      positivity
    have htailRaw' :
        ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) N‖ ≤
          (R : ℝ) * fixedAwayUnshiftedElementaryShellConstant t δ +
            (12 * F) * fixedAwayUnshiftedHighMultiplierConstant t δ := by
      have hfactorEq :
          12 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
                Real.sqrt (K : ℝ) / (P : ℝ) =
            12 * F := by
        dsimp [F]
        ring
      rw [← hPdef] at htailRaw
      rw [hfactorEq] at htailRaw
      exact htailRaw
    have hhighActual :
        0 ≤ fixedAwayUnshiftedHighMultiplierConstant t δ :=
      fixedAwayUnshiftedHighMultiplierConstant_nonneg t δ
    have hhighLe :
        fixedAwayUnshiftedHighMultiplierConstant t δ ≤
          fixedAwayUnshiftedHighMultiplierUniformConstant T δ :=
      fixedAwayUnshiftedHighMultiplierConstant_le_uniform
        hδ hδt.le htT
    have htail :
        ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) N‖ ≤
          (R : ℝ) *
              fixedAwayUnshiftedElementaryShellUniformConstant T δ +
            48 * fixedAwayUnshiftedHighMultiplierUniformConstant T δ := by
      calc
        ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) N‖ ≤
            (R : ℝ) *
                fixedAwayUnshiftedElementaryShellConstant t δ +
              (12 * F) *
                fixedAwayUnshiftedHighMultiplierConstant t δ := htailRaw'
        _ ≤ (R : ℝ) *
                fixedAwayUnshiftedElementaryShellUniformConstant T δ +
              48 * fixedAwayUnshiftedHighMultiplierConstant t δ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hshellLe hRnonneg
          · have hfactor : 12 * F ≤ 48 := by nlinarith
            exact mul_le_mul_of_nonneg_right hfactor hhighActual
        _ ≤ (R : ℝ) *
                fixedAwayUnshiftedElementaryShellUniformConstant T δ +
              48 *
                fixedAwayUnshiftedHighMultiplierUniformConstant T δ := by
          gcongr
    rw [hsplit]
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ K 2 Q +
          fixedAwayUnshiftedFiniteVector t δ K (Q + 1) N‖ ≤
        ‖fixedAwayUnshiftedFiniteVector t δ K 2 Q‖ +
          ‖fixedAwayUnshiftedFiniteVector t δ K (Q + 1) N‖ :=
        norm_add_le _ _
      _ ≤ 2 * fixedAwayUnshiftedLowShellUniformConstant T δ +
          ((R : ℝ) *
              fixedAwayUnshiftedElementaryShellUniformConstant T δ +
            48 * fixedAwayUnshiftedHighMultiplierUniformConstant T δ) :=
        add_le_add hlow htail
      _ = fixedAwayUnshiftedPowerShellUniformBound T δ s := by
        unfold fixedAwayUnshiftedPowerShellUniformBound
        dsimp [R]
        ring

end

end Erdos1002

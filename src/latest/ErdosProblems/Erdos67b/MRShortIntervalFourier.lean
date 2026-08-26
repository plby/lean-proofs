import ErdosProblems.Erdos67b.MRMeanSquareProof

/-!
# A finite Fourier majorant for short-interval second moments

The Matomaki--Radziwill argument applies large-value estimates to a product
of two finite Fourier polynomials.  This file supplies the exact finite
bridge.  We first prove Parseval for the ``forward-shift'' convolution on an
arbitrary finite abelian group.  We then embed the interval in a cyclic group
whose modulus is larger than every integer which occurs.  Consequently there
is no wraparound on the starting points in `(X,2X]`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

section FiniteConvolution

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Forward-shift convolution.  This orientation makes its value at `x`
equal to a short sum of `F (x+j)` when `K` is an interval indicator. -/
def forwardShiftConvolution (F K : G → ℂ) (x : G) : ℂ :=
  ∑ y : G, F (x + y) * K y

/-- The Fourier coefficient with the conjugation convention opposite to
`rawCoeff`. -/
def forwardRawCoeff (K : G → ℂ) (psi : AddChar G ℂ) : ℂ :=
  ∑ y : G, psi y * K y

/-- Fourier transform of the forward-shift convolution. -/
theorem rawCoeff_forwardShiftConvolution
    (F K : G → ℂ) (psi : AddChar G ℂ) :
    rawCoeff (forwardShiftConvolution F K) psi =
      rawCoeff F psi * forwardRawCoeff K psi := by
  classical
  unfold forwardShiftConvolution forwardRawCoeff rawCoeff
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [show (∑ x : G, conj (psi x) * (F (x + y) * K y)) =
      (∑ x : G, conj (psi x) * F (x + y)) * K y by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        ring]
  have htranslate :
      (∑ x : G, conj (psi x) * F (x + y)) =
        psi y * ∑ x : G, conj (psi x) * F x := by
    simpa only [rawCoeff, smul_eq_mul] using
      (rawCoeff_translate (F := F) y psi)
  rw [htranslate]
  ring

/-- Exact Plancherel identity for a forward-shift convolution, in the
unnormalized convention. -/
theorem card_mul_sum_normSq_forwardShiftConvolution
    (F K : G → ℂ) :
    (Fintype.card G : ℝ) *
        ∑ x : G, ‖forwardShiftConvolution F K x‖ ^ 2 =
      ∑ psi : AddChar G ℂ,
        ‖rawCoeff F psi‖ ^ 2 * ‖forwardRawCoeff K psi‖ ^ 2 := by
  rw [← sum_sq_norm_rawCoeff (forwardShiftConvolution F K)]
  apply Finset.sum_congr rfl
  intro psi hpsi
  rw [rawCoeff_forwardShiftConvolution, norm_mul]
  ring

end FiniteConvolution

/-- Enumerating a positive `ZMod` by its canonical representatives. -/
theorem sum_zmod_eq_sum_range {N : ℕ} [NeZero N]
    {R : Type*} [AddCommMonoid R] (g : ZMod N → R) :
    ∑ x : ZMod N, g x = ∑ n ∈ Finset.range N, g (n : ZMod N) := by
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
  intro n
  have hn : (n.val : ZMod N) = (ZMod.finEquiv N).toEquiv n := by
    cases N with
    | zero => exact Fin.elim0 n
    | succ N =>
        simp only [ZMod.finEquiv, RingEquiv.toEquiv_eq_coe]
        apply Fin.ext
        change n.val % (N + 1) = n.val
        exact Nat.mod_eq_of_lt n.isLt
  exact congrArg g hn

/-! ## A no-wrap cyclic model of short intervals -/

/-- The cyclic modulus used for the short-interval embedding. -/
def shortIntervalFourierModulus (X H : ℕ) : ℕ :=
  2 * X + H + 1

instance shortIntervalFourierModulus_neZero (X H : ℕ) :
    NeZero (shortIntervalFourierModulus X H) :=
  ⟨by simp [shortIntervalFourierModulus]⟩

/-- Zero extension of `f` to the cyclic group.  The support contains every
`n+j` with `X < n ≤ 2X` and `1 ≤ j ≤ H`. -/
def cyclicShortIntervalCoefficient (f : ℕ → ℂ) (X H : ℕ)
    (x : ZMod (shortIntervalFourierModulus X H)) : ℂ :=
  if x.val ∈ Finset.Icc 1 (2 * X + H) then f x.val else 0

/-- Indicator of the positive interval `[1,H]` in the same cyclic group. -/
def cyclicShortIntervalKernel (X H : ℕ)
    (x : ZMod (shortIntervalFourierModulus X H)) : ℂ :=
  if x.val ∈ Finset.Icc 1 H then 1 else 0

/-- The cyclic convolution whose target values are the ordinary short
interval sums. -/
def cyclicShortIntervalConvolution (f : ℕ → ℂ) (X H : ℕ)
    (x : ZMod (shortIntervalFourierModulus X H)) : ℂ :=
  forwardShiftConvolution
    (cyclicShortIntervalCoefficient f X H)
    (cyclicShortIntervalKernel X H) x

/-- Residues represented by the target starting interval. -/
def cyclicShortIntervalStartSet (X H : ℕ) :
    Finset (ZMod (shortIntervalFourierModulus X H)) :=
  (Finset.Ioc X (2 * X)).image
    (fun n : ℕ ↦ (n : ZMod (shortIntervalFourierModulus X H)))

/-- On every target starting point, the cyclic convolution is exactly the
ordinary short-interval sum. -/
theorem cyclicShortIntervalConvolution_natCast
    (f : ℕ → ℂ) {X H n : ℕ} (hn : n ∈ Finset.Ioc X (2 * X)) :
    cyclicShortIntervalConvolution f X H
        (n : ZMod (shortIntervalFourierModulus X H)) =
      ∑ j ∈ Finset.Icc 1 H, f (n + j) := by
  classical
  let N := shortIntervalFourierModulus X H
  have hn_le : n ≤ 2 * X := (Finset.mem_Ioc.mp hn).2
  have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le X) (Finset.mem_Ioc.mp hn).1
  have hH_lt : H < N := by
    dsimp [N, shortIntervalFourierModulus]
    omega
  have hn_lt : n < N := by
    dsimp [N, shortIntervalFourierModulus]
    omega
  have hsubset : Finset.Icc 1 H ⊆ Finset.range N := by
    intro j hj
    rw [Finset.mem_range]
    exact (Finset.mem_Icc.mp hj).2.trans_lt hH_lt
  unfold cyclicShortIntervalConvolution forwardShiftConvolution
  rw [sum_zmod_eq_sum_range]
  rw [show
      (∑ j ∈ Finset.range N,
          cyclicShortIntervalCoefficient f X H
              ((n : ZMod N) + (j : ZMod N)) *
            cyclicShortIntervalKernel X H (j : ZMod N)) =
        ∑ j ∈ Finset.Icc 1 H,
          cyclicShortIntervalCoefficient f X H
              ((n : ZMod N) + (j : ZMod N)) *
            cyclicShortIntervalKernel X H (j : ZMod N) by
    symm
    apply Finset.sum_subset hsubset
    intro j hjrange hjnot
    have hj_lt : j < N := Finset.mem_range.mp hjrange
    rw [cyclicShortIntervalKernel, ZMod.val_natCast_of_lt hj_lt]
    simp [hjnot]]
  apply Finset.sum_congr rfl
  intro j hj
  have hj_le : j ≤ H := (Finset.mem_Icc.mp hj).2
  have hj_lt : j < N := hj_le.trans_lt hH_lt
  have hnj_lt : n + j < N := by
    dsimp [N, shortIntervalFourierModulus]
    omega
  have hnj_mem : n + j ∈ Finset.Icc 1 (2 * X + H) := by
    rw [Finset.mem_Icc]
    omega
  rw [cyclicShortIntervalKernel, ZMod.val_natCast_of_lt hj_lt]
  simp only [hj, ↓reduceIte, mul_one]
  rw [cyclicShortIntervalCoefficient]
  have hadd :
      ((n : ZMod N) + (j : ZMod N)).val = n + j := by
    rw [← Nat.cast_add, ZMod.val_natCast_of_lt hnj_lt]
  rw [hadd]
  simp [hnj_mem]

/-- The requested short-interval second moment is bounded by the full cyclic
convolution energy.  The only loss is the harmless addition of starting
points outside `(X,2X]`. -/
theorem uncenteredShortIntervalMeanSquare_le_cyclic_energy
    (f : ℕ → ℂ) (X H : ℕ) :
    uncenteredShortIntervalMeanSquare f X H ≤
      ∑ x : ZMod (shortIntervalFourierModulus X H),
        ‖cyclicShortIntervalConvolution f X H x‖ ^ 2 := by
  classical
  have hinj : Set.InjOn
      (fun n : ℕ ↦ (n : ZMod (shortIntervalFourierModulus X H)))
      (↑(Finset.Ioc X (2 * X)) : Set ℕ) := by
    intro a ha b hb hab
    have ha_le : a ≤ 2 * X := (Finset.mem_Ioc.mp ha).2
    have hb_le : b ≤ 2 * X := (Finset.mem_Ioc.mp hb).2
    have ha_lt : a < shortIntervalFourierModulus X H := by
      simp only [shortIntervalFourierModulus]
      omega
    have hb_lt : b < shortIntervalFourierModulus X H := by
      simp only [shortIntervalFourierModulus]
      omega
    have hval := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt ha_lt,
      ZMod.val_natCast_of_lt hb_lt] using hval
  have hsum_image :
      (∑ n ∈ Finset.Ioc X (2 * X),
          ‖cyclicShortIntervalConvolution f X H
            (n : ZMod (shortIntervalFourierModulus X H))‖ ^ 2) =
        ∑ x ∈ cyclicShortIntervalStartSet X H,
          ‖cyclicShortIntervalConvolution f X H x‖ ^ 2 := by
    unfold cyclicShortIntervalStartSet
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact hinj ha hb hab
  calc
    uncenteredShortIntervalMeanSquare f X H =
        ∑ n ∈ Finset.Ioc X (2 * X),
          ‖cyclicShortIntervalConvolution f X H
            (n : ZMod (shortIntervalFourierModulus X H))‖ ^ 2 := by
      unfold uncenteredShortIntervalMeanSquare
      apply Finset.sum_congr rfl
      intro n hn
      rw [cyclicShortIntervalConvolution_natCast f hn,
        Complex.normSq_eq_norm_sq]
    _ = ∑ x ∈ cyclicShortIntervalStartSet X H,
          ‖cyclicShortIntervalConvolution f X H x‖ ^ 2 := hsum_image
    _ ≤ ∑ x : ZMod (shortIntervalFourierModulus X H),
          ‖cyclicShortIntervalConvolution f X H x‖ ^ 2 := by
      exact sum_le_univ_sum_of_nonneg (fun x ↦ sq_nonneg _)

/-- Exact Fourier-side energy identity for the cyclic model. -/
theorem shortIntervalFourierModulus_mul_cyclic_energy
    (f : ℕ → ℂ) (X H : ℕ) :
    (shortIntervalFourierModulus X H : ℝ) *
        ∑ x : ZMod (shortIntervalFourierModulus X H),
          ‖cyclicShortIntervalConvolution f X H x‖ ^ 2 =
      ∑ psi : AddChar (ZMod (shortIntervalFourierModulus X H)) ℂ,
        ‖rawCoeff (cyclicShortIntervalCoefficient f X H) psi‖ ^ 2 *
          ‖forwardRawCoeff (cyclicShortIntervalKernel X H) psi‖ ^ 2 := by
  simpa [cyclicShortIntervalConvolution, ZMod.card] using
    (card_mul_sum_normSq_forwardShiftConvolution
      (cyclicShortIntervalCoefficient f X H)
      (cyclicShortIntervalKernel X H))

/-- Finite Fourier large-values majorant for the uncentered short-interval
mean square.  The right side is a product of the coefficient polynomial and
the interval kernel at every cyclic frequency, exactly the form consumed by
a Ramaré/MRT large-spectrum argument. -/
theorem shortIntervalFourierModulus_mul_uncenteredMeanSquare_le
    (f : ℕ → ℂ) (X H : ℕ) :
    (shortIntervalFourierModulus X H : ℝ) *
        uncenteredShortIntervalMeanSquare f X H ≤
      ∑ psi : AddChar (ZMod (shortIntervalFourierModulus X H)) ℂ,
        ‖rawCoeff (cyclicShortIntervalCoefficient f X H) psi‖ ^ 2 *
          ‖forwardRawCoeff (cyclicShortIntervalKernel X H) psi‖ ^ 2 := by
  calc
    (shortIntervalFourierModulus X H : ℝ) *
        uncenteredShortIntervalMeanSquare f X H ≤
      (shortIntervalFourierModulus X H : ℝ) *
        ∑ x : ZMod (shortIntervalFourierModulus X H),
          ‖cyclicShortIntervalConvolution f X H x‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (uncenteredShortIntervalMeanSquare_le_cyclic_energy f X H)
        (Nat.cast_nonneg _)
    _ = _ := shortIntervalFourierModulus_mul_cyclic_energy f X H

/-! ## Continuous additive-polynomial form -/

/-- A finite additive Fourier polynomial. -/
def finiteAdditivePolynomial (S : Finset ℕ) (a : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ S, a n * additivePhase α n

theorem additivePhase_add_shortFourier (α : ℝ) (m n : ℕ) :
    additivePhase α (m + n) = additivePhase α m * additivePhase α n := by
  rw [additivePhase, additivePhase, additivePhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Orthogonality of distinct integral frequencies on one period. -/
theorem intervalIntegral_conj_additivePhase_mul_additivePhase
    (m n : ℕ) :
    (∫ α in (0 : ℝ)..1,
        conj (additivePhase α m) * additivePhase α n) =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst n
    simp only [← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, norm_additivePhase, one_pow]
    norm_num
  · rw [if_neg hmn]
    let d : ℤ := (n : ℤ) - (m : ℤ)
    let c : ℂ := (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
    have hd : d ≠ 0 := by
      dsimp [d]
      omega
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (by exact_mod_cast hd)
        (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
          Complex.I_ne_zero)
    rw [show (fun α : ℝ ↦
        conj (additivePhase α m) * additivePhase α n) =
        fun α : ℝ ↦ Complex.exp (c * α) by
      funext α
      rw [additivePhase, additivePhase, ← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      dsimp [c, d]
      simp only [map_mul, map_natCast, map_ofNat,
        Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring]
    rw [integral_exp_mul_complex hc]
    have hc_one : Complex.exp (c * (1 : ℂ)) = 1 := by
      rw [mul_one]
      exact Complex.exp_int_mul_two_pi_mul_I d
    have hc_one' : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
      simpa using hc_one
    have hc_zero' : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by simp
    rw [hc_one', hc_zero']
    simp

/-- Complex-cast form of exact Parseval for a finite additive polynomial. -/
theorem finiteAdditivePolynomial_intervalIntegral_normSq_complex
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ α in (0 : ℝ)..1,
        ((Complex.normSq (finiteAdditivePolynomial S a α) : ℝ) : ℂ)) =
      ∑ n ∈ S, ((Complex.normSq (a n) : ℝ) : ℂ) := by
  classical
  unfold finiteAdditivePolynomial
  simp_rw [Complex.normSq_eq_conj_mul_self, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.sum_eq_single m]
      · rw [show (fun x : ℝ ↦
            conj (a m) * conj (additivePhase x m) *
              (a m * additivePhase x m)) =
            fun x : ℝ ↦
              (conj (a m) * a m) *
                (conj (additivePhase x m) * additivePhase x m) by
              funext x; ring]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral_conj_additivePhase_mul_additivePhase]
        simp
      · intro n hn hnm
        rw [show (fun x : ℝ ↦
            conj (a m) * conj (additivePhase x m) *
              (a n * additivePhase x n)) =
            fun x : ℝ ↦
              (conj (a m) * a n) *
                (conj (additivePhase x m) * additivePhase x n) by
              funext x; ring]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral_conj_additivePhase_mul_additivePhase]
        simp [hnm.symm]
      · exact fun hnot ↦ (hnot hm).elim
    · intro n hn
      apply Continuous.intervalIntegrable
      unfold additivePhase
      fun_prop
  · intro m hm
    apply Continuous.intervalIntegrable
    unfold additivePhase
    fun_prop

/-- Exact real-valued Parseval identity for a finite additive polynomial on
one period. -/
theorem finiteAdditivePolynomial_intervalIntegral_normSq
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ α in (0 : ℝ)..1,
        Complex.normSq (finiteAdditivePolynomial S a α)) =
      ∑ n ∈ S, Complex.normSq (a n) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  push_cast
  exact finiteAdditivePolynomial_intervalIntegral_normSq_complex S a

/-- Pairs `(m,j)` occurring in the product of the ambient coefficient
polynomial and the reversed interval kernel. -/
def shiftedShortIntervalPairSet (X H : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Icc 1 (2 * X + H) ×ˢ Finset.Icc 1 H

/-- Nonnegative shifted frequency `m + H - j`. -/
def shiftedShortIntervalFrequency (H : ℕ) (p : ℕ × ℕ) : ℕ :=
  p.1 + H - p.2

/-- Coefficient at a shifted frequency after multiplying by the reversed
interval polynomial. -/
def shiftedShortIntervalCoefficient (f : ℕ → ℂ) (X H k : ℕ) : ℂ :=
  ∑ p ∈ shiftedShortIntervalPairSet X H with
      shiftedShortIntervalFrequency H p = k, f p.1

/-- The shifted product frequencies all lie in this range. -/
theorem shiftedShortIntervalFrequency_mem_range
    {X H : ℕ} {p : ℕ × ℕ} (hp : p ∈ shiftedShortIntervalPairSet X H) :
    shiftedShortIntervalFrequency H p ∈ Finset.range (2 * X + 2 * H + 1) := by
  rw [Finset.mem_range]
  rcases Finset.mem_product.mp hp with ⟨hm, hj⟩
  rw [Finset.mem_Icc] at hm hj
  unfold shiftedShortIntervalFrequency
  omega

/-- At the shifted target frequency `n+H`, the product coefficient is exactly
the short sum beginning at `n+1`. -/
theorem shiftedShortIntervalCoefficient_add_H
    (f : ℕ → ℂ) {X H n : ℕ} (hn : n ∈ Finset.Ioc X (2 * X)) :
    shiftedShortIntervalCoefficient f X H (n + H) =
      ∑ j ∈ Finset.Icc 1 H, f (n + j) := by
  classical
  unfold shiftedShortIntervalCoefficient shiftedShortIntervalPairSet
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Icc] at hj
  rw [Finset.sum_eq_single (n + j)]
  · have hn' := Finset.mem_Ioc.mp hn
    have heq : shiftedShortIntervalFrequency H (n + j, j) = n + H := by
      unfold shiftedShortIntervalFrequency
      omega
    rw [if_pos heq]
  · intro m hm hne
    rw [Finset.mem_Icc] at hm
    simp only [shiftedShortIntervalFrequency]
    split_ifs with heq
    · exfalso
      apply hne
      omega
    · simp [heq]
  · intro hnot
    have hn' := Finset.mem_Ioc.mp hn
    exfalso
    apply hnot
    rw [Finset.mem_Icc]
    omega

/-- Ambient coefficient polynomial, supported just beyond `2X`. -/
def ambientAdditivePolynomial (f : ℕ → ℂ) (X H : ℕ) (α : ℝ) : ℂ :=
  finiteAdditivePolynomial (Finset.Icc 1 (2 * X + H)) f α

/-- Reversed interval kernel.  The shift by `H` makes all frequencies
nonnegative without changing its norm. -/
def reversedIntervalAdditivePolynomial (H : ℕ) (α : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 H, additivePhase α (H - j)

/-- Exact Cauchy-product factorization after collecting equal frequencies. -/
theorem shiftedShortIntervalPolynomial_eq_product
    (f : ℕ → ℂ) (X H : ℕ) (α : ℝ) :
    finiteAdditivePolynomial (Finset.range (2 * X + 2 * H + 1))
        (shiftedShortIntervalCoefficient f X H) α =
      ambientAdditivePolynomial f X H α *
        reversedIntervalAdditivePolynomial H α := by
  classical
  unfold finiteAdditivePolynomial shiftedShortIntervalCoefficient
  rw [show
      (∑ k ∈ Finset.range (2 * X + 2 * H + 1),
          (∑ p ∈ shiftedShortIntervalPairSet X H with
              shiftedShortIntervalFrequency H p = k, f p.1) *
            additivePhase α k) =
        ∑ k ∈ Finset.range (2 * X + 2 * H + 1),
          ∑ p ∈ shiftedShortIntervalPairSet X H with
              shiftedShortIntervalFrequency H p = k,
            f p.1 * additivePhase α (shiftedShortIntervalFrequency H p) by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]]
  rw [Finset.sum_fiberwise_of_maps_to
    (fun p hp ↦ shiftedShortIntervalFrequency_mem_range hp)]
  unfold ambientAdditivePolynomial reversedIntervalAdditivePolynomial
  unfold finiteAdditivePolynomial
  rw [Finset.sum_mul]
  simp only [shiftedShortIntervalPairSet, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ H := (Finset.mem_Icc.mp hj).2
  unfold shiftedShortIntervalFrequency
  rw [Nat.add_sub_assoc hjle]
  rw [additivePhase_add_shortFourier]
  ring

/-- The target second moment is at most the `L²` norm of the full product
polynomial.  This is the continuous Fourier form used before the MRT
large-values decomposition. -/
theorem uncenteredShortIntervalMeanSquare_le_intervalIntegral_product
    (f : ℕ → ℂ) (X H : ℕ) :
    uncenteredShortIntervalMeanSquare f X H ≤
      ∫ α in (0 : ℝ)..1,
        Complex.normSq
          (ambientAdditivePolynomial f X H α *
            reversedIntervalAdditivePolynomial H α) := by
  classical
  let T : Finset ℕ :=
    (Finset.Ioc X (2 * X)).image (fun n : ℕ ↦ n + H)
  have hTsub : T ⊆ Finset.range (2 * X + 2 * H + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
    rw [Finset.mem_range]
    have hn' := (Finset.mem_Ioc.mp hn).2
    omega
  have hsum_image :
      (∑ n ∈ Finset.Ioc X (2 * X),
          Complex.normSq (shiftedShortIntervalCoefficient f X H (n + H))) =
        ∑ k ∈ T, Complex.normSq (shiftedShortIntervalCoefficient f X H k) := by
    dsimp [T]
    rw [Finset.sum_image]
    intro a ha b hb hab
    dsimp at hab
    omega
  calc
    uncenteredShortIntervalMeanSquare f X H =
        ∑ n ∈ Finset.Ioc X (2 * X),
          Complex.normSq (shiftedShortIntervalCoefficient f X H (n + H)) := by
      unfold uncenteredShortIntervalMeanSquare
      apply Finset.sum_congr rfl
      intro n hn
      rw [shiftedShortIntervalCoefficient_add_H f hn]
    _ = ∑ k ∈ T,
          Complex.normSq (shiftedShortIntervalCoefficient f X H k) := hsum_image
    _ ≤ ∑ k ∈ Finset.range (2 * X + 2 * H + 1),
          Complex.normSq (shiftedShortIntervalCoefficient f X H k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hTsub
      intro k hk hnot
      exact Complex.normSq_nonneg _
    _ = ∫ α in (0 : ℝ)..1,
          Complex.normSq
            (finiteAdditivePolynomial (Finset.range (2 * X + 2 * H + 1))
              (shiftedShortIntervalCoefficient f X H) α) := by
      symm
      exact finiteAdditivePolynomial_intervalIntegral_normSq _ _
    _ = ∫ α in (0 : ℝ)..1,
          Complex.normSq
            (ambientAdditivePolynomial f X H α *
              reversedIntervalAdditivePolynomial H α) := by
      apply intervalIntegral.integral_congr
      intro α hα
      change Complex.normSq
          (finiteAdditivePolynomial (Finset.range (2 * X + 2 * H + 1))
            (shiftedShortIntervalCoefficient f X H) α) =
        Complex.normSq
          (ambientAdditivePolynomial f X H α *
            reversedIntervalAdditivePolynomial H α)
      rw [shiftedShortIntervalPolynomial_eq_product]

end

end Erdos67b

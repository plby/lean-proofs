/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import ErdosProblems.Erdos730.PadicIsometry

/-!
# Erdős 730: fixed-depth finite Fourier infrastructure

This module formalizes the exact finite Fourier identity, complete-sum support
restriction, prime-power quadratic Gauss magnitudes, low-effective-modulus
cancellation, the shifted harmonic layer estimate, and the sharp product
`L¹` bound for consecutive-interval digit boxes.  Every analytic estimate is
proved here rather than introduced as an assumption.
-/

namespace Erdos730
namespace FixedDepthFourier

open scoped ZMod
open Finset AddChar

noncomputable section

/-! ## Exact finite Fourier inversion for an interval count -/

/-- Complex-valued indicator of a finite subset. -/
def finsetIndicator {α : Type*} [DecidableEq α] (A : Finset α) (x : α) : ℂ :=
  if x ∈ A then 1 else 0

@[simp] theorem finsetIndicator_apply_mem
    {α : Type*} [DecidableEq α] {A : Finset α} {x : α} (hx : x ∈ A) :
    finsetIndicator A x = 1 := by
  simp [finsetIndicator, hx]

@[simp] theorem finsetIndicator_apply_not_mem
    {α : Type*} [DecidableEq α] {A : Finset α} {x : α} (hx : x ∉ A) :
    finsetIndicator A x = 0 := by
  simp [finsetIndicator, hx]

theorem sum_finsetIndicator_eq_card
    {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
    ∑ x : α, finsetIndicator A x = (A.card : ℂ) := by
  simp [finsetIndicator]

/-- Pointwise unnormalized Fourier inversion on `ZMod Q`. -/
theorem finiteFourier_inversion_at
    {Q : ℕ} [NeZero Q] (Φ : ZMod Q → ℂ) (x : ZMod Q) :
    Φ x = (Q : ℂ)⁻¹ *
      ∑ h : ZMod Q, ZMod.stdAddChar (h * x) * ZMod.dft Φ h := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply Φ) x
  rw [ZMod.invDFT_apply] at hinv
  simpa [smul_eq_mul, mul_comm] using hinv.symm

/-- The incomplete phase sum occurring after Fourier inversion. -/
def intervalPhaseSum {Q : ℕ} [NeZero Q]
    (N : ℕ) (F : ℕ → ZMod Q) (h : ZMod Q) : ℂ :=
  ∑ t ∈ Finset.range N, ZMod.stdAddChar (h * F t)

/-- Number of interval parameters whose phase lands in `A`. -/
def intervalHitCount {Q : ℕ} [NeZero Q]
    (N : ℕ) (F : ℕ → ZMod Q) (A : Finset (ZMod Q)) : ℕ :=
  ((Finset.range N).filter fun t => F t ∈ A).card

/-- **Exact identity (30).**  This is Fourier inversion followed by a finite
interchange of the frequency and interval sums. -/
theorem intervalHitCount_fourier_identity
    {Q : ℕ} [NeZero Q]
    (N : ℕ) (F : ℕ → ZMod Q) (A : Finset (ZMod Q)) :
    (intervalHitCount N F A : ℂ) =
      (Q : ℂ)⁻¹ * ∑ h : ZMod Q,
        ZMod.dft (finsetIndicator A) h * intervalPhaseSum N F h := by
  have hcount :
      (intervalHitCount N F A : ℂ) =
        ∑ t ∈ Finset.range N, finsetIndicator A (F t) := by
    simp only [intervalHitCount, Finset.sum_boole, finsetIndicator]
  rw [hcount]
  simp_rw [finiteFourier_inversion_at (finsetIndicator A)]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext h
  simp only [intervalPhaseSum]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-- The zero-frequency term in (30) is exactly `|A| * N / Q`. -/
theorem zeroFrequency_term
    {Q : ℕ} [NeZero Q]
    (N : ℕ) (A : Finset (ZMod Q)) :
    (Q : ℂ)⁻¹ * ZMod.dft (finsetIndicator A) 0 *
        intervalPhaseSum (Q := Q) N (fun _ => 0) 0 =
      (A.card : ℂ) * N / Q := by
  rw [ZMod.dft_apply_zero, sum_finsetIndicator_eq_card]
  simp [intervalPhaseSum]
  field_simp

/-! ## Exact finite completion identity -/

/-- Fourier phase mass of an arbitrary finite subset of `ZMod Q`. -/
def finsetPhaseSum {Q : ℕ} [NeZero Q]
    (B : Finset (ZMod Q)) (s : ZMod Q) : ℂ :=
  ∑ x ∈ B, ZMod.stdAddChar (s * x)

/-- Complete additive twist of a function on `ZMod Q`. -/
def completeTwist {Q : ℕ} [NeZero Q]
    (f : ZMod Q → ℂ) (s : ZMod Q) : ℂ :=
  ∑ z : ZMod Q, ZMod.stdAddChar (s * z) * f z

/-- Exact finite completion: a sum over `B` is a normalized sum of complete
twists against the Fourier mass of `B`. -/
theorem finiteCompletion_identity
    {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) (B : Finset (ZMod Q)) :
    (∑ x ∈ B, f x) =
      (Q : ℂ)⁻¹ * ∑ s : ZMod Q,
        completeTwist f s * finsetPhaseSum B (-s) := by
  calc
    (∑ x ∈ B, f x) =
        ∑ x ∈ B, (Q : ℂ)⁻¹ *
          ∑ h : ZMod Q,
            ZMod.stdAddChar (h * x) * ZMod.dft f h := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact finiteFourier_inversion_at f x
    _ = (Q : ℂ)⁻¹ * ∑ h : ZMod Q,
          ZMod.dft f h * finsetPhaseSum B h := by
      simp only [finsetPhaseSum, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      funext h
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = (Q : ℂ)⁻¹ * ∑ s : ZMod Q,
          completeTwist f s * finsetPhaseSum B (-s) := by
      congr 1
      exact Fintype.sum_equiv (Equiv.neg (ZMod Q))
        (fun h : ZMod Q ↦ ZMod.dft f h * finsetPhaseSum B h)
        (fun s : ZMod Q ↦ completeTwist f s * finsetPhaseSum B (-s))
        (fun h ↦ by
          simp only [Equiv.neg_apply, neg_neg]
          congr 1
          simp only [completeTwist, ZMod.dft_apply, smul_eq_mul]
          apply Finset.sum_congr rfl
          intro z _hz
          congr 2
          ring)

/-- Zero frequency of an incomplete phase sum. -/
@[simp] theorem intervalPhaseSum_zero
    {Q : ℕ} [NeZero Q] (N : ℕ) (F : ℕ → ZMod Q) :
    intervalPhaseSum N F 0 = N := by
  simp [intervalPhaseSum]

/-- Exact removal of the zero frequency from (30). -/
theorem intervalHitCount_discrepancy_identity
    {Q : ℕ} [NeZero Q]
    (N : ℕ) (F : ℕ → ZMod Q) (A : Finset (ZMod Q)) :
    (intervalHitCount N F A : ℂ) - (A.card : ℂ) * N / Q =
      (Q : ℂ)⁻¹ * ∑ h ∈ (Finset.univ.erase (0 : ZMod Q)),
        ZMod.dft (finsetIndicator A) h * intervalPhaseSum N F h := by
  rw [intervalHitCount_fourier_identity]
  rw [← Finset.add_sum_erase Finset.univ
    (fun h : ZMod Q ↦
      ZMod.dft (finsetIndicator A) h * intervalPhaseSum N F h)
    (Finset.mem_univ (0 : ZMod Q))]
  rw [ZMod.dft_apply_zero, sum_finsetIndicator_eq_card, intervalPhaseSum_zero]
  simp only [div_eq_mul_inv]
  ring

/-- Norm form of the nonzero-frequency discrepancy bound. -/
theorem intervalHitCount_discrepancy_le
    {Q : ℕ} [NeZero Q]
    (N : ℕ) (F : ℕ → ZMod Q) (A : Finset (ZMod Q)) :
    ‖(intervalHitCount N F A : ℂ) - (A.card : ℂ) * N / Q‖ ≤
      (Q : ℝ)⁻¹ * ∑ h ∈ (Finset.univ.erase (0 : ZMod Q)),
        ‖ZMod.dft (finsetIndicator A) h‖ * ‖intervalPhaseSum N F h‖ := by
  rw [intervalHitCount_discrepancy_identity, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg Q))
  calc
    ‖∑ h ∈ (Finset.univ.erase (0 : ZMod Q)),
        ZMod.dft (finsetIndicator A) h * intervalPhaseSum N F h‖ ≤
      ∑ h ∈ (Finset.univ.erase (0 : ZMod Q)),
        ‖ZMod.dft (finsetIndicator A) h * intervalPhaseSum N F h‖ := by
          exact norm_sum_le _ _
    _ = ∑ h ∈ (Finset.univ.erase (0 : ZMod Q)),
        ‖ZMod.dft (finsetIndicator A) h‖ * ‖intervalPhaseSum N F h‖ := by
          apply Finset.sum_congr rfl
          intro h _hh
          rw [norm_mul]

/-! ## Complete residue blocks -/

/-- Summing a function of a residue class through one natural residue block
is the same as summing it over `ZMod Q`. -/
theorem sum_range_zmod_eq_sum
    {Q : ℕ} [NeZero Q] {M : Type*} [AddCommMonoid M] (g : ZMod Q → M) :
    (∑ n ∈ Finset.range Q, g n) = ∑ z : ZMod Q, g z := by
  cases Q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ Q =>
      rw [← Fin.sum_univ_eq_sum_range]
      exact Fintype.sum_equiv (ZMod.finEquiv (Q + 1))
        (fun i : Fin (Q + 1) ↦ g ((i : ℕ) : ZMod (Q + 1))) g
        (fun i ↦
          congrArg g <| ZMod.natCast_zmod_val ((ZMod.finEquiv (Q + 1)) i))

/-- A natural interval of `K` complete residue blocks contributes `K` times
the corresponding complete `ZMod Q` sum. -/
theorem sum_range_zmod_blocks
    {Q : ℕ} [NeZero Q] (g : ZMod Q → ℂ) (K : ℕ) :
    (∑ n ∈ Finset.range (Q * K), g n) = K • ∑ z : ZMod Q, g z := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have hblock :
          (∑ x ∈ Finset.range Q,
              g ((Q * K + x : ℕ) : ZMod Q)) =
            ∑ x ∈ Finset.range Q, g x := by
        apply Finset.sum_congr rfl
        intro x _hx
        congr 1
        simp
      rw [hblock, sum_range_zmod_eq_sum]
      exact (succ_nsmul (∑ z : ZMod Q, g z) K).symm

/-! ## Translation and complete-sum vanishing -/

/-- A complete character sum vanishes whenever translation changes every
phase by the same nontrivial character value. -/
theorem completeSum_eq_zero_of_constantShift
    {R : Type*} [AddCommGroup R] [Fintype R]
    (ψ : AddChar R ℂ) (f : R → R) (d c : R)
    (hshift : ∀ z, f (d + z) = f z + c)
    (hc : ψ c ≠ 1) :
    ∑ z : R, ψ (f z) = 0 := by
  have hperm :
      (∑ z : R, ψ (f (d + z))) = ∑ z : R, ψ (f z) :=
    Fintype.sum_equiv (Equiv.addLeft d) _ _ fun _ => rfl
  simp_rw [hshift, map_add_eq_mul] at hperm
  have hmul : ψ c * (∑ z : R, ψ (f z)) = ∑ z : R, ψ (f z) := by
    rw [Finset.mul_sum]
    simpa [mul_comm] using hperm
  exact eq_zero_of_mul_eq_self_left hc hmul

/-- Quadratic phase over a commutative ring. -/
def quadraticPhase {R : Type*} [CommRing R]
    (A B C z : R) : R := A * z ^ 2 + B * z + C

/-- If `A*d=0`, translation by `d` changes the quadratic phase by the
constant `B*d`. -/
theorem quadraticPhase_shift_of_mul_eq_zero
    {R : Type*} [CommRing R] (A B C d z : R) (hAd : A * d = 0) :
    quadraticPhase A B C (d + z) =
      quadraticPhase A B C z + B * d := by
  simp only [quadraticPhase]
  linear_combination (d + 2 * z) * hAd

/-- The top `p`-power layer annihilates one further factor of `p` modulo
`p^m`. -/
theorem primePow_shift_mul_eq_zero
    {p m : ℕ} [NeZero (p ^ m)] (hm : 1 ≤ m) :
    (p : ZMod (p ^ m)) * (p ^ (m - 1) : ZMod (p ^ m)) = 0 := by
  rw [← Nat.cast_pow, ← Nat.cast_mul]
  have heq : p * p ^ (m - 1) = p ^ m := by
    calc
      p * p ^ (m - 1) = p ^ (m - 1) * p := by ac_rfl
      _ = p ^ ((m - 1) + 1) := (pow_succ p (m - 1)).symm
      _ = p ^ m := by
        congr 1
        all_goals omega
  rw [heq, ZMod.natCast_self]

/-- If `p∤b`, then `b*p^(m-1)` is nonzero modulo `p^m`. -/
theorem primePow_topLayer_ne_zero
    {p m b : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hm : 1 ≤ m) (hb : ¬p ∣ b) :
    (b : ZMod (p ^ m)) * (p ^ (m - 1) : ZMod (p ^ m)) ≠ 0 := by
  rw [← Nat.cast_pow, ← Nat.cast_mul]
  intro hz
  have hdiv : p ^ m ∣ b * p ^ (m - 1) :=
    (ZMod.natCast_eq_zero_iff (b * p ^ (m - 1)) (p ^ m)).mp hz
  apply hb
  have hpow : 0 < p ^ (m - 1) := pow_pos hp.pos _
  have hm' : m = (m - 1) + 1 := by omega
  have hbase : p ^ m = p ^ (m - 1) * p := by
    conv_lhs => rw [hm', pow_succ]
  have hrhs : b * p ^ (m - 1) = p ^ (m - 1) * b := by ac_rfl
  rw [hbase, hrhs] at hdiv
  exact (Nat.mul_dvd_mul_iff_left hpow).mp hdiv

/-- The `p` explicit elements of the kernel of multiplication by `p` on
`ZMod (p^m)`. -/
def primePowKernelMap
    {p m : ℕ} [NeZero (p ^ m)] (hm : 1 ≤ m) (j : Fin p) :
    {z : ZMod (p ^ m) // (p : ZMod (p ^ m)) * z = 0} := by
  refine ⟨((j.val * p ^ (m - 1) : ℕ) : ZMod (p ^ m)), ?_⟩
  rw [Nat.cast_mul]
  calc
    (p : ZMod (p ^ m)) *
        ((j.val : ZMod (p ^ m)) *
          ((p ^ (m - 1) : ℕ) : ZMod (p ^ m))) =
      (j.val : ZMod (p ^ m)) *
        ((p : ZMod (p ^ m)) *
          ((p ^ (m - 1) : ℕ) : ZMod (p ^ m))) := by ring
    _ = 0 := by
      rw [Nat.cast_pow, primePow_shift_mul_eq_zero hm, mul_zero]

/-- Multiplication by `p` on `ZMod (p^m)` has exactly `p` kernel elements
when `m ≥ 1`. -/
theorem card_primePow_mul_kernel
    {p m : ℕ} [NeZero (p ^ m)] (hp : p.Prime) (hm : 1 ≤ m) :
    Fintype.card {z : ZMod (p ^ m) // (p : ZMod (p ^ m)) * z = 0} = p := by
  let d := p ^ (m - 1)
  have hd : 0 < d := pow_pos hp.pos _
  have hq : p ^ m = p * d := by
    dsimp [d]
    calc
      p ^ m = p ^ ((m - 1) + 1) := by
        congr 1
        all_goals omega
      _ = p ^ (m - 1) * p := pow_succ p (m - 1)
      _ = p * p ^ (m - 1) := by ac_rfl
  have hinj : Function.Injective (primePowKernelMap (p := p) (m := m) hm) := by
    intro j k hjk
    apply Fin.ext
    have hval := congrArg (fun z ↦ z.1.val) hjk
    have hjlt : j.val * d < p ^ m := by
      rw [hq]
      exact Nat.mul_lt_mul_of_pos_right j.isLt hd
    have hklt : k.val * d < p ^ m := by
      rw [hq]
      exact Nat.mul_lt_mul_of_pos_right k.isLt hd
    have hmul : j.val * d = k.val * d := by
      simpa only [primePowKernelMap, d, ZMod.val_natCast_of_lt hjlt,
        ZMod.val_natCast_of_lt hklt] using hval
    exact Nat.mul_right_cancel hd hmul
  have hsurj : Function.Surjective (primePowKernelMap (p := p) (m := m) hm) := by
    intro z
    have hzcast :
        (((p * z.1.val : ℕ) : ZMod (p ^ m))) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      exact z.2
    have hqdiv : p ^ m ∣ p * z.1.val :=
      (ZMod.natCast_eq_zero_iff (p * z.1.val) (p ^ m)).mp hzcast
    have hqdiv' : p * d ∣ p * z.1.val := by
      rcases hqdiv with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      calc
        p * z.1.val = p ^ m * c := hc
        _ = (p * d) * c := by rw [hq]
    have hddiv : d ∣ z.1.val :=
      (Nat.mul_dvd_mul_iff_left hp.pos).mp hqdiv'
    have hjlt : z.1.val / d < p := by
      rw [Nat.div_lt_iff_lt_mul hd]
      calc
        z.1.val < p ^ m := ZMod.val_lt z.1
        _ = p * d := hq
    let j : Fin p := ⟨z.1.val / d, hjlt⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    change (((j.val * p ^ (m - 1) : ℕ) : ZMod (p ^ m))) = z.1
    have hjd : j.val * p ^ (m - 1) = z.1.val := by
      dsimp [j, d] at *
      exact Nat.div_mul_cancel hddiv
    rw [hjd]
    exact ZMod.natCast_zmod_val z.1
  let e := Equiv.ofBijective (primePowKernelMap (p := p) (m := m) hm) ⟨hinj, hsurj⟩
  simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm

/-- **Complete-sum support restriction from Lemma 2.**  For
`A=p*alpha`, the complete quadratic sum modulo `p^m` vanishes unless its
linear coefficient is divisible by `p`. -/
theorem completeQuadraticSum_eq_zero_of_not_dvd
    {p m alpha b gamma : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hm : 1 ≤ m) (hb : ¬p ∣ b) :
    (∑ z : ZMod (p ^ m),
      ZMod.stdAddChar
        (quadraticPhase ((p : ZMod (p ^ m)) * (alpha : ZMod (p ^ m)))
          (b : ZMod (p ^ m)) (gamma : ZMod (p ^ m)) z)) = 0 := by
  let d : ZMod (p ^ m) := (p ^ (m - 1) : ℕ)
  let c : ZMod (p ^ m) := (b : ZMod (p ^ m)) * d
  have hpd : (p : ZMod (p ^ m)) * d = 0 := by
    simpa [d] using primePow_shift_mul_eq_zero (p := p) (m := m) hm
  have hAd :
      ((p : ZMod (p ^ m)) * (alpha : ZMod (p ^ m))) * d = 0 := by
    calc
      ((p : ZMod (p ^ m)) * (alpha : ZMod (p ^ m))) * d =
          (alpha : ZMod (p ^ m)) * ((p : ZMod (p ^ m)) * d) := by ring
      _ = 0 := by rw [hpd, mul_zero]
  have hc0 : c ≠ 0 := by
    simpa [c, d] using
      primePow_topLayer_ne_zero (p := p) (m := m) (b := b) hp hm hb
  have hchar : ZMod.stdAddChar c ≠ 1 := by
    intro hc
    exact hc0
      ((ZMod.isPrimitive_stdAddChar (p ^ m)).zmod_char_eq_one_iff
        (p ^ m) c |>.mp hc)
  apply completeSum_eq_zero_of_constantShift
    ZMod.stdAddChar
    (quadraticPhase ((p : ZMod (p ^ m)) * (alpha : ZMod (p ^ m)))
      (b : ZMod (p ^ m)) (gamma : ZMod (p ^ m))) d c
  · intro z
    simpa [add_comm, c] using
      quadraticPhase_shift_of_mul_eq_zero
        ((p : ZMod (p ^ m)) * (alpha : ZMod (p ^ m)))
          (b : ZMod (p ^ m)) (gamma : ZMod (p ^ m)) d z hAd
  · exact hchar

/-! ## Exact low-effective-modulus vanishing -/

/-- The fixed-depth polynomial `p * α * t² + β * t + γ`. -/
def fixedDepthQuadratic {p m : ℕ}
    (α β γ t : ZMod (p ^ m)) : ZMod (p ^ m) :=
  (p : ZMod (p ^ m)) * α * t ^ 2 + β * t + γ

/-- A unit linear coefficient makes the fixed-depth quadratic polynomial a
permutation modulo every positive prime power (indeed, the proof only needs
`p > 0`). -/
theorem fixedDepthQuadratic_bijective
    {p m : ℕ} (hp0 : 0 < p) {β : ZMod (p ^ m)} (hβ : IsUnit β)
    (α γ : ZMod (p ^ m)) :
    Function.Bijective (fixedDepthQuadratic α β γ) := by
  have hfun : fixedDepthQuadratic α β γ =
      padicBranchMap (p : ZMod (p ^ m)) α 0 β γ := by
    funext t
    simp [fixedDepthQuadratic, padicBranchMap]
  rw [hfun]
  exact padicBranchMap_bijective (p := p) (j := m) hp0 hβ α 0 γ

/-- A nontrivial character summed over the permuted fixed-depth polynomial
vanishes on a complete residue system. -/
theorem completeFixedDepthQuadraticSum_eq_zero
    {p m : ℕ} [NeZero (p ^ m)] (hp0 : 0 < p)
    {β : ZMod (p ^ m)} (hβ : IsUnit β)
    (α γ u : ZMod (p ^ m)) (hu : u ≠ 0) :
    (∑ z : ZMod (p ^ m),
      ZMod.stdAddChar (u * fixedDepthQuadratic α β γ z)) = 0 := by
  have hperm :
      (∑ z : ZMod (p ^ m),
          ZMod.stdAddChar (u * fixedDepthQuadratic α β γ z)) =
        ∑ y : ZMod (p ^ m), ZMod.stdAddChar (u * y) :=
    Fintype.sum_bijective (fixedDepthQuadratic α β γ)
      (fixedDepthQuadratic_bijective hp0 hβ α γ)
      (fun z ↦ ZMod.stdAddChar (u * fixedDepthQuadratic α β γ z))
      (fun y ↦ ZMod.stdAddChar (u * y)) (fun _z ↦ rfl)
  rw [hperm]
  simpa [hu, mul_comm] using
    AddChar.sum_mulShift u (ZMod.isPrimitive_stdAddChar (p ^ m))

/-- If the effective modulus exponent `m` is at most the interval depth
`r`, the length-`p^r` interval is a union of complete residue systems and
the quadratic phase sum vanishes exactly. -/
theorem incompleteFixedDepthQuadraticSum_eq_zero_of_le
    {p m r : ℕ} [NeZero (p ^ m)] (hp0 : 0 < p) (hmr : m ≤ r)
    {β : ZMod (p ^ m)} (hβ : IsUnit β)
    (α γ u : ZMod (p ^ m)) (hu : u ≠ 0) :
    (∑ t ∈ Finset.range (p ^ r),
      ZMod.stdAddChar
        (u * fixedDepthQuadratic α β γ (t : ZMod (p ^ m)))) = 0 := by
  have hpow : p ^ r = p ^ m * p ^ (r - m) := by
    rw [← pow_add, Nat.add_sub_of_le hmr]
  rw [hpow]
  calc
    (∑ t ∈ Finset.range (p ^ m * p ^ (r - m)),
      ZMod.stdAddChar
        (u * fixedDepthQuadratic α β γ (t : ZMod (p ^ m)))) =
        p ^ (r - m) • ∑ z : ZMod (p ^ m),
          ZMod.stdAddChar (u * fixedDepthQuadratic α β γ z) := by
      exact sum_range_zmod_blocks
        (fun z : ZMod (p ^ m) ↦
          ZMod.stdAddChar (u * fixedDepthQuadratic α β γ z)) _
    _ = 0 := by
      rw [completeFixedDepthQuadraticSum_eq_zero hp0 hβ α γ u hu, nsmul_zero]

/-- A quadratic Gauss sum with invertible doubled leading coefficient has
exact squared magnitude equal to the modulus.  This is the kernel-checked
form of the classical odd-modulus Gauss bound. -/
theorem quadraticGaussSum_normSq
    {n : ℕ} [NeZero n] (a b c : ZMod n)
    (ha : IsUnit ((2 : ZMod n) * a)) :
    Complex.normSq
      (∑ x : ZMod n, ZMod.stdAddChar (quadraticPhase a b c x)) = n := by
  let G : ℂ := ∑ x : ZMod n, ZMod.stdAddChar (quadraticPhase a b c x)
  have hzero (h : ZMod n) : ((2 : ZMod n) * a) * h = 0 ↔ h = 0 := by
    constructor
    · intro hh
      apply ha.mul_left_cancel
      simpa using hh
    · rintro rfl
      simp
  have hshift (x : ZMod n) :
      (∑ y : ZMod n,
          ZMod.stdAddChar
            (-quadraticPhase a b c x + quadraticPhase a b c y)) =
        ∑ h : ZMod n,
          ZMod.stdAddChar
            (quadraticPhase a b c (x + h) - quadraticPhase a b c x) := by
    exact (Fintype.sum_equiv (Equiv.addLeft x)
      (fun h : ZMod n ↦
        ZMod.stdAddChar
          (quadraticPhase a b c (x + h) - quadraticPhase a b c x))
      (fun y : ZMod n ↦
        ZMod.stdAddChar
          (-quadraticPhase a b c x + quadraticPhase a b c y))
      (fun h ↦ by
        change ZMod.stdAddChar
            (quadraticPhase a b c (x + h) - quadraticPhase a b c x) =
          ZMod.stdAddChar
            (-quadraticPhase a b c x + quadraticPhase a b c (x + h))
        congr 1
        ring)).symm
  have hcomplex : ((Complex.normSq G : ℝ) : ℂ) = (n : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [G]
    rw [map_sum]
    simp_rw [← AddChar.map_neg_eq_conj]
    rw [Finset.sum_mul_sum]
    simp_rw [← AddChar.map_add_eq_mul]
    simp_rw [hshift]
    rw [Finset.sum_comm]
    simp_rw [quadraticPhase]
    have hphase (h x : ZMod n) :
        a * (x + h) ^ 2 + b * (x + h) + c -
            (a * x ^ 2 + b * x + c) =
          (a * h ^ 2 + b * h) + x * (((2 : ZMod n) * a) * h) := by
      ring
    simp_rw [hphase, AddChar.map_add_eq_mul]
    simp_rw [← Finset.mul_sum]
    simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n)]
    simp_rw [hzero]
    simp [ZMod.card]
  exact_mod_cast hcomplex

/-- Degenerate prime-power Gauss identity used in (31): if both quadratic
and linear coefficients have one factor of `p`, and `2α` is a unit, then the
squared magnitude is `p^(m+1)`. -/
theorem primePowDegenerateQuadraticGaussSum_normSq
    {p m : ℕ} [NeZero (p ^ m)] (hp : p.Prime) (hm : 1 ≤ m)
    (α b c : ZMod (p ^ m)) (h2α : IsUnit ((2 : ZMod (p ^ m)) * α)) :
    Complex.normSq
      (∑ x : ZMod (p ^ m),
        ZMod.stdAddChar
          (quadraticPhase ((p : ZMod (p ^ m)) * α)
            ((p : ZMod (p ^ m)) * b) c x)) =
      ((p ^ (m + 1) : ℕ) : ℝ) := by
  let A : ZMod (p ^ m) := (p : ZMod (p ^ m)) * α
  let B : ZMod (p ^ m) := (p : ZMod (p ^ m)) * b
  let G : ℂ := ∑ x : ZMod (p ^ m),
    ZMod.stdAddChar (quadraticPhase A B c x)
  have hkernel (h : ZMod (p ^ m)) :
      ((2 : ZMod (p ^ m)) * A) * h = 0 ↔
        (p : ZMod (p ^ m)) * h = 0 := by
    have hrewrite : ((2 : ZMod (p ^ m)) * A) * h =
        ((2 : ZMod (p ^ m)) * α) * ((p : ZMod (p ^ m)) * h) := by
      dsimp only [A]
      ring
    rw [hrewrite]
    constructor
    · intro hh
      apply h2α.mul_left_cancel
      simpa using hh
    · intro hh
      rw [hh, mul_zero]
  have hphasezero (h : ZMod (p ^ m))
      (hh : (p : ZMod (p ^ m)) * h = 0) :
      A * h ^ 2 + B * h = 0 := by
    dsimp only [A, B]
    calc
      ((p : ZMod (p ^ m)) * α) * h ^ 2 +
          ((p : ZMod (p ^ m)) * b) * h =
        α * h * ((p : ZMod (p ^ m)) * h) +
          b * ((p : ZMod (p ^ m)) * h) := by ring
      _ = 0 := by rw [hh]; simp
  have hshift (x : ZMod (p ^ m)) :
      (∑ y : ZMod (p ^ m),
          ZMod.stdAddChar
            (-quadraticPhase A B c x + quadraticPhase A B c y)) =
        ∑ h : ZMod (p ^ m),
          ZMod.stdAddChar
            (quadraticPhase A B c (x + h) - quadraticPhase A B c x) := by
    exact (Fintype.sum_equiv (Equiv.addLeft x)
      (fun h : ZMod (p ^ m) ↦
        ZMod.stdAddChar
          (quadraticPhase A B c (x + h) - quadraticPhase A B c x))
      (fun y : ZMod (p ^ m) ↦
        ZMod.stdAddChar
          (-quadraticPhase A B c x + quadraticPhase A B c y))
      (fun h ↦ by
        change ZMod.stdAddChar
            (quadraticPhase A B c (x + h) - quadraticPhase A B c x) =
          ZMod.stdAddChar
            (-quadraticPhase A B c x + quadraticPhase A B c (x + h))
        congr 1
        ring)).symm
  have hsum :
      (∑ h : ZMod (p ^ m),
          ZMod.stdAddChar (A * h ^ 2 + B * h) *
            ((if (p : ZMod (p ^ m)) * h = 0 then p ^ m else 0 : ℕ) : ℂ)) =
        ((p ^ (m + 1) : ℕ) : ℂ) := by
    calc
      (∑ h : ZMod (p ^ m),
          ZMod.stdAddChar (A * h ^ 2 + B * h) *
            ((if (p : ZMod (p ^ m)) * h = 0 then p ^ m else 0 : ℕ) : ℂ)) =
        ∑ h : ZMod (p ^ m),
          if (p : ZMod (p ^ m)) * h = 0 then
            (((p ^ m : ℕ) : ℂ)) else 0 := by
            apply Finset.sum_congr rfl
            intro h _hh
            by_cases hz : (p : ZMod (p ^ m)) * h = 0
            · simp [hz, hphasezero h hz]
            · simp [hz]
      _ = (Fintype.card
            {h : ZMod (p ^ m) // (p : ZMod (p ^ m)) * h = 0} : ℂ) *
              ((p ^ m : ℕ) : ℂ) := by
          rw [Fintype.card_subtype]
          simp [Finset.sum_ite]
      _ = ((p ^ (m + 1) : ℕ) : ℂ) := by
          rw [card_primePow_mul_kernel hp hm, pow_succ]
          push_cast
          ring
  have hcomplex : ((Complex.normSq G : ℝ) : ℂ) = (p ^ (m + 1) : ℕ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    dsimp only [G]
    rw [map_sum]
    simp_rw [← AddChar.map_neg_eq_conj]
    rw [Finset.sum_mul_sum]
    simp_rw [← AddChar.map_add_eq_mul]
    simp_rw [hshift]
    rw [Finset.sum_comm]
    simp_rw [quadraticPhase]
    have hphase (h x : ZMod (p ^ m)) :
        A * (x + h) ^ 2 + B * (x + h) + c -
            (A * x ^ 2 + B * x + c) =
          (A * h ^ 2 + B * h) +
            x * (((2 : ZMod (p ^ m)) * A) * h) := by
      ring
    simp_rw [hphase, AddChar.map_add_eq_mul]
    simp_rw [← Finset.mul_sum]
    simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar (p ^ m))]
    simp_rw [hkernel]
    simpa only [ZMod.card, AddChar.map_add_eq_mul] using hsum
  dsimp only [G, A, B] at hcomplex
  exact_mod_cast hcomplex

/-- Norm form of the degenerate prime-power identity, matching (31). -/
theorem primePowDegenerateQuadraticGaussSum_norm
    {p m : ℕ} [NeZero (p ^ m)] (hp : p.Prime) (hm : 1 ≤ m)
    (α b c : ZMod (p ^ m)) (h2α : IsUnit ((2 : ZMod (p ^ m)) * α)) :
    ‖∑ x : ZMod (p ^ m),
      ZMod.stdAddChar
        (quadraticPhase ((p : ZMod (p ^ m)) * α)
          ((p : ZMod (p ^ m)) * b) c x)‖ =
      Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) := by
  have hsq :
      ‖∑ x : ZMod (p ^ m),
        ZMod.stdAddChar
          (quadraticPhase ((p : ZMod (p ^ m)) * α)
            ((p : ZMod (p ^ m)) * b) c x)‖ ^ 2 =
        ((p ^ (m + 1) : ℕ) : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq,
      primePowDegenerateQuadraticGaussSum_normSq hp hm α b c h2α]
  have hsqrt :
      (Real.sqrt (((p ^ (m + 1) : ℕ) : ℝ))) ^ 2 =
        ((p ^ (m + 1) : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  nlinarith [norm_nonneg
    (∑ x : ZMod (p ^ m),
      ZMod.stdAddChar
        (quadraticPhase ((p : ZMod (p ^ m)) * α)
          ((p : ZMod (p ^ m)) * b) c x)),
    Real.sqrt_nonneg (((p ^ (m + 1) : ℕ) : ℝ))]

/-- Norm form of `quadraticGaussSum_normSq`. -/
theorem quadraticGaussSum_norm
    {n : ℕ} [NeZero n] (a b c : ZMod n)
    (ha : IsUnit ((2 : ZMod n) * a)) :
    ‖∑ x : ZMod n, ZMod.stdAddChar (quadraticPhase a b c x)‖ =
      Real.sqrt n := by
  have hsq :
      ‖∑ x : ZMod n, ZMod.stdAddChar (quadraticPhase a b c x)‖ ^ 2 =
        (n : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, quadraticGaussSum_normSq a b c ha]
  have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  nlinarith [norm_nonneg
    (∑ x : ZMod n, ZMod.stdAddChar (quadraticPhase a b c x)),
    Real.sqrt_nonneg (n : ℝ)]

/-- Prime-power specialization: an odd-prime unit leading coefficient has
the exact classical square-root Gauss magnitude. -/
theorem primePowQuadraticGaussSum_norm
    {p k A B C : ℕ} [NeZero (p ^ k)]
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : ¬p ∣ A) :
    ‖∑ x : ZMod (p ^ k),
      ZMod.stdAddChar
        (quadraticPhase (A : ZMod (p ^ k)) (B : ZMod (p ^ k))
          (C : ZMod (p ^ k)) x)‖ = Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  have h2 : ¬p ∣ 2 := by
    rw [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
    exact hp2
  have hunit2 : IsUnit (2 : ZMod (p ^ k)) :=
    natCast_isUnit_zmod_primePow hp h2
  have hunitA : IsUnit (A : ZMod (p ^ k)) :=
    natCast_isUnit_zmod_primePow hp hA
  exact quadraticGaussSum_norm (A : ZMod (p ^ k))
    (B : ZMod (p ^ k)) (C : ZMod (p ^ k)) (hunit2.mul hunitA)

/-! ## Geometric sums and the harmonic layer bound -/

/-- A finite geometric progression, in the notation used by both completion
and one-digit Fourier factors. -/
def geometricPhaseSum (z : ℂ) (N : ℕ) : ℂ :=
  ∑ v ∈ Finset.range N, z ^ v

/-- Trivial length bound for a geometric sum on the unit circle. -/
theorem norm_geometricPhaseSum_le_length
    {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖geometricPhaseSum z N‖ ≤ N := by
  calc
    ‖geometricPhaseSum z N‖ ≤ ∑ v ∈ Finset.range N, ‖z ^ v‖ := by
      exact norm_sum_le _ _
    _ = ∑ _v ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro v _hv
      simp [norm_pow, hz]
    _ = N := by simp

/-- Nontrivial geometric-series bound.  The numerator contributes at most
two and the exact chord length remains in the denominator. -/
theorem norm_geometricPhaseSum_le_two_div
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖geometricPhaseSum z N‖ ≤ 2 / ‖z - 1‖ := by
  rw [geometricPhaseSum, geom_sum_eq hz1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      simp [norm_pow, hz]
      all_goals norm_num

/-- Moving the start of a consecutive power interval only multiplies its
sum by a unit-modulus scalar. -/
theorem norm_consecutivePowerSum_eq
    {z : ℂ} (hz : ‖z‖ = 1) (M N : ℕ) :
    ‖∑ e ∈ Finset.Ico M (M + N), z ^ e‖ = ‖geometricPhaseSum z N‖ := by
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show M + N - M = N by omega]
  simp only [pow_add, ← Finset.mul_sum, geometricPhaseSum,
    norm_mul, norm_pow, hz, one_pow, one_mul]

/-- Chord separation for the lower half of the `p`th roots of unity.  This
is the analytic input behind the geometric-series layer cake. -/
theorem stdAddChar_chord_lower_half
    {p j : ℕ} [NeZero p] (hp : 0 < p) (hj : 0 < j) (hhalf : 2 * j ≤ p) :
    (4 : ℝ) * j / p ≤ ‖ZMod.stdAddChar (j : ZMod p) - 1‖ := by
  have hchar : ZMod.stdAddChar (j : ZMod p) =
      Complex.exp (Complex.I * (((2 : ℝ) * Real.pi * j) / p)) := by
    rw [show (j : ZMod p) = ((j : ℤ) : ZMod p) by norm_num,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hchar]
  have harg :
      Complex.I *
          (((2 : ℝ) : ℂ) * (Real.pi : ℂ) * (j : ℂ) / (p : ℂ)) =
        Complex.I * ((((2 : ℝ) * Real.pi * j) / p : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have hx0 : 0 ≤ Real.pi * (j : ℝ) / p := by positivity
  have hxhalf : Real.pi * (j : ℝ) / p ≤ Real.pi / 2 := by
    apply (div_le_iff₀ (show (0 : ℝ) < p by positivity)).2
    have hpile : (2 : ℝ) * j ≤ p := by exact_mod_cast hhalf
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin
    (x := Real.pi * (j : ℝ) / p)
    (abs_le.2 ⟨by linarith, hxhalf⟩)
  rw [abs_of_nonneg hx0] at hsin
  have hpR : (0 : ℝ) < p := by positivity
  field_simp [Real.pi_ne_zero, ne_of_gt hpR] at hsin ⊢
  nlinarith [Real.pi_pos]

/-- Geometric-sum decay at a nonzero lower-half frequency. -/
theorem norm_geometricPhaseSum_stdAddChar_lower_half
    {p j : ℕ} [NeZero p] (hp : 0 < p) (hj : 0 < j) (hhalf : 2 * j ≤ p)
    (N : ℕ) :
    ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ ≤
      (p : ℝ) / (2 * j) := by
  have hjp : j < p := by omega
  have hjz : (j : ZMod p) ≠ 0 := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt hj hjp)
      ((ZMod.natCast_eq_zero_iff j p).mp hz)
  have hchar1 : ZMod.stdAddChar (j : ZMod p) ≠ 1 := by
    intro h
    exact hjz ((ZMod.isPrimitive_stdAddChar p).zmod_char_eq_one_iff
      p (j : ZMod p) |>.mp h)
  have hphaseNorm : ‖ZMod.stdAddChar (j : ZMod p)‖ = 1 :=
    AddChar.norm_apply ZMod.stdAddChar (j : ZMod p)
  refine (norm_geometricPhaseSum_le_two_div hphaseNorm hchar1 N).trans ?_
  have hden : 0 < ‖ZMod.stdAddChar (j : ZMod p) - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hchar1)
  have hjR : (0 : ℝ) < 2 * j := by positivity
  rw [div_le_div_iff₀ hden hjR]
  have hchord := stdAddChar_chord_lower_half hp hj hhalf
  have hpR : (0 : ℝ) < p := by positivity
  have hmul := (div_le_iff₀ hpR).mp hchord
  nlinarith

/-- Negating a frequency conjugates its geometric sum, hence preserves its
norm. -/
theorem norm_geometricPhaseSum_stdAddChar_neg
    {p : ℕ} [NeZero p] (s : ZMod p) (N : ℕ) :
    ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ =
      ‖geometricPhaseSum (ZMod.stdAddChar s) N‖ := by
  have hconj :
      geometricPhaseSum (ZMod.stdAddChar (-s)) N =
        (starRingEnd ℂ) (geometricPhaseSum (ZMod.stdAddChar s) N) := by
    simp only [geometricPhaseSum, AddChar.map_neg_eq_conj]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    exact (map_pow (starRingEnd ℂ) (ZMod.stdAddChar s) v).symm
  rw [hconj, Complex.norm_conj]

/-- Upper-half frequency decay, obtained from the lower half by conjugation. -/
theorem norm_geometricPhaseSum_stdAddChar_upper_half
    {p j : ℕ} [NeZero p] (hp : 0 < p) (hjp : j < p) (hhalf : p ≤ 2 * j)
    (N : ℕ) :
    ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ ≤
      (p : ℝ) / (2 * ((p - j : ℕ) : ℝ)) := by
  have hsub0 : 0 < p - j := Nat.sub_pos_of_lt hjp
  have hsubhalf : 2 * (p - j) ≤ p := by omega
  have hjneg : (j : ZMod p) = -((p - j : ℕ) : ZMod p) := by
    apply (eq_neg_iff_add_eq_zero).2
    rw [← Nat.cast_add]
    rw [Nat.add_sub_of_le hjp.le, ZMod.natCast_self]
  rw [hjneg, norm_geometricPhaseSum_stdAddChar_neg]
  exact norm_geometricPhaseSum_stdAddChar_lower_half hp hsub0 hsubhalf N

/-- Symmetric pointwise majorant valid at every nonzero natural frequency
`1 ≤ j < p`. -/
theorem norm_geometricPhaseSum_stdAddChar_le_symmetric
    {p j : ℕ} [NeZero p] (hp : 0 < p) (hj : 0 < j) (hjp : j < p)
    (N : ℕ) :
    ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ ≤
      (p : ℝ) / 2 *
        (((j : ℝ)⁻¹) + ((((p - j : ℕ) : ℝ))⁻¹)) := by
  rcases le_total (2 * j) p with hhalf | hhalf
  · refine (norm_geometricPhaseSum_stdAddChar_lower_half hp hj hhalf N).trans ?_
    calc
      (p : ℝ) / (2 * j) = (p : ℝ) / 2 * (j : ℝ)⁻¹ := by
        field_simp
      _ ≤ (p : ℝ) / 2 *
          (((j : ℝ)⁻¹) + ((((p - j : ℕ) : ℝ))⁻¹)) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  · refine (norm_geometricPhaseSum_stdAddChar_upper_half hp hjp hhalf N).trans ?_
    calc
      (p : ℝ) / (2 * ((p - j : ℕ) : ℝ)) =
          (p : ℝ) / 2 * (((p - j : ℕ) : ℝ))⁻¹ := by
        field_simp
      _ ≤ (p : ℝ) / 2 *
          (((j : ℝ)⁻¹) + ((((p - j : ℕ) : ℝ))⁻¹)) := by
        gcongr
        exact le_add_of_nonneg_left (by positivity)

/-- The real harmonic layer used after ordering nonzero frequencies by
distance from the zero frequency. -/
theorem real_harmonic_layer_le (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, ((k : ℝ)⁻¹)) ≤ 1 + Real.log N := by
  calc
    (∑ k ∈ Finset.Icc 1 N, ((k : ℝ)⁻¹)) =
        ((harmonic N : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

/-- Reflection preserves the reciprocal mass on the nonzero natural
frequency interval. -/
theorem sum_Ico_inv_sub_eq (p : ℕ) :
    (∑ j ∈ Finset.Ico 1 p, ((((p - j : ℕ) : ℝ))⁻¹)) =
      ∑ j ∈ Finset.Ico 1 p, ((j : ℝ)⁻¹) := by
  simpa using
    (Finset.sum_Ico_reflect (fun j : ℕ ↦ ((j : ℝ)⁻¹)) 1
      (m := p) (n := p) (by omega))

/-- Harmonic bound on the nonzero natural frequency interval. -/
theorem sum_Ico_inv_le_one_add_log (p : ℕ) :
    (∑ j ∈ Finset.Ico 1 p, ((j : ℝ)⁻¹)) ≤ 1 + Real.log p := by
  calc
    (∑ j ∈ Finset.Ico 1 p, ((j : ℝ)⁻¹)) ≤
        ∑ j ∈ Finset.Icc 1 p, ((j : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_Ico, Finset.mem_Icc] at hj ⊢
        omega
      · intro j _hjIcc _hjIco
        positivity
    _ ≤ 1 + Real.log p := real_harmonic_layer_le p

/-- Unshifted one-dimensional layer cake over all nonzero frequencies. -/
theorem nonzero_natural_frequency_mass_le
    {p : ℕ} [NeZero p] (hp : 0 < p) (N : ℕ) :
    (∑ j ∈ Finset.Ico 1 p,
      ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖) ≤
        (p : ℝ) * (1 + Real.log p) := by
  calc
    (∑ j ∈ Finset.Ico 1 p,
      ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖) ≤
        ∑ j ∈ Finset.Ico 1 p, (p : ℝ) / 2 *
          (((j : ℝ)⁻¹) + ((((p - j : ℕ) : ℝ))⁻¹)) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_Ico] at hj
      exact norm_geometricPhaseSum_stdAddChar_le_symmetric hp hj.1 hj.2 N
    _ = (p : ℝ) * ∑ j ∈ Finset.Ico 1 p, ((j : ℝ)⁻¹) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, sum_Ico_inv_sub_eq]
      ring
    _ ≤ (p : ℝ) * (1 + Real.log p) :=
      mul_le_mul_of_nonneg_left (sum_Ico_inv_le_one_add_log p) (Nat.cast_nonneg p)

/-- Unshifted one-dimensional layer cake including the zero frequency. -/
theorem unshifted_frequency_mass_le
    {p : ℕ} [NeZero p] (hp : 0 < p) {N : ℕ} (hN : N ≤ p) :
    (∑ s : ZMod p,
      ‖geometricPhaseSum (ZMod.stdAddChar s) N‖) ≤
        (p : ℝ) * (2 + Real.log p) := by
  have hsplit :
      (∑ j ∈ Finset.range p,
          ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖) =
        ‖geometricPhaseSum (ZMod.stdAddChar (0 : ZMod p)) N‖ +
          ∑ j ∈ Finset.Ico 1 p,
            ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ := by
    let f : ℕ → ℝ := fun j ↦
      ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖
    have hone : ∑ j ∈ Finset.Ico 0 1, f j = f 0 := by
      norm_num
    rw [Finset.range_eq_Ico]
    calc
      ∑ j ∈ Finset.Ico 0 p, f j =
          (∑ j ∈ Finset.Ico 0 1, f j) + ∑ j ∈ Finset.Ico 1 p, f j :=
        (Finset.sum_Ico_consecutive f (show 0 ≤ 1 by omega)
          (show 1 ≤ p by omega)).symm
      _ = f 0 + ∑ j ∈ Finset.Ico 1 p, f j := by rw [hone]
      _ = ‖geometricPhaseSum (ZMod.stdAddChar (0 : ZMod p)) N‖ +
          ∑ j ∈ Finset.Ico 1 p,
            ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ := by
        simp [f]
  have hzero :
      ‖geometricPhaseSum (ZMod.stdAddChar (0 : ZMod p)) N‖ = (N : ℝ) := by
    simp [geometricPhaseSum]
  calc
    (∑ s : ZMod p,
      ‖geometricPhaseSum (ZMod.stdAddChar s) N‖) =
        ∑ j ∈ Finset.range p,
          ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ :=
      (sum_range_zmod_eq_sum
        (fun s : ZMod p ↦ ‖geometricPhaseSum (ZMod.stdAddChar s) N‖)).symm
    _ = (N : ℝ) + ∑ j ∈ Finset.Ico 1 p,
        ‖geometricPhaseSum (ZMod.stdAddChar (j : ZMod p)) N‖ := by
      rw [hsplit, hzero]
    _ ≤ (p : ℝ) + (p : ℝ) * (1 + Real.log p) := by
      exact add_le_add (by exact_mod_cast hN)
        (nonzero_natural_frequency_mass_le hp N)
    _ = (p : ℝ) * (2 + Real.log p) := by ring

/-! ## Shifted one-dimensional layer cake -/

/-- The unit-circle phase at real angle `x`. -/
def realUnitPhase (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (x : ℂ))

@[simp] theorem norm_realUnitPhase (x : ℝ) :
    ‖realUnitPhase x‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal x

/-- A point in the lower half-circle has chord length at least four times
its normalized distance from the origin. -/
theorem realUnitPhase_chord_lower
    (u v : ℝ) (hvu : v ≤ u) (hu0 : 0 ≤ u) (huhalf : u ≤ 1 / 2) :
    4 * v ≤ ‖realUnitPhase (2 * Real.pi * u) - 1‖ := by
  rw [realUnitPhase, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * u / 2 = Real.pi * u by ring]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have hx0 : 0 ≤ Real.pi * u := mul_nonneg Real.pi_pos.le hu0
  have hxhalf : Real.pi * u ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin
    (x := Real.pi * u) (abs_le.2 ⟨by linarith, hxhalf⟩)
  rw [abs_of_nonneg hx0] at hsin
  field_simp [Real.pi_ne_zero] at hsin
  nlinarith [Real.pi_pos]

/-- The reflected upper-half version of `realUnitPhase_chord_lower`. -/
theorem realUnitPhase_chord_upper
    (u v : ℝ) (hvu : v ≤ 1 - u)
    (huhalf : 1 / 2 ≤ u) (hu1 : u ≤ 1) :
    4 * v ≤ ‖realUnitPhase (2 * Real.pi * u) - 1‖ := by
  have hy0 : 0 ≤ 1 - u := by linarith
  have hyhalf : 1 - u ≤ 1 / 2 := by linarith
  have hbase := realUnitPhase_chord_lower (1 - u) v hvu hy0 hyhalf
  rw [realUnitPhase, Complex.norm_exp_I_mul_ofReal_sub_one] at hbase ⊢
  rw [show 2 * Real.pi * u / 2 = Real.pi * u by ring]
  rw [show 2 * Real.pi * (1 - u) / 2 =
      Real.pi - Real.pi * u by ring] at hbase
  rw [Real.sin_pi_sub] at hbase
  exact hbase

/-- Geometric decay for a shifted grid point in the lower half-circle. -/
theorem norm_geometricPhaseSum_shiftedGrid_lower
    {p j : ℕ} (hp : 0 < p) (hj : 0 < j)
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hhalf : theta + (j : ℝ) / p ≤ 1 / 2) (N : ℕ) :
    ‖geometricPhaseSum
        (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))) N‖ ≤
      (p : ℝ) / (2 * j) := by
  let z := realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))
  have hchord : (4 : ℝ) * ((j : ℝ) / p) ≤ ‖z - 1‖ := by
    exact realUnitPhase_chord_lower
      (theta + (j : ℝ) / p) ((j : ℝ) / p)
      (by linarith) (by positivity) hhalf
  have hchordpos : 0 < ‖z - 1‖ := by
    have : 0 < (4 : ℝ) * ((j : ℝ) / p) := by positivity
    linarith
  have hz1 : z ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp hchordpos)
  refine (norm_geometricPhaseSum_le_two_div
    (z := z) (by simp [z]) hz1 N).trans ?_
  have hpR : (0 : ℝ) < p := by positivity
  have hjR : (0 : ℝ) < 2 * j := by positivity
  rw [div_le_div_iff₀ hchordpos hjR]
  have hchord' : (4 : ℝ) * j / p ≤ ‖z - 1‖ := by
    convert hchord using 1
    all_goals ring
  have hmul := (div_le_iff₀ hpR).mp hchord'
  nlinarith

/-- Geometric decay for a shifted grid point in the upper half-circle. -/
theorem norm_geometricPhaseSum_shiftedGrid_upper
    {p j : ℕ} (hp : 0 < p) (hjp : j + 1 < p)
    (theta : ℝ) (htheta : theta ≤ (1 : ℝ) / p)
    (hhalf : 1 / 2 ≤ theta + (j : ℝ) / p) (N : ℕ) :
    ‖geometricPhaseSum
        (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))) N‖ ≤
      (p : ℝ) / (2 * ((p - 1 - j : ℕ) : ℝ)) := by
  let u : ℝ := theta + (j : ℝ) / p
  let v : ℝ := ((p - 1 - j : ℕ) : ℝ) / p
  let z := realUnitPhase (2 * Real.pi * u)
  have hsubpos : 0 < p - 1 - j := by omega
  have hvpos : 0 < v := by
    dsimp [v]
    positivity
  have hvu : v ≤ 1 - u := by
    dsimp [u, v]
    have hpR : (0 : ℝ) < p := by positivity
    have hjcast : ((p - 1 - j : ℕ) : ℝ) = p - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      norm_num
    rw [hjcast]
    have htheta' := (le_div_iff₀ hpR).mp htheta
    field_simp [ne_of_gt hpR]
    nlinarith
  have hu1 : u ≤ 1 := by
    dsimp [u]
    have hpR : (0 : ℝ) < p := by positivity
    have hjcast : (j : ℝ) + 1 ≤ p := by
      exact_mod_cast (show j + 1 ≤ p by omega)
    have htheta' := (le_div_iff₀ hpR).mp htheta
    field_simp [ne_of_gt hpR]
    nlinarith
  have hchord : (4 : ℝ) * v ≤ ‖z - 1‖ := by
    exact realUnitPhase_chord_upper u v hvu hhalf hu1
  have hchordpos : 0 < ‖z - 1‖ := by
    have : 0 < (4 : ℝ) * v := by positivity
    linarith
  have hz1 : z ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp hchordpos)
  refine (norm_geometricPhaseSum_le_two_div
    (z := z) (by simp [z]) hz1 N).trans ?_
  have hpR : (0 : ℝ) < p := by positivity
  have hsubR : (0 : ℝ) < 2 * (p - 1 - j : ℕ) := by positivity
  rw [div_le_div_iff₀ hchordpos hsubR]
  have hchord' : (4 : ℝ) * (p - 1 - j : ℕ) / p ≤ ‖z - 1‖ := by
    dsimp [v] at hchord
    convert hchord using 1
    all_goals ring
  have hmul := (div_le_iff₀ hpR).mp hchord'
  nlinarith

/-- Symmetric majorant for every interior point of a shifted `p`-grid whose
shift lies in one canonical grid cell. -/
theorem norm_geometricPhaseSum_shiftedGrid_le_symmetric
    {p j : ℕ} (hp : 0 < p) (hj : 0 < j) (hjp : j + 1 < p)
    (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hthetap : theta ≤ (1 : ℝ) / p) (N : ℕ) :
    ‖geometricPhaseSum
        (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))) N‖ ≤
      (p : ℝ) / 2 *
        (((j : ℝ)⁻¹) + ((((p - 1 - j : ℕ) : ℝ))⁻¹)) := by
  rcases le_total (theta + (j : ℝ) / p) (1 / 2) with hhalf | hhalf
  · refine (norm_geometricPhaseSum_shiftedGrid_lower
      hp hj theta htheta0 hhalf N).trans ?_
    calc
      (p : ℝ) / (2 * j) = (p : ℝ) / 2 * (j : ℝ)⁻¹ := by
        field_simp
      _ ≤ (p : ℝ) / 2 *
          (((j : ℝ)⁻¹) + ((((p - 1 - j : ℕ) : ℝ))⁻¹)) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  · refine (norm_geometricPhaseSum_shiftedGrid_upper
      hp hjp theta hthetap hhalf N).trans ?_
    calc
      (p : ℝ) / (2 * ((p - 1 - j : ℕ) : ℝ)) =
          (p : ℝ) / 2 * (((p - 1 - j : ℕ) : ℝ))⁻¹ := by
        field_simp
      _ ≤ (p : ℝ) / 2 *
          (((j : ℝ)⁻¹) + ((((p - 1 - j : ℕ) : ℝ))⁻¹)) := by
        gcongr
        exact le_add_of_nonneg_left (by positivity)

/-- **Shifted one-dimensional layer cake (34).**  For a shift in one
canonical grid cell, the two endpoint frequencies cost at most `2p`; the
remaining frequencies form a reflected harmonic layer. -/
theorem shiftedGrid_frequency_mass_le
    {p N : ℕ} (hp2 : 2 ≤ p) (hN : N ≤ p)
    (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hthetap : theta ≤ (1 : ℝ) / p) :
    (∑ j ∈ Finset.range p,
      ‖geometricPhaseSum
        (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))) N‖) ≤
      (p : ℝ) * (3 + Real.log p) := by
  have hp : 0 < p := by omega
  let f : ℕ → ℝ := fun j ↦
    ‖geometricPhaseSum
      (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p))) N‖
  have hend (j : ℕ) : f j ≤ (p : ℝ) := by
    refine (norm_geometricPhaseSum_le_length
      (z := realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / p)))
      (by simp) N).trans ?_
    exact_mod_cast hN
  have hsplit :
      (∑ j ∈ Finset.range p, f j) =
        f 0 + (∑ j ∈ Finset.Ico 1 (p - 1), f j) + f (p - 1) := by
    rw [Finset.range_eq_Ico]
    calc
      ∑ j ∈ Finset.Ico 0 p, f j =
          (∑ j ∈ Finset.Ico 0 (p - 1), f j) +
            ∑ j ∈ Finset.Ico (p - 1) p, f j :=
        (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm
      _ = ((∑ j ∈ Finset.Ico 0 1, f j) +
            ∑ j ∈ Finset.Ico 1 (p - 1), f j) +
            ∑ j ∈ Finset.Ico (p - 1) p, f j := by
        congr 1
        exact (Finset.sum_Ico_consecutive f (by omega) (by omega)).symm
      _ = f 0 + (∑ j ∈ Finset.Ico 1 (p - 1), f j) + f (p - 1) := by
        have hp_succ : p = (p - 1) + 1 := by omega
        rw [hp_succ]
        norm_num
  have hreflect :
      (∑ j ∈ Finset.Ico 1 (p - 1),
        ((((p - 1 - j : ℕ) : ℝ))⁻¹)) =
        ∑ j ∈ Finset.Ico 1 (p - 1), ((j : ℝ)⁻¹) := by
    exact sum_Ico_inv_sub_eq (p - 1)
  have hharmonic :
      (∑ j ∈ Finset.Ico 1 (p - 1), ((j : ℝ)⁻¹)) ≤
        1 + Real.log p := by
    calc
      (∑ j ∈ Finset.Ico 1 (p - 1), ((j : ℝ)⁻¹)) ≤
          ∑ j ∈ Finset.Ico 1 p, ((j : ℝ)⁻¹) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_Ico] at hj ⊢
          omega
        · intro j _hj _hj'
          positivity
      _ ≤ 1 + Real.log p := sum_Ico_inv_le_one_add_log p
  have hinterior :
      (∑ j ∈ Finset.Ico 1 (p - 1), f j) ≤
        (p : ℝ) * (1 + Real.log p) := by
    calc
      (∑ j ∈ Finset.Ico 1 (p - 1), f j) ≤
          ∑ j ∈ Finset.Ico 1 (p - 1),
            (p : ℝ) / 2 *
              (((j : ℝ)⁻¹) + ((((p - 1 - j : ℕ) : ℝ))⁻¹)) := by
        apply Finset.sum_le_sum
        intro j hj
        simp only [Finset.mem_Ico] at hj
        exact norm_geometricPhaseSum_shiftedGrid_le_symmetric
          hp hj.1 (by omega) theta htheta0 hthetap N
      _ = (p : ℝ) *
          ∑ j ∈ Finset.Ico 1 (p - 1), ((j : ℝ)⁻¹) := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib, hreflect]
        ring
      _ ≤ (p : ℝ) * (1 + Real.log p) :=
        mul_le_mul_of_nonneg_left hharmonic (Nat.cast_nonneg p)
  rw [hsplit]
  calc
    f 0 + (∑ j ∈ Finset.Ico 1 (p - 1), f j) + f (p - 1) ≤
        (p : ℝ) + (p : ℝ) * (1 + Real.log p) + (p : ℝ) :=
      add_le_add (add_le_add (hend 0) hinterior) (hend (p - 1))
    _ = (p : ℝ) * (3 + Real.log p) := by ring

/-! ## Exact digit-box factorization and an unconditional `L¹` bound -/

/-- A point of a digit box: at coordinate `i` its digit belongs to `E i`. -/
abbrev DigitTuple {d : ℕ} (E : Fin d → Finset ℕ) :=
  (i : Fin d) → ↑(E i)

/-- The contribution of one digit to the negative Fourier phase modulo
`p^d`. -/
def digitPhase {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d))
    (i : Fin d) (e : ↑(E i)) : ZMod (p ^ d) :=
  -(h * (((e : ℕ) * p ^ (i : ℕ) : ℕ) : ZMod (p ^ d)))

/-- Fourier coefficient of a digit box, written directly as a sum over its
digit tuples. -/
def digitBoxFourierCoeff {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d)) : ℂ :=
  ∑ x : DigitTuple E,
    ZMod.stdAddChar (∑ i : Fin d, digitPhase E h i (x i))

/-- The one-coordinate factor in the Fourier coefficient of a digit box. -/
def digitFourierFactor {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d)) (i : Fin d) : ℂ :=
  ∑ e : ↑(E i), ZMod.stdAddChar (digitPhase E h i e)

/-- The Fourier coefficient of a digit box factors exactly digit by digit. -/
theorem digitBoxFourierCoeff_factorization
    {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d)) :
    digitBoxFourierCoeff E h = ∏ i : Fin d, digitFourierFactor E h i := by
  simp only [digitBoxFourierCoeff, digitFourierFactor]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  have hmap (s : Finset (Fin d)) :
      ZMod.stdAddChar (∑ i ∈ s, digitPhase E h i (x i)) =
        ∏ i ∈ s, ZMod.stdAddChar (digitPhase E h i (x i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, Finset.prod_insert hi,
          AddChar.map_add_eq_mul, ih]
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte,
    Finset.prod_filter] using hmap Finset.univ

/-- Triangle inequality for a one-coordinate digit factor. -/
theorem norm_digitFourierFactor_le_card
    {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d)) (i : Fin d) :
    ‖digitFourierFactor E h i‖ ≤ (E i).card := by
  calc
    ‖digitFourierFactor E h i‖ ≤
        ∑ e : ↑(E i), ‖ZMod.stdAddChar (digitPhase E h i e)‖ := by
      exact norm_sum_le _ _
    _ = ∑ _e : ↑(E i), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _he
      exact AddChar.norm_apply ZMod.stdAddChar (digitPhase E h i e)
    _ = (E i).card := by simp

/-- Pointwise trivial bound for a digit-box Fourier coefficient. -/
theorem norm_digitBoxFourierCoeff_le_cardProduct
    {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) (h : ZMod (p ^ d)) :
    ‖digitBoxFourierCoeff E h‖ ≤ ∏ i : Fin d, ((E i).card : ℝ) := by
  rw [digitBoxFourierCoeff_factorization, norm_prod]
  exact Finset.prod_le_prod
    (fun i _hi ↦ norm_nonneg (digitFourierFactor E h i))
    (fun i _hi ↦ norm_digitFourierFactor_le_card E h i)

/-- Unconditional finite `L¹` bound obtained from exact factorization and
the triangle inequality.  The sharper logarithmic bound (35) replaces the
factor `∏ |E_i|` here by `(3 + log p)^d`. -/
theorem digitBoxFourierCoeff_l1_le
    {d p : ℕ} [NeZero (p ^ d)]
    (E : Fin d → Finset ℕ) :
    (∑ h : ZMod (p ^ d), ‖digitBoxFourierCoeff E h‖) ≤
      (p ^ d : ℝ) * ∏ i : Fin d, ((E i).card : ℝ) := by
  calc
    (∑ h : ZMod (p ^ d), ‖digitBoxFourierCoeff E h‖) ≤
        ∑ _h : ZMod (p ^ d), ∏ i : Fin d, ((E i).card : ℝ) := by
      exact Finset.sum_le_sum fun h _hh ↦
        norm_digitBoxFourierCoeff_le_cardProduct E h
    _ = (p ^ d : ℝ) * ∏ i : Fin d, ((E i).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
      norm_num

/-! ## Sharp Fourier L1 bound for interval digit boxes -/

theorem stdAddChar_primeScale {p d x : ℕ} [NeZero p] :
    ZMod.stdAddChar (((p * x : ℕ) : ZMod (p ^ (d + 1)))) =
      ZMod.stdAddChar ((x : ℕ) : ZMod (p ^ d)) := by
  rw [show ((p * x : ℕ) : ZMod (p ^ (d + 1))) =
      ((p * x : ℤ) : ZMod (p ^ (d + 1))) by norm_num,
    show ((x : ℕ) : ZMod (p ^ d)) = ((x : ℤ) : ZMod (p ^ d)) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_succ]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp [hpC]

theorem stdAddChar_tailDigit {p d a b e i : ℕ} [NeZero p] :
    ZMod.stdAddChar
        (-((((a + p ^ d * b) * e * p ^ (i + 1) : ℕ)) :
          ZMod (p ^ (d + 1)))) =
      ZMod.stdAddChar
        (-(((a * e * p ^ i : ℕ)) : ZMod (p ^ d))) := by
  have hnat :
      (a + p ^ d * b) * e * p ^ (i + 1) =
        p * (a * e * p ^ i) + p ^ (d + 1) * (b * e * p ^ i) := by
    rw [pow_succ p d, pow_succ p i]
    ring
  have hphase :
      ((((a + p ^ d * b) * e * p ^ (i + 1) : ℕ)) :
          ZMod (p ^ (d + 1))) =
        ((p * (a * e * p ^ i) : ℕ) : ZMod (p ^ (d + 1))) := by
    rw [hnat]
    push_cast
    have hpzero : (p : ZMod (p ^ (d + 1))) ^ (d + 1) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hpzero, zero_mul, add_zero]
  rw [hphase, AddChar.map_neg_eq_conj, AddChar.map_neg_eq_conj,
    stdAddChar_primeScale]

def naturalDigitFourierFactor (p : ℕ) [NeZero p] {d : ℕ}
    (E : Fin d → Finset ℕ) (h : ℕ) (i : Fin d) : ℂ :=
  ∑ e : ↑(E i), ZMod.stdAddChar
    (-(((h * (e : ℕ) * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d)))

def naturalDigitBoxFourierCoeff (p : ℕ) [NeZero p] {d : ℕ}
    (E : Fin d → Finset ℕ) (h : ℕ) : ℂ :=
  ∏ i : Fin d, naturalDigitFourierFactor p E h i

theorem digitFourierFactor_natCast_eq {d p : ℕ} [NeZero p]
    (E : Fin d → Finset ℕ) (h : ℕ) (i : Fin d) :
    digitFourierFactor E (h : ZMod (p ^ d)) i = naturalDigitFourierFactor p E h i := by
  apply Finset.sum_congr rfl
  intro e _he
  congr 1
  simp only [digitPhase]
  push_cast
  ring

theorem digitBoxFourierCoeff_natCast_eq {d p : ℕ} [NeZero p]
    (E : Fin d → Finset ℕ) (h : ℕ) :
    digitBoxFourierCoeff E (h : ZMod (p ^ d)) = naturalDigitBoxFourierCoeff p E h := by
  rw [digitBoxFourierCoeff_factorization]
  apply Finset.prod_congr rfl
  intro i _hi
  exact digitFourierFactor_natCast_eq E h i

theorem norm_naturalDigitFourierFactor_interval
    {d p : ℕ} [NeZero p] (E : Fin d → Finset ℕ)
    (h : ℕ) (i : Fin d) (M N : ℕ)
    (hE : E i = Finset.Ico M (M + N)) :
    ‖naturalDigitFourierFactor p E h i‖ =
      ‖geometricPhaseSum
        (ZMod.stdAddChar
          (-(((h * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d)))) N‖ := by
  let z : ℂ := ZMod.stdAddChar
    (-(((h * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d)))
  have hterm (e : ℕ) :
      ZMod.stdAddChar
          (-(((h * e * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d))) =
        z ^ e := by
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    push_cast
    simp only [nsmul_eq_mul]
    ring
  rw [naturalDigitFourierFactor, hE]
  rw [Finset.sum_coe_sort (Finset.Ico M (M + N))
    (fun e : ℕ ↦ ZMod.stdAddChar
      (-(((h * e * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d))))]
  simp_rw [hterm]
  exact norm_consecutivePowerSum_eq
    (AddChar.norm_apply ZMod.stdAddChar
      (-(((h * p ^ (i : ℕ) : ℕ)) : ZMod (p ^ d)))) M N

theorem realUnitPhase_neg (x : ℝ) :
    realUnitPhase (-x) = (starRingEnd ℂ) (realUnitPhase x) := by
  rw [realUnitPhase, realUnitPhase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  push_cast
  ring

theorem stdAddChar_natCast_as_realUnitPhase
    {q h : ℕ} [NeZero q] :
    ZMod.stdAddChar (h : ZMod q) =
      realUnitPhase (2 * Real.pi * ((h : ℝ) / q)) := by
  rw [show (h : ZMod q) = ((h : ℤ) : ZMod q) by norm_num,
    ZMod.stdAddChar_coe]
  unfold realUnitPhase
  congr 1
  push_cast
  ring

theorem stdAddChar_neg_natCast_as_realUnitPhase
    {q h : ℕ} [NeZero q] :
    ZMod.stdAddChar (-(h : ZMod q)) =
      realUnitPhase (-2 * Real.pi * ((h : ℝ) / q)) := by
  rw [AddChar.map_neg_eq_conj, stdAddChar_natCast_as_realUnitPhase]
  convert (realUnitPhase_neg (2 * Real.pi * ((h : ℝ) / q))).symm using 1
  all_goals ring_nf

theorem norm_geometricPhaseSum_realUnitPhase_neg (x : ℝ) (N : ℕ) :
    ‖geometricPhaseSum (realUnitPhase (-x)) N‖ =
      ‖geometricPhaseSum (realUnitPhase x) N‖ := by
  have hconj :
      geometricPhaseSum (realUnitPhase (-x)) N =
        (starRingEnd ℂ) (geometricPhaseSum (realUnitPhase x) N) := by
    rw [realUnitPhase_neg]
    simp only [geometricPhaseSum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    exact (map_pow (starRingEnd ℂ) (realUnitPhase x) v).symm
  rw [hconj, Complex.norm_conj]

theorem topDigitFactor_block_mass_le
    {p d : ℕ} [NeZero p] (hp2 : 2 ≤ p)
    (E : Fin (d + 1) → Finset ℕ) (a M N : ℕ) (ha : a < p ^ d)
    (hE : E ⟨0, Nat.succ_pos d⟩ = Finset.Ico M (M + N))
    (hN : N ≤ p) :
    (∑ b ∈ Finset.range p,
      ‖naturalDigitFourierFactor p E (a + p ^ d * b) ⟨0, Nat.succ_pos d⟩‖) ≤
        (p : ℝ) * (3 + Real.log p) := by
  have hp : 0 < p := by omega
  let theta : ℝ := (a : ℝ) / p ^ (d + 1)
  have htheta0 : 0 ≤ theta := by
    dsimp [theta]
    positivity
  have hthetap : theta ≤ (1 : ℝ) / p := by
    dsimp [theta]
    have hpR : (0 : ℝ) < p := by positivity
    have hpowR : (0 : ℝ) < p ^ d := by positivity
    have haR : (a : ℝ) ≤ p ^ d := by exact_mod_cast ha.le
    rw [pow_succ]
    field_simp [ne_of_gt hpR, ne_of_gt hpowR]
    nlinarith
  have hfactor (b : ℕ) :
      ‖naturalDigitFourierFactor p E (a + p ^ d * b) ⟨0, Nat.succ_pos d⟩‖ =
        ‖geometricPhaseSum
          (realUnitPhase (2 * Real.pi * (theta + (b : ℝ) / p))) N‖ := by
    rw [norm_naturalDigitFourierFactor_interval E (a + p ^ d * b)
      ⟨0, Nat.succ_pos d⟩ M N hE]
    simp only [pow_zero, mul_one,
      stdAddChar_neg_natCast_as_realUnitPhase]
    calc
      ‖geometricPhaseSum
          (realUnitPhase
            (-2 * Real.pi * (((a + p ^ d * b : ℕ) : ℝ) /
              ((p ^ (d + 1) : ℕ) : ℝ)))) N‖ =
        ‖geometricPhaseSum
          (realUnitPhase
            (2 * Real.pi * (((a + p ^ d * b : ℕ) : ℝ) /
              ((p ^ (d + 1) : ℕ) : ℝ)))) N‖ := by
          convert norm_geometricPhaseSum_realUnitPhase_neg
            (2 * Real.pi * (((a + p ^ d * b : ℕ) : ℝ) /
              ((p ^ (d + 1) : ℕ) : ℝ))) N using 1
          all_goals ring_nf
      _ = ‖geometricPhaseSum
          (realUnitPhase (2 * Real.pi * (theta + (b : ℝ) / p))) N‖ := by
        congr 3
        dsimp [theta]
        push_cast
        rw [pow_succ]
        have hpR : (p : ℝ) ≠ 0 := by positivity
        have hpowR : (p : ℝ) ^ d ≠ 0 := pow_ne_zero _ hpR
        field_simp [hpR, hpowR]
  simp_rw [hfactor]
  exact shiftedGrid_frequency_mass_le hp2 hN theta htheta0 hthetap

theorem naturalDigitFourierFactor_succ
    {p d a b : ℕ} [NeZero p] (E : Fin (d + 1) → Finset ℕ)
    (i : Fin d) :
    naturalDigitFourierFactor p E (a + p ^ d * b) i.succ =
      naturalDigitFourierFactor p (fun k : Fin d ↦ E k.succ) a i := by
  apply Finset.sum_congr rfl
  intro e _he
  exact stdAddChar_tailDigit

theorem naturalDigitBoxFourierCoeff_split
    {p d a b : ℕ} [NeZero p] (E : Fin (d + 1) → Finset ℕ) :
    naturalDigitBoxFourierCoeff p E (a + p ^ d * b) =
      naturalDigitFourierFactor p E (a + p ^ d * b) ⟨0, Nat.succ_pos d⟩ *
        naturalDigitBoxFourierCoeff p (fun k : Fin d ↦ E k.succ) a := by
  rw [naturalDigitBoxFourierCoeff, Fin.prod_univ_succ, naturalDigitBoxFourierCoeff]
  congr 1
  apply Finset.prod_congr rfl
  intro i _hi
  exact naturalDigitFourierFactor_succ E i

theorem sum_range_mul_blocks
    {M : Type*} [AddCommMonoid M] (A p : ℕ) (f : ℕ → M) :
    (∑ h ∈ Finset.range (A * p), f h) =
      ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range p, f (a + A * b) := by
  rw [mul_comm A p]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ h : Fin (p * A), f h) =
        ∑ ba : Fin p × Fin A, f ((finProdFinEquiv ba : Fin (p * A)) : ℕ) := by
      exact (Fintype.sum_equiv finProdFinEquiv
        (fun ba : Fin p × Fin A ↦
          f ((finProdFinEquiv ba : Fin (p * A)) : ℕ))
        (fun h : Fin (p * A) ↦ f h) (fun _ ↦ rfl)).symm
    _ = ∑ a : Fin A, ∑ b : Fin p, f ((a : ℕ) + A * (b : ℕ)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl

def IsIntervalDigitBox {d : ℕ} (p : ℕ) (E : Fin d → Finset ℕ) : Prop :=
  ∀ i, ∃ M N : ℕ, E i = Finset.Ico M (M + N) ∧ N ≤ p

theorem naturalDigitBoxFourierCoeff_l1_le
    {d p : ℕ} [NeZero p] (hp2 : 2 ≤ p)
    (E : Fin d → Finset ℕ) (hE : IsIntervalDigitBox p E) :
    (∑ h ∈ Finset.range (p ^ d), ‖naturalDigitBoxFourierCoeff p E h‖) ≤
      (p : ℝ) ^ d * (3 + Real.log p) ^ d := by
  induction d with
  | zero =>
      simp [naturalDigitBoxFourierCoeff]
  | succ d ih =>
      let E' : Fin d → Finset ℕ := fun i ↦ E i.succ
      have hE' : IsIntervalDigitBox p E' := by
        intro i
        exact hE i.succ
      rcases hE ⟨0, Nat.succ_pos d⟩ with ⟨M, N, hE0, hN⟩
      have hC : 0 ≤ (p : ℝ) * (3 + Real.log p) := by positivity
      have hblock (a : ℕ) (ha : a < p ^ d) :
          (∑ b ∈ Finset.range p,
            ‖naturalDigitBoxFourierCoeff p E (a + p ^ d * b)‖) ≤
            (p : ℝ) * (3 + Real.log p) * ‖naturalDigitBoxFourierCoeff p E' a‖ := by
        have htop := topDigitFactor_block_mass_le hp2 E a M N ha hE0 hN
        calc
          (∑ b ∈ Finset.range p,
            ‖naturalDigitBoxFourierCoeff p E (a + p ^ d * b)‖) =
              (∑ b ∈ Finset.range p,
                ‖naturalDigitFourierFactor p E (a + p ^ d * b)
                  ⟨0, Nat.succ_pos d⟩‖) * ‖naturalDigitBoxFourierCoeff p E' a‖ := by
            simp_rw [naturalDigitBoxFourierCoeff_split, norm_mul]
            rw [Finset.sum_mul]
          _ ≤ ((p : ℝ) * (3 + Real.log p)) * ‖naturalDigitBoxFourierCoeff p E' a‖ :=
            mul_le_mul_of_nonneg_right htop (norm_nonneg _)
      rw [pow_succ, sum_range_mul_blocks]
      calc
        (∑ a ∈ Finset.range (p ^ d),
          ∑ b ∈ Finset.range p,
            ‖naturalDigitBoxFourierCoeff p E (a + p ^ d * b)‖) ≤
            ∑ a ∈ Finset.range (p ^ d),
              ((p : ℝ) * (3 + Real.log p)) * ‖naturalDigitBoxFourierCoeff p E' a‖ := by
          apply Finset.sum_le_sum
          intro a ha
          exact hblock a (Finset.mem_range.mp ha)
        _ = ((p : ℝ) * (3 + Real.log p)) *
            ∑ a ∈ Finset.range (p ^ d), ‖naturalDigitBoxFourierCoeff p E' a‖ := by
          rw [Finset.mul_sum]
        _ ≤ ((p : ℝ) * (3 + Real.log p)) *
            ((p : ℝ) ^ d * (3 + Real.log p) ^ d) :=
          mul_le_mul_of_nonneg_left (ih E' hE') hC
        _ = (p : ℝ) ^ (d + 1) * (3 + Real.log p) ^ (d + 1) := by
          ring

theorem digitBoxFourierCoeff_interval_l1_le
    {d p : ℕ} [NeZero p] (hp2 : 2 ≤ p)
    (E : Fin d → Finset ℕ) (hE : IsIntervalDigitBox p E) :
    (∑ h : ZMod (p ^ d), ‖digitBoxFourierCoeff E h‖) ≤
      (p : ℝ) ^ d * (3 + Real.log p) ^ d := by
  calc
    (∑ h : ZMod (p ^ d), ‖digitBoxFourierCoeff E h‖) =
        ∑ h ∈ Finset.range (p ^ d),
          ‖digitBoxFourierCoeff E (h : ZMod (p ^ d))‖ :=
      (sum_range_zmod_eq_sum
        (fun h : ZMod (p ^ d) ↦ ‖digitBoxFourierCoeff E h‖)).symm
    _ = ∑ h ∈ Finset.range (p ^ d), ‖naturalDigitBoxFourierCoeff p E h‖ := by
      apply Finset.sum_congr rfl
      intro h _hh
      rw [digitBoxFourierCoeff_natCast_eq]
    _ ≤ (p : ℝ) ^ d * (3 + Real.log p) ^ d :=
      naturalDigitBoxFourierCoeff_l1_le hp2 E hE


def residueClassMap {p q s0 : ℕ} [NeZero p] [NeZero q]
    (hs0 : s0 < p) (j : Fin q) :
    {s : ZMod (p * q) // s.val % p = s0} := by
  have hnlt : s0 + p * j.val < p * q := by
    have hp : 0 < p := NeZero.pos p
    have hq : 0 < q := NeZero.pos q
    calc
      s0 + p * j.val < p + p * j.val := Nat.add_lt_add_right hs0 _
      _ = p * (j.val + 1) := by ring
      _ ≤ p * q := Nat.mul_le_mul_left p (Nat.succ_le_of_lt j.isLt)
  refine ⟨((s0 + p * j.val : ℕ) : ZMod (p * q)), ?_⟩
  rw [ZMod.val_natCast_of_lt hnlt, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hs0]

theorem residueClassMap_bijective
    {p q s0 : ℕ} [NeZero p] [NeZero q] (hs0 : s0 < p) :
    Function.Bijective (residueClassMap (p := p) (q := q) hs0) := by
  have hp : 0 < p := NeZero.pos p
  have hq : 0 < q := NeZero.pos q
  constructor
  · intro j k hjk
    apply Fin.ext
    have hval := congrArg (fun z ↦ z.1.val) hjk
    have hjlt : s0 + p * j.val < p * q := by
      calc
        s0 + p * j.val < p + p * j.val := Nat.add_lt_add_right hs0 _
        _ = p * (j.val + 1) := by ring
        _ ≤ p * q := Nat.mul_le_mul_left p (Nat.succ_le_of_lt j.isLt)
    have hklt : s0 + p * k.val < p * q := by
      calc
        s0 + p * k.val < p + p * k.val := Nat.add_lt_add_right hs0 _
        _ = p * (k.val + 1) := by ring
        _ ≤ p * q := Nat.mul_le_mul_left p (Nat.succ_le_of_lt k.isLt)
    simp only [residueClassMap, ZMod.val_natCast_of_lt hjlt,
      ZMod.val_natCast_of_lt hklt] at hval
    have hmul : p * j.val = p * k.val := Nat.add_left_cancel hval
    exact Nat.mul_left_cancel hp hmul
  · intro s
    have hdivlt : s.1.val / p < q := by
      rw [Nat.div_lt_iff_lt_mul hp]
      simpa [mul_comm] using s.1.val_lt
    let j : Fin q := ⟨s.1.val / p, hdivlt⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    change (((s0 + p * j.val : ℕ) : ZMod (p * q))) = s.1
    have hn : s0 + p * j.val = s.1.val := by
      dsimp [j]
      calc
        s0 + p * (s.1.val / p) =
            s.1.val % p + p * (s.1.val / p) := by rw [s.2]
        _ = s.1.val := Nat.mod_add_div s.1.val p
    rw [hn]
    exact ZMod.natCast_zmod_val s.1

def residueClassEquiv {p q s0 : ℕ} [NeZero p] [NeZero q]
    (hs0 : s0 < p) :
    Fin q ≃ {s : ZMod (p * q) // s.val % p = s0} :=
  Equiv.ofBijective (residueClassMap (p := p) (q := q) hs0)
    (residueClassMap_bijective hs0)

theorem sum_residueClass_eq
    {p q s0 : ℕ} [NeZero p] [NeZero q] (hs0 : s0 < p)
    (f : ZMod (p * q) → ℝ) :
    (∑ s : ZMod (p * q), if s.val % p = s0 then f s else 0) =
      ∑ j ∈ Finset.range q, f ((s0 + p * j : ℕ) : ZMod (p * q)) := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ s : ZMod (p * q), if s.val % p = s0 then f s else 0) =
        ∑ s : {s : ZMod (p * q) // s.val % p = s0}, f s.1 := by
      rw [← Finset.sum_filter]
      simpa using
        (Finset.sum_subtype
          (Finset.univ.filter fun s : ZMod (p * q) ↦ s.val % p = s0)
          (fun s ↦ by simp) f)
    _ = ∑ j : Fin q,
        f ((residueClassEquiv hs0 j).1) := by
      exact Fintype.sum_equiv (residueClassEquiv hs0).symm
        (fun s : {s : ZMod (p * q) // s.val % p = s0} ↦ f s.1)
        (fun j : Fin q ↦ f ((residueClassEquiv hs0 j).1)) (fun s ↦ by simp)
    _ = ∑ j : Fin q, f ((s0 + p * (j : ℕ) : ℕ) : ZMod (p * q)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rfl

theorem residueClass_geometric_mass_le
    {p q s0 N : ℕ} [NeZero p] [NeZero q]
    (hq2 : 2 ≤ q) (hs0 : s0 < p) (hN : N ≤ q) :
    (∑ s : ZMod (p * q),
      if s.val % p = s0 then
        ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ else 0) ≤
      (q : ℝ) * (3 + Real.log q) := by
  have hp : 0 < p := NeZero.pos p
  have hq : 0 < q := NeZero.pos q
  let theta : ℝ := (s0 : ℝ) / (p * q)
  have htheta0 : 0 ≤ theta := by
    dsimp [theta]
    positivity
  have hthetaq : theta ≤ (1 : ℝ) / q := by
    dsimp [theta]
    have hpR : (0 : ℝ) < p := by positivity
    have hqR : (0 : ℝ) < q := by positivity
    have hs0R : (s0 : ℝ) ≤ p := by exact_mod_cast hs0.le
    field_simp [ne_of_gt hpR, ne_of_gt hqR]
    nlinarith
  rw [sum_residueClass_eq hs0]
  have hfactor (j : ℕ) :
      ‖geometricPhaseSum
          (ZMod.stdAddChar
            (-((s0 + p * j : ℕ) : ZMod (p * q)))) N‖ =
        ‖geometricPhaseSum
          (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / q))) N‖ := by
    rw [stdAddChar_neg_natCast_as_realUnitPhase]
    calc
      ‖geometricPhaseSum
          (realUnitPhase
            (-2 * Real.pi * (((s0 + p * j : ℕ) : ℝ) / ((p * q : ℕ) : ℝ)))) N‖ =
          ‖geometricPhaseSum
            (realUnitPhase
              (2 * Real.pi * (((s0 + p * j : ℕ) : ℝ) /
                ((p * q : ℕ) : ℝ)))) N‖ := by
        convert norm_geometricPhaseSum_realUnitPhase_neg
          (2 * Real.pi * (((s0 + p * j : ℕ) : ℝ) /
            ((p * q : ℕ) : ℝ))) N using 1
        all_goals ring_nf
      _ = ‖geometricPhaseSum
          (realUnitPhase (2 * Real.pi * (theta + (j : ℝ) / q))) N‖ := by
        congr 3
        dsimp [theta]
        push_cast
        have hpR : (p : ℝ) ≠ 0 := by positivity
        have hqR : (q : ℝ) ≠ 0 := by positivity
        field_simp [hpR, hqR]
  simp_rw [hfactor]
  exact shiftedGrid_frequency_mass_le hq2 hN theta htheta0 hthetaq

theorem residueClass_geometric_mass_le_of_modulus_eq
    {Q p q s0 N : ℕ} [NeZero Q] [NeZero p] [NeZero q]
    (hQ : Q = p * q) (hq2 : 2 ≤ q) (hs0 : s0 < p) (hN : N ≤ q) :
    (∑ s : ZMod Q,
      if s.val % p = s0 then
        ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ else 0) ≤
      (q : ℝ) * (3 + Real.log q) := by
  subst Q
  exact residueClass_geometric_mass_le hq2 hs0 hN

theorem dvd_add_iff_mod_eq_complement
    {p c n : ℕ} (hp : 0 < p) (hc : ¬p ∣ c) :
    p ∣ c + n ↔ n % p = p - c % p := by
  have hcp : c % p < p := Nat.mod_lt c hp
  have hnp : n % p < p := Nat.mod_lt n hp
  have hcmod : c % p ≠ 0 := by
    intro h
    exact hc (Nat.dvd_iff_mod_eq_zero.2 h)
  constructor
  · intro hdiv
    have hmod : (c % p + n % p) % p = 0 := by
      rw [← Nat.add_mod]
      exact Nat.dvd_iff_mod_eq_zero.1 hdiv
    have hsumdiv : p ∣ c % p + n % p :=
      Nat.dvd_iff_mod_eq_zero.2 hmod
    rcases hsumdiv with ⟨k, hk⟩
    have hsumpos : 0 < c % p + n % p := by omega
    have hsumlt : c % p + n % p < 2 * p := by omega
    have hk1 : k = 1 := by nlinarith
    have hsumeq : c % p + n % p = p := by simpa [hk1] using hk
    omega
  · intro hn
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hn]
    have hcp_le : c % p ≤ p := hcp.le
    rw [Nat.add_sub_of_le hcp_le, Nat.mod_self]

def residueInterval {Q : ℕ} [NeZero Q] (N : ℕ) : Finset (ZMod Q) :=
  (Finset.range N).image fun t : ℕ ↦ (t : ZMod Q)

theorem natCast_injective_on_range
    {Q N : ℕ} [NeZero Q] (hN : N ≤ Q) :
    Set.InjOn (fun t : ℕ ↦ (t : ZMod Q)) (Finset.range N) := by
  intro a ha b hb hab
  have haQ : a < Q := (Finset.mem_range.mp ha).trans_le hN
  have hbQ : b < Q := (Finset.mem_range.mp hb).trans_le hN
  have hval := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt haQ,
    Nat.mod_eq_of_lt hbQ] using hval

theorem sum_residueInterval
    {Q N : ℕ} [NeZero Q] (hN : N ≤ Q) (f : ZMod Q → ℂ) :
    (∑ x ∈ residueInterval N, f x) =
      ∑ t ∈ Finset.range N, f (t : ZMod Q) := by
  rw [residueInterval, Finset.sum_image (natCast_injective_on_range hN)]

theorem finsetPhaseSum_residueInterval
    {Q N : ℕ} [NeZero Q] (hN : N ≤ Q) (s : ZMod Q) :
    finsetPhaseSum (residueInterval N) s =
      intervalPhaseSum N (fun t : ℕ ↦ (t : ZMod Q)) s := by
  rw [finsetPhaseSum, sum_residueInterval hN]
  rfl

theorem intervalCompletion_identity
    {Q N : ℕ} [NeZero Q] (hN : N ≤ Q) (f : ZMod Q → ℂ) :
    (∑ t ∈ Finset.range N, f (t : ZMod Q)) =
      (Q : ℂ)⁻¹ * ∑ s : ZMod Q,
        completeTwist f s *
          intervalPhaseSum N (fun t : ℕ ↦ (t : ZMod Q)) (-s) := by
  rw [← sum_residueInterval hN]
  rw [finiteCompletion_identity]
  congr 1
  apply Finset.sum_congr rfl
  intro s _hs
  rw [finsetPhaseSum_residueInterval hN]

def fixedDepthPhaseFunction {p m : ℕ} [NeZero (p ^ m)]
    (alpha beta gamma u : ℕ) (z : ZMod (p ^ m)) : ℂ :=
  ZMod.stdAddChar
    ((u : ZMod (p ^ m)) *
      fixedDepthQuadratic (p := p) (m := m)
        (alpha : ZMod (p ^ m)) (beta : ZMod (p ^ m))
        (gamma : ZMod (p ^ m)) z)

theorem completeTwist_fixedDepthPhaseFunction
    {p m : ℕ} [NeZero (p ^ m)]
    (alpha beta gamma u : ℕ) (s : ZMod (p ^ m)) :
    completeTwist (fixedDepthPhaseFunction alpha beta gamma u) s =
      ∑ z : ZMod (p ^ m),
        ZMod.stdAddChar
          (quadraticPhase
            ((p : ZMod (p ^ m)) *
              ((u * alpha : ℕ) : ZMod (p ^ m)))
            ((u * beta + s.val : ℕ) : ZMod (p ^ m))
            ((u * gamma : ℕ) : ZMod (p ^ m)) z) := by
  simp only [completeTwist, fixedDepthPhaseFunction, ← AddChar.map_add_eq_mul]
  apply Finset.sum_congr rfl
  intro z _hz
  congr 1
  have hs : ((s.val : ℕ) : ZMod (p ^ m)) = s :=
    ZMod.natCast_zmod_val s
  rw [Nat.cast_add, hs]
  simp only [fixedDepthQuadratic, quadraticPhase]
  push_cast
  ring

theorem completeTwist_fixedDepthPhaseFunction_eq_zero_of_not_dvd
    {p m alpha beta gamma u : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hm : 1 ≤ m) (s : ZMod (p ^ m))
    (hs : ¬p ∣ u * beta + s.val) :
    completeTwist (fixedDepthPhaseFunction alpha beta gamma u) s = 0 := by
  rw [completeTwist_fixedDepthPhaseFunction]
  exact completeQuadraticSum_eq_zero_of_not_dvd
    (p := p) (m := m) (alpha := u * alpha)
    (b := u * beta + s.val) (gamma := u * gamma) hp hm hs

theorem norm_completeTwist_fixedDepthPhaseFunction_of_dvd
    {p m alpha beta gamma u : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hm : 1 ≤ m) (hp2 : p ≠ 2)
    (halpha : ¬p ∣ alpha) (hu : ¬p ∣ u)
    (s : ZMod (p ^ m)) (hs : p ∣ u * beta + s.val) :
    ‖completeTwist (fixedDepthPhaseFunction alpha beta gamma u) s‖ =
      Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) := by
  have h2 : ¬p ∣ 2 := by
    rw [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
    exact hp2
  have hua : ¬p ∣ u * alpha := by
    simpa only [hp.dvd_mul] using not_or_intro hu halpha
  have hunit2 : IsUnit (2 : ZMod (p ^ m)) :=
    natCast_isUnit_zmod_primePow hp h2
  have hunitUA : IsUnit ((u * alpha : ℕ) : ZMod (p ^ m)) :=
    natCast_isUnit_zmod_primePow hp hua
  have h2ua :
      IsUnit ((2 : ZMod (p ^ m)) *
        ((u * alpha : ℕ) : ZMod (p ^ m))) := hunit2.mul hunitUA
  let b' : ℕ := (u * beta + s.val) / p
  have hb : p * b' = u * beta + s.val := by
    exact Nat.mul_div_cancel' hs
  rw [completeTwist_fixedDepthPhaseFunction]
  convert primePowDegenerateQuadraticGaussSum_norm hp hm
    (((u * alpha : ℕ) : ZMod (p ^ m)))
    ((b' : ℕ) : ZMod (p ^ m))
    (((u * gamma : ℕ) : ZMod (p ^ m))) h2ua using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro z _hz
  congr 2
  push_cast
  simpa only [Nat.cast_add, Nat.cast_mul] using
    congrArg (fun n : ℕ ↦ (n : ZMod (p ^ m))) hb.symm

theorem intervalPhaseSum_natural_eq_geometric
    {Q N : ℕ} [NeZero Q] (s : ZMod Q) :
    intervalPhaseSum N (fun t : ℕ ↦ (t : ZMod Q)) s =
      geometricPhaseSum (ZMod.stdAddChar s) N := by
  simp only [intervalPhaseSum, geometricPhaseSum]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul]
  ring

theorem norm_fixedDepthIncompleteSum_le_completion
    {p m N alpha beta gamma u : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hm2 : 2 ≤ m) (hp2 : p ≠ 2)
    (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta) (hu : ¬p ∣ u)
    (hN : N ≤ p ^ (m - 1)) :
    ‖∑ t ∈ Finset.range N,
      fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
        (t : ZMod (p ^ m))‖ ≤
      ((p ^ m : ℕ) : ℝ)⁻¹ *
        Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
          (((p ^ (m - 1) : ℕ) : ℝ) *
            (3 + Real.log (p ^ (m - 1)))) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let q : ℕ := p ^ (m - 1)
  have hmq : 1 ≤ m - 1 := by omega
  have hq2 : 2 ≤ q := by
    calc
      2 ≤ p := hp.two_le
      _ = p ^ 1 := by simp
      _ ≤ p ^ (m - 1) := Nat.pow_le_pow_right hp.pos hmq
      _ = q := rfl
  let : NeZero q := ⟨by omega⟩
  have hQ : p ^ m = p * q := by
    dsimp [q]
    calc
      p ^ m = p ^ ((m - 1) + 1) := by
        congr 1
        all_goals omega
      _ = p ^ (m - 1) * p := pow_succ p (m - 1)
      _ = p * p ^ (m - 1) := by ac_rfl
  have hNQ : N ≤ p ^ m := by
    refine hN.trans ?_
    rw [hQ]
    calc
      q = 1 * q := by simp
      _ ≤ p * q := Nat.mul_le_mul_right q hp.one_le
  have hc : ¬p ∣ u * beta := by
    simpa only [hp.dvd_mul] using not_or_intro hu hbeta
  let s0 : ℕ := p - (u * beta) % p
  have hcmod : (u * beta) % p ≠ 0 := by
    intro h
    exact hc (Nat.dvd_iff_mod_eq_zero.2 h)
  have hcmodlt : (u * beta) % p < p := Nat.mod_lt _ hp.pos
  have hs0pos : 0 < s0 := by omega
  have hs0lt : s0 < p := by omega
  have hmass :
      (∑ s : ZMod (p ^ m),
        if s.val % p = s0 then
          ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ else 0) ≤
        (q : ℝ) * (3 + Real.log q) := by
    exact residueClass_geometric_mass_le_of_modulus_eq
      hQ hq2 hs0lt hN
  rw [intervalCompletion_identity hNQ]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    ‖∑ s : ZMod (p ^ m),
        completeTwist (fixedDepthPhaseFunction alpha beta gamma u) s *
          intervalPhaseSum N (fun t : ℕ ↦ (t : ZMod (p ^ m))) (-s)‖ ≤
        ∑ s : ZMod (p ^ m),
          ‖completeTwist (fixedDepthPhaseFunction alpha beta gamma u) s *
            intervalPhaseSum N (fun t : ℕ ↦ (t : ZMod (p ^ m))) (-s)‖ :=
      norm_sum_le _ _
    _ = ∑ s : ZMod (p ^ m),
        if s.val % p = s0 then
          Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
            ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ else 0 := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [intervalPhaseSum_natural_eq_geometric]
      have hsupport : p ∣ u * beta + s.val ↔ s.val % p = s0 := by
        simpa [s0] using
          (dvd_add_iff_mod_eq_complement (p := p) (c := u * beta)
            (n := s.val) hp.pos hc)
      by_cases hs : s.val % p = s0
      · have hdvd : p ∣ u * beta + s.val := hsupport.2 hs
        rw [if_pos hs, norm_mul,
          norm_completeTwist_fixedDepthPhaseFunction_of_dvd
            hp (by omega) hp2 halpha hu s hdvd]
      · have hndvd : ¬p ∣ u * beta + s.val := by
          exact fun h ↦ hs (hsupport.1 h)
        rw [if_neg hs,
          completeTwist_fixedDepthPhaseFunction_eq_zero_of_not_dvd
            hp (by omega) s hndvd, zero_mul, norm_zero]
    _ = Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
        (∑ s : ZMod (p ^ m),
          if s.val % p = s0 then
            ‖geometricPhaseSum (ZMod.stdAddChar (-s)) N‖ else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      by_cases hs : s.val % p = s0 <;> simp [hs]
    _ ≤ Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
        ((q : ℝ) * (3 + Real.log q)) :=
      mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _)
    _ = Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
        (((p ^ (m - 1) : ℕ) : ℝ) *
          (3 + Real.log (p ^ (m - 1)))) := by
      dsimp [q]
      simp only [Nat.cast_pow]

theorem primePower_completion_prefactor_eq_sqrt
    {p m : ℕ} (hp : 0 < p) (hm : 1 ≤ m) :
    ((p ^ m : ℕ) : ℝ)⁻¹ * Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
        ((p ^ (m - 1) : ℕ) : ℝ) =
      Real.sqrt ((p ^ (m - 1) : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < p := by positivity
  have hpowR : (0 : ℝ) < (p : ℝ) ^ (m - 1) := by positivity
  push_cast
  have hexp : m + 1 = 2 + (m - 1) := by omega
  rw [hexp, pow_add]
  rw [Real.sqrt_mul (sq_nonneg (p : ℝ))]
  rw [show (p : ℝ) ^ 2 = (p : ℝ) ^ 2 by rfl,
    Real.sqrt_sq_eq_abs, abs_of_pos hpR]
  rw [show m = 1 + (m - 1) by omega, pow_add, pow_one]
  field_simp [ne_of_gt hpR, ne_of_gt hpowR]
  congr 1
  omega

theorem primePower_logFactor_le
    {p m r : ℕ} (hp : 0 < p) (hmr : m ≤ 2 * r) :
    3 + Real.log (p ^ (m - 1)) ≤
      ((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  rw [Real.log_pow]
  have hmcast : ((m - 1 : ℕ) : ℝ) ≤ 2 * r := by exact_mod_cast (by omega : m - 1 ≤ 2 * r)
  have hrcast : (0 : ℝ) ≤ r := by positivity
  push_cast
  nlinarith

theorem primePower_sqrtFactor_le
    {p m r : ℕ} (hp : 0 < p) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (hmr : m ≤ 2 * r) :
    Real.sqrt ((p ^ (m - 1) : ℕ) : ℝ) ≤
      Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.pow_le_pow_right hp (by omega : m - 1 ≤ 2 * r - 1)

theorem norm_fixedDepthIncompleteSum_le_uniform
    {p m r alpha beta gamma u : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hr : 1 ≤ r) (hrm : r < m) (hmr : m ≤ 2 * r)
    (hp2 : p ≠ 2) (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta)
    (hu : ¬p ∣ u) :
    ‖∑ t ∈ Finset.range (p ^ r),
      fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
        (t : ZMod (p ^ m))‖ ≤
      Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) := by
  have hm2 : 2 ≤ m := by omega
  have hN : p ^ r ≤ p ^ (m - 1) :=
    Nat.pow_le_pow_right hp.pos (by omega)
  have hbase := norm_fixedDepthIncompleteSum_le_completion
    (p := p) (m := m) (N := p ^ r) (alpha := alpha) (beta := beta)
    (gamma := gamma) (u := u) hp hm2 hp2 halpha hbeta hu hN
  calc
    ‖∑ t ∈ Finset.range (p ^ r),
      fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
        (t : ZMod (p ^ m))‖ ≤
        ((p ^ m : ℕ) : ℝ)⁻¹ *
          Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
            (((p ^ (m - 1) : ℕ) : ℝ) *
              (3 + Real.log (p ^ (m - 1)))) := hbase
    _ = Real.sqrt ((p ^ (m - 1) : ℕ) : ℝ) *
        (3 + Real.log (p ^ (m - 1))) := by
      rw [show
        ((p ^ m : ℕ) : ℝ)⁻¹ *
            Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
              (((p ^ (m - 1) : ℕ) : ℝ) *
                (3 + Real.log (p ^ (m - 1)))) =
          (((p ^ m : ℕ) : ℝ)⁻¹ *
            Real.sqrt ((p ^ (m + 1) : ℕ) : ℝ) *
              ((p ^ (m - 1) : ℕ) : ℝ)) *
                (3 + Real.log (p ^ (m - 1))) by ring]
      rw [primePower_completion_prefactor_eq_sqrt hp.pos (by omega)]
    _ ≤ Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) := by
      apply mul_le_mul
      · exact primePower_sqrtFactor_le hp.pos (by omega) hr hmr
      · exact primePower_logFactor_le hp.pos hmr
      · apply add_nonneg (by norm_num)
        apply Real.log_nonneg
        exact_mod_cast (Nat.one_le_pow (m - 1) p hp.one_le)
      · exact Real.sqrt_nonneg _

theorem norm_fixedDepthIncompleteSum_shift_le_uniform
    {p m r alpha beta gamma u : ℕ} [NeZero (p ^ m)]
    (hp : p.Prime) (hr : 1 ≤ r) (hrm : r < m) (hmr : m ≤ 2 * r)
    (hp2 : p ≠ 2) (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta)
    (hu : ¬p ∣ u) (M : ℕ) :
    ‖∑ t ∈ Finset.range (p ^ r),
      fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
        ((M + t : ℕ) : ZMod (p ^ m))‖ ≤
      Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) := by
  let beta' : ℕ := beta + 2 * p * alpha * M
  let gamma' : ℕ := p * alpha * M ^ 2 + beta * M + gamma
  have hmultiple : p ∣ 2 * p * alpha * M := by
    refine ⟨2 * alpha * M, ?_⟩
    ring
  have hbeta' : ¬p ∣ beta' := by
    intro h
    exact hbeta ((Nat.dvd_add_iff_left hmultiple).mpr h)
  have hphase (t : ℕ) :
      fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
          ((M + t : ℕ) : ZMod (p ^ m)) =
        fixedDepthPhaseFunction (p := p) (m := m) alpha beta' gamma' u
          (t : ZMod (p ^ m)) := by
    simp only [fixedDepthPhaseFunction]
    congr 1
    simp only [fixedDepthQuadratic]
    dsimp [beta', gamma']
    push_cast
    ring
  simp_rw [hphase]
  exact norm_fixedDepthIncompleteSum_le_uniform
    hp hr hrm hmr hp2 halpha hbeta' hu

theorem stdAddChar_powScale {p v m x : ℕ} [NeZero p] :
    ZMod.stdAddChar (((p ^ v * x : ℕ) : ZMod (p ^ (v + m)))) =
      ZMod.stdAddChar ((x : ℕ) : ZMod (p ^ m)) := by
  rw [show ((p ^ v * x : ℕ) : ZMod (p ^ (v + m))) =
      ((p ^ v * x : ℤ) : ZMod (p ^ (v + m))) by norm_num,
    show ((x : ℕ) : ZMod (p ^ m)) = ((x : ℤ) : ZMod (p ^ m)) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_add]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp [pow_ne_zero _ hpC]

def fixedDepthQuadraticNat
    (p alpha beta gamma t : ℕ) : ℕ :=
  p * alpha * t ^ 2 + beta * t + gamma

theorem fixedDepthPhase_reduce
    {p v m alpha beta gamma u t : ℕ} [NeZero p] :
    ZMod.stdAddChar
        (((p ^ v * u : ℕ) : ZMod (p ^ (v + m))) *
          fixedDepthQuadratic
            (alpha : ZMod (p ^ (v + m)))
            (beta : ZMod (p ^ (v + m)))
            (gamma : ZMod (p ^ (v + m)))
            (t : ZMod (p ^ (v + m)))) =
      fixedDepthPhaseFunction (p := p) (m := m)
        alpha beta gamma u (t : ZMod (p ^ m)) := by
  rw [show
      (((p ^ v * u : ℕ) : ZMod (p ^ (v + m))) *
        fixedDepthQuadratic
          (alpha : ZMod (p ^ (v + m)))
          (beta : ZMod (p ^ (v + m)))
          (gamma : ZMod (p ^ (v + m)))
          (t : ZMod (p ^ (v + m)))) =
        ((p ^ v * (u * fixedDepthQuadraticNat p alpha beta gamma t) : ℕ) :
          ZMod (p ^ (v + m))) by
      simp only [fixedDepthQuadratic, fixedDepthQuadraticNat]
      push_cast
      ring]
  rw [stdAddChar_powScale]
  simp only [fixedDepthPhaseFunction, fixedDepthQuadratic, fixedDepthQuadraticNat]
  congr 1
  push_cast
  ring

theorem fixedDepthPhase_reduce_of_exponent_eq
    {p q v m alpha beta gamma u t : ℕ} [NeZero p]
    (hq : q = v + m) :
    ZMod.stdAddChar
        (((p ^ v * u : ℕ) : ZMod (p ^ q)) *
          fixedDepthQuadratic
            (alpha : ZMod (p ^ q))
            (beta : ZMod (p ^ q))
            (gamma : ZMod (p ^ q))
            (t : ZMod (p ^ q))) =
      fixedDepthPhaseFunction (p := p) (m := m)
        alpha beta gamma u (t : ZMod (p ^ m)) := by
  rw [show
      (((p ^ v * u : ℕ) : ZMod (p ^ q)) *
        fixedDepthQuadratic
          (alpha : ZMod (p ^ q))
          (beta : ZMod (p ^ q))
          (gamma : ZMod (p ^ q))
          (t : ZMod (p ^ q))) =
        ((p ^ v * (u * fixedDepthQuadraticNat p alpha beta gamma t) : ℕ) :
          ZMod (p ^ q)) by
      simp only [fixedDepthQuadratic, fixedDepthQuadraticNat]
      push_cast
      ring]
  rw [show
      fixedDepthPhaseFunction (p := p) (m := m)
          alpha beta gamma u (t : ZMod (p ^ m)) =
        ZMod.stdAddChar
          ((u * fixedDepthQuadraticNat p alpha beta gamma t : ℕ) :
            ZMod (p ^ m)) by
      simp only [fixedDepthPhaseFunction, fixedDepthQuadratic,
        fixedDepthQuadraticNat]
      congr 1
      push_cast
      ring]
  rw [show
      ((p ^ v * (u * fixedDepthQuadraticNat p alpha beta gamma t) : ℕ) :
          ZMod (p ^ q)) =
        ((p ^ v * (u * fixedDepthQuadraticNat p alpha beta gamma t) : ℤ) :
          ZMod (p ^ q)) by norm_num,
    show
      ((u * fixedDepthQuadraticNat p alpha beta gamma t : ℕ) : ZMod (p ^ m)) =
        ((u * fixedDepthQuadraticNat p alpha beta gamma t : ℤ) : ZMod (p ^ m)) by
          norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [hq, pow_add]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp [pow_ne_zero _ hpC]

theorem norm_fixedDepthIntervalPhaseSum_le_uniform
    {p r alpha beta gamma : ℕ} [NeZero p]
    (hp : p.Prime) (hr : 1 ≤ r) (hp2 : p ≠ 2)
    (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta)
    (M : ℕ) (h : ZMod (p ^ (2 * r))) (hh : h ≠ 0) :
    ‖intervalPhaseSum (p ^ r)
        (fun t : ℕ ↦
          fixedDepthQuadratic
            (alpha : ZMod (p ^ (2 * r)))
            (beta : ZMod (p ^ (2 * r)))
            (gamma : ZMod (p ^ (2 * r)))
            ((M + t : ℕ) : ZMod (p ^ (2 * r)))) h‖ ≤
      Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) := by
  have hn : h.val ≠ 0 := (ZMod.val_ne_zero h).2 hh
  rcases Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one with
    ⟨v, u, hu, hval⟩
  have hv : v < 2 * r := by
    by_contra hnot
    have hvle : 2 * r ≤ v := Nat.le_of_not_gt hnot
    have hdvd : p ^ (2 * r) ∣ h.val := by
      rw [hval]
      exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow p hvle) u
    have hpos : 0 < h.val := Nat.pos_of_ne_zero hn
    have hle : p ^ (2 * r) ≤ h.val := Nat.le_of_dvd hpos hdvd
    exact (not_le_of_gt h.val_lt) hle
  let m : ℕ := 2 * r - v
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmle : m ≤ 2 * r := by dsimp [m]; omega
  have hexp : 2 * r = v + m := by dsimp [m]; omega
  have hsum :
      intervalPhaseSum (p ^ r)
          (fun t : ℕ ↦
            fixedDepthQuadratic
              (alpha : ZMod (p ^ (2 * r)))
              (beta : ZMod (p ^ (2 * r)))
              (gamma : ZMod (p ^ (2 * r)))
              ((M + t : ℕ) : ZMod (p ^ (2 * r)))) h =
        ∑ t ∈ Finset.range (p ^ r),
          fixedDepthPhaseFunction (p := p) (m := m)
            alpha beta gamma u ((M + t : ℕ) : ZMod (p ^ m)) := by
    simp only [intervalPhaseSum]
    apply Finset.sum_congr rfl
    intro t _ht
    rw [← ZMod.natCast_zmod_val h, hval]
    exact
      (fixedDepthPhase_reduce_of_exponent_eq (p := p) (q := 2 * r)
        (v := v) (m := m)
        (alpha := alpha) (beta := beta) (gamma := gamma) (u := u)
        (t := M + t) hexp)
  rw [hsum]
  by_cases hmr : m ≤ r
  · let beta' : ℕ := beta + 2 * p * alpha * M
    let gamma' : ℕ := p * alpha * M ^ 2 + beta * M + gamma
    have hmultiple : p ∣ 2 * p * alpha * M := by
      refine ⟨2 * alpha * M, ?_⟩
      ring
    have hbeta' : ¬p ∣ beta' := by
      intro hdiv
      exact hbeta ((Nat.dvd_add_iff_left hmultiple).mpr hdiv)
    have hphase (t : ℕ) :
        fixedDepthPhaseFunction (p := p) (m := m) alpha beta gamma u
            ((M + t : ℕ) : ZMod (p ^ m)) =
          fixedDepthPhaseFunction (p := p) (m := m) alpha beta' gamma' u
            (t : ZMod (p ^ m)) := by
      simp only [fixedDepthPhaseFunction]
      congr 1
      simp only [fixedDepthQuadratic]
      dsimp [beta', gamma']
      push_cast
      ring
    simp_rw [hphase]
    have hbetaUnit : IsUnit (beta' : ZMod (p ^ m)) :=
      natCast_isUnit_zmod_primePow hp hbeta'
    have huNe : (u : ZMod (p ^ m)) ≠ 0 := by
      intro hzero
      have hpowdvd : p ^ m ∣ u :=
        (ZMod.natCast_eq_zero_iff u (p ^ m)).1 hzero
      exact hu (by
        simpa only [pow_one] using
          ((Nat.pow_dvd_pow p hm).trans hpowdvd))
    have hzero := incompleteFixedDepthQuadraticSum_eq_zero_of_le
      (p := p) (m := m) (r := r) hp.pos hmr hbetaUnit
      (alpha : ZMod (p ^ m)) (gamma' : ZMod (p ^ m))
      (u : ZMod (p ^ m)) huNe
    have hzero' :
        (∑ t ∈ Finset.range (p ^ r),
          fixedDepthPhaseFunction (p := p) (m := m)
            alpha beta' gamma' u (t : ZMod (p ^ m))) = 0 := by
      simpa only [fixedDepthPhaseFunction] using hzero
    rw [hzero', norm_zero]
    positivity
  · exact norm_fixedDepthIncompleteSum_shift_le_uniform
      hp hr (Nat.lt_of_not_ge hmr) hmle hp2 halpha hbeta hu M

theorem fixedDepth_intervalHitCount_discrepancy_le
    {p r alpha beta gamma : ℕ} [NeZero p]
    (hp : p.Prime) (hr : 1 ≤ r) (hp2 : p ≠ 2)
    (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta)
    (M : ℕ) (A : Finset (ZMod (p ^ (2 * r))))
    (hA :
      (∑ h : ZMod (p ^ (2 * r)),
          ‖ZMod.dft (finsetIndicator A) h‖) ≤
        ((p ^ (2 * r) : ℕ) : ℝ) *
          (3 + Real.log p) ^ (2 * r)) :
    ‖(intervalHitCount (p ^ r)
          (fun t : ℕ ↦
            fixedDepthQuadratic
              (alpha : ZMod (p ^ (2 * r)))
              (beta : ZMod (p ^ (2 * r)))
              (gamma : ZMod (p ^ (2 * r)))
              ((M + t : ℕ) : ZMod (p ^ (2 * r)))) A : ℂ) -
        (A.card : ℂ) * (p ^ r) / (p ^ (2 * r))‖ ≤
      Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) *
          (3 + Real.log p) ^ (2 * r) := by
  let F : ℕ → ZMod (p ^ (2 * r)) := fun t ↦
    fixedDepthQuadratic
      (alpha : ZMod (p ^ (2 * r)))
      (beta : ZMod (p ^ (2 * r)))
      (gamma : ZMod (p ^ (2 * r)))
      ((M + t : ℕ) : ZMod (p ^ (2 * r)))
  let C : ℝ :=
    Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
      (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p))
  let L : ℝ := (3 + Real.log p) ^ (2 * r)
  have hlog : 0 ≤ Real.log (p : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hphase (h : ZMod (p ^ (2 * r))) (hh : h ≠ 0) :
      ‖intervalPhaseSum (p ^ r) F h‖ ≤ C := by
    exact norm_fixedDepthIntervalPhaseSum_le_uniform
      hp hr hp2 halpha hbeta M h hh
  have herase :
      (∑ h ∈ (Finset.univ.erase (0 : ZMod (p ^ (2 * r)))),
          ‖ZMod.dft (finsetIndicator A) h‖) ≤
        ∑ h : ZMod (p ^ (2 * r)),
          ‖ZMod.dft (finsetIndicator A) h‖ := by
    exact Finset.sum_le_univ_sum_of_nonneg
      (fun h ↦ norm_nonneg (ZMod.dft (finsetIndicator A) h))
  change
    ‖(intervalHitCount (p ^ r) F A : ℂ) -
        (A.card : ℂ) * (p ^ r) / (p ^ (2 * r))‖ ≤ C * L
  calc
    ‖(intervalHitCount (p ^ r) F A : ℂ) -
        (A.card : ℂ) * (p ^ r) / (p ^ (2 * r))‖ ≤
      (((p ^ (2 * r) : ℕ) : ℝ)⁻¹) *
        ∑ h ∈ (Finset.univ.erase (0 : ZMod (p ^ (2 * r)))),
          ‖ZMod.dft (finsetIndicator A) h‖ * ‖intervalPhaseSum (p ^ r) F h‖ :=
      by
        simpa only [Nat.cast_pow] using
          (intervalHitCount_discrepancy_le (p ^ r) F A)
    _ ≤ (((p ^ (2 * r) : ℕ) : ℝ)⁻¹) *
        ∑ h ∈ (Finset.univ.erase (0 : ZMod (p ^ (2 * r)))),
          ‖ZMod.dft (finsetIndicator A) h‖ * C := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_le_sum
      intro h hhmem
      exact mul_le_mul_of_nonneg_left
        (hphase h (Finset.ne_of_mem_erase hhmem))
        (norm_nonneg _)
    _ = (((p ^ (2 * r) : ℕ) : ℝ)⁻¹) *
        ((∑ h ∈ (Finset.univ.erase (0 : ZMod (p ^ (2 * r)))),
          ‖ZMod.dft (finsetIndicator A) h‖) * C) := by
      rw [Finset.sum_mul]
    _ ≤ (((p ^ (2 * r) : ℕ) : ℝ)⁻¹) *
        ((∑ h : ZMod (p ^ (2 * r)),
          ‖ZMod.dft (finsetIndicator A) h‖) * C) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right herase hC)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (((p ^ (2 * r) : ℕ) : ℝ)⁻¹) *
        ((((p ^ (2 * r) : ℕ) : ℝ) * L) * C) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hA hC)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = C * L := by
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hQnat : p ^ (2 * r) ≠ 0 := pow_ne_zero _ hp.ne_zero
      have hQ : (((p ^ (2 * r) : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hQnat
      field_simp [hQ]

theorem fixedDepth_intervalHitCount_le
    {p r alpha beta gamma : ℕ} [NeZero p]
    (hp : p.Prime) (hr : 1 ≤ r) (hp2 : p ≠ 2)
    (halpha : ¬p ∣ alpha) (hbeta : ¬p ∣ beta)
    (M : ℕ) (A : Finset (ZMod (p ^ (2 * r))))
    (hA :
      (∑ h : ZMod (p ^ (2 * r)),
          ‖ZMod.dft (finsetIndicator A) h‖) ≤
        ((p ^ (2 * r) : ℕ) : ℝ) *
          (3 + Real.log p) ^ (2 * r)) :
    (intervalHitCount (p ^ r)
        (fun t : ℕ ↦
          fixedDepthQuadratic
            (alpha : ZMod (p ^ (2 * r)))
            (beta : ZMod (p ^ (2 * r)))
            (gamma : ZMod (p ^ (2 * r)))
            ((M + t : ℕ) : ZMod (p ^ (2 * r)))) A : ℝ) ≤
      (A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ) +
        Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
          (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) *
            (3 + Real.log p) ^ (2 * r) := by
  let F : ℕ → ZMod (p ^ (2 * r)) := fun t ↦
    fixedDepthQuadratic
      (alpha : ZMod (p ^ (2 * r)))
      (beta : ZMod (p ^ (2 * r)))
      (gamma : ZMod (p ^ (2 * r)))
      ((M + t : ℕ) : ZMod (p ^ (2 * r)))
  let D : ℝ :=
    Real.sqrt ((p ^ (2 * r - 1) : ℕ) : ℝ) *
      (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) *
        (3 + Real.log p) ^ (2 * r)
  have hdisc := fixedDepth_intervalHitCount_discrepancy_le
    (p := p) (r := r) (alpha := alpha) (beta := beta) (gamma := gamma)
    hp hr hp2 halpha hbeta M A hA
  have hre :
      ((intervalHitCount (p ^ r) F A : ℝ) -
        (A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ)) ≤
        ‖(intervalHitCount (p ^ r) F A : ℂ) -
          (A.card : ℂ) * (p ^ r) / (p ^ (2 * r))‖ := by
    have hre0 := Complex.re_le_norm
      ((intervalHitCount (p ^ r) F A : ℂ) -
        (A.card : ℂ) * (p ^ r) / (p ^ (2 * r)))
    have hexp :
        ((A.card : ℂ) * (p ^ r) / (p ^ (2 * r))).re =
          (A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ) := by
      have hz :
          (A.card : ℂ) * (p ^ r) / (p ^ (2 * r)) =
            Complex.ofReal ((A.card : ℝ) * (p ^ r : ℕ) /
              (p ^ (2 * r) : ℕ)) := by
        norm_num
      rw [hz, Complex.ofReal_re]
    simpa only [Complex.sub_re, Complex.natCast_re, hexp] using hre0
  change (intervalHitCount (p ^ r) F A : ℝ) ≤
    (A.card : ℝ) * (p ^ r : ℕ) / (p ^ (2 * r) : ℕ) + D
  have hdisc' :
      ‖(intervalHitCount (p ^ r) F A : ℂ) -
          (A.card : ℂ) * (p ^ r) / (p ^ (2 * r))‖ ≤ D := by
    simpa only [F, D] using hdisc
  linarith

#print axioms finiteFourier_inversion_at
#print axioms intervalHitCount_fourier_identity
#print axioms finiteCompletion_identity
#print axioms intervalHitCount_discrepancy_le
#print axioms completeSum_eq_zero_of_constantShift
#print axioms primePow_topLayer_ne_zero
#print axioms completeQuadraticSum_eq_zero_of_not_dvd
#print axioms incompleteFixedDepthQuadraticSum_eq_zero_of_le
#print axioms card_primePow_mul_kernel
#print axioms quadraticGaussSum_normSq
#print axioms primePowDegenerateQuadraticGaussSum_norm
#print axioms shiftedGrid_frequency_mass_le
#print axioms digitBoxFourierCoeff_factorization
#print axioms digitBoxFourierCoeff_l1_le
#print axioms digitBoxFourierCoeff_interval_l1_le
#print axioms norm_fixedDepthIncompleteSum_shift_le_uniform
#print axioms norm_fixedDepthIntervalPhaseSum_le_uniform
#print axioms fixedDepth_intervalHitCount_discrepancy_le
#print axioms fixedDepth_intervalHitCount_le

end

end FixedDepthFourier
end Erdos730

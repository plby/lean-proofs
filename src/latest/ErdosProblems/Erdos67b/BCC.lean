import ErdosProblems.Erdos67b.CompletelyMultiplicative
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The finitary Borwein--Choi--Coons construction

This file contains the finite cyclic identities used in the generalized
Borwein--Choi--Coons argument in Tao's proof of the Erdős discrepancy problem.
The modulus of the ambient cyclic group is kept separate from the conductor of
the Dirichlet character; this is important when the construction is applied at
several different scales.
-/

open scoped BigOperators ZMod
open Finset

namespace Erdos67b

/-- A residue is good if none of its short positive translates is divisible by
the prescribed power of any prime factor of `q`. -/
def GoodResidue (q k H a : ℕ) : Prop :=
  ∀ p ∈ q.primeFactors, ∀ m ∈ Finset.Icc 1 (2 * H), ¬p ^ k ∣ a + m

/-- Extend a Dirichlet character of conductor `q` to a function on `ZMod N`
supported on the multiples of `d`, dividing the canonical representative by
`d` on that support. -/
noncomputable def scaledCharacter {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (d : ℕ) (a : ZMod N) : ℂ :=
  if _h : d ∣ a.val then χ ((a.val / d : ℕ) : ZMod q) else 0

/-- A cyclic translate of `scaledCharacter`. -/
noncomputable def scaledShiftedCharacter {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (d m : ℕ) (a : ZMod N) : ℂ :=
  scaledCharacter χ d (a + (m : ZMod N))

@[simp]
theorem scaledShiftedCharacter_zero {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (d : ℕ) (a : ZMod N) :
    scaledShiftedCharacter χ d 0 a = scaledCharacter χ d a := by
  simp [scaledShiftedCharacter]

theorem dvd_val_of_scaledCharacter_ne_zero {q N : ℕ} [NeZero q] [NeZero N]
    {χ : DirichletCharacter ℂ q} {d : ℕ} {a : ZMod N}
    (ha : scaledCharacter χ d a ≠ 0) : d ∣ a.val := by
  simp only [scaledCharacter] at ha
  split at ha <;> simp_all

theorem castHom_eq_zero_of_dvd_val {N d : ℕ} [NeZero N] (hd : d ∣ N)
    {a : ZMod N} (ha : d ∣ a.val) : ZMod.castHom hd (ZMod d) a = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  exact ha

/-- Distinct shifts in a block of length `d` have disjoint supports, provided
the ambient cyclic modulus is divisible by `d`. -/
theorem scaledShiftedCharacter_support_disjoint {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) {d i j : ℕ} (hdN : d ∣ N)
    (hi : i < d) (hj : j < d) (hij : i ≠ j) (a : ZMod N) :
    scaledShiftedCharacter χ d i a = 0 ∨ scaledShiftedCharacter χ d j a = 0 := by
  by_contra h
  simp only [not_or] at h
  have hi0 : ZMod.castHom hdN (ZMod d) (a + (i : ZMod N)) = 0 :=
    castHom_eq_zero_of_dvd_val hdN
      (dvd_val_of_scaledCharacter_ne_zero h.1)
  have hj0 : ZMod.castHom hdN (ZMod d) (a + (j : ZMod N)) = 0 :=
    castHom_eq_zero_of_dvd_val hdN
      (dvd_val_of_scaledCharacter_ne_zero h.2)
  have hi0' : ZMod.castHom hdN (ZMod d) a + (i : ZMod d) = 0 := by
    simpa only [map_add, map_natCast] using hi0
  have hj0' : ZMod.castHom hdN (ZMod d) a + (j : ZMod d) = 0 := by
    simpa only [map_add, map_natCast] using hj0
  have hc : (i : ZMod d) = (j : ZMod d) := by
    exact add_left_cancel (hi0'.trans hj0'.symm)
  have heq : i = j :=
    ((ZMod.natCast_eq_natCast_iff i j d).mp hc).eq_of_lt_of_lt hi hj
  exact hij heq

/-- The squared norm of a sum of pointwise-disjoint complex terms is the sum
of their squared norms. -/
theorem normSq_sum_eq_sum_normSq_of_pairwise_disjoint {ι : Type*}
    (s : Finset ι) (f : ι → ℂ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i = 0 ∨ f j = 0) :
    Complex.normSq (∑ i ∈ s, f i) = ∑ i ∈ s, Complex.normSq (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have ih' : Complex.normSq (∑ j ∈ s, f j) =
          ∑ j ∈ s, Complex.normSq (f j) := by
        apply ih
        intro j hj k hk hjk
        exact hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
      have hcross : (f i * (starRingEnd ℂ) (∑ j ∈ s, f j)).re = 0 := by
        have hz : ∑ j ∈ s, f i * (starRingEnd ℂ) (f j) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rcases hdisj i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
              (by exact fun hij ↦ hi (hij ▸ hj)) with hfi | hfj
          · simp [hfi]
          · simp [hfj]
        rw [map_sum, Finset.mul_sum, hz]
        rfl
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Complex.normSq_add, ih', hcross]
      ring

/-- Exact pointwise energy decomposition for a complete length-`d` cyclic
block of translates of a scaled character. -/
theorem scaledShiftedCharacter_block_normSq {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) {d : ℕ} (hdN : d ∣ N) (a : ZMod N) :
    Complex.normSq (∑ m ∈ Finset.range d, scaledShiftedCharacter χ d m a) =
      ∑ m ∈ Finset.range d, Complex.normSq (scaledShiftedCharacter χ d m a) := by
  classical
  apply normSq_sum_eq_sum_normSq_of_pairwise_disjoint
  intro i hi j hj hij
  exact scaledShiftedCharacter_support_disjoint χ hdN
    (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij a

/-- Exact total block energy.  A cyclic block of `d` shifts has precisely `d`
times the energy of the unshifted scaled character. -/
theorem scaledShiftedCharacter_block_energy {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) {d : ℕ} (hdN : d ∣ N) :
    ∑ a : ZMod N,
        Complex.normSq (∑ m ∈ Finset.range d, scaledShiftedCharacter χ d m a) =
      (d : ℝ) * ∑ a : ZMod N, Complex.normSq (scaledCharacter χ d a) := by
  classical
  simp_rw [scaledShiftedCharacter_block_normSq χ hdN]
  rw [Finset.sum_comm]
  have hshift (m : ℕ) :
      (∑ a : ZMod N, Complex.normSq (scaledShiftedCharacter χ d m a)) =
        ∑ a : ZMod N, Complex.normSq (scaledCharacter χ d a) := by
    apply Fintype.sum_equiv (Equiv.addRight (m : ZMod N))
    intro a
    rfl
  simp_rw [hshift]
  simp

/-- The total squared energy of a Dirichlet character over one full period is
Euler's totient of its conductor. -/
theorem dirichletCharacter_sum_normSq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, Complex.normSq (χ a) = (q.totient : ℝ) := by
  classical
  have hterm (a : ZMod q) :
      Complex.normSq (χ a) = (1 : DirichletCharacter ℝ q) a := by
    by_cases ha : IsUnit a
    · have hn : ‖χ a‖ = 1 := by
        simpa only [ha.unit_spec] using χ.unit_norm_eq_one ha.unit
      rw [Complex.normSq_eq_norm_sq, hn, one_pow]
      exact (MulChar.one_apply (R' := ℝ) ha).symm
    · rw [χ.map_nonunit ha, Complex.normSq_zero]
      exact ((1 : DirichletCharacter ℝ q).map_nonunit ha).symm
  simp_rw [hterm]
  rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]

@[simp]
theorem scaledCharacter_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    scaledCharacter χ 1 a = χ a := by
  simp only [scaledCharacter, one_dvd, ↓reduceDIte, Nat.div_one]
  rw [a.natCast_zmod_val]

/-- In the mixed-radix enumeration `r + d * b` of `Fin (q * d)`, the
multiples of `d` are exactly the terms with `r = 0`. -/
theorem sum_fin_if_dvd_add_mul {q d : ℕ} [NeZero d]
    {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    (∑ x : Fin q × Fin d,
        if d ∣ x.2.val + d * x.1.val then F ((x.2.val + d * x.1.val) / d) else 0) =
      ∑ b : Fin q, F b.val := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _hb
  have hdvd (r : Fin d) : d ∣ r.val + d * b.val ↔ r = 0 := by
    constructor
    · intro h
      have hr : d ∣ r.val :=
        (Nat.dvd_add_iff_left (dvd_mul_right d b.val)).mpr h
      exact Fin.ext (Nat.eq_zero_of_dvd_of_lt hr r.isLt)
    · intro h
      subst r
      simp
  simp_rw [hdvd]
  simp [NeZero.ne d]

@[simp]
theorem val_finEquiv {n : ℕ} [NeZero n] (x : Fin n) :
    (ZMod.finEquiv n x).val = x.val := by
  cases n with
  | zero => exact Fin.elim0 x
  | succ n => rfl

theorem finEquiv_apply_eq_natCast {n : ℕ} [NeZero n] (x : Fin n) :
    ZMod.finEquiv n x = (x.val : ZMod n) := by
  apply ZMod.val_injective n
  rw [val_finEquiv, ZMod.val_natCast_of_lt x.isLt]

/-- A scaled character on `ZMod (q * d)` has the same total energy as one
unscaled period of the original character. -/
theorem scaledCharacter_sum_normSq_mul {q d : ℕ} [NeZero q] [NeZero d]
    (χ : DirichletCharacter ℂ q) :
    (∑ a : ZMod (q * d), Complex.normSq (scaledCharacter χ d a)) =
      (q.totient : ℝ) := by
  classical
  let e : Fin q × Fin d ≃ ZMod (q * d) :=
    finProdFinEquiv.trans (ZMod.finEquiv (q * d)).toEquiv
  calc
    (∑ a : ZMod (q * d), Complex.normSq (scaledCharacter χ d a)) =
        ∑ x : Fin q × Fin d, Complex.normSq (scaledCharacter χ d (e x)) := by
      exact (Fintype.sum_equiv e _ _ (fun _ ↦ rfl)).symm
    _ = ∑ x : Fin q × Fin d,
        if d ∣ x.2.val + d * x.1.val then
          Complex.normSq (χ (((x.2.val + d * x.1.val) / d : ℕ) : ZMod q)) else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      have heval : (e x).val = x.2.val + d * x.1.val := by
        change (ZMod.finEquiv (q * d) (finProdFinEquiv x)).val = _
        rw [val_finEquiv]
        rfl
      simp only [scaledCharacter, heval]
      split_ifs <;> simp
    _ = ∑ b : Fin q, Complex.normSq (χ ((b.val : ℕ) : ZMod q)) :=
      sum_fin_if_dvd_add_mul
        (fun n ↦ Complex.normSq (χ ((n : ℕ) : ZMod q)))
    _ = ∑ a : ZMod q, Complex.normSq (χ a) := by
      apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
      intro b
      change Complex.normSq (χ ((b.val : ℕ) : ZMod q)) =
        Complex.normSq (χ (ZMod.finEquiv q b))
      rw [finEquiv_apply_eq_natCast]
    _ = (q.totient : ℝ) := dirichletCharacter_sum_normSq χ

/-- Closed form of the exact block energy on the natural ambient modulus
`q * d`: it is `d * φ(q)`. -/
theorem scaledShiftedCharacter_block_energy_mul {q d : ℕ} [NeZero q] [NeZero d]
    (χ : DirichletCharacter ℂ q) :
    (∑ a : ZMod (q * d),
        Complex.normSq
          (∑ m ∈ Finset.range d, scaledShiftedCharacter χ d m a)) =
      (d : ℝ) * (q.totient : ℝ) := by
  rw [scaledShiftedCharacter_block_energy χ (dvd_mul_left d q),
    scaledCharacter_sum_normSq_mul χ]

/-- Compatibility of the standard additive characters with cancelling a
scale `d` between the modulus `q * d` and an argument divisible by `d`. -/
theorem stdAddChar_scaled_castHom {q d : ℕ} [NeZero q] [NeZero d]
    (b : ℕ) (k : ZMod (q * d)) :
    ZMod.stdAddChar (-(((d * b : ℕ) : ZMod (q * d)) * k)) =
      ZMod.stdAddChar
        (-(((b : ℕ) : ZMod q) * ZMod.castHom (dvd_mul_right q d) (ZMod q) k)) := by
  rw [← k.natCast_zmod_val]
  simp only [map_natCast]
  rw [show -(((d * b : ℕ) : ZMod (q * d)) * (k.val : ZMod (q * d))) =
      ((-((d * b * k.val : ℕ) : ℤ) : ℤ) : ZMod (q * d)) by
        push_cast
        ring,
    show -(((b : ℕ) : ZMod q) * (k.val : ZMod q)) =
      ((-((b * k.val : ℕ) : ℤ) : ℤ) : ZMod q) by
        push_cast
        ring]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp [NeZero.ne q, NeZero.ne d]

/-- Exact Fourier transform of a scaled character on its natural modulus.
Scaling the input support by `d` simply reduces the frequency modulo `q`. -/
theorem dft_scaledCharacter_mul {q d : ℕ} [NeZero q] [NeZero d]
    (χ : DirichletCharacter ℂ q) (k : ZMod (q * d)) :
    ZMod.dft (scaledCharacter χ d : ZMod (q * d) → ℂ) k =
      ZMod.dft χ (ZMod.castHom (dvd_mul_right q d) (ZMod q) k) := by
  classical
  let e : Fin q × Fin d ≃ ZMod (q * d) :=
    finProdFinEquiv.trans (ZMod.finEquiv (q * d)).toEquiv
  rw [ZMod.dft_apply]
  calc
    (∑ a : ZMod (q * d),
        ZMod.stdAddChar (-(a * k)) * scaledCharacter χ d a) =
        ∑ x : Fin q × Fin d,
          ZMod.stdAddChar (-((e x) * k)) * scaledCharacter χ d (e x) := by
      exact (Fintype.sum_equiv e _ _ (fun _ ↦ rfl)).symm
    _ = ∑ x : Fin q × Fin d,
        if d ∣ x.2.val + d * x.1.val then
          ZMod.stdAddChar
              (-(((d * ((x.2.val + d * x.1.val) / d) : ℕ) : ZMod (q * d)) * k)) *
            χ ((((x.2.val + d * x.1.val) / d : ℕ) : ZMod q))
        else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      have heval : (e x).val = x.2.val + d * x.1.val := by
        change (ZMod.finEquiv (q * d) (finProdFinEquiv x)).val = _
        rw [val_finEquiv]
        rfl
      simp only [scaledCharacter, heval]
      split_ifs with hx
      · have hnat : d * ((x.2.val + d * x.1.val) / d) =
            x.2.val + d * x.1.val := Nat.mul_div_cancel' hx
        have he : e x =
            ((d * ((x.2.val + d * x.1.val) / d) : ℕ) : ZMod (q * d)) := by
          rw [← (e x).natCast_zmod_val, heval, hnat]
        rw [he]
      · simp
    _ = ∑ b : Fin q,
        ZMod.stdAddChar (-(((d * b.val : ℕ) : ZMod (q * d)) * k)) *
          χ ((b.val : ℕ) : ZMod q) := by
      exact sum_fin_if_dvd_add_mul
        (fun n ↦ ZMod.stdAddChar (-(((d * n : ℕ) : ZMod (q * d)) * k)) *
          χ ((n : ℕ) : ZMod q))
    _ = ∑ b : Fin q,
        ZMod.stdAddChar
            (-(((b.val : ℕ) : ZMod q) *
              ZMod.castHom (dvd_mul_right q d) (ZMod q) k)) *
          χ ((b.val : ℕ) : ZMod q) := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [stdAddChar_scaled_castHom]
    _ = ∑ a : ZMod q,
        ZMod.stdAddChar
            (-(a * ZMod.castHom (dvd_mul_right q d) (ZMod q) k)) * χ a := by
      apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
      intro b
      change ZMod.stdAddChar
          (-(((b.val : ℕ) : ZMod q) *
            ZMod.castHom (dvd_mul_right q d) (ZMod q) k)) * χ ((b.val : ℕ) : ZMod q) =
        ZMod.stdAddChar
          (-(ZMod.finEquiv q b * ZMod.castHom (dvd_mul_right q d) (ZMod q) k)) *
            χ (ZMod.finEquiv q b)
      rw [finEquiv_apply_eq_natCast]
    _ = ZMod.dft χ (ZMod.castHom (dvd_mul_right q d) (ZMod q) k) := by
      rw [ZMod.dft_apply]
      simp only [smul_eq_mul]

/-- Fourier transform of a cyclic translate. -/
theorem dft_comp_add {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (h k : ZMod N) :
    ZMod.dft (fun a ↦ F (a + h)) k =
      ZMod.stdAddChar (h * k) * ZMod.dft F k := by
  classical
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  simp only [smul_eq_mul]
  calc
    (∑ a : ZMod N, ZMod.stdAddChar (-(a * k)) * F (a + h)) =
        ∑ x : ZMod N, ZMod.stdAddChar (-((x - h) * k)) * F x := by
      apply Fintype.sum_equiv (Equiv.addRight h)
      intro a
      simp
    _ = ∑ x : ZMod N,
        ZMod.stdAddChar (h * k) *
          (ZMod.stdAddChar (-(x * k)) * F x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      have hc : ZMod.stdAddChar (-((x - h) * k)) =
          ZMod.stdAddChar (h * k) * ZMod.stdAddChar (-(x * k)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      rw [hc]
      ring

/-- Pull a function on `ZMod M` back to the cyclic cover `ZMod (t * M)`. -/
noncomputable def periodicLift {M t : ℕ} [NeZero M] [NeZero t]
    (F : ZMod M → ℂ) (a : ZMod (t * M)) : ℂ :=
  F (ZMod.castHom (dvd_mul_left M t) (ZMod M) a)

theorem periodicLift_add_period {M t : ℕ} [NeZero M] [NeZero t]
    (F : ZMod M → ℂ) (a : ZMod (t * M)) :
    periodicLift F (a + (M : ZMod (t * M))) = periodicLift F a := by
  unfold periodicLift
  rw [map_add, map_natCast]
  have hM : (M : ZMod M) = 0 :=
    (ZMod.natCast_eq_zero_iff M M).mpr (dvd_refl M)
  rw [hM, add_zero]

/-- A nonzero Fourier coefficient of a function lifted through a cyclic cover
must be at a frequency divisible by the covering degree. -/
theorem dvd_val_of_dft_periodicLift_ne_zero {M t : ℕ} [NeZero M] [NeZero t]
    (F : ZMod M → ℂ) (k : ZMod (t * M))
    (hk : ZMod.dft (periodicLift F : ZMod (t * M) → ℂ) k ≠ 0) :
    t ∣ k.val := by
  have hfun : (fun a : ZMod (t * M) ↦
      periodicLift F (a + (M : ZMod (t * M)))) = periodicLift F := by
    funext a
    exact periodicLift_add_period F a
  have hdft := congrArg (fun G : ZMod (t * M) → ℂ ↦ ZMod.dft G k) hfun
  rw [dft_comp_add] at hdft
  have hpsi : ZMod.stdAddChar ((M : ZMod (t * M)) * k) = 1 := by
    apply mul_right_cancel₀ hk
    simpa only [one_mul] using hdft
  have hz : (M : ZMod (t * M)) * k = 0 := by
    apply ZMod.injective_stdAddChar
    simpa using hpsi
  have hz' : ((M * k.val : ℕ) : ZMod (t * M)) = 0 := by
    rw [Nat.cast_mul, k.natCast_zmod_val]
    exact hz
  have hdiv : t * M ∣ M * k.val :=
    (ZMod.natCast_eq_zero_iff (M * k.val) (t * M)).mp hz'
  have hdiv' : M * t ∣ M * k.val := by
    simpa only [mul_comm t M] using hdiv
  exact Nat.dvd_of_mul_dvd_mul_left (NeZero.pos M) hdiv'

/-- Compatibility of standard additive characters when both a natural
frequency and the ambient modulus are enlarged on the left by `t`. -/
theorem stdAddChar_mul_left_scaled {M t : ℕ} [NeZero M] [NeZero t]
    (b s : ℕ) :
    ZMod.stdAddChar (-(((b * (t * s) : ℕ) : ZMod (t * M)))) =
      ZMod.stdAddChar (-(((b * s : ℕ) : ZMod M))) := by
  rw [show -(((b * (t * s) : ℕ) : ZMod (t * M))) =
      ((-((b * (t * s) : ℕ) : ℤ) : ℤ) : ZMod (t * M)) by
        push_cast
        ring,
    show -(((b * s : ℕ) : ZMod M)) =
      ((-((b * s : ℕ) : ℤ) : ℤ) : ZMod M) by
        push_cast
        ring]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp [NeZero.ne M, NeZero.ne t]

theorem stdAddChar_periodicLift_kernel {M t : ℕ} [NeZero M] [NeZero t]
    (b r : ℕ) (k : ZMod (t * M)) (hk : t ∣ k.val) :
    ZMod.stdAddChar
        (-(((b + M * r : ℕ) : ZMod (t * M)) * k)) =
    ZMod.stdAddChar
        (-(((b * (k.val / t) : ℕ) : ZMod M))) := by
  let s := k.val / t
  have hval : t * s = k.val := Nat.mul_div_cancel' hk
  have hkcast : k = ((t * s : ℕ) : ZMod (t * M)) := by
    rw [hval, k.natCast_zmod_val]
  have harg :
      (((b + M * r : ℕ) : ZMod (t * M)) * k) =
        ((b * (t * s) : ℕ) : ZMod (t * M)) := by
    rw [hkcast]
    push_cast
    have hzero : ((t * M : ℕ) : ZMod (t * M)) = 0 := by simp
    have hzero' : (t : ZMod (t * M)) * (M : ZMod (t * M)) = 0 := by
      simpa only [Nat.cast_mul] using hzero
    rw [show ((b : ZMod (t * M)) + (M : ZMod (t * M)) * (r : ZMod (t * M))) *
          ((t : ZMod (t * M)) * (s : ZMod (t * M))) =
        (b : ZMod (t * M)) * ((t : ZMod (t * M)) * (s : ZMod (t * M))) +
          ((t : ZMod (t * M)) * (M : ZMod (t * M))) *
            ((r : ZMod (t * M)) * (s : ZMod (t * M))) by ring,
      hzero', zero_mul, add_zero]
  rw [harg]
  exact stdAddChar_mul_left_scaled b s

/-- Exact Fourier coefficient of a periodic lift.  At a frequency divisible
by the covering degree, the coefficient is the covering degree times the
corresponding coefficient downstairs. -/
theorem dft_periodicLift_of_dvd {M t : ℕ} [NeZero M] [NeZero t]
    (F : ZMod M → ℂ) (k : ZMod (t * M)) (hk : t ∣ k.val) :
    ZMod.dft (periodicLift F : ZMod (t * M) → ℂ) k =
      (t : ℂ) * ZMod.dft F ((k.val / t : ℕ) : ZMod M) := by
  classical
  let e : Fin t × Fin M ≃ ZMod (t * M) :=
    finProdFinEquiv.trans (ZMod.finEquiv (t * M)).toEquiv
  rw [ZMod.dft_apply]
  calc
    (∑ a : ZMod (t * M),
        ZMod.stdAddChar (-(a * k)) * periodicLift F a) =
        ∑ x : Fin t × Fin M,
          ZMod.stdAddChar (-((e x) * k)) * periodicLift F (e x) := by
      exact (Fintype.sum_equiv e _ _ (fun _ ↦ rfl)).symm
    _ = ∑ x : Fin t × Fin M,
        ZMod.stdAddChar
            (-(((x.2.val * (k.val / t) : ℕ) : ZMod M))) *
          F ((x.2.val : ℕ) : ZMod M) := by
      apply Finset.sum_congr rfl
      intro x _hx
      have heval : (e x).val = x.2.val + M * x.1.val := by
        change (ZMod.finEquiv (t * M) (finProdFinEquiv x)).val = _
        rw [val_finEquiv]
        rfl
      have he : e x =
          ((x.2.val + M * x.1.val : ℕ) : ZMod (t * M)) := by
        rw [← (e x).natCast_zmod_val, heval]
      have hlift : periodicLift F (e x) = F ((x.2.val : ℕ) : ZMod M) := by
        unfold periodicLift
        congr 1
        rw [ZMod.castHom_apply, ZMod.cast_eq_val, heval]
        push_cast
        have hM : (M : ZMod M) = 0 := by simp
        rw [hM, zero_mul, add_zero]
      rw [hlift, he, stdAddChar_periodicLift_kernel x.2.val x.1.val k hk]
    _ = ∑ r : Fin t, ∑ b : Fin M,
        ZMod.stdAddChar
            (-(((b.val : ℕ) : ZMod M) *
              ((k.val / t : ℕ) : ZMod M))) *
          F ((b.val : ℕ) : ZMod M) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _hr
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Nat.cast_mul]
    _ = (t : ℂ) * ZMod.dft F ((k.val / t : ℕ) : ZMod M) := by
      have hbase :
          (∑ b : Fin M,
              ZMod.stdAddChar
                  (-(((b.val : ℕ) : ZMod M) *
                    ((k.val / t : ℕ) : ZMod M))) *
                F ((b.val : ℕ) : ZMod M)) =
            ZMod.dft F ((k.val / t : ℕ) : ZMod M) := by
        rw [ZMod.dft_apply]
        simp only [smul_eq_mul]
        apply Fintype.sum_equiv (ZMod.finEquiv M).toEquiv
        intro b
        change
          ZMod.stdAddChar
                (-(((b.val : ℕ) : ZMod M) * ((k.val / t : ℕ) : ZMod M))) *
              F ((b.val : ℕ) : ZMod M) =
            ZMod.stdAddChar
                (-(ZMod.finEquiv M b * ((k.val / t : ℕ) : ZMod M))) *
              F (ZMod.finEquiv M b)
        rw [finEquiv_apply_eq_natCast]
      simp_rw [hbase]
      simp

/-- A scaled character on a common cyclic multiple is exactly the periodic
lift of the same scaled character on its natural modulus. -/
theorem scaledCharacter_eq_periodicLift {q d t : ℕ}
    [NeZero q] [NeZero d] [NeZero t] (χ : DirichletCharacter ℂ q)
    (a : ZMod (t * (q * d))) :
    scaledCharacter χ d a =
      periodicLift (scaledCharacter χ d : ZMod (q * d) → ℂ) a := by
  let b : ZMod (q * d) :=
    ZMod.castHom (dvd_mul_left (q * d) t) (ZMod (q * d)) a
  have hbval : b.val = a.val % (q * d) := by
    simp only [b, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  have hmod : b.val ≡ a.val [MOD q * d] := by
    rw [hbval]
    exact Nat.mod_modEq _ _
  have hdvd : d ∣ b.val ↔ d ∣ a.val :=
    hmod.dvd_iff (dvd_mul_left d q)
  unfold periodicLift
  change scaledCharacter χ d a = scaledCharacter χ d b
  simp only [scaledCharacter]
  by_cases ha : d ∣ a.val
  · have hb : d ∣ b.val := hdvd.mpr ha
    simp only [ha, hb, ↓reduceDIte]
    have hmul : d * (b.val / d) ≡ d * (a.val / d) [MOD q * d] := by
      simpa only [Nat.mul_div_cancel' hb, Nat.mul_div_cancel' ha] using hmod
    have hcancel := hmul.cancel_left_div_gcd (mul_pos (NeZero.pos q) (NeZero.pos d))
    have hgcd : Nat.gcd (q * d) d = d :=
      Nat.gcd_eq_right_iff_dvd.mpr (dvd_mul_left d q)
    have hquot : b.val / d ≡ a.val / d [MOD q] := by
      rw [hgcd] at hcancel
      have hqd : q * d / d = q := by
        rw [Nat.mul_comm, Nat.mul_div_right q (NeZero.pos d)]
      rw [hqd] at hcancel
      exact hcancel
    exact congrArg χ ((ZMod.natCast_eq_natCast_iff _ _ q).mpr hquot).symm
  · have hb : ¬d ∣ b.val := fun h ↦ ha (hdvd.mp h)
    simp only [ha, hb, ↓reduceDIte]
/-- A nonzero Fourier coefficient of a scaled primitive character on `q * d`
reduces to a unit frequency modulo `q`. -/
theorem isUnit_castHom_of_dft_scaledCharacter_ne_zero {q d : ℕ}
    [NeZero q] [NeZero d] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (k : ZMod (q * d))
    (hk : ZMod.dft (scaledCharacter χ d : ZMod (q * d) → ℂ) k ≠ 0) :
    IsUnit (ZMod.castHom (dvd_mul_right q d) (ZMod q) k) := by
  rw [dft_scaledCharacter_mul] at hk
  rw [hχ.fourierTransform_eq_inv_mul_gaussSum] at hk
  have hval : χ⁻¹ (-ZMod.castHom (dvd_mul_right q d) (ZMod q) k) ≠ 0 :=
    (mul_ne_zero_iff.mp hk).1
  have hu : IsUnit (-ZMod.castHom (dvd_mul_right q d) (ZMod q) k) :=
    MulChar.apply_ne_zero_iff.mp hval
  simpa only [neg_neg] using hu.neg

/-- Two functions have disjoint Fourier support if at every frequency at least
one of their discrete Fourier transforms vanishes. -/
def DisjointFourierSupport {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) : Prop :=
  ∀ k, ZMod.dft f k = 0 ∨ ZMod.dft g k = 0

/-- `f` has Fourier support contained in `s`.  Stating support containment via
nonvanishing avoids introducing a decidable finite-support object. -/
def FourierSupportedOn {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (s : Set (ZMod N)) : Prop :=
  ∀ ⦃k⦄, ZMod.dft f k ≠ 0 → k ∈ s

/-- On the natural modulus `q * d`, a scaled primitive character is supported
only at frequencies whose reduction modulo `q` is a unit. -/
theorem scaledCharacter_fourierSupportedOn_units {q d : ℕ} [NeZero q] [NeZero d]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    FourierSupportedOn (scaledCharacter χ d : ZMod (q * d) → ℂ)
      {k | IsUnit (ZMod.castHom (dvd_mul_right q d) (ZMod q) k)} := by
  intro k hk
  exact isUnit_castHom_of_dft_scaledCharacter_ne_zero hχ k hk

/-- The `t`-th Fourier layer: frequencies divisible by `t` for which the
quotient remains a unit modulo `q`. -/
def SmoothFrequencyLayer (q t N : ℕ) : Set (ZMod N) :=
  {k | t ∣ k.val ∧ IsUnit ((k.val / t : ℕ) : ZMod q)}

/-- The explicit Fourier-support set of a scaled primitive character after
putting its natural modulus on a cyclic cover of degree `t`. -/
def ScaledCharacterFrequencySet (q d t : ℕ) : Set (ZMod (t * (q * d))) :=
  SmoothFrequencyLayer q t (t * (q * d))

/-- Actual common-modulus Fourier support theorem for scaled primitive
characters.  Frequencies are exactly constrained to the `t`-divisible layer,
and after removing that layer their reduction modulo `q` must be a unit. -/
theorem scaledCharacter_fourierSupportedOn_common {q d t : ℕ}
    [NeZero q] [NeZero d] [NeZero t]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    FourierSupportedOn
      (scaledCharacter χ d : ZMod (t * (q * d)) → ℂ)
      (ScaledCharacterFrequencySet q d t) := by
  intro k hk
  have heq :
      (scaledCharacter χ d : ZMod (t * (q * d)) → ℂ) =
        periodicLift (scaledCharacter χ d : ZMod (q * d) → ℂ) := by
    funext a
    exact scaledCharacter_eq_periodicLift χ a
  rw [heq] at hk
  have ht : t ∣ k.val :=
    dvd_val_of_dft_periodicLift_ne_zero
      (scaledCharacter χ d : ZMod (q * d) → ℂ) k hk
  have hbase :
      ZMod.dft (scaledCharacter χ d : ZMod (q * d) → ℂ)
          ((k.val / t : ℕ) : ZMod (q * d)) ≠ 0 := by
    rw [dft_periodicLift_of_dvd _ k ht] at hk
    exact (mul_ne_zero_iff.mp hk).2
  have hu := isUnit_castHom_of_dft_scaledCharacter_ne_zero hχ
    ((k.val / t : ℕ) : ZMod (q * d)) hbase
  refine ⟨ht, ?_⟩
  simpa only [map_natCast] using hu

/-- Version of the common-modulus support theorem with an independently named
ambient modulus. -/
theorem scaledCharacter_fourierSupportedOn_of_eq {q d t N : ℕ}
    [NeZero q] [NeZero d] [NeZero t] [NeZero N]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hN : N = t * (q * d)) :
    FourierSupportedOn (scaledCharacter χ d : ZMod N → ℂ)
      (SmoothFrequencyLayer q t N) := by
  subst N
  exact scaledCharacter_fourierSupportedOn_common hχ

/-- Two Fourier layers are disjoint when their scales differ by a positive
power of `q` (the statement records one factor of `q` explicitly). -/
theorem smoothFrequencyLayer_disjoint_of_eq_mul {q N t₁ t₂ c : ℕ}
    [NeZero q] [NeZero N] [NeZero t₂] (hq : 1 < q)
    (ht : t₁ = q * c * t₂) :
    Disjoint (SmoothFrequencyLayer q t₁ N)
      (SmoothFrequencyLayer q t₂ N) := by
  letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr (Nat.ne_of_gt hq)
  rw [Set.disjoint_left]
  intro k hk₁ hk₂
  rcases hk₁.1 with ⟨z, hz⟩
  have hfactor : k.val = t₂ * (q * (c * z)) := by
    rw [hz, ht]
    ring
  have hquot : k.val / t₂ = q * (c * z) := by
    rw [hfactor, Nat.mul_div_right _ (NeZero.pos t₂)]
  have hzero : ((k.val / t₂ : ℕ) : ZMod q) = 0 := by
    rw [hquot, Nat.cast_mul]
    simp
  exact not_isUnit_zero (hzero ▸ hk₂.2)

/-- Explicit disjointness for distinct `q`-power layers, with the gap between
the exponents displayed as `c + 1`. -/
theorem smoothFrequencyLayer_disjoint_pow_gap {q N b c : ℕ}
    [NeZero q] [NeZero N] (hq : 1 < q) :
    Disjoint (SmoothFrequencyLayer q (q ^ (b + c + 1)) N)
      (SmoothFrequencyLayer q (q ^ b) N) := by
  haveI : NeZero (q ^ b) := ⟨pow_ne_zero _ (NeZero.ne q)⟩
  apply smoothFrequencyLayer_disjoint_of_eq_mul hq
  rw [show b + c + 1 = 1 + c + b by omega, pow_add, pow_add, pow_one]

theorem smoothFrequencyLayer_disjoint_pow_of_ne {q N i j : ℕ}
    [NeZero q] [NeZero N] (hq : 1 < q) (hij : i ≠ j) :
    Disjoint (SmoothFrequencyLayer q (q ^ i) N)
      (SmoothFrequencyLayer q (q ^ j) N) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · rcases Nat.exists_eq_add_of_lt hij with ⟨c, rfl⟩
    exact (smoothFrequencyLayer_disjoint_pow_gap (q := q) (N := N)
      (b := i) (c := c) hq).symm
  · rcases Nat.exists_eq_add_of_lt hji with ⟨c, rfl⟩
    exact smoothFrequencyLayer_disjoint_pow_gap (q := q) (N := N)
      (b := j) (c := c) hq

/-- Disjointness for arbitrary `q`-smooth scales.  The scale `dᵢ` is only
required to divide one common power of `q`; no ratio between `d₁` and `d₂`
need be integral.  This includes, for example, `q = 6`, `d₁ = 2`, `d₂ = 3`.
-/
theorem smoothFrequencyLayer_disjoint_of_smooth_complements
    {q N K d₁ d₂ t₁ t₂ : ℕ}
    [NeZero q] [NeZero N] [NeZero t₁] [NeZero t₂]
    (hN₁ : N = t₁ * (q * d₁)) (hN₂ : N = t₂ * (q * d₂))
    (hd₁ : d₁ ∣ q ^ K) (hd₂ : d₂ ∣ q ^ K) (hne : d₁ ≠ d₂) :
    Disjoint (SmoothFrequencyLayer q t₁ N)
      (SmoothFrequencyLayer q t₂ N) := by
  rw [Set.disjoint_left]
  intro k hk₁ hk₂
  let s₁ := k.val / t₁
  let s₂ := k.val / t₂
  have hfreq : t₁ * s₁ = t₂ * s₂ := by
    rw [show t₁ * s₁ = k.val by
        exact Nat.mul_div_cancel' hk₁.1,
      show t₂ * s₂ = k.val by
        exact Nat.mul_div_cancel' hk₂.1]
  have htd : t₁ * d₁ = t₂ * d₂ := by
    have hqmul : q * (t₁ * d₁) = q * (t₂ * d₂) := by
      calc
        q * (t₁ * d₁) = t₁ * (q * d₁) := by ring
        _ = N := hN₁.symm
        _ = t₂ * (q * d₂) := hN₂
        _ = q * (t₂ * d₂) := by ring
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos q) hqmul
  have hcross : s₁ * d₂ = s₂ * d₁ := by
    apply Nat.eq_of_mul_eq_mul_left (NeZero.pos t₂)
    calc
      t₂ * (s₁ * d₂) = (t₂ * d₂) * s₁ := by ring
      _ = (t₁ * d₁) * s₁ := by rw [← htd]
      _ = (t₁ * s₁) * d₁ := by ring
      _ = (t₂ * s₂) * d₁ := by rw [hfreq]
      _ = t₂ * (s₂ * d₁) := by ring
  have hs₁q : s₁.Coprime q :=
    (ZMod.isUnit_iff_coprime s₁ q).mp hk₁.2
  have hs₂q : s₂.Coprime q :=
    (ZMod.isUnit_iff_coprime s₂ q).mp hk₂.2
  have hs₁d₁ : s₁.Coprime d₁ :=
    (hs₁q.pow_right K).of_dvd_right hd₁
  have hs₂d₂ : s₂.Coprime d₂ :=
    (hs₂q.pow_right K).of_dvd_right hd₂
  have hd₁d₂ : d₁ ∣ d₂ := by
    apply hs₁d₁.symm.dvd_of_dvd_mul_left
    exact ⟨s₂, by simpa only [mul_comm] using hcross⟩
  have hd₂d₁ : d₂ ∣ d₁ := by
    apply hs₂d₂.symm.dvd_of_dvd_mul_left
    exact ⟨s₁, by simpa only [mul_comm] using hcross.symm⟩
  exact hne (Nat.dvd_antisymm hd₁d₂ hd₂d₁)

theorem qpow_separated_of_ne {q i j : ℕ} (hij : i ≠ j) :
    ∃ c : ℕ, q ^ i = q * c * q ^ j ∨ q ^ j = q * c * q ^ i := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · rcases Nat.exists_eq_add_of_lt hij with ⟨c, rfl⟩
    refine ⟨q ^ c, Or.inr ?_⟩
    rw [show i + c + 1 = 1 + c + i by omega, pow_add, pow_add, pow_one]
  · rcases Nat.exists_eq_add_of_lt hji with ⟨c, rfl⟩
    refine ⟨q ^ c, Or.inl ?_⟩
    rw [show j + c + 1 = 1 + c + j by omega, pow_add, pow_add, pow_one]

/-- Fourier transform commutes with a finite pointwise sum. -/
theorem dft_finset_sum {N : ℕ} [NeZero N] {ι : Type*}
    (s : Finset ι) (F : ι → ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun a ↦ ∑ i ∈ s, F i a) k =
      ∑ i ∈ s, ZMod.dft (F i) k := by
  classical
  simp only [ZMod.dft_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem dft_const_mul {N : ℕ} [NeZero N]
    (c : ℂ) (F : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun a ↦ c * F a) k = c * ZMod.dft F k := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem fourierSupportedOn_const_mul {N : ℕ} [NeZero N]
    {F : ZMod N → ℂ} {u : Set (ZMod N)}
    (hF : FourierSupportedOn F u) (c : ℂ) :
    FourierSupportedOn (fun a ↦ c * F a) u := by
  intro k hk
  rw [dft_const_mul] at hk
  exact hF (mul_ne_zero_iff.mp hk).2

theorem normSq_const_mul_of_norm_eq_one (c z : ℂ) (hc : ‖c‖ = 1) :
    Complex.normSq (c * z) = Complex.normSq z := by
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, hc, one_pow, one_mul]

theorem fourierSupportedOn_finset_sum {N : ℕ} [NeZero N]
    {ι : Type*} (s : Finset ι) (F : ι → ZMod N → ℂ)
    (u : Set (ZMod N))
    (hF : ∀ i ∈ s, FourierSupportedOn (F i) u) :
    FourierSupportedOn (fun a ↦ ∑ i ∈ s, F i a) u := by
  classical
  intro k hk
  by_contra hku
  apply hk
  rw [dft_finset_sum]
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hne
  exact hku (hF i hi hne)

theorem fourierSupportedOn_comp_add {N : ℕ} [NeZero N]
    {F : ZMod N → ℂ} {u : Set (ZMod N)} (hF : FourierSupportedOn F u)
    (h : ZMod N) :
    FourierSupportedOn (fun a ↦ F (a + h)) u := by
  intro k hk
  rw [dft_comp_add] at hk
  exact hF (mul_ne_zero_iff.mp hk).2

/-- A complete block of short translates of a scaled character. -/
noncomputable def scaledCharacterBlock {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (d : ℕ) (a : ZMod N) : ℂ :=
  ∑ m ∈ Finset.range d, scaledShiftedCharacter χ d m a

/-- A prefix of the translates belonging to one scaled-character layer. -/
noncomputable def scaledCharacterPrefix {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (d L : ℕ) (a : ZMod N) : ℂ :=
  ∑ m ∈ Finset.range L, scaledShiftedCharacter χ d m a

theorem scaledCharacterPrefix_add {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (d L : ℕ) (a : ZMod N) :
    scaledCharacterPrefix χ d (L + d) a =
      scaledCharacterPrefix χ d L a +
        scaledCharacterBlock χ d (a + (L : ZMod N)) := by
  unfold scaledCharacterPrefix scaledCharacterBlock
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro m _hm
  unfold scaledShiftedCharacter
  congr 1
  push_cast
  ring

theorem scaledCharacterPrefix_sub {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (d L : ℕ) (a : ZMod N) :
    scaledCharacterPrefix χ d (L + d) a - scaledCharacterPrefix χ d L a =
      scaledCharacterBlock χ d (a + (L : ZMod N)) := by
  rw [scaledCharacterPrefix_add]
  ring

theorem scaledCharacterPrefix_fourierSupportedOn_of_eq {q d t N L : ℕ}
    [NeZero q] [NeZero d] [NeZero t] [NeZero N]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hN : N = t * (q * d)) :
    FourierSupportedOn (scaledCharacterPrefix χ d L : ZMod N → ℂ)
      (SmoothFrequencyLayer q t N) := by
  unfold scaledCharacterPrefix
  apply fourierSupportedOn_finset_sum
  intro m _hm
  unfold scaledShiftedCharacter
  exact fourierSupportedOn_comp_add
    (scaledCharacter_fourierSupportedOn_of_eq hχ hN) (m : ZMod N)

theorem norm_scaledCharacter_le_one {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (d : ℕ) (a : ZMod N) :
    ‖scaledCharacter χ d a‖ ≤ 1 := by
  unfold scaledCharacter
  split
  · exact χ.norm_le_one _
  · simp

theorem norm_scaledCharacterPrefix_le {q N : ℕ} [NeZero q] [NeZero N]
    (χ : DirichletCharacter ℂ q) (d L : ℕ) (a : ZMod N) :
    ‖scaledCharacterPrefix χ d L a‖ ≤ L := by
  unfold scaledCharacterPrefix
  calc
    ‖∑ m ∈ Finset.range L, scaledShiftedCharacter χ d m a‖ ≤
        ∑ m ∈ Finset.range L, ‖scaledShiftedCharacter χ d m a‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range L, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m _hm
      unfold scaledShiftedCharacter
      exact norm_scaledCharacter_le_one χ d _
    _ = L := by simp

/-- Trivial square bound for a sum of `s.card` prefixes of length `L`. -/
theorem normSq_sum_scaledCharacterPrefix_le {q N : ℕ}
    [NeZero q] [NeZero N] (s : Finset ℕ)
    (χ : DirichletCharacter ℂ q) (d : ℕ → ℕ) (L : ℕ) (a : ZMod N) :
    Complex.normSq (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) ≤
      (((s.card * L : ℕ) : ℝ) ^ 2) := by
  rw [Complex.normSq_eq_norm_sq]
  have hnorm :
      ‖∑ i ∈ s, scaledCharacterPrefix χ (d i) L a‖ ≤
        ((s.card * L : ℕ) : ℝ) := by
    calc
      ‖∑ i ∈ s, scaledCharacterPrefix χ (d i) L a‖ ≤
          ∑ i ∈ s, ‖scaledCharacterPrefix χ (d i) L a‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, (L : ℝ) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact norm_scaledCharacterPrefix_le χ (d i) L a
      _ = ((s.card * L : ℕ) : ℝ) := by
        simp [nsmul_eq_mul]
  nlinarith [norm_nonneg (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a)]

theorem normSq_sum_weighted_scaledCharacterPrefix_le {q N : ℕ}
    [NeZero q] [NeZero N] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (χ : DirichletCharacter ℂ q) (d : ι → ℕ)
    (c : ι → ℂ) (hc : ∀ i ∈ s, ‖c i‖ = 1)
    (L : ℕ) (a : ZMod N) :
    Complex.normSq
        (∑ i ∈ s, c i * scaledCharacterPrefix χ (d i) L a) ≤
      (((s.card * L : ℕ) : ℝ) ^ 2) := by
  rw [Complex.normSq_eq_norm_sq]
  have hnorm :
      ‖∑ i ∈ s, c i * scaledCharacterPrefix χ (d i) L a‖ ≤
        ((s.card * L : ℕ) : ℝ) := by
    calc
      ‖∑ i ∈ s, c i * scaledCharacterPrefix χ (d i) L a‖ ≤
          ∑ i ∈ s, ‖c i * scaledCharacterPrefix χ (d i) L a‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, (L : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, hc i hi, one_mul]
        exact norm_scaledCharacterPrefix_le χ (d i) L a
      _ = ((s.card * L : ℕ) : ℝ) := by
        simp [nsmul_eq_mul]
  nlinarith [norm_nonneg
    (∑ i ∈ s, c i * scaledCharacterPrefix χ (d i) L a)]

theorem normSq_sub_le_two_mul_add (x y : ℂ) :
    Complex.normSq (x - y) ≤
      2 * (Complex.normSq x + Complex.normSq y) := by
  simp only [Complex.normSq_eq_norm_sq]
  have htri : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  nlinarith [norm_nonneg (x - y), norm_nonneg x, norm_nonneg y,
    sq_nonneg (‖x‖ - ‖y‖)]

/-- Comparing a block with two prefixes, after summing over the cyclic
ambient variable. -/
theorem scaledCharacterBlock_energy_le_prefix_pair {q N : ℕ}
    [NeZero q] [NeZero N] (χ : DirichletCharacter ℂ q) (d L : ℕ) :
    (∑ a : ZMod N, Complex.normSq (scaledCharacterBlock χ d a)) ≤
      2 * ((∑ a : ZMod N,
          Complex.normSq (scaledCharacterPrefix χ d (L + d) a)) +
        ∑ a : ZMod N, Complex.normSq (scaledCharacterPrefix χ d L a)) := by
  have hshift :
      (∑ a : ZMod N,
          Complex.normSq (scaledCharacterBlock χ d (a + (L : ZMod N)))) =
        ∑ a : ZMod N, Complex.normSq (scaledCharacterBlock χ d a) := by
    apply Fintype.sum_equiv (Equiv.addRight (L : ZMod N))
    intro a
    rfl
  rw [← hshift]
  calc
    (∑ a : ZMod N,
        Complex.normSq (scaledCharacterBlock χ d (a + (L : ZMod N)))) =
        ∑ a : ZMod N,
          Complex.normSq
            (scaledCharacterPrefix χ d (L + d) a -
              scaledCharacterPrefix χ d L a) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [scaledCharacterPrefix_sub]
    _ ≤ ∑ a : ZMod N,
        2 * (Complex.normSq (scaledCharacterPrefix χ d (L + d) a) +
          Complex.normSq (scaledCharacterPrefix χ d L a)) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact normSq_sub_le_two_mul_add _ _
    _ = 2 * ((∑ a : ZMod N,
          Complex.normSq (scaledCharacterPrefix χ d (L + d) a)) +
        ∑ a : ZMod N, Complex.normSq (scaledCharacterPrefix χ d L a)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]

/-- Prefix-difference averaging on the medium interval `(H,2H]`.  The
condition `2d ≤ H` leaves at least half of the interval after shifting by
`d`, giving the explicit constant eight. -/
theorem H_mul_block_energy_le_eight_mul_medium_prefix_energy {q N : ℕ}
    [NeZero q] [NeZero N] (χ : DirichletCharacter ℂ q)
    (d H : ℕ) (hdH : 2 * d ≤ H) :
    (H : ℝ) *
        (∑ a : ZMod N, Complex.normSq (scaledCharacterBlock χ d a)) ≤
      8 * ∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a : ZMod N,
          Complex.normSq (scaledCharacterPrefix χ d L a) := by
  classical
  let E : ℕ → ℝ := fun L ↦
    ∑ a : ZMod N, Complex.normSq (scaledCharacterPrefix χ d L a)
  let B : ℝ :=
    ∑ a : ZMod N, Complex.normSq (scaledCharacterBlock χ d a)
  let J : Finset ℕ := Finset.Ioc H (2 * H - d)
  let T : ℝ := ∑ L ∈ Finset.Ioc H (2 * H), E L
  have hnonnegE (L : ℕ) : 0 ≤ E L :=
    Finset.sum_nonneg fun a _ha ↦ Complex.normSq_nonneg _
  have hnonnegB : 0 ≤ B :=
    Finset.sum_nonneg fun a _ha ↦ Complex.normSq_nonneg _
  have hJsub : J ⊆ Finset.Ioc H (2 * H) := by
    intro L hL
    simp only [J, Finset.mem_Ioc] at hL ⊢
    omega
  have himageSub : J.image (fun L ↦ L + d) ⊆ Finset.Ioc H (2 * H) := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨L, hL, rfl⟩
    simp only [J, Finset.mem_Ioc] at hL ⊢
    omega
  have hbase : (∑ L ∈ J, E L) ≤ T := by
    dsimp only [T]
    exact Finset.sum_le_sum_of_subset_of_nonneg hJsub
      (fun L _hL _hnot ↦ hnonnegE L)
  have hshift : (∑ L ∈ J, E (L + d)) ≤ T := by
    have himage :
        (∑ u ∈ J.image (fun L ↦ L + d), E u) =
          ∑ L ∈ J, E (L + d) := by
      apply Finset.sum_image
      intro x _hx y _hy hxy
      exact Nat.add_right_cancel hxy
    rw [← himage]
    dsimp only [T]
    exact Finset.sum_le_sum_of_subset_of_nonneg himageSub
      (fun L _hL _hnot ↦ hnonnegE L)
  have hpairs : (J.card : ℝ) * B ≤
      2 * ((∑ L ∈ J, E (L + d)) + ∑ L ∈ J, E L) := by
    calc
      (J.card : ℝ) * B = ∑ _L ∈ J, B := by simp [nsmul_eq_mul]
      _ ≤ ∑ L ∈ J, 2 * (E (L + d) + E L) := by
        apply Finset.sum_le_sum
        intro L _hL
        exact scaledCharacterBlock_energy_le_prefix_pair χ d L
      _ = 2 * ((∑ L ∈ J, E (L + d)) + ∑ L ∈ J, E L) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hpairs' : (J.card : ℝ) * B ≤ 4 * T := by
    calc
      (J.card : ℝ) * B ≤
          2 * ((∑ L ∈ J, E (L + d)) + ∑ L ∈ J, E L) := hpairs
      _ ≤ 2 * (T + T) := by gcongr
      _ = 4 * T := by ring
  have hcard : J.card = H - d := by
    dsimp only [J]
    rw [Nat.card_Ioc]
    omega
  have hHcard : (H : ℝ) ≤ 2 * (J.card : ℝ) := by
    rw [hcard]
    exact_mod_cast (show H ≤ 2 * (H - d) by omega)
  change (H : ℝ) * B ≤ 8 * T
  calc
    (H : ℝ) * B ≤ (2 * (J.card : ℝ)) * B :=
      mul_le_mul_of_nonneg_right hHcard hnonnegB
    _ = 2 * ((J.card : ℝ) * B) := by ring
    _ ≤ 2 * (4 * T) := by gcongr
    _ = 8 * T := by ring

theorem scaledCharacterBlock_fourierSupportedOn_of_eq {q d t N : ℕ}
    [NeZero q] [NeZero d] [NeZero t] [NeZero N]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hN : N = t * (q * d)) :
    FourierSupportedOn (scaledCharacterBlock χ d : ZMod N → ℂ)
      (SmoothFrequencyLayer q t N) := by
  unfold scaledCharacterBlock
  apply fourierSupportedOn_finset_sum
  intro m _hm
  unfold scaledShiftedCharacter
  exact fourierSupportedOn_comp_add
    (scaledCharacter_fourierSupportedOn_of_eq hχ hN) (m : ZMod N)

/-- Total energy of a periodic lift is the covering degree times the energy
downstairs. -/
theorem periodicLift_sum_normSq {M t : ℕ} [NeZero M] [NeZero t]
    (F : ZMod M → ℂ) :
    (∑ a : ZMod (t * M), Complex.normSq (periodicLift F a)) =
      (t : ℝ) * ∑ b : ZMod M, Complex.normSq (F b) := by
  classical
  let e : Fin t × Fin M ≃ ZMod (t * M) :=
    finProdFinEquiv.trans (ZMod.finEquiv (t * M)).toEquiv
  calc
    (∑ a : ZMod (t * M), Complex.normSq (periodicLift F a)) =
        ∑ x : Fin t × Fin M, Complex.normSq (periodicLift F (e x)) := by
      exact (Fintype.sum_equiv e _ _ (fun _ ↦ rfl)).symm
    _ = ∑ x : Fin t × Fin M,
        Complex.normSq (F ((x.2.val : ℕ) : ZMod M)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      congr 1
      unfold periodicLift
      congr 1
      have heval : (e x).val = x.2.val + M * x.1.val := by
        change (ZMod.finEquiv (t * M) (finProdFinEquiv x)).val = _
        rw [val_finEquiv]
        rfl
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, heval]
      push_cast
      have hM : (M : ZMod M) = 0 := by simp
      rw [hM, zero_mul, add_zero]
    _ = ∑ r : Fin t, ∑ b : Fin M,
        Complex.normSq (F ((b.val : ℕ) : ZMod M)) := by
      rw [Fintype.sum_prod_type]
    _ = (t : ℝ) * ∑ b : Fin M,
        Complex.normSq (F ((b.val : ℕ) : ZMod M)) := by simp
    _ = (t : ℝ) * ∑ b : ZMod M, Complex.normSq (F b) := by
      congr 1
      apply Fintype.sum_equiv (ZMod.finEquiv M).toEquiv
      intro b
      change Complex.normSq (F ((b.val : ℕ) : ZMod M)) =
        Complex.normSq (F (ZMod.finEquiv M b))
      rw [finEquiv_apply_eq_natCast]

/-- Exact energy of a scaled character on an arbitrary common cyclic
multiple. -/
theorem scaledCharacter_sum_normSq_of_eq {q d t N : ℕ}
    [NeZero q] [NeZero d] [NeZero t] [NeZero N]
    (χ : DirichletCharacter ℂ q) (hN : N = t * (q * d)) :
    (∑ a : ZMod N, Complex.normSq (scaledCharacter χ d a)) =
      (t : ℝ) * (q.totient : ℝ) := by
  subst N
  simp_rw [scaledCharacter_eq_periodicLift χ]
  rw [periodicLift_sum_normSq, scaledCharacter_sum_normSq_mul]

/-- Exact energy of one BCC block on a common cyclic modulus. -/
theorem scaledCharacterBlock_energy_of_eq {q d t N : ℕ}
    [NeZero q] [NeZero d] [NeZero t] [NeZero N]
    (χ : DirichletCharacter ℂ q) (hN : N = t * (q * d)) :
    (∑ a : ZMod N, Complex.normSq (scaledCharacterBlock χ d a)) =
      (d : ℝ) * ((t : ℝ) * (q.totient : ℝ)) := by
  unfold scaledCharacterBlock
  rw [scaledShiftedCharacter_block_energy χ]
  · rw [scaledCharacter_sum_normSq_of_eq χ hN]
  · rw [hN]
    exact dvd_mul_of_dvd_right (dvd_mul_left d q) t

theorem disjointFourierSupport_of_supportedOn_disjoint {N : ℕ} [NeZero N]
    {f g : ZMod N → ℂ} {s t : Set (ZMod N)} (hst : Disjoint s t)
    (hf : FourierSupportedOn f s) (hg : FourierSupportedOn g t) :
    DisjointFourierSupport f g := by
  intro k
  by_cases hfk : ZMod.dft f k = 0
  · exact Or.inl hfk
  · right
    by_contra hgk
    exact Set.disjoint_left.mp hst (hf hfk) (hg hgk)

/-- Orthogonality of two rows of the unnormalised Fourier matrix on `ZMod N`. -/
theorem dft_kernel_orthogonality {N : ℕ} [NeZero N] (j l : ZMod N) :
    (∑ k : ZMod N,
        ZMod.stdAddChar (-(j * k)) *
          (starRingEnd ℂ) (ZMod.stdAddChar (-(l * k)))) =
      if j = l then (N : ℂ) else 0 := by
  classical
  have hstar (k : ZMod N) :
      (starRingEnd ℂ) (ZMod.stdAddChar (-(l * k))) = ZMod.stdAddChar (l * k) := by
    simpa only [starRingEnd_apply, neg_neg] using
      (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) (-(l * k))).symm
  simp_rw [hstar, ← AddChar.map_add_eq_mul]
  have hsum (t : ZMod N) :
      (∑ k : ZMod N, ZMod.stdAddChar (t * k)) =
        if t = 0 then (N : ℂ) else 0 := by
    split_ifs with ht
    · simp [ht]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ht)
  simp_rw [show ∀ k : ZMod N, -(j * k) + l * k = (l - j) * k by
      intro k
      ring]
  rw [hsum]
  simp only [sub_eq_zero]
  by_cases h : j = l
  · rw [if_pos h, if_pos h.symm]
  · have h' : l ≠ j := fun h' ↦ h h'.symm
    rw [if_neg h, if_neg h']

/-- Parseval's identity for the unnormalised discrete Fourier transform. -/
theorem dft_parseval {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    (∑ k : ZMod N, ZMod.dft f k * (starRingEnd ℂ) (ZMod.dft g k)) =
      (N : ℂ) * ∑ j : ZMod N, f j * (starRingEnd ℂ) (g j) := by
  classical
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul]
  simp_rw [Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_comm]
  have hfactor (j : ZMod N) :
      (∑ k : ZMod N,
          ZMod.stdAddChar (-(i * k)) * f i *
            ((starRingEnd ℂ) (ZMod.stdAddChar (-(j * k))) *
              (starRingEnd ℂ) (g j))) =
        (f i * (starRingEnd ℂ) (g j)) *
          ∑ k : ZMod N,
            ZMod.stdAddChar (-(i * k)) *
              (starRingEnd ℂ) (ZMod.stdAddChar (-(j * k))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  simp_rw [hfactor, dft_kernel_orthogonality]
  simp
  ring

/-- The exact off-diagonal cancellation supplied by disjoint Fourier support.
This is the frequency-side identity used after expanding the BCC second
moment. -/
theorem dft_product_sum_eq_zero_of_disjoint_support {N : ℕ} [NeZero N]
    {f g : ZMod N → ℂ} (hfg : DisjointFourierSupport f g) :
    ∑ k : ZMod N, ZMod.dft f k * (starRingEnd ℂ) (ZMod.dft g k) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _hk
  rcases hfg k with hk | hk
  · simp [hk]
  · simp [hk]

/-- Disjoint Fourier support implies exact orthogonality in the original cyclic
variable.  This is the spatial form of the BCC off-diagonal cancellation. -/
theorem sum_mul_star_eq_zero_of_disjointFourierSupport {N : ℕ} [NeZero N]
    {f g : ZMod N → ℂ} (hfg : DisjointFourierSupport f g) :
    ∑ a : ZMod N, f a * (starRingEnd ℂ) (g a) = 0 := by
  have hp := dft_parseval f g
  rw [dft_product_sum_eq_zero_of_disjoint_support hfg] at hp
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  exact (mul_eq_zero.mp hp.symm).resolve_left hN

theorem sum_mul_star_eq_zero_of_supportedOn_disjoint {N : ℕ} [NeZero N]
    {f g : ZMod N → ℂ} {s t : Set (ZMod N)} (hst : Disjoint s t)
    (hf : FourierSupportedOn f s) (hg : FourierSupportedOn g t) :
    ∑ a : ZMod N, f a * (starRingEnd ℂ) (g a) = 0 := by
  apply sum_mul_star_eq_zero_of_disjointFourierSupport
  exact disjointFourierSupport_of_supportedOn_disjoint hst hf hg

/-- A family version of the off-diagonal cancellation, convenient when the
scales are indexed by a finite set. -/
theorem dft_offDiagonal_sum_eq_zero {N : ℕ} [NeZero N]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ZMod N → ℂ)
    (hF : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → DisjointFourierSupport (F i) (F j)) :
    ∑ i ∈ s, ∑ j ∈ s.filter (fun j ↦ i ≠ j),
        ∑ k : ZMod N, ZMod.dft (F i) k * (starRingEnd ℂ) (ZMod.dft (F j) k) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  apply dft_product_sum_eq_zero_of_disjoint_support
  exact hF i hi j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2

/-- Spatial family version of the exact off-diagonal cancellation. -/
theorem offDiagonal_sum_mul_star_eq_zero {N : ℕ} [NeZero N]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ZMod N → ℂ)
    (hF : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → DisjointFourierSupport (F i) (F j)) :
    ∑ i ∈ s, ∑ j ∈ s.filter (fun j ↦ i ≠ j),
        ∑ a : ZMod N, F i a * (starRingEnd ℂ) (F j a) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  apply sum_mul_star_eq_zero_of_disjointFourierSupport
  exact hF i hi j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2

/-- Finite-dimensional Pythagoras for a family which is orthogonal after
summing over the ambient cyclic group. -/
theorem sum_normSq_finset_sum_of_orthogonal {N : ℕ} [NeZero N]
    {ι : Type*} (s : Finset ι) (F : ι → ZMod N → ℂ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∑ a : ZMod N, F i a * (starRingEnd ℂ) (F j a) = 0) :
    (∑ a : ZMod N, Complex.normSq (∑ i ∈ s, F i a)) =
      ∑ i ∈ s, ∑ a : ZMod N, Complex.normSq (F i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      let G : ZMod N → ℂ := fun a ↦ ∑ j ∈ s, F j a
      have ih' :
          (∑ a : ZMod N, Complex.normSq (G a)) =
            ∑ j ∈ s, ∑ a : ZMod N, Complex.normSq (F j a) := by
        apply ih
        intro j hj l hl hjl
        exact horth j (Finset.mem_insert_of_mem hj) l
          (Finset.mem_insert_of_mem hl) hjl
      have hcrossC :
          (∑ a : ZMod N, F i a * (starRingEnd ℂ) (G a)) = 0 := by
        simp only [G, map_sum, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro j hj
        exact horth i (Finset.mem_insert_self i s) j
          (Finset.mem_insert_of_mem hj) (fun hij ↦ hi (hij ▸ hj))
      have hcrossR :
          (∑ a : ZMod N, (F i a * (starRingEnd ℂ) (G a)).re) = 0 := by
        have hre := congrArg Complex.re hcrossC
        rw [Complex.re_sum] at hre
        simpa only [Complex.zero_re] using hre
      simp_rw [Finset.sum_insert hi]
      change (∑ a : ZMod N, Complex.normSq (F i a + G a)) = _
      simp_rw [Complex.normSq_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        hcrossR, mul_zero, add_zero, ih']

/-- Exact finitary endpoint of the generalized Borwein--Choi--Coons
construction.  Each scale contributes its full block energy and all
off-diagonal terms vanish because the corresponding `q`-smooth Fourier layers
are disjoint. -/
theorem generalized_bcc_energy {q N : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d t : ι → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i)) (ht : ∀ i ∈ s, NeZero (t i))
    (hN : ∀ i ∈ s, N = t i * (q * d i))
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∃ c : ℕ, t i = q * c * t j ∨ t j = q * c * t i) :
    (∑ a : ZMod N,
        Complex.normSq (∑ i ∈ s, scaledCharacterBlock χ (d i) a)) =
      ∑ i ∈ s, (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ)) := by
  have hsupport (i : ι) (hi : i ∈ s) :
      FourierSupportedOn (scaledCharacterBlock χ (d i) : ZMod N → ℂ)
        (SmoothFrequencyLayer q (t i) N) := by
    letI : NeZero (d i) := hd i hi
    letI : NeZero (t i) := ht i hi
    exact scaledCharacterBlock_fourierSupportedOn_of_eq hχ (hN i hi)
  have horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∑ a : ZMod N,
          scaledCharacterBlock χ (d i) a *
            (starRingEnd ℂ) (scaledCharacterBlock χ (d j) a) = 0 := by
    intro i hi j hj hij
    apply sum_mul_star_eq_zero_of_supportedOn_disjoint
    · rcases hsep i hi j hj hij with ⟨c, hc | hc⟩
      · letI : NeZero (t j) := ht j hj
        exact smoothFrequencyLayer_disjoint_of_eq_mul hq hc
      · letI : NeZero (t i) := ht i hi
        exact (smoothFrequencyLayer_disjoint_of_eq_mul hq hc).symm
    · exact hsupport i hi
    · exact hsupport j hj
  rw [sum_normSq_finset_sum_of_orthogonal s
    (fun i ↦ scaledCharacterBlock χ (d i)) horth]
  apply Finset.sum_congr rfl
  intro i hi
  letI : NeZero (d i) := hd i hi
  letI : NeZero (t i) := ht i hi
  exact scaledCharacterBlock_energy_of_eq χ (hN i hi)

/-- Quantitative finitary BCC lower bound.  Some residue class carries at
least the average of the exact diagonal energy.  This form avoids division:
the total diagonal energy is bounded by `N` times the attained square norm. -/
theorem generalized_bcc_lower {q N : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d t : ι → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i)) (ht : ∀ i ∈ s, NeZero (t i))
    (hN : ∀ i ∈ s, N = t i * (q * d i))
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∃ c : ℕ, t i = q * c * t j ∨ t j = q * c * t i) :
    ∃ a : ZMod N,
      (∑ i ∈ s, (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))) ≤
        (N : ℝ) *
          Complex.normSq (∑ i ∈ s, scaledCharacterBlock χ (d i) a) := by
  let E : ZMod N → ℝ := fun a ↦
    Complex.normSq (∑ i ∈ s, scaledCharacterBlock χ (d i) a)
  obtain ⟨a, _ha, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (ZMod N)) E Finset.univ_nonempty
  refine ⟨a, ?_⟩
  rw [← generalized_bcc_energy s χ hχ d t hq hd ht hN hsep]
  have hsum : (∑ x : ZMod N, E x) ≤ Fintype.card (ZMod N) • E a :=
    Finset.sum_le_card_nsmul Finset.univ E (E a) (fun x _hx ↦ hmax x (Finset.mem_univ x))
  simpa only [E, ZMod.card, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_id] using hsum

/-- The family off-diagonal cancellation instantiated at the distinct
`q`-smooth covering degrees `q^i`. -/
theorem scaledCharacterBlock_offDiagonal_qpowers_eq_zero {q N : ℕ}
    [NeZero q] [NeZero N] (s : Finset ℕ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i))
    (hN : ∀ i ∈ s, N = q ^ i * (q * d i)) :
    ∑ i ∈ s, ∑ j ∈ s.filter (fun j ↦ i ≠ j),
        ∑ a : ZMod N,
          scaledCharacterBlock χ (d i) a *
            (starRingEnd ℂ) (scaledCharacterBlock χ (d j) a) = 0 := by
  apply offDiagonal_sum_mul_star_eq_zero s
  intro i hi j hj hij
  apply disjointFourierSupport_of_supportedOn_disjoint
  · exact smoothFrequencyLayer_disjoint_pow_of_ne hq hij
  · letI : NeZero (d i) := hd i hi
    letI : NeZero (q ^ i) := ⟨pow_ne_zero _ (NeZero.ne q)⟩
    exact scaledCharacterBlock_fourierSupportedOn_of_eq hχ (hN i hi)
  · letI : NeZero (d j) := hd j hj
    letI : NeZero (q ^ j) := ⟨pow_ne_zero _ (NeZero.ne q)⟩
    exact scaledCharacterBlock_fourierSupportedOn_of_eq hχ (hN j hj)

/-- Concrete `q`-power version of the generalized BCC lower bound. -/
theorem generalized_bcc_lower_qpowers {q N : ℕ} [NeZero q] [NeZero N]
    (s : Finset ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i))
    (hN : ∀ i ∈ s, N = q ^ i * (q * d i)) :
    ∃ a : ZMod N,
      (∑ i ∈ s, (d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ))) ≤
        (N : ℝ) *
          Complex.normSq (∑ i ∈ s, scaledCharacterBlock χ (d i) a) := by
  apply generalized_bcc_lower s χ hχ d (fun i ↦ q ^ i) hq hd
  · intro i _hi
    exact ⟨pow_ne_zero _ (NeZero.ne q)⟩
  · exact hN
  · intro i _hi j _hj hij
    exact qpow_separated_of_ne hij

/-- Exact orthogonal splitting of a combined prefix at distinct `q`-power
layers. -/
theorem scaledCharacterPrefix_family_energy_qpowers {q N L : ℕ}
    [NeZero q] [NeZero N] (s : Finset ℕ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i))
    (hN : ∀ i ∈ s, N = q ^ i * (q * d i)) :
    (∑ a : ZMod N,
        Complex.normSq (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a)) =
      ∑ i ∈ s, ∑ a : ZMod N,
        Complex.normSq (scaledCharacterPrefix χ (d i) L a) := by
  apply sum_normSq_finset_sum_of_orthogonal
  intro i hi j hj hij
  apply sum_mul_star_eq_zero_of_supportedOn_disjoint
  · exact smoothFrequencyLayer_disjoint_pow_of_ne hq hij
  · letI : NeZero (d i) := hd i hi
    letI : NeZero (q ^ i) := ⟨pow_ne_zero _ (NeZero.ne q)⟩
    exact scaledCharacterPrefix_fourierSupportedOn_of_eq hχ (hN i hi)
  · letI : NeZero (d j) := hd j hj
    letI : NeZero (q ^ j) := ⟨pow_ne_zero _ (NeZero.ne q)⟩
    exact scaledCharacterPrefix_fourierSupportedOn_of_eq hχ (hN j hj)

/-- Coefficient-weighted orthogonal splitting for an arbitrary family of
distinct `q`-smooth scales.  Unit-modulus coefficients do not alter either
support or diagonal energy. -/
theorem scaledCharacterPrefix_family_energy_smooth {q N K L : ℕ}
    [NeZero q] [NeZero N] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d t : ι → ℕ) (c : ι → ℂ)
    (hd : ∀ i ∈ s, NeZero (d i)) (ht : ∀ i ∈ s, NeZero (t i))
    (hN : ∀ i ∈ s, N = t i * (q * d i))
    (hsmooth : ∀ i ∈ s, d i ∣ q ^ K)
    (hinj : Set.InjOn d s) (hc : ∀ i ∈ s, ‖c i‖ = 1) :
    (∑ a : ZMod N,
        Complex.normSq
          (∑ i ∈ s, c i * scaledCharacterPrefix χ (d i) L a)) =
      ∑ i ∈ s, ∑ a : ZMod N,
        Complex.normSq (scaledCharacterPrefix χ (d i) L a) := by
  have hsupport (i : ι) (hi : i ∈ s) :
      FourierSupportedOn
        (fun a : ZMod N ↦ c i * scaledCharacterPrefix χ (d i) L a)
        (SmoothFrequencyLayer q (t i) N) := by
    letI : NeZero (d i) := hd i hi
    letI : NeZero (t i) := ht i hi
    exact fourierSupportedOn_const_mul
      (scaledCharacterPrefix_fourierSupportedOn_of_eq hχ (hN i hi)) (c i)
  have horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∑ a : ZMod N,
          (c i * scaledCharacterPrefix χ (d i) L a) *
            (starRingEnd ℂ) (c j * scaledCharacterPrefix χ (d j) L a) = 0 := by
    intro i hi j hj hij
    apply sum_mul_star_eq_zero_of_supportedOn_disjoint
    · letI : NeZero (t i) := ht i hi
      letI : NeZero (t j) := ht j hj
      exact smoothFrequencyLayer_disjoint_of_smooth_complements
        (hN i hi) (hN j hj) (hsmooth i hi) (hsmooth j hj)
          (fun hdij ↦ hij (hinj hi hj hdij))
    · exact hsupport i hi
    · exact hsupport j hj
  rw [sum_normSq_finset_sum_of_orthogonal s
    (fun i a ↦ c i * scaledCharacterPrefix χ (d i) L a) horth]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a _ha
  exact normSq_const_mul_of_norm_eq_one _ _ (hc i hi)

/-- Prefix-difference lower bound after expanding *all* distinct smooth
divisor layers, while retaining only a chosen subfamily on the diagonal.
This is the form needed for the gcd decomposition: unselected divisor layers
are harmless because every diagonal term is nonnegative. -/
theorem smooth_selected_block_energy_le_medium_weighted_prefix_energy
    {q N K H : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι]
    (all selected : Finset ι) (hsel : selected ⊆ all)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d t : ι → ℕ) (c : ι → ℂ)
    (hd : ∀ i ∈ all, NeZero (d i)) (ht : ∀ i ∈ all, NeZero (t i))
    (hN : ∀ i ∈ all, N = t i * (q * d i))
    (hsmooth : ∀ i ∈ all, d i ∣ q ^ K)
    (hinj : Set.InjOn d all) (hc : ∀ i ∈ all, ‖c i‖ = 1)
    (hdH : ∀ i ∈ selected, 2 * d i ≤ H) :
    (H : ℝ) *
        (∑ i ∈ selected,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))) ≤
      8 * ∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a : ZMod N,
          Complex.normSq
            (∑ i ∈ all,
              c i * scaledCharacterPrefix χ (d i) L a) := by
  have hone (i : ι) (hi : i ∈ selected) :
      (H : ℝ) *
          (∑ a : ZMod N,
            Complex.normSq (scaledCharacterBlock χ (d i) a)) ≤
        8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a) :=
    H_mul_block_energy_le_eight_mul_medium_prefix_energy χ (d i) H (hdH i hi)
  have hsum :
      (∑ i ∈ selected, (H : ℝ) *
          (∑ a : ZMod N,
            Complex.normSq (scaledCharacterBlock χ (d i) a))) ≤
        ∑ i ∈ selected, 8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hone i hi
  have hprefixSubset :
      (∑ i ∈ selected, ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a)) ≤
        ∑ i ∈ all, ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsel
    intro i _hi _hnot
    exact Finset.sum_nonneg fun L _hL ↦
      Finset.sum_nonneg fun a _ha ↦ Complex.normSq_nonneg _
  have hfull :
      (∑ i ∈ all, ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a)) =
        ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq
              (∑ i ∈ all,
                c i * scaledCharacterPrefix χ (d i) L a) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro L _hL
    exact (scaledCharacterPrefix_family_energy_smooth
      all χ hχ d t c hd ht hN hsmooth hinj hc).symm
  have henergy :
      (∑ i ∈ selected, ∑ a : ZMod N,
          Complex.normSq (scaledCharacterBlock χ (d i) a)) =
        ∑ i ∈ selected,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ∈ all := hsel hi
    letI : NeZero (d i) := hd i hia
    letI : NeZero (t i) := ht i hia
    exact scaledCharacterBlock_energy_of_eq χ (hN i hia)
  calc
    (H : ℝ) *
        (∑ i ∈ selected,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))) =
        ∑ i ∈ selected, (H : ℝ) *
          (∑ a : ZMod N,
            Complex.normSq (scaledCharacterBlock χ (d i) a)) := by
      rw [← henergy, Finset.mul_sum]
    _ ≤ ∑ i ∈ selected, 8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a) := hsum
    _ = 8 * (∑ i ∈ selected, ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a)) := by
      rw [Finset.mul_sum]
    _ ≤ 8 * (∑ i ∈ all, ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a)) := by
      gcongr
    _ = 8 * ∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a : ZMod N,
          Complex.normSq
            (∑ i ∈ all,
              c i * scaledCharacterPrefix χ (d i) L a) := by rw [hfull]

theorem medium_full_energy_le_good_add_bad_aux {N H : ℕ} [NeZero N]
    (good : Finset (ZMod N)) (A : ℕ → ZMod N → ℂ) (R : ℝ)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H), ∀ a ∉ good,
      Complex.normSq (A L a) ≤ R) :
    (∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a : ZMod N, Complex.normSq (A L a)) ≤
      (∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a ∈ good, Complex.normSq (A L a)) +
      (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R) := by
  classical
  have hone (L : ℕ) (hL : L ∈ Finset.Ioc H (2 * H)) :
      (∑ a : ZMod N, Complex.normSq (A L a)) ≤
        (∑ a ∈ good, Complex.normSq (A L a)) +
          (((Finset.univ \ good).card : ℝ) * R) := by
    have hsplit :
        (∑ a : ZMod N, Complex.normSq (A L a)) =
          (∑ a ∈ good, Complex.normSq (A L a)) +
            ∑ a ∈ Finset.univ \ good, Complex.normSq (A L a) := by
      have hs := Finset.sum_sdiff (Finset.subset_univ good)
        (f := fun a : ZMod N ↦ Complex.normSq (A L a))
      simpa only [add_comm] using hs.symm
    rw [hsplit]
    gcongr
    have hs := Finset.sum_le_card_nsmul (Finset.univ \ good)
      (fun a ↦ Complex.normSq (A L a)) R
      (fun a ha ↦ hbad L hL a (Finset.mem_sdiff.mp ha).2)
    simpa only [nsmul_eq_mul] using hs
  calc
    (∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a : ZMod N, Complex.normSq (A L a)) ≤
        ∑ L ∈ Finset.Ioc H (2 * H),
          ((∑ a ∈ good, Complex.normSq (A L a)) +
            (((Finset.univ \ good).card : ℝ) * R)) := by
      apply Finset.sum_le_sum
      intro L hL
      exact hone L hL
    _ = (∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A L a)) +
        (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R) := by
      rw [Finset.sum_add_distrib]
      have hcard : (Finset.Ioc H (2 * H)).card = H := by
        rw [Nat.card_Ioc]
        omega
      simp [hcard, nsmul_eq_mul]

/-- Restore bad residue classes in the coefficient-weighted, all-divisor
smooth family, while retaining only `selected` diagonal layers. -/
theorem smooth_selected_block_energy_le_medium_good_weighted_prefix_energy
    {q N K H : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι]
    (all selected : Finset ι) (hsel : selected ⊆ all)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d t : ι → ℕ) (c : ι → ℂ)
    (hd : ∀ i ∈ all, NeZero (d i)) (ht : ∀ i ∈ all, NeZero (t i))
    (hN : ∀ i ∈ all, N = t i * (q * d i))
    (hsmooth : ∀ i ∈ all, d i ∣ q ^ K)
    (hinj : Set.InjOn d all) (hc : ∀ i ∈ all, ‖c i‖ = 1)
    (hdH : ∀ i ∈ selected, 2 * d i ≤ H)
    (good : Finset (ZMod N)) (R : ℝ)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H), ∀ a ∉ good,
      Complex.normSq
        (∑ i ∈ all,
          c i * scaledCharacterPrefix χ (d i) L a) ≤ R) :
    (H : ℝ) *
        (∑ i ∈ selected,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))) ≤
      8 * ((∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good,
            Complex.normSq
              (∑ i ∈ all,
                c i * scaledCharacterPrefix χ (d i) L a)) +
        (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) := by
  calc
    (H : ℝ) *
        (∑ i ∈ selected,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))) ≤
        8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq
              (∑ i ∈ all,
                c i * scaledCharacterPrefix χ (d i) L a) :=
      smooth_selected_block_energy_le_medium_weighted_prefix_energy
        all selected hsel χ hχ d t c hd ht hN hsmooth hinj hc hdH
    _ ≤ 8 * ((∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good,
            Complex.normSq
              (∑ i ∈ all,
                c i * scaledCharacterPrefix χ (d i) L a)) +
        (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) := by
      gcongr
      exact medium_full_energy_le_good_add_bad_aux good
        (fun L a ↦ ∑ i ∈ all,
          c i * scaledCharacterPrefix χ (d i) L a) R hbad

/-- Fully explicit all-divisor consumer using the trivial medium-prefix
bound for the restored residue classes. -/
theorem smooth_selected_block_energy_le_medium_good_weighted_prefix_energy_trivial
    {q N K H : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι]
    (all selected : Finset ι) (hsel : selected ⊆ all)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d t : ι → ℕ) (c : ι → ℂ)
    (hd : ∀ i ∈ all, NeZero (d i)) (ht : ∀ i ∈ all, NeZero (t i))
    (hN : ∀ i ∈ all, N = t i * (q * d i))
    (hsmooth : ∀ i ∈ all, d i ∣ q ^ K)
    (hinj : Set.InjOn d all) (hc : ∀ i ∈ all, ‖c i‖ = 1)
    (hdH : ∀ i ∈ selected, 2 * d i ≤ H)
    (good : Finset (ZMod N)) :
    (H : ℝ) *
        (∑ i ∈ selected,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))) ≤
      8 * ((∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good,
            Complex.normSq
              (∑ i ∈ all,
                c i * scaledCharacterPrefix χ (d i) L a)) +
        (H : ℝ) * (((Finset.univ \ good).card : ℝ) *
          ((((all.card * (2 * H) : ℕ) : ℝ) ^ 2)))) := by
  apply smooth_selected_block_energy_le_medium_good_weighted_prefix_energy
    all selected hsel χ hχ d t c hd ht hN hsmooth hinj hc hdH good
      ((((all.card * (2 * H) : ℕ) : ℝ) ^ 2))
  intro L hL a _ha
  refine (normSq_sum_weighted_scaledCharacterPrefix_le
    all χ d c hc L a).trans ?_
  have hLle : L ≤ 2 * H := (Finset.mem_Ioc.mp hL).2
  have hprod : all.card * L ≤ all.card * (2 * H) :=
    Nat.mul_le_mul_left all.card hLle
  have hprodR :
      (((all.card * L : ℕ) : ℝ)) ≤
        (((all.card * (2 * H) : ℕ) : ℝ)) := by
    exact_mod_cast hprod
  gcongr

theorem q_mul_smooth_diagonal_energy_eq_card {q N : ℕ}
    {ι : Type*} (s : Finset ι) (d t : ι → ℕ)
    (hN : ∀ i ∈ s, N = t i * (q * d i)) :
    (q : ℝ) *
        (∑ i ∈ s,
          (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ))) =
      (s.card : ℝ) * (N : ℝ) * (q.totient : ℝ) := by
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ s, (q : ℝ) *
        ((d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ)))) =
        ∑ _i ∈ s, (N : ℝ) * (q.totient : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hNR : (N : ℝ) =
          (t i : ℝ) * ((q : ℝ) * (d i : ℝ)) := by
        exact_mod_cast hN i hi
      rw [hNR]
      ring
    _ = (s.card : ℝ) * (N : ℝ) * (q.totient : ℝ) := by
      simp [nsmul_eq_mul]
      ring

/-- The all-divisor, unit-coefficient BCC lower bound with linear growth in
the number of retained diagonal layers. -/
theorem smooth_selected_card_lower_le_medium_good_weighted_prefix_energy
    {q N K H : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι]
    (all selected : Finset ι) (hsel : selected ⊆ all)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d t : ι → ℕ) (c : ι → ℂ)
    (hd : ∀ i ∈ all, NeZero (d i)) (ht : ∀ i ∈ all, NeZero (t i))
    (hN : ∀ i ∈ all, N = t i * (q * d i))
    (hsmooth : ∀ i ∈ all, d i ∣ q ^ K)
    (hinj : Set.InjOn d all) (hc : ∀ i ∈ all, ‖c i‖ = 1)
    (hdH : ∀ i ∈ selected, 2 * d i ≤ H)
    (good : Finset (ZMod N)) (R : ℝ)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H), ∀ a ∉ good,
      Complex.normSq
        (∑ i ∈ all,
          c i * scaledCharacterPrefix χ (d i) L a) ≤ R) :
    (H : ℝ) *
        ((selected.card : ℝ) * (N : ℝ) * (q.totient : ℝ)) ≤
      8 * (q : ℝ) *
        ((∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good,
            Complex.normSq
              (∑ i ∈ all,
                c i * scaledCharacterPrefix χ (d i) L a)) +
        (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) := by
  have hbridge :=
    smooth_selected_block_energy_le_medium_good_weighted_prefix_energy
      all selected hsel χ hχ d t c hd ht hN hsmooth hinj hc hdH good R hbad
  have hmul := mul_le_mul_of_nonneg_left hbridge (show (0 : ℝ) ≤ q by positivity)
  have hdiag := q_mul_smooth_diagonal_energy_eq_card selected d t
    (fun i hi ↦ hN i (hsel hi))
  calc
    (H : ℝ) *
        ((selected.card : ℝ) * (N : ℝ) * (q.totient : ℝ)) =
        (q : ℝ) * ((H : ℝ) *
          (∑ i ∈ selected,
            (d i : ℝ) * ((t i : ℝ) * (q.totient : ℝ)))) := by
      rw [← hdiag]
      ring
    _ ≤ (q : ℝ) *
        (8 * ((∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good,
            Complex.normSq
              (∑ i ∈ all,
                c i * scaledCharacterPrefix χ (d i) L a)) +
        (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R))) := hmul
    _ = 8 * (q : ℝ) *
        ((∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good,
            Complex.normSq
              (∑ i ∈ all,
                c i * scaledCharacterPrefix χ (d i) L a)) +
        (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) := by ring

/-- Final finite contradiction endpoint.  A normalized good-residue bound
`B` and an exceptional contribution of the same size force the number of
retained smooth layers to be at most `16 q B / φ(q)`. -/
theorem smooth_selected_family_card_bound
    {q N K H : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι]
    (all selected : Finset ι) (hsel : selected ⊆ all)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d t : ι → ℕ) (c : ι → ℂ)
    (hd : ∀ i ∈ all, NeZero (d i)) (ht : ∀ i ∈ all, NeZero (t i))
    (hN : ∀ i ∈ all, N = t i * (q * d i))
    (hsmooth : ∀ i ∈ all, d i ∣ q ^ K)
    (hinj : Set.InjOn d all) (hc : ∀ i ∈ all, ‖c i‖ = 1)
    (hdH : ∀ i ∈ selected, 2 * d i ≤ H)
    (good : Finset (ZMod N)) (R B : ℝ) (hH : 0 < H)
    (hbadPoint : ∀ L ∈ Finset.Ioc H (2 * H), ∀ a ∉ good,
      Complex.normSq
        (∑ i ∈ all,
          c i * scaledCharacterPrefix χ (d i) L a) ≤ R)
    (hgood : (∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good,
            Complex.normSq
              (∑ i ∈ all,
                c i * scaledCharacterPrefix χ (d i) L a)) ≤
        B * (N : ℝ) * (H : ℝ))
    (hbad : (((Finset.univ \ good).card : ℝ) * R) ≤ B * (N : ℝ)) :
    (selected.card : ℝ) * (q.totient : ℝ) ≤ 16 * (q : ℝ) * B := by
  have hraw := smooth_selected_card_lower_le_medium_good_weighted_prefix_energy
    all selected hsel χ hχ d t c hd ht hN hsmooth hinj hc hdH good R hbadPoint
  have hupper :
      8 * (q : ℝ) *
          ((∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ i ∈ all,
                  c i * scaledCharacterPrefix χ (d i) L a)) +
          (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) ≤
        ((H : ℝ) * (N : ℝ)) * (16 * (q : ℝ) * B) := by
    calc
      8 * (q : ℝ) *
          ((∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ i ∈ all,
                  c i * scaledCharacterPrefix χ (d i) L a)) +
          (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) ≤
          8 * (q : ℝ) *
            ((B * (N : ℝ) * (H : ℝ)) + (H : ℝ) * (B * (N : ℝ))) := by
        gcongr
      _ = ((H : ℝ) * (N : ℝ)) * (16 * (q : ℝ) * B) := by ring
  have hfactored :
      ((H : ℝ) * (N : ℝ)) *
          ((selected.card : ℝ) * (q.totient : ℝ)) ≤
        ((H : ℝ) * (N : ℝ)) * (16 * (q : ℝ) * B) := by
    calc
      ((H : ℝ) * (N : ℝ)) *
          ((selected.card : ℝ) * (q.totient : ℝ)) =
          (H : ℝ) *
            ((selected.card : ℝ) * (N : ℝ) * (q.totient : ℝ)) := by ring
      _ ≤ 8 * (q : ℝ) *
          ((∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ i ∈ all,
                  c i * scaledCharacterPrefix χ (d i) L a)) +
          (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) := hraw
      _ ≤ ((H : ℝ) * (N : ℝ)) * (16 * (q : ℝ) * B) := hupper
  exact le_of_mul_le_mul_left hfactored (mul_pos (by exact_mod_cast hH)
    (by exact_mod_cast NeZero.pos N))

theorem smooth_selected_family_contradiction
    {q N K H : ℕ} [NeZero q] [NeZero N]
    {ι : Type*} [DecidableEq ι]
    (all selected : Finset ι) (hsel : selected ⊆ all)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d t : ι → ℕ) (c : ι → ℂ)
    (hd : ∀ i ∈ all, NeZero (d i)) (ht : ∀ i ∈ all, NeZero (t i))
    (hN : ∀ i ∈ all, N = t i * (q * d i))
    (hsmooth : ∀ i ∈ all, d i ∣ q ^ K)
    (hinj : Set.InjOn d all) (hc : ∀ i ∈ all, ‖c i‖ = 1)
    (hdH : ∀ i ∈ selected, 2 * d i ≤ H)
    (good : Finset (ZMod N)) (R B : ℝ) (hH : 0 < H)
    (hbadPoint : ∀ L ∈ Finset.Ioc H (2 * H), ∀ a ∉ good,
      Complex.normSq
        (∑ i ∈ all,
          c i * scaledCharacterPrefix χ (d i) L a) ≤ R)
    (hgood : (∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good,
            Complex.normSq
              (∑ i ∈ all,
                c i * scaledCharacterPrefix χ (d i) L a)) ≤
        B * (N : ℝ) * (H : ℝ))
    (hbad : (((Finset.univ \ good).card : ℝ) * R) ≤ B * (N : ℝ))
    (hlarge : 16 * (q : ℝ) * B <
      (selected.card : ℝ) * (q.totient : ℝ)) : False := by
  exact (not_lt_of_ge (smooth_selected_family_card_bound
    all selected hsel χ hχ d t c hd ht hN hsmooth hinj hc hdH
      good R B hH hbadPoint hgood hbad)) hlarge

/-- Prefix-difference/averaging bridge for a family of `q`-power layers.
The left side is the exact diagonal block energy; the right side is the
medium-length energy of the combined prefixes. -/
theorem qpower_block_energy_le_medium_prefix_energy {q N H : ℕ}
    [NeZero q] [NeZero N] (s : Finset ℕ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i))
    (hdH : ∀ i ∈ s, 2 * d i ≤ H)
    (hN : ∀ i ∈ s, N = q ^ i * (q * d i)) :
    (H : ℝ) *
        (∑ i ∈ s,
          (d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ))) ≤
      8 * ∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a : ZMod N,
          Complex.normSq
            (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) := by
  have hi (i : ℕ) (hi : i ∈ s) :
      (H : ℝ) *
          (∑ a : ZMod N,
            Complex.normSq (scaledCharacterBlock χ (d i) a)) ≤
        8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a) :=
    H_mul_block_energy_le_eight_mul_medium_prefix_energy χ (d i) H (hdH i hi)
  have hsum :
      (∑ i ∈ s, (H : ℝ) *
          (∑ a : ZMod N,
            Complex.normSq (scaledCharacterBlock χ (d i) a))) ≤
        ∑ i ∈ s, 8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a) := by
    apply Finset.sum_le_sum
    intro i his
    exact hi i his
  have hmedium :
      (∑ i ∈ s, ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a)) =
        ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq
              (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro L _hL
    exact (scaledCharacterPrefix_family_energy_qpowers s χ hχ d hq hd hN).symm
  have hsum' :
      (H : ℝ) * (∑ i ∈ s, ∑ a : ZMod N,
          Complex.normSq (scaledCharacterBlock χ (d i) a)) ≤
        8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq
              (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) := by
    calc
      (H : ℝ) * (∑ i ∈ s, ∑ a : ZMod N,
          Complex.normSq (scaledCharacterBlock χ (d i) a)) =
          ∑ i ∈ s, (H : ℝ) * (∑ a : ZMod N,
            Complex.normSq (scaledCharacterBlock χ (d i) a)) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ s, 8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a) := hsum
      _ = 8 * (∑ i ∈ s, ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq (scaledCharacterPrefix χ (d i) L a)) := by
        rw [Finset.mul_sum]
      _ = 8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq
              (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) := by rw [hmedium]
  have henergy :
      (∑ i ∈ s, ∑ a : ZMod N,
          Complex.normSq (scaledCharacterBlock χ (d i) a)) =
        ∑ i ∈ s,
          (d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    letI : NeZero (d i) := hd i hi
    letI : NeZero (q ^ i) := ⟨pow_ne_zero _ (NeZero.ne q)⟩
    exact scaledCharacterBlock_energy_of_eq χ (hN i hi)
  rw [henergy] at hsum'
  exact hsum'

/-- Restore omitted residue classes in a medium-prefix average.  The error is
the number of bad residues times the number `H` of medium lengths and a
pointwise square-norm bound `R`. -/
theorem medium_full_energy_le_good_add_bad {N H : ℕ} [NeZero N]
    (good : Finset (ZMod N)) (A : ℕ → ZMod N → ℂ) (R : ℝ)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H), ∀ a ∉ good,
      Complex.normSq (A L a) ≤ R) :
    (∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a : ZMod N, Complex.normSq (A L a)) ≤
      (∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a ∈ good, Complex.normSq (A L a)) +
      (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R) := by
  classical
  have hone (L : ℕ) (hL : L ∈ Finset.Ioc H (2 * H)) :
      (∑ a : ZMod N, Complex.normSq (A L a)) ≤
        (∑ a ∈ good, Complex.normSq (A L a)) +
          (((Finset.univ \ good).card : ℝ) * R) := by
    have hsplit :
        (∑ a : ZMod N, Complex.normSq (A L a)) =
          (∑ a ∈ good, Complex.normSq (A L a)) +
            ∑ a ∈ Finset.univ \ good, Complex.normSq (A L a) := by
      have hs := Finset.sum_sdiff (Finset.subset_univ good)
        (f := fun a : ZMod N ↦ Complex.normSq (A L a))
      simpa only [add_comm] using hs.symm
    rw [hsplit]
    gcongr
    have hs := Finset.sum_le_card_nsmul (Finset.univ \ good)
      (fun a ↦ Complex.normSq (A L a)) R
      (fun a ha ↦ hbad L hL a (Finset.mem_sdiff.mp ha).2)
    simpa only [nsmul_eq_mul] using hs
  calc
    (∑ L ∈ Finset.Ioc H (2 * H),
        ∑ a : ZMod N, Complex.normSq (A L a)) ≤
        ∑ L ∈ Finset.Ioc H (2 * H),
          ((∑ a ∈ good, Complex.normSq (A L a)) +
            (((Finset.univ \ good).card : ℝ) * R)) := by
      apply Finset.sum_le_sum
      intro L hL
      exact hone L hL
    _ = (∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good, Complex.normSq (A L a)) +
        (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R) := by
      rw [Finset.sum_add_distrib]
      have hcard : (Finset.Ioc H (2 * H)).card = H := by
        rw [Nat.card_Ioc]
        omega
      simp [hcard, nsmul_eq_mul]

/-- Consumer form combining restoration of bad residues with the exact BCC
prefix-difference lower bound.  A normalized good-residue estimate can be
inserted directly into the first term on the right. -/
theorem qpower_block_energy_le_medium_good_prefix_energy {q N H : ℕ}
    [NeZero q] [NeZero N] (s : Finset ℕ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i))
    (hdH : ∀ i ∈ s, 2 * d i ≤ H)
    (hN : ∀ i ∈ s, N = q ^ i * (q * d i))
    (good : Finset (ZMod N)) (R : ℝ)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H), ∀ a ∉ good,
      Complex.normSq
        (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) ≤ R) :
    (H : ℝ) *
        (∑ i ∈ s,
          (d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ))) ≤
      8 * ((∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good,
            Complex.normSq
              (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a)) +
        (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) := by
  calc
    (H : ℝ) *
        (∑ i ∈ s,
          (d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ))) ≤
        8 * ∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a : ZMod N,
            Complex.normSq
              (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) :=
      qpower_block_energy_le_medium_prefix_energy s χ hχ d hq hd hdH hN
    _ ≤ 8 * ((∑ L ∈ Finset.Ioc H (2 * H),
          ∑ a ∈ good,
            Complex.normSq
              (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a)) +
        (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) := by
      gcongr
      exact medium_full_energy_le_good_add_bad good
        (fun L a ↦ ∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) R hbad

/-- Every admissible `q`-power layer contributes the same normalized amount
`N * φ(q) / q`; this division-free identity exposes linear growth in the
number of selected exponents. -/
theorem q_mul_qpower_diagonal_energy_eq_card {q N : ℕ}
    (s : Finset ℕ) (d : ℕ → ℕ)
    (hN : ∀ i ∈ s, N = q ^ i * (q * d i)) :
    (q : ℝ) *
        (∑ i ∈ s,
          (d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ))) =
      (s.card : ℝ) * (N : ℝ) * (q.totient : ℝ) := by
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ s, (q : ℝ) *
        ((d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ)))) =
        ∑ _i ∈ s, (N : ℝ) * (q.totient : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hNR : (N : ℝ) =
          ((q ^ i : ℕ) : ℝ) * ((q : ℝ) * (d i : ℝ)) := by
        exact_mod_cast hN i hi
      rw [hNR]
      ring
    _ = (s.card : ℝ) * (N : ℝ) * (q.totient : ℝ) := by
      simp [nsmul_eq_mul]
      ring

/-- Final division-free consumer inequality.  Its left side grows linearly
with `s.card`; the two terms on the right are respectively the normalized
good-residue input and the explicitly restored exceptional-set loss. -/
theorem qpower_card_lower_le_medium_good_prefix_energy {q N H : ℕ}
    [NeZero q] [NeZero N] (s : Finset ℕ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i))
    (hdH : ∀ i ∈ s, 2 * d i ≤ H)
    (hN : ∀ i ∈ s, N = q ^ i * (q * d i))
    (good : Finset (ZMod N)) (R : ℝ)
    (hbad : ∀ L ∈ Finset.Ioc H (2 * H), ∀ a ∉ good,
      Complex.normSq
        (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a) ≤ R) :
    (H : ℝ) * ((s.card : ℝ) * (N : ℝ) * (q.totient : ℝ)) ≤
      8 * (q : ℝ) *
        ((∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a)) +
          (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) := by
  have hbridge := qpower_block_energy_le_medium_good_prefix_energy
    s χ hχ d hq hd hdH hN good R hbad
  have hmul := mul_le_mul_of_nonneg_left hbridge (show (0 : ℝ) ≤ q by positivity)
  have hdiag := q_mul_qpower_diagonal_energy_eq_card s d hN
  calc
    (H : ℝ) * ((s.card : ℝ) * (N : ℝ) * (q.totient : ℝ)) =
        (q : ℝ) * ((H : ℝ) *
          (∑ i ∈ s,
            (d i : ℝ) * (((q ^ i : ℕ) : ℝ) * (q.totient : ℝ)))) := by
      rw [← hdiag]
      ring
    _ ≤ (q : ℝ) *
        (8 * ((∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a)) +
          (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R))) := hmul
    _ = 8 * (q : ℝ) *
        ((∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a)) +
          (H : ℝ) * (((Finset.univ \ good).card : ℝ) * R)) := by ring

/-- Fully explicit form using only the trivial bound for a prefix of length at
most `2H`; no separate pointwise exceptional-set hypothesis remains. -/
theorem qpower_card_lower_le_medium_good_prefix_energy_trivial {q N H : ℕ}
    [NeZero q] [NeZero N] (s : Finset ℕ)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ → ℕ) (hq : 1 < q)
    (hd : ∀ i ∈ s, NeZero (d i))
    (hdH : ∀ i ∈ s, 2 * d i ≤ H)
    (hN : ∀ i ∈ s, N = q ^ i * (q * d i))
    (good : Finset (ZMod N)) :
    (H : ℝ) * ((s.card : ℝ) * (N : ℝ) * (q.totient : ℝ)) ≤
      8 * (q : ℝ) *
        ((∑ L ∈ Finset.Ioc H (2 * H),
            ∑ a ∈ good,
              Complex.normSq
                (∑ i ∈ s, scaledCharacterPrefix χ (d i) L a)) +
          (H : ℝ) * (((Finset.univ \ good).card : ℝ) *
            ((((s.card * (2 * H) : ℕ) : ℝ) ^ 2)))) := by
  apply qpower_card_lower_le_medium_good_prefix_energy
    s χ hχ d hq hd hdH hN good
      ((((s.card * (2 * H) : ℕ) : ℝ) ^ 2))
  intro L hL a _ha
  refine (normSq_sum_scaledCharacterPrefix_le s χ d L a).trans ?_
  have hLle : L ≤ 2 * H := (Finset.mem_Ioc.mp hL).2
  have hprod : s.card * L ≤ s.card * (2 * H) :=
    Nat.mul_le_mul_left s.card hLle
  have hprodR :
      (((s.card * L : ℕ) : ℝ)) ≤ (((s.card * (2 * H) : ℕ) : ℝ)) := by
    exact_mod_cast hprod
  gcongr

end Erdos67b

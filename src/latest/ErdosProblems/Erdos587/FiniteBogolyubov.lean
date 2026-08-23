import Mathlib
import ErdosProblems.Erdos587.FiniteFourier

/-!
# A finite cyclic Bogolyubov lemma
-/

namespace Erdos587

open scoped BigOperators ComplexConjugate
open Finset

/-- Explicit membership in `2A-2A` in a cyclic group. -/
def ZModInFourfoldDifference {N : ℕ} (A : Finset (ZMod N)) (x : ZMod N) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A, x = a + b - c - d

/-- The fourth Fourier moment with a character twist is the exact weighted
count of representations in `2A-2A`. -/
theorem fourth_fourier_identity {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) :
    (∑ k : ZMod N,
      cyclicFinsetFourier A k ^ 2 * conj (cyclicFinsetFourier A k) ^ 2 *
        ZMod.stdAddChar (x * k)) =
    ∑ a ∈ A, ∑ c ∈ A, ∑ b ∈ A, ∑ d ∈ A,
      if x = a + b - c - d then (N : ℂ) else 0 := by
  classical
  simp only [cyclicFinsetFourier, pow_two, map_sum, Finset.sum_mul_sum]
  have hconj (y : ZMod N) :
      conj (ZMod.stdAddChar (-y)) = ZMod.stdAddChar y := by
    rw [AddChar.map_neg_eq_conj, Complex.conj_conj]
  simp_rw [hconj]
  have hprod (a b c d k : ZMod N) :
      ZMod.stdAddChar (-(a * k)) * ZMod.stdAddChar (-(b * k)) *
          (ZMod.stdAddChar (c * k) * ZMod.stdAddChar (d * k)) *
          ZMod.stdAddChar (x * k) =
        ZMod.stdAddChar ((x - a - b + c + d) * k) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [Finset.sum_mul]
  simp_rw [hprod]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [cyclic_character_orthogonality]
  congr 1
  apply propext
  constructor <;> intro h
  · linear_combination h
  · linear_combination h

lemma fourth_fourier_sum_eq_zero_of_not_mem {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N)
    (hx : ¬ ZModInFourfoldDifference A x) :
    (∑ k : ZMod N,
      cyclicFinsetFourier A k ^ 2 * conj (cyclicFinsetFourier A k) ^ 2 *
        ZMod.stdAddChar (x * k)) = 0 := by
  rw [fourth_fourier_identity A x]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro c hc
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro d hd
  simp only [ite_eq_right_iff]
  intro hEq
  exfalso
  apply hx
  exact ⟨a, ha, b, hb, c, hc, d, hd, hEq⟩

lemma pow_two_mul_conj_pow_two (z : ℂ) :
    z ^ 2 * conj z ^ 2 = ((‖z‖ ^ 4 : ℝ) : ℂ) := by
  calc
    z ^ 2 * conj z ^ 2 = (z * conj z) ^ 2 := by ring
    _ = (((‖z‖ : ℂ) ^ 2)) ^ 2 := by rw [Complex.mul_conj']
    _ = ((‖z‖ ^ 4 : ℝ) : ℂ) := by
      push_cast
      ring

lemma stdAddChar_re_ge_half_of_close {N : ℕ} [NeZero N]
    {y : ZMod N}
    (hy : ‖ZMod.stdAddChar y - 1‖ ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ (ZMod.stdAddChar y).re := by
  have hre := Complex.abs_re_le_norm (ZMod.stdAddChar y - 1)
  have habs : |(ZMod.stdAddChar y - 1).re| ≤ (1 / 2 : ℝ) :=
    le_trans hre hy
  have hneg := neg_abs_le ((ZMod.stdAddChar y - 1).re)
  norm_num [Complex.sub_re] at habs hneg ⊢
  linarith

lemma stdAddChar_re_ge_neg_one {N : ℕ} [NeZero N] (y : ZMod N) :
    (-1 : ℝ) ≤ (ZMod.stdAddChar y).re := by
  have hre := Complex.abs_re_le_norm (ZMod.stdAddChar y)
  have hnorm : ‖ZMod.stdAddChar y‖ = (1 : ℝ) := by simp
  rw [hnorm] at hre
  exact le_trans (neg_le_neg hre) (neg_abs_le _)

/-- Quantitative Fourier Bogolyubov criterion.  A point approximately
annihilating every large Fourier frequency belongs to `2A-2A`. -/
theorem mem_fourfoldDifference_of_largeSpectrum_close
    {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (x : ZMod N)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτA : τ ≤ A.card)
    (hsmall :
      2 * ((N : ℝ) * A.card * τ ^ 2) < (A.card : ℝ) ^ 4)
    (hclose : ∀ k ∈ cyclicLargeSpectrum A τ,
      ‖ZMod.stdAddChar (x * k) - 1‖ ≤ (1 / 2 : ℝ)) :
    ZModInFourfoldDifference A x := by
  classical
  let F : ZMod N → ℂ := cyclicFinsetFourier A
  let w : ZMod N → ℝ := fun k => ‖F k‖ ^ 4
  let Γ : Finset (ZMod N) := cyclicLargeSpectrum A τ
  let Δ : Finset (ZMod N) :=
    Finset.univ.filter fun k => ¬ τ ≤ ‖F k‖
  have h0Γ : (0 : ZMod N) ∈ Γ := by
    simp only [Γ, cyclicLargeSpectrum, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa [F] using hτA
  have hw0 : w (0 : ZMod N) = (A.card : ℝ) ^ 4 := by
    simp [w, F]
  have hw_nonneg (k : ZMod N) : 0 ≤ w k := by
    exact pow_nonneg (norm_nonneg _) _
  have hlarge_point : ∀ k ∈ Γ,
      (1 / 2 : ℝ) * w k ≤
        w k * (ZMod.stdAddChar (x * k)).re := by
    intro k hk
    have hre := stdAddChar_re_ge_half_of_close (hclose k hk)
    nlinarith [hw_nonneg k]
  have hlarge :
      (1 / 2 : ℝ) * (A.card : ℝ) ^ 4 ≤
        ∑ k ∈ Γ, w k * (ZMod.stdAddChar (x * k)).re := by
    have hsum := Finset.sum_le_sum hlarge_point
    have hsingle : w 0 ≤ ∑ k ∈ Γ, w k := by
      exact Finset.single_le_sum (fun k _ => hw_nonneg k) h0Γ
    rw [hw0] at hsingle
    calc
      (1 / 2 : ℝ) * (A.card : ℝ) ^ 4 ≤
          (1 / 2 : ℝ) * ∑ k ∈ Γ, w k := by nlinarith
      _ = ∑ k ∈ Γ, (1 / 2 : ℝ) * w k := by
        rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ Γ, w k * (ZMod.stdAddChar (x * k)).re := hsum
  have hsmall_point : ∀ k ∈ Δ,
      w k ≤ τ ^ 2 * ‖F k‖ ^ 2 := by
    intro k hk
    have hk' : ‖F k‖ < τ := by
      have := (Finset.mem_filter.mp hk).2
      exact lt_of_not_ge this
    have hn := norm_nonneg (F k)
    have hsquare : ‖F k‖ ^ 2 ≤ τ ^ 2 :=
      (sq_le_sq₀ hn hτ).2 (le_of_lt hk')
    dsimp [w]
    calc
      ‖F k‖ ^ 4 = ‖F k‖ ^ 2 * ‖F k‖ ^ 2 := by ring
      _ ≤ τ ^ 2 * ‖F k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
  have hsmall_sum :
      (∑ k ∈ Δ, w k) ≤ (N : ℝ) * A.card * τ ^ 2 := by
    calc
      (∑ k ∈ Δ, w k) ≤ ∑ k ∈ Δ, τ ^ 2 * ‖F k‖ ^ 2 :=
        Finset.sum_le_sum hsmall_point
      _ = τ ^ 2 * ∑ k ∈ Δ, ‖F k‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ τ ^ 2 * ∑ k : ZMod N, ‖F k‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_univ_sum_of_nonneg fun k => sq_nonneg _) (sq_nonneg τ)
      _ = (N : ℝ) * A.card * τ ^ 2 := by
        rw [show (∑ k : ZMod N, ‖F k‖ ^ 2) = (N : ℝ) * A.card by
          simpa [F] using sum_norm_sq_cyclicFinsetFourier A]
        ring
  have hsmall_lower :
      -(∑ k ∈ Δ, w k) ≤
        ∑ k ∈ Δ, w k * (ZMod.stdAddChar (x * k)).re := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro k hk
    have hre := stdAddChar_re_ge_neg_one (x * k)
    nlinarith [hw_nonneg k]
  have hsplit (v : ZMod N → ℝ) :
      (∑ k ∈ Γ, v k) + ∑ k ∈ Δ, v k = ∑ k : ZMod N, v k := by
    simpa [Γ, Δ, cyclicLargeSpectrum] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k => τ ≤ ‖F k‖) v)
  have hreal :
      0 < (∑ k : ZMod N,
        cyclicFinsetFourier A k ^ 2 * conj (cyclicFinsetFourier A k) ^ 2 *
          ZMod.stdAddChar (x * k)).re := by
    have hbound :
        0 < (1 / 2 : ℝ) * (A.card : ℝ) ^ 4 -
          ((N : ℝ) * A.card * τ ^ 2) := by
      linarith
    have hcombined :
        (1 / 2 : ℝ) * (A.card : ℝ) ^ 4 -
            ((N : ℝ) * A.card * τ ^ 2) ≤
          (∑ k ∈ Γ, w k * (ZMod.stdAddChar (x * k)).re) +
            ∑ k ∈ Δ, w k * (ZMod.stdAddChar (x * k)).re := by
      linarith [hlarge, hsmall_sum, hsmall_lower]
    rw [hsplit (fun k => w k * (ZMod.stdAddChar (x * k)).re)] at hcombined
    have hrewrite :
        (∑ k : ZMod N,
          cyclicFinsetFourier A k ^ 2 * conj (cyclicFinsetFourier A k) ^ 2 *
            ZMod.stdAddChar (x * k)).re =
          ∑ k : ZMod N, w k * (ZMod.stdAddChar (x * k)).re := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_two_mul_conj_pow_two, Complex.re_ofReal_mul]
    rw [hrewrite]
    exact lt_of_lt_of_le hbound hcombined
  by_contra hx
  have hz := fourth_fourier_sum_eq_zero_of_not_mem A x hx
  rw [hz] at hreal
  norm_num at hreal

/-- A parameter-free density form. If `A` has density at least `1/q`, at most
`16q³` frequencies cut out a radius-`1/2` Bohr set contained in `2A-2A`. -/
theorem finite_cyclic_bogolyubov_uniform
    {N : ℕ} [NeZero N] (q : ℕ) (hq : 1 ≤ q)
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hdense : N ≤ q * A.card) (x : ZMod N)
    (hclose : ∀ k ∈ cyclicLargeSpectrum A
        ((A.card : ℝ) / (4 * q)),
      ‖ZMod.stdAddChar (x * k) - 1‖ ≤ (1 / 2 : ℝ)) :
    ZModInFourfoldDifference A x ∧
      (cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))).card ≤ 16 * q ^ 3 := by
  classical
  let a : ℝ := A.card
  let n : ℝ := N
  let qr : ℝ := q
  let den : ℝ := 4 * qr
  let τ : ℝ := a / den
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast hA.card_pos
  have hqr : 1 ≤ qr := by
    dsimp [qr]
    exact_mod_cast hq
  have hden : 0 < den := by
    dsimp [den]
    positivity
  have hdenseR : n ≤ qr * a := by
    dsimp [n, qr, a]
    exact_mod_cast hdense
  have hτ : 0 ≤ τ := by
    dsimp [τ]
    positivity
  have hτA : τ ≤ a := by
    dsimp [τ]
    apply div_le_self (le_of_lt ha)
    dsimp [den]
    nlinarith
  have hsmall : 2 * (n * a * τ ^ 2) < a ^ 4 := by
    have hmul : n * a ≤ (qr * a) * a :=
      mul_le_mul_of_nonneg_right hdenseR (le_of_lt ha)
    calc
      2 * (n * a * τ ^ 2) ≤ 2 * ((qr * a) * a * τ ^ 2) := by
        gcongr
      _ = a ^ 4 / (8 * qr) := by
        dsimp [τ, den]
        field_simp
        ring
      _ < a ^ 4 := by
        apply div_lt_self (pow_pos ha 4)
        nlinarith
  have hmem : ZModInFourfoldDifference A x := by
    apply mem_fourfoldDifference_of_largeSpectrum_close A x hτ
    · simpa [a] using hτA
    · simpa [n, a, τ, den, qr] using hsmall
    · intro k hk
      exact hclose k (by simpa [τ, a, den, qr] using hk)
  have hspectrum := card_cyclicLargeSpectrum_mul_sq_le A hτ
  have hspectrum' :
      ((cyclicLargeSpectrum A τ).card : ℝ) * a ^ 2 ≤
        n * a * den ^ 2 := by
    calc
      ((cyclicLargeSpectrum A τ).card : ℝ) * a ^ 2 =
          (((cyclicLargeSpectrum A τ).card : ℝ) * τ ^ 2) * den ^ 2 := by
            dsimp [τ]
            field_simp
      _ ≤ (n * a) * den ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · simpa [n, a] using hspectrum
        · exact sq_nonneg den
  have hright : n * a * den ^ 2 ≤ (16 * qr ^ 3) * a ^ 2 := by
    calc
      n * a * den ^ 2 ≤ (qr * a) * a * den ^ 2 := by gcongr
      _ = (16 * qr ^ 3) * a ^ 2 := by
        dsimp [den]
        ring
  have hcardR : ((cyclicLargeSpectrum A τ).card : ℝ) ≤ 16 * qr ^ 3 := by
    have hprod := le_trans hspectrum' hright
    apply le_of_mul_le_mul_right (a := a ^ 2) (by simpa [mul_assoc] using hprod)
    exact pow_pos ha 2
  refine ⟨hmem, ?_⟩
  have hcardN : (cyclicLargeSpectrum A τ).card ≤ 16 * q ^ 3 := by
    dsimp [qr] at hcardR
    exact_mod_cast hcardR
  simpa [τ, a, den, qr] using hcardN

end Erdos587

import ErdosProblems.Erdos67b.FourierReduction
import ErdosProblems.Erdos67b.Compactness
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Exponent boxes for the arbitrary-sequence Fourier reduction

These constructions connect an arbitrary sequence on the positive integers
to finite Fourier analysis.  In particular, the input sequence is not
assumed multiplicative.  The no-wrap identity is exact, and the exceptional
set remains visible in the energy bound.
-/

open scoped BigOperators

namespace Erdos67b

/-- A finite box of exponents, reduced modulo `M`. -/
abbrev ExponentBox (s : Finset ℕ) (M : ℕ) := s → ZMod M

/-- The integer represented by the canonical exponent representatives. -/
def exponentBoxNat (s : Finset ℕ) (M : ℕ) (a : ExponentBox s M) : ℕ :=
  ∏ p : s, (p : ℕ) ^ (a p).val

/-- The prime-exponent vector of an integer on the selected coordinates. -/
def exponentBoxVector (s : Finset ℕ) (M n : ℕ) : ExponentBox s M :=
  fun p ↦ (n.factorization p : ZMod M)

theorem exponentBoxNat_pos {s : Finset ℕ} {M : ℕ}
    (hs : ∀ p ∈ s, 0 < p) (a : ExponentBox s M) :
    0 < exponentBoxNat s M a := by
  apply Finset.prod_pos
  intro p _
  exact pow_pos (hs p p.property) _

theorem prod_factorization_eq_of_support_subset {s : Finset ℕ} {n : ℕ}
    (hn : n ≠ 0) (hs : n.factorization.support ⊆ s) :
    ∏ p : s, (p : ℕ) ^ n.factorization p = n := by
  rw [Finset.prod_coe_sort s (fun p : ℕ ↦ p ^ n.factorization p)]
  calc
    ∏ p ∈ s, p ^ n.factorization p =
        ∏ p ∈ n.factorization.support, p ^ n.factorization p := by
      symm
      apply Finset.prod_subset hs
      intro p _ hp
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]
    _ = n := Nat.prod_factorization_pow_eq_self hn

/-- Addition of a small exponent vector represents multiplication without
any reduction error when all coordinate sums are below `M`. -/
theorem exponentBoxNat_add_vector {s : Finset ℕ} {M n : ℕ}
    (a : ExponentBox s M) (hn : n ≠ 0)
    (hs : n.factorization.support ⊆ s)
    (hwrap : ∀ p : s, (a p).val + n.factorization p < M) :
    exponentBoxNat s M (a + exponentBoxVector s M n) =
      exponentBoxNat s M a * n := by
  have hcoord (p : s) :
      ((a + exponentBoxVector s M n) p).val =
        (a p).val + n.factorization p := by
    change (a p + (n.factorization p : ZMod M)).val = _
    have hlt : n.factorization p < M := by
      have := hwrap p
      omega
    rw [ZMod.val_add_of_lt, ZMod.val_natCast_of_lt hlt]
    simpa only [ZMod.val_natCast_of_lt hlt] using hwrap p
  unfold exponentBoxNat
  simp_rw [hcoord, pow_add]
  rw [Finset.prod_mul_distrib, prod_factorization_eq_of_support_subset hn hs]

theorem exponentBoxVector_one (s : Finset ℕ) (M : ℕ) :
    exponentBoxVector s M 1 = 0 := by
  ext p
  simp [exponentBoxVector]

theorem exponentBoxVector_mul (s : Finset ℕ) (M : ℕ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    exponentBoxVector s M (m * n) =
      exponentBoxVector s M m + exponentBoxVector s M n := by
  ext p
  simp [exponentBoxVector, Nat.factorization_mul hm hn]

/-- A dual frequency defines a unit-valued completely multiplicative
function on every positive integer, including integers beyond the cutoff. -/
noncomputable def exponentBoxCharacter (s : Finset ℕ) (M : ℕ) [NeZero M]
    (ψ : AddChar (ExponentBox s M) ℂ) : CompactCircleCharacter :=
  ⟨fun n ↦ ⟨ψ (exponentBoxVector s M n),
      mem_sphere_zero_iff_norm.mpr (ψ.norm_apply _)⟩, by
    constructor
    · apply Subtype.ext
      change ψ (exponentBoxVector s M 1) = 1
      rw [exponentBoxVector_one, ψ.map_zero_eq_one]
    · intro m n
      apply Subtype.ext
      change ψ (exponentBoxVector s M ((m * n : ℕ+) : ℕ)) =
        ψ (exponentBoxVector s M m) * ψ (exponentBoxVector s M n)
      change ψ (exponentBoxVector s M ((m : ℕ) * (n : ℕ))) = _
      rw [exponentBoxVector_mul s M (m := (m : ℕ)) (n := (n : ℕ))
        m.property.ne' n.property.ne', ψ.map_add_eq_mul]⟩

@[simp] theorem exponentBoxCharacter_apply (s : Finset ℕ) (M : ℕ) [NeZero M]
    (ψ : AddChar (ExponentBox s M) ℂ) (n : ℕ+) :
    ((exponentBoxCharacter s M ψ).val n : ℂ) =
      ψ (exponentBoxVector s M n) := rfl

/-- Pull an arbitrary sequence back to the finite exponent box. -/
def exponentBoxPullback {E : Type*} (s : Finset ℕ) (M : ℕ)
    (f : ℕ → E) (a : ExponentBox s M) : E :=
  f (exponentBoxNat s M a)

theorem exponentBoxPullback_unit {E : Type*} [NormedAddCommGroup E]
    {s : Finset ℕ} {M : ℕ} (hs : ∀ p ∈ s, 0 < p)
    (f : ℕ → E) (hf : ∀ n, 0 < n → ‖f n‖ = 1)
    (a : ExponentBox s M) : ‖exponentBoxPullback s M f a‖ = 1 :=
  hf _ (exponentBoxNat_pos hs a)

theorem translateSum_exponentBoxPullback {E : Type*} [NormedAddCommGroup E]
    {s : Finset ℕ} {M m : ℕ} (f : ℕ → E) (a : ExponentBox s M)
    (hs : ∀ j ∈ Finset.Icc 1 m, j.factorization.support ⊆ s)
    (hwrap : ∀ j ∈ Finset.Icc 1 m, ∀ p : s,
      (a p).val + j.factorization p < M) :
    translateSum (Finset.Icc 1 m) (exponentBoxVector s M)
        (exponentBoxPullback s M f) a =
      ∑ j ∈ Finset.Icc 1 m, f (j * exponentBoxNat s M a) := by
  apply Finset.sum_congr rfl
  intro j hj
  change f (exponentBoxNat s M (a + exponentBoxVector s M j)) = _
  rw [exponentBoxNat_add_vector a (by have := (Finset.mem_Icc.mp hj).1; omega)
    (hs j hj) (hwrap j hj), Nat.mul_comm]

/-- A translated unit-vector sum has the trivial length bound, even when
some exponent coordinates wrap around. -/
theorem norm_translateSum_exponentBoxPullback_le
    {E : Type*} [NormedAddCommGroup E]
    {s : Finset ℕ} {M m : ℕ} (hs : ∀ p ∈ s, 0 < p)
    (f : ℕ → E) (hf : ∀ n, 0 < n → ‖f n‖ = 1)
    (a : ExponentBox s M) :
    ‖translateSum (Finset.Icc 1 m) (exponentBoxVector s M)
      (exponentBoxPullback s M f) a‖ ≤ m := by
  unfold translateSum
  calc
    ‖∑ j ∈ Finset.Icc 1 m,
        exponentBoxPullback s M f (a + exponentBoxVector s M j)‖ ≤
        ∑ j ∈ Finset.Icc 1 m,
          ‖exponentBoxPullback s M f (a + exponentBoxVector s M j)‖ :=
      norm_sum_le _ _
    _ = m := by simp [exponentBoxPullback_unit hs f hf]

/-- Quantitative finite Fourier reduction for an arbitrary unit-vector
sequence.  Only the boundary count is left as an explicit numerical term;
there is no multiplicativity hypothesis on `f`. -/
theorem spectral_exponentBox_energy_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Finset ℕ} {M m : ℕ} [NeZero M]
    (hspos : ∀ p ∈ s, 0 < p)
    (f : ℕ → E) (hf : ∀ n, 0 < n → ‖f n‖ = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hdiscrepancy : ∀ d l : ℕ, 0 < d →
      ‖∑ j ∈ Finset.Icc 1 l, f (j * d)‖ ≤ C)
    (hs : ∀ j ∈ Finset.Icc 1 m, j.factorization.support ⊆ s)
    (bad : Finset (ExponentBox s M))
    (hwrap : ∀ a, a ∉ bad → ∀ j ∈ Finset.Icc 1 m, ∀ p : s,
      (a p).val + j.factorization p < M) :
    ∑ ψ : AddChar (ExponentBox s M) ℂ,
      (spectralPMF (exponentBoxPullback s M f)
        (exponentBoxPullback_unit hspos f hf) ψ).toReal *
          ‖∑ j ∈ Finset.Icc 1 m, ψ (exponentBoxVector s M j)‖ ^ 2 ≤
      C ^ 2 + (bad.card : ℝ) * (m : ℝ) ^ 2 /
        Fintype.card (ExponentBox s M) := by
  classical
  rw [spectralPMF_expectation]
  have hcard : (0 : ℝ) < Fintype.card (ExponentBox s M) := by
    exact_mod_cast Fintype.card_pos
  have hpoint (a : ExponentBox s M) :
      ‖translateSum (Finset.Icc 1 m) (exponentBoxVector s M)
        (exponentBoxPullback s M f) a‖ ^ 2 ≤
      C ^ 2 + if a ∈ bad then (m : ℝ) ^ 2 else 0 := by
    by_cases ha : a ∈ bad
    · rw [if_pos ha]
      have htriv := norm_translateSum_exponentBoxPullback_le hspos f hf (m := m) a
      have hsq := sq_le_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ m) |>.2 htriv
      nlinarith [sq_nonneg C]
    · rw [if_neg ha, add_zero, translateSum_exponentBoxPullback f a hs (hwrap a ha)]
      exact (sq_le_sq₀ (norm_nonneg _) hC).2
        (hdiscrepancy _ m (exponentBoxNat_pos hspos a))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦ hpoint a)
  have hsum' :
      (∑ a : ExponentBox s M,
        ‖translateSum (Finset.Icc 1 m) (exponentBoxVector s M)
          (exponentBoxPullback s M f) a‖ ^ 2) ≤
      (Fintype.card (ExponentBox s M) : ℝ) * C ^ 2 +
        (bad.card : ℝ) * (m : ℝ) ^ 2 := by
    simpa [Finset.sum_add_distrib] using hsum
  apply (div_le_iff₀ hcard).2
  calc
    _ ≤ (Fintype.card (ExponentBox s M) : ℝ) * C ^ 2 +
        (bad.card : ℝ) * (m : ℝ) ^ 2 := hsum'
    _ = _ := by field_simp

/-- The canonical representatives safely below the wrapping boundary. -/
def safeExponentValues (M X : ℕ) : Finset (ZMod M) :=
  (Finset.range (M - X)).image fun a : ℕ ↦ (a : ZMod M)

/-- The product of safe exponent ranges. -/
def safeExponentBox (s : Finset ℕ) (M X : ℕ) : Finset (ExponentBox s M) :=
  Fintype.piFinset fun _ : s ↦ safeExponentValues M X

theorem card_safeExponentValues {M X : ℕ} :
    (safeExponentValues M X).card = M - X := by
  unfold safeExponentValues
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  have haM : a < M := (Finset.mem_range.mp ha).trans_le (Nat.sub_le M X)
  have hbM : b < M := (Finset.mem_range.mp hb).trans_le (Nat.sub_le M X)
  have h := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt haM, ZMod.val_natCast_of_lt hbM] using h

theorem card_safeExponentBox (s : Finset ℕ) (M X : ℕ) :
    (safeExponentBox s M X).card = (M - X) ^ s.card := by
  simp [safeExponentBox, card_safeExponentValues]

theorem safeExponentBox_no_wrap {s : Finset ℕ} {M X : ℕ}
    {a : ExponentBox s M} (ha : a ∈ safeExponentBox s M X) (p : s) :
    (a p).val + X < M := by
  have hp := Fintype.mem_piFinset.mp ha p
  obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hp
  have hb' : b < M - X := Finset.mem_range.mp hb
  have hbM : b < M := hb'.trans_le (Nat.sub_le M X)
  rw [← hab, ZMod.val_natCast_of_lt hbM]
  omega

/-- The elementary product estimate behind the boundary union bound. -/
theorem one_sub_mul_le_pow_one_sub (x : ℝ) (hx : x ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmul := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hx)
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)]

/-- Exact size of the wrapping boundary, including the empty-coordinate
case.  The dimension is the cardinality of the chosen finite coordinate set. -/
theorem card_unsafeExponentBox (s : Finset ℕ) (M X : ℕ) [NeZero M] :
    (Finset.univ \ safeExponentBox s M X).card =
      M ^ s.card - (M - X) ^ s.card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), card_safeExponentBox]
  simp [ExponentBox]

/-- The fraction of wrapping points is at most dimension times the
coordinate boundary fraction. -/
theorem unsafeExponentBox_fraction_le (s : Finset ℕ) {M X : ℕ} [NeZero M]
    (hXM : X ≤ M) :
    ((Finset.univ \ safeExponentBox s M X).card : ℝ) /
        Fintype.card (ExponentBox s M) ≤
      (s.card : ℝ) * X / M := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hXM' : (X : ℝ) ≤ M := by exact_mod_cast hXM
  have hfrac : (X : ℝ) / M ≤ 1 := (div_le_one hM).2 hXM'
  have hpow := one_sub_mul_le_pow_one_sub ((X : ℝ) / M) hfrac s.card
  have hsub : ((M - X : ℕ) : ℝ) / M = 1 - (X : ℝ) / M := by
    rw [Nat.cast_sub hXM, sub_div, div_self hM.ne']
  have hle : (M - X) ^ s.card ≤ M ^ s.card :=
    Nat.pow_le_pow_left (Nat.sub_le M X) s.card
  rw [card_unsafeExponentBox, Nat.cast_sub hle]
  simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, Nat.cast_pow]
  rw [sub_div, div_self (pow_ne_zero _ hM.ne'), ← div_pow, hsub]
  rw [mul_div_assoc]
  linarith

theorem factorization_le_index (n p : ℕ) : n.factorization p ≤ n := by
  by_cases hp : p.Prime
  · apply Nat.factorization_le_of_le_pow
    exact n.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hp.two_le n)
  · simp [Nat.factorization_eq_zero_of_not_prime n hp]

/-- An actual finite Fourier law with one bound for every prefix through
the cutoff.  The selected modulus absorbs the full wrapping error. -/
theorem exists_bounded_spectral_exponentBox
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : ℕ → E) (hf : ∀ n, 0 < n → ‖f n‖ = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hdiscrepancy : ∀ d l : ℕ, 0 < d →
      ‖∑ j ∈ Finset.Icc 1 l, f (j * d)‖ ≤ C) (X : ℕ) :
    ∃ M : ℕ, ∃ _hM : NeZero M,
      let s := Finset.Icc 1 X
      let F := exponentBoxPullback s M f
      ∃ hF : ∀ a, ‖F a‖ = 1,
        ∀ m : ℕ, m ≤ X →
          ∑ ψ : AddChar (ExponentBox s M) ℂ,
            (spectralPMF F hF ψ).toReal *
              ‖∑ j ∈ Finset.Icc 1 m, ψ (exponentBoxVector s M j)‖ ^ 2 ≤
            C ^ 2 + 1 := by
  classical
  let s := Finset.Icc 1 X
  let M := s.card * X * X ^ 2 + X + 1
  have hMpos : 0 < M := by dsimp [M]; omega
  let : NeZero M := ⟨hMpos.ne'⟩
  have hspos : ∀ p ∈ s, 0 < p := by
    intro p hp
    exact (Finset.mem_Icc.mp hp).1
  refine ⟨M, inferInstance, exponentBoxPullback_unit hspos f hf, ?_⟩
  intro m hm
  let bad := Finset.univ \ safeExponentBox s M X
  have hs : ∀ j ∈ Finset.Icc 1 m, j.factorization.support ⊆ s := by
    intro j hj p hp
    have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
    have hp' := Nat.mem_primeFactors.mp hp
    exact Finset.mem_Icc.mpr ⟨hp'.1.one_le,
      (Nat.le_of_dvd hjpos hp'.2.1).trans ((Finset.mem_Icc.mp hj).2.trans hm)⟩
  have hwrap : ∀ a, a ∉ bad → ∀ j ∈ Finset.Icc 1 m, ∀ p : s,
      (a p).val + j.factorization p < M := by
    intro a ha j hj p
    have ha' : a ∈ safeExponentBox s M X := by simpa [bad] using ha
    have haM := safeExponentBox_no_wrap ha' p
    have hjX := (Finset.mem_Icc.mp hj).2.trans hm
    have hfac := factorization_le_index j p
    omega
  have henergy := spectral_exponentBox_energy_le hspos f hf C hC
    hdiscrepancy hs bad hwrap
  have hXM : X ≤ M := by dsimp [M]; omega
  have hboundary := unsafeExponentBox_fraction_le s hXM
  have hprod := mul_le_mul_of_nonneg_right hboundary (sq_nonneg (m : ℝ))
  have hsize : (s.card : ℝ) * X * (m : ℝ) ^ 2 ≤ M := by
    have hnat : s.card * X * m ^ 2 ≤ M := by
      calc
        s.card * X * m ^ 2 ≤ s.card * X * X ^ 2 := by gcongr
        _ ≤ M := by dsimp [M]; omega
    exact_mod_cast hnat
  have herror : (bad.card : ℝ) * (m : ℝ) ^ 2 /
      Fintype.card (ExponentBox s M) ≤ 1 := by
    calc
      _ = ((bad.card : ℝ) / Fintype.card (ExponentBox s M)) * (m : ℝ) ^ 2 := by
        ring
      _ ≤ ((s.card : ℝ) * X / M) * (m : ℝ) ^ 2 := hprod
      _ = ((s.card : ℝ) * X * (m : ℝ) ^ 2) / M := by ring
      _ ≤ 1 := (div_le_one (by exact_mod_cast hMpos)).2 hsize
  exact henergy.trans (add_le_add_right herror _)

end Erdos67b

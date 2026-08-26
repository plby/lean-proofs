import ErdosProblems.Erdos1002.DivisorSubpolynomial
import ErdosProblems.Erdos1002.WindowErrorReduction
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A uniform divisor envelope for the window kernel

This file proves the arithmetic estimate needed after the finite reduction
in `WindowErrorReduction`.  We use only the already established fact

`reciprocalDivisorSum m / log m -> 0`.

The formulation is deliberately finite and uniform.  Given `epsilon > 0`,
all sufficiently large indices satisfy the same pointwise divisor estimate.
On a centred ball we split the remaining indices into a central block and
dyadic annuli.  The central block has `O(d)` points, the `j`-th annulus has
`O(2^j d)` points, and the squared window kernel is `O(4^{-j})` there.
The finitely many exceptional small indices contribute one constant which
is independent of the centre, the window width, and every Fourier cutoff.

No infinite Fourier series or principal value is used in this module.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- The elementary squared-kernel majorant.  Its value at zero distance is
defined separately, as required by the analytic kernel. -/
def windowDecayWeight (d m M : ℕ) : ℝ :=
  if Nat.dist m M ≤ d then 1
  else (d : ℝ) ^ 2 / (Nat.dist m M : ℝ) ^ 2

/-- Positive integers up to `K` lying in the closed ball of radius `R`
about the natural centre `M`. -/
def centeredWindowBall (K M R : ℕ) : Finset ℕ :=
  (Icc 1 K).filter fun m ↦ Nat.dist m M ≤ R

/-- The annulus with inner radius `2^j d` removed and outer radius
`2^(j+1)d` retained. -/
def centeredWindowAnnulus (K M d j : ℕ) : Finset ℕ :=
  centeredWindowBall K M (2 ^ (j + 1) * d) \
    centeredWindowBall K M (2 ^ j * d)

theorem windowDecayWeight_nonneg (d m M : ℕ) :
    0 ≤ windowDecayWeight d m M := by
  unfold windowDecayWeight
  split_ifs
  · positivity
  · positivity

theorem windowDecayWeight_le_one (d m M : ℕ) :
    windowDecayWeight d m M ≤ 1 := by
  unfold windowDecayWeight
  split_ifs with h
  · exact le_rfl
  · have hdist : d < Nat.dist m M := Nat.lt_of_not_ge h
    have hdistR : (d : ℝ) ≤ (Nat.dist m M : ℝ) := by
      exact_mod_cast hdist.le
    have hdist0 : 0 < (Nat.dist m M : ℝ) := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le d) hdist)
    rw [div_le_one (sq_pos_of_pos hdist0)]
    nlinarith [sq_nonneg ((d : ℝ) - (Nat.dist m M : ℝ))]

theorem centeredWindowBall_subset_Icc (K M R : ℕ) :
    centeredWindowBall K M R ⊆ Icc (M - R) (M + R) := by
  intro m hm
  have hdist : Nat.dist m M ≤ R := (mem_filter.mp hm).2
  rw [mem_Icc]
  constructor
  · by_cases hmM : m ≤ M
    · rw [Nat.dist_eq_sub_of_le hmM] at hdist
      omega
    · omega
  · by_cases hMm : M ≤ m
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hMm] at hdist
      omega
    · omega

theorem card_centeredWindowBall_le (K M R : ℕ) :
    (centeredWindowBall K M R).card ≤ 2 * R + 1 := by
  have hcard := card_le_card (centeredWindowBall_subset_Icc K M R)
  rw [Nat.card_Icc] at hcard
  omega

theorem centeredWindowBall_mono_radius
    {K M R S : ℕ} (hRS : R ≤ S) :
    centeredWindowBall K M R ⊆ centeredWindowBall K M S := by
  intro m hm
  rw [centeredWindowBall, mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.trans hRS⟩

theorem mem_centeredWindowBall_log_le
    {K M R m : ℕ} (hm : m ∈ centeredWindowBall K M R) :
    Real.log (m : ℝ) ≤ Real.log (Real.exp 1 + M + R) := by
  have hmPos : 0 < m := (mem_Icc.mp (mem_filter.mp hm).1).1
  have hmUpper : m ≤ M + R :=
    (mem_Icc.mp (centeredWindowBall_subset_Icc K M R hm)).2
  have hmRPos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmPos
  apply Real.log_le_log hmRPos
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  have hmCast : (m : ℝ) ≤ (M : ℝ) + R := by exact_mod_cast hmUpper
  have hstrict : (M : ℝ) + R < Real.exp 1 + M + R := by linarith
  exact hmCast.trans hstrict.le

/-- The asymptotic divisor estimate in the one-sided form used below. -/
theorem eventually_reciprocalDivisorSum_le_mul_log
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in atTop,
      reciprocalDivisorSum m ≤ epsilon * Real.log (m : ℝ) := by
  have hlim := tendsto_reciprocalDivisorSum_div_log
  have hratio : ∀ᶠ m : ℕ in atTop,
      reciprocalDivisorSum m / Real.log (m : ℝ) < epsilon := by
    have hopen : Set.Iio epsilon ∈ nhds (0 : ℝ) := by
      exact Iio_mem_nhds hepsilon
    exact hlim.eventually hopen
  filter_upwards [hratio,
    eventually_atTop.2 ⟨3, fun m hm ↦ hm⟩] with m hmRatio hm3
  have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos hmOne
  have := (div_lt_iff₀ hlog).mp hmRatio
  exact this.le

/-- The scale with respect to which the envelope is uniform.  The
`exp 1` term guarantees that its logarithm is at least one. -/
def windowEnvelopeScale (M d : ℕ) : ℝ :=
  Real.exp 1 + M + d

theorem one_le_log_windowEnvelopeScale (M d : ℕ) :
    1 ≤ Real.log (windowEnvelopeScale M d) := by
  have hbase : Real.exp 1 ≤ windowEnvelopeScale M d := by
    unfold windowEnvelopeScale
    have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  calc
    1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (windowEnvelopeScale M d) :=
      Real.log_le_log (Real.exp_pos 1) hbase

theorem card_centeredWindowAnnulus_le (K M d j : ℕ) :
    (centeredWindowAnnulus K M d j).card ≤
      2 * (2 ^ (j + 1) * d) + 1 := by
  exact (card_le_card (sdiff_subset :
    centeredWindowAnnulus K M d j ⊆
      centeredWindowBall K M (2 ^ (j + 1) * d))).trans
    (card_centeredWindowBall_le K M (2 ^ (j + 1) * d))

theorem windowDecayWeight_le_on_annulus
    {K M d j m : ℕ} (hd : 0 < d)
    (hm : m ∈ centeredWindowAnnulus K M d j) :
    windowDecayWeight d m M ≤ 1 / ((2 ^ j : ℕ) : ℝ) ^ 2 := by
  rcases mem_sdiff.mp hm with ⟨hmOuter, hmInner⟩
  have hdist : 2 ^ j * d < Nat.dist m M := by
    by_contra h
    apply hmInner
    rw [centeredWindowBall, mem_filter]
    exact ⟨(mem_filter.mp hmOuter).1, Nat.le_of_not_gt h⟩
  have hpow : 1 ≤ 2 ^ j := one_le_pow₀ (by omega)
  have hdDist : d < Nat.dist m M :=
    lt_of_le_of_lt (by simpa using! Nat.mul_le_mul_right d hpow) hdist
  rw [windowDecayWeight, if_neg (Nat.not_le.mpr hdDist)]
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hqR : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hdistR : (0 : ℝ) < (Nat.dist m M : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hdist)
  have hlower :
      ((2 ^ j : ℕ) : ℝ) * d ≤ (Nat.dist m M : ℝ) := by
    exact_mod_cast hdist.le
  calc
    (d : ℝ) ^ 2 / (Nat.dist m M : ℝ) ^ 2 ≤
        (d : ℝ) ^ 2 /
          (((2 ^ j : ℕ) : ℝ) * d) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hdistR)
        (sq_pos_of_pos (mul_pos hqR hdR))).2
      have hsquare :
          (((2 ^ j : ℕ) : ℝ) * d) ^ 2 ≤
            (Nat.dist m M : ℝ) ^ 2 :=
        (sq_le_sq₀ (mul_nonneg hqR.le hdR.le) hdistR.le).2 hlower
      exact mul_le_mul_of_nonneg_left hsquare (sq_nonneg (d : ℝ))
    _ = 1 / ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      field_simp

/-- On the `j`-th outer ball, logarithms grow by at most the linear
dyadic correction `(j+1) log 2`. -/
theorem log_le_on_dyadic_ball
    {K M d j m : ℕ}
    (hm : m ∈ centeredWindowBall K M (2 ^ (j + 1) * d)) :
    Real.log (m : ℝ) ≤
      Real.log (windowEnvelopeScale M d) +
        (j + 1 : ℕ) * Real.log 2 := by
  have hfirst := mem_centeredWindowBall_log_le hm
  let q : ℕ := 2 ^ (j + 1)
  have hq : 1 ≤ q := by dsimp [q]; exact one_le_pow₀ (by omega)
  have hqPos : (0 : ℝ) < (q : ℝ) := by positivity
  have hscalePos : 0 < windowEnvelopeScale M d := by
    unfold windowEnvelopeScale
    positivity
  have hcompare :
      Real.exp 1 + (M : ℝ) + (q : ℝ) * d ≤
        (q : ℝ) * windowEnvelopeScale M d := by
    unfold windowEnvelopeScale
    have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hleftNonneg : 0 ≤ (q : ℝ) - 1 := sub_nonneg.mpr hqR
    have hrightNonneg : 0 ≤ Real.exp 1 + (M : ℝ) := by positivity
    nlinarith [mul_nonneg hleftNonneg hrightNonneg]
  calc
    Real.log (m : ℝ) ≤
        Real.log (Real.exp 1 + (M : ℝ) +
          ((2 ^ (j + 1) * d : ℕ) : ℝ)) := hfirst
    _ = Real.log (Real.exp 1 + (M : ℝ) + (q : ℝ) * d) := by
      simp only [q, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ Real.log ((q : ℝ) * windowEnvelopeScale M d) := by
      apply Real.log_le_log
      · positivity
      · exact hcompare
    _ = Real.log (q : ℝ) + Real.log (windowEnvelopeScale M d) := by
      rw [Real.log_mul hqPos.ne' hscalePos.ne']
    _ = Real.log (windowEnvelopeScale M d) +
          (j + 1 : ℕ) * Real.log 2 := by
      dsimp [q]
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      ring

/-- Exact finite telescoping into the central block and dyadic annuli.
This identity is valid for an arbitrary coefficient function. -/
theorem sum_centeredWindowBall_dyadic
    (K M d n : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ centeredWindowBall K M (2 ^ n * d), f m) =
      (∑ m ∈ centeredWindowBall K M d, f m) +
        ∑ j ∈ range n, ∑ m ∈ centeredWindowAnnulus K M d j, f m := by
  induction n with
  | zero => simp [centeredWindowBall]
  | succ n ih =>
      have hrad : 2 ^ n * d ≤ 2 ^ (n + 1) * d := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right d
          (Nat.le_mul_of_pos_right (2 ^ n) (by omega))
      have hsub :
          centeredWindowBall K M (2 ^ n * d) ⊆
            centeredWindowBall K M (2 ^ (n + 1) * d) :=
        centeredWindowBall_mono_radius hrad
      have hsplit := Finset.sum_sdiff (f := f) hsub
      change
        (∑ m ∈ centeredWindowAnnulus K M d n, f m) +
          ∑ m ∈ centeredWindowBall K M (2 ^ n * d), f m =
            ∑ m ∈ centeredWindowBall K M (2 ^ (n + 1) * d), f m at hsplit
      rw [← hsplit, ih, sum_range_succ]
      ring

/-- The fixed contribution of all exceptional indices below `T`. -/
def reciprocalDivisorExceptionalMass (T : ℕ) : ℝ :=
  ∑ m ∈ Ico 1 T, reciprocalDivisorSum m

theorem reciprocalDivisorExceptionalMass_nonneg (T : ℕ) :
    0 ≤ reciprocalDivisorExceptionalMass T := by
  unfold reciprocalDivisorExceptionalMass
  exact Finset.sum_nonneg fun m _hm ↦ reciprocalDivisorSum_nonneg m

/-- The part of the kernel sum coming from indices below `T` is bounded
by one fixed finite constant, uniformly in every window parameter. -/
theorem small_indices_kernel_sum_le
    (K M R d T : ℕ) :
    (∑ m ∈ centeredWindowBall K M R with m < T,
        reciprocalDivisorSum m * windowDecayWeight d m M) ≤
      reciprocalDivisorExceptionalMass T := by
  have hsub :
      (centeredWindowBall K M R).filter (fun m ↦ m < T) ⊆ Ico 1 T := by
    intro m hm
    rcases mem_filter.mp hm with ⟨hmBall, hmT⟩
    exact mem_Ico.mpr ⟨(mem_Icc.mp (mem_filter.mp hmBall).1).1, hmT⟩
  unfold reciprocalDivisorExceptionalMass
  calc
    (∑ m ∈ centeredWindowBall K M R with m < T,
        reciprocalDivisorSum m * windowDecayWeight d m M) ≤
        ∑ m ∈ centeredWindowBall K M R with m < T,
          reciprocalDivisorSum m := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_of_le_one_right (reciprocalDivisorSum_nonneg m)
        (windowDecayWeight_le_one d m M)
    _ ≤ ∑ m ∈ Ico 1 T, reciprocalDivisorSum m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro m _hm _hnot
      exact reciprocalDivisorSum_nonneg m

/-- The summand with the fixed exceptional initial segment deleted. -/
def largeWindowKernelTerm (T d M m : ℕ) : ℝ :=
  if T ≤ m then reciprocalDivisorSum m * windowDecayWeight d m M else 0

theorem largeWindowKernelTerm_nonneg (T d M m : ℕ) :
    0 ≤ largeWindowKernelTerm T d M m := by
  unfold largeWindowKernelTerm
  split_ifs
  · exact mul_nonneg (reciprocalDivisorSum_nonneg m)
      (windowDecayWeight_nonneg d m M)
  · exact le_rfl

/-- Uniform bound for the central block. -/
theorem central_large_kernel_sum_le
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {T K M d : ℕ} (hd : 0 < d)
    (hlarge : ∀ m, T ≤ m →
      reciprocalDivisorSum m ≤ epsilon * Real.log (m : ℝ)) :
    (∑ m ∈ centeredWindowBall K M d,
        largeWindowKernelTerm T d M m) ≤
      3 * epsilon * d * Real.log (windowEnvelopeScale M d) := by
  let B : ℝ := epsilon * Real.log (windowEnvelopeScale M d)
  have hB : 0 ≤ B := mul_nonneg hepsilon
    (le_trans (by norm_num) (one_le_log_windowEnvelopeScale M d))
  have hpoint : ∀ m ∈ centeredWindowBall K M d,
      largeWindowKernelTerm T d M m ≤ B := by
    intro m hm
    unfold largeWindowKernelTerm
    split_ifs with hmT
    · have hsigma := hlarge m hmT
      have hlog := mem_centeredWindowBall_log_le hm
      have hlogScale :
          Real.log (m : ℝ) ≤ Real.log (windowEnvelopeScale M d) := by
        simpa only [windowEnvelopeScale] using! hlog
      calc
        reciprocalDivisorSum m * windowDecayWeight d m M ≤
            reciprocalDivisorSum m :=
          mul_le_of_le_one_right (reciprocalDivisorSum_nonneg m)
            (windowDecayWeight_le_one d m M)
        _ ≤ epsilon * Real.log (m : ℝ) := hsigma
        _ ≤ B := mul_le_mul_of_nonneg_left hlogScale hepsilon
    · exact hB
  have hsum := Finset.sum_le_card_nsmul
    (centeredWindowBall K M d) (largeWindowKernelTerm T d M) B hpoint
  have hcardNat : (centeredWindowBall K M d).card ≤ 3 * d := by
    calc
      (centeredWindowBall K M d).card ≤ 2 * d + 1 :=
        card_centeredWindowBall_le K M d
      _ ≤ 3 * d := by omega
  have hcard : ((centeredWindowBall K M d).card : ℝ) ≤ 3 * d := by
    exact_mod_cast hcardNat
  calc
    (∑ m ∈ centeredWindowBall K M d,
        largeWindowKernelTerm T d M m) ≤
        ((centeredWindowBall K M d).card : ℝ) * B := by
      simpa only [nsmul_eq_mul] using! hsum
    _ ≤ (3 * d : ℝ) * B := mul_le_mul_of_nonneg_right hcard hB
    _ = 3 * epsilon * d * Real.log (windowEnvelopeScale M d) := by
      dsimp [B]
      ring

/-- Uniform bound on one dyadic annulus.  The factor `1/2^j` is the
product of `O(2^j d)` lattice points and the squared `O(2^{-2j})`
kernel decay. -/
theorem annulus_large_kernel_sum_le
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {T K M d j : ℕ} (hd : 0 < d)
    (hlarge : ∀ m, T ≤ m →
      reciprocalDivisorSum m ≤ epsilon * Real.log (m : ℝ)) :
    (∑ m ∈ centeredWindowAnnulus K M d j,
        largeWindowKernelTerm T d M m) ≤
      5 * epsilon * d / (2 ^ j : ℕ) *
        (Real.log (windowEnvelopeScale M d) +
          (j + 1 : ℕ) * Real.log 2) := by
  let q : ℕ := 2 ^ j
  let L : ℝ := Real.log (windowEnvelopeScale M d) +
    (j + 1 : ℕ) * Real.log 2
  have hqPos : (0 : ℝ) < (q : ℝ) := by positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    have hscale : 0 ≤ Real.log (windowEnvelopeScale M d) :=
      le_trans (by norm_num) (one_le_log_windowEnvelopeScale M d)
    have hlogTwo : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    positivity
  have hpoint : ∀ m ∈ centeredWindowAnnulus K M d j,
      largeWindowKernelTerm T d M m ≤ epsilon * L / (q : ℝ) ^ 2 := by
    intro m hm
    unfold largeWindowKernelTerm
    split_ifs with hmT
    · have hsigma := hlarge m hmT
      have hmOuter := (mem_sdiff.mp hm).1
      have hlog : Real.log (m : ℝ) ≤ L := by
        simpa only [L] using! log_le_on_dyadic_ball hmOuter
      have hw : windowDecayWeight d m M ≤ 1 / (q : ℝ) ^ 2 := by
        simpa only [q] using! windowDecayWeight_le_on_annulus hd hm
      have hlogNonneg : 0 ≤ Real.log (m : ℝ) := by
        have hmOne : 1 ≤ m := (mem_Icc.mp (mem_filter.mp hmOuter).1).1
        exact Real.log_nonneg (by exact_mod_cast hmOne)
      calc
        reciprocalDivisorSum m * windowDecayWeight d m M ≤
            (epsilon * Real.log (m : ℝ)) *
              windowDecayWeight d m M :=
          mul_le_mul_of_nonneg_right hsigma
            (windowDecayWeight_nonneg d m M)
        _ ≤ (epsilon * L) * windowDecayWeight d m M := by
          apply mul_le_mul_of_nonneg_right _ (windowDecayWeight_nonneg d m M)
          exact mul_le_mul_of_nonneg_left hlog hepsilon
        _ ≤ (epsilon * L) * (1 / (q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hw (mul_nonneg hepsilon hL)
        _ = epsilon * L / (q : ℝ) ^ 2 := by ring
    · exact div_nonneg (mul_nonneg hepsilon hL) (sq_nonneg _)
  have hsum := Finset.sum_le_card_nsmul
    (centeredWindowAnnulus K M d j) (largeWindowKernelTerm T d M)
      (epsilon * L / (q : ℝ) ^ 2) hpoint
  have hqd : 1 ≤ q * d := Nat.mul_pos (by positivity) hd
  have hcardNat : (centeredWindowAnnulus K M d j).card ≤ 5 * q * d := by
    calc
      (centeredWindowAnnulus K M d j).card ≤
          2 * (2 ^ (j + 1) * d) + 1 :=
        card_centeredWindowAnnulus_le K M d j
      _ = 4 * q * d + 1 := by dsimp [q]; rw [pow_succ]; ring
      _ ≤ 4 * q * d + q * d := Nat.add_le_add_left hqd _
      _ = 5 * q * d := by ring
  have hcard : ((centeredWindowAnnulus K M d j).card : ℝ) ≤
      5 * (q : ℝ) * d := by exact_mod_cast hcardNat
  have hfactor : 0 ≤ epsilon * L / (q : ℝ) ^ 2 := by positivity
  calc
    (∑ m ∈ centeredWindowAnnulus K M d j,
        largeWindowKernelTerm T d M m) ≤
        ((centeredWindowAnnulus K M d j).card : ℝ) *
          (epsilon * L / (q : ℝ) ^ 2) := by
      simpa only [nsmul_eq_mul] using! hsum
    _ ≤ (5 * (q : ℝ) * d) *
          (epsilon * L / (q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard hfactor
    _ = 5 * epsilon * d / (q : ℝ) * L := by
      field_simp
    _ = 5 * epsilon * d / (2 ^ j : ℕ) *
          (Real.log (windowEnvelopeScale M d) +
            (j + 1 : ℕ) * Real.log 2) := by rfl

/-- The exact finite dyadic envelope before summing the two convergent
geometric moments. -/
theorem finite_window_kernel_envelope_explicit
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {T K M d n : ℕ} (hd : 0 < d)
    (hlarge : ∀ m, T ≤ m →
      reciprocalDivisorSum m ≤ epsilon * Real.log (m : ℝ)) :
    (∑ m ∈ centeredWindowBall K M (2 ^ n * d),
        reciprocalDivisorSum m * windowDecayWeight d m M) ≤
      reciprocalDivisorExceptionalMass T +
        3 * epsilon * d * Real.log (windowEnvelopeScale M d) +
        ∑ j ∈ range n,
          5 * epsilon * d / (2 ^ j : ℕ) *
            (Real.log (windowEnvelopeScale M d) +
              (j + 1 : ℕ) * Real.log 2) := by
  let B := centeredWindowBall K M (2 ^ n * d)
  let f : ℕ → ℝ := fun m ↦
    reciprocalDivisorSum m * windowDecayWeight d m M
  have hsplit :
      (∑ m ∈ B, f m) =
        (∑ m ∈ B with m < T, f m) +
          ∑ m ∈ B, largeWindowKernelTerm T d M m := by
    rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hmT : m < T
    · simp [hmT, largeWindowKernelTerm]
    · have hTm : T ≤ m := Nat.le_of_not_gt hmT
      simp [f, hmT, hTm, largeWindowKernelTerm]
  have hsmall :
      (∑ m ∈ B with m < T, f m) ≤
        reciprocalDivisorExceptionalMass T := by
    simpa only [B, f] using!
      small_indices_kernel_sum_le K M (2 ^ n * d) d T
  have hdecomp := sum_centeredWindowBall_dyadic K M d n
    (largeWindowKernelTerm T d M)
  have hcentral := central_large_kernel_sum_le
    (T := T) (K := K) (M := M) (d := d) hepsilon hd hlarge
  have hannuli :
      (∑ j ∈ range n,
          ∑ m ∈ centeredWindowAnnulus K M d j,
            largeWindowKernelTerm T d M m) ≤
        ∑ j ∈ range n,
          5 * epsilon * d / (2 ^ j : ℕ) *
            (Real.log (windowEnvelopeScale M d) +
              (j + 1 : ℕ) * Real.log 2) := by
    apply Finset.sum_le_sum
    intro j hj
    exact annulus_large_kernel_sum_le hepsilon hd hlarge
  change (∑ m ∈ centeredWindowBall K M (2 ^ n * d), f m) ≤ _
  calc
    (∑ m ∈ centeredWindowBall K M (2 ^ n * d), f m) =
        (∑ m ∈ B with m < T, f m) +
          ∑ m ∈ B, largeWindowKernelTerm T d M m := hsplit
    _ ≤ reciprocalDivisorExceptionalMass T +
          ∑ m ∈ B, largeWindowKernelTerm T d M m :=
      add_le_add hsmall le_rfl
    _ = reciprocalDivisorExceptionalMass T +
          ((∑ m ∈ centeredWindowBall K M d,
              largeWindowKernelTerm T d M m) +
            ∑ j ∈ range n,
              ∑ m ∈ centeredWindowAnnulus K M d j,
                largeWindowKernelTerm T d M m) := by
      dsimp only [B]
      rw [hdecomp]
    _ ≤ reciprocalDivisorExceptionalMass T +
          (3 * epsilon * d * Real.log (windowEnvelopeScale M d) +
            ∑ j ∈ range n,
              5 * epsilon * d / (2 ^ j : ℕ) *
                (Real.log (windowEnvelopeScale M d) +
                (j + 1 : ℕ) * Real.log 2)) := by
      exact add_le_add le_rfl (add_le_add hcentral hannuli)
    _ = reciprocalDivisorExceptionalMass T +
          3 * epsilon * d * Real.log (windowEnvelopeScale M d) +
          ∑ j ∈ range n,
            5 * epsilon * d / (2 ^ j : ℕ) *
              (Real.log (windowEnvelopeScale M d) +
                (j + 1 : ℕ) * Real.log 2) := by ring

/-- Zeroth geometric moment of the dyadic decomposition. -/
def windowDyadicMassConstant : ℝ :=
  ∑' j : ℕ, (1 / 2 : ℝ) ^ j

/-- First geometric moment of the dyadic decomposition. -/
def windowDyadicMomentConstant : ℝ :=
  ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j

theorem summable_windowDyadicMass :
    Summable fun j : ℕ ↦ (1 / 2 : ℝ) ^ j := by
  exact summable_geometric_of_norm_lt_one (by norm_num)

theorem summable_windowDyadicMoment :
    Summable fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j := by
  have hfirst : Summable fun j : ℕ ↦
      (j : ℝ) * (1 / 2 : ℝ) ^ j := by
    simpa only [pow_one] using!
      (summable_pow_mul_geometric_of_norm_lt_one 1
        (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num))
  convert! hfirst.add summable_windowDyadicMass using 1
  funext j
  push_cast
  ring

theorem windowDyadicMassConstant_nonneg :
    0 ≤ windowDyadicMassConstant := by
  exact tsum_nonneg fun j ↦ by positivity

theorem windowDyadicMomentConstant_nonneg :
    0 ≤ windowDyadicMomentConstant := by
  exact tsum_nonneg fun j ↦ by positivity

theorem sum_range_dyadicMass_le (n : ℕ) :
    (∑ j ∈ range n, 1 / ((2 ^ j : ℕ) : ℝ)) ≤
      windowDyadicMassConstant := by
  have heq : (fun j : ℕ ↦ 1 / ((2 ^ j : ℕ) : ℝ)) =
      fun j : ℕ ↦ (1 / 2 : ℝ) ^ j := by
    funext j
    simp only [Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow]
  rw [heq]
  exact summable_windowDyadicMass.sum_le_tsum (range n)
    (fun j hj ↦ by positivity)

theorem sum_range_dyadicMoment_le (n : ℕ) :
    (∑ j ∈ range n,
        ((j + 1 : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)) ≤
      windowDyadicMomentConstant := by
  have heq : (fun j : ℕ ↦
      ((j + 1 : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)) =
      fun j : ℕ ↦ ((j + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j := by
    funext j
    rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
    rfl
  rw [heq]
  exact summable_windowDyadicMoment.sum_le_tsum (range n)
    (fun j hj ↦ by positivity)

/-- A fixed finite constant for the central block and both geometric
moments. -/
def windowKernelEnvelopeConstant : ℝ :=
  3 + 5 * windowDyadicMassConstant +
    5 * Real.log 2 * windowDyadicMomentConstant

theorem three_le_windowKernelEnvelopeConstant :
    3 ≤ windowKernelEnvelopeConstant := by
  unfold windowKernelEnvelopeConstant
  have hlogTwo : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hmass : 0 ≤ 5 * windowDyadicMassConstant := by
    exact mul_nonneg (by norm_num) windowDyadicMassConstant_nonneg
  have hmoment :
      0 ≤ 5 * Real.log 2 * windowDyadicMomentConstant := by
    exact mul_nonneg (mul_nonneg (by norm_num) hlogTwo)
      windowDyadicMomentConstant_nonneg
  linarith

theorem windowKernelEnvelopeConstant_pos :
    0 < windowKernelEnvelopeConstant :=
  lt_of_lt_of_le (by norm_num) three_le_windowKernelEnvelopeConstant

private theorem sum_range_annulus_envelope_le
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (M d n : ℕ) :
    (∑ j ∈ range n,
        5 * epsilon * d / (2 ^ j : ℕ) *
          (Real.log (windowEnvelopeScale M d) +
            (j + 1 : ℕ) * Real.log 2)) ≤
      (5 * windowDyadicMassConstant +
          5 * Real.log 2 * windowDyadicMomentConstant) *
        epsilon * d * Real.log (windowEnvelopeScale M d) := by
  let L : ℝ := Real.log (windowEnvelopeScale M d)
  have hLone : 1 ≤ L := by
    dsimp [L]
    exact one_le_log_windowEnvelopeScale M d
  have hL : 0 ≤ L := le_trans (by norm_num) hLone
  have hlogTwo : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hpoint : ∀ j : ℕ,
      5 * epsilon * d / (2 ^ j : ℕ) *
          (L + (j + 1 : ℕ) * Real.log 2) ≤
        (5 * epsilon * d * L) * (1 / ((2 ^ j : ℕ) : ℝ)) +
          (5 * epsilon * d * L * Real.log 2) *
            (((j + 1 : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by
    intro j
    let X : ℝ :=
      5 * epsilon * d * ((j + 1 : ℕ) : ℝ) * Real.log 2 /
        ((2 ^ j : ℕ) : ℝ)
    have hX : 0 ≤ X := by
      dsimp [X]
      positivity
    have hXL : X ≤ L * X := by
      have := mul_le_mul_of_nonneg_right hLone hX
      simpa only [one_mul] using! this
    dsimp [X] at hXL
    calc
      5 * epsilon * d / (2 ^ j : ℕ) *
          (L + (j + 1 : ℕ) * Real.log 2) =
        (5 * epsilon * d * L) * (1 / ((2 ^ j : ℕ) : ℝ)) +
          5 * epsilon * d * ((j + 1 : ℕ) : ℝ) * Real.log 2 /
            ((2 ^ j : ℕ) : ℝ) := by ring
      _ ≤ (5 * epsilon * d * L) * (1 / ((2 ^ j : ℕ) : ℝ)) +
          L * (5 * epsilon * d * ((j + 1 : ℕ) : ℝ) * Real.log 2 /
            ((2 ^ j : ℕ) : ℝ)) := add_le_add le_rfl hXL
      _ = (5 * epsilon * d * L) * (1 / ((2 ^ j : ℕ) : ℝ)) +
          (5 * epsilon * d * L * Real.log 2) *
            (((j + 1 : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by ring
  have hsumPoint :
      (∑ j ∈ range n,
          5 * epsilon * d / (2 ^ j : ℕ) *
            (L + (j + 1 : ℕ) * Real.log 2)) ≤
        (5 * epsilon * d * L) *
            (∑ j ∈ range n, 1 / ((2 ^ j : ℕ) : ℝ)) +
          (5 * epsilon * d * L * Real.log 2) *
            (∑ j ∈ range n,
              ((j + 1 : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by
    calc
      (∑ j ∈ range n,
          5 * epsilon * d / (2 ^ j : ℕ) *
            (L + (j + 1 : ℕ) * Real.log 2)) ≤
          ∑ j ∈ range n,
            ((5 * epsilon * d * L) * (1 / ((2 ^ j : ℕ) : ℝ)) +
              (5 * epsilon * d * L * Real.log 2) *
                (((j + 1 : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))) := by
        exact Finset.sum_le_sum fun j hj ↦ hpoint j
      _ = (5 * epsilon * d * L) *
            (∑ j ∈ range n, 1 / ((2 ^ j : ℕ) : ℝ)) +
          (5 * epsilon * d * L * Real.log 2) *
            (∑ j ∈ range n,
              ((j + 1 : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hmass := sum_range_dyadicMass_le n
  have hmoment := sum_range_dyadicMoment_le n
  have hcoefMass : 0 ≤ 5 * epsilon * d * L := by positivity
  have hcoefMoment : 0 ≤ 5 * epsilon * d * L * Real.log 2 := by positivity
  calc
    (∑ j ∈ range n,
        5 * epsilon * d / (2 ^ j : ℕ) *
          (Real.log (windowEnvelopeScale M d) +
            (j + 1 : ℕ) * Real.log 2)) =
        ∑ j ∈ range n,
          5 * epsilon * d / (2 ^ j : ℕ) *
            (L + (j + 1 : ℕ) * Real.log 2) := by rfl
    _ ≤ (5 * epsilon * d * L) *
            (∑ j ∈ range n, 1 / ((2 ^ j : ℕ) : ℝ)) +
          (5 * epsilon * d * L * Real.log 2) *
            (∑ j ∈ range n,
              ((j + 1 : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)) := hsumPoint
    _ ≤ (5 * epsilon * d * L) * windowDyadicMassConstant +
          (5 * epsilon * d * L * Real.log 2) *
            windowDyadicMomentConstant :=
      add_le_add (mul_le_mul_of_nonneg_left hmass hcoefMass)
        (mul_le_mul_of_nonneg_left hmoment hcoefMoment)
    _ = (5 * windowDyadicMassConstant +
          5 * Real.log 2 * windowDyadicMomentConstant) *
        epsilon * d * Real.log (windowEnvelopeScale M d) := by
      dsimp [L]
      ring

/-- Uniform finite envelope with a fixed exceptional constant.  Every
quantifier relevant to Fourier truncation is displayed explicitly. -/
theorem finite_window_kernel_envelope
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {T K M d n : ℕ} (hd : 0 < d)
    (hlarge : ∀ m, T ≤ m →
      reciprocalDivisorSum m ≤ epsilon * Real.log (m : ℝ)) :
    (∑ m ∈ centeredWindowBall K M (2 ^ n * d),
        reciprocalDivisorSum m * windowDecayWeight d m M) ≤
      reciprocalDivisorExceptionalMass T +
        windowKernelEnvelopeConstant * epsilon * d *
          Real.log (windowEnvelopeScale M d) := by
  have hexplicit := finite_window_kernel_envelope_explicit
    (T := T) (K := K) (M := M) (d := d) (n := n)
    hepsilon hd hlarge
  have hannuli := sum_range_annulus_envelope_le hepsilon M d n
  calc
    (∑ m ∈ centeredWindowBall K M (2 ^ n * d),
        reciprocalDivisorSum m * windowDecayWeight d m M) ≤
      reciprocalDivisorExceptionalMass T +
        3 * epsilon * d * Real.log (windowEnvelopeScale M d) +
        ∑ j ∈ range n,
          5 * epsilon * d / (2 ^ j : ℕ) *
            (Real.log (windowEnvelopeScale M d) +
              (j + 1 : ℕ) * Real.log 2) := hexplicit
    _ ≤ reciprocalDivisorExceptionalMass T +
        3 * epsilon * d * Real.log (windowEnvelopeScale M d) +
        (5 * windowDyadicMassConstant +
            5 * Real.log 2 * windowDyadicMomentConstant) *
          epsilon * d * Real.log (windowEnvelopeScale M d) :=
      add_le_add le_rfl hannuli
    _ = reciprocalDivisorExceptionalMass T +
        windowKernelEnvelopeConstant * epsilon * d *
          Real.log (windowEnvelopeScale M d) := by
      unfold windowKernelEnvelopeConstant
      ring

/-- Uniform little-`o` formulation.  For every target coefficient `eta`,
there is one finite exceptional mass, after which all centres, widths,
Fourier cutoffs, and dyadic truncations satisfy the same bound. -/
theorem uniform_finite_window_kernel_is_sublogarithmic
    {eta : ℝ} (heta : 0 < eta) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (K M d n : ℕ), 0 < d →
        (∑ m ∈ centeredWindowBall K M (2 ^ n * d),
            reciprocalDivisorSum m * windowDecayWeight d m M) ≤
          A + eta * d * Real.log (windowEnvelopeScale M d) := by
  let epsilon : ℝ := eta / windowKernelEnvelopeConstant
  have hepsilon : 0 < epsilon := div_pos heta windowKernelEnvelopeConstant_pos
  have hevent := eventually_reciprocalDivisorSum_le_mul_log hepsilon
  rw [eventually_atTop] at hevent
  rcases hevent with ⟨T, hT⟩
  refine ⟨reciprocalDivisorExceptionalMass T,
    reciprocalDivisorExceptionalMass_nonneg T, ?_⟩
  intro K M d n hd
  have hbound := finite_window_kernel_envelope
    (T := T) (K := K) (M := M) (d := d) (n := n)
    hepsilon.le hd hT
  calc
    (∑ m ∈ centeredWindowBall K M (2 ^ n * d),
        reciprocalDivisorSum m * windowDecayWeight d m M) ≤
      reciprocalDivisorExceptionalMass T +
        windowKernelEnvelopeConstant * epsilon * d *
          Real.log (windowEnvelopeScale M d) := hbound
    _ = reciprocalDivisorExceptionalMass T +
        eta * d * Real.log (windowEnvelopeScale M d) := by
      dsimp [epsilon]
      field_simp [windowKernelEnvelopeConstant_pos.ne']

private theorem nat_le_two_pow_window (r : ℕ) : r ≤ 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hone : 1 ≤ 2 ^ r := one_le_pow₀ (by omega)
      rw [pow_succ]
      omega

theorem centeredWindowBall_eq_Icc_of_large_radius
    {K M R : ℕ} (hR : K + M ≤ R) :
    centeredWindowBall K M R = Icc 1 K := by
  apply Finset.ext
  intro m
  simp only [centeredWindowBall, mem_filter]
  constructor
  · exact fun hm ↦ hm.1
  · intro hm
    refine ⟨hm, ?_⟩
    have hmK : m ≤ K := (mem_Icc.mp hm).2
    have hKR : K ≤ R := by omega
    by_cases hmM : m ≤ M
    · rw [Nat.dist_eq_sub_of_le hmM]
      omega
    · have hMm : M ≤ m := Nat.le_of_not_ge hmM
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hMm]
      have hsub : m - M ≤ m := Nat.sub_le m M
      exact hsub.trans (hmK.trans hKR)

/-- Cutoff form of the uniform envelope.  Unlike the dyadic statement,
this conclusion quantifies only over the actual Fourier cutoff `K`; the
proof chooses a sufficiently large dyadic ball internally. -/
theorem uniform_finite_cutoff_window_kernel_is_sublogarithmic
    {eta : ℝ} (heta : 0 < eta) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (K M d : ℕ), 0 < d →
        (∑ m ∈ Icc 1 K,
            reciprocalDivisorSum m * windowDecayWeight d m M) ≤
          A + eta * d * Real.log (windowEnvelopeScale M d) := by
  rcases uniform_finite_window_kernel_is_sublogarithmic heta with
    ⟨A, hA, hball⟩
  refine ⟨A, hA, ?_⟩
  intro K M d hd
  let n : ℕ := K + M
  have hradius : K + M ≤ 2 ^ n * d := by
    calc
      K + M ≤ 2 ^ n := by
        dsimp [n]
        exact nat_le_two_pow_window (K + M)
      _ ≤ 2 ^ n * d := Nat.le_mul_of_pos_right _ hd
  have hbound := hball K M d n hd
  rw [centeredWindowBall_eq_Icc_of_large_radius hradius] at hbound
  exact hbound

/-- The finite weighted divisor energy which occurs after applying the
squared window-kernel decay estimate. -/
def finiteDivisorWindowEnergy (K M d : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 K,
    reciprocalDivisorSum m * windowDecayWeight d m M

theorem uniform_finiteDivisorWindowEnergy_additive
    {eta : ℝ} (heta : 0 < eta) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (K M d : ℕ), 0 < d →
        finiteDivisorWindowEnergy K M d ≤
          A + eta * d * Real.log (windowEnvelopeScale M d) := by
  simpa only [finiteDivisorWindowEnergy] using!
    uniform_finite_cutoff_window_kernel_is_sublogarithmic heta

/-- Literal uniform little-`o` form: after one scale threshold, the
exceptional finite mass is absorbed, uniformly over every Fourier cutoff,
centre, and positive width. -/
theorem uniform_finiteDivisorWindowEnergy_small_above_scale
    {eta : ℝ} (heta : 0 < eta) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ (K M d : ℕ), 0 < d →
        H ≤ Real.log (windowEnvelopeScale M d) →
          finiteDivisorWindowEnergy K M d ≤
            eta * d * Real.log (windowEnvelopeScale M d) := by
  have hetaHalf : 0 < eta / 2 := by positivity
  rcases uniform_finiteDivisorWindowEnergy_additive hetaHalf with
    ⟨A, hA, hbound⟩
  let H : ℝ := 2 * A / eta
  have hH : 0 ≤ H := by
    dsimp [H]
    positivity
  refine ⟨H, hH, ?_⟩
  intro K M d hd hscale
  let L : ℝ := Real.log (windowEnvelopeScale M d)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact le_trans (by norm_num) (one_le_log_windowEnvelopeScale M d)
  have hAeq : A = (eta / 2) * H := by
    dsimp [H]
    field_simp [heta.ne']
  have hAtoL : A ≤ (eta / 2) * L := by
    rw [hAeq]
    exact mul_le_mul_of_nonneg_left hscale hetaHalf.le
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hLd : (eta / 2) * L ≤ (eta / 2) * d * L := by
    have hnonneg : 0 ≤ (eta / 2) * L := mul_nonneg hetaHalf.le hL
    have hmul := mul_le_mul_of_nonneg_right hdR hnonneg
    nlinarith
  have hAabsorb : A ≤ (eta / 2) * d * L := hAtoL.trans hLd
  have hraw := hbound K M d hd
  change finiteDivisorWindowEnergy K M d ≤ A + (eta / 2) * d * L at hraw
  change finiteDivisorWindowEnergy K M d ≤ eta * d * L
  calc
    finiteDivisorWindowEnergy K M d ≤
        A + (eta / 2) * d * L := hraw
    _ ≤ (eta / 2) * d * L + (eta / 2) * d * L :=
      add_le_add hAabsorb le_rfl
    _ = eta * d * L := by ring

end

end Erdos1002

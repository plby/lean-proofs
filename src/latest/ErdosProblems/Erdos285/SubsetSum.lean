import ErdosProblems.Erdos285.Dispersion
import ErdosProblems.Erdos285.FourierBound

/-!
# Martin's sparse modular subset-sum lemma

This file supplies the analytic bridge between Martin's centered-inverse
dispersion lemma and the exact finite-Fourier counting formula in
`Erdos285.Modular`.  If at least half of the indexed inverse residues stay a
scaled distance `δ` from zero at every nonzero frequency, then the associated
character product is at most

`2 ^ |M| * exp (-δ² |M|)`.

Martin's published lower bound on `|M|` makes this decay stronger than all
`n - 1` nonzero Fourier frequencies combined.  Consequently every residue
modulo `n` is a sum of inverses of a subset of `M`.
-/

namespace Erdos285.SubsetSum

open scoped BigOperators Real
open Finset
open Filter

noncomputable section

/-- Least absolute integer representative of the character argument used in
Martin's Fourier product. -/
def characterDistance (n : ℕ) (h : ZMod n) (m : ℕ) : ℕ :=
  (-((m : ZMod n)⁻¹ * h)).valMinAbs.natAbs

/-- The character distance is the absolute value of Martin's centered inverse.
The frequency is represented by its canonical natural value. -/
theorem characterDistance_eq_centeredInverse {n : ℕ} [NeZero n]
    (h : ZMod n) (m : ℕ) :
    characterDistance n h m =
      (Erdos285.Modular.centeredInverse n h.val m).natAbs := by
  rw [characterDistance, Erdos285.Modular.centeredInverse]
  rw [show ((h.val : ℕ) : ZMod n) = h by simp]
  rw [mul_comm]
  exact ZMod.natAbs_valMinAbs_neg _

/-- The same identity, stated with the centered representative used by the
unconditional dispersion theorem. -/
theorem characterDistance_eq_dispersion_centeredInverse {n : ℕ} [NeZero n]
    (h : ZMod n) (m : ℕ) :
    characterDistance n h m =
      (Erdos285.Dispersion.centeredInverse n h.val m).natAbs := by
  rw [characterDistance, Erdos285.Dispersion.centeredInverse]
  rw [show ((h.val : ℕ) : ZMod n) = h by simp]
  rw [mul_comm]
  exact ZMod.natAbs_valMinAbs_neg _

/-- Half-angle identity for a point on the complex unit circle. -/
theorem norm_one_add_exp_two_pi (x : ℝ) :
    ‖1 + Complex.exp (2 * Real.pi * Complex.I * x)‖ =
      2 * |Real.cos (Real.pi * x)| := by
  have hid :
      (1 : ℂ) + Complex.exp (2 * Real.pi * Complex.I * x) =
        Complex.exp (Real.pi * x * Complex.I) *
          (Complex.exp (-(Real.pi * x) * Complex.I) +
            Complex.exp (Real.pi * x * Complex.I)) := by
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
    ring_nf
    simp [add_comm]
  rw [hid, norm_mul, Complex.norm_exp]
  have htwo :
      Complex.exp (-(Real.pi * x) * Complex.I) +
          Complex.exp (Real.pi * x * Complex.I) =
        2 * Complex.cos (Real.pi * x) := by
    rw [add_comm, ← Complex.two_cos]
  rw [htwo]
  norm_num [Complex.mul_re]
  have harg : (Real.pi : ℂ) * x = ((Real.pi * x : ℝ) : ℂ) := by norm_num
  have hcos : Complex.cos ((Real.pi : ℂ) * x) =
      (Real.cos (Real.pi * x) : ℂ) :=
    (congrArg Complex.cos harg).trans (Complex.ofReal_cos _).symm
  have hncos := congrArg (fun z : ℂ ↦ ‖z‖) hcos
  rw [Complex.norm_real, Real.norm_eq_abs] at hncos
  exact hncos

/-- A standard additive-character factor is exponentially smaller than two
in terms of its centered distance from zero. -/
theorem norm_one_add_stdAddChar_le (n : ℕ) [NeZero n] (z : ZMod n) :
    ‖1 + ZMod.stdAddChar z‖ ≤
      2 * Real.exp (-(2 * (((z.valMinAbs : ℝ) / n) ^ 2))) := by
  conv_lhs => rw [← z.coe_valMinAbs]
  rw [ZMod.stdAddChar_coe]
  have hid :
      (2 * Real.pi * Complex.I * (z.valMinAbs : ℂ) / (n : ℂ)) =
        2 * Real.pi * Complex.I * ((z.valMinAbs : ℝ) / n) := by
    push_cast
    ring
  rw [hid]
  calc
    ‖1 + Complex.exp (2 * Real.pi * Complex.I * ((z.valMinAbs : ℝ) / n))‖ =
        2 * |Real.cos (Real.pi * ((z.valMinAbs : ℝ) / n))| := by
      have hcast : ((((z.valMinAbs : ℝ) / (n : ℝ) : ℝ) : ℂ)) =
          (z.valMinAbs : ℂ) / (n : ℂ) := by
        push_cast
        norm_cast
      have hnorm := norm_one_add_exp_two_pi ((z.valMinAbs : ℝ) / n)
      rw [hcast] at hnorm
      exact hnorm
    _ ≤ 2 * Real.exp (-(2 * (((z.valMinAbs : ℝ) / n) ^ 2))) := by
      gcongr
      apply UnitFractions.cos_bound_abs
      have hle := z.natAbs_valMinAbs_le
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
      rw [show |(z.valMinAbs : ℝ)| = (z.valMinAbs.natAbs : ℝ) by simp]
      have hn : 0 < (n : ℝ) := by exact_mod_cast (NeZero.pos n)
      rw [div_le_iff₀ hn]
      calc
        (z.valMinAbs.natAbs : ℝ) ≤ (n / 2 : ℕ) := by exact_mod_cast hle
        _ ≤ (n : ℝ) / 2 := Nat.cast_div_le
        _ = 1 / 2 * (n : ℝ) := by ring

/-- Uniform trivial bound for a standard character factor. -/
theorem norm_one_add_stdAddChar_le_two {n : ℕ} [NeZero n] (z : ZMod n) :
    ‖1 + ZMod.stdAddChar z‖ ≤ 2 := by
  calc
    ‖1 + ZMod.stdAddChar z‖ ≤ ‖(1 : ℂ)‖ + ‖ZMod.stdAddChar z‖ := norm_add_le _ _
    _ = 2 := by rw [norm_one, AddChar.norm_apply]; norm_num

/-- Product estimate when a designated subset of factors has an additional
multiplicative saving `rho`. -/
theorem norm_prod_le_two_pow_mul {M G : Finset ℕ} (f : ℕ → ℂ) (rho : ℝ)
    (hG : G ⊆ M) (hrho : 0 ≤ rho)
    (hall : ∀ m ∈ M, ‖f m‖ ≤ 2)
    (hgood : ∀ m ∈ G, ‖f m‖ ≤ 2 * rho) :
    ‖M.prod f‖ ≤ (2 : ℝ) ^ M.card * rho ^ G.card := by
  have hsplit : G.prod f * (M \ G).prod f = M.prod f := by
    simpa [mul_comm] using (Finset.prod_sdiff (f := f) hG)
  rw [← hsplit, norm_mul]
  calc
    ‖G.prod f‖ * ‖(M \ G).prod f‖ ≤
        ((G.prod fun _ ↦ (2 : ℝ) * rho) * ((M \ G).prod fun _ ↦ (2 : ℝ))) := by
      gcongr
      · simpa only [norm_prod] using
          Finset.prod_le_prod (fun _ _ ↦ by positivity) hgood
      · simpa only [norm_prod] using
          Finset.prod_le_prod (fun _ _ ↦ by positivity)
            (fun m hm ↦ hall m (Finset.mem_sdiff.mp hm).1)
    _ = ((2 : ℝ) * rho) ^ G.card * (2 : ℝ) ^ (M \ G).card := by simp
    _ = (2 : ℝ) ^ M.card * rho ^ G.card := by
      rw [mul_pow]
      rw [show (2 : ℝ) ^ G.card * rho ^ G.card * 2 ^ (M \ G).card =
          (2 ^ G.card * 2 ^ (M \ G).card) * rho ^ G.card by ring]
      congr 1
      rw [← pow_add]
      congr 1
      have hcard := Finset.card_sdiff_add_card_eq_card hG
      omega

/-- If at least half the factors have centered scale at least `δ`, the
complete character product has Martin's exponential decay. -/
theorem characterProduct_le_of_scaled_dispersion {n : ℕ} [NeZero n]
    (M : Finset ℕ) (h : ZMod n) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hdisp : M.card ≤
      2 * (M.filter fun m ↦ delta ≤ (characterDistance n h m : ℝ) / n).card) :
    ‖M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤
      (2 : ℝ) ^ M.card * Real.exp (-(delta ^ 2 * M.card)) := by
  let G := M.filter fun m ↦ delta ≤ (characterDistance n h m : ℝ) / n
  have hG : G ⊆ M := filter_subset _ _
  have hall : ∀ m ∈ M,
      ‖1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤ 2 := by
    intro m _
    exact norm_one_add_stdAddChar_le_two _
  have hgood : ∀ m ∈ G,
      ‖1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤
        2 * Real.exp (-(2 * delta ^ 2)) := by
    intro m hm
    have hmScale : delta ≤ (characterDistance n h m : ℝ) / n :=
      (mem_filter.mp hm).2
    let z : ZMod n := -((m : ZMod n)⁻¹ * h)
    have hbase := norm_one_add_stdAddChar_le n z
    have habs : |((z.valMinAbs : ℝ) / n)| =
        (characterDistance n h m : ℝ) / n := by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
      rw [show |(z.valMinAbs : ℝ)| = (z.valMinAbs.natAbs : ℝ) by simp]
      rfl
    have hsq : delta ^ 2 ≤ ((z.valMinAbs : ℝ) / n) ^ 2 := by
      have hxabs : delta ≤ |((z.valMinAbs : ℝ) / n)| := by
        rw [habs]
        exact hmScale
      simpa only [sq_abs] using
        (sq_le_sq₀ hdelta (abs_nonneg ((z.valMinAbs : ℝ) / n))).2 hxabs
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num))
  have hbase := norm_prod_le_two_pow_mul
    (M := M) (G := G)
    (fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))
    (Real.exp (-(2 * delta ^ 2))) hG (Real.exp_pos _).le hall hgood
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hhalf : (M.card : ℝ) ≤ 2 * (G.card : ℝ) := by
    exact_mod_cast hdisp
  nlinarith [sq_nonneg delta]

/-- Real-cardinality version of the product estimate.  This is the form
needed to apply `Dispersion.martin_inverse_dispersion`, whose parameter `C`
may be any real number strictly below `M.card`. -/
theorem characterProduct_le_of_real_scaled_dispersion {n : ℕ} [NeZero n]
    (M : Finset ℕ) (h : ZMod n) (delta C : ℝ) (hdelta : 0 ≤ delta)
    (hdisp : C ≤
      2 * ((M.filter fun m ↦
        delta ≤ (characterDistance n h m : ℝ) / n).card : ℝ)) :
    ‖M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤
      (2 : ℝ) ^ M.card * Real.exp (-(delta ^ 2 * C)) := by
  let G := M.filter fun m ↦ delta ≤ (characterDistance n h m : ℝ) / n
  have hG : G ⊆ M := filter_subset _ _
  have hall : ∀ m ∈ M,
      ‖1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤ 2 := by
    intro m _
    exact norm_one_add_stdAddChar_le_two _
  have hgood : ∀ m ∈ G,
      ‖1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤
        2 * Real.exp (-(2 * delta ^ 2)) := by
    intro m hm
    have hmScale : delta ≤ (characterDistance n h m : ℝ) / n :=
      (mem_filter.mp hm).2
    let z : ZMod n := -((m : ZMod n)⁻¹ * h)
    have hbase := norm_one_add_stdAddChar_le n z
    have habs : |((z.valMinAbs : ℝ) / n)| =
        (characterDistance n h m : ℝ) / n := by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
      rw [show |(z.valMinAbs : ℝ)| = (z.valMinAbs.natAbs : ℝ) by simp]
      rfl
    have hsq : delta ^ 2 ≤ ((z.valMinAbs : ℝ) / n) ^ 2 := by
      have hxabs : delta ≤ |((z.valMinAbs : ℝ) / n)| := by
        rw [habs]
        exact hmScale
      simpa only [sq_abs] using
        (sq_le_sq₀ hdelta (abs_nonneg ((z.valMinAbs : ℝ) / n))).2 hxabs
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num))
  have hbase := norm_prod_le_two_pow_mul
    (M := M) (G := G)
    (fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))
    (Real.exp (-(2 * delta ^ 2))) hG (Real.exp_pos _).le hall hgood
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hhalf : C ≤ 2 * (G.card : ℝ) := by
    simpa [G] using hdisp
  nlinarith [sq_nonneg delta]

/-- Sparse Fourier branch with a real lower bound `C` for twice the number
of dispersed factors. -/
theorem inverse_subset_sum_surjective_of_real_scaled_dispersion
    {n : ℕ} [NeZero n]
    (hn : 1 < n) (M : Finset ℕ) (delta C : ℝ) (hdelta : 0 ≤ delta)
    (hdisp : ∀ h : ZMod n, h ≠ 0 → C ≤
      2 * ((M.filter fun m ↦
        delta ≤ (characterDistance n h m : ℝ) / n).card : ℝ))
    (hdecay : 2 * Real.log n < delta ^ 2 * C) :
    ∀ a : ZMod n, ∃ K ⊆ M,
      K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  intro a
  apply Erdos285.FourierBound.inverse_subset_sum_surjective_of_exp_decay
    hn M a (2 * (delta ^ 2 * C))
  · intro h hh
    have hexp : -(2 * (delta ^ 2 * C)) / 2 = -(delta ^ 2 * C) := by ring
    rw [hexp]
    exact characterProduct_le_of_real_scaled_dispersion
      M h delta C hdelta (hdisp h hh)
  · have hpos : 0 < delta ^ 2 * C :=
      lt_trans (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))) hdecay
    nlinarith

/-- Sparse Fourier branch: scaled centered-inverse dispersion at every
nonzero frequency, together with Martin's quantitative decay threshold,
forces every residue to be an inverse subset sum. -/
theorem inverse_subset_sum_surjective_of_scaled_dispersion {n : ℕ} [NeZero n]
    (hn : 1 < n) (M : Finset ℕ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hdisp : ∀ h : ZMod n, h ≠ 0 →
      M.card ≤
        2 * (M.filter fun m ↦ delta ≤ (characterDistance n h m : ℝ) / n).card)
    (hdecay : 2 * Real.log n < delta ^ 2 * M.card) :
    ∀ a : ZMod n, ∃ K ⊆ M,
      K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  intro a
  apply Erdos285.FourierBound.inverse_subset_sum_surjective_of_martin_decay
    hn M a delta
  · intro h hh
    exact characterProduct_le_of_scaled_dispersion M h delta hdelta (hdisp h hh)
  · exact hdecay

/-- Bounded form consumed by the prime-power elimination step. -/
theorem bounded_inverse_subset_sum_of_scaled_dispersion {n C : ℕ} [NeZero n]
    (hn : 1 < n) (M : Finset ℕ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hcard : M.card ≤ C)
    (hdisp : ∀ h : ZMod n, h ≠ 0 →
      M.card ≤
        2 * (M.filter fun m ↦ delta ≤ (characterDistance n h m : ℝ) / n).card)
    (hdecay : 2 * Real.log n < delta ^ 2 * M.card) (a : ZMod n) :
    ∃ K ⊆ M, K.card ≤ C ∧
      K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  obtain ⟨K, hKM, hsum⟩ :=
    inverse_subset_sum_surjective_of_scaled_dispersion hn M delta hdelta hdisp hdecay a
  exact ⟨K, hKM, (card_le_card hKM).trans hcard, hsum⟩

/-- The lower bound on `B` in Martin's subset-sum lemma makes its displayed
cardinality expression strictly larger than the cardinality threshold in
the preceding dispersion lemma. -/
theorem martin_source_factor_gt_dispersion_factor
    {B L LL : ℝ} {k : ℕ} (hk : 0 < k)
    (hL : 0 < L) (hLL : 0 < LL)
    (hBsource :
      L ^ (((k - 1 : ℕ) : ℝ) / 2) /
          LL ^ ((k : ℝ) / 2) < B) :
    (L / LL) ^ k <
      B ^ (2 / 3 : ℝ) * L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
        LL ^ (((2 * k : ℕ) : ℝ) / 3) := by
  let A := L ^ (((k - 1 : ℕ) : ℝ) / 2) / LL ^ ((k : ℝ) / 2)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hpow : A ^ (2 / 3 : ℝ) < B ^ (2 / 3 : ℝ) :=
    Real.rpow_lt_rpow hA.le hBsource (by norm_num)
  have hrest : 0 < L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
      LL ^ (((2 * k : ℕ) : ℝ) / 3) := by positivity
  have heq : (L / LL) ^ k = A ^ (2 / 3 : ℝ) *
      (L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
        LL ^ (((2 * k : ℕ) : ℝ) / 3)) := by
    dsimp [A]
    rw [← Real.rpow_natCast]
    rw [Real.div_rpow hL.le hLL.le,
      Real.div_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul hL.le, ← Real.rpow_mul hLL.le]
    rw [div_mul_div_comm]
    rw [← Real.rpow_add hL, ← Real.rpow_add hLL]
    congr 2 <;>
      push_cast [Nat.cast_sub hk] <;>
      norm_num <;> ring
  calc
    (L / LL) ^ k = A ^ (2 / 3 : ℝ) *
        (L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
          LL ^ (((2 * k : ℕ) : ℝ) / 3)) := heq
    _ < B ^ (2 / 3 : ℝ) *
        (L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
          LL ^ (((2 * k : ℕ) : ℝ) / 3)) :=
      mul_lt_mul_of_pos_right hpow hrest
    _ = B ^ (2 / 3 : ℝ) * L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
        LL ^ (((2 * k : ℕ) : ℝ) / 3) := by ring

/-- Dense Cauchy--Davenport--Chowla branch, with the same bounded output
shape as the sparse theorem. -/
theorem bounded_inverse_subset_sum_of_card {n C : ℕ} [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n)
    (hdense : n ≤ M.card) (hcard : M.card ≤ C) (a : ZMod n) :
    ∃ K ⊆ M, K.card ≤ C ∧
      K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  obtain ⟨K, hKM, hsum⟩ :=
    Erdos285.Modular.inverse_subset_sum_surjective_of_card n M hcoprime hdense a
  exact ⟨K, hKM, (card_le_card hKM).trans hcard, hsum⟩

/-- **Martin's prescribed inverse subset-sum lemma** (published Lemma 11).

For every fixed positive `k` and all sufficiently large moduli `n`, a set
`M` satisfying Martin's displayed lower bounds and whose elements are
products of `k` distinct primes avoiding `n` represents every residue as a
sum of inverses of a subset.  The subset cardinality is bounded by any
given `D` bounding `M.card`.

The proof uses Chowla's dense branch when `n ≤ M.card`.  Otherwise it
instantiates `Dispersion.martin_inverse_dispersion` at a real number strictly
between Martin's cardinality bound and `M.card`, then applies the finite
Fourier product estimate above. -/
theorem eventually_bounded_inverse_subset_sum_of_martin_hypotheses
    (k : ℕ) (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : ℕ) (B : ℝ) (M : Finset ℕ),
      M.card ≤ D →
      0 < B →
      Real.log n ^ (((k - 1 : ℕ) : ℝ) / 2) /
          Real.log (Real.log n) ^ ((k : ℝ) / 2) < B →
      200 *
          (B ^ (2 / 3 : ℝ) *
              Real.log n ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
            Real.log (Real.log n) ^ (((2 * k : ℕ) : ℝ) / 3)) <
        M.card →
      (∀ m ∈ M, (m : ℝ) < B ∧
        Erdos285.Dispersion.IsKPrimeProductAway k n m) →
      ∀ a : ZMod n, ∃ K : Finset ℕ, K ⊆ M ∧ K.card ≤ D ∧
        K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  have hllTop : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [Erdos285.Dispersion.martin_inverse_dispersion k hk,
    eventually_gt_atTop (1 : ℕ),
    hllTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hMartin hn hnll
  intro D B M hMD hB hBsource hcardSource hM a
  have : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  by_cases hdense : n ≤ M.card
  · have hcoprime : ∀ m ∈ M, Nat.Coprime m n := by
      intro m hm
      exact Erdos285.Dispersion.isKPrimeProductAway_coprime (hM m hm).2
    exact bounded_inverse_subset_sum_of_card M hcoprime hdense hMD a
  · have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hn)
    let S : ℝ :=
      200 *
        (B ^ (2 / 3 : ℝ) *
            Real.log n ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
          Real.log (Real.log n) ^ (((2 * k : ℕ) : ℝ) / 3))
    let C : ℝ := (S + M.card) / 2
    have hSM : S < (M.card : ℝ) := by
      simpa [S] using hcardSource
    have hSC : S < C := by
      dsimp [C]
      linarith
    have hCM : C < (M.card : ℝ) := by
      dsimp [C]
      linarith
    have hSpos : 0 < S := by
      dsimp [S]
      positivity
    have hCpos : 0 < C := hSpos.trans hSC
    have hfactor := martin_source_factor_gt_dispersion_factor
      hk hlog hnll hBsource
    have hdispCard :
        200 * (Real.log n / Real.log (Real.log n)) ^ k < C := by
      calc
        200 * (Real.log n / Real.log (Real.log n)) ^ k < S := by
          dsimp [S]
          exact mul_lt_mul_of_pos_left hfactor (by norm_num)
        _ < C := hSC
    have hMlt : M.card < n := Nat.lt_of_not_ge hdense
    have hCn : C < (n : ℝ) := by
      have hMltR : (M.card : ℝ) < n := by exact_mod_cast hMlt
      exact hCM.trans hMltR
    have hDispersion := hMartin B C M hB hCpos hdispCard hCn hCM hM
    let delta : ℝ := Erdos285.Dispersion.dispersionThreshold n k B C
    have hdelta : 0 ≤ delta := by
      dsimp [delta, Erdos285.Dispersion.dispersionThreshold]
      positivity
    have hdecay : 2 * Real.log n < delta ^ 2 * C := by
      have hthreshold :=
        Erdos285.FourierBound.martin_published_cardinality_bound_implies_threshold
          hB hlog hnll hSC
      simpa [delta, S, Erdos285.Dispersion.dispersionThreshold, mul_comm] using
        hthreshold
    have hscaled : ∀ h : ZMod n, h ≠ 0 → C ≤
        2 * ((M.filter fun m ↦
          delta ≤ (characterDistance n h m : ℝ) / n).card : ℝ) := by
      intro h hh
      have hhpos : 0 < h.val := ZMod.val_pos.mpr hh
      have hfar := hDispersion h.val hhpos (ZMod.val_lt h)
      let far := M.filter fun m ↦
        Erdos285.Dispersion.dispersionThreshold n k B C <
          Erdos285.Dispersion.inverseDistance n h.val m
      let scaled := M.filter fun m ↦
        delta ≤ (characterDistance n h m : ℝ) / n
      have hsub : far ⊆ scaled := by
        intro m hm
        have hm' := mem_filter.mp hm
        apply mem_filter.mpr
        refine ⟨hm'.1, ?_⟩
        have hle := le_of_lt hm'.2
        simpa [far, scaled, delta, Erdos285.Dispersion.inverseDistance,
          characterDistance_eq_dispersion_centeredInverse] using hle
      have hcards : far.card ≤ scaled.card := card_le_card hsub
      have hfarC : C ≤ 2 * (far.card : ℝ) := by
        have hfar' : C / 2 ≤ (far.card : ℝ) := by
          simpa [far] using hfar
        linarith
      calc
        C ≤ 2 * (far.card : ℝ) := hfarC
        _ ≤ 2 * (scaled.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcards) (by norm_num)
        _ = 2 * ((M.filter fun m ↦
            delta ≤ (characterDistance n h m : ℝ) / n).card : ℝ) := by
          rfl
    obtain ⟨K, hKM, hsum⟩ :=
      inverse_subset_sum_surjective_of_real_scaled_dispersion
        hn M delta C hdelta hscaled hdecay a
    exact ⟨K, hKM, (card_le_card hKM).trans hMD, hsum⟩

end

end Erdos285.SubsetSum

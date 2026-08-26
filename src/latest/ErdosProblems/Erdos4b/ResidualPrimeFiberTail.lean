/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.ResidualPrimeFiberMertens
import BoundedGaps.Arithmetic.ReciprocalTotientPrefix

/-!
# Summing residual prime fibres over a cofactor interval

The pointwise residual-prime estimate contains the factor `1 / φ(m)`.
This file proves the multiplicative-interval estimate needed to sum it
without replacing the interval by a full prefix.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

/-- A quotient harmonic interval is controlled by the logarithm of the
original endpoint ratio, uniformly in the divisor. -/
theorem sum_inv_natDiv_interval_le_one_add_log_ratio
    {A B d : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) :
    (∑ k ∈ Finset.Ioc (A / d) (B / d), ((k : ℝ))⁻¹) ≤
      1 + Real.log ((B : ℝ) / A) := by
  have hquotient : A / d ≤ B / d := Nat.div_le_div_right hAB
  have hBdiv : 0 < B / d := Nat.div_pos hdB hd
  have hsum :
      (∑ k ∈ Finset.Ioc (A / d) (B / d), ((k : ℝ))⁻¹) =
        ((harmonic (B / d) : ℚ) : ℝ) -
          ((harmonic (A / d) : ℚ) : ℝ) := by
    have hsubset : Finset.Icc 1 (A / d) ⊆
        Finset.Icc 1 (B / d) := by
      intro k hk
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hk).1,
          (Finset.mem_Icc.mp hk).2.trans hquotient⟩
    have hdiff : Finset.Icc 1 (B / d) \ Finset.Icc 1 (A / d) =
        Finset.Ioc (A / d) (B / d) := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨hkOne, hkB⟩, hkNot⟩
        refine ⟨?_, hkB⟩
        by_contra hk
        apply hkNot
        exact ⟨hkOne, by omega⟩
      · rintro ⟨hkA, hkB⟩
        have hkPos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hkA
        refine ⟨⟨Nat.succ_le_iff.mpr hkPos, hkB⟩, ?_⟩
        rintro ⟨_hkOne, hkUpper⟩
        omega
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    rw [← hdiff, ← Finset.sum_sdiff hsubset]
    ring
  have hupper := harmonic_le_one_add_log (B / d)
  have hlower := log_add_one_le_harmonic (A / d)
  have hNmul :
      (((B / d : ℕ) : ℝ) * d) ≤ (B : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self B d
  have hAmul :
      (A : ℝ) < (((A / d + 1 : ℕ) : ℝ) * d) := by
    exact_mod_cast
      ((Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (A / d)))
  have hratio :
      (((B / d : ℕ) : ℝ) / ((A / d + 1 : ℕ) : ℝ)) ≤
        (B : ℝ) / A := by
    have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
    have hMreal : (0 : ℝ) < ((A / d + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ hMreal hAreal]
    calc
      ((B / d : ℕ) : ℝ) * A ≤
          ((B / d : ℕ) : ℝ) *
            (((A / d + 1 : ℕ) : ℝ) * d) :=
        mul_le_mul_of_nonneg_left hAmul.le (by positivity)
      _ = (((B / d : ℕ) : ℝ) * d) *
          ((A / d + 1 : ℕ) : ℝ) := by ring
      _ ≤ (B : ℝ) * ((A / d + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hNmul (by positivity)
  have hlogRatio :
      Real.log (((B / d : ℕ) : ℝ) /
          ((A / d + 1 : ℕ) : ℝ)) ≤
        Real.log ((B : ℝ) / A) := by
    have hNumPos : (0 : ℝ) < ((B / d : ℕ) : ℝ) := by
      exact_mod_cast hBdiv
    have hDenPos : (0 : ℝ) < ((A / d + 1 : ℕ) : ℝ) := by
      positivity
    have hBreal : (0 : ℝ) < (B : ℝ) := by
      exact_mod_cast hA.trans_le hAB
    have hAreal : (0 : ℝ) < (A : ℝ) := by
      exact_mod_cast hA
    apply Real.strictMonoOn_log.monotoneOn
    · exact div_pos hNumPos hDenPos
    · exact div_pos hBreal hAreal
    · exact hratio
  rw [hsum]
  calc
    ((harmonic (B / d) : ℚ) : ℝ) -
        ((harmonic (A / d) : ℚ) : ℝ) ≤
        (1 + Real.log (B / d : ℕ)) -
          Real.log (A / d + 1 : ℕ) := sub_le_sub hupper hlower
    _ = 1 + Real.log (((B / d : ℕ) : ℝ) /
          ((A / d + 1 : ℕ) : ℝ)) := by
      rw [Real.log_div]
      · ring
      · exact_mod_cast (Nat.ne_of_gt hBdiv)
      · positivity
    _ ≤ 1 + Real.log ((B : ℝ) / A) := by linarith

private def squarefreePositiveUpTo (B : ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter Squarefree

/-- Reciprocal totients have uniformly bounded mass on every fixed-ratio
multiplicative interval.  The explicit constant `4` comes from the complete
squarefree reciprocal-totient Euler coefficient. -/
theorem sum_inv_totient_Ioc_le_four_mul_one_add_log_ratio
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ioc A B, (Nat.totient n : ℝ)⁻¹) ≤
      4 * (1 + Real.log ((B : ℝ) / A)) := by
  classical
  let S : Finset (Σ _n : ℕ, ℕ) :=
    (Finset.Ioc A B).sigma (fun n => n.divisors.filter Squarefree)
  let T : Finset (Σ _d : ℕ, ℕ) :=
    (squarefreePositiveUpTo B).sigma
      (fun d => Finset.Ioc (A / d) (B / d))
  let f : (Σ _n : ℕ, ℕ) → (Σ _d : ℕ, ℕ) :=
    fun x => ⟨x.2, x.1 / x.2⟩
  let g : (Σ _d : ℕ, ℕ) → ℝ := fun x =>
    (1 : ℝ) / ((x.1 : ℝ) * Nat.totient x.1) *
      (1 / (x.2 : ℝ))
  have hinj : Set.InjOn f S := by
    intro x hx y hy hxy
    have hxmem := Finset.mem_sigma.mp hx
    have hymem := Finset.mem_sigma.mp hy
    have hd : x.2 = y.2 := congrArg Sigma.fst hxy
    have hquot : x.1 / x.2 = y.1 / y.2 := by
      exact congrArg Sigma.snd hxy
    rw [hd] at hquot
    apply Sigma.ext
    · calc
        x.1 = x.2 * (x.1 / x.2) :=
          (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hxmem.2).1)).symm
        _ = y.2 * (y.1 / y.2) := by rw [hd, hquot]
        _ = y.1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors
          (Finset.mem_filter.mp hymem.2).1)
    · simp [hd]
  have himage : S.image f ⊆ T := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxmem := Finset.mem_sigma.mp hx
    have hn := Finset.mem_Ioc.mp hxmem.1
    have hdmem := Finset.mem_filter.mp hxmem.2
    have hdvd := Nat.dvd_of_mem_divisors hdmem.1
    have hnpos : 0 < x.1 := lt_trans hA hn.1
    have hdpos : 0 < x.2 := Nat.pos_of_dvd_of_pos hdvd hnpos
    have hdle : x.2 ≤ x.1 := Nat.le_of_dvd hnpos hdvd
    have hdlB : x.2 ≤ B := hdle.trans hn.2
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hdpos, hdlB⟩, hdmem.2⟩, ?_⟩
    apply Finset.mem_Ioc.mpr
    constructor
    · change A / x.2 < x.1 / x.2
      rw [Nat.div_lt_iff_lt_mul hdpos]
      rw [Nat.div_mul_cancel hdvd]
      exact hn.1
    · exact Nat.div_le_div_right hn.2
  have hlogNonneg : 0 ≤ Real.log ((B : ℝ) / A) := by
    apply Real.log_nonneg
    rw [one_le_div₀]
    · exact_mod_cast hAB
    · exact_mod_cast hA
  calc
    (∑ n ∈ Finset.Ioc A B, (Nat.totient n : ℝ)⁻¹) =
        ∑ n ∈ Finset.Ioc A B,
          ∑ d ∈ n.divisors.filter Squarefree,
            (1 : ℝ) / ((n : ℝ) * Nat.totient d) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact BoundedGaps.Maynard.inv_totient_eq_sum_squarefree_divisors
        (lt_trans hA (Finset.mem_Ioc.mp hn).1)
    _ = ∑ x ∈ S,
        (1 : ℝ) / ((x.1 : ℝ) * Nat.totient x.2) := by
      unfold S
      rw [Finset.sum_sigma']
    _ = ∑ x ∈ S, g (f x) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxmem := Finset.mem_sigma.mp hx
      have hdvd := Nat.dvd_of_mem_divisors
        (Finset.mem_filter.mp hxmem.2).1
      have hprodR : (x.1 : ℝ) =
          (x.2 : ℝ) * (x.1 / x.2 : ℕ) := by
        exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
      dsimp [g, f]
      rw [hprodR]
      ring
    _ = ∑ z ∈ S.image f, g z := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    _ ≤ ∑ z ∈ T, g z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro z hz hznot
      unfold g
      positivity
    _ = ∑ d ∈ squarefreePositiveUpTo B,
        ((1 : ℝ) / ((d : ℝ) * Nat.totient d)) *
          (∑ k ∈ Finset.Ioc (A / d) (B / d),
            (1 / (k : ℝ))) := by
      unfold T
      rw [← Finset.sum_sigma' (squarefreePositiveUpTo B)
        (fun d => Finset.Ioc (A / d) (B / d))
        (fun d k => g ⟨d, k⟩)]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [g]
      rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ squarefreePositiveUpTo B,
        ((1 : ℝ) / ((d : ℝ) * Nat.totient d)) *
          (1 + Real.log ((B : ℝ) / A)) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdData := Finset.mem_filter.mp hdmem
      have hdInterval := Finset.mem_Icc.mp hdData.1
      apply mul_le_mul_of_nonneg_left
      · simpa only [one_div] using
          (sum_inv_natDiv_interval_le_one_add_log_ratio hA hAB
            hdInterval.1 hdInterval.2)
      positivity
    _ = BoundedGaps.Maynard.squarefreeInvNatTotientSum B *
          (1 + Real.log ((B : ℝ) / A)) := by
      rw [← Finset.sum_mul]
      unfold squarefreePositiveUpTo
      rw [show (∑ d ∈ (Finset.Icc 1 B).filter Squarefree,
          (1 : ℝ) / ((d : ℝ) * Nat.totient d)) =
          BoundedGaps.Maynard.squarefreeInvNatTotientSum B by
        unfold BoundedGaps.Maynard.squarefreeInvNatTotientSum
        rw [Finset.sum_filter]]
    _ ≤ 4 * (1 + Real.log ((B : ℝ) / A)) := by
      exact mul_le_mul_of_nonneg_right
        (BoundedGaps.Maynard.squarefreeInvNatTotientSum_le_four B)
        (by linarith)

/-- The quotient occurring in the prime-counting main term cancels the
cofactor at most to the ambient endpoint `U`. -/
theorem natDiv_cast_mul_le (U m : ℕ) :
    (((U / m : ℕ) : ℝ) * m) ≤ (U : ℝ) := by
  exact_mod_cast Nat.div_mul_le_self U m

/-- Sum the complete principal term supplied by
`exists_residualPrimeFiber_beta_mertens_upper_bound` over a multiplicative
cofactor interval.  A uniform lower bound `L` for `log (U / m)` is kept
explicit so that the later parameter assembly can substitute `L ≍ log x`.
-/
theorem sum_residualPrime_principalTerm_Ioc_le
    {A B U y : ℕ} {Cπ CV eta L : ℝ}
    (hA : 0 < A) (hAB : A ≤ B)
    (hCπ : 0 ≤ Cπ) (hCV : 0 ≤ CV) (heta : 0 ≤ eta)
    (hL : 0 < L) (hylog : 0 < Real.log (y : ℝ))
    (hlog : ∀ m ∈ Finset.Ioc A B,
      L ≤ Real.log ((U / m : ℕ) : ℝ)) :
    (∑ m ∈ Finset.Ioc A B,
      (Cπ * ((U / m : ℕ) : ℝ) /
          Real.log ((U / m : ℕ) : ℝ)) *
        ((1 + eta) *
          (CV * ((m : ℝ) / Nat.totient m) /
            Real.log (y : ℝ)))) ≤
      (Cπ * (1 + eta) * CV * (U : ℝ) /
          (L * Real.log (y : ℝ))) *
        (4 * (1 + Real.log ((B : ℝ) / A))) := by
  have hcoef : 0 ≤ Cπ * (1 + eta) * CV /
      (L * Real.log (y : ℝ)) := by positivity
  calc
    (∑ m ∈ Finset.Ioc A B,
      (Cπ * ((U / m : ℕ) : ℝ) /
          Real.log ((U / m : ℕ) : ℝ)) *
        ((1 + eta) *
          (CV * ((m : ℝ) / Nat.totient m) /
            Real.log (y : ℝ)))) ≤
        ∑ m ∈ Finset.Ioc A B,
          (Cπ * (1 + eta) * CV * (U : ℝ) /
            (L * Real.log (y : ℝ))) *
              (Nat.totient m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      have hmPos : 0 < m := lt_trans hA (Finset.mem_Ioc.mp hm).1
      have hφPos : (0 : ℝ) < Nat.totient m := by
        exact_mod_cast Nat.totient_pos.mpr hmPos
      have hlogLower := hlog m hm
      have hlogPos : 0 < Real.log ((U / m : ℕ) : ℝ) :=
        hL.trans_le hlogLower
      have hquotNonneg : (0 : ℝ) ≤ (U / m : ℕ) := by positivity
      have hdiv :
          ((U / m : ℕ) : ℝ) /
              Real.log ((U / m : ℕ) : ℝ) ≤
            ((U / m : ℕ) : ℝ) / L := by
        rw [div_le_div_iff₀ hlogPos hL]
        exact mul_le_mul_of_nonneg_left hlogLower hquotNonneg
      have hfirst :
          Cπ * ((U / m : ℕ) : ℝ) /
              Real.log ((U / m : ℕ) : ℝ) ≤
            Cπ * (((U / m : ℕ) : ℝ) / L) := by
        simpa only [mul_div_assoc] using
          mul_le_mul_of_nonneg_left hdiv hCπ
      have hsecond : 0 ≤
          (1 + eta) *
            (CV * ((m : ℝ) / Nat.totient m) /
              Real.log (y : ℝ)) := by positivity
      calc
        (Cπ * ((U / m : ℕ) : ℝ) /
            Real.log ((U / m : ℕ) : ℝ)) *
          ((1 + eta) *
            (CV * ((m : ℝ) / Nat.totient m) /
              Real.log (y : ℝ))) ≤
            (Cπ * (((U / m : ℕ) : ℝ) / L)) *
          ((1 + eta) *
            (CV * ((m : ℝ) / Nat.totient m) /
              Real.log (y : ℝ))) :=
          mul_le_mul_of_nonneg_right hfirst hsecond
        _ = (Cπ * (1 + eta) * CV /
              (L * Real.log (y : ℝ))) *
            ((((U / m : ℕ) : ℝ) * m) *
              (Nat.totient m : ℝ)⁻¹) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
            div_eq_mul_inv]
          ring
        _ ≤ (Cπ * (1 + eta) * CV /
              (L * Real.log (y : ℝ))) *
            ((U : ℝ) * (Nat.totient m : ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right (natDiv_cast_mul_le U m)
              (inv_nonneg.mpr hφPos.le)
          · exact hcoef
        _ = (Cπ * (1 + eta) * CV * (U : ℝ) /
              (L * Real.log (y : ℝ))) *
            (Nat.totient m : ℝ)⁻¹ := by ring
    _ = (Cπ * (1 + eta) * CV * (U : ℝ) /
          (L * Real.log (y : ℝ))) *
        (∑ m ∈ Finset.Ioc A B,
          (Nat.totient m : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ (Cπ * (1 + eta) * CV * (U : ℝ) /
          (L * Real.log (y : ℝ))) *
        (4 * (1 + Real.log ((B : ℝ) / A))) := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_inv_totient_Ioc_le_four_mul_one_add_log_ratio hA hAB
      · positivity

/-- Even cofactors in a multiplicative interval.  The actual Rankin
construction uses a further smoothness restriction, which is a subset of
this set and therefore only decreases the nonnegative principal mass. -/
def residualEvenCofactors (A B : ℕ) : Finset ℕ :=
  (Finset.Ioc A B).filter Even

@[simp] theorem mem_residualEvenCofactors {A B m : ℕ} :
    m ∈ residualEvenCofactors A B ↔ A < m ∧ m ≤ B ∧ Even m := by
  simp [residualEvenCofactors, and_assoc]

/-- End-to-end summation of the finite beta-sieve/Mertens fibre theorem.
All pointwise sieve-range conditions are collected in one explicit
hypothesis; the two Bombieri--Vinogradov losses remain as a displayed finite
sum, ready for the final parameter estimates. -/
theorem exists_sum_residualPrimeFiber_beta_mertens_upper_bound :
    ∃ Aβ Cπ CV : ℝ,
      1 ≤ Aβ ∧ 0 < Cπ ∧ 0 < CV ∧
      ∀ {theta Bexp CBV L : ℝ}
        {X₀ U y z S Aco Bco : ℕ},
        0 < Aco → Aco ≤ Bco → 0 < L → 1 < y → 101 ≤ S →
        Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 →
        BoundedGaps.Maynard.PrimeLevelWitness theta Bexp CBV X₀ →
        X₀ ≤ z →
        y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta z →
        (∀ m ∈ residualEvenCofactors Aco Bco,
          z ≤ U / m ∧ X₀ ≤ U / m ∧
          y ^ S ≤ BoundedGaps.Maynard.modulusCutoff theta (U / m) ∧
          2 ≤ U / m) →
        (∀ m ∈ Finset.Ioc Aco Bco,
          L ≤ Real.log ((U / m : ℕ) : ℝ)) →
        let eta := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        (∑ m ∈ residualEvenCofactors Aco Bco,
          ((residualPrimeFiber U y z m).card : ℝ)) ≤
          (Cπ * (1 + eta) * CV * (U : ℝ) /
              (L * Real.log (y : ℝ))) *
            (4 * (1 + Real.log ((Bco : ℝ) / Aco))) +
          ∑ m ∈ residualEvenCofactors Aco Bco,
            (CBV * ((U / m : ℕ) : ℝ) /
                Real.rpow (Real.log ((U / m : ℕ) : ℝ)) Bexp +
              CBV * (z : ℝ) /
                Real.rpow (Real.log (z : ℝ)) Bexp) := by
  obtain ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, hpoint⟩ :=
    exists_residualPrimeFiber_beta_mertens_upper_bound
  refine ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, ?_⟩
  intro theta Bexp CBV L X₀ U y z S Aco Bco hAco hABco hL hy hS
    hlogAβ hw hXz hDz hparams hlog
  dsimp only
  have heta : 0 ≤
      (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
    positivity
  have hylog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have hmainFull := sum_residualPrime_principalTerm_Ioc_le
    hAco hABco hCπ.le hCV.le heta hL hylog hlog
  have hsubset : residualEvenCofactors Aco Bco ⊆
      Finset.Ioc Aco Bco := Finset.filter_subset _ _
  have hmainSubset :
      (∑ m ∈ residualEvenCofactors Aco Bco,
        (Cπ * ((U / m : ℕ) : ℝ) /
            Real.log ((U / m : ℕ) : ℝ)) *
          ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (CV * ((m : ℝ) / Nat.totient m) /
              Real.log (y : ℝ)))) ≤
        (Cπ *
              (1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              CV * (U : ℝ) /
            (L * Real.log (y : ℝ))) *
          (4 * (1 + Real.log ((Bco : ℝ) / Aco))) := by
    calc
      (∑ m ∈ residualEvenCofactors Aco Bco,
        (Cπ * ((U / m : ℕ) : ℝ) /
            Real.log ((U / m : ℕ) : ℝ)) *
          ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (CV * ((m : ℝ) / Nat.totient m) /
              Real.log (y : ℝ)))) ≤
          ∑ m ∈ Finset.Ioc Aco Bco,
            (Cπ * ((U / m : ℕ) : ℝ) /
                Real.log ((U / m : ℕ) : ℝ)) *
              ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
                (CV * ((m : ℝ) / Nat.totient m) /
                  Real.log (y : ℝ))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro m hm hmnot
        have hmPos : 0 < m := lt_trans hAco (Finset.mem_Ioc.mp hm).1
        have hlogPos : 0 < Real.log ((U / m : ℕ) : ℝ) :=
          hL.trans_le (hlog m hm)
        have hφPos : (0 : ℝ) < Nat.totient m := by
          exact_mod_cast Nat.totient_pos.mpr hmPos
        positivity
      _ ≤ _ := hmainFull
  have hpointwise : ∀ m ∈ residualEvenCofactors Aco Bco,
      ((residualPrimeFiber U y z m).card : ℝ) ≤
        (Cπ * ((U / m : ℕ) : ℝ) /
            Real.log ((U / m : ℕ) : ℝ)) *
          ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            (CV * ((m : ℝ) / Nat.totient m) /
              Real.log (y : ℝ))) +
        CBV * ((U / m : ℕ) : ℝ) /
            Real.rpow (Real.log ((U / m : ℕ) : ℝ)) Bexp +
          CBV * (z : ℝ) /
            Real.rpow (Real.log (z : ℝ)) Bexp := by
    intro m hm
    have hmData := mem_residualEvenCofactors.mp hm
    have hmPos : 0 < m := lt_trans hAco hmData.1
    have hp := hparams m hm
    exact hpoint hmPos hmData.2.2 hp.1 hy hS hlogAβ hw hp.2.1 hXz
      hp.2.2.1 hDz hp.2.2.2
  calc
    (∑ m ∈ residualEvenCofactors Aco Bco,
        ((residualPrimeFiber U y z m).card : ℝ)) ≤
        ∑ m ∈ residualEvenCofactors Aco Bco,
          ((Cπ * ((U / m : ℕ) : ℝ) /
              Real.log ((U / m : ℕ) : ℝ)) *
            ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (CV * ((m : ℝ) / Nat.totient m) /
                Real.log (y : ℝ))) +
          (CBV * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) Bexp +
            CBV * (z : ℝ) /
              Real.rpow (Real.log (z : ℝ)) Bexp)) := by
      apply Finset.sum_le_sum
      intro m hm
      simpa only [add_assoc] using hpointwise m hm
    _ = (∑ m ∈ residualEvenCofactors Aco Bco,
          (Cπ * ((U / m : ℕ) : ℝ) /
              Real.log ((U / m : ℕ) : ℝ)) *
            ((1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (CV * ((m : ℝ) / Nat.totient m) /
                Real.log (y : ℝ)))) +
        ∑ m ∈ residualEvenCofactors Aco Bco,
          (CBV * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) Bexp +
            CBV * (z : ℝ) /
              Real.rpow (Real.log (z : ℝ)) Bexp) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (Cπ *
              (1 + (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              CV * (U : ℝ) /
            (L * Real.log (y : ℝ))) *
          (4 * (1 + Real.log ((Bco : ℝ) / Aco))) +
        ∑ m ∈ residualEvenCofactors Aco Bco,
          (CBV * ((U / m : ℕ) : ℝ) /
              Real.rpow (Real.log ((U / m : ℕ) : ℝ)) Bexp +
            CBV * (z : ℝ) /
              Real.rpow (Real.log (z : ℝ)) Bexp) :=
      add_le_add hmainSubset le_rfl

end

end Erdos4b

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import UnitFractions.MainResults

/-!
# A stable good-condition bound for the Croot extraction

The local Croot--Bloom argument uses `2/3` only to leave a positive gap below
twice `35/100`.  The proof below records the same argument with `17/25`.
This small amount of slack permits adjoining a fixed-divisibility marker whose
prime-power reciprocal mass is negligible compared with `log log N`.
-/

open Filter Real
open scoped BigOperators Topology ArithmeticFunction.omega

namespace Erdos284.Croot

open UnitFractions
open _root_.Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem force_good_properties_relaxed :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℝ, ∀ A ⊆ Finset.range (N + 1),
      0 < M → M ≤ N → (N : ℝ) ≤ M ^ 2 → 0 ∉ A →
      (∀ n ∈ A, M ≤ (n : ℝ)) → arith_regular N A →
      (∀ q ∈ ppowers_in_set A, (log N) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A q) →
      (ppower_rec_sum A : ℝ) ≤ (17 / 25) * log (log N) →
      good_condition A (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) ((M : ℝ) / log N)
        (M / (2 * (log N) ^ (1 / 100 : ℝ))) := by
  classical
  let c := (35 : ℝ) / 100
  filter_upwards
    [ eventually_gt_atTop (1 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((2 : ℝ) / (1 / 2)))
    , rec_pp_sum_close
    , find_good_x ] with
    N hlarge hlarge0 hlarge4 hrecN hgoodx M A hA h0M hMN hNM h0A hMA hreg hreclocal hpprecA
  dsimp at hlarge0
  have hlarge3 : 0 < log (log N) := by
    refine lt_of_lt_of_le ?_ hlarge4
    norm_num1
  have hlarge1 : 1 ≤ M * N ^ ((-2 : ℝ) / log (log N)) := by
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_trans zero_lt_one hlarge)
    have hexp : (2 : ℝ) / log (log N) ≤ (1 : ℝ) / 2 := by
      have hlarge4' := hlarge4
      norm_num at hlarge4'
      refine (div_le_iff₀ hlarge3).2 ?_
      nlinarith
    have hpow : (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ M := by
      calc
        (N : ℝ) ^ ((2 : ℝ) / log (log N)) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast le_of_lt hlarge) hexp
        _ ≤ M := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_iff.mpr ⟨le_of_lt h0M, hNM⟩
    have hneg : (-2 : ℝ) / log (log N) = -((2 : ℝ) / log (log N)) := by ring
    rw [hneg, Real.rpow_neg, div_eq_mul_inv]
    · exact (one_le_div (Real.rpow_pos_of_pos hNpos _)).2 hpow
    · exact Nat.cast_nonneg N
  have hlarge2 : M * N ^ ((-2 : ℝ) / log (log N)) ≤ N := by
    have hrpow : N ^ ((-2 : ℝ) / log (log N)) ≤ (1 : ℝ) := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast le_of_lt hlarge
      · apply div_nonpos_of_nonpos_of_nonneg
        · rw [neg_nonpos]
          exact zero_le_two
        · exact le_of_lt hlarge3
    calc
      _ ≤ M := by simpa [mul_one] using mul_le_mul_of_nonneg_left hrpow h0M.le
      _ ≤ N := hMN
  rw [good_condition]
  intro t I hI
  refine or_iff_not_imp_left.2 ?_
  intro hP
  let D := interval_rare_ppowers I A (M / (2 * log N ^ ((1 : ℝ) / 100)))
  let K := M / (2 * log N ^ ((1 : ℝ) / 100))
  by_cases hDne : D.Nonempty
  · rcases hDne with ⟨x1, hx1⟩
    have hlocal :
        ∀ q ∈ D, ∃ x ∈ I, ((q : ℤ) ∣ x) ∧
            ((35 : ℝ) / 100) * log (log N) ≤
            (((ppowers_in_set A).filter fun n : ℕ => (n : ℤ) ∣ x).sum
              fun r : ℕ => (1 / r : ℝ)) := by
      intro q hq
      specialize hgoodx M A hA h0M hMN h0A hMA hreg t I q
        (interval_rare_ppowers_subset I K hq) hI
      have hgoodq :
          (1 : ℝ) / (2 * log N ^ ((1 : ℝ) / 100)) ≤
            rec_sum_local (A.filter fun n => ∃ x ∈ I, ((n : ℤ) ∣ x)) q := by
        refine good_d N M (1 / (2 * log N ^ ((1 : ℝ) / 100))) A hA h0M hMA ?_ I q ?_
        · intro q hq'
          rw [two_mul, one_div, ← inv_div_left, add_halves, ← Real.rpow_neg]
          · exact hreclocal q hq'
          · exact le_of_lt hlarge0
        · rw [← div_eq_mul_one_div]
          exact hq
      exact hgoodx hgoodq
    clear hgoodx
    choose! f hf using hlocal
    use f x1
    have hfcopy := hf
    specialize hf x1 hx1
    refine ⟨hf.1, ?_⟩
    intro q hq
    specialize hfcopy q hq
    by_cases htwoxs : f q = f x1
    · obtain hf' := hfcopy.2.1
      rw [htwoxs] at hf'
      exact hf'
    · exfalso
      let S1 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f x1
      let S2 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f q
      let S12 : Finset ℕ := (ppowers_in_set A).filter fun n => (n : ℤ) ∣ f q ∧ (n : ℤ) ∣ f x1
      have hfS1 : c * log (log N) ≤ S1.sum (fun r => (1 / r : ℝ)) := by
        simpa [S1, c] using hf.2.2
      have hfcopyS2 : c * log (log N) ≤ S2.sum (fun r => (1 / r : ℝ)) := by
        simpa [S2, c] using hfcopy.2.2
      have hsum1 :
          2 * c * log (log N) ≤
            S1.sum (fun r => (1 / r : ℝ)) + S2.sum (fun r => (1 / r : ℝ)) := by
        rw [two_mul, add_mul]
        exact add_le_add hfS1 hfcopyS2
      have hsum2 :
          S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) -
              S12.sum (fun r => (1 : ℝ) / r) ≤ ppower_rec_sum A := by
        have hS12 : S1 ∩ S2 = S12 := by
          ext r
          simp [S1, S2, S12, and_left_comm, and_assoc, and_comm]
        have hEq :
            S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) -
                S12.sum (fun r => (1 : ℝ) / r) =
              (S1 ∪ S2).sum (fun r => (1 : ℝ) / r) := by
          rw [← hS12]
          linarith [Finset.sum_union_inter (s₁ := S1) (s₂ := S2) (f := fun r => (1 : ℝ) / r)]
        rw [ppower_rec_sum]
        push_cast
        rw [hEq]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro r hr
          rw [Finset.mem_union] at hr
          cases hr with
          | inl hr1 => exact (Finset.mem_filter.mp hr1).1
          | inr hr2 => exact (Finset.mem_filter.mp hr2).1
        · intro i _ _
          rw [one_div_nonneg]
          exact Nat.cast_nonneg i
      have hsum3 :
          S1.sum (fun r => (1 : ℝ) / r) + S2.sum (fun r => (1 : ℝ) / r) - ppower_rec_sum A ≤
            S12.sum (fun r => (1 : ℝ) / r) := by linarith
      have hsum4 :
          ((1 : ℝ) / 500) * log (log N) ≤ S12.sum (fun r => (1 : ℝ) / r) := by
        have hsilly : c = 35 / 100 := by rfl
        nlinarith
      have hqx1close : |(f q : ℝ) - f x1| ≤ N := by
        apply @le_trans _ _ _
          (((⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) -
            ⌈t - M * N ^ ((-2 : ℝ) / log (log N)) / 2⌉) N
        · apply two_in_Icc
          · rw [← hI]
            exact hfcopy.1
          · rw [← hI]
            exact hf.1
        · have hfloor :
              ((⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) : ℝ) ≤
                t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 := Int.floor_le _
          have hceil :
              t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
                (⌈t - M * N ^ ((-2 : ℝ) / log (log N)) / 2⌉ : ℤ) := Int.le_ceil _
          nlinarith
      specialize hrecN (f q) (f x1) htwoxs hqx1close
      rw [lt_iff_not_ge] at hrecN
      apply hrecN
      refine le_trans hsum4 ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro r hr
        simp only [S12, Finset.mem_filter] at hr
        rw [ppowers_in_set, Finset.mem_biUnion] at hr
        rcases hr.1 with ⟨m, hm1, hm2⟩
        rw [Finset.mem_filter] at hm2
        rw [Finset.mem_filter]
        refine ⟨?_, hm2.2.1, hr.2⟩
        rw [Finset.mem_range]
        exact lt_of_le_of_lt (Nat.divisor_le hm2.1) (by
          rw [← Finset.mem_range]
          exact hA hm1)
      · intro i _ _
        exact div_nonneg zero_le_one (Nat.cast_nonneg i)
  · have hIne : I.Nonempty := by
      rw [hI, Finset.nonempty_Icc]
      rw [Int.ceil_le]
      have hfloor : t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 <
          (⌊t + M * N ^ ((-2 : ℝ) / log (log N)) / 2⌋ : ℤ) := Int.sub_one_lt_floor _
      have hgap :
          t - M * N ^ ((-2 : ℝ) / log (log N)) / 2 ≤
            t + M * N ^ ((-2 : ℝ) / log (log N)) / 2 - 1 := by nlinarith
      exact le_trans hgap (le_of_lt hfloor)
    rcases hIne with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro q hq
    exfalso
    apply hDne
    exact ⟨q, hq⟩

end

end Erdos284.Croot

#print axioms Erdos284.Croot.force_good_properties_relaxed

import Util.Bernays.ClassSieveUpper
import Util.Bernays.ReciprocalSieve

/-!
# Divergence of split primes outside a proper ideal-class subgroup

The proof compares a uniform lattice lower bound with a covering by prime-ideal
divisors. It applies to nonmaximal orders as well as maximal orders.
-/

open Filter Topology

namespace Bernays

noncomputable def badSplitPrimeWeight {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)) → SplitPrime d b → ℝ := by
  classical
  letI := quadraticOrderIsDomain hD
  exact fun H s => if s.idealClass hD ∉ H then (s.1 : ℝ)⁻¹ else 0

theorem badSplitPrimeWeight_nonneg {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)), ∀ s : SplitPrime d b,
      0 ≤ badSplitPrimeWeight hD H s := by
  let := quadraticOrderIsDomain hD
  intro H s
  unfold badSplitPrimeWeight
  split_ifs <;> positivity

theorem splitPrime_inv_le_half {d b : ℤ} (s : SplitPrime d b) : (s.1 : ℝ)⁻¹ ≤ 1 / 2 := by
  have hq : (2 : ℝ) ≤ s.1 := by exact_mod_cast s.2.1.two_le
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hq

theorem badSplitPrimeWeight_headProduct {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)),
      Summable (badSplitPrimeWeight hD H) → ∀ S : Finset (SplitPrime d b),
      (∀ s ∈ S, s.idealClass hD ∉ H) →
      Real.exp (-2 * ∑' s, badSplitPrimeWeight hD H s) ≤
        ∏ s ∈ S, (1 - (s.1 : ℝ)⁻¹) := by
  let := quadraticOrderIsDomain hD
  intro H hsum S hS
  have hhalf (s : SplitPrime d b) : badSplitPrimeWeight hD H s ≤ 1 / 2 := by
    unfold badSplitPrimeWeight
    split_ifs <;> first | exact splitPrime_inv_le_half s | norm_num
  have h := exp_neg_two_tsum_le_prod_one_sub (badSplitPrimeWeight hD H)
    (badSplitPrimeWeight_nonneg hD H) hhalf hsum S
  convert h using 1
  apply Finset.prod_congr rfl
  intro s hs
  simp only [badSplitPrimeWeight, if_pos (hS s hs)]

theorem cast_prod_splitPrime_sub_one_sq {d b : ℤ} (S : Finset (SplitPrime d b)) :
    ((∏ s ∈ S, (s.1 - 1) ^ 2 : ℕ) : ℝ) =
      (splitSieveModulus S : ℝ) ^ 2 * (∏ s ∈ S, (1 - (s.1 : ℝ)⁻¹)) ^ 2 := by
  have hterm (s : SplitPrime d b) : (((s.1 - 1) ^ 2 : ℕ) : ℝ) =
      (s.1 : ℝ) ^ 2 * (1 - (s.1 : ℝ)⁻¹) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub s.2.1.one_le, Nat.cast_one]
    have hq : (s.1 : ℝ) ≠ 0 := by exact_mod_cast s.2.1.ne_zero
    field_simp [hq]
  rw [Nat.cast_prod]
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow]
  simp only [splitSieveModulus, Nat.cast_prod]

theorem sieve_bounds_contradiction {A Q L B U K Y E t : ℝ}
    (hQ : 0 < Q) (hL : 0 < L) (hB : 0 < B) (hU : 0 < U) (hK : 0 < K) (hE : 0 < E)
    (hhead : E ^ 2 * Q ^ 2 ≤ A)
    (hlower : A * L ^ 2 ≤ U * Y)
    (hupper : Y ≤ 2 * B * (K * Q ^ 2 * L ^ 2) * t)
    (ht : t < E ^ 2 / (4 * U * B * K)) : False := by
  have hscale : U * (2 * B * (K * Q ^ 2 * L ^ 2) * (E ^ 2 / (4 * U * B * K))) =
      (E ^ 2 * Q ^ 2 * L ^ 2) / 2 := by
    field_simp [hU.ne', hB.ne', hK.ne']
    ring
  have hlt := mul_lt_mul_of_pos_left ht
    (by positivity : 0 < 2 * B * (K * Q ^ 2 * L ^ 2))
  have hlt' := mul_lt_mul_of_pos_left (hupper.trans_lt hlt) hU
  rw [hscale] at hlt'
  have hh := mul_le_mul_of_nonneg_right hhead (sq_nonneg L)
  have hp : 0 < E ^ 2 * Q ^ 2 * L ^ 2 := by positivity
  linarith

theorem not_summable_badSplitPrimeWeight {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)), H ≠ ⊤ →
      ¬ Summable (badSplitPrimeWeight hD H) := by
  classical
  let := quadraticOrderIsDomain hD
  intro H hH hsum
  let O := QuadraticAlgebra ℤ d b
  obtain ⟨B, hB, hbound⟩ := exists_uniform_natCard_idealClassBall_le hD
  have hex : ∃ C : ClassGroup O, C ∉ H := by
    by_contra! h
    apply hH
    ext C
    simp [h C]
  obtain ⟨C, hC⟩ := hex
  obtain ⟨I, hI⟩ := InvertibleIdeal.idealClass_surjective C⁻¹
  let m := (I : Ideal O).cardQuot
  let M := discriminantLevel (b ^ 2 + 4 * d) * m
  let μ := classSieveMultiplier I M
  have hm : 0 < m := I.cardQuot_pos
  have hM : 0 < M := Nat.mul_pos (discriminantLevel_pos hD.ne) hm
  have hMcast : (M : O) ≠ 0 := by
    intro hz
    change (M : QuadraticAlgebra ℤ d b) = 0 at hz
    have hr := congrArg QuadraticAlgebra.re hz
    have : (M : ℤ) = 0 := by simpa using hr
    exact hM.ne' (by exact_mod_cast this)
  obtain ⟨c, _, hc⟩ := InvertibleIdeal.exists_generator_mod_mul I (Ideal.span {(M : O)})
    (by
      intro hbot
      have hmembot : (M : O) ∈ (⊥ : Ideal O) := hbot ▸ Ideal.mem_span_singleton_self (M : O)
      exact hMcast (Ideal.mem_bot.mp hmembot))
  let U := Nat.card Oˣ
  let := finite_quadraticOrder_units hD
  have hU : 0 < U := Nat.card_pos
  let K := classSieveScale d b μ
  have hK : 0 < K := by dsimp only [K, classSieveScale]; positivity
  let E := Real.exp (-2 * ∑' s, badSplitPrimeWeight hD H s)
  have hE : 0 < E := Real.exp_pos _
  let ε : ℝ := E ^ 2 / (4 * U * B * K)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨F, hF⟩ := summable_nonneg_finite_tail (badSplitPrimeWeight hD H)
    (badSplitPrimeWeight_nonneg hD H) hsum hε
  let S := F.filter fun s => s.idealClass hD ∉ H ∧ ¬s.1 ∣ μ
  have hS (s : SplitPrime d b) (hs : s ∈ S) : s.idealClass hD ∉ H ∧ ¬s.1 ∣ μ :=
    (Finset.mem_filter.mp hs).2
  have hhead := badSplitPrimeWeight_headProduct hD H hsum S (fun s hs => (hS s hs).1)
  let L := (c : O).re.natAbs + (c : O).im.natAbs + 1
  have hrL : (c : O).re.natAbs < L := by omega
  have hiL : (c : O).im.natAbs < L := by omega
  have hL : 0 < L := by omega
  let Q := splitSieveModulus S
  have hQ : 0 < Q := splitSieveModulus_pos S
  let N := K * Q ^ 2 * L ^ 2
  let A := ∏ s ∈ S, (s.1 - 1) ^ 2
  have hlower : A * L ^ 2 ≤ U * Nat.card (ClassSieveBall C N M S) := by
    have h := classSieve_lower hD I M hM c hc S (fun s hs => (hS s hs).2) L hrL hiL
    simpa only [hI, inv_inv] using h
  let T := (boundedSplitPrimes d b N).filter fun s =>
    s.idealClass hD ∉ H ∧ ¬s.1 ∣ μ ∧ s ∉ S
  have hT (s : SplitPrime d b) (hs : s ∈ T) :
      s.idealClass hD ∉ H ∧ ¬s.1 ∣ μ ∧ s ∉ S := (Finset.mem_filter.mp hs).2
  have hcover : ∀ J : ClassSieveBall C N M S, ∃ s ∈ T, ∃ e : Bool,
      (J.1.1 : Ideal O) ≤ (s.ideal hD e : Ideal O) := by
    intro J
    have hμM (q : ℕ) (hq : q.Prime) (h : q ∣ μ) : q ∣ M := by
      rcases hq.dvd_mul.mp h with h | h
      · exact h
      · exact h.trans (dvd_mul_left _ _)
    obtain ⟨s, hsN, hsH, hsμ, hsS, e, he⟩ := classSieve_cover hD H C hC N M μ
      (dvd_mul_right _ _) hμM S J
    exact ⟨s, Finset.mem_filter.mpr ⟨(mem_boundedSplitPrimes s).mpr hsN, hsH, hsμ, hsS⟩, e, he⟩
  have hupper := classSieve_upper_of_cover hD B hbound C N M S T hcover
  have hTF : Disjoint T F := by
    apply Finset.disjoint_left.mpr
    intro s hsT hsF
    exact (hT s hsT).2.2 (Finset.mem_filter.mpr ⟨hsF, (hT s hsT).1, (hT s hsT).2.1⟩)
  have htail : ∑ s ∈ T, (s.1 : ℝ)⁻¹ < ε := by
    convert hF T hTF using 1
    apply Finset.sum_congr rfl
    intro s hs
    simp only [badSplitPrimeWeight, if_pos (hT s hs).1]
  have hheadSq : E ^ 2 ≤ (∏ s ∈ S, (1 - (s.1 : ℝ)⁻¹)) ^ 2 := by
    have hp : 0 ≤ ∏ s ∈ S, (1 - (s.1 : ℝ)⁻¹) := hE.le.trans hhead
    nlinarith
  have hAQ : E ^ 2 * (Q : ℝ) ^ 2 ≤ (A : ℝ) := by
    rw [show (A : ℝ) = (Q : ℝ) ^ 2 * (∏ s ∈ S, (1 - (s.1 : ℝ)⁻¹)) ^ 2 from
      cast_prod_splitPrime_sub_one_sq S, mul_comm ((Q : ℝ) ^ 2)]
    exact mul_le_mul_of_nonneg_right hheadSq (sq_nonneg _)
  apply sieve_bounds_contradiction (A := (A : ℝ)) (Q := (Q : ℝ)) (L := (L : ℝ))
    (B := (B : ℝ)) (U := (U : ℝ)) (K := (K : ℝ))
    (Y := (Nat.card (ClassSieveBall C N M S) : ℝ)) (E := E)
    (by exact_mod_cast hQ) (by exact_mod_cast hL) (by exact_mod_cast hB)
    (by exact_mod_cast hU) (by exact_mod_cast hK) hE hAQ
    (by exact_mod_cast hlower) ?_ htail
  simpa only [N, Nat.cast_mul, Nat.cast_pow] using hupper

end Bernays

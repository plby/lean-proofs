import ErdosProblems.Erdos981.Core
import ErdosProblems.Erdos981.External.Erdos980.ElliottTail.Burgess
import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.CharacterLargeSieve

open scoped BigOperators NumberTheorySymbols
open Filter Finset

namespace Erdos981

def test_primeQuadraticCharacterMod (p : ℕ) (hp : p.Prime) :
    QuadraticCharacterMod p where
  toFun a := jacobiSym (a : ℤ) p
  periodic := by
    intro a b hab
    apply jacobiSym.mod_left'
    exact_mod_cast hab
  map_non_coprime := by
    intro a ha
    rw [jacobiSym.eq_zero_iff]
    refine ⟨hp.ne_zero, ?_⟩
    simpa [Int.gcd_eq_natAbs, Nat.gcd_comm,
      Nat.coprime_iff_gcd_eq_one] using ha
  map_coprime := by
    intro a ha
    rcases jacobiSym.trichotomy (a : ℤ) p with hzero | hone | hneg
    · exfalso
      have hgcd := (jacobiSym.eq_zero_iff.mp hzero).2
      exact hgcd (by
        simpa [Int.gcd_eq_natAbs, Nat.gcd_comm,
          Nat.coprime_iff_gcd_eq_one] using ha)
    · exact Or.inl hone
    · exact Or.inr hneg
  map_mul := by
    intro a b ha hb
    simpa only [Nat.cast_mul] using jacobiSym.mul_left (a : ℤ) (b : ℤ) p

noncomputable def test_primeQuadraticDirichletCharacter
    (p : ℕ) (hp : p.Prime) : DirichletCharacter ℂ p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (test_primeQuadraticCharacterMod p hp).toDirichletCharacterComplex

@[simp] lemma test_primeQuadraticDirichletCharacter_apply_nat
    (p : ℕ) (hp : p.Prime) (n : ℕ) :
    test_primeQuadraticDirichletCharacter p hp (n : ZMod p) =
      (jacobiSym (n : ℤ) p : ℂ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact QuadraticCharacterMod.toDirichletCharacterComplex_apply_nat
    (n := n) (test_primeQuadraticCharacterMod p hp)

lemma test_primeQuadraticDirichletCharacter_eq_quadraticChar
    {p : ℕ} [Fact p.Prime] [NeZero p] :
    test_primeQuadraticDirichletCharacter p Fact.out =
      (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) := by
  rw [MulChar.ext_iff]
  intro a
  rw [show (a : ZMod p) = (((a : ZMod p).val : ℕ) : ZMod p) by
    exact (ZMod.natCast_zmod_val (a : ZMod p)).symm]
  rw [test_primeQuadraticDirichletCharacter_apply_nat]
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  simp [legendreSym]

lemma test_primeQuadraticDirichletCharacter_ne_one
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    test_primeQuadraticDirichletCharacter p hp ≠ 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [test_primeQuadraticDirichletCharacter_eq_quadraticChar]
  exact (MulChar.ringHomComp_ne_one_iff
      (f := Int.castRingHom ℂ) Int.cast_injective).mpr
    (quadraticChar_ne_one ((ZMod.ringChar_zmod_n p).substr
      (hpodd.ne_two_of_dvd_nat (dvd_refl p))))

lemma test_primeQuadraticDirichletCharacter_isPrimitive
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    (test_primeQuadraticDirichletCharacter p hp).IsPrimitive :=
  Erdos980.dirichletCharacter_isPrimitive_of_prime_of_ne_one hp _
    (test_primeQuadraticDirichletCharacter_ne_one hp hpodd)

noncomputable def test_primeQuadraticPrimitiveCharacter
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    BoundedGaps.Maynard.primitiveCharacters p :=
  ⟨test_primeQuadraticDirichletCharacter p hp,
    test_primeQuadraticDirichletCharacter_isPrimitive hp hpodd⟩

lemma test_sum_primeQuadraticCharacter_Ioc_eq
    {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑ n ∈ Finset.Ioc (0 : ℤ) (N : ℤ),
        test_primeQuadraticDirichletCharacter p hp (n : ZMod p)) =
      (legendrePartialSum p N : ℂ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  calc
    (∑ n ∈ Finset.Ioc (0 : ℤ) (N : ℤ),
        test_primeQuadraticDirichletCharacter p hp (n : ZMod p)) =
        ∑ n ∈ Finset.Icc 1 N,
          test_primeQuadraticDirichletCharacter p hp (n : ZMod p) := by
      apply Finset.sum_bij (fun n _hn => n.toNat)
      · intro n hn
        rcases Finset.mem_Ioc.mp hn with ⟨hn0, hnN⟩
        rw [Finset.mem_Icc]
        constructor <;> omega
      · intro n₁ hn₁ n₂ hn₂ heq
        have h₁ := (Finset.mem_Ioc.mp hn₁).1
        have h₂ := (Finset.mem_Ioc.mp hn₂).1
        omega
      · intro n hn
        refine ⟨(n : ℤ), Finset.mem_Ioc.mpr ?_, by simp⟩
        exact_mod_cast Finset.mem_Icc.mp hn
      · intro n hn
        congr 1
        have hncast : (n.toNat : ℤ) = n :=
          Int.toNat_of_nonneg (le_of_lt (Finset.mem_Ioc.mp hn).1)
        rw [← hncast]
        simp
    _ = ∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) p : ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [test_primeQuadraticDirichletCharacter_apply_nat]
    _ = (legendrePartialSum p N : ℂ) := by
      rw [legendrePartialSum_eq_sum_Icc]
      push_cast
      rfl

lemma test_norm_legendrePartialSum_lt_sqrt_mul_log
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (N : ℕ) :
    ‖(legendrePartialSum p N : ℂ)‖ <
      Real.sqrt (p : ℝ) * Real.log (p : ℝ) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h := BoundedGaps.Maynard.norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log
    hp.one_lt (test_primeQuadraticDirichletCharacter p hp)
      (test_primeQuadraticDirichletCharacter_isPrimitive hp hpodd) 0 N
  norm_num at h
  rwa [test_sum_primeQuadraticCharacter_Ioc_eq hp N] at h

noncomputable def test_polyaThreshold (ε : ℝ) (p : ℕ) : ℕ :=
  Nat.ceil ((Real.sqrt (p : ℝ) * Real.log (p : ℝ)) / ε) + 1

lemma test_isEventualThreshold_polya {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    IsEventualThreshold ε p (test_polyaThreshold ε p) := by
  have hm1 : 1 ≤ test_polyaThreshold ε p := by
    simp [test_polyaThreshold]
  refine ⟨hm1, ?_⟩
  intro N hN
  let B : ℝ := Real.sqrt (p : ℝ) * Real.log (p : ℝ)
  have hsumComplex := test_norm_legendrePartialSum_lt_sqrt_mul_log hp hpodd N
  have hsum : (legendrePartialSum p N : ℝ) < B := by
    refine (le_abs_self (legendrePartialSum p N : ℝ)).trans_lt ?_
    simpa only [Complex.norm_intCast] using hsumComplex
  have hratio : B / ε < (test_polyaThreshold ε p : ℝ) := by
    calc
      B / ε ≤ (Nat.ceil (B / ε) : ℕ) := Nat.le_ceil _
      _ < (Nat.ceil (B / ε) + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self _
      _ = (test_polyaThreshold ε p : ℕ) := by rfl
  have hB : B < ε * (test_polyaThreshold ε p : ℝ) := by
    rw [show ε * (test_polyaThreshold ε p : ℝ) =
      (test_polyaThreshold ε p : ℝ) * ε by ring]
    exact (div_lt_iff₀ hε).mp hratio
  have hmono : ε * (test_polyaThreshold ε p : ℝ) ≤ ε * (N : ℝ) := by
    gcongr
  exact hsum.trans (hB.trans_le hmono)

lemma test_eventualThreshold_le_polya {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) :
    eventualThreshold ε p ≤ test_polyaThreshold ε p :=
  eventualThreshold_minimal (test_isEventualThreshold_polya hε hp hpodd)

lemma test_eventually_two_add_const_mul_sqrt_mul_log_le_fourFifths_rpow
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop,
      2 + C * (Real.sqrt x * Real.log x) ≤ x ^ (4 / 5 : ℝ) := by
  let c : ℝ := 1 / (2 * (C + 1))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hlog :=
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 3 / 10 by norm_num)).bound hc
  have hpow := (tendsto_rpow_atTop
    (show (0 : ℝ) < 4 / 5 by norm_num)).eventually
      (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hlog, hpow, eventually_gt_atTop (1 : ℝ)] with x hxlog hxpow hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hdeltaPow : 0 < x ^ (3 / 10 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hdeltaPow.le] at hxlog
  have hrpow : Real.sqrt x * x ^ (3 / 10 : ℝ) = x ^ (4 / 5 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    congr 2
    norm_num
  have hcoef : C * c ≤ 1 / 2 := by
    dsimp [c]
    have hden : 0 < 2 * (C + 1) := by positivity
    have hquot : C / (2 * (C + 1)) ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ hden]
      nlinarith
    convert hquot using 1 <;> ring
  have hmain : C * (Real.sqrt x * Real.log x) ≤
      (1 / 2 : ℝ) * x ^ (4 / 5 : ℝ) := by
    calc
      C * (Real.sqrt x * Real.log x) ≤
          C * (Real.sqrt x * (c * x ^ (3 / 10 : ℝ))) := by
        gcongr
      _ = (C * c) * x ^ (4 / 5 : ℝ) := by rw [← hrpow]; ring
      _ ≤ (1 / 2 : ℝ) * x ^ (4 / 5 : ℝ) := by
        gcongr
  have htwo : 2 ≤ (1 / 2 : ℝ) * x ^ (4 / 5 : ℝ) := by
    nlinarith
  nlinarith

lemma test_eventually_eventualThreshold_le_fourFifths_rpow
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p : ℕ in atTop,
      p.Prime → Odd p →
        (eventualThreshold ε p : ℝ) ≤ (p : ℝ) ^ (4 / 5 : ℝ) := by
  have hevent := tendsto_natCast_atTop_atTop.eventually
    (test_eventually_two_add_const_mul_sqrt_mul_log_le_fourFifths_rpow
      ε⁻¹ (inv_nonneg.mpr hε.le))
  filter_upwards [hevent, eventually_ge_atTop 3] with p hpbound hp3
  intro hp hpodd
  have hthreshold := test_eventualThreshold_le_polya hε hp hpodd
  calc
    (eventualThreshold ε p : ℝ) ≤ (test_polyaThreshold ε p : ℕ) := by
      exact_mod_cast hthreshold
    _ ≤ 2 + ε⁻¹ * (Real.sqrt (p : ℝ) * Real.log (p : ℝ)) := by
      rw [test_polyaThreshold, Nat.cast_add, Nat.cast_one]
      have hceil := Nat.ceil_lt_add_one
        (show 0 ≤ (Real.sqrt (p : ℝ) * Real.log (p : ℝ)) / ε by
          positivity)
      have hεne : ε ≠ 0 := hε.ne'
      rw [div_eq_inv_mul, mul_comm] at hceil ⊢
      linarith
    _ ≤ (p : ℝ) ^ (4 / 5 : ℝ) := hpbound

noncomputable def test_productMultiplicity (r N k : ℕ) : ℕ :=
  (tupleProductFiber r N k).card

lemma test_tupleProduct_mapsTo_Icc (r N : ℕ) :
    Set.MapsTo tupleProduct (↑(tupleBox r N) : Set (Fin r → ℕ))
      (↑(Finset.Icc 1 (N ^ r)) : Set ℕ) := by
  intro a ha
  exact Finset.mem_Icc.mpr
    ⟨tupleProduct_pos_of_mem ha, tupleProduct_le_pow_of_mem ha⟩

lemma test_dirichlet_sum_pow_eq_productMultiplicity
    {q : ℕ} (χ : DirichletCharacter ℂ q) (r N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q)) ^ r =
      ∑ k ∈ Finset.Icc 1 (N ^ r),
        (test_productMultiplicity r N k : ℂ) * χ (k : ZMod q) := by
  classical
  rw [Finset.sum_pow']
  calc
    (∑ a ∈ tupleBox r N, ∏ i, χ (a i : ZMod q)) =
        ∑ a ∈ tupleBox r N, χ (tupleProduct a : ZMod q) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [show (tupleProduct a : ZMod q) = ∏ i, (a i : ZMod q) by
        change ((∏ i, a i : ℕ) : ZMod q) = ∏ i, (a i : ZMod q)
        push_cast
        rfl]
      exact (map_prod χ (fun i => (a i : ZMod q)) Finset.univ).symm
    _ = ∑ k ∈ Finset.Icc 1 (N ^ r),
        ∑ a ∈ tupleBox r N with tupleProduct a = k,
          χ (tupleProduct a : ZMod q) := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (test_tupleProduct_mapsTo_Icc r N)
        (fun a => χ (tupleProduct a : ZMod q))]
    _ = ∑ k ∈ Finset.Icc 1 (N ^ r),
        (test_productMultiplicity r N k : ℂ) * χ (k : ZMod q) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [test_productMultiplicity, tupleProductFiber]
      rw [show (∑ a ∈ tupleBox r N with tupleProduct a = k,
          χ (tupleProduct a : ZMod q)) =
          ∑ _a ∈ (tupleBox r N).filter (fun a => tupleProduct a = k),
            χ (k : ZMod q) by
        apply Finset.sum_congr rfl
        intro a ha
        rw [(Finset.mem_filter.mp ha).2]]
      simp

lemma test_sum_productMultiplicity (r N : ℕ) :
    ∑ k ∈ Finset.Icc 1 (N ^ r), test_productMultiplicity r N k = N ^ r := by
  calc
    ∑ k ∈ Finset.Icc 1 (N ^ r), test_productMultiplicity r N k =
        (tupleBox r N).card := by
      exact (Finset.card_eq_sum_card_fiberwise
        (test_tupleProduct_mapsTo_Icc r N)).symm
    _ = N ^ r := tupleBox_card r N

lemma test_productMultiplicity_le_envelope (r : ℕ) (hr : 0 < r) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k ∈ Finset.Icc 1 (N ^ r),
      (test_productMultiplicity r N k : ℝ) ≤
        Erdos439.PowerDecay.divisorSubpowerEnvelope N := by
  obtain ⟨N₀, hN₀⟩ :=
    Erdos439.PowerDecay.exists_uniform_divisor_power_le_subpower r hr
  refine ⟨N₀, ?_⟩
  intro N hN k hk
  have hfiber : (test_productMultiplicity r N k : ℝ) ≤
      (k.divisors.card : ℝ) ^ r := by
    exact_mod_cast tupleProductFiber_card_le_divisors_pow r N k
      (Finset.mem_Icc.mp hk).1
  exact hfiber.trans (hN₀ N hN k hk)

lemma test_productMultiplicity_energy_le (r : ℕ) (hr : 0 < r) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∑ k ∈ Finset.Icc 1 (N ^ r),
        ‖(test_productMultiplicity r N k : ℂ)‖ ^ 2) ≤
          Erdos439.PowerDecay.divisorSubpowerEnvelope N * (N : ℝ) ^ r := by
  obtain ⟨N₀, hN₀⟩ := test_productMultiplicity_le_envelope r hr
  refine ⟨N₀, ?_⟩
  intro N hN
  calc
    (∑ k ∈ Finset.Icc 1 (N ^ r),
        ‖(test_productMultiplicity r N k : ℂ)‖ ^ 2) =
        ∑ k ∈ Finset.Icc 1 (N ^ r),
          (test_productMultiplicity r N k : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Complex.norm_natCast]
    _ ≤ ∑ k ∈ Finset.Icc 1 (N ^ r),
        Erdos439.PowerDecay.divisorSubpowerEnvelope N *
          test_productMultiplicity r N k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hN₀ N hN k hk) (by positivity)
    _ = Erdos439.PowerDecay.divisorSubpowerEnvelope N * (N : ℝ) ^ r := by
      rw [← Finset.mul_sum]
      have hsum := congrArg (fun n : ℕ => (n : ℝ))
        (test_sum_productMultiplicity r N)
      push_cast at hsum
      rw [hsum]

noncomputable def test_endpointBadPrimes (ε : ℝ) (N x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun p =>
    p.Prime ∧ Odd p ∧ ε * (N : ℝ) ≤ (legendrePartialSum p N : ℝ)

lemma test_sum_primeQuadraticCharacter_Icc_eq
    {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        test_primeQuadraticDirichletCharacter p hp (n : ZMod p)) =
      (legendrePartialSum p N : ℂ) := by
  rw [legendrePartialSum_eq_sum_Icc]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  exact test_primeQuadraticDirichletCharacter_apply_nat p hp n

lemma test_primeQuadratic_twist_eq
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (r N : ℕ) :
    (∑ k ∈ Finset.Icc 1 (N ^ r),
        (test_productMultiplicity r N k : ℂ) *
          (test_primeQuadraticPrimitiveCharacter p hp hpodd).1
            (k : ZMod p)) =
      (legendrePartialSum p N : ℂ) ^ r := by
  change (∑ k ∈ Finset.Icc 1 (N ^ r),
      (test_productMultiplicity r N k : ℂ) *
        test_primeQuadraticDirichletCharacter p hp (k : ZMod p)) = _
  rw [← test_dirichlet_sum_pow_eq_productMultiplicity
    (test_primeQuadraticDirichletCharacter p hp) r N,
    test_sum_primeQuadraticCharacter_Icc_eq hp N]

lemma test_endpointBadPrimes_card_mul_largeSieve_le
    {ε : ℝ} (hε : 0 < ε) (r N x : ℕ) :
    (ε * (N : ℝ)) ^ (2 * r) *
        ((test_endpointBadPrimes ε N x).card : ℝ) ≤
      (∑ q ∈ Finset.Ioc 0 x,
        (q : ℝ) / (Nat.totient q : ℝ) *
          ∑ ψ : BoundedGaps.Maynard.primitiveCharacters q,
            ‖∑ k ∈ Finset.Icc 1 (N ^ r),
              (test_productMultiplicity r N k : ℂ) * ψ.1 k‖ ^ 2) := by
  classical
  let bad := test_endpointBadPrimes ε N x
  let eta : ℝ := (ε * (N : ℝ)) ^ r
  have hbadsub : bad ⊆ Finset.Ioc 0 x := by
    intro p hpbad
    have h := (Finset.mem_filter.mp hpbad)
    exact Finset.mem_Ioc.mpr ⟨h.2.1.pos, (Finset.mem_range.mp h.1).le⟩
  have hpoint : ∀ p ∈ bad,
      eta ^ 2 ≤
        (p : ℝ) / (Nat.totient p : ℝ) *
          ∑ ψ : BoundedGaps.Maynard.primitiveCharacters p,
            ‖∑ k ∈ Finset.Icc 1 (N ^ r),
              (test_productMultiplicity r N k : ℂ) * ψ.1 k‖ ^ 2 := by
    intro p hpbad
    have hpdata := (Finset.mem_filter.mp hpbad).2
    have hp := hpdata.1
    have hpodd := hpdata.2.1
    have hpge := hpdata.2.2
    have hNnonneg : 0 ≤ ε * (N : ℝ) := mul_nonneg hε.le (by positivity)
    have hpowge : eta ≤
        ‖(legendrePartialSum p N : ℂ) ^ r‖ := by
      rw [norm_pow, Complex.norm_intCast]
      exact pow_le_pow_left₀ hNnonneg
        (hpge.trans (le_abs_self (legendrePartialSum p N : ℝ))) r
    have hsqge : eta ^ 2 ≤
        ‖∑ k ∈ Finset.Icc 1 (N ^ r),
          (test_productMultiplicity r N k : ℂ) *
            (test_primeQuadraticPrimitiveCharacter p hp hpodd).1 k‖ ^ 2 := by
      rw [test_primeQuadratic_twist_eq hp hpodd r N]
      exact pow_le_pow_left₀ (by positivity) hpowge 2
    have hinner :
        ‖∑ k ∈ Finset.Icc 1 (N ^ r),
          (test_productMultiplicity r N k : ℂ) *
            (test_primeQuadraticPrimitiveCharacter p hp hpodd).1 k‖ ^ 2 ≤
          ∑ ψ : BoundedGaps.Maynard.primitiveCharacters p,
            ‖∑ k ∈ Finset.Icc 1 (N ^ r),
              (test_productMultiplicity r N k : ℂ) * ψ.1 k‖ ^ 2 := by
      let F : BoundedGaps.Maynard.primitiveCharacters p → ℝ := fun ψ =>
        ‖∑ k ∈ Finset.Icc 1 (N ^ r),
          (test_productMultiplicity r N k : ℂ) * ψ.1 k‖ ^ 2
      change F (test_primeQuadraticPrimitiveCharacter p hp hpodd) ≤
        ∑ ψ, F ψ
      exact Finset.single_le_sum (s := Finset.univ) (f := F)
        (fun _ _ => sq_nonneg _)
        (Finset.mem_univ (test_primeQuadraticPrimitiveCharacter p hp hpodd))
    have hphiPos : (0 : ℝ) < Nat.totient p := by
      exact_mod_cast Nat.totient_pos.mpr hp.pos
    have hweight : (1 : ℝ) ≤ (p : ℝ) / (Nat.totient p : ℝ) := by
      rw [one_le_div₀ hphiPos]
      exact_mod_cast Nat.totient_le p
    calc
      eta ^ 2 ≤ ∑ ψ : BoundedGaps.Maynard.primitiveCharacters p,
          ‖∑ k ∈ Finset.Icc 1 (N ^ r),
            (test_productMultiplicity r N k : ℂ) * ψ.1 k‖ ^ 2 :=
        hsqge.trans hinner
      _ ≤ (p : ℝ) / (Nat.totient p : ℝ) *
          ∑ ψ : BoundedGaps.Maynard.primitiveCharacters p,
            ‖∑ k ∈ Finset.Icc 1 (N ^ r),
              (test_productMultiplicity r N k : ℂ) * ψ.1 k‖ ^ 2 := by
        let T : ℝ := ∑ ψ : BoundedGaps.Maynard.primitiveCharacters p,
          ‖∑ k ∈ Finset.Icc 1 (N ^ r),
            (test_productMultiplicity r N k : ℂ) * ψ.1 k‖ ^ 2
        change T ≤ (p : ℝ) / (Nat.totient p : ℝ) * T
        calc
          T = 1 * T := by ring
          _ ≤ (p : ℝ) / (Nat.totient p : ℝ) * T :=
            mul_le_mul_of_nonneg_right hweight (by
              dsimp [T]
              exact Finset.sum_nonneg fun ψ _ => sq_nonneg _)
  rw [show (ε * (N : ℝ)) ^ (2 * r) = eta ^ 2 by
    dsimp [eta]
    rw [← pow_mul]
    congr 1
    omega]
  calc
    eta ^ 2 * (bad.card : ℝ) = ∑ _p ∈ bad, eta ^ 2 := by
      simp [mul_comm]
    _ ≤ ∑ p ∈ bad,
        (p : ℝ) / (Nat.totient p : ℝ) *
          ∑ ψ : BoundedGaps.Maynard.primitiveCharacters p,
            ‖∑ k ∈ Finset.Icc 1 (N ^ r),
              (test_productMultiplicity r N k : ℂ) * ψ.1 k‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hbadsub
      (fun _ _ _ => by positivity)

lemma test_exists_endpointBadPrimes_largeSieve_bound
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 0 < r) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ℕ,
      (ε * (N : ℝ)) ^ (2 * r) *
          ((test_endpointBadPrimes ε N x).card : ℝ) ≤
        (((N : ℝ) ^ r + (x : ℝ) ^ 2) *
          Erdos439.PowerDecay.divisorSubpowerEnvelope N *
            (N : ℝ) ^ r) := by
  obtain ⟨N₀, henergy⟩ := test_productMultiplicity_energy_le r hr
  refine ⟨N₀, ?_⟩
  intro N hN x
  let s := Finset.Icc 1 (N ^ r)
  let c : ℕ → ℂ := fun k => (test_productMultiplicity r N k : ℂ)
  have hs : s ⊆ Finset.Ioc 0 (0 + N ^ r) := by
    intro k hk
    rw [Finset.mem_Ioc]
    have h := Finset.mem_Icc.mp hk
    omega
  have hLS :=
    BoundedGaps.Maynard.sum_weighted_norm_sq_primitiveTwists_subset_Ioc_le
      x 0 (N ^ r) s hs c
  norm_num [s, c] at hLS
  calc
    (ε * (N : ℝ)) ^ (2 * r) *
        ((test_endpointBadPrimes ε N x).card : ℝ) ≤
      (∑ q ∈ Finset.Ioc 0 x,
        (q : ℝ) / (Nat.totient q : ℝ) *
          ∑ ψ : BoundedGaps.Maynard.primitiveCharacters q,
            ‖∑ k ∈ Finset.Icc 1 (N ^ r),
              (test_productMultiplicity r N k : ℂ) * ψ.1 k‖ ^ 2) :=
      test_endpointBadPrimes_card_mul_largeSieve_le hε r N x
    _ ≤ (((N : ℝ) ^ r + (x : ℝ) ^ 2) *
        ∑ k ∈ Finset.Icc 1 (N ^ r),
          ‖(test_productMultiplicity r N k : ℂ)‖ ^ 2) := by
      convert hLS using 1 <;> simp
    _ ≤ ((N : ℝ) ^ r + (x : ℝ) ^ 2) *
        Erdos439.PowerDecay.divisorSubpowerEnvelope N * (N : ℝ) ^ r := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (henergy N hN) (by positivity)

lemma test_jacobiSym_neg_one_le (a : ℤ) (p : ℕ) :
    -1 ≤ jacobiSym a p := by
  rcases jacobiSym.trichotomy a p with h | h | h <;> omega

lemma test_legendrePartialSum_sub_le_of_le (p : ℕ) {t U : ℕ} (htU : t ≤ U) :
    legendrePartialSum p t - (U - t : ℕ) ≤ legendrePartialSum p U := by
  have hdecomp : legendrePartialSum p U = legendrePartialSum p t +
      ∑ n ∈ Finset.range (U - t), jacobiSym (t + n + 1 : ℤ) p := by
    rw [legendrePartialSum, show U = t + (U - t) by omega,
      Finset.sum_range_add, legendrePartialSum]
    simp only [Nat.add_sub_cancel_left]
    apply congrArg (fun z : ℤ => legendrePartialSum p t + z)
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
  have htail : -((U - t : ℕ) : ℤ) ≤
      ∑ n ∈ Finset.range (U - t),
        jacobiSym (t + n + 1 : ℤ) p := by
    calc
      -((U - t : ℕ) : ℤ) =
          ∑ _n ∈ Finset.range (U - t), (-1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun n _hn =>
        test_jacobiSym_neg_one_le (t + n + 1 : ℤ) p
  rw [hdecomp]
  linarith

def test_gridStep (A K : ℕ) : ℕ := A / K

def test_gridIndex (A K t : ℕ) : ℕ :=
  (t - A) / test_gridStep A K + 1

def test_gridEndpoint (A K j : ℕ) : ℕ :=
  A + j * test_gridStep A K

lemma test_grid_arithmetic {A K t : ℕ} (hK : 0 < K) (hA : 2 * K ≤ A)
    (ht : t ∈ Finset.Icc A (2 * A)) :
    let D := test_gridStep A K
    let j := test_gridIndex A K t
    0 < D ∧ j < A / D + 2 ∧ t ≤ test_gridEndpoint A K j ∧
      test_gridEndpoint A K j - t ≤ D ∧
      test_gridEndpoint A K j ≤ 2 * A + D ∧ A / D ≤ 2 * K := by
  dsimp [test_gridStep, test_gridIndex, test_gridEndpoint]
  rcases Finset.mem_Icc.mp ht with ⟨hAt, htA2⟩
  have hAK : K ≤ A := by omega
  have hDpos : 0 < A / K := Nat.div_pos hAK hK
  have hDtwo : 2 ≤ A / K := by
    exact (Nat.le_div_iff_mul_le hK).2 (by simpa [Nat.mul_comm] using hA)
  have htrem := Nat.mod_lt (t - A) hDpos
  have hteq := Nat.mod_add_div (t - A) (A / K)
  have hteq' :
      (t - A) / (A / K) * (A / K) + (t - A) % (A / K) = t - A := by
    simpa [Nat.add_comm, Nat.mul_comm] using hteq
  have htdecomp :
      t = A + (t - A) / (A / K) * (A / K) +
        (t - A) % (A / K) := by omega
  have hendpoint :
      A + ((t - A) / (A / K) + 1) * (A / K) =
        A + (t - A) / (A / K) * (A / K) + (A / K) := by
    rw [Nat.add_mul, one_mul, Nat.add_assoc]
  have hjbound : (t - A) / (A / K) ≤ A / (A / K) := by
    exact Nat.div_le_div_right (by omega)
  have hArem := Nat.mod_lt A hK
  have hAeq := Nat.mod_add_div A K
  have hKleKD : K ≤ K * (A / K) := by
    calc
      K = K * 1 := by simp
      _ ≤ K * (A / K) := Nat.mul_le_mul_left K (by omega)
  have hAlt : A < 2 * K * (A / K) := by
    calc
      A = A % K + K * (A / K) := hAeq.symm
      _ < K + K * (A / K) := Nat.add_lt_add_right hArem _
      _ ≤ K * (A / K) + K * (A / K) := by
        exact Nat.add_le_add_right hKleKD _
      _ = 2 * K * (A / K) := by ring
  have hADiv : A / (A / K) < 2 * K :=
    (Nat.div_lt_iff_lt_mul hDpos).2 (by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hAlt)
  constructor
  · exact hDpos
  constructor
  · omega
  constructor
  · rw [hendpoint]
    omega
  constructor
  · rw [hendpoint]
    omega
  constructor
  · rw [hendpoint]
    have hqmul : (t - A) / (A / K) * (A / K) ≤ A := by
      calc
        _ ≤ (A / (A / K)) * (A / K) :=
          Nat.mul_le_mul_right (A / K) hjbound
        _ ≤ A := Nat.div_mul_le_self A (A / K)
    omega
  · omega

noncomputable def test_blockBadPrimes (ε : ℝ) (A x : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range x).filter fun p =>
      p.Prime ∧ Odd p ∧ ∃ t ∈ Finset.Icc A (2 * A),
        ε * (t : ℝ) ≤ (legendrePartialSum p t : ℝ)

@[simp] lemma test_mem_blockBadPrimes {ε : ℝ} {A x p : ℕ} :
    p ∈ test_blockBadPrimes ε A x ↔
      p < x ∧ p.Prime ∧ Odd p ∧ ∃ t ∈ Finset.Icc A (2 * A),
        ε * (t : ℝ) ≤ (legendrePartialSum p t : ℝ) := by
  classical
  simp [test_blockBadPrimes]

lemma test_blockBadPrime_has_gridEndpoint
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {K A x p : ℕ} (hK : 0 < K) (hKε : (4 : ℝ) < ε * K)
    (hA : 2 * K ≤ A) (hp : p ∈ test_blockBadPrimes ε A x) :
    ∃ j ∈ Finset.range (A / test_gridStep A K + 2),
      p ∈ test_endpointBadPrimes (ε / 3) (test_gridEndpoint A K j) x := by
  classical
  rw [test_mem_blockBadPrimes] at hp
  rcases hp with ⟨hpx, hpprime, hpodd, t, ht, hbad⟩
  let D := test_gridStep A K
  let j := test_gridIndex A K t
  let U := test_gridEndpoint A K j
  have hgrid := test_grid_arithmetic hK hA ht
  change 0 < D ∧ j < A / D + 2 ∧ t ≤ U ∧ U - t ≤ D ∧
    U ≤ 2 * A + D ∧ A / D ≤ 2 * K at hgrid
  rcases hgrid with ⟨hDpos, hj, htU, hUt, hU, hcard⟩
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hDle : (D : ℝ) ≤ (A : ℝ) / K := by
    dsimp [D, test_gridStep]
    exact Nat.cast_div_le
  have hquot : (A : ℝ) / K < ε * (A : ℝ) / 4 := by
    have hA0 : (0 : ℝ) ≤ A := by positivity
    have hinv : (K : ℝ)⁻¹ < ε / 4 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      have hfour : (4 : ℝ) / K < ε := by
        rw [div_lt_iff₀ hKreal]
        simpa [mul_comm] using hKε
      simpa [div_eq_mul_inv, mul_comm] using hfour
    rw [div_eq_mul_inv, show ε * (A : ℝ) / 4 = (A : ℝ) * (ε / 4) by ring]
    exact mul_lt_mul_of_pos_left hinv (by exact_mod_cast (by omega : 0 < A))
  have hDsmall : (D : ℝ) < ε * (A : ℝ) / 4 := hDle.trans_lt hquot
  have hlip := test_legendrePartialSum_sub_le_of_le p htU
  have hlipR : (legendrePartialSum p t : ℝ) - (U - t : ℕ) ≤
      (legendrePartialSum p U : ℝ) := by exact_mod_cast hlip
  have hloss : ((U - t : ℕ) : ℝ) ≤ D := by exact_mod_cast hUt
  have hAt : (A : ℝ) ≤ t := by exact_mod_cast (Finset.mem_Icc.mp ht).1
  have hsumU : 3 * ε * (A : ℝ) / 4 ≤
      (legendrePartialSum p U : ℝ) := by
    nlinarith
  have hUreal : (U : ℝ) ≤ 2 * (A : ℝ) + (D : ℝ) := by exact_mod_cast hU
  have hUA : (U : ℝ) ≤ 9 * (A : ℝ) / 4 := by
    have hεA : ε * (A : ℝ) / 4 ≤ (A : ℝ) / 4 := by
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (by positivity) hε1) (by norm_num)
    linarith
  have hendpointBad : ε / 3 * (U : ℝ) ≤
      (legendrePartialSum p U : ℝ) := by
    calc
      ε / 3 * (U : ℝ) ≤ ε / 3 * (9 * (A : ℝ) / 4) := by
        gcongr
      _ = 3 * ε * (A : ℝ) / 4 := by ring
      _ ≤ _ := hsumU
  refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hpx, hpprime, hpodd, hendpointBad⟩

lemma test_blockBadPrimes_card_le_endpoint_sum
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {K A x : ℕ} (hK : 0 < K) (hKε : (4 : ℝ) < ε * K)
    (hA : 2 * K ≤ A) :
    (test_blockBadPrimes ε A x).card ≤
      ∑ j ∈ Finset.range (A / test_gridStep A K + 2),
        (test_endpointBadPrimes (ε / 3) (test_gridEndpoint A K j) x).card := by
  classical
  calc
    (test_blockBadPrimes ε A x).card ≤
        ((Finset.range (A / test_gridStep A K + 2)).biUnion fun j =>
          test_endpointBadPrimes (ε / 3) (test_gridEndpoint A K j) x).card := by
      apply Finset.card_le_card
      intro p hp
      rcases test_blockBadPrime_has_gridEndpoint hε hε1 hK hKε hA hp with
        ⟨j, hj, hpj⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj, hpj⟩
    _ ≤ _ := Finset.card_biUnion_le

lemma test_grid_count_le {A K : ℕ} (hK : 0 < K) (hA : 2 * K ≤ A) :
    A / test_gridStep A K + 2 ≤ 2 * K + 2 := by
  have hmem : A ∈ Finset.Icc A (2 * A) :=
    Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hgrid := test_grid_arithmetic hK hA hmem
  exact Nat.add_le_add_right hgrid.2.2.2.2.2 2

lemma test_gridEndpoint_between {A K j : ℕ} (hK : 0 < K)
    (hA : 2 * K ≤ A)
    (hj : j ∈ Finset.range (A / test_gridStep A K + 2)) :
    A ≤ test_gridEndpoint A K j ∧ test_gridEndpoint A K j ≤ 3 * A := by
  have hDpos : 0 < test_gridStep A K := by
    dsimp [test_gridStep]
    exact Nat.div_pos (by omega) hK
  have hjle : j ≤ A / test_gridStep A K + 1 := by
    exact Nat.le_pred_of_lt (Finset.mem_range.mp hj)
  have hmul : j * test_gridStep A K ≤ A + test_gridStep A K := by
    calc
      j * test_gridStep A K ≤
          (A / test_gridStep A K + 1) * test_gridStep A K := by gcongr
      _ = A / test_gridStep A K * test_gridStep A K +
          test_gridStep A K := by ring
      _ ≤ A + test_gridStep A K := by
        gcongr
        exact Nat.div_mul_le_self A (test_gridStep A K)
  have hDle : test_gridStep A K ≤ A := by
    dsimp [test_gridStep]
    exact Nat.div_le_self A K
  dsimp [test_gridEndpoint]
  omega

lemma test_divisorSubpowerEnvelope_mono {m n : ℕ} (hmn : m ≤ n) :
    Erdos439.PowerDecay.divisorSubpowerEnvelope m ≤
      Erdos439.PowerDecay.divisorSubpowerEnvelope n := by
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmn) (by norm_num)

lemma test_exists_blockBadPrimes_largeSieve_bound
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {K : ℕ} (hK : 0 < K) (hKε : (4 : ℝ) < ε * K) :
    ∃ A₀ : ℕ, ∀ A ≥ A₀, ∀ x : ℕ,
      (ε / 3 * (A : ℝ)) ^ 600 *
          ((test_blockBadPrimes ε A x).card : ℝ) ≤
        ((2 * K + 2 : ℕ) : ℝ) *
          ((((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
            Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) *
              ((3 * A : ℕ) : ℝ) ^ 300) := by
  obtain ⟨N₀, hLS⟩ :=
    test_exists_endpointBadPrimes_largeSieve_bound (by positivity : 0 < ε / 3)
      300 (by norm_num)
  refine ⟨max (2 * K) N₀, ?_⟩
  intro A hA x
  have hAK : 2 * K ≤ A := (le_max_left _ _).trans hA
  have hAN₀ : N₀ ≤ A := (le_max_right _ _).trans hA
  have hcard := test_blockBadPrimes_card_le_endpoint_sum
    (x := x) hε hε1 hK hKε hAK
  have hcount := test_grid_count_le hK hAK
  have hterm : ∀ j ∈ Finset.range (A / test_gridStep A K + 2),
      (ε / 3 * (A : ℝ)) ^ 600 *
          ((test_endpointBadPrimes (ε / 3)
            (test_gridEndpoint A K j) x).card : ℝ) ≤
        (((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
          Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) *
            ((3 * A : ℕ) : ℝ) ^ 300 := by
    intro j hj
    let U := test_gridEndpoint A K j
    have hU := test_gridEndpoint_between hK hAK hj
    have hUN₀ : N₀ ≤ U := hAN₀.trans hU.1
    have hbase : 0 ≤ ε / 3 * (A : ℝ) := by positivity
    have hbasele : ε / 3 * (A : ℝ) ≤ ε / 3 * (U : ℝ) := by
      gcongr
      exact_mod_cast hU.1
    have hfac : (ε / 3 * (A : ℝ)) ^ 600 ≤
        (ε / 3 * (U : ℝ)) ^ 600 :=
      pow_le_pow_left₀ hbase hbasele 600
    have hcardnonneg :
        (0 : ℝ) ≤ (test_endpointBadPrimes (ε / 3) U x).card := by positivity
    have hsmall : (ε / 3 * (A : ℝ)) ^ 600 *
          ((test_endpointBadPrimes (ε / 3) U x).card : ℝ) ≤
        (ε / 3 * (U : ℝ)) ^ 600 *
          ((test_endpointBadPrimes (ε / 3) U x).card : ℝ) :=
      mul_le_mul_of_nonneg_right hfac hcardnonneg
    have hlsU := hLS U hUN₀ x
    norm_num at hlsU
    have hUR : (U : ℝ) ≤ ((3 * A : ℕ) : ℝ) := by exact_mod_cast hU.2
    have hpow : (U : ℝ) ^ 300 ≤ ((3 * A : ℕ) : ℝ) ^ 300 := by gcongr
    have henv := test_divisorSubpowerEnvelope_mono hU.2
    calc
      (ε / 3 * (A : ℝ)) ^ 600 *
          ((test_endpointBadPrimes (ε / 3) U x).card : ℝ) ≤
        (ε / 3 * (U : ℝ)) ^ 600 *
          ((test_endpointBadPrimes (ε / 3) U x).card : ℝ) := hsmall
      _ ≤ ((U : ℝ) ^ 300 + (x : ℝ) ^ 2) *
          Erdos439.PowerDecay.divisorSubpowerEnvelope U * (U : ℝ) ^ 300 := hlsU
      _ ≤ (((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
          Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) *
            ((3 * A : ℕ) : ℝ) ^ 300 := by
        have hsum : (U : ℝ) ^ 300 + (x : ℝ) ^ 2 ≤
            ((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2 :=
          add_le_add hpow le_rfl
        have henvU : 0 ≤ Erdos439.PowerDecay.divisorSubpowerEnvelope U := by
          unfold Erdos439.PowerDecay.divisorSubpowerEnvelope
          exact Real.rpow_nonneg (by positivity) _
        have henv3A :
            0 ≤ Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) := by
          unfold Erdos439.PowerDecay.divisorSubpowerEnvelope
          exact Real.rpow_nonneg (by positivity) _
        have hsum3A :
            0 ≤ ((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2 :=
          add_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _)
        have hfirst : ((U : ℝ) ^ 300 + (x : ℝ) ^ 2) *
              Erdos439.PowerDecay.divisorSubpowerEnvelope U ≤
            (((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
              Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) := by
          exact mul_le_mul hsum henv henvU hsum3A
        have hfirstNonneg : 0 ≤
            (((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
              Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) :=
          mul_nonneg hsum3A henv3A
        exact mul_le_mul hfirst hpow (pow_nonneg (by positivity) _) hfirstNonneg
  calc
    (ε / 3 * (A : ℝ)) ^ 600 *
        ((test_blockBadPrimes ε A x).card : ℝ) ≤
      (ε / 3 * (A : ℝ)) ^ 600 *
        (∑ j ∈ Finset.range (A / test_gridStep A K + 2),
          ((test_endpointBadPrimes (ε / 3)
            (test_gridEndpoint A K j) x).card : ℕ) : ℝ) := by
      gcongr
      exact_mod_cast hcard
    _ = ∑ j ∈ Finset.range (A / test_gridStep A K + 2),
        (ε / 3 * (A : ℝ)) ^ 600 *
          ((test_endpointBadPrimes (ε / 3)
            (test_gridEndpoint A K j) x).card : ℝ) := by
      simp [Finset.mul_sum]
    _ ≤ ∑ _j ∈ Finset.range (A / test_gridStep A K + 2),
        ((((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
          Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) *
            ((3 * A : ℕ) : ℝ) ^ 300) := Finset.sum_le_sum hterm
    _ ≤ ((2 * K + 2 : ℕ) : ℝ) *
        ((((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
          Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) *
            ((3 * A : ℕ) : ℝ) ^ 300) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have henv : 0 ≤ Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) := by
        unfold Erdos439.PowerDecay.divisorSubpowerEnvelope
        positivity
      have hC : 0 ≤ ((((3 * A : ℕ) : ℝ) ^ 300 + (x : ℝ) ^ 2) *
          Erdos439.PowerDecay.divisorSubpowerEnvelope (3 * A) *
            ((3 * A : ℕ) : ℝ) ^ 300) := by positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hC

end Erdos981

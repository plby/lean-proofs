import ErdosProblems.Erdos88.SwitchingMomentLower

open Classical
open scoped BigOperators

namespace Erdos88.Switching

lemma degeneracyTerm_normalize
    {n t m s k : ℕ} (K : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hk : k ≤ s) :
    (((t : ℝ) ^ s / Real.sqrt n ^ k) *
        ((2 : ℝ) ^ n * (2 : ℝ) ^ (s - k) /
          Real.sqrt m ^ (s - k) *
            (K * (n : ℝ) ^ (-(3 / 2 : ℝ))))) =
      (2 : ℝ) ^ n * (K * (n : ℝ) ^ (-(3 / 2 : ℝ))) *
        (((t : ℝ) / Real.sqrt n) ^ s *
          ((2 * Real.sqrt n / Real.sqrt m) ^ (s - k))) := by
  have hnroot : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have hmroot : Real.sqrt (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hm))
  have hs : k + (s - k) = s := Nat.add_sub_of_le hk
  rw [show s = k + (s - k) by omega, pow_add]
  simp only [div_pow, mul_pow]
  field_simp
  simp only [Nat.add_sub_cancel_left]
  ring

lemma degeneracyFactor_le
    {n m s k d : ℕ} (R : ℝ)
    (hk : k ≤ s) (hsd : s ≤ d) (hR : 1 ≤ R)
    (hroot : 2 * Real.sqrt n / Real.sqrt m ≤ R) :
    (2 * Real.sqrt n / Real.sqrt m) ^ (s - k) ≤ R ^ d := by
  have hbase : 0 ≤ 2 * Real.sqrt n / Real.sqrt m := by positivity
  calc
    (2 * Real.sqrt n / Real.sqrt m) ^ (s - k) ≤ R ^ (s - k) :=
      pow_le_pow_left₀ hbase hroot _
    _ ≤ R ^ d := pow_le_pow_right₀ hR (by omega)

lemma degeneracySum_le
    {n t m s d : ℕ} (K R : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hK : 0 ≤ K)
    (hR : 1 ≤ R) (hsd : s ≤ d)
    (hroot : 2 * Real.sqrt n / Real.sqrt m ≤ R) :
    (∑ k ∈ Finset.range (s + 1),
        (((t : ℝ) ^ s / Real.sqrt n ^ k) *
          ((2 : ℝ) ^ n * (2 : ℝ) ^ (s - k) /
            Real.sqrt m ^ (s - k) *
              (K * (n : ℝ) ^ (-(3 / 2 : ℝ)))))) ≤
      ((d + 1 : ℕ) : ℝ) *
        ((2 : ℝ) ^ n * (K * (n : ℝ) ^ (-(3 / 2 : ℝ))) *
          (((t : ℝ) / Real.sqrt n) ^ s * R ^ d)) := by
  let common :=
    (2 : ℝ) ^ n * (K * (n : ℝ) ^ (-(3 / 2 : ℝ))) *
      (((t : ℝ) / Real.sqrt n) ^ s * R ^ d)
  have hcommon : 0 ≤ common := by
    dsimp only [common]
    positivity
  calc
    (∑ k ∈ Finset.range (s + 1),
        (((t : ℝ) ^ s / Real.sqrt n ^ k) *
          ((2 : ℝ) ^ n * (2 : ℝ) ^ (s - k) /
            Real.sqrt m ^ (s - k) *
              (K * (n : ℝ) ^ (-(3 / 2 : ℝ)))))) ≤
        ∑ _k ∈ Finset.range (s + 1), common := by
      apply Finset.sum_le_sum
      intro k hk
      have hks : k ≤ s := by
        have := Finset.mem_range.mp hk
        omega
      rw [degeneracyTerm_normalize K hn hm hks]
      dsimp only [common]
      gcongr
      exact degeneracyFactor_le R hks hsd hR hroot
    _ = ((s + 1 : ℕ) : ℝ) * common := by simp
    _ ≤ ((d + 1 : ℕ) : ℝ) * common := by
      gcongr
    _ = _ := by rfl

lemma rawMomentExpectation_upper_of_degeneracySum
    {n t m s d : ℕ} (K R : ℝ)
    (window : Finset (Fin n) → Prop)
    (Y : ℤ → Finset (Fin n) → ℝ) (labels : Finset ℤ)
    (a : ℤ → ℕ)
    (hn : 0 < n) (hm : 0 < m) (hK : 0 ≤ K)
    (hR : 1 ≤ R) (hsd : s ≤ d)
    (hroot : 2 * Real.sqrt n / Real.sqrt m ≤ R)
    (hraw : rawMoment (Finset.univ : Finset (Finset (Fin n)))
        window Y a labels ≤
      ∑ k ∈ Finset.range (s + 1),
        (((t : ℝ) ^ s / Real.sqrt n ^ k) *
          ((2 : ℝ) ^ n * (2 : ℝ) ^ (s - k) /
            Real.sqrt m ^ (s - k) *
              (K * (n : ℝ) ^ (-(3 / 2 : ℝ)))))) :
    rawMomentExpectation (Finset.univ : Finset (Finset (Fin n)))
        window Y a labels ≤
      (((d + 1 : ℕ) : ℝ) * K * R ^ d) *
          ((t : ℝ) / Real.sqrt n) ^ s /
        (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have htwo : 0 < (2 : ℝ) ^ n := by positivity
  have hsum := hraw.trans
    (degeneracySum_le K R hn hm hK hR hsd hroot)
  rw [rawMomentExpectation]
  have hcard : ((Finset.univ : Finset (Finset (Fin n))).card : ℝ) =
      (2 : ℝ) ^ n := by
    norm_num [Nat.cast_pow]
  rw [hcard]
  apply (div_le_iff₀ htwo).2
  apply hsum.trans_eq
  rw [Real.rpow_neg hnpos.le]
  field_simp

lemma two_mul_sqrt_div_sqrt_le
    {n m : ℕ} (gamma : ℝ)
    (hn : 0 < n) (hgamma : 0 < gamma)
    (hmn : gamma * n ≤ m) :
    2 * Real.sqrt n / Real.sqrt m ≤ 2 / Real.sqrt gamma := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hgamma0 : 0 ≤ gamma := hgamma.le
  have hmpos : (0 : ℝ) < m := by
    have : 0 < gamma * (n : ℝ) := mul_pos hgamma (by exact_mod_cast hn)
    exact this.trans_le hmn
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
  have hsqrtgamma : 0 < Real.sqrt gamma := Real.sqrt_pos.2 hgamma
  rw [div_le_div_iff₀ hsqrtm hsqrtgamma]
  calc
    2 * Real.sqrt n * Real.sqrt gamma =
        2 * Real.sqrt (gamma * n) := by
      rw [Real.sqrt_mul hgamma0]
      ring
    _ ≤ 2 * Real.sqrt m := by
      gcongr

lemma rpow_neg_three_halves_le_of_mul_le
    {n N : ℕ} (eta : ℝ)
    (hn : 0 < n) (heta : 0 < eta)
    (hN : eta * n ≤ N) :
    (N : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      eta ^ (-(3 / 2 : ℝ)) *
        (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hbase : 0 < eta * (n : ℝ) :=
    mul_pos heta (by exact_mod_cast hn)
  calc
    (N : ℝ) ^ (-(3 / 2 : ℝ)) ≤
        (eta * (n : ℝ)) ^ (-(3 / 2 : ℝ)) := by
      exact Real.rpow_le_rpow_of_nonpos hbase hN (by norm_num)
    _ = eta ^ (-(3 / 2 : ℝ)) *
        (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.mul_rpow heta.le (by positivity)]

lemma eventually_half_mul_natCast_le_floor_mul
    (gamma : ℝ) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (gamma / 2) * n ≤ (Nat.floor (gamma * n) : ℝ) := by
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, 2 / gamma ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [hlarge] with n hn
  have hhalf : 1 ≤ gamma / 2 * (n : ℝ) := by
    apply (div_le_iff₀ hgamma).mp at hn
    nlinarith
  have hfloor := Nat.lt_floor_add_one (gamma * (n : ℝ))
  nlinarith

lemma eventually_switchingUpper_parameter_bounds
    (D : ℕ) (rho delta base gamma : ℝ)
    (hrho : 0 < rho) (hdelta : 0 < delta) (hbase : 0 < base)
    (hgamma : 0 < gamma)
    (hscaleGap : ((3 ^ D : ℕ) : ℝ) * gamma <
      rho * delta * base)
    (hsupplyGap : ((3 ^ D : ℕ) : ℝ) * delta +
        ((3 ^ D : ℕ) : ℝ) * gamma / base < rho ^ 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ S₀card : ℕ, base * n ≤ S₀card →
      let richFiberSize := Nat.ceil (delta * S₀card)
      let halaszFiberSize := Nat.floor (gamma * n)
      let deletionBudget := 3 ^ D * halaszFiberSize
      0 < richFiberSize ∧ 0 < halaszFiberSize ∧
        (gamma / 2) * n ≤ halaszFiberSize ∧
        ((deletionBudget + 2 : ℕ) : ℝ) ≤
            rho * richFiberSize ∧
        delta * S₀card ≤ richFiberSize ∧
        ∀ s : ℕ, s ≤ D →
          3 ^ s * (halaszFiberSize - 1) ≤ deletionBudget ∧
          ∀ k : ℕ, k ≤ s →
            3 ^ (s - k) * richFiberSize + deletionBudget + 2 ≤
              Nat.ceil (rho ^ 2 * S₀card) := by
  let P : ℝ := ((3 ^ D : ℕ) : ℝ)
  let scaleGap := rho * delta * base - P * gamma
  let supplyGap := rho ^ 2 - (P * delta + P * gamma / base)
  have hscaleGapPos : 0 < scaleGap := by
    dsimp only [scaleGap, P]
    linarith
  have hsupplyGapPos : 0 < supplyGap := by
    dsimp only [supplyGap, P]
    linarith
  have hfloor := eventually_half_mul_natCast_le_floor_mul gamma hgamma
  have hnOne : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n :=
    Filter.eventually_ge_atTop 1
  have hscaleLarge : ∀ᶠ n : ℕ in Filter.atTop,
      2 / scaleGap ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop _)
  have hsupplyLarge : ∀ᶠ n : ℕ in Filter.atTop,
      (P + 2) / (supplyGap * base) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [hfloor, hnOne, hscaleLarge, hsupplyLarge] with
      n hfloor hn hscaleLarge hsupplyLarge
  intro S₀card hS₀
  let richFiberSize := Nat.ceil (delta * (S₀card : ℝ))
  let halaszFiberSize := Nat.floor (gamma * (n : ℝ))
  let deletionBudget := 3 ^ D * halaszFiberSize
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hS₀pos : (0 : ℝ) < S₀card :=
    (mul_pos hbase hnpos).trans_le hS₀
  have hrichLower : delta * (S₀card : ℝ) ≤ richFiberSize := by
    dsimp only [richFiberSize]
    exact_mod_cast Nat.le_ceil _
  have hrichUpper : (richFiberSize : ℝ) ≤
      delta * (S₀card : ℝ) + 1 := by
    dsimp only [richFiberSize]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hrichPos : 0 < richFiberSize := by
    apply Nat.ceil_pos.mpr
    positivity
  have hhalaszPosReal : 0 < (halaszFiberSize : ℝ) := by
    have hleft : 0 < gamma / 2 * (n : ℝ) := by positivity
    exact hleft.trans_le (by simpa only [halaszFiberSize] using hfloor)
  have hhalaszPos : 0 < halaszFiberSize := by exact_mod_cast hhalaszPosReal
  have hfloorUpper : (halaszFiberSize : ℝ) ≤ gamma * n := by
    dsimp only [halaszFiberSize]
    exact Nat.floor_le (by positivity)
  have hbudgetUpper : (deletionBudget : ℝ) ≤ P * gamma * n := by
    calc
      (deletionBudget : ℝ) = P * halaszFiberSize := by
        simp only [deletionBudget, P, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat]
      _ ≤ P * (gamma * n) :=
        mul_le_mul_of_nonneg_left hfloorUpper (by dsimp only [P]; positivity)
      _ = P * gamma * n := by ring
  have hscaleSlack : P * gamma * (n : ℝ) + 2 ≤
      rho * delta * base * n := by
    have hlarge := (div_le_iff₀ hscaleGapPos).mp hscaleLarge
    dsimp only [scaleGap] at hlarge
    nlinarith
  have hscale : ((deletionBudget + 2 : ℕ) : ℝ) ≤
      rho * richFiberSize := by
    calc
      ((deletionBudget + 2 : ℕ) : ℝ) =
          (deletionBudget : ℝ) + 2 := by push_cast; ring
      _ ≤ P * gamma * n + 2 := by gcongr
      _ ≤ rho * delta * base * n := hscaleSlack
      _ ≤ rho * (delta * (S₀card : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hS₀ hdelta.le
        nlinarith
      _ ≤ rho * richFiberSize := by gcongr
  refine ⟨hrichPos, hhalaszPos,
    (by simpa only [halaszFiberSize] using hfloor),
    hscale, hrichLower, ?_⟩
  intro s hsD
  have hpowNat : 3 ^ s ≤ 3 ^ D :=
    Nat.pow_le_pow_right (by omega) hsD
  constructor
  · calc
      3 ^ s * (halaszFiberSize - 1) ≤
          3 ^ D * halaszFiberSize := by gcongr <;> omega
      _ = deletionBudget := by rfl
  · intro k hks
    have hpowsubNat : 3 ^ (s - k) ≤ 3 ^ D :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpowReal : (3 : ℝ) ^ (s - k) ≤ P := by
      dsimp only [P]
      exact_mod_cast hpowsubNat
    have hbudgetSupply : (deletionBudget : ℝ) ≤
        P * gamma / base * S₀card := by
      calc
        (deletionBudget : ℝ) ≤ P * gamma * n := hbudgetUpper
        _ = (P * gamma / base) * (base * n) := by field_simp
        _ ≤ (P * gamma / base) * S₀card := by
          exact mul_le_mul_of_nonneg_left hS₀ (by positivity)
        _ = P * gamma / base * S₀card := by ring
    have hsupplySlack :
        (P * delta + P * gamma / base) * S₀card + P + 2 ≤
          rho ^ 2 * S₀card := by
      have hlarge := (div_le_iff₀ (mul_pos hsupplyGapPos hbase)).mp
        hsupplyLarge
      have hSgap : P + 2 ≤ supplyGap * S₀card := by
        calc
          P + 2 ≤ (n : ℝ) * (supplyGap * base) := hlarge
          _ = supplyGap * (base * n) := by ring
          _ ≤ supplyGap * S₀card := by
            exact mul_le_mul_of_nonneg_left hS₀ hsupplyGapPos.le
      dsimp only [supplyGap] at hSgap
      nlinarith
    have hsupplyReal :
        ((3 ^ (s - k) * richFiberSize + deletionBudget + 2 : ℕ) : ℝ) ≤
          rho ^ 2 * S₀card := by
      push_cast
      have hterm : (3 : ℝ) ^ (s - k) * (richFiberSize : ℝ) ≤
          P * (delta * (S₀card : ℝ) + 1) :=
        mul_le_mul hpowReal hrichUpper (by positivity) (by positivity)
      have hsum := add_le_add (add_le_add hterm hbudgetSupply)
        (le_refl (2 : ℝ))
      calc
        (3 : ℝ) ^ (s - k) * richFiberSize +
              deletionBudget + 2 ≤
            P * (delta * S₀card + 1) +
              (P * gamma / base * S₀card) + 2 := hsum
        _ = (P * delta + P * gamma / base) * S₀card + P + 2 := by
          ring
        _ ≤ rho ^ 2 * S₀card := hsupplySlack
    have hceil : rho ^ 2 * (S₀card : ℝ) ≤
        (Nat.ceil (rho ^ 2 * (S₀card : ℝ)) : ℝ) := by
      exact_mod_cast Nat.le_ceil _
    exact_mod_cast hsupplyReal.trans hceil

noncomputable def canonicalUpperFiberRate
    (d : ℕ) (rho delta base : ℝ) : ℝ :=
  rho * delta * base / (8 * ((3 ^ d : ℕ) : ℝ))

lemma canonicalUpperFiberRate_pos
    (d : ℕ) {rho delta base : ℝ}
    (hrho : 0 < rho) (hdelta : 0 < delta) (hbase : 0 < base) :
    0 < canonicalUpperFiberRate d rho delta base := by
  unfold canonicalUpperFiberRate
  positivity

lemma canonicalUpperFiberRate_gaps
    (d : ℕ) {rho delta base : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hdelta : 0 < delta)
    (hbase : 0 < base)
    (hdeltaBound : delta <
      rho ^ 3 / (3 : ℝ) ^ (2 * d + 1)) :
    let gamma := canonicalUpperFiberRate d rho delta base
    ((3 ^ d : ℕ) : ℝ) * gamma < rho * delta * base ∧
      ((3 ^ d : ℕ) : ℝ) * delta +
          ((3 ^ d : ℕ) : ℝ) * gamma / base < rho ^ 2 := by
  let P : ℝ := ((3 ^ d : ℕ) : ℝ)
  let gamma := canonicalUpperFiberRate d rho delta base
  have hP : 0 < P := by dsimp only [P]; positivity
  have hden : 0 < (3 : ℝ) ^ (2 * d + 1) := by positivity
  have hdenLowerNat : 3 * 3 ^ d ≤ 3 ^ (2 * d + 1) := by
    rw [show 3 * 3 ^ d = 3 ^ (d + 1) by
      simpa only [pow_succ']]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hdenLower : 3 * P ≤ (3 : ℝ) ^ (2 * d + 1) := by
    dsimp only [P]
    exact_mod_cast hdenLowerNat
  have hdeltaMul : delta * (3 : ℝ) ^ (2 * d + 1) < rho ^ 3 :=
    (lt_div_iff₀ hden).mp hdeltaBound
  have hPdelta : 3 * (P * delta) < rho ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_right hdenLower hdelta.le
    nlinarith
  have hrhoCube : rho ^ 3 ≤ rho ^ 2 := by
    nlinarith [sq_nonneg rho, mul_nonneg (sq_nonneg rho) hrho.le]
  have hdeltaRho : delta ≤ rho :=
    delta_le_rho_of_lemma131_bound hrho hrho1 hdeltaBound
  have hfirst : P * gamma < rho * delta * base := by
    dsimp only [gamma, canonicalUpperFiberRate]
    have hmain : P * (rho * delta * base /
        (8 * P)) = rho * delta * base / 8 := by field_simp
    rw [hmain]
    nlinarith [mul_pos (mul_pos hrho hdelta) hbase]
  refine ⟨hfirst, ?_⟩
  have hsecondTerm : P * gamma / base = rho * delta / 8 := by
    dsimp only [P, gamma, canonicalUpperFiberRate]
    field_simp
  rw [hsecondTerm]
  have hPdelta' : P * delta < rho ^ 2 / 3 := by nlinarith
  have hrhodelta : rho * delta ≤ rho ^ 2 := by
    nlinarith [mul_nonneg hrho.le hdelta.le]
  nlinarith [sq_pos_of_pos hrho]

/-- Fixed-radius version of the conditional bounded-window upper count. -/
lemma conditional_edgeScore_window_upper_of_data
    {B N₀ : ℕ} (C H K : ℝ)
    (hdata : ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N₀ ≤ Fintype.card V → FiniteRamseyFree C G →
      ∀ (e₀ : ℝ) (c : V → ℝ),
        (∀ v, 0 ≤ c v ∧ c v ≤ H * Fintype.card V) →
        ∀ x : ℤ,
          Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
              |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
            K * (Fintype.card V : ℝ) ^ (-(3 / 2 : ℝ)))
    {n : ℕ} (G : SimpleGraph (Fin n)) (N O : Finset (Fin n))
    (hON : Disjoint O N) (hNcard : N₀ ≤ N.card)
    (hRamsey : FiniteRamseyFree C (G.induce (N : Set (Fin n))))
    (hc : ∀ v ∈ N, (AKSGraph.degreeInto G v O : ℝ) ≤ H * N.card)
    (x : ℤ) :
    ((N.powerset.filter fun R ↦
        |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) ≤
      K * (N.card : ℝ) ^ (-(3 / 2 : ℝ)) * (2 : ℝ) ^ N.card := by
  classical
  have hsize : N₀ ≤ Fintype.card (N : Set (Fin n)) := by
    simpa only [card_subtype_coe_finset N] using hNcard
  have hcoeff : ∀ v : (N : Set (Fin n)),
      0 ≤ (AKSGraph.degreeInto G v.1 O : ℝ) ∧
        (AKSGraph.degreeInto G v.1 O : ℝ) ≤
          H * Fintype.card (N : Set (Fin n)) := by
    intro v
    constructor
    · positivity
    · simpa only [card_subtype_coe_finset N] using hc v.1 v.2
  have hprob := hdata (N : Set (Fin n))
    (G.induce (N : Set (Fin n))) hsize hRamsey
    (edgeScore G O : ℝ)
    (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)) hcoeff x
  exact card_conditional_edgeScore_window_le_of_probability
    G N O hON x B
      (K * (N.card : ℝ) ^ (-(3 / 2 : ℝ)))
      (by simpa only [card_subtype_coe_finset N] using hprob)

/-- Ambient-normalized conditional window bound at the radius already chosen
by `KSSSBoundedWindow`. -/
theorem exists_uniform_switchingConditional_window_upper_of_data
    {B : ℕ} (C delta base : ℝ)
    (hupper : ∀ H : ℝ, 0 < H →
      ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          N₀ ≤ Fintype.card V → FiniteRamseyFree (2 * C) G →
          ∀ (e₀ : ℝ) (c : V → ℝ),
            (∀ v, 0 ≤ c v ∧ c v ≤ H * Fintype.card V) →
            ∀ x : ℤ,
              Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                  |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
                K * (Fintype.card V : ℝ) ^ (-(3 / 2 : ℝ)))
    (hC : 0 < C) (hdelta : 0 < delta) (hbase : 0 < base) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)), RamseyFree C G →
      ∀ (I : Type) [Fintype I] [DecidableEq I]
        (S S₀ : Finset (Fin n)) (p : I → Fin n × Fin n) (D : ℕ),
        HasLargeCommonNonneighbors G S S₀ delta D →
        2 * Fintype.card I ≤ D →
        (∀ j, p j ∈ S ×ˢ S) →
        base * n ≤ (S₀.card : ℝ) →
        ∀ O ∈ ((Finset.univ : Finset (Fin n)) \
            switchingCommonNonneighbors G p S₀).powerset,
          ∀ x : ℤ,
          (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
              |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) ≤
            (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card *
              (K₀ * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let eta := delta * base
  have heta : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨K, hK, Nwindow, hwindow⟩ := hupper eta⁻¹ (inv_pos.mpr heta)
  obtain ⟨Nsqrt, hsqrt⟩ := exists_sqrt_le_mul_natCast eta heta
  obtain ⟨Nsize, hsize⟩ := exists_nat_rpow_ge
    1 (Nwindow / eta) (by norm_num)
  let K₀ := K * eta ^ (-(3 / 2 : ℝ))
  let N₀ := max 1 (max Nsqrt Nsize)
  have hK₀ : 0 < K₀ := by dsimp only [K₀]; positivity
  refine ⟨K₀, hK₀, N₀, ?_⟩
  intro n hn G hG I instI instDecI S S₀ p D hcommon hID hp hS₀ O hO x
  let N := switchingCommonNonneighbors G p S₀
  have hn1 : 1 ≤ n := by dsimp only [N₀] at hn; omega
  have hnSqrt : Nsqrt ≤ n := by dsimp only [N₀] at hn; omega
  have hnSize : Nsize ≤ n := by dsimp only [N₀] at hn; omega
  have hNlinear : eta * n ≤ (N.card : ℝ) := by
    simpa only [eta, N] using switchingCommonNonneighbors_card_ge_linear
      G S S₀ p delta base D hdelta.le hcommon hID hp hS₀
  have hNwindowReal : (Nwindow : ℝ) ≤ eta * n := by
    have hpow := hsize n hnSize
    rw [Real.rpow_one] at hpow
    simpa only [mul_comm] using (div_le_iff₀ heta).mp hpow
  have hNwindow : Nwindow ≤ N.card := by
    exact_mod_cast hNwindowReal.trans hNlinear
  have hstruct := switchingCommonNonneighbors_boundedWindow_hypotheses
    G S S₀ p hC hn1 hG hdelta hbase hcommon hID hp hS₀
      (by simpa only [eta] using hsqrt n hnSqrt)
  have hON : Disjoint O N := by
    rw [Finset.disjoint_left]
    intro v hvO hvN
    have hv := Finset.mem_powerset.mp hO hvO
    exact (Finset.mem_sdiff.mp hv).2 hvN
  have hraw := conditional_edgeScore_window_upper_of_data
    (B := B) (N₀ := Nwindow) (2 * C) eta⁻¹ K hwindow
    G N O hON hNwindow
      (by simpa only [N] using hstruct.1)
      (by simpa only [eta, N] using hstruct.2 O) x
  have hrpow := rpow_neg_three_halves_le_of_mul_le eta
    (by omega : 0 < n) heta hNlinear
  calc
    (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
        |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) ≤
        K * (N.card : ℝ) ^ (-(3 / 2 : ℝ)) * (2 : ℝ) ^ N.card := by
      simpa only [N] using hraw
    _ ≤ K * (eta ^ (-(3 / 2 : ℝ)) *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) * (2 : ℝ) ^ N.card := by
      gcongr
    _ = (2 : ℝ) ^ N.card *
        (K₀ * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
      dsimp only [K₀]
      ring

lemma ambient_switchingPairs_lower_of_source_bounds
    {n T S : ℕ} (hn : 0 < n)
    (hS : (n : ℝ) ^ (12 / 25 : ℝ) ≤ S)
    (hT : (S : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 ≤ T) :
    (n : ℝ) ^ (24 / 25 : ℝ) / 4 ≤ T := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (12 / 25 : ℝ) *
      (n : ℝ) ^ (12 / 25 : ℝ) =
        (n : ℝ) ^ (24 / 25 : ℝ) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  calc
    (n : ℝ) ^ (24 / 25 : ℝ) / 4 ≤
        (n : ℝ) ^ (24 / 25 : ℝ) / 2 := by
      have := Real.rpow_nonneg hnpos.le (24 / 25 : ℝ)
      linarith
    _ = (n : ℝ) ^ (12 / 25 : ℝ) *
        (n : ℝ) ^ (12 / 25 : ℝ) / 2 := by rw [hpow]
    _ ≤ (S : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 := by
      gcongr
    _ ≤ T := hT

/-- Upper half of the raw-moment comparison required by KSSS Lemma 13.4. -/
def KSSSUnbiasedSwitchingUpperMoments : Prop :=
  ∀ (C A : ℝ), 0 < C → 0 < A →
    ∃ (B : ℕ) (upper : ℝ),
      0 < upper ∧ ∃ N : ℕ,
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n → RamseyFree C G →
          ∀ x : ℕ,
            |(x : ℝ) - (1 / 4 : ℝ) * (G.edgeFinset.card : ℝ)| ≤
                A * (n : ℝ) ^ (3 / 2 : ℝ) →
              ∃ T : Finset (Fin n × Fin n),
                IsSymmetric T ∧ 0 < (T.card : ℝ) / Real.sqrt n ∧
                  ∀ a : ℤ → ℕ,
                    (∀ i ∈ switchingLabels B, a i ≤ 2) →
                      rawMomentExpectation
                          (Finset.univ : Finset (Finset (Fin n)))
                          (fun U ↦ |edgeScore G U - (x : ℤ)| ≤ (B : ℤ))
                          (fun ell U ↦
                            (switchingCount T (edgeScore G) ell U : ℝ))
                          a (switchingLabels B) ≤
                        upper * ((T.card : ℝ) / Real.sqrt n) ^
                            (∑ i ∈ switchingLabels B, a i) /
                          (n : ℝ) ^ (3 / 2 : ℝ)

/-- The upper half of KSSS Lemma 13.4 follows from the fixed-radius
bounded-window input, Lemma 13.1, Lemma 13.10, and the finite Halasz bound. -/
theorem ksssUnbiasedSwitchingUpperMoments_of_boundedWindow
    (hBW : KSSSBoundedWindow) : KSSSUnbiasedSwitchingUpperMoments := by
  intro C A hC hA
  obtain ⟨B, hB, hupperData, _hlowerData⟩ :=
    hBW (2 * C) (mul_pos (by norm_num) hC)
  let d := 4 * B + 2
  let D := 2 * d
  have hD : 0 < D := by dsimp only [D, d]; omega
  obtain ⟨rho, delta, hrho, hrho1, hdelta, hdeltaBound,
      Nrich, hrichData⟩ :=
    ksssLemma131 C 1 hC (by norm_num) D hD
  have hdeltaRho : delta ≤ rho :=
    delta_le_rho_of_lemma131_bound hrho hrho1 hdeltaBound
  let base := delta ^ (1 / rho)
  have hbase : 0 < base := by dsimp only [base]; positivity
  let gamma := canonicalUpperFiberRate d rho delta base
  have hgamma : 0 < gamma :=
    canonicalUpperFiberRate_pos d hrho hdelta hbase
  have hdeltaBound' : delta <
      rho ^ 3 / (3 : ℝ) ^ (2 * d + 1) := by
    simpa only [D] using hdeltaBound
  have hgaps := canonicalUpperFiberRate_gaps d hrho hrho1 hdelta hbase
    hdeltaBound'
  obtain ⟨K₀, hK₀, Nwindow, hwindowData⟩ :=
    exists_uniform_switchingConditional_window_upper_of_data
      (B := B) C delta base hupperData hC hdelta hbase
  obtain ⟨Nparam, hparamData⟩ := Filter.eventually_atTop.1
    (eventually_switchingUpper_parameter_bounds d rho delta base gamma
      hrho hdelta hbase hgamma hgaps.1 hgaps.2)
  obtain ⟨Nratio, hratioData⟩ := Filter.eventually_atTop.1
    (eventually_switchingDegeneracy_ratio d)
  obtain ⟨Npair, hpairData⟩ := Filter.eventually_atTop.1
    eventually_switchingPairs_large_from_lemma131_sizes
  let fiberRate := gamma / 2
  let R := max 1 (2 / Real.sqrt fiberRate)
  let upper := ((d + 1 : ℕ) : ℝ) * K₀ * R ^ d
  have hfiberRate : 0 < fiberRate := by dsimp only [fiberRate]; positivity
  have hR : 1 ≤ R := le_max_left _ _
  have hupper : 0 < upper := by
    dsimp only [upper]
    have hd : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
    positivity
  refine ⟨B, upper, hupper,
    max 1 (max Nrich (max Nwindow (max Nparam (max Nratio Npair)))), ?_⟩
  intro n G hn hG x _hx
  have hn1 : 1 ≤ n := by omega
  have hnRich : Nrich ≤ n := by omega
  have hnWindow : Nwindow ≤ n := by omega
  have hnParam : Nparam ≤ n := by omega
  have hnRatio : Nratio ≤ n := by omega
  have hnPair : Npair ≤ n := by omega
  obtain ⟨S, S₀, hSS₀, hS, hS₀, hrich, hcommon, hdegree⟩ :=
    hrichData n hnRich G hG (fun _ ↦ 0) (by
      intro v
      constructor <;> norm_num)
  let q := switchingThreshold rho S₀
  let T := switchingPairs G S S₀ q
  have hTlarge : (S.card : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 ≤
      (T.card : ℝ) := by
    simpa only [T, q] using
      hpairData n hnPair G S S₀ delta rho hSS₀ hS hrich
        hrho hrho1.le hdeltaRho
  have hTambient : (n : ℝ) ^ (24 / 25 : ℝ) / 4 ≤
      (T.card : ℝ) :=
    ambient_switchingPairs_lower_of_source_bounds (by omega) hS hTlarge
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hSp : 0 < (S.card : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hS
  have hTp : 0 < (T.card : ℝ) := by
    have hleft : 0 < (S.card : ℝ) *
        (n : ℝ) ^ (12 / 25 : ℝ) / 2 := by positivity
    exact hleft.trans_le hTlarge
  have hS₀n : (S₀.card : ℝ) ≤ n := by
    exact_mod_cast (show S₀.card ≤ n by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ S₀))
  let codeBound := ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊
  have hcode : (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤ codeBound := by
    calc
      (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤
          (n : ℝ) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hS₀n (by norm_num)
      _ ≤ codeBound := by
        dsimp only [codeBound]
        exact_mod_cast Nat.le_ceil _
  let richFiberSize := Nat.ceil (delta * (S₀.card : ℝ))
  let halaszFiberSize := Nat.floor (gamma * (n : ℝ))
  let deletionBudget := 3 ^ d * halaszFiberSize
  have hparams := hparamData n hnParam S₀.card (by simpa only [base] using hS₀)
  change 0 < richFiberSize ∧ 0 < halaszFiberSize ∧
      fiberRate * n ≤ halaszFiberSize ∧
      ((deletionBudget + 2 : ℕ) : ℝ) ≤ rho * richFiberSize ∧
      delta * S₀.card ≤ richFiberSize ∧
      ∀ s : ℕ, s ≤ d →
        3 ^ s * (halaszFiberSize - 1) ≤ deletionBudget ∧
        ∀ k : ℕ, k ≤ s →
          3 ^ (s - k) * richFiberSize + deletionBudget + 2 ≤ q at hparams
  have hroot : 2 * Real.sqrt n / Real.sqrt halaszFiberSize ≤ R := by
    exact (two_mul_sqrt_div_sqrt_le fiberRate (by omega) hfiberRate
      hparams.2.2.1).trans (le_max_right _ _)
  refine ⟨T, switchingPairs_isSymmetric G S S₀ q,
    div_pos hTp (Real.sqrt_pos.2 hnpos), ?_⟩
  intro a ha
  let s := Fintype.card (RawTupleIndex (switchingLabels B) a)
  have hsd : s ≤ d := by
    dsimp only [s, d]
    simpa only [Nat.card_eq_fintype_card] using
      switchingTuple_dimension_le a ha
  have hID : 2 * s ≤ D := by dsimp only [D]; omega
  have hnum := hparams.2.2.2.2.2 s hsd
  have hraw := rawMoment_switchingCount_le_of_lemma1310_and_conditional_window
    (n := n) (by omega) G S S₀ delta rho (1 / 5 : ℝ)
      q deletionBudget richFiberSize halaszFiberSize codeBound
      (switchingLabels B) a
      (fun U ↦ |edgeScore G U - (x : ℤ)| ≤ (B : ℤ))
      (K₀ * (n : ℝ) ^ (-(3 / 2 : ℝ))) (by positivity)
      hparams.1 hparams.2.1 hrho.le hrich hSS₀
      hparams.2.2.2.1 hparams.2.2.2.2.1 hcode hnum.1
      (by
        intro k hkpos hks
        exact hnum.2 k hks)
      (by
        intro k hkpos hks
        exact (hratioData n hnRatio s k T.card hsd hkpos hks hTambient).1)
      (by
        intro k hkpos hks
        exact (hratioData n hnRatio s k T.card hsd hkpos hks hTambient).2)
      (by
        intro p hpT O hO
        have hpS : ∀ j, p j ∈ S ×ˢ S := by
          intro j
          have hj := (mem_switchingPairs_iff G S S₀ q
            (p j).1 (p j).2).mp (by simpa only [T] using hpT j)
          exact Finset.mem_product.mpr ⟨hj.1, hj.2.1⟩
        have hw := hwindowData n hnWindow G hG
          (RawTupleIndex (switchingLabels B) a) S S₀ p D hcommon
          (by simpa only [s] using hID) hpS (by simpa only [base] using hS₀)
          O hO (x : ℤ)
        convert hw using 1
        apply congrArg (fun z : ℕ ↦ (z : ℝ))
        apply congrArg Finset.card
        ext Rset
        simp only [Finset.mem_filter, Finset.mem_powerset])
  dsimp only [upper]
  rw [show (∑ i ∈ switchingLabels B, a i) = s by
    simpa only [s, Nat.card_eq_fintype_card] using
      (card_rawTupleIndex (switchingLabels B) a).symm]
  exact rawMomentExpectation_upper_of_degeneracySum
    K₀ R
      (fun U ↦ |edgeScore G U - (x : ℤ)| ≤ (B : ℤ))
      (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
      (switchingLabels B) a (by omega) hparams.2.1 hK₀.le hR hsd hroot
      (by simpa only [T, s] using hraw)


end Erdos88.Switching

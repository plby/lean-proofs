import PrimeNumberTheoremAnd.Consequences

/-! # Prime reciprocals in arithmetic progressions -/

open Filter Finset Asymptotics
open scoped Topology

noncomputable section

namespace Nat.Primes

/-- Disjoint finite blocks with harmonic lower bounds force divergence. -/
private lemma not_summable_of_disjoint_harmonic_blocks
    {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (F : ℕ → Finset ι)
    (hdisj : ∀ {m n}, m ≠ n → Disjoint (F m) (F n))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ n, c / (n + 1 : ℕ) ≤ ∑ i ∈ F n, w i) :
    ¬Summable w := by
  intro hsum
  let e : (Σ n, ↥(F n)) → ι := fun x ↦ x.2
  have he : Function.Injective e := by
    rintro ⟨m, i⟩ ⟨n, j⟩ hij
    dsimp [e] at hij
    by_cases hmn : m = n
    · subst n
      simp_all
    · exact (Finset.disjoint_left.mp (hdisj hmn) i.2 (hij ▸ j.2)).elim
  have hsigma : Summable (fun x : (Σ n, ↥(F n)) ↦ w (e x)) :=
    hsum.comp_injective he
  have hblocksTsum :
      Summable (fun n ↦ ∑' i : ↥(F n), w i) :=
    ((summable_sigma_of_nonneg (fun x ↦ hw (e x))).1 hsigma).2
  have hblocks :
      Summable (fun n ↦ ∑ i ∈ F n, w i) := by
    convert hblocksTsum using 1
    funext n
    rw [tsum_fintype]
    simpa only [Finset.univ_eq_attach] using (Finset.sum_attach (F n) w).symm
  have hlowerSummable : Summable (fun n : ℕ ↦ c / (n + 1 : ℕ)) :=
    Summable.of_nonneg_of_le
      (fun _ ↦ by positivity) hlower hblocks
  have hshiftedHarmonic :
      ¬Summable (fun n : ℕ ↦ (1 : ℝ) / (n + 1 : ℕ)) := by
    exact_mod_cast
      mt (summable_nat_add_iff 1).1 Real.not_summable_one_div_natCast
  apply hshiftedHarmonic
  have hscaled := hlowerSummable.mul_left c⁻¹
  exact hscaled.congr fun n ↦ by
    field_simp [hc.ne']

/-- Chebyshev's `θ`-sum restricted to one residue class. -/
private noncomputable def residueTheta
    (M : ℕ) [NeZero M] (a : ZMod M) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
    if p % M = a.val then Real.log p else 0

/-- Prime number theorem in an invertible residue class, in the form needed below. -/
private lemma residueTheta_isEquivalent
    (M : ℕ) [NeZero M] (a : ZMod M) (ha : IsUnit a) :
    (residueTheta M a) ~[atTop] (fun x : ℝ ↦ x / M.totient) := by
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have haCoprime : a.val.Coprime M := by
    rw [← ZMod.isUnit_iff_coprime]
    simpa using ha
  change
    (fun x : ℝ ↦
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        if p % M = a.val then Real.log p else 0) ~[atTop]
      (fun x : ℝ ↦ x / M.totient)
  exact chebyshev_asymptotic_pnt hM haCoprime a.val_lt

/-- Eventually `residueTheta` lies between `3/4` and `5/4` of its main term. -/
private lemma eventually_residueTheta_bounds
    (M : ℕ) [NeZero M] (a : ZMod M) (ha : IsUnit a) :
    ∀ᶠ x : ℝ in atTop,
      3 * x / (4 * M.totient) ≤ residueTheta M a x ∧
      residueTheta M a x ≤ 5 * x / (4 * M.totient) := by
  have hφ : (0 : ℝ) < M.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M))
  have hden :
      ∀ᶠ x : ℝ in atTop, x / (M.totient : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_ne_zero hx.ne' hφ.ne'
  have hratio :
      Tendsto
        (fun x : ℝ ↦ residueTheta M a x / (x / M.totient))
        atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hden).mp
      (residueTheta_isEquivalent M a ha)
  have hclose :
      ∀ᶠ x : ℝ in atTop,
        |residueTheta M a x / (x / M.totient) - 1| < 1 / 4 :=
    hratio.eventually (Metric.ball_mem_nhds 1 (by norm_num))
  filter_upwards [hclose, eventually_gt_atTop (0 : ℝ)] with x hxclose hx
  have hmain : 0 < x / (M.totient : ℝ) := _root_.div_pos hx hφ
  have hratioBounds :
      (3 / 4 : ℝ) <
          residueTheta M a x / (x / M.totient) ∧
        residueTheta M a x / (x / M.totient) < 5 / 4 := by
    rw [abs_lt] at hxclose
    constructor <;> linarith
  have hleft :
      (3 / 4 : ℝ) * (x / M.totient) < residueTheta M a x :=
    (lt_div_iff₀ hmain).mp hratioBounds.1
  have hright :
      residueTheta M a x < (5 / 4 : ℝ) * (x / M.totient) :=
    (div_lt_iff₀ hmain).mp hratioBounds.2
  have hφne : (M.totient : ℝ) ≠ 0 := hφ.ne'
  constructor
  · have heq :
        3 * x / (4 * (M.totient : ℝ)) =
          (3 / 4 : ℝ) * (x / M.totient) := by
        field_simp
    rw [heq]
    exact hleft.le
  · have heq :
        5 * x / (4 * (M.totient : ℝ)) =
          (5 / 4 : ℝ) * (x / M.totient) := by
        field_simp
    rw [heq]
    exact hright.le

/-- The cast formulation of a residue condition agrees with the `%` formulation. -/
private lemma natCast_eq_iff_mod_eq_val
    (M : ℕ) [NeZero M] (a : ZMod M) (p : ℕ) :
    (p : ZMod M) = a ↔ p % M = a.val := by
  rw [← ZMod.natCast_zmod_val a, ZMod.natCast_eq_natCast_iff']
  simp [Nat.mod_eq_of_lt a.val_lt]

/-- Primes in a half-open interval and in one residue class. -/
private def residuePrimeBlock
    (M : ℕ) [NeZero M] (a : ZMod M) (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter fun p ↦ p.Prime ∧ (p : ZMod M) = a

/-- At a natural argument, `residueTheta` is the corresponding finite logarithmic sum. -/
private lemma residueTheta_nat
    (M : ℕ) [NeZero M] (a : ZMod M) (N : ℕ) :
    residueTheta M a N =
      ∑ p ∈ (Finset.Iic N).filter
          (fun p : ℕ ↦ p.Prime ∧ (p : ZMod M) = a),
        Real.log p := by
  classical
  simp only [residueTheta, Nat.floor_natCast, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · by_cases hres : (p : ZMod M) = a
    · simp [hprime, hres, (natCast_eq_iff_mod_eq_val M a p).mp hres]
    · simp [hprime, hres, (natCast_eq_iff_mod_eq_val M a p).not.mp hres]
  · simp [hprime]

/-- The increment of `residueTheta` across a natural interval is its block log-sum. -/
private lemma residueTheta_sub_eq_sum_block
    (M : ℕ) [NeZero M] (a : ZMod M) {L U : ℕ} (hLU : L ≤ U) :
    residueTheta M a U - residueTheta M a L =
      ∑ p ∈ residuePrimeBlock M a L U, Real.log p := by
  classical
  rw [residueTheta_nat, residueTheta_nat]
  let pred : ℕ → Prop := fun p ↦ p.Prime ∧ (p : ZMod M) = a
  let left := (Finset.Iic L).filter pred
  let block := (Finset.Ioc L U).filter pred
  have hdis : Disjoint left block := by
    exact (Finset.Iic_disjoint_Ioc le_rfl).mono
      (Finset.filter_subset pred (Finset.Iic L))
      (Finset.filter_subset pred (Finset.Ioc L U))
  have hunion : left ∪ block = (Finset.Iic U).filter pred := by
    dsimp [left, block]
    rw [← Finset.filter_union, Finset.Iic_union_Ioc_eq_Iic hLU]
  have hsum :=
    Finset.sum_union hdis (f := fun p : ℕ ↦ Real.log p)
  rw [hunion] at hsum
  dsimp [left, block, pred] at hsum
  rw [residuePrimeBlock]
  linarith

/--
The elementary partial-summation estimate needed for a dyadic block.  The
PNT bounds at `L` and `2L` force a definite reciprocal mass in that block.
-/
private lemma residuePrimeBlock_inv_lower
    (M : ℕ) [NeZero M] (a : ZMod M) {L : ℕ} (hL : 1 ≤ L)
    (hlow :
      3 * (2 * (L : ℝ)) / (4 * M.totient) ≤
        residueTheta M a (2 * L))
    (hupp :
      residueTheta M a L ≤
        5 * (L : ℝ) / (4 * M.totient)) :
    1 / (8 * (M.totient : ℝ) * Real.log (2 * L)) ≤
      ∑ p ∈ residuePrimeBlock M a L (2 * L), (1 : ℝ) / p := by
  have hφ : (0 : ℝ) < M.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M))
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have htwoL : (1 : ℝ) < 2 * L := by
    exact_mod_cast (show 1 < 2 * L by omega)
  have hlog : 0 < Real.log (2 * (L : ℝ)) := Real.log_pos htwoL
  have hden : 0 < (2 * (L : ℝ)) * Real.log (2 * L) :=
    mul_pos (by positivity) hlog
  have htheta :
      (L : ℝ) / (4 * M.totient) ≤
        residueTheta M a (2 * L) - residueTheta M a L := by
    calc
      (L : ℝ) / (4 * M.totient) =
          3 * (2 * (L : ℝ)) / (4 * M.totient) -
            5 * (L : ℝ) / (4 * M.totient) := by
              field_simp
              ring
      _ ≤ residueTheta M a (2 * L) - residueTheta M a L :=
        sub_le_sub hlow hupp
  have hpoint :
      ∀ p ∈ residuePrimeBlock M a L (2 * L),
        Real.log p / ((2 * (L : ℝ)) * Real.log (2 * L)) ≤
          (1 : ℝ) / p := by
    intro p hp
    have hpdata := (Finset.mem_filter.mp hp)
    have hpinterval := Finset.mem_Ioc.mp hpdata.1
    have hpprime : p.Prime := hpdata.2.1
    have hppos : (0 : ℝ) < p := by
      exact_mod_cast hpprime.pos
    have hpone : (1 : ℝ) < p := by
      exact_mod_cast hpprime.one_lt
    have hplog : 0 ≤ Real.log p := (Real.log_pos hpone).le
    have hple : (p : ℝ) ≤ 2 * L := by exact_mod_cast hpinterval.2
    have hlogle : Real.log p ≤ Real.log (2 * L) :=
      Real.log_le_log hppos hple
    apply (div_le_iff₀ hden).2
    have hreorder :
        (1 : ℝ) / p * ((2 * (L : ℝ)) * Real.log (2 * L)) =
          ((2 * (L : ℝ)) * Real.log (2 * L)) / p := by
      field_simp
    rw [hreorder]
    apply (le_div_iff₀ hppos).2
    nlinarith
  have hsum :
      (residueTheta M a (2 * L) - residueTheta M a L) /
          ((2 * (L : ℝ)) * Real.log (2 * L)) ≤
        ∑ p ∈ residuePrimeBlock M a L (2 * L), (1 : ℝ) / p := by
    have hthetaSum :=
      residueTheta_sub_eq_sum_block M a (L := L) (U := 2 * L) (by omega)
    norm_num only [Nat.cast_ofNat, Nat.cast_mul] at hthetaSum
    rw [hthetaSum, Finset.sum_div]
    exact Finset.sum_le_sum fun p hp ↦ hpoint p hp
  calc
    1 / (8 * (M.totient : ℝ) * Real.log (2 * L)) =
        ((L : ℝ) / (4 * M.totient)) /
          ((2 * (L : ℝ)) * Real.log (2 * L)) := by
            field_simp
            ring
    _ ≤ (residueTheta M a (2 * L) - residueTheta M a L) /
          ((2 * (L : ℝ)) * Real.log (2 * L)) :=
      (div_le_div_iff_of_pos_right hden).2 htheta
    _ ≤ _ := hsum

/-- The reciprocal series over the primes in an invertible residue class diverges. -/
theorem residue_reciprocals_not_summable
    (M : ℕ) [NeZero M] (a : ZMod M) (ha : IsUnit a) :
    ¬Summable
      (fun p : ℕ ↦
        if p.Prime ∧ (p : ZMod M) = a then (1 : ℝ) / p else 0) := by
  let bounds : ℝ → Prop := fun x ↦
    3 * x / (4 * M.totient) ≤ residueTheta M a x ∧
      residueTheta M a x ≤ 5 * x / (4 * M.totient)
  have hpows :
      Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent : ∀ᶠ n : ℕ in atTop, bounds ((2 : ℝ) ^ n) :=
    hpows.eventually (eventually_residueTheta_bounds M a ha)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let k := N + 1
  let F : ℕ → Finset ℕ := fun n ↦
    residuePrimeBlock M a (2 ^ (n + k)) (2 * 2 ^ (n + k))
  let w : ℕ → ℝ := fun p ↦
    if p.Prime ∧ (p : ZMod M) = a then (1 : ℝ) / p else 0
  have hkpos : 0 < k := by simp [k]
  have hφ : (0 : ℝ) < M.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M))
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply not_summable_of_disjoint_harmonic_blocks w
    (F := F)
    (c := 1 / (8 * (M.totient : ℝ) * (k + 1) * Real.log 2))
  · intro p
    simp only [w]
    split_ifs <;> positivity
  · intro m n hmn
    have hfilterSubset :
        ∀ L U, residuePrimeBlock M a L U ⊆ Finset.Ioc L U :=
      fun L U ↦ Finset.filter_subset _ _
    rcases lt_or_gt_of_ne hmn with hmnlt | hmnlt
    · have hgap :
          2 * 2 ^ (m + k) ≤ 2 ^ (n + k) := by
        calc
          2 * 2 ^ (m + k) = 2 ^ (m + k + 1) := by
            rw [pow_succ]
            omega
          _ ≤ 2 ^ (n + k) :=
            Nat.pow_le_pow_right (by omega) (by omega)
      exact (Finset.Ioc_disjoint_Ioc_of_le hgap).mono
        (hfilterSubset _ _) (hfilterSubset _ _)
    · have hgap :
          2 * 2 ^ (n + k) ≤ 2 ^ (m + k) := by
        calc
          2 * 2 ^ (n + k) = 2 ^ (n + k + 1) := by
            rw [pow_succ]
            omega
          _ ≤ 2 ^ (m + k) :=
            Nat.pow_le_pow_right (by omega) (by omega)
      exact ((Finset.Ioc_disjoint_Ioc_of_le hgap).mono
        (hfilterSubset _ _) (hfilterSubset _ _)).symm
  · positivity
  · intro n
    let L : ℕ := 2 ^ (n + k)
    have hNk : N ≤ n + k := by
      dsimp [k]
      omega
    have hNk' : N ≤ n + k + 1 := hNk.trans (Nat.le_succ _)
    have hbL : bounds (L : ℝ) := by
      have h := hN (n + k) hNk
      simpa only [L, Nat.cast_pow, Nat.cast_ofNat] using h
    have hb2L : bounds (2 * (L : ℝ)) := by
      have h := hN (n + k + 1) hNk'
      have hpow :
          (2 : ℝ) ^ (n + k + 1) = 2 * (L : ℝ) := by
        norm_num only [L, Nat.cast_pow, Nat.cast_ofNat]
        rw [pow_succ]
        ring
      rwa [hpow] at h
    have hLone : 1 ≤ L := by
      simpa [L] using Nat.one_le_pow' (n + k) 1
    have hblock :
        1 / (8 * (M.totient : ℝ) * Real.log (2 * L)) ≤
          ∑ p ∈ residuePrimeBlock M a L (2 * L), (1 : ℝ) / p :=
      residuePrimeBlock_inv_lower M a hLone hb2L.1 hbL.2
    have hlogeq :
        Real.log (2 * (L : ℝ)) =
          (n + k + 1 : ℕ) * Real.log 2 := by
      have hpow :
          2 * (L : ℝ) = (2 : ℝ) ^ (n + k + 1) := by
        norm_num only [L, Nat.cast_pow, Nat.cast_ofNat]
        rw [pow_succ]
        ring
      rw [hpow, Real.log_pow]
    have hexp :
        n + k + 1 ≤ (n + 1) * (k + 1) := by
      nlinarith
    have hdenpos :
        0 < 8 * (M.totient : ℝ) *
            ((n + k + 1 : ℕ) * Real.log 2) := by
      positivity
    have hdenle :
        8 * (M.totient : ℝ) *
              ((n + k + 1 : ℕ) * Real.log 2) ≤
          8 * (M.totient : ℝ) *
              (((n + 1 : ℕ) * (k + 1 : ℕ)) * Real.log 2) := by
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
      have hexp' :
          (n : ℝ) + k + 1 ≤ ((n : ℝ) + 1) * ((k : ℝ) + 1) := by
        exact_mod_cast hexp
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hexp' hlogTwo.le) (by positivity)
    calc
      (1 / (8 * (M.totient : ℝ) * (k + 1) * Real.log 2)) /
            (n + 1 : ℕ) =
          1 /
            (8 * (M.totient : ℝ) *
              (((n + 1 : ℕ) * (k + 1 : ℕ)) * Real.log 2)) := by
            norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
            field_simp
      _ ≤ 1 /
            (8 * (M.totient : ℝ) *
              ((n + k + 1 : ℕ) * Real.log 2)) :=
        one_div_le_one_div_of_le hdenpos hdenle
      _ = 1 / (8 * (M.totient : ℝ) * Real.log (2 * L)) := by
        rw [hlogeq]
      _ ≤ ∑ p ∈ residuePrimeBlock M a L (2 * L), (1 : ℝ) / p :=
        hblock
      _ = ∑ p ∈ F n, w p := by
        apply Finset.sum_congr
        · simp [F, L]
        · intro p hp
          have hpdata := (Finset.mem_filter.mp hp).2
          simp [w, hpdata]

end Nat.Primes

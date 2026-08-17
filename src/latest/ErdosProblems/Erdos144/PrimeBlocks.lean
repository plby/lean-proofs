import PrimeNumberTheoremAnd.Consequences

/-!
# Prime blocks for Erdős Problem 144

This file contains finite and analytic inputs for replacing harmonic Bernoulli
coordinates by divisibility by primes.  The qualitative prime number theorem
controls every fixed multiplicative block ratio.  A use in which the block
resolution grows simultaneously with the combinatorial scale needs either a
separate diagonal synchronization argument or a stronger quantitative prime
estimate.
-/

namespace Erdos144.PrimeBlocks

open Filter Finset Real Asymptotics
open scoped Topology BigOperators

/-- The primes in the real half-open interval `(x, r * x]`. -/
noncomputable def block (r x : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊x⌋₊ ⌊r * x⌋₊).filter Nat.Prime

/-- Reciprocal prime mass of a block. -/
noncomputable def mass (r x : ℝ) : ℝ :=
  ∑ p ∈ block r x, (p : ℝ)⁻¹

/-- The probability that at least one prime in the block divides a uniformly
random residue class modulo their product. -/
noncomputable def occupancy (r x : ℝ) : ℝ :=
  1 - ∏ p ∈ block r x, (1 - (p : ℝ)⁻¹)

lemma block_card_eq (r x : ℝ) (hrx : x ≤ r * x) :
    (block r x).card = Nat.primeCounting ⌊r * x⌋₊ - Nat.primeCounting ⌊x⌋₊ := by
  have hfloor : ⌊x⌋₊ ≤ ⌊r * x⌋₊ := Nat.floor_mono hrx
  let A := (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime
  let B := (Finset.range (⌊r * x⌋₊ + 1)).filter Nat.Prime
  have hsub : A ⊆ B := by
    intro p hp
    simp only [A, B, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ hfloor), hp.2⟩
  have heq : block r x = B \ A := by
    ext p
    simp only [block, A, B, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨ha, hb⟩, hp⟩
      exact ⟨⟨Nat.lt_succ_iff.mpr hb, hp⟩,
        fun h ↦ (not_le_of_gt ha) (Nat.lt_succ_iff.mp h.1)⟩
    · rintro ⟨⟨hb, hp⟩, hnot⟩
      have ha : ⌊x⌋₊ < p := lt_of_not_ge fun h ↦ hnot ⟨Nat.lt_succ_iff.mpr h, hp⟩
      exact ⟨⟨ha, Nat.lt_succ_iff.mp hb⟩, hp⟩
  rw [heq, Finset.card_sdiff_of_subset hsub]
  simp only [A, B, Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
  simp only [Nat.primesBelow]

lemma mem_block {r x : ℝ} {p : ℕ} (hrx : 0 ≤ r * x) (hp : p ∈ block r x) :
    Nat.Prime p ∧ x < p ∧ (p : ℝ) ≤ r * x := by
  simp only [block, Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨hp.2, ?_, ?_⟩
  · exact (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast Nat.succ_le_of_lt hp.1.1)
  · exact (by exact_mod_cast hp.1.2 : (p : ℝ) ≤ (⌊r * x⌋₊ : ℕ)).trans (Nat.floor_le hrx)

lemma mass_nonneg (r x : ℝ) : 0 ≤ mass r x := by
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Crude but uniform bounds for the reciprocal mass in a multiplicative
block.  They are the bridge from the PNT prime count to Bernoulli parameters. -/
lemma card_div_upper_le_mass_le_card_div_lower {r x : ℝ}
    (hx : 0 < x) (hr : 0 < r) :
    ((block r x).card : ℝ) / (r * x) ≤ mass r x ∧
      mass r x ≤ ((block r x).card : ℝ) / x := by
  have hrx : 0 < r * x := mul_pos hr hx
  constructor
  · rw [mass, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum fun p hp ↦ by
      have hpmem := mem_block hrx.le hp
      simpa only [Nat.cast_one, one_div] using
        (one_div_le_one_div_of_le (by exact_mod_cast hpmem.1.pos) hpmem.2.2)
  · rw [mass, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum fun p hp ↦ by
      have hpmem := mem_block hrx.le hp
      simpa only [Nat.cast_one, one_div] using
        (one_div_le_one_div_of_le hx hpmem.2.1.le)

/-- The elementary second-order Bonferroni estimate, in the exact form needed
for the probability that a finite family of independent events has nonempty
union. -/
lemma one_sub_prod_bounds {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    let q := 1 - ∏ i ∈ s, (1 - a i)
    let S := ∑ i ∈ s, a i
    0 ≤ q ∧ q ≤ 1 ∧ q ≤ S ∧ S - q ≤ S ^ 2 / 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hai0 : 0 ≤ a i := ha0 i (Finset.mem_insert_self i s)
      have hai1 : a i ≤ 1 := ha1 i (Finset.mem_insert_self i s)
      have ih' := ih (fun j hj ↦ ha0 j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ ha1 j (Finset.mem_insert_of_mem hj))
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      dsimp only at ih' ⊢
      rcases ih' with ⟨hq0, hq1, hqS, herr⟩
      constructor
      · nlinarith [mul_nonneg hai0 (sub_nonneg.mpr hq1)]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr hai1) (sub_nonneg.mpr hq1)]
      constructor
      · nlinarith [mul_nonneg hai0 hq0]
      · nlinarith [sq_nonneg (a i)]

lemma occupancy_bounds (r x : ℝ) :
    0 ≤ occupancy r x ∧ occupancy r x ≤ 1 ∧
      occupancy r x ≤ mass r x ∧
      mass r x - occupancy r x ≤ (mass r x) ^ 2 / 2 := by
  apply one_sub_prod_bounds (block r x) (fun p ↦ (p : ℝ)⁻¹)
  · intro p hp
    exact inv_nonneg.mpr (Nat.cast_nonneg p)
  · intro p hp
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hprime.one_le)

lemma abs_occupancy_sub_mass_le (r x : ℝ) :
    |occupancy r x - mass r x| ≤ (mass r x) ^ 2 / 2 := by
  have h := occupancy_bounds r x
  rw [abs_of_nonpos (sub_nonpos.mpr h.2.2.1)]
  linarith [h.2.2.2]

/-- Any approximation to the reciprocal mass transfers to the actual CRT
occupancy probability, at a quadratic cost. -/
lemma abs_occupancy_sub_le (r x target err : ℝ)
    (hmass : |mass r x - target| ≤ err) :
    |occupancy r x - target| ≤ err + (mass r x) ^ 2 / 2 := by
  calc
    |occupancy r x - target| ≤
        |occupancy r x - mass r x| + |mass r x - target| := by
          simpa only [sub_add_sub_cancel] using
            abs_add_le (occupancy r x - mass r x) (mass r x - target)
    _ ≤ err + (mass r x) ^ 2 / 2 := by
      linarith [abs_occupancy_sub_mass_le r x]

/-- Logarithmic prime blocks of resolution `K`. -/
noncomputable def logBlock (K i : ℕ) : Finset ℕ :=
  block (Real.exp ((K : ℝ)⁻¹)) (Real.exp ((i : ℝ) / K))

noncomputable def logBlockMass (K i : ℕ) : ℝ :=
  mass (Real.exp ((K : ℝ)⁻¹)) (Real.exp ((i : ℝ) / K))

noncomputable def logBlockOccupancy (K i : ℕ) : ℝ :=
  occupancy (Real.exp ((K : ℝ)⁻¹)) (Real.exp ((i : ℝ) / K))

lemma mem_logBlock {K i p : ℕ} (hK : 0 < K) (hp : p ∈ logBlock K i) :
    Nat.Prime p ∧ Real.exp ((i : ℝ) / K) < p ∧
      (p : ℝ) ≤ Real.exp (((i + 1 : ℕ) : ℝ) / K) := by
  have hmem := mem_block (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hp
  refine ⟨hmem.1, hmem.2.1, ?_⟩
  calc
    (p : ℝ) ≤ Real.exp ((K : ℝ)⁻¹) * Real.exp ((i : ℝ) / K) := hmem.2.2
    _ = Real.exp ((K : ℝ)⁻¹ + (i : ℝ) / K) := (Real.exp_add _ _).symm
    _ = Real.exp (((i + 1 : ℕ) : ℝ) / K) := by
      congr 1
      norm_num only [Nat.cast_add, Nat.cast_one]
      field_simp
      ring

lemma mem_logBlock_log_bounds {K i p : ℕ} (hK : 0 < K) (hp : p ∈ logBlock K i) :
    (i : ℝ) / K < Real.log p ∧
      Real.log p ≤ ((i + 1 : ℕ) : ℝ) / K := by
  have hm := mem_logBlock hK hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hm.1.pos
  constructor
  · apply (Real.exp_lt_exp).mp
    simpa [Real.exp_log hp0] using hm.2.1
  · apply (Real.exp_le_exp).mp
    simpa [Real.exp_log hp0] using hm.2.2

lemma logBlock_log_error_bounds {K i p : ℕ} (hK : 0 < K)
    (hp : p ∈ logBlock K i) :
    0 ≤ Real.log p - (i : ℝ) / K ∧
      Real.log p - (i : ℝ) / K ≤ (K : ℝ)⁻¹ := by
  have h := mem_logBlock_log_bounds hK hp
  constructor
  · linarith
  · norm_num only [Nat.cast_add, Nat.cast_one] at h
    have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    rw [inv_eq_one_div]
    field_simp
    field_simp at h
    linarith

/-- Distinct logarithmic blocks are disjoint. -/
lemma eq_of_mem_logBlock_of_mem_logBlock {K i j p : ℕ} (hK : 0 < K)
    (hi : p ∈ logBlock K i) (hj : p ∈ logBlock K j) : i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hip := mem_logBlock hK hi
    have hjp := mem_logBlock hK hj
    have hexp : Real.exp (((i + 1 : ℕ) : ℝ) / K) ≤ Real.exp ((j : ℝ) / K) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right
      · exact_mod_cast Nat.succ_le_of_lt hij
      · exact_mod_cast hK.le
    linarith
  · have hip := mem_logBlock hK hi
    have hjp := mem_logBlock hK hj
    have hexp : Real.exp (((j + 1 : ℕ) : ℝ) / K) ≤ Real.exp ((i : ℝ) / K) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right
      · exact_mod_cast Nat.succ_le_of_lt hji
      · exact_mod_cast hK.le
    linarith

/-- Prime-counting in the normalization convenient for multiplicative blocks. -/
lemma primeCounting_mul_log_div_tendsto_one :
    Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x)
      atTop (𝓝 1) := by
  obtain ⟨c, hc, hpi⟩ := pi_alt
  have hc0 : Tendsto c atTop (𝓝 0) := (isLittleO_one_iff ℝ).mp hc
  have ht : Tendsto (fun x : ℝ ↦ 1 + c x) atTop (𝓝 1) := by
    simpa using hc0.const_add 1
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [hpi]
  field_simp [(Real.log_pos hx).ne', hx.ne']

lemma log_div_log_const_mul_tendsto_one {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ ↦ Real.log x / Real.log (r * x)) atTop (𝓝 1) := by
  have hzero : Tendsto (fun x : ℝ ↦ Real.log r / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hden : Tendsto (fun x : ℝ ↦ 1 + Real.log r / Real.log x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hzero
  have hquot : Tendsto (fun x : ℝ ↦ 1 / (1 + Real.log r / Real.log x)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hraw : Tendsto ((fun _ : ℝ ↦ (1 : ℝ)) /
        (fun x : ℝ ↦ 1 + Real.log r / Real.log x)) atTop (𝓝 1) := by
      simpa using hone.div hden one_ne_zero
    refine hraw.congr' ?_
    exact Filter.Eventually.of_forall fun x ↦ by simp [one_div]
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Real.log_mul hr.ne' (ne_of_gt (zero_lt_one.trans hx))]
  field_simp [(Real.log_pos hx).ne']
  ring

/-- For a fixed multiplicative ratio, the PNT determines the asymptotic
number of primes in the block. -/
lemma block_card_scaled_tendsto {r : ℝ} (hr : 1 < r) :
    Tendsto (fun x : ℝ ↦
      Real.log x / x * ((block r x).card : ℝ)) atTop (𝓝 (r - 1)) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hrxTop : Tendsto (fun x : ℝ ↦ r * x) atTop atTop :=
    tendsto_id.const_mul_atTop hr0
  have hPNT_r := primeCounting_mul_log_div_tendsto_one.comp hrxTop
  have hlogRatio := log_div_log_const_mul_tendsto_one hr0
  have hfirst : Tendsto (fun x : ℝ ↦
      Real.log x / x * (Nat.primeCounting ⌊r * x⌋₊ : ℝ)) atTop (𝓝 r) := by
    have hmul := (hPNT_r.mul hlogRatio).mul_const r
    have hmul' : Tendsto
        (fun x : ℝ ↦ (((Nat.primeCounting ⌊r * x⌋₊ : ℝ) * Real.log (r * x) /
          (r * x)) * (Real.log x / Real.log (r * x))) * r) atTop (𝓝 r) := by
      simpa [Function.comp_def] using hmul
    refine hmul'.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
    have hlogrx : Real.log (r * x) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      nlinarith [mul_lt_mul_of_pos_left hx hr0]
    field_simp
  have hsecond : Tendsto (fun x : ℝ ↦
      Real.log x / x * (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop (𝓝 1) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      primeCounting_mul_log_div_tendsto_one
  have hdiff := hfirst.sub hsecond
  refine hdiff.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hxmul : x ≤ r * x := le_mul_of_one_le_left hx.le hr.le
  rw [block_card_eq r x hxmul,
    Nat.cast_sub (Nat.monotone_primeCounting (Nat.floor_mono hxmul))]
  ring

/-- A fixed-ratio consequence of the qualitative PNT.  Notice that the two
limiting constants differ by a factor `r`; making the logarithmic mesh fine
means subsequently taking `r` close to one. -/
lemma eventually_mass_scaled_bounds {r ε : ℝ} (hr : 1 < r) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (r - 1) / r - ε < Real.log x * mass r x ∧
        Real.log x * mass r x < (r - 1) + ε := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hcard := block_card_scaled_tendsto hr
  have hlower : Tendsto (fun x : ℝ ↦
      (Real.log x / x * ((block r x).card : ℝ)) / r) atTop
      (𝓝 ((r - 1) / r)) := hcard.div_const r
  filter_upwards [
      hlower.eventually (Ioi_mem_nhds (show (r - 1) / r - ε < (r - 1) / r by linarith)),
      hcard.eventually (Iio_mem_nhds (show r - 1 < (r - 1) + ε by linarith)),
      eventually_gt_atTop (1 : ℝ)] with x hlowerx hupperx hx
  have hm := card_div_upper_le_mass_le_card_div_lower (r := r) (x := x)
    (zero_lt_one.trans hx) hr0
  have hlog0 : 0 ≤ Real.log x := (Real.log_pos hx).le
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  constructor
  · refine hlowerx.trans_le ?_
    calc
      Real.log x / x * ((block r x).card : ℝ) / r =
          Real.log x * (((block r x).card : ℝ) / (r * x)) := by
            field_simp [hr0.ne', hx0]
      _ ≤ Real.log x * mass r x := mul_le_mul_of_nonneg_left hm.1 hlog0
  · refine (mul_le_mul_of_nonneg_left hm.2 hlog0).trans_lt ?_
    convert hupperx using 1
    field_simp [hx0]

end Erdos144.PrimeBlocks

import ErdosProblems.Erdos260.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Elementary composition, lattice, and slope lemmas

This module corresponds to Appendix A of the manuscript.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators

namespace Erdos260

private theorem binaryEntropy_eq_binEntropy_div_log_two (x : ℝ) :
    binaryEntropy x = Real.binEntropy x / Real.log 2 := by
  rw [binaryEntropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog, Real.logb]
  field_simp
  ring

/-- A concrete structural hierarchy and a sufficiently small positive entropy
parameter exist.  This closes the denominator-level constant selection used
when `thm_main_density` instantiates the pressure argument. -/
theorem exists_structural_entropy_params :
    ∃ p : StructuralParams, ∃ entropy : EntropyParams,
      entropy.structural = p := by
  let p : StructuralParams :=
    { Caff := 3
      B := 3
      Gamma := 2
      rho := 1 / 100
      cI := 1
      C0 := 0
      Caff_gt := by norm_num
      B_gt := by norm_num
      Gamma_gt := by norm_num
      rho_pos := by norm_num
      rho_lt := by norm_num
      cI_pos := by norm_num }
  have hEntropyContinuous : Continuous binaryEntropy := by
    rw [show binaryEntropy = fun x => Real.binEntropy x / Real.log 2 by
      funext x
      exact binaryEntropy_eq_binEntropy_div_log_two x]
    exact Real.binEntropy_continuous.div_const _
  have hEntropyZero : binaryEntropy 0 = 0 := by simp [binaryEntropy]
  have harg : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have harg4 : Tendsto (fun n : ℕ => ((1 : ℝ) / (n : ℝ)) / 4)
      atTop (𝓝 0) := by simpa using harg.div_const 4
  have harg3 : Tendsto (fun n : ℕ => ((1 : ℝ) / (n : ℝ)) / 3)
      atTop (𝓝 0) := by simpa using harg.div_const 3
  have hH4 : Tendsto
      (fun n : ℕ => binaryEntropy (((1 : ℝ) / (n : ℝ)) / 4))
      atTop (𝓝 0) := by
    have h := hEntropyContinuous.continuousAt.tendsto.comp harg4
    rw [hEntropyZero] at h
    simpa [Function.comp_def] using h
  have hH3 : Tendsto
      (fun n : ℕ => binaryEntropy (((1 : ℝ) / (n : ℝ)) / 3))
      atTop (𝓝 0) := by
    have h := hEntropyContinuous.continuousAt.tendsto.comp harg3
    rw [hEntropyZero] at h
    simpa [Function.comp_def] using h
  have hinitial : Tendsto
      (fun n : ℕ => 4 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 4))
      atTop (𝓝 0) := by simpa using tendsto_const_nhds.mul hH4
  have htotal : Tendsto
      (fun n : ℕ =>
        4 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 4) +
          3 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 3))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hH4).add
      (tendsto_const_nhds.mul hH3)
  have heventInitial : ∀ᶠ n : ℕ in atTop,
      4 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 4) < 47 / 100 :=
    (tendsto_order.1 hinitial).2 _ (by norm_num)
  have heventTotal : ∀ᶠ n : ℕ in atTop,
      4 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 4) +
        3 * binaryEntropy (((1 : ℝ) / (n : ℝ)) / 3) < 49 / 50 :=
    (tendsto_order.1 htotal).2 _ (by norm_num)
  obtain ⟨n, hnInitial, hnTotal, hn⟩ :=
    (heventInitial.and (heventTotal.and (eventually_ge_atTop 1))).exists
  let κ : ℝ := 1 / (n : ℝ)
  have hκ : 0 < κ := by
    dsimp [κ]
    positivity
  let entropy : EntropyParams :=
    { structural := p
      kappa := κ
      kappa_pos := hκ
      kappa_initial_half := by
        dsimp [p, κ]
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        field_simp
        exact_mod_cast (show 2 ≤ n * (3 + 1) by omega)
      kappa_exterior_half := by
        dsimp [p, κ]
        have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        field_simp
        exact_mod_cast (show 2 ≤ n * (2 + 1) by omega)
      initial_margin := by
        dsimp [p, κ]
        norm_num at hnInitial ⊢
        exact hnInitial
      total_margin := by
        dsimp [p, κ]
        norm_num at hnTotal ⊢
        exact hnTotal }
  exact ⟨p, entropy, rfl⟩

private theorem choose_le_exp_binEntropy (h r : ℕ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1 / 2)
    (hr1 : 1 ≤ r) (hrα : (r : ℝ) ≤ α * h) :
    (Nat.choose (h - 1) (r - 1) : ℝ) ≤
      Real.exp ((h : ℝ) * Real.binEntropy α) := by
  have hαlt1 : α < 1 := lt_of_le_of_lt hα1 (by norm_num)
  have hβ0 : 0 < 1 - α := sub_pos.mpr hαlt1
  have hαβ : α ≤ 1 - α := by linarith
  have hrh_real : (r : ℝ) ≤ h := by nlinarith [hα1]
  have hrh : r ≤ h := by exact_mod_cast hrh_real
  have hrsub : r - 1 ≤ h - 1 := Nat.sub_le_sub_right hrh 1
  have hprobability :
      (Nat.choose (h - 1) (r - 1) : ℝ) * α ^ (r - 1) *
          (1 - α) ^ ((h - 1) - (r - 1)) ≤ 1 := by
    have hterm :
        α ^ (r - 1) * (1 - α) ^ ((h - 1) - (r - 1)) *
            (Nat.choose (h - 1) (r - 1) : ℝ) ≤
          ∑ m ∈ Finset.range ((h - 1) + 1),
            α ^ m * (1 - α) ^ ((h - 1) - m) *
              (Nat.choose (h - 1) m : ℝ) := by
      exact Finset.single_le_sum (s := Finset.range ((h - 1) + 1))
        (f := fun m => α ^ m * (1 - α) ^ ((h - 1) - m) *
          (Nat.choose (h - 1) m : ℝ))
        (fun _ _ => by positivity) (by simpa using Nat.lt_succ_iff.mpr hrsub)
    rw [← add_pow] at hterm
    have hone : α + (1 - α) = (1 : ℝ) := by ring
    rw [hone, one_pow] at hterm
    simpa [mul_assoc, mul_comm, mul_left_comm] using hterm
  have hrsubα : (((r - 1 : ℕ) : ℕ) : ℝ) ≤ α * h := by
    calc
      (((r - 1 : ℕ) : ℕ) : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast Nat.sub_le r 1
      _ ≤ α * h := hrα
  have hlogαβ : Real.log α ≤ Real.log (1 - α) :=
    Real.strictMonoOn_log.monotoneOn hα0 hβ0 hαβ
  have hlogβ_nonpos : Real.log (1 - α) ≤ 0 :=
    Real.log_nonpos hβ0.le (by linarith)
  have hcomplement_cast :
      ((((h - 1) - (r - 1) : ℕ) : ℕ) : ℝ) =
        (h : ℝ) - 1 - ((r : ℝ) - 1) := by
    rw [show (h - 1) - (r - 1) = h - r by omega, Nat.cast_sub hrh]
    ring
  have hrsub_cast : (((r - 1 : ℕ) : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr1]
    norm_num
  have hlogweight :
      - (h : ℝ) * Real.binEntropy α ≤
        Real.log (α ^ (r - 1) * (1 - α) ^ ((h - 1) - (r - 1))) := by
    rw [Real.log_mul (pow_ne_zero _ hα0.ne') (pow_ne_zero _ hβ0.ne'),
      Real.log_pow, Real.log_pow]
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog]
    rw [hrsub_cast, hcomplement_cast]
    nlinarith
  have hweight :
      Real.exp (- (h : ℝ) * Real.binEntropy α) ≤
        α ^ (r - 1) * (1 - α) ^ ((h - 1) - (r - 1)) := by
    rw [← Real.exp_log (mul_pos (pow_pos hα0 _) (pow_pos hβ0 _))]
    exact Real.exp_le_exp.mpr hlogweight
  have hmul :
      (Nat.choose (h - 1) (r - 1) : ℝ) *
          Real.exp (- (h : ℝ) * Real.binEntropy α) ≤ 1 := by
    calc
      _ ≤ (Nat.choose (h - 1) (r - 1) : ℝ) *
          (α ^ (r - 1) * (1 - α) ^ ((h - 1) - (r - 1))) := by gcongr
      _ = (Nat.choose (h - 1) (r - 1) : ℝ) * α ^ (r - 1) *
          (1 - α) ^ ((h - 1) - (r - 1)) := by ring
      _ ≤ 1 := hprobability
  calc
    (Nat.choose (h - 1) (r - 1) : ℝ) =
        ((Nat.choose (h - 1) (r - 1) : ℝ) *
            Real.exp (- (h : ℝ) * Real.binEntropy α)) *
          Real.exp ((h : ℝ) * Real.binEntropy α) := by
            rw [mul_assoc, ← Real.exp_add]
            ring_nf
            simp
    _ ≤ 1 * Real.exp ((h : ℝ) * Real.binEntropy α) := by gcongr
    _ = _ := one_mul _

/-- Oriented determinant of two integer vectors. -/
def intDet (z₁ z₂ : ℤ × ℤ) : ℤ := z₁.1 * z₂.2 - z₁.2 * z₂.1

/-- Congruence lattice from Appendix A. -/
def congruenceLattice (A : ℤ) (M : ℕ) : Set (ℤ × ℤ) :=
  {z | Int.ModEq M (A * z.1 + z.2) 0}

/-- Integer multiplier attached to an interior-slope gap word. -/
def wordMultiplier (w : GapWord) : ℕ :=
  ((List.range w.length).map fun j =>
    2 ^ (w.span - w.prefixSpan (j + 1))).sum

/-- Actual iteration of the slope map `μ ↦ 2^g μ - 1`. -/
def slopeAfter : GapWord → ℝ → ℝ
  | [], μ => μ
  | g :: gs, μ => slopeAfter gs ((2 : ℝ) ^ g * μ - 1)

/-- A finite set of integer parameters whose values under a decreasing affine
map lie in an integer interval of length `B` has the expected spacing bound.
This elementary helper is used for both the interior source count and the
exterior corridor count. -/
theorem integerAffineIntervalCount
    (S : Set ℤ) (C J B : ℤ) (hJ : J < 0) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ S, 0 ≤ C + J * t ∧ C + J * t ≤ B) :
    S.Finite ∧
      (S.ncard : ℝ) ≤ 1 + (B : ℝ) / (-(J : ℝ)) := by
  let f : ℤ → ℤ := fun t => C + J * t
  have himage : f '' S ⊆ Set.Icc 0 B := by
    rintro y ⟨t, ht, rfl⟩
    exact hbound t ht
  have hfimage : (f '' S).Finite :=
    (Set.finite_Icc 0 B).subset himage
  have hinj : Set.InjOn f S := by
    intro x _ y _ hxy
    dsimp [f] at hxy
    apply mul_left_cancel₀ (ne_of_lt hJ)
    exact add_left_cancel hxy
  have hfinite : S.Finite :=
    Set.Finite.of_finite_image hfimage hinj
  refine ⟨hfinite, ?_⟩
  by_cases hempty : S = ∅
  · rw [hempty, Set.ncard_empty]
    have hBreal : (0 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have hJreal : (0 : ℝ) < -(J : ℝ) := by
      exact_mod_cast (neg_pos.mpr hJ)
    have hquot : (0 : ℝ) ≤ (B : ℝ) / (-(J : ℝ)) :=
      div_nonneg hBreal hJreal.le
    norm_num
    linarith
  · have hnonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
    let s : Finset ℤ := hfinite.toFinset
    have hsne : s.Nonempty := by
      rcases hnonempty with ⟨t, ht⟩
      exact ⟨t, by simpa [s] using ht⟩
    let lo : ℤ := s.min' hsne
    let hi : ℤ := s.max' hsne
    have hlo_mem : lo ∈ s := s.min'_mem hsne
    have hhi_mem : hi ∈ s := s.max'_mem hsne
    have hlohi : lo ≤ hi := s.min'_le hi hhi_mem
    have hsubset : s ⊆ Finset.Icc lo hi := by
      intro t ht
      simp only [Finset.mem_Icc]
      exact ⟨s.min'_le t ht, s.le_max' t ht⟩
    have hcard_nat : s.card ≤ (Finset.Icc lo hi).card :=
      Finset.card_le_card hsubset
    rw [Int.card_Icc] at hcard_nat
    have hnonneg : 0 ≤ hi + 1 - lo := by omega
    have hcard_int : (s.card : ℤ) ≤ hi + 1 - lo := by
      have hcast : (s.card : ℤ) ≤ ((hi + 1 - lo).toNat : ℤ) := by
        exact_mod_cast hcard_nat
      rwa [Int.toNat_of_nonneg hnonneg] at hcast
    have hncard_eq : S.ncard = s.card := by
      simpa [s] using Set.ncard_eq_toFinset_card S hfinite
    have hcard_real : (S.ncard : ℝ) ≤ ((hi + 1 - lo : ℤ) : ℝ) := by
      rw [hncard_eq]
      exact_mod_cast hcard_int
    have hloS : lo ∈ S := by simpa [s] using hlo_mem
    have hhiS : hi ∈ S := by simpa [s] using hhi_mem
    have hspan_int : (-J) * (hi - lo) ≤ B := by
      calc
        (-J) * (hi - lo) =
            (C + J * lo) - (C + J * hi) := by ring
        _ ≤ B := by
          linarith [(hbound lo hloS).2, (hbound hi hhiS).1]
    have hstep : (0 : ℝ) < -(J : ℝ) := by
      exact_mod_cast (neg_pos.mpr hJ)
    have hspan_real₀ :
        (-(J : ℝ)) * ((hi - lo : ℤ) : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast hspan_int
    have hspan_real :
        ((hi - lo : ℤ) : ℝ) * (-(J : ℝ)) ≤ (B : ℝ) := by
      simpa [mul_comm] using hspan_real₀
    have hspan_div :
        ((hi - lo : ℤ) : ℝ) ≤ (B : ℝ) / (-(J : ℝ)) :=
      (le_div_iff₀ hstep).2 hspan_real
    push_cast at hcard_real hspan_div
    linarith

/-- Paper label: `lem:composition-entropy` (Appendix A).

The sum of binomial coefficients is the exact number of positive
compositions with the indicated allowed part counts. -/
theorem lem_composition_entropy (h rMax : ℕ) (α : ℝ)
    (hh : 2 ≤ h) (hα0 : 0 < α) (hα1 : α ≤ 1 / 2)
    (hr : (rMax : ℝ) ≤ α * h) :
    ((∑ r ∈ Finset.Icc 1 rMax, Nat.choose (h - 1) (r - 1) : ℕ) : ℝ) ≤
      (h : ℝ) ^ 2 * Real.rpow 2 ((h : ℝ) * binaryEntropy α) := by
  have hrMaxh_real : (rMax : ℝ) ≤ h := by nlinarith [hα1]
  have hrMaxh : rMax ≤ h := by exact_mod_cast hrMaxh_real
  have hrpow : Real.rpow 2 ((h : ℝ) * binaryEntropy α) =
      Real.exp ((h : ℝ) * Real.binEntropy α) := by
    change (2 : ℝ) ^ ((h : ℝ) * binaryEntropy α) = _
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      binaryEntropy_eq_binEntropy_div_log_two]
    congr 1
    field_simp
  rw [hrpow]
  calc
    ((∑ r ∈ Finset.Icc 1 rMax, Nat.choose (h - 1) (r - 1) : ℕ) : ℝ) =
        ∑ r ∈ Finset.Icc 1 rMax,
          (Nat.choose (h - 1) (r - 1) : ℝ) := by push_cast; rfl
    _ ≤ ∑ _r ∈ Finset.Icc 1 rMax,
        Real.exp ((h : ℝ) * Real.binEntropy α) := by
      refine Finset.sum_le_sum fun r hrmem => ?_
      have hrmem' : r ∈ Finset.Icc 1 rMax := by simpa only using hrmem
      rw [Finset.mem_Icc] at hrmem'
      have hrr : (r : ℝ) ≤ rMax := by exact_mod_cast hrmem'.2
      exact choose_le_exp_binEntropy h r α hα0 hα1 hrmem'.1 (hrr.trans hr)
    _ = ((Finset.Icc 1 rMax).card : ℝ) *
        Real.exp ((h : ℝ) * Real.binEntropy α) := by simp
    _ ≤ (h : ℝ) * Real.exp ((h : ℝ) * Real.binEntropy α) := by
      gcongr
      exact_mod_cast (calc
        (Finset.Icc 1 rMax).card = rMax := by rw [Nat.card_Icc]; omega
        _ ≤ h := hrMaxh)
    _ ≤ (h : ℝ) ^ 2 * Real.exp ((h : ℝ) * Real.binEntropy α) := by
      gcongr
      have h0 : (0 : ℝ) ≤ h := by positivity
      have h1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

/-- Paper label: `lem:lattice-det` (Appendix A). -/
theorem lem_lattice_det (A : ℤ) (M : ℕ) (hM : 1 ≤ M)
    (z₁ z₂ : ℤ × ℤ)
    (hz₁ : z₁ ∈ congruenceLattice A M)
    (hz₂ : z₂ ∈ congruenceLattice A M) :
    ∃ k : ℤ, intDet z₁ z₂ = (M : ℤ) * k := by
  have _hMne : (M : ℤ) ≠ 0 := by
    exact_mod_cast (show M ≠ 0 by omega)
  change Int.ModEq (M : ℤ) (A * z₁.1 + z₁.2) 0 at hz₁
  change Int.ModEq (M : ℤ) (A * z₂.1 + z₂.2) 0 at hz₂
  have hleft : Int.ModEq (M : ℤ)
      (z₁.1 * (A * z₂.1 + z₂.2)) 0 := by
    simpa using (Int.ModEq.refl z₁.1).mul hz₂
  have hright : Int.ModEq (M : ℤ)
      (z₂.1 * (A * z₁.1 + z₁.2)) 0 := by
    simpa using (Int.ModEq.refl z₂.1).mul hz₁
  have hdet : Int.ModEq (M : ℤ) (intDet z₁ z₂) 0 := by
    have h := hleft.sub hright
    convert h using 1 <;> (simp [intDet] <;> ring)
  rcases (Int.modEq_iff_dvd.mp hdet.symm) with ⟨k, hk⟩
  exact ⟨k, by simpa using hk⟩

/-- Paper label: `lem:farey` (Appendix A). -/
theorem lem_farey (a c : ℤ) (b d D : ℕ)
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hbD : b < 2 * D) (hdD : d < 2 * D)
    (hne : (a : ℚ) / b ≠ (c : ℚ) / d) :
    1 / (4 * (D : ℝ) ^ 2) ≤
      |(a : ℝ) / b - (c : ℝ) / d| := by
  have hb0 : (b : ℚ) ≠ 0 := by positivity
  have hd0 : (d : ℚ) ≠ 0 := by positivity
  have hcross : (a : ℚ) * d ≠ (c : ℚ) * b := by
    intro h
    exact hne ((div_eq_div_iff hb0 hd0).2 h)
  have hz : a * (d : ℤ) - c * (b : ℤ) ≠ 0 := by
    intro h
    apply hcross
    exact_mod_cast (sub_eq_zero.mp h)
  have hnum : (1 : ℝ) ≤
      |(a : ℝ) * d - (c : ℝ) * b| := by
    exact_mod_cast Int.one_le_abs hz
  have hb_le : b ≤ 2 * D := Nat.le_of_lt hbD
  have hd_le : d ≤ 2 * D := Nat.le_of_lt hdD
  have hbd_nat0 : b * d ≤ (2 * D) * (2 * D) :=
    Nat.mul_le_mul hb_le hd_le
  have hbd_nat : b * d ≤ 4 * D ^ 2 := by
    nlinarith [hbd_nat0]
  have hbd : (b : ℝ) * d ≤ 4 * (D : ℝ) ^ 2 := by
    exact_mod_cast hbd_nat
  have hden_pos : (0 : ℝ) < (b : ℝ) * d := by positivity
  have hdiff : (a : ℝ) / b - (c : ℝ) / d =
      ((a : ℝ) * d - (c : ℝ) * b) / ((b : ℝ) * d) := by
    field_simp
  rw [hdiff, abs_div, abs_of_pos hden_pos]
  calc
    1 / (4 * (D : ℝ) ^ 2) ≤ 1 / ((b : ℝ) * d) :=
      one_div_le_one_div_of_le hden_pos hbd
    _ ≤ |(a : ℝ) * d - (c : ℝ) * b| / ((b : ℝ) * d) :=
      (div_le_div_iff_of_pos_right hden_pos).2 hnum

/-- Paper label: `lem:word-cylinder` (Appendix A). -/
theorem lem_word_cylinder (w : GapWord) (μ₀ : ℝ)
    (hfinal : slopeAfter w μ₀ ∈ Set.Ioo (0 : ℝ) 1) :
    μ₀ ∈ Set.Ioo
      ((wordMultiplier w : ℝ) / (2 : ℝ) ^ w.span)
      (((wordMultiplier w : ℝ) + 1) / (2 : ℝ) ^ w.span) := by
  have hclosed (v : GapWord) (μ : ℝ) :
      slopeAfter v μ = (2 : ℝ) ^ v.span * μ - (wordMultiplier v : ℝ) := by
    induction v generalizing μ with
    | nil => simp [slopeAfter, wordMultiplier, GapWord.span]
    | cons g tail ih =>
        have hmul : wordMultiplier (g :: tail) =
            (2 : ℕ) ^ GapWord.span tail + wordMultiplier tail := by
          simp [wordMultiplier, List.range_succ_eq_map, GapWord.span,
            GapWord.prefixSpan, Function.comp_def, Nat.add_sub_add_left]
        rw [slopeAfter, ih, hmul]
        simp only [GapWord.span, List.sum_cons, Nat.cast_add, Nat.cast_pow,
          Nat.cast_ofNat]
        rw [pow_add]
        ring
  rw [hclosed] at hfinal
  have hpow : (0 : ℝ) < (2 : ℝ) ^ w.span := by positivity
  constructor
  · rw [div_lt_iff₀ hpow]
    linarith [hfinal.1]
  · rw [lt_div_iff₀ hpow]
    linarith [hfinal.2]

private theorem eventually_logarithmic_entropy_bound (C : ℝ) (hC : 0 < C) :
    ∀ᶠ D : ℕ in atTop,
      let ell := Nat.ceil (Real.logb 2 (4 * D))
      C * (ell : ℝ) ^ 4 * Real.rpow 2 ((ell : ℝ) / 8) ≤ Real.sqrt D := by
  let K : ℝ := C * 625 * Real.rpow 8 (1 / 8 : ℝ)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hsmallReal :=
    (isLittleO_log_rpow_rpow_atTop (4 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 4)).bound
      (show 0 < (1 : ℝ) / K by positivity)
  have hsmallNat := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [hsmallNat, eventually_ge_atTop 3] with D hsmall hD
  dsimp only
  have hDpos : (0 : ℝ) < D := by positivity
  have hlog : 1 ≤ Real.log (D : ℝ) := by
    rw [Real.le_log_iff_exp_le hDpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hD)
  have hlog0 : 0 ≤ Real.log (D : ℝ) := le_trans (by norm_num) hlog
  have hsmall' : Real.log (D : ℝ) ^ 4 ≤
      (1 / K) * (D : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog0 (4 : ℝ)),
      Real.norm_of_nonneg (Real.rpow_nonneg hDpos.le (1 / 4 : ℝ))] at hsmall
    rw [← Real.rpow_natCast]
    exact hsmall
  have habsorb : K * Real.log (D : ℝ) ^ 4 ≤
      (D : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ K * ((1 / K) * (D : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall' hK.le
      _ = _ := by field_simp
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 :=
    lt_of_lt_of_le (by norm_num) hlog2
  have hlogb_nonneg : 0 ≤ Real.logb 2 (4 * D) := by
    rw [Real.logb]
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 4 * D by omega)
    · exact hlog2pos.le
  have hceil_lt := Nat.ceil_lt_add_one hlogb_nonneg
  have hident : Real.logb 2 (4 * (D : ℝ)) =
      2 + Real.log (D : ℝ) / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hDpos.ne']
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog4]
    field_simp
  have hdiv : Real.log (D : ℝ) / Real.log 2 ≤ 2 * Real.log (D : ℝ) := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [mul_nonneg hlog0 (sub_nonneg.mpr hlog2)]
  have hell : ((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) ≤
      5 * Real.log (D : ℝ) := by
    rw [show (4 * D : ℝ) = 4 * (D : ℝ) by norm_num, hident] at hceil_lt ⊢
    linarith
  have hellpow : ((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) ^ 4 ≤
      625 * Real.log (D : ℝ) ^ 4 := by
    have hell0 : (0 : ℝ) ≤ (Nat.ceil (Real.logb 2 (4 * D)) : ℕ) := by
      positivity
    have hp := pow_le_pow_left₀ hell0 hell 4
    nlinarith
  have hexp :
      Real.rpow 2 (((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) / 8) ≤
        Real.rpow 8 (1 / 8 : ℝ) * (D : ℝ) ^ (1 / 8 : ℝ) := by
    have harg : (((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) / 8) ≤
        (Real.logb 2 (4 * (D : ℝ)) + 1) / 8 := by
      have hc : ((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) <
          Real.logb 2 (4 * (D : ℝ)) + 1 := by
        simpa only [Nat.cast_ofNat, Nat.cast_mul] using hceil_lt
      linarith
    calc
      Real.rpow 2 (((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) / 8) ≤
          Real.rpow 2 ((Real.logb 2 (4 * (D : ℝ)) + 1) / 8) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) harg
      _ = Real.rpow (8 * (D : ℝ)) (1 / 8 : ℝ) := by
        change (2 : ℝ) ^ ((Real.logb 2 (4 * (D : ℝ)) + 1) / 8) = _
        rw [show (Real.logb 2 (4 * (D : ℝ)) + 1) / 8 =
            (Real.logb 2 (4 * (D : ℝ)) + 1) * (1 / 8 : ℝ) by ring,
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
          Real.rpow_one]
        congr 1
        ring
      _ = _ := by
        change (8 * (D : ℝ)) ^ (1 / 8 : ℝ) =
          8 ^ (1 / 8 : ℝ) * (D : ℝ) ^ (1 / 8 : ℝ)
        exact Real.mul_rpow (by norm_num) hDpos.le
  have hpolyMul :
      C * ((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) ^ 4 ≤
        C * (625 * Real.log (D : ℝ) ^ 4) :=
    mul_le_mul_of_nonneg_left hellpow hC.le
  have hexpnonneg :
      0 ≤ Real.rpow 2 (((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) / 8) :=
    Real.rpow_nonneg (by norm_num) _
  have hpolyBoundNonneg : 0 ≤ C * (625 * Real.log (D : ℝ) ^ 4) := by
    positivity
  have hfirst := mul_le_mul hpolyMul hexp hexpnonneg hpolyBoundNonneg
  have hmain :
      C * ((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) ^ 4 *
          Real.rpow 2 (((Nat.ceil (Real.logb 2 (4 * D)) : ℕ) : ℝ) / 8) ≤
        (D : ℝ) ^ (3 / 8 : ℝ) := by
    calc
      _ ≤ C * (625 * Real.log (D : ℝ) ^ 4) *
          (Real.rpow 8 (1 / 8 : ℝ) * (D : ℝ) ^ (1 / 8 : ℝ)) := hfirst
      _ = (K * Real.log (D : ℝ) ^ 4) * (D : ℝ) ^ (1 / 8 : ℝ) := by
        dsimp [K]
        ring
      _ ≤ (D : ℝ) ^ (1 / 4 : ℝ) * (D : ℝ) ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right habsorb (Real.rpow_nonneg hDpos.le _)
      _ = (D : ℝ) ^ (3 / 8 : ℝ) := by
        have hr := (Real.rpow_add hDpos (1 / 4 : ℝ) (1 / 8 : ℝ)).symm
        norm_num at hr ⊢
        exact hr
  calc
    _ ≤ (D : ℝ) ^ (3 / 8 : ℝ) := hmain
    _ ≤ (D : ℝ) ^ (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ D by omega)) (by norm_num)
    _ = Real.sqrt D := by rw [Real.sqrt_eq_rpow]

/-- Paper label: `lem:quant-entropy` (Appendix A). -/
theorem lem_quant_entropy (B c C : ℝ) (hB : 2 < B) (hc : 0 < c) (hC : 0 < C) :
    ∃ Zstar : ℕ, ∀ Z D : ℕ,
      Zstar ≤ Z → c * (2 : ℝ) ^ Z ≤ D →
      let ell := Nat.ceil (Real.logb 2 (4 * D))
      C * (ell : ℝ) ^ 4 *
          Real.rpow 2 ((B + 1) * ell * binaryEntropy (5 / Z)) ≤
        Real.sqrt D := by
  have harg : Tendsto (fun Z : ℕ => (5 : ℝ) / (Z : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hEntropyContinuous : Continuous binaryEntropy := by
    rw [show binaryEntropy = fun x => Real.binEntropy x / Real.log 2 by
      funext x
      exact binaryEntropy_eq_binEntropy_div_log_two x]
    exact Real.binEntropy_continuous.div_const _
  have hEntropyZero : binaryEntropy 0 = 0 := by simp [binaryEntropy]
  have hEntropyTendsto :
      Tendsto (fun Z : ℕ => binaryEntropy (5 / (Z : ℝ))) atTop (nhds 0) := by
    change Tendsto (binaryEntropy ∘ fun Z : ℕ => (5 : ℝ) / (Z : ℝ))
      atTop (nhds 0)
    simpa only [hEntropyZero] using (hEntropyContinuous.tendsto 0).comp harg
  have hBplus : 0 < B + 1 := by linarith
  let δ : ℝ := 1 / (8 * (B + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hEntropySmall :
      ∀ᶠ Z : ℕ in atTop, binaryEntropy (5 / (Z : ℝ)) ≤ δ :=
    hEntropyTendsto.eventually (eventually_le_nhds hδ)
  obtain ⟨Dstar, hDstar⟩ :=
    eventually_atTop.mp (eventually_logarithmic_entropy_bound C hC)
  have hScaleLarge :
      ∀ᶠ Z : ℕ in atTop, (Dstar : ℝ) ≤ c * (2 : ℝ) ^ Z :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hc)
      |>.eventually_ge_atTop _
  obtain ⟨Zstar, hZstar⟩ := eventually_atTop.mp (hEntropySmall.and hScaleLarge)
  refine ⟨Zstar, fun Z D hZ hD => ?_⟩
  dsimp only
  have hpair := hZstar Z hZ
  have hDstarD_real : (Dstar : ℝ) ≤ D := hpair.2.trans hD
  have hDstarD : Dstar ≤ D := by exact_mod_cast hDstarD_real
  have hgeneric := hDstar D hDstarD
  let ell := Nat.ceil (Real.logb 2 (4 * D))
  have hell0 : (0 : ℝ) ≤ ell := by positivity
  have hcoef : (B + 1) * binaryEntropy (5 / (Z : ℝ)) ≤ 1 / 8 := by
    have hm := mul_le_mul_of_nonneg_left hpair.1 hBplus.le
    calc
      _ ≤ (B + 1) * δ := hm
      _ = 1 / 8 := by
        dsimp [δ]
        field_simp
  have hexponent :
      (B + 1) * (ell : ℝ) * binaryEntropy (5 / (Z : ℝ)) ≤ (ell : ℝ) / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left hcoef hell0]
  have hrpow :
      Real.rpow 2 ((B + 1) * (ell : ℝ) * binaryEntropy (5 / (Z : ℝ))) ≤
        Real.rpow 2 ((ell : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  calc
    C * (ell : ℝ) ^ 4 *
        Real.rpow 2 ((B + 1) * (ell : ℝ) * binaryEntropy (5 / (Z : ℝ))) ≤
      C * (ell : ℝ) ^ 4 * Real.rpow 2 ((ell : ℝ) / 8) := by
        exact mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ ≤ Real.sqrt D := by simpa [ell] using hgeneric

end Erdos260

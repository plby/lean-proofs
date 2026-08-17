/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos284.Assembly
import ErdosProblems.Erdos284.UpperBound

/-!
# Erdős Problem 284: the asymptotic squeeze

The lower estimate uses the exact-cardinality representations assembled from
Croot's theorem.  The upper estimate is the elementary harmonic-sum bound:
after fixing a large lower threshold for the maximal first denominator, its
exponentiated form gives a uniform coefficient converging to `e - 1`.
-/

open Filter
open scoped BigOperators Topology Real

namespace Erdos284

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The constant predicted in Erdős Problem 284. -/
def erdosConstant : ℝ := 1 / (Real.exp 1 - 1)

/-- The extremal function from Erdős Problem 284.  On the finitely many
indices for which no representation exists, `Nat.sSup` takes its harmless
default value; the Croot construction proves nonemptiness eventually. -/
def erdosF (k : ℕ) : ℕ := sSup (FirstDenominators k)

theorem erdosConstant_pos : 0 < erdosConstant := by
  exact div_pos zero_lt_one
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr zero_lt_one))

theorem half_lt_erdosConstant : (1 : ℝ) / 2 < erdosConstant := by
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hd : 0 < Real.exp 1 - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr zero_lt_one)
  rw [erdosConstant, lt_div_iff₀ hd]
  nlinarith

/-- Every possible first denominator is at most the number of terms.  This
also supplies boundedness of the set whose maximum defines `f(k)`. -/
theorem first_denominator_le_card {k : ℕ} {n : Fin (k + 1) → ℕ}
    (hn : StrictMono n) (hn0 : 0 ∉ Set.range n)
    (hsum : 1 = ∑ i, (1 : ℝ) / n i) :
    n 0 ≤ k + 1 := by
  have hu : (0 : ℝ) < n 0 := by
    exact_mod_cast Nat.pos_of_ne_zero fun hz ↦ hn0 ⟨0, hz⟩
  have hmono (i : Fin (k + 1)) : (n 0 : ℝ) ≤ n i := by
    exact_mod_cast hn.monotone (Fin.zero_le i)
  have hterm (i : Fin (k + 1)) :
      (1 : ℝ) / n i ≤ 1 / n 0 :=
    one_div_le_one_div_of_le hu (hmono i)
  have hsumle :
      (∑ i : Fin (k + 1), (1 : ℝ) / n i) ≤
        ∑ _i : Fin (k + 1), (1 : ℝ) / n 0 :=
    Finset.sum_le_sum fun i _ ↦ hterm i
  rw [← hsum] at hsumle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsumle
  have hsumle' : (1 : ℝ) ≤ (k + 1 : ℕ) / (n 0 : ℝ) := by
    simpa [div_eq_mul_inv] using hsumle
  have hmul := (le_div_iff₀ hu).mp hsumle'
  norm_num at hmul
  exact_mod_cast hmul

theorem firstDenominators_bddAbove (k : ℕ) :
    BddAbove (FirstDenominators k) := by
  refine ⟨k + 1, ?_⟩
  intro m hm
  rw [mem_firstDenominators] at hm
  rcases hm with ⟨n, hn, rfl⟩
  exact first_denominator_le_card hn.1 hn.2.1 hn.2.2

/-- Whenever a representation exists, `erdosF` is exactly the greatest
attainable first denominator. -/
theorem erdosF_isMaximal {k : ℕ} (hk : (FirstDenominators k).Nonempty) :
    IsMaximalFirstDenominator k (erdosF k) := by
  refine ⟨?_, ?_⟩
  · exact Nat.sSup_mem hk (firstDenominators_bddAbove k)
  · intro m hm
    exact le_csSup (firstDenominators_bddAbove k) hm

/-- Croot witnesses make the canonical extremal function maximal for every
sufficiently large index. -/
theorem eventually_erdosF_isMaximal (hCroot : HasCrootShortIntervals) :
    ∀ᶠ k : ℕ in atTop, IsMaximalFirstDenominator k (erdosF k) := by
  let c : ℝ := ((1 : ℝ) / 2 + erdosConstant) / 2
  have hcpos : 0 < c := by
    dsimp [c]
    linarith [erdosConstant_pos]
  have hchalf : (1 : ℝ) / 2 < c := by
    dsimp [c]
    linarith [half_lt_erdosConstant]
  have hctarget : c < 1 / (Real.exp 1 - 1) := by
    change c < erdosConstant
    dsimp [c]
    linarith [half_lt_erdosConstant]
  have hexact := eventually_exact_card_above_of_croot hCroot
    hcpos hchalf hctarget
  filter_upwards [hexact] with k hk
  rcases hk with ⟨E, hE, _hbelow⟩
  apply erdosF_isMaximal
  let n : Fin (k + 1) → ℕ := enumerate E hE.card_eq
  refine ⟨n 0, ?_⟩
  rw [mem_firstDenominators]
  exact ⟨n, by simpa only [Nat.succ_eq_add_one] using representation_enumerate hE, rfl⟩

/-- A finite-set representation produces a possible first denominator; if
all its terms exceed `N`, maximality forces the maximal first denominator to
exceed `N` as well. -/
theorem maximalFirstDenominator_gt_of_finset
    {k N f : ℕ} {E : Finset ℕ}
    (hE : FinsetRepresentation (k + 1) E)
    (hbelow : ∀ a ∈ E, N < a)
    (hf : IsMaximalFirstDenominator k f) :
    N < f := by
  let n : Fin (k + 1) → ℕ := enumerate E hE.card_eq
  have hn : Representation k n := by
    simpa only [Nat.succ_eq_add_one] using representation_enumerate hE
  have hnmem : n 0 ∈ FirstDenominators k := by
    rw [mem_firstDenominators]
    exact ⟨n, hn, rfl⟩
  have hnE : n 0 ∈ E := by
    unfold n enumerate
    change Erdos285.enumerate E hE.card_eq 0 ∈ (E : Set ℕ)
    rw [← Erdos285.range_enumerate E hE.card_eq]
    exact Set.mem_range_self 0
  exact (hbelow _ hnE).trans_le (hf.2 hnmem)

/-- The lower half of the squeeze, stated in the order-neighborhood form
used by `tendsto_order`. -/
theorem eventually_lower_ratio_of_croot
    (hCroot : HasCrootShortIntervals) {f : ℕ → ℕ}
    (hf : ∀ᶠ k : ℕ in atTop, IsMaximalFirstDenominator k (f k))
    {a : ℝ} (ha : a < erdosConstant) :
    ∀ᶠ k : ℕ in atTop, a < (f k : ℝ) / (k + 1 : ℕ) := by
  let c : ℝ := (max a ((1 : ℝ) / 2) + erdosConstant) / 2
  have hmaxlt : max a ((1 : ℝ) / 2) < erdosConstant :=
    max_lt ha half_lt_erdosConstant
  have hcpos : 0 < c := by
    dsimp [c]
    have := half_lt_erdosConstant
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    have := le_max_right a ((1 : ℝ) / 2)
    positivity
  have hachalf : (1 : ℝ) / 2 < c := by
    dsimp [c]
    have hle := le_max_right a ((1 : ℝ) / 2)
    linarith
  have hca : a < c := by
    dsimp [c]
    have hle := le_max_left a ((1 : ℝ) / 2)
    linarith
  have hctarget : c < erdosConstant := by
    dsimp [c]
    linarith
  have hexact := eventually_exact_card_above_of_croot hCroot
    hcpos hachalf hctarget
  have hcutratio := lowerCutoff_ratio_tendsto hcpos.le
  have hcutabove : ∀ᶠ k : ℕ in atTop,
      a < (lowerCutoff c k : ℝ) / (k + 1 : ℕ) :=
    (tendsto_order.1 hcutratio).1 a hca
  filter_upwards [hexact, hf, hcutabove] with k hk hfk hratio
  rcases hk with ⟨E, hE, hbelow⟩
  have hnat : lowerCutoff c k < f k :=
    maximalFirstDenominator_gt_of_finset hE hbelow hfk
  have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  exact hratio.trans_le (div_le_div_of_nonneg_right
    (by exact_mod_cast hnat.le) hkpos.le)

/-- The coefficient obtained by freezing the reciprocal error at `M+1`. -/
def frozenUpperConstant (M : ℕ) : ℝ :=
  1 / (Real.exp (1 - (1 : ℝ) / (M + 1 : ℕ)) - 1)

theorem frozenUpperConstant_tendsto :
    Tendsto frozenUpperConstant atTop (nhds erdosConstant) := by
  have hinv : Tendsto (fun M : ℕ ↦ (1 : ℝ) / (M + 1 : ℕ))
      atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have harg : Tendsto
      (fun M : ℕ ↦ 1 - (1 : ℝ) / (M + 1 : ℕ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hexp : Tendsto
      (fun M : ℕ ↦ Real.exp (1 - (1 : ℝ) / (M + 1 : ℕ)))
      atTop (nhds (Real.exp 1)) :=
    Real.continuous_exp.continuousAt.tendsto.comp harg
  have hdenom : Tendsto
      (fun M : ℕ ↦ Real.exp (1 - (1 : ℝ) / (M + 1 : ℕ)) - 1)
      atTop (nhds (Real.exp 1 - 1)) := hexp.sub tendsto_const_nhds
  have hne : Real.exp 1 - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr zero_lt_one)).ne'
  change Tendsto
    (fun M : ℕ ↦
      1 / (Real.exp (1 - (1 : ℝ) / (M + 1 : ℕ)) - 1))
    atTop (nhds erdosConstant)
  simpa only [erdosConstant, one_div, Nat.cast_add, Nat.cast_one] using
    hdenom.inv₀ hne

/-- The upper half of the squeeze. -/
theorem eventually_upper_ratio
    {f : ℕ → ℕ}
    (hf : ∀ᶠ k : ℕ in atTop, IsMaximalFirstDenominator k (f k))
    {b : ℝ} (hb : erdosConstant < b) :
    ∀ᶠ k : ℕ in atTop, (f k : ℝ) / (k + 1 : ℕ) < b := by
  have hbpos : 0 < b := erdosConstant_pos.trans hb
  have hfreeze : ∀ᶠ M : ℕ in atTop, frozenUpperConstant M < b :=
    (tendsto_order.1 frozenUpperConstant_tendsto).2 b hb
  obtain ⟨M, hMfreeze, hMone⟩ :
      ∃ M : ℕ, frozenUpperConstant M < b ∧ 1 ≤ M := by
    exact (hfreeze.and (eventually_ge_atTop 1)).exists
  have hsmalllim : Tendsto
      (fun k : ℕ ↦ ((M + 1 : ℕ) : ℝ) / (k + 1 : ℕ))
      atTop (nhds 0) := by
    have hinv : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1 : ℕ))
        atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  have hsmall : ∀ᶠ k : ℕ in atTop,
      ((M + 1 : ℕ) : ℝ) / (k + 1 : ℕ) < b :=
    (tendsto_order.1 hsmalllim).2 b hbpos
  filter_upwards [hf, hsmall] with k hfk hsmallk
  by_cases hfm : f k < M + 1
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast hfm.le)
      (by positivity : (0 : ℝ) ≤ (k + 1 : ℕ))).trans_lt hsmallk
  · have hMf : M + 1 ≤ f k := Nat.le_of_not_gt hfm
    rcases (mem_firstDenominators.mp hfk.1) with ⟨n, hn, hnzero⟩
    have hexpbound := UpperBound.first_denominator_exp_bound
      hn.1 hn.2.1 hn.2.2
    rw [hnzero] at hexpbound
    let d : ℝ := Real.exp (1 - (1 : ℝ) / (M + 1 : ℕ)) - 1
    have hargpos : 0 < 1 - (1 : ℝ) / (M + 1 : ℕ) := by
      have hMreal : (2 : ℝ) ≤ (M + 1 : ℕ) := by exact_mod_cast (by omega : 2 ≤ M + 1)
      have hdiv : (1 : ℝ) / (M + 1 : ℕ) ≤ 1 / 2 := by
        exact one_div_le_one_div_of_le (by norm_num) hMreal
      linarith
    have hdpos : 0 < d := by
      dsimp [d]
      exact sub_pos.mpr (Real.one_lt_exp_iff.mpr hargpos)
    have hinvle : (1 : ℝ) / f k ≤ 1 / (M + 1 : ℕ) := by
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hMf)
    have hexple : Real.exp (1 - (1 : ℝ) / (M + 1 : ℕ)) ≤
        Real.exp (1 - (1 : ℝ) / f k) := by
      exact Real.exp_monotone (sub_le_sub_left hinvle 1)
    have hlinear : d * (f k : ℝ) ≤ k := by
      dsimp [d]
      have hfnonneg : (0 : ℝ) ≤ f k := by positivity
      have hcoef := mul_le_mul_of_nonneg_right
        (sub_le_sub_right hexple 1) hfnonneg
      nlinarith
    have hklt : (k : ℝ) < (k + 1 : ℕ) := by
      norm_num [Nat.cast_add, Nat.cast_one]
    have hratiofreeze : (f k : ℝ) / (k + 1 : ℕ) < 1 / d := by
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (k + 1 : ℕ)) hdpos]
      norm_num
      nlinarith
    exact hratiofreeze.trans (by simpa [frozenUpperConstant, d] using hMfreeze)

/-- Assuming Croot's short-interval theorem, every choice of the maximal
first denominator has the asymptotic value claimed by Erdős. -/
theorem ratio_tendsto_of_croot
    (hCroot : HasCrootShortIntervals) {f : ℕ → ℕ}
    (hf : ∀ᶠ k : ℕ in atTop, IsMaximalFirstDenominator k (f k)) :
    Tendsto (fun k : ℕ ↦ (f k : ℝ) / (k + 1 : ℕ))
      atTop (nhds erdosConstant) := by
  rw [tendsto_order]
  exact ⟨fun a ha ↦ eventually_lower_ratio_of_croot hCroot hf ha,
    fun b hb ↦ eventually_upper_ratio hf hb⟩

/-- Erdős Problem 284, conditional only at this point on the named local
form of Croot's short-interval theorem.  The main module discharges that
theorem from the Croot--Bloom analytic library. -/
theorem erdos_284_of_croot (hCroot : HasCrootShortIntervals) :
    Tendsto (fun k : ℕ ↦ (erdosF k : ℝ) / (k + 1 : ℕ))
      atTop (nhds erdosConstant) :=
  ratio_tendsto_of_croot hCroot (eventually_erdosF_isMaximal hCroot)

end

end Erdos284

#print axioms Erdos284.first_denominator_le_card
#print axioms Erdos284.eventually_lower_ratio_of_croot
#print axioms Erdos284.eventually_upper_ratio
#print axioms Erdos284.ratio_tendsto_of_croot
#print axioms Erdos284.erdos_284_of_croot

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 146. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/146#post-8253
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import Mathlib

set_option linter.mathlibStandardSet false

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos146

lemma free_map_of_no_isolated
    {U V W : Type*}
    (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {host : SimpleGraph V}
    (embedding : V ↪ W)
    (hfree : forbidden.Free host) :
    forbidden.Free (host.map embedding) := by
  classical
  rintro ⟨copy⟩
  have hpreimage (u : U) :
      ∃ v : V, embedding v = copy u := by
    obtain ⟨w, huw⟩ := hneighbors u
    have hadj := copy.toHom.map_rel huw
    change (host.map embedding).Adj (copy u) (copy w) at hadj
    obtain ⟨v, _, _, hv, _⟩ :=
      (SimpleGraph.map_adj embedding host _ _).mp hadj
    exact ⟨v, hv⟩
  let lift : U → V := fun u => Classical.choose (hpreimage u)
  have hlift (u : U) : embedding (lift u) = copy u :=
    Classical.choose_spec (hpreimage u)
  apply hfree
  refine ⟨⟨⟨lift, ?_⟩, ?_⟩⟩
  · intro u v huv
    have hadj := copy.toHom.map_rel huv
    change (host.map embedding).Adj (copy u) (copy v) at hadj
    rw [← hlift u, ← hlift v] at hadj
    exact SimpleGraph.map_adj_apply.mp hadj
  · intro u v huv
    change lift u = lift v at huv
    apply copy.injective
    change copy u = copy v
    rw [← hlift u, ← hlift v]
    exact congrArg embedding huv

lemma extremalNumber_monotone_of_no_isolated
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {m n : ℕ} (hmn : m ≤ n) :
    SimpleGraph.extremalNumber m forbidden ≤
      SimpleGraph.extremalNumber n forbidden := by
  classical
  have hbound :
      SimpleGraph.extremalNumber (Fintype.card (Fin m)) forbidden ≤
        SimpleGraph.extremalNumber n forbidden := by
    apply (SimpleGraph.extremalNumber_le_iff
      (V := Fin m) forbidden
      (SimpleGraph.extremalNumber n forbidden)).mpr
    intro host _ hfree
    let embedding : Fin m ↪ Fin n := Fin.castLEEmb hmn
    have hpadded : forbidden.Free (host.map embedding) :=
      free_map_of_no_isolated forbidden hneighbors embedding hfree
    calc
      host.edgeFinset.card =
          (host.map embedding).edgeFinset.card := by
        simpa only [SimpleGraph.edgeFinset_card,
          ← Nat.card_eq_fintype_card] using
          (SimpleGraph.card_edgeFinset_map embedding host).symm
      _ ≤ SimpleGraph.extremalNumber n forbidden := by
        simpa using SimpleGraph.card_edgeFinset_le_extremalNumber hpadded
  simpa using hbound

lemma eventually_constant_le_positive_nat_rpow
    (constant coefficient exponent : ℝ)
    (hcoefficient : 0 < coefficient)
    (hexponent : 0 < exponent) :
    ∀ᶠ n : ℕ in Filter.atTop,
      constant ≤ coefficient * (n : ℝ) ^ exponent := by
  have hpower :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ) ^ exponent)
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexponent).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hpower.eventually
    (Filter.eventually_ge_atTop (constant / coefficient))]
    with n hn
  calc
    constant = coefficient * (constant / coefficient) := by
      field_simp
    _ ≤ coefficient * (n : ℝ) ^ exponent :=
      mul_le_mul_of_nonneg_left hn hcoefficient.le


section BinaryEntropy

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  Real.binEntropy x / Real.log 2

noncomputable def tau : ℝ := (Real.sqrt 3 - 1) / 2

noncomputable def kappa : ℝ := 3 / 2 - (3 / 4) * logTwo 3

noncomputable def certifiedWindowWidth : ℝ :=
  logTwo ((97 + 56 * Real.sqrt 3) / 192) / 4

theorem twelve_sevenths_lt_sqrt_three : (12 : ℝ) / 7 < Real.sqrt 3 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  nlinarith

theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

theorem binaryEntropy_nonneg {x : ℝ} (hzero : 0 ≤ x)
    (hone : x ≤ 1) : 0 ≤ binaryEntropy x := by
  exact div_nonneg (Real.binEntropy_nonneg hzero hone) log_two_pos.le

theorem binaryEntropy_le_one (x : ℝ) : binaryEntropy x ≤ 1 := by
  unfold binaryEntropy
  apply (div_le_iff₀ log_two_pos).2
  simpa using (Real.binEntropy_le_log_two (p := x))

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]

@[simp] theorem binaryEntropy_one_sub (x : ℝ) :
    binaryEntropy (1 - x) = binaryEntropy x := by
  simp [binaryEntropy]

@[fun_prop] theorem binaryEntropy_continuous : Continuous binaryEntropy := by
  exact Real.binEntropy_continuous.div_const _

theorem binaryEntropy_scale_le (probability scale : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1)
    (hscale_zero : 0 ≤ scale)
    (hscale_one : scale ≤ 1) :
    scale * binaryEntropy probability ≤
      binaryEntropy (scale * probability) := by
  have hconcavity := Real.strictConcave_binEntropy.concaveOn.2
    (show probability ∈ Set.Icc (0 : ℝ) 1 from
      ⟨hprobability_zero, hprobability_one⟩)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    hscale_zero (sub_nonneg.mpr hscale_one)
    (show scale + (1 - scale) = 1 by ring)
  have hnatural :
      scale * Real.binEntropy probability ≤
        Real.binEntropy (scale * probability) := by
    simpa [smul_eq_mul] using hconcavity
  unfold binaryEntropy
  calc
    scale * (Real.binEntropy probability / Real.log 2) =
      (scale * Real.binEntropy probability) / Real.log 2 := by ring
    _ ≤ Real.binEntropy (scale * probability) / Real.log 2 :=
      (div_le_div_iff_of_pos_right log_two_pos).mpr hnatural

theorem binaryEntropy_subadditive (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hsum : x + y ≤ 1) :
    binaryEntropy (x + y) ≤ binaryEntropy x + binaryEntropy y := by
  by_cases hzero : x + y = 0
  · have hxzero : x = 0 := by linarith
    have hyzero : y = 0 := by linarith
    simp [hxzero, hyzero]
  have hpositive : 0 < x + y :=
    lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hzero)
  have hxscale : 0 ≤ x / (x + y) :=
    div_nonneg hx hpositive.le
  have hyscale : 0 ≤ y / (x + y) :=
    div_nonneg hy hpositive.le
  have hxscale_one : x / (x + y) ≤ 1 := by
    apply (div_le_one hpositive).mpr
    linarith
  have hyscale_one : y / (x + y) ≤ 1 := by
    apply (div_le_one hpositive).mpr
    linarith
  have hxentropy := binaryEntropy_scale_le (x + y) (x / (x + y))
    (add_nonneg hx hy) hsum hxscale hxscale_one
  have hyentropy := binaryEntropy_scale_le (x + y) (y / (x + y))
    (add_nonneg hx hy) hsum hyscale hyscale_one
  have hxidentity : x / (x + y) * (x + y) = x := by
    field_simp [hpositive.ne']
  have hyidentity : y / (x + y) * (x + y) = y := by
    field_simp [hpositive.ne']
  rw [hxidentity] at hxentropy
  rw [hyidentity] at hyentropy
  have hcombined := add_le_add hxentropy hyentropy
  have hleft :
      x / (x + y) * binaryEntropy (x + y) +
          y / (x + y) * binaryEntropy (x + y) =
        binaryEntropy (x + y) := by
    field_simp [hpositive.ne']
  rw [hleft] at hcombined
  exact hcombined

theorem abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    (x y : ℝ)
    (hxzero : 0 ≤ x) (hxone : x ≤ 1)
    (hyzero : 0 ≤ y) (hyone : y ≤ 1) :
    |binaryEntropy x - binaryEntropy y| ≤
      binaryEntropy |x - y| := by
  have hordered :
      ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → x ≤ y →
        |binaryEntropy x - binaryEntropy y| ≤ binaryEntropy |x - y| := by
    intro a b hazero haone hbzero hbone hab
    have hdifference : 0 ≤ b - a := sub_nonneg.mpr hab
    have hforward :
        binaryEntropy b ≤ binaryEntropy a + binaryEntropy (b - a) := by
      have h := binaryEntropy_subadditive a (b - a)
        hazero hdifference (by linarith)
      have hargument : a + (b - a) = b := by ring
      rwa [hargument] at h
    have hbackward :
        binaryEntropy a ≤ binaryEntropy b + binaryEntropy (b - a) := by
      have h := binaryEntropy_subadditive (1 - b) (b - a)
        (sub_nonneg.mpr hbone) hdifference (by linarith)
      have hargument : 1 - b + (b - a) = 1 - a := by ring
      rw [hargument, binaryEntropy_one_sub, binaryEntropy_one_sub] at h
      exact h
    rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_le]
    have hneg : -(a - b) = b - a := by ring
    rw [hneg]
    constructor <;> linarith
  by_cases hxy : x ≤ y
  · exact hordered x y hxzero hxone hyzero hyone hxy
  · have hyx : y ≤ x := le_of_not_ge hxy
    have h := hordered y x hyzero hyone hxzero hxone hyx
    simpa [abs_sub_comm] using h

theorem binaryEntropy_mono_on_half
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyhalf : y ≤ (2 : ℝ)⁻¹) :
    binaryEntropy x ≤ binaryEntropy y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hxhalf : x ≤ (2 : ℝ)⁻¹ := hxy.trans hyhalf
  have hnatural := Real.binEntropy_strictMonoOn.monotoneOn
    (show x ∈ Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹) from ⟨hx, hxhalf⟩)
    (show y ∈ Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹) from ⟨hy, hyhalf⟩)
    hxy
  unfold binaryEntropy
  exact (div_le_div_iff_of_pos_right log_two_pos).mpr hnatural

noncomputable def binaryPinskerGap (q : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy q - (2 * q - 1) ^ 2 / 2

noncomputable def binaryPinskerGapDeriv (q : ℝ) : ℝ :=
  Real.log q - Real.log (1 - q) - 2 * (2 * q - 1)

noncomputable def binaryPinskerGapDerivTwo (q : ℝ) : ℝ :=
  q⁻¹ + (1 - q)⁻¹ - 4

theorem binaryPinskerGap_continuous : Continuous binaryPinskerGap := by
  unfold binaryPinskerGap
  fun_prop

theorem binaryPinskerGap_hasDerivAt {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGap (binaryPinskerGapDeriv q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hderiv :=
    ((Real.hasDerivAt_binEntropy hqzero hqone).const_sub (Real.log 2)).sub
      ((hlinear.pow 2).div_const 2)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [binaryPinskerGap, binaryPinskerGapDeriv]; ring)

theorem binaryPinskerGapDeriv_hasDerivAt {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGapDeriv (binaryPinskerGapDerivTwo q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hcomplement : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
    simpa using (hasDerivAt_id q).const_sub 1
  have hcomplement_ne : 1 - q ≠ 0 := sub_ne_zero.mpr hqone.symm
  have hderiv :=
    ((Real.hasDerivAt_log hqzero).sub
      (hcomplement.log hcomplement_ne)).sub (hlinear.const_mul 2)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [binaryPinskerGapDeriv, binaryPinskerGapDerivTwo]; ring)

theorem binaryPinskerGapDerivTwo_nonneg {q : ℝ}
    (hqzero : 0 < q) (hqone : q < 1) :
    0 ≤ binaryPinskerGapDerivTwo q := by
  have hcomplement : 0 < 1 - q := sub_pos.mpr hqone
  have hidentity :
      binaryPinskerGapDerivTwo q =
        (2 * q - 1) ^ 2 / (q * (1 - q)) := by
    unfold binaryPinskerGapDerivTwo
    field_simp [hqzero.ne', hcomplement.ne']
    ring
  rw [hidentity]
  exact div_nonneg (sq_nonneg _) (mul_pos hqzero hcomplement).le

theorem binaryPinskerGap_convex :
    ConvexOn ℝ (Set.Icc 0 1) binaryPinskerGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := binaryPinskerGapDeriv)
    (f'' := binaryPinskerGapDerivTwo)
    (convex_Icc (0 : ℝ) 1)
    binaryPinskerGap_continuous.continuousOn ?_ ?_ ?_
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact (binaryPinskerGap_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact
      (binaryPinskerGapDeriv_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact binaryPinskerGapDerivTwo_nonneg hq'.1 hq'.2

@[simp] theorem binaryPinskerGap_half :
    binaryPinskerGap ((2 : ℝ)⁻¹) = 0 := by
  unfold binaryPinskerGap
  rw [Real.binEntropy_two_inv]
  norm_num

@[simp] theorem binaryPinskerGapDeriv_half :
    binaryPinskerGapDeriv ((2 : ℝ)⁻¹) = 0 := by
  unfold binaryPinskerGapDeriv
  norm_num

theorem binary_pinsker (q : ℝ) (hqzero : 0 ≤ q) (hqone : q ≤ 1) :
    Real.binEntropy q ≤
      Real.log 2 - (2 * q - 1) ^ 2 / 2 := by
  have habove :
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (2 : ℝ)⁻¹ ≤ x →
        0 ≤ binaryPinskerGap x := by
    intro x hxzero hxone hxhalf
    by_cases hxeq : x = (2 : ℝ)⁻¹
    · simp [hxeq]
    · have hxstrict : (2 : ℝ)⁻¹ < x :=
        lt_of_le_of_ne hxhalf (Ne.symm hxeq)
      have hmid :
          HasDerivAt binaryPinskerGap 0 ((2 : ℝ)⁻¹) := by
        convert binaryPinskerGap_hasDerivAt
          (q := (2 : ℝ)⁻¹) (by norm_num) (by norm_num) using 1
        exact binaryPinskerGapDeriv_half.symm
      have hslope := binaryPinskerGap_convex.le_slope_of_hasDerivAt
        (show (2 : ℝ)⁻¹ ∈ Set.Icc 0 1 by constructor <;> norm_num)
        (show x ∈ Set.Icc 0 1 from ⟨hxzero, hxone⟩)
        hxstrict hmid
      rw [slope_def_field, binaryPinskerGap_half, sub_zero] at hslope
      rcases (div_nonneg_iff.mp hslope) with hpositive | hnegative
      · exact hpositive.1
      · exfalso
        have hden : 0 < x - (2 : ℝ)⁻¹ := sub_pos.mpr hxstrict
        linarith [hnegative.2]
  by_cases hhalf : (2 : ℝ)⁻¹ ≤ q
  · have hgap := habove q hqzero hqone hhalf
    unfold binaryPinskerGap at hgap
    linarith
  · have hcomplement : (2 : ℝ)⁻¹ ≤ 1 - q := by
      norm_num at hhalf ⊢
      linarith
    have hgap := habove (1 - q) (sub_nonneg.mpr hqone)
      (by linarith) hcomplement
    unfold binaryPinskerGap at hgap
    rw [Real.binEntropy_one_sub] at hgap
    nlinarith

theorem log_le_tangent {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ Real.log c + x / c - 1 := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hc)
  rw [Real.log_div hx.ne' hc.ne'] at hlog
  linarith

theorem log_four_thirds_lt_one_third :
    Real.log ((4 : ℝ) / 3) < (1 : ℝ) / 3 := by
  have hlog := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
    (show (4 : ℝ) / 3 ≠ 1 by norm_num)
  norm_num at hlog ⊢
  linarith

theorem sqrt_one_add_le (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + x / 2 := by
  have hroot := Real.sqrt_nonneg (1 + x)
  have hsquare := Real.sq_sqrt (show 0 ≤ 1 + x by linarith)
  nlinarith [sq_nonneg x]

theorem normalized_binary_cauchy (a b x y : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) :
    a * x + b * y ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
  have hrad : 0 ≤ x ^ 2 + y ^ 2 :=
    add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hroot := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  have hsquare := Real.sq_sqrt hrad
  have hidentity :
      (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 =
        (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    ring
  rw [hab, one_mul] at hidentity
  nlinarith [sq_nonneg (a * y - b * x)]

theorem binary_log_sum_bound (probability zeroWeight oneWeight : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1)
    (hzeroWeight : 0 < zeroWeight)
    (honeWeight : 0 < oneWeight) :
    Real.binEntropy probability +
        (1 - probability) * Real.log zeroWeight +
        probability * Real.log oneWeight ≤
      Real.log (zeroWeight + oneWeight) := by
  by_cases hzero : probability = 0
  · subst probability
    simpa using Real.log_le_log hzeroWeight
      (le_add_of_nonneg_right honeWeight.le)
  by_cases hone : probability = 1
  · subst probability
    simpa using Real.log_le_log honeWeight
      (le_add_of_nonneg_left hzeroWeight.le)
  have hprobability_pos : 0 < probability :=
    lt_of_le_of_ne hprobability_zero (Ne.symm hzero)
  have hcomplement_pos : 0 < 1 - probability :=
    sub_pos.mpr (lt_of_le_of_ne hprobability_one hone)
  have hnormalize :
      (1 - probability) * (zeroWeight / (1 - probability)) +
          probability * (oneWeight / probability) =
        zeroWeight + oneWeight := by
    field_simp [hprobability_pos.ne', hcomplement_pos.ne']
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.2
    (show zeroWeight / (1 - probability) ∈ Set.Ioi (0 : ℝ) from
      div_pos hzeroWeight hcomplement_pos)
    (show oneWeight / probability ∈ Set.Ioi (0 : ℝ) from
      div_pos honeWeight hprobability_pos)
    hcomplement_pos.le hprobability_pos.le
    (show (1 - probability) + probability = 1 by ring)
  simp only [smul_eq_mul] at hjensen
  rw [hnormalize] at hjensen
  rw [Real.log_div hzeroWeight.ne' hcomplement_pos.ne',
    Real.log_div honeWeight.ne' hprobability_pos.ne'] at hjensen
  have hentropy :
      Real.binEntropy probability =
        -(1 - probability) * Real.log (1 - probability) -
          probability * Real.log probability := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  rw [hentropy]
  linarith

noncomputable def entropyTangentSigma : ℝ :=
  4 / (3 * Real.sqrt 2)

noncomputable def entropyTangentRho : ℝ :=
  Real.sqrt 2 / Real.sqrt 3

theorem entropyTangentSigma_pos : 0 < entropyTangentSigma := by
  unfold entropyTangentSigma
  positivity

theorem entropyTangentRho_pos : 0 < entropyTangentRho := by
  unfold entropyTangentRho
  positivity

theorem log_entropyTangentSigma :
    Real.log entropyTangentSigma =
      (3 / 2 : ℝ) * Real.log 2 - Real.log 3 := by
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  unfold entropyTangentSigma
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), hlogfour]
  ring

theorem log_entropyTangentRho :
    Real.log entropyTangentRho =
      (Real.log 2 - Real.log 3) / 2 := by
  unfold entropyTangentRho
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_sqrt (by positivity)]
  ring

theorem sqrt_three_mul_entropyTangentRho :
    Real.sqrt 3 * entropyTangentRho = Real.sqrt 2 := by
  unfold entropyTangentRho
  have hthree : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp [hthree]

noncomputable def entropyTangentZeroCoefficient (q : ℝ) : ℝ :=
  Real.sqrt 2 * (3 - 2 * q) / 4

noncomputable def entropyTangentOneCoefficient (q : ℝ) : ℝ :=
  Real.sqrt 2 * (1 + 2 * q) / 4

theorem entropyTangentZeroCoefficient_eq (q : ℝ) :
    (1 - q) ^ 2 / entropyTangentSigma +
        q ^ 2 / (3 * entropyTangentSigma) +
        2 * q * (1 - q) /
          (Real.sqrt 3 * entropyTangentRho) =
      entropyTangentZeroCoefficient q := by
  rw [sqrt_three_mul_entropyTangentRho]
  unfold entropyTangentSigma entropyTangentZeroCoefficient
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [htwo]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem entropyTangentOneCoefficient_eq (q : ℝ) :
    (1 - q) ^ 2 / (3 * entropyTangentSigma) +
        q ^ 2 / entropyTangentSigma +
        2 * q * (1 - q) /
          (Real.sqrt 3 * entropyTangentRho) =
      entropyTangentOneCoefficient q := by
  rw [sqrt_three_mul_entropyTangentRho]
  unfold entropyTangentSigma entropyTangentOneCoefficient
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [htwo]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem entropyTangentCoefficient_norm (q : ℝ) :
    entropyTangentZeroCoefficient q ^ 2 +
        entropyTangentOneCoefficient q ^ 2 =
      1 + (2 * q - 1) ^ 2 / 4 := by
  unfold entropyTangentZeroCoefficient entropyTangentOneCoefficient
  calc
    (Real.sqrt 2 * (3 - 2 * q) / 4) ^ 2 +
        (Real.sqrt 2 * (1 + 2 * q) / 4) ^ 2 =
      (Real.sqrt 2) ^ 2 *
        (((3 - 2 * q) ^ 2 + (1 + 2 * q) ^ 2) / 16) := by ring
    _ = 1 + (2 * q - 1) ^ 2 / 4 := by
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      ring

theorem entropyTangentLog_constant (q : ℝ) :
    ((1 - q) ^ 2 + q ^ 2) * Real.log entropyTangentSigma +
        2 * q * (1 - q) * Real.log entropyTangentRho =
      Real.log 2 - (3 / 4 : ℝ) * Real.log 3 +
        (2 * q - 1) ^ 2 / 4 * Real.log ((4 : ℝ) / 3) := by
  have hlogfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [log_entropyTangentSigma, log_entropyTangentRho,
    Real.log_div (by positivity) (by positivity), hlogfour]
  ring

noncomputable def binaryConditionalLogPotential (q zeroAmplitude oneAmplitude : ℝ) : ℝ :=
  Real.binEntropy q / 2 +
    (1 - q) ^ 2 * Real.log (zeroAmplitude + oneAmplitude / 3) +
    q ^ 2 * Real.log (zeroAmplitude / 3 + oneAmplitude) +
    2 * q * (1 - q) *
      Real.log ((zeroAmplitude + oneAmplitude) / Real.sqrt 3)

theorem binaryConditionalLogPotential_tangent_bound
    (q zeroAmplitude oneAmplitude : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1)
    (hzeroAmplitude : 0 ≤ zeroAmplitude)
    (honeAmplitude : 0 ≤ oneAmplitude)
    (hamplitudes : zeroAmplitude ^ 2 + oneAmplitude ^ 2 = 1) :
    binaryConditionalLogPotential q zeroAmplitude oneAmplitude ≤
      Real.binEntropy q / 2 +
        Real.log 2 - (3 / 4 : ℝ) * Real.log 3 +
        (2 * q - 1) ^ 2 / 4 * Real.log ((4 : ℝ) / 3) +
        Real.sqrt (1 + (2 * q - 1) ^ 2 / 4) - 1 := by
  have hsum : 0 < zeroAmplitude + oneAmplitude := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hargzero : 0 < zeroAmplitude + oneAmplitude / 3 := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hargone : 0 < zeroAmplitude / 3 + oneAmplitude := by
    nlinarith [sq_nonneg zeroAmplitude, sq_nonneg oneAmplitude]
  have hthree : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hargmixed :
      0 < (zeroAmplitude + oneAmplitude) / Real.sqrt 3 :=
    div_pos hsum hthree
  have htangentzero := mul_le_mul_of_nonneg_left
    (log_le_tangent hargzero entropyTangentSigma_pos)
    (sq_nonneg (1 - q))
  have htangentone := mul_le_mul_of_nonneg_left
    (log_le_tangent hargone entropyTangentSigma_pos)
    (sq_nonneg q)
  have hmixedweight : 0 ≤ 2 * q * (1 - q) := by
    have hcomplement : 0 ≤ 1 - q := sub_nonneg.mpr hqone
    positivity
  have htangentmixed := mul_le_mul_of_nonneg_left
    (log_le_tangent hargmixed entropyTangentRho_pos)
    hmixedweight
  have hcombined :=
    add_le_add (add_le_add htangentzero htangentone) htangentmixed
  have hright :
      ((1 - q) ^ 2 *
          (Real.log entropyTangentSigma +
            (zeroAmplitude + oneAmplitude / 3) /
              entropyTangentSigma - 1) +
        q ^ 2 *
          (Real.log entropyTangentSigma +
            (zeroAmplitude / 3 + oneAmplitude) /
              entropyTangentSigma - 1)) +
        (2 * q * (1 - q)) *
          (Real.log entropyTangentRho +
            ((zeroAmplitude + oneAmplitude) / Real.sqrt 3) /
              entropyTangentRho - 1) =
        ((1 - q) ^ 2 + q ^ 2) * Real.log entropyTangentSigma +
          2 * q * (1 - q) * Real.log entropyTangentRho +
          zeroAmplitude * entropyTangentZeroCoefficient q +
          oneAmplitude * entropyTangentOneCoefficient q - 1 := by
    rw [← entropyTangentZeroCoefficient_eq,
      ← entropyTangentOneCoefficient_eq]
    field_simp [entropyTangentSigma_pos.ne',
      entropyTangentRho_pos.ne', hthree.ne']
    ring
  rw [hright, entropyTangentLog_constant] at hcombined
  have hcauchy := normalized_binary_cauchy
    zeroAmplitude oneAmplitude
    (entropyTangentZeroCoefficient q)
    (entropyTangentOneCoefficient q) hamplitudes
  rw [entropyTangentCoefficient_norm] at hcauchy
  unfold binaryConditionalLogPotential
  linarith

theorem binaryConditionalLogPotential_le_kappa
    (q zeroAmplitude oneAmplitude : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1)
    (hzeroAmplitude : 0 ≤ zeroAmplitude)
    (honeAmplitude : 0 ≤ oneAmplitude)
    (hamplitudes : zeroAmplitude ^ 2 + oneAmplitude ^ 2 = 1) :
    binaryConditionalLogPotential q zeroAmplitude oneAmplitude ≤
      kappa * Real.log 2 := by
  have htangent := binaryConditionalLogPotential_tangent_bound
    q zeroAmplitude oneAmplitude hqzero hqone
    hzeroAmplitude honeAmplitude hamplitudes
  have hpinsker := binary_pinsker q hqzero hqone
  have hsqrt := sqrt_one_add_le ((2 * q - 1) ^ 2 / 4)
    (by positivity)
  have hlogscaled := mul_le_mul_of_nonneg_left
    log_four_thirds_lt_one_third.le
    (show 0 ≤ (2 * q - 1) ^ 2 / 4 by positivity)
  have hkappa :
      kappa * Real.log 2 =
        (3 / 2 : ℝ) * Real.log 2 -
          (3 / 4 : ℝ) * Real.log 3 := by
    unfold kappa logTwo
    field_simp [log_two_pos.ne']
  rw [hkappa]
  nlinarith [sq_nonneg (2 * q - 1)]

def binaryCoinMass (q : ℝ) (outcome : Bool) : ℝ :=
  if outcome then q else 1 - q

theorem binaryCoinMass_nonneg {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (outcome : Bool) :
    0 ≤ binaryCoinMass q outcome := by
  cases outcome <;> simp [binaryCoinMass] <;> linarith

def independentBinaryPairMass (q : ℝ) (left right : Bool) : ℝ :=
  binaryCoinMass q left * binaryCoinMass q right

theorem independentBinaryPairMass_nonneg {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (left right : Bool) :
    0 ≤ independentBinaryPairMass q left right := by
  exact mul_nonneg
    (binaryCoinMass_nonneg hqzero hqone left)
    (binaryCoinMass_nonneg hqzero hqone right)

theorem independentBinaryPairMass_sum (q : ℝ) :
    (∑ left : Bool, ∑ right : Bool,
      independentBinaryPairMass q left right) = 1 := by
  simp [Fintype.univ_bool, independentBinaryPairMass, binaryCoinMass]
  ring

structure BinaryPairKernel where

  parentProbability : ℝ
  parentProbability_nonneg : 0 ≤ parentProbability
  parentProbability_le_one : parentProbability ≤ 1

  childProbability : Bool → Bool → ℝ
  childProbability_nonneg : ∀ left right, 0 ≤ childProbability left right
  childProbability_le_one : ∀ left right, childProbability left right ≤ 1

namespace BinaryPairKernel

noncomputable def childMarginal (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      kernel.childProbability left right

noncomputable def conditionalEntropy (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      binaryEntropy (kernel.childProbability left right)

def bitDisagreementProbability (parent : Bool) (childProbability : ℝ) : ℝ :=
  if parent then 1 - childProbability else childProbability

noncomputable def averageDisagreement (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      ((bitDisagreementProbability left
          (kernel.childProbability left right) +
        bitDisagreementProbability right
          (kernel.childProbability left right)) / 2)

theorem childMarginal_nonneg (kernel : BinaryPairKernel) :
    0 ≤ kernel.childMarginal := by
  unfold childMarginal
  apply Finset.sum_nonneg
  intro left _
  apply Finset.sum_nonneg
  intro right _
  exact mul_nonneg
    (independentBinaryPairMass_nonneg
      kernel.parentProbability_nonneg kernel.parentProbability_le_one
      left right)
    (kernel.childProbability_nonneg left right)

theorem childMarginal_le_one (kernel : BinaryPairKernel) :
    kernel.childMarginal ≤ 1 := by
  unfold childMarginal
  calc
    (∑ left : Bool, ∑ right : Bool,
        independentBinaryPairMass kernel.parentProbability left right *
          kernel.childProbability left right) ≤
      ∑ left : Bool, ∑ right : Bool,
        independentBinaryPairMass kernel.parentProbability left right * 1 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact mul_le_mul_of_nonneg_left
            (kernel.childProbability_le_one left right)
            (independentBinaryPairMass_nonneg
              kernel.parentProbability_nonneg kernel.parentProbability_le_one
              left right)
    _ = 1 := by
      simpa using independentBinaryPairMass_sum kernel.parentProbability

theorem childMarginal_eq_four_outcomes (kernel : BinaryPairKernel) :
    kernel.childMarginal =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        (1 - kernel.parentProbability) * kernel.parentProbability *
          kernel.childProbability false true +
        kernel.parentProbability * (1 - kernel.parentProbability) *
          kernel.childProbability true false +
        kernel.parentProbability ^ 2 *
          kernel.childProbability true true := by
  simp [childMarginal, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass]
  ring

theorem conditionalEntropy_mul_log_two (kernel : BinaryPairKernel) :
    kernel.conditionalEntropy * Real.log 2 =
      (1 - kernel.parentProbability) ^ 2 *
          Real.binEntropy (kernel.childProbability false false) +
        (1 - kernel.parentProbability) * kernel.parentProbability *
          Real.binEntropy (kernel.childProbability false true) +
        kernel.parentProbability * (1 - kernel.parentProbability) *
          Real.binEntropy (kernel.childProbability true false) +
        kernel.parentProbability ^ 2 *
          Real.binEntropy (kernel.childProbability true true) := by
  simp [conditionalEntropy, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass, binaryEntropy]
  field_simp [log_two_pos.ne']
  ring

theorem bitDisagreementProbability_mem_Icc (parent : Bool)
    (childProbability : ℝ)
    (hzero : 0 ≤ childProbability) (hone : childProbability ≤ 1) :
    0 ≤ bitDisagreementProbability parent childProbability ∧
      bitDisagreementProbability parent childProbability ≤ 1 := by
  cases parent <;> simp [bitDisagreementProbability] <;> constructor <;>
    linarith

theorem averageDisagreement_eq_four_outcomes (kernel : BinaryPairKernel) :
    kernel.averageDisagreement =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        kernel.parentProbability * (1 - kernel.parentProbability) +
        kernel.parentProbability ^ 2 *
          (1 - kernel.childProbability true true) := by
  simp [averageDisagreement, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass,
    bitDisagreementProbability]
  ring

noncomputable def smoothed (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) : BinaryPairKernel where
  parentProbability := kernel.parentProbability
  parentProbability_nonneg := kernel.parentProbability_nonneg
  parentProbability_le_one := kernel.parentProbability_le_one
  childProbability left right :=
    (1 - mixing) * kernel.childProbability left right + mixing / 2
  childProbability_nonneg := by
    intro left right
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hmixing_one)
        (kernel.childProbability_nonneg left right))
      (div_nonneg hmixing_zero (by norm_num))
  childProbability_le_one := by
    intro left right
    have hproduct := mul_le_mul_of_nonneg_left
      (kernel.childProbability_le_one left right)
      (sub_nonneg.mpr hmixing_one)
    nlinarith

theorem smoothed_childMarginal (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).childMarginal =
      (1 - mixing) * kernel.childMarginal + mixing / 2 := by
  rw [childMarginal_eq_four_outcomes,
    childMarginal_eq_four_outcomes kernel]
  simp [smoothed]
  ring

theorem smoothed_averageDisagreement (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).averageDisagreement =
      (1 - mixing) * kernel.averageDisagreement + mixing / 2 := by
  rw [averageDisagreement_eq_four_outcomes,
    averageDisagreement_eq_four_outcomes kernel]
  simp [smoothed]
  ring

noncomputable def smoothedConditionalEntropy
    (kernel : BinaryPairKernel) (mixing : ℝ) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      binaryEntropy
        ((1 - mixing) * kernel.childProbability left right + mixing / 2)

theorem smoothedConditionalEntropy_continuous (kernel : BinaryPairKernel) :
    Continuous (smoothedConditionalEntropy kernel) := by
  unfold smoothedConditionalEntropy
  fun_prop

theorem smoothed_conditionalEntropy (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).conditionalEntropy =
      smoothedConditionalEntropy kernel mixing := by
  rfl

theorem conditionalEntropy_logsum_reduction (kernel : BinaryPairKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy * Real.log 2 -
        Real.binEntropy kernel.childMarginal / 2 -
        Real.log 3 * kernel.averageDisagreement ≤
      binaryConditionalLogPotential kernel.parentProbability
          (Real.sqrt (1 - kernel.childMarginal))
          (Real.sqrt kernel.childMarginal) -
        Real.binEntropy kernel.parentProbability / 2 := by
  let q : ℝ := kernel.parentProbability
  let v : ℝ := kernel.childMarginal
  let a : ℝ := Real.sqrt (1 - v)
  let b : ℝ := Real.sqrt v
  let z₀₀ : ℝ := kernel.childProbability false false
  let z₀₁ : ℝ := kernel.childProbability false true
  let z₁₀ : ℝ := kernel.childProbability true false
  let z₁₁ : ℝ := kernel.childProbability true true
  have hqzero : 0 ≤ q := kernel.parentProbability_nonneg
  have hqone : q ≤ 1 := kernel.parentProbability_le_one
  have hvzero : 0 < v := hmarginal_zero
  have hvone : v < 1 := hmarginal_one
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr (sub_pos.mpr hvone)
  have hb : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.mpr hvzero
  have hthree : 0 < Real.sqrt (3 : ℝ) := by positivity
  have h₀₀ := binary_log_sum_bound z₀₀ a (b / 3)
    (kernel.childProbability_nonneg false false)
    (kernel.childProbability_le_one false false)
    ha (by positivity)
  have h₀₁ := binary_log_sum_bound z₀₁
    (a / Real.sqrt 3) (b / Real.sqrt 3)
    (kernel.childProbability_nonneg false true)
    (kernel.childProbability_le_one false true)
    (div_pos ha hthree) (div_pos hb hthree)
  have h₁₀ := binary_log_sum_bound z₁₀
    (a / Real.sqrt 3) (b / Real.sqrt 3)
    (kernel.childProbability_nonneg true false)
    (kernel.childProbability_le_one true false)
    (div_pos ha hthree) (div_pos hb hthree)
  have h₁₁ := binary_log_sum_bound z₁₁ (a / 3) b
    (kernel.childProbability_nonneg true true)
    (kernel.childProbability_le_one true true)
    (by positivity) hb
  have hcomplement : 0 ≤ 1 - q := sub_nonneg.mpr hqone
  have hscaled₀₀ := mul_le_mul_of_nonneg_left h₀₀
    (sq_nonneg (1 - q))
  have hscaled₀₁ := mul_le_mul_of_nonneg_left h₀₁
    (mul_nonneg hcomplement hqzero)
  have hscaled₁₀ := mul_le_mul_of_nonneg_left h₁₀
    (mul_nonneg hqzero hcomplement)
  have hscaled₁₁ := mul_le_mul_of_nonneg_left h₁₁ (sq_nonneg q)
  have hcombined := add_le_add
    (add_le_add (add_le_add hscaled₀₀ hscaled₀₁) hscaled₁₀)
    hscaled₁₁
  have hmarginal :
      v =
        (1 - q) ^ 2 * z₀₀ +
          (1 - q) * q * z₀₁ +
          q * (1 - q) * z₁₀ +
          q ^ 2 * z₁₁ := by
    simpa [q, v, z₀₀, z₀₁, z₁₀, z₁₁] using
      childMarginal_eq_four_outcomes kernel
  have hentropy :
      kernel.conditionalEntropy * Real.log 2 =
        (1 - q) ^ 2 * Real.binEntropy z₀₀ +
          (1 - q) * q * Real.binEntropy z₀₁ +
          q * (1 - q) * Real.binEntropy z₁₀ +
          q ^ 2 * Real.binEntropy z₁₁ := by
    simpa [q, z₀₀, z₀₁, z₁₀, z₁₁] using
      conditionalEntropy_mul_log_two kernel
  have hdisagreement :
      kernel.averageDisagreement =
        (1 - q) ^ 2 * z₀₀ +
          q * (1 - q) + q ^ 2 * (1 - z₁₁) := by
    simpa [q, z₀₀, z₁₁] using
      averageDisagreement_eq_four_outcomes kernel
  have hloga : Real.log a = Real.log (1 - v) / 2 := by
    dsimp [a]
    exact Real.log_sqrt (sub_pos.mpr hvone).le
  have hlogb : Real.log b = Real.log v / 2 := by
    dsimp [b]
    exact Real.log_sqrt hvzero.le
  have hlogthree :
      Real.log (Real.sqrt (3 : ℝ)) = Real.log 3 / 2 :=
    Real.log_sqrt (by positivity)
  have hchildentropy :
      Real.binEntropy v =
        -v * Real.log v - (1 - v) * Real.log (1 - v) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  have hleft :
      (((1 - q) ^ 2 *
          (Real.binEntropy z₀₀ +
            (1 - z₀₀) * Real.log a + z₀₀ * Real.log (b / 3)) +
        ((1 - q) * q) *
          (Real.binEntropy z₀₁ +
            (1 - z₀₁) * Real.log (a / Real.sqrt 3) +
              z₀₁ * Real.log (b / Real.sqrt 3))) +
        (q * (1 - q)) *
          (Real.binEntropy z₁₀ +
            (1 - z₁₀) * Real.log (a / Real.sqrt 3) +
              z₁₀ * Real.log (b / Real.sqrt 3))) +
        q ^ 2 *
          (Real.binEntropy z₁₁ +
            (1 - z₁₁) * Real.log (a / 3) + z₁₁ * Real.log b) =
        kernel.conditionalEntropy * Real.log 2 -
          Real.binEntropy v / 2 -
          Real.log 3 * kernel.averageDisagreement := by
    rw [hentropy, hdisagreement, hchildentropy,
      Real.log_div hb.ne' (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div ha.ne' hthree.ne',
      Real.log_div hb.ne' hthree.ne',
      Real.log_div ha.ne' (by norm_num : (3 : ℝ) ≠ 0),
      hloga, hlogb, hlogthree]
    linear_combination
      ((Real.log (1 - v) - Real.log v) / 2) * hmarginal
  have hright :
      (((1 - q) ^ 2 * Real.log (a + b / 3) +
        ((1 - q) * q) *
          Real.log (a / Real.sqrt 3 + b / Real.sqrt 3)) +
        (q * (1 - q)) *
          Real.log (a / Real.sqrt 3 + b / Real.sqrt 3)) +
        q ^ 2 * Real.log (a / 3 + b) =
        binaryConditionalLogPotential q a b - Real.binEntropy q / 2 := by
    have hmixed :
        a / Real.sqrt 3 + b / Real.sqrt 3 =
          (a + b) / Real.sqrt 3 := by ring
    rw [hmixed]
    unfold binaryConditionalLogPotential
    ring
  rw [hleft, hright] at hcombined
  simpa [q, v, a, b] using hcombined

theorem conditionalEntropy_bound_of_marginal_interior
    (kernel : BinaryPairKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy ≤
      kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  have hzeroAmplitude :
      0 ≤ Real.sqrt (1 - kernel.childMarginal) :=
    Real.sqrt_nonneg _
  have honeAmplitude : 0 ≤ Real.sqrt kernel.childMarginal :=
    Real.sqrt_nonneg _
  have hamplitudes :
      Real.sqrt (1 - kernel.childMarginal) ^ 2 +
          Real.sqrt kernel.childMarginal ^ 2 = 1 := by
    rw [Real.sq_sqrt (sub_pos.mpr hmarginal_one).le,
      Real.sq_sqrt hmarginal_zero.le]
    ring
  have hpotential := binaryConditionalLogPotential_le_kappa
    kernel.parentProbability
    (Real.sqrt (1 - kernel.childMarginal))
    (Real.sqrt kernel.childMarginal)
    kernel.parentProbability_nonneg kernel.parentProbability_le_one
    hzeroAmplitude honeAmplitude hamplitudes
  have hreduction := conditionalEntropy_logsum_reduction kernel
    hmarginal_zero hmarginal_one
  have hright :
      (kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2) * Real.log 2 =
        kappa * Real.log 2 +
          Real.log 3 * kernel.averageDisagreement +
          (Real.binEntropy kernel.childMarginal -
            Real.binEntropy kernel.parentProbability) / 2 := by
    unfold binaryEntropy logTwo
    field_simp [log_two_pos.ne']
  have hscaled :
      kernel.conditionalEntropy * Real.log 2 ≤
        (kappa + logTwo 3 * kernel.averageDisagreement +
          (binaryEntropy kernel.childMarginal -
            binaryEntropy kernel.parentProbability) / 2) * Real.log 2 := by
    rw [hright]
    linarith
  exact (mul_le_mul_iff_of_pos_right log_two_pos).mp hscaled

theorem conditionalEntropy_bound (kernel : BinaryPairKernel) :
    kernel.conditionalEntropy ≤
      kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  let mixing : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hmixing_pos (n : ℕ) : 0 < mixing n := by
    dsimp [mixing]
    positivity
  have hmixing_le_one (n : ℕ) : mixing n ≤ 1 := by
    dsimp [mixing]
    apply (div_le_one (by positivity)).mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  let approximation : ℕ → BinaryPairKernel := fun n =>
    smoothed kernel (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hmixing_tendsto :
      Filter.Tendsto mixing Filter.atTop (nhds 0) := by
    simpa [mixing] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmarginal_zero (n : ℕ) : 0 < (approximation n).childMarginal := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change 0 < (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal
    rw [hformula]
    have hnonnegative := mul_nonneg
      (sub_nonneg.mpr (hmixing_le_one n))
      (childMarginal_nonneg kernel)
    have hpositive := div_pos (hmixing_pos n) (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmarginal_one (n : ℕ) : (approximation n).childMarginal < 1 := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal < 1
    rw [hformula]
    have hproduct := mul_le_mul_of_nonneg_left
      (childMarginal_le_one kernel)
      (sub_nonneg.mpr (hmixing_le_one n))
    have hpositive := hmixing_pos n
    nlinarith
  have hconditional_tendsto :
      Filter.Tendsto (fun n => (approximation n).conditionalEntropy)
        Filter.atTop (nhds kernel.conditionalEntropy) := by
    have hcontinuous :=
      (smoothedConditionalEntropy_continuous kernel).continuousAt.tendsto.comp
        hmixing_tendsto
    have hzero :
        smoothedConditionalEntropy kernel 0 = kernel.conditionalEntropy := by
      simp [smoothedConditionalEntropy, conditionalEntropy]
    rw [hzero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with n
    exact (smoothed_conditionalEntropy kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)).symm
  have hmarginal_tendsto :
      Filter.Tendsto (fun n => (approximation n).childMarginal)
        Filter.atTop (nhds kernel.childMarginal) := by
    have hlinear :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
        (tendsto_const_nhds (x := kernel.childMarginal))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.childMarginal + mixing n / 2)
          Filter.atTop (nhds kernel.childMarginal) := by
      simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hdisagreement_tendsto :
      Filter.Tendsto (fun n => (approximation n).averageDisagreement)
        Filter.atTop (nhds kernel.averageDisagreement) := by
    have hlinear :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
        (tendsto_const_nhds (x := kernel.averageDisagreement))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.averageDisagreement + mixing n / 2)
          Filter.atTop (nhds kernel.averageDisagreement) := by
      simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_averageDisagreement kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hchildentropy_tendsto :=
    binaryEntropy_continuous.continuousAt.tendsto.comp hmarginal_tendsto
  have hparent (n : ℕ) :
      (approximation n).parentProbability = kernel.parentProbability := by
    rfl
  have hright_tendsto :
      Filter.Tendsto
        (fun n =>
          kappa + logTwo 3 * (approximation n).averageDisagreement +
            (binaryEntropy (approximation n).childMarginal -
              binaryEntropy (approximation n).parentProbability) / 2)
        Filter.atTop
        (nhds
          (kappa + logTwo 3 * kernel.averageDisagreement +
            (binaryEntropy kernel.childMarginal -
              binaryEntropy kernel.parentProbability) / 2)) := by
    simp_rw [hparent]
    have hdisagreement_term :=
      (tendsto_const_nhds (x := logTwo 3)).mul hdisagreement_tendsto
    have hentropy_term :=
      (hchildentropy_tendsto.sub
        (tendsto_const_nhds (x :=
          binaryEntropy kernel.parentProbability))).div_const 2
    have hsum :=
      (tendsto_const_nhds (x := kappa)).add
        (hdisagreement_term.add hentropy_term)
    simpa [add_assoc] using hsum
  refine le_of_tendsto_of_tendsto'
    hconditional_tendsto hright_tendsto ?_
  intro n
  exact conditionalEntropy_bound_of_marginal_interior
    (approximation n) (hmarginal_zero n) (hmarginal_one n)

end BinaryPairKernel

def empiricalBinaryOutcomeCount
    (parentCount oneCount : ℕ) (outcome : Bool) : ℝ :=
  if outcome then (oneCount : ℝ)
  else (parentCount : ℝ) - (oneCount : ℝ)

noncomputable def withoutReplacementBinaryPairMass
    (parentCount oneCount : ℕ) (left right : Bool) : ℝ :=
  empiricalBinaryOutcomeCount parentCount oneCount left *
      (empiricalBinaryOutcomeCount parentCount oneCount right -
        if left = right then 1 else 0) /
    ((parentCount : ℝ) * ((parentCount : ℝ) - 1))

theorem withoutReplacementBinaryPairMass_nonneg
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (left right : Bool) :
    0 ≤ withoutReplacementBinaryPairMass parentCount oneCount left right := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  have hdenominator :
      0 ≤ (parentCount : ℝ) * ((parentCount : ℝ) - 1) :=
    (mul_pos hparent_real hparent_minus).le
  have hone_nonneg : (0 : ℝ) ≤ (oneCount : ℝ) := by positivity
  have hcount : (oneCount : ℝ) ≤ (parentCount : ℝ) := by
    exact_mod_cast hones
  have hzero_nonneg : 0 ≤ (parentCount : ℝ) - (oneCount : ℝ) := by
    linarith
  have hone_diagonal :
      0 ≤ (oneCount : ℝ) * ((oneCount : ℝ) - 1) := by
    by_cases hzero : oneCount = 0
    · simp [hzero]
    · have hone : 1 ≤ oneCount := Nat.one_le_iff_ne_zero.mpr hzero
      have hone_real : (1 : ℝ) ≤ (oneCount : ℝ) := by
        exact_mod_cast hone
      positivity
  have hzero_diagonal :
      0 ≤ ((parentCount : ℝ) - (oneCount : ℝ)) *
        ((parentCount : ℝ) - (oneCount : ℝ) - 1) := by
    by_cases hfull : oneCount = parentCount
    · simp [hfull]
    · have hstrict : oneCount < parentCount :=
        lt_of_le_of_ne hones hfull
      have hsucc : oneCount + 1 ≤ parentCount := by omega
      have hsucc_real :
          (oneCount : ℝ) + 1 ≤ (parentCount : ℝ) := by
        exact_mod_cast hsucc
      have hfactor :
          0 ≤ (parentCount : ℝ) - (oneCount : ℝ) - 1 := by
        linarith
      exact mul_nonneg hzero_nonneg hfactor
  cases left <;> cases right
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg hzero_diagonal hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg (mul_nonneg hzero_nonneg hone_nonneg) hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg (mul_nonneg hone_nonneg hzero_nonneg) hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg hone_diagonal hdenominator

theorem withoutReplacementBinaryPairMass_sum
    (parentCount oneCount : ℕ) (hparents : 2 ≤ parentCount) :
    (∑ left : Bool, ∑ right : Bool,
      withoutReplacementBinaryPairMass parentCount oneCount left right) = 1 := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  simp [Fintype.univ_bool,
    withoutReplacementBinaryPairMass, empiricalBinaryOutcomeCount]
  field_simp [hparent_real.ne', hparent_minus.ne']
  ring

noncomputable def withoutReplacementBinaryPairExpectation
    (parentCount oneCount : ℕ) (f : Bool → Bool → ℝ) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    withoutReplacementBinaryPairMass parentCount oneCount left right *
      f left right

theorem withoutReplacementBinaryPairExpectation_sub
    (parentCount oneCount : ℕ) (hparents : 2 ≤ parentCount)
    (f : Bool → Bool → ℝ) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right) =
      (((oneCount : ℝ) / (parentCount : ℝ)) *
        (1 - (oneCount : ℝ) / (parentCount : ℝ)) /
          ((parentCount : ℝ) - 1)) *
        (f false true + f true false - f false false - f true true) := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  simp [withoutReplacementBinaryPairExpectation, Fintype.univ_bool,
    withoutReplacementBinaryPairMass, empiricalBinaryOutcomeCount,
    independentBinaryPairMass, binaryCoinMass]
  field_simp [hparent_real.ne', hparent_minus.ne']
  ring

theorem withoutReplacementBinaryPairExpectation_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right ∧ f left right ≤ 1) :
    |withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right)| ≤ 1 / (parentCount : ℝ) := by
  let q : ℝ := (oneCount : ℝ) / (parentCount : ℝ)
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  have hqzero : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    dsimp [q]
    apply (div_le_one hparent_real).mpr
    exact_mod_cast hones
  have hvariance : q * (1 - q) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (q - 1 / 2)]
  have hscaledvariance :=
    mul_le_mul_of_nonneg_right hvariance hparent_real.le
  have hdelta_nonneg : 0 ≤ q * (1 - q) / ((parentCount : ℝ) - 1) := by
    exact div_nonneg
      (mul_nonneg hqzero (sub_nonneg.mpr hqone))
      hparent_minus.le
  have hdelta_bound :
      2 * (q * (1 - q) / ((parentCount : ℝ) - 1)) ≤
        1 / (parentCount : ℝ) := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    rw [show 2 * (q * (1 - q) / ((parentCount : ℝ) - 1)) =
      (2 * (q * (1 - q))) / ((parentCount : ℝ) - 1) by ring]
    apply (div_le_div_iff₀ hparent_minus hparent_real).mpr
    nlinarith
  have hbracket :
      |f false true + f true false - f false false - f true true| ≤
        (2 : ℝ) := by
    rw [abs_le]
    have h₀₀ := hf false false
    have h₀₁ := hf false true
    have h₁₀ := hf true false
    have h₁₁ := hf true true
    constructor <;> linarith
  rw [withoutReplacementBinaryPairExpectation_sub
    parentCount oneCount hparents f, abs_mul]
  change
    |q * (1 - q) / ((parentCount : ℝ) - 1)| *
        |f false true + f true false - f false false - f true true| ≤
      1 / (parentCount : ℝ)
  rw [abs_of_nonneg hdelta_nonneg]
  calc
    (q * (1 - q) / ((parentCount : ℝ) - 1)) *
        |f false true + f true false - f false false - f true true| ≤
      (q * (1 - q) / ((parentCount : ℝ) - 1)) * 2 :=
        mul_le_mul_of_nonneg_left hbracket hdelta_nonneg
    _ ≤ 1 / (parentCount : ℝ) := by
      nlinarith

theorem withoutReplacementBinaryPairExpectation_nonneg
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right) :
    0 ≤ withoutReplacementBinaryPairExpectation parentCount oneCount f := by
  unfold withoutReplacementBinaryPairExpectation
  apply Finset.sum_nonneg
  intro left _
  apply Finset.sum_nonneg
  intro right _
  exact mul_nonneg
    (withoutReplacementBinaryPairMass_nonneg
      parentCount oneCount hparents hones left right)
    (hf left right)

theorem withoutReplacementBinaryPairExpectation_le_one
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, f left right ≤ 1) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f ≤ 1 := by
  unfold withoutReplacementBinaryPairExpectation
  calc
    (∑ left : Bool, ∑ right : Bool,
        withoutReplacementBinaryPairMass parentCount oneCount left right *
          f left right) ≤
      ∑ left : Bool, ∑ right : Bool,
        withoutReplacementBinaryPairMass parentCount oneCount left right * 1 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact mul_le_mul_of_nonneg_left (hf left right)
            (withoutReplacementBinaryPairMass_nonneg
              parentCount oneCount hparents hones left right)
    _ = 1 := by
      simpa using
        withoutReplacementBinaryPairMass_sum parentCount oneCount hparents

noncomputable def empiricalChildMarginal
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    kernel.childProbability

noncomputable def empiricalConditionalEntropy
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    (fun left right => binaryEntropy (kernel.childProbability left right))

noncomputable def empiricalAverageDisagreement
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    (fun left right =>
      (BinaryPairKernel.bitDisagreementProbability left
          (kernel.childProbability left right) +
        BinaryPairKernel.bitDisagreementProbability right
          (kernel.childProbability left right)) / 2)

theorem empiricalChildMarginal_mem_Icc
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel) :
    0 ≤ empiricalChildMarginal parentCount oneCount kernel ∧
      empiricalChildMarginal parentCount oneCount kernel ≤ 1 := by
  constructor
  · exact withoutReplacementBinaryPairExpectation_nonneg
      parentCount oneCount hparents hones kernel.childProbability
      kernel.childProbability_nonneg
  · exact withoutReplacementBinaryPairExpectation_le_one
      parentCount oneCount hparents hones kernel.childProbability
      kernel.childProbability_le_one

theorem empiricalChildMarginal_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalChildMarginal parentCount oneCount kernel -
      kernel.childMarginal| ≤ 1 / (parentCount : ℝ) := by
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones
    kernel.childProbability
    (fun left right =>
      ⟨kernel.childProbability_nonneg left right,
        kernel.childProbability_le_one left right⟩)
  rw [← hparameter] at herror
  simpa [empiricalChildMarginal, BinaryPairKernel.childMarginal] using herror

theorem empiricalConditionalEntropy_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalConditionalEntropy parentCount oneCount kernel -
      kernel.conditionalEntropy| ≤ 1 / (parentCount : ℝ) := by
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones
    (fun left right => binaryEntropy (kernel.childProbability left right))
    (fun left right =>
      ⟨binaryEntropy_nonneg
        (kernel.childProbability_nonneg left right)
        (kernel.childProbability_le_one left right),
        binaryEntropy_le_one (kernel.childProbability left right)⟩)
  rw [← hparameter] at herror
  simpa [empiricalConditionalEntropy,
    BinaryPairKernel.conditionalEntropy] using herror

theorem empiricalAverageDisagreement_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalAverageDisagreement parentCount oneCount kernel -
      kernel.averageDisagreement| ≤ 1 / (parentCount : ℝ) := by
  let observable : Bool → Bool → ℝ := fun left right =>
    (BinaryPairKernel.bitDisagreementProbability left
        (kernel.childProbability left right) +
      BinaryPairKernel.bitDisagreementProbability right
        (kernel.childProbability left right)) / 2
  have hobservable (left right : Bool) :
      0 ≤ observable left right ∧ observable left right ≤ 1 := by
    have hleft := BinaryPairKernel.bitDisagreementProbability_mem_Icc left
      (kernel.childProbability left right)
      (kernel.childProbability_nonneg left right)
      (kernel.childProbability_le_one left right)
    have hright := BinaryPairKernel.bitDisagreementProbability_mem_Icc right
      (kernel.childProbability left right)
      (kernel.childProbability_nonneg left right)
      (kernel.childProbability_le_one left right)
    dsimp [observable]
    constructor <;> linarith
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones observable hobservable
  rw [← hparameter] at herror
  simpa [empiricalAverageDisagreement,
    BinaryPairKernel.averageDisagreement, observable] using herror

noncomputable def binomialProbabilityMass
    (trialCount successCount : ℕ) (probability : ℝ) : ℝ :=
  (trialCount.choose successCount : ℝ) *
    probability ^ successCount *
    (1 - probability) ^ (trialCount - successCount)

theorem binomialProbabilityMass_nonneg
    (trialCount successCount : ℕ) (probability : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    0 ≤ binomialProbabilityMass trialCount successCount probability := by
  unfold binomialProbabilityMass
  have hcomplement : 0 ≤ 1 - probability := by linarith
  positivity

theorem binomialProbabilityMass_succ_mul
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1) probability *
        ((successCount + 1 : ℕ) : ℝ) * (1 - probability) =
      binomialProbabilityMass trialCount successCount probability *
        ((trialCount - successCount : ℕ) : ℝ) * probability := by
  have hc :
      ((trialCount.choose (successCount + 1) : ℕ) : ℝ) *
          ((successCount + 1 : ℕ) : ℝ) =
        ((trialCount.choose successCount : ℕ) : ℝ) *
          ((trialCount - successCount : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq trialCount successCount
  have hs : trialCount - successCount =
      (trialCount - (successCount + 1)) + 1 := by omega
  unfold binomialProbabilityMass
  rw [hs] at hc ⊢
  simp only [pow_succ]
  linear_combination
    (probability ^ successCount *
      (1 - probability) ^ (trialCount - (successCount + 1)) *
      probability * (1 - probability)) * hc

theorem binomialModeRatio_le_of_lt
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hcount : successCount < mode) :
    ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) ≤
      ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub hmode,
    Nat.cast_sub (show successCount ≤ trialCount by omega),
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (mode : ℝ) - (successCount : ℝ) - 1 := by
    have hcast : (successCount : ℝ) + 1 ≤ (mode : ℝ) := by
      exact_mod_cast (show successCount + 1 ≤ mode by omega)
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_nonneg : 0 ≤ (mode : ℝ) := Nat.cast_nonneg mode
  nlinarith

theorem binomialModeRatio_le_of_ge
    (trialCount mode successCount : ℕ)
    (htrials : 0 < trialCount)
    (hmode : mode ≤ trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub (Nat.le_of_lt hsuccess),
    Nat.cast_sub hmode,
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (successCount : ℝ) - (mode : ℝ) := by
    have hcast : (mode : ℝ) ≤ (successCount : ℝ) := by
      exact_mod_cast hcount
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_le : (mode : ℝ) ≤ (trialCount : ℝ) := by
    exact_mod_cast hmode
  nlinarith

theorem binomialProbabilityMass_le_succ_of_lt_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode < trialCount)
    (hcount : successCount < mode) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hprobability_zero :
      0 ≤ (mode : ℝ) / (trialCount : ℝ) := by positivity
  have hprobability_one :
      (mode : ℝ) / (trialCount : ℝ) < 1 := by
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode
  have hscale :
      0 < ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
    positivity
  have hmass := binomialProbabilityMass_nonneg
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    hprobability_zero hprobability_one.le
  have hratio := binomialModeRatio_le_of_lt
    trialCount mode successCount hmode.le hcount
  have hidentity := binomialProbabilityMass_succ_mul
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    (show successCount < trialCount by omega)
  apply le_of_mul_le_mul_right (a :=
    ((successCount + 1 : ℕ) : ℝ) *
      (1 - (mode : ℝ) / (trialCount : ℝ)))
    (a0 := hscale)
  calc
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) ≤
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio hmass
    _ = binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) := by
          nlinarith [hidentity]

theorem binomialProbabilityMass_succ_le_of_ge_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode < trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hprobability_zero :
      0 ≤ (mode : ℝ) / (trialCount : ℝ) := by positivity
  have hprobability_one :
      (mode : ℝ) / (trialCount : ℝ) < 1 := by
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode
  have hscale :
      0 < ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
    positivity
  have hmass := binomialProbabilityMass_nonneg
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    hprobability_zero hprobability_one.le
  have hratio := binomialModeRatio_le_of_ge
    trialCount mode successCount htrials hmode.le hcount hsuccess
  have hidentity := binomialProbabilityMass_succ_mul
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ)) hsuccess
  apply le_of_mul_le_mul_right (a :=
    ((successCount + 1 : ℕ) : ℝ) *
      (1 - (mode : ℝ) / (trialCount : ℝ)))
    (a0 := hscale)
  calc
    binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) =
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ))) := by
          nlinarith [hidentity]
    _ ≤ binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) :=
          mul_le_mul_of_nonneg_left hratio hmass

theorem binomialProbabilityMass_le_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hsuccess : successCount ≤ trialCount) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by
  by_cases htrials : trialCount = 0
  · subst trialCount
    have hmode_zero : mode = 0 := by omega
    have hsuccess_zero : successCount = 0 := by omega
    subst mode
    subst successCount
    exact le_rfl
  by_cases hmode_zero : mode = 0
  · subst mode
    by_cases hsuccess_zero : successCount = 0
    · subst successCount
      exact le_rfl
    · simp [binomialProbabilityMass, hsuccess_zero]
  by_cases hmode_full : mode = trialCount
  · subst mode
    have htrials_real : (trialCount : ℝ) ≠ 0 := by
      exact_mod_cast htrials
    rw [div_self htrials_real]
    by_cases hsuccess_full : successCount = trialCount
    · subst successCount
      exact le_rfl
    · have hpositive : 0 < trialCount - successCount := by omega
      simp [binomialProbabilityMass, hpositive.ne']
  have hmode_lt : mode < trialCount := by omega
  let probability : ℝ := (mode : ℝ) / (trialCount : ℝ)
  have hstep_up (index : ℕ) (hindex : index < mode) :
      binomialProbabilityMass trialCount index probability ≤
        binomialProbabilityMass trialCount (index + 1) probability := by
    exact binomialProbabilityMass_le_succ_of_lt_mode
      trialCount mode index hmode_lt hindex
  have hstep_down (index : ℕ)
      (hindex_mode : mode ≤ index)
      (hindex_trials : index < trialCount) :
      binomialProbabilityMass trialCount (index + 1) probability ≤
        binomialProbabilityMass trialCount index probability := by
    exact binomialProbabilityMass_succ_le_of_ge_mode
      trialCount mode index hmode_lt hindex_mode hindex_trials
  by_cases hbelow : successCount ≤ mode
  · have hwalk (index : ℕ) (hindex : successCount ≤ index) :
        index ≤ mode →
          binomialProbabilityMass trialCount successCount probability ≤
            binomialProbabilityMass trialCount index probability := by
      induction index, hindex using Nat.le_induction with
      | base =>
        intro _
        exact le_rfl
      | succ index hindex hinduction =>
        intro hupper
        exact (hinduction (by omega)).trans
          (hstep_up index (by omega))
    exact hwalk mode hbelow (le_refl mode)
  · have habove : mode ≤ successCount := by omega
    have hwalk (index : ℕ) (hindex : mode ≤ index) :
        index ≤ trialCount →
          binomialProbabilityMass trialCount index probability ≤
            binomialProbabilityMass trialCount mode probability := by
      induction index, hindex using Nat.le_induction with
      | base =>
        intro _
        exact le_rfl
      | succ index hindex hinduction =>
        intro hupper
        exact (hstep_down index hindex (by omega)).trans
          (hinduction (by omega))
    exact hwalk successCount habove hsuccess

theorem binomialProbabilityMass_sum_eq_one
    (trialCount : ℕ) (probability : ℝ) :
    (∑ successCount ∈ Finset.range (trialCount + 1),
      binomialProbabilityMass trialCount successCount probability) = 1 := by
  unfold binomialProbabilityMass
  calc
    (∑ successCount ∈ Finset.range (trialCount + 1),
      (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount)) =
      ∑ successCount ∈ Finset.range (trialCount + 1),
        probability ^ successCount *
          (1 - probability) ^ (trialCount - successCount) *
          (trialCount.choose successCount : ℝ) := by
            apply Finset.sum_congr rfl
            intro successCount _
            ring
    _ = (probability + (1 - probability)) ^ trialCount :=
      (add_pow probability (1 - probability) trialCount).symm
    _ = 1 := by
      rw [show probability + (1 - probability) = 1 by ring]
      simp

theorem binomialProbabilityMass_mode_ge_inverse
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    1 / ((trialCount + 1 : ℕ) : ℝ) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have hdenominator : 0 < ((trialCount + 1 : ℕ) : ℝ) := by
    positivity
  apply (div_le_iff₀ hdenominator).mpr
  calc
    (1 : ℝ) =
      ∑ successCount ∈ Finset.range (trialCount + 1),
        binomialProbabilityMass trialCount successCount
          ((mode : ℝ) / (trialCount : ℝ)) :=
      (binomialProbabilityMass_sum_eq_one
        trialCount ((mode : ℝ) / (trialCount : ℝ))).symm
    _ ≤ ∑ _successCount ∈ Finset.range (trialCount + 1),
        binomialProbabilityMass trialCount mode
          ((mode : ℝ) / (trialCount : ℝ)) := by
      apply Finset.sum_le_sum
      intro successCount hsuccess
      apply binomialProbabilityMass_le_mode
        trialCount mode successCount hmode
      have hbound := Finset.mem_range.mp hsuccess
      omega
    _ = binomialProbabilityMass trialCount mode
          ((mode : ℝ) / (trialCount : ℝ)) *
        ((trialCount + 1 : ℕ) : ℝ) := by
      simp [nsmul_eq_mul]
      ring

theorem binomialProbabilityMass_mode_mul_exp_entropy
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) *
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((mode : ℝ) / (trialCount : ℝ))) =
      (trialCount.choose mode : ℝ) := by
  by_cases hzero : mode = 0
  · subst mode
    simp [binomialProbabilityMass]
  by_cases hfull : mode = trialCount
  · subst mode
    have htrials : (trialCount : ℝ) ≠ 0 := by
      exact_mod_cast hzero
    simp [binomialProbabilityMass, htrials]
  have hmode_pos : 0 < mode := Nat.pos_of_ne_zero hzero
  have hmode_lt : mode < trialCount :=
    lt_of_le_of_ne hmode hfull
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  let probability : ℝ := (mode : ℝ) / (trialCount : ℝ)
  have hprobability : 0 < probability := by
    dsimp [probability]
    positivity
  have hprobability_one : probability < 1 := by
    dsimp [probability]
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode_lt
  have hcomplement : 0 < 1 - probability := by
    linarith
  have hproduct :
      0 < probability ^ mode *
        (1 - probability) ^ (trialCount - mode) := by
    positivity
  have hentropy :
      (trialCount : ℝ) * Real.binEntropy probability =
        -(mode : ℝ) * Real.log probability -
          ((trialCount - mode : ℕ) : ℝ) *
            Real.log (1 - probability) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv, Nat.cast_sub hmode]
    dsimp [probability]
    field_simp [htrials_real.ne']
    ring
  have hlog :
      Real.log
        (probability ^ mode *
          (1 - probability) ^ (trialCount - mode)) +
        (trialCount : ℝ) * Real.binEntropy probability = 0 := by
    rw [Real.log_mul
      (pow_pos hprobability mode).ne'
      (pow_pos hcomplement (trialCount - mode)).ne',
      Real.log_pow, Real.log_pow, hentropy]
    ring
  change
    binomialProbabilityMass trialCount mode probability *
      Real.exp ((trialCount : ℝ) * Real.binEntropy probability) =
      (trialCount.choose mode : ℝ)
  calc
    binomialProbabilityMass trialCount mode probability *
        Real.exp ((trialCount : ℝ) * Real.binEntropy probability) =
      (trialCount.choose mode : ℝ) *
        (probability ^ mode *
          (1 - probability) ^ (trialCount - mode) *
          Real.exp ((trialCount : ℝ) * Real.binEntropy probability)) := by
        unfold binomialProbabilityMass
        ring
    _ = (trialCount.choose mode : ℝ) *
        Real.exp
          (Real.log
              (probability ^ mode *
                (1 - probability) ^ (trialCount - mode)) +
            (trialCount : ℝ) * Real.binEntropy probability) := by
          rw [Real.exp_add, Real.exp_log hproduct]
    _ = (trialCount.choose mode : ℝ) := by
      rw [hlog]
      simp

theorem exp_binary_entropy_div_le_choose
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) ≤
      (trialCount.choose successCount : ℝ) := by
  have hmode := binomialProbabilityMass_mode_ge_inverse
    trialCount successCount hcount
  have hexponential :
      0 ≤ Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) :=
    (Real.exp_pos _).le
  calc
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) =
      (1 / ((trialCount + 1 : ℕ) : ℝ)) *
        Real.exp
          ((trialCount : ℝ) *
            Real.binEntropy
              ((successCount : ℝ) / (trialCount : ℝ))) := by
        ring
    _ ≤ binomialProbabilityMass trialCount successCount
          ((successCount : ℝ) / (trialCount : ℝ)) *
        Real.exp
          ((trialCount : ℝ) *
            Real.binEntropy
              ((successCount : ℝ) / (trialCount : ℝ))) :=
      mul_le_mul_of_nonneg_right hmode hexponential
    _ = (trialCount.choose successCount : ℝ) :=
      binomialProbabilityMass_mode_mul_exp_entropy
        trialCount successCount hcount

theorem binomial_probability_term_le_one
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount ≤ trialCount)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) ≤ 1 := by
  have hcomplement : 0 ≤ 1 - probability :=
    sub_nonneg.mpr hprobability_one
  have hsum :
      (∑ count ∈ Finset.range (trialCount + 1),
        probability ^ count *
          (1 - probability) ^ (trialCount - count) *
          (trialCount.choose count : ℝ)) = 1 := by
    calc
      (∑ count ∈ Finset.range (trialCount + 1),
          probability ^ count *
            (1 - probability) ^ (trialCount - count) *
            (trialCount.choose count : ℝ)) =
          (probability + (1 - probability)) ^ trialCount :=
        (add_pow probability (1 - probability) trialCount).symm
      _ = 1 := by
        rw [show probability + (1 - probability) = 1 by ring]
        simp
  have hterm := Finset.single_le_sum
    (s := Finset.range (trialCount + 1))
    (f := fun count : ℕ =>
      probability ^ count *
        (1 - probability) ^ (trialCount - count) *
        (trialCount.choose count : ℝ))
    (fun count _ => by positivity)
    (show successCount ∈ Finset.range (trialCount + 1) by
      simp; omega)
  rw [hsum] at hterm
  nlinarith

theorem log_choose_le_binary_entropy
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.log (trialCount.choose successCount : ℝ) ≤
      (trialCount : ℝ) *
        Real.binEntropy ((successCount : ℝ) / (trialCount : ℝ)) := by
  by_cases hzero : successCount = 0
  · subst successCount
    simp
  by_cases hfull : successCount = trialCount
  · subst successCount
    by_cases htrials : trialCount = 0
    · simp [htrials]
    · have htrials_real : (trialCount : ℝ) ≠ 0 := by
        exact_mod_cast htrials
      simp [htrials_real]
  have hsuccess : 0 < successCount := Nat.pos_of_ne_zero hzero
  have hstrict : successCount < trialCount :=
    lt_of_le_of_ne hcount hfull
  have htrials : 0 < trialCount :=
    lt_of_lt_of_le hsuccess hcount
  let probability : ℝ :=
    (successCount : ℝ) / (trialCount : ℝ)
  have hprobability_pos : 0 < probability := by
    dsimp [probability]
    positivity
  have hprobability_lt_one : probability < 1 := by
    dsimp [probability]
    apply (div_lt_one (by exact_mod_cast htrials)).mpr
    exact_mod_cast hstrict
  have hcomplement : 0 < 1 - probability :=
    sub_pos.mpr hprobability_lt_one
  have hchoose : 0 < (trialCount.choose successCount : ℝ) := by
    exact_mod_cast Nat.choose_pos hcount
  have hmass := binomial_probability_term_le_one
    trialCount successCount probability hcount
    hprobability_pos.le hprobability_lt_one.le
  have hproduct :
      0 < (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) := by
    positivity
  have hlogmass := Real.log_le_log hproduct hmass
  simp only [Real.log_one] at hlogmass
  rw [Real.log_mul
      (mul_pos hchoose (pow_pos hprobability_pos _)).ne'
      (pow_pos hcomplement _).ne',
    Real.log_mul hchoose.ne' (pow_pos hprobability_pos _).ne',
    Real.log_pow, Real.log_pow] at hlogmass
  have htrials_real : (trialCount : ℝ) ≠ 0 := by
    exact_mod_cast htrials.ne'
  have hentropy :
      (trialCount : ℝ) * Real.binEntropy probability =
        -(successCount : ℝ) * Real.log probability -
          ((trialCount - successCount : ℕ) : ℝ) *
            Real.log (1 - probability) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv, Nat.cast_sub hcount]
    dsimp [probability]
    field_simp [htrials_real]
    ring
  change Real.log (trialCount.choose successCount : ℝ) ≤
    (trialCount : ℝ) * Real.binEntropy probability
  rw [hentropy]
  linarith

theorem choose_le_exp_binary_entropy
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    (trialCount.choose successCount : ℝ) ≤
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((successCount : ℝ) / (trialCount : ℝ))) := by
  have hchoose : 0 < (trialCount.choose successCount : ℝ) := by
    exact_mod_cast Nat.choose_pos hcount
  exact (Real.log_le_iff_le_exp hchoose).mp
    (log_choose_le_binary_entropy trialCount successCount hcount)

theorem choose_product_le_exp_binary_entropy
    {ι : Type*} [Fintype ι]
    (population success : ι → ℕ)
    (hcount : ∀ index, success index ≤ population index) :
    (∏ index : ι,
      (population index).choose (success index) : ℝ) ≤
      Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
  calc
    (∏ index : ι,
        (population index).choose (success index) : ℝ) ≤
      ∏ index : ι,
        Real.exp
          ((population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
        apply Finset.prod_le_prod
        · intro index _
          positivity
        · intro index _
          exact choose_le_exp_binary_entropy
            (population index) (success index) (hcount index)
    _ = Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
      rw [Real.exp_sum]

theorem certificate_ratio_one_lt :
    (1 : ℝ) < (97 + 56 * Real.sqrt 3) / 192 := by
  have h := twelve_sevenths_lt_sqrt_three
  nlinarith

theorem certifiedWindowWidth_pos : 0 < certifiedWindowWidth := by
  unfold certifiedWindowWidth logTwo
  exact div_pos
    (div_pos (Real.log_pos certificate_ratio_one_lt)
      log_two_pos)
    (by norm_num)

theorem tau_pos : 0 < tau := by
  unfold tau
  nlinarith [twelve_sevenths_lt_sqrt_three]

theorem tau_lt_one_half : tau < (1 : ℝ) / 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  unfold tau
  nlinarith

theorem sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := by
  positivity

theorem tau_complement : 1 - tau = Real.sqrt 3 * tau := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  unfold tau
  nlinarith

theorem tau_reciprocal_identity :
    1 + 1 / Real.sqrt 3 = (1 - tau)⁻¹ := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  rw [tau_complement]
  field_simp [sqrt_three_pos.ne', tau_pos.ne']
  unfold tau
  nlinarith

theorem log_three_eq_twice_log_sqrt_three :
    Real.log (3 : ℝ) = 2 * Real.log (Real.sqrt 3) := by
  have hsqrt_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    exact Real.sq_sqrt (by positivity)
  calc
    Real.log (3 : ℝ) = Real.log ((Real.sqrt 3) ^ 2) := by rw [hsqrt_sq]
    _ = 2 * Real.log (Real.sqrt 3) := by
      rw [Real.log_pow]
      ring

theorem entropy_tau_identity :
    2 * binaryEntropy tau - tau * logTwo 3 =
      2 * logTwo (1 + 1 / Real.sqrt 3) := by
  have hlog_complement :
      Real.log (1 - tau) = Real.log (Real.sqrt 3) + Real.log tau := by
    rw [tau_complement, Real.log_mul sqrt_three_pos.ne' tau_pos.ne']
  unfold binaryEntropy logTwo Real.binEntropy
  rw [Real.log_inv, Real.log_inv, tau_reciprocal_identity, Real.log_inv,
    hlog_complement, log_three_eq_twice_log_sqrt_three]
  ring

theorem certificate_ratio_identity :
    (1 + 1 / Real.sqrt 3) ^ (8 : ℕ) * 27 / 1024 =
      (97 + 56 * Real.sqrt 3) / 192 := by
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by positivity)
  have hz : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp [hz]
  ring_nf at hs ⊢
  linear_combination
    (-1728 - 13824 * Real.sqrt 3
      - 48960 * Real.sqrt 3 ^ 2
      - 101376 * Real.sqrt 3 ^ 3
      - 137280 * Real.sqrt 3 ^ 4
      - 130560 * Real.sqrt 3 ^ 5
      - 94144 * Real.sqrt 3 ^ 6
      - 57344 * Real.sqrt 3 ^ 7) * hs

theorem log_certificate_ratio_identity :
    Real.log ((97 + 56 * Real.sqrt 3) / 192) =
      8 * Real.log (1 + 1 / Real.sqrt 3) +
        3 * Real.log 3 - 10 * Real.log 2 := by
  have hu : 0 < (1 : ℝ) + 1 / Real.sqrt 3 := by
    positivity
  have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    calc
      Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ (3 : ℕ)) := by norm_num
      _ = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
  have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    calc
      Real.log (1024 : ℝ) = Real.log ((2 : ℝ) ^ (10 : ℕ)) := by norm_num
      _ = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [← certificate_ratio_identity,
    Real.log_div (by positivity) (by norm_num),
    Real.log_mul (by positivity) (by norm_num),
    Real.log_pow, hlog27, hlog1024]
  ring

noncomputable def entropyLowerEndpoint : ℝ := kappa + tau * logTwo 3

noncomputable def entropyUpperEndpoint : ℝ := 2 * binaryEntropy tau - 1

noncomputable def midpointBeta : ℝ :=
  (entropyLowerEndpoint + entropyUpperEndpoint) / 2

theorem entropyWindow_eq_certifiedWindowWidth :
    entropyUpperEndpoint - entropyLowerEndpoint = certifiedWindowWidth := by
  have hentropy := entropy_tau_identity
  have hlog := log_certificate_ratio_identity
  unfold logTwo at hentropy
  have hlog_argument :
      (Real.sqrt 3 + 1) / Real.sqrt 3 =
        1 + 1 / Real.sqrt 3 := by
    field_simp [sqrt_three_pos.ne']
  unfold entropyUpperEndpoint entropyLowerEndpoint kappa
    certifiedWindowWidth logTwo
  field_simp [log_two_pos.ne'] at hentropy ⊢
  rw [hlog_argument] at hentropy
  ring_nf at hentropy hlog ⊢
  linarith

theorem entropyWindow_pos : entropyLowerEndpoint < entropyUpperEndpoint := by
  have h := certifiedWindowWidth_pos
  rw [← entropyWindow_eq_certifiedWindowWidth] at h
  linarith

theorem midpointBeta_gt_lower
    (hwindow : entropyLowerEndpoint < entropyUpperEndpoint) :
    entropyLowerEndpoint < midpointBeta := by
  unfold midpointBeta
  linarith

theorem midpointBeta_lt_upper
    (hwindow : entropyLowerEndpoint < entropyUpperEndpoint) :
    midpointBeta < entropyUpperEndpoint := by
  unfold midpointBeta
  linarith

theorem midpointBeta_gt_lower_unconditional :
    entropyLowerEndpoint < midpointBeta :=
  midpointBeta_gt_lower entropyWindow_pos

theorem midpointBeta_lt_upper_unconditional :
    midpointBeta < entropyUpperEndpoint :=
  midpointBeta_lt_upper entropyWindow_pos

theorem logTwo_three_pos : 0 < logTwo 3 := by
  unfold logTwo
  exact div_pos (Real.log_pos (by norm_num)) log_two_pos

theorem logTwo_three_lt_two : logTwo 3 < 2 := by
  have hlog : Real.log (3 : ℝ) < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  unfold logTwo
  apply (div_lt_iff₀ log_two_pos).mpr
  nlinarith [hlog]

theorem kappa_pos : 0 < kappa := by
  unfold kappa
  nlinarith [logTwo_three_lt_two]

theorem entropyLowerEndpoint_pos : 0 < entropyLowerEndpoint := by
  unfold entropyLowerEndpoint
  positivity [kappa_pos, tau_pos, logTwo_three_pos]

theorem binaryEntropy_tau_lt_one : binaryEntropy tau < 1 := by
  have htau_ne : tau ≠ (2 : ℝ)⁻¹ := by
    intro heq
    have hlt := tau_lt_one_half
    rw [heq] at hlt
    norm_num at hlt
  unfold binaryEntropy
  apply (div_lt_iff₀ log_two_pos).mpr
  simpa using (Real.binEntropy_lt_log_two.mpr htau_ne)

theorem entropyUpperEndpoint_lt_one : entropyUpperEndpoint < 1 := by
  unfold entropyUpperEndpoint
  nlinarith [binaryEntropy_tau_lt_one]

theorem midpointBeta_pos : 0 < midpointBeta :=
  entropyLowerEndpoint_pos.trans midpointBeta_gt_lower_unconditional

theorem midpointBeta_lt_one : midpointBeta < 1 :=
  midpointBeta_lt_upper_unconditional.trans entropyUpperEndpoint_lt_one

noncomputable def entropySlack : ℝ := certifiedWindowWidth / 8

noncomputable def exponentGain : ℝ :=
  certifiedWindowWidth / (8 * (1 - midpointBeta))

theorem entropySlack_pos : 0 < entropySlack := by
  unfold entropySlack
  exact div_pos certifiedWindowWidth_pos (by norm_num)

theorem exponentGain_pos : 0 < exponentGain := by
  unfold exponentGain
  exact div_pos certifiedWindowWidth_pos
    (mul_pos (by norm_num) (sub_pos.mpr midpointBeta_lt_one))

noncomputable def empiricalEntropyError (layerSize : ℕ) : ℝ :=
  (1 + logTwo 3) / (layerSize : ℝ) +
    binaryEntropy (1 / (layerSize : ℝ)) / 2

theorem empiricalChildMarginal_entropy_error
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |binaryEntropy (empiricalChildMarginal parentCount oneCount kernel) -
      binaryEntropy kernel.childMarginal| ≤
        binaryEntropy (1 / (parentCount : ℝ)) := by
  have hparents_two : 2 ≤ parentCount := by omega
  have hempirical := empiricalChildMarginal_mem_Icc
    parentCount oneCount hparents_two hones kernel
  have hchild :
      0 ≤ kernel.childMarginal ∧ kernel.childMarginal ≤ 1 :=
    ⟨BinaryPairKernel.childMarginal_nonneg kernel,
      BinaryPairKernel.childMarginal_le_one kernel⟩
  have hcoupling := empiricalChildMarginal_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hmodulus := abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    (empiricalChildMarginal parentCount oneCount kernel)
    kernel.childMarginal hempirical.1 hempirical.2 hchild.1 hchild.2
  have hparents_real : (4 : ℝ) ≤ (parentCount : ℝ) := by
    exact_mod_cast hparents
  have hparents_pos : (0 : ℝ) < (parentCount : ℝ) := by
    linarith
  have hhalf : 1 / (parentCount : ℝ) ≤ (2 : ℝ)⁻¹ := by
    apply (div_le_iff₀ hparents_pos).mpr
    norm_num
    linarith
  have hmonotone := binaryEntropy_mono_on_half
    |empiricalChildMarginal parentCount oneCount kernel -
      kernel.childMarginal|
    (1 / (parentCount : ℝ))
    (abs_nonneg _) hcoupling hhalf
  exact hmodulus.trans hmonotone

theorem empiricalConditionalEntropy_bound
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    empiricalConditionalEntropy parentCount oneCount kernel ≤
      kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by
  have hparents_two : 2 ≤ parentCount := by omega
  have hconditional := empiricalConditionalEntropy_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hdisagreement := empiricalAverageDisagreement_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hmarginal := empiricalChildMarginal_entropy_error
    parentCount oneCount hparents hones kernel hparameter
  have hindependent := BinaryPairKernel.conditionalEntropy_bound kernel
  have hconditional_upper :
      empiricalConditionalEntropy parentCount oneCount kernel ≤
        kernel.conditionalEntropy + 1 / (parentCount : ℝ) := by
    have h := (abs_le.mp hconditional).2
    linarith
  have hdisagreement_upper :
      kernel.averageDisagreement ≤
        empiricalAverageDisagreement parentCount oneCount kernel +
          1 / (parentCount : ℝ) := by
    have h := (abs_le.mp hdisagreement).1
    linarith
  have hdisagreement_scaled := mul_le_mul_of_nonneg_left
    hdisagreement_upper logTwo_three_pos.le
  have hmarginal_upper :
      binaryEntropy kernel.childMarginal ≤
        binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) +
          binaryEntropy (1 / (parentCount : ℝ)) := by
    have h := (abs_le.mp hmarginal).1
    linarith
  have herror :
      1 / (parentCount : ℝ) +
          logTwo 3 * (1 / (parentCount : ℝ)) +
          binaryEntropy (1 / (parentCount : ℝ)) / 2 =
        empiricalEntropyError parentCount := by
    unfold empiricalEntropyError
    ring
  calc
    empiricalConditionalEntropy parentCount oneCount kernel ≤
        kernel.conditionalEntropy + 1 / (parentCount : ℝ) :=
      hconditional_upper
    _ ≤ kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        (1 / (parentCount : ℝ) +
          logTwo 3 * (1 / (parentCount : ℝ)) +
          binaryEntropy (1 / (parentCount : ℝ)) / 2) := by
      nlinarith
    _ = kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by
      rw [herror]

theorem empiricalEntropyError_tendsto_zero :
    Filter.Tendsto empiricalEntropyError Filter.atTop (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun L : ℕ => 1 / (L : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hfirst :
      Filter.Tendsto
        (fun L : ℕ => (1 + logTwo 3) / (L : ℝ))
        Filter.atTop (nhds 0) := by
    have hconst :
        Filter.Tendsto (fun _ : ℕ => 1 + logTwo 3)
          Filter.atTop (nhds (1 + logTwo 3)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using hconst.mul hinv
  have hentropy :
      Filter.Tendsto
        (fun L : ℕ => binaryEntropy (1 / (L : ℝ)))
        Filter.atTop (nhds 0) := by
    have hcontinuous := binaryEntropy_continuous.continuousAt.tendsto.comp hinv
    rw [binaryEntropy_zero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with L
    rfl
  change Filter.Tendsto
    (fun L : ℕ => (1 + logTwo 3) / (L : ℝ) +
      binaryEntropy (1 / (L : ℝ)) / 2)
    Filter.atTop (nhds 0)
  simpa using hfirst.add (hentropy.div_const 2)

theorem logTwo_pairLayer_card_add_one_le (L : ℕ) (hL : 2 ≤ L) :
    logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
      2 * (L : ℝ) / Real.log 2 := by
  let x : ℝ := ((L.choose 2 + 1 : ℕ) : ℝ)
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hLreal : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hchoose : (L.choose 2 : ℝ) =
      (L : ℝ) * ((L : ℝ) - 1) / 2 := by
    exact Nat.cast_choose_two ℝ L
  have hxle : x ≤ (L : ℝ) ^ 2 := by
    dsimp [x]
    push_cast
    rw [hchoose]
    nlinarith [sq_nonneg ((L : ℝ) - 1)]
  have hsqrt : Real.sqrt x ≤ (L : ℝ) := by
    have hsq := Real.sq_sqrt hxpos.le
    have hsqrt_nonneg := Real.sqrt_nonneg x
    nlinarith
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have hbound := Real.log_le_rpow_div hxpos.le
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hbound
    norm_num at hbound
    linarith
  change Real.log x / Real.log 2 ≤ 2 * (L : ℝ) / Real.log 2
  apply (div_le_div_iff_of_pos_right log_two_pos).mpr
  linarith

theorem exists_empiricalEntropyError_base :
    ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → empiricalEntropyError L < entropySlack := by
  have heventually :
      ∀ᶠ L : ℕ in Filter.atTop,
        empiricalEntropyError L < entropySlack :=
    (tendsto_order.1 empiricalEntropyError_tendsto_zero).2
      entropySlack entropySlack_pos
  obtain ⟨L₀, hL₀⟩ := (Filter.eventually_atTop.1 heventually)
  refine ⟨max 4 L₀, le_max_left _ _, ?_⟩
  intro L hL
  exact hL₀ L ((le_max_right 4 L₀).trans hL)

theorem exists_entropy_exclusion_base :
    ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
        empiricalEntropyError L < entropySlack ∧
        (L : ℝ) +
            3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (L.choose 2 : ℝ) < -1 := by
  obtain ⟨Lerror, _, herror⟩ := exists_empiricalEntropyError_base
  let C : ℝ := 1 + 6 / Real.log 2
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (4 * (C + entropySlack + 1) / entropySlack)
  refine ⟨max 4 (max Lerror N), le_max_left _ _, ?_⟩
  intro L hL
  have hrest : max Lerror N ≤ L :=
    (le_max_right 4 (max Lerror N)).trans hL
  have herrorL : Lerror ≤ L := (le_max_left Lerror N).trans hrest
  have hNL : N ≤ L := (le_max_right Lerror N).trans hrest
  refine ⟨herror L herrorL, ?_⟩
  have hLfour : 4 ≤ L :=
    (le_max_left 4 (max Lerror N)).trans hL
  have hLreal : (4 : ℝ) ≤ L := by exact_mod_cast hLfour
  have hLpos : 0 < (L : ℝ) := by linarith
  have hNreal : (N : ℝ) ≤ L := by exact_mod_cast hNL
  have hthreshold :
      4 * (C + entropySlack + 1) / entropySlack < (L : ℝ) :=
    hN.trans_le hNreal
  have hbig :
      4 * (C + entropySlack + 1) < entropySlack * (L : ℝ) := by
    have h := (div_lt_iff₀ entropySlack_pos).mp hthreshold
    nlinarith
  have hscaled := mul_lt_mul_of_pos_right hbig hLpos
  have hlog := logTwo_pairLayer_card_add_one_le L (by omega)
  have hlinear :
      (L : ℝ) + 3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
        C * (L : ℝ) := by
    calc
      (L : ℝ) + 3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
          (L : ℝ) + 3 * (2 * (L : ℝ) / Real.log 2) := by
            gcongr
      _ = C * (L : ℝ) := by
        dsimp [C]
        ring
  have hchoose : (L.choose 2 : ℝ) =
      (L : ℝ) * ((L : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ L
  rw [hchoose]
  nlinarith [mul_pos entropySlack_pos hLpos]

theorem exists_entropy_exclusion_depth :
    ∃ depth : ℕ, 0 < depth ∧
      1 < (depth : ℝ) * (certifiedWindowWidth / 2) := by
  obtain ⟨depth, hdepth⟩ :=
    exists_nat_gt ((2 : ℝ) / certifiedWindowWidth)
  have hwidth := certifiedWindowWidth_pos
  have hdepth_real : 0 < (depth : ℝ) :=
    (div_pos (by norm_num) hwidth).trans hdepth
  have hdepth_nat : 0 < depth := by exact_mod_cast hdepth_real
  refine ⟨depth, hdepth_nat, ?_⟩
  have hproduct := (div_lt_iff₀ hwidth).mp hdepth
  nlinarith

theorem entropy_potential_increment
    (potentialBefore potentialAfter conditionalEntropy error : ℝ)
    (herror : error < entropySlack)
    (hlower : midpointBeta - entropySlack < conditionalEntropy)
    (hupper : conditionalEntropy ≤
      entropyLowerEndpoint +
        (potentialAfter - potentialBefore) / 2 + error) :
    certifiedWindowWidth / 2 < potentialAfter - potentialBefore := by
  have hwindow := entropyWindow_eq_certifiedWindowWidth
  unfold midpointBeta entropySlack at hlower
  unfold entropySlack at herror
  linarith

theorem entropy_potential_layers_impossible
    (depth : ℕ) (potential : ℕ → ℝ)
    (hrange : ∀ i ≤ depth, 0 ≤ potential i ∧ potential i ≤ 1)
    (hincrement : ∀ i < depth,
      certifiedWindowWidth / 2 < potential (i + 1) - potential i)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2)) : False := by
  have htotal :
      ∀ i ≤ depth,
        (i : ℝ) * (certifiedWindowWidth / 2) ≤
          potential i - potential 0 := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hiprev : i ≤ depth := by omega
        have histep : i < depth := by omega
        have hprevious := ih hiprev
        have hnext := (hincrement i histep).le
        push_cast
        linarith
  have hstart := (hrange 0 (by omega)).1
  have hfinish := (hrange depth le_rfl).2
  have hsum := htotal depth le_rfl
  linarith

theorem entropy_layer_exclusion
    (depth : ℕ) (potential conditionalEntropy error : ℕ → ℝ)
    (hrange : ∀ i ≤ depth, 0 ≤ potential i ∧ potential i ≤ 1)
    (herror : ∀ i < depth, error i < entropySlack)
    (hlower : ∀ i < depth,
      midpointBeta - entropySlack < conditionalEntropy i)
    (hupper : ∀ i < depth,
      conditionalEntropy i ≤
        entropyLowerEndpoint +
          (potential (i + 1) - potential i) / 2 + error i)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2)) : False := by
  apply entropy_potential_layers_impossible depth potential hrange
    (hdepth := hdepth)
  intro i hi
  exact entropy_potential_increment (potential i) (potential (i + 1))
    (conditionalEntropy i) (error i)
    (herror i hi) (hlower i hi) (hupper i hi)

end BinaryEntropy

end Erdos146

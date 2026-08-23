/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZConditionalProduct
import ErdosProblems.Erdos1166.Erdos1166HLOZNegBinCompare
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# HLOZ Lemma 4.11: event-level adjacent-band recursion

This file formalizes the finite conditional-product and adjacent-urn step behind
Hao--Li--Okada--Zheng equations (4.45)--(4.48).  Conditioning on finite block
history preserves a product law; negative-binomial masses in adjacent bands are
uniformly comparable; and the resulting binomial imbalance has an explicit
exponential tail.  A final union bound incorporates a supplied Theta-bad
estimate into the one-step recursion.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory unitInterval

namespace Erdos1166.HLOZLemma411Recursion

/-- The finite-history conditioning step used before exposing the adjacent
urn variables: conditioning a finite product law by coordinatewise history
events leaves a product of coordinatewise filtered laws. -/
theorem history_conditioned_blocks_remain_product
    {β : Type*} [Fintype β] {X : β → Type*}
    (μ : PMF (∀ b, X b)) (μb : ∀ b, PMF (X b))
    (hprod : ∀ x, μ x = ∏ b, μb b (x b))
    (E : ∀ b, Finset (X b))
    (hE : ∀ b, ∃ y ∈ (E b : Set (X b)), y ∈ (μb b).support)
    (x : ∀ b, X b) :
    (μ.filter (Erdos1166.HLOZConditionalProduct.blockEvent E)
      (Erdos1166.HLOZConditionalProduct.blockEvent_meets_support
        μ μb hprod E hE)) x =
      ∏ b, ((μb b).filter (E b : Set (X b)) (hE b)) (x b) := by
  exact Erdos1166.HLOZConditionalProduct.filter_blockEvent_apply_eq_prod
    μ μb hprod E hE x

noncomputable def imbalanceCountSet (h : ℕ) (C : ℝ) : Finset ℕ :=
  (Finset.range (h + 1)).filter fun u ↦ 2 * C * (h - u) < u

lemma exp_le_one_add_add_sq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hb := Real.exp_bound (x := x) (n := 2) hx (by norm_num)
  norm_num [Finset.sum_range_succ] at hb
  have hdiff := (le_abs_self (Real.exp x - (1 + x))).trans hb
  nlinarith [sq_nonneg x]

noncomputable def imbalanceTilt (C : ℝ) : ℝ :=
  1 / (8 * C * (C + 1))

noncomputable def imbalanceRate (C : ℝ) : ℝ :=
  1 / (16 * (C + 1) ^ 2)

lemma imbalanceRate_pos {C : ℝ} (hC : 1 ≤ C) : 0 < imbalanceRate C := by
  unfold imbalanceRate
  positivity

lemma binomial_imbalance_base_le_exp
    (p : unitInterval) {C : ℝ} (hC : 1 ≤ C)
    (hp : (p : ℝ) ≤ C / (C + 1)) :
    (p : ℝ) * Real.exp (imbalanceTilt C) +
        (1 - (p : ℝ)) * Real.exp (-2 * C * imbalanceTilt C) ≤
      Real.exp (-imbalanceRate C) := by
  let t := imbalanceTilt C
  let d := imbalanceRate C
  have hC0 : 0 ≤ C := hC.trans' zero_le_one
  have hp0 : 0 ≤ (p : ℝ) := p.property.1
  have hp1 : (p : ℝ) ≤ 1 := p.property.2
  have ht0 : 0 ≤ t := by dsimp [t, imbalanceTilt]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t, imbalanceTilt]
    apply (div_le_one (by positivity : (0 : ℝ) < 8 * C * (C + 1))).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (show 0 ≤ C + 9 by positivity)]
  have htwoCt0 : 0 ≤ 2 * C * t := mul_nonneg (mul_nonneg (by positivity) hC0) ht0
  have htwoCt1 : 2 * C * t ≤ 1 := by
    dsimp [t, imbalanceTilt]
    field_simp
    nlinarith
  have hexpUp := exp_le_one_add_add_sq_of_abs_le_one (show |t| ≤ 1 by
    rw [abs_of_nonneg ht0]
    exact ht1)
  have hexpLow := exp_le_one_add_add_sq_of_abs_le_one
    (show |-2 * C * t| ≤ 1 by
      rw [abs_of_nonpos (by nlinarith [mul_nonneg hC0 ht0] : -2 * C * t ≤ 0)]
      nlinarith)
  have hmean : (1 + 2 * C) * (p : ℝ) - 2 * C ≤ -C / (C + 1) := by
    have hp' := (le_div_iff₀ (by positivity : 0 < C + 1)).mp hp
    apply (le_div_iff₀ (by positivity : 0 < C + 1)).2
    nlinarith
  have hsecond : (p : ℝ) + 4 * C ^ 2 * (1 - (p : ℝ)) ≤ 4 * C ^ 2 := by
    have hfour : 1 ≤ 4 * C ^ 2 := by nlinarith [sq_nonneg (C - 1)]
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hfour)]
  have hraw :
      (p : ℝ) * Real.exp t + (1 - (p : ℝ)) * Real.exp (-2 * C * t) ≤
        1 - t * C / (C + 1) + t ^ 2 * (4 * C ^ 2) := by
    calc
      (p : ℝ) * Real.exp t + (1 - (p : ℝ)) * Real.exp (-2 * C * t) ≤
          (p : ℝ) * (1 + t + t ^ 2) +
            (1 - (p : ℝ)) * (1 + (-2 * C * t) + (-2 * C * t) ^ 2) := by
        gcongr
      _ = 1 + t * ((1 + 2 * C) * (p : ℝ) - 2 * C) +
          t ^ 2 * ((p : ℝ) + 4 * C ^ 2 * (1 - (p : ℝ))) := by ring
      _ ≤ 1 + t * (-C / (C + 1)) + t ^ 2 * (4 * C ^ 2) := by
        gcongr
      _ = 1 - t * C / (C + 1) + t ^ 2 * (4 * C ^ 2) := by ring
  have heq : 1 - t * C / (C + 1) + t ^ 2 * (4 * C ^ 2) = 1 - d := by
    dsimp [t, d, imbalanceTilt, imbalanceRate]
    field_simp
    ring
  calc
    (p : ℝ) * Real.exp (imbalanceTilt C) +
        (1 - (p : ℝ)) * Real.exp (-2 * C * imbalanceTilt C) =
      (p : ℝ) * Real.exp t + (1 - (p : ℝ)) * Real.exp (-2 * C * t) := rfl
    _ ≤ 1 - d := hraw.trans_eq heq
    _ ≤ Real.exp (-d) := by
      simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-d)
    _ = Real.exp (-imbalanceRate C) := rfl

lemma binomial_imbalance_mgf (h : ℕ) (p : unitInterval) (C t : ℝ) :
    ∑ u ∈ Finset.range (h + 1),
        Bin(h, p).real {u} *
          Real.exp (t * ((u : ℝ) - 2 * C * (h - u))) =
      ((p : ℝ) * Real.exp t +
        (1 - (p : ℝ)) * Real.exp (-2 * C * t)) ^ h := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro u hu
  rw [binomial_real_singleton]
  have hu_le : u ≤ h := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
  rw [show t * ((u : ℝ) - 2 * C * ((h : ℝ) - (u : ℝ))) =
      t * (u : ℝ) + (-2 * C * t) * ((h : ℝ) - (u : ℝ)) by ring,
    Real.exp_add]
  rw [mul_comm t (u : ℝ), Real.exp_nat_mul]
  rw [show (-2 * C * t) * ((h : ℝ) - (u : ℝ)) =
      ((h - u : ℕ) : ℝ) * (-2 * C * t) by
        rw [Nat.cast_sub hu_le]
        ring,
    Real.exp_nat_mul]
  rw [mul_pow, mul_pow]
  ring

lemma binomial_imbalance_tail_le
    (h : ℕ) (p : unitInterval) {C : ℝ} (hC : 1 ≤ C)
    (hp : (p : ℝ) ≤ C / (C + 1)) :
    ∑ u ∈ imbalanceCountSet h C, Bin(h, p).real {u} ≤
      Real.exp (-imbalanceRate C * h) := by
  let t := imbalanceTilt C
  have ht0 : 0 ≤ t := by dsimp [t, imbalanceTilt]; positivity
  calc
    ∑ u ∈ imbalanceCountSet h C, Bin(h, p).real {u} ≤
        ∑ u ∈ imbalanceCountSet h C,
          Bin(h, p).real {u} * Real.exp
            (t * ((u : ℝ) - 2 * C * (h - u))) := by
      apply Finset.sum_le_sum
      intro u hu
      have hubad : 2 * C * (h - u) < (u : ℝ) := by
        simpa [imbalanceCountSet] using (Finset.mem_filter.mp hu).2
      have hexp : 1 ≤ Real.exp (t * ((u : ℝ) - 2 * C * (h - u))) := by
        exact Real.one_le_exp (mul_nonneg ht0 (by linarith))
      calc
        Bin(h, p).real {u} = Bin(h, p).real {u} * 1 := (mul_one _).symm
        _ ≤ Bin(h, p).real {u} *
            Real.exp (t * ((u : ℝ) - 2 * C * (h - u))) :=
          mul_le_mul_of_nonneg_left hexp measureReal_nonneg
    _ ≤ ∑ u ∈ Finset.range (h + 1),
          Bin(h, p).real {u} * Real.exp
            (t * ((u : ℝ) - 2 * C * (h - u))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro u hu hnot
      positivity
    _ = ((p : ℝ) * Real.exp t +
        (1 - (p : ℝ)) * Real.exp (-2 * C * t)) ^ h :=
      binomial_imbalance_mgf h p C t
    _ ≤ (Real.exp (-imbalanceRate C)) ^ h := by
      have hbase0 : 0 ≤ (p : ℝ) * Real.exp t +
          (1 - (p : ℝ)) * Real.exp (-2 * C * t) :=
        add_nonneg
          (mul_nonneg p.property.1 (Real.exp_pos _).le)
          (mul_nonneg (sub_nonneg.mpr p.property.2) (Real.exp_pos _).le)
      exact pow_le_pow_left₀ hbase0
        (binomial_imbalance_base_le_exp p hC hp) h
    _ = Real.exp (-imbalanceRate C * h) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The pointwise comparison from `HLOZNegBinCompare` sums to the mass
comparison required for two equally sized adjacent urn bands. -/
theorem negBinMass_upper_sum_le_exp_one_mul_lower_sum
    (i w : ℕ) (upper lower : Finset ℕ)
    (hi : 1 ≤ i) (hw : 1 ≤ w)
    (hscale : 64 * w * (w + 1) ≤ i)
    (hcard : upper.card = lower.card) (hlower : lower.Nonempty)
    (horder : ∀ u ∈ upper, ∀ v ∈ lower, v ≤ u)
    (hdist : ∀ u ∈ upper, ∀ v ∈ lower, u - v ≤ 2 * w)
    (hupperBand : ∀ u ∈ upper, Erdos1166.HLOZUrn.InNegBinMeanBand i w u)
    (hlowerBand : ∀ v ∈ lower, Erdos1166.HLOZUrn.InNegBinMeanBand i w v) :
    ∑ u ∈ upper, Erdos1166.HLOZUrn.negBinMass i u ≤
      Real.exp 1 * ∑ v ∈ lower, Erdos1166.HLOZUrn.negBinMass i v := by
  have hcardPos : (0 : ℝ) < lower.card := by
    exact_mod_cast Finset.card_pos.mpr hlower
  apply le_of_mul_le_mul_left (a := (lower.card : ℝ)) _ hcardPos
  calc
    (lower.card : ℝ) * ∑ u ∈ upper, Erdos1166.HLOZUrn.negBinMass i u =
        ∑ u ∈ upper, ∑ v ∈ lower, Erdos1166.HLOZUrn.negBinMass i u := by
      simp [Finset.mul_sum]
    _ ≤ ∑ u ∈ upper, ∑ v ∈ lower,
          Real.exp 1 * Erdos1166.HLOZUrn.negBinMass i v := by
      gcongr with u hu v hv
      exact (Erdos1166.HLOZUrn.negBinMass_compare_exp_one_of_le
        i w v u hi hw hscale (horder u hu v hv) (hdist u hu v hv)
        (hlowerBand v hv) (hupperBand u hu)).1
    _ = Real.exp 1 * (upper.card : ℝ) *
          ∑ v ∈ lower, Erdos1166.HLOZUrn.negBinMass i v := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    _ = (lower.card : ℝ) *
          (Real.exp 1 * ∑ v ∈ lower, Erdos1166.HLOZUrn.negBinMass i v) := by
      rw [hcard]
      ring

lemma negBinMass_sum_nonneg (i : ℕ) (s : Finset ℕ) :
    0 ≤ ∑ j ∈ s, Erdos1166.HLOZUrn.negBinMass i j := by
  apply Finset.sum_nonneg
  intro j _hj
  exact Erdos1166.HLOZUrn.negBinMass_nonneg i j

section AdjacentBands

variable {β α : Type*} [DecidableEq α]

/-- A finite family of pairs of adjacent bands, with the source pointwise
mass comparison and equal band cardinalities recorded explicitly. -/
structure FiniteAdjacentBands (C : ℝ) where
  upper : β → Finset α
  lower : β → Finset α
  weight : β → α → ℝ
  disjoint : ∀ b, Disjoint (upper b) (lower b)
  same_card : ∀ b, (upper b).card = (lower b).card
  lower_nonempty : ∀ b, (lower b).Nonempty
  nonneg : ∀ b x, x ∈ upper b ∪ lower b → 0 ≤ weight b x
  comparable : ∀ b, ∀ u ∈ upper b, ∀ v ∈ lower b, weight b u ≤ C * weight b v

namespace FiniteAdjacentBands

noncomputable def upperMass {C : ℝ} (B : FiniteAdjacentBands (β := β) (α := α) C)
    (b : β) : ℝ :=
  ∑ u ∈ B.upper b, B.weight b u

noncomputable def lowerMass {C : ℝ} (B : FiniteAdjacentBands (β := β) (α := α) C)
    (b : β) : ℝ :=
  ∑ v ∈ B.lower b, B.weight b v

lemma upperMass_nonneg {C : ℝ} (B : FiniteAdjacentBands (β := β) (α := α) C)
    (b : β) : 0 ≤ B.upperMass b := by
  apply Finset.sum_nonneg
  intro u hu
  exact B.nonneg b u (by simp [hu])

lemma lowerMass_nonneg {C : ℝ} (B : FiniteAdjacentBands (β := β) (α := α) C)
    (b : β) : 0 ≤ B.lowerMass b := by
  apply Finset.sum_nonneg
  intro v hv
  exact B.nonneg b v (by simp [hv])

/-- Equal cardinalities turn pointwise adjacent-band comparability into
comparability of the two total masses. -/
lemma upperMass_le_mul_lowerMass {C : ℝ}
    (B : FiniteAdjacentBands (β := β) (α := α) C) (b : β) :
    B.upperMass b ≤ C * B.lowerMass b := by
  have hcardPos : (0 : ℝ) < (B.lower b).card := by
    exact_mod_cast Finset.card_pos.mpr (B.lower_nonempty b)
  apply le_of_mul_le_mul_left (a := ((B.lower b).card : ℝ)) _ hcardPos
  calc
    ((B.lower b).card : ℝ) * B.upperMass b =
        ∑ u ∈ B.upper b, ∑ v ∈ B.lower b, B.weight b u := by
      simp [upperMass, Finset.mul_sum]
    _ ≤ ∑ u ∈ B.upper b, ∑ v ∈ B.lower b, C * B.weight b v := by
      gcongr with u hu v hv
      exact B.comparable b u hu v hv
    _ = C * ((B.upper b).card : ℝ) * B.lowerMass b := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      simp only [lowerMass]
      ring
    _ = ((B.lower b).card : ℝ) * (C * B.lowerMass b) := by
      rw [B.same_card b]
      ring

end FiniteAdjacentBands

end AdjacentBands

/-- For fixed active labels, this is the event that the number assigned to
the upper band is more than `2 C` times the number assigned to the lower
band. -/
def urnImbalanceEvent (s : Finset ℕ) (C : ℝ) : Set (Set ℕ) :=
  {V | 2 * C * (s.card - ((↑s : Set ℕ) ∩ V).ncard) <
    ((↑s : Set ℕ) ∩ V).ncard}

/-- Conditional on a fixed `h`-label active set, the iid adjacent-urn law
has an exponentially small upper/lower imbalance probability.  The
binomial law is derived internally from `pairUrnCount_hasLaw_binomial`; it
is not an assumption of this theorem. -/
theorem finite_iid_urn_imbalance_real_le
    (n h : ℕ) (s : Finset ℕ) (hs : s ∈ (Finset.range n).powersetCard h)
    (p q C : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (hC : 1 ≤ C)
    (hpq : p ≤ C * q) :
    (setBer(Set.Iio n, Erdos1166.HLOZUrn.adjacentUrnParameter p q hp hq)).real
        (urnImbalanceEvent s C) ≤
      Real.exp (-imbalanceRate C * h) := by
  let θ := Erdos1166.HLOZUrn.adjacentUrnParameter p q hp hq
  let U : Set ℕ → ℕ := fun V => ((↑s : Set ℕ) ∩ V).ncard
  have hcard : s.card = h := (Finset.mem_powersetCard.mp hs).2
  have hUle : ∀ V, U V ≤ h := by
    intro V
    rw [← hcard, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (Set.inter_subset_left) s.finite_toSet
  have hevent : urnImbalanceEvent s C = {V | U V ∈ imbalanceCountSet h C} := by
    ext V
    simp only [urnImbalanceEvent, Set.mem_ofPred_eq, U]
    unfold imbalanceCountSet
    rw [Finset.mem_filter, Finset.mem_range, hcard, Nat.lt_succ_iff]
    exact (and_iff_right (hUle V)).symm
  have hLaw : HasLaw U Bin(h, θ) setBer(Set.Iio n, θ) := by
    exact Erdos1166.HLOZUrn.pairUrnCount_hasLaw_binomial n h s hs p q hp hq
  have hpθ : (θ : ℝ) ≤ C / (C + 1) := by
    exact Erdos1166.HLOZUrn.adjacentUrnParameter_le hp hq
      (zero_le_one.trans hC) hpq
  rw [hevent]
  calc
    (setBer(Set.Iio n, θ)).real {V | U V ∈ imbalanceCountSet h C} =
        Bin(h, θ).real {u | u ∈ imbalanceCountSet h C} :=
      hLaw.measureReal_eq MeasurableSet.of_discrete
    _ = Bin(h, θ).real (↑(imbalanceCountSet h C) : Set ℕ) := by rfl
    _ = ∑ u ∈ imbalanceCountSet h C, Bin(h, θ).real {u} := by
      exact (sum_measureReal_singleton (μ := Bin(h, θ)) (imbalanceCountSet h C)).symm
    _ ≤ Real.exp (-imbalanceRate C * h) :=
      binomial_imbalance_tail_le h θ hC hpθ

/-- Source-specialized adjacent-band estimate.  The hypotheses describe the
two negative-binomial bands geometrically; their total mass comparison is
proved above from `negBinMass_compare_exp_one_of_le`, and the conditional iid
urn law then gives the exponential imbalance tail. -/
theorem negBin_adjacent_band_urn_imbalance_real_le
    (i w n h : ℕ) (upper lower : Finset ℕ)
    (s : Finset ℕ) (hs : s ∈ (Finset.range n).powersetCard h)
    (hi : 1 ≤ i) (hw : 1 ≤ w)
    (hscale : 64 * w * (w + 1) ≤ i)
    (hcard : upper.card = lower.card) (hlower : lower.Nonempty)
    (horder : ∀ u ∈ upper, ∀ v ∈ lower, v ≤ u)
    (hdist : ∀ u ∈ upper, ∀ v ∈ lower, u - v ≤ 2 * w)
    (hupperBand : ∀ u ∈ upper, Erdos1166.HLOZUrn.InNegBinMeanBand i w u)
    (hlowerBand : ∀ v ∈ lower, Erdos1166.HLOZUrn.InNegBinMeanBand i w v)
    (hlowerMass : 0 < ∑ v ∈ lower, Erdos1166.HLOZUrn.negBinMass i v) :
    (setBer(Set.Iio n, Erdos1166.HLOZUrn.adjacentUrnParameter
      (∑ u ∈ upper, Erdos1166.HLOZUrn.negBinMass i u)
      (∑ v ∈ lower, Erdos1166.HLOZUrn.negBinMass i v)
      (negBinMass_sum_nonneg i upper) hlowerMass)).real
        (urnImbalanceEvent s (Real.exp 1)) ≤
      Real.exp (-imbalanceRate (Real.exp 1) * h) := by
  apply finite_iid_urn_imbalance_real_le n h s hs
  · exact Real.one_le_exp (by norm_num)
  · exact negBinMass_upper_sum_le_exp_one_mul_lower_sum i w upper lower
      hi hw hscale hcard hlower horder hdist hupperBand hlowerBand

section AdjacentBandUrn

variable {β α : Type*} [DecidableEq α]

/-- Event-level imbalance bound for every member of a finite adjacent-band
family.  Pointwise mass comparability is first summed over the bands, and
then the finite iid conditional urn theorem is applied. -/
theorem finite_adjacent_band_urn_imbalance_real_le
    {C : ℝ} (B : FiniteAdjacentBands (β := β) (α := α) C) (hC : 1 ≤ C)
    (b : β) (n h : ℕ) (s : Finset ℕ)
    (hs : s ∈ (Finset.range n).powersetCard h)
    (hlower : 0 < B.lowerMass b) :
    (setBer(Set.Iio n, Erdos1166.HLOZUrn.adjacentUrnParameter
      (B.upperMass b) (B.lowerMass b) (B.upperMass_nonneg b) hlower)).real
        (urnImbalanceEvent s C) ≤
      Real.exp (-imbalanceRate C * h) := by
  exact finite_iid_urn_imbalance_real_le n h s hs
    (B.upperMass b) (B.lowerMass b) C (B.upperMass_nonneg b) hlower hC
    (B.upperMass_le_mul_lowerMass b)

end AdjacentBandUrn

/-- A source-shaped event union for (4.45)--(4.48): failure at the next
level is contained in the previous failure, the supplied `Theta`-bad
event, or the adjacent-urn imbalance event. -/
theorem one_step_q_recursion_of_finite_iid_urn
    (n h : ℕ) (s : Finset ℕ) (hs : s ∈ (Finset.range n).powersetCard h)
    (p q C : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (hC : 1 ≤ C)
    (hpq : p ≤ C * q)
    (previous thetaBad next : Set (Set ℕ)) (qPrevious thetaError : ℝ)
    (hcover : next ⊆ previous ∪ thetaBad ∪ urnImbalanceEvent s C)
    (hprevious :
      (setBer(Set.Iio n, Erdos1166.HLOZUrn.adjacentUrnParameter p q hp hq)).real previous ≤
        qPrevious)
    (htheta :
      (setBer(Set.Iio n, Erdos1166.HLOZUrn.adjacentUrnParameter p q hp hq)).real thetaBad ≤
        thetaError) :
    (setBer(Set.Iio n, Erdos1166.HLOZUrn.adjacentUrnParameter p q hp hq)).real next ≤
      qPrevious + Real.exp (-imbalanceRate C * h) + thetaError := by
  let μ := setBer(Set.Iio n, Erdos1166.HLOZUrn.adjacentUrnParameter p q hp hq)
  have hurn : μ.real (urnImbalanceEvent s C) ≤ Real.exp (-imbalanceRate C * h) :=
    finite_iid_urn_imbalance_real_le n h s hs p q C hp hq hC hpq
  calc
    μ.real next ≤ μ.real (previous ∪ thetaBad ∪ urnImbalanceEvent s C) :=
      measureReal_mono hcover
    _ ≤ μ.real previous + μ.real thetaBad + μ.real (urnImbalanceEvent s C) := by
      calc
        μ.real (previous ∪ thetaBad ∪ urnImbalanceEvent s C) ≤
            μ.real (previous ∪ thetaBad) + μ.real (urnImbalanceEvent s C) :=
          measureReal_union_le _ _
        _ ≤ (μ.real previous + μ.real thetaBad) +
            μ.real (urnImbalanceEvent s C) := by
          gcongr
          exact measureReal_union_le _ _
    _ ≤ qPrevious + thetaError + Real.exp (-imbalanceRate C * h) := by gcongr
    _ = qPrevious + Real.exp (-imbalanceRate C * h) + thetaError := by ring

/-- Equation (4.48) in its source error shape: the supplied `Theta`-bad
estimate is `exp (-cTheta * m^a)`, while the other new error is obtained from
the finite conditional iid urn calculation above. -/
theorem one_step_q_recursion_with_theta_exp
    (n h m : ℕ) (s : Finset ℕ) (hs : s ∈ (Finset.range n).powersetCard h)
    (p q C : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (hC : 1 ≤ C)
    (hpq : p ≤ C * q) (cTheta a : ℝ)
    (previous thetaBad next : Set (Set ℕ)) (qPrevious : ℝ)
    (hcover : next ⊆ previous ∪ thetaBad ∪ urnImbalanceEvent s C)
    (hprevious :
      (setBer(Set.Iio n, Erdos1166.HLOZUrn.adjacentUrnParameter p q hp hq)).real previous ≤
        qPrevious)
    (htheta :
      (setBer(Set.Iio n, Erdos1166.HLOZUrn.adjacentUrnParameter p q hp hq)).real thetaBad ≤
        Real.exp (-cTheta * (m : ℝ) ^ a)) :
    (setBer(Set.Iio n, Erdos1166.HLOZUrn.adjacentUrnParameter p q hp hq)).real next ≤
      qPrevious + Real.exp (-imbalanceRate C * h) +
        Real.exp (-cTheta * (m : ℝ) ^ a) := by
  exact one_step_q_recursion_of_finite_iid_urn n h s hs p q C hp hq hC hpq
    previous thetaBad next qPrevious (Real.exp (-cTheta * (m : ℝ) ^ a))
    hcover hprevious htheta

end Erdos1166.HLOZLemma411Recursion

import ErdosProblems.Erdos1002.AnnularCompoundPoissonGrid
import ErdosProblems.Erdos1002.GaussDenominatorMaximal
import ErdosProblems.Erdos1002.GaussPrefixMixedSortedPartition
import Mathlib.Data.Int.CardIntervalMod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Deterministic annular depth boxes at logarithmic scale

This module records the exact deterministic data used when a labeled
annular-grid factorial expansion is put in chronological order.

* the continued-fraction depth clock is normalized by `gaussRoofMean`;
* a signed positive cell is assigned even depth and a signed negative cell
  odd depth;
* every time, signed-value, and torus endpoint is pulled back through the
  same canonical occurrence order;
* the elementary factor `1/2` coming from a prescribed parity class is
  proved by an exact residue-class count, including both endpoints.

The terminal singleton cells are deliberately not folded into these
interior boxes.  They are deleted and restored separately in the final
grid assembly.
-/

open Filter Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularDepthBoxesPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-! ## Exact parity counts in natural half-open intervals -/

/-- Natural numbers in `[a,b)` with one prescribed residue modulo two. -/
def parityIco (a b : ℕ) (parity : Fin 2) : Finset ℕ :=
  (Finset.Ico a b).filter fun n ↦ n % 2 = parity.1

private theorem parityIco_eq_sdiff
    (a b : ℕ) (parity : Fin 2) :
    parityIco a b parity =
      ((Finset.range b).filter fun n ↦ n % 2 = parity.1) \
        ((Finset.range a).filter fun n ↦ n % 2 = parity.1) := by
  ext n
  simp [parityIco]
  omega

private theorem filter_modEq_eq_filter_mod
    (b : ℕ) (parity : Fin 2) :
    ((Finset.range b).filter fun n ↦ n ≡ parity.1 [MOD 2]) =
      ((Finset.range b).filter fun n ↦ n % 2 = parity.1) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
  intro _hn
  change n % 2 = parity.1 % 2 ↔ n % 2 = parity.1
  rw [Nat.mod_eq_of_lt parity.2]

/-- Exact prefix-count subtraction for a parity-restricted half-open
interval.  This is the discrete Abel endpoint identity needed below. -/
theorem card_parityIco_eq_count_sub
    (a b : ℕ) (parity : Fin 2) (hab : a ≤ b) :
    (parityIco a b parity).card =
      Nat.count (fun n ↦ n ≡ parity.1 [MOD 2]) b -
        Nat.count (fun n ↦ n ≡ parity.1 [MOD 2]) a := by
  rw [parityIco_eq_sdiff a b parity, Finset.card_sdiff_of_subset]
  · rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
      filter_modEq_eq_filter_mod, filter_modEq_eq_filter_mod]
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨lt_of_lt_of_le hn.1 hab, hn.2⟩

private theorem count_mod_two_bounds (b : ℕ) (parity : Fin 2) :
    b / 2 ≤ Nat.count (fun n ↦ n ≡ parity.1 [MOD 2]) b ∧
      Nat.count (fun n ↦ n ≡ parity.1 [MOD 2]) b ≤ b / 2 + 1 := by
  rw [Nat.count_modEq_card b (by omega : 0 < 2) parity.1]
  split_ifs <;> omega

/-- The real prefix count differs from half the interval length by at most
one.  The estimate is uniform in the prescribed parity. -/
theorem abs_cast_count_mod_two_sub_half_le_one
    (b : ℕ) (parity : Fin 2) :
    |(Nat.count (fun n ↦ n ≡ parity.1 [MOD 2]) b : ℝ) -
        (b : ℝ) / 2| ≤ 1 := by
  have hbounds := count_mod_two_bounds b parity
  have hdivmod := Nat.div_add_mod b 2
  have hrem : b % 2 < 2 := Nat.mod_lt b (by omega)
  have hcastBounds :
      ((b / 2 : ℕ) : ℝ) ≤
          (Nat.count (fun n ↦ n ≡ parity.1 [MOD 2]) b : ℝ) ∧
        (Nat.count (fun n ↦ n ≡ parity.1 [MOD 2]) b : ℝ) ≤
          ((b / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hbounds
  have hcastDivMod :
      (b : ℝ) =
        2 * ((b / 2 : ℕ) : ℝ) + ((b % 2 : ℕ) : ℝ) := by
    exact_mod_cast hdivmod.symm
  have hcastRem : ((b % 2 : ℕ) : ℝ) < 2 := by
    exact_mod_cast hrem
  have hcastRemNonneg : (0 : ℝ) ≤ ((b % 2 : ℕ) : ℝ) := by
    positivity
  rw [abs_le]
  constructor <;> nlinarith

/-- A prescribed parity has asymptotic density `1/2` along every real
normalization tending to infinity. -/
theorem tendsto_count_mod_two_div_scale
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (b : ℕ → ℕ) (parity : Fin 2) {beta : ℝ}
    (hb : Tendsto (fun n ↦ (b n : ℝ) / scale n)
      atTop (nhds beta)) :
    Tendsto
      (fun n ↦
        (Nat.count (fun q ↦ q ≡ parity.1 [MOD 2]) (b n) : ℝ) /
          scale n)
      atTop (nhds (beta / 2)) := by
  have hrecip : Tendsto (fun n ↦ (1 : ℝ) / scale n)
      atTop (nhds 0) := by
    exact (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).div_atTop hscale
  have hdiff : Tendsto
      (fun n ↦
        (Nat.count (fun q ↦ q ≡ parity.1 [MOD 2]) (b n) : ℝ) /
            scale n -
          ((b n : ℝ) / scale n) / 2)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ abs_nonneg _
    · filter_upwards [hscale.eventually_gt_atTop 0] with n hn
      have habs :=
        abs_cast_count_mod_two_sub_half_le_one (b n) parity
      calc
        |(Nat.count (fun q ↦ q ≡ parity.1 [MOD 2]) (b n) : ℝ) /
              scale n -
            ((b n : ℝ) / scale n) / 2| =
            |(Nat.count (fun q ↦ q ≡ parity.1 [MOD 2]) (b n) : ℝ) -
              (b n : ℝ) / 2| / scale n := by
                have heq :
                    (Nat.count
                        (fun q ↦ q ≡ parity.1 [MOD 2]) (b n) : ℝ) /
                          scale n -
                        ((b n : ℝ) / scale n) / 2 =
                      ((Nat.count
                          (fun q ↦ q ≡ parity.1 [MOD 2]) (b n) : ℝ) -
                        (b n : ℝ) / 2) / scale n := by
                  field_simp [ne_of_gt hn]
                rw [heq, abs_div, abs_of_pos hn]
        _ ≤ 1 / scale n :=
          div_le_div_of_nonneg_right habs hn.le
    · exact hrecip
  have hbase := hb.div_const 2
  have hsum := hdiff.add hbase
  convert! hsum using 1
  · funext n
    ring
  · ring_nf

/-- Half-open intervals inherit the same `1/2` density, with both prefix
boundary terms retained explicitly. -/
theorem tendsto_card_parityIco_div_scale
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (a b : ℕ → ℕ) (parity : Fin 2) {alpha beta : ℝ}
    (hab : ∀ᶠ n in atTop, a n ≤ b n)
    (ha : Tendsto (fun n ↦ (a n : ℝ) / scale n)
      atTop (nhds alpha))
    (hb : Tendsto (fun n ↦ (b n : ℝ) / scale n)
      atTop (nhds beta)) :
    Tendsto
      (fun n ↦ ((parityIco (a n) (b n) parity).card : ℝ) / scale n)
      atTop (nhds ((beta - alpha) / 2)) := by
  have hca :=
    tendsto_count_mod_two_div_scale scale hscale a parity ha
  have hcb :=
    tendsto_count_mod_two_div_scale scale hscale b parity hb
  have hsub := hcb.sub hca
  have hsub' : Tendsto
      (fun n ↦
        (Nat.count (fun q ↦ q ≡ parity.1 [MOD 2]) (b n) : ℝ) /
            scale n -
          (Nat.count (fun q ↦ q ≡ parity.1 [MOD 2]) (a n) : ℝ) /
            scale n)
      atTop (nhds ((beta - alpha) / 2)) := by
    convert! hsub using 1
    ring_nf
  apply hsub'.congr'
  filter_upwards [hab, hscale.eventually_gt_atTop 0] with n habn _hscale
  rw [card_parityIco_eq_count_sub (a n) (b n) parity habn]
  rw [Nat.cast_sub]
  · ring
  · exact Nat.count_monotone
      (fun q ↦ q ≡ parity.1 [MOD 2]) habn

/-! ## Logarithmic clock boxes -/

/-- A moving natural ceiling has the expected normalized limit.  The
`c=0` endpoint is handled exactly rather than by invoking an at-top
rounding theorem outside its hypotheses. -/
theorem tendsto_natCeil_const_mul_scale_div
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d) :
    Tendsto
      (fun n ↦ (⌈c * scale n / d⌉₊ : ℝ) / scale n)
      atTop (nhds (c / d)) := by
  rcases hc.eq_or_lt with rfl | hcpos
  · simp
  · have hx : Tendsto (fun n ↦ c * scale n / d) atTop atTop :=
      (hscale.const_mul_atTop hcpos).atTop_div_const hd
    have hround : Tendsto
        (fun n ↦ (⌈c * scale n / d⌉₊ : ℝ) /
          (c * scale n / d))
        atTop (nhds 1) :=
      tendsto_nat_ceil_div_atTop.comp hx
    have hlinear : Tendsto
        (fun n ↦ (c * scale n / d) / scale n)
        atTop (nhds (c / d)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hscale.eventually_gt_atTop 0] with n hn
      field_simp [ne_of_gt hn, ne_of_gt hd]
    have hmul := hround.mul hlinear
    convert! hmul using 1
    · funext n
      by_cases hs : scale n = 0
      · simp [hs]
      · field_simp [hs, ne_of_gt hd]
    · ring_nf

/-- The natural depth corresponding to one deterministic time endpoint. -/
def gaussLogDepthEndpoint (N : ℕ) (time : ℝ) : ℕ :=
  ⌈time * Real.log (N : ℝ) / gaussRoofMean⌉₊

/-- The lower depth endpoint of a nonterminal annular time cell. -/
def annularTimeDepthLower
    (N grid : ℕ) (i : AnnularGridIndex grid) : ℕ :=
  gaussLogDepthEndpoint N
    (intervalGridPoint 0 1 grid i.time.1)

/-- The upper depth endpoint of a nonterminal annular time cell. -/
def annularTimeDepthUpper
    (N grid : ℕ) (i : AnnularGridIndex grid) : ℕ :=
  gaussLogDepthEndpoint N
    (intervalGridPoint 0 1 grid (i.time.1 + 1))

/-- Positive signed cells occur at even depth and negative signed cells at
odd depth. -/
def annularGridDepthParity
    {grid : ℕ} (i : AnnularGridIndex grid) : Fin 2 :=
  if i.sign then ⟨0, by omega⟩ else ⟨1, by omega⟩

/-- The parity-restricted logarithmic depth box of one nonterminal time
cell. -/
def annularTimeParityDepthBox
    (N grid : ℕ) (i : AnnularGridIndex grid) : Finset ℕ :=
  parityIco (annularTimeDepthLower N grid i)
    (annularTimeDepthUpper N grid i) (annularGridDepthParity i)

/-- The logarithmic normalization used by the literal marked process tends
to infinity. -/
theorem tendsto_log_natCast_atTop :
    Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Every grid point with index at most the subdivision order is
nonnegative in the time grid. -/
private theorem intervalGridPoint_zero_one_nonneg
    {grid q : ℕ} (hgrid : 0 < grid) (hq : q ≤ grid) :
    0 ≤ intervalGridPoint 0 1 grid q :=
  (intervalGridPoint_mem_Icc zero_le_one hgrid hq).1

/-- Normalized lower depth endpoints converge to the corresponding time
endpoint divided by the Gauss roof mean. -/
theorem tendsto_annularTimeDepthLower_div_log
    {grid : ℕ} (hgrid : 0 < grid) (i : AnnularGridIndex grid) :
    Tendsto
      (fun N ↦ (annularTimeDepthLower N grid i : ℝ) /
        Real.log (N : ℝ))
      atTop
      (nhds (intervalGridPoint 0 1 grid i.time.1 /
        gaussRoofMean)) := by
  have hq : i.time.1 ≤ grid := by omega
  simpa only [annularTimeDepthLower, gaussLogDepthEndpoint] using!
    tendsto_natCeil_const_mul_scale_div
      (fun N : ℕ ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop
      (intervalGridPoint_zero_one_nonneg hgrid hq)
      gaussRoofMean_pos

/-- The analogous upper-endpoint limit for a nonterminal time cell. -/
theorem tendsto_annularTimeDepthUpper_div_log
    {grid : ℕ} (hgrid : 0 < grid) (i : AnnularGridIndex grid)
    (hi : i.time.1 < grid) :
    Tendsto
      (fun N ↦ (annularTimeDepthUpper N grid i : ℝ) /
        Real.log (N : ℝ))
      atTop
      (nhds (intervalGridPoint 0 1 grid (i.time.1 + 1) /
        gaussRoofMean)) := by
  have hq : i.time.1 + 1 ≤ grid := by omega
  simpa only [annularTimeDepthUpper, gaussLogDepthEndpoint] using!
    tendsto_natCeil_const_mul_scale_div
      (fun N : ℕ ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop
      (intervalGridPoint_zero_one_nonneg hgrid hq)
      gaussRoofMean_pos

/-- Eventually the rounded lower endpoint does not exceed the rounded
upper endpoint of a nonterminal cell. -/
theorem eventually_annularTimeDepthLower_le_upper
    {grid : ℕ} (i : AnnularGridIndex grid)
    (hi : i.time.1 < grid) :
    ∀ᶠ N : ℕ in atTop,
      annularTimeDepthLower N grid i ≤
        annularTimeDepthUpper N grid i := by
  have hgrid' : 0 < grid := lt_of_le_of_lt (Nat.zero_le i.time.1) hi
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  apply Nat.ceil_mono
  have htime :=
    (intervalGridPoint_strictMono_step
      (a := (0 : ℝ)) (b := 1) zero_lt_one hgrid'
      (k := i.time.1)).le
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right htime hlog.le)
    gaussRoofMean_pos.le

/-- Exact parity density of one nonterminal annular time cell at the
literal scale `log N`. -/
theorem tendsto_annularTimeParityDepthBox_card_div_log
    {grid : ℕ} (hgrid : 0 < grid) (i : AnnularGridIndex grid)
    (hi : i.time.1 < grid) :
    Tendsto
      (fun N ↦ ((annularTimeParityDepthBox N grid i).card : ℝ) /
        Real.log (N : ℝ))
      atTop
      (nhds
        ((intervalGridPoint 0 1 grid (i.time.1 + 1) -
            intervalGridPoint 0 1 grid i.time.1) /
          (2 * gaussRoofMean))) := by
  have hraw :=
    tendsto_card_parityIco_div_scale
      (fun N : ℕ ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop
      (fun N ↦ annularTimeDepthLower N grid i)
      (fun N ↦ annularTimeDepthUpper N grid i)
      (annularGridDepthParity i)
      (eventually_annularTimeDepthLower_le_upper i hi)
      (tendsto_annularTimeDepthLower_div_log hgrid i)
      (tendsto_annularTimeDepthUpper_div_log hgrid i hi)
  convert! hraw using 1
  ring_nf

/-! ## Flattened annular-coordinate data -/

variable {ι : Type*} [Fintype ι]

/-- Label of the occurrence occupying chronological coordinate `j`. -/
abbrev flattenedMixedOccurrenceLabel
    {k : ι → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) : ι :=
  (e j).1

/-- Lower endpoint of the flattened time cell. -/
def flattenedAnnularTimeLower
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  intervalGridPoint 0 1 grid ((e j).1.time.1)

/-- Upper endpoint of the flattened nonterminal time cell. -/
def flattenedAnnularTimeUpper
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  intervalGridPoint 0 1 grid ((e j).1.time.1 + 1)

/-- Lower endpoint of the flattened signed-value cell. -/
def flattenedAnnularSignedLower
    (ε A : ℝ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  intervalGridPoint
    (signedGridLower ε A (e j).1.sign)
    (signedGridUpper ε A (e j).1.sign)
    grid ((e j).1.signed.1)

/-- Upper endpoint of the flattened nonterminal signed-value cell. -/
def flattenedAnnularSignedUpper
    (ε A : ℝ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  intervalGridPoint
    (signedGridLower ε A (e j).1.sign)
    (signedGridUpper ε A (e j).1.sign)
    grid ((e j).1.signed.1 + 1)

/-- Lower endpoint of the flattened torus cell. -/
def flattenedAnnularTorusLower
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  intervalGridPoint 0 1 grid ((e j).1.torus.1)

/-- Upper endpoint of the flattened nonterminal torus cell. -/
def flattenedAnnularTorusUpper
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) : ℝ :=
  intervalGridPoint 0 1 grid ((e j).1.torus.1 + 1)

/-- Prescribed parity in flattened chronological coordinates. -/
def flattenedAnnularParity
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) : Fin 2 :=
  annularGridDepthParity (e j).1

/-- Pull a labeled Fourier assignment into flattened chronological
coordinates. -/
def flattenedAnnularFourierMode
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (h : ∀ i, Fin (k i) → ℤ)
    (j : Fin (MixedOccurrenceCount k)) : ℤ :=
  h (e j).1 (e j).2

/-- Labeled logarithmic depth boxes, before chronological sorting. -/
def annularOccurrenceDepthBoxes
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    GaussPrefixMixedOccurrence k → Finset ℕ :=
  fun z ↦ Finset.Ico
    (annularTimeDepthLower N grid z.1)
    (annularTimeDepthUpper N grid z.1)

/-- Labeled prescribed parity, before chronological sorting. -/
def annularOccurrenceParity
    {grid : ℕ} (k : AnnularGridIndex grid → ℕ) :
    GaussPrefixMixedOccurrence k → Fin 2 :=
  fun z ↦ annularGridDepthParity z.1

/-- The parity-filtered depth box attached to one labeled occurrence. -/
def annularOccurrenceParityDepthBox
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    GaussPrefixMixedOccurrence k → Finset ℕ :=
  fun z ↦ annularTimeParityDepthBox N grid z.1

/-- The full rectangular product of labeled depth boxes, before collisions
are removed and the surviving assignments are chronologically sorted. -/
def annularOccurrenceAssignmentBox
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    Finset (GaussPrefixMixedOccurrence k → ℕ) :=
  Fintype.piFinset (annularOccurrenceParityDepthBox N k)

/-- Product of the deterministic time/parity densities of all labeled
occurrences. -/
def annularOccurrenceTimeDensity
    {grid : ℕ} (k : AnnularGridIndex grid → ℕ) : ℝ :=
  ∏ z : GaussPrefixMixedOccurrence k,
    (intervalGridPoint 0 1 grid (z.1.time.1 + 1) -
      intervalGridPoint 0 1 grid z.1.time.1) /
        (2 * gaussRoofMean)

/-- The rectangular labeled box has the product time/parity density.
Every label is required to use a nonterminal time cell; terminal layers
are handled by the explicit endpoint-deletion theorem. -/
theorem tendsto_annularOccurrenceAssignmentBox_card_div_log_pow
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦ ((annularOccurrenceAssignmentBox N k).card : ℝ) /
        (Real.log (N : ℝ)) ^ MixedOccurrenceCount k)
      atTop (nhds (annularOccurrenceTimeDensity k)) := by
  have hprod :
      Tendsto
        (fun N ↦ ∏ z : GaussPrefixMixedOccurrence k,
          ((annularOccurrenceParityDepthBox N k z).card : ℝ) /
            Real.log (N : ℝ))
        atTop (nhds (annularOccurrenceTimeDensity k)) := by
    apply tendsto_finset_prod Finset.univ
    intro z _hz
    exact tendsto_annularTimeParityDepthBox_card_div_log
      hgrid z.1 (htime z.1 (by
        have hz := z.2.isLt
        omega))
  apply hprod.congr'
  filter_upwards with N
  rw [annularOccurrenceAssignmentBox, Fintype.card_piFinset]
  symm
  change
    ((∏ z : GaussPrefixMixedOccurrence k,
        (annularOccurrenceParityDepthBox N k z).card : ℕ) : ℝ) /
        Real.log (N : ℝ) ^ MixedOccurrenceCount k =
      ∏ z : GaussPrefixMixedOccurrence k,
        ((annularOccurrenceParityDepthBox N k z).card : ℝ) /
          Real.log (N : ℝ)
  push_cast
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ]

/-- The exact chronological tuple family for one canonical occurrence
order. -/
def canonicalAnnularGridTupleFamily
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  canonicalMixedOrderParityBoxTimes N k e
    (annularOccurrenceDepthBoxes N k)
    (annularOccurrenceParity k)

theorem canonicalAnnularGridTupleFamily_chronological
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ canonicalAnnularGridTupleFamily N k e) :
    IsChronologicalNatTuple t :=
  canonicalMixedOrderParityBoxTimes_chronological e
    (annularOccurrenceDepthBoxes N k)
    (annularOccurrenceParity k) t ht

theorem canonicalAnnularGridTupleFamily_parity
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ canonicalAnnularGridTupleFamily N k e)
    (j : Fin (MixedOccurrenceCount k)) :
    t j % 2 = (flattenedAnnularParity e j).1 := by
  exact canonicalMixedOrderParityBoxTimes_parity e
    (annularOccurrenceDepthBoxes N k)
    (annularOccurrenceParity k) t ht j

end

end Erdos1002

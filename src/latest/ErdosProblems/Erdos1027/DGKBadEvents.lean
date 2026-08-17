/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1027.DGKWeight
import ErdosProblems.Erdos1027.DGKPriorities
import ErdosProblems.Erdos1027.DGKAnalytic

/-!
# The two elementary DGK bad events

This file gives concrete finite-probability estimates for the first two bad
events in the Duraj--Gutowski--Kozik recolouring argument.

* `hasLightEdge_lt_one_over_128` is the union bound for an initially
  monochromatic edge all of whose priorities miss its high window.
* `almostPairMass_bad_le_one_eighth` is the Markov estimate for the
  size-normalized number of pairs `(e,v)` for which `e.erase v` is initially
  monochromatic.

The second statistic is defined directly on the common finite
colour--priority outcome space.  Its expectation is proved exactly equal to
twice the doubled Boolean weight `q(H)`; no independence or probability
claim is left implicit.
-/

open scoped BigOperators

namespace Erdos1027.DGKBadEvents

open Finset
open Erdos1027.FiniteExpect

abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-! ## The light-edge event -/

/-- A light edge is initially monochromatic and all its priorities lie below
the high interval of density `d / |e|`. -/
def LightEdge {V : Type*} {N : ℕ} (d : ℕ)
    (w : DGKPriorities.Outcome V N) (e : Finset V) : Prop :=
  DGKPriorities.InitiallyMonochromatic w e ∧
    DGKPriorities.AllLow d e.card w e

/-- Some edge of `H` is light. -/
def HasLightEdge {V : Type*} {N : ℕ} (H : Hypergraph V) (d : ℕ)
    (w : DGKPriorities.Outcome V N) : Prop :=
  ∃ e ∈ H, LightEdge d w e

/-- The probability of one light edge is its doubled Boolean-weight summand
divided by at least `d+1`. -/
lemma expect_indicator_lightEdge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {N d : ℕ} (hN : 0 < N) (e : Finset V)
    (hdiv : e.card ∣ N) (hdcard : d ≤ e.card) :
    (𝔼 w : DGKPriorities.Outcome V N, indicator (LightEdge d w e)) ≤
      (2 : ℚ) ^ (1 - (e.card : ℤ)) / ((d : ℚ) + 1) := by
  classical
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hecard : 0 < e.card := Nat.pos_of_dvd_of_pos hdiv hN
  have he : e.Nonempty := Finset.card_pos.mp hecard
  rw [show (𝔼 w : DGKPriorities.Outcome V N, indicator (LightEdge d w e)) =
      (2 : ℚ) ^ (1 - (e.card : ℤ)) *
        (1 - (d : ℚ) / e.card) ^ e.card by
    simpa [LightEdge] using
      DGKPriorities.expect_indicator_initiallyMonochromatic_and_allLow
        hN hdcard hdiv e rfl he]
  simpa [div_eq_mul_inv, one_div] using
    mul_le_mul_of_nonneg_left
      (DGKAnalytic.one_sub_div_pow_le_inv_add_one_rat d e.card hdcard)
      (zpow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _)

private lemma two_zpow_neg_eq_zpow_one_sub (k : ℕ) :
    2 * (2 : ℚ) ^ (-(k : ℤ)) = (2 : ℚ) ^ (1 - (k : ℤ)) := by
  rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
  rw [zpow_neg]
  ring

/-- General rational union bound for light edges. -/
theorem expect_indicator_hasLightEdge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {N d : ℕ} (H : Hypergraph V) (hN : 0 < N)
    (hdiv : ∀ e ∈ H, e.card ∣ N) (hmin : ∀ e ∈ H, d ≤ e.card) :
    (𝔼 w : DGKPriorities.Outcome V N, indicator (HasLightEdge H d w)) ≤
      DGKWeight.qWeightQ H / ((d : ℚ) + 1) := by
  classical
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  calc
    (𝔼 w : DGKPriorities.Outcome V N, indicator (HasLightEdge H d w)) ≤
        ∑ e ∈ H,
          𝔼 w : DGKPriorities.Outcome V N, indicator (LightEdge d w e) := by
      simpa [HasLightEdge] using
        expect_indicator_biExists_le_sum H (fun e w ↦ LightEdge d w e)
    _ ≤ ∑ e ∈ H,
        (2 : ℚ) ^ (1 - (e.card : ℤ)) / ((d : ℚ) + 1) := by
      exact Finset.sum_le_sum fun e he ↦
        expect_indicator_lightEdge_le hN e (hdiv e he) (hmin e he)
    _ = DGKWeight.qWeightQ H / ((d : ℚ) + 1) := by
      rw [← Finset.sum_div]
      congr 1
      unfold DGKWeight.qWeightQ DGKWeight.booleanWeightQ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      exact (two_zpow_neg_eq_zpow_one_sub e.card).symm

private lemma Q_div_128Q_add_one_lt_one_over_128 (Q : ℕ) (hQ : 0 < Q) :
    (Q : ℚ) / ((128 * Q : ℕ) + 1) < (1 : ℚ) / 128 := by
  have hden : (0 : ℚ) < ((128 * Q : ℕ) + 1) := by positivity
  rw [div_lt_iff₀ hden]
  norm_num [div_eq_mul_inv]
  linarith

/-- For the standard choice `d = 128 Q`, the first bad event has probability
strictly below `1/128`, hence in particular below `1/64`. -/
theorem hasLightEdge_lt_one_over_128
    {V : Type*} [Fintype V] [DecidableEq V]
    {N Q : ℕ} (H : Hypergraph V) (hN : 0 < N) (hQ : 0 < Q)
    (hdiv : ∀ e ∈ H, e.card ∣ N)
    (hmin : ∀ e ∈ H, 128 * Q ≤ e.card)
    (hq : DGKWeight.qWeightQ H ≤ Q) :
    (𝔼 w : DGKPriorities.Outcome V N,
        indicator (HasLightEdge H (128 * Q) w)) < (1 : ℚ) / 128 := by
  calc
    (𝔼 w : DGKPriorities.Outcome V N,
        indicator (HasLightEdge H (128 * Q) w)) ≤
        DGKWeight.qWeightQ H / (((128 * Q : ℕ) : ℚ) + 1) :=
      expect_indicator_hasLightEdge_le H hN hdiv hmin
    _ ≤ (Q : ℚ) / (((128 * Q : ℕ) : ℚ) + 1) := by
      exact div_le_div_of_nonneg_right hq (by positivity)
    _ < (1 : ℚ) / 128 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        Q_div_128Q_add_one_lt_one_over_128 Q hQ

theorem hasLightEdge_lt_one_over_64
    {V : Type*} [Fintype V] [DecidableEq V]
    {N Q : ℕ} (H : Hypergraph V) (hN : 0 < N) (hQ : 0 < Q)
    (hdiv : ∀ e ∈ H, e.card ∣ N)
    (hmin : ∀ e ∈ H, 128 * Q ≤ e.card)
    (hq : DGKWeight.qWeightQ H ≤ Q) :
    (𝔼 w : DGKPriorities.Outcome V N,
        indicator (HasLightEdge H (128 * Q) w)) < (1 : ℚ) / 64 := by
  exact (hasLightEdge_lt_one_over_128 H hN hQ hdiv hmin hq).trans
    (by norm_num)

/-! ## Marginalizing away the priorities -/

/-- The Boolean colouring contained in a colour--priority outcome. -/
def initialColour {V : Type*} {N : ℕ}
    (w : DGKPriorities.Outcome V N) : V → Bool :=
  fun v ↦ DGKPriorities.colour w v

/-- A statistic depending only on the initial colours has the same
expectation on the colour--priority product space as on fair Boolean
colourings. -/
theorem expect_colourStatistic
    {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ} (hN : 0 < N)
    (f : (V → Bool) → ℚ) :
    (𝔼 w : DGKPriorities.Outcome V N, f (initialColour w)) =
      𝔼 χ : V → Bool, f χ := by
  classical
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  let e := Equiv.arrowProdEquivProdArrow V
    (fun _ : V ↦ Bool) (fun _ : V ↦ Fin N)
  calc
    (𝔼 w : DGKPriorities.Outcome V N, f (initialColour w)) =
        𝔼 p : (V → Bool) × (V → Fin N), f p.1 := by
          apply Fintype.expect_equiv e
          intro w
          rfl
    _ = 𝔼 χ : V → Bool, 𝔼 _priority : V → Fin N, f χ := by
          simpa only [Finset.univ_product_univ] using
            (Finset.expect_product
              (Finset.univ : Finset (V → Bool))
              (Finset.univ : Finset (V → Fin N))
              (fun p : (V → Bool) × (V → Fin N) ↦ f p.1))
    _ = 𝔼 χ : V → Bool, f χ := by simp

/-! ## Almost-monochromatic pairs -/

/-- Deleting the distinguished vertex makes the rest of the edge
monochromatic in the initial colouring. -/
def AlmostMonoAt {V : Type*} [DecidableEq V]
    (χ : V → Bool) (e : Finset V) (v : V) : Prop :=
  IsMonochromatic (e.erase v) χ

/-- The size-normalized number of almost-monochromatic pairs `(e,v)`, with
exact rational values. -/
noncomputable def almostPairMassQ {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (χ : V → Bool) : ℚ :=
  ∑ e ∈ H, ∑ v ∈ e,
    indicator (AlmostMonoAt χ e v) / (e.card : ℚ)

lemma almostPairMassQ_nonneg {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (χ : V → Bool) :
    0 ≤ almostPairMassQ H χ := by
  unfold almostPairMassQ
  exact Finset.sum_nonneg fun e _ ↦ Finset.sum_nonneg fun v _ ↦
    div_nonneg (indicator_nonneg _) (by positivity)

/-- Exact one-pair expectation. -/
lemma expect_indicator_almostMonoAt
    {V : Type*} [Fintype V] [DecidableEq V]
    (e : Finset V) {v : V} (hv : v ∈ e) (he : 2 ≤ e.card) :
    (𝔼 χ : V → Bool, indicator (AlmostMonoAt χ e v)) =
      2 / (2 : ℚ) ^ (e.card - 1) := by
  have herase : (e.erase v).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hv]
    omega
  simpa [AlmostMonoAt, Finset.card_erase_of_mem hv] using
    (expect_indicator_isMonochromatic (e.erase v) herase)

private lemma four_mul_zpow_neg_eq_two_div_pow_pred (j : ℕ) (hj : 1 ≤ j) :
    4 * (2 : ℚ) ^ (-(j : ℤ)) = 2 / (2 : ℚ) ^ (j - 1) := by
  rw [zpow_neg, zpow_natCast]
  rw [show j = (j - 1) + 1 by omega, pow_succ]
  field_simp
  rw [show j - 1 + 1 - 1 = j - 1 by omega]
  norm_num
  ring

/-- The exact first-moment identity behind the second DGK bad event.

The right side is twice `q(H)`: for a `j`-edge, each of its `j` possible
distinguished vertices has probability `2^(2-j)`, and the statistic gives
each pair weight `1/j`. -/
theorem expect_almostPairMassQ
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (hmin : ∀ e ∈ H, 2 ≤ e.card) :
    (𝔼 χ : V → Bool, almostPairMassQ H χ) =
      2 * DGKWeight.qWeightQ H := by
  classical
  unfold almostPairMassQ
  rw [Finset.expect_sum_comm]
  simp_rw [Finset.expect_sum_comm]
  calc
    (∑ e ∈ H, ∑ v ∈ e,
        𝔼 χ : V → Bool,
          indicator (AlmostMonoAt χ e v) / (e.card : ℚ)) =
        ∑ e ∈ H, 2 / (2 : ℚ) ^ (e.card - 1) := by
      apply Finset.sum_congr rfl
      intro e heH
      have hepos : (e.card : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) (hmin e heH)))
      calc
        (∑ v ∈ e,
            𝔼 χ : V → Bool,
              indicator (AlmostMonoAt χ e v) / (e.card : ℚ)) =
            ∑ v ∈ e,
              (𝔼 χ : V → Bool,
                indicator (AlmostMonoAt χ e v)) / (e.card : ℚ) := by
                  apply Finset.sum_congr rfl
                  intro v hv
                  rw [Finset.expect_div]
        _ = ∑ _v ∈ e,
              (2 / (2 : ℚ) ^ (e.card - 1)) / (e.card : ℚ) := by
                apply Finset.sum_congr rfl
                intro v hv
                rw [expect_indicator_almostMonoAt e hv (hmin e heH)]
        _ = 2 / (2 : ℚ) ^ (e.card - 1) := by
              simp only [Finset.sum_const, nsmul_eq_mul]
              field_simp [hepos]
    _ = 2 * DGKWeight.qWeightQ H := by
      calc
        (∑ e ∈ H, 2 / (2 : ℚ) ^ (e.card - 1)) =
            ∑ e ∈ H, 4 * (2 : ℚ) ^ (-(e.card : ℤ)) := by
          apply Finset.sum_congr rfl
          intro e heH
          have hecard := hmin e heH
          exact (four_mul_zpow_neg_eq_two_div_pow_pred e.card
            (by omega : 1 ≤ e.card)).symm
        _ = 4 * DGKWeight.booleanWeightQ H := by
          unfold DGKWeight.booleanWeightQ
          rw [Finset.mul_sum]
        _ = 2 * DGKWeight.qWeightQ H := by
          unfold DGKWeight.qWeightQ
          ring

/-- The same statistic evaluated on the initial-colour coordinate of a full
DGK outcome. -/
noncomputable def outcomeAlmostPairMassQ {V : Type*} [DecidableEq V] {N : ℕ}
    (H : Hypergraph V) (w : DGKPriorities.Outcome V N) : ℚ :=
  almostPairMassQ H (initialColour w)

lemma outcomeAlmostPairMassQ_nonneg {V : Type*} [DecidableEq V] {N : ℕ}
    (H : Hypergraph V) (w : DGKPriorities.Outcome V N) :
    0 ≤ outcomeAlmostPairMassQ H w :=
  almostPairMassQ_nonneg H (initialColour w)

/-- Exact expectation on the full finite colour--priority sample space. -/
theorem expect_outcomeAlmostPairMassQ
    {V : Type*} [Fintype V] [DecidableEq V]
    {N : ℕ} (hN : 0 < N) (H : Hypergraph V)
    (hmin : ∀ e ∈ H, 2 ≤ e.card) :
    (𝔼 w : DGKPriorities.Outcome V N, outcomeAlmostPairMassQ H w) =
      2 * DGKWeight.qWeightQ H := by
  unfold outcomeAlmostPairMassQ
  rw [expect_colourStatistic hN (almostPairMassQ H)]
  exact expect_almostPairMassQ H hmin

/-- Generic rational Markov estimate for the almost-pair mass. -/
theorem expect_indicator_outcomeAlmostPairMassQ_ge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {N : ℕ} (hN : 0 < N) (H : Hypergraph V)
    (hmin : ∀ e ∈ H, 2 ≤ e.card) {a : ℚ} (ha : 0 < a) :
    (𝔼 w : DGKPriorities.Outcome V N,
        indicator (a ≤ outcomeAlmostPairMassQ H w)) ≤
      (2 * DGKWeight.qWeightQ H) / a := by
  calc
    (𝔼 w : DGKPriorities.Outcome V N,
        indicator (a ≤ outcomeAlmostPairMassQ H w)) ≤
        (𝔼 w : DGKPriorities.Outcome V N,
          outcomeAlmostPairMassQ H w) / a :=
      expect_indicator_le_of_pos (outcomeAlmostPairMassQ H) a ha
        (outcomeAlmostPairMassQ_nonneg H)
    _ = (2 * DGKWeight.qWeightQ H) / a := by
      rw [expect_outcomeAlmostPairMassQ hN H hmin]

/-- At cutoff `16Q`, the concrete almost-pair bad event has probability at
most `1/8`. -/
theorem almostPairMass_bad_le_one_eighth
    {V : Type*} [Fintype V] [DecidableEq V]
    {N Q : ℕ} (H : Hypergraph V) (hN : 0 < N) (hQ : 0 < Q)
    (hmin : ∀ e ∈ H, 2 ≤ e.card)
    (hq : DGKWeight.qWeightQ H ≤ Q) :
    (𝔼 w : DGKPriorities.Outcome V N,
        indicator (((16 * Q : ℕ) : ℚ) ≤ outcomeAlmostPairMassQ H w)) ≤
      (1 : ℚ) / 8 := by
  calc
    (𝔼 w : DGKPriorities.Outcome V N,
        indicator (((16 * Q : ℕ) : ℚ) ≤ outcomeAlmostPairMassQ H w)) ≤
        (2 * DGKWeight.qWeightQ H) / (16 * Q : ℕ) :=
      expect_indicator_outcomeAlmostPairMassQ_ge_le hN H hmin (by positivity)
    _ ≤ (2 * (Q : ℚ)) / (16 * Q : ℕ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = (1 : ℚ) / 8 := by
      have hQr : (Q : ℚ) ≠ 0 := by positivity
      field_simp [hQr]
      push_cast
      ring

end Erdos1027.DGKBadEvents

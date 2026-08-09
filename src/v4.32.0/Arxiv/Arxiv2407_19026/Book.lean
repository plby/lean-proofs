import Arxiv.Arxiv2407_19026.EasyBound
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pochhammer

/-!
# The optimized book argument

This file formalizes Section 3 of arXiv:2407.19026.
-/

open Finset

noncomputable section

namespace Arxiv2407_19026

lemma densityBetween_mul_card_right {V : Type*} (G : SimpleGraph V)
    {X : Finset V} (hX : X.Nonempty) (Y : Finset V) :
    densityBetween G X Y * Y.card =
      (redEdgesBetween G X Y : ℝ) / X.card := by
  classical
  by_cases hY : Y = ∅
  · subst Y
    simp [densityBetween, redEdgesBetween]
  · have hx0 : (X.card : ℝ) ≠ 0 := by
      exact_mod_cast hX.card_ne_zero
    have hy0 : (Y.card : ℝ) ≠ 0 := by
      exact_mod_cast card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hY)
    rw [densityBetween]
    field_simp

/-- Lemma `l:FpAvg2`: the weighted average of the red-neighborhood
densities is at least the original density. -/
theorem density_averaging {V : Type*} (G : SimpleGraph V)
    (C : Candidate G) :
    (redEdgesBetween G C.X C.Y : ℝ) * C.density ≤
      ∑ v ∈ C.X,
        densityBetween G C.X (redNeighborsIn G v C.Y) *
          (redNeighborsIn G v C.Y).card := by
  classical
  have hx : 0 < (C.X.card : ℝ) := by
    exact_mod_cast C.card_X_pos
  have hy : 0 < (C.Y.card : ℝ) := by
    exact_mod_cast C.card_Y_pos
  have hsumEdges :
      (∑ v ∈ C.X,
          (redEdgesBetween G C.X (redNeighborsIn G v C.Y) : ℝ)) =
        ∑ y ∈ C.Y, ((redNeighborsIn G y C.X).card : ℝ) ^ 2 := by
    exact_mod_cast sum_redEdgesBetween_redNeighborsIn G C.X C.Y
  have hsumDegrees :
      (∑ y ∈ C.Y, ((redNeighborsIn G y C.X).card : ℝ)) =
        redEdgesBetween G C.X C.Y := by
    calc
      (∑ y ∈ C.Y, ((redNeighborsIn G y C.X).card : ℝ)) =
          redEdgesBetween G C.Y C.X := by
        exact_mod_cast sum_card_redNeighborsIn G C.Y C.X
      _ = redEdgesBetween G C.X C.Y := by
        exact_mod_cast redEdgesBetween_comm G C.Y C.X
  have hcauchy :
      (redEdgesBetween G C.X C.Y : ℝ) ^ 2 ≤
        C.Y.card *
          ∑ y ∈ C.Y, ((redNeighborsIn G y C.X).card : ℝ) ^ 2 := by
    have h :=
      sq_sum_le_card_mul_sum_sq
        (s := C.Y) (f := fun y ↦ ((redNeighborsIn G y C.X).card : ℝ))
    simpa [hsumDegrees] using h
  have hmain :
      (redEdgesBetween G C.X C.Y : ℝ) ^ 2 /
          ((C.X.card : ℝ) * C.Y.card) ≤
        (∑ y ∈ C.Y, ((redNeighborsIn G y C.X).card : ℝ) ^ 2) /
          C.X.card := by
    rw [div_le_div_iff₀ (mul_pos hx hy) hx]
    have h := mul_le_mul_of_nonneg_left hcauchy (le_of_lt hx)
    nlinarith
  calc
    (redEdgesBetween G C.X C.Y : ℝ) * C.density =
        (redEdgesBetween G C.X C.Y : ℝ) ^ 2 /
          ((C.X.card : ℝ) * C.Y.card) := by
      rw [Candidate.density, densityBetween]
      ring
    _ ≤ (∑ y ∈ C.Y, ((redNeighborsIn G y C.X).card : ℝ) ^ 2) /
          C.X.card := hmain
    _ = ∑ v ∈ C.X,
          densityBetween G C.X (redNeighborsIn G v C.Y) *
            (redNeighborsIn G v C.Y).card := by
      rw [← hsumEdges, sum_div]
      apply sum_congr rfl
      intro v hv
      exact (densityBetween_mul_card_right G C.X_nonempty
        (redNeighborsIn G v C.Y)).symm

lemma excessBetween_eq_density {V : Type*} (G : SimpleGraph V)
    (p : ℝ) (X Y : Finset V) :
    excessBetween p G X Y =
      (X.card : ℝ) * Y.card * (densityBetween G X Y - p) := by
  classical
  by_cases hX : X = ∅
  · subst X
    simp [excessBetween, densityBetween, redEdgesBetween]
  · by_cases hY : Y = ∅
    · subst Y
      simp [excessBetween, densityBetween, redEdgesBetween]
    · have hx0 : (X.card : ℝ) ≠ 0 := by
        exact_mod_cast card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hX)
      have hy0 : (Y.card : ℝ) ≠ 0 := by
        exact_mod_cast card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hY)
      rw [excessBetween, densityBetween]
      field_simp

/-- Density form of the partition inequality used in equation `e:moment2`.
The final `|Y'|` bounds the contribution of the pivot vertex. -/
lemma density_partition_le {V : Type*} (G : SimpleGraph V)
    (p : ℝ) (hp : 0 ≤ p) {X : Finset V} {v : V} (hv : v ∈ X)
    (Y' : Finset V) :
    (X.card : ℝ) * Y'.card * (densityBetween G X Y' - p) ≤
      ((redNeighborsIn G v X).card : ℝ) * Y'.card *
          (densityBetween G (redNeighborsIn G v X) Y' - p) +
        ((blueNeighborsIn G v X).card : ℝ) * Y'.card *
          (densityBetween G (blueNeighborsIn G v X) Y' - p) +
        Y'.card := by
  have hpart := excessBetween_partition_neighbors p G hv Y'
  have hpivot := excessBetween_singleton_le_card p hp G v Y'
  rw [← excessBetween_eq_density G p X Y',
    ← excessBetween_eq_density G p (redNeighborsIn G v X) Y',
    ← excessBetween_eq_density G p (blueNeighborsIn G v X) Y']
  linarith

/-- Vertices of `X` joined by blue edges to every vertex of `S`. -/
def commonBlueNeighborsIn {V : Type*} (G : SimpleGraph V)
    (S X : Finset V) : Finset V := by
  classical
  exact X.filter fun v ↦ ∀ u ∈ S, u ≠ v ∧ ¬G.Adj u v

@[simp]
lemma mem_commonBlueNeighborsIn {V : Type*} (G : SimpleGraph V)
    (S X : Finset V) (v : V) :
    v ∈ commonBlueNeighborsIn G S X ↔
      v ∈ X ∧ ∀ u ∈ S, u ≠ v ∧ ¬G.Adj u v := by
  classical
  simp [commonBlueNeighborsIn]

/-- A blue book with spine `S` and pages `T`. -/
def IsBlueBook {V : Type*} (G : SimpleGraph V)
    (S T : Finset V) : Prop :=
  G.IsIndepSet (S : Set V) ∧ Disjoint S T ∧
    ∀ u ∈ S, ∀ v ∈ T, ¬G.Adj u v

lemma isBlueBook_commonBlueNeighborsIn {V : Type*} (G : SimpleGraph V)
    {U X S : Finset V} (hU : G.IsIndepSet (U : Set V))
    (hSU : S ⊆ U) (hUX : Disjoint U X) :
    IsBlueBook G S (commonBlueNeighborsIn G S X) := by
  classical
  refine ⟨hU.mono ?_, hUX.mono hSU ?_, ?_⟩
  · intro u hu
    exact hSU hu
  · exact filter_subset _ _
  · intro u hu v hv
    exact (mem_commonBlueNeighborsIn G S X v).1 hv |>.2 u hu |>.2

/-- The double-counting identity at the heart of Lemma `l:BBook`. -/
lemma sum_card_commonBlueNeighborsIn_powersetCard {V : Type*}
    (G : SimpleGraph V) (U X : Finset V) (b : ℕ) :
    ∑ S ∈ U.powersetCard b, (commonBlueNeighborsIn G S X).card =
      ∑ v ∈ X, (blueNeighborsIn G v U).card.choose b := by
  classical
  simp only [commonBlueNeighborsIn, card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  have hfilter :
      (U.powersetCard b).filter
          (fun S ↦ ∀ u ∈ S, u ≠ v ∧ ¬G.Adj u v) =
        (blueNeighborsIn G v U).powersetCard b := by
    ext S
    rw [mem_filter, mem_powersetCard, mem_powersetCard]
    constructor
    · rintro ⟨⟨hSU, hcard⟩, hblue⟩
      refine ⟨?_, hcard⟩
      intro u hu
      have hu' := hblue u hu
      rw [mem_blueNeighborsIn]
      exact ⟨hSU hu, Ne.symm hu'.1, by simpa [G.adj_comm] using hu'.2⟩
    · rintro ⟨hSB, hcard⟩
      refine ⟨⟨?_, hcard⟩, ?_⟩
      · intro u hu
        exact (mem_blueNeighborsIn G v u U).1 (hSB hu) |>.1
      · intro u hu
        have hu' := (mem_blueNeighborsIn G v u U).1 (hSB hu)
        exact ⟨Ne.symm hu'.2.1, by
          simpa [G.adj_comm] using hu'.2.2⟩
  rw [← card_powersetCard]
  rw [← hfilter]
  simp

/-- An averaging consequence of the preceding double count. -/
lemma exists_commonBlueNeighborsIn_of_choose_mul_le_sum {V : Type*}
    (G : SimpleGraph V) (U X : Finset V) {b q : ℕ} (hb : b ≤ U.card)
    (hsum :
      U.card.choose b * q ≤
        ∑ v ∈ X, (blueNeighborsIn G v U).card.choose b) :
    ∃ S : Finset V, S ⊆ U ∧ S.card = b ∧
      q ≤ (commonBlueNeighborsIn G S X).card := by
  classical
  have hP : (U.powersetCard b).Nonempty :=
    powersetCard_nonempty_of_le hb
  rw [← sum_card_commonBlueNeighborsIn_powersetCard] at hsum
  by_contra hnone
  push Not at hnone
  have hlt :
      (∑ S ∈ U.powersetCard b,
          (commonBlueNeighborsIn G S X).card) <
        ∑ S ∈ U.powersetCard b, q := by
    exact sum_lt_sum_of_nonempty hP fun S hS ↦ by
      have hmem := mem_powersetCard.mp hS
      exact hnone S hmem.1 hmem.2
  have hcardP : (U.powersetCard b).card = U.card.choose b :=
    card_powersetCard b U
  have hlt' :
      (∑ S ∈ U.powersetCard b,
          (commonBlueNeighborsIn G S X).card) <
        U.card.choose b * q := by
    simpa [sum_const, hcardP] using hlt
  omega

/-- Real-valued version of the same averaging consequence. -/
lemma exists_commonBlueNeighborsIn_of_real_choose_mul_le_sum {V : Type*}
    (G : SimpleGraph V) (U X : Finset V) {b : ℕ} {q : ℝ}
    (hb : b ≤ U.card)
    (hsum :
      (U.card.choose b : ℝ) * q ≤
        ∑ v ∈ X, (blueNeighborsIn G v U).card.choose b) :
    ∃ S : Finset V, S ⊆ U ∧ S.card = b ∧
      q ≤ (commonBlueNeighborsIn G S X).card := by
  classical
  have hP : (U.powersetCard b).Nonempty :=
    powersetCard_nonempty_of_le hb
  have hsum' :
      (U.card.choose b : ℝ) * q ≤
        ∑ S ∈ U.powersetCard b,
          ((commonBlueNeighborsIn G S X).card : ℝ) := by
    exact hsum.trans_eq (by
      exact_mod_cast
        (sum_card_commonBlueNeighborsIn_powersetCard G U X b).symm)
  by_contra hnone
  push Not at hnone
  have hlt :
      (∑ S ∈ U.powersetCard b,
          ((commonBlueNeighborsIn G S X).card : ℝ)) <
        ∑ S ∈ U.powersetCard b, q := by
    exact sum_lt_sum_of_nonempty hP fun S hS ↦ by
      have hmem := mem_powersetCard.mp hS
      exact hnone S hmem.1 hmem.2
  have hcardP : (U.powersetCard b).card = U.card.choose b :=
    card_powersetCard b U
  have hlt' :
      (∑ S ∈ U.powersetCard b,
          ((commonBlueNeighborsIn G S X).card : ℝ)) <
        (U.card.choose b : ℝ) * q := by
    simpa [sum_const, hcardP] using hlt
  exact (not_lt_of_ge hsum') hlt'

lemma pow_sub_pred_le_descPochhammer_eval {b : ℕ} {a : ℝ}
    (ha : (b - 1 : ℕ) ≤ a) :
    (a - (b - 1 : ℕ)) ^ b ≤ (descPochhammer ℝ b).eval a := by
  rw [descPochhammer_eval_eq_prod_range]
  calc
    (a - (b - 1 : ℕ)) ^ b =
        ∏ _i ∈ range b, (a - (b - 1 : ℕ)) := by simp
    _ ≤ ∏ i ∈ range b, (a - i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact sub_nonneg.mpr ha
      · intro i hi
        have hib : i ≤ b - 1 := Nat.le_pred_of_lt (mem_range.mp hi)
        have hibR : (i : ℝ) ≤ (b - 1 : ℕ) := by
          exact_mod_cast hib
        linarith

/-- Uniform-weight form of the binomial Jensen inequality. -/
lemma card_mul_descPochhammer_average_le_sum_choose {ι : Type*}
    (T : Finset ι) (hT : T.Nonempty) (d : ι → ℕ)
    {b : ℕ} (hb : b ≠ 0)
    (havg : (b : ℝ) - 1 ≤
      (∑ v ∈ T, (d v : ℝ)) / T.card) :
    (T.card : ℝ) *
        ((descPochhammer ℝ b).eval
          ((∑ v ∈ T, (d v : ℝ)) / T.card) / b.factorial) ≤
      ∑ v ∈ T, (d v).choose b := by
  let w : ι → ℝ := fun _ ↦ 1 / T.card
  have hcard : 0 < (T.card : ℝ) := by
    exact_mod_cast hT.card_pos
  have hw0 : ∀ i ∈ T, 0 ≤ w i := by
    intro i hi
    dsimp [w]
    positivity
  have hw1 : ∑ i ∈ T, w i = 1 := by
    simp [w, sum_const, nsmul_eq_mul, hcard.ne']
  have havg' :
      (b : ℝ) - 1 ≤ ∑ i ∈ T, w i * d i := by
    calc
      (b : ℝ) - 1 ≤
          (∑ v ∈ T, (d v : ℝ)) / T.card := havg
      _ = ∑ i ∈ T, w i * d i := by
        simp only [w, div_eq_mul_inv]
        rw [Finset.sum_mul]
        apply sum_congr rfl
        intro i hi
        ring
  have hj := descPochhammer_eval_div_factorial_le_sum_choose
    hb d w hw0 hw1 havg'
  have hmul := mul_le_mul_of_nonneg_left hj hcard.le
  simpa [w, mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
    hcard.ne']
    using hmul

/-- A convenient consequence of binomial Jensen: subtracting `b - 1`
from the average degree gives a pointwise lower bound for every factor of
the descending factorial. -/
lemma card_mul_pow_average_sub_pred_le_sum_choose {ι : Type*}
    (T : Finset ι) (hT : T.Nonempty) (d : ι → ℕ)
    {b : ℕ} (hb : b ≠ 0)
    (havg : (b - 1 : ℕ) ≤
      (∑ v ∈ T, (d v : ℝ)) / T.card) :
    (T.card : ℝ) *
        (((∑ v ∈ T, (d v : ℝ)) / T.card - (b - 1 : ℕ)) ^ b /
          b.factorial) ≤
      ∑ v ∈ T, (d v).choose b := by
  have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
  have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    rw [Nat.cast_sub hb1]
    norm_num
  have hpoch :=
    card_mul_descPochhammer_average_le_sum_choose T hT d hb
      (by simpa [hcast] using havg)
  have hpow := pow_sub_pred_le_descPochhammer_eval havg
  have hfac : 0 ≤ (b.factorial : ℝ) := by positivity
  have hdiv :
      ((∑ v ∈ T, (d v : ℝ)) / T.card - (b - 1 : ℕ)) ^ b /
          b.factorial ≤
        (descPochhammer ℝ b).eval
            ((∑ v ∈ T, (d v : ℝ)) / T.card) /
          b.factorial :=
    div_le_div_of_nonneg_right hpow hfac
  exact (mul_le_mul_of_nonneg_left hdiv (by positivity)).trans hpoch

lemma four_fifths_le_one_sub_inv_five_mul_pow {b : ℕ} (hb : b ≠ 0) :
    (4 / 5 : ℝ) ≤ (1 - 1 / (5 * b)) ^ b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (Nat.pos_of_ne_zero hb)
  have hbR1 : (1 : ℝ) ≤ b := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hb)
  have harg : (-2 : ℝ) ≤ -(1 / (5 * b)) := by
    have hinv : (1 : ℝ) / (5 * b) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      nlinarith [hbR1]
    linarith
  have hbern := one_add_mul_le_pow harg b
  have hleft : (1 : ℝ) + b * -(1 / (5 * b)) = 4 / 5 := by
    field_simp
    ring
  have hright : (1 : ℝ) + -(1 / (5 * b)) =
      1 - 1 / (5 * b) := by ring
  rwa [hleft, hright] at hbern

/-- The numerical heart of Lemma `l:BBook`.  This formulation separates
the incidence estimate from the convexity and constant estimates. -/
lemma choose_mul_half_le_sum_choose_of_average {ι : Type*}
    (T : Finset ι) (hT : T.Nonempty) (d : ι → ℕ)
    (μ N : ℝ) (m b : ℕ) (hb : b ≠ 0) (hμ : 0 < μ) (hN : 0 ≤ N)
    (hTcard : (4 / 5 : ℝ) * N ≤ T.card)
    (havg :
      μ * m * (1 - 1 / (5 * (b : ℝ))) + (b - 1 : ℕ) ≤
        (∑ v ∈ T, (d v : ℝ)) / T.card) :
    (m.choose b : ℝ) * (μ ^ b / 2 * N) ≤
      ∑ v ∈ T, (d v).choose b := by
  let c : ℝ := 1 - 1 / (5 * (b : ℝ))
  let A : ℝ := (∑ v ∈ T, (d v : ℝ)) / T.card
  have hbR1 : (1 : ℝ) ≤ b := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hb)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    have hinv : (1 : ℝ) / (5 * b) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      nlinarith
    linarith
  have hbase0 : 0 ≤ μ * m * c := by positivity
  have havg' :
      μ * m * c + (b - 1 : ℕ) ≤ A := by
    simpa [c, A] using havg
  have hpred : ((b - 1 : ℕ) : ℝ) ≤ A := by
    linarith
  have hsub : μ * m * c ≤ A - (b - 1 : ℕ) := by
    linarith
  have hpow :
      (μ * m * c) ^ b ≤ (A - (b - 1 : ℕ)) ^ b :=
    pow_le_pow_left₀ hbase0 hsub b
  have hmoment :=
    card_mul_pow_average_sub_pred_le_sum_choose T hT d hb
      (by simpa [A] using hpred)
  have hfac0 : 0 ≤ (b.factorial : ℝ) := by positivity
  have hmoment' :
      (T.card : ℝ) * ((μ * m * c) ^ b / b.factorial) ≤
        ∑ v ∈ T, (d v).choose b := by
    exact (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hpow hfac0) (by positivity)).trans
        (by simpa [A] using hmoment)
  have hc : (4 / 5 : ℝ) ≤ c ^ b := by
    simpa [c] using four_fifths_le_one_sub_inv_five_mul_pow hb
  have hfourN : 0 ≤ (4 / 5 : ℝ) * N := by positivity
  have hfour : 0 ≤ (4 / 5 : ℝ) := by norm_num
  have hfactor :
      N / 2 ≤ (T.card : ℝ) * c ^ b := by
    have hprod :=
      mul_le_mul hTcard hc hfour (by positivity : (0 : ℝ) ≤ T.card)
    have hhalf :
        N / 2 ≤ ((4 / 5 : ℝ) * N) * (4 / 5 : ℝ) := by
      nlinarith
    exact hhalf.trans hprod
  have hpowfac : 0 ≤ (μ * m) ^ b / (b.factorial : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hfactor hpowfac
  have hchoose : (m.choose b : ℝ) ≤
      (m : ℝ) ^ b / b.factorial :=
    Nat.choose_le_pow_div b m
  have hleftScale : 0 ≤ μ ^ b / 2 * N := by positivity
  calc
    (m.choose b : ℝ) * (μ ^ b / 2 * N) ≤
        ((m : ℝ) ^ b / b.factorial) * (μ ^ b / 2 * N) :=
      mul_le_mul_of_nonneg_right hchoose hleftScale
    _ = (N / 2) * ((μ * m) ^ b / b.factorial) := by
      rw [mul_pow]
      ring
    _ ≤ ((T.card : ℝ) * c ^ b) *
        ((μ * m) ^ b / b.factorial) := hscaled
    _ = (T.card : ℝ) * ((μ * m * c) ^ b / b.factorial) := by
      rw [mul_pow, mul_pow]
      ring
    _ ≤ ∑ v ∈ T, (d v).choose b := hmoment'

lemma card_blueNeighborsIn_le_sdiff_add_card {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (v : V) (X U : Finset V) :
    (blueNeighborsIn G v X).card ≤
      (blueNeighborsIn G v (X \ U)).card + U.card := by
  classical
  have hsub :
      blueNeighborsIn G v X ⊆
        blueNeighborsIn G v (X \ U) ∪ U := by
    intro u hu
    by_cases huU : u ∈ U
    · exact mem_union_right _ huU
    · apply mem_union_left
      rw [mem_blueNeighborsIn] at hu ⊢
      exact ⟨mem_sdiff.mpr ⟨hu.1, huU⟩, hu.2⟩
  exact (card_le_card hsub).trans (card_union_le _ _)

lemma sum_card_blueNeighborsIn_comm {V : Type*} (G : SimpleGraph V)
    (U Z : Finset V) :
    ∑ u ∈ U, (blueNeighborsIn G u Z).card =
      ∑ z ∈ Z, (blueNeighborsIn G z U).card := by
  calc
    ∑ u ∈ U, (blueNeighborsIn G u Z).card =
        redEdgesBetween Gᶜ U Z := sum_card_redNeighborsIn Gᶜ U Z
    _ = redEdgesBetween Gᶜ Z U := redEdgesBetween_comm Gᶜ U Z
    _ = ∑ z ∈ Z, (blueNeighborsIn G z U).card :=
      (sum_card_redNeighborsIn Gᶜ Z U).symm

/-- Summing high blue degrees over `U` and deleting `U` loses at most
`|U|²` incidences. -/
lemma blue_incidence_lower_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (X U : Finset V) (μ : ℝ) (m : ℕ) (hUm : U.card = m)
    (hhigh : ∀ u ∈ U,
      μ * X.card ≤ (blueNeighborsIn G u X).card) :
    (m : ℝ) * (μ * X.card - m) ≤
      ∑ z ∈ X \ U, ((blueNeighborsIn G z U).card : ℝ) := by
  have hu : ∀ u ∈ U,
      μ * X.card - m ≤
        ((blueNeighborsIn G u (X \ U)).card : ℝ) := by
    intro u huU
    have hcard := card_blueNeighborsIn_le_sdiff_add_card G u X U
    have hhigh' := hhigh u huU
    rw [hUm] at hcard
    have hcardR :
        ((blueNeighborsIn G u X).card : ℝ) ≤
          (blueNeighborsIn G u (X \ U)).card + m := by
      exact_mod_cast hcard
    linarith
  have hsum := sum_le_sum hu
  have hcommR :
      (∑ u ∈ U, ((blueNeighborsIn G u (X \ U)).card : ℝ)) =
        ∑ z ∈ X \ U, ((blueNeighborsIn G z U).card : ℝ) := by
    exact_mod_cast sum_card_blueNeighborsIn_comm G U (X \ U)
  rw [hcommR] at hsum
  simp only [sum_const, nsmul_eq_mul, hUm] at hsum
  nlinarith

/-- The size and average-degree estimates used after finding the blue
`m`-clique in Lemma `l:BBook`. -/
lemma blue_incidence_average_bounds {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (X U : Finset V) (μ : ℝ) (m b : ℕ)
    (hμ : 0 < μ) (hb : b ≠ 0)
    (hm : 5 * μ⁻¹ * (b : ℝ) ^ 2 ≤ m)
    (hX : 5 * m ^ 2 ≤ X.card)
    (hUX : U ⊆ X) (hUm : U.card = m)
    (hhigh : ∀ u ∈ U,
      μ * X.card ≤ (blueNeighborsIn G u X).card) :
    (X \ U).Nonempty ∧
      (4 / 5 : ℝ) * X.card ≤ (X \ U).card ∧
      μ * m * (1 - 1 / (5 * (b : ℝ))) + (b - 1 : ℕ) ≤
        (∑ z ∈ X \ U, ((blueNeighborsIn G z U).card : ℝ)) /
          (X \ U).card := by
  have hbNat : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hbNat
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hbm : 5 * (b : ℝ) ^ 2 ≤ μ * m := by
    calc
      5 * (b : ℝ) ^ 2 =
          μ * (5 * μ⁻¹ * (b : ℝ) ^ 2) := by
            field_simp
      _ ≤ μ * m := mul_le_mul_of_nonneg_left hm hμ.le
  have hm0 : m ≠ 0 := by
    intro hmzero
    subst m
    rw [hmzero] at hbm
    norm_num at hbm
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (Nat.pos_of_ne_zero hb)
    nlinarith [sq_pos_of_pos hbpos]
  have hmNat : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmNat
  have hXr : 5 * (m : ℝ) ^ 2 ≤ (X.card : ℝ) := by
    exact_mod_cast hX
  have hmX : m ≤ X.card := by
    calc
      m ≤ 5 * m ^ 2 := by nlinarith
      _ ≤ X.card := hX
  have hcardZ :
      (((X \ U).card : ℕ) : ℝ) = X.card - m := by
    rw [card_sdiff_of_subset hUX, hUm, Nat.cast_sub hmX]
  have hXpos : (0 : ℝ) < X.card := by
    have : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (by omega : m ≠ 0))
    nlinarith [sq_pos_of_pos this]
  have hZcard :
      (4 / 5 : ℝ) * X.card ≤ (X \ U).card := by
    rw [hcardZ]
    have hmm : (m : ℝ) ≤ m ^ 2 := by nlinarith
    nlinarith
  have hZpos : (0 : ℝ) < (X \ U).card := by
    nlinarith
  have hZ : (X \ U).Nonempty := by
    apply card_pos.mp
    exact_mod_cast hZpos
  refine ⟨hZ, hZcard, ?_⟩
  let Q : ℝ :=
    μ * m * (1 - 1 / (5 * (b : ℝ))) + (b - 1 : ℕ)
  have hc0 : 0 ≤ (1 - 1 / (5 * (b : ℝ))) := by
    have hinv : (1 : ℝ) / (5 * b) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      nlinarith
    linarith
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hdiv : (b : ℝ) ≤ μ * m / (5 * b) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  have hpredCast : (((b - 1 : ℕ) : ℝ)) = b - 1 := by
    rw [Nat.cast_sub hbNat]
    norm_num
  have hQle : Q ≤ μ * m - 1 := by
    dsimp [Q]
    rw [hpredCast]
    field_simp
    field_simp at hdiv
    nlinarith
  have hZN : ((X \ U).card : ℝ) ≤ X.card := by
    exact_mod_cast card_le_card (sdiff_subset : X \ U ⊆ X)
  have hNmm : (m : ℝ) ^ 2 ≤ X.card := by nlinarith
  have hQmul :
      Q * (X \ U).card ≤ (m : ℝ) * (μ * X.card - m) := by
    calc
      Q * (X \ U).card ≤ Q * X.card :=
        mul_le_mul_of_nonneg_left hZN hQ0
      _ ≤ (μ * m - 1) * X.card :=
        mul_le_mul_of_nonneg_right hQle (by positivity)
      _ ≤ (m : ℝ) * (μ * X.card - m) := by
        nlinarith
  have hsum :=
    blue_incidence_lower_bound G X U μ m hUm hhigh
  apply (le_div_iff₀ hZpos).2
  exact hQmul.trans hsum

/-- Lemma `l:BBook`: many vertices of high blue degree force either a red
clique or a large blue book.  The spine has exactly `b` vertices, which is
slightly stronger than the paper's `|S| ≥ b` conclusion. -/
theorem redClique_or_large_blueBook {V : Type*}
    (G : SimpleGraph V) (X W : Finset V) (μ : ℝ) (k m b : ℕ)
    (hμ : 0 < μ) (hμ1 : μ < 1) (hb : b ≠ 0)
    (hm : 5 * μ⁻¹ * (b : ℝ) ^ 2 ≤ m)
    (hX : 5 * m ^ 2 ≤ X.card)
    (hWX : W ⊆ X) (hW : ramseyNumber k m ≤ W.card)
    (hhigh : ∀ v ∈ W,
      μ * X.card ≤ (blueNeighborsIn G v X).card) :
    Candidate.ContainsRedClique (G := G) X k ∨
      ∃ S T : Finset V, S ⊆ X ∧ T ⊆ X ∧
        IsBlueBook G S T ∧ S.card = b ∧
          μ ^ b / 2 * X.card ≤ T.card := by
  classical
  have hbNat : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hbNat
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hbm : 5 * (b : ℝ) ^ 2 ≤ μ * m := by
    calc
      5 * (b : ℝ) ^ 2 =
          μ * (5 * μ⁻¹ * (b : ℝ) ^ 2) := by field_simp
      _ ≤ μ * m := mul_le_mul_of_nonneg_left hm hμ.le
  have hm0 : m ≠ 0 := by
    intro hmzero
    subst m
    norm_num at hbm
    have hbpos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
    nlinarith [sq_pos_of_pos hbpos]
  have hmR0 : (0 : ℝ) ≤ m := by positivity
  have hμm : μ * m ≤ (m : ℝ) :=
    mul_le_of_le_one_left hmR0 hμ1.le
  have hbmNat : b ≤ m := by
    have : (b : ℝ) ≤ m := by
      nlinarith [sq_nonneg ((b : ℝ) - 1)]
    exact_mod_cast this
  rcases red_or_blue_of_ramseyProperty W
      (Ramsey.ramseyProperty_of_ramseyNumber_le hW) with
    ⟨K, hKW, hK⟩ | ⟨U, hUW, hU⟩
  · exact Or.inl ⟨K, hKW.trans hWX, hK⟩
  · have hUX : U ⊆ X := hUW.trans hWX
    have hhighU : ∀ u ∈ U,
        μ * X.card ≤ (blueNeighborsIn G u X).card :=
      fun u hu ↦ hhigh u (hUW hu)
    obtain ⟨hZ, hZcard, havg⟩ :=
      blue_incidence_average_bounds G X U μ m b hμ hb hm hX hUX
        hU.card_eq hhighU
    have hmoment :=
      choose_mul_half_le_sum_choose_of_average
        (X \ U) hZ
        (fun z ↦ (blueNeighborsIn G z U).card)
        μ X.card m b hb hμ (by positivity) hZcard havg
    have hmoment' :
        (U.card.choose b : ℝ) * (μ ^ b / 2 * X.card) ≤
          ∑ z ∈ X \ U, (blueNeighborsIn G z U).card.choose b := by
      simpa [hU.card_eq] using hmoment
    obtain ⟨S, hSU, hScard, hTcard⟩ :=
      exists_commonBlueNeighborsIn_of_real_choose_mul_le_sum
        G U (X \ U) (hU.card_eq ▸ hbmNat) hmoment'
    let T := commonBlueNeighborsIn G S (X \ U)
    have hdisj : Disjoint U (X \ U) := Finset.disjoint_sdiff
    have hbook : IsBlueBook G S T :=
      isBlueBook_commonBlueNeighborsIn G hU.isIndepSet hSU hdisj
    refine Or.inr ⟨S, T, hSU.trans hUX, ?_, hbook, hScard, ?_⟩
    · intro v hv
      have hv' : v ∈ commonBlueNeighborsIn G S (X \ U) := by
        simpa [T] using hv
      exact sdiff_subset
        ((mem_commonBlueNeighborsIn G S (X \ U) v).1 hv' |>.1)
    · simpa [T] using hTcard

lemma isNIndepSet_union_of_blueBook {V : Type*} [DecidableEq V]
    (G : SimpleGraph V)
    {S T K : Finset V} {q : ℕ}
    (hbook : IsBlueBook G S T) (hKT : K ⊆ T)
    (hK : G.IsNIndepSet q K) :
    G.IsNIndepSet (S.card + q) (S ∪ K) := by
  classical
  rw [SimpleGraph.isNIndepSet_iff] at hK ⊢
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.isIndepSet_iff]
    have hS := (SimpleGraph.isIndepSet_iff G).1 hbook.1
    have hKI := (SimpleGraph.isIndepSet_iff G).1 hK.1
    intro u hu v hv huv
    change u ∈ S ∪ K at hu
    change v ∈ S ∪ K at hv
    rw [mem_union] at hu hv
    rcases hu with huS | huK <;> rcases hv with hvS | hvK
    · exact hS huS hvS huv
    · exact hbook.2.2 u huS v (hKT hvK)
    · simpa [G.adj_comm] using hbook.2.2 v hvS u (hKT huK)
    · exact hKI huK hvK huv
  · have hSK : Disjoint S K := hbook.2.1.mono_right hKT
    rw [card_union_of_disjoint hSK, hK.2]

/-- The lifting step used after a big-blue-step extraction in
`t:bookmain`. -/
lemma Candidate.good_of_blueBook_pages_good {V : Type*} {G : SimpleGraph V}
    (C D : Candidate G) {S : Finset V} {k l t b : ℕ}
    (hDX : D.X ⊆ C.X) (hDY : D.Y ⊆ C.Y)
    (hSX : S ⊆ C.X) (hbook : IsBlueBook G S D.X)
    (hScard : S.card = b) (hbt : b ≤ t)
    (hgood : D.Good k l (t - b)) :
    C.Good k l t := by
  classical
  rcases hgood with hred | hblueX | hblueY
  · exact Or.inl (Candidate.containsRedClique_mono
      (union_subset_union hDX hDY) hred)
  · rcases hblueX with ⟨K, hKD, hK⟩
    refine Or.inr (Or.inl ⟨S ∪ K, ?_, ?_⟩)
    · exact union_subset hSX (hKD.trans hDX)
    · have h :=
        isNIndepSet_union_of_blueBook G hbook hKD hK
      simpa [hScard, Nat.add_sub_of_le hbt] using h
  · exact Or.inr (Or.inr
      (Candidate.containsBlueClique_mono hDY hblueY))

/-- The finite combinatorial core of Lemma `l:BBook`.  Its final hypothesis
is precisely the binomial-moment estimate proved by the numerical part of
that lemma. -/
theorem redClique_or_blueBook_of_choose_bound {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (X W : Finset V) {k m b q : ℕ}
    (hWX : W ⊆ X) (hW : ramseyNumber k m ≤ W.card) (hb : b ≤ m)
    (hchoose : ∀ U : Finset V, U ⊆ W → U.card = m →
      G.IsIndepSet (U : Set V) →
      m.choose b * q ≤
        ∑ v ∈ X \ U, (blueNeighborsIn G v U).card.choose b) :
    Candidate.ContainsRedClique (G := G) X k ∨
      ∃ S T : Finset V, S ⊆ X ∧ T ⊆ X ∧
        IsBlueBook G S T ∧ S.card = b ∧ q ≤ T.card := by
  classical
  rcases red_or_blue_of_ramseyProperty W
      (Ramsey.ramseyProperty_of_ramseyNumber_le hW) with
    ⟨K, hKW, hK⟩ | ⟨U, hUW, hU⟩
  · exact Or.inl ⟨K, hKW.trans hWX, hK⟩
  · have hsum := hchoose U hUW hU.card_eq hU.isIndepSet
    obtain ⟨S, hSU, hScard, hTcard⟩ :=
      exists_commonBlueNeighborsIn_of_choose_mul_le_sum
        G U (X \ U) (hU.card_eq ▸ hb) (by simpa [hU.card_eq] using hsum)
    let T := commonBlueNeighborsIn G S (X \ U)
    have hUX : Disjoint U (X \ U) := by
      exact Finset.disjoint_sdiff
    have hbook : IsBlueBook G S T :=
      isBlueBook_commonBlueNeighborsIn G hU.isIndepSet hSU hUX
    refine Or.inr ⟨S, T, ?_, ?_, hbook, hScard, ?_⟩
    · exact hSU.trans (hUW.trans hWX)
    · intro v hv
      have hv' : v ∈ commonBlueNeighborsIn G S (X \ U) := by
        simpa [T] using hv
      exact sdiff_subset ((mem_commonBlueNeighborsIn G S (X \ U) v).1 hv' |>.1)
    · simpa [T] using hTcard

/-- Logarithmic core of Lemma `l:limit`, written with real powers and with
the constant factor `1 - μ` normalized out. -/
theorem book_limit_normalized {p μ : ℝ} (hp : 0 < p) (hμ : μ < 1) :
    Filter.Tendsto
      (fun r : ℝ ↦
        (1 + (p ^ r⁻¹ - 1) / (1 - μ)) ^ r)
      Filter.atTop
      (nhds (p ^ ((1 : ℝ) / (1 - μ)))) := by
  have ha : 0 < 1 - μ := sub_pos.mpr hμ
  have hroot :
      Filter.Tendsto
        (fun r : ℝ ↦ r * (p ^ r⁻¹ - 1))
        Filter.atTop (nhds (Real.log p)) := by
    have h :=
      (tendsto_rpow_sub_one_log hp).comp
        tendsto_inv_atTop_nhdsGT_zero
    change Filter.Tendsto
      (fun r : ℝ ↦ (r⁻¹)⁻¹ * (p ^ r⁻¹ - 1))
      Filter.atTop (nhds (Real.log p)) at h
    simpa using h
  have hg :
      Filter.Tendsto
        (fun r : ℝ ↦ r * ((p ^ r⁻¹ - 1) / (1 - μ)))
        Filter.atTop (nhds (Real.log p / (1 - μ))) := by
    simpa [div_eq_mul_inv, mul_assoc] using hroot.div_const (1 - μ)
  have hlim := Real.tendsto_one_add_rpow_exp_of_tendsto hg
  convert hlim using 1
  rw [Real.rpow_def_of_pos hp]
  congr 1
  ring_nf

/-- Lemma `l:limit`, using `Real.rpow` for all real exponents. -/
theorem book_limit {p μ : ℝ} (hp : 0 < p) (hμ : μ < 1) :
    Filter.Tendsto
      (fun r : ℝ ↦
        (p ^ r⁻¹ - μ) ^ r * (1 - μ) ^ (1 - r))
      Filter.atTop
      (nhds (p ^ ((1 : ℝ) / (1 - μ)) * (1 - μ))) := by
  have ha : 0 < 1 - μ := sub_pos.mpr hμ
  let z : ℝ → ℝ :=
    fun r ↦ 1 + (p ^ r⁻¹ - 1) / (1 - μ)
  have hinv :
      Filter.Tendsto (fun r : ℝ ↦ r⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_nhdsGT_zero.mono_right inf_le_left
  have hroot :
      Filter.Tendsto (fun r : ℝ ↦ p ^ r⁻¹)
        Filter.atTop (nhds 1) := by
    have h := (Real.continuousAt_const_rpow hp.ne').tendsto.comp hinv
    have h' :
        Filter.Tendsto ((fun x : ℝ ↦ p ^ x) ∘ fun r : ℝ ↦ r⁻¹)
          Filter.atTop (nhds 1) := by
      simpa only [Real.rpow_zero] using h
    exact h'.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hz :
      Filter.Tendsto z Filter.atTop (nhds 1) := by
    dsimp [z]
    have hone :
        Filter.Tendsto (fun _ : ℝ ↦ (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hone.add ((hroot.sub hone).div_const (1 - μ))
  have hzpos : ∀ᶠ r in Filter.atTop, z r ∈ Set.Ioi 0 :=
    hz.eventually (Ioi_mem_nhds zero_lt_one)
  have hznonneg : ∀ᶠ r in Filter.atTop, 0 ≤ z r := by
    filter_upwards [hzpos] with r hr
    exact le_of_lt hr
  have heq : (fun r : ℝ ↦
      (p ^ r⁻¹ - μ) ^ r * (1 - μ) ^ (1 - r)) =ᶠ[Filter.atTop]
      fun r ↦ (1 - μ) * z r ^ r := by
    filter_upwards [hznonneg] with r hzr
    have hfactor :
        p ^ r⁻¹ - μ = (1 - μ) * z r := by
      dsimp [z]
      field_simp
      ring
    rw [hfactor, Real.mul_rpow (le_of_lt ha) hzr]
    calc
      (1 - μ) ^ r * z r ^ r * (1 - μ) ^ (1 - r) =
          ((1 - μ) ^ r * (1 - μ) ^ (1 - r)) * z r ^ r := by ring
      _ = (1 - μ) ^ (r + (1 - r)) * z r ^ r := by
        rw [Real.rpow_add ha]
      _ = (1 - μ) * z r ^ r := by norm_num
  apply Filter.Tendsto.congr' heq.symm
  have hconst :
      Filter.Tendsto (fun _ : ℝ ↦ 1 - μ) Filter.atTop (nhds (1 - μ)) :=
    tendsto_const_nhds
  simpa [z, mul_comm] using
    hconst.mul (book_limit_normalized hp hμ)

/-- A multiplicative formulation of an eventual exponential Ramsey bound.
For positive `x,y`, this says exactly
`R(k,l) ≤ x⁻ᵏ y⁻ˡ` for all sufficiently large `k+l`. -/
def EventuallyRamseyBound (x y : ℝ) : Prop :=
  ∃ N : ℕ, ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → N ≤ k + l →
    (ramseyNumber k l : ℝ) * x ^ k * y ^ l ≤ 1

/-- The pre-closure set used to define `𝓡` in Section 3. -/
def ramseyBoundCore : Set (ℝ × ℝ) :=
  {z | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ z.2 < 1 ∧
    EventuallyRamseyBound z.1 z.2}

/-- The closed asymptotic Ramsey region `𝓡`. -/
def ramseyRegion : Set (ℝ × ℝ) :=
  closure ramseyBoundCore

/-- The interior `𝓡_*` of the asymptotic Ramsey region. -/
def ramseyRegionInterior : Set (ℝ × ℝ) :=
  interior ramseyRegion

lemma eventuallyRamseyBound_elementary (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) :
    EventuallyRamseyBound x (1 - x) := by
  refine ⟨2, fun k l hk hl hkl ↦ ?_⟩
  have hbase :=
    ramseyNumber_mul_weights_le_one x hx0 hx1 k l hk hl
  have hxpow : x ^ k = x ^ (k - 1) * x := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  have hypow : (1 - x) ^ l =
      (1 - x) ^ (l - 1) * (1 - x) := by
    conv_lhs => rw [show l = (l - 1) + 1 by omega, pow_succ]
  have hxy : x * (1 - x) ≤ 1 := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  rw [hxpow, hypow]
  calc
    (ramseyNumber k l : ℝ) * (x ^ (k - 1) * x) *
          ((1 - x) ^ (l - 1) * (1 - x)) =
        ((ramseyNumber k l : ℝ) * x ^ (k - 1) *
          (1 - x) ^ (l - 1)) * (x * (1 - x)) := by ring
    _ ≤ 1 * 1 := mul_le_mul hbase hxy
      (mul_nonneg (le_of_lt hx0) (le_of_lt (sub_pos.mpr hx1))) zero_le_one
    _ = 1 := one_mul 1

lemma eventuallyRamseyBound_mono {x y x' y' : ℝ}
    (hx' : 0 ≤ x') (hxx : x' ≤ x)
    (hy' : 0 ≤ y') (hyy : y' ≤ y)
    (h : EventuallyRamseyBound x y) :
    EventuallyRamseyBound x' y' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun k l hk hl hkl ↦ ?_⟩
  have hx : 0 ≤ x := hx'.trans hxx
  have hy : 0 ≤ y := hy'.trans hyy
  calc
    (ramseyNumber k l : ℝ) * x' ^ k * y' ^ l ≤
        (ramseyNumber k l : ℝ) * x ^ k * y ^ l := by
      gcongr
    _ ≤ 1 := hN k l hk hl hkl

/-- Observation `o:r` (1), before taking closure. -/
lemma elementary_mem_ramseyBoundCore (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) :
    (x, 1 - x) ∈ ramseyBoundCore := by
  exact ⟨hx0, hx1, sub_pos.mpr hx1, by linarith,
    eventuallyRamseyBound_elementary x hx0 hx1⟩

/-- Observation `o:r` (1). -/
lemma elementary_mem_ramseyRegion (x : ℝ) (hx0 : 0 < x)
    (hx1 : x < 1) :
    (x, 1 - x) ∈ ramseyRegion :=
  subset_closure (elementary_mem_ramseyBoundCore x hx0 hx1)

/-- Coordinate monotonicity in Observation `o:r` (2), on the defining
pre-closure set. -/
lemma ramseyBoundCore_mono {x y x' y' : ℝ}
    (h : (x, y) ∈ ramseyBoundCore)
    (hx' : 0 < x') (hxx : x' ≤ x)
    (hy' : 0 < y') (hyy : y' ≤ y) :
    (x', y') ∈ ramseyBoundCore := by
  rcases h with ⟨hx0, hx1, hy0, hy1, hbound⟩
  exact ⟨hx', hxx.trans_lt hx1, hy', hyy.trans_lt hy1,
    eventuallyRamseyBound_mono hx'.le hxx hy'.le hyy hbound⟩

/-- Coordinate monotonicity in Observation `o:r` (2), extended through the
closure defining `𝓡`. -/
lemma ramseyRegion_mono {x y x' y' : ℝ}
    (h : (x, y) ∈ ramseyRegion)
    (hx' : 0 < x') (hxx : x' ≤ x)
    (hy' : 0 < y') (hyy : y' ≤ y) :
    (x', y') ∈ ramseyRegion := by
  have hx : 0 < x := hx'.trans_le hxx
  have hy : 0 < y := hy'.trans_le hyy
  let a := x' / x
  let b := y' / y
  have ha0 : 0 < a := div_pos hx' hx
  have hb0 : 0 < b := div_pos hy' hy
  have ha1 : a ≤ 1 := (div_le_one hx).2 hxx
  have hb1 : b ≤ 1 := (div_le_one hy).2 hyy
  let f : ℝ × ℝ → ℝ × ℝ := fun z ↦ (a * z.1, b * z.2)
  have hf : Continuous f :=
    (continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd)
  have hmaps : Set.MapsTo f ramseyBoundCore ramseyBoundCore := by
    intro z hz
    apply ramseyBoundCore_mono hz
    · exact mul_pos ha0 hz.1
    · nlinarith [hz.1]
    · exact mul_pos hb0 hz.2.2.1
    · nlinarith [hz.2.2.1]
  have himage : f (x, y) ∈ closure ramseyBoundCore :=
    map_mem_closure hf h hmaps
  have hfx : f (x, y) = (x', y') := by
    dsimp [f, a, b]
    field_simp
  simpa [ramseyRegion, hfx] using himage

/-- Observation `o:r` (3): strict coordinate decrease moves a point of
`𝓡` into its interior. -/
lemma strict_mono_mem_ramseyRegionInterior {x y x' y' : ℝ}
    (h : (x, y) ∈ ramseyRegion)
    (hx' : 0 < x') (hxx : x' < x)
    (hy' : 0 < y') (hyy : y' < y) :
    (x', y') ∈ ramseyRegionInterior := by
  let U : Set (ℝ × ℝ) := Set.Ioo 0 x ×ˢ Set.Ioo 0 y
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hmem : (x', y') ∈ U := ⟨⟨hx', hxx⟩, ⟨hy', hyy⟩⟩
  have hsub : U ⊆ ramseyRegion := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ramseyRegion_mono h hu.1 hu.2.le hv.1 hv.2.le
  rw [ramseyRegionInterior, mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hUopen.mem_nhds hmem) hsub

/-- Observation `o:r` (4), with its informal `o(k),o(l)` hypothesis
expressed by the exact consequence used in the proof: every strict positive
coordinate decrease satisfies an eventual exponential Ramsey bound. -/
lemma mem_ramseyRegion_of_strict_eventuallyRamseyBound {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1)
    (hbound : ∀ x' y' : ℝ, 0 < x' → x' < x → 0 < y' → y' < y →
      EventuallyRamseyBound x' y') :
    (x, y) ∈ ramseyRegion := by
  let f : ℝ → ℝ × ℝ := fun r ↦ (x - r⁻¹, y - r⁻¹)
  have hinv :
      Filter.Tendsto (fun r : ℝ ↦ r⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hf : Filter.Tendsto f Filter.atTop (nhds (x, y)) := by
    rw [Prod.tendsto_iff]
    exact ⟨by simpa [f] using hinv.const_sub x,
      by simpa [f] using hinv.const_sub y⟩
  have hmin : 0 < min x y := lt_min hx0 hy0
  have hlt : ∀ᶠ r : ℝ in Filter.atTop, r⁻¹ < min x y :=
    hinv.eventually (Iio_mem_nhds hmin)
  have hpos : ∀ᶠ r : ℝ in Filter.atTop, 0 < r⁻¹ :=
    tendsto_inv_atTop_nhdsGT_zero.eventually self_mem_nhdsWithin
  have hcore : ∀ᶠ r : ℝ in Filter.atTop, f r ∈ ramseyBoundCore := by
    filter_upwards [hlt, hpos] with r hrlt hrpos
    have hrx : r⁻¹ < x := hrlt.trans_le (min_le_left _ _)
    have hry : r⁻¹ < y := hrlt.trans_le (min_le_right _ _)
    refine ⟨sub_pos.mpr hrx, by linarith, sub_pos.mpr hry, by linarith,
      hbound (x - r⁻¹) (y - r⁻¹) (sub_pos.mpr hrx) (by linarith)
        (sub_pos.mpr hry) (by linarith)⟩
  exact mem_closure_of_tendsto hf hcore

end Arxiv2407_19026

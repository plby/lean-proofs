import ErdosProblems.Erdos140.BohrBasic
import ErdosProblems.Erdos140.FiniteConvolution

/-!
# Regular scales for finite Bohr sets

The carrier of a dilated finite Bohr set is a monotone, integer-valued
function of the dilation parameter.  This file records two completely
elementary regular-value consequences of that fact.

* `exists_plateauRegularAt` is unconditional.  It finds a scale in `[1/2,1]`
  on which the carrier is literally constant in a (possibly very small, but
  explicit) neighbourhood.  Its proof uses `|G| + 1` adjacent intervals.
* `exists_coarselyRegularAt_of_card_growth` is the quantitative
  growth/pigeonhole form used together with a Bohr volumetric estimate.  If
  the cardinality grows by less than `2^n` between scales `1/2` and `1`, one
  of `n` adjacent shells grows by at most a factor two.

The exact plateau statement also gives exact translation invariance for
translations in the smaller Bohr carrier.  We state this both as a
symmetric-difference assertion and as an `L^1` assertion for the normalized
indicator used elsewhere in the Erdős 140 development.
-/

open Finset
open scoped BigOperators NNReal symmDiff

namespace Erdos140

namespace BohrData

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Two elementary discrete growth lemmas -/

private lemma exists_adjacent_eq_of_bounded
    (N : ℕ) (f : ℕ → ℕ) (hf : Monotone f)
    (hpos : 1 ≤ f 0) (hbound : f (N + 1) ≤ N) :
    ∃ i ≤ N, f i = f (i + 1) := by
  by_contra! h
  have hadj : ∀ i ≤ N, f i < f (i + 1) := by
    intro i hi
    exact lt_of_le_of_ne (hf (Nat.le_succ i)) (h i hi)
  have hgrow : ∀ k ≤ N + 1, f 0 + k ≤ f k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hkN : k ≤ N := by omega
        have hih := ih (by omega)
        have hstep := hadj k hkN
        omega
  have := hgrow (N + 1) (by omega)
  omega

private lemma exists_adjacent_double_le
    (n : ℕ) (_hn : 0 < n) (f : ℕ → ℕ)
    (hgrowth : f n < 2 ^ n * f 0) :
    ∃ i < n, f (i + 1) ≤ 2 * f i := by
  by_contra! h
  have hadj : ∀ i < n, 2 * f i < f (i + 1) := by
    intro i hi
    have hnot := h i hi
    omega
  have hgrow : ∀ k ≤ n, 2 ^ k * f 0 ≤ f k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hkn : k < n := by omega
        calc
          2 ^ (k + 1) * f 0 = 2 * (2 ^ k * f 0) := by
            rw [pow_succ]
            ring
          _ ≤ 2 * f k := Nat.mul_le_mul_left 2 (ih (by omega))
          _ ≤ f (k + 1) := (hadj k hkn).le
  exact (not_lt_of_ge (hgrow n le_rfl)) hgrowth

/-! ## Exact plateau regularity -/

/-- `B` is plateau-regular at `(rho, eta)` when every dilation at distance at
most `eta` from `rho` has exactly the same finite carrier.  Subtraction is the
truncated subtraction on `ℝ≥0`; applications below always have `eta ≤ rho`. -/
def IsPlateauRegularAt (B : BohrData G) (rho eta : ℝ≥0) : Prop :=
  0 < eta ∧
    ∀ kappa : ℝ≥0, kappa ≤ eta →
      (B.dilate (rho - kappa)).carrier = (B.dilate rho).carrier ∧
      (B.dilate (rho + kappa)).carrier = (B.dilate rho).carrier

/-- The explicit mesh used by the unconditional plateau argument. -/
noncomputable def plateauStep (G : Type*) [Fintype G] : ℝ≥0 :=
  (((2 * (Fintype.card G + 1) : ℕ) : ℝ≥0))⁻¹

private lemma plateauStep_pos : 0 < plateauStep G := by
  simp [plateauStep]

private lemma plateauStep_mul :
    plateauStep G * ((Fintype.card G + 1 : ℕ) : ℝ≥0) = 1 / 2 := by
  rw [plateauStep]
  have hne : (((Fintype.card G + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
  field_simp
  norm_num [Nat.cast_add, Nat.cast_mul]
  exact mul_comm _ _

/-- Every finite Bohr datum has an exactly regular plateau at a scale in
`[1/2,1]`.  The radius is the explicit number
`1 / (4 * (|G| + 1))`.

This is the finite growth/pigeonhole argument in its strongest unconditional
form: among `|G| + 1` adjacent inclusions, two carriers have equal cardinality,
since every carrier is nonempty and has cardinality at most `|G|`. -/
theorem exists_plateauRegularAt (B : BohrData G) :
    ∃ rho eta : ℝ≥0,
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      eta = plateauStep G / 2 ∧
      B.IsPlateauRegularAt rho eta := by
  let step : ℝ≥0 := plateauStep G
  let scale : ℕ → ℝ≥0 := fun i ↦ 1 / 2 + (i : ℝ≥0) * step
  let f : ℕ → ℕ := fun i ↦ (B.dilate (scale i)).carrier.card
  have hf : Monotone f := by
    intro i j hij
    apply Finset.card_le_card
    apply carrier_dilate_mono
    dsimp [scale]
    gcongr
  have hfpos : 1 ≤ f 0 := by
    exact (B.dilate (scale 0)).one_le_card_carrier
  have hfbound : f (Fintype.card G + 1) ≤ Fintype.card G := by
    simpa [f] using Finset.card_le_univ (B.dilate (scale (Fintype.card G + 1))).carrier
  obtain ⟨i, hi, heq⟩ :=
    exists_adjacent_eq_of_bounded (Fintype.card G) f hf hfpos hfbound
  refine ⟨scale i + step / 2, step / 2, ?_, ?_, rfl, ?_⟩
  · dsimp [scale]
    calc
      1 / 2 ≤ 1 / 2 + (i : ℝ≥0) * step :=
        le_add_of_nonneg_right (show 0 ≤ (i : ℝ≥0) * step by exact bot_le)
      _ ≤ 1 / 2 + (i : ℝ≥0) * step + step / 2 :=
        le_add_of_nonneg_right (show 0 ≤ step / 2 by exact bot_le)
  · have hi' : (i : ℝ≥0) + 1 / 2 ≤ (Fintype.card G + 1 : ℕ) := by
      have hicast : (i : ℝ≥0) ≤ (Fintype.card G : ℕ) := by
        exact_mod_cast hi
      calc
        (i : ℝ≥0) + 1 / 2 ≤ (Fintype.card G : ℕ) + 1 / 2 := by gcongr
        _ ≤ (Fintype.card G + 1 : ℕ) := by
          push_cast
          norm_num
    calc
      scale i + step / 2 =
          1 / 2 + ((i : ℝ≥0) + 1 / 2) * step := by
        simp [scale]
        ring
      _ ≤ 1 / 2 + ((Fintype.card G + 1 : ℕ) : ℝ≥0) * step := by
        gcongr
      _ = 1 := by
        rw [mul_comm, show step = plateauStep G by rfl, plateauStep_mul]
        norm_num
  · refine ⟨by simpa [step] using div_pos plateauStep_pos (by norm_num : (0 : ℝ≥0) < 2), ?_⟩
    intro kappa hkappa
    have hstep : 0 < step := by simpa [step] using (plateauStep_pos (G := G))
    have hkappa_mid : kappa ≤ scale i + step / 2 := by
      exact hkappa.trans (le_add_of_nonneg_left (by positivity))
    have hleft : scale i ≤ scale i + step / 2 - kappa := by
      rw [le_tsub_iff_right hkappa_mid]
      linarith
    have hmidleft : scale i ≤ scale i + step / 2 :=
      le_add_of_nonneg_right (by positivity)
    have hmidright : scale i + step / 2 ≤ scale (i + 1) := by
      dsimp [scale]
      push_cast
      linarith
    have hright : scale i + step / 2 + kappa ≤ scale (i + 1) := by
      dsimp [scale]
      push_cast
      linarith
    have hendsub :
        (B.dilate (scale i)).carrier ⊆ (B.dilate (scale (i + 1))).carrier :=
      carrier_dilate_mono (by
        dsimp [scale]
        push_cast
        nlinarith)
    have hendcard :
        (B.dilate (scale i)).carrier.card =
          (B.dilate (scale (i + 1))).carrier.card := by
      exact heq
    have hendeq :
        (B.dilate (scale i)).carrier =
          (B.dilate (scale (i + 1))).carrier :=
      Finset.eq_of_subset_of_card_le hendsub hendcard.ge
    have all_eq (s : ℝ≥0) (hlo : scale i ≤ s) (hhi : s ≤ scale (i + 1)) :
        (B.dilate s).carrier = (B.dilate (scale i)).carrier := by
      apply Finset.Subset.antisymm
      · have hs := carrier_dilate_mono (B := B) hhi
        rwa [← hendeq] at hs
      · exact carrier_dilate_mono hlo
    constructor
    · exact (all_eq _ hleft ((tsub_le_self.trans hmidright))).trans
        (all_eq _ hmidleft hmidright).symm
    · exact (all_eq _ (hmidleft.trans (le_add_of_nonneg_right (by positivity))) hright).trans
        (all_eq _ hmidleft hmidright).symm

/-! ## A rank-scale coarse regularity interface -/

/-- Coarse regularity on one shell: the outer carrier has cardinality at most
twice that of the inner carrier. -/
def IsCoarselyRegularAt (B : BohrData G) (rho eta : ℝ≥0) : Prop :=
  0 < eta ∧ eta ≤ rho ∧
    (B.dilate (rho + eta)).carrier.card ≤
      2 * (B.dilate (rho - eta)).carrier.card

/-- Standard rank-controlled Bohr regularity.  The harmless `max rank 1`
also covers the rank-zero case.  The constants are deliberately coarse and
fully explicit: for relative perturbations `kappa ≤ 1/(100 d)`, both inner
and outer cardinalities differ from the central one by at most
`100 d kappa` in relative terms. -/
def IsRankRegular (B : BohrData G) : Prop :=
  let d : ℕ := max B.rank 1
  ∀ kappa : ℝ≥0,
    kappa ≤ 1 / (100 * (d : ℝ≥0)) →
      (1 - 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ) ≤
          ((B.dilate (1 - kappa)).carrier.card : ℝ) ∧
      ((B.dilate (1 + kappa)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ)

/-- Rank regularity is stable under a further scalar dilation: this lemma is
only a normalization of the nested-dilation formula. -/
theorem isRankRegular_dilate_iff (B : BohrData G) (rho : ℝ≥0) :
    (B.dilate rho).IsRankRegular ↔
      let d : ℕ := max B.rank 1
      ∀ kappa : ℝ≥0,
        kappa ≤ 1 / (100 * (d : ℝ≥0)) →
          (1 - 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.dilate rho).carrier.card : ℝ) ≤
              ((B.dilate ((1 - kappa) * rho)).carrier.card : ℝ) ∧
          ((B.dilate ((1 + kappa) * rho)).carrier.card : ℝ) ≤
              (1 + 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.dilate rho).carrier.card : ℝ) := by
  simp [IsRankRegular, mul_comm]

/-- Quantitative regular-value lemma.  If the total growth from scale `1/2`
to scale `1` is less than `2^n`, one of the `n` equal shells has growth at
most two.  Its midpoint lies in `[1/2,1]` and its half-width is exactly
`1/(4n)`. -/
theorem exists_coarselyRegularAt_of_card_growth
    (B : BohrData G) (n : ℕ) (hn : 0 < n)
    (hgrowth :
      (B.dilate 1).carrier.card <
        2 ^ n * (B.dilate (1 / 2)).carrier.card) :
    ∃ rho eta : ℝ≥0,
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      eta = 1 / (4 * (n : ℝ≥0)) ∧
      B.IsCoarselyRegularAt rho eta := by
  let step : ℝ≥0 := 1 / (2 * (n : ℝ≥0))
  let scale : ℕ → ℝ≥0 := fun i ↦ 1 / 2 + (i : ℝ≥0) * step
  let f : ℕ → ℕ := fun i ↦ (B.dilate (scale i)).carrier.card
  have hscale_zero : scale 0 = 1 / 2 := by simp [scale]
  have hscale_n : scale n = 1 := by
    simp [scale, step]
    field_simp
    ring
  have hfgrowth : f n < 2 ^ n * f 0 := by
    simpa [f, hscale_zero, hscale_n] using hgrowth
  obtain ⟨i, hi, hiGrowth⟩ := exists_adjacent_double_le n hn f hfgrowth
  refine ⟨scale i + step / 2, step / 2, ?_, ?_, ?_, ?_⟩
  · dsimp [scale]
    calc
      1 / 2 ≤ 1 / 2 + (i : ℝ≥0) * step :=
        le_add_of_nonneg_right (show 0 ≤ (i : ℝ≥0) * step by exact bot_le)
      _ ≤ 1 / 2 + (i : ℝ≥0) * step + step / 2 :=
        le_add_of_nonneg_right (show 0 ≤ step / 2 by exact bot_le)
  · have hi_le : (i : ℝ≥0) + 1 / 2 ≤ (n : ℝ≥0) := by
      have hi1 : ((i + 1 : ℕ) : ℝ≥0) ≤ (n : ℝ≥0) := by
        exact_mod_cast (show i + 1 ≤ n by omega)
      calc
        (i : ℝ≥0) + 1 / 2 ≤ (i : ℝ≥0) + 1 := by norm_num
        _ = ((i + 1 : ℕ) : ℝ≥0) := by push_cast; rfl
        _ ≤ (n : ℝ≥0) := hi1
    calc
      scale i + step / 2 = 1 / 2 + ((i : ℝ≥0) + 1 / 2) * step := by
        simp [scale]
        ring
      _ ≤ 1 / 2 + (n : ℝ≥0) * step := by gcongr
      _ = 1 := by
        simp [step]
        field_simp
        ring
  · simp [step]
    ring
  · refine ⟨by positivity, ?_, ?_⟩
    · have : step / 2 ≤ 1 / 2 := by
        rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ≥0) < 2)]
        dsimp [step]
        rw [div_le_one]
        · exact_mod_cast (show 1 ≤ 2 * n by omega)
        · have hnreal : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
          positivity
      exact this.trans (by
        dsimp [scale]
        calc
          1 / 2 ≤ 1 / 2 + (i : ℝ≥0) * step :=
            le_add_of_nonneg_right (show 0 ≤ (i : ℝ≥0) * step by exact bot_le)
          _ ≤ 1 / 2 + (i : ℝ≥0) * step + step / 2 :=
            le_add_of_nonneg_right (show 0 ≤ step / 2 by exact bot_le))
    · have hminus : scale i + step / 2 - step / 2 = scale i := by
        exact add_tsub_cancel_right _ _
      have hplus : scale i + step / 2 + step / 2 = scale (i + 1) := by
        dsimp [scale]
        push_cast
        ring
      simpa [hminus, hplus, f] using hiGrowth

/-! ## Translation and normalized-indicator consequences -/

/-- Translation of a finite set by addition on the right. -/
noncomputable def translateFinset (A : Finset G) (t : G) : Finset G :=
  A.map (Equiv.addRight t).toEmbedding

@[simp] lemma mem_translateFinset {A : Finset G} {t x : G} :
    x ∈ translateFinset A t ↔ x - t ∈ A := by
  simp [translateFinset, sub_eq_add_neg]

@[simp] lemma card_translateFinset (A : Finset G) (t : G) :
    (translateFinset A t).card = A.card := by
  simp [translateFinset]

/-- A small translate and the central carrier can differ only in the shell
between the inner and outer dilates.  This is the set-theoretic heart of the
usual Bohr normalized-indicator translation estimate. -/
theorem symmDiff_translate_carrier_subset_shell
    {B : BohrData G} {rho eta : ℝ≥0} (heta : eta ≤ rho) {t : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    (translateFinset (B.dilate rho).carrier t) ∆ (B.dilate rho).carrier ⊆
      (B.dilate (rho + eta)).carrier \ (B.dilate (rho - eta)).carrier := by
  intro x hx
  rw [Finset.mem_symmDiff] at hx
  rw [Finset.mem_sdiff]
  constructor
  · rcases hx with hx | hx
    · rw [mem_translateFinset] at hx
      have hxt := add_mem_dilate hx.1 ht
      simpa using hxt
    · exact carrier_dilate_mono (le_add_of_nonneg_right (by positivity)) hx.1
  · intro hinner
    have hinner_center : x ∈ (B.dilate rho).carrier := by
      exact carrier_dilate_mono (tsub_le_self) hinner
    have hinner_shift : x - t ∈ (B.dilate rho).carrier := by
      have hneg : -t ∈ (B.dilate eta).carrier := neg_mem_carrier.mpr ht
      have hadd := add_mem_dilate hinner hneg
      simpa [sub_eq_add_neg, tsub_add_cancel_of_le heta] using hadd
    have hinner_translate : x ∈ translateFinset (B.dilate rho).carrier t := by
      rwa [mem_translateFinset]
    rcases hx with hx | hx
    · exact hx.2 hinner_center
    · exact hx.2 hinner_translate

/-- Cardinal form of `symmDiff_translate_carrier_subset_shell`. -/
theorem card_symmDiff_translate_carrier_le_shell
    {B : BohrData G} {rho eta : ℝ≥0} (heta : eta ≤ rho) {t : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    ((translateFinset (B.dilate rho).carrier t) ∆
        (B.dilate rho).carrier).card ≤
      (B.dilate (rho + eta)).carrier.card -
        (B.dilate (rho - eta)).carrier.card := by
  have hinner_outer :
      (B.dilate (rho - eta)).carrier ⊆
        (B.dilate (rho + eta)).carrier :=
    carrier_dilate_mono ((tsub_le_self).trans (le_add_of_nonneg_right (by positivity)))
  calc
    ((translateFinset (B.dilate rho).carrier t) ∆
        (B.dilate rho).carrier).card ≤
        ((B.dilate (rho + eta)).carrier \
          (B.dilate (rho - eta)).carrier).card :=
      Finset.card_le_card (symmDiff_translate_carrier_subset_shell heta ht)
    _ = (B.dilate (rho + eta)).carrier.card -
        (B.dilate (rho - eta)).carrier.card :=
      Finset.card_sdiff_of_subset hinner_outer

/-- The counting-measure `L^1` distance of two normalized indicators is the
relative cardinality of their symmetric difference.  Here the two finite sets
have equal cardinality because one is a translate of the other. -/
theorem sum_abs_normalizedIndicator_translate_eq_card_symmDiff
    (A : Finset G) (t : G) :
    ∑ x : G, |normalizedIndicator A (x - t) - normalizedIndicator A x| =
      (((translateFinset A t) ∆ A).card : ℝ) / (A.card : ℝ) := by
  have hpoint (x : G) :
      |normalizedIndicator A (x - t) - normalizedIndicator A x| =
        if x ∈ (translateFinset A t) ∆ A then (A.card : ℝ)⁻¹ else 0 := by
    by_cases hxt : x - t ∈ A <;> by_cases hx : x ∈ A <;>
      simp [normalizedIndicator, Finset.mem_symmDiff, mem_translateFinset,
        hxt, hx, abs_of_nonneg]
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- The standard normalized-indicator translation estimate in shell form. -/
theorem sum_abs_normalizedIndicator_translate_le_shell
    {B : BohrData G} {rho eta : ℝ≥0} (heta : eta ≤ rho) {t : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    ∑ x : G,
        |normalizedIndicator (B.dilate rho).carrier (x - t) -
          normalizedIndicator (B.dilate rho).carrier x| ≤
      (((B.dilate (rho + eta)).carrier.card -
        (B.dilate (rho - eta)).carrier.card : ℕ) : ℝ) /
          ((B.dilate rho).carrier.card : ℝ) := by
  rw [sum_abs_normalizedIndicator_translate_eq_card_symmDiff]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  gcongr
  exact_mod_cast card_symmDiff_translate_carrier_le_shell heta ht

/-- A coarsely regular shell gives the explicit normalized bound `≤ 1`. -/
theorem sum_abs_normalizedIndicator_translate_le_one_of_coarselyRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsCoarselyRegularAt rho eta) {t : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    ∑ x : G,
        |normalizedIndicator (B.dilate rho).carrier (x - t) -
          normalizedIndicator (B.dilate rho).carrier x| ≤ 1 := by
  rw [sum_abs_normalizedIndicator_translate_eq_card_symmDiff]
  rw [div_le_one]
  · have hsymm := card_symmDiff_translate_carrier_le_shell hreg.2.1 ht
    have houter_growth := hreg.2.2
    have hinner :
        (B.dilate (rho - eta)).carrier.card ≤ (B.dilate rho).carrier.card :=
      Finset.card_le_card (carrier_dilate_mono tsub_le_self)
    have hinner_outer :
        (B.dilate (rho - eta)).carrier.card ≤
          (B.dilate (rho + eta)).carrier.card :=
      Finset.card_le_card
        (carrier_dilate_mono
          (tsub_le_self.trans (le_add_of_nonneg_right (show 0 ≤ eta by exact bot_le))))
    have hshell :
        (B.dilate (rho + eta)).carrier.card -
            (B.dilate (rho - eta)).carrier.card ≤
          (B.dilate rho).carrier.card := by
      omega
    exact_mod_cast hsymm.trans hshell
  · exact_mod_cast (B.dilate rho).carrier_nonempty.card_pos

/-- The standard `O(rank * kappa)` normalized-indicator translation estimate
for a rank-regular Bohr carrier. -/
theorem sum_abs_normalizedIndicator_translate_le_of_rankRegular
    {B : BohrData G} (hreg : B.IsRankRegular) {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    {t : G} (ht : t ∈ (B.dilate kappa).carrier) :
    ∑ x : G,
        |normalizedIndicator B.carrier (x - t) -
          normalizedIndicator B.carrier x| ≤
      200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ) := by
  let d : ℕ := max B.rank 1
  have hd : 0 < d := by simp [d]
  have hkappa' : kappa ≤ 1 / (100 * (d : ℝ≥0)) := by
    simpa [d] using hkappa
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa'.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hshell :=
    sum_abs_normalizedIndicator_translate_le_shell
      (B := B) (rho := (1 : ℝ≥0)) (eta := kappa) hkappa_one ht
  simp only [dilate_one] at hshell
  simp only [IsRankRegular] at hreg
  have hcards := hreg kappa (by simpa [d] using hkappa')
  have hinner_outer :
      (B.dilate (1 - kappa)).carrier.card ≤
        (B.dilate (1 + kappa)).carrier.card :=
    Finset.card_le_card
      (carrier_dilate_mono
        (tsub_le_self.trans (le_add_of_nonneg_right (show 0 ≤ kappa by exact bot_le))))
  have hcenter_pos : (0 : ℝ) < B.carrier.card := by
    exact_mod_cast B.carrier_nonempty.card_pos
  apply hshell.trans
  rw [Nat.cast_sub hinner_outer]
  rw [div_le_iff₀ hcenter_pos]
  nlinarith [hcards.1, hcards.2]

/-- A translation belonging to the plateau radius preserves the central
Bohr carrier exactly. -/
theorem translate_carrier_eq_of_plateauRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsPlateauRegularAt rho eta) {t : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    translateFinset (B.dilate rho).carrier t = (B.dilate rho).carrier := by
  have houter := (hreg.2 eta le_rfl).2
  apply Finset.ext
  intro x
  rw [mem_translateFinset]
  constructor
  · intro hx
    have hxt : x - t + t ∈ (B.dilate (rho + eta)).carrier :=
      add_mem_dilate hx ht
    simpa [houter] using hxt
  · intro hx
    have hneg : -t ∈ (B.dilate eta).carrier := neg_mem_carrier.mpr ht
    have hxt : x + -t ∈ (B.dilate (rho + eta)).carrier :=
      add_mem_dilate hx hneg
    simpa [houter, sub_eq_add_neg] using hxt

/-- At an exact plateau, the symmetric difference with every sufficiently
small translate is empty. -/
theorem card_symmDiff_translate_carrier_eq_zero_of_plateauRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsPlateauRegularAt rho eta) {t : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    ((translateFinset (B.dilate rho).carrier t) ∆
      (B.dilate rho).carrier).card = 0 := by
  rw [translate_carrier_eq_of_plateauRegular hreg ht]
  simp

/-- Pointwise translation invariance of the probability-normalized indicator
at an exact regular plateau. -/
theorem normalizedIndicator_sub_eq_of_plateauRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsPlateauRegularAt rho eta) {t x : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    normalizedIndicator (B.dilate rho).carrier (x - t) =
      normalizedIndicator (B.dilate rho).carrier x := by
  have htranslate := translate_carrier_eq_of_plateauRegular hreg ht
  have hmem :
      x - t ∈ (B.dilate rho).carrier ↔ x ∈ (B.dilate rho).carrier := by
    rw [← mem_translateFinset, htranslate]
  by_cases hx : x ∈ (B.dilate rho).carrier
  · simp [normalizedIndicator, hx, hmem.mpr hx]
  · have hxt : x - t ∉ (B.dilate rho).carrier := fun h ↦ hx (hmem.mp h)
    simp [normalizedIndicator, hx, hxt]

/-- The corresponding counting-measure `L^1` translation bound is zero. -/
theorem sum_abs_normalizedIndicator_sub_eq_zero_of_plateauRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsPlateauRegularAt rho eta) {t : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    ∑ x : G,
      |normalizedIndicator (B.dilate rho).carrier (x - t) -
        normalizedIndicator (B.dilate rho).carrier x| = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [normalizedIndicator_sub_eq_of_plateauRegular hreg ht]
  simp

end BohrData

end Erdos140

#print axioms Erdos140.BohrData.exists_plateauRegularAt
#print axioms Erdos140.BohrData.exists_coarselyRegularAt_of_card_growth
#print axioms Erdos140.BohrData.sum_abs_normalizedIndicator_translate_le_of_rankRegular
#print axioms Erdos140.BohrData.sum_abs_normalizedIndicator_sub_eq_zero_of_plateauRegular

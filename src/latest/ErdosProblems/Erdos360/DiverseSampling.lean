import ErdosProblems.Erdos697.Erdos697Bernoulli

open scoped BigOperators

namespace Erdos360.DiverseSampling

open Erdos697.Bernoulli

noncomputable section

theorem exists_avoiding_weighted_bad
    {ι δ : Type*} [DecidableEq ι] [DecidableEq δ]
    (s : Finset ι) (D : Finset δ) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    (bad : δ → Finset ι → Prop) [DecidableRel bad]
    (b : δ → ℝ)
    (hbad : ∀ d ∈ D,
      (∑ T ∈ s.powerset.filter (bad d), weight s p T) ≤ b d)
    (hsum : (∑ d ∈ D, b d) < 1) :
    ∃ T ∈ s.powerset, ∀ d ∈ D, ¬ bad d T := by
  classical
  by_contra hnone
  push Not at hnone
  have hcover : ∀ T ∈ s.powerset, ∃ d ∈ D, bad d T := by
    intro T hT
    exact hnone T hT
  have hle :
      (∑ T ∈ s.powerset, weight s p T) ≤
        ∑ d ∈ D,
          ∑ T ∈ s.powerset.filter (bad d), weight s p T := by
    calc
      (∑ T ∈ s.powerset, weight s p T) ≤
          ∑ T ∈ s.powerset,
            ∑ d ∈ D, if bad d T then weight s p T else 0 := by
        apply Finset.sum_le_sum
        intro T hT
        obtain ⟨d, hdD, hdT⟩ := hcover T hT
        have hnonneg : ∀ e ∈ D,
            0 ≤ if bad e T then weight s p T else 0 := by
          intro e he
          split_ifs
          · exact weight_nonneg s p hp0 hp1 hT
          · exact le_rfl
        calc
          weight s p T = if bad d T then weight s p T else 0 := by
            simp [hdT]
          _ ≤ ∑ e ∈ D, if bad e T then weight s p T else 0 := by
            exact Finset.single_le_sum (fun e he => hnonneg e he) hdD
      _ = ∑ d ∈ D,
          ∑ T ∈ s.powerset, if bad d T then weight s p T else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ d ∈ D,
          ∑ T ∈ s.powerset.filter (bad d), weight s p T := by
        apply Finset.sum_congr rfl
        intro d hdD
        rw [Finset.sum_filter]
  have hupper :
      (∑ d ∈ D,
          ∑ T ∈ s.powerset.filter (bad d), weight s p T) ≤
        ∑ d ∈ D, b d := by
    apply Finset.sum_le_sum
    intro d hdD
    exact hbad d hdD
  have hone := sum_weight_powerset s p
  linarith

theorem sum_pow_inter_card_mul_weight
    {ι : Type*} [DecidableEq ι]
    (s X : Finset ι) (p : ι → ℝ) (a : ℝ) (hX : X ⊆ s) :
    (∑ T ∈ s.powerset,
        a ^ (T ∩ X).card * weight s p T) =
      ∏ i ∈ s, ((1 - p i) + p i * (if i ∈ X then a else 1)) := by
  unfold weight
  calc
    (∑ T ∈ s.powerset,
        a ^ (T ∩ X).card *
          ((∏ i ∈ T, p i) * ∏ i ∈ s \ T, (1 - p i))) =
        ∏ i ∈ s, (p i * (if i ∈ X then a else 1) + (1 - p i)) := by
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T hT
      have hprod_mul :
          (∏ i ∈ T, p i * (if i ∈ X then a else 1)) =
            (∏ i ∈ T, p i) * a ^ (T ∩ X).card := by
        rw [Finset.prod_mul_distrib]
        congr 1
        rw [Finset.prod_ite]
        simp [Finset.filter_mem_eq_inter]
      rw [hprod_mul]
      ring
    _ = ∏ i ∈ s, ((1 - p i) + p i * (if i ∈ X then a else 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      ring

theorem lower_inter_tail_chernoff
    {ι : Type*} [DecidableEq ι]
    (s X : Finset ι) (p : ι → ℝ) (_hX : X ⊆ s)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {K : ℕ} {EW r : ℝ} (hEW : EW = ∑ i ∈ X, p i)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hK : (K : ℝ) ≤ r * EW) :
    (∑ T ∈ s.powerset.filter (fun T => (T ∩ X).card < K),
        weight s p T) ≤
      Real.exp
        ((r * ((1 - r) / (2 * r)) +
            (1 / (1 + ((1 - r) / (2 * r))) - 1)) * EW) := by
  classical
  let t : ℝ := (1 - r) / (2 * r)
  let a : ℝ := Real.exp (-t)
  let b : ℝ := 1 / (1 + t) - 1
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ha_pos : 0 < a := by positivity
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have honept : 0 < 1 + t := by linarith
  have ha_le : a ≤ 1 / (1 + t) := by
    have hexp : 1 + t ≤ Real.exp t := by
      simpa [add_comm] using Real.add_one_le_exp t
    have hinv : (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ :=
      inv_anti₀ honept hexp
    simpa [a, Real.exp_neg, one_div] using hinv
  have hb_nonpos : b ≤ 0 := by
    dsimp [b]
    have : 1 / (1 + t) ≤ 1 := (div_le_one₀ honept).2 (by linarith)
    linarith
  have hfactor_nonneg : ∀ i ∈ s,
      0 ≤ (1 - p i) + p i * (if i ∈ X then a else 1) := by
    intro i hi
    by_cases hiX : i ∈ X
    · simp only [if_pos hiX]
      nlinarith [hp0 i hi, hp1 i hi,
        mul_nonneg (hp0 i hi) ha_nonneg]
    · simp [hiX]
  have hfactor_le : ∀ i ∈ s,
      (1 - p i) + p i * (if i ∈ X then a else 1) ≤
        Real.exp ((if i ∈ X then b * p i else 0)) := by
    intro i hi
    by_cases hiX : i ∈ X
    · simp only [if_pos hiX]
      have hpa : p i * a ≤ p i * (1 / (1 + t)) :=
        mul_le_mul_of_nonneg_left ha_le (hp0 i hi)
      calc
        (1 - p i) + p i * a
            ≤ (1 - p i) + p i * (1 / (1 + t)) := by linarith
        _ = 1 + b * p i := by dsimp [b]; ring
        _ = b * p i + 1 := by ring
        _ ≤ Real.exp (b * p i) := Real.add_one_le_exp _
    · simp [hiX]
  have hgen_le :
      (∑ T ∈ s.powerset,
          a ^ (T ∩ X).card * weight s p T) ≤
        Real.exp (b * EW) := by
    rw [sum_pow_inter_card_mul_weight s X p a _hX]
    calc
      ∏ i ∈ s, ((1 - p i) + p i * (if i ∈ X then a else 1))
          ≤ ∏ i ∈ s, Real.exp (if i ∈ X then b * p i else 0) :=
            Finset.prod_le_prod hfactor_nonneg hfactor_le
      _ = Real.exp (b * EW) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter]
        have hsX : s ∩ X = X := Finset.inter_eq_right.mpr _hX
        rw [hsX, ← Finset.mul_sum, ← hEW]
  have htail_le_gen :
      (∑ T ∈ s.powerset.filter (fun T => (T ∩ X).card < K),
          weight s p T) ≤
        Real.exp (t * (K : ℝ)) *
          (∑ T ∈ s.powerset,
            a ^ (T ∩ X).card * weight s p T) := by
    calc
      (∑ T ∈ s.powerset.filter (fun T => (T ∩ X).card < K),
          weight s p T)
          ≤ ∑ T ∈ s.powerset.filter (fun T => (T ∩ X).card < K),
              Real.exp (t * (K : ℝ)) *
                (a ^ (T ∩ X).card * weight s p T) := by
            apply Finset.sum_le_sum
            intro T hT
            have hTpowerset : T ∈ s.powerset :=
              (Finset.mem_filter.mp hT).1
            have hTcard : (T ∩ X).card ≤ K :=
              Nat.le_of_lt (Finset.mem_filter.mp hT).2
            have hscale :
                1 ≤ Real.exp (t * (K : ℝ)) * a ^ (T ∩ X).card := by
              dsimp [a]
              rw [← Real.exp_nat_mul, ← Real.exp_add]
              apply Real.one_le_exp
              have hcast : ((T ∩ X).card : ℝ) ≤ K := by
                exact_mod_cast hTcard
              nlinarith
            have hwT : 0 ≤ weight s p T :=
              weight_nonneg s p hp0 hp1 hTpowerset
            calc
              weight s p T
                  ≤ (Real.exp (t * (K : ℝ)) * a ^ (T ∩ X).card) *
                      weight s p T := le_mul_of_one_le_left hwT hscale
              _ = Real.exp (t * (K : ℝ)) *
                    (a ^ (T ∩ X).card * weight s p T) := by ring
      _ = Real.exp (t * (K : ℝ)) *
            (∑ T ∈ s.powerset.filter (fun T => (T ∩ X).card < K),
              a ^ (T ∩ X).card * weight s p T) := by
            rw [Finset.mul_sum]
      _ ≤ Real.exp (t * (K : ℝ)) *
            (∑ T ∈ s.powerset,
              a ^ (T ∩ X).card * weight s p T) := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro T hT
                exact (Finset.mem_filter.mp hT).1
              · intro T hTpowerset _
                exact mul_nonneg (pow_nonneg ha_nonneg _)
                  (weight_nonneg s p hp0 hp1 hTpowerset)
            · positivity
  calc
    (∑ T ∈ s.powerset.filter (fun T => (T ∩ X).card < K),
        weight s p T)
        ≤ Real.exp (t * (K : ℝ)) *
            (∑ T ∈ s.powerset,
              a ^ (T ∩ X).card * weight s p T) := htail_le_gen
    _ ≤ Real.exp (t * (K : ℝ)) * Real.exp (b * EW) := by
      exact mul_le_mul_of_nonneg_left hgen_le (by positivity)
    _ = Real.exp (t * (K : ℝ) + b * EW) := by rw [Real.exp_add]
    _ ≤ Real.exp ((r * t + b) * EW) := by
      apply Real.exp_le_exp.mpr
      have hEW_nonneg : 0 ≤ EW := by
        rw [hEW]
        exact Finset.sum_nonneg (fun i hi => hp0 i (_hX hi))
      nlinarith
    _ = Real.exp
        ((r * ((1 - r) / (2 * r)) +
            (1 / (1 + ((1 - r) / (2 * r))) - 1)) * EW) := by
      rfl

lemma weight_half_eq_pow_card
    {ι : Type*} [DecidableEq ι] (s T : Finset ι) (hT : T ⊆ s) :
    weight s (fun _ ↦ (1 / 2 : ℝ)) T = (1 / 2 : ℝ) ^ s.card := by
  unfold weight
  rw [Finset.prod_const, Finset.prod_const]
  have hhalf : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [hhalf]
  rw [← pow_add]
  congr 1
  rw [Finset.card_sdiff_of_subset hT]
  have := Finset.card_le_card hT
  omega

lemma sum_weight_half_complement
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : Finset ι → Prop) [DecidablePred P] :
    (∑ T ∈ s.powerset.filter (fun T ↦ P (s \ T)),
        weight s (fun _ ↦ (1 / 2 : ℝ)) T) =
      ∑ U ∈ s.powerset.filter P,
        weight s (fun _ ↦ (1 / 2 : ℝ)) U := by
  classical
  apply Finset.sum_bij'
      (fun T _ ↦ s \ T) (fun U _ ↦ s \ U)
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset), hT.2⟩
  · intro U hU
    rw [Finset.mem_filter] at hU ⊢
    have hUs : U ⊆ s := Finset.mem_powerset.mp hU.1
    exact ⟨Finset.mem_powerset.mpr Finset.sdiff_subset,
      by simpa [Finset.sdiff_sdiff_eq_self hUs] using hU.2⟩
  · intro T hT
    have hTs : T ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    exact Finset.sdiff_sdiff_eq_self hTs
  · intro U hU
    have hUs : U ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
    exact Finset.sdiff_sdiff_eq_self hUs
  · intro T hT
    have hTs : T ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have hsT : s \ T ⊆ s := Finset.sdiff_subset
    rw [weight_half_eq_pow_card s T hTs,
      weight_half_eq_pow_card s (s \ T) hsT]

lemma half_inter_low_weight_le
    {ι : Type*} [DecidableEq ι]
    (s X : Finset ι) (hXs : X ⊆ s) (k : ℕ) (hkX : k ≤ X.card) :
    (∑ T ∈ s.powerset.filter (fun T ↦ (T ∩ X).card < k / 4),
        weight s (fun _ ↦ (1 / 2 : ℝ)) T) ≤
      Real.exp (-(k : ℝ) / 24) := by
  have htail := lower_inter_tail_chernoff s X
    (fun _ ↦ (1 / 2 : ℝ)) hXs
    (by intro i hi; norm_num) (by intro i hi; norm_num)
    (K := k / 4) (EW := (X.card : ℝ) / 2) (r := (1 / 2 : ℝ))
    (by simp; ring) (by norm_num) (by norm_num) (by
      have hkdiv : k / 4 ≤ X.card / 4 := Nat.div_le_div_right hkX
      have hkdivR : ((k / 4 : ℕ) : ℝ) ≤ ((X.card / 4 : ℕ) : ℝ) := by
        exact_mod_cast hkdiv
      have hcastdiv : ((X.card / 4 : ℕ) : ℝ) ≤ (X.card : ℝ) / 4 :=
        Nat.cast_div_le
      calc
        ((k / 4 : ℕ) : ℝ) ≤ ((X.card / 4 : ℕ) : ℝ) := hkdivR
        _ ≤ (X.card : ℝ) / 4 := hcastdiv
        _ = (1 / 2 : ℝ) * ((X.card : ℝ) / 2) := by ring)
  have hcast : (k : ℝ) ≤ X.card := by exact_mod_cast hkX
  calc
    (∑ T ∈ s.powerset.filter (fun T ↦ (T ∩ X).card < k / 4),
        weight s (fun _ ↦ (1 / 2 : ℝ)) T)
        ≤ Real.exp (-(X.card : ℝ) / 24) := by
          convert htail using 1 <;> norm_num <;> ring
    _ ≤ Real.exp (-(k : ℝ) / 24) := by
      apply Real.exp_le_exp.mpr
      linarith

lemma half_sdiff_low_weight_le
    {ι : Type*} [DecidableEq ι]
    (s X : Finset ι) (hXs : X ⊆ s) (k : ℕ) (hkX : k ≤ X.card) :
    (∑ T ∈ s.powerset.filter (fun T ↦ (X \ T).card < k / 4),
        weight s (fun _ ↦ (1 / 2 : ℝ)) T) ≤
      Real.exp (-(k : ℝ) / 24) := by
  have hsymm := sum_weight_half_complement s
    (fun U ↦ (U ∩ X).card < k / 4)
  have hpred : ∀ T ⊆ s, (s \ T) ∩ X = X \ T := by
    intro T hTs
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hxs, hxT⟩, hxX⟩
      exact ⟨hxX, hxT⟩
    · rintro ⟨hxX, hxT⟩
      exact ⟨⟨hXs hxX, hxT⟩, hxX⟩
  have heq :
      (∑ T ∈ s.powerset.filter (fun T ↦ (X \ T).card < k / 4),
          weight s (fun _ ↦ (1 / 2 : ℝ)) T) =
        ∑ T ∈ s.powerset.filter (fun T ↦ (T ∩ X).card < k / 4),
          weight s (fun _ ↦ (1 / 2 : ℝ)) T := by
    rw [← hsymm]
    apply Finset.sum_congr
    · ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff]
      intro hTs
      rw [hpred T hTs]
    · intro T hT
      rfl
  rw [heq]
  exact half_inter_low_weight_le s X hXs k hkX

def DiverseNat (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ d : ℕ, 2 ≤ d → k ≤ (A.filter fun a ↦ ¬d ∣ a).card

private def splitFiber (A : Finset ℕ) (d : ℕ) : Finset ℕ :=
  if d < 2 then A else A.filter fun a ↦ ¬d ∣ a

private def splitParameter (A : Finset ℕ) (k d : ℕ) : ℕ :=
  if d < 2 then A.card else k

theorem exists_balanced_diverse_bisection
    {A : Finset ℕ} {k N : ℕ}
    (hA : DiverseNat A k)
    (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ N)
    (hprob : (2 * (N + 1) : ℝ) * Real.exp (-(k : ℝ) / 24) < 1) :
    ∃ B : Finset ℕ, B ⊆ A ∧
      DiverseNat B (k / 4) ∧ DiverseNat (A \ B) (k / 4) ∧
      A.card / 4 ≤ B.card ∧ A.card / 4 ≤ (A \ B).card := by
  classical
  let D : Finset (Bool × ℕ) := Finset.univ.product (Finset.Icc 0 N)
  let bad : Bool × ℕ → Finset ℕ → Prop := fun e T ↦
    let X := splitFiber A e.2
    let m := splitParameter A k e.2
    if e.1 then (X \ T).card < m / 4 else (T ∩ X).card < m / 4
  let q : ℕ → ℝ := fun _ ↦ 1 / 2
  have hkA : k ≤ A.card := by
    exact (hA 2 (by omega)).trans
      (Finset.card_le_card (Finset.filter_subset _ _))
  have hfiber (d : ℕ) : splitFiber A d ⊆ A := by
    simp only [splitFiber]
    split_ifs
    · exact Finset.Subset.rfl
    · exact Finset.filter_subset _ _
  have hparameter (d : ℕ) :
      splitParameter A k d ≤ (splitFiber A d).card := by
    simp only [splitParameter, splitFiber]
    by_cases hd : d < 2
    · simp [hd]
    · simp only [if_neg hd]
      exact hA d (by omega)
  have hkparam (d : ℕ) : k ≤ splitParameter A k d := by
    simp only [splitParameter]
    split_ifs
    · exact hkA
    · exact le_rfl
  have hbad : ∀ e ∈ D,
      (∑ T ∈ A.powerset.filter (bad e),
          Erdos697.Bernoulli.weight A q T) ≤
        Real.exp (-(k : ℝ) / 24) := by
    rintro ⟨side, d⟩ hed
    let X := splitFiber A d
    let m := splitParameter A k d
    have hXm : m ≤ X.card := by simpa [X, m] using hparameter d
    have hXsub : X ⊆ A := by simpa [X] using hfiber d
    have hmk : k ≤ m := by simpa [m] using hkparam d
    have hexp : Real.exp (-(m : ℝ) / 24) ≤
        Real.exp (-(k : ℝ) / 24) := by
      apply Real.exp_le_exp.mpr
      have hcast : (k : ℝ) ≤ m := by exact_mod_cast hmk
      linarith
    cases side with
    | false =>
        have htail := half_inter_low_weight_le A X hXsub m hXm
        exact htail.trans hexp
    | true =>
        have htail := half_sdiff_low_weight_le A X hXsub m hXm
        exact htail.trans hexp
  have hsum :
      (∑ e ∈ D, Real.exp (-(k : ℝ) / 24)) < 1 := by
    have hcardD : D.card = 2 * (N + 1) := by
      simp [D]
    rw [Finset.sum_const, nsmul_eq_mul, hcardD]
    norm_num at hprob ⊢
    exact hprob
  obtain ⟨B, hBpow, hgood⟩ :=
    exists_avoiding_weighted_bad A D q
      (by intro i hi; norm_num) (by intro i hi; norm_num)
      bad (fun _ ↦ Real.exp (-(k : ℝ) / 24)) hbad hsum
  have hBA : B ⊆ A := Finset.mem_powerset.mp hBpow
  have hzero : (false, 0) ∈ D := by simp [D]
  have hone : (true, 0) ∈ D := by simp [D]
  have hBcard : A.card / 4 ≤ B.card := by
    have hg := hgood (false, 0) hzero
    simp only [bad, splitFiber, splitParameter, Nat.zero_lt_succ,
      ↓reduceIte, Bool.false_eq_true, Finset.inter_eq_left.mpr hBA] at hg
    omega
  have hcompcard : A.card / 4 ≤ (A \ B).card := by
    have hg := hgood (true, 0) hone
    simp only [bad, splitFiber, splitParameter, Nat.zero_lt_succ,
      ↓reduceIte] at hg
    omega
  have hdivB : DiverseNat B (k / 4) := by
    intro d hd
    by_cases hdN : d ≤ N
    · have hdD : (false, d) ∈ D := by simp [D, hdN]
      have hg := hgood (false, d) hdD
      have hnotlt : ¬d < 2 := by omega
      simp only [bad, splitFiber, splitParameter, hnotlt, ↓reduceIte,
        Bool.false_eq_true] at hg
      have heq : B ∩ (A.filter fun a ↦ ¬d ∣ a) =
          B.filter fun a ↦ ¬d ∣ a := by
        ext a
        simp only [Finset.mem_inter, Finset.mem_filter]
        constructor
        · rintro ⟨haB, haA, had⟩
          exact ⟨haB, had⟩
        · rintro ⟨haB, had⟩
          exact ⟨haB, hBA haB, had⟩
      rw [heq] at hg
      omega
    · have hall : B.filter (fun a ↦ ¬d ∣ a) = B := by
        apply Finset.filter_eq_self.mpr
        intro a haB
        have har := hrange a (hBA haB)
        intro hda
        have hle := Nat.le_of_dvd har.1 hda
        omega
      rw [hall]
      exact (Nat.div_le_div_right hkA).trans hBcard
  have hdivComp : DiverseNat (A \ B) (k / 4) := by
    intro d hd
    by_cases hdN : d ≤ N
    · have hdD : (true, d) ∈ D := by simp [D, hdN]
      have hg := hgood (true, d) hdD
      have hnotlt : ¬d < 2 := by omega
      simp only [bad, splitFiber, splitParameter, hnotlt, ↓reduceIte] at hg
      have heq : (A.filter fun a ↦ ¬d ∣ a) \ B =
          (A \ B).filter fun a ↦ ¬d ∣ a := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_filter]
        constructor
        · rintro ⟨⟨haA, hda⟩, haB⟩
          exact ⟨⟨haA, haB⟩, hda⟩
        · rintro ⟨⟨haA, haB⟩, hda⟩
          exact ⟨⟨haA, hda⟩, haB⟩
      rw [heq] at hg
      omega
    · have hall : (A \ B).filter (fun a ↦ ¬d ∣ a) = A \ B := by
        apply Finset.filter_eq_self.mpr
        intro a haComp
        have haA := (Finset.mem_sdiff.mp haComp).1
        have har := hrange a haA
        intro hda
        have hle := Nat.le_of_dvd har.1 hda
        omega
      rw [hall]
      exact (Nat.div_le_div_right hkA).trans hcompcard
  exact ⟨B, hBA, hdivB, hdivComp, hBcard, hcompcard⟩

/-- A certificate for recursively bisecting a positive finite integer set.
At depth `d` its leaves form `2^d` disjoint pieces; every leaf has inherited
one quarter of the preceding diversity and cardinality at each split. -/
inductive BalancedDiverseTree (N : ℕ) : ℕ → Finset ℕ → ℕ → Prop
  | leaf {A : Finset ℕ} {k : ℕ}
      (hA : DiverseNat A k)
      (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ N) :
      BalancedDiverseTree N 0 A k
  | node {depth : ℕ} {A B : Finset ℕ} {k : ℕ}
      (hBA : B ⊆ A)
      (hBcard : A.card / 4 ≤ B.card)
      (hCcard : A.card / 4 ≤ (A \ B).card)
      (left : BalancedDiverseTree N depth B (k / 4))
      (right : BalancedDiverseTree N depth (A \ B) (k / 4)) :
      BalancedDiverseTree N (depth + 1) A k

/-- Iterated form of `exists_balanced_diverse_bisection`.  It packages all
choices in one finite binary tree and requires only the weakest (leaf-level)
Chernoff hypothesis. -/
theorem exists_balancedDiverseTree
    {A : Finset ℕ} {k N depth : ℕ}
    (hA : DiverseNat A k)
    (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ N)
    (hprob : (2 * (N + 1) : ℝ) *
      Real.exp (-((k / 4 ^ depth : ℕ) : ℝ) / 24) < 1) :
    BalancedDiverseTree N depth A k := by
  induction depth generalizing A k with
  | zero =>
      exact BalancedDiverseTree.leaf hA hrange
  | succ depth ih =>
      let kf := k / 4 ^ (depth + 1)
      have hkf : kf ≤ k := by
        dsimp [kf]
        exact Nat.div_le_self _ _
      have hkfR : (kf : ℝ) ≤ k := by exact_mod_cast hkf
      have hcurrent : (2 * (N + 1) : ℝ) *
          Real.exp (-(k : ℝ) / 24) < 1 := by
        apply lt_of_le_of_lt _ hprob
        apply mul_le_mul_of_nonneg_left
        · apply Real.exp_le_exp.mpr
          linarith
        · positivity
      obtain ⟨B, hBA, hdivB, hdivC, hBcard, hCcard⟩ :=
        exists_balanced_diverse_bisection hA hrange hcurrent
      have hrangeB : ∀ a ∈ B, 0 < a ∧ a ≤ N := by
        intro a ha
        exact hrange a (hBA ha)
      have hrangeC : ∀ a ∈ A \ B, 0 < a ∧ a ≤ N := by
        intro a ha
        exact hrange a (Finset.mem_sdiff.mp ha).1
      have hprob' : (2 * (N + 1) : ℝ) *
          Real.exp (-(((k / 4) / 4 ^ depth : ℕ) : ℝ) / 24) < 1 := by
        simpa [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc] using hprob
      exact BalancedDiverseTree.node hBA hBcard hCcard
        (ih hdivB hrangeB hprob') (ih hdivC hrangeC hprob')

/-- The leaves of a balanced diversity tree, as an actual disjoint covering
list with the quantitative invariants needed by the modular argument. -/
theorem exists_parts_of_balancedDiverseTree
    {N depth : ℕ} {A : Finset ℕ} {k : ℕ}
    (T : BalancedDiverseTree N depth A k) :
    ∃ parts : List (Finset ℕ),
      parts.length = 2 ^ depth ∧
      parts.Pairwise (fun P Q ↦ Disjoint P Q) ∧
      (∀ P ∈ parts, P ⊆ A) ∧
      (∀ a ∈ A, ∃ P ∈ parts, a ∈ P) ∧
      (∀ P ∈ parts, DiverseNat P (k / 4 ^ depth)) ∧
      (∀ P ∈ parts, A.card / 4 ^ depth ≤ P.card) := by
  induction depth generalizing A k with
  | zero =>
      cases T with
      | leaf hA hrange =>
        refine ⟨[A], by simp, by simp, ?_, ?_, ?_, ?_⟩
        · simp
        · intro a ha
          exact ⟨A, by simp, ha⟩
        · simpa using hA
        · simp
  | succ depth ih =>
      cases T with
      | @node depth' _ B k' hBA hBcard hCcard left right =>
        have ihL := ih left
        have ihR := ih right
        obtain ⟨L, hLlen, hLpair, hLsub, hLcover, hLdiv, hLcard⟩ := ihL
        obtain ⟨R, hRlen, hRpair, hRsub, hRcover, hRdiv, hRcard⟩ := ihR
        refine ⟨L ++ R, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.length_append, hLlen, hRlen, pow_succ]
          omega
        · rw [List.pairwise_append]
          refine ⟨hLpair, hRpair, ?_⟩
          intro P hPL Q hQR
          rw [Finset.disjoint_left]
          intro a haP haQ
          have haB : a ∈ B := hLsub P hPL haP
          have haC : a ∈ A \ B := hRsub Q hQR haQ
          exact (Finset.mem_sdiff.mp haC).2 haB
        · intro P hP
          rw [List.mem_append] at hP
          rcases hP with hP | hP
          · exact (hLsub P hP).trans hBA
          · exact (hRsub P hP).trans Finset.sdiff_subset
        · intro a haA
          by_cases haB : a ∈ B
          · obtain ⟨P, hPL, haP⟩ := hLcover a haB
            exact ⟨P, List.mem_append_left R hPL, haP⟩
          · have haC : a ∈ A \ B := Finset.mem_sdiff.mpr ⟨haA, haB⟩
            obtain ⟨P, hPR, haP⟩ := hRcover a haC
            exact ⟨P, List.mem_append_right L hPR, haP⟩
        · intro P hP
          rw [List.mem_append] at hP
          have heq : (k / 4) / 4 ^ depth = k / 4 ^ (depth + 1) := by
            simp [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
          rcases hP with hP | hP
          · simpa [heq] using hLdiv P hP
          · simpa [heq] using hRdiv P hP
        · intro Q hQ
          rw [List.mem_append] at hQ
          have heq : (A.card / 4) / 4 ^ depth =
              A.card / 4 ^ (depth + 1) := by
            simp [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
          rcases hQ with hQ | hQ
          · have hdiv : (A.card / 4) / 4 ^ depth ≤
                B.card / 4 ^ depth := Nat.div_le_div_right hBcard
            rw [heq] at hdiv
            exact hdiv.trans (hLcard Q hQ)
          · have hdiv : (A.card / 4) / 4 ^ depth ≤
                (A \ B).card / 4 ^ depth := Nat.div_le_div_right hCcard
            rw [heq] at hdiv
            exact hdiv.trans (hRcard Q hQ)

end

end Erdos360.DiverseSampling

/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos360.Core
import ErdosProblems.Erdos360.FiniteReduction
import ErdosProblems.Erdos360.LowerParameters

open scoped BigOperators

namespace Erdos360.RandomDiversity

open Erdos697.Bernoulli
open DiverseSampling

noncomputable section

/-!
The source samples uniformly from a fixed-cardinality layer.  The Bernoulli
tail estimate already proved in `DiverseSampling` applies before
conditioning.  The elementary lemmas below supply the missing conditioning
step: if `t = h*s`, the `s`-th layer of a Bernoulli `1/h` subset is a mode,
and hence has mass at least `1/(t+1)`.
-/

private def binomialNumerator (t h r : ℕ) : ℕ :=
  t.choose r * (h - 1) ^ (t - r)

private lemma binomialNumerator_step_up {t h r : ℕ}
    (hr : r < t)
    (hstep : (h - 1) * (r + 1) ≤ t - r) :
    binomialNumerator t h r ≤ binomialNumerator t h (r + 1) := by
  have hpow : t - r = (t - (r + 1)) + 1 := by omega
  have hchoose := Nat.choose_succ_right_eq t r
  unfold binomialNumerator
  rw [hpow, pow_succ]
  apply Nat.le_of_mul_le_mul_right (c := r + 1)
  · calc
      (t.choose r * ((h - 1) ^ (t - (r + 1)) * (h - 1))) * (r + 1)
          = (t.choose r * (h - 1) ^ (t - (r + 1))) *
              ((h - 1) * (r + 1)) := by ring
      _ ≤ (t.choose r * (h - 1) ^ (t - (r + 1))) * (t - r) :=
        Nat.mul_le_mul_left _ hstep
      _ = (t.choose (r + 1) * (h - 1) ^ (t - (r + 1))) * (r + 1) := by
        rw [mul_assoc, mul_comm ((h - 1) ^ _) (t - r), ← mul_assoc, ← hchoose]
        ring
  · omega

private lemma binomialNumerator_step_down {t h r : ℕ}
    (hr : r < t)
    (hstep : t - r ≤ (h - 1) * (r + 1)) :
    binomialNumerator t h (r + 1) ≤ binomialNumerator t h r := by
  have hpow : t - r = (t - (r + 1)) + 1 := by omega
  have hchoose := Nat.choose_succ_right_eq t r
  unfold binomialNumerator
  rw [hpow, pow_succ]
  apply Nat.le_of_mul_le_mul_right (c := r + 1)
  · calc
      (t.choose (r + 1) * (h - 1) ^ (t - (r + 1))) * (r + 1)
          = (t.choose r * (h - 1) ^ (t - (r + 1))) * (t - r) := by
            rw [mul_assoc, mul_comm ((h - 1) ^ _) (r + 1), ← mul_assoc,
              hchoose]
            ring
      _ ≤ (t.choose r * (h - 1) ^ (t - (r + 1))) *
            ((h - 1) * (r + 1)) := Nat.mul_le_mul_left _ hstep
      _ = (t.choose r * ((h - 1) ^ (t - (r + 1)) * (h - 1))) *
            (r + 1) := by ring
  · omega

private lemma binomialNumerator_le_mode {h s r : ℕ} (hh : 2 ≤ h) :
    binomialNumerator (h * s) h r ≤
      binomialNumerator (h * s) h s := by
  have hbelow : ∀ r ≤ s, binomialNumerator (h * s) h r ≤
      binomialNumerator (h * s) h s := by
    intro r hrs
    induction hrs using Nat.decreasingInduction with
    | self => rfl
    | of_succ r hrs ih =>
        have hrs' : r + 1 ≤ s := Nat.succ_le_iff.mpr hrs
        have hrltS : r < s := hrs
        have hsMul : s ≤ h * s := Nat.le_mul_of_pos_left s (by omega)
        have hrlt : r < h * s := hrltS.trans_le hsMul
        have hmul : h * s = (h - 1) * s + s := by
          conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ h by omega)]
          ring
        have hstep : (h - 1) * (r + 1) ≤ h * s - r := by
          calc
            (h - 1) * (r + 1) ≤ (h - 1) * s :=
              Nat.mul_le_mul_left _ hrs'
            _ ≤ h * s - r := by
              apply Nat.le_sub_of_add_le
              calc
                (h - 1) * s + r ≤ (h - 1) * s + s :=
                  Nat.add_le_add_left hrltS.le _
                _ = h * s := hmul.symm
        exact (binomialNumerator_step_up hrlt hstep).trans ih
  have habove : ∀ r, s ≤ r → binomialNumerator (h * s) h r ≤
      binomialNumerator (h * s) h s := by
    intro r hsr
    induction r, hsr using Nat.le_induction with
    | base => rfl
    | succ r hsr ih =>
        by_cases hrt : r < h * s
        · have hmul : h * s = (h - 1) * s + s := by
            conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ h by omega)]
            ring
          have hstep : h * s - r ≤ (h - 1) * (r + 1) := by
            calc
              h * s - r ≤ h * s - s := Nat.sub_le_sub_left hsr _
              _ = (h - 1) * s := by
                rw [hmul]
                exact Nat.add_sub_cancel_right _ _
              _ ≤ (h - 1) * (r + 1) :=
                Nat.mul_le_mul_left _ (by omega)
          exact (binomialNumerator_step_down hrt hstep).trans ih
        · have hzero : binomialNumerator (h * s) h (r + 1) = 0 := by
            unfold binomialNumerator
            rw [Nat.choose_eq_zero_of_lt]
            simp
            omega
          rw [hzero]
          exact Nat.zero_le _
  exact (le_total r s).elim (hbelow r) (habove r)

private lemma sum_binomialNumerator (t h : ℕ) (hh : 1 ≤ h) :
    ∑ r ∈ Finset.range (t + 1), binomialNumerator t h r = h ^ t := by
  calc
    ∑ r ∈ Finset.range (t + 1), binomialNumerator t h r =
        ∑ r ∈ Finset.range (t + 1),
          (1 : ℕ) ^ r * (h - 1) ^ (t - r) * t.choose r := by
            apply Finset.sum_congr rfl
            intro r hr
            simp [binomialNumerator, mul_comm]
    _ = (1 + (h - 1)) ^ t := (add_pow (1 : ℕ) (h - 1) t).symm
    _ = h ^ t := by rw [show 1 + (h - 1) = h by omega]

private lemma mode_numerator_lower {h s : ℕ} (hh : 2 ≤ h) :
    h ^ (h * s) ≤
      (h * s + 1) * binomialNumerator (h * s) h s := by
  rw [← sum_binomialNumerator _ _ (by omega)]
  calc
    ∑ r ∈ Finset.range (h * s + 1), binomialNumerator (h * s) h r
        ≤ ∑ _r ∈ Finset.range (h * s + 1),
            binomialNumerator (h * s) h s := by
          exact Finset.sum_le_sum fun r hr ↦ binomialNumerator_le_mode hh
    _ = (h * s + 1) * binomialNumerator (h * s) h s := by simp

private lemma one_sub_inv_nat {h : ℕ} (hh : 1 ≤ h) :
    1 - ((h : ℝ)⁻¹) = (h - 1 : ℕ) / (h : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hh)
  rw [Nat.cast_sub hh]
  field_simp
  ring

private lemma weight_inv_on_fixed_layer
    {A T : Finset ℕ} {h s : ℕ}
    (hh : 1 ≤ h) (hcardA : A.card = h * s)
    (hTA : T ⊆ A) (hcardT : T.card = s) :
    weight A (fun _ ↦ ((h : ℝ)⁻¹)) T =
      ((h - 1 : ℕ) : ℝ) ^ ((h - 1) * s) / (h : ℝ) ^ (h * s) := by
  unfold weight
  rw [Finset.prod_const, Finset.prod_const, one_sub_inv_nat hh,
    hcardT, Finset.card_sdiff_of_subset hTA, hcardA, hcardT]
  have hdiff : h * s - s = (h - 1) * s := by
    have hmul : h * s = (h - 1) * s + s := by
      conv_lhs => rw [← Nat.sub_add_cancel hh]
      ring
    rw [hmul]
    exact Nat.add_sub_cancel_right _ _
  rw [hdiff, div_pow, inv_pow]
  have hhR : (h : ℝ) ≠ 0 := by positivity
  rw [show h * s = s + (h - 1) * s by
    have hmul : h * s = (h - 1) * s + s := by
      conv_lhs => rw [← Nat.sub_add_cancel hh]
      ring
    omega, pow_add]
  field_simp

private lemma sum_weight_fixed_layer_inv
    {A : Finset ℕ} {h s : ℕ}
    (hh : 1 ≤ h) (hcardA : A.card = h * s) :
    (∑ T ∈ A.powersetCard s, weight A (fun _ ↦ ((h : ℝ)⁻¹)) T) =
      (binomialNumerator (h * s) h s : ℝ) / (h : ℝ) ^ (h * s) := by
  have hterm : ∀ T ∈ A.powersetCard s,
      weight A (fun _ ↦ ((h : ℝ)⁻¹)) T =
        ((h - 1 : ℕ) : ℝ) ^ ((h - 1) * s) / (h : ℝ) ^ (h * s) := by
    intro T hT
    exact weight_inv_on_fixed_layer hh hcardA
      (Finset.mem_powersetCard.mp hT).1 (Finset.mem_powersetCard.mp hT).2
  calc
    (∑ T ∈ A.powersetCard s, weight A (fun _ ↦ ((h : ℝ)⁻¹)) T) =
        ∑ _T ∈ A.powersetCard s,
          (((h - 1 : ℕ) : ℝ) ^ ((h - 1) * s) / (h : ℝ) ^ (h * s)) := by
            exact Finset.sum_congr rfl hterm
    _ = (A.card.choose s : ℝ) *
          (((h - 1 : ℕ) : ℝ) ^ ((h - 1) * s) / (h : ℝ) ^ (h * s)) := by
            rw [Finset.sum_const, Finset.card_powersetCard]
            simp [nsmul_eq_mul]
    _ = (binomialNumerator (h * s) h s : ℝ) / (h : ℝ) ^ (h * s) := by
      rw [hcardA]
      have hdiff : h * s - s = (h - 1) * s := by
        have hmul : h * s = (h - 1) * s + s := by
          conv_lhs => rw [← Nat.sub_add_cancel hh]
          ring
        rw [hmul]
        exact Nat.add_sub_cancel_right _ _
      unfold binomialNumerator
      rw [hdiff]
      push_cast
      ring

private lemma fixed_layer_mass_lower {A : Finset ℕ} {h s : ℕ}
    (hh : 2 ≤ h) (hcardA : A.card = h * s) :
    (1 : ℝ) / (h * s + 1) ≤
      ∑ T ∈ A.powersetCard s, weight A (fun _ ↦ ((h : ℝ)⁻¹)) T := by
  rw [sum_weight_fixed_layer_inv (by omega) hcardA]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < h * s + 1)
    (by positivity : (0 : ℝ) < (h : ℝ) ^ (h * s))]
  norm_num
  have hm := mode_numerator_lower (s := s) hh
  exact_mod_cast (by simpa [mul_comm] using hm)

private theorem exists_fixedCard_avoiding_weighted_bad
    {iota delta : Type*} [DecidableEq iota] [DecidableEq delta]
    (S : Finset iota) (m : ℕ) (D : Finset delta) (p : iota → ℝ)
    (hp0 : ∀ i ∈ S, 0 ≤ p i) (hp1 : ∀ i ∈ S, p i ≤ 1)
    (bad : delta → Finset iota → Prop) [DecidableRel bad]
    (b : delta → ℝ)
    (hbad : ∀ d ∈ D,
      (∑ T ∈ S.powerset.filter (bad d), weight S p T) ≤ b d)
    (hlayer : (∑ T ∈ S.powersetCard m, weight S p T) >
      ∑ d ∈ D, b d) :
    ∃ T ∈ S.powersetCard m, ∀ d ∈ D, ¬ bad d T := by
  classical
  by_contra hnone
  push Not at hnone
  have hcover : ∀ T ∈ S.powersetCard m, ∃ d ∈ D, bad d T := by
    intro T hT
    exact hnone T hT
  have hle :
      (∑ T ∈ S.powersetCard m, weight S p T) ≤
        ∑ d ∈ D, ∑ T ∈ S.powerset.filter (bad d), weight S p T := by
    calc
      (∑ T ∈ S.powersetCard m, weight S p T) ≤
          ∑ T ∈ S.powersetCard m,
            ∑ d ∈ D, if bad d T then weight S p T else 0 := by
        apply Finset.sum_le_sum
        intro T hT
        obtain ⟨d, hdD, hdT⟩ := hcover T hT
        have hTpow : T ∈ S.powerset :=
          Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hT).1
        calc
          weight S p T = if bad d T then weight S p T else 0 := by simp [hdT]
          _ ≤ ∑ e ∈ D, if bad e T then weight S p T else 0 := by
            exact Finset.single_le_sum (s := D)
              (f := fun e ↦ if bad e T then weight S p T else 0)
              (by
                intro e he
                split_ifs
                · exact weight_nonneg S p hp0 hp1 hTpow
                · exact le_rfl) hdD
      _ = ∑ d ∈ D,
          ∑ T ∈ S.powersetCard m,
            if bad d T then weight S p T else 0 := by
        rw [Finset.sum_comm]
      _ ≤ ∑ d ∈ D,
          ∑ T ∈ S.powerset.filter (bad d), weight S p T := by
        apply Finset.sum_le_sum
        intro d hdD
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro T hT
          exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hT).1
        · intro T hTpow _
          split_ifs
          · exact weight_nonneg S p hp0 hp1 hTpow
          · exact le_rfl
  have hupp :
      (∑ d ∈ D, ∑ T ∈ S.powerset.filter (bad d), weight S p T) ≤
        ∑ d ∈ D, b d := by
    exact Finset.sum_le_sum fun d hd ↦ hbad d hd
  linarith

/-- Fixed-cardinality form of CFP Lemma 5.4.  The only extra factor compared
with the paper's conditional hypergeometric estimate is `|A|+1`; it comes
from the completely explicit lower bound on the mass of the modal binomial
layer.  CFP's exponential ambient inequality has ample room for this
polynomial factor. -/
theorem exists_fixedCard_diverse_sample
    {A : Finset ℕ} {k N h s : ℕ}
    (hh : 2 ≤ h) (hcardA : A.card = h * s)
    (hA : DiverseNat A k)
    (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ N)
    (hprob : ((h * s + 1 : ℕ) : ℝ) * (N + 1) *
      Real.exp (-(k : ℝ) / (12 * h)) < 1) :
    ∃ B ∈ A.powersetCard s, DiverseNat B (k / (2 * h)) := by
  classical
  let D := Finset.Icc 2 N
  let p : ℕ → ℝ := fun _ ↦ (h : ℝ)⁻¹
  let X : ℕ → Finset ℕ := fun d ↦ A.filter fun a ↦ ¬d ∣ a
  let bad : ℕ → Finset ℕ → Prop := fun d T ↦
    (T ∩ X d).card < k / (2 * h)
  have hp0 : ∀ i ∈ A, 0 ≤ p i := by
    intro i hi
    dsimp [p]
    positivity
  have hp1 : ∀ i ∈ A, p i ≤ 1 := by
    intro i hi
    dsimp [p]
    exact (inv_le_one₀ (by exact_mod_cast (show 0 < h by omega))).2
      (by exact_mod_cast (show 1 ≤ h by omega))
  have hkA : k ≤ A.card :=
    (hA 2 (by omega)).trans (Finset.card_le_card (Finset.filter_subset _ _))
  have hks : k / (2 * h) ≤ s := by
    rw [hcardA] at hkA
    calc
      k / (2 * h) ≤ k / h := Nat.div_le_div_left (by nlinarith) (by omega)
      _ ≤ s := (Nat.div_le_iff_le_mul (by omega)).2 (by
        calc
          k ≤ h * s := hkA
          _ = s * h := by ring
          _ ≤ s * h + h - 1 := by omega)
  have htail : ∀ d ∈ D,
      (∑ T ∈ A.powerset.filter (bad d), weight A p T) ≤
        Real.exp (-(k : ℝ) / (12 * h)) := by
    intro d hdD
    have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hdD).1
    have hXd : k ≤ (X d).card := hA d hd2
    have hXsub : X d ⊆ A := Finset.filter_subset _ _
    have hKreal : ((k / (2 * h) : ℕ) : ℝ) ≤
        (1 / 2 : ℝ) * ((X d).card / (h : ℝ)) := by
      calc
        ((k / (2 * h) : ℕ) : ℝ) ≤
            (k : ℝ) / ((2 * h : ℕ) : ℝ) := Nat.cast_div_le
        _ = (k : ℝ) / (2 * h) := by norm_num
        _ ≤ ((X d).card : ℝ) / (2 * h) := by
          gcongr
        _ = (1 / 2 : ℝ) * ((X d).card / (h : ℝ)) := by ring
    have hchern := lower_inter_tail_chernoff A (X d) p hXsub hp0 hp1
      (K := k / (2 * h)) (EW := ((X d).card : ℝ) / h)
      (r := (1 / 2 : ℝ)) (by simp [p]; ring)
      (by norm_num) (by norm_num) hKreal
    calc
      (∑ T ∈ A.powerset.filter (bad d), weight A p T) ≤
          Real.exp (-((X d).card : ℝ) / (12 * h)) := by
            convert hchern using 1 <;> norm_num <;> ring
      _ ≤ Real.exp (-(k : ℝ) / (12 * h)) := by
        apply Real.exp_le_exp.mpr
        have hhR : (0 : ℝ) < h := by positivity
        have hcast : (k : ℝ) ≤ (X d).card := by exact_mod_cast hXd
        exact div_le_div_of_nonneg_right (neg_le_neg hcast) (by positivity)
  have hDcard : D.card ≤ N + 1 := by
    calc
      D.card ≤ (Finset.Icc 0 N).card := by
        apply Finset.card_le_card
        intro d hd
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hd).2⟩
      _ = N + 1 := by simp
  have hsumBad :
      (∑ d ∈ D, Real.exp (-(k : ℝ) / (12 * h))) ≤
        (N + 1 : ℕ) * Real.exp (-(k : ℝ) / (12 * h)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hDcard) (by positivity)
  have hlayerLower := fixed_layer_mass_lower (A := A) hh hcardA
  have hlayer :
      (∑ T ∈ A.powersetCard s, weight A p T) >
        ∑ d ∈ D, Real.exp (-(k : ℝ) / (12 * h)) := by
    have hsmall : (N + 1 : ℕ) * Real.exp (-(k : ℝ) / (12 * h)) <
        (1 : ℝ) / (h * s + 1) := by
      have hpos : (0 : ℝ) < h * s + 1 := by positivity
      rw [lt_div_iff₀ hpos]
      simpa [Nat.cast_add, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
        using hprob
    have hpdef : p = fun _ ↦ ((h : ℝ)⁻¹) := rfl
    rw [hpdef]
    exact (hsumBad.trans_lt hsmall).trans_le hlayerLower
  obtain ⟨B, hBcard, hgood⟩ :=
    exists_fixedCard_avoiding_weighted_bad A s D p hp0 hp1 bad
      (fun _ ↦ Real.exp (-(k : ℝ) / (12 * h))) htail hlayer
  refine ⟨B, hBcard, ?_⟩
  intro d hd2
  by_cases hdN : d ≤ N
  · have hdD : d ∈ D := Finset.mem_Icc.mpr ⟨hd2, hdN⟩
    have hnot := hgood d hdD
    have hBA := (Finset.mem_powersetCard.mp hBcard).1
    have hinter : B ∩ X d = B.filter fun a ↦ ¬d ∣ a := by
      ext a
      simp only [X, Finset.mem_inter, Finset.mem_filter]
      constructor
      · rintro ⟨haB, haA, hda⟩
        exact ⟨haB, hda⟩
      · rintro ⟨haB, hda⟩
        exact ⟨haB, hBA haB, hda⟩
    change ¬ (B ∩ X d).card < k / (2 * h) at hnot
    rw [hinter] at hnot
    omega
  · have hall : B.filter (fun a ↦ ¬d ∣ a) = B := by
      apply Finset.filter_eq_self.mpr
      intro a haB
      have haA := (Finset.mem_powersetCard.mp hBcard).1 haB
      intro hda
      have hle := Nat.le_of_dvd (hrange a haA).1 hda
      exact hdN (hle.trans (hrange a haA).2)
    rw [hall, (Finset.mem_powersetCard.mp hBcard).2]
    exact hks

/-! ## A source-faithful split with a still-diverse remainder -/

private lemma weight_complement_general
    {iota : Type*} [DecidableEq iota]
    (S T : Finset iota) (p : iota → ℝ) (hTS : T ⊆ S) :
    weight S p T = weight S (fun i ↦ 1 - p i) (S \ T) := by
  unfold weight
  rw [Finset.sdiff_sdiff_eq_self hTS]
  simp only [sub_sub_cancel]
  ring

private lemma sum_weight_complement_inter
    {iota : Type*} [DecidableEq iota]
    (S X : Finset iota) (p : iota → ℝ) (hXS : X ⊆ S)
    (K : ℕ) :
    (∑ T ∈ S.powerset.filter (fun T ↦ (X \ T).card < K),
        weight S p T) =
      ∑ U ∈ S.powerset.filter (fun U ↦ (U ∩ X).card < K),
        weight S (fun i ↦ 1 - p i) U := by
  classical
  apply Finset.sum_bij' (fun T _ ↦ S \ T) (fun U _ ↦ S \ U)
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢
    have hTS := Finset.mem_powerset.mp hT.1
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    have heq : (S \ T) ∩ X = X \ T := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hxS, hxT⟩, hxX⟩
        exact ⟨hxX, hxT⟩
      · rintro ⟨hxX, hxT⟩
        exact ⟨⟨hXS hxX, hxT⟩, hxX⟩
    rw [heq]
    exact hT.2
  · intro U hU
    rw [Finset.mem_filter] at hU ⊢
    have hUS := Finset.mem_powerset.mp hU.1
    refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    have heq : X \ (S \ U) = U ∩ X := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      constructor
      · rintro ⟨hxX, hnot⟩
        have hxU : x ∈ U := by
          by_contra hxUnot
          exact hnot ⟨hXS hxX, hxUnot⟩
        exact ⟨hxU, hxX⟩
      · rintro ⟨hxU, hxX⟩
        exact ⟨hxX, fun hx ↦ hx.2 hxU⟩
    rw [heq]
    exact hU.2
  · intro T hT
    have hTS := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    exact Finset.sdiff_sdiff_eq_self hTS
  · intro U hU
    have hUS := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
    exact Finset.sdiff_sdiff_eq_self hUS
  · intro T hT
    have hTS := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    exact weight_complement_general S T p hTS

noncomputable def complementDiversityTailBound (h k : ℕ) : ℝ :=
  let r : ℝ := ((h : ℝ) - 2) / ((h : ℝ) - 1)
  Real.exp
    ((r * ((1 - r) / (2 * r)) +
      (1 / (1 + ((1 - r) / (2 * r))) - 1)) *
        (((k : ℝ) * ((h : ℝ) - 1)) / h))

private lemma complement_diversity_tail
    {A X : Finset ℕ} {k h : ℕ}
    (hh : 3 ≤ h) (hXA : X ⊆ A) (hkX : k ≤ X.card) :
    (∑ T ∈ A.powerset.filter
        (fun T ↦ (X \ T).card < k * (h - 2) / h),
        weight A (fun _ ↦ ((h : ℝ)⁻¹)) T) ≤
      complementDiversityTailBound h k := by
  rw [sum_weight_complement_inter A X (fun _ ↦ ((h : ℝ)⁻¹)) hXA]
  let q : ℕ → ℝ := fun _ ↦ 1 - (h : ℝ)⁻¹
  let r : ℝ := ((h : ℝ) - 2) / ((h : ℝ) - 1)
  have hq0 : ∀ i ∈ A, 0 ≤ q i := by
    intro i hi
    dsimp [q]
    have hinv : (h : ℝ)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity)).2 (by exact_mod_cast (show 1 ≤ h by omega))
    linarith
  have hq1 : ∀ i ∈ A, q i ≤ 1 := by
    intro i hi
    dsimp [q]
    have hinv : 0 ≤ (h : ℝ)⁻¹ := by positivity
    linarith
  have hr0 : 0 < r := by
    dsimp [r]
    have hhR : (3 : ℝ) ≤ h := by exact_mod_cast hh
    exact div_pos (by linarith) (by linarith)
  have hr1 : r < 1 := by
    dsimp [r]
    have hhR : (3 : ℝ) ≤ h := by exact_mod_cast hh
    rw [div_lt_one (by linarith)]
    linarith
  have hKreal : ((k * (h - 2) / h : ℕ) : ℝ) ≤
      r * (((X.card : ℝ) * (h - 1)) / h) := by
    calc
      ((k * (h - 2) / h : ℕ) : ℝ) ≤
          ((k * (h - 2) : ℕ) : ℝ) / h := Nat.cast_div_le
      _ = (k : ℝ) * ((h : ℝ) - 2) / h := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ h)]
        norm_num
      _ ≤ (X.card : ℝ) * ((h : ℝ) - 2) / h := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hkX)
        have hhR : (3 : ℝ) ≤ h := by exact_mod_cast hh
        linarith
      _ = r * (((X.card : ℝ) * (h - 1)) / h) := by
        dsimp [r]
        have hhm1 : (0 : ℝ) < h - 1 := by
          have hhR : (3 : ℝ) ≤ h := by exact_mod_cast hh
          linarith
        field_simp
  have htail := lower_inter_tail_chernoff A X q hXA hq0 hq1
    (K := k * (h - 2) / h)
    (EW := ((X.card : ℝ) * (h - 1)) / h) (r := r)
    (by
      dsimp [q]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hhR : (h : ℝ) ≠ 0 := by positivity
      field_simp
      )
    hr0 hr1 hKreal
  have hcoeffNeg := lower_exponent_neg hr0 hr1
  have hbase : ((k : ℝ) * (h - 1)) / h ≤
      ((X.card : ℝ) * (h - 1)) / h := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hkX)
    have hhR : (3 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  calc
    (∑ U ∈ A.powerset.filter
        (fun U ↦ (U ∩ X).card < k * (h - 2) / h), weight A q U) ≤
        Real.exp
          ((r * ((1 - r) / (2 * r)) +
            (1 / (1 + ((1 - r) / (2 * r))) - 1)) *
              (((X.card : ℝ) * (h - 1)) / h)) := htail
    _ ≤ complementDiversityTailBound h k := by
      unfold complementDiversityTailBound
      dsimp only
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left hbase hcoeffNeg.le

private lemma sample_diversity_tail
    {A X : Finset ℕ} {k h : ℕ}
    (hh : 2 ≤ h) (hXA : X ⊆ A) (hkX : k ≤ X.card) :
    (∑ T ∈ A.powerset.filter
        (fun T ↦ (T ∩ X).card < k / (2 * h)),
        weight A (fun _ ↦ ((h : ℝ)⁻¹)) T) ≤
      Real.exp (-(k : ℝ) / (12 * h)) := by
  let p : ℕ → ℝ := fun _ ↦ (h : ℝ)⁻¹
  have hp0 : ∀ i ∈ A, 0 ≤ p i := by
    intro i hi
    dsimp [p]
    positivity
  have hp1 : ∀ i ∈ A, p i ≤ 1 := by
    intro i hi
    dsimp [p]
    exact (inv_le_one₀ (by positivity)).2
      (by exact_mod_cast (show 1 ≤ h by omega))
  have hKreal : ((k / (2 * h) : ℕ) : ℝ) ≤
      (1 / 2 : ℝ) * ((X.card : ℝ) / h) := by
    calc
      ((k / (2 * h) : ℕ) : ℝ) ≤
          (k : ℝ) / ((2 * h : ℕ) : ℝ) := Nat.cast_div_le
      _ = (k : ℝ) / (2 * h) := by norm_num
      _ ≤ (X.card : ℝ) / (2 * h) := by
        gcongr
      _ = (1 / 2 : ℝ) * ((X.card : ℝ) / h) := by ring
  have hchern := lower_inter_tail_chernoff A X p hXA hp0 hp1
    (K := k / (2 * h)) (EW := (X.card : ℝ) / h)
    (r := (1 / 2 : ℝ)) (by simp [p]; ring)
    (by norm_num) (by norm_num) hKreal
  calc
    (∑ T ∈ A.powerset.filter
        (fun T ↦ (T ∩ X).card < k / (2 * h)), weight A p T) ≤
        Real.exp (-(X.card : ℝ) / (12 * h)) := by
          convert hchern using 1 <;> norm_num <;> ring
    _ ≤ Real.exp (-(k : ℝ) / (12 * h)) := by
      apply Real.exp_le_exp.mpr
      have hcast : (k : ℝ) ≤ X.card := by exact_mod_cast hkX
      exact div_le_div_of_nonneg_right (neg_le_neg hcast) (by positivity)

/-- One exact cell together with a quantitatively diverse remainder.  This
is the induction step for the balanced `8ℓ`-cell partition used in CFP
Lemmas 5.4 and 5.6. -/
theorem exists_fixedCard_diverse_split
    {A : Finset ℕ} {k N h s : ℕ}
    (hh : 3 ≤ h) (hcardA : A.card = h * s)
    (hA : DiverseNat A k)
    (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ N)
    (hprob : ((h * s + 1 : ℕ) : ℝ) * (2 * (N + 1)) *
      (Real.exp (-(k : ℝ) / (12 * h)) +
        complementDiversityTailBound h k) < 1) :
    ∃ B ∈ A.powersetCard s,
      DiverseNat B (k / (2 * h)) ∧
      DiverseNat (A \ B) (k * (h - 2) / h) := by
  classical
  let D := Finset.Icc 2 N
  let p : ℕ → ℝ := fun _ ↦ (h : ℝ)⁻¹
  let X : ℕ → Finset ℕ := fun d ↦ A.filter fun a ↦ ¬d ∣ a
  let bad : Bool × ℕ → Finset ℕ → Prop := fun e T ↦
    if e.1 then (X e.2 \ T).card < k * (h - 2) / h
    else (T ∩ X e.2).card < k / (2 * h)
  let b : Bool × ℕ → ℝ := fun e ↦
    if e.1 then complementDiversityTailBound h k
    else Real.exp (-(k : ℝ) / (12 * h))
  have hp0 : ∀ i ∈ A, 0 ≤ p i := by
    intro i hi
    dsimp [p]
    positivity
  have hp1 : ∀ i ∈ A, p i ≤ 1 := by
    intro i hi
    dsimp [p]
    exact (inv_le_one₀ (by positivity)).2
      (by exact_mod_cast (show 1 ≤ h by omega))
  have hkA : k ≤ A.card :=
    (hA 2 (by omega)).trans (Finset.card_le_card (Finset.filter_subset _ _))
  have htail : ∀ e ∈ Finset.univ.product D,
      (∑ T ∈ A.powerset.filter (bad e), weight A p T) ≤ b e := by
    rintro ⟨side, d⟩ hed
    have hdD : d ∈ D := (Finset.mem_product.mp hed).2
    have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hdD).1
    have hXd : k ≤ (X d).card := hA d hd2
    have hXsub : X d ⊆ A := Finset.filter_subset _ _
    cases side with
    | false =>
        simpa [bad, b, p] using sample_diversity_tail (h := h) (by omega) hXsub hXd
    | true =>
        simpa [bad, b, p] using complement_diversity_tail (h := h) hh hXsub hXd
  have hDcard : D.card ≤ N + 1 := by
    calc
      D.card ≤ (Finset.Icc 0 N).card := by
        apply Finset.card_le_card
        intro d hd
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hd).2⟩
      _ = N + 1 := by simp
  have hbnonneg (e : Bool × ℕ) : 0 ≤ b e := by
    rcases e with ⟨side, d⟩
    cases side
    · simp only [b, Bool.false_eq_true, if_false]
      exact (Real.exp_pos _).le
    · simp only [b, if_true]
      unfold complementDiversityTailBound
      exact (Real.exp_pos _).le
  have hsumB :
      (∑ e ∈ Finset.univ.product D, b e) ≤
        (2 * (N + 1) : ℕ) *
          (Real.exp (-(k : ℝ) / (12 * h)) +
            complementDiversityTailBound h k) := by
    calc
      (∑ e ∈ Finset.univ.product D, b e) ≤
          ∑ _e ∈ Finset.univ.product D,
            (Real.exp (-(k : ℝ) / (12 * h)) +
              complementDiversityTailBound h k) := by
        apply Finset.sum_le_sum
        rintro ⟨side, d⟩ he
        cases side
        · change Real.exp (-(k : ℝ) / (12 * h)) ≤
              Real.exp (-(k : ℝ) / (12 * h)) +
                complementDiversityTailBound h k
          exact le_add_of_nonneg_right (by
            unfold complementDiversityTailBound
            exact (Real.exp_pos _).le)
        · change complementDiversityTailBound h k ≤
              Real.exp (-(k : ℝ) / (12 * h)) +
                complementDiversityTailBound h k
          exact le_add_of_nonneg_left (Real.exp_pos _).le
      _ = ((Finset.univ.product D).card : ℕ) *
            (Real.exp (-(k : ℝ) / (12 * h)) +
              complementDiversityTailBound h k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (N + 1) : ℕ) *
            (Real.exp (-(k : ℝ) / (12 * h)) +
              complementDiversityTailBound h k) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast (show (((Finset.univ : Finset Bool).product D).card) ≤
              2 * (N + 1) by
            simpa using Nat.mul_le_mul_left 2 hDcard)
        · exact add_nonneg (Real.exp_pos _).le (by
            unfold complementDiversityTailBound
            exact (Real.exp_pos _).le)
  have hlayerLower := fixed_layer_mass_lower (A := A) (by omega) hcardA
  have hlayer :
      (∑ T ∈ A.powersetCard s, weight A p T) >
        ∑ e ∈ Finset.univ.product D, b e := by
    have hsmall : (2 * (N + 1) : ℕ) *
        (Real.exp (-(k : ℝ) / (12 * h)) +
          complementDiversityTailBound h k) <
        (1 : ℝ) / (h * s + 1) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < h * s + 1)]
      simpa [Nat.cast_add, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
        using hprob
    have hpdef : p = fun _ ↦ ((h : ℝ)⁻¹) := rfl
    rw [hpdef]
    exact (hsumB.trans_lt hsmall).trans_le hlayerLower
  obtain ⟨B, hBcard, hgood⟩ :=
    exists_fixedCard_avoiding_weighted_bad A s (Finset.univ.product D)
      p hp0 hp1 bad b htail hlayer
  have hBA := (Finset.mem_powersetCard.mp hBcard).1
  have hBsize := (Finset.mem_powersetCard.mp hBcard).2
  have hks : k / (2 * h) ≤ s := by
    rw [hcardA] at hkA
    calc
      k / (2 * h) ≤ k / h := Nat.div_le_div_left (by nlinarith) (by omega)
      _ ≤ s := (Nat.div_le_iff_le_mul (by omega)).2 (by
        calc
          k ≤ h * s := hkA
          _ = s * h := by ring
          _ ≤ s * h + h - 1 := by omega)
  have hcompSize : (A \ B).card = (h - 1) * s := by
    rw [Finset.card_sdiff_of_subset hBA, hcardA, hBsize]
    have hmul : h * s = (h - 1) * s + s := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ h by omega)]
      ring
    rw [hmul]
    exact Nat.add_sub_cancel_right _ _
  have hkcomp : k * (h - 2) / h ≤ (h - 1) * s := by
    rw [hcardA] at hkA
    calc
      k * (h - 2) / h ≤ (h * s) * (h - 2) / h :=
        Nat.div_le_div_right (Nat.mul_le_mul_right (h - 2) hkA)
      _ = s * (h - 2) := by
        rw [show (h * s) * (h - 2) = h * (s * (h - 2)) by ring]
        exact Nat.mul_div_cancel_left _ (by omega)
      _ ≤ (h - 1) * s := by
        rw [mul_comm (h - 1) s]
        exact Nat.mul_le_mul_left s (by omega)
  refine ⟨B, hBcard, ?_, ?_⟩
  · intro d hd2
    by_cases hdN : d ≤ N
    · have hgood' := hgood (false, d)
          (Finset.mem_product.mpr ⟨by simp, Finset.mem_Icc.mpr ⟨hd2, hdN⟩⟩)
      change ¬ (B ∩ X d).card < k / (2 * h) at hgood'
      have hinter : B ∩ X d = B.filter fun a ↦ ¬d ∣ a := by
        ext a
        simp only [X, Finset.mem_inter, Finset.mem_filter]
        constructor
        · rintro ⟨haB, haA, hda⟩
          exact ⟨haB, hda⟩
        · rintro ⟨haB, hda⟩
          exact ⟨haB, hBA haB, hda⟩
      rw [hinter] at hgood'
      omega
    · have hall : B.filter (fun a ↦ ¬d ∣ a) = B := by
        apply Finset.filter_eq_self.mpr
        intro a haB hda
        exact hdN ((Nat.le_of_dvd (hrange a (hBA haB)).1 hda).trans
          (hrange a (hBA haB)).2)
      rw [hall, hBsize]
      exact hks
  · intro d hd2
    by_cases hdN : d ≤ N
    · have hgood' := hgood (true, d)
          (Finset.mem_product.mpr ⟨by simp, Finset.mem_Icc.mpr ⟨hd2, hdN⟩⟩)
      change ¬ (X d \ B).card < k * (h - 2) / h at hgood'
      have hdiff : X d \ B = (A \ B).filter fun a ↦ ¬d ∣ a := by
        ext a
        simp only [X, Finset.mem_sdiff, Finset.mem_filter]
        tauto
      rw [hdiff] at hgood'
      omega
    · have hall : (A \ B).filter (fun a ↦ ¬d ∣ a) = A \ B := by
        apply Finset.filter_eq_self.mpr
        intro a haC hda
        have haA := (Finset.mem_sdiff.mp haC).1
        exact hdN ((Nat.le_of_dvd (hrange a haA).1 hda).trans (hrange a haA).2)
      rw [hall, hcompSize]
      exact hkcomp

/-! ## The truncated form consumed by divisor extraction -/

/-- Diversity only for moduli in the finite interval `2 ≤ e ≤ M`.  This is
the exact form supplied by the divisor-extraction ledger once one knows
`d * M ≤ B`; it is intentionally weaker than `DiverseNat`. -/
def DiverseUpTo (A : Finset ℕ) (k M : ℕ) : Prop :=
  ∀ e : ℕ, 1 < e → e ≤ M →
    k ≤ (A.filter fun a ↦ ¬e ∣ a).card

lemma DiverseNat.diverseUpTo {A : Finset ℕ} {k M : ℕ}
    (hA : DiverseNat A k) : DiverseUpTo A k M := by
  intro e he _heM
  exact hA e he

/-- The quantitative output of `exists_divisorExtraction` implies
truncated diversity at every modulus for which the extraction cutoff is
available. -/
lemma diverseUpTo_of_divisorExtraction
    {Z : Finset ℕ} {d B L K M : ℕ}
    (hcutoff : d * M ≤ B)
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card) :
    DiverseUpTo Z L M := by
  intro e he heM
  have hde : d * e ≤ B :=
    (Nat.mul_le_mul_left d heM).trans hcutoff
  exact (Nat.le_add_right L (K * e)).trans (hdiverse e he hde)

lemma strongDiverseUpTo_of_divisorExtraction
    {Z : Finset ℕ} {d B L K M : ℕ}
    (hcutoff : d * M ≤ B)
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card) :
    DiverseUpTo Z (L + 2 * K) M := by
  intro e he heM
  have hde : d * e ≤ B :=
    (Nat.mul_le_mul_left d heM).trans hcutoff
  have he2 : 2 ≤ e := Nat.succ_le_iff.mp he
  have hscaled : L + 2 * K ≤ L + K * e := by
    simpa [Nat.mul_comm] using
      (Nat.add_le_add_left (Nat.mul_le_mul_right K he2) L)
  exact hscaled.trans (hdiverse e he hde)

/-- Source-facing fixed-cardinality random split.  Unlike
`exists_fixedCard_diverse_split`, this theorem assumes and preserves only
the finite divisor range controlled by the divisor-extraction cutoff. -/
theorem exists_fixedCard_diverse_split_upTo
    {A : Finset ℕ} {k M h s : ℕ}
    (hh : 3 ≤ h) (hcardA : A.card = h * s)
    (hA : DiverseUpTo A k M)
    (hprob : ((h * s + 1 : ℕ) : ℝ) * (2 * (M + 1)) *
      (Real.exp (-(k : ℝ) / (12 * h)) +
        complementDiversityTailBound h k) < 1) :
    ∃ B ∈ A.powersetCard s,
      DiverseUpTo B (k / (2 * h)) M ∧
      DiverseUpTo (A \ B) (k * (h - 2) / h) M := by
  classical
  let D := Finset.Icc 2 M
  let p : ℕ → ℝ := fun _ ↦ (h : ℝ)⁻¹
  let X : ℕ → Finset ℕ := fun e ↦ A.filter fun a ↦ ¬e ∣ a
  let bad : Bool × ℕ → Finset ℕ → Prop := fun e T ↦
    if e.1 then (X e.2 \ T).card < k * (h - 2) / h
    else (T ∩ X e.2).card < k / (2 * h)
  let b : Bool × ℕ → ℝ := fun e ↦
    if e.1 then complementDiversityTailBound h k
    else Real.exp (-(k : ℝ) / (12 * h))
  have hp0 : ∀ i ∈ A, 0 ≤ p i := by
    intro i hi
    dsimp [p]
    positivity
  have hp1 : ∀ i ∈ A, p i ≤ 1 := by
    intro i hi
    dsimp [p]
    exact (inv_le_one₀ (by positivity)).2
      (by exact_mod_cast (show 1 ≤ h by omega))
  have htail : ∀ e ∈ Finset.univ.product D,
      (∑ T ∈ A.powerset.filter (bad e), weight A p T) ≤ b e := by
    rintro ⟨side, e⟩ heD
    have heD' : e ∈ D := (Finset.mem_product.mp heD).2
    have heBounds := Finset.mem_Icc.mp heD'
    have hXe : k ≤ (X e).card := hA e (by omega) heBounds.2
    have hXsub : X e ⊆ A := Finset.filter_subset _ _
    cases side with
    | false =>
        simpa [bad, b, p] using
          sample_diversity_tail (h := h) (by omega) hXsub hXe
    | true =>
        simpa [bad, b, p] using
          complement_diversity_tail (h := h) hh hXsub hXe
  have hDcard : D.card ≤ M + 1 := by
    calc
      D.card ≤ (Finset.Icc 0 M).card := by
        apply Finset.card_le_card
        intro e he
        exact Finset.mem_Icc.mpr
          ⟨Nat.zero_le _, (Finset.mem_Icc.mp he).2⟩
      _ = M + 1 := by simp
  have hsumB :
      (∑ e ∈ Finset.univ.product D, b e) ≤
        (2 * (M + 1) : ℕ) *
          (Real.exp (-(k : ℝ) / (12 * h)) +
            complementDiversityTailBound h k) := by
    calc
      (∑ e ∈ Finset.univ.product D, b e) ≤
          ∑ _e ∈ Finset.univ.product D,
            (Real.exp (-(k : ℝ) / (12 * h)) +
              complementDiversityTailBound h k) := by
        apply Finset.sum_le_sum
        rintro ⟨side, e⟩ he
        cases side
        · change Real.exp (-(k : ℝ) / (12 * h)) ≤
              Real.exp (-(k : ℝ) / (12 * h)) +
                complementDiversityTailBound h k
          exact le_add_of_nonneg_right (by
            unfold complementDiversityTailBound
            exact (Real.exp_pos _).le)
        · change complementDiversityTailBound h k ≤
              Real.exp (-(k : ℝ) / (12 * h)) +
                complementDiversityTailBound h k
          exact le_add_of_nonneg_left (Real.exp_pos _).le
      _ = ((Finset.univ.product D).card : ℕ) *
            (Real.exp (-(k : ℝ) / (12 * h)) +
              complementDiversityTailBound h k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (M + 1) : ℕ) *
            (Real.exp (-(k : ℝ) / (12 * h)) +
              complementDiversityTailBound h k) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast (show
            (((Finset.univ : Finset Bool).product D).card) ≤
              2 * (M + 1) by
            simpa using Nat.mul_le_mul_left 2 hDcard)
        · exact add_nonneg (Real.exp_pos _).le (by
            unfold complementDiversityTailBound
            exact (Real.exp_pos _).le)
  have hlayerLower := fixed_layer_mass_lower (A := A) (by omega) hcardA
  have hlayer :
      (∑ T ∈ A.powersetCard s, weight A p T) >
        ∑ e ∈ Finset.univ.product D, b e := by
    have hsmall : (2 * (M + 1) : ℕ) *
        (Real.exp (-(k : ℝ) / (12 * h)) +
          complementDiversityTailBound h k) <
        (1 : ℝ) / (h * s + 1) := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < h * s + 1)]
      simpa [Nat.cast_add, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
        using hprob
    have hpdef : p = fun _ ↦ ((h : ℝ)⁻¹) := rfl
    rw [hpdef]
    exact (hsumB.trans_lt hsmall).trans_le hlayerLower
  obtain ⟨B, hBcard, hgood⟩ :=
    exists_fixedCard_avoiding_weighted_bad A s (Finset.univ.product D)
      p hp0 hp1 bad b htail hlayer
  have hBA := (Finset.mem_powersetCard.mp hBcard).1
  refine ⟨B, hBcard, ?_, ?_⟩
  · intro e he2 heM
    have hgood' := hgood (false, e)
      (Finset.mem_product.mpr
        ⟨by simp, Finset.mem_Icc.mpr ⟨by omega, heM⟩⟩)
    change ¬(B ∩ X e).card < k / (2 * h) at hgood'
    have hinter : B ∩ X e = B.filter fun a ↦ ¬e ∣ a := by
      ext a
      simp only [X, Finset.mem_inter, Finset.mem_filter]
      constructor
      · rintro ⟨haB, haA, hea⟩
        exact ⟨haB, hea⟩
      · rintro ⟨haB, hea⟩
        exact ⟨haB, hBA haB, hea⟩
    rw [hinter] at hgood'
    omega
  · intro e he2 heM
    have hgood' := hgood (true, e)
      (Finset.mem_product.mpr
        ⟨by simp, Finset.mem_Icc.mpr ⟨by omega, heM⟩⟩)
    change ¬(X e \ B).card < k * (h - 2) / h at hgood'
    have hdiff : X e \ B = (A \ B).filter fun a ↦ ¬e ∣ a := by
      ext a
      simp only [X, Finset.mem_sdiff, Finset.mem_filter]
      tauto
    rw [hdiff] at hgood'
    omega

/-! ## Iterating the exact split -/

/-- Diversity left after `i` exact cells have been removed.  At a stage
with `h-i` cells still available, the split theorem keeps the factor
`(h-i-2)/(h-i)` in the remainder. -/
def residualDiversity (k h : ℕ) : ℕ → ℕ
  | 0 => k
  | i + 1 =>
      residualDiversity k h i * (h - i - 2) / (h - i)

noncomputable def exactSplitFailureMass (N s h k : ℕ) : ℝ :=
  ((h * s + 1 : ℕ) : ℝ) * (2 * (N + 1)) *
    (Real.exp (-(k : ℝ) / (12 * h)) +
      complementDiversityTailBound h k)

lemma residualDiversity_shift (k h i : ℕ) :
    residualDiversity k h (i + 1) =
      residualDiversity (k * (h - 2) / h) (h - 1) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change residualDiversity k h (i + 1) * (h - (i + 1) - 2) /
          (h - (i + 1)) =
        residualDiversity (k * (h - 2) / h) (h - 1) i *
          ((h - 1) - i - 2) / ((h - 1) - i)
      rw [ih]
      have hindex : h - (i + 1) = (h - 1) - i := by omega
      rw [hindex]

/-- Iterated CFP random-diversity extraction.  It selects `count` disjoint
cells of the exact size `s`; every cell has the common requested diversity
`K`.  The hypotheses list the explicit finite exponential inequality and
the elementary diversity ledger at each stage. -/
theorem exists_disjoint_fixedCard_diverse_pieces
    {A : Finset ℕ} {k N h s count K : ℕ}
    (hcount : count + 2 ≤ h)
    (hcardA : A.card = h * s)
    (hA : DiverseNat A k)
    (hrange : ∀ a ∈ A, 0 < a ∧ a ≤ N)
    (hprob : ∀ i < count,
      exactSplitFailureMass N s (h - i) (residualDiversity k h i) < 1)
    (hK : ∀ i < count,
      K ≤ residualDiversity k h i / (2 * (h - i))) :
    ∃ parts : List (Finset ℕ),
      parts.length = count ∧
      parts.Pairwise (fun P Q ↦ Disjoint P Q) ∧
      ∀ P ∈ parts, P ⊆ A ∧ P.card = s ∧ DiverseNat P K := by
  induction count generalizing A k h with
  | zero =>
      exact ⟨[], by simp⟩
  | succ count ih =>
      have hh : 3 ≤ h := by omega
      have hprob0 : exactSplitFailureMass N s h k < 1 := by
        simpa [residualDiversity] using hprob 0 (by omega)
      obtain ⟨B, hBcard, hBdiv, hCdiv⟩ :=
        exists_fixedCard_diverse_split hh hcardA hA hrange (by
          simpa [exactSplitFailureMass] using hprob0)
      let C := A \ B
      let k' := k * (h - 2) / h
      have hBA := (Finset.mem_powersetCard.mp hBcard).1
      have hBsize := (Finset.mem_powersetCard.mp hBcard).2
      have hCcard : C.card = (h - 1) * s := by
        dsimp [C]
        rw [Finset.card_sdiff_of_subset hBA, hcardA, hBsize]
        have hmul : h * s = (h - 1) * s + s := by
          conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ h by omega)]
          ring
        rw [hmul]
        exact Nat.add_sub_cancel_right _ _
      have hCrange : ∀ a ∈ C, 0 < a ∧ a ≤ N := by
        intro a ha
        exact hrange a (Finset.mem_sdiff.mp ha).1
      have hprob' : ∀ i < count,
          exactSplitFailureMass N s ((h - 1) - i)
            (residualDiversity k' (h - 1) i) < 1 := by
        intro i hi
        have hold := hprob (i + 1) (by omega)
        rw [residualDiversity_shift] at hold
        have hindex : h - (i + 1) = (h - 1) - i := by omega
        rwa [hindex] at hold
      have hK' : ∀ i < count,
          K ≤ residualDiversity k' (h - 1) i /
            (2 * ((h - 1) - i)) := by
        intro i hi
        have hold := hK (i + 1) (by omega)
        rw [residualDiversity_shift] at hold
        have hindex : h - (i + 1) = (h - 1) - i := by omega
        rwa [hindex] at hold
      obtain ⟨parts, hlen, hpair, hparts⟩ :=
        ih (A := C) (k := k') (h := h - 1) (by omega) hCcard hCdiv
          hCrange hprob' hK'
      refine ⟨B :: parts, by simp [hlen], ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hpair⟩
        intro P hP
        rw [Finset.disjoint_left]
        intro x hxB hxP
        have hxC := (hparts P hP).1 hxP
        exact (Finset.mem_sdiff.mp hxC).2 hxB
      · intro P hP
        rw [List.mem_cons] at hP
        rcases hP with rfl | hP
        · refine ⟨hBA, hBsize, ?_⟩
          intro d hd
          exact (hK 0 (by omega)).trans (hBdiv d hd)
        · obtain ⟨hPC, hPcard, hPdiv⟩ := hparts P hP
          exact ⟨hPC.trans Finset.sdiff_subset, hPcard, hPdiv⟩

/-- Iterated exact-card extraction in the finite modulus range controlled by
the source divisor cutoff. -/
theorem exists_disjoint_fixedCard_diverse_pieces_upTo
    {A : Finset ℕ} {k M h s count K : ℕ}
    (hcount : count + 2 ≤ h)
    (hcardA : A.card = h * s)
    (hA : DiverseUpTo A k M)
    (hprob : ∀ i < count,
      exactSplitFailureMass M s (h - i) (residualDiversity k h i) < 1)
    (hK : ∀ i < count,
      K ≤ residualDiversity k h i / (2 * (h - i))) :
    ∃ parts : List (Finset ℕ),
      parts.length = count ∧
      parts.Pairwise (fun P Q ↦ Disjoint P Q) ∧
      ∀ P ∈ parts, P ⊆ A ∧ P.card = s ∧ DiverseUpTo P K M := by
  induction count generalizing A k h with
  | zero =>
      exact ⟨[], by simp⟩
  | succ count ih =>
      have hh : 3 ≤ h := by omega
      have hprob0 : exactSplitFailureMass M s h k < 1 := by
        simpa [residualDiversity] using hprob 0 (by omega)
      obtain ⟨B, hBcard, hBdiv, hCdiv⟩ :=
        exists_fixedCard_diverse_split_upTo hh hcardA hA (by
          simpa [exactSplitFailureMass] using hprob0)
      let C := A \ B
      let k' := k * (h - 2) / h
      have hBA := (Finset.mem_powersetCard.mp hBcard).1
      have hBsize := (Finset.mem_powersetCard.mp hBcard).2
      have hCcard : C.card = (h - 1) * s := by
        dsimp [C]
        rw [Finset.card_sdiff_of_subset hBA, hcardA, hBsize]
        have hmul : h * s = (h - 1) * s + s := by
          conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ h by omega)]
          ring
        rw [hmul]
        exact Nat.add_sub_cancel_right _ _
      have hprob' : ∀ i < count,
          exactSplitFailureMass M s ((h - 1) - i)
            (residualDiversity k' (h - 1) i) < 1 := by
        intro i hi
        have hold := hprob (i + 1) (by omega)
        rw [residualDiversity_shift] at hold
        have hindex : h - (i + 1) = (h - 1) - i := by omega
        rwa [hindex] at hold
      have hK' : ∀ i < count,
          K ≤ residualDiversity k' (h - 1) i /
            (2 * ((h - 1) - i)) := by
        intro i hi
        have hold := hK (i + 1) (by omega)
        rw [residualDiversity_shift] at hold
        have hindex : h - (i + 1) = (h - 1) - i := by omega
        rwa [hindex] at hold
      obtain ⟨parts, hlen, hpair, hparts⟩ :=
        ih (A := C) (k := k') (h := h - 1) (by omega) hCcard hCdiv
          hprob' hK'
      refine ⟨B :: parts, by simp [hlen], ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hpair⟩
        intro P hP
        rw [Finset.disjoint_left]
        intro x hxB hxP
        have hxC := (hparts P hP).1 hxP
        exact (Finset.mem_sdiff.mp hxC).2 hxB
      · intro P hP
        rw [List.mem_cons] at hP
        rcases hP with rfl | hP
        · refine ⟨hBA, hBsize, ?_⟩
          intro e he heM
          exact (hK 0 (by omega)).trans (hBdiv e he heM)
        · obtain ⟨hPC, hPcard, hPdiv⟩ := hparts P hP
          exact ⟨hPC.trans Finset.sdiff_subset, hPcard, hPdiv⟩

/-- Exact application to the quotient set `Z` returned by
`exists_divisorExtraction`.  The source count `L + K*e` is converted to the
uniform initial diversity `L + 2*K`, and every later loss is recorded by
`residualDiversity`; no probabilistic premise remains hidden. -/
theorem exists_extracted_diverse_pieces
    {Z : Finset ℕ} {d B L K M h s count Kpiece : ℕ}
    (hcutoff : d * M ≤ B)
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card)
    (hcount : count + 2 ≤ h)
    (hcardZ : Z.card = h * s)
    (hprob : ∀ i < count,
      exactSplitFailureMass M s (h - i)
        (residualDiversity (L + 2 * K) h i) < 1)
    (hKpiece : ∀ i < count,
      Kpiece ≤ residualDiversity (L + 2 * K) h i /
        (2 * (h - i))) :
    ∃ parts : List (Finset ℕ),
      parts.length = count ∧
      parts.Pairwise (fun P Q ↦ Disjoint P Q) ∧
      ∀ P ∈ parts,
        P ⊆ Z ∧ P.card = s ∧ DiverseUpTo P Kpiece M := by
  exact exists_disjoint_fixedCard_diverse_pieces_upTo hcount hcardZ
    (strongDiverseUpTo_of_divisorExtraction hcutoff hdiverse)
    hprob hKpiece

end

end Erdos360.RandomDiversity

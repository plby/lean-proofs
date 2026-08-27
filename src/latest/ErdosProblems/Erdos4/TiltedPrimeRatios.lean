import ErdosProblems.Erdos4.FGKMTConditionalSurvival
import ErdosProblems.Erdos4.TiltedMoments

/-! Relative joint-survival estimates control exact inverse-probability weights. -/

namespace Erdos4.Tilted

open FGKMT

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem constant_survival_bounds (ν : FiniteLaw (Finset V)) {σ ε : ℝ} {A : ℕ}
    (hσ : 0 < σ) (hacc : SurvivalAccurate ν (fun _ => σ) A ε)
    {E : Finset V} (hE : E.card ≤ A) :
    (1 - ε) * σ ^ E.card ≤ survival ν E ∧ survival ν E ≤ (1 + ε) * σ ^ E.card := by
  have hh := abs_le.mp (hacc E hE)
  simp only [setProduct, Finset.prod_const] at hh
  constructor
  · exact (le_div_iff₀ (pow_pos hσ _)).mp (by linarith [hh.1])
  · exact (div_le_iff₀ (pow_pos hσ _)).mp (by linarith [hh.2])

theorem survival_pair_ratio_lower (ν : FiniteLaw (Finset V)) {σ ε : ℝ} {A : ℕ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hacc : SurvivalAccurate ν (fun _ => σ) A ε)
    (E F : Finset V) (hsize : E.card + F.card ≤ A) :
    1 - 4 * ε ≤ survival ν (E ∪ F) / (survival ν E * survival ν F) := by
  have hE := constant_survival_bounds ν hσ hacc (show E.card ≤ A by omega)
  have hF := constant_survival_bounds ν hσ hacc (show F.card ≤ A by omega)
  have hU := constant_survival_bounds ν hσ hacc ((Finset.card_union_le E F).trans hsize)
  have hposE := survival_pos_of_accurate ν (fun _ => σ) (fun _ => hσ) (by linarith : ε < 1)
    hacc (show E.card ≤ A by omega)
  have hposF := survival_pos_of_accurate ν (fun _ => σ) (fun _ => hσ) (by linarith : ε < 1)
    hacc (show F.card ≤ A by omega)
  have hk : 0 ≤ 1 - 4 * ε := by linarith
  have hcoef : (1 - 4 * ε) * (1 + ε) ^ 2 ≤ 1 - ε := by
    have hh : 0 ≤ ε * (1 + 7 * ε + 4 * ε ^ 2) := by positivity
    nlinarith
  have hprod : survival ν E * survival ν F ≤ (1 + ε) ^ 2 * (σ ^ E.card * σ ^ F.card) := by
    calc
      _ ≤ ((1 + ε) * σ ^ E.card) * ((1 + ε) * σ ^ F.card) :=
        mul_le_mul hE.2 hF.2 hposF.le (by positivity)
      _ = _ := by ring
  apply (le_div_iff₀ (mul_pos hposE hposF)).mpr
  calc
    _ ≤ (1 - 4 * ε) * ((1 + ε) ^ 2 * (σ ^ E.card * σ ^ F.card)) :=
      mul_le_mul_of_nonneg_left hprod hk
    _ ≤ (1 - ε) * (σ ^ E.card * σ ^ F.card) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ (1 - ε) * σ ^ (E ∪ F).card := by
      rw [← pow_add]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hσ.le hσ1 (Finset.card_union_le E F)) (by linarith)
    _ ≤ _ := hU.1

theorem survival_triple_ratio_upper_disjoint (ν : FiniteLaw (Finset V)) {σ ε : ℝ} {A : ℕ}
    (hσ : 0 < σ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hacc : SurvivalAccurate ν (fun _ => σ) A ε)
    (T E F : Finset V) (hsize : T.card + E.card + F.card ≤ A)
    (hTE : Disjoint T E) (hTF : Disjoint T F) (hEF : Disjoint E F) :
    survival ν (T ∪ E ∪ F) / (survival ν T * survival ν E * survival ν F) ≤ 1 + 16 * ε := by
  have hT := constant_survival_bounds ν hσ hacc (show T.card ≤ A by omega)
  have hE := constant_survival_bounds ν hσ hacc (show E.card ≤ A by omega)
  have hF := constant_survival_bounds ν hσ hacc (show F.card ≤ A by omega)
  have hcard : (T ∪ E ∪ F).card = T.card + E.card + F.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hTF, hEF⟩),
      Finset.card_union_of_disjoint hTE]
  have hU := (constant_survival_bounds ν hσ hacc (hcard.le.trans hsize)).2
  rw [hcard, pow_add, pow_add] at hU
  have hpos (S : Finset V) (hS : S.card ≤ A) : 0 < survival ν S :=
    survival_pos_of_accurate ν (fun _ => σ) (fun _ => hσ) (by linarith : ε < 1) hacc hS
  have hpT := hpos T (by omega)
  have hpE := hpos E (by omega)
  have hpF := hpos F (by omega)
  have hepos : 0 < 1 - ε := by linarith
  have hcoef : 1 + ε ≤ (1 + 16 * ε) * (1 - ε) ^ 3 := by
    have hh : 0 ≤ ε * (12 - 45 * ε) + ε ^ 3 * (47 - 16 * ε) :=
      add_nonneg (mul_nonneg hε0 (by linarith)) (mul_nonneg (pow_nonneg hε0 _) (by linarith))
    nlinarith
  have hprod : (1 - ε) ^ 3 * (σ ^ T.card * σ ^ E.card * σ ^ F.card) ≤
      survival ν T * survival ν E * survival ν F := by
    calc
      _ = ((1 - ε) * σ ^ T.card) * ((1 - ε) * σ ^ E.card) * ((1 - ε) * σ ^ F.card) := by ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul hT.1 hE.1 (by positivity) hpT.le) hF.1 (by positivity) (mul_pos hpT hpE).le
  apply (div_le_iff₀ (mul_pos (mul_pos hpT hpE) hpF)).mpr
  calc
    _ ≤ (1 + ε) * (σ ^ T.card * σ ^ E.card * σ ^ F.card) := hU
    _ ≤ ((1 + 16 * ε) * (1 - ε) ^ 3) * (σ ^ T.card * σ ^ E.card * σ ^ F.card) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (1 + 16 * ε) * ((1 - ε) ^ 3 * (σ ^ T.card * σ ^ E.card * σ ^ F.card)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

theorem survival_triple_ratio_upper (ν : FiniteLaw (Finset V)) {σ ε : ℝ} {r : ℕ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : ε ≤ 1 / 4)
    (hacc : SurvivalAccurate ν (fun _ => σ) (3 * r) ε)
    (T E F : Finset V) (hT : T.card ≤ r) (hE : E.card ≤ r) (hF : F.card ≤ r) :
    survival ν (T ∪ E ∪ F) / (survival ν T * survival ν E * survival ν F) ≤ 4 / σ ^ (3 * r) := by
  have hlo (S : Finset V) (hS : S.card ≤ r) : (3 / 4 : ℝ) * σ ^ r ≤ survival ν S := by
    calc
      _ ≤ (1 - ε) * σ ^ r := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (1 - ε) * σ ^ S.card := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hσ.le hσ1 hS) (by linarith)
      _ ≤ _ := (constant_survival_bounds ν hσ hacc (by omega)).1
  have hpT : 0 < survival ν T := (by positivity : 0 < (3 / 4 : ℝ) * σ ^ r).trans_le (hlo T hT)
  have hpE : 0 < survival ν E := (by positivity : 0 < (3 / 4 : ℝ) * σ ^ r).trans_le (hlo E hE)
  have hpF : 0 < survival ν F := (by positivity : 0 < (3 / 4 : ℝ) * σ ^ r).trans_le (hlo F hF)
  have hprod : σ ^ (3 * r) / 4 ≤ survival ν T * survival ν E * survival ν F := by
    calc
      _ ≤ ((3 / 4 : ℝ) * σ ^ r) * ((3 / 4 : ℝ) * σ ^ r) * ((3 / 4 : ℝ) * σ ^ r) := by
        rw [show 3 * r = r + r + r by omega, pow_add, pow_add]
        nlinarith [pow_pos hσ r]
      _ ≤ _ := mul_le_mul
        (mul_le_mul (hlo T hT) (hlo E hE) (by positivity) hpT.le)
        (hlo F hF) (by positivity) (mul_pos hpT hpE).le
  calc
    _ ≤ 1 / (survival ν T * survival ν E * survival ν F) :=
      div_le_div_of_nonneg_right (ν.prob_le_one _) (mul_pos (mul_pos hpT hpE) hpF).le
    _ ≤ 1 / (σ ^ (3 * r) / 4) := one_div_le_one_div_of_le (by positivity) hprod
    _ = _ := by ring

omit [DecidableEq V] in
theorem constant_survival_inverse_le (ν : FiniteLaw (Finset V)) {σ ε : ℝ} {r A : ℕ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : ε ≤ 1 / 2)
    (hacc : SurvivalAccurate ν (fun _ => σ) A ε) (hrA : r ≤ A)
    (E : Finset V) (hE : E.card ≤ r) : 1 / survival ν E ≤ 2 / σ ^ r := by
  have hprob : σ ^ r / 2 ≤ survival ν E := by
    calc
      _ ≤ (1 - ε) * σ ^ r := by nlinarith [pow_pos hσ r]
      _ ≤ (1 - ε) * σ ^ E.card := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hσ.le hσ1 hE) (by linarith)
      _ ≤ _ := (constant_survival_bounds ν hσ hacc (hE.trans hrA)).1
  exact (one_div_le_one_div_of_le (by positivity) hprob).trans_eq (by ring)

end Erdos4.Tilted

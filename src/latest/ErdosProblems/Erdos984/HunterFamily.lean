/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterRecurrence
import ErdosProblems.Erdos984.Eventual

/-!
# A subpower family of finite off-diagonal colorings

The construction is available at the scales `hunterN D = D^(D^2)`.  For an
arbitrary interval length we use the least dimension whose scale covers it.
The preceding scale then gives the lower bound needed to prove that the red
forbidden length `hunterX D = D^(100000D)` is subpolynomial.
-/

namespace Erdos984

noncomputable section

lemma hunterN_mono {D E : ℕ} (hD : 1 ≤ D) (hDE : D ≤ E) :
    hunterN D ≤ hunterN E := by
  unfold hunterN
  calc
    D ^ (D ^ 2) ≤ E ^ (D ^ 2) := Nat.pow_le_pow_left hDE _
    _ ≤ E ^ (E ^ 2) := by
      apply Nat.pow_le_pow_right (by omega)
      exact Nat.pow_le_pow_left hDE 2

lemma exists_hunterDimension (N : ℕ) :
    ∃ D : ℕ, 400 ≤ D ∧ N ≤ hunterN D := by
  refine ⟨N + 400, by omega, ?_⟩
  unfold hunterN
  calc
    N ≤ N + 400 := by omega
    _ = (N + 400) ^ 1 := by simp
    _ ≤ (N + 400) ^ ((N + 400) ^ 2) := by
      apply Nat.pow_le_pow_right (by omega)
      have hpos : 0 < (N + 400) ^ 2 := pow_pos (by omega) 2
      omega

/-- Least admissible dimension whose Hunter interval contains `[0,N)`. -/
noncomputable def hunterDimension (N : ℕ) : ℕ :=
  Nat.find (exists_hunterDimension N)

lemma hunterDimension_spec (N : ℕ) :
    400 ≤ hunterDimension N ∧ N ≤ hunterN (hunterDimension N) := by
  exact Nat.find_spec (exists_hunterDimension N)

lemma hunterDimension_gt_of_hunterN_lt {E N : ℕ}
    (hEN : hunterN E < N) : E < hunterDimension N := by
  by_contra hnot
  have hdimE : hunterDimension N ≤ E := by omega
  have hmono : hunterN (hunterDimension N) ≤ hunterN E :=
    hunterN_mono
      (le_trans (by norm_num) (hunterDimension_spec N).1) hdimE
  have hcover := (hunterDimension_spec N).2
  exact (not_lt_of_ge (hcover.trans hmono)) hEN

lemma hunterN_dimension_pred_lt {N : ℕ} (hN : hunterN 400 < N) :
    hunterN (hunterDimension N - 1) < N := by
  have hdim : 400 < hunterDimension N :=
    hunterDimension_gt_of_hunterN_lt (E := 400) hN
  by_contra hnot
  have hcandidate :
      400 ≤ hunterDimension N - 1 ∧
        N ≤ hunterN (hunterDimension N - 1) := by omega
  have hminimal := Nat.find_min (exists_hunterDimension N)
    (show hunterDimension N - 1 < hunterDimension N by omega)
  exact hminimal hcandidate

lemma three_le_hunterX (D : ℕ) (hD : 3 ≤ D) : 3 ≤ hunterX D := by
  unfold hunterX
  calc
    3 ≤ D := hD
    _ = D ^ 1 := by simp
    _ ≤ D ^ (100000 * D) := by
      apply Nat.pow_le_pow_right (by omega)
      omega

/-- The elementary comparison behind the subpower estimate. -/
lemma hunterX_pow_le_hunterN_pred (D q : ℕ) (hq : 0 < q)
    (hD : 400000 * q + 2 ≤ D) :
    hunterX D ^ q ≤ hunterN (D - 1) := by
  have hDtwo : 2 ≤ D := by omega
  have hbase : D ≤ (D - 1) ^ 2 := by
    have hD₁ : D = (D - 2) + 2 := by omega
    have hD₂ : D - 1 = (D - 2) + 1 := by omega
    calc
      D = (D - 2) + 2 := hD₁
      _ ≤ ((D - 2) + 1) ^ 2 := by
        nlinarith [Nat.zero_le (D - 2)]
      _ = (D - 1) ^ 2 := by rw [hD₂]
  have hlinear : 200000 * q ≤ D - 2 := by omega
  have hmul : 200000 * D * q ≤ (D - 2) * D := by
    calc
      200000 * D * q = (200000 * q) * D := by ring
      _ ≤ (D - 2) * D := Nat.mul_le_mul_right D hlinear
  have hquad : (D - 2) * D ≤ (D - 1) ^ 2 := by
    have hD₁ : D = (D - 2) + 2 := by omega
    have hD₂ : D - 1 = (D - 2) + 1 := by omega
    calc
      (D - 2) * D = (D - 2) * ((D - 2) + 2) :=
        congrArg (fun x ↦ (D - 2) * x) hD₁
      _ ≤ ((D - 2) + 1) ^ 2 := by
        nlinarith [Nat.zero_le (D - 2)]
      _ = (D - 1) ^ 2 := by rw [hD₂]
  have hexponent : 2 * (100000 * D) * q ≤ (D - 1) ^ 2 := by
    have := hmul.trans hquad
    nlinarith
  unfold hunterX hunterN
  rw [← pow_mul]
  calc
    D ^ (100000 * D * q) ≤ ((D - 1) ^ 2) ^ (100000 * D * q) :=
      Nat.pow_le_pow_left hbase _
    _ = (D - 1) ^ (2 * (100000 * D * q)) := by rw [← pow_mul]
    _ ≤ (D - 1) ^ ((D - 1) ^ 2) := by
      apply Nat.pow_le_pow_right (by omega)
      simpa only [mul_assoc] using hexponent

lemma GoodOffDiagonal.mono_interval
    {color : ℕ → Bool} {N N' H : ℕ}
    (hgood : GoodOffDiagonal color N' H) (hNN' : N ≤ N') :
    GoodOffDiagonal color N H := by
  constructor
  · intro a d hd hend
    exact hgood.1 a d hd (lt_of_lt_of_le hend hNN')
  · intro a d hd hend
    exact hgood.2 a d hd (lt_of_lt_of_le hend hNN')

lemma exists_hunter_goodOffDiagonal (D : ℕ) (hD : 400 ≤ D) :
    ∃ color : ℕ → Bool,
      GoodOffDiagonal color (hunterN D) (hunterX D) := by
  obtain ⟨R⟩ := exists_hunterRecurrenceData D hD
  exact exists_goodOffDiagonal_of_hunterRecurrenceData D (by omega) R

noncomputable def hunterFamilyColor (N : ℕ) : ℕ → Bool :=
  Classical.choose
    (exists_hunter_goodOffDiagonal (hunterDimension N)
      (hunterDimension_spec N).1)

def hunterFamilyH (N : ℕ) : ℕ := hunterX (hunterDimension N)

lemma hunterFamily_good (N : ℕ) :
    GoodOffDiagonal (hunterFamilyColor N) N (hunterFamilyH N) := by
  have hgood : GoodOffDiagonal (hunterFamilyColor N)
      (hunterN (hunterDimension N)) (hunterFamilyH N) := by
    simpa only [hunterFamilyColor, hunterFamilyH] using
      (Classical.choose_spec
        (exists_hunter_goodOffDiagonal (hunterDimension N)
          (hunterDimension_spec N).1))
  exact hgood.mono_interval (hunterDimension_spec N).2

lemma hunterFamily_three_le_H (N : ℕ) : 3 ≤ hunterFamilyH N :=
  three_le_hunterX (hunterDimension N)
    (le_trans (by norm_num) (hunterDimension_spec N).1)

lemma hunterFamily_eventually_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
      (hunterFamilyH N : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨q, hqε⟩ := exists_nat_gt ε⁻¹
  have hq : 0 < q := by
    have hinv : 0 < ε⁻¹ := inv_pos.mpr hε
    exact_mod_cast (show (0 : ℝ) < q by linarith)
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hqinverse : ((q : ℝ)⁻¹) < ε := by
    have := (inv_lt_inv₀ hqreal (inv_pos.mpr hε)).2 hqε
    simpa using this
  let E : ℕ := 400000 * q + 402
  refine ⟨hunterN E + 1, ?_⟩
  intro N hN _hNpos
  have hEN : hunterN E < N := by omega
  have hE400 : 400 ≤ E := by dsimp [E]; omega
  have hdimE : E < hunterDimension N :=
    hunterDimension_gt_of_hunterN_lt hEN
  have h400N : hunterN 400 < N :=
    lt_of_le_of_lt (hunterN_mono (by norm_num) hE400) hEN
  have hprevious : hunterN (hunterDimension N - 1) < N :=
    hunterN_dimension_pred_lt h400N
  have hpow : hunterFamilyH N ^ q ≤
      hunterN (hunterDimension N - 1) := by
    exact hunterX_pow_le_hunterN_pred (hunterDimension N) q hq (by
      dsimp [E] at hdimE
      omega)
  have hpowN : hunterFamilyH N ^ q ≤ N :=
    hpow.trans (Nat.le_of_lt hprevious)
  have hpowReal : (hunterFamilyH N : ℝ) ^ (q : ℕ) ≤ (N : ℝ) := by
    exact_mod_cast hpowN
  have hrpowReal : (hunterFamilyH N : ℝ) ^ (q : ℝ) ≤ (N : ℝ) := by
    simpa only [Real.rpow_natCast] using hpowReal
  have hroot : (hunterFamilyH N : ℝ) ≤ (N : ℝ) ^ (q : ℝ)⁻¹ :=
    (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) hqreal).2
      hrpowReal
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact hroot.trans
    (Real.rpow_le_rpow_of_exponent_le hNone hqinverse.le)

/-- Hunter's constructed family, in the exact form used by the assembly. -/
noncomputable def hunterEventualOffDiagonalData : EventualOffDiagonalData where
  H := hunterFamilyH
  three_le_H := hunterFamily_three_le_H
  coloring := hunterFamilyColor
  good := hunterFamily_good
  eventually_subpower := hunterFamily_eventually_subpower

end

end Erdos984

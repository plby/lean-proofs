/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTQuadraticMeanDecay
import ErdosProblems.Erdos4b.FGKMTPinnedRelativePrimeError

/-!
# The original prime mass compared with its actual positive main term

Both errors are now quantitative and uniform in every permitted dimension.
The excluded prime is selected before the varying arithmetic data.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

def primeMeanErrorEnvelope (d : ℝ) (x : ℕ) : ℝ :=
  Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) + Real.log (x : ℝ) ^ (-1 / 4 : ℝ)

theorem primeMeanErrorEnvelope_pos (d : ℝ) (x : ℕ) : 0 < primeMeanErrorEnvelope d x :=
  add_pos_of_pos_of_nonneg (Real.exp_pos _)
    (Real.rpow_nonneg (Real.log_natCast_nonneg x) _)

theorem relative_mul_main_error_le {A Q P s e f : ℝ} (hP : 0 < P) (hs : 0 < s)
    (hA : |A - s * Q| / (s * P) ≤ e) (hQ : |Q - P| / P ≤ f) :
    |A - s * P| / (s * P) ≤ e + f := by
  have hcancel : |s * Q - s * P| / (s * P) = |Q - P| / P := by
    rw [← mul_sub, abs_mul, abs_of_pos hs, mul_div_mul_left _ _ hs.ne']
  calc
    _ ≤ (|A - s * Q| + |s * Q - s * P|) / (s * P) :=
      div_le_div_of_nonneg_right (abs_sub_le _ _ _) (mul_pos hs hP).le
    _ = |A - s * Q| / (s * P) + |Q - P| / P := by rw [add_div, hcancel]
    _ ≤ _ := add_le_add hA hQ

theorem exists_commonPinnedPrimeMass_relative_decay :
    ∃ a d : ℝ, 0 < a ∧ 0 < d ∧ ∀ H b : ℝ, 0 < H → 0 < b →
      ∃ X0 : ℕ, 4 ≤ X0 ∧ ∀ x : ℕ, X0 ≤ x → ∃ B0 : ℕ,
        1 ≤ B0 ∧ (B0 : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) ∧
        (B0 = 1 ∨ B0.Prime) ∧ ∀ m W R Q : ℕ, ∀ y : ℝ,
          1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
          1 < R → R ≤ x → 1 ≤ Real.log (R : ℝ) →
          b * Real.log (x : ℝ) ≤ Real.log (R : ℝ) →
          0 < W → B0.Coprime W → Q.Coprime W →
          W * R ^ 2 ≤ x / 2 + 1 → ((W * R ^ 2 : ℕ) : ℝ) ≤ vaughanCubeRoot x →
          (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
          (W : ℝ) ≤ Real.exp (H * (m + 1 : ℕ) ^ 2) →
          Q.Prime → R < Q → (∀ q : ℕ, q.Prime → q ∣ W → q ≤ x / 2) →
          (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ B0 * W) →
          ∀ h : Fin (m + 1) → ℕ, Function.Injective h → (∀ i, h i < 2 * (m + 1) ^ 2) →
          ∀ j : Fin (m + 1), (Q : ℝ) ≤ y → (h j : ℝ) * x ≤ y →
          ∀ n : ℤ, preSieveCondition W (fun i => (h i : ℤ)) n →
          |commonPinnedPrimeMass m W (B0 * W) R Q (x / 2) x y h j -
              commonPinnedPrimeMainTerm m W (B0 * W) R Q (x / 2) x h j| /
            commonPinnedPrimeMainTerm m W (B0 * W) R Q (x / 2) x h j ≤
              primeMeanErrorEnvelope d x := by
  obtain ⟨a, d, ha, hd, hprogress⟩ := exists_commonPinnedPrimeMass_relative_progression_error
  refine ⟨a, d, ha, hd, ?_⟩
  intro H b hH hb
  obtain ⟨Xa, hXa, herror⟩ := hprogress H hH
  obtain ⟨Xq, hquad⟩ := eventually_atTop.mp
    (eventually_commonPinnedQuadratic_relative_decay ha.le hH.le hb)
  obtain ⟨Xp, hmain⟩ := eventually_atTop.mp
    (eventually_commonPinnedPrimeMainTerm_exp_lower hH (by norm_num : (0 : ℝ) < 1))
  refine ⟨max Xa (max Xq Xp), hXa.trans (le_max_left _ _), ?_⟩
  intro x hx
  have hxa : Xa ≤ x := (le_max_left _ _).trans hx
  have hxq : Xq ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxp : Xp ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  obtain ⟨B0, hB0pos, hB0bound, hB0, hbound⟩ := herror x hxa
  refine ⟨B0, hB0pos, hB0bound, hB0, ?_⟩
  intro m W R Q y hm hlog hR hRx hRlog hRlower hW hBW hQW hmod hcube hdim hsize
    hQ hRQ hWsmall hsmall h hinj hshift j hQy hxy n hn
  have hBpos : 0 < B0 := by omega
  have hp := commonPinnedMainTerm_pos hm hlog (Nat.mul_pos hBpos hW) hR hsmall
  have hfull := hmain x hxp m B0 W R Q hm hlog hdim hB0 hW hBW hQW
    hRlog hsmall hsize h j n hn
  have hfullpos : 0 < commonPinnedPrimeMainTerm m W (B0 * W) R Q (x / 2) x h j :=
    (mul_pos hxpos (Real.exp_pos _)).trans_le hfull
  have hs : 0 < primePreSieveDensity W Q (fun i => (h i : ℤ)) j *
      (commonPinnedPrimeSet (x / 2) x).card := pos_of_mul_pos_left hfullpos hp.le
  have he := hbound m W R Q y hm hlog hR hRlog hW hBW hQW hmod hcube hdim hsize
    hQ hRQ hWsmall hsmall h hinj hshift j hQy hxy n hn
  have hq := hquad x hxq m B0 W R hm hlog hBpos hW hR hRx hB0bound hsize
    hdim hRlower hsmall j
  exact relative_mul_main_error_le hp hs he hq

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.relative_mul_main_error_le
#print axioms Erdos4b.FGKMT.exists_commonPinnedPrimeMass_relative_decay

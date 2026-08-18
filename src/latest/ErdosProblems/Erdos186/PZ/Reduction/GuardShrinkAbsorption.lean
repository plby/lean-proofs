/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Asymptotic

/-!
# Absorbing a guarded shrink trace

This is the scalar power estimate used at the population stopping boundary
in Pham--Zakharov Lemma 10.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

/-- If a trace has crossed the population guard, then all but the bounded
number of dimension-changing moves contribute shrink factors.  The source
relations `gamma <= delta^K` and `m^(-1/3) <= gamma` convert those factors
into the displayed negative power of the original population. -/
theorem guarded_shrink_power_bound
    (m L changes shrinks K changeCap : ℕ) (δ γ τ β : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hγ0 : 0 < γ) (hγδ : γ ≤ δ ^ K)
    (hγlower : Real.rpow (m : ℝ) (-(1 / 3 : ℝ)) ≤ γ)
    (hguard : δ ^ (L + 1) * (m : ℝ) ≤ Real.rpow (m : ℝ) τ)
    (hlength : L = changes + shrinks) (hchanges : changes ≤ changeCap)
    (hm : 2 ≤ m) :
    γ ^ shrinks * Real.rpow (m : ℝ) β ≤
      Real.rpow (m : ℝ)
        (β - (K : ℝ) * (1 - τ) + ((changeCap + 1 : ℕ) : ℝ) / 3) := by
  let c : ℕ := changeCap + 1
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hδnonneg : 0 ≤ δ := hδ0.le
  have hγnonneg : 0 ≤ γ := hγ0.le
  have hrpowPow : ∀ (x : ℝ) (n : ℕ),
      (Real.rpow (m : ℝ) x) ^ n =
        Real.rpow (m : ℝ) (x * (n : ℝ)) := by
    intro x n
    have hnat := Real.rpow_natCast (Real.rpow (m : ℝ) x) n
    have hmul : Real.rpow (m : ℝ) (x * (n : ℝ)) =
        Real.rpow (Real.rpow (m : ℝ) x) (n : ℝ) :=
      Real.rpow_mul hmpos.le x (n : ℝ)
    exact hnat.symm.trans hmul.symm
  have hguardBase : δ ^ (L + 1) ≤
      Real.rpow (m : ℝ) (τ - 1) := by
    calc
      δ ^ (L + 1) ≤ Real.rpow (m : ℝ) τ / (m : ℝ) :=
        (le_div_iff₀ hmpos).2 hguard
      _ = Real.rpow (m : ℝ) τ / Real.rpow (m : ℝ) 1 := by simp
      _ = Real.rpow (m : ℝ) (τ - 1) :=
        (Real.rpow_sub hmpos τ 1).symm
  have hlength' : L + 1 ≤ shrinks + c := by
    dsimp [c]
    omega
  have hexponents : K * (L + 1) ≤ K * (shrinks + c) :=
    Nat.mul_le_mul_left K hlength'
  have htotal : γ ^ (shrinks + c) ≤
      Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) := by
    calc
      γ ^ (shrinks + c) ≤ (δ ^ K) ^ (shrinks + c) :=
        pow_le_pow_left₀ hγnonneg hγδ _
      _ = δ ^ (K * (shrinks + c)) := by rw [pow_mul]
      _ ≤ δ ^ (K * (L + 1)) :=
        pow_le_pow_of_le_one hδnonneg hδ1 hexponents
      _ = (δ ^ (L + 1)) ^ K := by
        rw [Nat.mul_comm K (L + 1)]
        exact pow_mul δ (L + 1) K
      _ ≤ (Real.rpow (m : ℝ) (τ - 1)) ^ K :=
        pow_le_pow_left₀ (pow_nonneg hδnonneg _) hguardBase _
      _ = Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) := hrpowPow _ _
  have hgammaPow : γ ^ shrinks * γ ^ c ≤
      Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) := by
    simpa [pow_add] using htotal
  have hgammaC : 0 < γ ^ c := pow_pos hγ0 _
  have hshrinkDiv : γ ^ shrinks ≤
      Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) / γ ^ c :=
    (le_div_iff₀ hgammaC).2 hgammaPow
  have hlowerPow : (Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ c ≤ γ ^ c :=
    pow_le_pow_left₀ (Real.rpow_nonneg hmpos.le _) hγlower _
  have hlowerPowPos : 0 < (Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ c := by
    exact pow_pos (Real.rpow_pos_of_pos hmpos _) _
  have hinv : (γ ^ c)⁻¹ ≤
      ((Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ c)⁻¹ := by
    exact (inv_le_inv₀ hgammaC hlowerPowPos).2 hlowerPow
  have hinvPower :
      ((Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ c)⁻¹ =
        Real.rpow (m : ℝ) ((c : ℝ) / 3) := by
    calc
      ((Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ c)⁻¹ =
          (Real.rpow (m : ℝ) ((-(1 / 3 : ℝ)) * (c : ℝ)))⁻¹ := by
            rw [hrpowPow]
      _ = Real.rpow (m : ℝ) (-((-(1 / 3 : ℝ)) * (c : ℝ))) :=
        (Real.rpow_neg hmpos.le _).symm
      _ = Real.rpow (m : ℝ) ((c : ℝ) / 3) := by
        congr 1
        ring
  have hshrink : γ ^ shrinks ≤
      Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) *
        Real.rpow (m : ℝ) ((c : ℝ) / 3) := by
    calc
      γ ^ shrinks ≤
          Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) / γ ^ c := hshrinkDiv
      _ = Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) * (γ ^ c)⁻¹ :=
        div_eq_mul_inv _ _
      _ ≤ Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) *
          ((Real.rpow (m : ℝ) (-(1 / 3 : ℝ))) ^ c)⁻¹ := by
        gcongr
        exact Real.rpow_nonneg hmpos.le _
      _ = Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) *
          Real.rpow (m : ℝ) ((c : ℝ) / 3) := by rw [hinvPower]
  calc
    γ ^ shrinks * Real.rpow (m : ℝ) β ≤
        (Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) *
          Real.rpow (m : ℝ) ((c : ℝ) / 3)) *
            Real.rpow (m : ℝ) β := by
              gcongr
              exact Real.rpow_nonneg hmpos.le _
    _ = Real.rpow (m : ℝ)
        (β - (K : ℝ) * (1 - τ) + ((changeCap + 1 : ℕ) : ℝ) / 3) := by
      calc
        (Real.rpow (m : ℝ) ((τ - 1) * (K : ℝ)) *
              Real.rpow (m : ℝ) ((c : ℝ) / 3)) *
            Real.rpow (m : ℝ) β =
          Real.rpow (m : ℝ) (((τ - 1) * (K : ℝ)) + (c : ℝ) / 3) *
            Real.rpow (m : ℝ) β := by
              exact congrArg (fun z ↦ z * Real.rpow (m : ℝ) β)
                (Real.rpow_add hmpos _ _).symm
        _ = Real.rpow (m : ℝ)
            ((((τ - 1) * (K : ℝ)) + (c : ℝ) / 3) + β) := by
              exact (Real.rpow_add hmpos _ _).symm
        _ = Real.rpow (m : ℝ)
            (β - (K : ℝ) * (1 - τ) + ((changeCap + 1 : ℕ) : ℝ) / 3) := by
              dsimp [c]
              congr 1
              ring

end

end Erdos186.PZ.Reduction

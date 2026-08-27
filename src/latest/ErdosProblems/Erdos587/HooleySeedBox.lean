import ErdosProblems.Erdos587.HooleyGeneratedSeed

/-! # A coefficient box containing the index periods of the generated lattice -/

namespace Erdos587.GeneralizedAP

noncomputable def deltaSeedBox {d : ℕ} (L : Fin d → ℕ) (I : ℕ) : ConvexProgression :=
  (GeneralizedAP.mk d 0 (fun _ => 0) (fun i => I * (L i + 1))).toConvexProgression

lemma deltaSeedBox_mem_iff {d : ℕ} (L : Fin d → ℕ) (I : ℕ) (x : Fin d → ℝ) :
    x ∈ (deltaSeedBox L I).body ↔ ∀ i, |x i| ≤ ((I * (L i + 1) + 1 : ℕ) : ℝ) := by
  change ((fun i => -(((I * (L i + 1) : ℕ) : ℝ) + 1)) ≤ x ∧
    x ≤ fun i => ((I * (L i + 1) : ℕ) : ℝ) + 1) ↔ _
  simp only [Pi.le_def, Nat.cast_add, Nat.cast_one, abs_le, forall_and]

lemma deltaSeedBox_period {d : ℕ} (L : Fin d → ℕ)
    (Γ : AddSubgroup (Fin d → ℤ)) (i : Fin d) :
    @intCastVec d (Γ.index • Pi.single i (1 : ℤ)) ∈ (deltaSeedBox L Γ.index).body := by
  classical
  dsimp only [deltaSeedBox, toConvexProgression, Set.mem_Icc, Pi.le_def, intCastVec]
  constructor <;> intro j
  · change -(((Γ.index * (L j + 1) : ℕ) : ℝ) + 1) ≤
      ((Γ.index • Pi.single i (1 : ℤ) : Fin d → ℤ) j : ℝ)
    have hnonneg : (0 : ℝ) ≤ ((Γ.index • Pi.single i (1 : ℤ) : Fin d → ℤ) j : ℝ) := by
      by_cases hij : j = i <;> simp [hij]
    have hleft : -(((Γ.index * (L j + 1) : ℕ) : ℝ) + 1) ≤ 0 := neg_nonpos.mpr (by positivity)
    exact hleft.trans hnonneg
  · change ((Γ.index • Pi.single i (1 : ℤ) : Fin d → ℤ) j : ℝ) ≤
      ((Γ.index * (L j + 1) : ℕ) : ℝ) + 1
    by_cases hij : j = i
    · subst j
      simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, Int.cast_natCast]
      exact_mod_cast (show Γ.index ≤ Γ.index * (L i + 1) + 1 by nlinarith)
    · simp only [Pi.smul_apply, Pi.single_eq_of_ne hij, smul_zero, Int.cast_zero]
      positivity

lemma deltaSeedBox_contains {d : ℕ} (L : Fin d → ℕ) (I : ℕ) (hI : 0 < I)
    (u : Fin d → ℤ) (hu : ∀ i, |u i| ≤ (L i : ℤ)) :
    intCastVec u ∈ (deltaSeedBox L I).body := by
  rw [deltaSeedBox_mem_iff]
  intro i
  have hi : |(u i : ℝ)| ≤ (L i : ℝ) := by exact_mod_cast hu i
  exact hi.trans (by exact_mod_cast (show L i ≤ I * (L i + 1) + 1 by nlinarith))

lemma deltaSeedBox_dilate_bound {d : ℕ} (L : Fin d → ℕ) (I k : ℕ)
    (u : Fin d → ℤ)
    (hu : intCastVec u ∈ bodyDilate (k : ℝ) (deltaSeedBox L I).body) :
    ∀ i, |u i| ≤ ((k * (I * (L i + 1) + 1) : ℕ) : ℤ) := by
  obtain ⟨v, hv, heq⟩ := hu
  have hb := (deltaSeedBox_mem_iff L I v).mp hv
  intro i
  have hi : (k : ℝ) * v i = (u i : ℝ) := congrFun heq i
  have hbound : |(u i : ℝ)| ≤ ((k * (I * (L i + 1) + 1) : ℕ) : ℝ) := by
    rw [← hi, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (hb i) (by positivity)
  exact_mod_cast hbound

end Erdos587.GeneralizedAP

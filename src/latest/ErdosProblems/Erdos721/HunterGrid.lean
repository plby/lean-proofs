/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterPhase

/-!
# Explicit finite nets in the unit torus

The `Q` equally spaced points in each circle coordinate give a finite
`1/Q`-net of every finite-dimensional torus.  This is the compactness step
which turns Hunter's positive-volume phase targets into finitely many events.
-/

namespace Erdos721.HunterGrid

open Set

open HunterTorus

/-- The coordinatewise `Q`-grid in the unit torus. -/
noncomputable def gridPoint {D Q : ℕ} (a : Fin D → Fin Q) : Torus D :=
  fun i ↦ ((((a i : ℕ) : ℝ) / (Q : ℝ)) : AddCircle (1 : ℝ))

@[simp] lemma gridPoint_apply {D Q : ℕ} (a : Fin D → Fin Q)
    (i : Fin D) :
    gridPoint a i =
      ((((a i : ℕ) : ℝ) / (Q : ℝ)) : AddCircle (1 : ℝ)) := rfl

/-- Every point of the torus is coordinatewise within `1/Q` of a grid
point. -/
theorem exists_gridPoint_norm_sub_le {D Q : ℕ} (hQ : 2 ≤ Q)
    (x : Torus D) :
    ∃ a : Fin D → Fin Q,
      ∀ i, ‖gridPoint a i - x i‖ ≤ ((Q : ℝ)⁻¹) := by
  let y : Fin D → ℝ := fun i ↦
    (AddCircle.equivIco 1 (0 : ℝ) (x i) : ℝ)
  have hy (i : Fin D) : y i ∈ Set.Ico (0 : ℝ) 1 := by
    simpa [y] using
      (AddCircle.equivIco 1 (0 : ℝ) (x i)).2
  let a : Fin D → Fin Q := fun i ↦
    ⟨⌊(Q : ℝ) * y i⌋₊, (Nat.floor_lt (mul_nonneg (by positivity)
      (hy i).1)).2 (by
        have hQpos : (0 : ℝ) < Q := by positivity
        have := (hy i).2
        nlinarith)⟩
  refine ⟨a, fun i ↦ ?_⟩
  have hQpos : (0 : ℝ) < Q := by positivity
  have hfloorLow :
      ((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) ≤ (Q : ℝ) * y i :=
    Nat.floor_le (mul_nonneg (by positivity) (hy i).1)
  have hfloorHigh :
      (Q : ℝ) * y i < ((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have herr0 :
      0 ≤ y i - ((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) / (Q : ℝ) := by
    have hdiv :
        ((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) / (Q : ℝ) ≤ y i :=
      (div_le_iff₀ hQpos).2 (by simpa [mul_comm] using hfloorLow)
    linarith
  have herr :
      y i - ((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) / (Q : ℝ) <
        (Q : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    have hdiv : y i <
        (((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) + 1) / (Q : ℝ) :=
      (lt_div_iff₀ hQpos).2 (by simpa [mul_comm] using hfloorHigh)
    have hsplit :
        (((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) + 1) / (Q : ℝ) =
          ((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) / (Q : ℝ) +
            1 / (Q : ℝ) := by ring
    rw [hsplit] at hdiv
    linarith
  have habs :
      |((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) / (Q : ℝ) - y i| ≤
        (Q : ℝ)⁻¹ := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hinvhalf : (Q : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    exact_mod_cast hQ
  have hnorm :
      ‖(((((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) / (Q : ℝ) - y i) : ℝ) :
          AddCircle (1 : ℝ))‖ =
        |((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) / (Q : ℝ) - y i| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
      (by simpa using habs.trans hinvhalf)
  rw [← AddCircle.coe_equivIco (p := (1 : ℝ))
    (a := (0 : ℝ)) (y := x i)]
  change ‖(((((a i : ℕ) : ℝ) / (Q : ℝ) - y i) : ℝ) :
      AddCircle (1 : ℝ))‖ ≤ (Q : ℝ)⁻¹
  change ‖(((((⌊(Q : ℝ) * y i⌋₊ : ℕ) : ℝ) / (Q : ℝ) - y i) : ℝ) :
      AddCircle (1 : ℝ))‖ ≤ (Q : ℝ)⁻¹
  rw [hnorm]
  exact habs

end Erdos721.HunterGrid

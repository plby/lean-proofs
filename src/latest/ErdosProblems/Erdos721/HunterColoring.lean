/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.HunterOrbitCenters

/-!
# The finite torus-shell coloring

This file defines Hunter's red set from a direction, a separated center
family, and one radial-shell label per center.  It proves the deterministic
geometric half of the construction: affine separation and exclusion of small
multiples rule out red nonconstant three-term progressions.
-/

namespace Erdos721.HunterColoring

open Function Set
open scoped BigOperators

open HunterParameters HunterAnnulus HunterTorus HunterPhase HunterCenters
  HunterDistributedCenters HunterSeparatedCenters HunterDiophantine

/-- One radial-shell label for each center coordinate. -/
abbrev ShellLabeling (Y S K : ℕ) := Fin Y → Fin S → Fin K

/-- The lifted orbit point lies in the shell assigned to some center. -/
def IsHunterRed {D Y S K : ℕ} (q : ℝ) (theta : Torus D)
    (x : CenterFamily Y S D) (label : ShellLabeling Y S K)
    (n : ℕ) : Prop :=
  ∃ p : Fin Y × Fin S,
    centeredLift (n • theta - centerAt x p) ∈
      shell q (label p.1 p.2).val

/-- Every positive-step progression of length `L` below `N` meets a set. -/
def HitsEveryAP (N L : ℕ) (red : ℕ → Prop) : Prop :=
  ∀ a d : ℕ, 0 < d → a + (L - 1) * d < N →
    ∃ i : Fin L, red (a + i.val * d)

/-- A set has no nonconstant three-term arithmetic progression below `N`. -/
def ThreeAPFreeBelow (N : ℕ) (red : ℕ → Prop) : Prop :=
  ∀ a d : ℕ, 0 < d → a + 2 * d < N →
    ¬(red a ∧ red (a + d) ∧ red (a + 2 * d))

lemma abs_apply_le_norm {D : ℕ} (v : EuclideanSpace ℝ (Fin D)) (i : Fin D) :
    |v i| ≤ ‖v‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg |v j|) (Finset.mem_univ i)

/-- A short Euclidean vector projects into the corresponding torus box. -/
lemma project_mem_centeredBox_of_norm_le {D : ℕ}
    {v : EuclideanSpace ℝ (Fin D)} {r : ℝ}
    (hrhalf : r ≤ 1 / 2) (hv : ‖v‖ ≤ r) :
    project v ∈ centeredBox D r := by
  intro i _hi
  rw [Metric.mem_closedBall, dist_eq_norm]
  have habs : |v i| ≤ r := (abs_apply_le_norm v i).trans hv
  have heq : ‖((v i : ℝ) : AddCircle (1 : ℝ))‖ = |v i| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by
      norm_num
      exact habs.trans hrhalf)
  simpa [project, heq] using habs

/-- A vector shorter than half a period whose torus projection is zero is
itself zero. -/
lemma eq_zero_of_project_eq_zero_of_norm_lt_half {D : ℕ}
    {v : EuclideanSpace ℝ (Fin D)} (hv : ‖v‖ < 1 / 2)
    (hproject : project v = 0) : v = 0 := by
  ext i
  have habs : |v i| < 1 / 2 := (abs_apply_le_norm v i).trans_lt hv
  have heq : ‖((v i : ℝ) : AddCircle (1 : ℝ))‖ = |v i| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by
      simpa using habs.le)
  have hi := congrFun hproject i
  change ((v i : ℝ) : AddCircle (1 : ℝ)) = 0 at hi
  have habszero : |v i| = 0 := by rw [← heq, hi, norm_zero]
  exact abs_eq_zero.mp habszero

/-- A point in a labeled shell has norm below the common outer radius. -/
lemma norm_lt_outer_of_mem_shell {D K : ℕ} {q rho : ℝ}
    (hshell : ∀ k : Fin K, ((k.val + 1 : ℕ) : ℝ) * q ≤ rho)
    {v : EuclideanSpace ℝ (Fin D)} {k : Fin K}
    (hv : v ∈ shell q k.val) : ‖v‖ < rho := by
  exact hv.2.trans_le (hshell k)

lemma nsmul_threeAP_combo {D : ℕ} (theta : Torus D) (a d : ℕ) :
    a • theta - 2 • ((a + d) • theta) + (a + 2 * d) • theta = 0 := by
  simp only [add_nsmul, mul_nsmul]
  rw [show d • (2 • theta) = 2 • (d • theta) by
    rw [← mul_nsmul, Nat.mul_comm, mul_nsmul]]
  abel

/-- The affine relation among three center indices is the negative
projection of the second difference of their centered lifts. -/
lemma affineCombo_eq_neg_project_secondDifference
    {D Y S : ℕ} (theta : Torus D) (a d : ℕ)
    (x : CenterFamily Y S D) (p₀ p₁ p₂ : Fin Y × Fin S)
    (v₀ v₁ v₂ : EuclideanSpace ℝ (Fin D))
    (hv₀ : project v₀ = a • theta - centerAt x p₀)
    (hv₁ : project v₁ = (a + d) • theta - centerAt x p₁)
    (hv₂ : project v₂ = (a + 2 * d) • theta - centerAt x p₂) :
    affineCombo (D := D) p₀ p₁ p₂ x =
      -project (v₀ - 2 • v₁ + v₂) := by
  rw [show project (v₀ - 2 • v₁ + v₂) =
      project v₀ - 2 • project v₁ + project v₂ by
    simp only [sub_eq_add_neg, two_nsmul, project_add, project_neg],
    hv₀, hv₁, hv₂]
  change centerAt x p₀ - 2 • centerAt x p₁ + centerAt x p₂ = _
  have horbit := nsmul_threeAP_combo theta a d
  symm
  calc
    _ = centerAt x p₀ - 2 • centerAt x p₁ + centerAt x p₂ -
        (a • theta - 2 • ((a + d) • theta) +
          (a + 2 * d) • theta) := by abel
    _ = centerAt x p₀ - 2 • centerAt x p₁ + centerAt x p₂ := by
      rw [horbit, sub_zero]

/-- After the three center indices coincide, the Euclidean first difference
projects to the positive orbit step. -/
lemma project_firstDifference
    {D Y S : ℕ} (theta : Torus D) (a d : ℕ)
    (x : CenterFamily Y S D) (p : Fin Y × Fin S)
    (v₀ v₁ : EuclideanSpace ℝ (Fin D))
    (hv₀ : project v₀ = a • theta - centerAt x p)
    (hv₁ : project v₁ = (a + d) • theta - centerAt x p) :
    project (v₁ - v₀) = d • theta := by
  rw [show project (v₁ - v₀) = project v₁ - project v₀ by
    simp [sub_eq_add_neg], hv₀, hv₁]
  simp only [add_nsmul]
  abel

/-- The deterministic geometric core of Hunter's coloring.  Radial shell
membership forces the Euclidean first difference to be tiny; affine
separation makes the three selected centers coincide; exclusion of small
positive torus multiples then gives the contradiction. -/
theorem threeAPFreeBelow_of_geometric_data
    {D Y S K N : ℕ} {q rho delta tau : ℝ}
    {theta : Torus D} {x : CenterFamily Y S D}
    {label : ShellLabeling Y S K}
    (hq : 0 < q)
    (hshell : ∀ k : Fin K, ((k.val + 1 : ℕ) : ℝ) * q ≤ rho)
    (houter : ∀ k : Fin K, 2 * (k.val : ℝ) * q + q ≤ 1 / 4)
    (hsep : AffinelySeparated delta x)
    (hfourrho : 4 * rho ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hfourrhoHalf : 4 * rho < 1 / 2)
    (htau : Real.sqrt q / 2 ≤ tau) (htauHalf : tau ≤ 1 / 2)
    (hsmall : NoSmallMultiple N tau theta) :
    ThreeAPFreeBelow N (IsHunterRed q theta x label) := by
  intro a d hd hbound hred
  obtain ⟨p₀, hp₀⟩ := hred.1
  obtain ⟨p₁, hp₁⟩ := hred.2.1
  obtain ⟨p₂, hp₂⟩ := hred.2.2
  let v₀ : EuclideanSpace ℝ (Fin D) :=
    centeredLift (a • theta - centerAt x p₀)
  let v₁ : EuclideanSpace ℝ (Fin D) :=
    centeredLift ((a + d) • theta - centerAt x p₁)
  let v₂ : EuclideanSpace ℝ (Fin D) :=
    centeredLift ((a + 2 * d) • theta - centerAt x p₂)
  have hv₀proj : project v₀ = a • theta - centerAt x p₀ := by
    simp [v₀]
  have hv₁proj : project v₁ = (a + d) • theta - centerAt x p₁ := by
    simp [v₁]
  have hv₂proj : project v₂ = (a + 2 * d) • theta - centerAt x p₂ := by
    simp [v₂]
  have hv₀norm : ‖v₀‖ < rho :=
    norm_lt_outer_of_mem_shell hshell hp₀
  have hv₁norm : ‖v₁‖ < rho :=
    norm_lt_outer_of_mem_shell hshell hp₁
  have hv₂norm : ‖v₂‖ < rho :=
    norm_lt_outer_of_mem_shell hshell hp₂
  let w : EuclideanSpace ℝ (Fin D) := v₀ - 2 • v₁ + v₂
  have hwnorm : ‖w‖ < 4 * rho := by
    calc
      ‖w‖ ≤ ‖v₀ - 2 • v₁‖ + ‖v₂‖ := by
        simpa only [w] using norm_add_le (v₀ - 2 • v₁) v₂
      _ ≤ (‖v₀‖ + ‖2 • v₁‖) + ‖v₂‖ := by
        gcongr
        exact norm_sub_le v₀ (2 • v₁)
      _ = ‖v₀‖ + 2 * ‖v₁‖ + ‖v₂‖ := by
        rw [RCLike.norm_nsmul (K := ℝ)]
        simp [nsmul_eq_mul]
      _ < 4 * rho := by linarith
  have haffine : affineCombo (D := D) p₀ p₁ p₂ x = -project w := by
    simpa only [w] using
      affineCombo_eq_neg_project_secondDifference theta a d x p₀ p₁ p₂
        v₀ v₁ v₂ hv₀proj hv₁proj hv₂proj
  have haffineBox : affineCombo (D := D) p₀ p₁ p₂ x ∈
      centeredBox D delta := by
    rw [haffine, ← project_neg]
    apply project_mem_centeredBox_of_norm_le hdeltaHalf
    simpa only [norm_neg] using hwnorm.le.trans hfourrho
  obtain ⟨hp₀₁, hp₁₂⟩ := hsep p₀ p₁ p₂ haffineBox
  subst p₁
  subst p₂
  have hwproj : project w = 0 := by
    have hneg : -project w = 0 := by
      rw [← haffine]
      change centerAt x p₀ - 2 • centerAt x p₀ + centerAt x p₀ = 0
      abel
    exact neg_eq_zero.mp hneg
  have hwzero : w = 0 :=
    eq_zero_of_project_eq_zero_of_norm_lt_half
      (hwnorm.trans hfourrhoHalf) hwproj
  let v : EuclideanSpace ℝ (Fin D) := v₁ - v₀
  have hmiddle : v₀ + v = v₁ := by
    simp only [v]
    abel
  have hlast : v₀ + v + v = v₂ := by
    have hwzero' : v₀ - 2 • v₁ + v₂ = 0 := by
      simpa only [w] using hwzero
    calc
      _ = -(v₀ - 2 • v₁ + v₂) + v₂ := by
        simp only [v, two_nsmul]
        abel
      _ = v₂ := by rw [hwzero', neg_zero, zero_add]
  have hmiddleShell : v₀ + v ∈ shell q (label p₀.1 p₀.2).val := by
    rw [hmiddle]
    exact hp₁
  have hlastShell : v₀ + v + v ∈ shell q (label p₀.1 p₀.2).val := by
    rw [hlast]
    exact hp₂
  have hvshort : ‖v‖ < Real.sqrt q / 2 :=
    norm_step_lt_half_sqrt_of_mem_shell hq (houter (label p₀.1 p₀.2))
      hp₀ hmiddleShell hlastShell
  have hvshortTau : ‖v‖ < tau := hvshort.trans_le htau
  have hvproject : project v = d • theta := by
    simpa only [v] using
      project_firstDifference theta a d x p₀ v₀ v₁ hv₀proj hv₁proj
  let di : Fin N := ⟨d - 1, by omega⟩
  have hdi : di.val + 1 = d := by
    dsimp only [di]
    omega
  apply hsmall di
  change (di.val + 1) • theta ∈ centeredBox D tau
  rw [hdi, ← hvproject]
  exact project_mem_centeredBox_of_norm_le htauHalf hvshortTau.le

end Erdos721.HunterColoring

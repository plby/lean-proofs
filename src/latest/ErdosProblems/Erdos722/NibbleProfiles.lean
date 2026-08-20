/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.NibbleBarrier
import ErdosProblems.Erdos722.Asymptotics
import Mathlib

/-!
# Explicit profiles for clique removal

If `g` is the initial number of host edges and every selected clique covers
`K` edges, then `remaining g K i = g-Ki` and `density g K i = 1-Ki/g`.
The degree and clique profiles below use reciprocal-power rather than
logarithmic error envelopes.  Their absolute errors are proportional to
`A / density^(4K-1)` and `A / density^(4K-2)` respectively;
it therefore grows as the process approaches its stopping density.  This is
the feature needed by the critical-interval argument: the upper envelope
falls more slowly, and the lower envelope falls more quickly, than the
mean-field trajectory.

For lower-face degrees we use the exact reciprocal weight `g/(g-Ki)`.
Its slightly excessive positive drift is paid for by `faceCap`, whose
increment is an explicit `eps` fraction of the weight increment.  At the
endpoint, division by the weight gives the useful bound
`(n+slack) * density + n*eps`.
-/

namespace Erdos722.NibbleProfiles

noncomputable section

/-- Real number of uncovered auxiliary vertices after `i` choices. -/
def remaining (g K i : ℕ) : ℝ := (g : ℝ) - K * i

/-- Fraction of uncovered auxiliary vertices. -/
def density (g K i : ℕ) : ℝ := remaining g K i / g

/-- Ideal surviving edge degree. -/
def degreeCenter (D : ℝ) (g K i : ℕ) : ℝ :=
  D * density g K i ^ (K - 1)

/-- Reciprocal edge-degree error envelope. -/
def degreeError (A D : ℝ) (g K i : ℕ) : ℝ :=
  A * D / density g K i ^ (4 * K - 1)

def degreeUpper (A D : ℝ) (g K i : ℕ) : ℝ :=
  degreeCenter D g K i + degreeError A D g K i

def degreeLower (A D : ℝ) (g K i : ℕ) : ℝ :=
  degreeCenter D g K i - degreeError A D g K i

/-- Ideal total number of surviving cliques. -/
def cliqueCenter (D : ℝ) (g K i : ℕ) : ℝ :=
  (g : ℝ) * D / K * density g K i ^ K

/-- Reciprocal total-clique error envelope. -/
def cliqueError (A D : ℝ) (g K i : ℕ) : ℝ :=
  (A * (g : ℝ) * D / K) / density g K i ^ (4 * K - 2)

def cliqueUpper (A D : ℝ) (g K i : ℕ) : ℝ :=
  cliqueCenter D g K i + cliqueError A D g K i

def cliqueLower (A D : ℝ) (g K i : ℕ) : ℝ :=
  cliqueCenter D g K i - cliqueError A D g K i

/-- Reciprocal-density weight for a residual lower-face degree. -/
def faceWeight (g K i : ℕ) : ℝ :=
  (g : ℝ) / remaining g K i

/-- Face barrier.  `slack` supplies the initial concentration margin and
`eps` pays for the discrepancy between the lower and upper edge profiles. -/
def faceCap (n : ℕ) (slack eps : ℝ) (g K i : ℕ) : ℝ :=
  (n : ℝ) + slack +
    (n : ℝ) * eps * (faceWeight g K i - 1)

@[simp] lemma remaining_zero (g K : ℕ) : remaining g K 0 = g := by
  simp [remaining]

lemma remaining_succ (g K i : ℕ) :
    remaining g K (i + 1) = remaining g K i - K := by
  simp [remaining]
  ring

@[simp] lemma density_zero {g K : ℕ} (hg : 0 < g) :
    density g K 0 = 1 := by
  simp [density, remaining, ne_of_gt (show (0 : ℝ) < g by exact_mod_cast hg)]

lemma density_succ (g K i : ℕ) :
    density g K (i + 1) = density g K i - (K : ℝ) / g := by
  simp only [density, remaining_succ]
  ring

lemma remaining_pos {g K i : ℕ} (h : K * i < g) :
    0 < remaining g K i := by
  have h' : ((K * i : ℕ) : ℝ) < g := by exact_mod_cast h
  simpa [remaining] using sub_pos.mpr h'

lemma density_pos {g K i : ℕ} (hg : 0 < g) (h : K * i < g) :
    0 < density g K i := by
  exact div_pos (remaining_pos h) (by exact_mod_cast hg)

@[simp] lemma degreeCenter_zero {D : ℝ} {g K : ℕ} (hg : 0 < g) :
    degreeCenter D g K 0 = D := by
  simp [degreeCenter, density_zero hg]

@[simp] lemma degreeError_zero {A D : ℝ} {g K : ℕ} (hg : 0 < g) :
    degreeError A D g K 0 = A * D := by
  simp [degreeError, density_zero hg]

@[simp] lemma degreeUpper_zero {A D : ℝ} {g K : ℕ} (hg : 0 < g) :
    degreeUpper A D g K 0 = D + A * D := by
  simp [degreeUpper, hg]

@[simp] lemma degreeLower_zero {A D : ℝ} {g K : ℕ} (hg : 0 < g) :
    degreeLower A D g K 0 = D - A * D := by
  simp [degreeLower, hg]

@[simp] lemma cliqueCenter_zero {D : ℝ} {g K : ℕ} (hg : 0 < g) :
    cliqueCenter D g K 0 = (g : ℝ) * D / K := by
  simp [cliqueCenter, density_zero hg]

@[simp] lemma cliqueError_zero {A D : ℝ} {g K : ℕ} (hg : 0 < g) :
    cliqueError A D g K 0 = A * (g : ℝ) * D / K := by
  simp [cliqueError, density_zero hg]

@[simp] lemma faceWeight_zero {g K : ℕ} (hg : 0 < g) :
    faceWeight g K 0 = 1 := by
  simp [faceWeight, remaining, ne_of_gt (show (0 : ℝ) < g by exact_mod_cast hg)]

@[simp] lemma faceCap_zero {n g K : ℕ} {slack eps : ℝ} (hg : 0 < g) :
    faceCap n slack eps g K 0 = n + slack := by
  simp [faceCap, faceWeight_zero hg]

lemma faceWeight_pos {g K i : ℕ} (hg : 0 < g) (hi : K * i < g) :
    0 < faceWeight g K i := by
  exact div_pos (by exact_mod_cast hg) (remaining_pos hi)

/-- The relative weight increment is exactly `K / remaining`. -/
lemma faceWeight_sub_div_next
    {g K i : ℕ} (hg : 0 < g) (hi : K * (i + 1) < g) :
    (faceWeight g K (i + 1) - faceWeight g K i) /
        faceWeight g K (i + 1) =
      (K : ℝ) / remaining g K i := by
  have hii : K * i ≤ K * (i + 1) := Nat.mul_le_mul_left K (by omega)
  have hri : remaining g K i ≠ 0 :=
    ne_of_gt (remaining_pos (hii.trans_lt hi))
  have hrnext : remaining g K (i + 1) ≠ 0 := ne_of_gt (remaining_pos hi)
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  have hnext : remaining g K (i + 1) = remaining g K i - K :=
    remaining_succ g K i
  unfold faceWeight
  rw [hnext]
  have hrsub : remaining g K i - (K : ℝ) ≠ 0 := hnext ▸ hrnext
  field_simp [hri, hrsub, hg0]
  ring

lemma faceWeight_mono_step
    {g K i : ℕ} (hK : 0 < K) (hi : K * (i + 1) < g) :
    faceWeight g K i < faceWeight g K (i + 1) := by
  have hmul : K * i < K * (i + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) hK
  have hri := remaining_pos (hmul.trans hi)
  have hrnext := remaining_pos hi
  unfold faceWeight
  apply div_lt_div_of_pos_left (by exact_mod_cast (show 0 < g by omega)) hrnext
  rw [remaining_succ]
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  linarith

lemma faceCap_succ_sub
    (n g K i : ℕ) (slack eps : ℝ) :
    faceCap n slack eps g K (i + 1) - faceCap n slack eps g K i =
      (n : ℝ) * eps *
        (faceWeight g K (i + 1) - faceWeight g K i) := by
  simp only [faceCap]
  ring

/-- Dividing the terminal cap by the reciprocal-density weight gives the
transparent endpoint expression used in the leave estimate. -/
lemma faceCap_div_weight
    {n g K i : ℕ} {slack eps : ℝ}
    (hg : 0 < g) (hi : K * i < g) :
    faceCap n slack eps g K i / faceWeight g K i =
      ((n : ℝ) + slack) * density g K i +
        (n : ℝ) * eps * (1 - density g K i) := by
  have hrem : remaining g K i ≠ 0 := ne_of_gt (remaining_pos hi)
  have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  unfold faceCap faceWeight density
  field_simp

end

end Erdos722.NibbleProfiles

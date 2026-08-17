import ErdosProblems.Erdos581.Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Numerical lemmas for the stable-vertex cut argument
-/

open Finset

namespace Erdos581

/-- The mass of the middle layer of `2*r` independent fair bits. -/
noncomputable def centralProb (r : ℕ) : ℝ :=
  (Nat.centralBinom r : ℝ) / (4 : ℝ) ^ r

@[simp] lemma centralProb_zero : centralProb 0 = 1 := by
  simp [centralProb, Nat.centralBinom_zero]

lemma centralProb_pos (r : ℕ) : 0 < centralProb r := by
  unfold centralProb
  apply div_pos
  · exact_mod_cast Nat.centralBinom_pos r
  · positivity

lemma centralProb_succ (r : ℕ) :
    centralProb (r + 1) = centralProb r * (2 * (r : ℝ) + 1) / (2 * (r : ℝ) + 2) := by
  have hrec : ((r + 1 : ℕ) : ℝ) * (Nat.centralBinom (r + 1) : ℝ) =
      (2 * (2 * r + 1) * Nat.centralBinom r : ℕ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ r
  rw [centralProb, centralProb, pow_succ]
  norm_num at hrec ⊢
  field_simp
  nlinarith

lemma centralProb_le_half {r : ℕ} (hr : 1 ≤ r) : centralProb r ≤ 1 / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction k with
  | zero => norm_num [centralProb, Nat.centralBinom]
  | succ k ih =>
      rw [show 1 + (k + 1) = (1 + k) + 1 by omega, centralProb_succ]
      have hp := centralProb_pos (1 + k)
      have hratio : (2 * ((1 + k : ℕ) : ℝ) + 1) /
          (2 * ((1 + k : ℕ) : ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        norm_num
      calc
        centralProb (1 + k) * (2 * ((1 + k : ℕ) : ℝ) + 1) /
              (2 * ((1 + k : ℕ) : ℝ) + 2)
            = centralProb (1 + k) *
                ((2 * ((1 + k : ℕ) : ℝ) + 1) /
                  (2 * ((1 + k : ℕ) : ℝ) + 2)) := by ring
        _ ≤ centralProb (1 + k) * 1 := by gcongr
        _ ≤ 1 / 2 := by simpa [Nat.add_comm] using ih

private lemma centralProb_sq_lower : ∀ r : ℕ, 1 ≤ r →
    1 ≤ 4 * (r : ℝ) * (centralProb r) ^ 2 := by
  intro r hr
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction k with
  | zero => norm_num [centralProb, Nat.centralBinom]
  | succ k ih =>
      let r : ℕ := 1 + k
      have hrpos : (0 : ℝ) < r := by positivity
      have hden : (0 : ℝ) < 2 * r + 2 := by positivity
      have hpoly : 4 * (r : ℝ) * (r + 1) ≤ (2 * r + 1) ^ 2 := by
        push_cast
        nlinarith
      have hratio : 1 ≤ ((r + 1 : ℕ) : ℝ) / r *
          ((2 * (r : ℝ) + 1) / (2 * (r : ℝ) + 2)) ^ 2 := by
        field_simp
        push_cast at hpoly ⊢
        nlinarith
      have ih' : 1 ≤ 4 * (r : ℝ) * centralProb r ^ 2 := by
        simpa [r, Nat.add_comm] using ih (by omega)
      have hnonneg : 0 ≤ 4 * (r : ℝ) * centralProb r ^ 2 := by positivity
      rw [show 1 + (k + 1) = r + 1 by dsimp [r]; omega, centralProb_succ]
      have hid :
          4 * (((r + 1 : ℕ) : ℝ)) *
              (centralProb r * (2 * (r : ℝ) + 1) / (2 * (r : ℝ) + 2)) ^ 2 =
            (4 * (r : ℝ) * centralProb r ^ 2) *
              ((((r + 1 : ℕ) : ℝ) / r) *
                ((2 * (r : ℝ) + 1) / (2 * (r : ℝ) + 2)) ^ 2) := by
        field_simp <;> ring
      rw [hid]
      exact one_le_mul_of_one_le_of_one_le ih' hratio

/-- Elementary middle-binomial lower bound, with deliberately loose constant. -/
theorem one_div_two_sqrt_le_centralProb {r : ℕ} (hr : 1 ≤ r) :
    1 / (2 * Real.sqrt r) ≤ centralProb r := by
  have hspos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr)
  have hsquare : (Real.sqrt (r : ℝ)) ^ 2 = r := by
    rw [sq, Real.mul_self_sqrt]
    positivity
  have hcp := centralProb_pos r
  have hsq := centralProb_sq_lower r hr
  have hrewrite :
      (2 * Real.sqrt (r : ℝ) * centralProb r) ^ 2 =
        4 * (r : ℝ) * centralProb r ^ 2 := by
    rw [mul_pow, mul_pow, hsquare]
    ring
  rw [← hrewrite] at hsq
  have hone : 1 ≤ 2 * Real.sqrt (r : ℝ) * centralProb r := by
    have hnonneg : 0 ≤ 2 * Real.sqrt (r : ℝ) * centralProb r := by positivity
    nlinarith
  rw [div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (r : ℝ))]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hone

/-- The pivotal probability attached to a vertex of degree `d`. -/
noncomputable def degreeInfluence (d : ℕ) : ℝ :=
  centralProb (d / 2)

lemma degreeInfluence_pos {d : ℕ} (hd : 1 ≤ d) : 0 < degreeInfluence d := by
  exact centralProb_pos _

lemma degreeInfluence_le_half {d : ℕ} (hd : 2 ≤ d) : degreeInfluence d ≤ 1 / 2 := by
  apply centralProb_le_half
  omega

/-- The form used after incidence double counting. -/
lemma sqrt_degree_le_two_mul_degreeInfluence {d : ℕ} (hd : 1 ≤ d) :
    Real.sqrt d ≤ 2 * d * degreeInfluence d := by
  by_cases h1 : d = 1
  · subst d
    norm_num [degreeInfluence, centralProb, Nat.centralBinom]
  · have hr : 1 ≤ d / 2 := by omega
    have hmid := one_div_two_sqrt_le_centralProb hr
    have hrd : (d / 2 : ℕ) ≤ d := Nat.div_le_self _ _
    have hsqrt_le : Real.sqrt (d / 2 : ℕ) ≤ Real.sqrt d := by
      exact Real.sqrt_le_sqrt (by exact_mod_cast hrd)
    have hsqrtd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
    have hsqrtr : 0 < Real.sqrt ((d / 2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr)
    have hweak : 1 / (2 * Real.sqrt (d : ℝ)) ≤ degreeInfluence d := by
      have hden : 2 * Real.sqrt ((d / 2 : ℕ) : ℝ) ≤ 2 * Real.sqrt (d : ℝ) := by
        gcongr
      have hinv : 1 / (2 * Real.sqrt (d : ℝ)) ≤
          1 / (2 * Real.sqrt ((d / 2 : ℕ) : ℝ)) := by
        exact one_div_le_one_div_of_le (by positivity) hden
      exact hinv.trans (by simpa [degreeInfluence] using hmid)
    rw [div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (d : ℝ))] at hweak
    have hsquare : (Real.sqrt (d : ℝ)) ^ 2 = d := by
      rw [sq, Real.mul_self_sqrt]
      positivity
    nlinarith

end Erdos581

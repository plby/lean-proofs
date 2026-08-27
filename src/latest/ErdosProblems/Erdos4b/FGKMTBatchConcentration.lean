/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCategoricalBatches
import ErdosProblems.Erdos4b.FGKMTFiniteGoodBad
import ErdosProblems.Erdos703.McDiarmid

/-! # Simultaneous categorical batch-degree concentration using the proved finite inequality -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem categoricalDegree_tail {n : ℕ} (p : J → ℝ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1) (hw : ∀ i, 0 ≤ w i)
    {b t : ℝ} (hb : 0 ≤ b) (hwb : ∀ i, w i ≤ b) (ht : 0 ≤ t) (j : J) :
    (∑ a : Fin n → Option J,
      if t ≤ |categoricalDegree w a j - p j * ∑ i, w i|
        then categoricalAssignmentMass p a else 0) ≤
      2 * Real.exp (-2 * t ^ 2 / ((n : ℝ) * b ^ 2)) := by
  let : MeasurableSpace (Option J) := ⊤
  have h := Erdos703McDiarmid.mcdiarmid_two_sided n (fun _ => categoricalMass p)
    (fun a => categoricalDegree w a j) (fun _ => b)
    (fun _ => categoricalMass_nonneg p hp hpsum) (fun _ => categoricalMass_sum_one p)
    (fun _ => hb)
    (fun i a c hac => (categoricalDegree_bounded_difference w hw j i a c hac).trans (hwb i))
    t ht
  have hmean : Erdos703McDiarmid.weightedMean (fun _ : Fin n => categoricalMass p)
      (fun a => categoricalDegree w a j) = p j * ∑ i, w i := categoricalDegree_mean p w j
  rw [hmean] at h
  simpa only [Erdos703McDiarmid.eventMass, Finset.sum_filter,
    Erdos703McDiarmid.productMass, categoricalAssignmentMass, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Set.mem_ofPred_eq] using h

theorem exists_numbered_categorical_partition {n : ℕ} {α : Type*}
    (V : Finset α) (p : J → ℝ) (w : Fin n → α → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1)
    (hw : ∀ i, ∀ v ∈ V, 0 ≤ w i v) {b t : ℝ} (hb : 0 ≤ b)
    (hwb : ∀ i, ∀ v ∈ V, w i v ≤ b) (ht : 0 ≤ t)
    (hsmall : 2 * (V.card : ℝ) * Fintype.card J *
      Real.exp (-2 * t ^ 2 / ((n : ℝ) * b ^ 2)) < 1) :
    ∃ a : Fin n → Option J, ∀ v ∈ V, ∀ j,
      |categoricalDegree (fun i => w i v) a j - p j * ∑ i, w i v| < t := by
  classical
  let μ := fun a : Fin n → Option J => categoricalAssignmentMass p a
  let E : Finset (α × J) := V ×ˢ Finset.univ
  let Bad := fun z : α × J => fun a : Fin n → Option J =>
    t ≤ |categoricalDegree (fun i => w i z.1) a z.2 - p z.2 * ∑ i, w i z.1|
  have hμ : ∀ a, 0 ≤ μ a := categoricalAssignmentMass_nonneg p hp hpsum
  have hbad : (∑ a, if ∃ z ∈ E, Bad z a then μ a else 0) ≤
      2 * (V.card : ℝ) * Fintype.card J * Real.exp (-2 * t ^ 2 / ((n : ℝ) * b ^ 2)) := by
    calc
      _ ≤ ∑ z ∈ E, ∑ a, if Bad z a then μ a else 0 :=
        finite_event_union_mass_le μ hμ E Bad
      _ ≤ ∑ _z ∈ E, 2 * Real.exp (-2 * t ^ 2 / ((n : ℝ) * b ^ 2)) := by
        apply Finset.sum_le_sum
        intro z hz
        have hzV : z.1 ∈ V := (Finset.mem_product.mp hz).1
        exact categoricalDegree_tail p (fun i => w i z.1) hp hpsum
          (fun i => hw i z.1 hzV) hb (fun i => hwb i z.1 hzV) ht z.2
      _ = _ := by
        simp only [E, Finset.sum_const, Finset.card_product, Finset.card_univ,
          nsmul_eq_mul, Nat.cast_mul]
        ring
  by_contra! hnone
  have hfull : (∑ a, if ∃ z ∈ E, Bad z a then μ a else 0) = 1 := by
    calc
      _ = ∑ a, μ a := by
        apply Finset.sum_congr rfl
        intro a _
        obtain ⟨v, hv, j, hj⟩ := hnone a
        exact if_pos ⟨(v, j), Finset.mem_product.mpr ⟨hv, Finset.mem_univ j⟩, hj⟩
      _ = 1 := categoricalAssignmentMass_sum_one p
  linarith

end

end Erdos4b.FGKMT

import Mathlib

/-!
# The compact configuration space for the stationary discrepancy model

We keep a two-sided sign sequence and all positive-modulus residues. Using the
full product avoids requiring a separate construction of the profinite integers;
the finite sampling laws will impose the requisite consistency of the residues.
-/

open scoped BigOperators Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

/-- A sign sequence together with one residue for each positive modulus. -/
abbrev Configuration := (ℤ → Bool) × ((q : ℕ+) → ZMod q.val)

/-- Interpret a Boolean as a real sign. -/
def signValue (b : Bool) : ℝ := if b then 1 else -1

theorem abs_signValue (b : Bool) : |signValue b| = 1 := by
  cases b <;> norm_num [signValue]

theorem sq_signValue (b : Bool) : signValue b ^ 2 = 1 := by
  cases b <;> norm_num [signValue]

/-- Joint translation of the sign sequence and all residues. -/
def shift (k : ℤ) (ω : Configuration) : Configuration :=
  (fun j ↦ ω.1 (j + k), fun q ↦ ω.2 q + (k : ZMod q.val))

theorem shift_zero (ω : Configuration) : shift 0 ω = ω := by
  ext <;> simp [shift]

theorem shift_add (k l : ℤ) (ω : Configuration) : shift (k + l) ω = shift k (shift l ω) := by
  ext <;> simp [shift, add_assoc, add_comm, add_left_comm]

theorem continuous_shift (k : ℤ) : Continuous (shift k) := by
  apply Continuous.prodMk
  · exact continuous_pi fun j ↦ (continuous_apply (j + k)).comp continuous_fst
  · exact continuous_pi fun q ↦
      ((continuous_apply q).comp continuous_snd).add continuous_const

def shiftHomeomorph (k : ℤ) : Configuration ≃ₜ Configuration where
  toFun := shift k
  invFun := shift (-k)
  left_inv ω := by rw [← shift_add, neg_add_cancel, shift_zero]
  right_inv ω := by rw [← shift_add, add_neg_cancel, shift_zero]
  continuous_toFun := continuous_shift k
  continuous_invFun := continuous_shift (-k)

/-- The real-valued sign coordinate. -/
def coordinate (j : ℤ) (ω : Configuration) : ℝ := signValue (ω.1 j)

theorem continuous_coordinate (j : ℤ) : Continuous (coordinate j) :=
  (continuous_of_discreteTopology : Continuous signValue).comp
    ((continuous_apply j).comp continuous_fst)

theorem abs_coordinate (j : ℤ) (ω : Configuration) : |coordinate j ω| = 1 :=
  abs_signValue _

theorem sq_coordinate (j : ℤ) (ω : Configuration) : coordinate j ω ^ 2 = 1 :=
  sq_signValue _

theorem coordinate_shift (j k : ℤ) (ω : Configuration) :
    coordinate j (shift k ω) = coordinate (j + k) ω := rfl

/-- The first `M` coordinates, starting at index zero. -/
def blockSum (M : ℕ) (ω : Configuration) : ℝ :=
  ∑ j ∈ range M, coordinate (j : ℤ) ω

theorem continuous_blockSum (M : ℕ) : Continuous (blockSum M) :=
  continuous_finsetSum _ fun j _ ↦ continuous_coordinate j

theorem abs_blockSum_le (M : ℕ) (ω : Configuration) : |blockSum M ω| ≤ M := by
  calc
    |blockSum M ω| ≤ ∑ j ∈ range M, |coordinate (j : ℤ) ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = M := by simp [abs_coordinate]

theorem configuration_probability_tendsto_subseq
    (P : ℕ → ProbabilityMeasure Configuration) :
    ∃ (Q : ProbabilityMeasure Configuration) (r : ℕ → ℕ),
      StrictMono r ∧ Tendsto (P ∘ r) atTop (nhds Q) := by
  exact CompactSpace.tendsto_subseq P

theorem tendsto_integral_continuous_observable
    {P : ℕ → ProbabilityMeasure Configuration} {Q : ProbabilityMeasure Configuration}
    (hP : Tendsto P atTop (nhds Q)) (F : Configuration → ℝ) (hF : Continuous F) :
    Tendsto (fun n ↦ ∫ ω, F ω ∂(P n : Measure Configuration)) atTop
      (nhds (∫ ω, F ω ∂(Q : Measure Configuration))) := by
  let F' : C(Configuration, ℝ) := ⟨F, hF⟩
  exact (ProbabilityMeasure.continuous_integral_continuousMap F').tendsto Q |>.comp hP

/-- The finite sample before averaging its dilation and starting point. -/
def sample (f : ℕ → Bool) (D N : ℕ) : Configuration :=
  (fun j ↦ f (D * ((N : ℤ) + j).toNat), fun q ↦ (N : ZMod q.val))

theorem shift_one_sample (f : ℕ → Bool) (D N : ℕ) :
    shift 1 (sample f D N) = sample f D (N + 1) := by
  ext <;> simp [shift, sample, Nat.cast_add, add_comm, add_left_comm]

/-- Homogeneous partial sums are indexed by the positive integers `1,…,M`. -/
def homogeneousSum (f : ℕ → Bool) (d M : ℕ) : ℝ :=
  ∑ k ∈ range M, signValue (f ((k + 1) * d))

theorem blockSum_sample_eq_sub (f : ℕ → Bool) (D N M : ℕ) (hN : 0 < N) :
    blockSum M (sample f D N) =
      homogeneousSum f D (N - 1 + M) - homogeneousSum f D (N - 1) := by
  unfold homogeneousSum
  rw [Finset.sum_range_add, add_sub_cancel_left]
  unfold blockSum coordinate sample
  apply Finset.sum_congr rfl
  intro j _
  have harg : D * ((N : ℤ) + (j : ℤ)).toNat = (N - 1 + j + 1) * D := by
    rw [← Nat.cast_add, Int.toNat_natCast]
    have he : N - 1 + j + 1 = N + j := by omega
    rw [he, Nat.mul_comm]
  change signValue (f (D * ((N : ℤ) + (j : ℤ)).toNat)) = _
  rw [harg]

/-- Bounded homogeneous prefixes bound every interval in each sampled dilation. -/
theorem abs_blockSum_sample_le (f : ℕ → Bool) (C : ℝ)
    (hbound : ∀ d M, 0 < d → |homogeneousSum f d M| ≤ C)
    (D N M : ℕ) (hD : 0 < D) (hN : 0 < N) :
    |blockSum M (sample f D N)| ≤ 2 * C := by
  rw [blockSum_sample_eq_sub f D N M hN]
  have h := abs_sub (homogeneousSum f D (N - 1 + M)) (homogeneousSum f D (N - 1))
  linarith [hbound D (N - 1 + M) hD, hbound D (N - 1) hD]

end Erdos67.StationaryModel

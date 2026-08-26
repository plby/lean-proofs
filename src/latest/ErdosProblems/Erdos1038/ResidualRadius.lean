import ErdosProblems.Erdos1038.ResidualConfiguration

/-!
# Residual local radii and their energy identity

This file defines the explicit radii from equation (2.9) of the manuscript
and proves their positivity together with the exact weighted logarithmic
energy identity.  The later local-component theorem supplies the geometric
interpretation of these algebraic radii.
-/

open scoped BigOperators Real
open Finset

namespace Erdos1038

noncomputable section

def residualBackgroundAt {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (i : ι) : ℝ := by
  classical
  exact k * Real.log (C.location i) +
    ∑ j ∈ (Finset.univ.erase i),
      C.weight j * Real.log |C.location i - C.location j|

def residualRadius {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (i : ι) : ℝ :=
  Real.exp (-(C.weight i)⁻¹ * residualBackgroundAt C k i)

def residualPairEnergy {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) : ℝ := by
  classical
  exact ∑ i, C.weight i *
    (∑ j ∈ (Finset.univ.erase i),
      C.weight j * Real.log |C.location i - C.location j|)

theorem residualRadius_pos {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (i : ι) :
    0 < residualRadius C k i := by
  exact Real.exp_pos _

theorem log_residualRadius {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) (i : ι) :
    Real.log (residualRadius C k i) =
      -(C.weight i)⁻¹ * residualBackgroundAt C k i := by
  exact Real.log_exp _

theorem residualRadius_energy_identity {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) :
    ∑ i, (C.weight i) ^ 2 * Real.log (residualRadius C k i) =
      -k * (∑ i, C.weight i * Real.log (C.location i)) -
        residualPairEnergy C := by
  classical
  simp_rw [log_residualRadius]
  have hcancel (i : ι) :
      (C.weight i) ^ 2 * (-(C.weight i)⁻¹ * residualBackgroundAt C k i) =
        -C.weight i * residualBackgroundAt C k i := by
    field_simp [(C.weight_pos i).ne']
  simp_rw [hcancel]
  rw [residualPairEnergy]
  simp only [residualBackgroundAt]
  have hexpand (i : ι) :
      -C.weight i *
          (k * Real.log (C.location i) +
            ∑ j ∈ Finset.univ.erase i,
              C.weight j * Real.log |C.location i - C.location j|) =
        -k * (C.weight i * Real.log (C.location i)) -
          C.weight i *
            (∑ j ∈ Finset.univ.erase i,
              C.weight j * Real.log |C.location i - C.location j|) := by
    ring
  simp_rw [hexpand]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [Finset.mul_sum]

end

end Erdos1038

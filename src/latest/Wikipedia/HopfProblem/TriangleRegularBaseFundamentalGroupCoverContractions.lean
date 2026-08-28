import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCoverSets
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Tactic.FunProp

/-!
# Explicit contractions of the two slit domains

The upper slit domain first moves vertically to the line of imaginary
part one, preserving the real coordinate, and then moves horizontally to
`I`.  Both stages stay in the actual slit domain.  Complex conjugation
transports this contraction to the lower slit domain.
-/

noncomputable section

open Set Complex ContinuousMap
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

def upperSlitBasepoint : upperSlitPlane := ⟨Complex.I, Or.inl (by simp)⟩

def lowerSlitBasepoint : lowerSlitPlane := ⟨-Complex.I, Or.inl (by simp)⟩

/-- Vertical projection to the horizontal line of imaginary part one. -/
def upperSlitHeightMap : C(upperSlitPlane, upperSlitPlane) where
  toFun z := ⟨(z.val.re : ℂ) + Complex.I, Or.inl (by simp)⟩
  continuous_toFun := by fun_prop

private theorem upperSlit_vertical_mem (t : unitInterval) (z : upperSlitPlane) :
    (z.val.re : ℂ) + (((1 - t.val) * z.val.im + t.val : ℝ) : ℂ) * Complex.I ∈
      upperSlitPlane := by
  simp only [upperSlitPlane, mem_ofPred_eq, add_im, ofReal_im, mul_im, ofReal_re,
    I_im, mul_one, I_re, mul_zero, add_zero, zero_add, add_re, mul_re,
    sub_zero]
  rcases z.property with hz | hz
  · left
    by_cases ht : t.val = 1
    · simp [ht]
    · have hp : 0 < 1 - t.val :=
        sub_pos.mpr ((lt_or_eq_of_le t.property.2).resolve_right ht)
      exact add_pos_of_pos_of_nonneg (mul_pos hp hz) t.property.1
  · exact Or.inr hz

/-- The first stage changes only the imaginary coordinate. -/
def upperSlitVerticalHomotopy :
    Homotopy (ContinuousMap.id upperSlitPlane) upperSlitHeightMap where
  toFun p := ⟨(p.2.val.re : ℂ) +
    (((1 - p.1.val) * p.2.val.im + p.1.val : ℝ) : ℂ) * Complex.I,
      upperSlit_vertical_mem p.1 p.2⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by
    apply Subtype.ext
    simp
  map_one_left z := by
    apply Subtype.ext
    simp [upperSlitHeightMap]

/-- The second stage lies entirely on the safe horizontal line. -/
def upperSlitHorizontalHomotopy :
    Homotopy upperSlitHeightMap (ContinuousMap.const upperSlitPlane upperSlitBasepoint) where
  toFun p := ⟨(((1 - p.1.val) * p.2.val.re : ℝ) : ℂ) + Complex.I,
    Or.inl (by simp)⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by
    apply Subtype.ext
    simp [upperSlitHeightMap]
  map_one_left z := by
    apply Subtype.ext
    simp [upperSlitBasepoint]

/-- An actual contraction, with all intermediate points in the slit domain. -/
def upperSlitContraction :
    Homotopy (ContinuousMap.id upperSlitPlane)
      (ContinuousMap.const upperSlitPlane upperSlitBasepoint) :=
  upperSlitVerticalHomotopy.trans upperSlitHorizontalHomotopy

instance upperSlitPlane_contractibleSpace : ContractibleSpace upperSlitPlane :=
  (contractible_iff_id_nullhomotopic upperSlitPlane).mpr
    ⟨upperSlitBasepoint, ⟨upperSlitContraction⟩⟩

/-- The actual conjugation homeomorphism exchanges the two slit domains. -/
def slitConjugation : upperSlitPlane ≃ₜ lowerSlitPlane where
  toFun z := ⟨conj (z : ℂ), by
    simpa [upperSlitPlane, lowerSlitPlane] using z.property⟩
  invFun z := ⟨conj (z : ℂ), by
    simpa [upperSlitPlane, lowerSlitPlane] using z.property⟩
  left_inv z := Subtype.ext (Complex.conj_conj _)
  right_inv z := Subtype.ext (Complex.conj_conj _)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem slitConjugation_basepoint :
    slitConjugation upperSlitBasepoint = lowerSlitBasepoint := by
  apply Subtype.ext
  simp [slitConjugation, upperSlitBasepoint, lowerSlitBasepoint]

instance lowerSlitPlane_contractibleSpace : ContractibleSpace lowerSlitPlane :=
  slitConjugation.symm.contractibleSpace

theorem upperSlitPlane_simplyConnectedSpace : SimplyConnectedSpace upperSlitPlane :=
  inferInstance

theorem lowerSlitPlane_simplyConnectedSpace : SimplyConnectedSpace lowerSlitPlane :=
  inferInstance

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

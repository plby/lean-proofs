import Wikipedia.NoExoticSixSphere.QuaternionCommutatorColumns
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Differentiating the literal quaternionic first-column expression

The derivative is computed at A=D=0, B=1, q=-1. These algebraic
differential identities will be applied to the actual sphere charts;
they do not assume that a sphere map is locally regular.
-/

noncomputable section

namespace NoExoticSixSphere.QuaternionCommutatorColumnDifferential

local notation "ℍ" => Quaternion ℝ

local instance : StarModule ℝ ℍ where
  star_smul r q := by simp [Quaternion.star_smul]

def conjugation : ℍ →L[ℝ] ℍ := (starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap

theorem conjugation_apply (q : ℍ) : conjugation q = star q := rfl

def top (a b q : ℍ) : ℍ := a * star a + b * star q * star b

def bottom (a b d q : ℍ) : ℍ := q * (b * star a + d * star q * star b)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b d q : E → ℍ} {a' b' d' q' : E →L[ℝ] ℍ} {x : E}

theorem hasFDerivAt_top (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x)
    (hq : HasFDerivAt q q' x) (ha₀ : a x = 0) (hb₀ : b x = 1) (hq₀ : q x = -1) :
    HasFDerivAt (fun y ↦ top (a y) (b y) (q y))
      (-b' + conjugation.comp q' - conjugation.comp b') x := by
  have h := (ha.mul' ha.star).add ((hb.mul' hq.star).mul' hb.star)
  convert! h using 1 <;> try rfl
  ext v : 1
  simp [ha₀, hb₀, hq₀, conjugation, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem hasFDerivAt_bottom (ha : HasFDerivAt a a' x) (hb : HasFDerivAt b b' x)
    (hd : HasFDerivAt d d' x) (hq : HasFDerivAt q q' x)
    (ha₀ : a x = 0) (hb₀ : b x = 1) (hd₀ : d x = 0) (hq₀ : q x = -1) :
    HasFDerivAt (fun y ↦ bottom (a y) (b y) (d y) (q y))
      (d' - conjugation.comp a') x := by
  have h := hq.mul' ((hb.mul' ha.star).add ((hd.mul' hq.star).mul' hb.star))
  convert! h using 1 <;> try rfl
  ext v : 1
  simp [ha₀, hb₀, hd₀, hq₀, conjugation, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

end NoExoticSixSphere.QuaternionCommutatorColumnDifferential

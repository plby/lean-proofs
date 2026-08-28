import Wikipedia.HopfProblem.SpecialPeriodsLocal
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Cayley coordinates on the actual upper half-plane

The coordinate in Lemma 2.10 and Definition 2.14 is a genuine
biholomorphism from the upper half-plane to the unit disc, with the chosen
elliptic center sent to zero.  Its inverse is the explicit Cayley formula
already used in the local period construction.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem sub_conj_ne_zero (a z : ℍ) : (z : ℂ) - starRingEnd ℂ (a : ℂ) ≠ 0 := by
  intro he
  have him := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im, UpperHalfPlane.coe_im] at him
  linarith [a.im_pos, z.im_pos]

/-- The source's centered Cayley coordinate. -/
def cayleyCoordinate (a z : ℍ) : ℂ := ((z : ℂ) - a) / ((z : ℂ) - starRingEnd ℂ (a : ℂ))

theorem cayleyCoordinate_norm_lt_one (a z : ℍ) : ‖cayleyCoordinate a z‖ < 1 := by
  rw [cayleyCoordinate, norm_div]
  apply (div_lt_one (norm_pos_iff.mpr (sub_conj_ne_zero a z))).mpr
  have hsq : Complex.normSq ((z : ℂ) - a) <
      Complex.normSq ((z : ℂ) - starRingEnd ℂ (a : ℂ)) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im, UpperHalfPlane.coe_im]
    nlinarith [mul_pos a.im_pos z.im_pos]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg ((z : ℂ) - a), norm_nonneg ((z : ℂ) - starRingEnd ℂ (a : ℂ))]

def toDisc (a z : ℍ) : Disc :=
  ⟨cayleyCoordinate a z, by simpa [unitDisc] using cayleyCoordinate_norm_lt_one a z⟩

@[simp] theorem toDisc_val (a z : ℍ) : (toDisc a z : ℂ) = cayleyCoordinate a z := rfl

def fromDisc (a : ℍ) (z : Disc) : ℍ := ofComplex (cayley a z)

@[simp] theorem fromDisc_val (a : ℍ) (z : Disc) :
    (fromDisc a z : ℂ) = cayley a z := by
  simp only [fromDisc,
    ofComplex_apply_of_im_pos (cayley_im_pos a.im_pos (disc_norm_lt_one z))]

@[simp] theorem toDisc_center (a : ℍ) : toDisc a a =
    (⟨0, by simp [unitDisc]⟩ : Disc) := by
  apply Subtype.ext
  simp [toDisc, cayleyCoordinate]

theorem cayleyCoordinate_holomorphic (a : ℍ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyCoordinate a) :=
  (UpperHalfPlane.contMDiff_coe.sub contMDiff_const).div₀
    (UpperHalfPlane.contMDiff_coe.sub contMDiff_const) (sub_conj_ne_zero a)

theorem toDisc_holomorphic (a : ℍ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toDisc a) := by
  intro z
  have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℍ => (toDisc a w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (toDisc a) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (cayleyCoordinate_holomorphic a z)

theorem fromDisc_holomorphic (a : ℍ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fromDisc a) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : Disc => cayley a z) :=
    (cayley_contDiffOn (a : ℂ)).contMDiffOn.comp_contMDiff contMDiff_subtype_val
      (fun z => z.property)
  intro z
  exact (contMDiffAt_ofComplex (cayley_im_pos a.im_pos (disc_norm_lt_one z))).comp z (hc z)

theorem fromDisc_toDisc (a z : ℍ) : fromDisc a (toDisc a z) = z := by
  apply UpperHalfPlane.ext
  rw [fromDisc_val, toDisc_val]
  have hd := sub_conj_ne_zero a z
  have ha := sub_conj_ne_zero a a
  have hc := one_sub_ne_zero_of_norm_lt_one (cayleyCoordinate_norm_lt_one a z)
  unfold cayley cayleyCoordinate at *
  field_simp [hd, ha, hc]
  ring

theorem toDisc_fromDisc (a : ℍ) (z : Disc) : toDisc a (fromDisc a z) = z := by
  apply Subtype.ext
  rw [toDisc_val]
  unfold cayleyCoordinate
  rw [fromDisc_val]
  have hd := one_sub_ne_zero_of_norm_lt_one (disc_norm_lt_one z)
  have ha := sub_conj_ne_zero a a
  have hz := sub_conj_ne_zero a (fromDisc a z)
  rw [fromDisc_val] at hz
  unfold cayley at *
  field_simp [hd, ha, hz]
  ring_nf
  field_simp [ha]

/-- The actual biholomorphism in Lemma 2.10, with both analytic directions. -/
def cayleyBiholomorph (a : ℍ) : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ Disc ω where
  toFun := toDisc a
  invFun := fromDisc a
  left_inv := fromDisc_toDisc a
  right_inv := toDisc_fromDisc a
  contMDiff_toFun := toDisc_holomorphic a
  contMDiff_invFun := fromDisc_holomorphic a

end Wikipedia.HopfProblem.SpecialPeriods.Triangle

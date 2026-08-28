import Wikipedia.HopfProblem.CuspSection
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Null-homotopy of the section circle

Corollary 4.8(ii) of `tex/s6.tex` asserts that a circle in the extended zero
section is null-homotopic in the cusp neighbourhood. The homotopy here is
explicit: a loop in the disc is contracted to its basepoint by affine
interpolation, and this based contraction is mapped through the actual
section. In particular, its basepoint remains fixed throughout.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricSpace

/-- Every positive-radius cusp disc is contractible. -/
theorem disc_contractibleSpace {ε : ℝ} (hε : 0 < ε) : ContractibleSpace (disc ε) :=
  (convex_ball (0 : ℂ) ε).contractibleSpace ⟨0, by simpa [disc] using hε⟩

/-- The based affine contraction of an arbitrary loop inside the cusp disc. -/
def discLoopContraction {ε : ℝ} {z : disc ε} (p : Path z z) :
    p.Homotopy (Path.refl z) where
  toFun u := ⟨(1 - (u.1 : ℝ)) • (p u.2 : ℂ) + (u.1 : ℝ) • (z : ℂ),
    (convex_ball (0 : ℂ) ε) (p u.2).2 z.2
      (sub_nonneg.mpr u.1.2.2) u.1.2.1 (sub_add_cancel _ _)⟩
  continuous_toFun := by fun_prop
  map_zero_left t := by apply Subtype.ext; simp
  map_one_left t := by apply Subtype.ext; simp
  prop' s t ht := by
    apply Subtype.ext
    change (1 - (s : ℝ)) • (p t : ℂ) + (s : ℝ) • (z : ℂ) = (p t : ℂ)
    rcases ht with rfl | rfl <;> simp <;> ring

@[simp] theorem discLoopContraction_apply {ε : ℝ} {z : disc ε} (p : Path z z)
    (s t : I) :
    (discLoopContraction p (s, t) : ℂ) =
      (1 - (s : ℝ)) • (p t : ℂ) + (s : ℝ) • (z : ℂ) := rfl

/-- The same contraction already exists upstairs in the actual toric tube. -/
def sectionLiftLoopContraction {ε : ℝ} {z : disc ε} (p : Path z z) :
    (p.map (sectionLift_continuous ε)).Homotopy (Path.refl (sectionLift ε z)) :=
  (discLoopContraction p).map ⟨sectionLift ε, sectionLift_continuous ε⟩

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

/-- The zero section carries every based loop in the disc to a based
null-homotopic loop in the actual cusp quotient. -/
def zeroSectionLoopContraction {ε : ℝ} {z : disc ε} (p : Path z z) :
    (p.map (zeroSection_continuous C ε)).Homotopy (Path.refl (zeroSection C ε z)) :=
  (discLoopContraction p).map ⟨zeroSection C ε, zeroSection_continuous C ε⟩

theorem zeroSection_loop_nullhomotopic {ε : ℝ} {z : disc ε} (p : Path z z) :
    Path.Homotopic (p.map (zeroSection_continuous C ε))
      (Path.refl (zeroSection C ε z)) :=
  ⟨zeroSectionLoopContraction C p⟩

/-- The map induced by the section on actual fundamental groups is trivial. -/
theorem zeroSection_fundamentalGroup_map_eq_one {ε : ℝ} (z : disc ε)
    (γ : FundamentalGroup (disc ε) z) :
    FundamentalGroup.map ⟨zeroSection C ε, zeroSection_continuous C ε⟩ z γ = 1 := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk p => exact Path.Homotopic.Quotient.eq.mpr (zeroSection_loop_nullhomotopic C p)

/-- The usual positively oriented parametrization of the circle of radius `ρ`. -/
def circleValue (ρ : ℝ) (t : I) : ℂ :=
  (ρ : ℂ) * Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)

theorem circleValue_norm {ρ : ℝ} (hρ : 0 ≤ ρ) (t : I) : ‖circleValue ρ t‖ = ρ := by
  rw [circleValue, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  simp [abs_of_nonneg hρ]

theorem circleValue_continuous (ρ : ℝ) : Continuous (circleValue ρ) := by
  unfold circleValue
  fun_prop

theorem circleValue_mem_disc {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) (t : I) :
    circleValue ρ t ∈ disc ε := by
  change dist (circleValue ρ t) 0 < ε
  rw [dist_zero_right, circleValue_norm hρ.le]
  exact hρε

/-- The parametrization traverses the whole circle, not just a subset of it. -/
theorem circleValue_range {ρ : ℝ} (hρ : 0 < ρ) :
    range (circleValue ρ) = Metric.sphere (0 : ℂ) ρ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simpa only [Metric.mem_sphere, dist_zero_right] using circleValue_norm hρ.le t
  · intro hz
    have hn : ‖z‖ = ρ := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    obtain ⟨θ, hθ, hθeq⟩ :=
      (periodic_circleMap 0 ρ).exists_mem_Ico₀ Real.two_pi_pos z.arg
    let t : I := ⟨θ / (2 * Real.pi),
      div_nonneg hθ.1 Real.two_pi_pos.le,
      (div_le_one Real.two_pi_pos).mpr hθ.2.le⟩
    have ht : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by field_simp
    have hv : circleValue ρ t = circleMap 0 ρ θ := by
      change (ρ : ℂ) * Complex.exp
        (((2 * Real.pi * (θ / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) = _
      rw [ht, circleMap_zero]
    refine ⟨t, hv.trans (hθeq.symm.trans ?_)⟩
    rw [circleMap_zero, ← hn, Complex.norm_mul_exp_arg_mul_I]

/-- The positive real basepoint of the circle in the cusp disc. -/
def circleBasepoint {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) : disc ε :=
  ⟨(ρ : ℂ), by
    change dist (ρ : ℂ) 0 < ε
    simpa [abs_of_pos hρ] using hρε⟩

/-- The circle as an actual based loop in the disc. -/
def discCircleLoop {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) :
    Path (circleBasepoint hρ hρε) (circleBasepoint hρ hρε) where
  toFun t := ⟨circleValue ρ t, circleValue_mem_disc hρ hρε t⟩
  continuous_toFun := (circleValue_continuous ρ).subtype_mk _
  source' := by
    apply Subtype.ext
    simp [circleValue, circleBasepoint]
  target' := by
    apply Subtype.ext
    simp [circleValue, circleBasepoint, Complex.ofReal_mul, Complex.exp_two_pi_mul_I]

@[simp] theorem discCircleLoop_apply {ε ρ : ℝ}
    (hρ : 0 < ρ) (hρε : ρ < ε) (t : I) :
    (discCircleLoop hρ hρε t : ℂ) =
      (ρ : ℂ) * Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) := rfl

theorem discCircleLoop_norm {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) (t : I) :
    ‖(discCircleLoop hρ hρε t : ℂ)‖ = ρ := circleValue_norm hρ.le t

theorem discCircleLoop_ne_zero {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) (t : I) :
    (discCircleLoop hρ hρε t : ℂ) ≠ 0 := by
  intro h
  have hh := discCircleLoop_norm hρ hρε t
  rw [h, norm_zero] at hh
  exact hρ.ne' hh.symm

theorem discCircleLoop_range {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) :
    range (discCircleLoop hρ hρε) = {z : disc ε | ‖(z : ℂ)‖ = ρ} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact discCircleLoop_norm hρ hρε t
  · intro hz
    have hz' : (z : ℂ) ∈ Metric.sphere (0 : ℂ) ρ := by
      simpa only [Metric.mem_sphere, dist_zero_right, mem_ofPred_eq] using hz
    rw [← circleValue_range hρ] at hz'
    obtain ⟨t, ht⟩ := hz'
    exact ⟨t, Subtype.ext ht⟩

/-- The circle in the actual zero section of the cusp quotient. -/
def zeroSectionCircleLoop {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) :
    Path (zeroSection C ε (circleBasepoint hρ hρε))
      (zeroSection C ε (circleBasepoint hρ hρε)) :=
  (discCircleLoop hρ hρε).map (zeroSection_continuous C ε)

/-- This loop has exactly the section circle occurring in Corollary 4.8(ii)
as its image. -/
theorem zeroSectionCircleLoop_range {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) :
    range (zeroSectionCircleLoop C hρ hρε) =
      zeroSection C ε '' {z : disc ε | ‖(z : ℂ)‖ = ρ} := by
  change range (zeroSection C ε ∘ discCircleLoop hρ hρε) = _
  rw [range_comp, discCircleLoop_range]

/-- The section circle is the projection of its explicit closed lift in the
toric tube, whose null-homotopy is `sectionLiftLoopContraction`. -/
theorem zeroSectionCircleLoop_lifts {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) :
    ((discCircleLoop hρ hρε).map (sectionLift_continuous ε)).map
      (quotientMap_continuous C ε) = zeroSectionCircleLoop C hρ hρε := by
  ext t
  rfl

/-- The displayed section loop really projects to the circle of radius `ρ`. -/
@[simp] theorem zeroSectionCircleLoop_projection {ε ρ : ℝ}
    (hρ : 0 < ρ) (hρε : ρ < ε) (t : I) :
    projection C ε (zeroSectionCircleLoop C hρ hρε t) = circleValue ρ t :=
  projection_zeroSection C ε _

/-- The explicit based null-homotopy of the section circle. -/
def zeroSectionCircleContraction {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) :
    (zeroSectionCircleLoop C hρ hρε).Homotopy
      (Path.refl (zeroSection C ε (circleBasepoint hρ hρε))) :=
  zeroSectionLoopContraction C (discCircleLoop hρ hρε)

theorem zeroSectionCircleContraction_mem_range {ε ρ : ℝ}
    (hρ : 0 < ρ) (hρε : ρ < ε) (u : I × I) :
    zeroSectionCircleContraction C hρ hρε u ∈ range (zeroSection C ε) :=
  mem_range_self (discLoopContraction (discCircleLoop hρ hρε) u)

/-- In disc coordinates the contraction is affine interpolation to the
positive real basepoint, so it is a based, rather than merely free, homotopy. -/
theorem zeroSectionCircleContraction_projection {ε ρ : ℝ}
    (hρ : 0 < ρ) (hρε : ρ < ε) (s t : I) :
    projection C ε (zeroSectionCircleContraction C hρ hρε (s, t)) =
      (1 - (s : ℝ)) • circleValue ρ t + (s : ℝ) • (ρ : ℂ) := by
  exact projection_zeroSection C ε (discLoopContraction (discCircleLoop hρ hρε) (s, t))

/-- Corollary 4.8(ii): every small circle in the extended zero section is
null-homotopic in the actual cusp neighbourhood. -/
theorem zeroSection_circle_nullhomotopic {ε ρ : ℝ} (hρ : 0 < ρ) (hρε : ρ < ε) :
    Path.Homotopic (zeroSectionCircleLoop C hρ hρε)
      (Path.refl (zeroSection C ε (circleBasepoint hρ hρε))) :=
  ⟨zeroSectionCircleContraction C hρ hρε⟩

end Wikipedia.HopfProblem.CuspQuotient

import Wikipedia.HopfProblem.ToricAction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The parameter-dependent twisted cusp action

For an actual holomorphic matrix function `C(t)`, the multipliers
`exp(2πi C(t) λ)` combine with the integral shears to act on the toric space.
The construction and action identities are explicit; no freeness,
proper-discontinuity, compactness, or existence of the special period
function `C` is assumed here.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

@[simp] theorem fibreMultiplier_one : fibreMultiplier 1 = 1 := by
  ext i
  fin_cases i <;> simp [fibreMultiplier]

theorem fibreMultiplier_mul (u v : Fin 2 → ℂˣ) :
    fibreMultiplier (u * v) = fibreMultiplier u * fibreMultiplier v := by
  ext i
  fin_cases i <;> simp [fibreMultiplier]

def variableMultiplier (u : ℂ → Fin 2 → ℂˣ) (x : Space) : Space :=
  torusAction (fibreMultiplier (u (time x))) x

@[simp] theorem variableMultiplier_inclusion (u : ℂ → Fin 2 → ℂˣ)
    (s : Triangle) (z : CoordinateSpace 3) :
    variableMultiplier u (inclusion s z) =
      inclusion s (scale s (fibreMultiplier (u (Triangle.time z))) z) := by
  simp [variableMultiplier]

@[simp] theorem time_variableMultiplier (u : ℂ → Fin 2 → ℂˣ) (x : Space) :
    time (variableMultiplier u x) = time x := by
  simp [variableMultiplier]

@[simp] theorem variableMultiplier_one (x : Space) :
    variableMultiplier (fun _ => 1) x = x := by
  simp [variableMultiplier]

theorem variableMultiplier_mul (u v : ℂ → Fin 2 → ℂˣ) (x : Space) :
    variableMultiplier u (variableMultiplier v x) =
      variableMultiplier (fun t => u t * v t) x := by
  simp only [variableMultiplier, time_fibreMultiplier, torusAction_mul, fibreMultiplier_mul]

theorem variableMultiplier_translate (u : ℂ → Fin 2 → ℂˣ) (v : Fin 2 → ℤ) (x : Space) :
    variableMultiplier u (translate v x) = translate v (variableMultiplier u x) := by
  simp [variableMultiplier, fibreMultiplier_translate]

theorem varying_scale_holomorphic (s : Triangle) (u : ℂ → Fin 2 → ℂˣ) {D : Set ℂ}
    (hu : ∀ j, ContDiffOn ℂ ω (fun t => (u t j : ℂ)) D) :
    ContDiffOn ℂ ω (fun z => scale s (fibreMultiplier (u (Triangle.time z))) z)
      (Triangle.time ⁻¹' D) := by
  have hval : ContDiffOn ℂ ω
      (fun z : CoordinateSpace 3 => fun j => (fibreMultiplier (u (Triangle.time z)) j : ℂ))
      (Triangle.time ⁻¹' D) := by
    apply contDiffOn_pi.mpr
    intro j
    fin_cases j
    · exact (hu 0).comp Triangle.time_holomorphic.contDiffOn (fun _ hz => hz)
    · exact (hu 1).comp Triangle.time_holomorphic.contDiffOn (fun _ hz => hz)
    · exact contDiffOn_const
  have hfactors : ContDiffOn ℂ ω
      (fun z : CoordinateSpace 3 => factors s (fibreMultiplier (u (Triangle.time z))))
      (Triangle.time ⁻¹' D) :=
    (monomial_contDiffOn s.dual ω).comp hval
      (fun z _ => torus_subset_domain _
        (fun j => (fibreMultiplier (u (Triangle.time z)) j).ne_zero))
  exact hfactors.mul contDiffOn_id

theorem variableMultiplier_holomorphic (u : ℂ → Fin 2 → ℂˣ) {D : Set ℂ}
    (hD : IsOpen D) (hu : ∀ j, ContDiffOn ℂ ω (fun t => (u t j : ℂ)) D) :
    ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (variableMultiplier u) (time ⁻¹' D) := by
  apply contMDiffOn_of_comp_inclusion _ _ (hD.preimage time_holomorphic.continuous)
  intro s
  have he : (variableMultiplier u ∘ inclusion s) =
      (inclusion s ∘ fun z => scale s (fibreMultiplier (u (Triangle.time z))) z) := by
    funext z
    exact variableMultiplier_inclusion u s z
  rw [he]
  have hpre : inclusion s ⁻¹' (time ⁻¹' D) = Triangle.time ⁻¹' D := by
    ext z
    simp
  rw [hpre]
  exact (inclusion_holomorphic s).comp_contMDiffOn (varying_scale_holomorphic s u hu).contMDiffOn

/-- The integral shear `B₀ λ = (λ₁,-λ₀)` in the marking of §4. -/
def cuspVector (v : Fin 2 → ℤ) : Fin 2 → ℤ := ![v 1, -v 0]

@[simp] theorem cuspVector_zero : cuspVector 0 = 0 := by ext i; fin_cases i <;> rfl

theorem cuspVector_add (v w : Fin 2 → ℤ) :
    cuspVector (v + w) = cuspVector v + cuspVector w := by
  ext i
  fin_cases i <;> simp [cuspVector, add_comm]

def exponentialMultiplier (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) : Fin 2 → ℂˣ := fun j =>
  Units.mk0 (Complex.exp (2 * Real.pi * Complex.I *
    ((C t) *ᵥ (fun i => (v i : ℂ))) j)) (Complex.exp_ne_zero _)

@[simp] theorem exponentialMultiplier_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    exponentialMultiplier C 0 t = 1 := by
  ext j
  simp [exponentialMultiplier, Matrix.mulVec, dotProduct]

theorem exponentialMultiplier_add (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v w : Fin 2 → ℤ) (t : ℂ) :
    exponentialMultiplier C (v + w) t =
      exponentialMultiplier C v t * exponentialMultiplier C w t := by
  have he : (fun i => ((v + w) i : ℂ)) =
      (fun i => (v i : ℂ)) + (fun i => (w i : ℂ)) := by
    ext i
    simp
  ext j
  change Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => ((v + w) i : ℂ))) j) =
    Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => (v i : ℂ))) j) *
    Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => (w i : ℂ))) j)
  rw [he, Matrix.mulVec_add]
  simp only [Pi.add_apply, mul_add, Complex.exp_add]

theorem exponentialMultiplier_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {D : Set ℂ} (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) D)
    (j : Fin 2) : ContDiffOn ℂ ω (fun t => (exponentialMultiplier C v t j : ℂ)) D := by
  apply ContDiffOn.cexp
  apply contDiffOn_const.mul
  change ContDiffOn ℂ ω (fun t => ∑ i, C t j i * (v i : ℂ)) D
  apply ContDiffOn.sum
  intro i _
  exact (hC j i).mul contDiffOn_const

def twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : Space) : Space :=
  variableMultiplier (exponentialMultiplier C v) (translate (cuspVector v) x)

@[simp] theorem time_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : Space) : time (twistedTranslate C v x) = time x := by
  simp [twistedTranslate]

@[simp] theorem twistedTranslate_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (x : Space) :
    twistedTranslate C 0 x = x := by
  have he : exponentialMultiplier C 0 = (fun _ => 1) := funext (exponentialMultiplier_zero C)
  simp [twistedTranslate, he]

theorem twistedTranslate_add (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v w : Fin 2 → ℤ) (x : Space) :
    twistedTranslate C v (twistedTranslate C w x) = twistedTranslate C (v + w) x := by
  simp only [twistedTranslate]
  rw [← variableMultiplier_translate, translate_add, variableMultiplier_mul]
  have he : (fun t => exponentialMultiplier C v t * exponentialMultiplier C w t) =
      exponentialMultiplier C (v + w) := funext fun t => (exponentialMultiplier_add C v w t).symm
  rw [he, cuspVector_add]

theorem twistedTranslate_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {D : Set ℂ} (hD : IsOpen D)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) D) :
    ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (twistedTranslate C v) (time ⁻¹' D) := by
  exact (variableMultiplier_holomorphic _ hD (exponentialMultiplier_holomorphic C v hC)).comp
    (translate_holomorphic (cuspVector v)).contMDiffOn (fun x hx => by simpa using hx)

def tubeOpen (D : TopologicalSpace.Opens ℂ) : TopologicalSpace.Opens Space :=
  ⟨time ⁻¹' (D : Set ℂ), D.isOpen.preimage time_holomorphic.continuous⟩

abbrev Tube (D : TopologicalSpace.Opens ℂ) := tubeOpen D

def tubeTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (D : TopologicalSpace.Opens ℂ) (v : Fin 2 → ℤ) (x : Tube D) : Tube D :=
  ⟨twistedTranslate C v x, by
    change time (twistedTranslate C v x) ∈ D
    rw [time_twistedTranslate]
    exact x.2⟩

@[instance_reducible] def tubeAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (D : TopologicalSpace.Opens ℂ) : MulAction (Multiplicative (Fin 2 → ℤ)) (Tube D) where
  smul v x := tubeTranslate C D v.toAdd x
  one_smul x := Subtype.ext (twistedTranslate_zero C x)
  mul_smul v w x := Subtype.ext (twistedTranslate_add C v.toAdd w.toAdd x).symm

theorem tubeTranslate_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (D : TopologicalSpace.Opens ℂ) (v : Fin 2 → ℤ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (D : Set ℂ)) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (tubeTranslate C D v) := by
  intro x
  have he : ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (fun y : Tube D => (tubeTranslate C D v y : Space)) x ↔
    ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (tubeTranslate C D v) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  change ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 3))
    (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
    (fun y : Tube D => twistedTranslate C v (y : Space)) x
  apply (contMDiffAt_subtype_iff (U := tubeOpen D) (f := twistedTranslate C v)).mpr
  exact (twistedTranslate_holomorphic C v D.isOpen hC).contMDiffAt
    ((tubeOpen D).isOpen.mem_nhds x.2)

def tubeTranslationHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (D : TopologicalSpace.Opens ℂ) (v : Fin 2 → ℤ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (D : Set ℂ)) : Tube D ≃ₜ Tube D where
  toFun := tubeTranslate C D v
  invFun := tubeTranslate C D (-v)
  left_inv x := by
    apply Subtype.ext
    exact (twistedTranslate_add C (-v) v x).trans (by simp)
  right_inv x := by
    apply Subtype.ext
    exact (twistedTranslate_add C v (-v) x).trans (by simp)
  continuous_toFun := (tubeTranslate_holomorphic C D v hC).continuous
  continuous_invFun := (tubeTranslate_holomorphic C D (-v) hC).continuous

end Wikipedia.HopfProblem.ToricSpace

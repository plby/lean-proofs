import Wikipedia.HopfProblem.CuspNormalizationGermsIntegral

/-!
# Actual analytic germ maps along coordinate axes

Axis restriction is pullback along the actual coordinate-axis inclusion,
and axis extension is pullback along the actual coordinate projection.
Their identities follow from those maps on analytic representatives.
In particular, restricting an extension to a different axis is its
constant value at the origin.  Both two- and three-dimensional versions
use the original neighbourhood-germ rings.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex

open ToricCharts ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

/-- Actual analytic germs on the complex coordinate axis. -/
abbrev AxisGerm := Germs.AnalyticGerm (0 : ℂ)

theorem coordinateInclusion_analyticAt (n : ℕ) (i : Fin n) :
    AnalyticAt ℂ (fun t : ℂ => (Pi.single i t : CoordinateSpace n)) 0 := by
  have h : ContDiff ℂ ω (fun t : ℂ => (Pi.single i t : CoordinateSpace n)) :=
    contDiff_single (fun _ : Fin n => ℂ) ω i
  exact h.contDiffAt.analyticAt

@[simp] theorem coordinateInclusion_zero (n : ℕ) (i : Fin n) :
    (Pi.single i (0 : ℂ) : CoordinateSpace n) = 0 := by simp

theorem coordinateProjection_analyticAt (n : ℕ) (i : Fin n) :
    AnalyticAt ℂ (fun w : CoordinateSpace n => w i) 0 :=
  (contDiff_apply ℂ ℂ i (n := ω)).contDiffAt.analyticAt

/-- Actual pullback along a coordinate-axis inclusion. -/
def coordinateRestriction (n : ℕ) (i : Fin n) :
    Germs.AnalyticGerm (0 : CoordinateSpace n) →+* AxisGerm :=
  Germs.pullbackAt (fun t : ℂ => (Pi.single i t : CoordinateSpace n))
    (coordinateInclusion_analyticAt n i)
    (coordinateInclusion_zero n i)

/-- Actual pullback along a coordinate projection. -/
def coordinateExtension (n : ℕ) (i : Fin n) :
    AxisGerm →+* Germs.AnalyticGerm (0 : CoordinateSpace n) :=
  Germs.pullbackAt (fun w : CoordinateSpace n => w i)
    (coordinateProjection_analyticAt n i) rfl

theorem coordinateRestriction_ofAnalytic (n : ℕ) (i : Fin n)
    (f : CoordinateSpace n → ℂ) (hf : AnalyticAt ℂ f 0) :
    coordinateRestriction n i (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (f ∘ Pi.single i)
        (hf.comp_of_eq (coordinateInclusion_analyticAt n i) (coordinateInclusion_zero n i)) :=
  Germs.pullbackAt_ofAnalytic ..

theorem coordinateExtension_ofAnalytic (n : ℕ) (i : Fin n)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    coordinateExtension n i (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (f ∘ fun w : CoordinateSpace n => w i)
        (hf.comp_of_eq (coordinateProjection_analyticAt n i) rfl) :=
  Germs.pullbackAt_ofAnalytic ..

@[simp] theorem coordinateRestriction_extension (n : ℕ) (i : Fin n) (φ : AxisGerm) :
    coordinateRestriction n i (coordinateExtension n i φ) = φ := by
  obtain ⟨f, hf, rfl⟩ := Germs.exists_representative φ
  rw [coordinateExtension_ofAnalytic, coordinateRestriction_ofAnalytic]
  apply (Germs.ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall fun z => by simp only [Function.comp_apply, Pi.single_eq_same]

theorem coordinateRestriction_extension_ne (n : ℕ) {i j : Fin n} (hij : i ≠ j)
    (φ : AxisGerm) :
    coordinateRestriction n i (coordinateExtension n j φ) =
      Germs.constant (0 : ℂ) (Germs.eval (0 : ℂ) φ) := by
  obtain ⟨f, hf, rfl⟩ := Germs.exists_representative φ
  change coordinateRestriction n i (coordinateExtension n j (Germs.ofAnalytic f hf)) =
    Germs.ofAnalytic (fun _ : ℂ => f 0) analyticAt_const
  rw [coordinateExtension_ofAnalytic, coordinateRestriction_ofAnalytic]
  apply (Germs.ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall fun z => by
    simp only [Function.comp_apply, Pi.single_eq_of_ne hij.symm]

@[simp] theorem eval_coordinateRestriction (n : ℕ) (i : Fin n)
    (φ : Germs.AnalyticGerm (0 : CoordinateSpace n)) :
    Germs.eval (0 : ℂ) (coordinateRestriction n i φ) =
      Germs.eval (0 : CoordinateSpace n) φ :=
  Germs.eval_pullbackAt _ _ _ φ

@[simp] theorem eval_coordinateExtension (n : ℕ) (i : Fin n) (φ : AxisGerm) :
    Germs.eval (0 : CoordinateSpace n) (coordinateExtension n i φ) =
      Germs.eval (0 : ℂ) φ :=
  Germs.eval_pullbackAt _ _ _ φ

@[simp] theorem coordinateRestriction_constant (n : ℕ) (i : Fin n) (c : ℂ) :
    coordinateRestriction n i (Germs.constant (0 : CoordinateSpace n) c) =
      Germs.constant (0 : ℂ) c := by
  change coordinateRestriction n i (Germs.ofAnalytic (fun _ => c) analyticAt_const) = _
  rw [coordinateRestriction_ofAnalytic]
  rfl

@[simp] theorem coordinateExtension_constant (n : ℕ) (i : Fin n) (c : ℂ) :
    coordinateExtension n i (Germs.constant (0 : ℂ) c) =
      Germs.constant (0 : CoordinateSpace n) c := by
  change coordinateExtension n i (Germs.ofAnalytic (fun _ => c) analyticAt_const) = _
  rw [coordinateExtension_ofAnalytic]
  rfl

/-- Restriction of a branch germ to an actual coordinate axis. -/
abbrev axisRestriction (i : Fin 2) : Germs.BranchGerm →+* AxisGerm :=
  coordinateRestriction 2 i

/-- Extension of an axis germ, constant along the other branch coordinate. -/
abbrev axisExtension (i : Fin 2) : AxisGerm →+* Germs.BranchGerm :=
  coordinateExtension 2 i

/-- Restriction of an ambient germ to an actual coordinate axis. -/
abbrev ambientAxisRestriction (k : Fin 3) : Germs.AmbientGerm →+* AxisGerm :=
  coordinateRestriction 3 k

/-- Extension of an axis germ to the actual ambient three-space. -/
abbrev ambientAxisExtension (k : Fin 3) : AxisGerm →+* Germs.AmbientGerm :=
  coordinateExtension 3 k

theorem axisRestriction_ofAnalytic (i : Fin 2) (f : E₂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    axisRestriction i (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (f ∘ Pi.single i)
        (hf.comp_of_eq (coordinateInclusion_analyticAt 2 i) (coordinateInclusion_zero 2 i)) :=
  coordinateRestriction_ofAnalytic 2 i f hf

theorem axisExtension_ofAnalytic (i : Fin 2) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    axisExtension i (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (f ∘ fun w : E₂ => w i)
        (hf.comp_of_eq (coordinateProjection_analyticAt 2 i) rfl) :=
  coordinateExtension_ofAnalytic 2 i f hf

theorem ambientAxisRestriction_ofAnalytic (k : Fin 3) (f : E₃ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    ambientAxisRestriction k (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (f ∘ Pi.single k)
        (hf.comp_of_eq (coordinateInclusion_analyticAt 3 k) (coordinateInclusion_zero 3 k)) :=
  coordinateRestriction_ofAnalytic 3 k f hf

theorem ambientAxisExtension_ofAnalytic (k : Fin 3) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    ambientAxisExtension k (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (f ∘ fun w : E₃ => w k)
        (hf.comp_of_eq (coordinateProjection_analyticAt 3 k) rfl) :=
  coordinateExtension_ofAnalytic 3 k f hf

@[simp] theorem axisRestriction_extension (i : Fin 2) (φ : AxisGerm) :
    axisRestriction i (axisExtension i φ) = φ := coordinateRestriction_extension 2 i φ

theorem axisRestriction_extension_ne {i j : Fin 2} (hij : i ≠ j) (φ : AxisGerm) :
    axisRestriction i (axisExtension j φ) =
      Germs.constant (0 : ℂ) (Germs.eval (0 : ℂ) φ) :=
  coordinateRestriction_extension_ne 2 hij φ

@[simp] theorem ambientAxisRestriction_extension (k : Fin 3) (φ : AxisGerm) :
    ambientAxisRestriction k (ambientAxisExtension k φ) = φ :=
  coordinateRestriction_extension 3 k φ

theorem ambientAxisRestriction_extension_ne {i j : Fin 3} (hij : i ≠ j) (φ : AxisGerm) :
    ambientAxisRestriction i (ambientAxisExtension j φ) =
      Germs.constant (0 : ℂ) (Germs.eval (0 : ℂ) φ) :=
  coordinateRestriction_extension_ne 3 hij φ

@[simp] theorem eval_axisRestriction (i : Fin 2) (φ : Germs.BranchGerm) :
    Germs.eval (0 : ℂ) (axisRestriction i φ) = Germs.eval (0 : E₂) φ :=
  eval_coordinateRestriction 2 i φ

@[simp] theorem eval_axisExtension (i : Fin 2) (φ : AxisGerm) :
    Germs.eval (0 : E₂) (axisExtension i φ) = Germs.eval (0 : ℂ) φ :=
  eval_coordinateExtension 2 i φ

@[simp] theorem eval_ambientAxisRestriction (k : Fin 3) (φ : Germs.AmbientGerm) :
    Germs.eval (0 : ℂ) (ambientAxisRestriction k φ) = Germs.eval (0 : E₃) φ :=
  eval_coordinateRestriction 3 k φ

@[simp] theorem eval_ambientAxisExtension (k : Fin 3) (φ : AxisGerm) :
    Germs.eval (0 : E₃) (ambientAxisExtension k φ) = Germs.eval (0 : ℂ) φ :=
  eval_coordinateExtension 3 k φ

@[simp] theorem axisRestriction_constant (i : Fin 2) (c : ℂ) :
    axisRestriction i (Germs.constant (0 : E₂) c) = Germs.constant (0 : ℂ) c :=
  coordinateRestriction_constant 2 i c

@[simp] theorem axisExtension_constant (i : Fin 2) (c : ℂ) :
    axisExtension i (Germs.constant (0 : ℂ) c) = Germs.constant (0 : E₂) c :=
  coordinateExtension_constant 2 i c

@[simp] theorem ambientAxisRestriction_constant (k : Fin 3) (c : ℂ) :
    ambientAxisRestriction k (Germs.constant (0 : E₃) c) = Germs.constant (0 : ℂ) c :=
  coordinateRestriction_constant 3 k c

@[simp] theorem ambientAxisExtension_constant (k : Fin 3) (c : ℂ) :
    ambientAxisExtension k (Germs.constant (0 : ℂ) c) = Germs.constant (0 : E₃) c :=
  coordinateExtension_constant 3 k c

@[simp] theorem eval_toBranch (j : Fin 3) (φ : Germs.AmbientGerm) :
    Germs.eval (0 : E₂) (Germs.toBranch j φ) = Germs.eval (0 : E₃) φ :=
  Germs.eval_pullbackAt _ _ _ φ

@[simp] theorem eval_extendBranch (j : Fin 3) (φ : Germs.BranchGerm) :
    Germs.eval (0 : E₃) (Germs.extendBranch j φ) = Germs.eval (0 : E₂) φ :=
  Germs.eval_pullbackAt _ _ _ φ

@[simp] theorem toBranch_constant (j : Fin 3) (c : ℂ) :
    Germs.toBranch j (Germs.constant (0 : E₃) c) = Germs.constant (0 : E₂) c := by
  change Germs.toBranch j (Germs.ofAnalytic (fun _ => c) analyticAt_const) = _
  rw [Germs.toBranch_ofAnalytic]
  rfl

@[simp] theorem extendBranch_constant (j : Fin 3) (c : ℂ) :
    Germs.extendBranch j (Germs.constant (0 : E₂) c) = Germs.constant (0 : E₃) c := by
  change Germs.extendBranch j (Germs.ofAnalytic (fun _ => c) analyticAt_const) = _
  rw [Germs.extendBranch_ofAnalytic]
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex

import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreSections
import Mathlib.Tactic.FieldSimp

/-!
# Native algebra of the multiplier comparing two frames

Two nonvanishing actual bundle sections on an open set determine a unit
multiplier in the preferred fibre coordinates. In arbitrary original
bundle charts its coefficient is the ratio of the two native local
frame coefficients. This file makes no holomorphicity assumptions.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.OpenMaps

open HolomorphicCharacterBundle

variable {M ι η : Type*} [TopologicalSpace M]
    (A : TransitionData M ι) (B : TransitionData M η)
    (U : Opens M) (s : ∀ x, A.core.Fiber x) (t : ∀ x, B.core.Fiber x)
    (hs : ∀ x ∈ U, s x ≠ 0) (ht : ∀ x ∈ U, t x ≠ 0)

include hs in
/-- Nonvanishing in the actual fibre implies nonvanishing of every native
local coefficient, even when only nonvanishing on the given open is known. -/
theorem localCoefficient_ne_zero_on (i : ι) {x : M} (hx : x ∈ U) :
    A.localCoefficient s i x ≠ 0 :=
  mul_ne_zero (A.transition_ne_zero _ _ _) (hs x hx)

/-- The ratio of two original frame values, extended by the unit `1`
outside the open set on which the frames are nonvanishing. -/
def frameMultiplier (x : M) : ℂˣ := by
  classical
  exact if hx : x ∈ U then
    Units.mk0 (id (α := ℂ) (t x) / id (α := ℂ) (s x))
      (div_ne_zero (ht x hx) (hs x hx))
  else 1

@[simp] theorem frameMultiplier_val {x : M} (hx : x ∈ U) :
    (frameMultiplier A B U s t hs ht x : ℂ) =
      id (α := ℂ) (t x) / id (α := ℂ) (s x) := by
  simp only [frameMultiplier, dif_pos hx, Units.val_mk0]

@[simp] theorem frameMultiplier_of_notMem {x : M} (hx : x ∉ U) :
    frameMultiplier A B U s t hs ht x = 1 := by
  simp only [frameMultiplier, dif_neg hx]

@[simp] theorem frameMultiplier_val_of_notMem {x : M} (hx : x ∉ U) :
    (frameMultiplier A B U s t hs ht x : ℂ) = 1 := by
  rw [frameMultiplier_of_notMem A B U s t hs ht hx]
  rfl

theorem frameMultiplier_ne_zero (x : M) :
    (frameMultiplier A B U s t hs ht x : ℂ) ≠ 0 :=
  (frameMultiplier A B U s t hs ht x).ne_zero

/-- Reversing the two frames gives precisely the reciprocal unit multiplier. -/
theorem frameMultiplier_symm (x : M) :
    frameMultiplier B A U t s ht hs x = (frameMultiplier A B U s t hs ht x)⁻¹ := by
  by_cases hx : x ∈ U
  · apply Units.ext
    rw [Units.val_inv_eq_inv_val, frameMultiplier_val B A U t s ht hs hx,
      frameMultiplier_val A B U s t hs ht hx, inv_div]
  · rw [frameMultiplier_of_notMem B A U t s ht hs hx,
      frameMultiplier_of_notMem A B U s t hs ht hx, inv_one]

/-- Multiplication by the preferred frame ratio sends the original first
frame exactly to the original second frame in the native target total space. -/
theorem frameMultiplier_frame {x : M} (hx : x ∈ U) :
    (⟨x, (frameMultiplier A B U s t hs ht x : ℂ) * id (α := ℂ) (s x)⟩ :
      B.core.TotalSpace) = ⟨x, t x⟩ := by
  have hv : (frameMultiplier A B U s t hs ht x : ℂ) * id (α := ℂ) (s x) =
      id (α := ℂ) (t x) := by
    rw [frameMultiplier_val A B U s t hs ht hx]
    exact div_mul_cancel₀ _ (hs x hx)
  exact congrArg (fun v : ℂ => (⟨x, v⟩ : B.core.TotalSpace)) hv

/-- The exact native chart coefficient of multiplication by a frame ratio.
The two chart indices are independent, and no cover-set equality is assumed. -/
theorem frameMultiplier_localCoefficient (i : ι) (j : η) (p : A.core.TotalSpace)
    (hp : p.proj ∈ U) :
    (B.core.localTriv j
      (⟨p.proj, (frameMultiplier A B U s t hs ht p.proj : ℂ) * id (α := ℂ) p.2⟩ :
        B.core.TotalSpace)).2 =
      (B.localCoefficient t j p.proj / A.localCoefficient s i p.proj) *
        (A.core.localTriv i p).2 := by
  change (B.transition (B.indexAt p.proj) j p.proj : ℂ) *
      ((frameMultiplier A B U s t hs ht p.proj : ℂ) * id (α := ℂ) p.2) =
    ((B.transition (B.indexAt p.proj) j p.proj : ℂ) * id (α := ℂ) (t p.proj) /
      ((A.transition (A.indexAt p.proj) i p.proj : ℂ) * id (α := ℂ) (s p.proj))) *
      ((A.transition (A.indexAt p.proj) i p.proj : ℂ) * id (α := ℂ) p.2)
  rw [frameMultiplier_val A B U s t hs ht hp]
  field_simp [A.transition_ne_zero (A.indexAt p.proj) i p.proj, hs p.proj hp]

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.OpenMaps

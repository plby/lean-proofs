import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The actual graph deformation used in cellwise homotopy excision

A height function moves the bottom face of a cylinder upward, leaving
the top face and every zero-height parameter fixed. A set below the
final graph is removed; another set whose projection has height zero
is avoided by the entire moving bottom face. These are actual continuous
homotopies, before any cell-coordinate or dimension argument is applied.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.CellExcisionGraph

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

def clock (φ : C(P, I)) (s t : I) (p : P) : I :=
  ⟨(s : ℝ) * φ p + (1 - (s : ℝ) * φ p) * (t : ℝ), by
    have h0 : 0 ≤ (s : ℝ) * φ p := mul_nonneg s.property.1 (φ p).property.1
    have h1 : (s : ℝ) * φ p ≤ 1 := calc
      (s : ℝ) * φ p ≤ 1 * (φ p : ℝ) :=
        mul_le_mul_of_nonneg_right s.property.2 (φ p).property.1
      _ ≤ 1 := by simpa only [one_mul] using (φ p).property.2
    refine ⟨add_nonneg h0 (mul_nonneg (sub_nonneg.mpr h1) t.property.1), ?_⟩
    have h := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr t.property.2)
    nlinarith⟩

theorem continuous_clock (φ : C(P, I)) :
    Continuous (fun q : I × (I × P) ↦ clock φ q.1 q.2.1 q.2.2) := by
  apply Continuous.subtype_mk
  have hs : Continuous (fun q : I × (I × P) ↦ (q.1 : ℝ) * φ q.2.2) :=
    (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (φ.continuous.comp (continuous_snd.comp continuous_snd)))
  exact hs.add ((continuous_const.sub hs).mul
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))

theorem clock_initial (φ : C(P, I)) (t : I) (p : P) : clock φ 0 t p = t := by
  apply Subtype.ext
  simp [clock]

theorem clock_top (φ : C(P, I)) (s : I) (p : P) : clock φ s 1 p = 1 := by
  apply Subtype.ext
  simp [clock]

theorem clock_fixed (φ : C(P, I)) (s t : I) (p : P) (h : φ p = 0) :
    clock φ s t p = t := by
  apply Subtype.ext
  simp [clock, h]

theorem clock_final_ge (φ : C(P, I)) (t : I) (p : P) : φ p ≤ clock φ 1 t p := by
  change (φ p : ℝ) ≤ 1 * (φ p : ℝ) + (1 - 1 * (φ p : ℝ)) * (t : ℝ)
  simp only [one_mul]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (φ p).property.2) t.property.1)

def endpoint (φ : C(P, I)) : C(I × P, I × P) :=
  ⟨fun z ↦ (clock φ 1 z.1 z.2, z.2),
    ((continuous_clock φ).comp (continuous_const.prodMk continuous_id)).prodMk continuous_snd⟩

def domainHomotopy (φ : C(P, I)) :
    (ContinuousMap.id (I × P)).Homotopy (endpoint φ) where
  toFun q := (clock φ q.1 q.2.1 q.2.2, q.2.2)
  continuous_toFun := (continuous_clock φ).prodMk (continuous_snd.comp continuous_snd)
  map_zero_left z := Prod.ext (clock_initial φ z.1 z.2) rfl
  map_one_left _ := rfl

theorem domainHomotopy_fixed (φ : C(P, I)) (s : I) (z : I × P) (h : φ z.2 = 0) :
    domainHomotopy φ (s, z) = z := Prod.ext (clock_fixed φ s z.1 z.2 h) rfl

theorem domainHomotopy_top (φ : C(P, I)) (s : I) (p : P) :
    domainHomotopy φ (s, (1, p)) = (1, p) := Prod.ext (clock_top φ s p) rfl

theorem endpoint_avoids (φ : C(P, I)) (Q : Set (I × P))
    (hQ : ∀ z ∈ Q, z.1 < φ z.2) (z : I × P) : endpoint φ z ∉ Q := by
  intro hz
  exact (not_lt_of_ge (clock_final_ge φ z.1 z.2)) (hQ _ hz)

theorem moving_bottom_avoids (φ : C(P, I)) (L : Set (I × P))
    (hL : ∀ z ∈ L, φ z.2 = 0) (h0 : ∀ p, (0, p) ∉ L) (s : I) (p : P) :
    domainHomotopy φ (s, (0, p)) ∉ L := by
  intro hz
  have hp : φ p = 0 := hL _ hz
  rw [domainHomotopy_fixed φ s (0, p) hp] at hz
  exact h0 p hz

def homotopy (f : C(I × P, X)) (φ : C(P, I)) : f.Homotopy (f.comp (endpoint φ)) where
  toContinuousMap := f.comp (domainHomotopy φ).toContinuousMap
  map_zero_left z := congrArg f ((domainHomotopy φ).apply_zero z)
  map_one_left _ := rfl

theorem homotopy_fixed (f : C(I × P, X)) (φ : C(P, I)) (s : I) (z : I × P)
    (h : φ z.2 = 0) : homotopy f φ (s, z) = f z :=
  congrArg f (domainHomotopy_fixed φ s z h)

theorem homotopy_top (f : C(I × P, X)) (φ : C(P, I)) (s : I) (p : P) :
    homotopy f φ (s, (1, p)) = f (1, p) := congrArg f (domainHomotopy_top φ s p)

end NoExoticSixSphere.CellExcisionGraph

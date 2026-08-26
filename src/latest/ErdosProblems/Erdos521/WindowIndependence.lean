/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Statistics on disjoint coefficient windows are mutually independent.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Model
import Mathlib.Probability.Independence.InfinitePi

namespace Erdos521

open MeasureTheory ProbabilityTheory

theorem window_sigma_injective {ι : Type*} (W : ι → Finset ℕ)
    (hW : Pairwise (fun i j ↦ Disjoint (W i) (W j))) :
    Function.Injective (fun p : (i : ι) × W i ↦ (p.2 : ℕ)) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ hkl
  change (k : ℕ) = (l : ℕ) at hkl
  have hij : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hW hne) k.property (hkl.symm ▸ l.property)
  subst j
  have h : k = l := Subtype.ext hkl
  subst l
  rfl

theorem sequenceLaw_map_window_tuples {ι : Type*} (W : ι → Finset ℕ)
    (hW : Pairwise (fun i j ↦ Disjoint (W i) (W j))) :
    sequenceLaw.map (fun ε : ℕ → ℝ ↦ fun i (k : W i) ↦ ε k) =
      Measure.infinitePi (fun i ↦ Measure.infinitePi (fun _ : W i ↦ signLaw)) := by
  have hmap := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ signLaw)
    (window_sigma_injective W hW)
  change sequenceLaw.map (fun ε : ℕ → ℝ ↦ fun p : (i : ι) × W i ↦ ε p.2) =
    Measure.infinitePi (fun _ : (i : ι) × W i ↦ signLaw) at hmap
  calc
    sequenceLaw.map (fun ε : ℕ → ℝ ↦ fun i (k : W i) ↦ ε k) =
        (sequenceLaw.map (fun ε : ℕ → ℝ ↦ fun p : (i : ι) × W i ↦ ε p.2)).map
          (MeasurableEquiv.piCurry (fun i (_ : W i) ↦ ℝ)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [hmap]
      exact Measure.infinitePi_map_piCurry (fun i (_ : W i) ↦ signLaw)

theorem independent_window_tuples {ι : Type*} (W : ι → Finset ℕ)
    (hW : Pairwise (fun i j ↦ Disjoint (W i) (W j))) :
    iIndepFun (fun i (ε : ℕ → ℝ) (k : W i) ↦ ε k) sequenceLaw := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop), sequenceLaw_map_window_tuples W hW]
  congr 1
  funext i
  exact (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ signLaw)
    (f := fun k : W i ↦ (k : ℕ)) Subtype.val_injective).symm

theorem independent_window_statistics {ι : Type*} (W : ι → Finset ℕ)
    (hW : Pairwise (fun i j ↦ Disjoint (W i) (W j)))
    (F : (i : ι) → (W i → ℝ) → ℝ) (hF : ∀ i, Measurable (F i)) :
    iIndepFun (fun i (ε : ℕ → ℝ) ↦ F i (fun k ↦ ε k)) sequenceLaw :=
  (independent_window_tuples W hW).comp F hF

end Erdos521

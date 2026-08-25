import StackExchange.Puzzling139335.N4Diagonal.Defs
import Mathlib.Topology.Order.Compact

/-!
# Actual maximal bottom and left contacts

Compactness of the Jordan prototype makes each nonempty axis-contact set
attain its maximal coordinate.  The one-corner condition makes both maxima
strictly less than one.  No positive lower bound is needed by the side
coverage estimates.
-/

open Set

namespace Puzzling139335.N4Diagonal.Model

/-- The maximal bottom contact is an actual point of the prototype. -/
theorem exists_bottom_maximum (m : Model) :
    ∃ x₀ : ℝ, x₀ ∈ Ico (0 : ℝ) 1 ∧ (!₂[x₀, 0] : Plane) ∈ m.P ∧
      ∀ x ∈ m.P, x 1 = 0 → x 0 ≤ x₀ := by
  have hclosed : IsClosed {x : Plane | x 1 = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hcompact := m.jordan.isCompact.inter_right hclosed
  have hnonempty : (m.P ∩ {x : Plane | x 1 = 0}).Nonempty :=
    ⟨0, m.origin_mem, rfl⟩
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    (f := fun x : Plane => x 0) (by fun_prop)
  have hpzero : p 1 = 0 := hp.2
  have hlt : p 0 < 1 := by
    by_contra hnot
    have hpone : p 0 = 1 :=
      le_antisymm (m.subset_square hp.1).1.2 (not_lt.mp hnot)
    have heq : p = corner 1 := by
      ext i
      fin_cases i <;> simp [corner, hpone, hpzero, Fin.ext_iff]
    have hj := m.origin_only_corner 1 (heq ▸ hp.1)
    norm_num [Fin.ext_iff] at hj
  refine ⟨p 0, ⟨(m.triangle hp.1).1, hlt⟩, ?_, ?_⟩
  · have heq : (!₂[p 0, 0] : Plane) = p := by
      ext i
      fin_cases i
      · rfl
      · exact hpzero.symm
    rw [heq]
    exact hp.1
  · intro x hx hxzero
    exact hmax ⟨hx, hxzero⟩

/-- The maximal left contact is an actual point of the prototype. -/
theorem exists_left_maximum (m : Model) :
    ∃ y₀ : ℝ, y₀ ∈ Ico (0 : ℝ) 1 ∧ (!₂[0, y₀] : Plane) ∈ m.P ∧
      ∀ x ∈ m.P, x 0 = 0 → x 1 ≤ y₀ := by
  have hclosed : IsClosed {x : Plane | x 0 = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hcompact := m.jordan.isCompact.inter_right hclosed
  have hnonempty : (m.P ∩ {x : Plane | x 0 = 0}).Nonempty :=
    ⟨0, m.origin_mem, rfl⟩
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    (f := fun x : Plane => x 1) (by fun_prop)
  have hpzero : p 0 = 0 := hp.2
  have hlt : p 1 < 1 := by
    by_contra hnot
    have hpone : p 1 = 1 :=
      le_antisymm (m.subset_square hp.1).2.2 (not_lt.mp hnot)
    have heq : p = corner 3 := by
      ext i
      fin_cases i <;> simp [corner, hpone, hpzero, Fin.ext_iff]
    have hj := m.origin_only_corner 3 (heq ▸ hp.1)
    norm_num [Fin.ext_iff] at hj
  refine ⟨p 1, ⟨(m.triangle hp.1).2.1, hlt⟩, ?_, ?_⟩
  · have heq : (!₂[0, p 1] : Plane) = p := by
      ext i
      fin_cases i
      · exact hpzero.symm
      · rfl
    rw [heq]
    exact hp.1
  · intro x hx hxzero
    exact hmax ⟨hx, hxzero⟩

/-- Simultaneous bottom and left maxima, with actual endpoint membership
and the upper bounds needed to exclude the repeated piece on each side. -/
theorem exists_axis_maxima (m : Model) :
    ∃ x₀ y₀ : ℝ, x₀ ∈ Ico (0 : ℝ) 1 ∧ y₀ ∈ Ico (0 : ℝ) 1 ∧
      (!₂[x₀, 0] : Plane) ∈ m.P ∧ (!₂[0, y₀] : Plane) ∈ m.P ∧
      (∀ x ∈ m.P, x 1 = 0 → x 0 ≤ x₀) ∧
      (∀ x ∈ m.P, x 0 = 0 → x 1 ≤ y₀) := by
  obtain ⟨x₀, hx₀, hbottom, hmaxBottom⟩ := m.exists_bottom_maximum
  obtain ⟨y₀, hy₀, hleft, hmaxLeft⟩ := m.exists_left_maximum
  exact ⟨x₀, y₀, hx₀, hy₀, hbottom, hleft, hmaxBottom, hmaxLeft⟩

end Puzzling139335.N4Diagonal.Model

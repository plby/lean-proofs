import Wikipedia.HopfProblem.DegreeCollapseSelectiveIntersectionControl

/-!
# The selected two-point fibers determine the removed original pairs

Each selected crossing value has precisely its specified two preimages,
one on each source side. Every off-diagonal pair over those values is
therefore cross-side. The selective difference formula removes exactly
the old pairs over the two selected values, with no remaining side test.
-/

open Set Function

namespace Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet

variable {X Y : Type*} {f : X → Y} {U : Set X}

theorem opposite_sides_of_two_point_fiber {x₀ y₀ x y : X}
    (hx₀ : x₀ ∈ U) (hy₀ : y₀ ∉ U)
    (hfib : ∀ z, f z = f x₀ → z = x₀ ∨ z = y₀)
    (hne : x ≠ y) (hxy : f x = f y) (hx : f x = f x₀) :
    ¬ (x ∈ U ↔ y ∈ U) := by
  rcases hfib x hx with rfl | rfl <;>
    rcases hfib y (hxy.symm.trans hx) with rfl | rfl
  · exact (hne rfl).elim
  · exact fun hh => hy₀ (hh.mp hx₀)
  · exact fun hh => hy₀ (hh.mpr hx₀)
  · exact (hne rfl).elim

theorem selective_pair_removal_eq_value_removal {x₀ x₁ y₀ y₁ : X}
    (hx₀ : x₀ ∈ U) (hx₁ : x₁ ∈ U) (hy₀ : y₀ ∉ U) (hy₁ : y₁ ∉ U)
    (hfib₀ : ∀ z, f z = f x₀ → z = x₀ ∨ z = y₀)
    (hfib₁ : ∀ z, f z = f x₁ → z = x₁ ∨ z = y₁) :
    {p : X × X | p.1 ≠ p.2 ∧ f p.1 = f p.2} \
        {p : X × X | f p.1 ∈ ({f x₀, f x₁} : Set Y) ∧ ¬ (p.1 ∈ U ↔ p.2 ∈ U)} =
      {p : X × X | p.1 ≠ p.2 ∧ f p.1 = f p.2} \
        {p : X × X | f p.1 ∈ ({f x₀, f x₁} : Set Y)} := by
  ext p
  constructor
  · rintro ⟨hp, hnot⟩
    refine ⟨hp, ?_⟩
    intro hc
    apply hnot
    refine ⟨hc, ?_⟩
    rcases hc with hc | hc
    · exact opposite_sides_of_two_point_fiber hx₀ hy₀ hfib₀ hp.1 hp.2 hc
    · exact opposite_sides_of_two_point_fiber hx₁ hy₁ hfib₁ hp.1 hp.2 hc
  · rintro ⟨hp, hnot⟩
    exact ⟨hp, fun hc => hnot hc.1⟩

end Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet

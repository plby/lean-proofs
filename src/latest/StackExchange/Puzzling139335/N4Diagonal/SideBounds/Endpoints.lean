import StackExchange.Puzzling139335.N4Diagonal.SideBounds.Coverage
import StackExchange.Puzzling139335.N4Diagonal.SideBounds.Faces

/-!
# Source endpoints forced by actual square-side coverage

The endpoints below belong to the prototype itself.  They follow from
actual image coverage and finite contacts, with closedness supplying the
limiting endpoint of each side interval.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners ReflectionSeparation

private theorem image_mem_of_pointwise {P : Set Plane} {e g : Plane → Plane}
    (h : ∀ x, e x = g x) {y : Plane} (hy : y ∈ e '' P) : y ∈ g '' P := by
  obtain ⟨x, hx, heq⟩ := hy
  exact ⟨x, hx, (h x).symm.trans heq⟩

namespace Model

private theorem cover_last_first (m : Model) :
    ∀ x ∈ unitSquare, x ∈ m.P ∨ x ∈ antiDiagonal '' m.P ∨
      x ∈ m.f '' m.P ∨ x ∈ m.e '' m.P := by
  intro x hx
  rcases m.cover x hx with hp | hc | he | hf
  · exact Or.inl hp
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inr he))
  · exact Or.inr (Or.inr (Or.inl hf))

/-- Assignment II: top coverage forces the first incoming endpoint. -/
theorem first_incoming_mem_of_top_finite (m : Model)
    (hform : ∀ x, m.e x = firstPlus 3 m.p m.θ x)
    (hfinite : (m.f '' m.P ∩ {x : Plane | x 1 = 1}).Finite)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 0 = 0 → x 1 ≤ y₀) :
    m.p - (1 - y₀) • ray m.θ ∈ m.P := by
  have hmaps := m.top_source_interval (source := fun t => m.p - t • ray m.θ)
    (by fun_prop) m.cover
    (fun t ht => (mem_firstPlus_three_top_iff m.P m.p m.θ t).mp
      (image_mem_of_pointwise hform ht)) hfinite hy₀ hmax
  exact hmaps ⟨sub_nonneg.mpr hy₀.2.le, le_rfl⟩

/-- Assignment I: bottom coverage forces the first incoming endpoint. -/
theorem first_incoming_mem_of_bottom_finite (m : Model)
    (hform : ∀ x, m.e x = firstPlus 1 m.p m.θ x)
    (hfinite : (m.f '' m.P ∩ {x : Plane | x 1 = 0}).Finite)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 1 = 0 → x 0 ≤ x₀) :
    m.p - (1 - x₀) • ray m.θ ∈ m.P := by
  have hmaps := m.bottom_source_interval (source := fun t => m.p - t • ray m.θ)
    (by fun_prop) m.cover
    (fun t ht => (mem_firstPlus_one_bottom_iff m.P m.p m.θ t).mp
      (image_mem_of_pointwise hform ht)) hfinite hx₀ hmax
  exact hmaps ⟨sub_nonneg.mpr hx₀.2.le, le_rfl⟩

/-- Assignment II with preserving last placement: right coverage forces
the last incoming endpoint. -/
theorem last_incoming_mem_of_right_finite (m : Model)
    (hform : ∀ x, m.f x = lastPlus 1 m.q m.β x)
    (hfinite : (m.e '' m.P ∩ {x : Plane | x 0 = 1}).Finite)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 1 = 0 → x 0 ≤ x₀) :
    m.q - (1 - x₀) • ray m.β ∈ m.P := by
  have hmaps := m.right_source_interval (source := fun t => m.q - t • ray m.β)
    (by fun_prop) m.cover_last_first
    (fun t ht => (mem_lastPlus_one_right_iff m.P m.q m.β t).mp
      (image_mem_of_pointwise hform ht)) hfinite hx₀ hmax
  exact hmaps ⟨sub_nonneg.mpr hx₀.2.le, le_rfl⟩

/-- Assignment II with reversing last placement: bottom coverage forces
the same source endpoint as in the preserving case. -/
theorem last_incoming_mem_of_bottom_finite (m : Model)
    (hform : ∀ x, m.f x = lastMinus 1 m.q m.β x)
    (hfinite : (m.e '' m.P ∩ {x : Plane | x 1 = 0}).Finite)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 1 = 0 → x 0 ≤ x₀) :
    m.q - (1 - x₀) • ray m.β ∈ m.P := by
  have hmaps := m.bottom_source_interval (source := fun t => m.q - t • ray m.β)
    (by fun_prop) m.cover_last_first
    (fun t ht => (mem_lastMinus_one_bottom_iff m.P m.q m.β t).mp
      (image_mem_of_pointwise hform ht)) hfinite hx₀ hmax
  exact hmaps ⟨sub_nonneg.mpr hx₀.2.le, le_rfl⟩

/-- Assignment I with preserving last placement: left coverage forces
the last incoming endpoint. -/
theorem last_incoming_mem_of_left_finite (m : Model)
    (hform : ∀ x, m.f x = lastPlus 3 m.q m.β x)
    (hfinite : (m.e '' m.P ∩ {x : Plane | x 0 = 0}).Finite)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 0 = 0 → x 1 ≤ y₀) :
    m.q - (1 - y₀) • ray m.β ∈ m.P := by
  have hmaps := m.left_source_interval (source := fun t => m.q - t • ray m.β)
    (by fun_prop) m.cover_last_first
    (fun t ht => (mem_lastPlus_three_left_iff m.P m.q m.β t).mp
      (image_mem_of_pointwise hform ht)) hfinite hy₀ hmax
  exact hmaps ⟨sub_nonneg.mpr hy₀.2.le, le_rfl⟩

/-- Assignment I with reversing last placement: top coverage forces
the same source endpoint as in the preserving case. -/
theorem last_incoming_mem_of_top_finite (m : Model)
    (hform : ∀ x, m.f x = lastMinus 3 m.q m.β x)
    (hfinite : (m.e '' m.P ∩ {x : Plane | x 1 = 1}).Finite)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 0 = 0 → x 1 ≤ y₀) :
    m.q - (1 - y₀) • ray m.β ∈ m.P := by
  have hmaps := m.top_source_interval (source := fun t => m.q - t • ray m.β)
    (by fun_prop) m.cover_last_first
    (fun t ht => (mem_lastMinus_three_top_iff m.P m.q m.β t).mp
      (image_mem_of_pointwise hform ht)) hfinite hy₀ hmax
  exact hmaps ⟨sub_nonneg.mpr hy₀.2.le, le_rfl⟩

/-- Left coverage at the first corner forces its outgoing endpoint.
At angle zero this is the vertical endpoint used in the limiting case. -/
theorem first_outgoing_mem_of_left_finite (m : Model)
    (hform : ∀ x, m.e x = firstPlus 3 m.p m.θ x)
    (hfinite : (m.f '' m.P ∩ {x : Plane | x 0 = 0}).Finite)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Ico (0 : ℝ) 1)
    (hmax : ∀ x ∈ m.P, x 0 = 0 → x 1 ≤ y₀) :
    m.p + (1 - y₀) • perpRay m.θ ∈ m.P := by
  have hmaps := m.left_source_interval (source := fun t => m.p + t • perpRay m.θ)
    (by fun_prop) m.cover
    (fun t ht => (mem_firstPlus_three_left_iff m.P m.p m.θ t).mp
      (image_mem_of_pointwise hform ht)) hfinite hy₀ hmax
  exact hmaps ⟨sub_nonneg.mpr hy₀.2.le, le_rfl⟩

end Model

end Puzzling139335.N4Diagonal

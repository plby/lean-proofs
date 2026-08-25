import StackExchange.Puzzling139335.N4TwoOneOne.SupportContacts.AffineSides
import StackExchange.Puzzling139335.N4TwoOneOne.SupportContacts.Angles

/-!
# Contact classification for actual copies of the three-corner source

A cornerless nonaxis copy can have two distinct points on at most one square
side. Its top supporting normal belongs to the prefix, aligned, suffix, or
axis cases, with the angles constructed from its actual matrix coefficients.
-/

open Set

namespace Puzzling139335.N4TwoOneOne.SupportContacts

noncomputable section

/-- Adjacent nontrivial contacts force an actual square corner in the image. -/
theorem exists_square_corner_of_adjacent_contacts {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : e '' P ⊆ unitSquare)
    {i j : Fin 2} {upper other : Bool} (hij : i ≠ j)
    (hi : HasTwoSidePoints (e '' P) i upper)
    (hj : HasTwoSidePoints (e '' P) j other) :
    ∃ k : Fin 4, corner k ∈ e '' P := by
  have hfirst := hasTwoSupportPoints_of_hasTwoSidePoints e hfit hi
  have hsecond := hasTwoSupportPoints_of_hasTwoSidePoints e hfit hj
  obtain ⟨p, _, hpfirst, hpsecond⟩ := common_support_of_perpendicular_faces h hc hs
    (sideNormal_unit e i upper) (sideNormal_unit e j other)
    (sideNormals_orthogonal e hij upper other) hfirst hsecond
  have hpi := image_on_side_of_support e hfit hi hpfirst
  have hpj := image_on_side_of_support e hfit hj hpsecond
  obtain ⟨k, hk⟩ := exists_corner_of_two_side_coordinates hij hpi hpj
  exact ⟨k, p, hpfirst.1, hk⟩

/-- Opposite nontrivial contacts make the corresponding matrix row horizontal. -/
theorem matrix_entry_zero_of_opposite_contacts {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : e '' P ⊆ unitSquare) {i : Fin 2}
    (hbottom : HasTwoSidePoints (e '' P) i false)
    (htop : HasTwoSidePoints (e '' P) i true) :
    PlaneIsometries.linearMatrix e i 1 = 0 := by
  have hfirst : HasTwoSupportPoints P
      (PlaneIsometries.linearMatrix e i 0) (PlaneIsometries.linearMatrix e i 1) := by
    simpa [sideNormalX, sideNormalY, sideSign] using
      hasTwoSupportPoints_of_hasTwoSidePoints e hfit htop
  have hsecond : HasTwoSupportPoints P
      (-PlaneIsometries.linearMatrix e i 0) (-PlaneIsometries.linearMatrix e i 1) := by
    simpa [sideNormalX, sideNormalY, sideSign] using
      hasTwoSupportPoints_of_hasTwoSidePoints e hfit hbottom
  have hne : PlaneIsometries.linearMatrix e i 0 ≠ 0 ∨
      PlaneIsometries.linearMatrix e i 1 ≠ 0 := by
    simpa [sideNormalX, sideNormalY, sideSign] using sideNormal_nonzero e i true
  exact opposite_hasTwoSupportPoints_y_eq_zero h hc hs hne hfirst hsecond

/-- A cornerless copy's nontrivial side contacts must be parallel. -/
theorem contact_coordinates_eq_of_cornerless {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : e '' P ⊆ unitSquare)
    (hcornerless : ∀ k : Fin 4, corner k ∉ e '' P)
    {i j : Fin 2} {upper other : Bool}
    (hi : HasTwoSidePoints (e '' P) i upper)
    (hj : HasTwoSidePoints (e '' P) j other) : i = j := by
  by_contra hij
  obtain ⟨k, hk⟩ := exists_square_corner_of_adjacent_contacts h hc hs e hfit hij hi hj
  exact hcornerless k hk

/-- A cornerless copy whose vertical source axis has two nonzero image
components has nontrivial contact with at most one square side. -/
theorem hasTwoSidePoints_unique {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : e '' P ⊆ unitSquare)
    (hcornerless : ∀ k : Fin 4, corner k ∉ e '' P)
    (hnonaxis : ∀ i : Fin 2, PlaneIsometries.linearMatrix e i 1 ≠ 0)
    {i j : Fin 2} {upper other : Bool}
    (hi : HasTwoSidePoints (e '' P) i upper)
    (hj : HasTwoSidePoints (e '' P) j other) : i = j ∧ upper = other := by
  have hij := contact_coordinates_eq_of_cornerless h hc hs e hfit hcornerless hi hj
  refine ⟨hij, ?_⟩
  subst j
  cases upper <;> cases other
  · rfl
  · exact (hnonaxis i (matrix_entry_zero_of_opposite_contacts h hc hs e hfit hi hj)).elim
  · exact (hnonaxis i (matrix_entry_zero_of_opposite_contacts h hc hs e hfit hj hi)).elim
  · rfl

/-- Both nonzero coefficients of the top normal give the nonaxis condition
needed in the preceding theorem. -/
theorem second_column_nonzero_of_top_row_nonzero (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hx : PlaneIsometries.linearMatrix e 1 0 ≠ 0)
    (hy : PlaneIsometries.linearMatrix e 1 1 ≠ 0) :
    ∀ i : Fin 2, PlaneIsometries.linearMatrix e i 1 ≠ 0 := by
  intro i
  fin_cases i
  · intro hz
    change PlaneIsometries.linearMatrix e 0 1 = 0 at hz
    have horth : PlaneIsometries.linearMatrix e 0 0 * PlaneIsometries.linearMatrix e 0 1 +
        PlaneIsometries.linearMatrix e 1 0 * PlaneIsometries.linearMatrix e 1 1 = 0 := by
      simpa using PlaneIsometries.linearMatrix_column_dot e 0 1
    rw [hz, mul_zero, zero_add] at horth
    exact mul_ne_zero hx hy horth
  · exact hy

theorem hasTwoSidePoints_unique_of_top_nonaxis {P : Set Plane} {θ u v : ℝ}
    (h : SourceSupport P θ u v) (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : e '' P ⊆ unitSquare)
    (hcornerless : ∀ k : Fin 4, corner k ∉ e '' P)
    (hx : PlaneIsometries.linearMatrix e 1 0 ≠ 0)
    (hy : PlaneIsometries.linearMatrix e 1 1 ≠ 0)
    {i j : Fin 2} {upper other : Bool}
    (hi : HasTwoSidePoints (e '' P) i upper)
    (hj : HasTwoSidePoints (e '' P) j other) : i = j ∧ upper = other :=
  hasTwoSidePoints_unique h hc hs e hfit hcornerless
    (second_column_nonzero_of_top_row_nonzero e hx hy) hi hj

/-- Complete normal classification from two distinct actual supporting
points. Every nonaxis angle comes with its explicit sine/cosine coordinates. -/
theorem hasTwoSupportPoints_angle_classification {P : Set Plane} {θ u v a b : ℝ}
    (h : SourceSupport P θ u v) (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ)
    (hunit : a ^ 2 + b ^ 2 = 1) (hface : HasTwoSupportPoints P a b) :
    (a = 0 ∨ b = 0) ∨
    (∃ φ : ℝ, 0 < φ ∧ φ < θ ∧ a = Real.cos φ ∧ b = Real.sin φ) ∨
    (a = Real.cos θ ∧ b = Real.sin θ) ∨
    (a = -Real.sin θ ∧ b = Real.cos θ) ∨
    (∃ φ : ℝ, θ < φ ∧ φ < Real.pi / 2 ∧ a = -Real.sin φ ∧ b = Real.cos φ) := by
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hn
    push Not at hn
    rw [hn.1, hn.2] at hunit
    norm_num at hunit
  rcases hasTwoSupportPoints_allowed h hc hs hne hface with
    ⟨ha, _⟩ | ⟨hb, _⟩ | ⟨ha, hb, hbound⟩ | ⟨ha, hb, hbound⟩
  · exact Or.inl (Or.inl ha)
  · exact Or.inl (Or.inr hb)
  · obtain ⟨φ, hφ0, hφθ, hcos, hsin⟩ :=
      exists_prefix_angle hθ0 hθπ hunit ha hb hbound
    rcases lt_or_eq_of_le hφθ with hφθ | rfl
    · exact Or.inr (Or.inl ⟨φ, hφ0, hφθ, hcos, hsin⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hcos, hsin⟩))
  · obtain ⟨φ, hθφ, hφπ, hsin, hcos⟩ :=
      exists_suffix_angle hθ0 hθπ hunit ha hb hbound
    rcases lt_or_eq_of_le hθφ with hθφ | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨φ, hθφ, hφπ, hsin, hcos⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hsin, hcos⟩)))

end

end Puzzling139335.N4TwoOneOne.SupportContacts

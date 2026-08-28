import Wikipedia.HopfProblem.CuspCollapseCentralDeck
import Wikipedia.HopfProblem.CuspHoneycombHexagonPositiveBasic
import Wikipedia.HopfProblem.ToricRayIncidence

/-!
# The actual compact cells of the positive central fibre

These cells are the literal intersections with the toric ray divisors.
They form a locally finite closed compact cover of the actual positive
central fibre.  Their translation identifications and intersections are
inherited from the original twisted action and triangular fan.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombPositive

open ToricCharts ToricFan ToricSpace CuspPositiveRetraction CuspCollapse CuspHoneycombHexagon

/-- The literal positive central cell indexed by an integral fan vertex. -/
def positiveCell (v : Fin 2 → ℤ) : Set PositiveCentralFibre :=
  {q | (q.1 : Space) ∈ rayDivisor v}

@[simp] theorem mem_positiveCell (v : Fin 2 → ℤ) (q : PositiveCentralFibre) :
    q ∈ positiveCell v ↔ (q.1 : Space) ∈ rayDivisor v := Iff.rfl

theorem positiveCell_isClosed (v : Fin 2 → ℤ) : IsClosed (positiveCell v) :=
  (rayDivisor_isClosed v).preimage (continuous_subtype_val.comp continuous_subtype_val)

theorem positiveCells_locallyFinite : LocallyFinite positiveCell :=
  rayDivisors_locallyFinite.preimage_continuous
    (continuous_subtype_val.comp continuous_subtype_val)

theorem iUnion_positiveCell : (⋃ v : Fin 2 → ℤ, positiveCell v) = univ := by
  apply Set.eq_univ_of_forall
  intro q
  have hq : (q.1 : Space) ∈ time ⁻¹' {0} := q.2
  rw [central_fibre_eq_rayDivisors] at hq
  obtain ⟨v, hv⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨v, hv⟩

/-- The two literal descriptions differ only in the order of their
subtype predicates; centrality follows from membership in the ray divisor. -/
def positiveCellComponentHomeomorph (v : Fin 2 → ℤ) :
    positiveCell v ≃ₜ PositiveComponent v where
  toFun q := ⟨⟨q.1.1.1, q.2⟩, q.1.1.2⟩
  invFun x := ⟨⟨⟨x.1.1, x.2⟩, time_eq_zero_of_mem_rayDivisor x.1.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

@[simp] theorem positiveCellComponentHomeomorph_coe (v : Fin 2 → ℤ) (q : positiveCell v) :
    ((positiveCellComponentHomeomorph v q).1 : Space) = (q.1.1 : Space) := rfl

@[simp] theorem positiveCellComponentHomeomorph_symm_coe (v : Fin 2 → ℤ)
    (x : PositiveComponent v) :
    (((positiveCellComponentHomeomorph v).symm x).1.1 : Space) = (x.1 : Space) := rfl

/-- In particular the zero cell is the existing actual positive component `E₀`. -/
abbrev positiveCellZeroHomeomorph : positiveCell 0 ≃ₜ PositiveE0 :=
  positiveCellComponentHomeomorph 0

instance positiveCell_compactSpace (v : Fin 2 → ℤ) : CompactSpace (positiveCell v) :=
  (positiveCellComponentHomeomorph v).symm.compactSpace

theorem positiveCell_isCompact (v : Fin 2 → ℤ) : IsCompact (positiveCell v) :=
  isCompact_iff_compactSpace.mpr inferInstance

/-- The actual positive action translates the component labels by `cuspVector`. -/
theorem positiveCentralTranslate_mem_positiveCell (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u v : Fin 2 → ℤ) (q : PositiveCentralFibre) :
    positiveCentralTranslate C₀ u q ∈ positiveCell v ↔
      q ∈ positiveCell (v - cuspVector u) :=
  twistedTranslate_mem_rayDivisor (CuspPositive.positiveTwist C₀) u v (q.1 : Space)

theorem positiveCentralHomeomorph_preimage_positiveCell (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u v : Fin 2 → ℤ) :
    positiveCentralHomeomorph C₀ u ⁻¹' positiveCell v = positiveCell (v - cuspVector u) :=
  Set.ext (positiveCentralTranslate_mem_positiveCell C₀ u v)

theorem positiveCentralHomeomorph_image_positiveCell (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u v : Fin 2 → ℤ) :
    positiveCentralHomeomorph C₀ u '' positiveCell v = positiveCell (v + cuspVector u) := by
  rw [Homeomorph.image_eq_preimage_symm]
  ext q
  change positiveCentralTranslate C₀ (-u) q ∈ positiveCell v ↔
    q ∈ positiveCell (v + cuspVector u)
  rw [positiveCentralTranslate_mem_positiveCell, cuspVector_neg, sub_neg_eq_add]

/-- Translation gives a homeomorphism between the actual translated cells. -/
def positiveCellTranslationHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u v : Fin 2 → ℤ) : positiveCell v ≃ₜ positiveCell (v + cuspVector u) :=
  (positiveCentralHomeomorph C₀ u).subtype (fun q => by
    change q ∈ positiveCell v ↔
      positiveCentralTranslate C₀ u q ∈ positiveCell (v + cuspVector u)
    rw [positiveCentralTranslate_mem_positiveCell, add_sub_cancel_right])

@[simp] theorem positiveCellTranslationHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u v : Fin 2 → ℤ) (q : positiveCell v) :
    (positiveCellTranslationHomeomorph C₀ u v q : PositiveCentralFibre) =
      positiveCentralTranslate C₀ u q.1 := rfl

theorem positiveCentralHomeomorph_image_zeroCell (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) :
    positiveCentralHomeomorph C₀ (-cuspVector v) '' positiveCell 0 = positiveCell v := by
  rw [positiveCentralHomeomorph_image_positiveCell, cuspVector_neg, cuspVector_cuspVector,
    neg_neg, zero_add]

/-- Every actual positive cell is the zero component translated by the
prescribed positive action; the sign compensates for `cuspVector² = -id`. -/
def positiveE0CellHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    PositiveE0 ≃ₜ positiveCell v :=
  positiveCellZeroHomeomorph.symm.trans
    ((positiveCentralHomeomorph C₀ (-cuspVector v)).subtype (fun q => by
      change q ∈ positiveCell 0 ↔ positiveCentralTranslate C₀ (-cuspVector v) q ∈ positiveCell v
      rw [positiveCentralTranslate_mem_positiveCell, cuspVector_neg, cuspVector_cuspVector,
        neg_neg, sub_self]))

@[simp] theorem positiveE0CellHomeomorph_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : PositiveE0) :
    ((positiveE0CellHomeomorph C₀ v x).1.1 : Space) =
      twistedTranslate (CuspPositive.positiveTwist C₀) (-cuspVector v) (x.1 : Space) := rfl

theorem positiveCell_nonempty (v : Fin 2 → ℤ) : (positiveCell v).Nonempty := by
  obtain ⟨x, hx⟩ := rayDivisor_nonempty v
  have hm : modulus x ∈ rayDivisor v := (modulus_mem_rayDivisor_iff v x).mpr hx
  exact ⟨⟨⟨modulus x, modulus_mem_positivePart x⟩, time_eq_zero_of_mem_rayDivisor hm⟩, hm⟩

theorem positiveCell_inter_nonempty_iff_rayDivisors (v w : Fin 2 → ℤ) :
    (positiveCell v ∩ positiveCell w).Nonempty ↔ (rayDivisor v ∩ rayDivisor w).Nonempty := by
  constructor
  · rintro ⟨q, hqv, hqw⟩
    exact ⟨(q.1 : Space), hqv, hqw⟩
  · rintro ⟨x, hxv, hxw⟩
    have hmv : modulus x ∈ rayDivisor v := (modulus_mem_rayDivisor_iff v x).mpr hxv
    have hmw : modulus x ∈ rayDivisor w := (modulus_mem_rayDivisor_iff w x).mpr hxw
    exact ⟨⟨⟨modulus x, modulus_mem_positivePart x⟩,
      time_eq_zero_of_mem_rayDivisor hmv⟩, hmv, hmw⟩

/-- Two literal positive cells meet precisely for equal or adjacent fan vertices. -/
theorem positiveCell_inter_nonempty_iff (v w : Fin 2 → ℤ) :
    (positiveCell v ∩ positiveCell w).Nonempty ↔ v = w ∨ AreAdjacent v w := by
  by_cases hvw : v = w
  · subst w
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      simpa only [inter_self] using positiveCell_nonempty v
  · rw [positiveCell_inter_nonempty_iff_rayDivisors, rayDivisor_inter_nonempty_iff v w hvw]
    simp only [hvw, false_or]

end Wikipedia.HopfProblem.CuspHoneycombPositive

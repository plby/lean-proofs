import Wikipedia.HopfProblem.CuspRetractionRadius
import Wikipedia.HopfProblem.CuspHoneycombHexagonGluing

/-!
# Literal fixed-level quotients and continuous descent

The fixed-time subspace of the original closed cusp quotient is the open
quotient of the corresponding literal toric level. Its fibres are exactly
the original twisted lattice orbits. A continuous invariant map on that
toric level therefore gives a continuous map on the original quotient
level, with an exact formula on every representative.
-/

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricCharts ToricSpace CuspQuotient CuspRetraction
open CuspHoneycombHexagon.CommonFibres

/-- The literal fixed-time subspace of the actual closed toric tube. -/
abbrev ToricLevel (η : ℝ) (t : ℂ) :=
  {x : ClosedTube η // time (x : Space) = t}

/-- The literal fixed-time subspace of the original closed cusp quotient. -/
abbrev QuotientLevel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r η : ℝ) (t : ℂ) :=
  {q : ClosedQuotient C r η // projection C r q = t}

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r η : ℝ}

/-- The actual closed-tube quotient map restricted to a fixed time. -/
noncomputable def levelProjection (hηr : η < r) (t : ℂ) (x : ToricLevel η t) :
    QuotientLevel C r η t :=
  ⟨closedQuotientMap C hηr x.1, x.2⟩

theorem levelProjection_coe (hηr : η < r) (t : ℂ) (x : ToricLevel η t) :
    (levelProjection C hηr t x : ClosedQuotient C r η) =
      closedQuotientMap C hηr x.1 := rfl

theorem levelProjection_surjective (hηr : η < r) (t : ℂ) :
    Function.Surjective (levelProjection C hηr t) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := closedQuotientMap_surjective C hηr q
  exact ⟨⟨x, hq⟩, rfl⟩

theorem levelProjection_continuous (hηr : η < r) (t : ℂ) :
    Continuous (levelProjection C hηr t) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (quotientMap_continuous C r).comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

/-- Restriction to the exact level preimage preserves the open quotient
property, including at time zero and for empty levels. -/
theorem levelProjection_isOpenQuotientMap (hηr : η < r) (t : ℂ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    IsOpenQuotientMap (levelProjection C hηr t) :=
  (closedQuotientMap_isOpenQuotientMap C hηr hC).restrictPreimage
    {q : ClosedQuotient C r η | projection C r q = t}

theorem levelProjection_isQuotientMap (hηr : η < r) (t : ℂ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    IsQuotientMap (levelProjection C hηr t) :=
  (levelProjection_isOpenQuotientMap C hηr t hC).isQuotientMap

/-- The original closed-tube translation, restricted to its invariant time level. -/
noncomputable def levelTranslate (η : ℝ) (t : ℂ) (v : Fin 2 → ℤ)
    (x : ToricLevel η t) : ToricLevel η t :=
  ⟨closedTranslate C η v x.1, by
    change time (twistedTranslate C v (x.1 : Space)) = t
    rw [time_twistedTranslate]
    exact x.2⟩

theorem levelTranslate_coe (η : ℝ) (t : ℂ) (v : Fin 2 → ℤ) (x : ToricLevel η t) :
    (levelTranslate C η t v x : ClosedTube η) = closedTranslate C η v x.1 := rfl

/-- The exact fixed-level orbit relation in the original closed toric tube. -/
theorem levelProjection_eq_iff (hηr : η < r) (t : ℂ) (x y : ToricLevel η t) :
    levelProjection C hηr t x = levelProjection C hηr t y ↔
      ∃ v : Fin 2 → ℤ, closedTranslate C η v y.1 = x.1 := by
  constructor
  · intro hxy
    have hq := congrArg (fun q : QuotientLevel C r η t => (q : ClosedQuotient C r η)) hxy
    obtain ⟨v, hv⟩ := (closedQuotientMap_eq_iff C hηr x.1 y.1).mp hq
    exact ⟨v, Subtype.ext hv⟩
  · rintro ⟨v, hv⟩
    apply Subtype.ext
    apply (closedQuotientMap_eq_iff C hηr x.1 y.1).mpr
    exact ⟨v, congrArg (fun z : ClosedTube η => (z : Space)) hv⟩

theorem levelProjection_eq_iff_levelTranslate (hηr : η < r) (t : ℂ)
    (x y : ToricLevel η t) :
    levelProjection C hηr t x = levelProjection C hηr t y ↔
      ∃ v : Fin 2 → ℤ, levelTranslate C η t v y = x := by
  constructor
  · intro hxy
    obtain ⟨v, hv⟩ := (levelProjection_eq_iff C hηr t x y).mp hxy
    exact ⟨v, Subtype.ext hv⟩
  · rintro ⟨v, hv⟩
    apply (levelProjection_eq_iff C hηr t x y).mpr
    exact ⟨v, congrArg (fun z : ToricLevel η t => (z : ClosedTube η)) hv⟩

theorem levelProjection_translate (hηr : η < r) (t : ℂ)
    (v : Fin 2 → ℤ) (x : ToricLevel η t) :
    levelProjection C hηr t (levelTranslate C η t v x) = levelProjection C hηr t x :=
  (levelProjection_eq_iff_levelTranslate C hηr t _ x).mpr ⟨v, rfl⟩

variable {Z : Type*}

/-- Invariance under the actual translations implies constancy on the
fibres of the actual fixed-level projection. -/
theorem levelProjection_fibre_compatible_of_invariant (hηr : η < r) (t : ℂ)
    (f : ToricLevel η t → Z)
    (hinv : ∀ (v : Fin 2 → ℤ) (x : ToricLevel η t), f (levelTranslate C η t v x) = f x) :
    ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y := by
  intro x y hxy
  obtain ⟨v, hv⟩ := (levelProjection_eq_iff_levelTranslate C hηr t x y).mp hxy
  rw [← hv]
  exact hinv v y

/-- Descend a supplied representative formula through the literal level
projection. The fibre-compatibility lemmas below remove dependence on choice. -/
noncomputable def levelDescend (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z) :
    QuotientLevel C r η t → Z :=
  descend (levelProjection C hηr t) f (levelProjection_surjective C hηr t)

theorem levelDescend_levelProjection (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z)
    (hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y)
    (x : ToricLevel η t) : levelDescend C hηr t f (levelProjection C hηr t x) = f x :=
  descend_apply (levelProjection C hηr t) f (levelProjection_surjective C hηr t) hcompat x

theorem levelDescend_levelProjection_of_invariant (hηr : η < r) (t : ℂ)
    (f : ToricLevel η t → Z)
    (hinv : ∀ (v : Fin 2 → ℤ) (x : ToricLevel η t), f (levelTranslate C η t v x) = f x)
    (x : ToricLevel η t) : levelDescend C hηr t f (levelProjection C hηr t x) = f x :=
  levelDescend_levelProjection C hηr t f
    (levelProjection_fibre_compatible_of_invariant C hηr t f hinv) x

theorem levelDescend_unique (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z)
    (hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y)
    (g : QuotientLevel C r η t → Z)
    (hg : ∀ x, g (levelProjection C hηr t x) = f x) : g = levelDescend C hηr t f := by
  funext q
  obtain ⟨x, rfl⟩ := levelProjection_surjective C hηr t q
  rw [hg, levelDescend_levelProjection C hηr t f hcompat]

variable [TopologicalSpace Z]

/-- The descended representative formula is continuous for the original
fixed-level quotient topology. -/
theorem levelDescend_continuous (hηr : η < r) (t : ℂ) (f : ToricLevel η t → Z)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hf : Continuous f)
    (hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y) :
    Continuous (levelDescend C hηr t f) :=
  descend_continuous (levelProjection C hηr t) f (levelProjection_surjective C hηr t)
    (levelProjection_isQuotientMap C hηr t hC) hf hcompat

theorem levelDescend_continuous_of_invariant (hηr : η < r) (t : ℂ)
    (f : ToricLevel η t → Z)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hf : Continuous f)
    (hinv : ∀ (v : Fin 2 → ℤ) (x : ToricLevel η t), f (levelTranslate C η t v x) = f x) :
    Continuous (levelDescend C hηr t f) :=
  levelDescend_continuous C hηr t f hC hf
    (levelProjection_fibre_compatible_of_invariant C hηr t f hinv)

/-- Bundled descent of an actual continuous representative formula. -/
noncomputable def levelDescendMap (hηr : η < r) (t : ℂ) (f : C(ToricLevel η t, Z))
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hcompat : ∀ x y, levelProjection C hηr t x = levelProjection C hηr t y → f x = f y) :
    C(QuotientLevel C r η t, Z) :=
  ⟨levelDescend C hηr t f, levelDescend_continuous C hηr t f hC f.continuous hcompat⟩

end Wikipedia.HopfProblem.CuspControlledRetraction

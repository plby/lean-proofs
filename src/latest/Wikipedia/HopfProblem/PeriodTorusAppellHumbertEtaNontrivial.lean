import Wikipedia.HopfProblem.PeriodTorusAppellHumbertEtaBundles
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreTrivialization

/-!
# Exact analytic triviality of the distinguished bundle family

The zero multiple has an explicit nowhere-zero holomorphic section and
therefore a genuine analytic fibre-linear product trivialization. Every
nonzero multiple has no such trivialization, since its pulled-back unit
section would contradict the proved vanishing of all actual holomorphic
sections. This is a statement about the constructed bundle family, not
an identification with the Picard or Néron--Severi group.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

/-- The actual constant unit section in the zero-factor bundle charts. -/
def etaZeroSection (p : PeriodDomain) : Core.HolomorphicSection (etaFactor p 0) :=
  (Core.data (etaFactor p 0)).holomorphicSectionFromLocal
    (modelWithCornersSelf ℂ ComplexPlane₂) (fun _ _ => (1 : ℂ))
    (by
      intro i j b hb
      change ((etaFactor p 0).factor (Core.deck p i j b) (Core.lift p i b) : ℂ) * 1 = 1
      rw [etaFactor_power]
      simp)
    (fun _ => contMDiffOn_const)

@[simp] theorem etaZeroSection_apply (p : PeriodDomain) (b : p.Torus) :
    id (α := ℂ) (etaZeroSection p b) = 1 := rfl

/-- The zero multiple is trivialized by an actual analytic fibre-linear diffeomorphism. -/
def etaZeroTrivialization (p : PeriodDomain) :
    (Core.data (etaFactor p 0)).AnalyticTrivialization
      (modelWithCornersSelf ℂ ComplexPlane₂) :=
  (Core.data (etaFactor p 0)).analyticTrivializationOfSection
    (etaZeroSection p) (modelWithCornersSelf ℂ ComplexPlane₂)
    (etaZeroSection p).contMDiff (fun _ => by
      change (1 : ℂ) ≠ 0
      exact one_ne_zero)

theorem etaBundle_not_analyticallyTrivial (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0) :
    ¬ Nonempty ((Core.data (etaFactor p n)).AnalyticTrivialization
      (modelWithCornersSelf ℂ ComplexPlane₂)) := by
  rintro ⟨e⟩
  let s : Core.HolomorphicSection (etaFactor p n) := ⟨e.frame, e.frame_holomorphic⟩
  have hs := etaBundleSection_eq_zero p n hn s
  have h0 := congrArg (fun t : Core.HolomorphicSection (etaFactor p n) => t (0 : p.Torus)) hs
  exact e.frame_ne_zero (0 : p.Torus) h0

/-- In this actual family, analytic bundle triviality occurs exactly at the zero integer. -/
theorem etaBundle_analyticallyTrivial_iff (p : PeriodDomain) (n : ℤ) :
    Nonempty ((Core.data (etaFactor p n)).AnalyticTrivialization
      (modelWithCornersSelf ℂ ComplexPlane₂)) ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    exact etaBundle_not_analyticallyTrivial p n hn h
  · rintro rfl
    exact ⟨etaZeroTrivialization p⟩

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert

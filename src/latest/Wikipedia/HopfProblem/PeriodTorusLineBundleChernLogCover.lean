import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreIdentification
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCanonical

/-!
# Logarithmic lifts of the actual nonzero bundle vectors

Exponentiating the last coordinate maps the covering vector space into
the actual native Appell--Humbert bundle.  Its image is exactly the
nonzero vectors.  The lifted lattice transformations preserve this map,
and their failure to compose is the negative of the proved integer
logarithmic defect.  These are statements about the actual bundle maps,
not an assigned cohomology class or a Chern-class comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassification
open PeriodTorusTypeOneOne Bundle
open scoped ContDiff

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- Exponentiating a genuine fibre coordinate in the actual diagonal quotient bundle. -/
def logCoverMap (u : ComplexPlane₂ × ℂ) : (Core.data F).core.TotalSpace :=
  Core.fromAssociated F (associatedMap F (u.1, Complex.exp u.2))

@[simp] theorem logCoverMap_proj (u : ComplexPlane₂ × ℂ) :
    (logCoverMap F u).proj = p.lattice.mkQ u.1 := rfl

theorem logCoverMap_toAssociated (u : ComplexPlane₂ × ℂ) :
    Core.toAssociated F (logCoverMap F u) = associatedMap F (u.1, Complex.exp u.2) :=
  Core.toAssociated_fromAssociated F _

/-- The map is holomorphic in the original native bundle atlas. -/
theorem logCoverMap_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ))
      ((modelWithCornersSelf ℂ ComplexPlane₂).prod (modelWithCornersSelf ℂ ℂ)) ω
      (logCoverMap F) := by
  have he : ContDiff ℂ ω (fun u : ComplexPlane₂ × ℂ => (u.1, Complex.exp u.2)) :=
    contDiff_fst.prodMk (Complex.contDiff_exp.comp contDiff_snd)
  exact (Core.fromAssociated_comp_holomorphic F).comp he.contMDiff

/-- Every vector constructed by this actual exponential map is nonzero. -/
theorem logCoverMap_ne_zero (u : ComplexPlane₂ × ℂ) : (logCoverMap F u).2 ≠ 0 := by
  intro hz
  have he := logCoverMap_toAssociated F u
  dsimp only [Core.toAssociated] at he
  rw [hz] at he
  obtain ⟨l, _, hl⟩ := (associatedMap_eq_iff F _ _).mp he.symm
  change _ * (0 : ℂ) = Complex.exp u.2 at hl
  have h0 : Complex.exp u.2 = 0 := by simpa only [mul_zero] using hl.symm
  exact Complex.exp_ne_zero u.2 h0

/-- Every actual nonzero native vector has a logarithmic lift. -/
theorem logCoverMap_surjective_nonzero (v : (Core.data F).core.TotalSpace) (hv : v.2 ≠ 0) :
    ∃ u : ComplexPlane₂ × ℂ, logCoverMap F u = v := by
  refine ⟨(Core.lift p v.proj v.proj, Complex.log (id (α := ℂ) v.2)), ?_⟩
  apply Core.toAssociated_injective F
  rw [logCoverMap_toAssociated]
  change associatedMap F (Core.lift p v.proj v.proj,
    Complex.exp (Complex.log (id (α := ℂ) v.2))) = Core.toAssociated F v
  rw [Complex.exp_log (show id (α := ℂ) v.2 ≠ 0 from hv)]
  rfl

/-- The actual logarithmic lift of positive lattice translation. -/
def logDeck (l : p.lattice) (u : ComplexPlane₂ × ℂ) : ComplexPlane₂ × ℂ :=
  (u.1 + l, u.2 + factorLog F l u.1)

theorem logDeck_holomorphic (l : p.lattice) : ContDiff ℂ ω (logDeck F l) :=
  (contDiff_fst.add contDiff_const).prodMk
    (contDiff_snd.add ((factorLog_holomorphic F l).comp contDiff_fst))

@[simp] theorem logDeck_zero (u : ComplexPlane₂ × ℂ) : logDeck F 0 u = u := by
  simp [logDeck]

/-- The lifted transformation preserves the actual native exponential projection. -/
theorem logCoverMap_logDeck (l : p.lattice) (u : ComplexPlane₂ × ℂ) :
    logCoverMap F (logDeck F l u) = logCoverMap F u := by
  apply Core.toAssociated_injective F
  rw [logCoverMap_toAssociated, logCoverMap_toAssociated]
  change associatedMap F (u.1 + l, Complex.exp (u.2 + factorLog F l u.1)) = _
  rw [Complex.exp_add, factorLog_exp, mul_comm (Complex.exp u.2)]
  exact associatedMap_diagonal F l (u.1, Complex.exp u.2)

/-- The actual composition defect is a negative integral vertical period. -/
theorem logDeck_comp (l m : p.lattice) (u : ComplexPlane₂ × ℂ) :
    logDeck F l (logDeck F m u) =
      (u.1 + (l + m : p.lattice),
        u.2 + factorLog F (l + m) u.1 -
          (factorLogIntegerCocycle F l m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
  apply Prod.ext
  · simp only [logDeck, Submodule.coe_add]
    abel
  · dsimp only [logDeck]
    have h := factorLog_add F l m u.1
    linear_combination -h

/-- The difference of the two lifted orders has the sign forced by actual composition. -/
theorem logDeck_commutator_coordinate (l m : p.lattice) (u : ComplexPlane₂ × ℂ) :
    (logDeck F l (logDeck F m u)).2 - (logDeck F m (logDeck F l u)).2 =
      -(factorLogAlternatingForm F l m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [logDeck_comp, logDeck_comp]
  simp only [factorLogAlternatingForm_apply, Int.cast_sub]
  rw [add_comm m l]
  ring

/-- Canonical factors have the negative original alternating period in this actual
lifted commutator. -/
theorem canonical_logDeck_commutator_coordinate (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l m : p.lattice) (u : ComplexPlane₂ × ℂ) :
    (logDeck (integralFactor p E hType) l (logDeck (integralFactor p E hType) m u)).2 -
      (logDeck (integralFactor p E hType) m (logDeck (integralFactor p E hType) l u)).2 =
      -(coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [logDeck_commutator_coordinate, canonicalFactorLogAlternatingForm_apply]

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

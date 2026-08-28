import Wikipedia.HopfProblem.PeriodTorusAppellHumbertSectionsAnalytic
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertFactorMultiplicativity
import Wikipedia.HopfProblem.PeriodTorusThetaSpecial

/-!
# Vanishing of actual holomorphic sections for the distinguished multiples

Each integer multiple of `η` gives a constructed factor of automorphy,
and therefore an actual orbit quotient. Pulling an actual holomorphic
section back to the covering vector space gives an entire theta
function with exactly the canonical Appell--Humbert transformation law.
The proved analytic obstruction makes that section zero when the
integer is nonzero. No classification of arbitrary line bundles is used.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

open PeriodTorusTypeOneOne SpecialPeriods

/-- The canonical genuine factor for the integer multiple `nη`. -/
def etaFactor (p : PeriodDomain) (n : ℤ) : FactorOfAutomorphy p :=
  integralFactor p (n • periodRelationEta) (etaMultipleTangent_isTypeOneOne p n)

theorem integralHermitian_eta (p : PeriodDomain) (n : ℤ) :
    integralHermitian p (n • periodRelationEta) (etaMultipleTangent_isTypeOneOne p n) =
      etaMultipleHermitian p n := rfl

/-- Integer multiples give literal integer powers of the actual nonzero factors. -/
theorem etaFactor_power (p : PeriodDomain) (n : ℤ) (l : p.lattice) (z : ComplexPlane₂) :
    (etaFactor p n).factor l z =
      ((integralFactor p periodRelationEta (etaTangent_isTypeOneOne p)).factor l z) ^ n :=
  integralFactor_zsmul p n periodRelationEta (etaTangent_isTypeOneOne p) l z

/-- The precise theta law obtained from the actual section pullback. -/
theorem etaFactor_automorphy_iff (p : PeriodDomain) (n : ℤ) (θ : ComplexPlane₂ → ℂ) :
    IsAutomorphic (etaFactor p n) θ ↔
      PeriodTorusTheta.AppellHumbertAutomorphy p (etaMultipleHermitian p n)
        (latticeSemicharacter p (n • periodRelationEta)) θ := by
  simpa only [IsAutomorphic, etaFactor, integralHermitian_eta] using
    integralFactor_automorphy_iff p (n • periodRelationEta)
      (etaMultipleTangent_isTypeOneOne p n) θ

/-- Every actual holomorphic section of a nonzero distinguished multiple is zero. -/
theorem etaSection_eq_zero (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0)
    (s : Section (etaFactor p n)) (hs : s.IsHolomorphic (etaFactor p n)) :
    s = zeroSection (etaFactor p n) := by
  apply (s.eq_zero_iff_pullback (etaFactor p n)).mpr
  apply PeriodTorusTheta.theta_eta_multiple_eq_zero p n hn
    (latticeSemicharacter p (n • periodRelationEta))
    (latticeSemicharacter_norm p (n • periodRelationEta))
    (s.pullback (etaFactor p n))
    ((s.pullback_contDiff (etaFactor p n) hs).differentiable (by simp))
  exact (etaFactor_automorphy_iff p n _).mp (s.pullback_automorphic (etaFactor p n))

/-- The vanishing statement refers to actual holomorphic quotient sections. -/
theorem not_exists_nonzero_etaSection (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0) :
    ¬ ∃ s : Section (etaFactor p n),
      s.IsHolomorphic (etaFactor p n) ∧ s ≠ zeroSection (etaFactor p n) := by
  rintro ⟨s, hs, hne⟩
  exact hne (etaSection_eq_zero p n hn s hs)

theorem etaHolomorphicSections_subsingleton (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0) :
    Subsingleton {s : Section (etaFactor p n) // s.IsHolomorphic (etaFactor p n)} := by
  constructor
  intro s t
  apply Subtype.ext
  exact (etaSection_eq_zero p n hn s.val s.property).trans
    (etaSection_eq_zero p n hn t.val t.property).symm

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert

import Wikipedia.HopfProblem.CuspNormalizationGermsBasicDomain
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Actual representatives of integral relations between analytic germs

The ring of functions analytic at a point surjects onto the ring of actual
analytic germs.  Consequently a monic relation between germs can be lifted
to a genuinely monic polynomial whose coefficients are analytic functions.
Clearing a nonzero germ denominator then gives a polynomial identity on a
neighbourhood.  No integral-closedness assertion is used here.
-/

noncomputable section

open Set Filter Topology Polynomial

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual functions analytic at a point form a ring before taking
neighbourhood germs. -/
def analyticFunctionSubring (a : E) : Subring (E → ℂ) where
  carrier := {f | AnalyticAt ℂ f a}
  zero_mem' := analyticAt_const
  one_mem' := analyticAt_const
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  neg_mem' hf := hf.neg

/-- Taking the actual neighbourhood germ of an analytic function. -/
def analyticFunctionToGerm (a : E) :
    analyticFunctionSubring a →+* AnalyticGerm a where
  toFun f := ofAnalytic (f : E → ℂ) f.property
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem analyticFunctionToGerm_apply (a : E)
    (f : analyticFunctionSubring a) :
    analyticFunctionToGerm a f = ofAnalytic (f : E → ℂ) f.property := rfl

theorem analyticFunctionToGerm_surjective (a : E) :
    Function.Surjective (analyticFunctionToGerm a) := by
  intro φ
  obtain ⟨f, hf, hφ⟩ := exists_representative φ
  exact ⟨⟨f, hf⟩, hφ⟩

/-- Vanishing after taking germs is actual vanishing on a neighbourhood. -/
theorem analyticFunctionToGerm_eq_zero_iff {a : E}
    (f : analyticFunctionSubring a) :
    analyticFunctionToGerm a f = 0 ↔
      (f : E → ℂ) =ᶠ[𝓝 a] 0 :=
  ofAnalytic_eq_zero_iff (f : E → ℂ) f.property

/-- Evaluation of an actual analytic representative at any point.  The
representative is required to be analytic only at the fixed basepoint. -/
def analyticFunctionEval (a z : E) : analyticFunctionSubring a →+* ℂ :=
  (Pi.evalRingHom (fun _ : E => ℂ) z).comp (analyticFunctionSubring a).subtype

@[simp] theorem analyticFunctionEval_apply (a z : E)
    (f : analyticFunctionSubring a) :
    analyticFunctionEval a z f = (f : E → ℂ) z := rfl

/-- A monic polynomial in analytic germs has a monic lift with actual
analytic-function coefficients, and with the same degree. -/
theorem exists_monic_analytic_polynomial_lift {a : E}
    (p : Polynomial (AnalyticGerm a)) (hp : p.Monic) :
    ∃ q : Polynomial (analyticFunctionSubring a),
      q.map (analyticFunctionToGerm a) = p ∧
      q.natDegree = p.natDegree ∧ q.Monic :=
  Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (analyticFunctionToGerm a)
      (analyticFunctionToGerm_surjective a) p) hp

/-- The monic relation for an integral fraction, with its denominator
cleared inside the original domain. -/
theorem exists_monic_scaleRoots_eval_eq_zero
    {R : Type*} [CommRing R] [IsDomain R] {r s : R} (hs : s ≠ 0)
    (hint : IsIntegral R
      (algebraMap R (FractionRing R) r / algebraMap R (FractionRing R) s)) :
    ∃ p : Polynomial R, p.Monic ∧ (p.scaleRoots s).eval r = 0 := by
  obtain ⟨p, hp, hroot⟩ := hint
  refine ⟨p, hp, ?_⟩
  apply IsFractionRing.injective R (FractionRing R)
  rw [map_zero]
  rw [← Polynomial.eval₂_at_apply]
  exact Polynomial.scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero
    (IsFractionRing.injective R (FractionRing R)) hroot
    (mem_nonZeroDivisors_iff_ne_zero.mpr hs)

/-- Lifting a cleared polynomial relation produces an actual identity on
a neighbourhood of the basepoint. -/
theorem eventually_lifted_scaleRoots_eval_eq_zero {a : E}
    (f g : analyticFunctionSubring a)
    (q : Polynomial (analyticFunctionSubring a)) (hq : q.Monic)
    (hzero : ((q.map (analyticFunctionToGerm a)).scaleRoots
        (analyticFunctionToGerm a g)).eval (analyticFunctionToGerm a f) = 0) :
    ∀ᶠ z in 𝓝 a,
      (((q.map (analyticFunctionEval a z)).scaleRoots ((g : E → ℂ) z)).eval
        ((f : E → ℂ) z)) = 0 := by
  have hcleared : analyticFunctionToGerm a ((q.scaleRoots g).eval f) = 0 := by
    rw [← Polynomial.eval_map_apply]
    rw [Polynomial.map_scaleRoots q g (analyticFunctionToGerm a) (by
      rw [hq, map_one]
      exact one_ne_zero)]
    exact hzero
  have hevent := (analyticFunctionToGerm_eq_zero_iff ((q.scaleRoots g).eval f)).mp hcleared
  filter_upwards [hevent] with z hz
  change analyticFunctionEval a z ((q.scaleRoots g).eval f) = 0 at hz
  rw [← Polynomial.eval_map_apply] at hz
  rw [Polynomial.map_scaleRoots q g (analyticFunctionEval a z) (by
    rw [hq, map_one]
    exact one_ne_zero)] at hz
  exact hz

/-- A zero of a cleared polynomial yields a zero of the original polynomial
where the actual complex denominator does not vanish. -/
theorem isRoot_div_of_scaleRoots_eval_eq_zero
    (p : Polynomial ℂ) {f g : ℂ} (hg : g ≠ 0)
    (hzero : (p.scaleRoots g).eval f = 0) : p.IsRoot (f / g) := by
  have heq := Polynomial.scaleRoots_eval_mul p (f / g) g
  rw [mul_div_cancel₀ f hg, hzero] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hg)

/-- An integral fraction of actual analytic germs satisfies a genuinely
monic analytic-function relation on a common neighbourhood, away from
the zero set of its actual denominator. -/
theorem exists_monic_eventually_isRoot_div {a : E} {f g : E → ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hgerm : ofAnalytic g hg ≠ 0)
    (hint : IsIntegral (AnalyticGerm a)
      (algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic f hf) /
        algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic g hg))) :
    ∃ q : Polynomial (analyticFunctionSubring a), q.Monic ∧
      ∀ᶠ z in 𝓝 a, g z ≠ 0 →
        (q.map (analyticFunctionEval a z)).IsRoot (f z / g z) := by
  obtain ⟨p, hp, hzero⟩ := exists_monic_scaleRoots_eval_eq_zero hgerm hint
  obtain ⟨q, hmap, _, hq⟩ := exists_monic_analytic_polynomial_lift p hp
  have hevent := eventually_lifted_scaleRoots_eval_eq_zero
    (⟨f, hf⟩ : analyticFunctionSubring a) (⟨g, hg⟩ : analyticFunctionSubring a) q hq
    (by rw [hmap]; exact hzero)
  refine ⟨q, hq, ?_⟩
  filter_upwards [hevent] with z hz hgz
  exact isRoot_div_of_scaleRoots_eval_eq_zero _ hgz hz

end Wikipedia.HopfProblem.CuspNormalization.Germs

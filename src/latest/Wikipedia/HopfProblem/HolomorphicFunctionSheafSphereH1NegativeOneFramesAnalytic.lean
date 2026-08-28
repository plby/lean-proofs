import Wikipedia.HopfProblem.HolomorphicCousinDivision
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.RingTheory.Ideal.Maps

/-!
# Local analytic division by the coordinate

The divided difference of a holomorphic function is holomorphic on any
open subset of the complex plane, whether or not that subset contains
zero.  Multiplication by the coordinate is injective on such functions:
ordinary cancellation works off zero, and continuity gives the value at
zero.  These local statements apply to arbitrary reciprocal-chart opens.

As a global consequence, multiplication by the coordinate identifies the
ring of entire holomorphic functions, as a module over itself, with the
actual kernel of evaluation at zero.  Its inverse is the analytic divided
difference, not a formal quotient or an assumed trivialization.
-/

noncomputable section

open Set Filter Topology Complex
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- Analytic coordinate division on an arbitrary actual open set.  If
zero is absent, the same divided difference is holomorphic there without
any assumption on the value of the original function at zero. -/
theorem analyticOnNhd_dslope_open {s : Set ℂ} {f : ℂ → ℂ}
    (hs : IsOpen s) (hf : AnalyticOnNhd ℂ f s) :
    AnalyticOnNhd ℂ (dslope f 0) s := by
  apply (analyticOnNhd_iff_differentiableOn hs).mpr
  by_cases h0 : (0 : ℂ) ∈ s
  · exact (differentiableOn_dslope (hs.mem_nhds h0)).mpr hf.differentiableOn
  · exact (differentiableOn_dslope_of_notMem h0).mpr hf.differentiableOn

/-- Multiplication by the coordinate is injective on holomorphic
functions on every open subset, including at the coordinate origin. -/
theorem coordinate_mul_injective_on {s : Set ℂ} {f g : ℂ → ℂ}
    (hs : IsOpen s) (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s)
    (he : ∀ z ∈ s, z * f z = z * g z) : ∀ z ∈ s, f z = g z := by
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    have hfg : f =ᶠ[𝓝[≠] (0 : ℂ)] g := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (hs.mem_nhds hz)] with z hz0 hzs
      exact mul_left_cancel₀ (show z ≠ 0 from hz0) (he z hzs)
    exact tendsto_nhds_unique_of_eventuallyEq
      ((hf 0 hz).continuousAt.mono_left nhdsWithin_le_nhds)
      ((hg 0 hz).continuousAt.mono_left nhdsWithin_le_nhds) hfg
  · exact mul_left_cancel₀ hz0 (he z hz)

/-- The ring of actual entire holomorphic functions. -/
abbrev Entire := ContMDiffMap 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ω

theorem entire_analytic (f : Entire) : AnalyticOnNhd ℂ (f : ℂ → ℂ) univ :=
  fun z _ => (f.contMDiff z).contDiffAt.analyticAt

/-- The actual coordinate function. -/
def coordinate : Entire := ⟨id, contMDiff_id⟩

@[simp] theorem coordinate_apply (z : ℂ) : coordinate z = z := rfl

/-- The analytic divided difference, bundled as an entire function. -/
def divideCoordinate (f : Entire) : Entire :=
  ⟨dslope f 0, by
    intro z
    have hz := (analyticOnNhd_dslope_open isOpen_univ (entire_analytic f)) z trivial
    exact hz.contDiffAt.contMDiffAt⟩

@[simp] theorem divideCoordinate_apply (f : Entire) (z : ℂ) :
    divideCoordinate f z = dslope f 0 z := rfl

/-- The exact coordinate factorization of an entire function vanishing
at zero, including equality at the removable point. -/
theorem coordinate_mul_dslope (f : Entire) (hf : f 0 = 0) :
    coordinate * divideCoordinate f = f := by
  apply ContMDiffMap.ext
  intro z
  exact HolomorphicCousin.zero_mul_dslope hf z

/-- Dividing the coordinate multiple recovers the original entire
function, with the value at zero forced by local analytic cancellation. -/
theorem dslope_coordinate_mul (f : Entire) :
    divideCoordinate (coordinate * f) = f := by
  have hf0 : (coordinate * f) 0 = 0 := by
    change 0 * f 0 = 0
    exact zero_mul _
  have he := coordinate_mul_dslope (coordinate * f) hf0
  have hc := coordinate_mul_injective_on isOpen_univ
    (entire_analytic (divideCoordinate (coordinate * f))) (entire_analytic f)
    (fun z _ => congrArg (fun g : Entire => g z) he)
  exact ContMDiffMap.ext fun z => hc z trivial

/-- The actual ideal of entire holomorphic functions vanishing at zero. -/
def coordinateIdeal : Ideal Entire :=
  RingHom.ker (ContMDiffMap.evalRingHom (0 : ℂ) : Entire →+* ℂ)

@[simp] theorem mem_coordinateIdeal (f : Entire) :
    f ∈ coordinateIdeal ↔ f 0 = 0 := Iff.rfl

/-- Multiplication by the coordinate as a linear map into the actual
vanishing ideal, over the ring of entire functions itself. -/
def coordinateIdealMap : Entire →ₗ[Entire] coordinateIdeal where
  toFun f := ⟨coordinate * f, by
    change 0 * f 0 = 0
    exact zero_mul _⟩
  map_add' f g := Subtype.ext (mul_add coordinate f g)
  map_smul' r f := by
    apply Subtype.ext
    apply ContMDiffMap.ext
    intro z
    change z * (r z * f z) = r z * (z * f z)
    ac_rfl

@[simp] theorem coordinateIdealMap_apply (f : Entire) (z : ℂ) :
    (coordinateIdealMap f : Entire) z = z * f z := rfl

/-- The vanishing ideal is genuinely free of rank one, with explicit
coordinate generator and analytic divided-difference inverse. -/
def coordinateIdealEquiv : Entire ≃ₗ[Entire] coordinateIdeal :=
  { coordinateIdealMap with
    invFun := fun f => divideCoordinate (f : Entire)
    left_inv := dslope_coordinate_mul
    right_inv := fun f => Subtype.ext
      (coordinate_mul_dslope (f : Entire) ((mem_coordinateIdeal f).mp f.property)) }

@[simp] theorem coordinateIdealEquiv_apply (f : Entire) (z : ℂ) :
    (coordinateIdealEquiv f : Entire) z = z * f z := rfl

@[simp] theorem coordinateIdealEquiv_symm_apply (f : coordinateIdeal) (z : ℂ) :
    coordinateIdealEquiv.symm f z = dslope (f : Entire) 0 z := rfl

theorem coordinateIdealMap_bijective : Function.Bijective coordinateIdealMap :=
  coordinateIdealEquiv.bijective

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

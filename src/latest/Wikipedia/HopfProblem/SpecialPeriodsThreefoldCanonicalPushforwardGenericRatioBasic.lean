import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsBasic
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Ratios in an original native holomorphic line bundle

Two sections of the same original line bundle have a scalar ratio wherever
the denominator section is nonzero.  The ratio is holomorphic because it
is the quotient of their coefficients in any one native local chart.
No holomorphicity of the preferred fibre coordinates is assumed.
-/

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.NativeBundleSections

variable {M : Type} {ι : Type*} [TopologicalSpace M]
  (C : VectorBundleCore ℂ M ℂ ι)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The scalar quotient of two vectors in the same original native fibre. -/
def ratio (U : Opens M) (s t : Section C I U) (x : U) : ℂ :=
  id (α := ℂ) (s x) / id (α := ℂ) (t x)

/-- The quotient recovers the numerator in the original fibre. -/
theorem ratio_smul (U : Opens M) (s t : Section C I U)
    (ht : ∀ x, t x ≠ 0) (x : U) : ratio C I U s t x • t x = s x := by
  change id (α := ℂ) (s x) / id (α := ℂ) (t x) * id (α := ℂ) (t x) = s x
  exact div_mul_cancel₀ _ (ht x)

/-- A nonzero vector determines its scalar multiplier uniquely. -/
theorem ratio_unique (U : Opens M) (s t : Section C I U)
    (ht : ∀ x, t x ≠ 0) (f : U → ℂ)
    (hf : ∀ x, f x • t x = s x) : f = ratio C I U s t := by
  funext x
  apply (mul_right_cancel₀ (show id (α := ℂ) (t x) ≠ 0 from ht x))
  exact (hf x).trans (ratio_smul C I U s t ht x).symm

/-- In every original chart the denominator's coefficient is nonzero. -/
theorem localCoefficient_ne_zero (U : Opens M) (t : Section C I U)
    (ht : ∀ x, t x ≠ 0) (i : ι) (x : U) (hx : (x : M) ∈ C.baseSet i) :
    (C.localTriv i ⟨(x : M), t x⟩).2 ≠ 0 := by
  exact ((C.localTriv i).linearEquivAt ℂ (x : M) hx).map_ne_zero_iff.mpr (ht x)

/-- The ratio equals the quotient of the two genuine native chart coefficients. -/
theorem ratio_localCoefficient (U : Opens M) (s t : Section C I U)
    (ht : ∀ x, t x ≠ 0) (i : ι) (x : U) (hx : (x : M) ∈ C.baseSet i) :
    ratio C I U s t x =
      (C.localTriv i ⟨(x : M), s x⟩).2 /
        (C.localTriv i ⟨(x : M), t x⟩).2 := by
  apply (eq_div_iff (localCoefficient_ne_zero C I U t ht i x hx)).mpr
  exact (((C.localTriv i).linear ℂ hx).2 (ratio C I U s t x) (t x)).symm.trans
    (congrArg (fun v : C.Fiber (x : M) =>
      (C.localTriv i ⟨(x : M), v⟩).2) (ratio_smul C I U s t ht x))

/-- Holomorphicity follows locally in a fixed original bundle chart. -/
theorem ratio_holomorphic [C.IsContMDiff I ω] (U : Opens M)
    (s t : Section C I U) (ht : ∀ x, t x ≠ 0) :
    ContMDiff I I₁ ω (ratio C I U s t) := by
  intro x
  let i := C.indexAt (x : M)
  have hx : (x : M) ∈ C.baseSet i := C.mem_baseSet_at x
  have hs := (Section.holomorphicAt_iff C I s x i hx).mp (s.contMDiff_toFun x)
  have ht' := (Section.holomorphicAt_iff C I t x i hx).mp (t.contMDiff_toFun x)
  apply (hs.div₀ ht' (localCoefficient_ne_zero C I U t ht i x hx)).congr_of_eventuallyEq
  filter_upwards [continuous_subtype_val.continuousAt
    ((C.isOpen_baseSet i).mem_nhds hx)] with y hy
  exact ratio_localCoefficient C I U s t ht i y hy

/-- The ratio as an actual holomorphic scalar section of the original open set. -/
def ratioSection [C.IsContMDiff I ω] (U : Opens M)
    (s t : Section C I U) (ht : ∀ x, t x ≠ 0) :
    HolomorphicFunctionSheaf.Section I M U :=
  ⟨ratio C I U s t, ratio_holomorphic C I U s t ht⟩

@[simp] theorem ratioSection_apply [C.IsContMDiff I ω] (U : Opens M)
    (s t : Section C I U) (ht : ∀ x, t x ≠ 0) (x : U) :
    ratioSection C I U s t ht x = ratio C I U s t x := rfl

/-- Scalar division commutes with literal restriction of the original sections. -/
theorem ratio_restrict {U V : Opens M} (h : U ≤ V) (s t : Section C I V) (x : U) :
    ratio C I U (Section.restrict C I h s) (Section.restrict C I h t) x =
      ratio C I V s t ⟨(x : M), h x.property⟩ := rfl

end Wikipedia.HopfProblem.NativeBundleSections

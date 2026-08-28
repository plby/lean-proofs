import Wikipedia.NoExoticSixSphere.LocalHomologyChartTransport
import Wikipedia.NoExoticSixSphere.RelativeCoefficientQuotient

/-!
# Chart-independent mod-two local classes

In dimensions at least three, the preceding integral local group vanishes,
so native coefficient reduction gives the local mod-two group. Reducing the
primitive integral chart class gives a nonzero class, independent of the
chart: the only possible integral change is a sign, and that sign vanishes
in the actual mod-two group. No global fundamental class is assumed or
constructed in this file.
-/

noncomputable section

namespace NoExoticSixSphere.ModTwoLocalClass

open RelativeSingularHomology

variable {M : Type} [TopologicalSpace M]

/-- Local homology formed from the original relative complex with native coefficients. -/
abbrev Group (p : ℕ) (x : M) (k : ℕ) := RelativeCoefficients.ModHomology p ({x}ᶜ : Set M) k

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  [T1Space M]

/-- The actual preceding local integral group vanishes in every chart. -/
theorem preceding_subsingleton (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source) :
    Subsingleton (LocalHomology x (n + 2)) :=
  chartLocalHomology_subsingleton (n + 1) e x hx (n + 1) (Nat.succ_ne_zero n)
    (Nat.ne_of_lt (Nat.lt_succ_self (n + 1)))

/-- Surjectivity of the original coefficient reduction is derived, not assumed. -/
theorem reduction_surjective (p : ℕ) (hp : p ≠ 0) (e : OpenPartialHomeomorph M E)
    (x : M) (hx : x ∈ e.source) :
    Function.Surjective (RelativeCoefficients.reductionMap p ({x}ᶜ : Set M) (n + 3)) := by
  let := preceding_subsingleton n e x hx
  exact RelativeCoefficients.reductionMap_surjective_of_subsingleton p hp ({x}ᶜ : Set M)
    (n + 2)

/-- The marking is on actual relative homology with the specified native cyclic coefficients. -/
def chartEquiv (p : ℕ) (hp : p ≠ 0) (e : OpenPartialHomeomorph M E) (x : M)
    (hx : x ∈ e.source) : Group p x (n + 3) ≃ₗ[ℤ] ZMod p :=
  RelativeCoefficients.markingEquiv p hp ({x}ᶜ : Set M) (n + 3)
    (reduction_surjective n p hp e x hx) (chartLocalTopEquiv (n + 1) e x hx)

theorem chartEquiv_reduction (p : ℕ) (hp : p ≠ 0) (e : OpenPartialHomeomorph M E)
    (x : M) (hx : x ∈ e.source) (a : LocalHomology x (n + 3)) :
    chartEquiv n p hp e x hx
        (RelativeCoefficients.reductionMap p ({x}ᶜ : Set M) (n + 3) a) =
      (chartLocalTopEquiv (n + 1) e x hx a : ZMod p) :=
  RelativeCoefficients.markingEquiv_reduction p hp ({x}ᶜ : Set M) (n + 3)
    (reduction_surjective n p hp e x hx) (chartLocalTopEquiv (n + 1) e x hx) a

/-- Reduce the primitive original integral local class through the native coefficient map. -/
def chartClass (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source) :
    Group 2 x (n + 3) :=
  RelativeCoefficients.reductionMap 2 ({x}ᶜ : Set M) (n + 3)
    (chartLocalTopClass (n + 1) e x hx)

theorem chartEquiv_class (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source) :
    chartEquiv n 2 (by decide) e x hx (chartClass n e x hx) = 1 := by
  rw [chartClass, chartEquiv_reduction, chartLocalTopEquiv_class, Int.cast_one]

theorem chartClass_ne_zero (e : OpenPartialHomeomorph M E) (x : M) (hx : x ∈ e.source) :
    chartClass n e x hx ≠ 0 := by
  intro h
  have he := congrArg (chartEquiv n 2 (by decide) e x hx) h
  rw [chartEquiv_class, map_zero] at he
  exact one_ne_zero he

/-- The integral sign ambiguity disappears in the original mod-two local homology group. -/
theorem chartClass_independent (e f : OpenPartialHomeomorph M E) (x : M)
    (he : x ∈ e.source) (hf : x ∈ f.source) : chartClass n e x he = chartClass n f x hf := by
  rcases chartLocalTopClass_eq_or_neg (n + 1) e f x he hf with h | h
  · exact congrArg (RelativeCoefficients.reductionMap 2 ({x}ᶜ : Set M) (n + 3)) h
  · change RelativeCoefficients.reductionMap 2 ({x}ᶜ : Set M) (n + 3)
      (chartLocalTopClass (n + 1) e x he) = _
    rw [h, map_neg]
    change -chartClass n f x hf = chartClass n f x hf
    apply (chartEquiv n 2 (by decide) f x hf).injective
    rw [map_neg, chartEquiv_class]
    decide

variable [ChartedSpace E M]

/-- A chart-independent nonzero local class on the original manifold's topological space. -/
def manifoldClass (x : M) : Group 2 x (n + 3) :=
  chartClass n (chartAt E x) x (mem_chart_source E x)

theorem manifoldClass_eq_chart (x : M) (e : OpenPartialHomeomorph M E) (hx : x ∈ e.source) :
    manifoldClass (E := E) n x = chartClass n e x hx :=
  chartClass_independent n (chartAt E x) e x (mem_chart_source E x) hx

theorem manifoldClass_ne_zero (x : M) : manifoldClass (E := E) n x ≠ 0 :=
  chartClass_ne_zero n (chartAt E x) x (mem_chart_source E x)

end NoExoticSixSphere.ModTwoLocalClass

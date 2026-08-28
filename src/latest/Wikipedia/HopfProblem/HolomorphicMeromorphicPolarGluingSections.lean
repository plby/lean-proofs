import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarGluingCocycle
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarBundle

/-!
# Native numerator and denominator sections from polar presentations

The actual local numerator and denominator functions glue in the native
line bundle constructed from their scalar cocycle. Their full native
trivialization coordinates are the original functions. The quotient of
these actual chart sections recovers the original meromorphic section as
an equality of full meromorphic germs, including at denominator zeros.
-/

noncomputable section

open Set Topology TopologicalSpace Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarGluing

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M] {s : Section I M ⊤}

def localNumerator (A : PolarLocal.Presentation I M s) : M → ℂ :=
  HolomorphicFunctionSheaf.extendManifoldSection I A.domain A.numerator

def localDenominator (A : PolarLocal.Presentation I M s) : M → ℂ :=
  HolomorphicFunctionSheaf.extendManifoldSection I A.domain A.denominator

@[simp] theorem localNumerator_apply (A : PolarLocal.Presentation I M s)
    (x : M) (hx : x ∈ A.domain) : localNumerator I M A x = A.numerator ⟨x, hx⟩ :=
  HolomorphicFunctionSheaf.extendManifoldSection_apply I A.domain A.numerator x hx

@[simp] theorem localDenominator_apply (A : PolarLocal.Presentation I M s)
    (x : M) (hx : x ∈ A.domain) : localDenominator I M A x = A.denominator ⟨x, hx⟩ :=
  HolomorphicFunctionSheaf.extendManifoldSection_apply I A.domain A.denominator x hx

theorem localNumerator_holomorphic (A : PolarLocal.Presentation I M s) :
    ContMDiffOn I 𝓘(ℂ) ω (localNumerator I M A) A.domain := by
  intro x hx
  exact (HolomorphicFunctionSheaf.extendManifoldSection_contMDiffAt I A.domain
    A.numerator x hx).contMDiffWithinAt

theorem localDenominator_holomorphic (A : PolarLocal.Presentation I M s) :
    ContMDiffOn I 𝓘(ℂ) ω (localDenominator I M A) A.domain := by
  intro x hx
  exact (HolomorphicFunctionSheaf.extendManifoldSection_contMDiffAt I A.domain
    A.denominator x hx).contMDiffWithinAt

theorem localNumerator_compatible (A B : PolarLocal.Presentation I M s)
    (x : M) (hx : x ∈ A.overlap B) :
    transition I M A B x * localNumerator I M A x = localNumerator I M B x := by
  rw [transition_apply I M A B x hx, localNumerator_apply I M A x hx.1,
    localNumerator_apply I M B x hx.2]
  exact congrArg (fun f : HolomorphicFunctionSheaf.Section I M (A.overlap B) ↦ f ⟨x, hx⟩)
    (transitionSection_mul_numerator I M A B)

theorem localDenominator_compatible (A B : PolarLocal.Presentation I M s)
    (x : M) (hx : x ∈ A.overlap B) :
    transition I M A B x * localDenominator I M A x = localDenominator I M B x := by
  rw [transition_apply I M A B x hx, localDenominator_apply I M A x hx.1,
    localDenominator_apply I M B x hx.2]
  exact congrArg (fun f : HolomorphicFunctionSheaf.Section I M (A.overlap B) ↦ f ⟨x, hx⟩)
    (transitionSection_mul_denominator I M A B)

variable {ι : Type*} (A : ι → PolarLocal.Presentation I M s)
  (hcover : ∀ x : M, ∃ i, x ∈ (A i).domain)

/-- The genuine native numerator section of the constructed line bundle. -/
def numeratorSection : ContMDiffSection I ℂ ω (cocycle I M A hcover).core.Fiber :=
  (cocycle I M A hcover).sectionOfCompatible (fun i ↦ localNumerator I M (A i))
    (fun i ↦ localNumerator_holomorphic I M (A i))
    (fun i j x hx ↦ localNumerator_compatible I M (A i) (A j) x hx)

/-- The genuine native denominator section of the same constructed bundle. -/
def denominatorSection : ContMDiffSection I ℂ ω (cocycle I M A hcover).core.Fiber :=
  (cocycle I M A hcover).sectionOfCompatible (fun i ↦ localDenominator I M (A i))
    (fun i ↦ localDenominator_holomorphic I M (A i))
    (fun i j x hx ↦ localDenominator_compatible I M (A i) (A j) x hx)

/-- The complete original-chart coordinates of the numerator section. -/
theorem numeratorSection_localTriv (i : ι) {x : M} (hx : x ∈ (A i).domain) :
    (cocycle I M A hcover).core.localTriv i ⟨x, numeratorSection I M A hcover x⟩ =
      (x, (A i).numerator ⟨x, hx⟩) := by
  calc
    _ = (x, localNumerator I M (A i) x) :=
      (cocycle I M A hcover).sectionOfCompatible_localTriv
        (fun i ↦ localNumerator I M (A i)) (fun i ↦ localNumerator_holomorphic I M (A i))
        (fun i j x hx ↦ localNumerator_compatible I M (A i) (A j) x hx) i hx
    _ = _ := congrArg (fun v : ℂ ↦ (x, v)) (localNumerator_apply I M (A i) x hx)

/-- The complete original-chart coordinates of the denominator section. -/
theorem denominatorSection_localTriv (i : ι) {x : M} (hx : x ∈ (A i).domain) :
    (cocycle I M A hcover).core.localTriv i ⟨x, denominatorSection I M A hcover x⟩ =
      (x, (A i).denominator ⟨x, hx⟩) := by
  calc
    _ = (x, localDenominator I M (A i) x) :=
      (cocycle I M A hcover).sectionOfCompatible_localTriv
        (fun i ↦ localDenominator I M (A i)) (fun i ↦ localDenominator_holomorphic I M (A i))
        (fun i j x hx ↦ localDenominator_compatible I M (A i) (A j) x hx) i hx
    _ = _ := congrArg (fun v : ℂ ↦ (x, v)) (localDenominator_apply I M (A i) x hx)

theorem numeratorSection_eq_zero_iff (i : ι) {x : M} (hx : x ∈ (A i).domain) :
    numeratorSection I M A hcover x = 0 ↔ (A i).numerator ⟨x, hx⟩ = 0 := by
  simpa only [numeratorSection, localNumerator_apply I M (A i) x hx] using
    (cocycle I M A hcover).sectionOfCompatible_eq_zero_iff
      (fun i ↦ localNumerator I M (A i)) (fun i ↦ localNumerator_holomorphic I M (A i))
      (fun i j x hx ↦ localNumerator_compatible I M (A i) (A j) x hx) i hx

theorem denominatorSection_eq_zero_iff (i : ι) {x : M} (hx : x ∈ (A i).domain) :
    denominatorSection I M A hcover x = 0 ↔ (A i).denominator ⟨x, hx⟩ = 0 := by
  simpa only [denominatorSection, localDenominator_apply I M (A i) x hx] using
    (cocycle I M A hcover).sectionOfCompatible_eq_zero_iff
      (fun i ↦ localDenominator I M (A i)) (fun i ↦ localDenominator_holomorphic I M (A i))
      (fun i j x hx ↦ localDenominator_compatible I M (A i) (A j) x hx) i hx

/-- The actual native numerator coordinates, bundled on the original open set. -/
def numeratorInChart (i : ι) : HolomorphicFunctionSheaf.Section I M (A i).domain :=
  ⟨fun x ↦ ((cocycle I M A hcover).core.localTriv i
      ⟨x.val, numeratorSection I M A hcover x.val⟩).2, by
    have he : (fun x : (A i).domain ↦ ((cocycle I M A hcover).core.localTriv i
        ⟨x.val, numeratorSection I M A hcover x.val⟩).2) =
        ((A i).numerator : (A i).domain → ℂ) := by
      funext x
      exact congrArg Prod.snd (numeratorSection_localTriv I M A hcover i x.property)
    rw [he]
    exact (A i).numerator.contMDiff⟩

/-- The actual native denominator coordinates, bundled on the same original open set. -/
def denominatorInChart (i : ι) : HolomorphicFunctionSheaf.Section I M (A i).domain :=
  ⟨fun x ↦ ((cocycle I M A hcover).core.localTriv i
      ⟨x.val, denominatorSection I M A hcover x.val⟩).2, by
    have he : (fun x : (A i).domain ↦ ((cocycle I M A hcover).core.localTriv i
        ⟨x.val, denominatorSection I M A hcover x.val⟩).2) =
        ((A i).denominator : (A i).domain → ℂ) := by
      funext x
      exact congrArg Prod.snd (denominatorSection_localTriv I M A hcover i x.property)
    rw [he]
    exact (A i).denominator.contMDiff⟩

@[simp] theorem numeratorInChart_eq (i : ι) :
    numeratorInChart I M A hcover i = (A i).numerator := by
  apply ContMDiffMap.ext
  intro x
  exact congrArg Prod.snd (numeratorSection_localTriv I M A hcover i x.property)

@[simp] theorem denominatorInChart_eq (i : ι) :
    denominatorInChart I M A hcover i = (A i).denominator := by
  apply ContMDiffMap.ext
  intro x
  exact congrArg Prod.snd (denominatorSection_localTriv I M A hcover i x.property)

theorem denominatorInChart_germ_ne_zero (i : ι) (x : (A i).domain) :
    holomorphicGerm I M (A i).domain x (denominatorInChart I M A hcover i) ≠ 0 := by
  rw [denominatorInChart_eq]
  exact (A i).denominator_ne_zero x

/-- The quotient of the actual bundle-chart sections has exactly the
original meromorphic germ, also at pointwise denominator zeros. -/
theorem quotient_germ (i : ι) (x : (A i).domain) :
    s ⟨x.val, Set.mem_univ x.val⟩ =
      fraction I M (A i).domain (numeratorInChart I M A hcover i)
        (denominatorInChart I M A hcover i) x := by
  rw [numeratorInChart_eq, denominatorInChart_eq]
  exact (A i).fraction_eq x

/-- The quotient identity is equality of genuine meromorphic sections on
each member of the original cover, not merely an identity of ordinary values. -/
theorem quotient_in_chart (i : ι) :
    restrict I M le_top s =
      ofFraction I M (A i).domain (numeratorInChart I M A hcover i)
        (denominatorInChart I M A hcover i) (denominatorInChart_germ_ne_zero I M A hcover i) := by
  apply section_ext
  intro x
  exact quotient_germ I M A hcover i x

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarGluing

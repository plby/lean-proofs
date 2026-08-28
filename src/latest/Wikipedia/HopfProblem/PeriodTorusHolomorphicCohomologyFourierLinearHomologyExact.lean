import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierLinearComplex

/-!
# Exact mean coordinates for actual closed Dolbeault pairs

The cycle space is the kernel of the genuine top differential.  The
normalized smooth Fourier primitive shows that the kernel of its literal
componentwise Haar mean is exactly the image of the first differential.
Constant pairs split the mean map.  These are exact sequences in `ModuleCat`.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear

open PeriodTorusLineBundleClassification

/-- The actual kernel of the top differential, not a replacement cohomology space. -/
abbrev closedPairs (p : PeriodDomain) := (top p).ker

def closedInclusion (p : PeriodDomain) : closedPairs p →ₗ[ℂ] Pair :=
  (top p).ker.subtype

@[simp] theorem closedInclusion_apply (p : PeriodDomain) (a : closedPairs p) :
    closedInclusion p a = a.val := rfl

/-- The first actual differential, with its proved closedness recorded. -/
def differentialToClosed (p : PeriodDomain) : Smooth →ₗ[ℂ] closedPairs p :=
  (differential p).codRestrict (top p).ker fun f => by
    change top p (differential p f) = 0
    exact LinearMap.congr_fun (top_differential p) f

@[simp] theorem differentialToClosed_val (p : PeriodDomain) (f : Smooth) :
    (differentialToClosed p f).val = differential p f := rfl

/-- Literal probability Haar means of the two closed coefficient functions. -/
def closedMean (p : PeriodDomain) : closedPairs p →ₗ[ℂ] (Fin 2 → ℂ) :=
  pairMean.comp (closedInclusion p)

@[simp] theorem closedMean_apply (p : PeriodDomain) (a : closedPairs p) :
    closedMean p a = pairMean a.val := rfl

def closedConstantPair (p : PeriodDomain) : (Fin 2 → ℂ) →ₗ[ℂ] closedPairs p :=
  constantPair.codRestrict (top p).ker (top_constantPair p)

@[simp] theorem closedConstantPair_val (p : PeriodDomain) (c : Fin 2 → ℂ) :
    (closedConstantPair p c).val = constantPair c := rfl

@[simp] theorem closedMean_constantPair (p : PeriodDomain) (c : Fin 2 → ℂ) :
    closedMean p (closedConstantPair p c) = c := pairMean_constantPair c

@[simp] theorem closedMean_differential (p : PeriodDomain) (f : Smooth) :
    closedMean p (differentialToClosed p f) = 0 := pairMean_differential p f

/-- The existing normalized smooth primitive gives equality of actual coefficient pairs. -/
theorem differential_potential (p : PeriodDomain) (a : Pair) (ha : top p a = 0) :
    differential p (torusDbarPotential p a) = a - constantPair (pairMean a) := by
  funext i
  apply smooth_ext
  intro x
  exact torusDbar_torusDbarPotential p a ((top_eq_zero_iff p a).mp ha) i x

theorem exists_differential_eq_iff_of_closed (p : PeriodDomain) (a : Pair)
    (ha : top p a = 0) :
    (∃ f : Smooth, differential p f = a) ↔ pairMean a = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    exact pairMean_differential p f
  · intro hm
    refine ⟨torusDbarPotential p a, ?_⟩
    rw [differential_potential p a ha, hm, map_zero, sub_zero]

/-- Zero means of a genuinely closed pair imply an actual smooth primitive. -/
theorem closedMean_exact (p : PeriodDomain) (a : closedPairs p)
    (ha : closedMean p a = 0) :
    ∃ f : Smooth, differentialToClosed p f = a := by
  obtain ⟨f, hf⟩ := (exists_differential_eq_iff_of_closed p a.val a.property).mpr ha
  exact ⟨f, Subtype.ext hf⟩

theorem closedMean_surjective (p : PeriodDomain) : Function.Surjective (closedMean p) :=
  fun c => ⟨closedConstantPair p c, closedMean_constantPair p c⟩

instance closedInclusion_mono (p : PeriodDomain) : Mono (ModuleCat.ofHom (closedInclusion p)) :=
  ConcreteCategory.mono_of_injective _ (top p).ker.injective_subtype

instance closedMean_epi (p : PeriodDomain) : Epi (ModuleCat.ofHom (closedMean p)) :=
  ConcreteCategory.epi_of_surjective _ (closedMean_surjective p)

/-- The genuine kernel inclusion followed by the genuine top derivative. -/
abbrev closedKernelComplex (p : PeriodDomain) : ShortComplex (ModuleCat ℂ) :=
  ShortComplex.moduleCatMk (closedInclusion p) (top p) (by
    apply LinearMap.ext
    intro a
    exact a.property)

theorem closedKernelComplex_exact (p : PeriodDomain) : (closedKernelComplex p).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  exact ⟨⟨a, ha⟩, rfl⟩

/-- The actual first differential followed by actual mean coordinates on its closed pairs. -/
abbrev closedMeanComplex (p : PeriodDomain) : ShortComplex (ModuleCat ℂ) :=
  ShortComplex.moduleCatMk (differentialToClosed p) (closedMean p) (by
    apply LinearMap.ext
    exact closedMean_differential p)

theorem closedMeanComplex_exact (p : PeriodDomain) : (closedMeanComplex p).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  exact closedMean_exact p

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear

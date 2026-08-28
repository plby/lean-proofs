import Wikipedia.HopfProblem.CuspNormalizationSheafReducedBasic

/-!
# Actual holomorphic pullback from a reduced subset

A locally ambient-holomorphic function on a subset pulls back to an
actual holomorphic function along any actual holomorphic map with image
in that subset. The proof composes the supplied local ambient
representatives with the given map. No normalization or extension
property is imposed on the reduced function beyond its definition.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafPullback

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H)

/-- A section extended by zero outside its original ambient open set.
Only its values and holomorphicity inside that open set are used. -/
def ambientSectionExtension (V : Opens M)
    (s : HolomorphicFunctionSheaf.Section I M V) (x : M) : ℂ := by
  classical
  exact if hx : x ∈ V then s ⟨x, hx⟩ else 0

@[simp] theorem ambientSectionExtension_apply (V : Opens M)
    (s : HolomorphicFunctionSheaf.Section I M V) (x : M) (hx : x ∈ V) :
    ambientSectionExtension I V s x = s ⟨x, hx⟩ := by
  classical
  simp only [ambientSectionExtension, dif_pos hx]

/-- The literal extension is holomorphic at every point of the original open set. -/
theorem ambientSectionExtension_contMDiffAt (V : Opens M)
    (s : HolomorphicFunctionSheaf.Section I M V) (x : M) (hx : x ∈ V) :
    ContMDiffAt I 𝓘(ℂ) ω (ambientSectionExtension I V s) x := by
  apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : V))).mp
  have he : (fun y : V => ambientSectionExtension I V s y) = (s : V → ℂ) :=
    funext fun y => ambientSectionExtension_apply I V s y y.property
  rw [he]
  exact s.contMDiff _

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace G] {N : Type} [TopologicalSpace N] [ChartedSpace G N]
  (J : ModelWithCorners ℂ F G) (S : Set M)
  (g : ContMDiffMap J I N M ω) (hg : ∀ x : N, g x ∈ S)

/-- The actual map with its codomain restricted to the subset. -/
def subsetMap (x : N) : S := ⟨g x, hg x⟩

theorem subsetMap_continuous : Continuous (subsetMap I J S g hg) :=
  g.contMDiff.continuous.subtype_mk _

/-- The actual inverse image of a relative open set. -/
def preimageOpen (U : Opens S) : Opens N :=
  ⟨subsetMap I J S g hg ⁻¹' (U : Set S),
    U.isOpen.preimage (subsetMap_continuous I J S g hg)⟩

@[simp] theorem mem_preimageOpen (U : Opens S) (x : N) :
    x ∈ preimageOpen I J S g hg U ↔ subsetMap I J S g hg x ∈ U := Iff.rfl

/-- Literal composition of a reduced holomorphic section with the map. -/
def pullbackFunction (U : Opens S) (s : SheafReduced.Section I S U)
    (x : preimageOpen I J S g hg U) : ℂ :=
  s ⟨subsetMap I J S g hg x, x.property⟩

/-- Actual local ambient representatives prove that the pullback is
holomorphic on its actual open inverse image. -/
theorem pullbackFunction_contMDiff (U : Opens S) (s : SheafReduced.Section I S U) :
    ContMDiff J 𝓘(ℂ) ω (pullbackFunction I J S g hg U s) := by
  intro x
  obtain ⟨V, hxV, φ, hφ⟩ := SheafReduced.Section.locallyAmbient I S s
    (⟨subsetMap I J S g hg x, x.property⟩ : U)
  have hg' : ContMDiffAt J I ω
      (fun y : preimageOpen I J S g hg U => g (y : N)) x :=
    (g.contMDiff _).comp x contMDiff_subtype_val.contMDiffAt
  have hh := (ambientSectionExtension_contMDiffAt I V φ (g x) hxV).comp x hg'
  apply hh.congr_of_eventuallyEq
  have hc : Continuous (fun y : preimageOpen I J S g hg U => g (y : N)) :=
    g.contMDiff.continuous.comp continuous_subtype_val
  filter_upwards [(V.isOpen.preimage hc).mem_nhds hxV] with y hy
  change s ⟨subsetMap I J S g hg y, y.property⟩ = ambientSectionExtension I V φ (g y)
  rw [ambientSectionExtension_apply I V φ (g y) hy]
  exact hφ ⟨subsetMap I J S g hg y, y.property⟩ hy

/-- Actual pullback of reduced holomorphic functions is a complex
algebra homomorphism into the genuine holomorphic section ring. -/
def pullbackSection (U : Opens S) :
    SheafReduced.Section I S U →ₐ[ℂ]
      HolomorphicFunctionSheaf.Section J N (preimageOpen I J S g hg U) where
  toFun s := ⟨pullbackFunction I J S g hg U s,
    pullbackFunction_contMDiff I J S g hg U s⟩
  map_zero' := by apply ContMDiffMap.ext; intro x; rfl
  map_one' := by apply ContMDiffMap.ext; intro x; rfl
  map_add' _ _ := by apply ContMDiffMap.ext; intro x; rfl
  map_mul' _ _ := by apply ContMDiffMap.ext; intro x; rfl
  commutes' _ := by apply ContMDiffMap.ext; intro x; rfl

@[simp] theorem pullbackSection_apply (U : Opens S) (s : SheafReduced.Section I S U)
    (x : preimageOpen I J S g hg U) :
    pullbackSection I J S g hg U s x = s ⟨subsetMap I J S g hg x, x.property⟩ := rfl

/-- Composition with the actual map commutes with literal restrictions. -/
theorem pullbackSection_restrict {U V : Opens S} (h : U ≤ V)
    (s : SheafReduced.Section I S V) :
    pullbackSection I J S g hg U (SheafReduced.restriction I S h s) =
      ContMDiffMap.restrictRingHom J 𝓘(ℂ) ℂ
        (show preimageOpen I J S g hg U ≤ preimageOpen I J S g hg V from fun _ hx => h hx)
        (pullbackSection I J S g hg V s) := by
  apply ContMDiffMap.ext
  intro x
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafPullback

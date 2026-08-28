import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkSections

/-!
# Actual smooth and holomorphic functions on the affine complex plane

The affine space here is the literal product `ℂ × ℂ`. Ambient representatives
are extended by zero only to name their derivatives; their smoothness is
asserted only on the original open domain. The holomorphic inclusion is the
literal inclusion of functions, with real smoothness proved in the actual
induced charts.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

abbrev HolomorphicSection (U : Opens (ℂ × ℂ)) :=
  HolomorphicFunctionSheaf.Section 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ) U

abbrev SmoothSection (U : Opens (ℂ × ℂ)) :=
  SmoothFunctions.Section 𝓘(ℝ, ℂ × ℂ) (ℂ × ℂ) U

abbrev holomorphicSheaf :=
  HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ)

abbrev smoothSheaf := SmoothFunctions.additiveSheaf 𝓘(ℝ, ℂ × ℂ) (ℂ × ℂ)

/-- Literal smooth restriction to an actual smaller open set. -/
abbrev restriction {U V : Opens (ℂ × ℂ)} (h : U ≤ V) :
    SmoothSection V →+* SmoothSection U :=
  ContMDiffMap.restrictRingHom 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ) ℂ h

/-- An ambient representative, with no regularity claim outside `U`. -/
def smoothExtend (U : Opens (ℂ × ℂ)) (s : SmoothSection U) (q : ℂ × ℂ) : ℂ := by
  classical
  exact if hq : q ∈ U then s ⟨q, hq⟩ else 0

@[simp] theorem smoothExtend_apply (U : Opens (ℂ × ℂ)) (s : SmoothSection U)
    (q : ℂ × ℂ) (hq : q ∈ U) : smoothExtend U s q = s ⟨q, hq⟩ := by
  classical
  simp only [smoothExtend, dif_pos hq]

theorem smoothExtend_comp_val (U : Opens (ℂ × ℂ)) (s : SmoothSection U) :
    (fun q : U => smoothExtend U s q) = (s : U → ℂ) :=
  funext fun q => smoothExtend_apply U s q q.property

/-- The representative is genuinely smooth at every point of its domain. -/
theorem smoothExtend_contDiffAt (U : Opens (ℂ × ℂ)) (s : SmoothSection U)
    (q : ℂ × ℂ) (hq : q ∈ U) : ContDiffAt ℝ ∞ (smoothExtend U s) q := by
  have h : ContMDiffAt 𝓘(ℝ, ℂ × ℂ) 𝓘(ℝ, ℂ) ∞ (smoothExtend U s) q := by
    apply (contMDiffAt_subtype_iff (x := (⟨q, hq⟩ : U))).mp
    rw [smoothExtend_comp_val]
    exact s.contMDiff _
  exact h.contDiffAt

theorem smoothExtend_contDiffOn (U : Opens (ℂ × ℂ)) (s : SmoothSection U) :
    ContDiffOn ℝ ∞ (smoothExtend U s) U :=
  fun q hq => (smoothExtend_contDiffAt U s q hq).contDiffWithinAt

theorem smoothExtend_add (U : Opens (ℂ × ℂ)) (s t : SmoothSection U) :
    smoothExtend U (s + t) = fun q => smoothExtend U s q + smoothExtend U t q := by
  classical
  funext q
  by_cases hq : q ∈ U
  · simp only [smoothExtend, dif_pos hq]
    rfl
  · simp only [smoothExtend, dif_neg hq, add_zero]

theorem smoothExtend_smul (U : Opens (ℂ × ℂ)) (c : ℂ) (s : SmoothSection U) :
    smoothExtend U (c • s) = fun q => c * smoothExtend U s q := by
  classical
  funext q
  by_cases hq : q ∈ U
  · simp only [smoothExtend, dif_pos hq]
    rfl
  · simp only [smoothExtend, dif_neg hq, mul_zero]

theorem smoothExtend_restrict_germ {U V : Opens (ℂ × ℂ)} (h : U ≤ V)
    (s : SmoothSection V) (q : ℂ × ℂ) (hq : q ∈ U) :
    smoothExtend U (restriction h s) =ᶠ[𝓝 q] smoothExtend V s := by
  filter_upwards [U.isOpen.mem_nhds hq] with p hp
  rw [smoothExtend_apply _ _ p hp, smoothExtend_apply _ _ p (h hp)]
  rfl

/-- A genuinely smooth ambient function on `U` gives a literal section. -/
def sectionOfSmooth (U : Opens (ℂ × ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ f U) : SmoothSection U :=
  ⟨fun q => f q, fun q => contMDiffAt_subtype_iff.mpr
    ((hf q q.property).contDiffAt (U.isOpen.mem_nhds q.property)).contMDiffAt⟩

@[simp] theorem sectionOfSmooth_apply (U : Opens (ℂ × ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ f U) (q : U) : sectionOfSmooth U f hf q = f q := rfl

theorem smoothExtend_sectionOfSmooth_germ (U : Opens (ℂ × ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ f U) (q : ℂ × ℂ) (hq : q ∈ U) :
    smoothExtend U (sectionOfSmooth U f hf) =ᶠ[𝓝 q] f := by
  filter_upwards [U.isOpen.mem_nhds hq] with p hp
  exact smoothExtend_apply U (sectionOfSmooth U f hf) p hp

/-- The actual complex-linear inclusion of holomorphic sections. -/
def inclusionSection (U : Opens (ℂ × ℂ)) : HolomorphicSection U →ₗ[ℂ] SmoothSection U where
  toFun f := ⟨f, by
    have hf := f.contMDiff
    rw [contMDiff_iff] at hf ⊢
    exact ⟨hf.1, fun x y => ((hf.2 x y).of_le (by simp)).restrict_scalars ℝ⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem inclusionSection_apply (U : Opens (ℂ × ℂ))
    (f : HolomorphicSection U) (q : U) : inclusionSection U f q = f q := rfl

/-- The inclusion is an actual morphism of the genuine additive sheaves. -/
def inclusion : holomorphicSheaf ⟶ smoothSheaf where
  hom :=
    { app U := AddCommGrpCat.ofHom (inclusionSection U.unop).toAddMonoidHom
      naturality _ _ _ := rfl }

instance inclusion_mono : Mono inclusion := by
  have h (U : (Opens (TopCat.of (ℂ × ℂ)))ᵒᵖ) : Mono (inclusion.hom.app U) := by
    apply ConcreteCategory.mono_of_injective
    intro f g he
    exact ContMDiffMap.ext fun q => congrArg (fun s : SmoothSection U.unop => s q) he
  have : Mono inclusion.hom := NatTrans.mono_of_mono_app _
  exact (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of (ℂ × ℂ))).mono_of_mono_map this

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

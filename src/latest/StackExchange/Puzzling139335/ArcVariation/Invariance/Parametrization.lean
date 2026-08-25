import StackExchange.Puzzling139335.ArcVariation.Invariance
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Independence of continuous injective interval parameters

A continuous injective real-valued map on a real interval is either increasing
or decreasing. In the decreasing case, reversing the source interval reduces
the concrete chain argument to the increasing case. Two continuous injective
parametrizations with the same image induce a homeomorphism between their
compact parameter intervals, so their sets of attainable scores are equal.
-/

open Set

namespace Puzzling139335.ArcVariation

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

/-- A decreasing surjective change of a real interval parameter preserves
exactly the attainable finite-chain scores. -/
theorem scoresOn_comp_eq_of_antitoneOn_surjOn_Icc (ε : ℝ) (f : ℝ → X)
    {g : ℝ → ℝ} {a b : ℝ} {t : Set ℝ}
    (hg : AntitoneOn g (Icc a b)) (hmaps : MapsTo g (Icc a b) t)
    (hsurj : SurjOn g (Icc a b) t) :
    scoresOn ε (f ∘ g) (Icc a b) = scoresOn ε f t := by
  have hreflect : MapsTo (fun u : ℝ => a + b - u) (Icc a b) (Icc a b) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hmono : MonotoneOn (fun u : ℝ => g (a + b - u)) (Icc a b) := by
    intro u hu v hv huv
    exact hg (hreflect hv) (hreflect hu) (by linarith)
  have hmaps' : MapsTo (fun u : ℝ => g (a + b - u)) (Icc a b) t := by
    intro u hu
    exact hmaps (hreflect hu)
  have hsurj' : SurjOn (fun u : ℝ => g (a + b - u)) (Icc a b) t := by
    intro y hy
    obtain ⟨u, hu, hgu⟩ := hsurj hy
    refine ⟨a + b - u, hreflect hu, ?_⟩
    simpa only [show a + b - (a + b - u) = u by ring] using hgu
  calc
    scoresOn ε (f ∘ g) (Icc a b) =
        scoresOn ε (fun u => f (g (a + b - u))) (Icc a b) :=
      (scoresOn_reflect_Icc ε (f ∘ g) a b).symm
    _ = scoresOn ε f t :=
      scoresOn_comp_eq_of_monotoneOn_surjOn ε f hmono hmaps' hsurj'

theorem variationOn_comp_eq_of_antitoneOn_surjOn_Icc (ε : ℝ) (f : ℝ → X)
    {g : ℝ → ℝ} {a b : ℝ} {t : Set ℝ}
    (hg : AntitoneOn g (Icc a b)) (hmaps : MapsTo g (Icc a b) t)
    (hsurj : SurjOn g (Icc a b) t) :
    variationOn ε (f ∘ g) (Icc a b) = variationOn ε f t := by
  unfold variationOn
  rw [scoresOn_comp_eq_of_antitoneOn_surjOn_Icc ε f hg hmaps hsurj]

/-- A continuous injective reparametrization of a real interval preserves the
set of concrete chain scores whenever it maps onto the target parameter set.
The interval may be empty or degenerate. -/
theorem scoresOn_comp_eq_of_continuousOn_injOn_Icc (ε : ℝ) (f : ℝ → X)
    {g : ℝ → ℝ} {a b : ℝ} {t : Set ℝ}
    (hg_cont : ContinuousOn g (Icc a b)) (hg_inj : InjOn g (Icc a b))
    (hmaps : MapsTo g (Icc a b) t) (hsurj : SurjOn g (Icc a b) t) :
    scoresOn ε (f ∘ g) (Icc a b) = scoresOn ε f t := by
  by_cases hab : a ≤ b
  · rcases hg_cont.strictMonoOn_of_injOn_Icc' hab hg_inj with hmono | hanti
    · exact scoresOn_comp_eq_of_monotoneOn_surjOn ε f hmono.monotoneOn hmaps hsurj
    · exact scoresOn_comp_eq_of_antitoneOn_surjOn_Icc ε f hanti.antitoneOn hmaps hsurj
  · have hmono : MonotoneOn g (Icc a b) := by
      intro u hu v hv huv
      exact (hab (hu.1.trans hu.2)).elim
    exact scoresOn_comp_eq_of_monotoneOn_surjOn ε f hmono hmaps hsurj

/-- Finite-resolution variation is independent of continuous injective changes
of a real interval parameter, with no boundedness or positivity premise. -/
theorem variationOn_comp_eq_of_continuousOn_injOn_Icc (ε : ℝ) (f : ℝ → X)
    {g : ℝ → ℝ} {a b : ℝ} {t : Set ℝ}
    (hg_cont : ContinuousOn g (Icc a b)) (hg_inj : InjOn g (Icc a b))
    (hmaps : MapsTo g (Icc a b) t) (hsurj : SurjOn g (Icc a b) t) :
    variationOn ε (f ∘ g) (Icc a b) = variationOn ε f t := by
  unfold variationOn
  rw [scoresOn_comp_eq_of_continuousOn_injOn_Icc ε f hg_cont hg_inj hmaps hsurj]

section ParameterChange

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z]
variable {f g : ℝ → Z} {a b c d : ℝ}

private def parameterImageHomeomorph
    (hf : ContinuousOn f (Icc a b)) (hfi : InjOn f (Icc a b)) :
    Icc a b ≃ₜ f '' Icc a b := by
  let e : Icc a b ≃ f '' Icc a b := Equiv.Set.imageOfInjOn f (Icc a b) hfi
  have he : Continuous e := hf.domRestrict.subtype_mk _
  exact e.toHomeomorphOfContinuousClosed he he.isClosedMap

private def equalImageParameterHomeomorph
    (hf : ContinuousOn f (Icc a b)) (hfi : InjOn f (Icc a b))
    (hg : ContinuousOn g (Icc c d)) (hgi : InjOn g (Icc c d))
    (hfg : f '' Icc a b = g '' Icc c d) : Icc a b ≃ₜ Icc c d :=
  (parameterImageHomeomorph hf hfi).trans
    ((Homeomorph.setCongr hfg).trans (parameterImageHomeomorph hg hgi).symm)

private theorem equalImageParameterHomeomorph_agreement
    (hf : ContinuousOn f (Icc a b)) (hfi : InjOn f (Icc a b))
    (hg : ContinuousOn g (Icc c d)) (hgi : InjOn g (Icc c d))
    (hfg : f '' Icc a b = g '' Icc c d) (x : Icc a b) :
    g (equalImageParameterHomeomorph hf hfi hg hgi hfg x) = f x := by
  have h := congrArg Subtype.val ((parameterImageHomeomorph hg hgi).apply_symm_apply
    ((Homeomorph.setCongr hfg) ((parameterImageHomeomorph hf hfi) x)))
  exact h

private def ambientParameterChange (e : Icc a b ≃ₜ Icc c d) (x : ℝ) : ℝ :=
  if hx : x ∈ Icc a b then e ⟨x, hx⟩ else 0

private theorem ambientParameterChange_of_mem (e : Icc a b ≃ₜ Icc c d)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ambientParameterChange e x = (e ⟨x, hx⟩ : ℝ) := by
  simp only [ambientParameterChange, dif_pos hx]

private theorem ambientParameterChange_continuousOn (e : Icc a b ≃ₜ Icc c d) :
    ContinuousOn (ambientParameterChange e) (Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : Continuous (fun x : Icc a b => (e x : ℝ)) :=
    continuous_subtype_val.comp e.continuous
  convert he using 1
  funext x
  exact ambientParameterChange_of_mem e x.property

private theorem ambientParameterChange_injOn (e : Icc a b ≃ₜ Icc c d) :
    InjOn (ambientParameterChange e) (Icc a b) := by
  intro x hx y hy hxy
  rw [ambientParameterChange_of_mem e hx, ambientParameterChange_of_mem e hy] at hxy
  exact congrArg Subtype.val (e.injective (Subtype.ext hxy))

private theorem ambientParameterChange_mapsTo (e : Icc a b ≃ₜ Icc c d) :
    MapsTo (ambientParameterChange e) (Icc a b) (Icc c d) := by
  intro x hx
  rw [ambientParameterChange_of_mem e hx]
  exact (e ⟨x, hx⟩).property

private theorem ambientParameterChange_surjOn (e : Icc a b ≃ₜ Icc c d) :
    SurjOn (ambientParameterChange e) (Icc a b) (Icc c d) := by
  intro y hy
  obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
  refine ⟨x, x.property, ?_⟩
  simpa only [ambientParameterChange_of_mem e x.property] using congrArg Subtype.val hx

/-- Equal-image injective continuous parametrizations of compact real intervals
admit a continuous injective parameter change. Only the Hausdorff property of
the common target is needed. The intervals may be empty or degenerate. -/
theorem exists_continuous_parameter_change_Icc
    (hf : ContinuousOn f (Icc a b)) (hfi : InjOn f (Icc a b))
    (hg : ContinuousOn g (Icc c d)) (hgi : InjOn g (Icc c d))
    (hfg : f '' Icc a b = g '' Icc c d) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc a b) ∧ InjOn φ (Icc a b) ∧
      MapsTo φ (Icc a b) (Icc c d) ∧ SurjOn φ (Icc a b) (Icc c d) ∧
      EqOn (g ∘ φ) f (Icc a b) := by
  let e := equalImageParameterHomeomorph hf hfi hg hgi hfg
  refine ⟨ambientParameterChange e, ambientParameterChange_continuousOn e,
    ambientParameterChange_injOn e, ambientParameterChange_mapsTo e,
    ambientParameterChange_surjOn e, ?_⟩
  intro x hx
  simpa only [Function.comp_apply, ambientParameterChange_of_mem e hx] using
    equalImageParameterHomeomorph_agreement hf hfi hg hgi hfg ⟨x, hx⟩

end ParameterChange

section EqualImage

variable [T2Space X] {f g : ℝ → X} {a b c d : ℝ}

/-- Two continuous injective parametrizations of the same arc have exactly the
same attainable finite-chain scores, irrespective of their orientations. -/
theorem scoresOn_eq_of_continuousOn_injOn_image_eq_Icc (ε : ℝ)
    (hf : ContinuousOn f (Icc a b)) (hfi : InjOn f (Icc a b))
    (hg : ContinuousOn g (Icc c d)) (hgi : InjOn g (Icc c d))
    (hfg : f '' Icc a b = g '' Icc c d) :
    scoresOn ε f (Icc a b) = scoresOn ε g (Icc c d) := by
  obtain ⟨φ, hφ_cont, hφ_inj, hφ_maps, hφ_surj, hφ_agree⟩ :=
    exists_continuous_parameter_change_Icc hf hfi hg hgi hfg
  calc
    scoresOn ε f (Icc a b) = scoresOn ε (g ∘ φ) (Icc a b) :=
      scoresOn_congr (fun x hx => (hφ_agree hx).symm)
    _ = scoresOn ε g (Icc c d) :=
      scoresOn_comp_eq_of_continuousOn_injOn_Icc ε g hφ_cont hφ_inj hφ_maps hφ_surj

/-- Truncated variation depends only on the image of a continuous injective
compact-interval parametrization. No finiteness premise is needed for equality. -/
theorem variationOn_eq_of_continuousOn_injOn_image_eq_Icc (ε : ℝ)
    (hf : ContinuousOn f (Icc a b)) (hfi : InjOn f (Icc a b))
    (hg : ContinuousOn g (Icc c d)) (hgi : InjOn g (Icc c d))
    (hfg : f '' Icc a b = g '' Icc c d) :
    variationOn ε f (Icc a b) = variationOn ε g (Icc c d) := by
  unfold variationOn
  rw [scoresOn_eq_of_continuousOn_injOn_image_eq_Icc ε hf hfi hg hgi hfg]

end EqualImage

end

end Puzzling139335.ArcVariation

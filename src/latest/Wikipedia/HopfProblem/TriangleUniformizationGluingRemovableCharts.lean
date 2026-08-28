import Wikipedia.HopfProblem.TriangleUniformizationGluingRemovable
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Transport of continuous removability through holomorphic coordinates

An actual open partial homeomorphism with holomorphic forward and inverse
maps transports removability.  In particular, a curve that a proved local
complex coordinate sends to the real axis is continuously removable.
-/

noncomputable section

open Function Set
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

/-- Pull back a removable set through an actual biholomorphic coordinate.
Only the source inclusion and holomorphy of the two coordinate functions
are hypotheses; removability is proved by composing the test function. -/
theorem ContinuousRemovable.preimage {Ω S : Set ℂ}
    {e : OpenPartialHomeomorph ℂ ℂ} (hS : ContinuousRemovable (e '' Ω) S)
    (hΩ : Ω ⊆ e.source) (he : DifferentiableOn ℂ e e.source)
    (he' : DifferentiableOn ℂ e.symm e.target) :
    ContinuousRemovable Ω (e ⁻¹' S) := by
  intro V hV hVΩ f hf hd
  have hVs : V ⊆ e.source := hVΩ.trans hΩ
  have hW : IsOpen (e '' V) := e.isOpen_image_of_subset_source hV hVs
  have hWt : e '' V ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hVs hz)
  have hinv : MapsTo e.symm (e '' V) V := by
    rintro y ⟨z, hz, rfl⟩
    simpa only [e.left_inv (hVs hz)] using hz
  have hc : ContinuousOn (f ∘ e.symm) (e '' V) :=
    hf.comp (e.symm.continuousOn.mono hWt) hinv
  have hd' : ∀ y ∈ (e '' V) \ S, DifferentiableAt ℂ (f ∘ e.symm) y := by
    intro y hy
    have hnot : e.symm y ∉ e ⁻¹' S := by
      change e (e.symm y) ∉ S
      rw [e.right_inv (hWt hy.1)]
      exact hy.2
    exact (hd (e.symm y) ⟨hinv hy.1, hnot⟩).comp y
      (he'.differentiableAt (e.open_target.mem_nhds (hWt hy.1)))
  have hdiff := hS (e '' V) hW (image_mono hVΩ) (f ∘ e.symm) hc hd'
  have hcomp : DifferentiableOn ℂ ((f ∘ e.symm) ∘ e) V :=
    hdiff.comp (he.mono hVs) (fun z hz => ⟨z, hz, rfl⟩)
  apply hcomp.congr
  intro z hz
  simp only [comp_apply, e.left_inv (hVs hz)]

/-- Push forward a removable subset of the ambient domain through an
actual biholomorphic coordinate. -/
theorem ContinuousRemovable.image {Ω S : Set ℂ}
    {e : OpenPartialHomeomorph ℂ ℂ} (hS : ContinuousRemovable Ω S)
    (hΩ : Ω ⊆ e.source) (hSΩ : S ⊆ Ω) (he : DifferentiableOn ℂ e e.source)
    (he' : DifferentiableOn ℂ e.symm e.target) :
    ContinuousRemovable (e '' Ω) (e '' S) := by
  have htarget : e '' Ω ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hΩ hz)
  have hinverse : e.symm '' (e '' Ω) = Ω :=
    e.toPartialEquiv.symm_image_image_of_subset_source hΩ
  have hS' : ContinuousRemovable (e.symm '' (e '' Ω)) S := by
    rwa [hinverse]
  have hp : ContinuousRemovable (e '' Ω) (e.symm ⁻¹' S) :=
    hS'.preimage (e := e.symm) htarget he' he
  apply hp.mono_set_on
  rintro y _ ⟨z, hz, rfl⟩
  change e.symm (e z) ∈ S
  simpa only [e.left_inv (hΩ (hSΩ hz))] using hz

/-- An actual holomorphic coordinate that straightens a curve to the
real axis proves that the curve is continuously removable. -/
theorem continuousRemovable_preimage_realAxis (e : OpenPartialHomeomorph ℂ ℂ)
    (Ω : Set ℂ) (hΩ : Ω ⊆ e.source) (he : DifferentiableOn ℂ e e.source)
    (he' : DifferentiableOn ℂ e.symm e.target) :
    ContinuousRemovable Ω {z : ℂ | (e z).im = 0} :=
  (continuousRemovable_realAxis (e '' Ω)).preimage hΩ he he'

end Wikipedia.HopfProblem.TriangleUniformizationGluing

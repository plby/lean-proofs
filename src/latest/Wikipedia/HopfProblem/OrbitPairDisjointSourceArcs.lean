import Wikipedia.SmoothSixDPoincare.ShortEmbeddedArc
import Wikipedia.SmoothSixDPoincare.FinitePointPathAvoidance

/-!
# Two disjoint smooth source arcs with finite avoidance

In a connected manifold of dimension at least two, four distinct points
can be joined in any prescribed pairing by two disjoint embedded immersive
arcs. Start with two short arcs in disjoint neighborhoods. Two actual
global diffeomorphisms move their far endpoints to the requested points,
while fixing the other endpoints and the finite obstacle set. Applying
each diffeomorphism to both arcs preserves disjointness.

This source construction is valid in dimension two: it does not use
generic removal of intersections between two curves in a surface.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SourceArcs

open Wikipedia.SmoothSixDPoincare

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [PathConnectedSpace M]

theorem exists_disjoint_embedded_arc_pair
    (hdim : 2 ≤ Module.finrank ℝ E)
    {x₀ x₁ y₀ y₁ : M} (hxx : x₀ ≠ x₁) (hyy : y₀ ≠ y₁)
    (hcross : Disjoint ({x₀, x₁} : Set M) {y₀, y₁})
    {S : Set M} (hS : S.Finite)
    (hx₀S : x₀ ∉ S) (hx₁S : x₁ ∉ S) (hy₀S : y₀ ∉ S) (hy₁S : y₁ ∉ S) :
    ∃ f : C(ℝ, M), ∃ g : C(ℝ, M),
      ContMDiff 𝓘(ℝ, ℝ) I ∞ f ∧ ContMDiff 𝓘(ℝ, ℝ) I ∞ g ∧
      f 0 = x₀ ∧ f 1 = x₁ ∧ g 0 = y₀ ∧ g 1 = y₁ ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) I f t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) I g t)) ∧
      Disjoint (range (fun t : unitInterval => f t)) (range (fun t : unitInterval => g t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, f t ∉ S) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, g t ∉ S) := by
  classical
  have hx₀y₀ : x₀ ≠ y₀ := by
    intro heq
    exact disjoint_left.mp hcross (show x₀ ∈ ({x₀, x₁} : Set M) by simp) (by simp [heq])
  have hx₀y₁ : x₀ ≠ y₁ := by
    intro heq
    exact disjoint_left.mp hcross (show x₀ ∈ ({x₀, x₁} : Set M) by simp) (by simp [heq])
  have hx₁y₀ : x₁ ≠ y₀ := by
    intro heq
    exact disjoint_left.mp hcross (show x₁ ∈ ({x₀, x₁} : Set M) by simp) (by simp [heq])
  have hx₁y₁ : x₁ ≠ y₁ := by
    intro heq
    exact disjoint_left.mp hcross (show x₁ ∈ ({x₀, x₁} : Set M) by simp) (by simp [heq])
  let T : Set M := insert x₁ (insert y₁ S)
  have hT : T.Finite := (hS.insert y₁).insert x₁
  have hx₀T : x₀ ∉ T := by simp [T, hxx, hx₀y₁, hx₀S]
  have hy₀T : y₀ ∉ T := by simp [T, hx₁y₀.symm, hyy, hy₀S]
  obtain ⟨U, V, hU, hV, hx₀U, hy₀V, hUV⟩ := t2_separation hx₀y₀
  obtain ⟨f, hf, hf0, hf1, hembf, hif, hfU⟩ := exists_short_embedded_arc (J := I)
    (hU.inter hT.isClosed.isOpen_compl) ⟨hx₀U, hx₀T⟩ hdim
  obtain ⟨g, hg, hg0, hg1, hembg, hig, hgV⟩ := exists_short_embedded_arc (J := I)
    (hV.inter hT.isClosed.isOpen_compl) ⟨hy₀V, hy₀T⟩ hdim
  have hsep : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, f s ≠ g t := by
    intro s hs t ht heq
    exact disjoint_left.mp hUV (hfU s hs).1 (heq.symm ▸ (hgV t ht).1)
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hf1T : f 1 ≠ x₁ ∧ f 1 ≠ y₁ ∧ f 1 ∉ S := by simpa [T] using (hfU 1 h1I).2
  have hg1T : g 1 ≠ x₁ ∧ g 1 ≠ y₁ ∧ g 1 ∉ S := by simpa [T] using (hgV 1 h1I).2
  have hf1y₀ : f 1 ≠ y₀ := by simpa only [hg0] using hsep 1 h1I 0 h0I
  have hg1x₀ : g 1 ≠ x₀ := by simpa only [hf0] using (hsep 0 h0I 1 h1I).symm
  let C₁ : Set M := insert x₀ (insert y₀ (insert (g 1) (insert y₁ S)))
  have hC₁ : C₁.Finite := (((hS.insert y₁).insert (g 1)).insert y₀).insert x₀
  have hf1C₁ : f 1 ∉ C₁ := by
    simp [C₁, hf1, hf1y₀, hsep 1 h1I 1 h1I, hf1T.2.1, hf1T.2.2]
  have hx₁C₁ : x₁ ∉ C₁ := by
    simp [C₁, hxx.symm, hx₁y₀, hg1T.1.symm, hx₁y₁, hx₁S]
  obtain ⟨d₁, hd₁, hfix₁⟩ := exists_pointMoving_fixing_finite (J := I)
    (PathConnectedSpace.somePath (f 1) x₁) hdim hC₁ hf1C₁ hx₁C₁
  let C₂ : Set M := insert x₀ (insert x₁ (insert y₀ S))
  have hC₂ : C₂.Finite := ((hS.insert y₀).insert x₁).insert x₀
  have hg1C₂ : g 1 ∉ C₂ := by simp [C₂, hg1x₀, hg1T.1, hg1, hg1T.2.2]
  have hy₁C₂ : y₁ ∉ C₂ := by simp [C₂, hx₀y₁.symm, hx₁y₁.symm, hyy.symm, hy₁S]
  obtain ⟨d₂, hd₂, hfix₂⟩ := exists_pointMoving_fixing_finite (J := I)
    (PathConnectedSpace.somePath (g 1) y₁) hdim hC₂ hg1C₂ hy₁C₂
  let d := d₁.trans d₂
  have hdx₀ : d x₀ = x₀ := by
    change d₂ (d₁ x₀) = x₀
    rw [hfix₁ x₀ (by simp [C₁]), hfix₂ x₀ (by simp [C₂])]
  have hdf1 : d (f 1) = x₁ := by
    change d₂ (d₁ (f 1)) = x₁
    rw [hd₁, hfix₂ x₁ (by simp [C₂])]
  have hdy₀ : d y₀ = y₀ := by
    change d₂ (d₁ y₀) = y₀
    rw [hfix₁ y₀ (by simp [C₁]), hfix₂ y₀ (by simp [C₂])]
  have hdg1 : d (g 1) = y₁ := by
    change d₂ (d₁ (g 1)) = y₁
    rw [hfix₁ (g 1) (by simp [C₁]), hd₂]
  have hdfix : ∀ z ∈ S, d z = z := by
    intro z hz
    change d₂ (d₁ z) = z
    rw [hfix₁ z (by simp [C₁, hz]), hfix₂ z (by simp [C₂, hz])]
  let f' : C(ℝ, M) := ⟨d ∘ f, d.continuous.comp f.continuous⟩
  let g' : C(ℝ, M) := ⟨d ∘ g, d.continuous.comp g.continuous⟩
  refine ⟨f', g', d.contMDiff.comp hf, d.contMDiff.comp hg,
    (congrArg d hf0).trans hdx₀, hdf1, (congrArg d hg0).trans hdy₀, hdg1,
    d.toHomeomorph.isClosedEmbedding.comp hembf,
    d.toHomeomorph.isClosedEmbedding.comp hembg, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    change Injective (mfderiv 𝓘(ℝ, ℝ) I (d ∘ f) t)
    rw [mfderiv_comp t (d.contMDiff.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv d.toPartialDiffeomorph (mem_univ (f t))).1.comp (hif t ht)
  · intro t ht
    change Injective (mfderiv 𝓘(ℝ, ℝ) I (d ∘ g) t)
    rw [mfderiv_comp t (d.contMDiff.mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv d.toPartialDiffeomorph (mem_univ (g t))).1.comp (hig t ht)
  · apply disjoint_left.mpr
    rintro z ⟨t, rfl⟩ ⟨s, hs⟩
    exact hsep t t.property s s.property (d.injective hs.symm)
  · intro t ht hftS
    have heq : f t = f' t := d.injective (hdfix (f' t) hftS).symm
    exact (hfU t ht).2 (by simp [T, heq, hftS])
  · intro t ht hgtS
    have heq : g t = g' t := d.injective (hdfix (g' t) hgtS).symm
    exact (hgV t ht).2 (by simp [T, heq, hgtS])

end Wikipedia.HopfProblem.OrbitPair.SourceArcs

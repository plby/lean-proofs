import Wikipedia.SmoothSixDPoincare.BigonCollarGluing
import Wikipedia.SmoothSixDPoincare.OpenSubmanifoldDerivative

/-!
# The full clean embedded bigon from contractions in the codimension-two complement

Contract the inner boundary in the actual open complement, retain its full
germ under smooth embedding and obstacle avoidance, remove its intersections
with the whole collar, and glue back the original cornered boundary. The
result is a global smooth map with the original manifold as target, embedded
and immersive on the entire bigon and disjoint from both sheets in its interior.

Complement contractions remain an explicit intermediate hypothesis; deriving
them from the original handle geometry and proving the Whitney framing remain
separate obligations for the unconditional target.
-/

noncomputable section

open Set Function Topology ContinuousMap TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M D Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace Y] [ChartedSpace D Y] [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y]

/-- Contractions in the complement of the actual closed second sheet construct the full
clean embedded immersive bigon, including both original corner and strip germs. -/
theorem CleanBigonBoundary.exists_filled_bigon_of_complement_contractions
    (g : C(Y, M)) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (range g) T a b k l h)
    (hT : IsClosed T)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, (⟨Tᶜ, hT.isOpen_compl⟩ : Opens M)),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E)
    (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E) :
    ∃ f : C(ℝ × ℝ, M), ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f ∧
      IsClosedEmbedding (fun p : bigon h => f p) ∧
      (∀ p ∈ bigon h, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
      (∀ p ∈ interior (bigon h), f p ∉ range g ∪ T) ∧
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ frontier (bigon h) ⊆ V ∧ EqOn f d.map V := by
  let U : Opens M := ⟨Tᶜ, hT.isOpen_compl⟩
  have hU : (range g ∪ T)ᶜ ⊆ U := fun _ hp ht => hp (Or.inr ht)
  obtain ⟨r, hr, hcollar, F, hF, hemb, hi, havoid, havoidCollar, W, hW, hfrontW, hEq⟩ :=
    d.exists_collar_disjoint_inner_extension_in_open g hg U hU hnull hdim hobstacle
  let F' : C(ℝ × ℝ, M) := ⟨Subtype.val ∘ F,
    continuous_subtype_val.comp F.continuous⟩
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Subtype.val : U → M) :=
    contMDiff_subtype_val
  have hF' : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F' := hv.comp hF
  have hinjF' : InjOn F' (bigon h) := by
    intro p hp z hz heq
    have hFval : F p = F z := Subtype.ext heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) hFval)
  have hiF' : ∀ p ∈ bigon h, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F' p) := by
    intro p hp
    change Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Subtype.val ∘ F) p)
    rw [mfderiv_comp p (hv.mdifferentiableAt (by simp)) (hF.mdifferentiableAt (by simp))]
    exact (NativeOpenSubmanifold.injective_mfderiv_subtype_val U (F p)).comp (hi p hp)
  have havoidF' : ∀ p ∈ bigon h, F' p ∉ range g ∪ T := by
    intro p hp hmem
    rcases hmem with hmem | hmem
    · exact havoid p hp hmem
    · exact (F p).property hmem
  exact exists_filled_clean_bigon_of_collar_disjoint_inner d hr hcollar F' hF' hinjF' hiF'
    havoidF' havoidCollar hW hfrontW hEq

end Wikipedia.SmoothSixDPoincare

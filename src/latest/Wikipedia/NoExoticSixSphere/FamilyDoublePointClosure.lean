import Wikipedia.NoExoticSixSphere.FamilyEmbeddingTrack
import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity

/-!
# Diagonal limits of actual family double points are singular

An immersive slice has a locally injective parameter-retaining track.
This rules out collisions approaching its diagonal, even when nearby slices
are not globally injective. Thus the only new points in the closure of the
actual double-point locus lie at singular diagonal points.
-/

noncomputable section

open Function Set
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

def doublePoints (f : P → E → F) : Set (P × (E × E)) :=
  {q | q.2.1 ≠ q.2.2 ∧ f q.1 q.2.1 = f q.1 q.2.2}

theorem diagonal_not_mem_closure_doublePoints (f : P → E → F)
    (hf : ContDiff ℝ ∞ (uncurry f)) (t : P) (x : E)
    (hi : Injective (fderiv ℝ (f t) x)) :
    (t, (x, x)) ∉ closure (doublePoints f) := by
  have ht := (injective_fderiv_track_iff f hf t x).mpr hi
  obtain ⟨V, hV, hxV, _, hVi⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldImmersion.exists_open_injOn_of_injective_fderiv
      isOpen_univ (mem_univ (t, x)) (contDiff_track f hf).contDiffOn ht
  let W : Set (P × (E × E)) :=
    {q | (q.1, q.2.1) ∈ V ∧ (q.1, q.2.2) ∈ V}
  have hW : IsOpen W :=
    (hV.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).inter
      (hV.preimage (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  intro h
  obtain ⟨q, hqW, hq⟩ := (mem_closure_iff.mp h) W hW ⟨hxV, hxV⟩
  apply hq.1
  have he : track f (q.1, q.2.1) = track f (q.1, q.2.2) := Prod.ext rfl hq.2
  exact congrArg Prod.snd (hVi hqW.1 hqW.2 he)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem closure_doublePoints_equal_image (f : P → E → F)
    (hf : ContDiff ℝ ∞ (uncurry f)) {q : P × (E × E)}
    (hq : q ∈ closure (doublePoints f)) : f q.1 q.2.1 = f q.1 q.2.2 := by
  have hc : IsClosed {q : P × (E × E) | f q.1 q.2.1 = f q.1 q.2.2} :=
    isClosed_eq
      (hf.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
      (hf.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  exact (closure_minimal (fun _ h ↦ h.2) hc) hq

theorem closure_doublePoints_subset (f : P → E → F)
    (hf : ContDiff ℝ ∞ (uncurry f)) :
    closure (doublePoints f) ⊆ doublePoints f ∪
      {q | q.2.1 = q.2.2 ∧ ¬ Injective (fderiv ℝ (f q.1) q.2.1)} := by
  intro q hq
  by_cases he : q.2.1 = q.2.2
  · right
    refine ⟨he, ?_⟩
    intro hi
    have h := diagonal_not_mem_closure_doublePoints f hf q.1 q.2.1 hi
    apply h
    have hdiag : q = (q.1, (q.2.1, q.2.1)) := by
      exact Prod.ext rfl (Prod.ext rfl he.symm)
    rwa [← hdiag]
  · exact Or.inl ⟨he, closure_doublePoints_equal_image f hf hq⟩

end NoExoticSixSphere.FamilyEmbedding

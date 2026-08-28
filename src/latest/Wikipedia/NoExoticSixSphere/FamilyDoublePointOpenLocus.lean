import Wikipedia.NoExoticSixSphere.UnorderedFamilyDoublePoints
import Wikipedia.NoExoticSixSphere.InvolutionQuotientTopology

/-!
# The off-diagonal locus is open in the actual double-point closure

Continuity of the original family preserves the same-image equation under
closure. Consequently the old double-point subtype is an open subspace of
its closure, precisely the complement of the diagonal there. The diagonal
orbit set is closed in the genuine unordered quotient.
-/

open Set Function Topology

namespace NoExoticSixSphere.FamilyEmbedding

open InvolutionQuotient

variable {P E F : Type*} [TopologicalSpace P] [TopologicalSpace E]

def orderedInclusion (f : P → E → F) : doublePoints f → closure (doublePoints f) :=
  inclusion subset_closure

theorem closure_doublePoints_equal_image_of_continuous [TopologicalSpace F] [T2Space F]
    (f : P → E → F) (hf : Continuous (uncurry f))
    {q : P × (E × E)} (hq : q ∈ closure (doublePoints f)) :
    f q.1 q.2.1 = f q.1 q.2.2 := by
  have heq : IsClosed {q : P × (E × E) | f q.1 q.2.1 = f q.1 q.2.2} :=
    isClosed_eq (hf.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
      (hf.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  exact closure_minimal (fun _ hy ↦ hy.2) heq hq

theorem isOpenEmbedding_orderedInclusion [T2Space E] [TopologicalSpace F] [T2Space F]
    (f : P → E → F) (hf : Continuous (uncurry f)) :
    IsOpenEmbedding (orderedInclusion f) := by
  apply IsOpenEmbedding.inclusion subset_closure
  have heq : IsClosed {q : P × (E × E) | f q.1 q.2.1 = f q.1 q.2.2} :=
    isClosed_eq (hf.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
      (hf.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  have he : (Subtype.val ⁻¹' doublePoints f) =
      {q : closure (doublePoints f) | q.val.2.1 ≠ q.val.2.2} := by
    ext q
    constructor
    · exact fun h ↦ h.1
    · intro h
      exact ⟨h, closure_minimal (fun _ hy ↦ hy.2) heq q.property⟩
  rw [he]
  exact (isClosed_eq
    (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
    (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))).isOpen_compl

def diagonalOrbits (f : P → E → F) : Set (UnorderedClosedDoublePoints f) :=
  unorderedProj f '' {r : closure (doublePoints f) | r.val.2.1 = r.val.2.2}

theorem diagonalOrbits_eq_fixed (f : P → E → F) :
    diagonalOrbits f = unorderedProj f '' {r | swapClosure f r = r} := by
  unfold diagonalOrbits
  congr 1
  ext r
  exact (swapClosure_fixed_iff f r).symm

theorem mem_diagonalOrbits_iff (f : P → E → F) (r : closure (doublePoints f)) :
    unorderedProj f r ∈ diagonalOrbits f ↔ r.val.2.1 = r.val.2.2 := by
  rw [diagonalOrbits_eq_fixed]
  exact (mem_fixed_orbits_iff (swapClosure f) (swapClosure_involutive f) r).trans
    (swapClosure_fixed_iff f r)

theorem isClosed_diagonalOrbits [T2Space P] [T2Space E] (f : P → E → F) :
    IsClosed (diagonalOrbits f) := by
  rw [diagonalOrbits_eq_fixed]
  exact isClosed_fixed_orbits (swapClosure f) (swapClosure_involutive f)
    (swapClosure f).continuous

theorem t2Space_unordered [T2Space P] [T2Space E] (f : P → E → F) :
    T2Space (UnorderedClosedDoublePoints f) :=
  t2Space_orbit (swapClosure f) (swapClosure_involutive f) (swapClosure f).continuous

theorem secondCountable_unordered [SecondCountableTopology P] [SecondCountableTopology E]
    (f : P → E → F) : SecondCountableTopology (UnorderedClosedDoublePoints f) :=
  secondCountable_orbit (swapClosure f) (swapClosure_involutive f) (swapClosure f).continuous

end NoExoticSixSphere.FamilyEmbedding

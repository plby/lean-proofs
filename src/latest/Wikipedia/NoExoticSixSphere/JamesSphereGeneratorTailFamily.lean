import Wikipedia.NoExoticSixSphere.JamesSphereOverlapPaths
import Wikipedia.NoExoticSixSphere.JamesSphereTimeSeparation
import Wikipedia.NoExoticSixSphere.EndingPathLoopAppend

/-!
# The continuous family of generator tails followed by loops

The initial point moves along the actual sphere generator. At the middle
time this is exactly the inverse of the proved overlap-path equivalence.
At zero it is full generator concatenation, and at one it has a constant
prefix. These are equalities of the original compact-open ending paths.
-/

noncomputable section

open scoped unitInterval ContinuousMap

namespace NoExoticSixSphere.JamesSphere

abbrev LoopParameter (n : ℕ) :=
  Sphere n × Path (spherePole (n + 1)) (spherePole (n + 1))

def loopProjection (n : ℕ) : C(LoopParameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  ⟨Prod.snd, continuous_snd⟩

def generatorAction (n : ℕ) : C(LoopParameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  ⟨fun p ↦ (unitLoop n p.1).trans p.2,
    ((continuous_unitLoop n).comp continuous_fst).path_trans continuous_snd⟩

def generatorTailFamily (n : ℕ) : C(I × LoopParameter n, EndingPath.Space (spherePole (n + 1))) :=
  ⟨fun p ↦ EndingPath.append
    (EndingPath.shorten p.1 (EndingPath.ofPath (unitLoop n p.2.1))) p.2.2, by
    have hg : Continuous (fun p : I × LoopParameter n ↦
        EndingPath.ofPath (unitLoop n p.2.1)) :=
      EndingPath.continuous_ofPath.comp
        ((continuous_unitLoop n).comp (continuous_fst.comp continuous_snd))
    have hs : Continuous (fun p : I × LoopParameter n ↦
        EndingPath.shorten p.1 (EndingPath.ofPath (unitLoop n p.2.1))) :=
      EndingPath.continuous_shorten.comp (continuous_fst.prodMk hg)
    exact EndingPath.continuous_append.comp
      (hs.prodMk (continuous_snd.comp continuous_snd))⟩

theorem generatorTailFamily_source (n : ℕ) (a : I) (p : LoopParameter n) :
    EndingPath.source (spherePole (n + 1)) (generatorTailFamily n (a, p)) =
      loopEvaluation n (p.1, a) := by
  change EndingPath.source _ (EndingPath.append
    (EndingPath.shorten a (EndingPath.ofPath (unitLoop n p.1))) p.2) = _
  rw [EndingPath.append_source, EndingPath.shorten_source]
  rfl

theorem generatorTailFamily_zero (n : ℕ) (p : LoopParameter n) :
    generatorTailFamily n (0, p) = EndingPath.ofPath (generatorAction n p) := by
  change EndingPath.append (EndingPath.shorten 0 (EndingPath.ofPath (unitLoop n p.1))) p.2 = _
  rw [EndingPath.shorten_zero, EndingPath.append_ofPath]
  rfl

theorem generatorTailFamily_one (n : ℕ) (p : LoopParameter n) :
    generatorTailFamily n (1, p) = EndingPath.ofPath (EndingPath.constantPrefix p.2) := by
  change EndingPath.append (EndingPath.shorten 1 (EndingPath.ofPath (unitLoop n p.1))) p.2 = _
  rw [EndingPath.shorten_one]
  rfl

theorem generatorTailFamily_middle (n : ℕ) (p : LoopParameter n) :
    generatorTailFamily n (middleTime, p) = ((Overlap.loopProductEquiv n).symm p).val := by
  let γ : Path (middle n p.1) (spherePole (n + 1)) :=
    (middleNullhomotopy n).toHomotopy.evalAt p.1
  have he : EndingPath.shorten middleTime (EndingPath.ofPath (unitLoop n p.1)) =
      EndingPath.ofPath γ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change unitLoop n p.1 (EndingPath.remainingTime middleTime t) =
      unitLoop n p.1 (Set.Icc.convexComb middleTime 1 t)
    rw [EndingPath.remainingTime_convexComb]
  change EndingPath.append (EndingPath.shorten middleTime
    (EndingPath.ofPath (unitLoop n p.1))) p.2 = _
  rw [he, EndingPath.append_ofPath]
  apply Subtype.ext
  exact (Overlap.loopProductEquiv_symm_curve n p.1 p.2).symm

end NoExoticSixSphere.JamesSphere

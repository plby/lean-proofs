import Wikipedia.NoExoticSixSphere.ManifoldAffinePairDomain

/-!
# Actual three-source-chart domains and two target differences

The intersection of three genuine pair domains records three distinct source
points, one common target chart, and the original tubular domain. There is
no use of global continuity of a partial chart outside its domain.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TripleParameters

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding ManifoldAffineSphereFamily

abbrev TripleCoordinates := ℝ × (Vector 3 × Vector 3 × Vector 3)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)

def triplePair01 (q : Parameters e × TripleCoordinates) :
    Parameters e × (ℝ × (Vector 3 × Vector 3)) := (q.1, q.2.1, q.2.2.1, q.2.2.2.1)

def triplePair02 (q : Parameters e × TripleCoordinates) :
    Parameters e × (ℝ × (Vector 3 × Vector 3)) := (q.1, q.2.1, q.2.2.1, q.2.2.2.2)

def triplePair12 (q : Parameters e × TripleCoordinates) :
    Parameters e × (ℝ × (Vector 3 × Vector 3)) := (q.1, q.2.1, q.2.2.2.1, q.2.2.2.2)

theorem contDiff_triplePair01 : ContDiff ℝ ∞ (triplePair01 e) := by unfold triplePair01; fun_prop

theorem contDiff_triplePair02 : ContDiff ℝ ∞ (triplePair02 e) := by unfold triplePair02; fun_prop

theorem contDiff_triplePair12 : ContDiff ℝ ∞ (triplePair12 e) := by unfold triplePair12; fun_prop

def tripleDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (a b c : SourceChart) (d : TargetChart n M) : Opens (Parameters e × TripleCoordinates) :=
  ⟨triplePair01 e ⁻¹' (pairDomain e r f hf a b d : Set _) ∩
      (triplePair02 e ⁻¹' (pairDomain e r f hf a c d : Set _) ∩
       triplePair12 e ⁻¹' (pairDomain e r f hf b c d : Set _)),
    ((pairDomain e r f hf a b d).isOpen.preimage (contDiff_triplePair01 e).continuous).inter
      (((pairDomain e r f hf a c d).isOpen.preimage (contDiff_triplePair02 e).continuous).inter
        ((pairDomain e r f hf b c d).isOpen.preimage (contDiff_triplePair12 e).continuous))⟩

def tripleChartDifference (a b c : SourceChart) (d : TargetChart n M)
    (q : Parameters e × TripleCoordinates) : Vector n × Vector n :=
  (chartDifference e r f a b d (triplePair01 e q),
    chartDifference e r f a c d (triplePair02 e q))

theorem contDiffOn_tripleChartDifference
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (a b c : SourceChart) (d : TargetChart n M) :
    ContDiffOn ℝ ∞ (tripleChartDifference e r f a b c d) (tripleDomain e r f hf a b c d) :=
  ((contDiffOn_chartDifference e r f hf a b d).comp (contDiff_triplePair01 e).contDiffOn
    (fun _ hq ↦ hq.1)).prodMk
      ((contDiffOn_chartDifference e r f hf a c d).comp (contDiff_triplePair02 e).contDiffOn
        (fun _ hq ↦ hq.2.1))

theorem tripleChartDifference_zero_iff
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (a b c : SourceChart) (d : TargetChart n M) (q : Parameters e × TripleCoordinates)
    (hq : q ∈ tripleDomain e r f hf a b c d) :
    tripleChartDifference e r f a b c d q = 0 ↔
      map e r f q.1 q.2.1 (a.symm q.2.2.1) = map e r f q.1 q.2.1 (b.symm q.2.2.2.1) ∧
      map e r f q.1 q.2.1 (a.symm q.2.2.1) = map e r f q.1 q.2.1 (c.symm q.2.2.2.2) := by
  have h₁ := chartDifference_zero_iff e r f hf a b d (triplePair01 e q) hq.1
  have h₂ := chartDifference_zero_iff e r f hf a c d (triplePair02 e q) hq.2.1
  constructor
  · intro h
    exact ⟨h₁.mp (congrArg Prod.fst h), h₂.mp (congrArg Prod.snd h)⟩
  · rintro ⟨h, h'⟩
    exact Prod.ext (h₁.mpr h) (h₂.mpr h')

end Wikipedia.HopfProblem.DegreeCollapse.TripleParameters

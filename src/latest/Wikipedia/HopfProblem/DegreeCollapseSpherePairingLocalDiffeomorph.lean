import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteRepresentative

/-!
# The original sphere pairing is a local diffeomorphism on its finite locus

The source retains the product of the two original sphere atlases. The
Euclidean product chart is only an intermediate chart, not a new source atlas.
-/

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SpherePairingLocalDiffeomorph

open NoExoticSixSphere FiniteSphereProductCharts SphereFiniteRepresentative

def sourcePairChart (n : ℕ) :
    PartialDiffeomorph ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, V n × V n)
      (Sphere n × Sphere n) (V n × V n) ∞ where
  toPartialEquiv := ((sphereProjection n).prod (sphereProjection n)).toPartialEquiv
  open_source := (sphereProjection n).open_source.prod (sphereProjection n).open_source
  open_target := (sphereProjection n).open_target.prod (sphereProjection n).open_target
  contMDiffOn_toFun :=
    ((sphereProjectionDiffeomorph n).contMDiffOn_toFun.comp contMDiffOn_fst
      (fun _ hp ↦ hp.1)).prodMk_space
    ((sphereProjectionDiffeomorph n).contMDiffOn_toFun.comp contMDiffOn_snd
      (fun _ hp ↦ hp.2))
  contMDiffOn_invFun :=
    (((point_contMDiff n).comp
      (ContinuousLinearMap.fst ℝ (V n) (V n)).contDiff.contMDiff).prodMk
      ((point_contMDiff n).comp
        (ContinuousLinearMap.snd ℝ (V n) (V n)).contDiff.contMDiff)).contMDiffOn

theorem sourcePairChart_source (n : ℕ) :
    (sourcePairChart n).source = {spherePole n}ᶜ ×ˢ {spherePole n}ᶜ := by
  change (sphereProjection n).source ×ˢ (sphereProjection n).source = _
  rw [sphereProjection_source]

theorem sourcePairChart_target (n : ℕ) : (sourcePairChart n).target = univ := by
  change (sphereProjection n).target ×ˢ (sphereProjection n).target = _
  rw [sphereProjection_target, univ_prod_univ]

theorem sourcePairChart_apply (n : ℕ) (p : Sphere n × Sphere n) :
    sourcePairChart n p = (sphereProjection n p.1, sphereProjection n p.2) := rfl

theorem sourcePairChart_symm_apply (n : ℕ) (p : V n × V n) :
    (sourcePairChart n).symm p = (point n p.1, point n p.2) := rfl

def pairingChart (n : ℕ) :
    PartialDiffeomorph ((𝓡 n).prod (𝓡 n)) (𝓡 (n + n))
      (Sphere n × Sphere n) (Sphere (n + n)) ∞ :=
  (sourcePairChart n).trans (pairChart n).symm

theorem pairingChart_source (n : ℕ) :
    (pairingChart n).source = {spherePole n}ᶜ ×ˢ {spherePole n}ᶜ := by
  ext p
  change (p ∈ (sourcePairChart n).source ∧ sourcePairChart n p ∈ (pairChart n).target) ↔ _
  rw [sourcePairChart_source, pairChart, chart_target]
  simp only [mem_univ, and_true]

theorem pairingChart_apply (n : ℕ) (p : Sphere n × Sphere n) :
    pairingChart n p = (pairChart n).symm
      (sphereProjection n p.1, sphereProjection n p.2) := rfl

theorem pairing_isLocalDiffeomorphAt (n : ℕ) {p : Sphere n × Sphere n}
    (hx : p.1 ≠ spherePole n) (hy : p.2 ≠ spherePole n) :
    IsLocalDiffeomorphAt ((𝓡 n).prod (𝓡 n)) (𝓡 (n + n)) ∞
      (JamesSphere.pairing n) p := by
  refine ⟨pairingChart n, ?_, ?_⟩
  · simpa only [pairingChart_source, mem_prod, mem_compl_iff, mem_singleton_iff]
      using And.intro hx hy
  · intro q hq
    have h : q.1 ≠ spherePole n ∧ q.2 ≠ spherePole n := by
      simpa only [pairingChart_source, mem_prod, mem_compl_iff, mem_singleton_iff] using hq
    exact pairing_finite n h.1 h.2

theorem pairing_contMDiffAt (n : ℕ) {p : Sphere n × Sphere n}
    (hx : p.1 ≠ spherePole n) (hy : p.2 ≠ spherePole n) :
    ContMDiffAt ((𝓡 n).prod (𝓡 n)) (𝓡 (n + n)) ∞ (JamesSphere.pairing n) p :=
  (pairing_isLocalDiffeomorphAt n hx hy).contMDiffAt

theorem pairing_mfderiv_bijective (n : ℕ) {p : Sphere n × Sphere n}
    (hx : p.1 ≠ spherePole n) (hy : p.2 ≠ spherePole n) :
    Function.Bijective (mfderiv ((𝓡 n).prod (𝓡 n)) (𝓡 (n + n))
      (JamesSphere.pairing n) p) :=
  ((pairing_isLocalDiffeomorphAt n hx hy).mfderivToContinuousLinearEquiv (by simp)).bijective

end Wikipedia.HopfProblem.DegreeCollapse.SpherePairingLocalDiffeomorph


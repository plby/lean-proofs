import Wikipedia.NoExoticSixSphere.PairedTubeCollapse
import Wikipedia.NoExoticSixSphere.CollapseAmbientEquiv
import Wikipedia.NoExoticSixSphere.CollapseFiberEquiv
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Actual paired tube collapse in Hilbert ambient and normal coordinates

Both product-coordinate homeomorphisms are explicit. The collapse identity
holds on the whole compactification, including the collapsed complement.
-/

noncomputable section

namespace NoExoticSixSphere.OpenFiberCollapse

variable {M N K L E F : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup L] [NormedSpace ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (τ : M × K → E) (σ : N × L → F)

def hilbertPairedTube (p : (M × N) × WithLp 2 (K × L)) : WithLp 2 (E × F) :=
  WithLp.toLp 2 (τ (p.1.1, p.2.fst), σ (p.1.2, p.2.snd))

theorem hilbertPairedTube_isOpenEmbedding
    (hτ : Topology.IsOpenEmbedding τ) (hσ : Topology.IsOpenEmbedding σ) :
    Topology.IsOpenEmbedding (hilbertPairedTube τ σ) := by
  let a := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toHomeomorph
  let b := (Homeomorph.refl (M × N)).prodCongr
    (WithLp.prodContinuousLinearEquiv 2 ℝ K L).toHomeomorph
  exact a.isOpenEmbedding.comp ((pairedTube_isOpenEmbedding τ σ hτ hσ).comp b.isOpenEmbedding)

theorem hilbertPairedTube_collapseOnePoint
    (hτ : Function.Injective τ) (hσ : Function.Injective σ) (z : OnePoint (E × F)) :
    collapseOnePoint (hilbertPairedTube τ σ)
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toHomeomorph.onePointCongr z) =
      (WithLp.prodContinuousLinearEquiv 2 ℝ K L).symm.toHomeomorph.onePointCongr
        (collapseOnePoint (pairedTube τ σ) z) := by
  let p := (WithLp.prodContinuousLinearEquiv 2 ℝ K L).toHomeomorph
  let τ' : (M × N) × WithLp 2 (K × L) → E × F := fun q ↦ pairedTube τ σ (q.1, p q.2)
  have hi : Function.Injective τ' := (pairedTube_injective τ σ hτ hσ).comp
    ((Homeomorph.refl (M × N)).prodCongr p).injective
  have ha := collapseOnePoint_ambientEquiv τ'
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toHomeomorph hi z
  have hb := collapseOnePoint_fiberEquiv (pairedTube τ σ) p.toEquiv
    (pairedTube_injective τ σ hτ hσ) z
  exact ha.trans hb

variable [CompactSpace M] [CompactSpace N]
  [LocallyCompactSpace E] [LocallyCompactSpace F]
  [LocallyCompactSpace K] [LocallyCompactSpace L]

theorem hilbertPairedTube_collapse_map
    (hτ : Topology.IsOpenEmbedding τ) (hσ : Topology.IsOpenEmbedding σ)
    (u : OnePoint E) (v : OnePoint F) :
    collapseOnePoint (hilbertPairedTube τ σ)
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toHomeomorph.onePointCongr
          (OnePointProduct.map (u, v))) =
      (WithLp.prodContinuousLinearEquiv 2 ℝ K L).symm.toHomeomorph.onePointCongr
        (OnePointProduct.map (collapseOnePoint τ u, collapseOnePoint σ v)) := by
  rw [hilbertPairedTube_collapseOnePoint τ σ hτ.injective hσ.injective,
    pairedTube_collapseOnePoint τ σ hτ hσ, OnePointProduct.productMap_apply]
  rfl

end NoExoticSixSphere.OpenFiberCollapse

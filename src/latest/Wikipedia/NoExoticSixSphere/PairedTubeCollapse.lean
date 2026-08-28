import Wikipedia.NoExoticSixSphere.ProductTubeCollapse

/-!
# The actual collapse of two independent tubes

Both base manifolds and both ordered normal factors are retained. After
the explicit middle-factor interchange, the collapse of the product tube
is exactly the descended product of the two original collapses.
-/

noncomputable section

open Set Function Topology
open scoped OnePoint

namespace NoExoticSixSphere.OpenFiberCollapse

variable {M N K L Y Z : Type*} (τ : M × K → Y) (σ : N × L → Z)

def pairedTube (p : (M × N) × (K × L)) : Y × Z :=
  (τ (p.1.1, p.2.1), σ (p.1.2, p.2.2))

theorem pairedTube_injective (hτ : Injective τ) (hσ : Injective σ) :
    Injective (pairedTube τ σ) := by
  rintro ⟨⟨m, n⟩, k, l⟩ ⟨⟨m', n'⟩, k', l'⟩ h
  have hm : (m, k) = (m', k') := hτ (congrArg Prod.fst h)
  have hn : (n, l) = (n', l') := hσ (congrArg Prod.snd h)
  exact Prod.ext
    (Prod.ext (congrArg (fun p : M × K ↦ p.1) hm) (congrArg (fun p : N × L ↦ p.1) hn))
    (Prod.ext (congrArg (fun p : M × K ↦ p.2) hm) (congrArg (fun p : N × L ↦ p.2) hn))

theorem pairedTube_mem_range_iff (y : Y) (z : Z) :
    (y, z) ∈ range (pairedTube τ σ) ↔ y ∈ range τ ∧ z ∈ range σ := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨⟨(p.1.1, p.2.1), congrArg Prod.fst hp⟩,
      ⟨(p.1.2, p.2.2), congrArg Prod.snd hp⟩⟩
  · rintro ⟨⟨⟨m, k⟩, rfl⟩, ⟨⟨n, l⟩, rfl⟩⟩
    exact ⟨((m, n), (k, l)), rfl⟩

variable [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace Y] [TopologicalSpace Z]

theorem pairedTube_isOpenEmbedding (hτ : IsOpenEmbedding τ) (hσ : IsOpenEmbedding σ) :
    IsOpenEmbedding (pairedTube τ σ) :=
  (hτ.prodMap hσ).comp (Homeomorph.prodProdProdComm M N K L).isOpenEmbedding

variable [CompactSpace M] [CompactSpace N]
  [T2Space Y] [LocallyCompactSpace Y] [T2Space Z] [LocallyCompactSpace Z]
  [T2Space K] [LocallyCompactSpace K] [T2Space L] [LocallyCompactSpace L]
  (hτ : IsOpenEmbedding τ) (hσ : IsOpenEmbedding σ)

theorem pairedTube_collapseOnePoint (p : OnePoint (Y × Z)) :
    collapseOnePoint (pairedTube τ σ) p =
      OnePointProduct.productMap
        ⟨collapseOnePoint τ, continuous_collapseOnePoint τ hτ⟩
        ⟨collapseOnePoint σ, continuous_collapseOnePoint σ hσ⟩
        (collapseOnePoint_infty τ) (collapseOnePoint_infty σ) p := by
  induction p using OnePoint.rec with
  | infty => rw [collapseOnePoint_infty, OnePointProduct.productMap_infty]
  | coe p =>
    rcases p with ⟨y, z⟩
    rw [OnePointProduct.productMap_coe]
    change collapseOnePoint (pairedTube τ σ) ((y, z) : OnePoint (Y × Z)) =
      OnePointProduct.map (collapseOnePoint τ (y : OnePoint Y),
        collapseOnePoint σ (z : OnePoint Z))
    by_cases hy : y ∈ range τ
    · by_cases hz : z ∈ range σ
      · obtain ⟨⟨m, k⟩, rfl⟩ := hy
        obtain ⟨⟨n, l⟩, rfl⟩ := hz
        have hleft : collapseOnePoint τ (τ (m, k) : OnePoint Y) = (k : OnePoint K) :=
          (collapseOnePoint_eq_coe_iff τ hτ.injective _ k).mpr ⟨m, rfl⟩
        have hright : collapseOnePoint σ (σ (n, l) : OnePoint Z) = (l : OnePoint L) :=
          (collapseOnePoint_eq_coe_iff σ hσ.injective _ l).mpr ⟨n, rfl⟩
        have hpair : collapseOnePoint (pairedTube τ σ)
            ((τ (m, k), σ (n, l)) : OnePoint (Y × Z)) = ((k, l) : OnePoint (K × L)) :=
          (collapseOnePoint_eq_coe_iff (pairedTube τ σ)
            (pairedTube_injective τ σ hτ.injective hσ.injective) _ (k, l)).mpr
              ⟨(m, n), rfl⟩
        rw [hleft, hright, hpair, OnePointProduct.map_coe]
      · have hnot : (y, z) ∉ range (pairedTube τ σ) :=
          fun h ↦ hz ((pairedTube_mem_range_iff τ σ y z).mp h).2
        rw [collapseOnePoint_coe_of_not_mem σ hz,
          collapseOnePoint_coe_of_not_mem (pairedTube τ σ) hnot,
          OnePointProduct.map_infty_right]
    · have hnot : (y, z) ∉ range (pairedTube τ σ) :=
        fun h ↦ hy ((pairedTube_mem_range_iff τ σ y z).mp h).1
      rw [collapseOnePoint_coe_of_not_mem τ hy,
        collapseOnePoint_coe_of_not_mem (pairedTube τ σ) hnot,
        OnePointProduct.map_infty_left]

theorem pairedTube_collapseMap :
    (⟨collapseOnePoint (pairedTube τ σ), continuous_collapseOnePoint (pairedTube τ σ)
      (pairedTube_isOpenEmbedding τ σ hτ hσ)⟩ :
        C(OnePoint (Y × Z), OnePoint (K × L))) =
      OnePointProduct.productMap
        ⟨collapseOnePoint τ, continuous_collapseOnePoint τ hτ⟩
        ⟨collapseOnePoint σ, continuous_collapseOnePoint σ hσ⟩
        (collapseOnePoint_infty τ) (collapseOnePoint_infty σ) := by
  ext p
  exact pairedTube_collapseOnePoint τ σ hτ hσ p

end NoExoticSixSphere.OpenFiberCollapse

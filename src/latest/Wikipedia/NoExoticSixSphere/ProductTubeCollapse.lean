import Wikipedia.NoExoticSixSphere.OnePointProductMap

/-!
# Adding a genuine normal factor commutes with the original tube collapse

The base manifold is unchanged. A product normal factor is added to the
open tube and to its ambient space. Its actual one-point collapse is exactly
the descended product of the old collapse and the identity on that factor.
This is an equality of continuous maps, not an identification of assigned
stable classes or an assumption about suspension.
-/

noncomputable section

open Set Function Topology
open scoped OnePoint

namespace NoExoticSixSphere.OpenFiberCollapse

variable {M K Y T : Type*} (τ : M × K → Y)

def productTube (p : M × (K × T)) : Y × T := (τ (p.1, p.2.1), p.2.2)

theorem productTube_injective (hτ : Injective τ) : Injective (productTube (T := T) τ) := by
  rintro ⟨m, k, t⟩ ⟨m', k', t'⟩ h
  have hmk : (m, k) = (m', k') := hτ (congrArg Prod.fst h)
  have ht : t = t' := congrArg Prod.snd h
  have hm : m = m' := congrArg (fun q : M × K ↦ q.1) hmk
  have hk : k = k' := congrArg (fun q : M × K ↦ q.2) hmk
  exact Prod.ext hm (Prod.ext hk ht)

theorem collapseOnePoint_coe_of_not_mem {y : Y} (hy : y ∉ range τ) :
    collapseOnePoint τ (y : OnePoint Y) = ∞ := by
  apply collapse_of_not_mem
  rintro ⟨p, hp⟩
  exact hy ⟨p, OnePoint.coe_injective hp⟩

variable [TopologicalSpace M] [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace T]

theorem productTube_isOpenEmbedding (hτ : IsOpenEmbedding τ) :
    IsOpenEmbedding (productTube (T := T) τ) :=
  (hτ.prodMap (Homeomorph.refl T).isOpenEmbedding).comp
    (Homeomorph.prodAssoc M K T).symm.isOpenEmbedding

variable [CompactSpace M] [T2Space Y] [LocallyCompactSpace Y]
  [T2Space K] [LocallyCompactSpace K] [T2Space T] [LocallyCompactSpace T]
  (hτ : IsOpenEmbedding τ)

theorem productTube_collapseOnePoint (z : OnePoint (Y × T)) :
    collapseOnePoint (productTube τ) z =
      OnePointProduct.productMap
        ⟨collapseOnePoint τ, continuous_collapseOnePoint τ hτ⟩
        (ContinuousMap.id (OnePoint T)) (collapseOnePoint_infty τ)
        (ContinuousMap.id_apply ∞) z := by
  induction z using OnePoint.rec with
  | infty => rw [collapseOnePoint_infty, OnePointProduct.productMap_infty]
  | coe p =>
    rcases p with ⟨y, t⟩
    rw [OnePointProduct.productMap_coe]
    change collapseOnePoint (productTube τ) ((y, t) : OnePoint (Y × T)) =
      OnePointProduct.map (collapseOnePoint τ (y : OnePoint Y), (t : OnePoint T))
    by_cases hy : y ∈ range τ
    · obtain ⟨⟨m, k⟩, rfl⟩ := hy
      have hold : collapseOnePoint τ (τ (m, k) : OnePoint Y) = (k : OnePoint K) :=
        (collapseOnePoint_eq_coe_iff τ hτ.injective _ k).mpr ⟨m, rfl⟩
      have hnew : collapseOnePoint (productTube τ)
          ((τ (m, k), t) : OnePoint (Y × T)) = ((k, t) : OnePoint (K × T)) :=
        (collapseOnePoint_eq_coe_iff (productTube τ)
          (productTube_injective τ hτ.injective) _ (k, t)).mpr ⟨m, rfl⟩
      rw [hold, hnew, OnePointProduct.map_coe]
    · have hnot : (y, t) ∉ range (productTube τ) := by
        rintro ⟨p, hp⟩
        exact hy ⟨(p.1, p.2.1), congrArg Prod.fst hp⟩
      rw [collapseOnePoint_coe_of_not_mem τ hy,
        collapseOnePoint_coe_of_not_mem (productTube τ) hnot,
        OnePointProduct.map_infty_left]

theorem productTube_collapseMap :
    (⟨collapseOnePoint (productTube τ), continuous_collapseOnePoint (productTube τ)
      (productTube_isOpenEmbedding τ hτ)⟩ : C(OnePoint (Y × T), OnePoint (K × T))) =
      OnePointProduct.productMap
        ⟨collapseOnePoint τ, continuous_collapseOnePoint τ hτ⟩
        (ContinuousMap.id (OnePoint T)) (collapseOnePoint_infty τ)
        (ContinuousMap.id_apply ∞) := by
  ext z
  exact productTube_collapseOnePoint τ hτ z

end NoExoticSixSphere.OpenFiberCollapse

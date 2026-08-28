import Wikipedia.HopfProblem.OrbitPairRealizationSubcomplexSupport
import Wikipedia.HopfProblem.OrbitPairRealizationPointFibres

/-!
# Realized subcomplex inclusions are closed embeddings

The preimage of an image of a closed subset is expressed, in each
characteristic simplex, as a finite union of compact geometric face
images. Combined with the native weak topology and injectivity, this
proves the actual closed-embedding property.
-/

noncomputable section

open CategoryTheory Simplicial Topology

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable {S : SSet} (A : S.Subcomplex)

def subcomplexImagePiece (n : ℕ) (x : S _⦋n⦌)
    (F : Set (SSet.toTop.obj A.toSSet)) (a : FaceIndex n) : Set (Simplex n) := by
  classical
  exact if h : S.map a.2.op x ∈ A.obj (Opposite.op ⦋a.1.val⦌) then
    (SimplexCategory.toTop₀.map a.2).hom ''
      (characteristic A.toSSet a.1.val ⟨S.map a.2.op x, h⟩ ⁻¹' F)
  else ∅

theorem isClosed_subcomplexImagePiece (n : ℕ) (x : S _⦋n⦌)
    (F : Set (SSet.toTop.obj A.toSSet)) (hF : IsClosed F) (a : FaceIndex n) :
    IsClosed (subcomplexImagePiece A n x F a) := by
  classical
  unfold subcomplexImagePiece
  split_ifs with ha
  · let f : C(Simplex a.1.val, Simplex n) := (SimplexCategory.toTop₀.map a.2).hom
    have hc := hF.preimage (characteristic A.toSSet a.1.val ⟨S.map a.2.op x, ha⟩).continuous
    exact (hc.isCompact.image f.continuous).isClosed
  · exact isClosed_empty

theorem characteristic_subcomplex_image (n : ℕ) (x : S _⦋n⦌)
    (F : Set (SSet.toTop.obj A.toSSet)) :
    characteristic S n x ⁻¹' ((SSet.toTop.map A.ι) '' F) =
      ⋃ a : FaceIndex n, subcomplexImagePiece A n x F a := by
  classical
  ext t
  constructor
  · rintro ⟨u, hu, he⟩
    let a := SimplexSupport.face n t
    have hd : a.dim < n + 1 := Nat.lt_succ_of_le (SimplexCategory.len_le_of_mono a.inclusion)
    have ha := support_simplex_mem A n x t a ⟨u, he⟩
    refine Set.mem_iUnion.mpr ⟨⟨⟨a.dim, hd⟩, a.inclusion⟩, ?_⟩
    rw [subcomplexImagePiece, dif_pos ha]
    refine ⟨a.point, ?_, a.map_point⟩
    have he' : characteristic A.toSSet a.dim ⟨S.map a.inclusion.op x, ha⟩ a.point = u :=
      realizedMap_injective A.ι ((subcomplex_support_characteristic A n x t a ha).trans he.symm)
    change characteristic A.toSSet a.dim ⟨S.map a.inclusion.op x, ha⟩ a.point ∈ F
    rwa [he']
  · intro ht
    obtain ⟨a, ht⟩ := Set.mem_iUnion.mp ht
    by_cases ha : S.map a.2.op x ∈ A.obj (Opposite.op ⦋a.1.val⦌)
    · rw [subcomplexImagePiece, dif_pos ha] at ht
      obtain ⟨s, hs, hst⟩ := ht
      refine ⟨characteristic A.toSSet a.1.val ⟨S.map a.2.op x, ha⟩ s, hs, ?_⟩
      have hc := congrArg (fun f : C(Simplex a.1.val, SSet.toTop.obj S) ↦ f s)
        (characteristic_map S a.1.val n a.2 x)
      exact (realizedMap_characteristic A.ι a.1.val ⟨S.map a.2.op x, ha⟩ s).trans
        (hc.trans (congrArg (characteristic S n x) hst))
    · rw [subcomplexImagePiece, dif_neg ha] at ht
      exact False.elim ht

theorem isClosedMap_realizedSubcomplex : IsClosedMap (SSet.toTop.map A.ι) := by
  intro F hF
  apply (isClosed_iff_characteristic S _).mpr
  intro n x
  rw [characteristic_subcomplex_image A n x F]
  exact isClosed_iUnion_of_finite (fun a ↦ isClosed_subcomplexImagePiece A n x F hF a)

theorem isClosedEmbedding_realizedSubcomplex : IsClosedEmbedding (SSet.toTop.map A.ι) :=
  .of_continuous_injective_isClosedMap (SSet.toTop.map A.ι).hom.continuous
    (realizedMap_injective A.ι) (isClosedMap_realizedSubcomplex A)

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

import Wikipedia.HopfProblem.OrbitPairRealizationNormalParameters

/-!
# Closed point-fibres in native geometric realization

In a characteristic n-simplex, a point-fibre is a finite union of compact
geometric images of closed coordinate conditions. Closedness is checked
inside the standard simplex; no separation property of the realization is
assumed. The native weak topology then gives T1 separation.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable (S : SSet)

abbrev FaceIndex (n : ℕ) := Σ k : Fin (n + 1), (⦋k.val⦌ ⟶ ⦋n⦌)

def fibrePiece (n : ℕ) (x : S _⦋n⦌) (z : SSet.toTop.obj S) (a : FaceIndex n) :
    Set (Simplex n) :=
  (SimplexCategory.toTop₀.map a.2).hom ''
    {s | coreParameters S a.1.val (S.map a.2.op x) s = normalParameters S z}

theorem isClosed_fibrePiece (n : ℕ) (x : S _⦋n⦌) (z : SSet.toTop.obj S)
    (a : FaceIndex n) : IsClosed (fibrePiece S n x z a) := by
  have hc := (isClosed_singleton : IsClosed ({normalParameters S z} : Set (Parameters S))).preimage
    (coreParameterMap S a.1.val (S.map a.2.op x)).continuous
  let f : C(Simplex a.1.val, Simplex n) := (SimplexCategory.toTop₀.map a.2).hom
  have hi : IsCompact (fibrePiece S n x z a) := hc.isCompact.image f.continuous
  exact hi.isClosed

theorem characteristic_point_fibre (n : ℕ) (x : S _⦋n⦌) (z : SSet.toTop.obj S) :
    characteristic S n x ⁻¹' {z} = ⋃ a : FaceIndex n, fibrePiece S n x z a := by
  ext t
  constructor
  · intro ht
    have ht' : characteristic S n x t = z := ht
    let a := SimplexSupport.face n t
    have hd : a.dim < n + 1 := Nat.lt_succ_of_le (SimplexCategory.len_le_of_mono a.inclusion)
    refine Set.mem_iUnion.mpr ⟨⟨⟨a.dim, hd⟩, a.inclusion⟩, ?_⟩
    refine ⟨a.point, ?_, a.map_point⟩
    change coreParameters S a.dim (S.map a.inclusion.op x) a.point = normalParameters S z
    have hn : normalize S ⟨⟨n, x⟩, t⟩ = normalParameters S z := by
      rw [normalize_eq_normalParameters, projection_apply, ht']
    rwa [normalize_eq_face S n x t a] at hn
  · intro ht
    obtain ⟨a, s, hs, hst⟩ := Set.mem_iUnion.mp ht
    have hp := congrArg (projection S) hs
    have hp' : characteristic S a.1.val (S.map a.2.op x) s = z :=
      (coreParameters_projection S a.1.val (S.map a.2.op x) s).symm.trans
        (hp.trans (projection_normalParameters S z))
    have hc := congrArg (fun f : C(Simplex a.1.val, SSet.toTop.obj S) ↦ f s)
      (characteristic_map S a.1.val n a.2 x)
    change characteristic S n x t = z
    exact (congrArg (characteristic S n x) hst.symm).trans (hc.symm.trans hp')

theorem isClosed_characteristic_point_fibre (n : ℕ) (x : S _⦋n⦌)
    (z : SSet.toTop.obj S) : IsClosed (characteristic S n x ⁻¹' {z}) := by
  rw [characteristic_point_fibre]
  exact isClosed_iUnion_of_finite (fun a ↦ isClosed_fibrePiece S n x z a)

theorem isClosed_point (z : SSet.toTop.obj S) : IsClosed ({z} : Set (SSet.toTop.obj S)) :=
  (isClosed_iff_characteristic S {z}).mpr (fun n x ↦ isClosed_characteristic_point_fibre S n x z)

instance realizationT1 : T1Space (SSet.toTop.obj S) := ⟨isClosed_point S⟩

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

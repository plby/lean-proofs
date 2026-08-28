import Wikipedia.NoExoticSixSphere.SmallModTwoCap

/-!
# The boundary identity for cap localized to the actual subspace

The original small-chain inclusion commutes with the differential.
After applying the injective original subspace-chain inclusion, the
localized boundary identity is exactly the already proved ambient cap
boundary identity. Hence the identity holds in the actual subspace
chain group, with no chosen chain model.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.SmallModTwoCap

open ModTwoCapProduct (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The original small-simplex inclusion commutes with every native coefficient differential. -/
theorem boundary_smallInclusion (i j : ℕ) (c : SmallChains Coefficient U V i) :
    ((modComplex 2 X).d i j).hom (smallInclusionMap Coefficient U V i c) =
      smallInclusionMap Coefficient U V j (((complex U V).d i j).hom c) :=
  congrArg (fun m => m.hom c)
    (((SimplicialCoefficients.chains Coefficient).map
      (SingularSubcomplex.smallInclusion U V)).comm i j)

/-- The complete cap boundary formula holds in the original localized subspace chain group. -/
theorem boundary_capInDegree {p q n : ℕ} (h : p + q + 1 = n)
    (α : RelativeModTwoCochains.Cochain V p) (c : SmallChains Coefficient U V n) :
    ((modComplex 2 U).d (q + 1) q).hom
        (capInDegree U V (p := p) (q := q + 1) (n := n) (by omega) α c) =
      capInDegree U V (p := p) (q := q) rfl α (((complex U V).d n (p + q)).hom c) +
        capInDegree U V (p := p + 1) (q := q) (n := n) (by omega)
          (RelativeModTwoCochains.coboundary V α) c := by
  apply inclusion_injective U q
  have hi := congrArg (fun m => m.hom
    (capInDegree U V (p := p) (q := q + 1) (n := n) (by omega) α c))
    ((RelativeCoefficients.inclusion Coefficient U).comm (q + 1) q)
  apply hi.symm.trans
  apply (congrArg ((modComplex 2 X).d (q + 1) q).hom
    (inclusion_capInDegree U V (p := p) (q := q + 1) (n := n) (by omega) α c)).trans
  apply (ModTwoCapProduct.boundary_capInDegree h
    (RelativeModTwoCochains.toAbsolute V p α) (smallInclusionMap Coefficient U V n c)).trans
  have he₁ := inclusion_capInDegree U V (p := p) (q := q) rfl α
    (((complex U V).d n (p + q)).hom c)
  have he₂ := inclusion_capInDegree U V (p := p + 1) (q := q) (n := n) (by omega)
    (RelativeModTwoCochains.coboundary V α) c
  rw [boundary_smallInclusion U V n (p + q) c,
    ← RelativeModTwoCochains.toAbsolute_coboundary V p α]
  exact (congrArg₂ (fun x y => x + y) he₁.symm he₂.symm).trans
    (((RelativeCoefficients.inclusion Coefficient U).f q).hom.map_add _ _).symm

end NoExoticSixSphere.SmallModTwoCap

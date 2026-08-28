import Wikipedia.HopfProblem.DegreeCollapseSmallIntegralCap

/-!
# The signed boundary of original localized integral cap chains

Original small-chain and subspace inclusions commute with the
differentials. The injective original inclusion therefore transfers
the ambient signed cap formula to the actual subspace chain group.
When the lower cap is zero, the remaining factor is -(-1)^p.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCap

open FirstHurewicz SingularCohomologyCup

variable {X : Type} [TopologicalSpace X]

theorem capInDegree_sub {p q n : ℕ} (h : p + q = n) (α β : Cochain X p) :
    capInDegree h (α - β) = capInDegree h α - capInDegree h β := by
  apply eq_sub_iff_add_eq.mpr
  rw [← capInDegree_add, sub_add_cancel]

/-- The actual ambient boundary formula solved for the boundary of cap, retaining its sign. -/
theorem boundary_capInDegree {p q n : ℕ} (h : p + q + 1 = n)
    (α : Cochain X p) (c : Chains X n) :
    ((singularComplex X).d (q + 1) q).hom
        (capInDegree (p := p) (q := q + 1) (by omega) α c) =
      (-1 : ℤ) ^ p • capInDegree rfl α (((singularComplex X).d n (p + q)).hom c) -
        (-1 : ℤ) ^ p • capInDegree (p := p + 1) (q := q) (by omega) (coboundary α) c := by
  subst n
  have he := congrArg (fun z : Chains X q => (-1 : ℤ) ^ p • z) (cap_boundary p q α c)
  rw [zsmul_add, ← mul_zsmul, sign_mul_self, one_zsmul] at he
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans he.symm)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCap

namespace Wikipedia.HopfProblem.DegreeCollapse.SmallIntegralCap

open FirstHurewicz SingularMayerVietoris SingularCohomologyCup NoExoticSixSphere
open IntegralCap (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

theorem inclusion_boundary (i j : ℕ) (c : Chains U i) :
    inducedChain (subtypeInclusion U) j (((singularComplex U).d i j).hom c) =
      ((singularComplex X).d i j).hom (inducedChain (subtypeInclusion U) i c) :=
  (congrArg (fun m => m.hom c) ((RelativeSingularHomology.inclusion U).comm i j)).symm

theorem boundary_smallInclusion (i j : ℕ) (c : SmallChains Coefficient U V i) :
    ((singularComplex X).d i j).hom (smallInclusionMap Coefficient U V i c) =
      smallInclusionMap Coefficient U V j (((complex U V).d i j).hom c) :=
  congrArg (fun m => m.hom c)
    (((SimplicialCoefficients.chains Coefficient).map
      (SingularSubcomplex.smallInclusion U V)).comm i j)

/-- The original localized cap boundary has its full integer sign and subtraction. -/
theorem boundary_capInDegree {p q n : ℕ} (h : p + q + 1 = n)
    (α : RelativeIntegralCap.Cochain V p) (c : SmallChains Coefficient U V n) :
    ((singularComplex U).d (q + 1) q).hom
        (capInDegree U V (p := p) (q := q + 1) (n := n) (by omega) α c) =
      (-1 : ℤ) ^ p • capInDegree U V (p := p) (q := q) rfl α
          (((complex U V).d n (p + q)).hom c) -
        (-1 : ℤ) ^ p • capInDegree U V (p := p + 1) (q := q) (n := n) (by omega)
          (RelativeIntegralCap.coboundary V α) c := by
  let z : Chains X n := smallInclusionMap Coefficient U V n c
  let dz : Chains X (p + q) :=
    smallInclusionMap Coefficient U V (p + q) (((complex U V).d n (p + q)).hom c)
  apply inclusion_injective U q
  calc
    _ = ((singularComplex X).d (q + 1) q).hom
        (IntegralCap.capInDegree (p := p) (q := q + 1) (by omega)
          (RelativeIntegralCap.toAbsolute V p α) z) :=
      (inclusion_boundary U (q + 1) q
        (capInDegree U V (p := p) (q := q + 1) (by omega) α c)).trans
          (congrArg ((singularComplex X).d (q + 1) q).hom
            (inclusion_capInDegree U V (p := p) (q := q + 1) (by omega) α c))
    _ = (-1 : ℤ) ^ p • IntegralCap.capInDegree rfl (RelativeIntegralCap.toAbsolute V p α)
          (((singularComplex X).d n (p + q)).hom z) -
        (-1 : ℤ) ^ p • IntegralCap.capInDegree (p := p + 1) (q := q) (by omega)
          (coboundary (RelativeIntegralCap.toAbsolute V p α)) z :=
      IntegralCap.boundary_capInDegree h (RelativeIntegralCap.toAbsolute V p α) z
    _ = (-1 : ℤ) ^ p • IntegralCap.capInDegree rfl (RelativeIntegralCap.toAbsolute V p α) dz -
        (-1 : ℤ) ^ p • IntegralCap.capInDegree (p := p + 1) (q := q) (by omega)
          (RelativeIntegralCap.toAbsolute V (p + 1) (RelativeIntegralCap.coboundary V α)) z :=
      congrArg₂ (fun x y => (-1 : ℤ) ^ p • x - (-1 : ℤ) ^ p • y)
        (congrArg (IntegralCap.capInDegree (q := q) rfl (RelativeIntegralCap.toAbsolute V p α))
          (boundary_smallInclusion U V n (p + q) c))
        (congrArg (fun β => IntegralCap.capInDegree (p := p + 1) (q := q) (by omega) β z)
          (RelativeIntegralCap.toAbsolute_coboundary V p α).symm)
    _ = _ := by
      rw [map_sub, map_zsmul, map_zsmul]
      exact congrArg₂ (fun x y => (-1 : ℤ) ^ p • x - (-1 : ℤ) ^ p • y)
        (inclusion_capInDegree U V (p := p) (q := q) rfl α
          (((complex U V).d n (p + q)).hom c)).symm
        (inclusion_capInDegree U V (p := p + 1) (q := q) (by omega)
          (RelativeIntegralCap.coboundary V α) c).symm

/-- Killing the lower cap leaves precisely the signed coboundary cap. -/
theorem boundary_capInDegree_of_boundary_killed {p q n : ℕ} (h : p + q + 1 = n)
    (α : RelativeIntegralCap.Cochain V p) (c : SmallChains Coefficient U V n)
    (hc : capInDegree U V (p := p) (q := q) rfl α
      (((complex U V).d n (p + q)).hom c) = 0) :
    ((singularComplex U).d (q + 1) q).hom
        (capInDegree U V (p := p) (q := q + 1) (n := n) (by omega) α c) =
      -((-1 : ℤ) ^ p) • capInDegree U V (p := p + 1) (q := q) (n := n) (by omega)
        (RelativeIntegralCap.coboundary V α) c := by
  rw [boundary_capInDegree U V h α c, hc, zsmul_zero, zero_sub, neg_zsmul]

end Wikipedia.HopfProblem.DegreeCollapse.SmallIntegralCap

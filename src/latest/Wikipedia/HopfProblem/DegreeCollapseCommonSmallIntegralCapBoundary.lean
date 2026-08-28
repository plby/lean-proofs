import Wikipedia.HopfProblem.DegreeCollapseCommonSmallIntegralCap

/-!
# Signed cap boundaries in the actual overlap

The original injective overlap inclusion transfers the signed ambient
cap formula to the genuine overlap-chain group. A boundary in an
annihilated piece leaves precisely -(-1)^p times the coboundary cap.
Closed original small-relative cochains consequently cap to actual
overlap cycles.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap

open FirstHurewicz SingularMayerVietoris NoExoticSixSphere
open IntegralCap (Coefficient)
open SmallRelativeIntegralCochains (Cochain toAbsolute coboundary)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

theorem capInDegree_sub {p q n : ℕ} (h : p + q = n) (α β : Cochain A B p) :
    capInDegree U A V B h (α - β) = capInDegree U A V B h α - capInDegree U A V B h β := by
  apply eq_sub_iff_add_eq.mpr
  rw [← capInDegree_add, sub_add_cancel]

theorem boundary_inclusion (i j : ℕ) (c : (complex U A V B).X i) :
    ((singularComplex X).d i j).hom (((inclusion U A V B).f i).hom c) =
      ((inclusion U A V B).f j).hom (((complex U A V B).d i j).hom c) :=
  congrArg (fun m => m.hom c) ((inclusion U A V B).comm i j)

/-- Both terms and the integer sign are retained in the original overlap chain group. -/
theorem boundary_capInDegree {p q n : ℕ} (h : p + q + 1 = n) (α : Cochain A B p)
    (c : (complex U A V B).X n) :
    ((singularComplex (U ∩ V : Set X)).d (q + 1) q).hom
        (capInDegree U A V B (p := p) (q := q + 1) (n := n) (by omega) α c) =
      (-1 : ℤ) ^ p • capInDegree U A V B (p := p) (q := q) rfl α
          (((complex U A V B).d n (p + q)).hom c) -
        (-1 : ℤ) ^ p • capInDegree U A V B (p := p + 1) (q := q) (n := n) (by omega)
          (coboundary A B α) c := by
  let z : Chains X n := ((inclusion U A V B).f n).hom c
  let dz : Chains X (p + q) :=
    ((inclusion U A V B).f (p + q)).hom (((complex U A V B).d n (p + q)).hom c)
  apply SmallIntegralCap.inclusion_injective (U ∩ V) q
  calc
    _ = ((singularComplex X).d (q + 1) q).hom
        (IntegralCap.capInDegree (p := p) (q := q + 1) (by omega) (toAbsolute A B p α) z) :=
      (SmallIntegralCap.inclusion_boundary (U ∩ V) (q + 1) q
        (capInDegree U A V B (p := p) (q := q + 1) (by omega) α c)).trans
          (congrArg ((singularComplex X).d (q + 1) q).hom
            (inclusion_capInDegree U A V B (p := p) (q := q + 1) (by omega) α c))
    _ = (-1 : ℤ) ^ p • IntegralCap.capInDegree rfl (toAbsolute A B p α)
          (((singularComplex X).d n (p + q)).hom z) -
        (-1 : ℤ) ^ p • IntegralCap.capInDegree (p := p + 1) (q := q) (by omega)
          (SingularCohomologyCup.coboundary (toAbsolute A B p α)) z :=
      IntegralCap.boundary_capInDegree h (toAbsolute A B p α) z
    _ = (-1 : ℤ) ^ p • IntegralCap.capInDegree rfl (toAbsolute A B p α) dz -
        (-1 : ℤ) ^ p • IntegralCap.capInDegree (p := p + 1) (q := q) (by omega)
          (toAbsolute A B (p + 1) (coboundary A B α)) z :=
      congrArg₂ (fun x y => (-1 : ℤ) ^ p • x - (-1 : ℤ) ^ p • y)
        (congrArg (IntegralCap.capInDegree (q := q) rfl (toAbsolute A B p α))
          (boundary_inclusion U A V B n (p + q) c))
        (congrArg (fun β => IntegralCap.capInDegree (p := p + 1) (q := q) (by omega) β z)
          (SmallRelativeIntegralCochains.toAbsolute_coboundary A B p α).symm)
    _ = _ := by
      rw [map_sub, map_zsmul, map_zsmul]
      exact congrArg₂ (fun x y => (-1 : ℤ) ^ p • x - (-1 : ℤ) ^ p • y)
        (inclusion_capInDegree U A V B (p := p) (q := q) rfl α
          (((complex U A V B).d n (p + q)).hom c)).symm
        (inclusion_capInDegree U A V B (p := p + 1) (q := q) (by omega)
          (coboundary A B α) c).symm

/-- A genuine relative-cycle boundary contributes zero in the annihilated piece. -/
theorem boundary_capInDegree_of_relative_cycle {p q n : ℕ} (h : p + q + 1 = n)
    (α : Cochain A B p) (c : (complex U A V B).X n)
    (hc : ((inclusion U A V B).f (p + q)).hom
        (((complex U A V B).d n (p + q)).hom c) ∈
      LinearMap.range (inducedChain (subtypeInclusion A) (p + q))) :
    ((singularComplex (U ∩ V : Set X)).d (q + 1) q).hom
        (capInDegree U A V B (p := p) (q := q + 1) (n := n) (by omega) α c) =
      -((-1 : ℤ) ^ p) • capInDegree U A V B (p := p + 1) (q := q) (n := n) (by omega)
        (coboundary A B α) c := by
  have hz : capInDegree U A V B (p := p) (q := q) rfl α
      (((complex U A V B).d n (p + q)).hom c) = 0 := by
    apply SmallIntegralCap.inclusion_injective (U ∩ V) q
    exact (inclusion_capInDegree U A V B rfl α _).trans
      ((IntegralCap.capInDegree_eq_zero_of_pullback_zero A rfl (toAbsolute A B p α)
        (SmallRelativeIntegralCochains.pullback_toAbsolute_left A B p α) _ hc).trans
          (inducedChain (subtypeInclusion (U ∩ V)) q).map_zero.symm)
  exact (boundary_capInDegree U A V B h α c).trans
    (by rw [hz, zsmul_zero, zero_sub, neg_zsmul])

/-- Original closed small-relative cochains give genuine integral cycles in the overlap. -/
theorem cap_is_cycle {p q n : ℕ} (h : p + q = n) (α : Cochain A B p)
    (hα : coboundary A B α = 0) (c : (complex U A V B).X n)
    (hc : ((inclusion U A V B).f (n - 1)).hom
        (((complex U A V B).d n (n - 1)).hom c) ∈
      LinearMap.range (inducedChain (subtypeInclusion A) (n - 1))) :
    ((singularComplex (U ∩ V : Set X)).d q (q - 1)).hom
      (capInDegree U A V B h α c) = 0 := by
  cases q with
  | zero =>
      change ((singularComplex (U ∩ V : Set X)).d 0 0).hom _ = 0
      rw [(singularComplex (U ∩ V : Set X)).shape 0 0 (by simp)]
      rfl
  | succ q =>
      have hc' : ((inclusion U A V B).f (p + q)).hom
          (((complex U A V B).d n (p + q)).hom c) ∈
        LinearMap.range (inducedChain (subtypeInclusion A) (p + q)) := by
        exact (congrArg (fun j => ((inclusion U A V B).f j).hom
          (((complex U A V B).d n j).hom c) ∈
            LinearMap.range (inducedChain (subtypeInclusion A) j))
          (show n - 1 = p + q by omega)).mp hc
      have he := boundary_capInDegree_of_relative_cycle U A V B (p := p) (q := q)
        (n := n) (by omega) α c hc'
      rw [hα, capInDegree_zero, LinearMap.zero_apply, zsmul_zero] at he
      exact he

end Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap

import Wikipedia.NoExoticSixSphere.ModTwoCapFaces

/-!
# The boundary identity for the native mod-two cap operation

The two identical middle contributions cancel in the actual mod-two
chain group. Applying the native coproduct universal property then proves
the boundary identity on every original coefficient chain, not only on
simplex generators.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients

namespace NoExoticSixSphere.ModTwoCapProduct

variable {X : Type} [TopologicalSpace X]

/-- The paired middle terms cancel in the original mod-two chain group. -/
theorem cap_face_sum_cancel (p q : ℕ) (α : Cochain X p)
    (σ : SingularSimplex X (p + q + 1)) (a : ZMod 2) :
    ((∑ i : Fin (p + 1), frontTerm p q α σ a i.castSucc) +
        ∑ j : Fin (q + 1), backTerm p q α σ a j.succ) +
        (∑ i : Fin (p + 2), frontTerm p q α σ a i) =
      ∑ j : Fin (q + 2), backTerm p q α σ a j := by
  rw [Fin.sum_univ_castSucc (frontTerm p q α σ a),
    Fin.sum_univ_succ (backTerm p q α σ a), front_last_eq_back_zero]
  calc
    _ = ((∑ i : Fin (p + 1), frontTerm p q α σ a i.castSucc) +
        (∑ i : Fin (p + 1), frontTerm p q α σ a i.castSucc)) +
        (backTerm p q α σ a 0 + ∑ j : Fin (q + 1), backTerm p q α σ a j.succ) := by abel
    _ = _ := by rw [ModTwoChains.add_self_eq_zero, zero_add]

/-- The cap boundary formula as an equality of actual integral-linear maps of native chains. -/
theorem boundary_cap_map (p q : ℕ) (α : Cochain X p) :
    (((modComplex 2 X).d (q + 1) q).hom).comp
        (capInDegree (p := p) (q := q + 1) (n := p + q + 1) (by omega) α) =
      (capInDegree (p := p) (q := q) rfl α).comp
          ((modComplex 2 X).d (p + q + 1) (p + q)).hom +
        capInDegree (p := p + 1) (q := q) (n := p + q + 1) (by omega) (coboundary α) := by
  apply CoefficientChains.map_ext Coefficient X (p + q + 1)
  intro σ a
  exact (boundary_cap_simplex p q α σ a).trans ((cap_face_sum_cancel p q α σ a).symm.trans
    (congrArg₂ (fun x y => x + y) (cap_boundary_split p q α σ a)
      (cap_coboundary_simplex p q α σ a)).symm)

/-- Boundary of cap equals cap of boundary plus cap with coboundary, on every actual chain. -/
theorem boundary_cap (p q : ℕ) (α : Cochain X p) (c : ModTwoChains.Chains X (p + q + 1)) :
    ((modComplex 2 X).d (q + 1) q).hom
        (capInDegree (p := p) (q := q + 1) (n := p + q + 1) (by omega) α c) =
      capInDegree (p := p) (q := q) rfl α
          (((modComplex 2 X).d (p + q + 1) (p + q)).hom c) +
        capInDegree (p := p + 1) (q := q) (n := p + q + 1) (by omega) (coboundary α) c :=
  LinearMap.congr_fun (boundary_cap_map p q α) c

end NoExoticSixSphere.ModTwoCapProduct

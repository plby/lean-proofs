import Wikipedia.NoExoticSixSphere.ModTwoCapProduct
import Wikipedia.HopfProblem.SingularCohomologyCupFacesSigns

/-!
# The actual faces in the mod-two cap boundary calculation

Deleting a vertex before or after the common front/back vertex gives
the two parts of the cap boundary. The last front-face term is exactly
the first back-face term. All identities retain the actual simplex maps
and the native coefficient summands.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients SingularCohomologyCup

namespace NoExoticSixSphere.ModTwoCapProduct

variable {X : Type} [TopologicalSpace X]

/-- A front-face contribution, with the fixed complementary back simplex. -/
def frontTerm (p q : ℕ) (α : Cochain X p) (σ : SingularSimplex X (p + q + 1))
    (a : ZMod 2) (i : Fin (p + 2)) : ModTwoChains.Chains X q :=
  CoefficientChains.simplex Coefficient X q
    (σ.comp (windowFace (p + 1) q (p + q + 1) (by omega)))
    (α (simplexChain X p ((σ.comp (windowFace 0 (p + 1) (p + q + 1) (by omega))).comp
      (simplexFace p i))) * a)

/-- A back-face contribution, with the fixed front-cochain value. -/
def backTerm (p q : ℕ) (α : Cochain X p) (σ : SingularSimplex X (p + q + 1))
    (a : ZMod 2) (j : Fin (q + 2)) : ModTwoChains.Chains X q :=
  CoefficientChains.simplex Coefficient X q
    ((σ.comp (windowFace p (q + 1) (p + q + 1) (by omega))).comp (simplexFace q j))
    (α (simplexChain X p (σ.comp (windowFace 0 p (p + q + 1) (by omega)))) * a)

/-- The part of the ambient boundary deleting a front vertex. -/
theorem cap_boundary_front (p q : ℕ) (α : Cochain X p)
    (σ : SingularSimplex X (p + q + 1)) (a : ZMod 2) (i : Fin (p + 1)) :
    capInDegree (p := p) (q := q) rfl α
        (CoefficientChains.simplex Coefficient X (p + q)
          (σ.comp (simplexFace (p + q) ⟨i.val, by omega⟩)) a) =
      frontTerm p q α σ a i.castSucc := by
  have hf := face_window_middle 0 p (p + q) (by omega)
    (⟨i.val, by omega⟩ : Fin (p + q + 2)) i.castSucc (by simp)
  have hb := face_window_before p q (p + q) (by omega)
    (⟨i.val, by omega⟩ : Fin (p + q + 2)) (by change i.val ≤ p; omega)
  refine (capInDegree_simplex rfl α _ a).trans ?_
  simp only [frontTerm, ContinuousMap.comp_assoc, hf, hb]

/-- The part of the ambient boundary deleting a vertex after the front block. -/
theorem cap_boundary_back (p q : ℕ) (α : Cochain X p)
    (σ : SingularSimplex X (p + q + 1)) (a : ZMod 2) (j : Fin (q + 1)) :
    capInDegree (p := p) (q := q) rfl α
        (CoefficientChains.simplex Coefficient X (p + q)
          (σ.comp (simplexFace (p + q) ⟨p + 1 + j.val, by omega⟩)) a) =
      backTerm p q α σ a j.succ := by
  have hf := face_window_after 0 p (p + q) (by omega)
    (⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2))
    (by change 0 + p < p + 1 + j.val; omega)
  have hb := face_window_middle p q (p + q) (by omega)
    (⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2)) j.succ (by simp; omega)
  refine (capInDegree_simplex rfl α _ a).trans ?_
  simp only [backTerm, ContinuousMap.comp_assoc, hf, hb]

/-- The two middle contributions are literally the same native coefficient chain. -/
theorem front_last_eq_back_zero (p q : ℕ) (α : Cochain X p)
    (σ : SingularSimplex X (p + q + 1)) (a : ZMod 2) :
    frontTerm p q α σ a (Fin.last (p + 1)) = backTerm p q α σ a 0 := by
  simp only [frontTerm, backTerm, ContinuousMap.comp_assoc, window_face_last, window_face_zero]

/-- Boundary of the original capped simplex is the full sum of back contributions. -/
theorem boundary_cap_simplex (p q : ℕ) (α : Cochain X p)
    (σ : SingularSimplex X (p + q + 1)) (a : ZMod 2) :
    ((modComplex 2 X).d (q + 1) q).hom
        (capInDegree (p := p) (q := q + 1) (n := p + q + 1) (by omega) α
          (CoefficientChains.simplex Coefficient X (p + q + 1) σ a)) =
      ∑ j : Fin (q + 2), backTerm p q α σ a j := by
  have he := capInDegree_simplex (p := p) (q := q + 1) (n := p + q + 1) (by omega) α σ a
  apply (congrArg ((modComplex 2 X).d (q + 1) q).hom he).trans
  exact ModTwoChains.boundary_simplex X q _ _

/-- Capping with the original coboundary gives the full sum of front contributions. -/
theorem cap_coboundary_simplex (p q : ℕ) (α : Cochain X p)
    (σ : SingularSimplex X (p + q + 1)) (a : ZMod 2) :
    capInDegree (p := p + 1) (q := q) (n := p + q + 1) (by omega) (coboundary α)
        (CoefficientChains.simplex Coefficient X (p + q + 1) σ a) =
      ∑ i : Fin (p + 2), frontTerm p q α σ a i := by
  refine (capInDegree_simplex (p := p + 1) (q := q) (n := p + q + 1)
    (by omega) (coboundary α) σ a).trans ?_
  rw [coboundary_simplex, Finset.sum_mul, map_sum]
  rfl

/-- The original ambient boundary splits into the proper front and back contributions. -/
theorem cap_boundary_split (p q : ℕ) (α : Cochain X p)
    (σ : SingularSimplex X (p + q + 1)) (a : ZMod 2) :
    capInDegree (p := p) (q := q) rfl α
        (((modComplex 2 X).d (p + q + 1) (p + q)).hom
          (CoefficientChains.simplex Coefficient X (p + q + 1) σ a)) =
      (∑ i : Fin (p + 1), frontTerm p q α σ a i.castSucc) +
        ∑ j : Fin (q + 1), backTerm p q α σ a j.succ := by
  have he := congrArg (capInDegree (p := p) (q := q) rfl α)
    (ModTwoChains.boundary_simplex X (p + q) σ a)
  rw [map_sum] at he
  apply he.trans
  apply (sum_faces_split p q _).trans
  apply congrArg₂ (fun x y => x + y)
  · exact Finset.sum_congr rfl (fun i _ => cap_boundary_front p q α σ a i)
  · exact Finset.sum_congr rfl (fun j _ => cap_boundary_back p q α σ a j)

end NoExoticSixSphere.ModTwoCapProduct

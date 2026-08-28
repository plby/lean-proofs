import Wikipedia.HopfProblem.MappingTorusTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Descending actual boundary-cylinder maps and homotopies

An integer-invariant continuous map on the real cylinder descends to the
actual mapping torus.  A jointly continuous invariant homotopy descends as
well, by the open quotient topology.  In particular a change in the lifted
base curve does not require discarding the original fibre-coordinate map.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cylinder

open MappingTorus SingularMayerVietoris PeriodTorusHigherHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (φ : X ≃ₜ X)

/-- The mapping-torus projection is an open quotient map. -/
theorem projection_isOpenQuotientMap : IsOpenQuotientMap (mk φ) :=
  ⟨mk_surjective φ, mk_continuous φ, mk_open φ⟩

/-- Descend the given continuous cylinder map itself, without replacing
its fibre coordinate by a homologically equivalent map. -/
def descend (F : C(ℝ × X, Y))
    (hF : ∀ (k : ℤ) p, F (deck φ k p) = F p) : C(Torus φ, Y) where
  toFun := Quotient.lift F (by
    rintro p q ⟨k, rfl⟩
    exact (hF k p).symm)
  continuous_toFun := F.continuous.quotient_lift _

@[simp] theorem descend_mk (F : C(ℝ × X, Y))
    (hF : ∀ (k : ℤ) p, F (deck φ k p) = F p) (p : ℝ × X) :
    descend φ F hF (mk φ p) = F p := rfl

/-- Equality of the literal cylinder representatives determines equality
of the descended continuous maps. -/
theorem descend_ext (F G : C(ℝ × X, Y))
    (hF : ∀ (k : ℤ) p, F (deck φ k p) = F p)
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = G p)
    (h : ∀ p, F p = G p) : descend φ F hF = descend φ G hG := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨p, rfl⟩ := mk_surjective φ x
  exact h p

/-- An invariant homotopy on the real cylinder descends jointly
continuously to the actual mapping torus. -/
def descendHomotopy (F G : C(ℝ × X, Y))
    (hF : ∀ (k : ℤ) p, F (deck φ k p) = F p)
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = G p)
    (H : F.Homotopy G)
    (hH : ∀ (s : unitInterval) (k : ℤ) p,
      H (s, deck φ k p) = H (s, p)) :
    (descend φ F hF).Homotopy (descend φ G hG) where
  toFun z := Quotient.lift (fun p => H (z.1, p)) (by
    rintro p q ⟨k, rfl⟩
    exact (hH z.1 k p).symm) z.2
  continuous_toFun := by
    apply (IsOpenQuotientMap.id.prodMap
      (projection_isOpenQuotientMap φ)).continuous_comp_iff.mp
    exact H.continuous
  map_zero_left x := by
    obtain ⟨p, rfl⟩ := mk_surjective φ x
    exact H.apply_zero p
  map_one_left x := by
    obtain ⟨p, rfl⟩ := mk_surjective φ x
    exact H.apply_one p

@[simp] theorem descendHomotopy_mk (F G : C(ℝ × X, Y))
    (hF : ∀ (k : ℤ) p, F (deck φ k p) = F p)
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = G p)
    (H : F.Homotopy G)
    (hH : ∀ (s : unitInterval) (k : ℤ) p,
      H (s, deck φ k p) = H (s, p))
    (s : unitInterval) (p : ℝ × X) :
    descendHomotopy φ F G hF hG H hH (s, mk φ p) = H (s, p) := rfl

/-- A genuine invariant cylinder homotopy preserves the induced map on
actual integral singular homology, in every degree. -/
theorem descend_homology_eq (F G : C(ℝ × X, Y))
    (hF : ∀ (k : ℤ) p, F (deck φ k p) = F p)
    (hG : ∀ (k : ℤ) p, G (deck φ k p) = G p)
    (H : F.Homotopy G)
    (hH : ∀ (s : unitInterval) (k : ℤ) p,
      H (s, deck φ k p) = H (s, p)) (n : ℕ) :
    singularHomologyMap (descend φ F hF) n =
      singularHomologyMap (descend φ G hG) n :=
  homotopy_homologyMap (descendHomotopy φ F G hF hG H hH) n

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cylinder

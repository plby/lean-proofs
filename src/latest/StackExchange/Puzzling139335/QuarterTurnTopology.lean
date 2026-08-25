import StackExchange.Puzzling139335.QuarterTurnTopology.InvariantCurve
import StackExchange.Puzzling139335.QuarterTurnTopology.CurveNesting
import StackExchange.Puzzling139335.QuarterTurnTopology.Orbit
import StackExchange.Puzzling139335.QuarterTurnTopology.PairwiseOrbit
import StackExchange.Puzzling139335.QuarterTurnTopology.Iterates
import StackExchange.Puzzling139335.JordanInvolution

/-!
# The quarter-turn separation lemma

If an open connected planar set misses its quarter-turn image, it also
misses its half-turn image.  The quarter-turn is specified by the concrete
identity that its square is reflection in the stated center; either
orientation is allowed.

The proof uses a simple arc between putative antipodal points.  A minimal
pair of exchanged parameters produces an invariant Jordan curve.  Its
center lies inside by the proved planar Brouwer and Jordan theorems, while
Jordan nesting prevents it from missing its quarter-turn image.
-/

open Set

namespace Puzzling139335.QuarterTurnTopology

/-- An open preconnected set disjoint from its quarter-turn image is also
disjoint from its half-turn image.  No boundedness or boundary regularity
condition on the set is needed. -/
theorem disjoint_halfTurn {T : Set Plane} {c : Plane}
    (e : Plane ≃ₜ Plane)
    (hsquare : ∀ x, e (e x) = AffineIsometryEquiv.pointReflection ℝ c x)
    (hopen : IsOpen T) (hconn : IsPreconnected T) (hadj : Disjoint T (e '' T)) :
    Disjoint T (AffineIsometryEquiv.pointReflection ℝ c '' T) := by
  let h := (AffineIsometryEquiv.pointReflection ℝ c).toHomeomorph
  have hinv : Function.Involutive h :=
    AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) c
  have hec : e c = c := fixed_center e hsquare
  have hcnot : c ∉ T := by
    intro hc
    exact disjoint_left.1 hadj hc (hec ▸ mem_image_of_mem e hc)
  have hfree : ∀ x ∈ T, h x ≠ x := by
    intro x hx hxx
    exact hcnot ((AffineIsometryEquiv.pointReflection_fixed_iff (𝕜 := ℝ)).mp hxx ▸ hx)
  apply disjoint_left.2
  rintro x hx ⟨y, hy, hyx⟩
  have hhx : h x ∈ T := by
    change h y = x at hyx
    rw [← hyx, hinv]
    exact hy
  obtain ⟨A, hAT, -, hA⟩ := Schoenflies.exists_simple_arc_of_isPreconnected
    hopen hconn hx hhx (hfree x hx).symm
  obtain ⟨C, hCsub, hC, hCsym⟩ :=
    hA.exists_invariant_jordanCurve h hinv (fun z hz => hfree z (hAT hz))
  have hregion : IsJordanRegion (closure (Schoenflies.inside C)) := ⟨C, hC, rfl⟩
  have hregionsym : AffineIsometryEquiv.pointReflection ℝ c ''
      closure (Schoenflies.inside C) = closure (Schoenflies.inside C) := by
    change h '' closure (Schoenflies.inside C) = closure (Schoenflies.inside C)
    rw [h.image_closure, Schoenflies.homeomorph_image_inside, hCsym]
  have hcinside : c ∈ Schoenflies.inside C := by
    have hc := hregion.center_mem_interior_of_pointReflection hregionsym
    simpa only [interior_closure_inside (Schoenflies.jordan_curve_theorem hC)] using hc
  have himage (D : Set Plane) : e '' (e '' D) = h '' D := by
    rw [← image_comp]
    have heq : (e ∘ e : Plane → Plane) = h := funext hsquare
    rw [heq]
  have hperiod : e '' (e '' C) = C := (himage C).trans hCsym
  have hCsub' : C ⊆ T ∪ e '' (e '' T) := by
    rw [himage]
    exact hCsub.trans (union_subset_union hAT (image_mono hAT))
  have hdis : Disjoint C (e '' C) :=
    (disjoint_even_odd e (fourth_apply e hsquare) hadj).mono hCsub' (image_mono hCsub')
  exact hC.not_disjoint_image_of_fixed_mem_inside e hperiod hcinside hec hdis

/-- Equivalent formulation using two applications of the quarter-turn. -/
theorem disjoint_second_image {T : Set Plane} {c : Plane}
    (e : Plane ≃ₜ Plane)
    (hsquare : ∀ x, e (e x) = AffineIsometryEquiv.pointReflection ℝ c x)
    (hopen : IsOpen T) (hconn : IsPreconnected T) (hadj : Disjoint T (e '' T)) :
    Disjoint T (e '' (e '' T)) := by
  have heq : (e ∘ e : Plane → Plane) = AffineIsometryEquiv.pointReflection ℝ c :=
    funext hsquare
  rw [← image_comp, heq]
  exact disjoint_halfTurn e hsquare hopen hconn hadj

/-- All four successive quarter-turn copies of the open set are pairwise disjoint. -/
theorem pairwise_disjoint_four_images {T : Set Plane} {c : Plane}
    (e : Plane ≃ₜ Plane)
    (hsquare : ∀ x, e (e x) = AffineIsometryEquiv.pointReflection ℝ c x)
    (hopen : IsOpen T) (hconn : IsPreconnected T) (hadj : Disjoint T (e '' T)) :
    Pairwise fun i j : Fin 4 =>
      Disjoint (((e : Plane → Plane)^[i.val]) '' T)
        (((e : Plane → Plane)^[j.val]) '' T) :=
  pairwise_disjoint_iterate_images e (fourth_apply e hsquare) hadj
    (disjoint_second_image e hsquare hopen hconn hadj)

end Puzzling139335.QuarterTurnTopology

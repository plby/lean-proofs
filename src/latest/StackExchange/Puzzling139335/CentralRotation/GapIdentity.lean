import StackExchange.Puzzling139335.Definitions
import Wikipedia.SchoenfliesTheorem.GeneralCrosscut
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The exact gap identity for the boundary-arc orbit

The boundaries `M ∪ cut` and `N ∪ cut` are congruent, while a central
symmetry sends `M` onto `N`.  Removing the relative interior of the common
cut before and after these bijections gives the exact domain and range of
the boundary-arc iteration.  This is set algebra: no polygonality,
rectifiability, or additional incidence assumptions are needed.
-/

open Set

namespace Puzzling139335.CentralRotation.GapIdentity

/-- Removing the shared arc except for its endpoints leaves the outer arc. -/
theorem union_sdiff_shared_arc {X : Type*} {M cut ends : Set X}
    (hinter : cut ∩ M = ends) : (M ∪ cut) \ (cut \ ends) = M := by
  ext x
  have hx : x ∈ cut ∧ x ∈ M ↔ x ∈ ends := by
    change x ∈ cut ∩ M ↔ x ∈ ends
    rw [hinter]
  simp only [mem_sdiff, mem_union]
  tauto

/-- Congruence maps the outer arc minus the preimage cut gap onto the other
outer arc minus the image cut gap. -/
theorem image_outer_gap (g : Plane ≃ₜ Plane) {M N cut ends : Set Plane}
    (hM : cut ∩ M = ends) (hN : cut ∩ N = ends)
    (hboundary : g '' (M ∪ cut) = N ∪ cut) :
    g '' (M \ g.symm '' (cut \ ends)) = N \ g '' (cut \ ends) := by
  have hremoveM := union_sdiff_shared_arc hM
  have hremoveN := union_sdiff_shared_arc hN
  have hgM : g '' M = (N ∪ cut) \ g '' (cut \ ends) := by
    calc
      g '' M = g '' ((M ∪ cut) \ (cut \ ends)) :=
        congrArg (fun S : Set Plane => g '' S) hremoveM.symm
      _ = (N ∪ cut) \ g '' (cut \ ends) := by
        rw [image_sdiff g.injective, hboundary]
  have hcancel (S : Set Plane) : g '' (g.symm '' S) = S := by
    simpa only [Homeomorph.coe_toEquiv, Homeomorph.coe_symm_toEquiv] using
      g.toEquiv.image_symm_image S
  rw [image_sdiff g.injective, hcancel, hgM,
    Set.sdiff_sdiff_comm, hremoveN]

/-- The exact gap-domain/range identity for `F = h ∘ g⁻¹`, proved from
the boundary unions and their shared endpoints.  Here `h` may be any plane
homeomorphism sending `M` onto `N`; a half-turn is the intended application. -/
theorem image_gap_of_boundary_intersections (g h F : Plane ≃ₜ Plane)
    {M N cut ends : Set Plane}
    (hM : cut ∩ M = ends) (hN : cut ∩ N = ends)
    (hboundary : g '' (M ∪ cut) = N ∪ cut) (houter : h '' M = N)
    (hF : ∀ x, F x = h (g.symm x)) :
    F '' (N \ g '' (cut \ ends)) = N \ F '' (cut \ ends) := by
  have hpre : g.symm '' (N \ g '' (cut \ ends)) =
      M \ g.symm '' (cut \ ends) := by
    rw [← image_outer_gap g hM hN hboundary]
    simpa only [Homeomorph.coe_toEquiv, Homeomorph.coe_symm_toEquiv] using
      g.toEquiv.symm_image_image (M \ g.symm '' (cut \ ends))
  have hcomp (S : Set Plane) : F '' S = h '' (g.symm '' S) := by
    rw [← image_comp]
    exact congrArg (fun f : Plane → Plane => f '' S) (funext hF)
  calc
    F '' (N \ g '' (cut \ ends)) =
        h '' (g.symm '' (N \ g '' (cut \ ends))) := hcomp _
    _ = h '' (M \ g.symm '' (cut \ ends)) := by rw [hpre]
    _ = N \ h '' (g.symm '' (cut \ ends)) := by
      rw [image_sdiff h.injective, houter]
    _ = N \ F '' (cut \ ends) := by rw [← hcomp]

/-- Version using the two actual boundary arc decompositions.  The open
part of the cut is precisely `cut \ {p,q}`. -/
theorem image_gap_of_cutPairs (g h F : Plane ≃ₜ Plane)
    {A B M N cut : Set Plane} {p q : Plane}
    (hA : Schoenflies.IsCutPair A p q M cut)
    (hB : Schoenflies.IsCutPair B p q N cut)
    (hboundary : g '' A = B) (houter : h '' M = N)
    (hF : ∀ x, F x = h (g.symm x)) :
    F '' (N \ g '' (cut \ {p, q})) = N \ F '' (cut \ {p, q}) := by
  apply image_gap_of_boundary_intersections g h F hA.symm.inter_eq hB.symm.inter_eq
    _ houter hF
  rw [hA.union_eq, hB.union_eq]
  exact hboundary

end Puzzling139335.CentralRotation.GapIdentity

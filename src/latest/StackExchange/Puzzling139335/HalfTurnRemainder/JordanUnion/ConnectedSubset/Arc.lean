import StackExchange.Puzzling139335.CentralRotation.LocalInvariantArc.CompactSubarc

/-!
# Compact connected nondegenerate subsets of an arc

The inverse of the ambient compact arc parametrization sends the subset to a
compact connected real set.  Its extrema delimit a closed interval, and two
distinct points of the subset force that interval to be nondegenerate.
-/

open Set unitInterval

namespace Schoenflies

/-- A compact connected subset of an arc containing two distinct points is
itself an arc.  Its endpoints need not be the ambient arc's endpoints. -/
theorem IsArcBetween.exists_isArcBetween_compact_connected
    {A E : Set Plane} {p q : Plane} (hA : IsArcBetween A p q)
    (hE : IsCompact E) (hc : IsConnected E) (hsub : E ⊆ A)
    (hnt : E.Nontrivial) :
    ∃ a b : Plane, IsArcBetween E a b := by
  obtain ⟨f, hf, hi, hfA, _, _⟩ := hA
  have hsub' : E ⊆ f '' I := by simpa only [hfA] using hsub
  obtain ⟨a, b, ha, hb, hab, _, himage⟩ :=
    compact_connected_subset_arc_parameters hf hi hE hc hsub'
  have hab_ne : a ≠ b := by
    intro heq
    have hsingle : E = {f a} := by
      rw [← himage, ← heq, Icc_self, image_singleton]
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    have hx' : x = f a := by simpa only [hsingle, mem_singleton_iff] using hx
    have hy' : y = f a := by simpa only [hsingle, mem_singleton_iff] using hy
    exact hxy (hx'.trans hy'.symm)
  refine ⟨f a, f b, ?_⟩
  simpa only [uIcc_of_le hab, himage] using
    isArcBetween_subarc_of_injOn_I hf hi ha hb hab_ne

end Schoenflies

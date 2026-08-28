import Wikipedia.HopfProblem.FundamentalGroupVanKampenUniqueness
import Wikipedia.HopfProblem.FundamentalGroupSimplyConnected

/-!
# Simple connectedness from the actual two-open-set van Kampen theorem

The genuine inclusion maps jointly determine homomorphisms out of the
ambient fundamental group. If both open pieces are simply connected,
the identity homomorphism and the trivial homomorphism agree on both
pieces, hence agree everywhere. The connected overlap and open-cover
hypotheses belong to the previously constructed `TwoOpenCover`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SphereHomology

open FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X]

/-- A genuine two-open-set van Kampen cover is path connected. -/
theorem twoOpenCover_pathConnectedSpace (D : TwoOpenCover X) : PathConnectedSpace X := by
  apply pathConnectedSpace_iff_univ.mpr
  rw [← D.cover]
  exact D.pathConnectedU.union D.pathConnectedV ⟨D.base, D.baseU, D.baseV⟩

/-- The actual fundamental group is trivial when both actual open pieces are simply connected. -/
theorem twoOpenCover_fundamentalGroup_eq_one (D : TwoOpenCover X)
    [SimplyConnectedSpace D.U] [SimplyConnectedSpace D.V]
    (g : FundamentalGroup X D.base) : g = 1 := by
  have h : MonoidHom.id (FundamentalGroup X D.base) =
      (1 : FundamentalGroup X D.base →* FundamentalGroup X D.base) := by
    apply D.hom_ext
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomU a = 1
      rw [ha, map_one]
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomV a = 1
      rw [ha, map_one]
  exact DFunLike.congr_fun h g

/-- Simply connected open pieces with a path-connected overlap have simply connected union. -/
theorem twoOpenCover_simplyConnectedSpace (D : TwoOpenCover X)
    [SimplyConnectedSpace D.U] [SimplyConnectedSpace D.V] : SimplyConnectedSpace X := by
  let := twoOpenCover_pathConnectedSpace D
  exact simplyConnectedSpace_of_fundamentalGroup_eq_one D.base
    (twoOpenCover_fundamentalGroup_eq_one D)

end Wikipedia.HopfProblem.SphereHomology

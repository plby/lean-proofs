import Wikipedia.HopfProblem.FundamentalGroupVanKampenCover
import Wikipedia.HopfProblem.FundamentalGroupVanKampenPathSubtypes
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupPathInduction
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupGenerationCore

/-!
# Uniqueness for the actual two-open-set fundamental group

The two inclusion homomorphisms jointly determine every homomorphism out
of the ambient fundamental group.  The proof closes local path segments
using actual coherent paths and subdivides arbitrary paths over the cover.
No presentation or generation statement about the ambient group is assumed.
-/

noncomputable section

open Set Path.Homotopic.Quotient
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

open TriangleRegularBaseFundamentalGroup

variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]

namespace TwoOpenCover

/-- Homomorphisms on the actual fundamental group are determined by their
restrictions to both members of the open cover. -/
theorem hom_ext (D : TwoOpenCover X) (f g : FundamentalGroup X D.base →* G)
    (hU : f.comp D.inclusionHomU = g.comp D.inclusionHomU)
    (hV : f.comp D.inclusionHomV = g.comp D.inclusionHomV) : f = g := by
  let F (x : X) : Path.Homotopic.Quotient D.base x :=
    Path.Homotopic.Quotient.mk (D.pathTo x)
  have hlocal : ∀ (i : Bool) {x y : X} (p : Path x y),
      (∀ t, p t ∈ D.chart i) →
        f (basedLoop F (Path.Homotopic.Quotient.mk p)) =
          g (basedLoop F (Path.Homotopic.Quotient.mk p)) := by
    intro i x y p hp
    have hx : x ∈ D.chart i := by simpa using hp 0
    have hy : y ∈ D.chart i := by simpa using hp 1
    let l : Path D.base D.base := ((D.pathTo x).trans p).trans (D.pathTo y).symm
    have hl : ∀ t, l t ∈ D.chart i :=
      SimplyConnectedCover.trans_mem _ _
        (SimplyConnectedCover.trans_mem _ _ (D.pathTo_mem i x hx) hp)
        (fun t => D.pathTo_mem i y hy (unitInterval.symm t))
    let l' : Path (D.baseChart i) (D.baseChart i) :=
      pathIn l (D.base_mem_chart i) (D.base_mem_chart i) hl
    have hmap : (Path.Homotopic.Quotient.mk l').map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(D.chart i, X)) =
        basedLoop F (Path.Homotopic.Quotient.mk p) := by
      change Path.Homotopic.Quotient.mk (l'.map continuous_subtype_val) =
        basedLoop F (Path.Homotopic.Quotient.mk p)
      rw [show l'.map continuous_subtype_val = l from pathIn_map _ _ _ _]
      rfl
    cases i with
    | false =>
        have h := DFunLike.congr_fun hU (Path.Homotopic.Quotient.mk l')
        exact (congrArg f hmap).symm.trans (h.trans (congrArg g hmap))
    | true =>
        have h := DFunLike.congr_fun hV (Path.Homotopic.Quotient.mk l')
        exact (congrArg f hmap).symm.trans (h.trans (congrArg g hmap))
  have hall : ∀ {x y : X} (q : Path.Homotopic.Quotient x y),
      f (basedLoop F q) = g (basedLoop F q) := by
    apply pathClass_induction_of_open_cover
      (fun i => (D.chart i : Set X)) D.chart_open D.chart_cover
      (fun q => f (basedLoop F q) = g (basedLoop F q))
    · intro x
      simp only [basedLoop_refl, map_one]
    · intro x y z p q hp hq
      rw [basedLoop_trans, map_mul, map_mul, hp, hq]
    · intro i x y p hp
      exact hlocal i p (range_subset_iff.mp hp)
  have hbase : F D.base = Path.Homotopic.Quotient.refl D.base := by
    simp only [F, D.pathTo_base, mk_refl]
  have hsymm : (Path.Homotopic.Quotient.refl D.base).symm =
      Path.Homotopic.Quotient.refl D.base := by
    change (1 : FundamentalGroup X D.base)⁻¹ = 1
    exact inv_one
  apply MonoidHom.ext
  intro q
  simpa only [basedLoop, hbase, refl_trans, hsymm, trans_refl] using hall q

end TwoOpenCover

end Wikipedia.HopfProblem.FundamentalGroupVanKampen

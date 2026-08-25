import StackExchange.Puzzling139335.SegmentCrossing.Defs
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Interior sides of a locally straight frontier

The local frontier hypothesis is an actual boundary statement. It does not
follow merely from a chord of a convex hull.
-/

open Set

namespace Puzzling139335.SegmentCrossing

/-- A connected open half-ball avoiding the frontier stays on the same side
of the region as any one of its interior points. -/
theorem hasInteriorHalfBall_of_local_frontier_of_witness
    {P : Set Plane} {x : Plane} {f : Plane →L[ℝ] ℝ} {r : ℝ}
    (hr : 0 < r)
    (hline : ∀ y ∈ Metric.ball x r, y ∈ frontier P → f y = f x)
    (hw : ∃ y ∈ Metric.ball x r, f x < f y ∧ y ∈ interior P) :
    HasInteriorHalfBall P x f := by
  let U : Set Plane := Metric.ball x r ∩ {y | f x < f y}
  have hconv : Convex ℝ U :=
    (convex_ball x r).inter ((convex_Ioi (f x)).linear_preimage f.toLinearMap)
  have hoff : U ⊆ (frontier P)ᶜ := by
    intro y hy hyf
    exact (ne_of_gt hy.2) (hline y hy.1 hyf)
  have hcover : U ⊆ interior P ∪ interior Pᶜ := by
    simpa only [compl_frontier_eq_union_interior] using hoff
  have hdis : Disjoint (interior P) (interior Pᶜ) := by
    apply Set.disjoint_left.mpr
    intro y hy hyc
    exact interior_subset hyc (interior_subset hy)
  obtain hin | hout := IsPreconnected.subset_or_subset isOpen_interior isOpen_interior
    hdis hcover hconv.isPreconnected
  · exact ⟨r, hr, hin⟩
  · obtain ⟨y, hyball, hyf, hyP⟩ := hw
    exact False.elim (interior_subset (hout ⟨hyball, hyf⟩) (interior_subset hyP))

/-- A nonconstant linear coordinate takes a value different from any prescribed
value on every nonempty open planar set. -/
theorem exists_linear_ne_on_open (f : Plane →L[ℝ] ℝ)
    (hf : Function.Surjective f) {V : Set Plane} (hV : IsOpen V)
    (hne : V.Nonempty) (c : ℝ) : ∃ y ∈ V, f y ≠ c := by
  have hopen : IsOpen (f '' V) := f.isOpenMap hf V hV
  have hnonempty : (f '' V).Nonempty := hne.image f
  have hnot : ¬ f '' V ⊆ {c} := by
    intro hsub
    obtain ⟨z, hz⟩ := hnonempty
    have hzc : z = c := hsub hz
    have heq : f '' V = {c} :=
      Subset.antisymm hsub (singleton_subset_iff.mpr (hzc ▸ hz))
    exact not_isOpen_singleton c (heq ▸ hopen)
  obtain ⟨z, hz, hzc⟩ := Set.not_subset.mp hnot
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨y, hy, hzc⟩

/-- A locally straight frontier has an interior half-ball on at least one of
its two sides. No global supporting-half-plane assumption is needed. -/
theorem hasInteriorHalfBall_or_neg_of_local_frontier
    {P : Set Plane} {x : Plane} (f : Plane →L[ℝ] ℝ)
    (hf : Function.Surjective f) (hx : x ∈ closure (interior P))
    (hline : ∃ r > 0, ∀ y ∈ Metric.ball x r, y ∈ frontier P → f y = f x) :
    HasInteriorHalfBall P x f ∨ HasInteriorHalfBall P x (-f) := by
  obtain ⟨r, hr, hline⟩ := hline
  obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.mp hx r hr
  have hV : (Metric.ball x r ∩ interior P).Nonempty :=
    ⟨z, by simpa only [Metric.mem_ball, dist_comm] using hzx, hz⟩
  obtain ⟨y, hy, hne⟩ := exists_linear_ne_on_open f hf
    (Metric.isOpen_ball.inter isOpen_interior) hV (f x)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · right
    apply hasInteriorHalfBall_of_local_frontier_of_witness hr
    · intro w hwr hwP
      change -(f w) = -(f x)
      rw [hline w hwr hwP]
    · exact ⟨y, hy.1, neg_lt_neg hlt, hy.2⟩
  · exact Or.inl (hasInteriorHalfBall_of_local_frontier_of_witness hr hline
      ⟨y, hy.1, hgt, hy.2⟩)

end Puzzling139335.SegmentCrossing

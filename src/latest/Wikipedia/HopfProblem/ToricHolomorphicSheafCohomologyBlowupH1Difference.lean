import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Cocycle

/-!
# The actual holomorphic difference on the two-chart overlap

The two affine cochains have the same original transition cocycle. Their
difference therefore does not depend on the cover index. Choosing an index
defines a function on the overlap; its equality near every point with one
fixed holomorphic representative proves actual analyticity.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1.Cocycle

variable {ι : Type} (C : Cocycle ι)

def overlapDifference (q : ℂ × ℂ) : ℂ :=
  let i := (C.cover (chartMap false q)).choose
  C.chartCochain false i q - C.chartCochain true i (cross q)

theorem overlapDifference_eq (i : ι) (q : ℂ × ℂ) (hq : q.2 ≠ 0)
    (hi : chartMap false q ∈ C.domain i) :
    C.overlapDifference q = C.chartCochain false i q - C.chartCochain true i (cross q) := by
  let j := (C.cover (chartMap false q)).choose
  have hj : chartMap false q ∈ C.domain j := (C.cover (chartMap false q)).choose_spec
  have hmap : chartMap true (cross q) = chartMap false q := chartMap_cross false q hq
  have hji : chartMap true (cross q) ∈ C.domain j := by rwa [hmap]
  have hii : chartMap true (cross q) ∈ C.domain i := by rwa [hmap]
  have hleft := C.chartCochain_sub false j i q hj hi
  have hright := C.chartCochain_sub true j i (cross q) hji hii
  rw [hmap] at hright
  change C.chartCochain false j q - C.chartCochain true j (cross q) = _
  linear_combination hleft - hright

theorem overlapDifference_analytic :
    AnalyticOnNhd ℂ C.overlapDifference {q : ℂ × ℂ | q.2 ≠ 0} := by
  intro q hq
  obtain ⟨i, hi⟩ := C.cover (chartMap false q)
  have hmap : chartMap true (cross q) = chartMap false q := chartMap_cross false q hq
  have hii : chartMap true (cross q) ∈ C.domain i := by rwa [hmap]
  have hleft := C.chartCochain_analytic false i q hi
  have hright : AnalyticAt ℂ (fun p => C.chartCochain true i (cross p)) q :=
    (C.chartCochain_analytic true i (cross q) hii).comp (cross_analytic q hq)
  apply (hleft.sub hright).congr
  have hZ : IsOpen {p : ℂ × ℂ | p.2 ≠ 0} :=
    isOpen_ne_fun continuous_snd continuous_const
  filter_upwards [((C.isOpen_domain i).preimage (chartMap_continuous false)).mem_nhds hi,
    hZ.mem_nhds hq] with p hp hpne
  exact (C.overlapDifference_eq i p hpne hp).symm

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1.Cocycle

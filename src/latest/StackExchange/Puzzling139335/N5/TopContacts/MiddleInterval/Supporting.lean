import StackExchange.Puzzling139335.N5.SideExclusion.Generic
import Wikipedia.SchoenfliesTheorem.ModelCurve

/-!
# Supporting segments on the top side

An interval of top-side contacts gives an actual horizontal segment in a
piece. Its open part is excluded from every other piece, since all the
pieces lie on the same side of the top supporting line.
-/

open Set

namespace Puzzling139335.N5.TopContacts

/-- A whole interval of top-side contacts contains the corresponding actual
horizontal segment. -/
theorem top_segment_subset_of_interval {P : Set Plane} {a b : ℝ}
    (hab : a ≤ b)
    (hmem : ∀ x ∈ Icc a b, Schoenflies.Plane.mk x 1 ∈ P) :
    segment ℝ (Schoenflies.Plane.mk a 1) (Schoenflies.Plane.mk b 1) ⊆ P := by
  intro p hp
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hab] at hp
  have heq : p = Schoenflies.Plane.mk (p 0) 1 := by
    ext k
    fin_cases k
    · rfl
    · exact hp.1
  rw [heq]
  exact hmem (p 0) hp.2

/-- A point strictly between the endpoints of a top-side segment in one
piece cannot belong to a distinct piece. -/
theorem top_open_not_mem_of_segment (d : SquareDissection)
    {i j : Fin 4} {a b x : ℝ} (hij : i ≠ j) (hab : a < b)
    (hseg : segment ℝ (Schoenflies.Plane.mk a 1) (Schoenflies.Plane.mk b 1) ⊆
      d.piece i)
    (hax : a < x) (hxb : x < b) : Schoenflies.Plane.mk x 1 ∉ d.piece j := by
  have hne : Schoenflies.Plane.mk a 1 ≠ Schoenflies.Plane.mk b 1 := by
    intro heq
    exact (ne_of_lt hab) (congrArg (fun p : Plane => p 0) heq)
  have hxseg : Schoenflies.Plane.mk x 1 ∈
      segment ℝ (Schoenflies.Plane.mk a 1) (Schoenflies.Plane.mk b 1) := by
    rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hab.le]
    exact ⟨rfl, hax.le, hxb.le⟩
  have hxends : Schoenflies.Plane.mk x 1 ∉
      ({Schoenflies.Plane.mk a 1, Schoenflies.Plane.mk b 1} : Set Plane) := by
    intro hmem
    rcases mem_insert_iff.mp hmem with heq | heq
    · exact (ne_of_gt hax) (congrArg (fun p : Plane => p 0) heq)
    · exact (ne_of_lt hxb)
        (congrArg (fun p : Plane => p 0) (mem_singleton_iff.mp heq))
  apply segment_interior_not_mem_of_same_supporting_halfspace
    (d.jordan i) (d.jordan j) (-(EuclideanSpace.proj (1 : Fin 2))) (c := -1)
    _ _ _ (d.disjoint_interiors hij) hne hseg rfl rfl ⟨hxseg, hxends⟩
  · intro t
    refine ⟨Schoenflies.Plane.mk 0 (-t), ?_⟩
    change -(-t) = t
    exact neg_neg t
  · intro y hy
    change (-1 : ℝ) ≤ -(y 1)
    exact neg_le_neg (d.piece_subset i hy).2.2
  · intro y hy
    change (-1 : ℝ) ≤ -(y 1)
    exact neg_le_neg (d.piece_subset j hy).2.2

end Puzzling139335.N5.TopContacts

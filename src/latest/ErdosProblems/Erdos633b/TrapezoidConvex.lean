import ErdosProblems.Erdos633b.TrapezoidTriangles

/-! Four vertex tests suffice for containment of the whole closed ideal trapezoid. -/

namespace Erdos633b.Sixty

theorem trapezoid_subset_convex (d : ℝ) (hd : 0 < d) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (S : Set Plane) (hS : Convex ℝ S)
    (hA : point d 0 0 ∈ S) (hB : point d (x + y) 0 ∈ S)
    (hC : point d x y ∈ S) (hD : point d 0 y ∈ S) :
    TrapezoidPartition.trapezoidSet (frame d hd) x y ⊆ S := by
  let p := x / 2
  have hp : 0 < p := div_pos hx (by norm_num)
  have hpp : p + p = x := by dsimp only [p]; ring
  have hE : point d p y ∈ S := by
    have hh := hS.midpoint_mem hD hC
    have he : point d p y = midpoint ℝ (point d 0 y) (point d x y) := by
      rw [midpoint_eq_smul_add]
      ext i
      fin_cases i <;> simp [point, p] <;> ring
    rwa [← he] at hh
  have hleft : (leftTriangle d hd p y hp hy).support ⊆ S := by
    apply convexHull_min
    · rintro z ⟨i, rfl⟩
      rw [leftTriangle_points]
      fin_cases i
      · exact hD
      · exact hA
      · exact hE
    · exact hS
  have hright : (rightTriangle d hd p p y hp hy).support ⊆ S := by
    apply convexHull_min
    · rintro z ⟨i, rfl⟩
      rw [rightTriangle_points]
      fin_cases i
      · change point d (p + p) y ∈ S
        simpa only [hpp] using hC
      · exact hE
      · change point d (p + p + y) 0 ∈ S
        simpa only [hpp] using hB
    · exact hS
  have hmiddle : (middleTriangle d hd p p y hp hp hy).support ⊆ S := by
    apply convexHull_min
    · rintro z ⟨i, rfl⟩
      rw [middleTriangle_points]
      fin_cases i
      · exact hE
      · change point d (p + p + y) 0 ∈ S
        simpa only [hpp] using hB
      · exact hA
    · exact hS
  intro z hz
  have hu := TrapezoidPartition.regions_cover (frame d hd) p p y hp hp hy
  rw [hpp] at hu
  have hz' : z ∈ ⋃ k, TrapezoidPartition.region (frame d hd) p p y k := by rwa [hu]
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz'
  cases k
  · apply hleft
    rwa [leftTriangle_support d hd p p y hp hy]
  · apply hright
    rwa [rightTriangle_support d hd p p y hp hy]
  · apply hmiddle
    rwa [middleTriangle_support d hd p p y hp hp hy]

end Erdos633b.Sixty

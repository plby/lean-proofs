import Wikipedia.NoExoticSixSphere.JamesSphereEHPAttachingMap

/-!
# A unital sphere multiplication contracts the actual James attaching map

Multiplying the two original characteristic-coordinate blocks extends
the second-cell attaching map over its literal disk. On the boundary
one block is the sphere pole, so the two unit identities give precisely
the original remaining letter. Straight disk contraction fixes the
selected corner and yields the required based nullhomotopy.
Associativity is not required by this construction.
-/

noncomputable section

open Set Metric
open scoped Topology
open Wikipedia.HopfProblem.DegreeCollapse

namespace NoExoticSixSphere.JamesSphere.UnitalAttaching

theorem characteristic_two (n : ℕ) (x : CellBoundary.Coordinates n) :
    Cell.characteristic n 2 x =
      inclusion n (Cell.array n 2 x 0) * inclusion n (Cell.array n 2 x 1) := by
  change James.word (spherePole n) (List.ofFn (Cell.array n 2 x)) =
    James.letter (spherePole n) (Cell.array n 2 x 0) *
      James.letter (spherePole n) (Cell.array n 2 x 1)
  simp only [List.ofFn_succ, List.ofFn_zero, James.word_cons, James.word_nil, mul_one]
  rfl

theorem boundary_block_pole (n : ℕ) (s : CellBoundary.Boundary n) :
    Cell.array n 2 s.val 0 = spherePole n ∨ Cell.array n 2 s.val 1 = spherePole n := by
  have h := Cell.boundary_size_lt n 2 s.property
  obtain ⟨i, hi⟩ := (James.size_word_array_lt_iff (spherePole n) 2 (Cell.array n 2 s.val)).mp h
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

theorem attaching_eq_second (n : ℕ) (s : CellBoundary.Boundary n)
    (hs : Cell.array n 2 s.val 0 = spherePole n) :
    CellBoundary.attaching n s = Cell.array n 2 s.val 1 := by
  apply inclusion_injective n
  have h := congrArg Subtype.val (CellBoundary.characteristic_boundary n s)
  change Cell.characteristic n 2 s.val = inclusion n (CellBoundary.attaching n s) at h
  rw [← h, characteristic_two, hs, NativeHopf.inclusion_pole, one_mul]

theorem attaching_eq_first (n : ℕ) (s : CellBoundary.Boundary n)
    (hs : Cell.array n 2 s.val 1 = spherePole n) :
    CellBoundary.attaching n s = Cell.array n 2 s.val 0 := by
  apply inclusion_injective n
  have h := congrArg Subtype.val (CellBoundary.characteristic_boundary n s)
  change Cell.characteristic n 2 s.val = inclusion n (CellBoundary.attaching n s) at h
  rw [← h, characteristic_two, hs, NativeHopf.inclusion_pole, mul_one]

variable (n : ℕ) (μ : C(Sphere n × Sphere n, Sphere n))
  (hleft : ∀ x, μ (spherePole n, x) = x) (hright : ∀ x, μ (x, spherePole n) = x)

def extension : C(DiskCylinder.Disk (E := CellBoundary.Coordinates n), Sphere n) :=
  ⟨fun x ↦ μ (Cell.array n 2 x.val 0, Cell.array n 2 x.val 1),
    μ.continuous.comp
      (((continuous_apply 0).comp ((Cell.array n 2).continuous.comp continuous_subtype_val)).prodMk
        ((continuous_apply 1).comp ((Cell.array n 2).continuous.comp continuous_subtype_val)))⟩

include hleft hright in
theorem extension_boundary (s : CellBoundary.Boundary n) :
    extension n μ (DiskCylinder.boundaryToDisk s) = CellBoundary.attaching n s := by
  change μ (Cell.array n 2 s.val 0, Cell.array n 2 s.val 1) = _
  rcases boundary_block_pole n s with h | h
  · rw [attaching_eq_second n s h, h, hleft]
  · rw [attaching_eq_first n s h, h, hright]

def nullhomotopy (hn : 0 < n) :
    (CellBoundary.attaching n).HomotopyRel (ContinuousMap.const _ (spherePole n))
      {CellBoundary.corner n hn} :=
  (DiskBoundary.contraction (extension n μ) (CellBoundary.corner n hn)).cast
    (ContinuousMap.ext (extension_boundary n μ hleft hright))
    (by rw [extension_boundary n μ hleft hright, CellBoundary.attaching_corner])

include hleft hright in
theorem attachingHom_eq_one (hn : 0 < n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere (RoundCell.sphereDimension n)) (spherePole (RoundCell.sphereDimension n))) :
    EHPCell.attachingHom n hn d c = 1 := by
  rw [← EHPCell.attachingHom_factor]
  have h := HigherHomotopy.map_eq_of_based_homotopy (CellBoundary.attaching n)
    (ContinuousMap.const _ (spherePole n)) (CellBoundary.attaching_corner n hn) rfl
    (nullhomotopy n μ hleft hright hn) (RoundCell.boundaryPiEquiv n hn d c)
  exact h.trans (HigherHomotopy.map_const (CellBoundary.corner n hn) (spherePole n) _)

include hleft hright in
theorem connecting_eq_one (d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n)
    (c : π_ (d + 1 + 1) (Sphere (n + n + 1)) (spherePole (n + n + 1))) :
    EHP.connectingHomMetastable n d hn hdn c = 1 := by
  obtain ⟨a, rfl⟩ := (EHPCell.comparisonHom_bijective n d hn hdn).surjective c
  rw [EHPCell.connecting_comparisonHom]
  exact attachingHom_eq_one n μ hleft hright (by omega) d a

include hleft hright in
theorem suspension_eq_one_iff (d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n)
    (x : π_ d (Sphere n) (spherePole n)) : CubicalSphereSuspension.hom d n x = 1 ↔ x = 1 := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := (EHPCell.suspension_eq_one_iff_attaching n d hn hdn x).mp hx
    exact hc.symm.trans (attachingHom_eq_one n μ hleft hright (by omega) d c)
  · rintro rfl
    exact map_one _

include hleft hright in
theorem suspension_injective (d : ℕ) [NeZero d] (hn : 2 ≤ n) (hdn : d + 3 ≤ 3 * n) :
    Function.Injective (CubicalSphereSuspension.hom d n) := by
  intro a b hab
  apply div_eq_one.mp
  apply (suspension_eq_one_iff n μ hleft hright d hn hdn (a / b)).mp
  rw [map_div, hab, div_self']

end NoExoticSixSphere.JamesSphere.UnitalAttaching

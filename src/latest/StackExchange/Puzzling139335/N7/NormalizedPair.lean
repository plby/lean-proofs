import StackExchange.Puzzling139335.N7.NormalizedPair.Basic
import StackExchange.Puzzling139335.N7.GapEndpoints
import StackExchange.Puzzling139335.N7.WedgePair
import StackExchange.Puzzling139335.N7.SingletonPlacement
import StackExchange.Puzzling139335.N7Geometry

/-!
# The normalized seven-incidence branch

The exact third and singleton matrices are consequences of actual cover,
local weighted corner areas, and the determinant bound on two actual gap
endpoints. The final checked geometric obstruction then excludes cover.
-/

open Set

namespace Puzzling139335.N7.NormalizedPair

noncomputable section

variable {d : SquareDissection}

theorem third_formula (C : NormalizedPair d) (p : Plane) :
    C.third p = thirdMap (1 - C.b 0) (C.b 1) p :=
  third_placement_formula C.third C.b_square C.b_half C.b_ne_zero
    C.third_a C.third_b C.third_zero_square p

theorem source_support (C : NormalizedPair d) :
    ∀ p ∈ d.piece 0, (1 - C.b 0) * p 1 ≤ C.b 1 * (1 - p 0) :=
  third_placement_support C.third C.b_square C.b_half C.b_ne_zero
    C.third_a C.third_b C.third_zero_square C.third_fit

theorem gap_members (C : NormalizedPair d) :
    gapLeft (1 - C.b 0) (C.b 1) ∈ d.piece 3 ∧
      gapRight (1 - C.b 0) (C.b 1) ∈ d.piece 3 := by
  have hpos := source_parameters_positive C.third C.b_square C.b_half C.b_ne_zero
    C.third_a C.third_b
  have hst := source_cosine_gt_sine C.third C.b_square C.b_half C.b_ne_zero
    C.third_a C.third_b
  have hunit := source_parameters_unit C.third C.third_a C.third_b
  have hcle : 1 - C.b 0 ≤ 1 := sub_le_self 1 C.b_square.1.1
  have hT : thirdMap (1 - C.b 0) (C.b 1) '' d.piece 0 = d.piece 2 := by
    simpa only [C.third_formula] using C.third_image
  exact gap_endpoints_mem_fourth d hpos.1 hst hcle hunit C.lower_half
    C.reflected hT C.source_support

/-- The third intrinsic point has the exact height required by the
normalized obstruction, proved without an angular-sum premise. -/
theorem source_height (C : NormalizedPair d) : C.b 1 = (1 / 2 : ℝ) := by
  have hpos := source_parameters_positive C.third C.b_square C.b_half C.b_ne_zero
    C.third_a C.third_b
  have hst := source_cosine_gt_sine C.third C.b_square C.b_half C.b_ne_zero
    C.third_a C.third_b
  apply half_height_of_gap_endpoints (d.piece_subset 0) hpos.2 hpos.1 hst C.b_half
    (source_parameters_unit C.third C.third_a C.third_b) C.source_support
    C.single C.singleton_common_corner
  · simpa only [C.singleton_image] using C.gap_members.1
  · simpa only [C.singleton_image] using C.gap_members.2

theorem source_cosine (C : NormalizedPair d) : 1 - C.b 0 = N7Geometry.c :=
  source_cosine_of_half_height C.third C.b_square C.source_height C.third_a C.third_b

theorem third_eq_T (C : NormalizedPair d) (p : Plane) : C.third p = N7Geometry.T p :=
  third_placement_eq_T C.third C.b_square C.source_height C.b_ne_zero
    C.third_a C.third_b C.third_zero_square p

theorem singleton_images (C : NormalizedPair d) :
    C.single '' d.piece 0 = N7Geometry.Uplus '' d.piece 0 ∨
      C.single '' d.piece 0 = N7Geometry.Uminus '' d.piece 0 := by
  refine singleton_placement_image C.single (d.piece_subset 0) ?_
    C.singleton_common_corner ?_ ?_
  · simpa only [C.source_cosine, C.source_height] using C.source_support
  · have hleft := C.gap_members.1
    simpa only [C.source_cosine, C.source_height, C.singleton_image] using hleft
  · have hright := C.gap_members.2
    simpa only [C.source_cosine, C.source_height, C.singleton_image] using hright

/-- The actual normalized configuration cannot be a dissection. -/
theorem impossible (C : NormalizedPair d) : False := by
  have hH (p : Plane) : ReflectionSeparation.horizontal p = N7Geometry.Q p := by
    ext k
    fin_cases k <;> simp [N7Geometry.Q]
  have hQ : d.piece 1 = N7Geometry.Q '' d.piece 0 := by
    simpa only [hH] using C.reflected.symm
  have hT : d.piece 2 = N7Geometry.T '' d.piece 0 := by
    simpa only [C.third_eq_T] using C.third_image.symm
  have hU : d.piece 3 = N7Geometry.Uplus '' d.piece 0 ∨
      d.piece 3 = N7Geometry.Uminus '' d.piece 0 := by
    simpa only [C.singleton_image] using C.singleton_images
  exact N7Geometry.no_normalized_dissection d hQ hT hU

end

end Puzzling139335.N7.NormalizedPair

import StackExchange.Puzzling139335.N7.CornerGap
import StackExchange.Puzzling139335.CornerIncidence

/-!
# Actual normalized data in the seven-incidence case

All fields specify actual piece memberships or actual Euclidean placement
maps. The finite incidence argument constructs this data from a dissection;
no angle, support cone, or final contradiction is assumed here.
-/

open Set

namespace Puzzling139335.N7

noncomputable section

structure NormalizedPair (d : SquareDissection) where
  third : Plane ≃ᵃⁱ[ℝ] Plane
  single : Plane ≃ᵃⁱ[ℝ] Plane
  b : Plane
  bottom_left : corner 0 ∈ d.piece 0
  bottom_right : corner 1 ∈ d.piece 0
  reflected : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1
  third_image : third '' d.piece 0 = d.piece 2
  singleton_image : single '' d.piece 0 = d.piece 3
  b_mem : b ∈ d.piece 0
  b_ne_zero : b ≠ corner 0
  third_a : third (corner 1) = corner 2
  third_b : third b = corner 1
  singleton_count : d.tileCornerCount 3 = 1
  singleton_type : ∀ j : Fin 4, corner j ∈ d.piece 3 →
    single (corner 1) = corner j ∨ single b = corner j

end

end Puzzling139335.N7

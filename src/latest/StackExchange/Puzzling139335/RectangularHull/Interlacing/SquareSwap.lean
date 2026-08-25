import StackExchange.Puzzling139335.ExteriorContact.Square
import StackExchange.Puzzling139335.JordanTransport
import StackExchange.Puzzling139335.RectangularHull.Interlacing.SquareBoundary

/-! # Exchanging the two square coordinates -/

open Set Schoenflies

namespace Puzzling139335.RectangularHull

noncomputable section

/-- The coordinate interchange, as an actual plane homeomorphism. -/
def squareCoordinateSwap : Plane ≃ₜ Plane where
  toFun p := Schoenflies.Plane.mk (p 1) (p 0)
  invFun p := Schoenflies.Plane.mk (p 1) (p 0)
  left_inv p := by
    ext i
    fin_cases i <;> simp
  right_inv p := by
    ext i
    fin_cases i <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem squareCoordinateSwap_mk (x y : ℝ) :
    squareCoordinateSwap (Schoenflies.Plane.mk x y) = Schoenflies.Plane.mk y x := by
  rfl

@[simp] theorem squareCoordinateSwap_twice (p : Plane) :
    squareCoordinateSwap (squareCoordinateSwap p) = p :=
  squareCoordinateSwap.left_inv p

theorem squareCoordinateSwap_mem_unitSquare (p : Plane) :
    squareCoordinateSwap p ∈ unitSquare ↔ p ∈ unitSquare := by
  change (p 1 ∈ Icc (0 : ℝ) 1 ∧ p 0 ∈ Icc (0 : ℝ) 1) ↔
    (p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (0 : ℝ) 1)
  exact and_comm

theorem squareCoordinateSwap_image_unitSquare :
    squareCoordinateSwap '' unitSquare = unitSquare := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (squareCoordinateSwap_mem_unitSquare q).mpr hq
  · intro hp
    exact ⟨squareCoordinateSwap p, (squareCoordinateSwap_mem_unitSquare p).mpr hp,
      squareCoordinateSwap_twice p⟩

theorem squareCoordinateSwap_image_frontier_unitSquare :
    squareCoordinateSwap '' frontier unitSquare = frontier unitSquare := by
  rw [squareCoordinateSwap.image_frontier, squareCoordinateSwap_image_unitSquare]

/-- Reversed vertical order on the left and right sides is alternating order
around the square boundary. -/
theorem left_right_alternating_cutPair {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hd : 0 ≤ d) (hdc : d < c) (hc : c ≤ 1) :
    ∃ A B : Set Plane,
      IsCutPair (frontier unitSquare)
        (Schoenflies.Plane.mk 0 a) (Schoenflies.Plane.mk 1 c) A B ∧
      Schoenflies.Plane.mk 1 d ∈ A ∧ Schoenflies.Plane.mk 1 d ∉ B ∧
      Schoenflies.Plane.mk 0 b ∈ B ∧ Schoenflies.Plane.mk 0 b ∉ A := by
  obtain ⟨A, B, hcut, hdA, hdB, hbB, hbA⟩ :=
    opposing_alternating_cutPair ha hab hb hd hdc hc
  have hmem (X : Set Plane) (x y : ℝ) :
      Schoenflies.Plane.mk y x ∈ squareCoordinateSwap '' X ↔
      Schoenflies.Plane.mk x y ∈ X := by
    rw [← squareCoordinateSwap_mk x y]
    exact squareCoordinateSwap.injective.mem_set_image
  refine ⟨squareCoordinateSwap '' A, squareCoordinateSwap '' B, ?_,
    (hmem A d 1).mpr hdA, fun h => hdB ((hmem B d 1).mp h),
    (hmem B b 0).mpr hbB, fun h => hbA ((hmem A b 0).mp h)⟩
  simpa only [squareCoordinateSwap_image_frontier_unitSquare,
    squareCoordinateSwap_mk] using hcut.image_homeomorph squareCoordinateSwap

end

end Puzzling139335.RectangularHull

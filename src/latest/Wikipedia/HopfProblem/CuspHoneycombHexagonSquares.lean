import Wikipedia.HopfProblem.CuspHoneycombHexagonPositiveBasic
import Wikipedia.HopfProblem.CuspHoneycombHexagonCharts
import Wikipedia.HopfProblem.CuspHoneycombHexagonSquare
import Wikipedia.HopfProblem.CuspBoundaryIdentifications

/-!
# The six compact squares in the actual positive zero component

The maps here use the actual oriented toric coordinate inclusions. Their
images cover the literal positive component, and their outer coordinate
edges lie in precisely the actual neighboring component boundaries.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

open ToricCharts ToricFan ToricSpace ToricComponent

/-- The coordinate interchange induced on the real unit square. -/
def orientedSquare (i : Fin 6) (p : Square) : Square :=
  if i = 1 ∨ i = 2 ∨ i = 3 then
    ⟨![p.1 1, p.1 0], by intro k; fin_cases k <;> exact p.2 _⟩
  else p

@[simp] theorem orientedSquare_involutive (i : Fin 6) (p : Square) :
    orientedSquare i (orientedSquare i p) = p := by
  by_cases hi : i = 1 ∨ i = 2 ∨ i = 3
  · apply Subtype.ext
    funext k
    fin_cases k <;> simp [orientedSquare, hi]
  · simp [orientedSquare, hi]

theorem orientedCoordinates_square (i : Fin 6) (p : Square) :
    orientedCoordinates i (fun k => (p.1 k : ℂ)) =
      fun k => ((orientedSquare i p).1 k : ℂ) := by
  by_cases hi : i = 1 ∨ i = 2 ∨ i = 3
  · funext k
    fin_cases k <;> simp [orientedSquare, orientedCoordinates, hi]
  · simp [orientedSquare, orientedCoordinates, hi]

/-- A compact unit-square tile of the actual positive component. -/
def squarePoint (i : Fin 6) (p : Square) : PositiveE0 :=
  ⟨chartPoint i (fun k => (p.1 k : ℂ)), by
    apply (affineInclusion_mem_positive_iff (zeroChart i) _).mpr
    rw [orientedCoordinates_square]
    exact ⟨(orientedSquare i p).1, fun k => ((orientedSquare i p).2 k).1, rfl⟩⟩

@[simp] theorem squarePoint_coe (i : Fin 6) (p : Square) :
    (squarePoint i p : rayDivisor 0) = chartPoint i (fun k => (p.1 k : ℂ)) := rfl

theorem squarePoint_continuous (i : Fin 6) : Continuous (squarePoint i) := by
  have h : Continuous (fun p : Square => fun k => (p.1 k : ℂ)) :=
    continuous_pi fun k => Complex.continuous_ofReal.comp
      ((continuous_apply k).comp continuous_subtype_val)
  exact ((chartPoint_continuous i).comp h).subtype_mk _

theorem squarePoint_injective (i : Fin 6) : Function.Injective (squarePoint i) := by
  intro p q hpq
  have he := chartPoint_injective i (congrArg Subtype.val hpq)
  apply Subtype.ext
  funext k
  exact Complex.ofReal_injective (congrFun he k)

/-- All identifications between compact positive toric squares are exactly
the adjacent inner edges and the common all-one center. -/
theorem squarePoint_eq_iff (i j : Fin 6) (p q : Square) :
    squarePoint i p = squarePoint j q ↔ SquareRel i j p q := by
  rw [← chartPoint_square_eq_iff]
  exact Subtype.ext_iff

/-- These are the six ordinary unit squares, not merely unbounded affine
quadrants, and together they cover every point of the positive component. -/
theorem squarePoint_jointly_surjective (x : PositiveE0) :
    ∃ (i : Fin 6) (p : Square), squarePoint i p = x := by
  obtain ⟨i, r, hr, he⟩ := positiveE0_bounded_chart x
  let p : Square := ⟨r.1, fun k => ⟨r.2 k, hr k⟩⟩
  refine ⟨i, orientedSquare i p, Subtype.ext ?_⟩
  change affineInclusion (zeroChart i)
    (orientedCoordinates i (fun k => ((orientedSquare i p).1 k : ℂ))) = x.1
  rw [orientedCoordinates_square, orientedSquare_involutive]
  exact congrArg Subtype.val he

abbrev TileSpace := Fin 6 × Square

def squareProjection (p : TileSpace) : PositiveE0 := squarePoint p.1 p.2

theorem squareProjection_continuous : Continuous squareProjection :=
  continuous_prod_of_discrete_left.mpr squarePoint_continuous

theorem squareProjection_surjective : Function.Surjective squareProjection := by
  intro x
  obtain ⟨i, p, hp⟩ := squarePoint_jointly_surjective x
  exact ⟨(i, p), hp⟩

theorem squareProjection_isClosedMap : IsClosedMap squareProjection :=
  squareProjection_continuous.isClosedMap

/-- The actual positive component has the quotient topology of its six
compact toric squares. -/
theorem squareProjection_isQuotientMap : IsQuotientMap squareProjection :=
  squareProjection_isClosedMap.isQuotientMap
    squareProjection_continuous squareProjection_surjective

/-- The actual intersection with the component indexed by a neighboring ray. -/
def positiveBoundary (k : Fin 6) : Set PositiveE0 :=
  Subtype.val ⁻¹' CuspQuotient.componentBoundary (hexagonRay k)

theorem squarePoint_mem_positiveBoundary_iff (i k : Fin 6) (p : Square) :
    squarePoint i p ∈ positiveBoundary k ↔
      (k = i ∧ p.1 0 = 0) ∨ (k = i + 1 ∧ p.1 1 = 0) := by
  change (chartPoint i (fun j => (p.1 j : ℂ)) : Space) ∈ rayDivisor (hexagonRay k) ↔ _
  rw [chartPoint_mem_rayDivisor_iff]
  simp

theorem positiveBoundary_isClosed (k : Fin 6) : IsClosed (positiveBoundary k) :=
  (rayDivisor_isClosed (hexagonRay k)).preimage
    (continuous_subtype_val.comp continuous_subtype_val)

end Wikipedia.HopfProblem.CuspHoneycombHexagon

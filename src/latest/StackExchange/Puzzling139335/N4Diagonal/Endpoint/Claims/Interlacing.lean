import StackExchange.Puzzling139335.RectangularHull.Interlacing
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Same-side interlacing on the remaining square sides

Square reflections transport alternating contacts on the left, right, or top
side to the bottom-side obstruction for two disjoint Jordan interiors.
-/

open Set

namespace Puzzling139335.N4Diagonal.Endpoint

open ReflectionSeparation

/-- Two Jordan pieces with disjoint interiors cannot occupy strictly
alternating contacts on the left side of the square. -/
theorem left_side_interlacing_impossible {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : !₂[0, a] ∈ P) (hcP : !₂[0, c] ∈ P)
    (hbQ : !₂[0, b] ∈ Q) (hdQ : !₂[0, d] ∈ Q) : False := by
  let e := diagonal.toHomeomorph
  have hS : e '' unitSquare = unitSquare := diagonal_image_unitSquare
  have hPS' : e '' P ⊆ unitSquare := hS ▸ image_mono hPS
  have hQS' : e '' Q ⊆ unitSquare := hS ▸ image_mono hQS
  have he (t : ℝ) : e !₂[0, t] = Schoenflies.Plane.mk t 0 := by
    ext i
    fin_cases i <;> rfl
  exact RectangularHull.bottom_side_interlacing_impossible
    (hP.image_homeomorph e) (hQ.image_homeomorph e) hPS' hQS'
    (RectangularHull.disjoint_interiors_image_homeomorph hdis e)
    ha hab hbc hcd hd ⟨_, haP, he a⟩ ⟨_, hcP, he c⟩
    ⟨_, hbQ, he b⟩ ⟨_, hdQ, he d⟩

/-- Two Jordan pieces with disjoint interiors cannot occupy strictly
alternating contacts on the right side of the square. -/
theorem right_side_interlacing_impossible {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : !₂[1, a] ∈ P) (hcP : !₂[1, c] ∈ P)
    (hbQ : !₂[1, b] ∈ Q) (hdQ : !₂[1, d] ∈ Q) : False := by
  let e := vertical.toHomeomorph
  have hS : e '' unitSquare = unitSquare := vertical_image_unitSquare
  have hPS' : e '' P ⊆ unitSquare := hS ▸ image_mono hPS
  have hQS' : e '' Q ⊆ unitSquare := hS ▸ image_mono hQS
  have he (t : ℝ) : e !₂[1, t] = !₂[0, t] := by
    change vertical !₂[1, t] = !₂[0, t]
    ext i
    fin_cases i <;> simp
  exact left_side_interlacing_impossible
    (hP.image_homeomorph e) (hQ.image_homeomorph e) hPS' hQS'
    (RectangularHull.disjoint_interiors_image_homeomorph hdis e)
    ha hab hbc hcd hd ⟨_, haP, he a⟩ ⟨_, hcP, he c⟩
    ⟨_, hbQ, he b⟩ ⟨_, hdQ, he d⟩

/-- Two Jordan pieces with disjoint interiors cannot occupy strictly
alternating contacts on the top side of the square. -/
theorem top_side_interlacing_impossible {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : !₂[a, 1] ∈ P) (hcP : !₂[c, 1] ∈ P)
    (hbQ : !₂[b, 1] ∈ Q) (hdQ : !₂[d, 1] ∈ Q) : False := by
  let e := horizontal.toHomeomorph
  have hS : e '' unitSquare = unitSquare := horizontal_image_unitSquare
  have hPS' : e '' P ⊆ unitSquare := hS ▸ image_mono hPS
  have hQS' : e '' Q ⊆ unitSquare := hS ▸ image_mono hQS
  have he (t : ℝ) : e !₂[t, 1] = Schoenflies.Plane.mk t 0 := by
    change horizontal !₂[t, 1] = !₂[t, 0]
    ext i
    fin_cases i <;> simp
  exact RectangularHull.bottom_side_interlacing_impossible
    (hP.image_homeomorph e) (hQ.image_homeomorph e) hPS' hQS'
    (RectangularHull.disjoint_interiors_image_homeomorph hdis e)
    ha hab hbc hcd hd ⟨_, haP, he a⟩ ⟨_, hcP, he c⟩
    ⟨_, hbQ, he b⟩ ⟨_, hdQ, he d⟩

end Puzzling139335.N4Diagonal.Endpoint

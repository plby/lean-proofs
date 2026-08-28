import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebraComplex

/-!
# The literal signed Godement--Dolbeault cup on one-cochains
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  (D : Data R0 R1 R2 R3)

/-- The actual signed mixed component, with its two original endpoint cofaces. -/
def mixedCup (a : R1) (b : R0) (c : R1) (d : R0) : R1 :=
  a * D.cofaces.δ0 0 d - D.cofaces.δ0 1 b * c

/-- The actual alternating horizontal product of two pairs. -/
def wedge (_D : Data R0 R1 R2 R3) (b d : R0 × R0) : R0 := b.1 * d.2 - b.2 * d.1

/-- The requested original vertical, mixed, and horizontal cup components. -/
def cupOne (x y : D.One) : D.Two :=
  (D.cofaces.cupOne x.1 y.1,
    (D.mixedCup x.1 x.2.1 y.1 y.2.1, D.mixedCup x.1 x.2.2 y.1 y.2.2),
    D.wedge x.2 y.2)

@[simp] theorem cupOne_zero_left (y : D.One) : D.cupOne 0 y = 0 := by
  simp [cupOne, mixedCup, wedge]

@[simp] theorem cupOne_zero_right (x : D.One) : D.cupOne x 0 = 0 := by
  simp [cupOne, mixedCup, wedge]

theorem cupOne_add_left (x y z : D.One) :
    D.cupOne (x + y) z = D.cupOne x z + D.cupOne y z := by
  ext <;> simp [cupOne, mixedCup, wedge, SheafCupProduct.Coface.Data.cupOne] <;> ring

theorem cupOne_add_right (x y z : D.One) :
    D.cupOne x (y + z) = D.cupOne x y + D.cupOne x z := by
  ext <;> simp [cupOne, mixedCup, wedge, SheafCupProduct.Coface.Data.cupOne] <;> ring

/-- Multiplication of pure first-column cochains is the original vertical coface cup. -/
theorem cupOne_first (a c : R1) :
    D.cupOne (a, 0) (c, 0) = (D.cofaces.cupOne a c, 0, 0) := by
  simp [cupOne, mixedCup, wedge]

/-- Multiplication of pure last-row cochains is the literal alternating horizontal product. -/
theorem cupOne_last (b d : R0 × R0) :
    D.cupOne (0, b) (0, d) = (0, 0, b.1 * d.2 - b.2 * d.1) := by
  simp [cupOne, mixedCup, wedge]

/-- The literal left multiplication primitive for a degree-zero input. -/
def leftPrimitive (u : R0) (x : D.One) : D.One :=
  (D.cofaces.leftPrimitive u x.1, (u * x.2.1, u * x.2.2))

/-- The negative literal right multiplication primitive for a degree-zero input. -/
def rightPrimitive (x : D.One) (u : R0) : D.One :=
  (D.cofaces.rightPrimitive x.1 u, (-(x.2.1 * u), -(x.2.2 * u)))

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data

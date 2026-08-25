import StackExchange.Puzzling139335.N4TwoOneOne.BoundaryIntervals.FiniteException
import StackExchange.Puzzling139335.N4TwoOneOne.BoundaryIntervals.SideTransport

/-!
# Actual side intervals for two Jordan pieces

Two pieces that uniquely own opposite endpoints of a side and together cover
that side meet at a single cutoff.  Jordan noninterlacing proves that all
contacts occur in the required order; closedness supplies the cutoff itself.
The same theorem holds if a third set has at most one contact on the side.
-/

open Set

namespace Puzzling139335.N4TwoOneOne.BoundaryIntervals

/-- The geometric noninterlacing input for any side of the square. -/
theorem side_noninterlacing (s : Fin 4) {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q)) :
    Noninterlacing (sidePoint s) P Q := by
  intro a b c d ha hab hbc hcd hd haP hcP hbQ hdQ
  exact side_interlacing_impossible s hP hQ hPS hQS hdis
    ha hab hbc hcd hd haP hcP hbQ hdQ

/-- The exact partition of a full square side by two actual Jordan pieces. -/
theorem exists_side_cutoff (s : Fin 4) {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (h0P : sidePoint s 0 ∈ P) (h0Q : sidePoint s 0 ∉ Q)
    (h1P : sidePoint s 1 ∉ P) (h1Q : sidePoint s 1 ∈ Q)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, sidePoint s t ∈ P ∨ sidePoint s t ∈ Q) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (sidePoint s t ∈ P ↔ t ≤ l) ∧ (sidePoint s t ∈ Q ↔ l ≤ t) := by
  exact exists_cutoff_of_noninterlacing (continuous_sidePoint s) hP.isClosed hQ.isClosed
    (side_noninterlacing s hP hQ hPS hQS hdis) h0P h0Q h1P h1Q hcover

/-- The full-side partition remains exact when a third set supplies at most
one actual contact. -/
theorem exists_side_cutoff_of_subsingleton_contact (s : Fin 4) {P Q R : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (h0P : sidePoint s 0 ∈ P) (h0Q : sidePoint s 0 ∉ Q)
    (h1P : sidePoint s 1 ∉ P) (h1Q : sidePoint s 1 ∈ Q)
    (hR : (R ∩ sidePoint s '' Icc (0 : ℝ) 1).Subsingleton)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1,
      sidePoint s t ∈ P ∨ sidePoint s t ∈ Q ∨ sidePoint s t ∈ R) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (sidePoint s t ∈ P ↔ t ≤ l) ∧ (sidePoint s t ∈ Q ↔ l ≤ t) := by
  exact exists_cutoff_of_subsingleton_contact (continuous_sidePoint s)
    (sidePoint_injective s).injOn hP.isClosed hQ.isClosed
    (side_noninterlacing s hP hQ hPS hQS hdis) h0P h0Q h1P h1Q hR hcover

/-- Any increasing affine restriction of a square side has the same actual
Jordan noninterlacing property. -/
theorem subside_noninterlacing (s : Fin 4) {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Noninterlacing (fun t => sidePoint s (a + (b - a) * t)) P Q :=
  (side_noninterlacing s hP hQ hPS hQS hdis).affine_restrict ha hab hb

/-- A normalized cutoff for a nondegenerate subinterval of a square side.
For example, `s = 2`, `a = 0`, `b = 1/2` describes `(t/2, 1)`. -/
theorem exists_subside_cutoff (s : Fin 4) {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (haP : sidePoint s a ∈ P) (haQ : sidePoint s a ∉ Q)
    (hbP : sidePoint s b ∉ P) (hbQ : sidePoint s b ∈ Q)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1,
      sidePoint s (a + (b - a) * t) ∈ P ∨ sidePoint s (a + (b - a) * t) ∈ Q) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (sidePoint s (a + (b - a) * t) ∈ P ↔ t ≤ l) ∧
      (sidePoint s (a + (b - a) * t) ∈ Q ↔ l ≤ t) := by
  apply exists_cutoff_of_noninterlacing
    ((continuous_sidePoint s).comp (continuous_const.add (continuous_const.mul continuous_id)))
    hP.isClosed hQ.isClosed (subside_noninterlacing s hP hQ hPS hQS hdis ha hab hb)
  · simpa using haP
  · simpa using haQ
  · simpa using hbP
  · simpa using hbQ
  · exact hcover

/-- Direct dissection API for two named pieces on a full side. -/
theorem squareDissection_exists_side_cutoff (D : SquareDissection)
    (s : Fin 4) {i j : Fin 4} (hij : i ≠ j)
    (h0P : sidePoint s 0 ∈ D.piece i) (h0Q : sidePoint s 0 ∉ D.piece j)
    (h1P : sidePoint s 1 ∉ D.piece i) (h1Q : sidePoint s 1 ∈ D.piece j)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1,
      sidePoint s t ∈ D.piece i ∨ sidePoint s t ∈ D.piece j) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (sidePoint s t ∈ D.piece i ↔ t ≤ l) ∧
      (sidePoint s t ∈ D.piece j ↔ l ≤ t) :=
  exists_side_cutoff s (D.jordan i) (D.jordan j) (D.piece_subset i)
    (D.piece_subset j) (D.disjoint_interiors hij) h0P h0Q h1P h1Q hcover

/-- Direct dissection API with a set of exceptional contacts of cardinality
at most one. -/
theorem squareDissection_exists_side_cutoff_of_subsingleton_contact
    (D : SquareDissection) (s : Fin 4) {i j : Fin 4} {R : Set Plane} (hij : i ≠ j)
    (h0P : sidePoint s 0 ∈ D.piece i) (h0Q : sidePoint s 0 ∉ D.piece j)
    (h1P : sidePoint s 1 ∉ D.piece i) (h1Q : sidePoint s 1 ∈ D.piece j)
    (hR : (R ∩ sidePoint s '' Icc (0 : ℝ) 1).Subsingleton)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1,
      sidePoint s t ∈ D.piece i ∨ sidePoint s t ∈ D.piece j ∨ sidePoint s t ∈ R) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (sidePoint s t ∈ D.piece i ↔ t ≤ l) ∧
      (sidePoint s t ∈ D.piece j ↔ l ≤ t) :=
  exists_side_cutoff_of_subsingleton_contact s (D.jordan i) (D.jordan j)
    (D.piece_subset i) (D.piece_subset j) (D.disjoint_interiors hij)
    h0P h0Q h1P h1Q hR hcover

end Puzzling139335.N4TwoOneOne.BoundaryIntervals

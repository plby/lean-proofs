import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyCube
import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyFlatFrontier

/-!
# A boundary-preserving homeomorphism between the actual simplex and cube

The flattened simplex and coordinate cube are compact convex sets with
nonempty interiors. Mathlib's proved gauge-rescaling construction gives
an ambient homeomorphism mapping their sets and frontiers. Combining this
with the explicit coordinate homeomorphisms identifies the literal
barycentric boundary with the native cube boundary.
-/

noncomputable section

open Set
open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz

/-- Existence follows from the proved convex gauge-rescaling theorem,
with every geometric hypothesis established for the actual sets. -/
theorem exists_ambientSimplexCubeHomeomorph (n : ℕ) :
    ∃ e : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
      e '' flatSimplexSet n = realCubeSet n ∧
        e '' frontier (flatSimplexSet n) = frontier (realCubeSet n) := by
  obtain ⟨e, _, hclosed, hfrontier⟩ := exists_homeomorph_image_eq
    (convex_flatSimplexSet n) (interior_flatSimplexSet_nonempty n)
    ((isCompact_flatSimplexSet n).isVonNBounded ℝ)
    (convex_realCubeSet n) (interior_realCubeSet_nonempty n)
    ((isCompact_realCubeSet n).isVonNBounded ℝ)
  refine ⟨e, ?_, hfrontier⟩
  simpa only [(isClosed_flatSimplexSet n).closure_eq,
    (isClosed_realCubeSet n).closure_eq] using hclosed

/-- A chosen actual ambient homeomorphism, obtained from gauge rescaling. -/
def ambientSimplexCubeHomeomorph (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  Classical.choose (exists_ambientSimplexCubeHomeomorph n)

theorem ambientSimplexCubeHomeomorph_image (n : ℕ) :
    ambientSimplexCubeHomeomorph n '' flatSimplexSet n = realCubeSet n :=
  (Classical.choose_spec (exists_ambientSimplexCubeHomeomorph n)).1

theorem ambientSimplexCubeHomeomorph_image_frontier (n : ℕ) :
    ambientSimplexCubeHomeomorph n '' frontier (flatSimplexSet n) =
      frontier (realCubeSet n) :=
  (Classical.choose_spec (exists_ambientSimplexCubeHomeomorph n)).2

theorem ambientSimplexCubeHomeomorph_mem_iff (n : ℕ) (v : Fin n → ℝ) :
    v ∈ flatSimplexSet n ↔ ambientSimplexCubeHomeomorph n v ∈ realCubeSet n := by
  constructor
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image]
    exact ⟨v, hv, rfl⟩
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image] at hv
    obtain ⟨w, hw, he⟩ := hv
    exact (ambientSimplexCubeHomeomorph n).injective he ▸ hw

theorem ambientSimplexCubeHomeomorph_mem_frontier_iff (n : ℕ) (v : Fin n → ℝ) :
    v ∈ frontier (flatSimplexSet n) ↔
      ambientSimplexCubeHomeomorph n v ∈ frontier (realCubeSet n) := by
  constructor
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image_frontier]
    exact ⟨v, hv, rfl⟩
  · intro hv
    rw [← ambientSimplexCubeHomeomorph_image_frontier] at hv
    obtain ⟨w, hw, he⟩ := hv
    exact (ambientSimplexCubeHomeomorph n).injective he ▸ hw

/-- Restriction of the actual ambient homeomorphism to the two closed sets. -/
def flatCubeHomeomorph (n : ℕ) : ↥(flatSimplexSet n) ≃ₜ ↥(realCubeSet n) :=
  (ambientSimplexCubeHomeomorph n).subtype (ambientSimplexCubeHomeomorph_mem_iff n)

/-- A genuine homeomorphism from Mathlib's actual simplex to its native cube. -/
def simplexCubeHomeomorph (n : ℕ) : Simplex n ≃ₜ (Fin n → I) :=
  (simplexFlatHomeomorph n).trans ((flatCubeHomeomorph n).trans (realCubeHomeomorph n))

/-- The actual barycentric and cubical boundary predicates correspond exactly. -/
theorem simplexCubeHomeomorph_boundary_iff (n : ℕ) (s : Simplex n) :
    simplexCubeHomeomorph n s ∈ Cube.boundary (Fin n) ↔
      s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n := by
  change realCubeHomeomorph n (flatCubeHomeomorph n (simplexFlatHomeomorph n s)) ∈
    Cube.boundary (Fin n) ↔ _
  rw [realCubeHomeomorph_mem_boundary_iff]
  change ambientSimplexCubeHomeomorph n (simplexFlatHomeomorph n s).val ∈
    frontier (realCubeSet n) ↔ _
  rw [← ambientSimplexCubeHomeomorph_mem_frontier_iff,
    simplexFlatHomeomorph_mem_frontier_iff]

theorem simplexCubeHomeomorph_symm_boundary_iff (n : ℕ) (u : Fin n → I) :
    (simplexCubeHomeomorph n).symm u ∈ SecondHurewicz.SimplyConnected.simplexBoundary n ↔
      u ∈ Cube.boundary (Fin n) := by
  rw [← simplexCubeHomeomorph_boundary_iff, Homeomorph.apply_symm_apply]

end Wikipedia.HopfProblem.HigherHurewicz

import ErdosProblems.Erdos186.PZ.ConvexDensity.Definitions
import Mathlib.Data.Finset.Sort

/-!
# The one-dimensional case of the Pham--Zakharov convex-density lemma

In one dimension a finite set in `δ`-convex position necessarily has
`δ ≥ 1 / 2`.  Indeed, choose a median of the set.  Every linear functional
on the line is either order-preserving or order-reversing, so a supporting
half-space through the median contains at least half of the points.

This proves the dimension-one input to the Pham--Zakharov density lemma with
the absolute threshold `δ₀ = 1 / 2`: its small-`δ` hypotheses are impossible.
-/

open scoped BigOperators

namespace Erdos186.PZ.ConvexDensity

open Erdos186.ConvexGeometry

noncomputable section

/-- A finite nonempty linear order has a point with at least half of the set
on either side (including the point itself).  The inequalities are kept over
`ℕ`, avoiding all rounding conventions for a median. -/
private theorem exists_bisecting_point
    {α : Type*} [LinearOrder α] (X : Finset α) (hX : X.Nonempty) :
    ∃ a ∈ X,
      X.card ≤ 2 * (X.filter fun x ↦ x ≤ a).card ∧
      X.card ≤ 2 * (X.filter fun x ↦ a ≤ x).card := by
  classical
  let n := X.card
  let m := n / 2
  have hn : 0 < n := by simpa [n] using Finset.card_pos.mpr hX
  have hm : m < n := by omega
  let e : Fin n ↪o α := X.orderEmbOfFin rfl
  let im : Fin n := ⟨m, hm⟩
  let a : α := e im
  have ha : a ∈ X := by
    simp [a, e]
  have hlower : m + 1 ≤ (X.filter fun x ↦ x ≤ a).card := by
    let f : Fin (m + 1) → {x // x ∈ X.filter fun x ↦ x ≤ a} := fun i ↦
      ⟨e ⟨i, by omega⟩, by
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · simp [e]
        · apply e.monotone
          simp [im]
          omega⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      simpa [f] using hij
    simpa using Fintype.card_le_of_injective f hf
  have hupper : n - m ≤ (X.filter fun x ↦ a ≤ x).card := by
    let f : Fin (n - m) → {x // x ∈ X.filter fun x ↦ a ≤ x} := fun i ↦
      ⟨e ⟨m + i, by omega⟩, by
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · simp [e]
        · apply e.monotone
          simp [im]⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      simpa [f] using hij
    simpa using Fintype.card_le_of_injective f hf
  refine ⟨a, ha, ?_, ?_⟩
  · change n ≤ 2 * (X.filter fun x ↦ x ≤ a).card
    omega
  · change n ≤ 2 * (X.filter fun x ↦ a ≤ x).card
    omega

/-- Every vector in `EuclideanSpace ℝ (Fin 1)` is its sole coordinate times
the constant unit vector. -/
private theorem eq_coordinate_smul_unit (x : EuclideanSpace ℝ (Fin 1)) :
    x = x 0 • (WithLp.toLp 2 fun _ : Fin 1 ↦ (1 : ℝ)) := by
  ext i
  fin_cases i
  simp

/-- The sharp universal obstruction in dimension one: a nonempty finite set
cannot be in `δ`-convex position for `δ < 1/2`. -/
theorem one_half_le_of_isDeltaConvexPosition
    {X : Finset (EuclideanSpace ℝ (Fin 1))} {δ : ℝ}
    (hX : X.Nonempty) (hconv : IsDeltaConvexPosition δ X) :
    (1 : ℝ) / 2 ≤ δ := by
  classical
  have hcoord : Function.Injective
      (fun x : EuclideanSpace ℝ (Fin 1) ↦ x 0) := by
    intro x y hxy
    ext i
    fin_cases i
    exact hxy
  let : LinearOrder (EuclideanSpace ℝ (Fin 1)) :=
    LinearOrder.lift' (fun x ↦ x 0) hcoord
  obtain ⟨a, ha, hlower, hupper⟩ := exists_bisecting_point X hX
  obtain ⟨ℓ, hcount⟩ :=
    (isDeltaConvexPosition_iff_supporting_through_point.mp hconv) a ha
  let u : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 fun _ : Fin 1 ↦ (1 : ℝ)
  have hvalue (x : EuclideanSpace ℝ (Fin 1)) : ℓ x = x 0 * ℓ u := by
    have hx : x = x 0 • u := by
      simpa [u] using eq_coordinate_smul_unit x
    calc
      ℓ x = ℓ (x 0 • u) := congrArg ℓ hx
      _ = x 0 • ℓ u := map_smul ℓ (x 0) u
      _ = x 0 * ℓ u := smul_eq_mul (x 0) (ℓ u)
  have hhalf : (X.card : ℝ) / 2 ≤ halfspaceCount X ℓ (ℓ a) := by
    rw [halfspaceCount_eq_card_filter]
    rcases le_total 0 (ℓ u) with hu | hu
    · have hsub :
          X.filter (fun x ↦ a ≤ x) ⊆ X.filter (fun x ↦ ℓ a ≤ ℓ x) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        have hxcoord := hx.2
        change a 0 ≤ x 0 at hxcoord
        calc
          ℓ a = a 0 * ℓ u := hvalue a
          _ ≤ x 0 * ℓ u := mul_le_mul_of_nonneg_right hxcoord hu
          _ = ℓ x := (hvalue x).symm
      have hc : (X.filter fun x ↦ a ≤ x).card ≤
          (X.filter fun x ↦ ℓ a ≤ ℓ x).card := Finset.card_le_card hsub
      have hnat : X.card ≤ 2 * (X.filter fun x ↦ ℓ a ≤ ℓ x).card := by omega
      have hreal : (X.card : ℝ) ≤
          2 * ((X.filter fun x ↦ ℓ a ≤ ℓ x).card : ℝ) := by
        exact_mod_cast hnat
      linarith
    · have hsub :
          X.filter (fun x ↦ x ≤ a) ⊆ X.filter (fun x ↦ ℓ a ≤ ℓ x) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        have hxcoord := hx.2
        change x 0 ≤ a 0 at hxcoord
        calc
          ℓ a = a 0 * ℓ u := hvalue a
          _ ≤ x 0 * ℓ u := mul_le_mul_of_nonpos_right hxcoord hu
          _ = ℓ x := (hvalue x).symm
      have hc : (X.filter fun x ↦ x ≤ a).card ≤
          (X.filter fun x ↦ ℓ a ≤ ℓ x).card := Finset.card_le_card hsub
      have hnat : X.card ≤ 2 * (X.filter fun x ↦ ℓ a ≤ ℓ x).card := by omega
      have hreal : (X.card : ℝ) ≤
          2 * ((X.filter fun x ↦ ℓ a ≤ ℓ x).card : ℝ) := by
        exact_mod_cast hnat
      linarith
  have hcard : (0 : ℝ) < X.card := by
    exact_mod_cast Finset.card_pos.mpr hX
  nlinarith

/-- Contrapositive form of the dimension-one convex-density obstruction. -/
theorem not_isDeltaConvexPosition_of_lt_one_half
    {X : Finset (EuclideanSpace ℝ (Fin 1))} {δ : ℝ}
    (hX : X.Nonempty) (hδ : δ < (1 : ℝ) / 2) :
    ¬ IsDeltaConvexPosition δ X := by
  intro hconv
  exact (not_le_of_gt hδ) (one_half_le_of_isDeltaConvexPosition hX hconv)

/-- The exact dimension-one specialization of `PZLemmaOneStatement`.

The choices are `tau = min (epsilon / 10) (1 / 2)`, `deltaZero = 1 / 2`,
and `largeEnough = 1`.  The cardinality hypothesis makes `X` nonempty, and
the one-dimensional median obstruction then contradicts `delta < deltaZero`.
Thus the full `ConvexDensityOutput` follows without weakening any of its
fields. -/
theorem pzLemmaOneStatement_dimension_one :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ tau deltaZero : ℝ,
        0 < tau ∧ tau < 1 ∧ 0 < deltaZero ∧
        ∀ delta : ℝ, 0 < delta → delta < deltaZero →
          ∃ largeEnough : ℕ,
            ∀ (Omega : Set (EuclideanPoint 1))
                (X : Finset (EuclideanPoint 1)),
              IsConvexBody Omega →
              (X : Set (EuclideanPoint 1)) ⊆ Omega →
              largeEnough ≤ X.card →
              IsDeltaConvexPosition delta X →
              ConvexDensityOutput epsilon tau delta Omega X := by
  intro epsilon hepsilon
  refine ⟨min (epsilon / 10) ((1 : ℝ) / 2), (1 : ℝ) / 2, ?_, ?_, by norm_num, ?_⟩
  · exact lt_min (by positivity) (by norm_num)
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · intro delta _hdelta hdeltaSmall
    refine ⟨1, ?_⟩
    intro Omega X _hOmega _hsubset hcard hconv
    have hX : X.Nonempty := Finset.card_pos.mp (by omega)
    exact False.elim
      ((not_isDeltaConvexPosition_of_lt_one_half hX hdeltaSmall) hconv)

end

end Erdos186.PZ.ConvexDensity

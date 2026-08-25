import Util.IncidenceGeometry.PolygonalPath
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic

open Classical
noncomputable section

lemma ArcCrossingCutWindowParameters
    (α : PolygonalPath) (i : ℕ) (hi : i + 1 < α.vertices.length)
    (x before after : EuclideanSpace ℝ (Fin 2)) (p : ℝ) :
    0 < p →
      p < 1 →
        AffineMap.lineMap α.vertices[i] α.vertices[i + 1] p = x →
          before ∈ openSegment ℝ α.vertices[i] x →
            after ∈ openSegment ℝ x α.vertices[i + 1] →
              ∃ b a : ℝ,
                0 < b ∧ b < p ∧ p < a ∧ a < 1 ∧
                  AffineMap.lineMap α.vertices[i] α.vertices[i + 1] b = before ∧
                    AffineMap.lineMap α.vertices[i] α.vertices[i + 1] a = after := by
  intro hp0 hp1 hx hbefore hafter
  let A := α.vertices[i]
  let B := α.vertices[i + 1]
  rw [openSegment_eq_image_lineMap] at hbefore
  rcases hbefore with ⟨θb, hθb, hθb_eq⟩
  rw [openSegment_eq_image_lineMap] at hafter
  rcases hafter with ⟨θa, hθa, hθa_eq⟩
  let b : ℝ := θb * p
  let a : ℝ := 1 - (1 - θa) * (1 - p)
  have hb_pos : 0 < b := by
    exact mul_pos hθb.1 hp0
  have hb_lt_p : b < p := by
    have hmul : θb * p < 1 * p := mul_lt_mul_of_pos_right hθb.2 hp0
    simpa [b] using hmul
  have h1mp_pos : 0 < 1 - p := by linarith
  have h1mθa_pos : 0 < 1 - θa := by linarith [hθa.2]
  have h1mθa_lt_one : 1 - θa < 1 := by linarith [hθa.1]
  have hprod_pos : 0 < (1 - θa) * (1 - p) :=
    mul_pos h1mθa_pos h1mp_pos
  have hprod_lt : (1 - θa) * (1 - p) < 1 * (1 - p) :=
    mul_lt_mul_of_pos_right h1mθa_lt_one h1mp_pos
  have hp_lt_a : p < a := by
    dsimp [a]
    linarith
  have ha_lt_one : a < 1 := by
    dsimp [a]
    linarith
  have hb_map :
      AffineMap.lineMap α.vertices[i] α.vertices[i + 1] b = before := by
    calc
      AffineMap.lineMap α.vertices[i] α.vertices[i + 1] b =
          AffineMap.lineMap A B (θb * p) := by rfl
      _ = AffineMap.lineMap A (AffineMap.lineMap A B p) θb := by
          rw [AffineMap.lineMap_lineMap_right]
      _ = AffineMap.lineMap A x θb := by rw [hx]
      _ = before := by simpa [A] using hθb_eq
  have ha_map :
      AffineMap.lineMap α.vertices[i] α.vertices[i + 1] a = after := by
    calc
      AffineMap.lineMap α.vertices[i] α.vertices[i + 1] a =
          AffineMap.lineMap A B (1 - (1 - θa) * (1 - p)) := by rfl
      _ = AffineMap.lineMap (AffineMap.lineMap A B p) B θa := by
          rw [AffineMap.lineMap_lineMap_left]
      _ = AffineMap.lineMap x B θa := by rw [hx]
      _ = after := by simpa [B] using hθa_eq
  exact ⟨b, a, hb_pos, hb_lt_p, hp_lt_a, ha_lt_one, hb_map, ha_map⟩

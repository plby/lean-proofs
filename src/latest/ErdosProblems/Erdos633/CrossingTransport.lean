import ErdosProblems.Erdos633.BoundaryChain
import ErdosProblems.Erdos633.CrossingDissection

/-!
# Transporting an actual dissection through its marked edge lines

A point map may reorder collinear vertices. If it preserves the supporting
lines at the finite marked vertices, and all triangle orientations change
by one common sign, the directed boundary theorem and crossing reconstruction
prove that the image triangles form an actual dissection.
-/

namespace Erdos633

open MeasureTheory
open scoped BigOperators

theorem edgeCrossingAt_add_onAxis (z p d a b : ℂ) (hd : d ≠ 0)
    (ha : OnAxis p d a) (hb : OnAxis p d b) :
    edgeCrossingAt z p a + edgeCrossingAt z a b = edgeCrossingAt z p b := by
  have h := edgeCrossingAt_lineMap_add z p (p + d) 0
    (axisParameter p d a) (axisParameter p d b)
  change edgeCrossingAt z (axisMap p d 0) (axisMap p d (axisParameter p d a)) +
      edgeCrossingAt z (axisMap p d (axisParameter p d a))
        (axisMap p d (axisParameter p d b)) =
      edgeCrossingAt z (axisMap p d 0) (axisMap p d (axisParameter p d b)) at h
  rw [axisMap_axisParameter p d a hd ha, axisMap_axisParameter p d b hd hb] at h
  simpa only [axisMap, AffineMap.lineMap_apply_zero] using h

def TriangleDissection.EdgeLinePreserving {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (f : ℂ → ℂ) : Prop :=
  ∀ Q : Triangle, (Q = P ∨ ∃ i : Fin N, Q = T.tile i) → ∀ k : Fin 3,
    f (Q.edgeStart k) ≠ f (Q.edgeEnd k) ∧
    ∀ a ∈ T.vertexFinset, OnAxis (Q.edgeStart k) (Q.edgeVector k) a →
      OnAxis (f (Q.edgeStart k)) (f (Q.edgeEnd k) - f (Q.edgeStart k)) (f a)

theorem TriangleDissection.edgeAdditive_crossing_of_line_preserving
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (f : ℂ → ℂ) (hf : T.EdgeLinePreserving f) (z : ℂ) :
    T.EdgeAdditive (fun a b => (edgeCrossingAt z (f a) (f b) : ℝ)) := by
  intro Q hQ k a ha b hb hla hlb
  have h := hf Q hQ k
  have heq := edgeCrossingAt_add_onAxis z (f (Q.edgeStart k))
    (f (Q.edgeEnd k) - f (Q.edgeStart k)) (f a) (f b)
    (sub_ne_zero.mpr h.1.symm) (h.2 a ha hla) (h.2 b hb hlb)
  dsimp only
  exact_mod_cast heq

def Triangle.VertexImage (P Q : Triangle) (f : ℂ → ℂ) : Prop :=
  ∀ k : Fin 3, Q.vertex k = f (P.vertex k)

theorem Triangle.VertexImage.edgeStart {P Q : Triangle} {f : ℂ → ℂ}
    (h : P.VertexImage Q f) (k : Fin 3) : Q.edgeStart k = f (P.edgeStart k) := by
  fin_cases k
  · exact h 1
  · exact h 2
  · exact h 0

theorem Triangle.VertexImage.edgeEnd {P Q : Triangle} {f : ℂ → ℂ}
    (h : P.VertexImage Q f) (k : Fin 3) : Q.edgeEnd k = f (P.edgeEnd k) := by
  fin_cases k
  · exact h 2
  · exact h 0
  · exact h 1

theorem Triangle.directedBoundaryValue_crossing_image (P Q : Triangle)
    (f : ℂ → ℂ) (h : P.VertexImage Q f) (z : ℂ) :
    P.directedBoundaryValue (fun a b => (edgeCrossingAt z (f a) (f b) : ℝ)) =
      P.orientationSign * (Q.crossingAt z : ℝ) := by
  rw [Q.crossingAt_eq_sum_edges, Int.cast_sum, Finset.mul_sum]
  unfold Triangle.directedBoundaryValue
  exact Finset.sum_congr rfl (fun k _ => by rw [h.edgeStart k, h.edgeEnd k])

theorem TriangleDissection.crossing_image_identity
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (f : ℂ → ℂ) (hf : T.EdgeLinePreserving f)
    (P' : Triangle) (Q' : Fin N → Triangle)
    (hP : P.VertexImage P' f) (hQ : ∀ i : Fin N, (T.tile i).VertexImage (Q' i) f)
    (z : ℂ) : P.orientationSign * (P'.crossingAt z : ℝ) =
      ∑ i : Fin N, (T.tile i).orientationSign * ((Q' i).crossingAt z : ℝ) := by
  have h := T.directedBoundaryValue_eq_sum
    (fun a b => (edgeCrossingAt z (f a) (f b) : ℝ))
    (T.edgeAdditive_crossing_of_line_preserving f hf z)
  simpa only [P.directedBoundaryValue_crossing_image P' f hP z,
    (T.tile _).directedBoundaryValue_crossing_image (Q' _) f (hQ _) z] using h

theorem TriangleDissection.oriented_crossing_image_identity
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (f : ℂ → ℂ) (hf : T.EdgeLinePreserving f)
    (P' : Triangle) (Q' : Fin N → Triangle)
    (hP : P.VertexImage P' f) (hQ : ∀ i : Fin N, (T.tile i).VertexImage (Q' i) f)
    (hsign : ∀ i : Fin N, (Q' i).orientationSign * (T.tile i).orientationSign =
      P'.orientationSign * P.orientationSign) (z : ℂ) :
    P'.orientationSign * (P'.crossingAt z : ℝ) =
      ∑ i : Fin N, (Q' i).orientationSign * ((Q' i).crossingAt z : ℝ) := by
  let ε := P'.orientationSign * P.orientationSign
  have heP : ε * P.orientationSign = P'.orientationSign := by
    dsimp [ε]
    rw [mul_assoc, P.orientationSign_mul_self, mul_one]
  have heQ (i : Fin N) : ε * (T.tile i).orientationSign = (Q' i).orientationSign := by
    change (P'.orientationSign * P.orientationSign) * (T.tile i).orientationSign = _
    rw [← hsign i, mul_assoc, (T.tile i).orientationSign_mul_self, mul_one]
  have h := congrArg (fun x : ℝ => ε * x) (T.crossing_image_identity f hf P' Q' hP hQ z)
  simpa only [Finset.mul_sum, ← mul_assoc, heP, heQ] using h

/-- Coverage and disjoint interiors are conclusions. The hypotheses refer only
to the original marked edge lines, vertex images, and orientation signs. -/
def TriangleDissection.mapVertexImages
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (f : ℂ → ℂ) (hf : T.EdgeLinePreserving f)
    (P' : Triangle) (Q' : Fin N → Triangle)
    (hP : P.VertexImage P' f) (hQ : ∀ i : Fin N, (T.tile i).VertexImage (Q' i) f)
    (hsign : ∀ i : Fin N, (Q' i).orientationSign * (T.tile i).orientationSign =
      P'.orientationSign * P.orientationSign) : TriangleDissection P' N :=
  TriangleDissection.ofOrientedCrossing P' Q' (Filter.Eventually.of_forall
    (T.oriented_crossing_image_identity f hf P' Q' hP hQ hsign))

end Erdos633

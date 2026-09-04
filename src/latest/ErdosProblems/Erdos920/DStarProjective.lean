import ErdosProblems.Erdos920.Projective
import ErdosProblems.Erdos920.DStar
import ErdosProblems.Erdos920.RamseyPackaging

/-!
# The projective `D*` digraph

This file realizes the vector-representative construction from `DStar.lean`
on the finite set of incident ordered pairs of projective points.  Its vertex
count is the product of the number of points of `PG(t,q)` and the number of
points of a projective hyperplane.
-/

open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.ProjectiveDStar

noncomputable section

open Erdos920.Projective

/-- The vertices of `D*(t,q)`: an ordered incident pair of projective points
in `PG(t,q)`. -/
abbrev Vertex (q t : ℕ) [Fact q.Prime] :=
  {p : Point (ZMod q) (t + 1) × Point (ZMod q) (t + 1) //
    Orthogonal p.1 p.2}

instance vertexFintype (q t : ℕ) [Fact q.Prime] : Fintype (Vertex q t) :=
  Fintype.ofFinite (Vertex q t)

/-- First projective coordinate of a `D*` vertex. -/
def leftPoint {q t : ℕ} [Fact q.Prime] (u : Vertex q t) :
    Point (ZMod q) (t + 1) := u.1.1

/-- Second projective coordinate of a `D*` vertex. -/
def rightPoint {q t : ℕ} [Fact q.Prime] (u : Vertex q t) :
    Point (ZMod q) (t + 1) := u.1.2

@[simp] theorem incident {q t : ℕ} [Fact q.Prime] (u : Vertex q t) :
    Orthogonal (leftPoint u) (rightPoint u) := u.2

/-- Incident pairs as a subtype are equivalent to a point together with one
of its neighbors. -/
def vertexEquivSigma (q t : ℕ) [Fact q.Prime] :
    Vertex q t ≃ (Σ x : Point (ZMod q) (t + 1), Neighbors x) where
  toFun u := ⟨leftPoint u, ⟨rightPoint u, incident u⟩⟩
  invFun u := ⟨(u.1, u.2.1), u.2.2⟩
  left_inv u := by cases u; rfl
  right_inv u := by cases u with | mk x y => cases y; rfl

/-- The projectively well-defined arc relation. -/
def Arc {q t : ℕ} [Fact q.Prime] (u v : Vertex q t) : Prop :=
  Orthogonal (leftPoint u) (rightPoint v) ∧
    ¬ Orthogonal (leftPoint v) (rightPoint u)

instance arcDecidable {q t : ℕ} [Fact q.Prime] : DecidableRel (@Arc q t _) :=
  Classical.decRel _

/-- Replace each projective point by Mathlib's chosen nonzero representative.
This lands in the vector construction from `DStar.lean`. -/
def toVectorVertex {q t : ℕ} [Fact q.Prime] (u : Vertex q t) :
    DStar.Vertex (ZMod q) t where
  left := (leftPoint u).rep
  right := (rightPoint u).rep
  left_ne_zero := (leftPoint u).rep_nonzero
  right_ne_zero := (rightPoint u).rep_nonzero
  orthogonal := by
    have h := incident u
    rw [← (leftPoint u).mk_rep, ← (rightPoint u).mk_rep] at h
    exact (Projectivization.orthogonal_mk
      (leftPoint u).rep_nonzero (rightPoint u).rep_nonzero).mp h

/-- The projective arc is exactly the vector-representative arc. -/
theorem arc_iff_vectorArc {q t : ℕ} [Fact q.Prime] (u v : Vertex q t) :
    Arc u v ↔ DStar.Arc (toVectorVertex u) (toVectorVertex v) := by
  constructor
  · rintro ⟨huv, hvu⟩
    constructor
    · rw [← (leftPoint u).mk_rep, ← (rightPoint v).mk_rep] at huv
      exact (Projectivization.orthogonal_mk
        (leftPoint u).rep_nonzero (rightPoint v).rep_nonzero).mp huv
    · intro hzero
      apply hvu
      rw [← (leftPoint v).mk_rep, ← (rightPoint u).mk_rep]
      exact (Projectivization.orthogonal_mk
        (leftPoint v).rep_nonzero (rightPoint u).rep_nonzero).mpr hzero
  · rintro ⟨huv, hvu⟩
    constructor
    · rw [← (leftPoint u).mk_rep, ← (rightPoint v).mk_rep]
      exact (Projectivization.orthogonal_mk
        (leftPoint u).rep_nonzero (rightPoint v).rep_nonzero).mpr huv
    · intro horth
      apply hvu
      rw [← (leftPoint v).mk_rep, ← (rightPoint u).mk_rep] at horth
      exact (Projectivization.orthogonal_mk
        (leftPoint v).rep_nonzero (rightPoint u).rep_nonzero).mp horth

/-- The projective `D*` relation has no transitive tournament on `t+1`
vertices. -/
theorem no_transitiveTournament (q t : ℕ) [Fact q.Prime] :
    ¬ ∃ v : Fin (t + 1) → Vertex q t, Function.Injective v ∧
      ∀ {i j : Fin (t + 1)}, i < j → Arc (v i) (v j) := by
  rintro ⟨v, hv, harc⟩
  apply DStar.no_transitiveTournament (K := ZMod q) t
  refine ⟨fun i ↦ toVectorVertex (v i), ?_, ?_⟩
  · intro i j hij
    apply hv
    -- Equality of chosen representatives determines both projective points.
    have hleft : leftPoint (v i) = leftPoint (v j) := by
      rw [← (leftPoint (v i)).mk_rep, ← (leftPoint (v j)).mk_rep]
      exact congrArg (fun z : DStar.Vertex (ZMod q) t ↦
        Projectivization.mk (ZMod q) z.left z.left_ne_zero) hij
    have hright : rightPoint (v i) = rightPoint (v j) := by
      rw [← (rightPoint (v i)).mk_rep, ← (rightPoint (v j)).mk_rep]
      exact congrArg (fun z : DStar.Vertex (ZMod q) t ↦
        Projectivization.mk (ZMod q) z.right z.right_ne_zero) hij
    apply Subtype.ext
    exact Prod.ext hleft hright
  · intro i j hij
    exact (arc_iff_vectorArc (v i) (v j)).mp (harc hij)

/-- The digraph interface used by `RamseyPackaging.DStarWitness`. -/
def digraph (q t : ℕ) [Fact q.Prime] :
    RamseyPackaging.Digraph (Vertex q t) where
  arc := Arc

theorem digraph_transitiveTournamentFree (q t : ℕ) [Fact q.Prime] :
    ¬ (digraph q t).HasTransitiveTournament (t + 1) := by
  rintro ⟨v, hv, harc⟩
  exact no_transitiveTournament q t ⟨v, hv, fun {_ _} h ↦ harc _ _ h⟩

/-- Exact cardinality of the projective `D*` vertex set. -/
theorem card_vertex (q t : ℕ) [Fact q.Prime] :
    Fintype.card (Vertex q t) =
      (∑ i ∈ Finset.range (t + 1), q ^ i) *
        (∑ i ∈ Finset.range t, q ^ i) := by
  let : Fintype (Point (ZMod q) (t + 1)) := Fintype.ofFinite _
  let (x : Point (ZMod q) (t + 1)) : Fintype (Neighbors x) :=
    Fintype.ofFinite _
  rw [Fintype.card_congr (vertexEquivSigma q t), Fintype.card_sigma]
  have hneigh (x : Point (ZMod q) (t + 1)) :
      Fintype.card (Neighbors x) = ∑ i ∈ Finset.range t, q ^ i := by
    rw [← Nat.card_eq_fintype_card]
    simpa using natCard_neighbors_zmod q x
  have hpoint : Fintype.card (Point (ZMod q) (t + 1)) =
      ∑ i ∈ Finset.range (t + 1), q ^ i := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_point_zmod q (t + 1)
  simp_rw [hneigh]
  rw [Finset.sum_const, Finset.card_univ, hpoint, nsmul_eq_mul]
  norm_num

/-- A single geometric-series term is bounded by the whole sum. -/
lemma pow_le_geometricSum (q d i : ℕ) (hi : i < d) :
    q ^ i ≤ ∑ j ∈ Finset.range d, q ^ j := by
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (by simp [hi])

/-- The vertex count has the lower order of magnitude used in the Ramsey
packaging. -/
theorem pow_two_mul_sub_one_le_card_vertex (q t : ℕ) [Fact q.Prime]
    (ht : 1 ≤ t) :
    q ^ (2 * t - 1) ≤ Fintype.card (Vertex q t) := by
  rw [card_vertex]
  have h1 := pow_le_geometricSum q (t + 1) t (by omega)
  have h2 := pow_le_geometricSum q t (t - 1) (by omega)
  calc
    q ^ (2 * t - 1) = q ^ t * q ^ (t - 1) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ (∑ i ∈ Finset.range (t + 1), q ^ i) *
        (∑ i ∈ Finset.range t, q ^ i) := Nat.mul_le_mul h1 h2

/-- Each geometric sum over a prime field is at most twice its largest term.
This coarse bound is convenient in the container estimates. -/
lemma geometricSum_le_two_mul_pow (q d : ℕ) (hq : 2 ≤ q) (hd : 1 ≤ d) :
    ∑ i ∈ Finset.range d, q ^ i ≤ 2 * q ^ (d - 1) := by
  rw [Nat.geomSum_eq hq]
  apply Nat.div_le_of_le_mul
  have hd_eq : d = (d - 1) + 1 := by omega
  have hqfactor : q ≤ 2 * (q - 1) := by omega
  calc
    q ^ d - 1 ≤ q ^ d := Nat.sub_le _ _
    _ = q ^ ((d - 1) + 1) := congrArg (fun n ↦ q ^ n) hd_eq
    _ = q ^ (d - 1) * q := by rw [pow_succ]
    _ ≤ q ^ (d - 1) * (2 * (q - 1)) :=
      Nat.mul_le_mul_left _ hqfactor
    _ = (q - 1) * (2 * q ^ (d - 1)) := by ring

/-- Coarse upper bound for the projective `D*` vertex set. -/
theorem card_vertex_le_four_mul_pow (q t : ℕ) [Fact q.Prime]
    (ht : 1 ≤ t) :
    Fintype.card (Vertex q t) ≤ 4 * q ^ (2 * t - 1) := by
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  rw [card_vertex]
  have h1 := geometricSum_le_two_mul_pow q (t + 1) hq (by omega)
  have h2 := geometricSum_le_two_mul_pow q t hq ht
  calc
    (∑ i ∈ Finset.range (t + 1), q ^ i) *
        (∑ i ∈ Finset.range t, q ^ i)
        ≤ (2 * q ^ t) * (2 * q ^ (t - 1)) := Nat.mul_le_mul h1 h2
    _ = 4 * q ^ (2 * t - 1) := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega

/-- The real-valued lower bound appearing literally in `DStarWitness`. -/
theorem vertex_lower_real (q t : ℕ) [Fact q.Prime] (ht : 1 ≤ t) :
    (q : ℝ) ^ (2 * t - 1) / 4 ≤ (Fintype.card (Vertex q t) : ℝ) := by
  have h := pow_two_mul_sub_one_le_card_vertex q t ht
  have hreal : (q : ℝ) ^ (2 * t - 1) ≤
      (Fintype.card (Vertex q t) : ℝ) := by exact_mod_cast h
  calc
    (q : ℝ) ^ (2 * t - 1) / 4 ≤ (q : ℝ) ^ (2 * t - 1) := by
      have hp : 0 ≤ (q : ℝ) ^ (2 * t - 1) :=
        pow_nonneg (Nat.cast_nonneg q) _
      linarith
    _ ≤ (Fintype.card (Vertex q t) : ℝ) := hreal

end

end Erdos920.ProjectiveDStar

import ErdosProblems.Erdos113.WalkFin
import ErdosProblems.Erdos113.Moments
import ErdosProblems.Erdos113.MomentsBipartite

/-!
# Counting finite vertex sequences which follow graph edges
-/

open scoped SimpleGraph BigOperators Real

namespace Erdos113Paths

open Conflict Lower

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A labelled walk written as its `m+1` successive vertices. -/
abbrev PathTuple (G : SimpleGraph V) (m : ℕ) :=
  {f : Fin (m + 1) → V //
    ∀ i : Fin m, G.Adj (f i.castSucc) (f i.succ)}

/-- Package a vertex sequence as a Mathlib walk, retaining both endpoints. -/
def encodePathTuple (G : SimpleGraph V) (m : ℕ) :
    PathTuple G m →
      Σ u : V, Σ v : V, Conflict.FixedWalk G m u v := fun f ↦
  ⟨f.1 ⟨0, Nat.zero_lt_succ m⟩,
    f.1 ⟨m, Nat.lt_succ_self m⟩,
    ⟨WF.walkOfFin m f.1 f.2, WF.walkOfFin_length m f.1 f.2⟩⟩

lemma encodePathTuple_injective (G : SimpleGraph V) (m : ℕ) :
    Function.Injective (encodePathTuple G m) := by
  intro f g h
  apply Subtype.ext
  funext i
  have hw := congrArg (fun z ↦ z.2.2.1.getVert i.val) h
  change (WF.walkOfFin m f.1 f.2).getVert i.val =
    (WF.walkOfFin m g.1 g.2).getVert i.val at hw
  rw [WF.walkOfFin_getVert m f.1 f.2 i.val (Nat.le_of_lt_succ i.2),
    WF.walkOfFin_getVert m g.1 g.2 i.val (Nat.le_of_lt_succ i.2)] at hw
  exact hw

lemma card_pathTuple_cast_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℝ) (hD : 0 ≤ D) (hdeg : ∀ x, (G.degree x : ℝ) ≤ D) (m : ℕ) :
    (Fintype.card (PathTuple G m) : ℝ) ≤ Fintype.card V * D ^ m := by
  classical
  have hinj := encodePathTuple_injective G m
  have hcard : Fintype.card (PathTuple G m) ≤
      Fintype.card (Σ u : V, Σ v : V, Conflict.FixedWalk G m u v) :=
    Fintype.card_le_of_injective (encodePathTuple G m) hinj
  calc
    (Fintype.card (PathTuple G m) : ℝ) ≤
        Fintype.card (Σ u : V, Σ v : V, Conflict.FixedWalk G m u v) := by
      exact_mod_cast hcard
    _ = ∑ u : V, ∑ v : V, (Conflict.walkCount G m u v : ℝ) := by
      simp only [Fintype.card_sigma, Nat.cast_sum]
      rfl
    _ = ∑ u : V, Lower.walkMass G m u := by
      rfl
    _ ≤ ∑ _u : V, D ^ m := by
      apply Finset.sum_le_sum
      intro u _
      exact Lower.walkMass_upper G D hD hdeg m u
    _ = Fintype.card V * D ^ m := by simp

lemma card_pathTuple_cast_le_bipartite
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (D : Bool → ℝ) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x)) (m : ℕ) :
    (Fintype.card (PathTuple G m) : ℝ) ≤
      Fintype.card V *
        (Erdos113LowerBipartite.alternatingProduct D false m +
          Erdos113LowerBipartite.alternatingProduct D true m) := by
  classical
  have hcard : Fintype.card (PathTuple G m) ≤
      Fintype.card (Σ u : V, Σ v : V, Conflict.FixedWalk G m u v) :=
    Fintype.card_le_of_injective (encodePathTuple G m)
      (encodePathTuple_injective G m)
  calc
    (Fintype.card (PathTuple G m) : ℝ) ≤
        Fintype.card (Σ u : V, Σ v : V, Conflict.FixedWalk G m u v) := by
      exact_mod_cast hcard
    _ = ∑ u : V, Lower.walkMass G m u := by
      simp only [Fintype.card_sigma, Nat.cast_sum]
      rfl
    _ ≤ ∑ _u : V,
        (Erdos113LowerBipartite.alternatingProduct D false m +
          Erdos113LowerBipartite.alternatingProduct D true m) := by
      apply Finset.sum_le_sum
      intro u _
      calc
        Lower.walkMass G m u ≤
            Erdos113LowerBipartite.alternatingProduct D (side u) m :=
          Erdos113LowerBipartite.walkMass_upper_bipartite
            G side D hD hcross hdeg m u
        _ ≤ Erdos113LowerBipartite.alternatingProduct D false m +
            Erdos113LowerBipartite.alternatingProduct D true m := by
          cases h : side u
          · exact le_add_of_nonneg_right
              (Erdos113LowerBipartite.alternatingProduct_nonneg D hD true m)
          · exact le_add_of_nonneg_left
              (Erdos113LowerBipartite.alternatingProduct_nonneg D hD false m)
    _ = Fintype.card V *
        (Erdos113LowerBipartite.alternatingProduct D false m +
          Erdos113LowerBipartite.alternatingProduct D true m) := by
      simp
      ring

lemma card_pathTuple_53_cast_le_bipartite
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (D : Bool → ℝ) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x)) :
    (Fintype.card (PathTuple G 53) : ℝ) ≤
      Fintype.card V *
        (D false ^ 27 * D true ^ 26 + D true ^ 27 * D false ^ 26) := by
  have h := card_pathTuple_cast_le_bipartite G side D hD hcross hdeg 53
  rw [show 53 = 2 * 26 + 1 by norm_num,
    Erdos113LowerBipartite.alternatingProduct_odd,
    Erdos113LowerBipartite.alternatingProduct_odd] at h
  simpa using h

/-- For an odd-length bipartite path, starting from its first oriented edge
replaces the crude vertex-count factor by twice the number of edges.  This is
the form used for adjacent-pair patterns in the many-four-cycle family. -/
lemma card_pathTuple_53_cast_le_bipartite_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (side : V → Bool) (D : Bool → ℝ) (hD : ∀ b, 0 ≤ D b)
    (hcross : ∀ {x y}, G.Adj x y → side y = !side x)
    (hdeg : ∀ x, (G.degree x : ℝ) ≤ D (side x)) :
    (Fintype.card (PathTuple G 53) : ℝ) ≤
      2 * G.edgeFinset.card * (D false * D true) ^ 26 := by
  classical
  have hcard : Fintype.card (PathTuple G 53) ≤
      Fintype.card (Σ u : V, Σ v : V, Conflict.FixedWalk G 53 u v) :=
    Fintype.card_le_of_injective (encodePathTuple G 53)
      (encodePathTuple_injective G 53)
  have hmass (x : V) :
      Lower.walkMass G 53 x ≤ (G.degree x : ℝ) * (D false * D true) ^ 26 := by
    rw [show 53 = 52 + 1 by norm_num, Lower.walkMass_succ]
    calc
      (∑ y ∈ G.neighborFinset x, Lower.walkMass G 52 y) ≤
          ∑ _y ∈ G.neighborFinset x, (D false * D true) ^ 26 := by
        apply Finset.sum_le_sum
        intro y hy
        have hyadj : G.Adj x y := (G.mem_neighborFinset x y).mp hy
        have hupper := Erdos113LowerBipartite.walkMass_upper_bipartite
          G side D hD hcross hdeg 52 y
        rw [show 52 = 2 * 26 by norm_num,
          Erdos113LowerBipartite.alternatingProduct_even] at hupper
        cases h : side y <;> simp [h] at hupper ⊢ <;>
          simpa [mul_comm] using hupper
      _ = (G.degree x : ℝ) * (D false * D true) ^ 26 := by
        simp [SimpleGraph.card_neighborFinset_eq_degree]
  calc
    (Fintype.card (PathTuple G 53) : ℝ) ≤
        Fintype.card (Σ u : V, Σ v : V, Conflict.FixedWalk G 53 u v) := by
      exact_mod_cast hcard
    _ = ∑ u : V, Lower.walkMass G 53 u := by
      simp only [Fintype.card_sigma, Nat.cast_sum]
      rfl
    _ ≤ ∑ u : V, (G.degree u : ℝ) * (D false * D true) ^ 26 := by
      exact Finset.sum_le_sum fun u _ ↦ hmass u
    _ = (∑ u : V, (G.degree u : ℝ)) * (D false * D true) ^ 26 := by
      rw [Finset.sum_mul]
    _ = 2 * G.edgeFinset.card * (D false * D true) ^ 26 := by
      norm_cast
      rw [G.sum_degrees_eq_twice_card_edges]

end Erdos113Paths

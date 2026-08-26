/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.DenseInducedMinDegree
import ErdosProblems.Erdos547b.EC2
import ErdosProblems.Erdos547b.Structures
import Mathlib.Tactic

/-!
# The host-density calculation in Zhao's Claim 6.10

If one half of a balanced cut consists of large-degree vertices and the cut
is not nearly complete, then the graph induced by that half has enough edges
to contain a nonempty induced subgraph of large minimum degree.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim610HostDensity

open Finset Fintype SimpleGraph
open Erdos547EC2
open Erdos547b.ZhaoDenseInducedMinDegree

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Degree in an induced graph is the number of ambient neighbors in the
inducing set. -/
theorem degree_induce_eq_degreeInto
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V)
    (x : {x // x ∈ X}) :
    (G.induce (X : Set V)).degree x = degreeInto G x.1 X := by
  rw [degreeInto]
  change #((G.induce (X : Set V)).neighborFinset x) = _
  apply Finset.card_bij (fun y _ ↦ y.1)
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    exact Finset.mem_filter.mpr ⟨y.2, hy⟩
  · intro y₁ _ y₂ _ heq
    exact Subtype.ext heq
  · intro y hy
    rw [Finset.mem_filter] at hy
    let ys : {x // x ∈ X} := ⟨y, hy.1⟩
    refine ⟨ys, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact hy.2

/-- The internal degree sum on `X` is twice the number of induced edges. -/
theorem sum_degreeInto_self_eq_twice_card_induced_edges
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) :
    ∑ x ∈ X, degreeInto G x X =
      2 * #(G.induce (X : Set V)).edgeFinset := by
  calc
    ∑ x ∈ X, degreeInto G x X =
        ∑ x : {x // x ∈ X}, (G.induce (X : Set V)).degree x := by
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro x _
      exact (degree_induce_eq_degreeInto G X x).symm
    _ = 2 * #(G.induce (X : Set V)).edgeFinset :=
      (G.induce (X : Set V)).sum_degrees_eq_twice_card_edges

/-- The elementary degree split behind the dense-half calculation. -/
theorem induced_edges_large_of_crossing_density_small
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (q : ℕ) (beta : ℚ)
    (hdisj : Disjoint X Y) (hcover : X ∪ Y = Finset.univ)
    (hXcard : X.card = q) (hYcard : Y.card = q) (hq : 0 < q)
    (hlarge : ∀ x ∈ X, q ≤ G.degree x)
    (hdensity : G.edgeDensity X Y < 1 - beta) :
    beta * q * q <
      2 * (#(G.induce (X : Set V)).edgeFinset : ℚ) := by
  have hdegreeSplit : ∀ x, degreeInto G x X + degreeInto G x Y = G.degree x := by
    intro x
    have h := degreeInto_partition G x hdisj hcover
    have huniv : degreeInto G x Finset.univ = G.degree x := by
      rw [degreeInto]
      change #(Finset.univ.filter fun w ↦ G.Adj x w) = _
      rw [← G.card_neighborFinset_eq_degree]
      congr 1
      ext w
      simp [G.mem_neighborFinset]
    simpa only [huniv] using h
  have hlargeSum : q * q ≤ ∑ x ∈ X, G.degree x := by
    calc
      q * q = ∑ _x ∈ X, q := by simp [hXcard]
      _ ≤ ∑ x ∈ X, G.degree x := by
        exact Finset.sum_le_sum fun x hx ↦ hlarge x hx
  have hsumSplit :
      (∑ x ∈ X, G.degree x) =
        (∑ x ∈ X, degreeInto G x X) +
          ∑ x ∈ X, degreeInto G x Y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ (hdegreeSplit x).symm
  have hcross :
      (∑ x ∈ X, degreeInto G x Y) = #(G.interedges X Y) :=
    sum_degreeInto_eq_card_interedges G X Y
  have hinternal :
      (∑ x ∈ X, degreeInto G x X) =
        2 * #(G.induce (X : Set V)).edgeFinset :=
    sum_degreeInto_self_eq_twice_card_induced_edges G X
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq
  have hdensity' :
      (#(G.interedges X Y) : ℚ) < (1 - beta) * q * Y.card := by
    rw [SimpleGraph.edgeDensity_def, hXcard] at hdensity
    have hYpos : (0 : ℚ) < Y.card := by rw [hYcard]; exact hqpos
    have h := (div_lt_iff₀ (mul_pos hqpos hYpos)).mp hdensity
    simpa [mul_assoc] using h
  have honeBeta_nonneg : 0 ≤ 1 - beta := by
    rw [hYcard] at hdensity'
    have hcross_nonneg : (0 : ℚ) ≤ #(G.interedges X Y) := by positivity
    have hrhspos : 0 < (1 - beta) * ((q : ℚ) * q) := by
      simpa [mul_assoc] using hcross_nonneg.trans_lt hdensity'
    rcases (mul_pos_iff.mp hrhspos) with hpos | hneg
    · exact le_of_lt hpos.1
    · exact False.elim ((not_lt_of_ge (mul_nonneg (le_of_lt hqpos)
        (le_of_lt hqpos))) hneg.2)
  have hdensityQ :
      (#(G.interedges X Y) : ℚ) < (1 - beta) * q * q := by
    simpa [hYcard] using hdensity'
  have hlargeQ : (q * q : ℚ) ≤ ∑ x ∈ X, (G.degree x : ℚ) := by
    exact_mod_cast hlargeSum
  have hsplitQ :
      (∑ x ∈ X, (G.degree x : ℚ)) =
        (2 * #(G.induce (X : Set V)).edgeFinset : ℚ) +
          #(G.interedges X Y) := by
    exact_mod_cast (hsumSplit.trans (by rw [hcross, hinternal]))
  nlinarith

/-- Outside EC1, a balanced half chosen from the large-degree vertices has a
nonempty induced subgraph of minimum degree greater than `k`.  Every vertex
of that subgraph still has ambient degree at least `n-1`. -/
theorem exists_large_induced_minDegree_of_not_extremalCaseOne
    {n k : ℕ} (hn : 2 ≤ n) (beta : ℚ)
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (hlarge : n - 1 ≤
      #(Finset.univ.filter fun v ↦ n - 1 ≤ G.degree v))
    (hnotEC1 : ¬ZhaoExtremalCaseOne beta G)
    (hnumeric : (2 * k * ((n - 1 : ℕ) : ℚ)) ≤
      beta * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ)) :
    ∃ X : Finset (Fin (2 * n - 2)),
      (∀ x ∈ X, n - 1 ≤ G.degree x) ∧
      ∃ U : Finset {x // x ∈ X}, U.Nonempty ∧
        ∀ u : {x // x ∈ U},
          k < ((G.induce (X : Set _)).induce (U : Set _)).degree u := by
  classical
  let L := Finset.univ.filter fun v ↦ n - 1 ≤ G.degree v
  obtain ⟨X, hXL, hXcard⟩ := Finset.exists_subset_card_eq hlarge
  let Y := Finset.univ \ X
  have hdisj : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro x hx hxy
    exact (Finset.mem_sdiff.mp hxy).2 hx
  have hcover : X ∪ Y = Finset.univ := by
    exact Finset.union_sdiff_of_subset (Finset.subset_univ X)
  have hhostCard : Fintype.card (Fin (2 * n - 2)) = 2 * (n - 1) := by
    simp only [Fintype.card_fin]
    omega
  have hYcard : Y.card = n - 1 := by
    have htotal : X.card + Y.card = Fintype.card (Fin (2 * n - 2)) := by
      rw [← Finset.card_union_of_disjoint hdisj, hcover, Finset.card_univ]
    rw [hXcard, hhostCard] at htotal
    omega
  have hcut : IsRamseyBalancedCut X Y :=
    ⟨hdisj, hcover, hXcard, hYcard⟩
  have hdensity : G.edgeDensity X Y < 1 - beta := by
    by_contra h
    apply hnotEC1
    refine ⟨X, Y, hcut, ?_⟩
    have hED :
        @SimpleGraph.edgeDensity _ G (Classical.decRel G.Adj) X Y =
          G.edgeDensity X Y := by
      congr 1
    rw [hED]
    exact le_of_not_gt h
  have hlargeX : ∀ x ∈ X, n - 1 ≤ G.degree x := by
    intro x hx
    exact (Finset.mem_filter.mp (hXL hx)).2
  have hedgeQ :
      beta * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) <
        2 * (#(G.induce (X : Set _)).edgeFinset : ℚ) := by
    exact induced_edges_large_of_crossing_density_small G X Y (n - 1) beta
      hdisj hcover hXcard hYcard (by omega) hlargeX hdensity
  have hdenseNat :
      k * Fintype.card {x // x ∈ X} < #(G.induce (X : Set _)).edgeFinset := by
    rw [Fintype.card_coe, hXcard]
    have htwice := lt_of_le_of_lt hnumeric hedgeQ
    have honeQ : (k : ℚ) * ((n - 1 : ℕ) : ℚ) <
        (#(G.induce (X : Set _)).edgeFinset : ℚ) := by
      apply lt_of_mul_lt_mul_left (a := (2 : ℚ)) (by
        simpa [mul_assoc] using htwice) (by norm_num)
    have honeCast : ((k * (n - 1) : ℕ) : ℚ) <
        (#(G.induce (X : Set _)).edgeFinset : ℚ) := by
      simpa only [Nat.cast_mul] using honeQ
    exact_mod_cast honeCast
  obtain ⟨U, hUne, hmin⟩ :=
    exists_induced_minDegree_gt_of_mul_card_lt_edges
      (G.induce (X : Set _)) k hdenseNat
  exact ⟨X, hlargeX, U, hUne, hmin⟩

end Erdos547b.ZhaoClaim610HostDensity

#print axioms Erdos547b.ZhaoClaim610HostDensity.exists_large_induced_minDegree_of_not_extremalCaseOne

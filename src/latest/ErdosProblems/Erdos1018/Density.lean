import Mathlib

open scoped Sym2
open Finset

namespace Erdos1018Aux

open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ S).card

def degreeOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  ((G.edgeFinset.filter fun e => e.toFinset ⊆ S).filter fun e => v ∈ e.toFinset).card

lemma edgesOn_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgesOn G univ = #G.edgeFinset := by
  unfold edgesOn
  simp

lemma edgesOn_eq_induce (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    edgesOn G S = #(G.induce (S : Set V)).edgeFinset := by
  unfold edgesOn
  exact G.card_filter_edgeFinset_toFinset_subset S

lemma edgesOn_erase_add_degreeOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {v : V} (_hv : v ∈ S) :
    edgesOn G (S.erase v) + degreeOn G S v = edgesOn G S := by
  unfold edgesOn degreeOn
  let F := G.edgeFinset.filter fun e => e.toFinset ⊆ S
  calc
    #({e ∈ G.edgeFinset | e.toFinset ⊆ S.erase v}) +
          #({e ∈ F | v ∈ e.toFinset}) =
        #({e ∈ F | v ∉ e.toFinset}) + #({e ∈ F | ¬v ∉ e.toFinset}) := by
      congr 1
      · apply congrArg card
        ext e
        simp only [F, mem_filter]
        constructor
        · rintro ⟨heG, heSub⟩
          refine ⟨⟨heG, ?_⟩, ?_⟩
          · intro x hx
            exact (mem_erase.mp (heSub hx)).2
          · intro hve
            exact (mem_erase.mp (heSub hve)).1 rfl
        · rintro ⟨⟨heG, heSub⟩, hev⟩
          refine ⟨heG, ?_⟩
          intro x hx
          exact mem_erase.mpr ⟨fun hxv => hev (hxv ▸ hx), heSub hx⟩
      · apply congrArg card
        ext e
        simp only [mem_filter, not_not]
    _ = #F := card_filter_add_card_filter_not (s := F) (p := fun e => v ∉ e.toFinset)

/-- A finite induced subgraph with at least `d |V|` edges contains a nonempty
induced subgraph of minimum degree strictly larger than `d`.  This is the
minimal-cardinality version of the usual vertex-pruning argument. -/
theorem exists_min_degree_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hV : 0 < Fintype.card V)
    (hE : d * Fintype.card V ≤ #G.edgeFinset) :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, d < degreeOn G S v := by
  let Good : Finset V → Prop := fun S ↦ S.Nonempty ∧ d * #S ≤ edgesOn G S
  let _ : DecidablePred Good := Classical.decPred _
  let candidates := (univ : Finset (Finset V)).filter Good
  have hunivGood : Good (univ : Finset V) := by
    refine ⟨Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hV), ?_⟩
    simpa [edgesOn_univ] using hE
  have hcandidates : candidates.Nonempty := by
    refine ⟨univ, ?_⟩
    exact mem_filter.mpr ⟨mem_univ _, hunivGood⟩
  obtain ⟨S, hScand, hmin⟩ := candidates.exists_min_image card hcandidates
  have hSGood : Good S := (mem_filter.mp hScand).2
  refine ⟨S, hSGood.1, ?_⟩
  intro v hv
  have hScard : 1 < #S := by
    have hSpos : 0 < #S := card_pos.mpr hSGood.1
    by_contra hn
    have hcard : #S = 1 := by omega
    have hedge0 : edgesOn G S = 0 := by
      rw [edgesOn_eq_induce]
      have hle := SimpleGraph.card_edgeFinset_le_card_choose_two
        (G := G.induce (S : Set V))
      have hsubcard : Fintype.card (S : Set V) = 1 := by simpa using hcard
      rw [hsubcard] at hle
      norm_num at hle ⊢
      exact hle
    have hdense := hSGood.2
    rw [hcard, hedge0] at hdense
    norm_num at hdense
    omega
  by_contra hn
  have hdeg : degreeOn G S v ≤ d := by omega
  have herase_ne : (S.erase v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro heq
    have : #(S.erase v) = 0 := by simp [heq]
    rw [card_erase_of_mem hv] at this
    omega
  have herase_dense : d * #(S.erase v) ≤ edgesOn G (S.erase v) := by
    have hsplit := edgesOn_erase_add_degreeOn G S hv
    have hcard_split : #S = (#S - 1) + 1 := by omega
    have hdense := hSGood.2
    rw [hcard_split, mul_add, mul_one] at hdense
    rw [card_erase_of_mem hv]
    omega
  have heraseGood : Good (S.erase v) := ⟨herase_ne, herase_dense⟩
  have heraseCand : S.erase v ∈ candidates :=
    mem_filter.mpr ⟨mem_univ _, heraseGood⟩
  have hminErase := hmin (S.erase v) heraseCand
  rw [card_erase_of_mem hv] at hminErase
  omega

/-- Real-threshold version of the same pruning lemma.  This is the form used
with real powers in the density localization argument. -/
theorem exists_min_degree_subset_real (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℝ) (hd : 0 < d) (hV : 0 < Fintype.card V)
    (hE : d * (Fintype.card V : ℝ) ≤ (#G.edgeFinset : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, d < (degreeOn G S v : ℝ) := by
  let Good : Finset V → Prop := fun S ↦
    S.Nonempty ∧ d * (#S : ℝ) ≤ (edgesOn G S : ℝ)
  let _ : DecidablePred Good := Classical.decPred _
  let candidates := (univ : Finset (Finset V)).filter Good
  have hunivGood : Good (univ : Finset V) := by
    refine ⟨Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hV), ?_⟩
    simpa [edgesOn_univ] using hE
  have hcandidates : candidates.Nonempty := by
    exact ⟨univ, mem_filter.mpr ⟨mem_univ _, hunivGood⟩⟩
  obtain ⟨S, hScand, hmin⟩ := candidates.exists_min_image card hcandidates
  have hSGood : Good S := (mem_filter.mp hScand).2
  refine ⟨S, hSGood.1, ?_⟩
  intro v hv
  have hScard : 1 < #S := by
    have hSpos : 0 < #S := card_pos.mpr hSGood.1
    by_contra hn
    have hcard : #S = 1 := by omega
    have hedge0 : edgesOn G S = 0 := by
      rw [edgesOn_eq_induce]
      have hle := SimpleGraph.card_edgeFinset_le_card_choose_two
        (G := G.induce (S : Set V))
      have hsubcard : Fintype.card (S : Set V) = 1 := by simpa using hcard
      rw [hsubcard] at hle
      norm_num at hle ⊢
      exact hle
    have hdense := hSGood.2
    rw [hcard, hedge0] at hdense
    norm_num at hdense
    linarith
  by_contra hn
  have hdeg : (degreeOn G S v : ℝ) ≤ d := le_of_not_gt hn
  have herase_ne : (S.erase v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro heq
    have : #(S.erase v) = 0 := by simp [heq]
    rw [card_erase_of_mem hv] at this
    omega
  have herase_dense : d * (#(S.erase v) : ℝ) ≤ (edgesOn G (S.erase v) : ℝ) := by
    have hsplitNat := edgesOn_erase_add_degreeOn G S hv
    have hsplit : (edgesOn G (S.erase v) : ℝ) + (degreeOn G S v : ℝ) =
        (edgesOn G S : ℝ) := by exact_mod_cast hsplitNat
    have hcardNat : #S = #(S.erase v) + 1 := by
      rw [card_erase_of_mem hv]
      omega
    have hcard : (#S : ℝ) = (#(S.erase v) : ℝ) + 1 := by exact_mod_cast hcardNat
    nlinarith [hSGood.2]
  have heraseGood : Good (S.erase v) := ⟨herase_ne, herase_dense⟩
  have heraseCand : S.erase v ∈ candidates :=
    mem_filter.mpr ⟨mem_univ _, heraseGood⟩
  have hminErase := hmin (S.erase v) heraseCand
  rw [card_erase_of_mem hv] at hminErase
  omega

/-- The incidences between a vertex set and the edges internal to a larger
set are at most twice the number of those edges. -/
theorem sum_degreeOn_le_twice_edgesOn
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    ∑ v ∈ S, degreeOn G T v ≤ 2 * edgesOn G T := by
  let E := G.edgeFinset.filter fun e ↦ e.toFinset ⊆ T
  have hrewrite (v : V) : degreeOn G T v = #(E.filter fun e ↦ v ∈ e.toFinset) := rfl
  calc
    ∑ v ∈ S, degreeOn G T v =
        ∑ v ∈ S, #(E.filter fun e ↦ v ∈ e.toFinset) := by
          apply Finset.sum_congr rfl
          intro v _
          exact hrewrite v
    _ = ∑ v ∈ S, ∑ e ∈ E, if v ∈ e.toFinset then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          simp
    _ = ∑ e ∈ E, ∑ v ∈ S, if v ∈ e.toFinset then 1 else 0 := by
          rw [Finset.sum_comm]
    _ ≤ ∑ e ∈ E, 2 := by
          apply Finset.sum_le_sum
          intro e he
          have hsub : (S.filter fun v ↦ v ∈ e.toFinset).card ≤ e.toFinset.card := by
            apply Finset.card_le_card
            intro v hv
            exact (Finset.mem_filter.mp hv).2
          have hcard : e.toFinset.card ≤ 2 := by
            rw [Sym2.card_toFinset]
            split <;> omega
          simpa using hsub.trans hcard
    _ = 2 * edgesOn G T := by
          simp [edgesOn, E, mul_comm]

/-- If `T` contains a vertex and all its neighbors, the internal incidence
count is its full degree. -/
theorem degreeOn_eq_degree_of_neighborSet_subset
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) {v : V}
    (hv : v ∈ T) (hclosed : G.neighborSet v ⊆ (T : Set V)) :
    degreeOn G T v = G.degree v := by
  rw [← G.card_incidenceFinset_eq_degree]
  unfold degreeOn
  apply congrArg Finset.card
  ext e
  rw [G.incidenceFinset_eq_filter]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨heG, _⟩, hve⟩
    exact ⟨heG, Sym2.mem_toFinset.mp hve⟩
  · rintro ⟨heG, hve⟩
    have hve' : v ∈ e.toFinset := Sym2.mem_toFinset.mpr hve
    refine ⟨⟨heG, ?_⟩, hve'⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hxy : G.Adj x y := by simpa using (G.mem_edgeFinset.mp heG)
      simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton] at hve' ⊢
      rcases hve' with (rfl | rfl)
      · exact ⟨hv, hclosed hxy⟩
      · exact ⟨hclosed hxy.symm, hv⟩

theorem degreeOn_eq_of_subset_of_closedWithin
    (G : SimpleGraph V) [DecidableRel G.Adj] {T R : Finset V} {v : V}
    (hTR : T ⊆ R) (hvT : v ∈ T)
    (hclosed : ∀ w, G.Adj v w → w ∈ R → w ∈ T) :
    degreeOn G T v = degreeOn G R v := by
  unfold degreeOn
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨heG, heT⟩, hve⟩
    exact ⟨⟨heG, heT.trans hTR⟩, hve⟩
  · rintro ⟨⟨heG, heR⟩, hve⟩
    refine ⟨⟨heG, ?_⟩, hve⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hxy : G.Adj x y := by simpa using (G.mem_edgeFinset.mp heG)
      simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
        Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton] at heR hve ⊢
      rcases hve with (rfl | rfl)
      · exact ⟨hvT, hclosed y hxy heR.2⟩
      · exact ⟨hclosed x hxy.symm heR.1, hvT⟩

/-- The finite breadth-first ball around `z`. -/
def ball (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) : ℕ → Finset V
  | 0 => {z}
  | i + 1 => ball G z i ∪ (ball G z i).biUnion (fun v ↦ G.neighborFinset v)

@[simp] lemma ball_zero (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) :
    ball G z 0 = {z} := rfl

lemma ball_subset_succ (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) (i : ℕ) :
    ball G z i ⊆ ball G z (i + 1) := by
  intro x hx
  exact Finset.mem_union_left _ hx

lemma mem_ball_succ_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : V) {i : ℕ} {x y : V} (hx : x ∈ ball G z i) (hxy : G.Adj x y) :
    y ∈ ball G z (i + 1) := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨x, hx, (G.mem_neighborFinset x y).mpr hxy⟩

lemma neighborSet_ball_subset_succ (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : V) (i : ℕ) {x : V} (hx : x ∈ ball G z i) :
    G.neighborSet x ⊆ (ball G z (i + 1) : Set V) := by
  intro y hy
  exact mem_ball_succ_of_adj G z hx hy

lemma mem_ball_self (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) (i : ℕ) :
    z ∈ ball G z i := by
  induction i with
  | zero => simp
  | succ i hi => exact ball_subset_succ G z i hi

lemma card_ball_le (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) (i : ℕ) :
    #(ball G z i) ≤ Fintype.card V := by
  simpa using Finset.card_le_card (Finset.subset_univ (ball G z i))

lemma exists_walk_of_mem_ball (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : V) {i : ℕ} {v : V} (hv : v ∈ ball G z i) :
    ∃ p : G.Walk z v, p.length ≤ i ∧ ∀ x ∈ p.support, x ∈ ball G z i := by
  induction i generalizing v with
  | zero =>
      have hvz : v = z := by simpa using hv
      subst v
      refine ⟨Walk.nil, by simp, ?_⟩
      simp
  | succ i ih =>
      rw [show i + 1 = Nat.succ i by omega] at hv ⊢
      change v ∈ ball G z i ∪ (ball G z i).biUnion (fun w ↦ G.neighborFinset w) at hv
      rcases Finset.mem_union.mp hv with hvold | hvnew
      · obtain ⟨p, hplen, hpsupp⟩ := ih hvold
        refine ⟨p, by omega, ?_⟩
        intro x hx
        exact ball_subset_succ G z i (hpsupp x hx)
      · obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hvnew
        have hadj : G.Adj w v := (G.mem_neighborFinset w v).mp hvw
        obtain ⟨p, hplen, hpsupp⟩ := ih hw
        refine ⟨p.concat hadj, ?_, ?_⟩
        · simp only [Walk.length_concat]
          omega
        · intro x hx
          rw [Walk.support_concat] at hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact ball_subset_succ G z i (hpsupp x hx)
          · exact mem_ball_succ_of_adj G z hw hadj

theorem connected_induce_ball (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : V) (i : ℕ) : (G.induce (ball G z i : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨z, mem_ball_self G z i⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨p, _hplen, hpsupp⟩ := exists_walk_of_mem_ball G z hv
  exact ⟨p.induce (ball G z i : Set V) hpsupp⟩

/-- Breadth-first ball using only vertices in the ambient finite set `R`. -/
def rball (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V) (z : V) : ℕ → Finset V
  | 0 => {z}
  | i + 1 => rball G R z i ∪
      (rball G R z i).biUnion (fun v ↦ G.neighborFinset v ∩ R)

@[simp] lemma rball_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (z : V) : rball G R z 0 = {z} := rfl

lemma rball_subset_succ (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (z : V) (i : ℕ) :
    rball G R z i ⊆ rball G R z (i + 1) := by
  intro x hx
  exact Finset.mem_union_left _ hx

lemma rball_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) {z : V} (hz : z ∈ R) (i : ℕ) : rball G R z i ⊆ R := by
  induction i with
  | zero => simpa
  | succ i ih =>
      intro x hx
      change x ∈ rball G R z i ∪
        (rball G R z i).biUnion (fun v ↦ G.neighborFinset v ∩ R) at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ih hx
      · obtain ⟨v, _hv, hx⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_inter.mp hx).2

lemma mem_rball_self (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (z : V) (i : ℕ) : z ∈ rball G R z i := by
  induction i with
  | zero => simp
  | succ i hi => exact rball_subset_succ G R z i hi

lemma mem_rball_succ_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (z : V) {i : ℕ} {x y : V}
    (hx : x ∈ rball G R z i) (hxy : G.Adj x y) (hyR : y ∈ R) :
    y ∈ rball G R z (i + 1) := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨x, hx, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y).mpr hxy, hyR⟩⟩

lemma exists_walk_of_mem_rball (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (z : V) {i : ℕ} {v : V} (hv : v ∈ rball G R z i) :
    ∃ p : G.Walk z v, p.length ≤ i ∧ ∀ x ∈ p.support, x ∈ rball G R z i := by
  induction i generalizing v with
  | zero =>
      have hvz : v = z := by simpa using hv
      subst v
      refine ⟨Walk.nil, by simp, ?_⟩
      simp
  | succ i ih =>
      rw [show i + 1 = Nat.succ i by omega] at hv ⊢
      change v ∈ rball G R z i ∪
        (rball G R z i).biUnion (fun w ↦ G.neighborFinset w ∩ R) at hv
      rcases Finset.mem_union.mp hv with hvold | hvnew
      · obtain ⟨p, hplen, hpsupp⟩ := ih hvold
        refine ⟨p, by omega, ?_⟩
        intro x hx
        exact rball_subset_succ G R z i (hpsupp x hx)
      · obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hvnew
        have hvw' := Finset.mem_inter.mp hvw
        have hadj : G.Adj w v := (G.mem_neighborFinset w v).mp hvw'.1
        obtain ⟨p, hplen, hpsupp⟩ := ih hw
        refine ⟨p.concat hadj, ?_, ?_⟩
        · simp only [Walk.length_concat]
          omega
        · intro x hx
          rw [Walk.support_concat] at hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact rball_subset_succ G R z i (hpsupp x hx)
          · exact mem_rball_succ_of_adj G R z hw hadj hvw'.2

theorem connected_induce_rball (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (z : V) (i : ℕ) :
    (G.induce (rball G R z i : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨z, mem_rball_self G R z i⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨p, _hplen, hpsupp⟩ := exists_walk_of_mem_rball G R z hv
  exact ⟨p.induce (rball G R z i : Set V) hpsupp⟩

theorem exists_dense_rball_of_internal_min_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V)
    (c a : ℝ) (r : ℕ) (hc : 0 < c) (ha : 0 < a) (hr : 0 < r)
    (hR : R.Nonempty) (hsize : (Fintype.card V : ℝ) ≤ a ^ r)
    (hmin : ∀ v ∈ R, c * a < (degreeOn G R v : ℝ)) :
    ∃ z ∈ R, ∃ i : ℕ, i ≤ r ∧
      c * (#(rball G R z i) : ℝ) ≤
        2 * (edgesOn G (rball G R z i) : ℝ) := by
  obtain ⟨z, hzR⟩ := hR
  refine ⟨z, hzR, ?_⟩
  by_contra hnone
  have hbad (i : ℕ) (hi : i ≤ r) :
      2 * (edgesOn G (rball G R z i) : ℝ) <
        c * (#(rball G R z i) : ℝ) := by
    exact lt_of_not_ge (fun h ↦ hnone ⟨i, hi, h⟩)
  have hgrow (i : ℕ) (hi : i < r) :
      a * (#(rball G R z i) : ℝ) < (#(rball G R z (i + 1)) : ℝ) := by
    let B := rball G R z i
    let T := rball G R z (i + 1)
    have hBne : B.Nonempty := ⟨z, mem_rball_self G R z i⟩
    have hsumLower : c * a * (#B : ℝ) <
        ∑ v ∈ B, (degreeOn G R v : ℝ) := by
      calc
        c * a * (#B : ℝ) = ∑ _v ∈ B, c * a := by
          simp [mul_assoc, mul_comm]
        _ < ∑ v ∈ B, (degreeOn G R v : ℝ) := by
          exact Finset.sum_lt_sum_of_nonempty hBne (fun v hv ↦
            hmin v (rball_subset G R hzR i hv))
    have hincNat := sum_degreeOn_le_twice_edgesOn G B T
    have hsumEq : ∑ v ∈ B, degreeOn G T v = ∑ v ∈ B, degreeOn G R v := by
      apply Finset.sum_congr rfl
      intro v hv
      apply degreeOn_eq_of_subset_of_closedWithin G
      · exact rball_subset G R hzR (i + 1)
      · exact rball_subset_succ G R z i hv
      · intro w hvw hwR
        exact mem_rball_succ_of_adj G R z hv hvw hwR
    rw [hsumEq] at hincNat
    have hinc : (∑ v ∈ B, (degreeOn G R v : ℝ)) ≤
        2 * (edgesOn G T : ℝ) := by exact_mod_cast hincNat
    have hdenseBad := hbad (i + 1) (by omega)
    change 2 * (edgesOn G T : ℝ) < c * (#T : ℝ) at hdenseBad
    change a * (#B : ℝ) < (#T : ℝ)
    have hchain : c * a * (#B : ℝ) < c * (#T : ℝ) :=
      hsumLower.trans_le hinc |>.trans hdenseBad
    nlinarith
  have hpower (i : ℕ) (hi : i ≤ r) :
      a ^ i ≤ (#(rball G R z i) : ℝ) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hprev : i ≤ r := by omega
      have hg := hgrow i (by omega)
      exact (calc
          a ^ (i + 1) = a * a ^ i := by rw [pow_succ']
          _ ≤ a * (#(rball G R z i) : ℝ) :=
            mul_le_mul_of_nonneg_left (ih hprev) ha.le
          _ < (#(rball G R z (i + 1)) : ℝ) := hg).le
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hlast := hgrow k (by omega)
  have hpowk := hpower k (by omega)
  have hpwlt : a ^ (k + 1) < (#(rball G R z (k + 1)) : ℝ) := by
    calc
      a ^ (k + 1) = a * a ^ k := by rw [pow_succ']
      _ ≤ a * (#(rball G R z k) : ℝ) := mul_le_mul_of_nonneg_left hpowk ha.le
      _ < (#(rball G R z (k + 1)) : ℝ) := hlast
  have hcard : #(rball G R z (k + 1)) ≤ Fintype.card V :=
    Finset.card_le_card (Finset.subset_univ _)
  have hcardReal : (#(rball G R z (k + 1)) : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
  have hsize' : (Fintype.card V : ℝ) ≤ a ^ (k + 1) := by
    simpa only [Nat.succ_eq_add_one] using hsize
  exact (not_lt_of_ge hsize') (hpwlt.trans_le hcardReal)

/-- Complete real bounded-radius density localization.  Starting from average
degree at least `D`, it loses the unavoidable factor `2` in pruning and the
factor `a` in localization. -/
theorem bounded_radius_density
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D a : ℝ) (r : ℕ) (hD : 0 < D) (ha : 1 ≤ a) (hr : 0 < r)
    (hV : 0 < Fintype.card V) (hpow : (Fintype.card V : ℝ) ≤ a ^ r)
    (hAvg : D * (Fintype.card V : ℝ) ≤ 2 * (#G.edgeFinset : ℝ)) :
    ∃ S : Finset V, ∃ z : V,
      S.Nonempty ∧ z ∈ S ∧ (G.induce (S : Set V)).Connected ∧
      (∀ v ∈ S, ∃ p : G.Walk z v,
        p.length ≤ r ∧ ∀ x ∈ p.support, x ∈ S) ∧
      (D / (2 * a)) * (#S : ℝ) ≤
        2 * (#(G.induce (S : Set V)).edgeFinset : ℝ) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hd : 0 < D / 2 := div_pos hD (by norm_num)
  have hprune : (D / 2) * (Fintype.card V : ℝ) ≤ (#G.edgeFinset : ℝ) := by
    nlinarith
  obtain ⟨R, hRne, hRmin⟩ := exists_min_degree_subset_real G (D / 2) hd hV hprune
  let c := D / (2 * a)
  have hc : 0 < c := div_pos hD (mul_pos (by norm_num) ha0)
  have hca : c * a = D / 2 := by
    dsimp [c]
    field_simp
  have hmin : ∀ v ∈ R, c * a < (degreeOn G R v : ℝ) := by
    intro v hv
    rw [hca]
    exact hRmin v hv
  obtain ⟨z, hzR, i, hir, hdense⟩ :=
    exists_dense_rball_of_internal_min_degree G R c a r hc ha0 hr hRne hpow hmin
  let S := rball G R z i
  refine ⟨S, z, ⟨z, mem_rball_self G R z i⟩, mem_rball_self G R z i,
    connected_induce_rball G R z i, ?_, ?_⟩
  · intro v hv
    obtain ⟨p, hplen, hpsupp⟩ := exists_walk_of_mem_rball G R z hv
    exact ⟨p, hplen.trans hir, hpsupp⟩
  · change (D / (2 * a)) * (#S : ℝ) ≤ _
    change c * (#S : ℝ) ≤ _ at hdense
    rw [← edgesOn_eq_induce] 
    exact hdense

/-- Ball-growth localization from a real minimum-degree threshold.  The
parameter `a` is the desired growth factor; after at most `r` layers, one ball
has average degree at least `c`. -/
theorem exists_dense_ball_of_min_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c a : ℝ) (r : ℕ) (hc : 0 < c) (ha : 0 < a) (hr : 0 < r)
    (hV : 0 < Fintype.card V)
    (hsize : (Fintype.card V : ℝ) ≤ a ^ r)
    (hmin : ∀ v : V, c * a < (G.degree v : ℝ)) :
    ∃ z : V, ∃ i : ℕ, i ≤ r ∧
      c * (#(ball G z i) : ℝ) ≤ 2 * (edgesOn G (ball G z i) : ℝ) := by
  obtain ⟨z : V⟩ := Fintype.card_pos_iff.mp hV
  refine ⟨z, ?_⟩
  by_contra hnone
  have hbad (i : ℕ) (hi : i ≤ r) :
      2 * (edgesOn G (ball G z i) : ℝ) < c * (#(ball G z i) : ℝ) := by
    exact lt_of_not_ge (fun h ↦ hnone ⟨i, hi, h⟩)
  have hgrow (i : ℕ) (hi : i < r) :
      a * (#(ball G z i) : ℝ) < (#(ball G z (i + 1)) : ℝ) := by
    let B := ball G z i
    let T := ball G z (i + 1)
    have hBne : B.Nonempty := ⟨z, mem_ball_self G z i⟩
    have hsumLower : c * a * (#B : ℝ) < ∑ v ∈ B, (G.degree v : ℝ) := by
      calc
        c * a * (#B : ℝ) = ∑ _v ∈ B, c * a := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        _ < ∑ v ∈ B, (G.degree v : ℝ) := by
          exact Finset.sum_lt_sum_of_nonempty hBne (fun v _ ↦ hmin v)
    have hincNat := sum_degreeOn_le_twice_edgesOn G B T
    have hsumEq : ∑ v ∈ B, degreeOn G T v = ∑ v ∈ B, G.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact degreeOn_eq_degree_of_neighborSet_subset G T
        (ball_subset_succ G z i hv) (neighborSet_ball_subset_succ G z i hv)
    rw [hsumEq] at hincNat
    have hinc : (∑ v ∈ B, (G.degree v : ℝ)) ≤
        2 * (edgesOn G T : ℝ) := by exact_mod_cast hincNat
    have hdenseBad := hbad (i + 1) (by omega)
    change 2 * (edgesOn G T : ℝ) < c * (#T : ℝ) at hdenseBad
    change a * (#B : ℝ) < (#T : ℝ)
    have hchain : c * a * (#B : ℝ) < c * (#T : ℝ) :=
      hsumLower.trans_le hinc |>.trans hdenseBad
    nlinarith
  have hpower (i : ℕ) (hi : i ≤ r) :
      a ^ i ≤ (#(ball G z i) : ℝ) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hprev : i ≤ r := by omega
      have hg := hgrow i (by omega)
      exact (calc
          a ^ (i + 1) = a * a ^ i := by rw [pow_succ']
          _ ≤ a * (#(ball G z i) : ℝ) :=
            mul_le_mul_of_nonneg_left (ih hprev) ha.le
          _ < (#(ball G z (i + 1)) : ℝ) := hg).le
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hlast := hgrow k (by omega)
  have hpowk := hpower k (by omega)
  have hpwlt : a ^ (k + 1) < (#(ball G z (k + 1)) : ℝ) := by
    calc
      a ^ (k + 1) = a * a ^ k := by rw [pow_succ']
      _ ≤ a * (#(ball G z k) : ℝ) := mul_le_mul_of_nonneg_left hpowk ha.le
      _ < (#(ball G z (k + 1)) : ℝ) := hlast
  have hcard := card_ball_le G z (k + 1)
  have hcardReal : (#(ball G z (k + 1)) : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
  have hsize' : (Fintype.card V : ℝ) ≤ a ^ (k + 1) := by
    simpa only [Nat.succ_eq_add_one] using hsize
  exact (not_lt_of_ge hsize') (hpwlt.trans_le hcardReal)

end Erdos1018Aux

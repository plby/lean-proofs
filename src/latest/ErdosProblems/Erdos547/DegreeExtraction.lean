import ErdosProblems.Erdos547.Ramsey

/-!
# Degree extraction for the tree Ramsey proof

We count degrees inside finite vertex sets. Deleting a vertex changes the total
degree by exactly twice its current degree. This permits peeling with a lower
bound on the number of retained vertices, which is needed when the initial
average degree has no positive multiplicative margin.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of neighbours of `v` in the specified finite vertex set. -/
def degreeIn (S : Finset V) (v : V) : ℕ := (S.filter (G.Adj v)).card

/-- The sum of all degrees in the induced graph, viewed as a real number. -/
def degreeMass (S : Finset V) : ℝ := ∑ v ∈ S, (degreeIn G S v : ℝ)

theorem degreeIn_le_card (S : Finset V) (v : V) : degreeIn G S v ≤ S.card :=
  Finset.card_le_card (Finset.filter_subset (G.Adj v) S)

theorem degreeIn_mono {S Q : Finset V} (hSQ : S ⊆ Q) (v : V) :
    degreeIn G S v ≤ degreeIn G Q v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hSQ)

theorem degreeIn_le_add_removed [DecidableEq V] (S Q : Finset V)
    (v : V) : degreeIn G S v ≤ degreeIn G Q v + (S \ Q).card := by
  have hsub : S.filter (G.Adj v) ⊆ Q.filter (G.Adj v) ∪ (S \ Q) := by
    intro u hu
    obtain ⟨hus, hadj⟩ := Finset.mem_filter.mp hu
    by_cases huq : u ∈ Q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨huq, hadj⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hus, huq⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Removing `r` vertices loses at most `2*r*|S|` from the total degree. -/
theorem degreeMass_le_delete_add [DecidableEq V] {S Q : Finset V} (hQS : Q ⊆ S) :
    degreeMass G S ≤ degreeMass G Q + 2 * ((S \ Q).card : ℝ) * S.card := by
  have hdis : Disjoint Q (S \ Q) := by
    apply Finset.disjoint_left.mpr
    intro v hvq hvr
    exact (Finset.mem_sdiff.mp hvr).2 hvq
  have hunion : Q ∪ (S \ Q) = S := Finset.union_sdiff_of_subset hQS
  have hsplit : degreeMass G S = (∑ v ∈ Q, (degreeIn G S v : ℝ)) +
      ∑ v ∈ S \ Q, (degreeIn G S v : ℝ) := by
    rw [← Finset.sum_union hdis, hunion]
    rfl
  have hQ : (∑ v ∈ Q, (degreeIn G S v : ℝ)) ≤
      degreeMass G Q + (Q.card : ℝ) * (S \ Q).card := by
    calc
      (∑ v ∈ Q, (degreeIn G S v : ℝ)) ≤
          ∑ v ∈ Q, ((degreeIn G Q v : ℝ) + (S \ Q).card) := by
        apply Finset.sum_le_sum
        intro v _hv
        exact_mod_cast degreeIn_le_add_removed G S Q v
      _ = degreeMass G Q + (Q.card : ℝ) * (S \ Q).card := by
        simp [degreeMass, Finset.sum_add_distrib]
  have hR : (∑ v ∈ S \ Q, (degreeIn G S v : ℝ)) ≤
      ((S \ Q).card : ℝ) * S.card := by
    calc
      (∑ v ∈ S \ Q, (degreeIn G S v : ℝ)) ≤ ∑ _v ∈ S \ Q, (S.card : ℝ) := by
        apply Finset.sum_le_sum
        intro v _hv
        exact_mod_cast degreeIn_le_card G S v
      _ = ((S \ Q).card : ℝ) * S.card := by simp
  have hcards : (Q.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hQS
  have hmul := mul_le_mul_of_nonneg_right hcards
    (Nat.cast_nonneg (S \ Q).card : (0 : ℝ) ≤ (S \ Q).card)
  linarith

theorem degreeIn_univ [Fintype V] (v : V) : degreeIn G Finset.univ v = G.degree v := by
  classical
  simp [degreeIn, SimpleGraph.degree, SimpleGraph.neighborFinset_def]

theorem degreeMass_univ [Fintype V] :
    degreeMass G Finset.univ = 2 * (G.edgeFinset.card : ℝ) := by
  classical
  simp only [degreeMass, degreeIn_univ, ← Nat.cast_sum,
    G.sum_degrees_eq_twice_card_edges, Nat.cast_mul, Nat.cast_ofNat]

theorem degreeIn_eq_induce_degree (S : Finset V) (v : (S : Set V)) :
    degreeIn G S v.val = (G.induce (S : Set V)).degree v := by
  classical
  let e : (S.filter (G.Adj v.val)) ≃ (G.induce (S : Set V)).neighborSet v := {
    toFun := fun x ↦ ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
      (Finset.mem_filter.mp x.property).2⟩
    invFun := fun y ↦ ⟨y.val.val, Finset.mem_filter.mpr ⟨y.val.property, y.property⟩⟩
    left_inv := fun x ↦ by apply Subtype.ext; rfl
    right_inv := fun y ↦ by apply Subtype.ext; apply Subtype.ext; rfl }
  calc
    degreeIn G S v.val = Fintype.card (S.filter (G.Adj v.val)) := by
      exact (Fintype.card_coe (S.filter (G.Adj v.val))).symm
    _ = Fintype.card ((G.induce (S : Set V)).neighborSet v) := Fintype.card_congr e
    _ = (G.induce (S : Set V)).degree v :=
      (G.induce (S : Set V)).card_neighborSet_eq_degree v

theorem degreeIn_add_one_le_card (S : Finset V) {v : V}
    (hv : v ∈ S) : degreeIn G S v + 1 ≤ S.card := by
  classical
  have hsub : S.filter (G.Adj v) ⊆ S.erase v := by
    intro w hw
    obtain ⟨hws, hvw⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_erase.mpr ⟨hvw.ne', hws⟩
  have hle := Finset.card_le_card hsub
  have he := Finset.card_erase_of_mem hv
  have hpos := Finset.card_pos.mpr ⟨v, hv⟩
  dsimp [degreeIn]
  omega

theorem degreeMass_le_complete (S : Finset V) :
    degreeMass G S ≤ (S.card : ℝ) * (S.card - 1) := by
  classical
  have hsum : degreeMass G S + S.card ≤ (S.card : ℝ) * S.card := by
    calc
      degreeMass G S + S.card = ∑ v ∈ S, ((degreeIn G S v : ℝ) + 1) := by
        simp [degreeMass, Finset.sum_add_distrib]
      _ ≤ ∑ _v ∈ S, (S.card : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast degreeIn_add_one_le_card G S hv
      _ = (S.card : ℝ) * S.card := by simp
  nlinarith

theorem degreeIn_erase_add [DecidableEq V] (S : Finset V) {v : V}
    (hv : v ∈ S) (u : V) :
    degreeIn G (S.erase v) u + (if G.Adj u v then 1 else 0) = degreeIn G S u := by
  unfold degreeIn
  rw [Finset.filter_erase]
  by_cases huv : G.Adj u v
  · rw [if_pos huv]
    have hmem : v ∈ S.filter (G.Adj u) := Finset.mem_filter.mpr ⟨hv, huv⟩
    have he := Finset.card_erase_of_mem hmem
    have hpos := Finset.card_pos.mpr ⟨v, hmem⟩
    omega
  · simp [huv]

theorem degreeMass_erase [DecidableEq V] (S : Finset V) {v : V} (hv : v ∈ S) :
    degreeMass G (S.erase v) + 2 * degreeIn G S v = degreeMass G S := by
  have hsum : degreeMass G (S.erase v) +
      ∑ u ∈ S.erase v, (if G.Adj u v then (1 : ℝ) else 0) =
      ∑ u ∈ S.erase v, (degreeIn G S u : ℝ) := by
    rw [degreeMass, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _hu
    exact_mod_cast degreeIn_erase_add G S hv u
  have hindicator : (∑ u ∈ S.erase v, if G.Adj u v then (1 : ℝ) else 0) =
      degreeIn G S v := by
    rw [Finset.sum_boole]
    have hfilter : (S.erase v).filter (fun u ↦ G.Adj u v) = S.filter (G.Adj v) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hu⟩, huv⟩
        exact ⟨hu, huv.symm⟩
      · rintro ⟨hu, hvu⟩
        exact ⟨⟨hvu.ne', hu⟩, hvu.symm⟩
    rw [hfilter]
    rfl
  have hsplit := Finset.sum_erase_add S (fun u ↦ (degreeIn G S u : ℝ)) hv
  rw [hindicator] at hsum
  change (∑ u ∈ S.erase v, (degreeIn G S u : ℝ)) + degreeIn G S v =
    degreeMass G S at hsplit
  linarith

/-- The density expression that is preserved while vertices of degree at
most `d` are removed. -/
def degreeExcess (d : ℝ) (S : Finset V) : ℝ := degreeMass G S - 2 * d * S.card

theorem degreeExcess_le_erase [DecidableEq V] (S : Finset V) {v : V}
    (hv : v ∈ S) (d : ℝ) (hd : (degreeIn G S v : ℝ) ≤ d) :
    degreeExcess G d S ≤ degreeExcess G d (S.erase v) := by
  have hmass := degreeMass_erase G S hv
  have hcard : ((S.erase v).card : ℝ) + 1 = S.card := by
    exact_mod_cast Finset.card_erase_add_one hv
  unfold degreeExcess
  nlinarith

/-- Peel vertices of degree at most `d`, stopping before the vertex count
falls below `b`. The degree excess never decreases. -/
theorem exists_peeling_set (S₀ : Finset V) (b : ℕ) (hb : b ≤ S₀.card) (d : ℝ) :
    ∃ S ⊆ S₀, b ≤ S.card ∧ degreeExcess G d S₀ ≤ degreeExcess G d S ∧
      (S.card = b ∨ ∀ v ∈ S, d < (degreeIn G S v : ℝ)) := by
  classical
  let candidates : Finset (Finset V) := S₀.powerset.filter fun S ↦
    b ≤ S.card ∧ degreeExcess G d S₀ ≤ degreeExcess G d S
  have hstart : S₀ ∈ candidates := by simp [candidates, hb]
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image candidates Finset.card ⟨S₀, hstart⟩
  have hs := Finset.mem_filter.mp hS
  have hsub : S ⊆ S₀ := Finset.mem_powerset.mp hs.1
  have hfloor : b ≤ S.card := hs.2.1
  have hexcess : degreeExcess G d S₀ ≤ degreeExcess G d S := hs.2.2
  refine ⟨S, hsub, hfloor, hexcess, ?_⟩
  by_cases heq : S.card = b
  · exact Or.inl heq
  right
  intro v hv
  by_contra hnot
  have hd : (degreeIn G S v : ℝ) ≤ d := le_of_not_gt hnot
  have herase : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hv
  have hmem : S.erase v ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ((Finset.erase_subset v S).trans hsub), ?_, ?_⟩
    · omega
    · exact hexcess.trans (degreeExcess_le_erase G S hv d hd)
  have hcontra := hmin (S.erase v) hmem
  omega

/-- A strict bound on the density of every boundary-sized set rules out
the stopping boundary and gives the desired minimum degree. -/
theorem exists_peeling_core (S₀ : Finset V) (b : ℕ) (hb : b ≤ S₀.card) (d : ℝ)
    (hboundary : ∀ S ⊆ S₀, S.card = b → degreeExcess G d S < degreeExcess G d S₀) :
    ∃ S ⊆ S₀, b < S.card ∧ degreeExcess G d S₀ ≤ degreeExcess G d S ∧
      ∀ v ∈ S, d < (degreeIn G S v : ℝ) := by
  obtain ⟨S, hsub, hfloor, hexcess, hstop⟩ := exists_peeling_set G S₀ b hb d
  have hne : S.card ≠ b := by
    intro heq
    exact (not_lt_of_ge hexcess) (hboundary S hsub heq)
  refine ⟨S, hsub, by omega, hexcess, ?_⟩
  exact hstop.resolve_left hne

/-- The quantitative first extraction in the Ramsey argument. From the
majority-colour degree mass on `2*m` vertices, retain at least `m/2` vertices,
minimum degree above `(1+a)*m/2`, and average degree at least `(1-4*a)*m`.
The explicit size assumptions are independent of the tree. -/
theorem exists_majority_degree_core (S₀ : Finset V) (m : ℕ) (a : ℝ)
    (hcard : S₀.card = 2 * m) (ha : 0 < a) (ha_small : a ≤ 1 / 100)
    (hm : (100 : ℝ) ≤ m) (ham : 2 ≤ a * m)
    (hmass : 2 * (m : ℝ) ^ 2 - m ≤ degreeMass G S₀) :
    ∃ S ⊆ S₀, (m : ℝ) / 2 ≤ S.card ∧
      (∀ v ∈ S, (1 + a) * m / 2 < (degreeIn G S v : ℝ)) ∧
      (1 - 4 * a) * m * S.card ≤ degreeMass G S := by
  classical
  let b : ℕ := m / 2
  let d : ℝ := (1 + a) * m / 2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hm_nat : 100 ≤ m := by exact_mod_cast hm
  have hb_floor : b ≤ S₀.card := by rw [hcard]; dsimp [b]; omega
  have hb_upper_nat : 2 * b ≤ m := by dsimp [b]; omega
  have hb_lower_nat : m ≤ 3 * b := by dsimp [b]; omega
  have hb_upper : 2 * (b : ℝ) ≤ m := by exact_mod_cast hb_upper_nat
  have hb_lower : (m : ℝ) ≤ 3 * b := by exact_mod_cast hb_lower_nat
  have hboundary : ∀ S ⊆ S₀, S.card = b →
      degreeExcess G d S < degreeExcess G d S₀ := by
    intro S _hsub hs
    have hcomplete : degreeMass G S ≤ (b : ℝ) * (b - 1) := by
      simpa only [hs] using degreeMass_le_complete G S
    have hb_square := mul_le_mul_of_nonneg_right hb_upper hb0
    have hmb := mul_le_mul_of_nonneg_left hb_lower hm0
    have ha_square := mul_le_mul_of_nonneg_right ha_small (sq_nonneg (m : ℝ))
    have hm_square := mul_le_mul_of_nonneg_right hm hm0
    have hab : 0 ≤ a * m * b := mul_nonneg (mul_nonneg ha.le hm0) hb0
    simp only [degreeExcess, hs, hcard, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [d]
    nlinarith
  obtain ⟨S, hsub, hfloor, hexcess, hdegree⟩ :=
    exists_peeling_core G S₀ b hb_floor d hboundary
  have hsize_nat : m ≤ 2 * S.card := by dsimp [b] at hfloor; omega
  have hsize_real : (m : ℝ) ≤ 2 * S.card := by exact_mod_cast hsize_nat
  have hsize : (m : ℝ) / 2 ≤ S.card := by linarith
  refine ⟨S, hsub, hsize, hdegree, ?_⟩
  have hproduct := mul_le_mul_of_nonneg_left hsize
    (show 0 ≤ 5 * a * m by positivity)
  have ham_product := mul_le_mul_of_nonneg_right ham hm0
  simp only [degreeExcess, hcard, Nat.cast_mul, Nat.cast_ofNat] at hexcess
  dsimp [d] at hexcess
  nlinarith

end Erdos547

#print axioms Erdos547.degreeMass_erase
#print axioms Erdos547.exists_peeling_core
#print axioms Erdos547.exists_majority_degree_core

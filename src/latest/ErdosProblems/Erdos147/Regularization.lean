import ErdosProblems.Erdos147.Conflict

open Filter
open Asymptotics
open scoped SimpleGraph Topology

namespace Erdos147

set_option autoImplicit false

noncomputable def walkTotal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u : V) : ℝ :=
  ∑ v : V, walkCount G j u v

lemma walkTotal_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : walkTotal G 0 u = 1 := by
  classical
  simp [walkTotal, walkCount, Matrix.one_apply, Pi.single_apply]

lemma walkTotal_succ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) (u : V) :
    walkTotal G (j + 1) u =
      ∑ z : V, (if G.Adj u z then 1 else 0) * walkTotal G j z := by
  rw [walkTotal]
  have hpow : G.adjMatrix ℝ ^ (j + 1) = G.adjMatrix ℝ * G.adjMatrix ℝ ^ j := by
    rw [show j + 1 = 1 + j by omega, pow_add]
    simp
  simp only [walkCount, hpow, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  by_cases h : G.Adj u z <;>
    simp [SimpleGraph.adjMatrix_apply, h, walkTotal, walkCount]

lemma walkTotal_succ_left_lower
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (j : ℕ) (A s : ℝ) (hA : 0 ≤ A)
    (hright : ∀ r, A ≤ walkTotal (bipartiteRelGraph B) j (Sum.inr r))
    (hdeg : ∀ l, s ≤ relLeftDegreeReal B l) (l : L) :
    s * A ≤ walkTotal (bipartiteRelGraph B) (j + 1) (Sum.inl l) := by
  rw [walkTotal_succ]
  simp only [Fintype.sum_sum_type, bipartiteRelGraph, ite_false, zero_mul,
    Finset.sum_const_zero, zero_add, ite_mul, one_mul]
  calc
    s * A ≤ relLeftDegreeReal B l * A :=
      mul_le_mul_of_nonneg_right (hdeg l) hA
    _ = ∑ r : R, if B l r then A else 0 := by
      rw [relLeftDegreeReal, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : B l r <;> simp [h]
    _ ≤ ∑ r : R, if B l r then walkTotal (bipartiteRelGraph B) j (Sum.inr r) else 0 := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases h : B l r <;> simp [h, hright]
    _ = ∑ r : R, (if B l r then 1 else 0) *
        walkTotal (bipartiteRelGraph B) j (Sum.inr r) := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : B l r <;> simp [h]

lemma walkTotal_succ_right_lower
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (j : ℕ) (A t : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ l, A ≤ walkTotal (bipartiteRelGraph B) j (Sum.inl l))
    (hdeg : ∀ r, t ≤ relLeftDegreeReal (fun r l ↦ B l r) r) (r : R) :
    t * A ≤ walkTotal (bipartiteRelGraph B) (j + 1) (Sum.inr r) := by
  rw [walkTotal_succ]
  simp only [Fintype.sum_sum_type, bipartiteRelGraph, ite_false, zero_mul,
    Finset.sum_const_zero, add_zero, ite_mul, one_mul]
  calc
    t * A ≤ relLeftDegreeReal (fun r l ↦ B l r) r * A :=
      mul_le_mul_of_nonneg_right (hdeg r) hA
    _ = ∑ l : L, if B l r then A else 0 := by
      rw [relLeftDegreeReal, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      by_cases h : B l r <;> simp [h]
    _ ≤ ∑ l : L, if B l r then walkTotal (bipartiteRelGraph B) j (Sum.inl l) else 0 := by
      apply Finset.sum_le_sum
      intro l hl
      by_cases h : B l r <;> simp [h, hleft]
    _ = ∑ l : L, (if B l r then 1 else 0) *
        walkTotal (bipartiteRelGraph B) j (Sum.inl l) := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases h : B l r <;> simp [h]

lemma bipartiteWalk_length_six_side_eq
    {L R : Type*} {B : L → R → Prop} {x y : L ⊕ R}
    (p : (bipartiteRelGraph B).Walk x y) (hp : p.length = 6) :
    bipartiteSide x = bipartiteSide y := by
  have h0 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 0) (by omega))
  have h1 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 1) (by omega))
  have h2 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 2) (by omega))
  have h3 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 3) (by omega))
  have h4 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 4) (by omega))
  have h5 := bipartiteSide_ne_of_adj (p.adj_getVert_succ (i := 5) (by omega))
  have h02 : bipartiteSide x = bipartiteSide (p.getVert 2) := by
    have := bool_eq_of_ne_of_ne h0 h1
    simpa using this
  have h24 : bipartiteSide (p.getVert 2) = bipartiteSide (p.getVert 4) :=
    bool_eq_of_ne_of_ne h2 h3
  have h46 : bipartiteSide (p.getVert 4) = bipartiteSide y := by
    have := bool_eq_of_ne_of_ne h4 h5
    simpa [p.getVert_of_length_le (by omega : p.length ≤ 6), hp] using this
  exact h02.trans (h24.trans h46)

lemma walkCount_six_left_right_eq_zero
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (l : L) (r : R) :
    walkCount (bipartiteRelGraph B) 6 (Sum.inl l) (Sum.inr r) = 0 := by
  rw [walkCount_eq_card]
  norm_cast
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun p ↦ by
    have hside := bipartiteWalk_length_six_side_eq p.1 p.2
    simp [bipartiteSide] at hside⟩

lemma homCycleCount_twelve_lower_of_minDegrees
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    [Nonempty L]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hdegL : ∀ l, s ≤ relLeftDegreeReal B l)
    (hdegR : ∀ r, t ≤ relLeftDegreeReal (fun r l ↦ B l r) r) :
    (s * t) ^ 6 ≤ homCycleCount (bipartiteRelGraph B) 12 := by
  let Q := bipartiteRelGraph B
  have hL0 : ∀ l, (1 : ℝ) ≤ walkTotal Q 0 (Sum.inl l) := by
    intro l
    rw [walkTotal_zero]
  have hR0 : ∀ r, (1 : ℝ) ≤ walkTotal Q 0 (Sum.inr r) := by
    intro r
    rw [walkTotal_zero]
  have hL1 : ∀ l, s ≤ walkTotal Q 1 (Sum.inl l) := by
    intro l
    simpa [Q] using walkTotal_succ_left_lower B 0 1 s (by norm_num) hR0 hdegL l
  have hR1 : ∀ r, t ≤ walkTotal Q 1 (Sum.inr r) := by
    intro r
    simpa [Q] using walkTotal_succ_right_lower B 0 1 t (by norm_num) hL0 hdegR r
  have hL2 : ∀ l, s * t ≤ walkTotal Q 2 (Sum.inl l) := by
    intro l
    simpa [Q] using walkTotal_succ_left_lower B 1 t s ht hR1 hdegL l
  have hR2 : ∀ r, t * s ≤ walkTotal Q 2 (Sum.inr r) := by
    intro r
    simpa [Q] using walkTotal_succ_right_lower B 1 s t hs hL1 hdegR r
  have hL3 : ∀ l, s * (t * s) ≤ walkTotal Q 3 (Sum.inl l) := by
    intro l
    simpa [Q] using walkTotal_succ_left_lower B 2 (t * s) s
      (mul_nonneg ht hs) hR2 hdegL l
  have hR3 : ∀ r, t * (s * t) ≤ walkTotal Q 3 (Sum.inr r) := by
    intro r
    simpa [Q] using walkTotal_succ_right_lower B 2 (s * t) t
      (mul_nonneg hs ht) hL2 hdegR r
  have hL4 : ∀ l, (s * t) ^ 2 ≤ walkTotal Q 4 (Sum.inl l) := by
    intro l
    have := walkTotal_succ_left_lower B 3 (t * (s * t)) s
      (mul_nonneg ht (mul_nonneg hs ht)) hR3 hdegL l
    convert this using 1 <;> ring
  have hR4 : ∀ r, (s * t) ^ 2 ≤ walkTotal Q 4 (Sum.inr r) := by
    intro r
    have := walkTotal_succ_right_lower B 3 (s * (t * s)) t
      (mul_nonneg hs (mul_nonneg ht hs)) hL3 hdegR r
    convert this using 1 <;> ring
  have hL5 : ∀ l, s * (s * t) ^ 2 ≤ walkTotal Q 5 (Sum.inl l) := by
    intro l
    simpa [Q] using walkTotal_succ_left_lower B 4 ((s * t) ^ 2) s
      (sq_nonneg _) hR4 hdegL l
  have hR5 : ∀ r, t * (s * t) ^ 2 ≤ walkTotal Q 5 (Sum.inr r) := by
    intro r
    simpa [Q] using walkTotal_succ_right_lower B 4 ((s * t) ^ 2) t
      (sq_nonneg _) hL4 hdegR r
  have hL6 : ∀ l, (s * t) ^ 3 ≤ walkTotal Q 6 (Sum.inl l) := by
    intro l
    have := walkTotal_succ_left_lower B 5 (t * (s * t) ^ 2) s
      (mul_nonneg ht (sq_nonneg _)) hR5 hdegL l
    convert this using 1 <;> ring
  let T : ℝ := ∑ l : L, ∑ l' : L, walkCount Q 6 (Sum.inl l) (Sum.inl l')
  let S : ℝ := ∑ l : L, ∑ l' : L, walkCount Q 6 (Sum.inl l) (Sum.inl l') ^ 2
  have htotal_l (l : L) : (s * t) ^ 3 ≤
      ∑ l' : L, walkCount Q 6 (Sum.inl l) (Sum.inl l') := by
    have htot := hL6 l
    rw [walkTotal] at htot
    simp only [Fintype.sum_sum_type, Q] at htot
    simpa [walkCount_six_left_right_eq_zero] using htot
  have hTlower : (Fintype.card L : ℝ) * (s * t) ^ 3 ≤ T := by
    dsimp [T]
    calc
      (Fintype.card L : ℝ) * (s * t) ^ 3 = ∑ _l : L, (s * t) ^ 3 := by simp
      _ ≤ ∑ l : L, ∑ l' : L, walkCount Q 6 (Sum.inl l) (Sum.inl l') := by
        apply Finset.sum_le_sum
        intro l hl
        exact htotal_l l
  have hcs : T ^ 2 ≤ (Fintype.card L : ℝ) ^ 2 * S := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (L × L)))
      (f := fun z ↦ walkCount Q 6 (Sum.inl z.1) (Sum.inl z.2))
    simpa [T, S, Fintype.sum_prod_type, Fintype.card_prod, pow_two] using h
  have hcardL : (0 : ℝ) < Fintype.card L := by positivity
  have hST : (s * t) ^ 6 ≤ S := by
    have hsq := pow_le_pow_left₀
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg hs ht) 3)) hTlower 2
    have hmul : (Fintype.card L : ℝ) ^ 2 * (s * t) ^ 6 ≤
        (Fintype.card L : ℝ) ^ 2 * S := by
      calc
        (Fintype.card L : ℝ) ^ 2 * (s * t) ^ 6 =
            ((Fintype.card L : ℝ) * (s * t) ^ 3) ^ 2 := by ring
        _ ≤ T ^ 2 := hsq
        _ ≤ (Fintype.card L : ℝ) ^ 2 * S := hcs
    by_contra hn
    have hlt : S < (s * t) ^ 6 := lt_of_not_ge hn
    have hstrict := mul_lt_mul_of_pos_left hlt (sq_pos_of_pos hcardL)
    exact (not_lt_of_ge hmul) hstrict
  calc
    (s * t) ^ 6 ≤ S := hST
    _ ≤ homCycleCount Q 12 := by
      rw [show 12 = 2 * 6 by norm_num, homCycleCount_even_eq_sum_sq]
      simp only [Fintype.sum_sum_type, Q, S]
      simp_rw [Finset.sum_add_distrib]
      have h₁ : 0 ≤ ∑ x : L, ∑ y : R,
          walkCount (bipartiteRelGraph B) 6 (Sum.inl x) (Sum.inr y) ^ 2 := by positivity
      have h₂ : 0 ≤ ∑ x : R, ∑ y : L,
          walkCount (bipartiteRelGraph B) 6 (Sum.inr x) (Sum.inl y) ^ 2 := by positivity
      have h₃ : 0 ≤ ∑ x : R, ∑ y : R,
          walkCount (bipartiteRelGraph B) 6 (Sum.inr x) (Sum.inr y) ^ 2 := by positivity
      linarith

def directedEdgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  Finset.univ.filter fun e ↦ G.Adj e.1 e.2

@[simp] lemma mem_directedEdgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    (u, v) ∈ directedEdgeFinset G ↔ G.Adj u v := by
  simp [directedEdgeFinset]

lemma directedEdgeFinset_card_eq_sum_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (directedEdgeFinset G).card = ∑ v : V, G.degree v := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ)
    (f := Prod.fst) (s := directedEdgeFinset G) (by simp)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [SimpleGraph.degree]
  apply Finset.card_bij (fun e _ ↦ e.2)
  · intro e he
    rw [Finset.mem_filter] at he
    have hadj := (mem_directedEdgeFinset G e.1 e.2).mp he.1
    simpa [he.2] using hadj
  · intro e₁ he₁ e₂ he₂ h
    have h₁ := (Finset.mem_filter.mp he₁).2
    have h₂ := (Finset.mem_filter.mp he₂).2
    exact Prod.ext (h₁.trans h₂.symm) h
  · intro w hw
    refine ⟨(v, w), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨(mem_directedEdgeFinset G v w).mpr (by simpa using hw), rfl⟩

noncomputable def degreeIndex200 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (v : V) : Fin 200 :=
  ⟨Nat.log b (G.degree v), Nat.log_lt_of_lt_pow' (by norm_num) (hdegree v)⟩

lemma degreeIndex200_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (v : V) (hv : G.degree v ≠ 0) :
    b ^ (degreeIndex200 G b hdegree v).1 ≤ G.degree v :=
  Nat.pow_log_le_self b hv

lemma degreeIndex200_upper {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ) (hb : 1 < b)
    (hdegree : ∀ v, G.degree v < b ^ 200) (v : V) :
    G.degree v < b ^ ((degreeIndex200 G b hdegree v).1 + 1) :=
  Nat.lt_pow_succ_log_self hb _

abbrev DegreeBin200 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i : Fin 200) :=
  {v : V // degreeIndex200 G b hdegree v = i ∧ G.degree v ≠ 0}

def degreeBinRel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i j : Fin 200) :
    DegreeBin200 G b hdegree i → DegreeBin200 G b hdegree j → Prop :=
  fun u v ↦ G.Adj u.1 v.1

instance degreeBinRel.instDecidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i j : Fin 200) :
    ∀ u v, Decidable (degreeBinRel G b hdegree i j u v) := by
  intro u v
  exact inferInstanceAs (Decidable (G.Adj u.1 v.1))

noncomputable def degreeEdgeFiber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (ij : Fin 200 × Fin 200) :
    Finset (V × V) :=
  (directedEdgeFinset G).filter fun e ↦
    (degreeIndex200 G b hdegree e.1, degreeIndex200 G b hdegree e.2) = ij

lemma degreeEdgeFiber_card_eq_rel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i j : Fin 200) :
    (degreeEdgeFiber G b hdegree (i, j)).card =
      (relEdgeFinset (degreeBinRel G b hdegree i j)).card := by
  classical
  apply Finset.card_bij (fun e he ↦
    (⟨e.1, congrArg Prod.fst (Finset.mem_filter.mp he).2,
      ((mem_directedEdgeFinset G e.1 e.2).mp (Finset.mem_filter.mp he).1).degree_pos_left.ne'⟩,
      ⟨e.2, congrArg Prod.snd (Finset.mem_filter.mp he).2,
      ((mem_directedEdgeFinset G e.1 e.2).mp (Finset.mem_filter.mp he).1).degree_pos_right.ne'⟩))
  · intro e he
    rw [mem_relEdgeFinset]
    exact (mem_directedEdgeFinset G e.1 e.2).mp (Finset.mem_filter.mp he).1
  · intro e₁ he₁ e₂ he₂ h
    exact Prod.ext (congrArg (fun z ↦ z.1.1) h) (congrArg (fun z ↦ z.2.1) h)
  · intro e he
    refine ⟨(e.1.1, e.2.1), ?_, rfl⟩
    rw [degreeEdgeFiber, Finset.mem_filter]
    have he' : degreeBinRel G b hdegree i j e.1 e.2 :=
      (mem_relEdgeFinset (degreeBinRel G b hdegree i j) e.1 e.2).mp he
    exact ⟨(mem_directedEdgeFinset G _ _).mpr he', Prod.ext e.1.2.1 e.2.2.1⟩

set_option linter.constructorNameAsVariable false in
lemma exists_large_degreeEdgeFiber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) :
    ∃ ij : Fin 200 × Fin 200, (directedEdgeFinset G).card ≤
      40000 * (degreeEdgeFiber G b hdegree ij).card := by
  classical
  let f : Fin 200 × Fin 200 → ℕ := fun ij ↦ (degreeEdgeFiber G b hdegree ij).card
  obtain ⟨ij, hij⟩ := Finite.exists_max f
  refine ⟨ij, ?_⟩
  calc
    (directedEdgeFinset G).card = ∑ z : Fin 200 × Fin 200, f z := by
      rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ)
        (f := fun e ↦ (degreeIndex200 G b hdegree e.1,
          degreeIndex200 G b hdegree e.2)) (s := directedEdgeFinset G) (by simp)]
      apply Finset.sum_congr rfl
      intro z hz
      rfl
    _ ≤ ∑ _z : Fin 200 × Fin 200, f ij := by
      apply Finset.sum_le_sum
      intro z hz
      exact hij z
    _ = 40000 * (degreeEdgeFiber G b hdegree ij).card := by
      simp [f]

def sumPairMap {L R V : Type*} (fL : L → OrderedPair V)
    (fR : R → OrderedPair V) : L ⊕ R → OrderedPair V
  | Sum.inl l => fL l
  | Sum.inr r => fR r

def pairSupportConflictVia {L R V : Type*} [DecidableEq V]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V) :
    (L ⊕ R) → (L ⊕ R) → Prop :=
  fun x y ↦ ¬Disjoint (orderedPairSupport (sumPairMap fL fR x))
    (orderedPairSupport (sumPairMap fL fR y))

noncomputable instance pairSupportConflictVia.instDecidableRel
    {L R V : Type*} [DecidableEq V]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V) :
    DecidableRel (pairSupportConflictVia fL fR) := by
  intro x y
  exact Classical.propDecidable _

lemma pairSupportConflictVia_symm {L R V : Type*} [DecidableEq V]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V) :
    Symmetric (pairSupportConflictVia fL fR) := by
  intro x y h
  exact fun hdisj ↦ h hdisj.symm

def ClosedWalk.mapHom12 {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (w : ClosedWalk G 12) : ClosedWalk H 12 :=
  ⟨f w.1, ⟨w.2.1.map f, by simpa using w.2.2⟩⟩

@[simp] lemma ClosedWalk.mapHom12_getVert {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G →g H) (w : ClosedWalk G 12) (i : ℕ) :
    (w.mapHom12 f).2.1.getVert i = f (w.2.1.getVert i) := by
  simp [ClosedWalk.mapHom12, SimpleGraph.Walk.getVert_map]

lemma all_closedWalks_conflicting_of_free
    {L R V : Type*} [Fintype L] [Fintype R] [Fintype V]
    [DecidableEq L] [DecidableEq R] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V)
    (hmap : ∀ l r, B l r → pairComplete G (fL l) (fR r))
    (hfree : counterexampleGraph.Free G)
    (w : ClosedWalk (bipartiteRelGraph B) 12) :
    ∃ i j : Fin 12, i ≠ j ∧
      pairSupportConflictVia fL fR (w.2.1.getVert i.1) (w.2.1.getVert j.1) := by
  let f := bipartiteRelGraphHom (pairAuxGraph G) fL fR hmap
  let w' := w.mapHom12 f
  by_contra hn
  push_neg at hn
  have hgood : w'.HasDisjointPairSupports G := by
    intro i j hij
    have := hn i j hij
    dsimp only [w', ClosedWalk.mapHom12]
    simp only [SimpleGraph.Walk.getVert_map]
    dsimp only [f, bipartiteRelGraphHom]
    simp only [RelHom.coeFn_mk]
    have hsum (x : L ⊕ R) : Sum.elim fL fR x = sumPairMap fL fR x := by
      cases x <;> rfl
    rw [hsum, hsum]
    exact Classical.not_not.mp this
  exact hfree (counterexampleGraph_isContained_of_goodClosedWalk G w' hgood)

lemma relLeftDegreeReal_le_auxDegree
    {L R V : Type*} [Fintype L] [Fintype R] [Fintype V]
    [DecidableEq L] [DecidableEq R] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V)
    (hfR : Function.Injective fR)
    (hmap : ∀ l r, B l r → pairComplete G (fL l) (fR r)) (l : L) :
    relLeftDegreeReal B l ≤ (pairAuxGraph G).degree (fL l) := by
  classical
  let candidates := Finset.univ.filter fun r ↦ B l r
  have hcard : (candidates.card : ℝ) = relLeftDegreeReal B l := by
    rw [relLeftDegreeReal]
    simp [candidates, apply_ite]
  rw [← hcard]
  norm_cast
  apply Finset.card_le_card_of_injOn fR
  · intro r hr
    change fR r ∈ (pairAuxGraph G).neighborFinset (fL l)
    rw [(pairAuxGraph G).mem_neighborFinset]
    exact hmap l r (Finset.mem_filter.mp hr).2
  · exact fun _ _ _ _ h ↦ hfR h

lemma leftConflictDegreeReal_le_auxConflict
    {L R V : Type*} [Fintype L] [Fintype R] [Fintype V]
    [DecidableEq L] [DecidableEq R] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (fL : L → OrderedPair V) (fR : R → OrderedPair V)
    (hfL : Function.Injective fL)
    (hmap : ∀ l r, B l r → pairComplete G (fL l) (fR r))
    (u : L ⊕ R) (r : R) :
    leftConflictDegreeReal B (pairSupportConflictVia fL fR) u r ≤
      4 * (Real.sqrt ((pairAuxGraph G).degree (fR r) : ℝ) + 1) := by
  classical
  let candidates := {l : L // B l r ∧
    pairSupportConflictVia fL fR (Sum.inl l) u}
  have hcard : (Nat.card candidates : ℝ) =
      leftConflictDegreeReal B (pairSupportConflictVia fL fR) u r := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, leftConflictDegreeReal]
    simp [candidates]
  rw [← hcard]
  let encode : candidates →
      LocalConflictNeighbor G (sumPairMap fL fR u) (fR r) := fun z ↦
    ⟨fL z.1, (pairComplete_comm G _ _).mpr (hmap z.1 r z.2.1),
      fun hd ↦ z.2.2 hd.symm⟩
  have hencode : Function.Injective encode := by
    intro z z' h
    apply Subtype.ext
    apply hfL
    exact congrArg Subtype.val h
  calc
    (Nat.card candidates : ℝ) ≤
        Nat.card (LocalConflictNeighbor G (sumPairMap fL fR u) (fR r)) := by
      exact_mod_cast Nat.card_le_card_of_injective encode hencode
    _ ≤ 4 * (Real.sqrt ((pairAuxGraph G).degree (fR r) : ℝ) + 1) :=
      localConflictNeighbor_card_real_le G _ _

abbrev CoreLeft {L : Type*} (S : Finset L) := {l : L // l ∈ S}
abbrev CoreRight {R : Type*} (T : Finset R) := {r : R // r ∈ T}

def coreRel {L R : Type*} (B : L → R → Prop) (S : Finset L) (T : Finset R) :
    CoreLeft S → CoreRight T → Prop := fun l r ↦ B l.1 r.1

instance coreRel.instDecidable {L R : Type*} (B : L → R → Prop)
    [∀ l r, Decidable (B l r)] (S : Finset L) (T : Finset R) :
    ∀ l r, Decidable (coreRel B S T l r) := by
  intro l r
  exact inferInstanceAs (Decidable (B l.1 r.1))

lemma relLeftDegreeReal_coreRel
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) (l : CoreLeft S) :
    relLeftDegreeReal (coreRel B S T) l = restrictedLeftDegree B T l.1 := by
  classical
  rw [relLeftDegreeReal]
  have hpoint (r : CoreRight T) :
      (if coreRel B S T l r then (1 : ℝ) else 0) =
        if B l.1 r.1 then 1 else 0 := by
    by_cases h : B l.1 r.1 <;> simp [coreRel, h]
  simp_rw [hpoint]
  calc
    (∑ r : CoreRight T, if B l.1 r.1 then (1 : ℝ) else 0) =
        ∑ r ∈ T, if B l.1 r then 1 else 0 :=
      (Finset.sum_subtype T (fun _ ↦ Iff.rfl)
        (fun r ↦ if B l.1 r then (1 : ℝ) else 0)).symm
    _ = restrictedLeftDegree B T l.1 := by
      simpa [restrictedLeftDegree] using
        (Finset.sum_boole (R := ℝ) (fun r : R ↦ B l.1 r) T)

lemma relRightDegreeReal_coreRel
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) (r : CoreRight T) :
    relLeftDegreeReal (fun r l ↦ coreRel B S T l r) r =
      restrictedRightDegree B S r.1 := by
  classical
  rw [relLeftDegreeReal]
  have hpoint (l : CoreLeft S) :
      (if coreRel B S T l r then (1 : ℝ) else 0) =
        if B l.1 r.1 then 1 else 0 := by
    by_cases h : B l.1 r.1 <;> simp [coreRel, h]
  simp_rw [hpoint]
  calc
    (∑ l : CoreLeft S, if B l.1 r.1 then (1 : ℝ) else 0) =
        ∑ l ∈ S, if B l r.1 then 1 else 0 :=
      (Finset.sum_subtype S (fun _ ↦ Iff.rfl)
        (fun l ↦ if B l r.1 then (1 : ℝ) else 0)).symm
    _ = restrictedRightDegree B S r.1 := by
      simpa [restrictedRightDegree] using
        (Finset.sum_boole (R := ℝ) (fun l : L ↦ B l r.1) S)

lemma relEdgeFinset_card_real_eq_sum_left
    {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    ((relEdgeFinset B).card : ℝ) = ∑ l : L, relLeftDegreeReal B l := by
  simp only [relLeftDegreeReal]
  rw [← Finset.sum_product' (Finset.univ : Finset L) (Finset.univ : Finset R)]
  rw [Finset.univ_product_univ]
  rw [relEdgeFinset]
  exact (Finset.sum_boole (R := ℝ) (fun e : L × R ↦ B e.1 e.2)
    (Finset.univ : Finset (L × R))).symm

lemma relLeftDegreeReal_le_graphDegree
    {L R V : Type*} [Fintype L] [Fintype R] [Fintype V]
    [DecidableEq R] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (fL : L → V) (fR : R → V) (hfR : Function.Injective fR)
    (hmap : ∀ l r, B l r → G.Adj (fL l) (fR r)) (l : L) :
    relLeftDegreeReal B l ≤ G.degree (fL l) := by
  classical
  let candidates := Finset.univ.filter fun r ↦ B l r
  have hcard : (candidates.card : ℝ) = relLeftDegreeReal B l := by
    rw [relLeftDegreeReal]
    simpa [candidates] using
      (Finset.sum_boole (R := ℝ) (fun r : R ↦ B l r) Finset.univ).symm
  rw [← hcard]
  norm_cast
  apply Finset.card_le_card_of_injOn fR
  · intro r hr
    simpa using hmap l r (Finset.mem_filter.mp hr).2
  · exact fun _ _ _ _ h ↦ hfR h

lemma relEdgeFinset_coreRel_card_le
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) :
    (relEdgeFinset (coreRel B S T)).card ≤ (relEdgeFinset B).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun e ↦ (e.1.1, e.2.1))
  · intro e he
    exact (mem_relEdgeFinset B _ _).mpr ((mem_relEdgeFinset (coreRel B S T) _ _).mp he)
  · intro e₁ he₁ e₂ he₂ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

lemma homCycleCount_bipartiteRel_two
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    homCycleCount (bipartiteRelGraph B) 2 = 2 * (relEdgeFinset B).card := by
  rw [show 2 = 2 * 1 by norm_num, homCycleCount_even_eq_sum_sq]
  simp only [Fintype.sum_sum_type]
  have hwalk (l : L) (r : R) :
      walkCount (bipartiteRelGraph B) 1 (Sum.inl l) (Sum.inr r) =
        if B l r then 1 else 0 := by
    rw [walkCount, pow_one]
    change (if B l r then 1 else 0) = _
    rfl
  have hwalk' (r : R) (l : L) :
      walkCount (bipartiteRelGraph B) 1 (Sum.inr r) (Sum.inl l) =
        if B l r then 1 else 0 := by
    rw [walkCount, pow_one]
    change (if B l r then 1 else 0) = _
    rfl
  have hzeroLL (l l' : L) :
      walkCount (bipartiteRelGraph B) 1 (Sum.inl l) (Sum.inl l') = 0 := by
    rw [walkCount, pow_one]
    change (if False then 1 else 0) = 0
    simp
  have hzeroRR (r r' : R) :
      walkCount (bipartiteRelGraph B) 1 (Sum.inr r) (Sum.inr r') = 0 := by
    rw [walkCount, pow_one]
    change (if False then 1 else 0) = 0
    simp
  simp_rw [hwalk, hwalk', hzeroLL, hzeroRR]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
    zero_add, add_zero]
  have hcount :
      (∑ l : L, ∑ r : R, (if B l r then (1 : ℝ) else 0) ^ 2) =
        (relEdgeFinset B).card := by
    calc
      (∑ l : L, ∑ r : R, (if B l r then (1 : ℝ) else 0) ^ 2) =
          ∑ e : L × R, (if B e.1 e.2 then (1 : ℝ) else 0) ^ 2 :=
        by
          simpa only [Finset.univ_product_univ] using
            (Finset.sum_product' (Finset.univ : Finset L)
              (Finset.univ : Finset R)
              (fun l r ↦ (if B l r then (1 : ℝ) else 0) ^ 2)).symm
      _ = (relEdgeFinset B).card := by
        have hsq (e : L × R) :
            (if B e.1 e.2 then (1 : ℝ) else 0) ^ 2 =
              if B e.1 e.2 then 1 else 0 := by
          by_cases h : B e.1 e.2 <;> simp [h]
        simp_rw [hsq]
        rw [relEdgeFinset]
        exact Finset.sum_boole (R := ℝ) (fun e : L × R ↦ B e.1 e.2)
          (Finset.univ : Finset (L × R))
  have hcount' :
      (∑ r : R, ∑ l : L, (if B l r then (1 : ℝ) else 0) ^ 2) =
        (relEdgeFinset B).card := by
    rw [Finset.sum_comm]
    exact hcount
  rw [hcount]
  rw [hcount']
  ring

lemma degreeBin_card_mul_lower_le_directedEdge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i : Fin 200) :
    Fintype.card (DegreeBin200 G b hdegree i) * b ^ i.1 ≤
      (directedEdgeFinset G).card := by
  classical
  rw [directedEdgeFinset_card_eq_sum_degree]
  calc
    Fintype.card (DegreeBin200 G b hdegree i) * b ^ i.1 =
        ∑ _v : DegreeBin200 G b hdegree i, b ^ i.1 := by simp
    _ ≤ ∑ v : DegreeBin200 G b hdegree i, G.degree v.1 := by
      apply Finset.sum_le_sum
      intro v hv
      simpa [v.2.1] using degreeIndex200_lower G b hdegree v.1 v.2.2
    _ ≤ ∑ v : V, G.degree v := by
      rw [← Finset.sum_subtype
        ((Finset.univ : Finset V).filter fun v ↦
          degreeIndex200 G b hdegree v = i ∧ G.degree v ≠ 0)
        (fun v ↦ by simp) (fun v ↦ G.degree v)]
      exact Finset.sum_le_sum_of_subset (by simp)

lemma degreeBinRel_edge_card_le_card_mul_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ) (hb : 1 < b)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i j : Fin 200) :
    (relEdgeFinset (degreeBinRel G b hdegree i j)).card ≤
      Fintype.card (DegreeBin200 G b hdegree i) * b ^ (i.1 + 1) := by
  have hsum := relEdgeFinset_card_real_eq_sum_left
    (degreeBinRel G b hdegree i j)
  have hdeg (l : DegreeBin200 G b hdegree i) :
      relLeftDegreeReal (degreeBinRel G b hdegree i j) l ≤
        (b ^ (i.1 + 1) : ℕ) := by
    calc
      relLeftDegreeReal (degreeBinRel G b hdegree i j) l ≤ G.degree l.1 :=
        relLeftDegreeReal_le_graphDegree G (degreeBinRel G b hdegree i j)
          (fun u ↦ u.1) (fun v ↦ v.1)
          (fun _ _ h ↦ Subtype.ext h) (fun _ _ h ↦ h) l
      _ ≤ (b ^ (i.1 + 1) : ℕ) := by
        have hu := (degreeIndex200_upper G b hb hdegree l.1).le
        rw [l.2.1] at hu
        exact_mod_cast hu
  have hreal :
      ((relEdgeFinset (degreeBinRel G b hdegree i j)).card : ℝ) ≤
        Fintype.card (DegreeBin200 G b hdegree i) *
          (b ^ (i.1 + 1) : ℕ) := by
    rw [hsum]
    calc
      (∑ l : DegreeBin200 G b hdegree i,
          relLeftDegreeReal (degreeBinRel G b hdegree i j) l) ≤
          ∑ _l : DegreeBin200 G b hdegree i,
            ((b ^ (i.1 + 1) : ℕ) : ℝ) := by
        exact Finset.sum_le_sum fun l _ ↦ hdeg l
      _ = Fintype.card (DegreeBin200 G b hdegree i) *
          (b ^ (i.1 + 1) : ℕ) := by simp
  exact_mod_cast hreal

lemma relEdgeFinset_transpose_card
    {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    (relEdgeFinset (fun r l ↦ B l r)).card = (relEdgeFinset B).card := by
  classical
  apply Finset.card_bij (fun e _ ↦ (e.2, e.1))
  · intro e he
    simpa using (mem_relEdgeFinset (fun r l ↦ B l r) e.1 e.2).mp he
  · intro e₁ h₁ e₂ h₂ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro e he
    refine ⟨(e.2, e.1), ?_, rfl⟩
    simpa using (mem_relEdgeFinset B e.1 e.2).mp he

/-- The explicit absolute constant in the seventh-power bound for the
ordered-pair auxiliary graph.  Its size is irrelevant; keeping it factored
makes the arithmetic proof transparent. -/
noncomputable def auxiliarySeventhPowerConstant : ℝ :=
  40000 ^ 7 * (2 * 160000 ^ 12 * 16000000 ^ 5) ^ 2

end Erdos147

import ErdosProblems.Erdos88.QuadraticHypergeometric
import ErdosProblems.Erdos88.Concentration
import ErdosProblems.Erdos88.PermutationConcentration
import ErdosProblems.Erdos88.BooleanSlices

/-!
# Joint hypergeometric anticoncentration for the quadratic argument

This file develops the finite conditioning machinery used in KSSS
Lemma 8.3.  The first layer is an exact counting version of the finite
chain rule: a uniform bound for every successive prefix extension gives
the corresponding power bound for the joint event.
-/

namespace Erdos88
namespace QuadraticCancellation

open scoped BigOperators

universe u

/-- The points satisfying the first `k` events of a finite sequence. -/
noncomputable def prefixEventFinset {Ω : Type u} [Fintype Ω] {q : ℕ}
    (E : Fin q → Ω → Prop) (k : ℕ) : Finset Ω := by
  classical
  exact Finset.univ.filter fun ω ↦ ∀ i : Fin q, i.val < k → E i ω

@[simp] lemma prefixEventFinset_zero {Ω : Type u} [Fintype Ω] {q : ℕ}
    (E : Fin q → Ω → Prop) :
    prefixEventFinset E 0 = Finset.univ := by
  classical
  ext ω
  simp [prefixEventFinset]

lemma mem_prefixEventFinset_succ {Ω : Type u} [Fintype Ω] {q k : ℕ}
    (E : Fin q → Ω → Prop) (hk : k < q) (ω : Ω) :
    ω ∈ prefixEventFinset E (k + 1) ↔
      ω ∈ prefixEventFinset E k ∧ E ⟨k, hk⟩ ω := by
  classical
  simp only [prefixEventFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro h
    refine ⟨fun i hi ↦ h i (Nat.lt_succ_of_lt hi),
      h ⟨k, hk⟩ (Nat.lt_succ_self k)⟩
  · rintro ⟨hprefix, hkEvent⟩ i hi
    by_cases hik : i.val = k
    · have hiEq : i = (⟨k, hk⟩ : Fin q) :=
        Fin.ext (by simpa using hik)
      simpa only [hiEq] using hkEvent
    · exact hprefix i (by omega)

lemma mem_prefixEventFinset_full {Ω : Type u} [Fintype Ω] {q : ℕ}
    (E : Fin q → Ω → Prop) (ω : Ω) :
    ω ∈ prefixEventFinset E q ↔ ∀ i, E i ω := by
  classical
  simp only [prefixEventFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro h i
    exact h i i.isLt
  · intro h i _
    exact h i

/-- Exact finite chain rule in cardinality form.  Empty prefixes cause no
special case: the successor inequality is stated without division. -/
lemma card_prefixEventFinset_le_pow {Ω : Type u} [Fintype Ω] {q : ℕ}
    (E : Fin q → Ω → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hstep : ∀ k (hk : k < q),
      ((prefixEventFinset E (k + 1)).card : ℝ) ≤
        B * (prefixEventFinset E k).card) :
    ((prefixEventFinset E q).card : ℝ) ≤ B ^ q * Fintype.card Ω := by
  have hprefix : ∀ k ≤ q,
      ((prefixEventFinset E k).card : ℝ) ≤
        B ^ k * Fintype.card Ω := by
    intro k hk
    induction k with
    | zero =>
        rw [prefixEventFinset_zero, Finset.card_univ, pow_zero, one_mul]
    | succ k ih =>
        calc
          ((prefixEventFinset E (k + 1)).card : ℝ) ≤
              B * (prefixEventFinset E k).card := hstep k (by omega)
          _ ≤ B * (B ^ k * Fintype.card Ω) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hB
          _ = B ^ (k + 1) * Fintype.card Ω := by
            rw [pow_succ]
            ring
  exact hprefix q le_rfl

/-- Uniform-probability form of the finite chain rule. -/
theorem uniformProbability_all_fin_le_pow
    {Ω : Type u} [Fintype Ω] [Nonempty Ω] {q : ℕ}
    (E : Fin q → Ω → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hstep : ∀ k (hk : k < q),
      ((prefixEventFinset E (k + 1)).card : ℝ) ≤
        B * (prefixEventFinset E k).card) :
    Concentration.uniformProbability (fun ω ↦ ∀ i, E i ω) ≤ B ^ q := by
  classical
  have hcard := card_prefixEventFinset_le_pow E B hB hstep
  have hprob :
      Concentration.uniformProbability (fun ω ↦ ∀ i, E i ω) =
        ((prefixEventFinset E q).card : ℝ) / Fintype.card Ω := by
    unfold Concentration.uniformProbability
    congr 1
    apply congrArg (fun S : Finset Ω ↦ (S.card : ℝ))
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_prefixEventFinset_full E ω).symm
  rw [hprob]
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ hΩ).2 (by simpa [mul_comm] using hcard)

/-! ### Fixed-size slice balance via a short permutation reveal -/

/-- The first `L` points of `Fin N`, embedded using a proof that they fit. -/
def finInitialSegment (N L : ℕ) (hL : L ≤ N) : Finset (Fin N) :=
  Finset.univ.map (Fin.castLEEmb hL)

@[simp] lemma card_finInitialSegment (N L : ℕ) (hL : L ≤ N) :
    (finInitialSegment N L hL).card = L := by
  simp [finInitialSegment]

@[simp] lemma mem_finInitialSegment {N L : ℕ} (hL : L ≤ N)
    (i : Fin N) :
    i ∈ finInitialSegment N L hL ↔ i.val < L := by
  constructor
  · intro hi
    rw [finInitialSegment, Finset.mem_map] at hi
    obtain ⟨j, _hj, rfl⟩ := hi
    exact j.isLt
  · intro hi
    rw [finInitialSegment, Finset.mem_map]
    exact ⟨⟨i.val, hi⟩, Finset.mem_univ _, Fin.ext rfl⟩

/-- Changing a predicate only on an exceptional set changes the real
cardinality of its filter by at most the size of that exceptional set. -/
lemma abs_card_filter_sub_le_card_exception {α : Type*} [DecidableEq α]
    (s : Finset α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred fun x ↦ P x ↔ ¬Q x] :
    |((s.filter P).card : ℝ) - (s.filter Q).card| ≤
      ((s.filter fun x ↦ P x ↔ ¬Q x).card : ℝ) := by
  let D := s.filter fun x ↦ P x ↔ ¬Q x
  have hPD : s.filter P ⊆ s.filter Q ∪ D := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    by_cases hQ : Q x
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx'.1, hQ⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hx'.1,
          ⟨fun _ ↦ hQ, fun _ ↦ hx'.2⟩⟩)
  have hQD : s.filter Q ⊆ s.filter P ∪ D := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    by_cases hP : P x
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx'.1, hP⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hx'.1, ⟨
          fun hp ↦ (hP hp).elim,
          fun hnq ↦ (hnq hx'.2).elim⟩⟩)
  have hPQNat : (s.filter P).card ≤ (s.filter Q).card + D.card :=
    (Finset.card_le_card hPD).trans (Finset.card_union_le _ _)
  have hQPNat : (s.filter Q).card ≤ (s.filter P).card + D.card :=
    (Finset.card_le_card hQD).trans (Finset.card_union_le _ _)
  have hPQ : ((s.filter P).card : ℝ) ≤
      (s.filter Q).card + D.card := by exact_mod_cast hPQNat
  have hQP : ((s.filter Q).card : ℝ) ≤
      (s.filter P).card + D.card := by exact_mod_cast hQPNat
  rw [abs_le]
  constructor <;> dsimp only [D] at * <;> linarith

/-- Number of the first `R` domain points that a permutation sends into
the first `L` range points. -/
noncomputable def permutationInitialCount
    (N R L : ℕ) (hR : R ≤ N) (hL : L ≤ N)
    (σ : Equiv.Perm (Fin N)) : ℝ :=
  ((finInitialSegment N R hR).filter fun i ↦
    σ i ∈ finInitialSegment N L hL).card

lemma permutationInitialCount_prefix
    (N R L : ℕ) (hR : R ≤ N) (hL : L ≤ N)
    (σ τ : Equiv.Perm (Fin N))
    (hστ : ∀ i : Fin R,
      σ (Fin.castLE hR i) = τ (Fin.castLE hR i)) :
    permutationInitialCount N R L hR hL σ =
      permutationInitialCount N R L hR hL τ := by
  unfold permutationInitialCount
  congr 2
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hiR, hiL⟩
    refine ⟨hiR, ?_⟩
    have hi : i.val < R := (mem_finInitialSegment hR i).mp hiR
    let j : Fin R := ⟨i.val, hi⟩
    have hij : Fin.castLE hR j = i := Fin.ext rfl
    have heq := hστ j
    rw [hij] at heq
    rw [← heq]
    exact hiL
  · rintro ⟨hiR, hiL⟩
    refine ⟨hiR, ?_⟩
    have hi : i.val < R := (mem_finInitialSegment hR i).mp hiR
    let j : Fin R := ⟨i.val, hi⟩
    have hij : Fin.castLE hR j = i := Fin.ext rfl
    have heq := hστ j
    rw [hij] at heq
    rw [heq]
    exact hiL

lemma permutationInitialCount_leftSwap_diff_le
    (N R L : ℕ) (hR : R ≤ N) (hL : L ≤ N)
    (σ : Equiv.Perm (Fin N)) (p q : Fin N) :
    |permutationInitialCount N R L hR hL σ -
      permutationInitialCount N R L hR hL (Equiv.swap p q * σ)| ≤ 2 := by
  classical
  let A := finInitialSegment N R hR
  let T := finInitialSegment N L hL
  let P : Fin N → Prop := fun i ↦ σ i ∈ T
  let Q : Fin N → Prop := fun i ↦ (Equiv.swap p q * σ) i ∈ T
  let D := A.filter fun i ↦ P i ↔ ¬Q i
  have hDmap : Set.MapsTo (fun i ↦ σ i) (D : Set (Fin N))
      ({p, q} : Finset (Fin N)) := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    by_contra hpq
    change σ i ∉ ({p, q} : Finset (Fin N)) at hpq
    have hpq' : σ i ≠ p ∧ σ i ≠ q := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hpq
    have hip : σ i ≠ p := hpq'.1
    have hiq : σ i ≠ q := hpq'.2
    have hfix : (Equiv.swap p q * σ) i = σ i := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hip hiq]
    dsimp only [P, Q] at hi'
    rw [hfix] at hi'
    by_cases hmem : σ i ∈ T
    · exact (hi'.mp hmem) hmem
    · exact hmem (hi'.mpr hmem)
  have hDcard : D.card ≤ 2 := by
    calc
      D.card ≤ ({p, q} : Finset (Fin N)).card :=
        Finset.card_le_card_of_injOn (fun i ↦ σ i) hDmap
          (fun _ _ _ _ h ↦ σ.injective h)
      _ ≤ 2 := by
        exact (Finset.card_insert_le p {q}).trans_eq (by simp)
  have hdiff := abs_card_filter_sub_le_card_exception A P Q
  change |permutationInitialCount N R L hR hL σ -
      permutationInitialCount N R L hR hL (Equiv.swap p q * σ)| ≤ 2
  change |((A.filter P).card : ℝ) - (A.filter Q).card| ≤ 2
  calc
    |((A.filter P).card : ℝ) - (A.filter Q).card| ≤ (D.card : ℝ) := by
      simpa only [D] using hdiff
    _ ≤ 2 := by exact_mod_cast hDcard

noncomputable def permutationHit
    (N L : ℕ) (hL : L ≤ N) (i : Fin N)
    (σ : Equiv.Perm (Fin N)) : ℝ :=
  if σ i ∈ finInitialSegment N L hL then 1 else 0

lemma sum_permutationHit (N L : ℕ) (hL : L ≤ N + 1)
    (i : Fin (N + 1)) :
    ∑ σ : Equiv.Perm (Fin (N + 1)),
        permutationHit (N + 1) L hL i σ =
      (N.factorial : ℝ) * L := by
  classical
  let T := finInitialSegment (N + 1) L hL
  have hmove :
      (∑ σ : Equiv.Perm (Fin (N + 1)),
          permutationHit (N + 1) L hL i σ) =
        ∑ σ : Equiv.Perm (Fin (N + 1)),
          permutationHit (N + 1) L hL 0 σ := by
    let e : Equiv.Perm (Equiv.Perm (Fin (N + 1))) :=
      Equiv.mulRight (Equiv.swap 0 i)
    have hsum := Equiv.sum_comp e (fun σ : Equiv.Perm (Fin (N + 1)) ↦
      permutationHit (N + 1) L hL 0 σ)
    calc
      (∑ σ : Equiv.Perm (Fin (N + 1)),
          permutationHit (N + 1) L hL i σ) =
          ∑ σ : Equiv.Perm (Fin (N + 1)),
            permutationHit (N + 1) L hL 0 (e σ) := by
              apply Finset.sum_congr rfl
              intro σ _
              simp [e, permutationHit, Equiv.Perm.mul_apply]
      _ = ∑ σ : Equiv.Perm (Fin (N + 1)),
          permutationHit (N + 1) L hL 0 σ := hsum
  rw [hmove]
  rw [FiniteSliceConcentration.sum_perm_decompose]
  simp only [permutationHit,
    Equiv.Perm.decomposeFin_symm_apply_zero]
  calc
    (∑ p : Fin (N + 1), ∑ _e : Equiv.Perm (Fin N),
        if p ∈ T then (1 : ℝ) else 0) =
        (N.factorial : ℝ) *
          ∑ p : Fin (N + 1), if p ∈ T then (1 : ℝ) else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _
            by_cases hp : p ∈ T <;>
              simp [hp, Fintype.card_perm, Fintype.card_fin]
    _ = (N.factorial : ℝ) * L := by
      rw [Finset.sum_boole]
      rw [show Finset.univ.filter (fun p : Fin (N + 1) ↦ p ∈ T) = T by
        ext p
        simp]
      rw [card_finInitialSegment]

lemma sum_permutationInitialCount
    (N R L : ℕ) (hR : R ≤ N + 1) (hL : L ≤ N + 1) :
    ∑ σ : Equiv.Perm (Fin (N + 1)),
        permutationInitialCount (N + 1) R L hR hL σ =
      (R : ℝ) * N.factorial * L := by
  classical
  let A := finInitialSegment (N + 1) R hR
  have hcount (σ : Equiv.Perm (Fin (N + 1))) :
      permutationInitialCount (N + 1) R L hR hL σ =
        ∑ i ∈ A, permutationHit (N + 1) L hL i σ := by
    unfold permutationInitialCount permutationHit
    change (((A.filter fun i ↦
      σ i ∈ finInitialSegment (N + 1) L hL).card : ℕ) : ℝ) = _
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  simp_rw [hcount]
  rw [Finset.sum_comm]
  simp_rw [sum_permutationHit N L hL]
  rw [Finset.sum_const, nsmul_eq_mul, card_finInitialSegment]
  ring

lemma uniformExpectation_permutationInitialCount
    (N R L : ℕ) (hR : R ≤ N + 1) (hL : L ≤ N + 1) :
    Concentration.uniformExpectation
        (permutationInitialCount (N + 1) R L hR hL) =
      (R : ℝ) * L / (N + 1) := by
  rw [Concentration.uniformExpectation,
    sum_permutationInitialCount N R L hR hL]
  simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]
  push_cast
  have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma uniformExpectation_permutationInitialCount_of_pos
    (N R L : ℕ) (hR : R ≤ N) (hL : L ≤ N) (hRpos : 0 < R) :
    Concentration.uniformExpectation
        (permutationInitialCount N R L hR hL) =
      (R : ℝ) * L / N := by
  cases N with
  | zero => omega
  | succ N =>
      simpa only [Nat.cast_succ] using
        uniformExpectation_permutationInitialCount N R L hR hL

/-- General ambient-size form of the permutation intersection-count tail. -/
theorem permutationInitialCount_two_sided_probability_of_pos
    (N R L : ℕ) (hR : R ≤ N) (hL : L ≤ N)
    (hRpos : 0 < R) (t : ℝ) (ht : 0 ≤ t) :
    Concentration.uniformProbability
        (fun σ : Equiv.Perm (Fin N) ↦
          t ≤ |permutationInitialCount N R L hR hL σ -
            (R : ℝ) * L / N|) ≤
      2 * Real.exp (-t ^ 2 / (8 * R)) := by
  rw [Concentration.uniformProbability]
  have htail := FiniteSliceConcentration.permutationPrefix_two_sided_tail
    hR (permutationInitialCount N R L hR hL) 2 t
    hRpos (by norm_num) ht
    (permutationInitialCount_prefix N R L hR hL)
    (permutationInitialCount_leftSwap_diff_le N R L hR hL)
  rw [uniformExpectation_permutationInitialCount_of_pos
    N R L hR hL hRpos] at htail
  have hden : (2 : ℝ) * R * 2 ^ 2 = 8 * R := by ring
  rw [hden] at htail
  have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin N)) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using htail

/-- Two-sided concentration for the number of the first `R` points sent
into the first `L` points by a uniform permutation.  This is the exact
fixed-size-slice balance estimate needed before applying Lemma 8.4. -/
theorem permutationInitialCount_two_sided_tail_count
    (N R L : ℕ) (hR : R ≤ N + 1) (hL : L ≤ N + 1)
    (hRpos : 0 < R) (t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin (N + 1)) ↦
        t ≤ |permutationInitialCount (N + 1) R L hR hL σ -
          (R : ℝ) * L / (N + 1)|).card : ℝ) ≤
      2 * Fintype.card (Equiv.Perm (Fin (N + 1))) *
        Real.exp (-t ^ 2 / (8 * R)) := by
  have htail := FiniteSliceConcentration.permutationPrefix_two_sided_tail
    hR (permutationInitialCount (N + 1) R L hR hL) 2 t
    hRpos (by norm_num) ht
    (permutationInitialCount_prefix (N + 1) R L hR hL)
    (permutationInitialCount_leftSwap_diff_le (N + 1) R L hR hL)
  rw [uniformExpectation_permutationInitialCount N R L hR hL] at htail
  convert htail using 1 <;> ring_nf

/-- Normalized probability form of
`permutationInitialCount_two_sided_tail_count`. -/
theorem permutationInitialCount_two_sided_probability
    (N R L : ℕ) (hR : R ≤ N + 1) (hL : L ≤ N + 1)
    (hRpos : 0 < R) (t : ℝ) (ht : 0 ≤ t) :
    Concentration.uniformProbability
        (fun σ : Equiv.Perm (Fin (N + 1)) ↦
          t ≤ |permutationInitialCount (N + 1) R L hR hL σ -
            (R : ℝ) * L / (N + 1)|) ≤
      2 * Real.exp (-t ^ 2 / (8 * R)) := by
  rw [Concentration.uniformProbability]
  have htail := permutationInitialCount_two_sided_tail_count
    N R L hR hL hRpos t ht
  have hcard : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin (N + 1))) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using htail

/-! ### Transport to a uniform Boolean slice -/

/-- Enumerate a finite ambient set so that an arbitrary subset occupies
the first block of slots. -/
lemma exists_aligned_finEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (I W : Finset α) (hW : W ⊆ I) :
    ∃ e : Fin I.card ≃ ↑I,
      (finInitialSegment I.card W.card (Finset.card_le_card hW)).map
          (e.toEmbedding.trans
            (Function.Embedding.subtype fun i : α ↦ i ∈ I)) = W := by
  classical
  let e₀ : Fin I.card ≃ ↑I := (Finset.equivFin I).symm
  let A := finInitialSegment I.card W.card (Finset.card_le_card hW)
  let C₀ := BooleanSlices.finsetLift I W
  let C : Finset (Fin I.card) := C₀.map e₀.symm.toEmbedding
  have hAC : A.card = C.card := by
    rw [show A.card = W.card by simp [A], Finset.card_map]
    exact (BooleanSlices.card_finsetLift I W hW).symm
  obtain ⟨ρ, hρ, _⟩ := BooleanSlices.exists_perm_map_disjoint_pair
    A ∅ C ∅ (Finset.disjoint_empty_right A)
      (Finset.disjoint_empty_right C) hAC rfl
  refine ⟨ρ.trans e₀, ?_⟩
  change A.map ((ρ.trans e₀).toEmbedding.trans
      (Function.Embedding.subtype fun i : α ↦ i ∈ I)) = W
  calc
    A.map ((ρ.trans e₀).toEmbedding.trans
        (Function.Embedding.subtype fun i : α ↦ i ∈ I)) =
        (A.map ρ.toEmbedding).map
          (e₀.toEmbedding.trans
            (Function.Embedding.subtype fun i : α ↦ i ∈ I)) := by
      rw [Finset.map_map]
      rfl
    _ = C.map (e₀.toEmbedding.trans
          (Function.Embedding.subtype fun i : α ↦ i ∈ I)) := by rw [hρ]
    _ = W := by
      simp only [C, C₀, Finset.map_map]
      convert BooleanSlices.map_finsetLift I W hW using 1
      ext i
      simp

/-- With an aligned enumeration, decoding the inverse permutation turns
intersection with `W` into the short-prefix permutation count. -/
lemma card_signedSlicePositiveSupport_inter_aligned
    {α : Type*} [Fintype α] [DecidableEq α]
    (I W : Finset α) (R ell : ℕ)
    (hR : R ≤ I.card) (hell : ell ≤ I.card)
    (e : Fin I.card ≃ ↑I)
    (hW : (finInitialSegment I.card R hR).map
      (e.toEmbedding.trans
        (Function.Embedding.subtype fun i : α ↦ i ∈ I)) = W)
    (σ : Equiv.Perm (Fin I.card)) :
    (((BooleanSlices.signedSlicePositiveSupport I ell 0
        (by simpa using hell) e σ.symm) ∩ W).card : ℝ) =
      permutationInitialCount I.card R ell hR hell σ := by
  classical
  let A := finInitialSegment I.card R hR
  let T := finInitialSegment I.card ell hell
  let emb : Fin I.card ↪ α := e.toEmbedding.trans
    (Function.Embedding.subtype fun i : α ↦ i ∈ I)
  have hset :
      BooleanSlices.signedSlicePositiveSupport I ell 0
          (by simpa using hell) e σ.symm ∩ W =
        (A.filter fun i ↦ σ i ∈ T).map emb := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxD, hxW⟩ := Finset.mem_inter.mp hx
      rw [← hW] at hxW
      obtain ⟨i, hiA, hix⟩ := Finset.mem_map.mp hxW
      rw [BooleanSlices.signedSlicePositiveSupport,
        Finset.mem_map] at hxD
      obtain ⟨j, _hj, hjx⟩ := hxD
      rw [Finset.mem_map]
      refine ⟨i, Finset.mem_filter.mpr ⟨hiA, ?_⟩, hix⟩
      have hslot : σ.symm (Fin.castLE hell j) = i := by
        apply emb.injective
        exact hjx.trans hix.symm
      have hσi : σ i = Fin.castLE hell j := by
        rw [← hslot, Equiv.apply_symm_apply]
      change σ i ∈ finInitialSegment I.card ell hell
      rw [mem_finInitialSegment hell]
      rw [hσi]
      exact j.isLt
    · intro hx
      obtain ⟨i, hi, hix⟩ := Finset.mem_map.mp hx
      obtain ⟨hiA, hiT⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · rw [BooleanSlices.signedSlicePositiveSupport, Finset.mem_map]
        have hlt : (σ i).val < ell :=
          (mem_finInitialSegment hell (σ i)).mp (by simpa only [T] using hiT)
        let j : Fin ell := ⟨(σ i).val, hlt⟩
        refine ⟨j, Finset.mem_univ _, ?_⟩
        have hj : Fin.castLE hell j = σ i := Fin.ext rfl
        change emb (σ.symm (Fin.castLE hell j)) = x
        rw [hj, Equiv.symm_apply_apply]
        exact hix
      · rw [← hW]
        exact Finset.mem_map.mpr ⟨i, hiA, hix⟩
  unfold permutationInitialCount
  change (((BooleanSlices.signedSlicePositiveSupport I ell 0
      (by simpa using hell) e σ.symm) ∩ W).card : ℝ) =
    (((A.filter fun i ↦ σ i ∈ T).card : ℕ) : ℝ)
  rw [hset, Finset.card_map]

/-- Uniform event probabilities are invariant under a finite equivalence. -/
lemma uniformProbability_comp_equiv {Ω Ω' : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Ω'] [Nonempty Ω']
    (E : Ω ≃ Ω') (Q : Ω' → Prop) :
    Concentration.uniformProbability (fun ω ↦ Q (E ω)) =
      Concentration.uniformProbability Q := by
  classical
  have h : (𝔼 ω : Ω, if Q (E ω) then (1 : ℝ) else 0) =
      𝔼 τ : Ω', if Q τ then (1 : ℝ) else 0 := by
    apply Fintype.expect_equiv E
    intro ω
    rfl
  simpa [Concentration.uniformProbability, Fintype.expect_eq_sum_div_card,
    Finset.sum_ite] using h

/-- Hypergeometric concentration for the intersection of a uniform
fixed-size subset with an arbitrary fixed coordinate set. -/
theorem booleanSlice_intersection_two_sided_probability
    {α : Type*} [Fintype α] [DecidableEq α]
    (I W : Finset α) (ell : ℕ) (hW : W ⊆ I)
    (hell : ell ≤ I.card) (hWpos : 0 < W.card)
    (t : ℝ) (ht : 0 ≤ t) :
    Concentration.uniformProbability
        (fun S : BooleanSlices.BooleanSlicePoint I ell ↦
          t ≤ |(((S.1 ∩ W).card : ℕ) : ℝ) -
            (W.card : ℝ) * ell / I.card|) ≤
      2 * Real.exp (-t ^ 2 / (8 * W.card)) := by
  classical
  let : Nonempty (BooleanSlices.BooleanSlicePoint I ell) :=
    BooleanSlices.booleanSlicePoint_nonempty hell
  let hR : W.card ≤ I.card := Finset.card_le_card hW
  obtain ⟨e, he⟩ := exists_aligned_finEquiv I W hW
  let hcount : ell + 0 ≤ I.card := by simpa using hell
  let : Nonempty (BooleanSlices.SignedSlicePoint I ell 0) :=
    BooleanSlices.signedSlicePoint_nonempty hcount
  let Q : BooleanSlices.BooleanSlicePoint I ell → Prop := fun S ↦
    t ≤ |(((S.1 ∩ W).card : ℕ) : ℝ) -
      (W.card : ℝ) * ell / I.card|
  let D : Equiv.Perm (Fin I.card) →
      BooleanSlices.BooleanSlicePoint I ell := fun σ ↦
    BooleanSlices.signedSliceZeroEquiv I ell
      (BooleanSlices.signedSliceDecode I ell 0 hcount e σ)
  have hzero := uniformProbability_comp_equiv
    (BooleanSlices.signedSliceZeroEquiv I ell) Q
  have hdecode := BooleanSlices.uniformProbability_signedSliceDecode
    I ell 0 hcount e
      (fun S ↦ Q (BooleanSlices.signedSliceZeroEquiv I ell S))
  let invE : Equiv.Perm (Equiv.Perm (Fin I.card)) :=
    Equiv.inv (Equiv.Perm (Fin I.card))
  have hinvRaw := uniformProbability_comp_equiv invE
    (fun σ : Equiv.Perm (Fin I.card) ↦ Q (D σ))
  have hinv :
      Concentration.uniformProbability
          (fun σ : Equiv.Perm (Fin I.card) ↦ Q (D σ.symm)) =
        Concentration.uniformProbability (fun σ ↦ Q (D σ)) := by
    simpa only [invE, Equiv.inv_apply, Equiv.Perm.inv_def] using hinvRaw
  have hevent :
      (fun σ : Equiv.Perm (Fin I.card) ↦ Q (D σ.symm)) =
        (fun σ ↦ t ≤ |permutationInitialCount I.card W.card ell
          hR hell σ - (W.card : ℝ) * ell / I.card|) := by
    funext σ
    apply propext
    have hcard : ((((D σ.symm).1 ∩ W).card : ℕ) : ℝ) =
        permutationInitialCount I.card W.card ell hR hell σ := by
      change (((BooleanSlices.signedSlicePositiveSupport I ell 0
        hcount e σ.symm ∩ W).card : ℕ) : ℝ) = _
      exact card_signedSlicePositiveSupport_inter_aligned
        I W W.card ell hR hell e he σ
    dsimp only [Q]
    rw [hcard]
  change Concentration.uniformProbability Q ≤
    2 * Real.exp (-t ^ 2 / (8 * W.card))
  calc
    Concentration.uniformProbability Q =
        Concentration.uniformProbability
          (fun S ↦ Q (BooleanSlices.signedSliceZeroEquiv I ell S)) :=
      hzero.symm
    _ = Concentration.uniformProbability (fun σ ↦ Q (D σ)) := by
      simpa only [D] using hdecode.symm
    _ = Concentration.uniformProbability
        (fun σ : Equiv.Perm (Fin I.card) ↦ Q (D σ.symm)) := hinv.symm
    _ = Concentration.uniformProbability
        (fun σ ↦ t ≤ |permutationInitialCount I.card W.card ell
          hR hell σ - (W.card : ℝ) * ell / I.card|) := by rw [hevent]
    _ ≤ 2 * Real.exp (-t ^ 2 / (8 * W.card)) :=
      permutationInitialCount_two_sided_probability_of_pos
        I.card W.card ell hR hell hWpos t ht

/-! ### Exact symmetric two-block fibers -/

/-- Split an `ell`-subset of two disjoint blocks according to its exact
intersection size `j` with the first block. -/
noncomputable def booleanSliceTwoBlockFiberEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (ell j : ℕ) (hj : j ≤ ell) :
    {U : BooleanSlices.BooleanSlicePoint (A ∪ B) ell //
        (U.1 ∩ A).card = j} ≃
      BooleanSlices.BooleanSlicePoint A j ×
        BooleanSlices.BooleanSlicePoint B (ell - j) := by
  classical
  let splitA (U : BooleanSlices.BooleanSlicePoint (A ∪ B) ell) := U.1 ∩ A
  let splitB (U : BooleanSlices.BooleanSlicePoint (A ∪ B) ell) := U.1 ∩ B
  have hsplit (U : BooleanSlices.BooleanSlicePoint (A ∪ B) ell) :
      U.1 = splitA U ∪ splitB U := by
    ext x
    constructor
    · intro hx
      have hxAB := (BooleanSlices.mem_booleanSlice.mp U.2).1 hx
      rcases Finset.mem_union.mp hxAB with hxA | hxB
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxB⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxA | hxB
      · exact (Finset.mem_inter.mp hxA).1
      · exact (Finset.mem_inter.mp hxB).1
  have hsplitDisjoint (U : BooleanSlices.BooleanSlicePoint (A ∪ B) ell) :
      Disjoint (splitA U) (splitB U) := by
    exact hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hInterA (P : BooleanSlices.BooleanSlicePoint A j)
      (Q : BooleanSlices.BooleanSlicePoint B (ell - j)) :
      (P.1 ∪ Q.1) ∩ A = P.1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxPQ, hxA⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp hxPQ with hxP | hxQ
      · exact hxP
      · exact (Finset.disjoint_left.mp hAB hxA
          ((BooleanSlices.mem_booleanSlice.mp Q.2).1 hxQ)).elim
    · intro hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hx,
        (BooleanSlices.mem_booleanSlice.mp P.2).1 hx⟩
  have hInterB (P : BooleanSlices.BooleanSlicePoint A j)
      (Q : BooleanSlices.BooleanSlicePoint B (ell - j)) :
      (P.1 ∪ Q.1) ∩ B = Q.1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxPQ, hxB⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp hxPQ with hxP | hxQ
      · exact (Finset.disjoint_left.mp hAB
          ((BooleanSlices.mem_booleanSlice.mp P.2).1 hxP) hxB).elim
      · exact hxQ
    · intro hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hx,
        (BooleanSlices.mem_booleanSlice.mp Q.2).1 hx⟩
  refine
    { toFun := fun U ↦
        (⟨splitA U.1, BooleanSlices.mem_booleanSlice.mpr
          ⟨Finset.inter_subset_right, U.2⟩⟩,
        ⟨splitB U.1, BooleanSlices.mem_booleanSlice.mpr
          ⟨Finset.inter_subset_right, ?_⟩⟩)
      invFun := fun PQ ↦ ⟨
        ⟨PQ.1.1 ∪ PQ.2.1, BooleanSlices.mem_booleanSlice.mpr ⟨
          Finset.union_subset_union
            (BooleanSlices.mem_booleanSlice.mp PQ.1.2).1
            (BooleanSlices.mem_booleanSlice.mp PQ.2.2).1,
          ?_⟩⟩,
        ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hcard := congrArg Finset.card (hsplit U.1)
    rw [Finset.card_union_of_disjoint (hsplitDisjoint U.1)] at hcard
    have hUcard := (BooleanSlices.mem_booleanSlice.mp U.1.2).2
    have hAcard := U.2
    dsimp only [splitA, splitB] at hcard hAcard ⊢
    omega
  · rw [Finset.card_union_of_disjoint]
    · rw [(BooleanSlices.mem_booleanSlice.mp PQ.1.2).2,
        (BooleanSlices.mem_booleanSlice.mp PQ.2.2).2]
      omega
    · exact hAB.mono
        (BooleanSlices.mem_booleanSlice.mp PQ.1.2).1
        (BooleanSlices.mem_booleanSlice.mp PQ.2.2).1
  · simpa only [hInterA]
      using (BooleanSlices.mem_booleanSlice.mp PQ.1.2).2
  · intro U
    apply Subtype.ext
    apply Subtype.ext
    exact (hsplit U.1).symm
  · rintro ⟨P, Q⟩
    apply Prod.ext <;> apply Subtype.ext
    · exact hInterA P Q
    · exact hInterB P Q

lemma card_booleanSliceTwoBlockFiber
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (ell j : ℕ) (hj : j ≤ ell) :
    Fintype.card {U : BooleanSlices.BooleanSlicePoint (A ∪ B) ell //
        (U.1 ∩ A).card = j} =
      Nat.choose A.card j * Nat.choose B.card (ell - j) := by
  rw [Fintype.card_congr
    (booleanSliceTwoBlockFiberEquiv A B hAB ell j hj),
    Fintype.card_prod, BooleanSlices.card_booleanSlicePoint,
    BooleanSlices.card_booleanSlicePoint]

/-- Exact hypergeometric mass identity for a statistic depending only on
the number chosen from the first of two equal disjoint blocks. -/
lemma card_booleanSliceTwoBlock_filter
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (m ell : ℕ)
    (hA : A.card = m) (hB : B.card = m) (P : ℕ → Prop)
    [DecidablePred P] :
    ((Finset.univ.filter fun U :
        BooleanSlices.BooleanSlicePoint (A ∪ B) ell ↦
          P ((U.1 ∩ A).card)).card) =
      ∑ j ∈ (Finset.range (ell + 1)).filter P,
        hypergeomWeight m ell j := by
  classical
  let Ω := BooleanSlices.BooleanSlicePoint (A ∪ B) ell
  let event : Finset Ω := Finset.univ.filter fun U ↦ P ((U.1 ∩ A).card)
  let g : Ω → ℕ := fun U ↦ (U.1 ∩ A).card
  have hmaps : Set.MapsTo g (event : Set Ω)
      (Finset.range (ell + 1) : Set ℕ) := by
    intro U _hU
    apply Finset.mem_range.mpr
    have hinter : (U.1 ∩ A).card ≤ U.1.card :=
      Finset.card_le_card Finset.inter_subset_left
    have hUcard := (BooleanSlices.mem_booleanSlice.mp U.2).2
    dsimp only [g]
    omega
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := event) (t := Finset.range (ell + 1)) (f := g) hmaps
  change event.card = _
  rw [hcard, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hjrange
  by_cases hP : P j
  · simp only [hP, if_true]
    have hj : j ≤ ell := by
      rw [Finset.mem_range] at hjrange
      omega
    have hfiber : event.filter (fun U ↦ g U = j) =
        Finset.univ.filter fun U : Ω ↦ (U.1 ∩ A).card = j := by
      ext U
      simp only [event, g, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h ↦ h.2
      · intro h
        exact ⟨by simpa only [h] using hP, h⟩
    rw [hfiber, ← Fintype.card_subtype]
    rw [card_booleanSliceTwoBlockFiber A B hAB ell j hj,
      hA, hB]
    rfl
  · simp only [hP, if_false]
    have hfiber : event.filter (fun U ↦ g U = j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro U hU
      obtain ⟨hUevent, hUg⟩ := Finset.mem_filter.mp hU
      have hUP := (Finset.mem_filter.mp hUevent).2
      exact hP (by simpa only [g, hUg] using hUP)
    rw [hfiber]
    rfl

/-- Lemma 8.4 transported to a uniform slice on two concrete equal blocks. -/
theorem booleanSliceTwoBlock_residue_probability
    {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) (m ell : ℕ)
    (hA : A.card = m) (hB : B.card = m)
    (eta tau x delta : ℝ)
    (heta : 0 < eta) (hm : 1 ≤ m)
    (hellower : eta * (2 * m : ℕ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * (2 * m : ℕ))
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint (A ∪ B) ell ↦
          RLCD.distToInt (tau * ((U.1 ∩ A).card : ℝ) + x) ≤ delta) ≤
      4096 / eta *
        ((|tau| + delta) *
          (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|) := by
  classical
  have hUnion : (A ∪ B).card = 2 * m := by
    rw [Finset.card_union_of_disjoint hAB, hA, hB]
    omega
  have hell : ell ≤ 2 * m := by
    have hη : 1 - eta ≤ 1 := by linarith
    have hnonneg : (0 : ℝ) ≤ (2 * m : ℕ) := by positivity
    have hreal : (ell : ℝ) ≤ (2 * m : ℕ) :=
      hellupper.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hη hnonneg)
    exact_mod_cast hreal
  let : Nonempty (BooleanSlices.BooleanSlicePoint (A ∪ B) ell) :=
    BooleanSlices.booleanSlicePoint_nonempty (by simpa only [hUnion] using hell)
  have hcount := card_booleanSliceTwoBlock_filter A B hAB m ell hA hB
    (fun j ↦ RLCD.distToInt (tau * (j : ℝ) + x) ≤ delta)
  have htail := ksssLemma84 eta m ell tau x delta heta hm
    hellower hellupper htau hdelta hdeltaUpper
  rw [Concentration.uniformProbability,
    BooleanSlices.card_booleanSlicePoint, hUnion]
  rw [hcount]
  simpa only [Nat.cast_sum] using htail

/-! ### Conditioning on the complement of a block -/

/-- A fixed outside fiber of a global Boolean slice is exactly a Boolean
slice on the remaining block. -/
noncomputable def booleanSliceOutsideFiberEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (I S T : Finset α) (ell : ℕ)
    (hS : S ⊆ I) (hT : T ⊆ I \ S) (hTell : T.card ≤ ell) :
    {U : BooleanSlices.BooleanSlicePoint I ell // U.1 \ S = T} ≃
      BooleanSlices.BooleanSlicePoint S (ell - T.card) := by
  classical
  have hTS : Disjoint T S := by
    exact Finset.disjoint_left.mpr fun x hxT hxSx ↦
      (Finset.mem_sdiff.mp (hT hxT)).2 hxSx
  have hsplit (U : BooleanSlices.BooleanSlicePoint I ell) :
      U.1 = (U.1 \ S) ∪ (U.1 ∩ S) := by
    ext x
    by_cases hxS : x ∈ S <;> simp [hxS]
  refine
    { toFun := fun U ↦ ⟨U.1.1 ∩ S,
        BooleanSlices.mem_booleanSlice.mpr ⟨Finset.inter_subset_right, ?_⟩⟩
      invFun := fun V ↦ ⟨
        ⟨T ∪ V.1, BooleanSlices.mem_booleanSlice.mpr ⟨
          Finset.union_subset
            (hT.trans Finset.sdiff_subset)
            ((BooleanSlices.mem_booleanSlice.mp V.2).1.trans hS),
          ?_⟩⟩,
        ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hcard := congrArg Finset.card (hsplit U.1)
    rw [Finset.card_union_of_disjoint
      (Finset.disjoint_sdiff_inter U.1.1 S)] at hcard
    have hUcard := (BooleanSlices.mem_booleanSlice.mp U.1.2).2
    rw [U.2] at hcard
    omega
  · rw [Finset.card_union_of_disjoint (hTS.mono_right
      (BooleanSlices.mem_booleanSlice.mp V.2).1)]
    rw [(BooleanSlices.mem_booleanSlice.mp V.2).2]
    omega
  · ext x
    constructor
    · intro hx
      have hx' := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp hx'.1 with hxT | hxV
      · exact hxT
      · exact (hx'.2 ((BooleanSlices.mem_booleanSlice.mp V.2).1 hxV)).elim
    · intro hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _ hx, Finset.disjoint_left.mp hTS hx⟩
  · intro U
    apply Subtype.ext
    apply Subtype.ext
    change T ∪ (U.1.1 ∩ S) = U.1.1
    calc
      T ∪ (U.1.1 ∩ S) = (U.1.1 \ S) ∪ (U.1.1 ∩ S) :=
        congrArg (fun Z : Finset α ↦ Z ∪ (U.1.1 ∩ S)) U.2.symm
      _ = U.1.1 := (hsplit U.1).symm
  · intro V
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      obtain ⟨hxTV, hxSx⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp hxTV with hxT | hxV
      · exact (Finset.disjoint_left.mp hTS hxT hxSx).elim
      · exact hxV
    · intro hxV
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hxV,
        (BooleanSlices.mem_booleanSlice.mp V.2).1 hxV⟩

/-- Conditional scalar step used in Lemma 8.3: after fixing every choice
outside two equal blocks, the remaining statistic has the symmetric
hypergeometric law controlled by Lemma 8.4. -/
theorem booleanSliceOutsideFiber_residue_probability
    {α : Type*} [Fintype α] [DecidableEq α]
    (I A B T : Finset α) (m ell : ℕ)
    (hAB : Disjoint A B) (hA : A.card = m) (hB : B.card = m)
    (hS : A ∪ B ⊆ I) (hT : T ⊆ I \ (A ∪ B))
    (hTell : T.card ≤ ell)
    (eta tau x delta : ℝ)
    (heta : 0 < eta) (hm : 1 ≤ m)
    (hellower : eta * (2 * m : ℕ) ≤ ((ell - T.card : ℕ) : ℝ))
    (hellupper : ((ell - T.card : ℕ) : ℝ) ≤
      (1 - eta) * (2 * m : ℕ))
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) :
    Concentration.uniformProbability
        (fun U : {U : BooleanSlices.BooleanSlicePoint I ell //
            U.1 \ (A ∪ B) = T} ↦
          RLCD.distToInt
            (tau * ((U.1.1 ∩ A).card : ℝ) + x) ≤ delta) ≤
      4096 / eta *
        ((|tau| + delta) *
          (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|) := by
  classical
  let E := booleanSliceOutsideFiberEquiv I (A ∪ B) T ell hS hT hTell
  have hell : ell - T.card ≤ 2 * m := by
    have hη : 1 - eta ≤ 1 := by linarith
    have hnonneg : (0 : ℝ) ≤ (2 * m : ℕ) := by positivity
    have hreal : (((ell - T.card : ℕ) : ℝ)) ≤ (2 * m : ℕ) :=
      hellupper.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hη hnonneg)
    exact_mod_cast hreal
  have hUnion : (A ∪ B).card = 2 * m := by
    rw [Finset.card_union_of_disjoint hAB, hA, hB]
    omega
  let : Nonempty
      (BooleanSlices.BooleanSlicePoint (A ∪ B) (ell - T.card)) :=
    BooleanSlices.booleanSlicePoint_nonempty (by simpa only [hUnion] using hell)
  let : Nonempty {U : BooleanSlices.BooleanSlicePoint I ell //
      U.1 \ (A ∪ B) = T} := ⟨E.symm (Classical.choice inferInstance)⟩
  let Q : BooleanSlices.BooleanSlicePoint (A ∪ B) (ell - T.card) → Prop :=
    fun V ↦ RLCD.distToInt (tau * ((V.1 ∩ A).card : ℝ) + x) ≤ delta
  have htransport :
      (fun U : {U : BooleanSlices.BooleanSlicePoint I ell //
          U.1 \ (A ∪ B) = T} ↦
        RLCD.distToInt (tau * ((U.1.1 ∩ A).card : ℝ) + x) ≤ delta) =
        (fun U ↦ Q (E U)) := by
    funext U
    apply propext
    have hinter : (U.1.1 ∩ (A ∪ B)) ∩ A = U.1.1 ∩ A := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    have hEU : (E U).1 = U.1.1 ∩ (A ∪ B) := rfl
    have hcard : ((E U).1 ∩ A).card = (U.1.1 ∩ A).card := by
      rw [hEU, hinter]
    dsimp only [Q]
    rw [hcard]
  rw [htransport, uniformProbability_comp_equiv E Q]
  exact booleanSliceTwoBlock_residue_probability A B hAB m
    (ell - T.card) hA hB eta tau x delta heta hm
    hellower hellupper htau hdelta hdeltaUpper

/-! ### The graph blocks supplied by Lemma 8.2 -/

noncomputable def lemma83BlockSize (n : ℕ) (beta : ℝ) : ℕ :=
  Nat.ceil ((n : ℝ) ^ (1 - beta))

@[simp] lemma mem_tuplePriorSet_iff
    {V : Type*} [Fintype V] {q : ℕ}
    (G : SimpleGraph V) (v : Fin q → V) (i : Fin q) (x : V) :
    x ∈ tuplePriorSet G v i ↔ ∀ j : Fin q, j < i → ¬G.Adj (v j) x := by
  classical
  simp only [tuplePriorSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Choose the two equal fresh blocks used for one coordinate of Lemma 8.3. -/
theorem Lemma82Witness.exists_lemma83Blocks
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i : Fin q) :
    ∃ A B : Finset (Fin n),
      A ⊆ tupleNewNeighborCell G (w.tuple a) i ∩ w.J ∧
      B ⊆ tupleRemainingCell G (w.tuple a) i ∩ w.J ∧
      A.card = lemma83BlockSize n beta ∧
      B.card = lemma83BlockSize n beta ∧
      Disjoint A B := by
  classical
  let m := lemma83BlockSize n beta
  have hmA : m ≤
      (tupleNewNeighborCell G (w.tuple a) i ∩ w.J).card := by
    apply Nat.ceil_le.mpr
    exact (w.newCell_large a i).le
  have hmB : m ≤
      (tupleRemainingCell G (w.tuple a) i ∩ w.J).card := by
    apply Nat.ceil_le.mpr
    exact (w.remainingCell_large a i).le
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq hmA
  obtain ⟨B, hB, hBcard⟩ := Finset.exists_subset_card_eq hmB
  refine ⟨A, B, hA, hB, hAcard, hBcard, ?_⟩
  rw [Finset.disjoint_left]
  intro x hxA hxB
  have hxNew : x ∈ tupleNewNeighborCell G (w.tuple a) i :=
    (Finset.mem_inter.mp (hA hxA)).1
  have hxRemain : x ∈ tupleRemainingCell G (w.tuple a) i :=
    (Finset.mem_inter.mp (hB hxB)).1
  exact (mem_tupleRemainingCell.mp hxRemain).2 hxNew

lemma degreeInto_inter_eq_outside_of_nonadj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (U J S : Finset V)
    (hnonadj : ∀ z ∈ S, ¬G.Adj v z) :
    AKSGraph.degreeInto G v (U ∩ J) =
      AKSGraph.degreeInto G v ((U \ S) ∩ J) := by
  unfold AKSGraph.degreeInto
  congr 1
  ext z
  simp only [Finset.mem_inter, Finset.mem_sdiff,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hzAdj, hzU, hzJ⟩
    exact ⟨hzAdj, ⟨hzU, fun hzS ↦ hnonadj z hzS hzAdj⟩, hzJ⟩
  · rintro ⟨hzAdj, ⟨hzU, _hzS⟩, hzJ⟩
    exact ⟨hzAdj, hzU, hzJ⟩

lemma degreeInto_inter_eq_outside_add_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (U J A B : Finset V)
    (hAB : Disjoint A B) (hAJ : A ⊆ J) (hBJ : B ⊆ J)
    (hadjA : ∀ z ∈ A, G.Adj v z)
    (hnonadjB : ∀ z ∈ B, ¬G.Adj v z) :
    AKSGraph.degreeInto G v (U ∩ J) =
      AKSGraph.degreeInto G v ((U \ (A ∪ B)) ∩ J) +
        (U ∩ A).card := by
  classical
  have hset : G.neighborFinset v ∩ (U ∩ J) =
      (G.neighborFinset v ∩ ((U \ (A ∪ B)) ∩ J)) ∪ (U ∩ A) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hzAdj, hzU, hzJ⟩
      by_cases hzA : z ∈ A
      · exact Or.inr ⟨hzU, hzA⟩
      · have hzB : z ∉ B := by
          intro hzB
          exact hnonadjB z hzB hzAdj
        exact Or.inl ⟨hzAdj, ⟨hzU, by simpa [hzA, hzB]⟩, hzJ⟩
    · rintro (⟨hzAdj, ⟨hzU, _hzUAB⟩, hzJ⟩ | ⟨hzU, hzAin⟩)
      · exact ⟨hzAdj, hzU, hzJ⟩
      · exact ⟨hadjA z hzAin, hzU, hAJ hzAin⟩
  have hdisj :
      Disjoint (G.neighborFinset v ∩ ((U \ (A ∪ B)) ∩ J)) (U ∩ A) := by
    rw [Finset.disjoint_left]
    intro z hzO hzA
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hzO hzA
    exact hzO.2.1.2 (Finset.mem_union_left _ hzA.2)
  unfold AKSGraph.degreeInto
  rw [hset, Finset.card_union_of_disjoint hdisj]

lemma lemma83Blocks_subset_J
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i : Fin q) (A B : Finset (Fin n))
    (hA : A ⊆ tupleNewNeighborCell G (w.tuple a) i ∩ w.J)
    (hB : B ⊆ tupleRemainingCell G (w.tuple a) i ∩ w.J) :
    A ∪ B ⊆ w.J := by
  intro z hz
  rcases Finset.mem_union.mp hz with hzA | hzB
  · exact (Finset.mem_inter.mp (hA hzA)).2
  · exact (Finset.mem_inter.mp (hB hzB)).2

lemma lemma83Blocks_prior_nonadj
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i j : Fin q) (A B : Finset (Fin n))
    (hA : A ⊆ tupleNewNeighborCell G (w.tuple a) i ∩ w.J)
    (hB : B ⊆ tupleRemainingCell G (w.tuple a) i ∩ w.J)
    (hji : j < i) {z : Fin n} (hz : z ∈ A ∪ B) :
    ¬G.Adj (w.tuple a j) z := by
  have hzPrior : z ∈ tuplePriorSet G (w.tuple a) i := by
    rcases Finset.mem_union.mp hz with hzA | hzB
    · exact (mem_neighborsIn.mp (Finset.mem_inter.mp (hA hzA)).1).1
    · exact (mem_tupleRemainingCell.mp (Finset.mem_inter.mp (hB hzB)).1).1
  exact (mem_tuplePriorSet_iff G (w.tuple a) i z).mp hzPrior j hji

lemma lemma83Blocks_current_adj_left
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i : Fin q) (A : Finset (Fin n))
    (hA : A ⊆ tupleNewNeighborCell G (w.tuple a) i ∩ w.J)
    {z : Fin n} (hz : z ∈ A) :
    G.Adj (w.tuple a i) z := by
  exact (mem_neighborsIn.mp (Finset.mem_inter.mp (hA hz)).1).2

lemma lemma83Blocks_current_nonadj_right
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i : Fin q) (B : Finset (Fin n))
    (hB : B ⊆ tupleRemainingCell G (w.tuple a) i ∩ w.J)
    {z : Fin n} (hz : z ∈ B) :
    ¬G.Adj (w.tuple a i) z := by
  have hzRemain := (Finset.mem_inter.mp (hB hz)).1
  have hzPrior := (mem_tupleRemainingCell.mp hzRemain).1
  have hzNotNew := (mem_tupleRemainingCell.mp hzRemain).2
  intro hzAdj
  exact hzNotNew (mem_neighborsIn.mpr ⟨hzPrior, hzAdj⟩)

lemma lemma83Blocks_prior_degree_eq_outside
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i j : Fin q) (A B U : Finset (Fin n))
    (hA : A ⊆ tupleNewNeighborCell G (w.tuple a) i ∩ w.J)
    (hB : B ⊆ tupleRemainingCell G (w.tuple a) i ∩ w.J)
    (hji : j < i) :
    AKSGraph.degreeInto G (w.tuple a j) (U ∩ w.J) =
      AKSGraph.degreeInto G (w.tuple a j) ((U \ (A ∪ B)) ∩ w.J) := by
  apply degreeInto_inter_eq_outside_of_nonadj
  intro z hz
  exact lemma83Blocks_prior_nonadj w a i j A B hA hB hji hz

lemma lemma83Blocks_current_degree_eq_outside_add_card
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i : Fin q) (A B U : Finset (Fin n))
    (hAB : Disjoint A B)
    (hA : A ⊆ tupleNewNeighborCell G (w.tuple a) i ∩ w.J)
    (hB : B ⊆ tupleRemainingCell G (w.tuple a) i ∩ w.J) :
    AKSGraph.degreeInto G (w.tuple a i) (U ∩ w.J) =
      AKSGraph.degreeInto G (w.tuple a i) ((U \ (A ∪ B)) ∩ w.J) +
        (U ∩ A).card := by
  apply degreeInto_inter_eq_outside_add_card G (w.tuple a i) U w.J A B
  · exact hAB
  · intro z hz
    exact (Finset.mem_inter.mp (hA hz)).2
  · intro z hz
    exact (Finset.mem_inter.mp (hB hz)).2
  · intro z hz
    exact lemma83Blocks_current_adj_left w a i A hA hz
  · intro z hz
    exact lemma83Blocks_current_nonadj_right w a i B hB hz

/-- After the choices outside a fresh pair of blocks are fixed, the degree
difference between the current tuple vertex and any earlier tuple vertex is
exactly a shifted symmetric hypergeometric count. -/
theorem lemma83Blocks_outsideFiber_residue_probability
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i j : Fin q) (hji : j < i)
    (I A B T : Finset (Fin n)) (m ell : ℕ)
    (hAB : Disjoint A B) (hAcard : A.card = m) (hBcard : B.card = m)
    (hA : A ⊆ tupleNewNeighborCell G (w.tuple a) i ∩ w.J)
    (hB : B ⊆ tupleRemainingCell G (w.tuple a) i ∩ w.J)
    (hS : A ∪ B ⊆ I) (hT : T ⊆ I \ (A ∪ B))
    (hTell : T.card ≤ ell)
    (eta tau x delta : ℝ)
    (heta : 0 < eta) (hm : 1 ≤ m)
    (hellower : eta * (2 * m : ℕ) ≤ ((ell - T.card : ℕ) : ℝ))
    (hellupper : ((ell - T.card : ℕ) : ℝ) ≤
      (1 - eta) * (2 * m : ℕ))
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) :
    Concentration.uniformProbability
        (fun U : {U : BooleanSlices.BooleanSlicePoint I ell //
            U.1 \ (A ∪ B) = T} ↦
          RLCD.distToInt
            (tau * (AKSGraph.degreeInto G (w.tuple a i)
                (U.1.1 ∩ w.J) : ℝ) -
              tau * (AKSGraph.degreeInto G (w.tuple a j)
                (U.1.1 ∩ w.J) : ℝ) + x) ≤ delta) ≤
      4096 / eta *
        ((|tau| + delta) *
          (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|) := by
  classical
  let xT : ℝ :=
    tau * (AKSGraph.degreeInto G (w.tuple a i) (T ∩ w.J) : ℝ) -
      tau * (AKSGraph.degreeInto G (w.tuple a j) (T ∩ w.J) : ℝ) + x
  have htransport :
      (fun U : {U : BooleanSlices.BooleanSlicePoint I ell //
          U.1 \ (A ∪ B) = T} ↦
        RLCD.distToInt
          (tau * (AKSGraph.degreeInto G (w.tuple a i)
              (U.1.1 ∩ w.J) : ℝ) -
            tau * (AKSGraph.degreeInto G (w.tuple a j)
              (U.1.1 ∩ w.J) : ℝ) + x) ≤ delta) =
      (fun U ↦ RLCD.distToInt
        (tau * ((U.1.1 ∩ A).card : ℝ) + xT) ≤ delta) := by
    funext U
    have hcur := lemma83Blocks_current_degree_eq_outside_add_card
      w a i A B U.1.1 hAB hA hB
    have hprev := lemma83Blocks_prior_degree_eq_outside
      w a i j A B U.1.1 hA hB hji
    rw [U.2] at hcur hprev
    dsimp only [xT]
    rw [hcur, hprev]
    push_cast
    ring_nf
  rw [htransport]
  exact booleanSliceOutsideFiber_residue_probability I A B T m ell
    hAB hAcard hBcard hS hT hTell eta tau xT delta heta hm
    hellower hellupper htau hdelta hdeltaUpper

/-! ### Summing conditional bounds over outside fibers -/

/-- A conditional bound on every good fiber gives a global one-step bound,
with the bad fibers paid for additively.  This is the finite counting form of
the conditioning step in the proof of Lemma 8.3. -/
lemma card_and_le_mul_add_bad_of_fibers
    {Ω : Type u} {Θ : Type*} [Fintype Ω] [Fintype Θ]
    [DecidableEq Θ]
    (f : Ω → Θ) (P Q : Ω → Prop) (Good : Θ → Prop) (B : ℝ)
    [DecidablePred P] [DecidablePred Q] [DecidablePred Good]
    (hB : 0 ≤ B)
    (hfiber : ∀ t, Good t →
      (((Finset.univ : Finset Ω).filter fun ω ↦
          f ω = t ∧ P ω ∧ Q ω).card : ℝ) ≤
        B * (((Finset.univ : Finset Ω).filter fun ω ↦
          f ω = t ∧ P ω).card : ℝ)) :
    (((Finset.univ : Finset Ω).filter fun ω ↦ P ω ∧ Q ω).card : ℝ) ≤
      B * (((Finset.univ : Finset Ω).filter P).card : ℝ) +
        (((Finset.univ : Finset Ω).filter fun ω ↦ ¬Good (f ω)).card : ℝ) := by
  classical
  let E : Finset Ω := Finset.univ.filter fun ω ↦ P ω ∧ Q ω
  let EG : Finset Ω := E.filter fun ω ↦ Good (f ω)
  let EB : Finset Ω := E.filter fun ω ↦ ¬Good (f ω)
  let PE : Finset Ω := Finset.univ.filter P
  let Bad : Finset Ω := Finset.univ.filter fun ω ↦ ¬Good (f ω)
  let GoodT : Finset Θ := Finset.univ.filter Good
  have hsplit : E = EG ∪ EB := by
    ext ω
    simp only [E, EG, EB, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    tauto
  have hdisj : Disjoint EG EB := by
    rw [Finset.disjoint_left]
    intro ω hωG hωB
    exact (Finset.mem_filter.mp hωB).2 (Finset.mem_filter.mp hωG).2
  have hEB : EB ⊆ Bad := by
    intro ω hω
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2⟩
  have hEGMaps : Set.MapsTo f (EG : Set Ω) (GoodT : Set Θ) := by
    intro ω hω
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2⟩
  have hEGcard := Finset.card_eq_sum_card_fiberwise
    (s := EG) (t := GoodT) (f := f) hEGMaps
  have hPEMaps : Set.MapsTo f (PE : Set Ω)
      (↑(Finset.univ : Finset Θ) : Set Θ) := by
    intro ω _hω
    exact Finset.mem_univ _
  have hPEcard := Finset.card_eq_sum_card_fiberwise
    (s := PE) (t := (Finset.univ : Finset Θ)) (f := f) hPEMaps
  have hgoodFiber (t : Θ) (ht : t ∈ GoodT) :
      (((EG.filter fun ω ↦ f ω = t).card : ℕ) : ℝ) ≤
        B * (((PE.filter fun ω ↦ f ω = t).card : ℕ) : ℝ) := by
    have htGood : Good t := (Finset.mem_filter.mp ht).2
    have hEGfiber : EG.filter (fun ω ↦ f ω = t) =
        (Finset.univ : Finset Ω).filter fun ω ↦
          f ω = t ∧ P ω ∧ Q ω := by
      ext ω
      simp only [EG, E, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨⟨hP, hQ⟩, _hGood⟩, hft⟩
        exact ⟨hft, hP, hQ⟩
      · rintro ⟨hft, hP, hQ⟩
        exact ⟨⟨⟨hP, hQ⟩, hft ▸ htGood⟩, hft⟩
    have hPEfiber : PE.filter (fun ω ↦ f ω = t) =
        (Finset.univ : Finset Ω).filter fun ω ↦ f ω = t ∧ P ω := by
      ext ω
      simp only [PE, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [hEGfiber, hPEfiber]
    exact hfiber t htGood
  have hEGbound : (EG.card : ℝ) ≤ B * (PE.card : ℝ) := by
    rw [hEGcard]
    push_cast
    calc
      (∑ t ∈ GoodT, ((EG.filter fun ω ↦ f ω = t).card : ℝ)) ≤
          ∑ t ∈ GoodT, B * ((PE.filter fun ω ↦ f ω = t).card : ℝ) := by
            exact Finset.sum_le_sum fun t ht ↦ hgoodFiber t ht
      _ = B * ∑ t ∈ GoodT,
          ((PE.filter fun ω ↦ f ω = t).card : ℝ) := by
            rw [Finset.mul_sum]
      _ ≤ B * (PE.card : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hB
        rw [hPEcard]
        push_cast
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset Good Finset.univ)
          (fun _ _ _ ↦ Nat.cast_nonneg _)
  have hEBbound : (EB.card : ℝ) ≤ (Bad.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hEB
  change (E.card : ℝ) ≤ B * (PE.card : ℝ) + (Bad.card : ℝ)
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  push_cast
  exact add_le_add hEGbound hEBbound

/-- Convert a uniform-probability estimate on one fiber into the corresponding
cardinality estimate in the ambient finite type. -/
lemma uniformProbability_eq_card_subtype
    {Ω : Type u} [Fintype Ω] (Q : Ω → Prop) :
    Concentration.uniformProbability Q =
      (Nat.card {ω : Ω // Q ω} : ℝ) / Fintype.card Ω := by
  classical
  unfold Concentration.uniformProbability
  congr 1
  norm_cast
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma uniformProbability_eq_filter_div
    {Ω : Type u} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] :
    Concentration.uniformProbability P =
      (((Finset.univ : Finset Ω).filter P).card : ℝ) / Fintype.card Ω := by
  classical
  unfold Concentration.uniformProbability
  congr 1
  norm_cast
  apply congrArg Finset.card
  ext ω
  simp

lemma card_fiber_le_mul_of_uniformProbability
    {Ω : Type u} {Θ : Type*} [Fintype Ω] [Fintype Θ]
    [DecidableEq Θ] (f : Ω → Θ) (Q : Ω → Prop) [DecidablePred Q]
    (t : Θ) (B : ℝ)
    (hprob : Concentration.uniformProbability
      (fun ω : {ω : Ω // f ω = t} ↦ Q ω) ≤ B) :
    (((Finset.univ : Finset Ω).filter fun ω ↦ f ω = t ∧ Q ω).card : ℝ) ≤
      B * (((Finset.univ : Finset Ω).filter fun ω ↦ f ω = t).card : ℝ) := by
  classical
  let E : {ω : {ω : Ω // f ω = t} // Q ω} ≃
      {ω : Ω // f ω = t ∧ Q ω} :=
    { toFun := fun ω ↦ ⟨ω.1.1, ω.1.2, ω.2⟩
      invFun := fun ω ↦ ⟨⟨ω.1, ω.2.1⟩, ω.2.2⟩
      left_inv := fun ω ↦ by rfl
      right_inv := fun ω ↦ by rfl }
  have hnum : Nat.card {ω : {ω : Ω // f ω = t} // Q ω} =
      ((Finset.univ : Finset Ω).filter fun ω ↦ f ω = t ∧ Q ω).card := by
    have hright : Nat.card {ω : Ω // f ω = t ∧ Q ω} =
        ((Finset.univ : Finset Ω).filter fun ω ↦ f ω = t ∧ Q ω).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact (Nat.card_congr E).trans hright
  have hden : Fintype.card {ω : Ω // f ω = t} =
      ((Finset.univ : Finset Ω).filter fun ω ↦ f ω = t).card := by
    rw [Fintype.card_subtype]
  have hnumR := congrArg (fun k : ℕ ↦ (k : ℝ)) hnum
  have hdenR := congrArg (fun k : ℕ ↦ (k : ℝ)) hden
  rw [uniformProbability_eq_card_subtype] at hprob
  have hprob' :
      (((Finset.univ : Finset Ω).filter fun ω ↦ f ω = t ∧ Q ω).card : ℝ) /
          (((Finset.univ : Finset Ω).filter fun ω ↦ f ω = t).card : ℝ) ≤ B := by
    calc
      _ = (Nat.card {ω : {ω : Ω // f ω = t} // Q ω} : ℝ) /
          (Fintype.card {ω : Ω // f ω = t} : ℝ) := by
            rw [hnumR, hdenR]
      _ ≤ B := hprob
  let D := (Finset.univ : Finset Ω).filter fun ω ↦ f ω = t
  let N := (Finset.univ : Finset Ω).filter fun ω ↦ f ω = t ∧ Q ω
  change (N.card : ℝ) ≤ B * (D.card : ℝ)
  change (N.card : ℝ) / (D.card : ℝ) ≤ B at hprob'
  by_cases hD : D.card = 0
  · have hND : N ⊆ D := by
      intro ω hω
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hω).2.1⟩
    have hN : N.card = 0 := Nat.eq_zero_of_le_zero
      (hD ▸ Finset.card_le_card hND)
    rw [hN, hD]
    norm_num
  · have hDpos : (0 : ℝ) < D.card := by
      exact_mod_cast Nat.pos_of_ne_zero hD
    exact (div_le_iff₀ hDpos).mp hprob'

/-- If a prefix predicate is constant on a fiber, a bound for the whole
fiber remains valid after intersecting with that prefix. -/
lemma card_fiber_and_le_of_invariant
    {Ω : Type u} {Θ : Type*} [Fintype Ω] [Fintype Θ]
    [DecidableEq Θ] (f : Ω → Θ) (P Q : Ω → Prop)
    [DecidablePred P] [DecidablePred Q] (t : Θ) (B : ℝ)
    (hPinvariant : ∀ ω₁ ω₂, f ω₁ = f ω₂ → (P ω₁ ↔ P ω₂))
    (hfiber :
      (((Finset.univ : Finset Ω).filter fun ω ↦ f ω = t ∧ Q ω).card : ℝ) ≤
        B * (((Finset.univ : Finset Ω).filter fun ω ↦ f ω = t).card : ℝ)) :
    (((Finset.univ : Finset Ω).filter fun ω ↦
        f ω = t ∧ P ω ∧ Q ω).card : ℝ) ≤
      B * (((Finset.univ : Finset Ω).filter fun ω ↦
        f ω = t ∧ P ω).card : ℝ) := by
  classical
  by_cases hP : ∃ ω, f ω = t ∧ P ω
  · obtain ⟨ω₀, hω₀t, hω₀P⟩ := hP
    have hPt : ∀ ω, f ω = t → P ω := by
      intro ω hωt
      exact (hPinvariant ω₀ ω (hω₀t.trans hωt.symm)).mp hω₀P
    have hleft :
        (Finset.univ : Finset Ω).filter (fun ω ↦ f ω = t ∧ P ω ∧ Q ω) =
          Finset.univ.filter (fun ω ↦ f ω = t ∧ Q ω) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hωt, _hωP, hωQ⟩
        exact ⟨hωt, hωQ⟩
      · rintro ⟨hωt, hωQ⟩
        exact ⟨hωt, hPt ω hωt, hωQ⟩
    have hright :
        (Finset.univ : Finset Ω).filter (fun ω ↦ f ω = t ∧ P ω) =
          Finset.univ.filter (fun ω ↦ f ω = t) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_iff_left_of_imp (hPt ω)
    rw [hleft, hright]
    exact hfiber
  · have hleft :
        (Finset.univ : Finset Ω).filter (fun ω ↦ f ω = t ∧ P ω ∧ Q ω) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hP ⟨ω, (Finset.mem_filter.mp hω).2.1,
        (Finset.mem_filter.mp hω).2.2.1⟩
    have hright :
        (Finset.univ : Finset Ω).filter (fun ω ↦ f ω = t ∧ P ω) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hP ⟨ω, (Finset.mem_filter.mp hω).2.1,
        (Finset.mem_filter.mp hω).2.2⟩
    rw [hleft, hright]
    norm_num

/-! ### Balanced outside fibers -/

lemma booleanSlice_inside_card_eq_sub_outside
    {α : Type*} [Fintype α] [DecidableEq α]
    (I S : Finset α) (ell : ℕ)
    (U : BooleanSlices.BooleanSlicePoint I ell) :
    (U.1 ∩ S).card = ell - (U.1 \ S).card := by
  have hsplit : U.1 = (U.1 \ S) ∪ (U.1 ∩ S) := by
    ext x
    by_cases hx : x ∈ S <;> simp [hx]
  have hcard := congrArg Finset.card hsplit
  rw [Finset.card_union_of_disjoint
    (Finset.disjoint_sdiff_inter U.1 S)] at hcard
  have hUcard := (BooleanSlices.mem_booleanSlice.mp U.2).2
  omega

lemma booleanSlice_outside_subset
    {α : Type*} [Fintype α] [DecidableEq α]
    {I S : Finset α} {ell : ℕ}
    (U : BooleanSlices.BooleanSlicePoint I ell) :
    U.1 \ S ⊆ I \ S := by
  intro x hx
  have hx' := Finset.mem_sdiff.mp hx
  exact Finset.mem_sdiff.mpr
    ⟨(BooleanSlices.mem_booleanSlice.mp U.2).1 hx'.1, hx'.2⟩

/-- The conditional number of selected points in the two fresh blocks stays
inside the buffered density interval needed by Lemma 8.4. -/
def lemma83BalancedResidue (eta : ℝ) (m ell outsideCard : ℕ) : Prop :=
  eta * m ≤ ((ell - outsideCard : ℕ) : ℝ) ∧
    ((ell - outsideCard : ℕ) : ℝ) ≤ (2 - eta) * m

noncomputable def lemma83BadResidueFinset
    {α : Type*} [Fintype α] [DecidableEq α]
    (I S : Finset α) (ell m : ℕ) (eta : ℝ) :
    Finset (BooleanSlices.BooleanSlicePoint I ell) := by
  classical
  exact Finset.univ.filter fun U ↦
    ¬lemma83BalancedResidue eta m ell (U.1 \ S).card

/-- The bad outside fibers have exponentially small total mass under a
uniform fixed-size slice. -/
theorem booleanSlice_bad_residue_probability
    {α : Type*} [Fintype α] [DecidableEq α]
    (I S : Finset α) (ell m : ℕ) (eta : ℝ)
    (hS : S ⊆ I) (hScard : S.card = 2 * m)
    (hell : ell ≤ I.card) (hm : 1 ≤ m) (heta : 0 < eta)
    (hellower : eta * (I.card : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * I.card) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
          ¬lemma83BalancedResidue eta m ell (U.1 \ S).card) ≤
      2 * Real.exp (-(eta * m) ^ 2 / (8 * S.card)) := by
  classical
  let : Nonempty (BooleanSlices.BooleanSlicePoint I ell) :=
    BooleanSlices.booleanSlicePoint_nonempty hell
  have hSpos : 0 < S.card := by omega
  have hIposNat : 0 < I.card := hSpos.trans_le (Finset.card_le_card hS)
  have hIpos : (0 : ℝ) < I.card := by exact_mod_cast hIposNat
  have hSnonneg : (0 : ℝ) ≤ S.card := by positivity
  have hmeanLower : eta * (S.card : ℝ) ≤
      (S.card : ℝ) * ell / I.card := by
    rw [le_div_iff₀ hIpos]
    calc
      eta * (S.card : ℝ) * I.card =
          (S.card : ℝ) * (eta * I.card) := by ring
      _ ≤ (S.card : ℝ) * ell :=
        mul_le_mul_of_nonneg_left hellower hSnonneg
  have hmeanUpper : (S.card : ℝ) * ell / I.card ≤
      (1 - eta) * S.card := by
    rw [div_le_iff₀ hIpos]
    calc
      (S.card : ℝ) * ell ≤
          (S.card : ℝ) * ((1 - eta) * I.card) :=
        mul_le_mul_of_nonneg_left hellupper hSnonneg
      _ = (1 - eta) * S.card * I.card := by ring
  have ht : 0 ≤ eta * (m : ℝ) :=
    mul_nonneg heta.le (by positivity)
  have htail := booleanSlice_intersection_two_sided_probability
    I S ell hS hell hSpos (eta * m) ht
  apply (Concentration.uniformProbability_mono (P := fun U :
      BooleanSlices.BooleanSlicePoint I ell ↦
        ¬lemma83BalancedResidue eta m ell (U.1 \ S).card)
      (Q := fun U ↦
        eta * m ≤
          |(((U.1 ∩ S).card : ℕ) : ℝ) -
            (S.card : ℝ) * ell / I.card|) ?_).trans
  · exact htail
  · intro U hbad
    have hins := booleanSlice_inside_card_eq_sub_outside I S ell U
    have hinsideReal : (((U.1 ∩ S).card : ℕ) : ℝ) =
        ((ell - (U.1 \ S).card : ℕ) : ℝ) := by exact_mod_cast hins
    unfold lemma83BalancedResidue at hbad
    rw [hScard] at hmeanLower hmeanUpper
    rw [hinsideReal]
    rw [hScard]
    by_cases hlow : eta * (m : ℝ) ≤
        ((ell - (U.1 \ S).card : ℕ) : ℝ)
    · have hupper : (2 - eta) * (m : ℝ) <
          ((ell - (U.1 \ S).card : ℕ) : ℝ) := by
        exact lt_of_not_ge fun hupp ↦ hbad ⟨hlow, hupp⟩
      rw [le_abs]
      left
      push_cast at hmeanUpper ⊢
      nlinarith
    · have hlower : ((ell - (U.1 \ S).card : ℕ) : ℝ) <
          eta * (m : ℝ) := lt_of_not_ge hlow
      rw [le_abs]
      right
      push_cast at hmeanLower ⊢
      nlinarith

lemma card_filter_le_mul_card_of_uniformProbability
    {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] (c : ℝ)
    (hprob : Concentration.uniformProbability P ≤ c) :
    (((Finset.univ : Finset Ω).filter P).card : ℝ) ≤
      c * Fintype.card Ω := by
  classical
  have hcard : Nat.card {ω : Ω // P ω} =
      ((Finset.univ : Finset Ω).filter P).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcardR := congrArg (fun k : ℕ ↦ (k : ℝ)) hcard
  rw [uniformProbability_eq_card_subtype] at hprob
  have hprob' :
      (((Finset.univ : Finset Ω).filter P).card : ℝ) /
          Fintype.card Ω ≤ c := by
    calc
      _ = (Nat.card {ω : Ω // P ω} : ℝ) / Fintype.card Ω := by
        rw [hcardR]
      _ ≤ c := hprob
  have hΩ : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ hΩ).mp hprob'

/-- One graph-coordinate extension of the Lemma 8.3 event.  Good outside
fibers pay the Lemma 8.4 factor, and all other fibers are isolated in the
explicit additive term. -/
theorem lemma83Blocks_oneStep_card
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i j : Fin q) (hji : j < i)
    (I A B : Finset (Fin n)) (m ell : ℕ)
    (hAB : Disjoint A B) (hAcard : A.card = m) (hBcard : B.card = m)
    (hA : A ⊆ tupleNewNeighborCell G (w.tuple a) i ∩ w.J)
    (hB : B ⊆ tupleRemainingCell G (w.tuple a) i ∩ w.J)
    (hS : A ∪ B ⊆ I) (hm : 1 ≤ m)
    (eta tau x delta : ℝ) (heta : 0 < eta)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2)
    (P : BooleanSlices.BooleanSlicePoint I ell → Prop) [DecidablePred P]
    (hPinvariant : ∀ U V,
      U.1 \ (A ∪ B) = V.1 \ (A ∪ B) → (P U ↔ P V)) :
    (((Finset.univ : Finset (BooleanSlices.BooleanSlicePoint I ell)).filter
        fun U ↦ P U ∧
          RLCD.distToInt
            (tau * (AKSGraph.degreeInto G (w.tuple a i)
                (U.1 ∩ w.J) : ℝ) -
              tau * (AKSGraph.degreeInto G (w.tuple a j)
                (U.1 ∩ w.J) : ℝ) + x) ≤ delta).card : ℝ) ≤
      (4096 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|)) *
        (((Finset.univ :
            Finset (BooleanSlices.BooleanSlicePoint I ell)).filter P).card : ℝ) +
      (lemma83BadResidueFinset I (A ∪ B) ell m eta).card := by
  classical
  let Ω := BooleanSlices.BooleanSlicePoint I ell
  let f : Ω → Finset (Fin n) := fun U ↦ U.1 \ (A ∪ B)
  let Q : Ω → Prop := fun U ↦
    RLCD.distToInt
      (tau * (AKSGraph.degreeInto G (w.tuple a i) (U.1 ∩ w.J) : ℝ) -
        tau * (AKSGraph.degreeInto G (w.tuple a j) (U.1 ∩ w.J) : ℝ) + x) ≤ delta
  let Good : Finset (Fin n) → Prop := fun T ↦
    lemma83BalancedResidue eta m ell T.card
  let C : ℝ := 4096 / (eta / 2) *
    ((|tau| + delta) *
      (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|)
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hetaHalf : 0 < eta / 2 := by positivity
    have htauAbs : 0 < |tau| := abs_pos.mpr htau
    positivity
  unfold lemma83BadResidueFinset
  change (((Finset.univ : Finset Ω).filter fun U ↦ P U ∧ Q U).card : ℝ) ≤
    C * (((Finset.univ : Finset Ω).filter P).card : ℝ) +
      (((Finset.univ : Finset Ω).filter fun U ↦ ¬Good (f U)).card : ℝ)
  apply card_and_le_mul_add_bad_of_fibers f P Q Good C hC
  intro T hTGood
  apply card_fiber_and_le_of_invariant f P Q T C
  · intro U V hUV
    exact hPinvariant U V hUV
  · by_cases hne : Nonempty {U : Ω // f U = T}
    · let U₀ : {U : Ω // f U = T} := Classical.choice hne
      have hTsub : T ⊆ I \ (A ∪ B) := by
        rw [← U₀.2]
        exact booleanSlice_outside_subset U₀.1
      have hTcard : T.card ≤ ell := by
        have hout : (U₀.1.1 \ (A ∪ B)).card ≤ U₀.1.1.card :=
          Finset.card_le_card Finset.sdiff_subset
        have hUcard := (BooleanSlices.mem_booleanSlice.mp U₀.1.2).2
        rw [← U₀.2]
        change (U₀.1.1 \ (A ∪ B)).card ≤ ell
        exact hout.trans_eq hUcard
      have hGood := hTGood
      dsimp only [Good] at hGood
      unfold lemma83BalancedResidue at hGood
      have hetaHalf : 0 < eta / 2 := by positivity
      have hlower : eta / 2 * (2 * m : ℕ) ≤
          ((ell - T.card : ℕ) : ℝ) := by
        push_cast
        nlinarith [hGood.1]
      have hupper : ((ell - T.card : ℕ) : ℝ) ≤
          (1 - eta / 2) * (2 * m : ℕ) := by
        push_cast
        nlinarith [hGood.2]
      have hprob := lemma83Blocks_outsideFiber_residue_probability
        w a i j hji I A B T m ell hAB hAcard hBcard hA hB hS hTsub
        hTcard (eta / 2) tau x delta hetaHalf hm hlower hupper htau
        hdelta hdeltaUpper
      exact card_fiber_le_mul_of_uniformProbability f Q T C hprob
    · have hbase :
          (Finset.univ : Finset Ω).filter (fun U ↦ f U = T) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro U hU
        exact hne ⟨⟨U, (Finset.mem_filter.mp hU).2⟩⟩
      have hleft :
          (Finset.univ : Finset Ω).filter (fun U ↦ f U = T ∧ Q U) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro U hU
        have hUT := (Finset.mem_filter.mp hU).2.1
        have : U ∈ (Finset.univ : Finset Ω).filter (fun V ↦ f V = T) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUT⟩
        rw [hbase] at this
        simpa using this
      rw [hleft, hbase]
      norm_num

/-- Probability form of the one-coordinate extension.  The first term is the
exact Lemma 8.4 factor, while the second is the exponentially small cost of
unbalanced conditioning fibers. -/
theorem lemma83Blocks_oneStep_probability
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i j : Fin q) (hji : j < i)
    (I A B : Finset (Fin n)) (m ell : ℕ)
    (hAB : Disjoint A B) (hAcard : A.card = m) (hBcard : B.card = m)
    (hA : A ⊆ tupleNewNeighborCell G (w.tuple a) i ∩ w.J)
    (hB : B ⊆ tupleRemainingCell G (w.tuple a) i ∩ w.J)
    (hS : A ∪ B ⊆ I) (hell : ell ≤ I.card) (hm : 1 ≤ m)
    (eta tau x delta : ℝ) (heta : 0 < eta)
    (hellower : eta * (I.card : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * I.card)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2)
    (P : BooleanSlices.BooleanSlicePoint I ell → Prop) [DecidablePred P]
    (hPinvariant : ∀ U V,
      U.1 \ (A ∪ B) = V.1 \ (A ∪ B) → (P U ↔ P V)) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint I ell ↦ P U ∧
          RLCD.distToInt
            (tau * (AKSGraph.degreeInto G (w.tuple a i)
                (U.1 ∩ w.J) : ℝ) -
              tau * (AKSGraph.degreeInto G (w.tuple a j)
                (U.1 ∩ w.J) : ℝ) + x) ≤ delta) ≤
      (4096 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|)) *
        Concentration.uniformProbability P +
      2 * Real.exp (-(eta * m) ^ 2 / (8 * (A ∪ B).card)) := by
  classical
  let Q : BooleanSlices.BooleanSlicePoint I ell → Prop := fun U ↦
    RLCD.distToInt
      (tau * (AKSGraph.degreeInto G (w.tuple a i) (U.1 ∩ w.J) : ℝ) -
        tau * (AKSGraph.degreeInto G (w.tuple a j) (U.1 ∩ w.J) : ℝ) + x) ≤ delta
  let C : ℝ := 4096 / (eta / 2) *
    ((|tau| + delta) *
      (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|)
  let eps : ℝ := 2 * Real.exp (-(eta * m) ^ 2 / (8 * (A ∪ B).card))
  let : Nonempty (BooleanSlices.BooleanSlicePoint I ell) :=
    BooleanSlices.booleanSlicePoint_nonempty hell
  have hScard : (A ∪ B).card = 2 * m := by
    rw [Finset.card_union_of_disjoint hAB, hAcard, hBcard]
    omega
  have hstep := lemma83Blocks_oneStep_card w a i j hji I A B m ell
    hAB hAcard hBcard hA hB hS hm eta tau x delta heta htau hdelta
    hdeltaUpper P hPinvariant
  have hbadProb := booleanSlice_bad_residue_probability
    I (A ∪ B) ell m eta hS hScard hell hm heta hellower hellupper
  have hbadCard := card_filter_le_mul_card_of_uniformProbability
    (Ω := BooleanSlices.BooleanSlicePoint I ell)
    (fun U : BooleanSlices.BooleanSlicePoint I ell ↦
      ¬lemma83BalancedResidue eta m ell (U.1 \ (A ∪ B)).card)
    eps hbadProb
  unfold lemma83BadResidueFinset at hstep
  change (((Finset.univ : Finset (BooleanSlices.BooleanSlicePoint I ell)).filter
      fun U ↦ P U ∧ Q U).card : ℝ) ≤
    C * (((Finset.univ : Finset (BooleanSlices.BooleanSlicePoint I ell)).filter
      P).card : ℝ) +
      (((Finset.univ : Finset (BooleanSlices.BooleanSlicePoint I ell)).filter fun U ↦
        ¬lemma83BalancedResidue eta m ell (U.1 \ (A ∪ B)).card).card : ℝ)
      at hstep
  change (((Finset.univ : Finset (BooleanSlices.BooleanSlicePoint I ell)).filter fun U ↦
      ¬lemma83BalancedResidue eta m ell (U.1 \ (A ∪ B)).card).card : ℝ) ≤
    eps * Fintype.card (BooleanSlices.BooleanSlicePoint I ell) at hbadCard
  have hcount :
      (((Finset.univ : Finset (BooleanSlices.BooleanSlicePoint I ell)).filter
          fun U ↦ P U ∧ Q U).card : ℝ) ≤
        C * (((Finset.univ : Finset (BooleanSlices.BooleanSlicePoint I ell)).filter
          P).card : ℝ) +
          eps * Fintype.card (BooleanSlices.BooleanSlicePoint I ell) :=
    hstep.trans (add_le_add le_rfl hbadCard)
  change Concentration.uniformProbability
      (fun U : BooleanSlices.BooleanSlicePoint I ell ↦ P U ∧ Q U) ≤
    C * Concentration.uniformProbability P + eps
  rw [uniformProbability_eq_filter_div,
    uniformProbability_eq_filter_div]
  have hΩ : (0 : ℝ) <
      Fintype.card (BooleanSlices.BooleanSlicePoint I ell) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hΩ).2
  calc
    (((Finset.univ : Finset (BooleanSlices.BooleanSlicePoint I ell)).filter
        fun U ↦ P U ∧ Q U).card : ℝ) ≤
        C * (((Finset.univ : Finset (BooleanSlices.BooleanSlicePoint I ell)).filter
          P).card : ℝ) +
          eps * Fintype.card (BooleanSlices.BooleanSlicePoint I ell) := hcount
    _ ≤ _ := by
      field_simp
      exact le_rfl

/-! ### Iterating over the tuple coordinates -/

structure Lemma83BlockPair
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i : Fin q) where
  A : Finset (Fin n)
  B : Finset (Fin n)
  A_subset : A ⊆ tupleNewNeighborCell G (w.tuple a) i ∩ w.J
  B_subset : B ⊆ tupleRemainingCell G (w.tuple a) i ∩ w.J
  card_A : A.card = lemma83BlockSize n beta
  card_B : B.card = lemma83BlockSize n beta
  disjoint : Disjoint A B

theorem Lemma82Witness.exists_lemma83BlockPair
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i : Fin q) :
    Nonempty (Lemma83BlockPair w a i) := by
  obtain ⟨A, B, hA, hB, hAcard, hBcard, hAB⟩ :=
    w.exists_lemma83Blocks a i
  exact ⟨{
    A := A
    B := B
    A_subset := hA
    B_subset := hB
    card_A := hAcard
    card_B := hBcard
    disjoint := hAB }⟩

noncomputable def selectedLemma83BlockPair
    {n q familySize : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta q familySize)
    (a : Fin familySize) (i : Fin q) : Lemma83BlockPair w a i :=
  Classical.choice (w.exists_lemma83BlockPair a i)

def lemma83DegreeEvent
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (a : Fin familySize) (tau delta : ℝ) (x : Fin q → ℝ)
    (r : Fin q) (U : BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) ell) : Prop :=
  RLCD.distToInt
    (tau * (AKSGraph.degreeInto G (w.tuple a r.succ) (U.1 ∩ w.J) : ℝ) -
      tau * (AKSGraph.degreeInto G (w.tuple a 0) (U.1 ∩ w.J) : ℝ) + x r) ≤ delta

lemma lemma83DegreePrefix_invariant
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (a : Fin familySize) (tau delta : ℝ) (x : Fin q → ℝ)
    (k : Fin q) (b : Lemma83BlockPair w a k.succ)
    (U V : BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) ell)
    (hUV : U.1 \ (b.A ∪ b.B) = V.1 \ (b.A ∪ b.B)) :
    (U ∈ prefixEventFinset (lemma83DegreeEvent w a tau delta x) k.val ↔
      V ∈ prefixEventFinset (lemma83DegreeEvent w a tau delta x) k.val) := by
  classical
  simp only [prefixEventFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h r hr
    have hrk : r.succ < k.succ := Fin.succ_lt_succ_iff.mpr hr
    have h0k : (0 : Fin (q + 1)) < k.succ := Fin.succ_pos k
    have hUr := lemma83Blocks_prior_degree_eq_outside
      w a k.succ r.succ b.A b.B U.1 b.A_subset b.B_subset hrk
    have hVr := lemma83Blocks_prior_degree_eq_outside
      w a k.succ r.succ b.A b.B V.1 b.A_subset b.B_subset hrk
    have hU0 := lemma83Blocks_prior_degree_eq_outside
      w a k.succ 0 b.A b.B U.1 b.A_subset b.B_subset h0k
    have hV0 := lemma83Blocks_prior_degree_eq_outside
      w a k.succ 0 b.A b.B V.1 b.A_subset b.B_subset h0k
    have hdegR : AKSGraph.degreeInto G (w.tuple a r.succ) (U.1 ∩ w.J) =
        AKSGraph.degreeInto G (w.tuple a r.succ) (V.1 ∩ w.J) := by
      calc
        _ = AKSGraph.degreeInto G (w.tuple a r.succ)
            ((U.1 \ (b.A ∪ b.B)) ∩ w.J) := hUr
        _ = AKSGraph.degreeInto G (w.tuple a r.succ)
            ((V.1 \ (b.A ∪ b.B)) ∩ w.J) := by rw [hUV]
        _ = _ := hVr.symm
    have hdeg0 : AKSGraph.degreeInto G (w.tuple a 0) (U.1 ∩ w.J) =
        AKSGraph.degreeInto G (w.tuple a 0) (V.1 ∩ w.J) := by
      calc
        _ = AKSGraph.degreeInto G (w.tuple a 0)
            ((U.1 \ (b.A ∪ b.B)) ∩ w.J) := hU0
        _ = AKSGraph.degreeInto G (w.tuple a 0)
            ((V.1 \ (b.A ∪ b.B)) ∩ w.J) := by rw [hUV]
        _ = _ := hV0.symm
    simpa only [lemma83DegreeEvent, hdegR, hdeg0] using h r hr
  · intro h r hr
    have hrk : r.succ < k.succ := Fin.succ_lt_succ_iff.mpr hr
    have h0k : (0 : Fin (q + 1)) < k.succ := Fin.succ_pos k
    have hUr := lemma83Blocks_prior_degree_eq_outside
      w a k.succ r.succ b.A b.B U.1 b.A_subset b.B_subset hrk
    have hVr := lemma83Blocks_prior_degree_eq_outside
      w a k.succ r.succ b.A b.B V.1 b.A_subset b.B_subset hrk
    have hU0 := lemma83Blocks_prior_degree_eq_outside
      w a k.succ 0 b.A b.B U.1 b.A_subset b.B_subset h0k
    have hV0 := lemma83Blocks_prior_degree_eq_outside
      w a k.succ 0 b.A b.B V.1 b.A_subset b.B_subset h0k
    have hdegR : AKSGraph.degreeInto G (w.tuple a r.succ) (V.1 ∩ w.J) =
        AKSGraph.degreeInto G (w.tuple a r.succ) (U.1 ∩ w.J) := by
      calc
        _ = AKSGraph.degreeInto G (w.tuple a r.succ)
            ((V.1 \ (b.A ∪ b.B)) ∩ w.J) := hVr
        _ = AKSGraph.degreeInto G (w.tuple a r.succ)
            ((U.1 \ (b.A ∪ b.B)) ∩ w.J) := by rw [hUV]
        _ = _ := hUr.symm
    have hdeg0 : AKSGraph.degreeInto G (w.tuple a 0) (V.1 ∩ w.J) =
        AKSGraph.degreeInto G (w.tuple a 0) (U.1 ∩ w.J) := by
      calc
        _ = AKSGraph.degreeInto G (w.tuple a 0)
            ((V.1 \ (b.A ∪ b.B)) ∩ w.J) := hV0
        _ = AKSGraph.degreeInto G (w.tuple a 0)
            ((U.1 \ (b.A ∪ b.B)) ∩ w.J) := by rw [hUV]
        _ = _ := hU0.symm
    simpa only [lemma83DegreeEvent, hdegR, hdeg0] using h r hr

theorem lemma83DegreePrefix_probability_step
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (a : Fin familySize) (tau delta eta : ℝ) (x : Fin q → ℝ)
    (hell : ell ≤ n) (hm : 1 ≤ lemma83BlockSize n beta)
    (heta : 0 < eta) (hellower : eta * (n : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * n)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) (k : Fin q) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) ell ↦
          U ∈ prefixEventFinset (lemma83DegreeEvent w a tau delta x)
            (k.val + 1)) ≤
      (4096 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + 1 /
              Real.sqrt (2 * lemma83BlockSize n beta : ℕ)) / |tau|)) *
        Concentration.uniformProbability
          (fun U : BooleanSlices.BooleanSlicePoint
              (Finset.univ : Finset (Fin n)) ell ↦
            U ∈ prefixEventFinset (lemma83DegreeEvent w a tau delta x)
              k.val) +
      2 * Real.exp
        (-(eta * lemma83BlockSize n beta) ^ 2 /
          (8 * (2 * lemma83BlockSize n beta : ℕ))) := by
  classical
  let m := lemma83BlockSize n beta
  let b := selectedLemma83BlockPair w a k.succ
  let E : Fin q → BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) ell → Prop :=
    lemma83DegreeEvent (ell := ell) w a tau delta x
  let P : BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) ell → Prop := fun U ↦
    U ∈ prefixEventFinset E k.val
  have hIcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hstep := lemma83Blocks_oneStep_probability
    w a k.succ 0 (Fin.succ_pos k)
    (Finset.univ : Finset (Fin n)) b.A b.B m ell
    b.disjoint b.card_A b.card_B b.A_subset b.B_subset
    (Finset.subset_univ _) (by simpa only [hIcard] using hell) hm
    eta tau (x k) delta heta
    (by simpa only [hIcard] using hellower)
    (by simpa only [hIcard] using hellupper)
    htau hdelta hdeltaUpper P
    (by
      intro U V hUV
      exact lemma83DegreePrefix_invariant w a tau delta x k b U V hUV)
  have hleft :
      (fun U : BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) ell ↦
        U ∈ prefixEventFinset E (k.val + 1)) =
      (fun U ↦ P U ∧ E k U) := by
    funext U
    apply propext
    exact mem_prefixEventFinset_succ E k.isLt U
  have hScard : (b.A ∪ b.B).card = 2 * m := by
    rw [Finset.card_union_of_disjoint b.disjoint, b.card_A, b.card_B]
    omega
  have hleft' :
      (fun U : BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) ell ↦
        U ∈ prefixEventFinset (lemma83DegreeEvent w a tau delta x)
          (k.val + 1)) =
      (fun U ↦ P U ∧ E k U) := by
    simpa only [E] using hleft
  rw [hleft']
  rw [hScard] at hstep
  simpa only [E, P, m, lemma83DegreeEvent] using hstep

/-- An affine probability recurrence with a contractive main coefficient
accumulates at most one copy of the additive error at each step. -/
lemma affine_recurrence_le_pow_add
    (p : ℕ → ℝ) (C eps : ℝ) (q : ℕ)
    (hC0 : 0 ≤ C) (hC1 : C ≤ 1) (heps : 0 ≤ eps)
    (hp0 : p 0 ≤ 1)
    (hstep : ∀ k < q, p (k + 1) ≤ C * p k + eps) :
    p q ≤ C ^ q + (q : ℝ) * eps := by
  induction q with
  | zero => simpa using hp0
  | succ q ih =>
      have hrec := hstep q (Nat.lt_succ_self q)
      have hprev : p q ≤ C ^ q + (q : ℝ) * eps :=
        ih (fun k hk => hstep k (Nat.lt.step hk))
      have hscale : C * ((q : ℝ) * eps) ≤ (q : ℝ) * eps := by
        have hnonneg : 0 ≤ (q : ℝ) * eps := mul_nonneg (by positivity) heps
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 hnonneg
      calc
        p (q + 1) ≤ C * p q + eps := hrec
        _ ≤ C * (C ^ q + (q : ℝ) * eps) + eps :=
          add_le_add (mul_le_mul_of_nonneg_left hprev hC0) le_rfl
        _ ≤ C ^ (q + 1) + ((q + 1 : ℕ) : ℝ) * eps := by
          rw [pow_succ]
          push_cast
          linarith

/-- Iterating the exact one-coordinate conditioning estimate gives the full
degree-prefix event, with the exponentially small imbalance contribution
still displayed additively.  This is the probabilistic recursion in the proof
of KSSS Lemma 8.3, before its final numerical absorption. -/
theorem lemma83DegreePrefix_probability
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (a : Fin familySize) (tau delta eta : ℝ) (x : Fin q → ℝ)
    (hell : ell ≤ n) (hm : 1 ≤ lemma83BlockSize n beta)
    (heta : 0 < eta) (hellower : eta * (n : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * n)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) ell ↦
          U ∈ prefixEventFinset (lemma83DegreeEvent w a tau delta x) q) ≤
      (4096 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + 1 /
              Real.sqrt (2 * lemma83BlockSize n beta : ℕ)) / |tau|)) ^ q +
      (q : ℝ) *
        (2 * Real.exp
          (-(eta * lemma83BlockSize n beta) ^ 2 /
            (8 * (2 * lemma83BlockSize n beta : ℕ)))) := by
  classical
  let : Nonempty (BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) ell) :=
    BooleanSlices.booleanSlicePoint_nonempty (by simpa using hell)
  let m := lemma83BlockSize n beta
  let E : Fin q → BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) ell → Prop :=
    lemma83DegreeEvent (ell := ell) w a tau delta x
  let p : ℕ → ℝ := fun k ↦
    Concentration.uniformProbability (fun U ↦
      U ∈ prefixEventFinset E k)
  let C : ℝ := 4096 / (eta / 2) *
    ((|tau| + delta) * (|tau| + 1 / Real.sqrt (2 * m : ℕ)) / |tau|)
  let eps : ℝ := 2 * Real.exp (-(eta * m) ^ 2 / (8 * (2 * m : ℕ)))
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have htauabs : 0 < |tau| := abs_pos.mpr htau
  have hsqrt : 0 < Real.sqrt (2 * m : ℕ) := by positivity
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have heps : 0 ≤ eps := by
    dsimp only [eps]
    positivity
  have hp0 : p 0 ≤ 1 := by
    dsimp only [p]
    exact Concentration.uniformProbability_le_one _
  have hstep : ∀ k < q, p (k + 1) ≤ C * p k + eps := by
    intro k hk
    have hs := lemma83DegreePrefix_probability_step
      w a tau delta eta x hell hm heta hellower hellupper htau hdelta
        hdeltaUpper ⟨k, hk⟩
    simpa only [p, C, eps, E, m] using hs
  by_cases hC1 : C ≤ 1
  · have hrec := affine_recurrence_le_pow_add p C eps q hC0 hC1 heps hp0 hstep
    simpa only [p, C, eps, E, m] using hrec
  · have hprob : p q ≤ 1 := by
      dsimp only [p]
      exact Concentration.uniformProbability_le_one _
    have hpow : 1 ≤ C ^ q := one_le_pow₀ (le_of_not_ge hC1)
    have herr : 0 ≤ (q : ℝ) * eps := mul_nonneg (by positivity) heps
    have hfinal : p q ≤ C ^ q + (q : ℝ) * eps := by linarith
    simpa only [p, C, eps, E, m] using hfinal

/-- Joint-event presentation of `lemma83DegreePrefix_probability`.  The
indices `r : Fin q` here represent the source indices `2, …, q+1`. -/
theorem lemma83DegreeJoint_probability
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (a : Fin familySize) (tau delta eta : ℝ) (x : Fin q → ℝ)
    (hell : ell ≤ n) (hm : 1 ≤ lemma83BlockSize n beta)
    (heta : 0 < eta) (hellower : eta * (n : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * n)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) ell ↦
          ∀ r : Fin q,
            RLCD.distToInt
              (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                  (U.1 ∩ w.J) : ℝ) -
                tau * (AKSGraph.degreeInto G (w.tuple a 0)
                  (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤
      (4096 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + 1 /
              Real.sqrt (2 * lemma83BlockSize n beta : ℕ)) / |tau|)) ^ q +
      (q : ℝ) *
        (2 * Real.exp
          (-(eta * lemma83BlockSize n beta) ^ 2 /
            (8 * (2 * lemma83BlockSize n beta : ℕ)))) := by
  classical
  let E : Fin q → BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) ell → Prop :=
    lemma83DegreeEvent (ell := ell) w a tau delta x
  have hevent :
      (fun U : BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin n)) ell ↦
        U ∈ prefixEventFinset E q) =
      (fun U ↦ ∀ r : Fin q,
        RLCD.distToInt
          (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
              (U.1 ∩ w.J) : ℝ) -
            tau * (AKSGraph.degreeInto G (w.tuple a 0)
              (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) := by
    funext U
    apply propext
    rw [mem_prefixEventFinset_full]
    rfl
  rw [← hevent]
  simpa only [E] using lemma83DegreePrefix_probability
    w a tau delta eta x hell hm heta hellower hellupper htau hdelta
      hdeltaUpper

/-- The canonical block size used in Lemma 8.3 is positive as soon as the
ambient graph is nonempty. -/
lemma one_le_lemma83BlockSize (n : ℕ) (beta : ℝ) (hn : 1 ≤ n) :
    1 ≤ lemma83BlockSize n beta := by
  rw [lemma83BlockSize]
  exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)

/-- The square-root scale of the canonical two-block hypergeometric law is
at most the source scale `n^{-(1-β)/2}`. -/
lemma inv_sqrt_lemma83BlockSize_le
    (n : ℕ) (beta : ℝ) (hn : 1 ≤ n) :
    1 / Real.sqrt (2 * lemma83BlockSize n beta : ℕ) ≤
      (n : ℝ) ^ (-(1 - beta) / 2) := by
  let m := lemma83BlockSize n beta
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpowpos : 0 < (n : ℝ) ^ (1 - beta) :=
    Real.rpow_pos_of_pos hnpos _
  have hceil : (n : ℝ) ^ (1 - beta) ≤ (m : ℝ) := by
    simpa only [m, lemma83BlockSize] using
      Nat.le_ceil ((n : ℝ) ^ (1 - beta))
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hroot : Real.sqrt ((n : ℝ) ^ (1 - beta)) ≤
      Real.sqrt (2 * m : ℕ) := by
    apply Real.sqrt_le_sqrt
    exact hceil.trans (by push_cast; linarith)
  have hsource : Real.sqrt ((n : ℝ) ^ (1 - beta)) =
      (n : ℝ) ^ ((1 - beta) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]
    congr 1
    ring
  calc
    1 / Real.sqrt (2 * lemma83BlockSize n beta : ℕ) =
        1 / Real.sqrt (2 * m : ℕ) := by rfl
    _ ≤ 1 / Real.sqrt ((n : ℝ) ^ (1 - beta)) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.2 hpowpos) hroot
    _ = (n : ℝ) ^ (-(1 - beta) / 2) := by
      rw [hsource]
      rw [div_eq_mul_inv, one_mul, ← Real.rpow_neg hnpos.le]
      congr 1
      ring

/-- The explicit one-step coefficient is bounded by the scale displayed in
the statement of KSSS Lemma 8.3. -/
lemma lemma83_coefficient_le_sourceScale
    (n : ℕ) (beta eta tau delta : ℝ) (hn : 1 ≤ n)
    (heta : 0 < eta) (htau : tau ≠ 0) (hdelta : 0 ≤ delta) :
    4096 / (eta / 2) *
        ((|tau| + delta) *
          (|tau| + 1 / Real.sqrt (2 * lemma83BlockSize n beta : ℕ)) /
            |tau|) ≤
      4096 / (eta / 2) *
        ((|tau| + delta) *
          (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|) := by
  have htauabs : 0 < |tau| := abs_pos.mpr htau
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ htauabs.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (inv_sqrt_lemma83BlockSize_le n beta hn)

/-- Fully source-normalized joint estimate, before absorbing the negligible
hypergeometric imbalance error. -/
theorem lemma83DegreeJoint_probability_sourceScale_additive
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (a : Fin familySize) (tau delta eta : ℝ) (x : Fin q → ℝ)
    (hell : ell ≤ n) (hn : 1 ≤ n)
    (heta : 0 < eta) (hellower : eta * (n : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * n)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) ell ↦
          ∀ r : Fin q,
            RLCD.distToInt
              (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                  (U.1 ∩ w.J) : ℝ) -
                tau * (AKSGraph.degreeInto G (w.tuple a 0)
                  (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤
      (4096 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q +
      (q : ℝ) *
        (2 * Real.exp
          (-(eta * lemma83BlockSize n beta) ^ 2 /
            (8 * (2 * lemma83BlockSize n beta : ℕ)))) := by
  have hraw := lemma83DegreeJoint_probability
    w a tau delta eta x hell (one_le_lemma83BlockSize n beta hn)
      heta hellower hellupper htau hdelta hdeltaUpper
  have hcoef := lemma83_coefficient_le_sourceScale
    n beta eta tau delta hn heta htau hdelta.le
  have hraw0 : 0 ≤ 4096 / (eta / 2) *
      ((|tau| + delta) *
        (|tau| + 1 / Real.sqrt (2 * lemma83BlockSize n beta : ℕ)) /
          |tau|) := by
    have htauabs : 0 < |tau| := abs_pos.mpr htau
    positivity
  exact hraw.trans (add_le_add (pow_le_pow_left₀ hraw0 hcoef q) le_rfl)

lemma eventually_const_le_natCast_rpow (C p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in Filter.atTop, C ≤ (n : ℝ) ^ p := by
  exact ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop C)

lemma eventually_const_mul_log_le_natCast_rpow (C p : ℝ)
    (hC : 0 ≤ C) (hp : 0 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * Real.log n ≤ (n : ℝ) ^ p := by
  let r := p / 2
  have hr : 0 < r := div_pos hp (by norm_num)
  have hgrow := eventually_const_le_natCast_rpow (C / r) r hr
  filter_upwards [Filter.eventually_ge_atTop 1, hgrow] with n hn hnGrow
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog := Real.log_natCast_le_rpow_div n hr
  calc
    C * Real.log n ≤ C * ((n : ℝ) ^ r / r) :=
      mul_le_mul_of_nonneg_left hlog hC
    _ = (C / r) * (n : ℝ) ^ r := by ring
    _ ≤ (n : ℝ) ^ r * (n : ℝ) ^ r :=
      mul_le_mul_of_nonneg_right hnGrow (Real.rpow_nonneg hnR.le r)
    _ = (n : ℝ) ^ p := by
      rw [← Real.rpow_add hnR]
      congr 1
      dsimp only [r]
      ring

lemma eventually_const_mul_log_sq_le_natCast_rpow (C p : ℝ)
    (_hC : 0 ≤ C) (hp : 0 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * Real.log n ^ 2 ≤ (n : ℝ) ^ p := by
  let D := max 1 C
  have hD0 : 0 ≤ D := le_trans zero_le_one (le_max_left _ _)
  have hCD : C ≤ D := le_max_right _ _
  have hlog := eventually_const_mul_log_le_natCast_rpow D (p / 2) hD0
    (div_pos hp (by norm_num))
  filter_upwards [Filter.eventually_ge_atTop 1, hlog] with n hn hnLog
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hClog : C * Real.log n ≤ (n : ℝ) ^ (p / 2) :=
    (mul_le_mul_of_nonneg_right hCD hlog0).trans hnLog
  have hlogD : Real.log n ≤ (n : ℝ) ^ (p / 2) := by
    calc
      Real.log n ≤ D * Real.log n := by
        nlinarith [le_max_left (1 : ℝ) C]
      _ ≤ (n : ℝ) ^ (p / 2) := hnLog
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  calc
    C * Real.log n ^ 2 = (C * Real.log n) * Real.log n := by ring
    _ ≤ (n : ℝ) ^ (p / 2) * (n : ℝ) ^ (p / 2) :=
      mul_le_mul hClog hlogD hlog0 (Real.rpow_nonneg hnpos.le _)
    _ = (n : ℝ) ^ p := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

lemma eventually_const_mul_natCast_le_exp_natCast_rpow (C p : ℝ)
    (hp : 0 < p) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * (n : ℝ) ≤ Real.exp ((n : ℝ) ^ p) := by
  let D := max 1 C
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCD : C ≤ D := le_max_right _ _
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (le_max_left _ _)
  have hconst := eventually_const_le_natCast_rpow (2 * Real.log D) p hp
  have hlog := eventually_const_mul_log_le_natCast_rpow 2 p (by norm_num) hp
  filter_upwards [Filter.eventually_ge_atTop 1, hconst, hlog]
    with n hn hnConst hnLog
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn0 : 0 ≤ (n : ℝ) := hnpos.le
  calc
    C * (n : ℝ) ≤ D * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hCD hn0
    _ = Real.exp (Real.log (D * (n : ℝ))) :=
      (Real.exp_log (mul_pos hDpos hnpos)).symm
    _ = Real.exp (Real.log D + Real.log n) := by
      rw [Real.log_mul (ne_of_gt hDpos) (ne_of_gt hnpos)]
    _ ≤ Real.exp ((n : ℝ) ^ p) := by
      apply Real.exp_le_exp.mpr
      nlinarith

lemma lemma83_imbalance_le_sourcePower_of_bounds
    (n q : ℕ) (beta eta zeta : ℝ)
    (hn : 1 ≤ n) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (heta : 0 < eta) (hzeta : 0 < zeta)
    (hq : (q : ℝ) ≤ zeta * Real.log n)
    (hpref : 2 * max 1 zeta * (n : ℝ) ≤
      Real.exp (eta ^ 2 * (n : ℝ) ^ (1 - beta) / 32))
    (hlogsq : (16 * (1 - beta) * zeta / eta ^ 2) *
      Real.log n ^ 2 ≤ (n : ℝ) ^ (1 - beta)) :
    (q : ℝ) *
        (2 * Real.exp
          (-(eta * lemma83BlockSize n beta) ^ 2 /
            (8 * (2 * lemma83BlockSize n beta : ℕ)))) ≤
      ((n : ℝ) ^ (-(1 - beta) / 2)) ^ q := by
  let p : ℝ := 1 - beta
  let m : ℕ := lemma83BlockSize n beta
  have hp : 0 < p := by dsimp only [p]; linarith
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hm : 1 ≤ m := by
    simpa only [m] using one_le_lemma83BlockSize n beta hn
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hceil : (n : ℝ) ^ p ≤ (m : ℝ) := by
    simpa only [p, m, lemma83BlockSize] using
      Nat.le_ceil ((n : ℝ) ^ (1 - beta))
  have hlogn : Real.log n ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hnpos
    linarith
  have hqDn : (q : ℝ) ≤ max 1 zeta * (n : ℝ) := by
    calc
      (q : ℝ) ≤ zeta * Real.log n := hq
      _ ≤ max 1 zeta * Real.log n :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hlog0
      _ ≤ max 1 zeta * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hlogn (le_trans zero_le_one (le_max_left _ _))
  have hprefq : 2 * (q : ℝ) ≤
      Real.exp (eta ^ 2 * (n : ℝ) ^ p / 32) := by
    dsimp only [p]
    refine (mul_le_mul_of_nonneg_left hqDn (by norm_num)).trans ?_
    simpa only [mul_assoc] using hpref
  have hnorm :
      -(eta * (m : ℝ)) ^ 2 / (8 * (2 * m : ℝ)) =
        -(eta ^ 2 * (m : ℝ) / 16) := by
    field_simp [ne_of_gt hmpos]
    ring
  have htail : Real.exp
      (-(eta * (m : ℝ)) ^ 2 / (8 * (2 * m : ℝ))) ≤
      Real.exp (-(eta ^ 2 * (n : ℝ) ^ p / 16)) := by
    apply Real.exp_le_exp.mpr
    rw [hnorm]
    have heta2 : 0 ≤ eta ^ 2 := sq_nonneg eta
    nlinarith [mul_le_mul_of_nonneg_left hceil heta2]
  have herr : (q : ℝ) *
      (2 * Real.exp
        (-(eta * (m : ℝ)) ^ 2 / (8 * (2 * m : ℝ)))) ≤
      Real.exp (-(eta ^ 2 * (n : ℝ) ^ p / 32)) := by
    calc
      (q : ℝ) *
          (2 * Real.exp
            (-(eta * (m : ℝ)) ^ 2 / (8 * (2 * m : ℝ)))) =
          (2 * (q : ℝ)) * Real.exp
            (-(eta * (m : ℝ)) ^ 2 / (8 * (2 * m : ℝ))) := by ring
      _ ≤ Real.exp (eta ^ 2 * (n : ℝ) ^ p / 32) *
          Real.exp (-(eta ^ 2 * (n : ℝ) ^ p / 16)) :=
        mul_le_mul hprefq htail (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (-(eta ^ 2 * (n : ℝ) ^ p / 32)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hexponent :
      -(eta ^ 2 * (n : ℝ) ^ p / 32) ≤
        Real.log n * ((-(p / 2)) * (q : ℝ)) := by
    have hqlog : (p / 2) * (q : ℝ) * Real.log n ≤
        (p / 2) * zeta * Real.log n ^ 2 := by
      have := mul_le_mul_of_nonneg_right hq hlog0
      nlinarith
    have hscale : (p / 2) * zeta * Real.log n ^ 2 ≤
        eta ^ 2 * (n : ℝ) ^ p / 32 := by
      have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta
      have hscaled := mul_le_mul_of_nonneg_left hlogsq
        (div_nonneg heta2.le (by norm_num : (0 : ℝ) ≤ 32))
      have hleft :
          eta ^ 2 / 32 *
              ((16 * (1 - beta) * zeta / eta ^ 2) * Real.log n ^ 2) =
            ((1 - beta) / 2) * zeta * Real.log n ^ 2 := by
        field_simp [ne_of_gt heta]
        ring
      have hright : eta ^ 2 / 32 * (n : ℝ) ^ (1 - beta) =
          eta ^ 2 * (n : ℝ) ^ (1 - beta) / 32 := by ring
      rw [hleft, hright] at hscaled
      simpa only [p] using hscaled
    nlinarith
  calc
    (q : ℝ) *
        (2 * Real.exp
          (-(eta * lemma83BlockSize n beta) ^ 2 /
            (8 * (2 * lemma83BlockSize n beta : ℕ)))) =
        (q : ℝ) *
          (2 * Real.exp
            (-(eta * (m : ℝ)) ^ 2 / (8 * (2 * m : ℝ)))) := by
      simp only [m, Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ Real.exp (-(eta ^ 2 * (n : ℝ) ^ p / 32)) := herr
    _ ≤ Real.exp (Real.log n * ((-(p / 2)) * (q : ℝ))) :=
      Real.exp_le_exp.mpr hexponent
    _ = ((n : ℝ) ^ (-(1 - beta) / 2)) ^ q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le,
        Real.rpow_def_of_pos hnpos]
      congr 1
      dsimp only [p]
      ring

/-- In the logarithmic tuple-length regime supplied by Lemma 8.2, the
accumulated imbalance probability is eventually dominated by the source
scale to the full tuple power. -/
lemma eventually_lemma83_imbalance_le_sourcePower
    (beta eta zeta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (heta : 0 < eta) (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ q : ℕ,
      (q : ℝ) ≤ zeta * Real.log n →
      (q : ℝ) *
          (2 * Real.exp
            (-(eta * lemma83BlockSize n beta) ^ 2 /
              (8 * (2 * lemma83BlockSize n beta : ℕ)))) ≤
        ((n : ℝ) ^ (-(1 - beta) / 2)) ^ q := by
  let p : ℝ := 1 - beta
  have hp : 0 < p := by dsimp only [p]; linarith
  have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta
  have hlin := eventually_const_mul_natCast_le_exp_natCast_rpow
    (2 * max 1 zeta) (p / 2) (div_pos hp (by norm_num))
  have hconst := eventually_const_le_natCast_rpow
    (32 / eta ^ 2) (p / 2) (div_pos hp (by norm_num))
  have hlogsq := eventually_const_mul_log_sq_le_natCast_rpow
    (16 * p * zeta / eta ^ 2) p (by positivity) hp
  filter_upwards [Filter.eventually_ge_atTop 1, hlin, hconst, hlogsq]
    with n hn hnLin hnConst hnLogSq
  intro q hq
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpowHalf0 : 0 ≤ (n : ℝ) ^ (p / 2) :=
    Real.rpow_nonneg hnpos.le _
  have hpowSplit : (n : ℝ) ^ p =
      (n : ℝ) ^ (p / 2) * (n : ℝ) ^ (p / 2) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hhalf : (n : ℝ) ^ (p / 2) ≤
      eta ^ 2 * (n : ℝ) ^ p / 32 := by
    calc
      (n : ℝ) ^ (p / 2) =
          (eta ^ 2 / 32) * ((32 / eta ^ 2) * (n : ℝ) ^ (p / 2)) := by
        field_simp [ne_of_gt heta]
      _ ≤ (eta ^ 2 / 32) * (n : ℝ) ^ p := by
        apply mul_le_mul_of_nonneg_left _
          (div_nonneg heta2.le (by norm_num))
        rw [hpowSplit]
        exact mul_le_mul_of_nonneg_right hnConst hpowHalf0
      _ = eta ^ 2 * (n : ℝ) ^ p / 32 := by ring
  have hpref : 2 * max 1 zeta * (n : ℝ) ≤
      Real.exp (eta ^ 2 * (n : ℝ) ^ p / 32) :=
    hnLin.trans (Real.exp_le_exp.mpr hhalf)
  apply lemma83_imbalance_le_sourcePower_of_bounds
    n q beta eta zeta hn hbeta0 hbeta1 heta hzeta hq
  · simpa only [p] using hpref
  · simpa only [p] using hnLogSq

lemma add_self_pow_le_two_mul_pow {B : ℝ} {q : ℕ}
    (hB : 0 ≤ B) (hq : 1 ≤ q) :
    B ^ q + B ^ q ≤ (2 * B) ^ q := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
  have htwo : (2 : ℝ) ≤ 2 ^ (1 + r) := by
    rw [pow_add, pow_one]
    nlinarith [one_le_pow₀ (n := r) (by norm_num : (1 : ℝ) ≤ 2)]
  rw [mul_pow]
  have hBpow : 0 ≤ B ^ (1 + r) := pow_nonneg hB _
  nlinarith [mul_le_mul_of_nonneg_right htwo hBpow]

/-- Absorbed finite form of Lemma 8.3.  The final hypothesis is precisely
the numerical imbalance estimate established eventually above. -/
theorem lemma83DegreeJoint_probability_sourcePower_of_imbalance
    {n q familySize ell : ℕ} {G : SimpleGraph (Fin n)} {beta : ℝ}
    (w : Lemma82Witness G beta (q + 1) familySize)
    (a : Fin familySize) (tau delta eta : ℝ) (x : Fin q → ℝ)
    (hell : ell ≤ n) (hn : 1 ≤ n)
    (heta : 0 < eta) (hellower : eta * (n : ℝ) ≤ ell)
    (hellupper : (ell : ℝ) ≤ (1 - eta) * n)
    (htau : tau ≠ 0) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 1 / 2)
    (himbalance :
      (q : ℝ) *
          (2 * Real.exp
            (-(eta * lemma83BlockSize n beta) ^ 2 /
              (8 * (2 * lemma83BlockSize n beta : ℕ)))) ≤
        ((n : ℝ) ^ (-(1 - beta) / 2)) ^ q) :
    Concentration.uniformProbability
        (fun U : BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin n)) ell ↦
          ∀ r : Fin q,
            RLCD.distToInt
              (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                  (U.1 ∩ w.J) : ℝ) -
                tau * (AKSGraph.degreeInto G (w.tuple a 0)
                  (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤
      (8192 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q := by
  classical
  let : Nonempty (BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin n)) ell) :=
    BooleanSlices.booleanSlicePoint_nonempty (by simpa using hell)
  by_cases hq0 : q = 0
  · subst q
    simpa using Concentration.uniformProbability_le_one
      (fun U : BooleanSlices.BooleanSlicePoint
        (Finset.univ : Finset (Fin n)) ell ↦
          ∀ r : Fin 0,
            RLCD.distToInt
              (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                  (U.1 ∩ w.J) : ℝ) -
                tau * (AKSGraph.degreeInto G (w.tuple a 0)
                  (U.1 ∩ w.J) : ℝ) + x r) ≤ delta)
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    let s : ℝ := (n : ℝ) ^ (-(1 - beta) / 2)
    let T : ℝ := (|tau| + delta) * (|tau| + s) / |tau|
    let A : ℝ := 4096 / (eta / 2)
    let B : ℝ := A * T
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hs0 : 0 ≤ s := by dsimp only [s]; positivity
    have htauabs : 0 < |tau| := abs_pos.mpr htau
    have hT0 : 0 ≤ T := by dsimp only [T]; positivity
    have hetaHalf : eta ≤ 1 / 2 := by
      have hboth : eta * (n : ℝ) ≤ (1 - eta) * n :=
        hellower.trans hellupper
      have hmul : (2 * eta) * (n : ℝ) ≤ 1 * (n : ℝ) := by
        nlinarith
      have := le_of_mul_le_mul_right hmul hnpos
      linarith
    have hA1 : 1 ≤ A := by
      dsimp only [A]
      rw [le_div_iff₀ (div_pos heta (by norm_num))]
      nlinarith
    have hsT : s ≤ T := by
      dsimp only [T]
      apply (le_div_iff₀ htauabs).mpr
      rw [mul_comm s |tau|]
      exact mul_le_mul (le_add_of_nonneg_right hdelta.le)
        (le_add_of_nonneg_left htauabs.le) hs0 (by positivity)
    have hTB : T ≤ B := by
      dsimp only [B]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA1 hT0
    have hsB : s ≤ B := hsT.trans hTB
    have hB0 : 0 ≤ B := mul_nonneg (le_trans zero_le_one hA1) hT0
    have hraw := lemma83DegreeJoint_probability_sourceScale_additive
      w a tau delta eta x hell hn heta hellower hellupper htau hdelta
        hdeltaUpper
    have hsPow : s ^ q ≤ B ^ q := pow_le_pow_left₀ hs0 hsB q
    calc
      Concentration.uniformProbability
          (fun U : BooleanSlices.BooleanSlicePoint
              (Finset.univ : Finset (Fin n)) ell ↦
            ∀ r : Fin q,
              RLCD.distToInt
                (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                    (U.1 ∩ w.J) : ℝ) -
                  tau * (AKSGraph.degreeInto G (w.tuple a 0)
                    (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤
          B ^ q + (q : ℝ) *
            (2 * Real.exp
              (-(eta * lemma83BlockSize n beta) ^ 2 /
                (8 * (2 * lemma83BlockSize n beta : ℕ)))) := by
            simpa only [B, A, T, s] using hraw
      _ ≤ B ^ q + s ^ q := add_le_add le_rfl himbalance
      _ ≤ B ^ q + B ^ q := add_le_add le_rfl hsPow
      _ ≤ (2 * B) ^ q := add_self_pow_le_two_mul_pow hB0 hq1
      _ = (8192 / (eta / 2) *
          ((|tau| + delta) *
            (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q := by
        congr 1
        dsimp only [B, A, T, s]
        ring

/-- Source-shaped Lemma 8.3 estimate in the logarithmic tuple-length regime
used by Lemma 8.2.  The implicit `O_η` constant is made explicit as
`8192 / (η/2)`. -/
theorem eventually_lemma83DegreeJoint_probability_sourcePower
    (beta eta zeta : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (heta : 0 < eta) (hzeta : 0 < zeta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (q familySize ell : ℕ) (G : SimpleGraph (Fin n))
        (w : Lemma82Witness G beta (q + 1) familySize)
        (a : Fin familySize) (tau delta : ℝ) (x : Fin q → ℝ),
        (q : ℝ) ≤ zeta * Real.log n →
        ell ≤ n → eta * (n : ℝ) ≤ ell →
        (ell : ℝ) ≤ (1 - eta) * n →
        tau ≠ 0 → 0 < delta → delta ≤ 1 / 2 →
        Concentration.uniformProbability
            (fun U : BooleanSlices.BooleanSlicePoint
                (Finset.univ : Finset (Fin n)) ell ↦
              ∀ r : Fin q,
                RLCD.distToInt
                  (tau * (AKSGraph.degreeInto G (w.tuple a r.succ)
                      (U.1 ∩ w.J) : ℝ) -
                    tau * (AKSGraph.degreeInto G (w.tuple a 0)
                      (U.1 ∩ w.J) : ℝ) + x r) ≤ delta) ≤
          (8192 / (eta / 2) *
              ((|tau| + delta) *
                (|tau| + (n : ℝ) ^ (-(1 - beta) / 2)) / |tau|)) ^ q := by
  have himbalance := eventually_lemma83_imbalance_le_sourcePower
    beta eta zeta hbeta0 hbeta1 heta hzeta
  filter_upwards [Filter.eventually_ge_atTop 1, himbalance]
    with n hn hnImbalance
  intro q familySize ell G w a tau delta x hq hell hellower hellupper
    htau hdelta hdeltaUpper
  exact lemma83DegreeJoint_probability_sourcePower_of_imbalance
    w a tau delta eta x hell hn heta hellower hellupper htau hdelta
      hdeltaUpper (hnImbalance q hq)

end QuadraticCancellation
end Erdos88

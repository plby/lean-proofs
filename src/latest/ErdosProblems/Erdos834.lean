/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 834

Erdős and Lovász asked whether a `3`-critical `3`-uniform hypergraph can
have minimum degree at least `7`.  The word "critical" has two standard
interpretations for hypergraphs.  This file makes both interpretations
explicit.

* For weak chromatic criticality, Ruiliang Li gave a `22`-edge example on
  nine vertices.  We define that example and verify all of its properties.
* For transversal criticality, the corresponding minimum-degree condition
  is impossible; the general obstruction is formalized below.

The finite set-system representation used here has no repeated edges.
-/

namespace Erdos834

open Finset

/-- A finite simple hypergraph, represented by its finite set of finite edges. -/
abbrev Hypergraph (α : Type*) [DecidableEq α] := Finset (Finset α)

/-- Computable uniformity test. -/
def isUniformB {α : Type*} [DecidableEq α] (H : Hypergraph α) (r : ℕ) : Bool :=
  decide (∀ e ∈ H, e.card = r)

/-- Every edge of `H` has exactly `r` vertices. -/
def IsUniform {α : Type*} [DecidableEq α] (H : Hypergraph α) (r : ℕ) : Prop :=
  isUniformB H r = true

instance {α : Type*} [DecidableEq α] (H : Hypergraph α) (r : ℕ) :
    Decidable (IsUniform H r) :=
  inferInstanceAs (Decidable (isUniformB H r = true))

theorem isUniform_iff {α : Type*} [DecidableEq α] (H : Hypergraph α) (r : ℕ) :
    IsUniform H r ↔ ∀ e ∈ H, e.card = r := by
  simp [IsUniform, isUniformB]

/-- A weakly proper coloring: no edge is monochromatic. -/
def properColoringB {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (H : Hypergraph α) (c : α → κ) : Bool :=
  decide (∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y)

/-- A weakly proper coloring: no edge is monochromatic. -/
def ProperColoring {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (H : Hypergraph α) (c : α → κ) : Prop :=
  properColoringB H c = true

instance {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (H : Hypergraph α) (c : α → κ) : Decidable (ProperColoring H c) :=
  inferInstanceAs (Decidable (properColoringB H c = true))

theorem properColoring_iff {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (H : Hypergraph α) (c : α → κ) :
    ProperColoring H c ↔ ∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y := by
  simp [ProperColoring, properColoringB]

/-- Existence of a weakly proper coloring with `k` colors. -/
def colorableB {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (k : ℕ) : Bool :=
  decide (∃ c : α → Fin k, properColoringB H c = true)

/-- Existence of a weakly proper coloring with `k` colors. -/
def Colorable {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (k : ℕ) : Prop :=
  colorableB H k = true

instance {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (k : ℕ) : Decidable (Colorable H k) :=
  inferInstanceAs (Decidable (colorableB H k = true))

theorem colorable_iff {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (k : ℕ) :
    Colorable H k ↔ ∃ c : α → Fin k, ProperColoring H c := by
  simp [Colorable, colorableB, ProperColoring]

/-- Delete a vertex and every edge incident with it. -/
def deleteVertex {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (v : α) : Hypergraph α :=
  H.filter (fun e ↦ v ∉ e)

/-- The number of edges incident with `v`. -/
def degree {α : Type*} [DecidableEq α] (H : Hypergraph α) (v : α) : ℕ :=
  (H.filter (fun e ↦ v ∈ e)).card

/-- Every vertex in the ambient finite vertex type has degree at least `d`. -/
def minDegreeAtLeastB {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (d : ℕ) : Bool :=
  decide (∀ v, d ≤ degree H v)

/-- Every vertex in the ambient finite vertex type has degree at least `d`. -/
def MinDegreeAtLeast {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (d : ℕ) : Prop :=
  minDegreeAtLeastB H d = true

instance {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (d : ℕ) : Decidable (MinDegreeAtLeast H d) :=
  inferInstanceAs (Decidable (minDegreeAtLeastB H d = true))

theorem minDegreeAtLeast_iff {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (d : ℕ) :
    MinDegreeAtLeast H d ↔ ∀ v, d ≤ degree H v := by
  simp [MinDegreeAtLeast, minDegreeAtLeastB]

/--
Weak chromatic `3`-criticality: chromatic number exactly three, and deleting
any single edge or any single vertex makes the hypergraph two-colorable.
-/
def chromaticThreeCriticalB {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) : Bool :=
  colorableB H 3 &&
    !colorableB H 2 &&
    decide (∀ e ∈ H, colorableB (H.erase e) 2 = true) &&
    decide (∀ v, colorableB (deleteVertex H v) 2 = true)

def ChromaticThreeCritical {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) : Prop :=
  chromaticThreeCriticalB H = true

instance {α : Type*} [Fintype α] [DecidableEq α] (H : Hypergraph α) :
    Decidable (ChromaticThreeCritical H) :=
  inferInstanceAs (Decidable (chromaticThreeCriticalB H = true))

theorem chromaticThreeCritical_iff {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) :
    ChromaticThreeCritical H ↔
      Colorable H 3 ∧
      ¬Colorable H 2 ∧
      (∀ e ∈ H, Colorable (H.erase e) 2) ∧
      ∀ v, Colorable (deleteVertex H v) 2 := by
  simp [ChromaticThreeCritical, chromaticThreeCriticalB, Colorable, colorableB]
  tauto

/-- A finite set `T` meets every edge of `H`. -/
def hitsB {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (T : Finset α) : Bool :=
  decide (∀ e ∈ H, ∃ v ∈ e, v ∈ T)

def Hits {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (T : Finset α) : Prop :=
  hitsB H T = true

instance {α : Type*} [DecidableEq α] (H : Hypergraph α) (T : Finset α) :
    Decidable (Hits H T) :=
  inferInstanceAs (Decidable (hitsB H T = true))

theorem hits_iff {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (T : Finset α) :
    Hits H T ↔ ∀ e ∈ H, ∃ v ∈ e, v ∈ T := by
  simp [Hits, hitsB]

/--
Transversal `3`-criticality: the transversal number is three and deletion of
each edge lowers it to at most two.
-/
def transversalThreeCriticalB {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) : Bool :=
  let subsets := (Finset.univ : Finset α).powerset
  decide (∃ T ∈ subsets, T.card = 3 ∧ hitsB H T = true) &&
    !decide (∃ T ∈ subsets, T.card ≤ 2 ∧ hitsB H T = true) &&
    decide (∀ e ∈ H, ∃ T ∈ subsets,
      T.card ≤ 2 ∧ hitsB (H.erase e) T = true)

def TransversalThreeCritical {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) : Prop :=
  transversalThreeCriticalB H = true

instance {α : Type*} [Fintype α] [DecidableEq α] (H : Hypergraph α) :
    Decidable (TransversalThreeCritical H) :=
  inferInstanceAs (Decidable (transversalThreeCriticalB H = true))

theorem transversalThreeCritical_iff {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) :
    TransversalThreeCritical H ↔
      (∃ T : Finset α, T.card = 3 ∧ Hits H T) ∧
      (∀ T : Finset α, T.card ≤ 2 → ¬Hits H T) ∧
      ∀ e ∈ H, ∃ T : Finset α, T.card ≤ 2 ∧ Hits (H.erase e) T := by
  simp [TransversalThreeCritical, transversalThreeCriticalB, Hits, hitsB]
  tauto

/-! ## The two-families inequality -/

/-- The reciprocal binomial weight occurring in Bollobás's two-families inequality. -/
private def pairWeight (a b : ℕ) : ℚ :=
  ((Nat.choose (a + b) a : ℚ))⁻¹

private lemma pairWeight_le_one (a b : ℕ) : pairWeight a b ≤ 1 := by
  have hc : 1 ≤ Nat.choose (a + b) a :=
    Nat.choose_pos (Nat.le_add_right a b)
  apply (inv_le_one₀ (by positivity)).2
  exact_mod_cast hc

/-- The numerical identity used when one ground-set element is removed. -/
private lemma pairWeight_erase_identity (a b n : ℕ) (hb : 0 < b)
    (hab : a + b ≤ n) :
    (b : ℚ) * pairWeight a (b - 1) +
        ((n - a - b : ℕ) : ℚ) * pairWeight a b =
      (n : ℚ) * pairWeight a b := by
  have habm : a ≤ a + b - 1 := by omega
  have hchooseNat :
      Nat.choose (a + b - 1) a * (a + b) =
        Nat.choose (a + b) a * b := by
    have h := Nat.choose_mul_succ_eq (a + b - 1) a
    have hs : a + b - 1 + 1 = a + b := by omega
    have hsa : a + b - a = b := by omega
    rw [hs, hsa] at h
    exact h
  have hchoose :
      (Nat.choose (a + b - 1) a : ℚ) * (a + b) =
        (Nat.choose (a + b) a : ℚ) * b := by
    exact_mod_cast hchooseNat
  have hzero : (Nat.choose (a + b) a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right a b)).ne'
  have hzero' : (Nat.choose (a + b - 1) a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos habm).ne'
  have hfrac :
      (b : ℚ) * (Nat.choose (a + b - 1) a : ℚ)⁻¹ =
        (a + b : ℚ) * (Nat.choose (a + b) a : ℚ)⁻¹ := by
    field_simp
    nlinarith [hchoose]
  have hsubNat : n - a - b + (a + b) = n := by omega
  have hsub : ((n - a - b : ℕ) : ℚ) + (a + b : ℚ) = n := by
    exact_mod_cast hsubNat
  rw [pairWeight, pairWeight]
  have harg : a + (b - 1) = a + b - 1 := by omega
  rw [harg, hfrac]
  rw [← add_mul]
  congr 1
  linarith

/--
For one pair `A,B`, summing the changed binomial weight over ground-set
elements outside `A` multiplies the original weight by the ground-set size.
-/
private lemma sum_pairWeight_erase {α : Type*} [DecidableEq α]
    (X A B : Finset α) (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hAB : Disjoint A B) (hB : B.Nonempty) :
    ∑ x ∈ X with x ∉ A, pairWeight A.card (B.erase x).card =
      (X.card : ℚ) * pairWeight A.card B.card := by
  let S := X.filter fun x ↦ x ∉ A
  have hSB : S.filter (fun x ↦ x ∈ B) = B := by
    ext x
    constructor
    · intro hx
      exact (mem_filter.mp hx).2
    · intro hx
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨hBX hx, ?_⟩, hx⟩
      exact fun hxa ↦ Finset.disjoint_left.mp hAB hxa hx
  have hSnotB : S.filter (fun x ↦ x ∉ B) = X \ (A ∪ B) := by
    ext x
    simp [S, and_assoc]
  have hABX : A ∪ B ⊆ X := union_subset hAX hBX
  have hpoint : ∀ x ∈ S,
      pairWeight A.card (B.erase x).card =
        if x ∈ B then pairWeight A.card (B.card - 1)
        else pairWeight A.card B.card := by
    intro x hx
    split_ifs with hxb
    · rw [card_erase_of_mem hxb]
    · rw [erase_eq_of_notMem hxb]
  change ∑ x ∈ S, pairWeight A.card (B.erase x).card = _
  calc
    ∑ x ∈ S, pairWeight A.card (B.erase x).card =
        ∑ x ∈ S,
          if x ∈ B then pairWeight A.card (B.card - 1)
          else pairWeight A.card B.card := by
            exact sum_congr rfl hpoint
    _ = ∑ x ∈ S.filter (fun x ↦ x ∈ B),
            (if x ∈ B then pairWeight A.card (B.card - 1)
              else pairWeight A.card B.card) +
          ∑ x ∈ S.filter (fun x ↦ x ∉ B),
            (if x ∈ B then pairWeight A.card (B.card - 1)
              else pairWeight A.card B.card) :=
            (sum_filter_add_sum_filter_not S (fun x ↦ x ∈ B)
              (fun x ↦ if x ∈ B then pairWeight A.card (B.card - 1)
                else pairWeight A.card B.card)).symm
    _ = ∑ x ∈ S.filter (fun x ↦ x ∈ B), pairWeight A.card (B.card - 1) +
          ∑ x ∈ S.filter (fun x ↦ x ∉ B), pairWeight A.card B.card := by
            congr 1
            · apply sum_congr rfl
              intro x hx
              rw [if_pos (mem_filter.mp hx).2]
            · apply sum_congr rfl
              intro x hx
              rw [if_neg (mem_filter.mp hx).2]
    _ = (B.card : ℚ) * pairWeight A.card (B.card - 1) +
          ((X.card - A.card - B.card : ℕ) : ℚ) * pairWeight A.card B.card := by
            rw [hSB, hSnotB, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
              card_sdiff_of_subset hABX, card_union_of_disjoint hAB]
            rw [Nat.sub_add_eq]
    _ = (X.card : ℚ) * pairWeight A.card B.card := by
            exact pairWeight_erase_identity A.card B.card X.card hB.card_pos
              (by rw [← card_union_of_disjoint hAB]; exact card_le_card hABX)

/--
Bollobás's weighted two-families inequality.  This formulation includes an
explicit finite ground set, which makes the induction constructive and avoids
any appeal to a probability space.
-/
private theorem bollobas_two_families {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (X : Finset α) (A B : ι → Finset α)
    (hAX : ∀ i ∈ I, A i ⊆ X) (hBX : ∀ i ∈ I, B i ⊆ X)
    (hdisj : ∀ i ∈ I, Disjoint (A i) (B i))
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (A i ∩ B j).Nonempty) :
    ∑ i ∈ I, pairWeight (A i).card (B i).card ≤ 1 := by
  classical
  induction X using Finset.strongInductionOn generalizing I A B with
  | _ X ih =>
      by_cases hI : I.card ≤ 1
      · rcases I.eq_empty_or_nonempty with (rfl | ⟨i, hi⟩)
        · simp
        · have hIsingle : I = {i} := by
            ext j
            constructor
            · intro hj
              simpa using (Finset.card_le_one.mp hI j hj i hi)
            · intro hji
              have hji' : j = i := by simpa using hji
              simpa [hji'] using hi
          rw [hIsingle]
          simpa using pairWeight_le_one (A i).card (B i).card
      · have hBne : ∀ i ∈ I, (B i).Nonempty := by
          intro i hi
          by_contra hne
          have hBeq : B i = ∅ := not_nonempty_iff_eq_empty.mp hne
          apply hI
          apply Finset.card_le_one.mpr
          intro j hj k hk
          have hji : j = i := by
            by_contra hji
            simpa [hBeq] using hcross j hj i hi hji
          have hki : k = i := by
            by_contra hki
            simpa [hBeq] using hcross k hk i hi hki
          exact hji.trans hki.symm
        have hXpos : 0 < X.card := by
          have hIpos : 0 < I.card := by omega
          obtain ⟨i, hi⟩ := card_pos.mp hIpos
          obtain ⟨x, hxB⟩ := hBne i hi
          exact card_pos.mpr ⟨x, hBX i hi hxB⟩
        have hone (x : α) (hx : x ∈ X) :
            ∑ i ∈ I.filter (fun i ↦ x ∉ A i),
                pairWeight (A i).card ((B i).erase x).card ≤ 1 := by
          apply ih (X.erase x) (erase_ssubset hx)
              (I.filter (fun i ↦ x ∉ A i)) A (fun i ↦ (B i).erase x)
          · intro i hi
            obtain ⟨hiI, hxi⟩ := mem_filter.mp hi
            intro y hy
            simp only [mem_erase]
            exact ⟨fun hyx ↦ hxi (hyx ▸ hy), hAX i hiI hy⟩
          · intro i hi
            obtain ⟨hiI, -⟩ := mem_filter.mp hi
            intro y hy
            simp only [mem_erase] at hy ⊢
            exact ⟨hy.1, hBX i hiI hy.2⟩
          · intro i hi
            exact (hdisj i (mem_filter.mp hi).1).mono_right (erase_subset _ _)
          · intro i hi j hj hij
            obtain ⟨hiI, hxi⟩ := mem_filter.mp hi
            obtain ⟨hjI, -⟩ := mem_filter.mp hj
            obtain ⟨y, hy⟩ := hcross i hiI j hjI hij
            obtain ⟨hyA, hyB⟩ := mem_inter.mp hy
            refine ⟨y, mem_inter.mpr ⟨hyA, ?_⟩⟩
            exact mem_erase.mpr ⟨fun hyx ↦ hxi (hyx ▸ hyA), hyB⟩
        have hsum :
            ∑ x ∈ X, ∑ i ∈ I.filter (fun i ↦ x ∉ A i),
                pairWeight (A i).card ((B i).erase x).card ≤ (X.card : ℚ) := by
          calc
            ∑ x ∈ X, ∑ i ∈ I.filter (fun i ↦ x ∉ A i),
                pairWeight (A i).card ((B i).erase x).card ≤
                ∑ _x ∈ X, (1 : ℚ) :=
                  sum_le_sum fun x hx ↦ hone x hx
            _ = (X.card : ℚ) := by simp
        have hswap :
            ∑ x ∈ X, ∑ i ∈ I.filter (fun i ↦ x ∉ A i),
                pairWeight (A i).card ((B i).erase x).card =
              ∑ i ∈ I, ∑ x ∈ X with x ∉ A i,
                pairWeight (A i).card ((B i).erase x).card := by
          simp_rw [sum_filter]
          rw [sum_comm]
        rw [hswap] at hsum
        have hweighted :
            (X.card : ℚ) *
                (∑ i ∈ I, pairWeight (A i).card (B i).card) ≤ X.card := by
          rw [mul_sum]
          apply le_of_eq_of_le _ hsum
          apply sum_congr rfl
          intro i hi
          exact (sum_pairWeight_erase X (A i) (B i) (hAX i hi) (hBX i hi)
            (hdisj i hi) (hBne i hi)).symm
        have hXposQ : (0 : ℚ) < X.card := by exact_mod_cast hXpos
        nlinarith

/-! ## The transversal-critical obstruction -/

/-- A deletion witness in a transversally critical three-graph has exactly two
vertices and is disjoint from the exceptional edge. -/
private lemma deletion_witness_exact {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (hunif : IsUniform H 3)
    (hsmall : ∀ T : Finset α, T.card ≤ 2 → ¬Hits H T)
    (e T : Finset α) (he : e ∈ H) (hTcard : T.card ≤ 2)
    (hThits : Hits (H.erase e) T) :
    T.card = 2 ∧ Disjoint e T := by
  have hsem := (hits_iff (H.erase e) T).mp hThits
  have hdisj : Disjoint e T := by
    rw [Finset.disjoint_left]
    intro x hxe hxT
    apply hsmall T hTcard
    apply (hits_iff H T).mpr
    intro f hf
    by_cases hfe : f = e
    · subst f
      exact ⟨x, hxe, hxT⟩
    · exact hsem f (mem_erase.mpr ⟨hfe, hf⟩)
  have hnotone : ¬T.card ≤ 1 := by
    intro hTone
    have hecard : e.card = 3 := (isUniform_iff H 3).mp hunif e he
    have hepos : 0 < e.card := by omega
    obtain ⟨x, hxe⟩ := card_pos.mp hepos
    let T' := insert x T
    have hT'card : T'.card ≤ 2 := by
      dsimp [T']
      exact (card_insert_le x T).trans (by omega)
    apply hsmall T' hT'card
    apply (hits_iff H T').mpr
    intro f hf
    by_cases hfe : f = e
    · subst f
      exact ⟨x, hxe, mem_insert_self x T⟩
    · obtain ⟨y, hyf, hyT⟩ := hsem f (mem_erase.mpr ⟨hfe, hf⟩)
      exact ⟨y, hyf, mem_insert_of_mem hyT⟩
  exact ⟨by omega, hdisj⟩

/-- Li's transversal-critical edge bound, obtained from the two-families
inequality with edge size three and deletion-witness size two. -/
theorem transversalThreeCritical_card_le_ten {α : Type*} [Fintype α]
    [DecidableEq α] (H : Hypergraph α) (hunif : IsUniform H 3)
    (hcrit : TransversalThreeCritical H) : H.card ≤ 10 := by
  classical
  obtain ⟨-, hsmall, hdelete⟩ := (transversalThreeCritical_iff H).mp hcrit
  choose B hBcard hBhits using fun e : ↑H ↦ hdelete e.1 e.2
  have hBexact (e : ↑H) : (B e).card = 2 :=
    (deletion_witness_exact H hunif hsmall e.1 (B e) e.2
      (hBcard e) (hBhits e)).1
  have hdisj (e : ↑H) : Disjoint e.1 (B e) :=
    (deletion_witness_exact H hunif hsmall e.1 (B e) e.2
      (hBcard e) (hBhits e)).2
  have hcross (e f : ↑H) (hef : e ≠ f) : (e.1 ∩ B f).Nonempty := by
    obtain ⟨x, hxe, hxB⟩ := ((hits_iff (H.erase f.1) (B f)).mp (hBhits f)) e.1
      (mem_erase.mpr ⟨Subtype.coe_ne_coe.mpr hef, e.2⟩)
    exact ⟨x, mem_inter.mpr ⟨hxe, hxB⟩⟩
  have hineq := bollobas_two_families
    (Finset.univ : Finset ↑H) (Finset.univ : Finset α)
    (fun e : ↑H ↦ e.1) B
    (by simp) (by simp) (by simpa using hdisj)
    (by intro e _ f _ hef; exact hcross e f hef)
  have hedgecard (e : ↑H) : e.1.card = 3 :=
    (isUniform_iff H 3).mp hunif e.1 e.2
  have hrat : (H.card : ℚ) / 10 ≤ 1 := by
    have hchoose : Nat.choose 5 3 = 10 := by norm_num [Nat.choose]
    simpa [pairWeight, hedgecard, hBexact, hchoose, div_eq_mul_inv] using hineq
  exact_mod_cast (show (H.card : ℚ) ≤ 10 by linarith)

/-- A transversally three-critical three-graph needs at least five ambient
vertices.  On at most four vertices, any two vertices of a fixed triple meet
every triple. -/
private lemma five_le_card_of_transversalThreeCritical {α : Type*} [Fintype α]
    [DecidableEq α] (H : Hypergraph α) (hunif : IsUniform H 3)
    (hcrit : TransversalThreeCritical H) : 5 ≤ Fintype.card α := by
  obtain ⟨-, hsmall, -⟩ := (transversalThreeCritical_iff H).mp hcrit
  have hHne : H.Nonempty := by
    by_contra hne
    apply hsmall ∅ (by simp)
    apply (hits_iff H ∅).mpr
    intro e he
    exact (hne ⟨e, he⟩).elim
  obtain ⟨e, he⟩ := hHne
  have hecard : e.card = 3 := (isUniform_iff H 3).mp hunif e he
  obtain ⟨x, hxe⟩ : e.Nonempty := card_pos.mp (by omega)
  let T := e.erase x
  have hTcard : T.card = 2 := by
    dsimp [T]
    rw [card_erase_of_mem hxe, hecard]
  by_contra hcard
  have hcard' : Fintype.card α ≤ 4 := by omega
  apply hsmall T (by omega)
  apply (hits_iff H T).mpr
  intro f hf
  have hfcard : f.card = 3 := (isUniform_iff H 3).mp hunif f hf
  by_contra hinter
  push Not at hinter
  have hdisj : Disjoint f T := Finset.disjoint_left.mpr hinter
  have hsub : f ∪ T ⊆ (Finset.univ : Finset α) := by simp
  have hle := card_le_card hsub
  rw [card_union_of_disjoint hdisj, hfcard, hTcard, card_univ] at hle
  omega

/-- Double-counting incidences: the sum of vertex degrees is the sum of edge
cardinalities. -/
private lemma sum_degrees_eq_sum_edge_cards {α : Type*} [Fintype α]
    [DecidableEq α] (H : Hypergraph α) :
    ∑ v : α, degree H v = ∑ e ∈ H, e.card := by
  classical
  calc
    ∑ v : α, degree H v =
        ∑ v : α, ∑ e ∈ H, if v ∈ e then 1 else 0 := by
          simp only [degree, Finset.card_filter]
    _ = ∑ e ∈ H, ∑ v : α, if v ∈ e then 1 else 0 := by
          rw [sum_comm]
    _ = ∑ e ∈ H, e.card := by
          apply sum_congr rfl
          intro e he
          rw [← Finset.card_filter]
          simp

/-- The negative resolution under transversal criticality: some vertex has
degree at most six. -/
theorem transversalThreeCritical_exists_degree_le_six {α : Type*} [Fintype α]
    [DecidableEq α] (H : Hypergraph α) (hunif : IsUniform H 3)
    (hcrit : TransversalThreeCritical H) : ∃ v, degree H v ≤ 6 := by
  have hedge : H.card ≤ 10 := transversalThreeCritical_card_le_ten H hunif hcrit
  have hver : 5 ≤ Fintype.card α :=
    five_le_card_of_transversalThreeCritical H hunif hcrit
  have hsum : ∑ v : α, degree H v = H.card * 3 := by
    rw [sum_degrees_eq_sum_edge_cards]
    calc
      ∑ e ∈ H, e.card = ∑ _e ∈ H, 3 := by
        apply sum_congr rfl
        intro e he
        exact (isUniform_iff H 3).mp hunif e he
      _ = H.card * 3 := by
        rw [sum_const, Nat.nsmul_eq_mul]
  by_contra hdegree
  push Not at hdegree
  have hlower : Fintype.card α * 7 ≤ ∑ v : α, degree H v := by
    calc
      Fintype.card α * 7 = ∑ _v : α, 7 := by simp
      _ ≤ ∑ v : α, degree H v :=
        sum_le_sum fun v _ ↦ by
          have hv := hdegree v
          omega
  omega

/-- Consequently no transversal-critical interpretation can satisfy the
minimum-degree-seven requirement from Problem 834. -/
theorem no_transversalThreeCritical_minDegreeSeven {α : Type*} [Fintype α]
    [DecidableEq α] :
    ¬∃ H : Hypergraph α,
      IsUniform H 3 ∧ TransversalThreeCritical H ∧ MinDegreeAtLeast H 7 := by
  rintro ⟨H, hunif, hcrit, hmin⟩
  obtain ⟨v, hv⟩ := transversalThreeCritical_exists_degree_le_six H hunif hcrit
  have := (minDegreeAtLeast_iff H 7).mp hmin v
  omega

/-! ## Li's nine-vertex chromatic example -/

/-- The vertices of Li's example.  Lean vertex `0` is mathematical vertex `1`. -/
abbrev LiVertex := Fin 9

/--
The `22` edges in Li's critically three-chromatic hypergraph.  Each numeral is
one less than the corresponding label in the paper.
-/
def liHypergraph : Hypergraph LiVertex :=
  {
    {0, 1, 2}, {0, 1, 8}, {0, 2, 7}, {0, 3, 5}, {0, 3, 7}, {0, 3, 8},
    {0, 4, 6}, {0, 4, 7}, {0, 4, 8}, {0, 5, 6},
    {1, 2, 5}, {1, 2, 6}, {1, 3, 8}, {1, 4, 8}, {1, 5, 6},
    {2, 3, 7}, {2, 4, 7}, {2, 5, 6},
    {3, 5, 7}, {3, 5, 8}, {4, 6, 7}, {4, 6, 8}
  }

/-- The exact degree vector of Li's example is `(10, 7, ..., 7)`. -/
theorem liHypergraph_degree_vector :
    (List.ofFn (fun v : LiVertex ↦ degree liHypergraph v)) =
      [10, 7, 7, 7, 7, 7, 7, 7, 7] := by
  decide

/-- Every edge in Li's example has exactly three vertices. -/
theorem liHypergraph_isUniform : IsUniform liHypergraph 3 := by
  decide

/-- Li's example has minimum degree exactly seven, in particular at least seven. -/
theorem liHypergraph_minDegreeSeven :
    MinDegreeAtLeast liHypergraph 7 ∧ ∃ v, degree liHypergraph v = 7 := by
  constructor
  · decide
  · exact ⟨1, by decide⟩

/-- The displayed three-coloring from Li's proof. -/
def liThreeColoring (v : LiVertex) : Fin 3 :=
  if v ∈ ({0, 1, 3, 4} : Finset LiVertex) then 0
  else if v = 6 then 2
  else 1

/-- The displayed three-coloring is proper. -/
theorem liThreeColoring_proper : ProperColoring liHypergraph liThreeColoring := by
  decide

/-- The two-coloring whose zero-color class is `blue`. -/
private def coloringFromBlue (blue : Finset LiVertex) (v : LiVertex) : Fin 2 :=
  if v ∈ blue then 0 else 1

/-- Li's displayed edge-deletion certificate, indexed by the deleted edge. -/
private def liEdgeDeletionBlue (e : Finset LiVertex) : Finset LiVertex :=
  if e = {0, 1, 2} then {5, 6, 7, 8}
  else if e = {0, 1, 8} then {2, 3, 4, 5}
  else if e = {0, 2, 7} then {1, 3, 4, 5}
  else if e = {0, 3, 5} then {1, 6, 7, 8}
  else if e = {0, 3, 7} then {2, 4, 5, 8}
  else if e = {0, 3, 8} then {1, 4, 5, 7}
  else if e = {0, 4, 6} then {1, 5, 7, 8}
  else if e = {0, 4, 7} then {2, 3, 6, 8}
  else if e = {0, 4, 8} then {1, 3, 6, 7}
  else if e = {0, 5, 6} then {1, 2, 3, 4}
  else if e = {1, 2, 5} then {0, 6, 7, 8}
  else if e = {1, 2, 6} then {0, 5, 7, 8}
  else if e = {1, 3, 8} then {0, 2, 4, 5}
  else if e = {1, 4, 8} then {0, 2, 3, 6}
  else if e = {1, 5, 6} then {0, 2, 3, 4}
  else if e = {2, 3, 7} then {0, 1, 4, 5}
  else if e = {2, 4, 7} then {0, 1, 3, 6}
  else if e = {2, 5, 6} then {0, 1, 3, 4}
  else if e = {3, 5, 7} then {0, 2, 6, 8}
  else if e = {3, 5, 8} then {0, 1, 6, 7}
  else if e = {4, 6, 7} then {0, 2, 5, 8}
  else {0, 1, 5, 7}

/-- Every listed edge-deletion certificate is a proper coloring. -/
private theorem liEdgeDeletionCertificate :
    ∀ e ∈ liHypergraph,
      ProperColoring (liHypergraph.erase e)
        (coloringFromBlue (liEdgeDeletionBlue e)) := by
  intro e he
  simp only [liHypergraph, mem_insert, mem_singleton] at he
  rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals decide

/-- Li's displayed vertex-deletion certificate. -/
private def liVertexDeletionBlue (v : LiVertex) : Finset LiVertex :=
  if v = 0 then {1, 2, 3, 4}
  else if v = 1 then {0, 2, 3, 4}
  else if v = 2 then {0, 1, 3, 4}
  else if v = 3 then {0, 1, 4, 5}
  else if v = 4 then {0, 1, 3, 6}
  else if v = 5 then {0, 1, 3, 4}
  else if v = 6 then {0, 1, 3, 4}
  else if v = 7 then {0, 1, 3, 6}
  else {0, 1, 5, 7}

/-- Every listed vertex-deletion certificate is a proper coloring. -/
private theorem liVertexDeletionCertificate :
    ∀ v, ProperColoring (deleteVertex liHypergraph v)
      (coloringFromBlue (liVertexDeletionBlue v)) := by
  decide

/-- The propositional core of the non-two-colorability certificate. -/
private theorem liNoTwoColorFormula (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Fin 2)
    (h012 : c0 ≠ c1 ∨ c0 ≠ c2) (h018 : c0 ≠ c1 ∨ c0 ≠ c8)
    (h027 : c0 ≠ c2 ∨ c0 ≠ c7) (h035 : c0 ≠ c3 ∨ c0 ≠ c5)
    (h037 : c0 ≠ c3 ∨ c0 ≠ c7) (h038 : c0 ≠ c3 ∨ c0 ≠ c8)
    (h046 : c0 ≠ c4 ∨ c0 ≠ c6) (h047 : c0 ≠ c4 ∨ c0 ≠ c7)
    (h048 : c0 ≠ c4 ∨ c0 ≠ c8) (h056 : c0 ≠ c5 ∨ c0 ≠ c6)
    (h125 : c1 ≠ c2 ∨ c1 ≠ c5) (h126 : c1 ≠ c2 ∨ c1 ≠ c6)
    (h138 : c1 ≠ c3 ∨ c1 ≠ c8) (h148 : c1 ≠ c4 ∨ c1 ≠ c8)
    (h156 : c1 ≠ c5 ∨ c1 ≠ c6) (h237 : c2 ≠ c3 ∨ c2 ≠ c7)
    (h247 : c2 ≠ c4 ∨ c2 ≠ c7) (h256 : c2 ≠ c5 ∨ c2 ≠ c6)
    (h357 : c3 ≠ c5 ∨ c3 ≠ c7) (h358 : c3 ≠ c5 ∨ c3 ≠ c8)
    (h467 : c4 ≠ c6 ∨ c4 ≠ c7) (h468 : c4 ≠ c6 ∨ c4 ≠ c8) :
    False := by
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2 <;> fin_cases c3 <;>
    fin_cases c4 <;> fin_cases c5 <;> fin_cases c6 <;> fin_cases c7 <;>
    fin_cases c8 <;> simp_all

/-- A proper coloring of a listed triple gives one of the two inequalities
from its first vertex. -/
private lemma proper_triple_inequality (c : LiVertex → Fin 2)
    (a b d : LiVertex) (hproper : ProperColoring liHypergraph c)
    (hedge : ({a, b, d} : Finset LiVertex) ∈ liHypergraph) :
    c a ≠ c b ∨ c a ≠ c d := by
  have h := (properColoring_iff liHypergraph c).mp hproper {a, b, d} hedge
  simp at h
  by_contra hne
  push Not at hne
  obtain ⟨hab, had⟩ := hne
  have hbd : c b = c d := hab.symm.trans had
  simp [hab, hbd] at h

/-- Li's hypergraph has no proper two-coloring. -/
private theorem liHypergraph_not_twoColorable_direct :
    ¬Colorable liHypergraph 2 := by
  rw [colorable_iff]
  rintro ⟨c, hc⟩
  exact liNoTwoColorFormula (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8)
    (proper_triple_inequality c 0 1 2 hc (by decide))
    (proper_triple_inequality c 0 1 8 hc (by decide))
    (proper_triple_inequality c 0 2 7 hc (by decide))
    (proper_triple_inequality c 0 3 5 hc (by decide))
    (proper_triple_inequality c 0 3 7 hc (by decide))
    (proper_triple_inequality c 0 3 8 hc (by decide))
    (proper_triple_inequality c 0 4 6 hc (by decide))
    (proper_triple_inequality c 0 4 7 hc (by decide))
    (proper_triple_inequality c 0 4 8 hc (by decide))
    (proper_triple_inequality c 0 5 6 hc (by decide))
    (proper_triple_inequality c 1 2 5 hc (by decide))
    (proper_triple_inequality c 1 2 6 hc (by decide))
    (proper_triple_inequality c 1 3 8 hc (by decide))
    (proper_triple_inequality c 1 4 8 hc (by decide))
    (proper_triple_inequality c 1 5 6 hc (by decide))
    (proper_triple_inequality c 2 3 7 hc (by decide))
    (proper_triple_inequality c 2 4 7 hc (by decide))
    (proper_triple_inequality c 2 5 6 hc (by decide))
    (proper_triple_inequality c 3 5 7 hc (by decide))
    (proper_triple_inequality c 3 5 8 hc (by decide))
    (proper_triple_inequality c 4 6 7 hc (by decide))
    (proper_triple_inequality c 4 6 8 hc (by decide))

/-- Li's example is weakly chromatically three-critical. -/
theorem liHypergraph_chromaticThreeCritical :
    ChromaticThreeCritical liHypergraph := by
  apply (chromaticThreeCritical_iff liHypergraph).mpr
  refine ⟨(colorable_iff liHypergraph 3).mpr ⟨liThreeColoring,
    liThreeColoring_proper⟩, liHypergraph_not_twoColorable_direct, ?_, ?_⟩
  · intro e he
    exact (colorable_iff (liHypergraph.erase e) 2).mpr
      ⟨coloringFromBlue (liEdgeDeletionBlue e), liEdgeDeletionCertificate e he⟩
  · intro v
    exact (colorable_iff (deleteVertex liHypergraph v) 2).mpr
      ⟨coloringFromBlue (liVertexDeletionBlue v), liVertexDeletionCertificate v⟩

/-- Li's example has no weakly proper two-coloring. -/
theorem liHypergraph_not_twoColorable : ¬Colorable liHypergraph 2 := by
  have h := (chromaticThreeCritical_iff liHypergraph).mp
    liHypergraph_chromaticThreeCritical
  exact h.2.1

/-- Deleting any edge of Li's example makes it two-colorable. -/
theorem liHypergraph_edgeCritical :
    ∀ e ∈ liHypergraph, Colorable (liHypergraph.erase e) 2 := by
  have h := (chromaticThreeCritical_iff liHypergraph).mp
    liHypergraph_chromaticThreeCritical
  exact h.2.2.1

/-- Deleting any vertex of Li's example makes it two-colorable. -/
theorem liHypergraph_vertexCritical :
    ∀ v, Colorable (deleteVertex liHypergraph v) 2 := by
  have h := (chromaticThreeCritical_iff liHypergraph).mp
    liHypergraph_chromaticThreeCritical
  exact h.2.2.2

/--
The affirmative resolution of Problem 834 under weak chromatic criticality.
-/
theorem exists_chromaticThreeCritical_minDegreeSeven :
    ∃ H : Hypergraph (Fin 9),
      IsUniform H 3 ∧ ChromaticThreeCritical H ∧ MinDegreeAtLeast H 7 := by
  exact ⟨liHypergraph, liHypergraph_isUniform,
    liHypergraph_chromaticThreeCritical, liHypergraph_minDegreeSeven.1⟩

/-! ## Sharpness example for transversal criticality -/

/-- The complete `3`-uniform hypergraph on five vertices. -/
def completeThreeGraphFive : Hypergraph (Fin 5) :=
  (Finset.univ : Finset (Fin 5)).powersetCard 3

/-- Every edge of the complete three-graph on five vertices has size three. -/
theorem completeThreeGraphFive_isUniform : IsUniform completeThreeGraphFive 3 := by
  decide

/-- The complete three-graph on five vertices is transversally three-critical. -/
theorem completeThreeGraphFive_transversalThreeCritical :
    TransversalThreeCritical completeThreeGraphFive := by
  decide

/-- The complete three-graph on five vertices is six-regular. -/
theorem completeThreeGraphFive_degree :
    ∀ v, degree completeThreeGraphFive v = 6 := by
  decide

/-- The complete three-graph on five vertices realizes the sharp degree six bound. -/
theorem completeThreeGraphFive_properties :
    IsUniform completeThreeGraphFive 3 ∧
      TransversalThreeCritical completeThreeGraphFive ∧
      (∀ v, degree completeThreeGraphFive v = 6) :=
  ⟨completeThreeGraphFive_isUniform,
    completeThreeGraphFive_transversalThreeCritical,
    completeThreeGraphFive_degree⟩

/-!
The complete formal resolution records the opposite answers forced by the two
standard meanings of `3`-critical: existence for weak chromatic criticality,
and the sharp degree-six obstruction for transversal criticality.
-/
theorem erdos_834 :
    (∃ H : Hypergraph (Fin 9),
      IsUniform H 3 ∧ ChromaticThreeCritical H ∧ MinDegreeAtLeast H 7) ∧
    (∀ (α : Type) [Fintype α] [DecidableEq α] (H : Hypergraph α),
      IsUniform H 3 → TransversalThreeCritical H →
        ∃ v, degree H v ≤ 6) := by
  constructor
  · exact exists_chromaticThreeCritical_minDegreeSeven
  · intro α _ _ H hunif hcrit
    exact transversalThreeCritical_exists_degree_le_six H hunif hcrit

end Erdos834

#print axioms Erdos834.erdos_834
#print axioms Erdos834.transversalThreeCritical_exists_degree_le_six

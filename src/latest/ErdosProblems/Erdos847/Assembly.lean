/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Assembly of separated finite blocks for Erdős 847

This file isolates the elementary infinitary assembly step.  The genuinely
combinatorial input is a sequence of finite blocks with a Ramsey property and
a hereditary positive-density independent-set property.  We translate those
blocks far apart, so that no three-term progression can use two blocks.
-/

namespace Erdos847Assembly

open Set
open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- A nonconstant monochromatic three-term arithmetic progression. -/
def HasMonochromaticThreeAP (A : Set ℕ) {r : ℕ} (color : ℕ → Fin r) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a + c = b + b ∧ a ≠ c ∧ color a = color b ∧ color b = color c

/-- Every nonempty finite coloring contains a monochromatic three-AP. -/
def RamseyForThreeAP (A : Set ℕ) : Prop :=
  ∀ r : ℕ, 0 < r → ∀ color : ℕ → Fin r, HasMonochromaticThreeAP A color

/-- The pair of global properties needed for the negative answer. -/
def IsRRSCounterexample (A : Set ℕ) (mu : ℝ) : Prop :=
  RamseyForThreeAP A ∧
    ∀ B : Set ℕ, B ⊆ A → B.Finite →
      ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ mu * B.ncard ∧ ThreeAPFree C

/-- The largest entry of a finite block (zero for the empty block). -/
def blockMax (X : ℕ → Finset ℕ) (n : ℕ) : ℕ := (X n).sup id

/-- `cap X n` is an upper bound for all translated blocks with index `< n`. -/
def cap (X : ℕ → Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * cap X n + 2 * blockMax X n + 1

/-- Translation used for block `n`.  The extra `blockMax` term prevents a
progression with two points in the new block and one point in the old union. -/
def offset (X : ℕ → Finset ℕ) (n : ℕ) : ℕ :=
  2 * cap X n + blockMax X n + 1

/-- Translate a finite subset of the `n`-th raw block. -/
def translate (X : ℕ → Finset ℕ) (n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => offset X n + x

/-- The translated `n`-th block. -/
def placed (X : ℕ → Finset ℕ) (n : ℕ) : Finset ℕ := translate X n (X n)

/-- The infinite union of the translated blocks. -/
def assembled (X : ℕ → Finset ℕ) : Set ℕ := ⋃ n, (placed X n : Set ℕ)

lemma le_blockMax {X : ℕ → Finset ℕ} {n x : ℕ} (hx : x ∈ X n) : x ≤ blockMax X n := by
  exact Finset.le_sup (f := id) hx

lemma cap_step (X : ℕ → Finset ℕ) (n : ℕ) :
    cap X (n + 1) = 2 * cap X n + 2 * blockMax X n + 1 := by
  rfl

lemma cap_le_succ (X : ℕ → Finset ℕ) (n : ℕ) : cap X n ≤ cap X (n + 1) := by
  rw [cap_step]
  omega

lemma cap_mono (X : ℕ → Finset ℕ) : Monotone (cap X) :=
  monotone_nat_of_le_succ (cap_le_succ X)

lemma offset_separated (X : ℕ → Finset ℕ) (n : ℕ) :
    2 * cap X n + blockMax X n < offset X n := by
  simp [offset]

lemma mem_translate_iff {X : ℕ → Finset ℕ} {n : ℕ} {S : Finset ℕ} {y : ℕ} :
    y ∈ translate X n S ↔ ∃ x ∈ S, offset X n + x = y := by
  simp [translate]

lemma translate_lower {X : ℕ → Finset ℕ} {n : ℕ} {S : Finset ℕ} {y : ℕ}
    (hy : y ∈ translate X n S) : offset X n ≤ y := by
  obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hy
  omega

lemma translate_upper {X : ℕ → Finset ℕ} {n : ℕ} {S : Finset ℕ} {y : ℕ}
    (hSX : S ⊆ X n) (hy : y ∈ translate X n S) : y ≤ cap X (n + 1) := by
  obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hy
  have hxmax := le_blockMax (hSX hx)
  simp only [offset, cap_step]
  omega

lemma translate_upper_short {X : ℕ → Finset ℕ} {n : ℕ} {S : Finset ℕ} {y : ℕ}
    (hSX : S ⊆ X n) (hy : y ∈ translate X n S) :
    y ≤ offset X n + blockMax X n := by
  obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hy
  have hxmax := le_blockMax (hSX hx)
  omega

lemma translate_injective (X : ℕ → Finset ℕ) (n : ℕ) :
    Function.Injective (fun x : ℕ => offset X n + x) := by
  intro a b h
  exact Nat.add_left_cancel h

@[simp] lemma card_translate (X : ℕ → Finset ℕ) (n : ℕ) (S : Finset ℕ) :
    (translate X n S).card = S.card := by
  exact Finset.card_image_of_injective S (translate_injective X n)

lemma translate_subset_translate {X : ℕ → Finset ℕ} {n : ℕ} {S T : Finset ℕ}
    (hST : S ⊆ T) : translate X n S ⊆ translate X n T := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hy
  exact mem_translate_iff.mpr ⟨x, hST hx, rfl⟩

lemma threeAPFree_translate {X : ℕ → Finset ℕ} {n : ℕ} {S : Finset ℕ}
    (hS : ThreeAPFree (S : Set ℕ)) : ThreeAPFree (translate X n S : Set ℕ) := by
  rw [threeAPFree_iff_eq_right] at hS ⊢
  intro a ha b hb c hc habc
  obtain ⟨a', ha', rfl⟩ := mem_translate_iff.mp ha
  obtain ⟨b', hb', rfl⟩ := mem_translate_iff.mp hb
  obtain ⟨c', hc', rfl⟩ := mem_translate_iff.mp hc
  congr 1
  apply hS ha' hb' hc'
  omega

/-- Two 3-AP-free finite sets remain 3-AP-free when the second lies in an
interval `[L,L+M]` and the first below `U`, provided `L > 2U+M`. -/
lemma threeAPFree_union_of_separated {S T : Finset ℕ} {U M L : ℕ}
    (hS : ThreeAPFree (S : Set ℕ)) (hT : ThreeAPFree (T : Set ℕ))
    (hSupper : ∀ x ∈ S, x ≤ U)
    (hTlower : ∀ x ∈ T, L ≤ x)
    (hTupper : ∀ x ∈ T, x ≤ L + M)
    (hsep : 2 * U + M < L) :
    ThreeAPFree ((S ∪ T : Finset ℕ) : Set ℕ) := by
  rw [threeAPFree_iff_eq_right] at hS hT ⊢
  intro a ha b hb c hc habc
  simp only [Finset.mem_coe, Finset.mem_union] at ha hb hc
  rcases ha with haS | haT <;> rcases hb with hbS | hbT <;> rcases hc with hcS | hcT
  · exact hS haS hbS hcS habc
  · have haU := hSupper a haS
    have hbU := hSupper b hbS
    have hcL := hTlower c hcT
    omega
  · have haU := hSupper a haS
    have hbL := hTlower b hbT
    have hcU := hSupper c hcS
    omega
  · have haU := hSupper a haS
    have hbL := hTlower b hbT
    have hcL := hTlower c hcT
    have hcTop := hTupper c hcT
    omega
  · have haL := hTlower a haT
    have hbU := hSupper b hbS
    have hcU := hSupper c hcS
    omega
  · have haL := hTlower a haT
    have haTop := hTupper a haT
    have hbU := hSupper b hbS
    have hcL := hTlower c hcT
    omega
  · have haL := hTlower a haT
    have haTop := hTupper a haT
    have hbL := hTlower b hbT
    have hcU := hSupper c hcS
    omega
  · exact hT haT hbT hcT habc

/-- Union of the first `n` translated finite subsets. -/
def blockPrefix (X D : ℕ → Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).biUnion fun i => translate X i (D i)

lemma blockPrefix_succ (X D : ℕ → Finset ℕ) (n : ℕ) :
    blockPrefix X D (n + 1) = translate X n (D n) ∪ blockPrefix X D n := by
  simp [blockPrefix, Finset.range_add_one]

lemma blockPrefix_upper {X D : ℕ → Finset ℕ} (hDX : ∀ i, D i ⊆ X i) {n y : ℕ}
    (hy : y ∈ blockPrefix X D n) : y ≤ cap X n := by
  obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hy
  have hi' : i + 1 ≤ n := by simpa using (Finset.mem_range.mp hi)
  exact (translate_upper (hDX i) hyi).trans (cap_mono X hi')

lemma disjoint_translate_of_lt {X D : ℕ → Finset ℕ} (hDX : ∀ i, D i ⊆ X i)
    {i j : ℕ} (hij : i < j) : Disjoint (translate X i (D i)) (translate X j (D j)) := by
  rw [Finset.disjoint_left]
  intro y hyi hyj
  have hycap : y ≤ cap X j :=
    (translate_upper (hDX i) hyi).trans (cap_mono X (by omega))
  have hyoff : offset X j ≤ y := translate_lower hyj
  have hsep := offset_separated X j
  omega

lemma pairwiseDisjoint_translate {X D : ℕ → Finset ℕ} (hDX : ∀ i, D i ⊆ X i)
    (s : Finset ℕ) : (s : Set ℕ).PairwiseDisjoint fun i => translate X i (D i) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact disjoint_translate_of_lt hDX hij'
  · exact (disjoint_translate_of_lt hDX hji').symm

/-- Every finite prefix of translated 3-AP-free subsets is still 3-AP-free. -/
lemma threeAPFree_blockPrefix {X D : ℕ → Finset ℕ} (hDX : ∀ i, D i ⊆ X i)
    (hDfree : ∀ i, ThreeAPFree (D i : Set ℕ)) :
    ∀ n, ThreeAPFree (blockPrefix X D n : Set ℕ) := by
  intro n
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
      rw [blockPrefix_succ]
      rw [Finset.union_comm]
      apply threeAPFree_union_of_separated (U := cap X n) (M := blockMax X n)
        (L := offset X n) ih (threeAPFree_translate (hDfree n))
      · intro y hy
        exact blockPrefix_upper hDX hy
      · intro y hy
        exact translate_lower hy
      · intro y hy
        exact translate_upper_short (hDX n) hy
      ·
        exact offset_separated X n

/-- Union of a subset chosen from every translated block. -/
def assembledSubsets (X D : ℕ → Finset ℕ) : Set ℕ :=
  ⋃ n, (translate X n (D n) : Set ℕ)

lemma mem_assembledSubsets_iff {X D : ℕ → Finset ℕ} {y : ℕ} :
    y ∈ assembledSubsets X D ↔ ∃ n, y ∈ translate X n (D n) := by
  simp [assembledSubsets]

lemma mem_blockPrefix_of_mem_translate {X D : ℕ → Finset ℕ} {i n y : ℕ}
    (hi : i < n) (hy : y ∈ translate X i (D i)) : y ∈ blockPrefix X D n := by
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hy⟩

/-- Arbitrary (not necessarily finite) unions of blockwise 3-AP-free choices
are 3-AP-free, because any three points lie in one finite prefix. -/
lemma threeAPFree_assembledSubsets {X D : ℕ → Finset ℕ} (hDX : ∀ i, D i ⊆ X i)
    (hDfree : ∀ i, ThreeAPFree (D i : Set ℕ)) :
    ThreeAPFree (assembledSubsets X D) := by
  rw [threeAPFree_iff_eq_right]
  intro a ha b hb c hc habc
  obtain ⟨ia, ha⟩ := mem_assembledSubsets_iff.mp ha
  obtain ⟨ib, hb⟩ := mem_assembledSubsets_iff.mp hb
  obtain ⟨ic, hc⟩ := mem_assembledSubsets_iff.mp hc
  let n := max ia (max ib ic) + 1
  apply (threeAPFree_iff_eq_right.mp (threeAPFree_blockPrefix hDX hDfree n))
    (mem_blockPrefix_of_mem_translate (by simp [n]) ha)
    (mem_blockPrefix_of_mem_translate (by simp [n]) hb)
    (mem_blockPrefix_of_mem_translate (by simp [n]) hc)
    habc

/-- Finite-block Ramsey input.  Only the block with index `r` is used against
an `r`-coloring. -/
def BlockRamsey (X : ℕ → Finset ℕ) : Prop :=
  ∀ r : ℕ, ∀ color : ℕ → Fin r, HasMonochromaticThreeAP (X r : Set ℕ) color

/-- Hereditary density input on every raw block. -/
def BlockDense (X : ℕ → Finset ℕ) (mu : ℝ) : Prop :=
  ∀ i : ℕ, ∀ B : Finset ℕ, B ⊆ X i →
    ∃ C : Finset ℕ, C ⊆ B ∧ (C.card : ℝ) ≥ mu * B.card ∧
      ThreeAPFree (C : Set ℕ)

lemma assembled_eq_subsets (X : ℕ → Finset ℕ) : assembled X = assembledSubsets X X := by
  rfl

/-- A monochromatic progression in raw block `r` translates to one in the
assembled set. -/
lemma ramseyForThreeAP_assembled {X : ℕ → Finset ℕ} (hRamsey : BlockRamsey X) :
    RamseyForThreeAP (assembled X) := by
  intro r hr color
  obtain ⟨a, ha, b, hb, c, hc, habc, hac, hab, hbc⟩ :=
    hRamsey r (fun x => color (offset X r + x))
  refine ⟨offset X r + a, ?_, offset X r + b, ?_, offset X r + c, ?_, ?_, ?_, hab, hbc⟩
  · exact Set.mem_iUnion.mpr ⟨r, mem_translate_iff.mpr ⟨a, ha, rfl⟩⟩
  · exact Set.mem_iUnion.mpr ⟨r, mem_translate_iff.mpr ⟨b, hb, rfl⟩⟩
  · exact Set.mem_iUnion.mpr ⟨r, mem_translate_iff.mpr ⟨c, hc, rfl⟩⟩
  · omega
  · intro h
    exact hac (Nat.add_left_cancel h)

lemma index_le_cap (X : ℕ → Finset ℕ) : ∀ n, n ≤ cap X n := by
  intro n
  induction n with
  | zero => simp [cap]
  | succ n ih =>
      rw [cap_step]
      omega

lemma cap_lt_offset (X : ℕ → Finset ℕ) (n : ℕ) : cap X n < offset X n := by
  have := offset_separated X n
  omega

lemma assembled_unbounded {X : ℕ → Finset ℕ} (hXne : ∀ i, (X i).Nonempty) (N : ℕ) :
    ∃ y ∈ assembled X, N < y := by
  obtain ⟨x, hx⟩ := hXne (N + 1)
  refine ⟨offset X (N + 1) + x, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨N + 1, mem_translate_iff.mpr ⟨x, hx, rfl⟩⟩
  · have hcap := index_le_cap X (N + 1)
    have hoff := cap_lt_offset X (N + 1)
    omega

lemma assembled_infinite {X : ℕ → Finset ℕ} (hXne : ∀ i, (X i).Nonempty) :
    (assembled X).Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.exists_le
  obtain ⟨y, hy, hNy⟩ := assembled_unbounded hXne N
  exact (not_lt_of_ge (hN y hy)) hNy

/-- The hereditary density property survives assembly.  A finite `B` meets
only finitely many translated blocks; extract in every raw fiber and add the
cardinality inequalities, using disjointness of the translated intervals. -/
lemma dense_assembled {X : ℕ → Finset ℕ} {mu : ℝ} (hDense : BlockDense X mu) :
    ∀ B : Set ℕ, B ⊆ assembled X → B.Finite →
      ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ mu * B.ncard ∧ ThreeAPFree C := by
  intro B hBA hBfin
  let BF : Finset ℕ := hBfin.toFinset
  have hBcover : B ⊆ ⋃ i, (placed X i : Set ℕ) := by
    simpa [assembled] using hBA
  obtain ⟨I, hIfin, hBI⟩ := finite_subset_iUnion hBfin hBcover
  let IF : Finset ℕ := hIfin.toFinset
  let P : ℕ → Finset ℕ := fun i =>
    (X i).filter fun x => offset X i + x ∈ BF
  have hPX : ∀ i, P i ⊆ X i := by
    intro i x hx
    exact (Finset.mem_filter.mp hx).1
  have hBFunion : BF = IF.biUnion fun i => translate X i (P i) := by
    ext y
    constructor
    · intro hy
      have hyB : y ∈ B := by simpa [BF] using hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hBI hyB)
      obtain ⟨hiI, hyplace⟩ := Set.mem_iUnion.mp hi
      change y ∈ translate X i (X i) at hyplace
      obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hyplace
      apply Finset.mem_biUnion.mpr
      refine ⟨i, ?_, mem_translate_iff.mpr ⟨x, ?_, rfl⟩⟩
      · simpa [IF] using hiI
      · exact Finset.mem_filter.mpr ⟨hx, hy⟩
    · intro hy
      obtain ⟨i, hiI, hyi⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hyi
      exact (Finset.mem_filter.mp hx).2
  have hBcard : BF.card = ∑ i ∈ IF, (P i).card := by
    calc
      BF.card = (IF.biUnion fun i => translate X i (P i)).card :=
        congrArg Finset.card hBFunion
      _ = ∑ i ∈ IF, (translate X i (P i)).card :=
        Finset.card_biUnion (pairwiseDisjoint_translate hPX IF)
      _ = ∑ i ∈ IF, (P i).card := by simp
  let D : ℕ → Finset ℕ := fun i => Classical.choose (hDense i (P i) (hPX i))
  have hDspec (i : ℕ) :
      D i ⊆ P i ∧ (D i).card ≥ mu * (P i).card ∧ ThreeAPFree (D i : Set ℕ) := by
    exact Classical.choose_spec (hDense i (P i) (hPX i))
  have hDP : ∀ i, D i ⊆ P i := fun i => (hDspec i).1
  have hDX : ∀ i, D i ⊆ X i := fun i => (hDP i).trans (hPX i)
  have hDcard : ∀ i, (D i).card ≥ mu * (P i).card := fun i => (hDspec i).2.1
  have hDfree : ∀ i, ThreeAPFree (D i : Set ℕ) := fun i => (hDspec i).2.2
  let CF : Finset ℕ := IF.biUnion fun i => translate X i (D i)
  have hCFsubset : CF ⊆ BF := by
    intro y hy
    obtain ⟨i, hiI, hyi⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hyi
    exact (Finset.mem_filter.mp (hDP i hx)).2
  have hCcard : CF.card = ∑ i ∈ IF, (D i).card := by
    calc
      CF.card = (IF.biUnion fun i => translate X i (D i)).card := rfl
      _ = ∑ i ∈ IF, (translate X i (D i)).card :=
        Finset.card_biUnion (pairwiseDisjoint_translate hDX IF)
      _ = ∑ i ∈ IF, (D i).card := by simp
  have hsum :
      ∑ i ∈ IF, mu * ((P i).card : ℝ) ≤ ∑ i ∈ IF, ((D i).card : ℝ) := by
    exact Finset.sum_le_sum fun i hi => hDcard i
  have hcardineq : (CF.card : ℝ) ≥ mu * (BF.card : ℝ) := by
    rw [hCcard, hBcard]
    simp only [Nat.cast_sum, Finset.mul_sum]
    exact hsum
  have hCFfree : ThreeAPFree (CF : Set ℕ) := by
    apply (threeAPFree_assembledSubsets hDX hDfree).mono
    intro y hy
    obtain ⟨i, hiI, hyi⟩ := Finset.mem_biUnion.mp hy
    exact mem_assembledSubsets_iff.mpr ⟨i, hyi⟩
  refine ⟨(CF : Set ℕ), ?_, ?_, hCFfree⟩
  · intro y hy
    have : y ∈ BF := hCFsubset hy
    simpa [BF] using this
  · simpa [BF, Set.ncard_eq_toFinset_card B hBfin] using hcardineq

/-- Complete elementary assembly theorem. -/
theorem isRRSCounterexample_assembled {X : ℕ → Finset ℕ} {mu : ℝ}
    (hRamsey : BlockRamsey X) (hDense : BlockDense X mu) :
    IsRRSCounterexample (assembled X) mu := by
  exact ⟨ramseyForThreeAP_assembled hRamsey, dense_assembled hDense⟩

/-- Nonempty finite blocks therefore give an infinite global counterexample. -/
theorem infinite_and_isRRSCounterexample_assembled {X : ℕ → Finset ℕ} {mu : ℝ}
    (hXne : ∀ i, (X i).Nonempty) (hRamsey : BlockRamsey X) (hDense : BlockDense X mu) :
    (assembled X).Infinite ∧ IsRRSCounterexample (assembled X) mu := by
  exact ⟨assembled_infinite hXne, isRRSCounterexample_assembled hRamsey hDense⟩

theorem exists_infinite_isRRSCounterexample {X : ℕ → Finset ℕ} {mu : ℝ}
    (hXne : ∀ i, (X i).Nonempty) (hRamsey : BlockRamsey X) (hDense : BlockDense X mu) :
    ∃ A : Set ℕ, A.Infinite ∧ IsRRSCounterexample A mu := by
  exact ⟨assembled X, infinite_and_isRRSCounterexample_assembled hXne hRamsey hDense⟩

end Erdos847Assembly

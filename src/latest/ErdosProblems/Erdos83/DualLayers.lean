import ErdosProblems.Erdos83.Prefix
import ErdosProblems.Erdos83.Counting

/-!
# Duality and two-block layers for Erdős Problem 83

This module contains the part of the proof after prefix symmetrisation.  Reversed
complementation transports first-block invariance to the second block.  The two
block invariances then show that a compressed family consists of whole layers;
compression makes the present layers upward closed, while two-intersection
excludes the middle layer.
-/

namespace Erdos83

open Finset

attribute [local instance] Classical.propDecidable

/-- Order reversal on `Fin N`. -/
def reverseFin {N : ℕ} (x : Fin N) : Fin N :=
  ⟨N - 1 - x.1, by omega⟩

@[simp] lemma reverseFin_val {N : ℕ} (x : Fin N) :
    (reverseFin x).1 = N - 1 - x.1 := rfl

@[simp] lemma reverseFin_reverseFin {N : ℕ} (x : Fin N) :
    reverseFin (reverseFin x) = x := by
  ext
  simp [reverseFin]
  omega

/-- Order reversal as an equivalence. -/
def reverseFinEquiv (N : ℕ) : Fin N ≃ Fin N where
  toFun := reverseFin
  invFun := reverseFin
  left_inv := reverseFin_reverseFin
  right_inv := reverseFin_reverseFin

@[simp] lemma reverseFinEquiv_apply {N : ℕ} (x : Fin N) :
    reverseFinEquiv N x = reverseFin x := rfl

@[simp] lemma reverseFinEquiv_symm (N : ℕ) :
    (reverseFinEquiv N).symm = reverseFinEquiv N := by
  rfl

/-- Reversed complement of a finite set. -/
def dualSet {N : ℕ} (A : Finset (Fin N)) : Finset (Fin N) :=
  Aᶜ.map (reverseFinEquiv N).toEmbedding

/-- Reversed complement of every member of a family. -/
def dualFamily {N : ℕ} (F : Finset (Finset (Fin N))) :
    Finset (Finset (Fin N)) :=
  F.image dualSet

@[simp] lemma mem_dualSet {N : ℕ} {A : Finset (Fin N)} {x : Fin N} :
    x ∈ dualSet A ↔ reverseFin x ∉ A := by
  simp [dualSet, reverseFinEquiv]

@[simp] lemma card_dualSet {N : ℕ} (A : Finset (Fin N)) :
    (dualSet A).card = N - A.card := by
  simp only [dualSet, Finset.card_map, Finset.card_compl, Fintype.card_fin]

@[simp] lemma dualSet_dualSet {N : ℕ} (A : Finset (Fin N)) :
    dualSet (dualSet A) = A := by
  ext x
  simp

lemma dualSet_injective {N : ℕ} : Function.Injective (@dualSet N) := by
  intro A B h
  simpa only [dualSet_dualSet] using congrArg dualSet h

@[simp] lemma mem_dualFamily {N : ℕ} {F : Finset (Finset (Fin N))}
    {A : Finset (Fin N)} :
    A ∈ dualFamily F ↔ dualSet A ∈ F := by
  rw [dualFamily, Finset.mem_image]
  constructor
  · rintro ⟨B, hBF, rfl⟩
    simpa using hBF
  · intro hA
    exact ⟨dualSet A, hA, dualSet_dualSet A⟩

@[simp] lemma card_dualFamily {N : ℕ} (F : Finset (Finset (Fin N))) :
    (dualFamily F).card = F.card := by
  exact Finset.card_image_iff.mpr dualSet_injective.injOn

@[simp] lemma dualFamily_dualFamily {N : ℕ} (F : Finset (Finset (Fin N))) :
    dualFamily (dualFamily F) = F := by
  ext A
  simp

/-- Reversed complementation preserves the middle uniform layer. -/
lemma Uniform.dualFamily {N k : ℕ} {F : Finset (Finset (Fin N))}
    (hF : Uniform k F) (hN : N = 2 * k) :
    Uniform k (dualFamily F) := by
  intro A hA
  have hdual : (dualSet A).card = k := hF (mem_dualFamily.mp hA)
  have hle : A.card ≤ N := by
    simpa using Finset.card_le_card (Finset.subset_univ A)
  rw [card_dualSet] at hdual
  omega

/-- On the middle layer, reversed complementation preserves intersection
cardinality. -/
lemma card_dualSet_inter_dualSet {N k : ℕ}
    (hN : N = 2 * k) (A B : Finset (Fin N))
    (hA : A.card = k) (hB : B.card = k) :
    (dualSet A ∩ dualSet B).card = (A ∩ B).card := by
  have heq :
      dualSet A ∩ dualSet B =
        (Aᶜ ∩ Bᶜ).map (reverseFinEquiv N).toEmbedding := by
    ext x
    simp
  have hcompl : Aᶜ ∩ Bᶜ = (A ∪ B)ᶜ := by
    ext x
    simp
  have hunion := Finset.card_union_add_card_inter A B
  rw [heq, Finset.card_map, hcompl, Finset.card_compl]
  simp only [Fintype.card_fin]
  omega

/-- Reversed complementation preserves two-intersection on the middle layer. -/
lemma TwoIntersecting.dualFamily {N k : ℕ}
    {F : Finset (Finset (Fin N))} (hinter : TwoIntersecting F)
    (hN : N = 2 * k) (hunif : Uniform k F) :
    TwoIntersecting (dualFamily F) := by
  intro A B hA hB
  have hdualA : dualSet A ∈ F := mem_dualFamily.mp hA
  have hdualB : dualSet B ∈ F := mem_dualFamily.mp hB
  calc
    2 ≤ (dualSet A ∩ dualSet B).card := hinter hdualA hdualB
    _ = (A ∩ B).card := by
      symm
      simpa using card_dualSet_inter_dualSet hN (dualSet A) (dualSet B)
        (hunif hdualA) (hunif hdualB)

/-- Maximality by cardinality is preserved by reversed complementation. -/
lemma maximal_dualFamily {N k : ℕ} (hN : N = 2 * k)
    {F : Finset (Finset (Fin N))}
    (hunif : Uniform k F) (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin N)),
      Uniform k G → TwoIntersecting G → G.card ≤ F.card) :
    ∀ G : Finset (Finset (Fin N)),
      Uniform k G → TwoIntersecting G → G.card ≤ (dualFamily F).card := by
  intro G hGunif hGinter
  rw [card_dualFamily]
  simpa using hmax (dualFamily G) (hGunif.dualFamily hN)
    (hGinter.dualFamily hN hGunif)

lemma reverseFin_lt_reverseFin {N : ℕ} {i j : Fin N} (hij : i < j) :
    reverseFin j < reverseFin i := by
  simp only [Fin.lt_iff_val_lt_val, reverseFin_val]
  omega

private lemma reverseFin_swap {N : ℕ} (i j x : Fin N) :
    Equiv.swap (reverseFin j) (reverseFin i) (reverseFin x) =
      reverseFin (Equiv.swap i j x) := by
  rw [Equiv.swap_comm]
  exact (reverseFinEquiv N).injective.swap_apply i j x

lemma dualSet_setTranspose {N : ℕ} (i j : Fin N) (A : Finset (Fin N)) :
    dualSet (setTranspose i j A) =
      setTranspose (reverseFin j) (reverseFin i) (dualSet A) := by
  ext x
  simp only [mem_dualSet, mem_setTranspose]
  have hswap : Equiv.swap i j (reverseFin x) =
      reverseFin (Equiv.swap (reverseFin j) (reverseFin i) x) := by
    simpa using reverseFin_swap (reverseFin j) (reverseFin i) x
  rw [hswap]

lemma dualSet_singletonLeftShift {N : ℕ} (i j : Fin N)
    (A : Finset (Fin N)) :
    dualSet (singletonLeftShift i j A) =
      singletonLeftShift (reverseFin j) (reverseFin i) (dualSet A) := by
  by_cases h : j ∈ A ∧ i ∉ A
  · have hdual : reverseFin i ∈ dualSet A ∧ reverseFin j ∉ dualSet A := by
      constructor
      · simpa using h.2
      · simpa using h.1
    rw [singletonLeftShift_eq_transpose h,
      singletonLeftShift_eq_transpose hdual, dualSet_setTranspose]
  · have hdual : ¬ (reverseFin i ∈ dualSet A ∧ reverseFin j ∉ dualSet A) := by
      intro hd
      apply h
      constructor
      · simpa using hd.2
      · simpa using hd.1
    rw [singletonLeftShift_eq_self h, singletonLeftShift_eq_self hdual]

/-- Left compression is invariant under reversed complementation. -/
lemma LeftCompressed.dualFamily {N : ℕ} {F : Finset (Finset (Fin N))}
    (hleft : LeftCompressed F) : LeftCompressed (Erdos83.dualFamily F) := by
  intro i j hij
  have hclosed : ∀ ⦃A : Finset (Fin N)⦄, A ∈ Erdos83.dualFamily F →
      singletonLeftShift i j A ∈ Erdos83.dualFamily F := by
    intro A hA
    by_cases hmove : j ∈ A ∧ i ∉ A
    · apply mem_dualFamily.mpr
      rw [dualSet_singletonLeftShift]
      exact hleft.shifted_mem (reverseFin_lt_reverseFin hij)
        (mem_dualFamily.mp hA) (by simpa using hmove.2) (by simpa using hmove.1)
    · simpa [singletonLeftShift_eq_self hmove] using hA
  ext A
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨B, hBF, rfl⟩
    have hshift := hclosed hBF
    simp [familyShiftMember, hshift, hBF]
  · intro hA
    have hshift := hclosed hA
    exact Finset.mem_image.mpr ⟨A, hA, by simp [familyShiftMember, hshift]⟩

/-- Points before the split at `k`. -/
def firstBlock (N k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x ↦ x.1 < k

/-- Points at or after the split at `k`. -/
def secondBlock (N k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun x ↦ k ≤ x.1

@[simp] lemma mem_firstBlock {N k : ℕ} {x : Fin N} :
    x ∈ firstBlock N k ↔ x.1 < k := by
  simp [firstBlock]

@[simp] lemma mem_secondBlock {N k : ℕ} {x : Fin N} :
    x ∈ secondBlock N k ↔ k ≤ x.1 := by
  simp [secondBlock]

lemma firstBlock_union_secondBlock (N k : ℕ) :
    firstBlock N k ∪ secondBlock N k = Finset.univ := by
  ext x
  simp [firstBlock, secondBlock]
  omega

lemma firstBlock_disjoint_secondBlock (N k : ℕ) :
    Disjoint (firstBlock N k) (secondBlock N k) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx hy
  simp only [mem_firstBlock] at hx
  simp only [mem_secondBlock] at hy
  omega

@[simp] lemma firstBlock_four_mul_two_mul (q : ℕ) :
    firstBlock (4 * q) (2 * q) = firstHalf q := rfl

lemma secondBlock_four_mul_two_mul (q : ℕ) :
    secondBlock (4 * q) (2 * q) = secondHalf q := by
  ext x
  by_cases hx : x.1 < 2 * q
  · simp [secondBlock, secondHalf, firstHalf, hx]
  · have hx' : 2 * q ≤ x.1 := by omega
    simp [secondBlock, secondHalf, firstHalf, hx, hx']

/-- In the `4q`-point ground set, duality exchanges the two blocks and
complements within them. -/
lemma card_dualSet_inter_firstBlock (q : ℕ) (A : Finset (Fin (4 * q))) :
    (dualSet A ∩ firstBlock (4 * q) (2 * q)).card =
      2 * q - (A ∩ secondBlock (4 * q) (2 * q)).card := by
  calc
    (dualSet A ∩ firstBlock (4 * q) (2 * q)).card =
        (secondBlock (4 * q) (2 * q) \ A).card := by
      apply Finset.card_bij
          (fun x (_ : x ∈ dualSet A ∩ firstBlock (4 * q) (2 * q)) ↦ reverseFin x)
      · intro x hx
        have hxdual := (Finset.mem_inter.mp hx).1
        have hxfirst := (Finset.mem_inter.mp hx).2
        apply Finset.mem_sdiff.mpr
        constructor
        · simp only [mem_secondBlock, reverseFin_val]
          simp only [mem_firstBlock] at hxfirst
          omega
        · simpa using hxdual
      · intro x hx y hy hxy
        exact (reverseFinEquiv (4 * q)).injective hxy
      · intro y hy
        have hysecond := (Finset.mem_sdiff.mp hy).1
        have hyA := (Finset.mem_sdiff.mp hy).2
        refine ⟨reverseFin y, ?_, ?_⟩
        · apply Finset.mem_inter.mpr
          constructor
          · simpa using hyA
          · simp only [mem_firstBlock, reverseFin_val]
            simp only [mem_secondBlock] at hysecond
            omega
        · exact reverseFin_reverseFin y
    _ = 2 * q - (A ∩ secondBlock (4 * q) (2 * q)).card := by
      rw [Finset.card_sdiff, Finset.inter_comm,
        secondBlock_four_mul_two_mul, card_secondHalf]

/-- Membership depends only on the two block cardinalities.  The formulation
with equal intersections is convenient for deriving it from `PrefixInvariant`.
-/
def BlockInvariant {N : ℕ} (F : Finset (Finset (Fin N))) (k : ℕ) : Prop :=
  ∀ (A B : Finset (Fin N)),
    (A ∩ firstBlock N k).card = (B ∩ firstBlock N k).card →
    (A ∩ secondBlock N k).card = (B ∩ secondBlock N k).card →
    (A ∈ F ↔ B ∈ F)

lemma prefixInvariant_iff {N : ℕ} {F : Finset (Finset (Fin N))} {k : ℕ} :
    PrefixInvariant F k ↔
      ∀ ⦃A B : Finset (Fin N)⦄,
        A ∩ secondBlock N k = B ∩ secondBlock N k →
        (A ∩ firstBlock N k).card = (B ∩ firstBlock N k).card →
        (A ∈ F ↔ B ∈ F) := by
  rfl

/-- The right-handed analogue of `PrefixInvariant`: the first block is fixed
pointwise and membership depends on the cardinality in the second block. -/
def SuffixInvariant {N : ℕ} (F : Finset (Finset (Fin N))) (k : ℕ) : Prop :=
  ∀ ⦃A B : Finset (Fin N)⦄,
    A ∩ firstBlock N k = B ∩ firstBlock N k →
    (A ∩ secondBlock N k).card = (B ∩ secondBlock N k).card →
    (A ∈ F ↔ B ∈ F)

/-- Prefix invariance of the reversed-complement family is precisely the
right-block invariance needed for the original family. -/
lemma suffixInvariant_of_dual_prefix {q : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hdual : PrefixInvariant (dualFamily F) (2 * q)) :
    SuffixInvariant F (2 * q) := by
  intro A B hfirst hsecond
  have htail :
      dualSet A ∩ secondBlock (4 * q) (2 * q) =
        dualSet B ∩ secondBlock (4 * q) (2 * q) := by
    ext x
    simp only [Finset.mem_inter, mem_dualSet, mem_secondBlock]
    constructor
    · rintro ⟨hna, hx⟩
      have hrfirst : reverseFin x ∈ firstBlock (4 * q) (2 * q) := by
        simp only [mem_firstBlock, reverseFin_val]
        omega
      have hab : reverseFin x ∈ A ↔ reverseFin x ∈ B := by
        have hmem : reverseFin x ∈ A ∩ firstBlock (4 * q) (2 * q) ↔
            reverseFin x ∈ B ∩ firstBlock (4 * q) (2 * q) := by rw [hfirst]
        simpa only [Finset.mem_inter, hrfirst, and_true] using hmem
      exact ⟨fun hb ↦ hna (hab.mpr hb), hx⟩
    · rintro ⟨hnb, hx⟩
      have hrfirst : reverseFin x ∈ firstBlock (4 * q) (2 * q) := by
        simp only [mem_firstBlock, reverseFin_val]
        omega
      have hab : reverseFin x ∈ A ↔ reverseFin x ∈ B := by
        have hmem : reverseFin x ∈ A ∩ firstBlock (4 * q) (2 * q) ↔
            reverseFin x ∈ B ∩ firstBlock (4 * q) (2 * q) := by rw [hfirst]
        simpa only [Finset.mem_inter, hrfirst, and_true] using hmem
      exact ⟨fun ha ↦ hnb (hab.mp ha), hx⟩
  have hfirstCard :
      (dualSet A ∩ firstBlock (4 * q) (2 * q)).card =
        (dualSet B ∩ firstBlock (4 * q) (2 * q)).card := by
    rw [card_dualSet_inter_firstBlock, card_dualSet_inter_firstBlock, hsecond]
  simpa using hdual htail hfirstCard

lemma blockInvariant_of_prefix_suffix {N k : ℕ}
    {F : Finset (Finset (Fin N))}
    (hprefix : PrefixInvariant F k) (hsuffix : SuffixInvariant F k) :
    BlockInvariant F k := by
  intro A B hfirst hsecond
  let C := (B ∩ firstBlock N k) ∪ (A ∩ secondBlock N k)
  have hCfirst : C ∩ firstBlock N k = B ∩ firstBlock N k := by
    ext x
    simp only [C, mem_inter, mem_union, mem_firstBlock, mem_secondBlock]
    constructor
    · rintro ⟨hB | hA, hx⟩
      · exact hB
      · omega
    · intro hx
      exact ⟨Or.inl hx, hx.2⟩
  have hCsecond : C ∩ secondBlock N k = A ∩ secondBlock N k := by
    ext x
    simp only [C, mem_inter, mem_union, mem_firstBlock, mem_secondBlock]
    constructor
    · rintro ⟨hB | hA, hx⟩
      · omega
      · exact hA
    · intro hx
      exact ⟨Or.inr hx, hx.2⟩
  exact (hprefix hCsecond.symm (hfirst.trans (congrArg Finset.card hCfirst).symm)).trans
    (hsuffix hCfirst ((congrArg Finset.card hCsecond).trans hsecond))

lemma card_inter_firstBlock_add_secondBlock {N k : ℕ}
    (A : Finset (Fin N)) :
    (A ∩ firstBlock N k).card + (A ∩ secondBlock N k).card = A.card := by
  exact card_inter_prefix_add_card_inter_tailAfter A

/-- One compression step moves a point from the second half into the first
half, increasing the first-half count by one. -/
lemma exists_member_firstBlock_card_succ {q : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hleft : LeftCompressed F)
    {A : Finset (Fin (4 * q))} (hA : A ∈ F)
    (hlt : (A ∩ firstBlock (4 * q) (2 * q)).card < 2 * q) :
    ∃ B ∈ F,
      (B ∩ firstBlock (4 * q) (2 * q)).card =
        (A ∩ firstBlock (4 * q) (2 * q)).card + 1 := by
  have hfirstCard : (firstBlock (4 * q) (2 * q)).card = 2 * q := by
    rw [firstBlock_four_mul_two_mul, card_firstHalf]
  have hcardlt :
      (A ∩ firstBlock (4 * q) (2 * q)).card <
        (firstBlock (4 * q) (2 * q)).card := by
    rw [hfirstCard]
    exact hlt
  obtain ⟨i, hiFirst, hiNotInter⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcardlt
  have hiA : i ∉ A := by
    intro hi
    exact hiNotInter (Finset.mem_inter.mpr ⟨hi, hiFirst⟩)
  have hdecomp := card_inter_firstBlock_add_secondBlock
    (k := 2 * q) A
  have hsecondPos : 0 < (A ∩ secondBlock (4 * q) (2 * q)).card := by
    have hAcard := hunif hA
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hsecondPos
  have hjA : j ∈ A := (Finset.mem_inter.mp hj).1
  have hjSecond : j ∈ secondBlock (4 * q) (2 * q) :=
    (Finset.mem_inter.mp hj).2
  have hij : i < j := by
    simp only [Fin.lt_iff_val_lt_val]
    simp only [mem_firstBlock] at hiFirst
    simp only [mem_secondBlock] at hjSecond
    omega
  let B := singletonLeftShift i j A
  have hB : B ∈ F := hleft.shifted_mem hij hA hjA hiA
  refine ⟨B, hB, ?_⟩
  have hmove : j ∈ A ∧ i ∉ A := ⟨hjA, hiA⟩
  have hBform : B = insert i (A.erase j) := by
    dsimp only [B]
    rw [singletonLeftShift_eq_transpose hmove,
      setTranspose_eq_insert_erase hmove]
  have hjNotFirst : j ∉ firstBlock (4 * q) (2 * q) := by
    simp only [mem_firstBlock]
    simp only [mem_secondBlock] at hjSecond
    omega
  have hInter :
      B ∩ firstBlock (4 * q) (2 * q) =
        insert i (A ∩ firstBlock (4 * q) (2 * q)) := by
    rw [hBform]
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | hx, hxFirst⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hx.2, hxFirst⟩
    · rintro (rfl | ⟨hxA, hxFirst⟩)
      · exact ⟨Or.inl rfl, hiFirst⟩
      · have hxj : x ≠ j := by
          intro h
          subst x
          exact hjNotFirst hxFirst
        exact ⟨Or.inr ⟨hxj, hxA⟩, hxFirst⟩
  have hiNot : i ∉ A ∩ firstBlock (4 * q) (2 * q) := by
    intro hi
    exact hiA (Finset.mem_inter.mp hi).1
  rw [hInter, Finset.card_insert_of_notMem hiNot]

/-- Any member whose first-half count is at most `q` can be compressed, layer
by layer, to a member of the middle layer. -/
lemma exists_middle_member {q : ℕ} (hq : 1 ≤ q)
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hleft : LeftCompressed F)
    {A : Finset (Fin (4 * q))} (hA : A ∈ F)
    (hle : (A ∩ firstBlock (4 * q) (2 * q)).card ≤ q) :
    ∃ B ∈ F, (B ∩ firstBlock (4 * q) (2 * q)).card = q := by
  generalize hd : q - (A ∩ firstBlock (4 * q) (2 * q)).card = d
  induction d generalizing A with
  | zero =>
      refine ⟨A, hA, ?_⟩
      omega
  | succ d ih =>
      have halt : (A ∩ firstBlock (4 * q) (2 * q)).card < q := by omega
      have haltTwo : (A ∩ firstBlock (4 * q) (2 * q)).card < 2 * q := by omega
      obtain ⟨B, hB, hBcount⟩ :=
        exists_member_firstBlock_card_succ hunif hleft hA haltTwo
      apply ih (A := B)
      · exact hB
      · omega
      · omega

/-- Two-intersection rules out the middle layer once membership is invariant
under permutations inside both halves. -/
lemma middle_layer_absent {q : ℕ}
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F)
    (hblock : BlockInvariant F (2 * q)) :
    ∀ {A : Finset (Fin (4 * q))}, A ∈ F →
      (A ∩ firstBlock (4 * q) (2 * q)).card ≠ q := by
  intro A hA hAfirst
  have hdecomp := card_inter_firstBlock_add_secondBlock
    (k := 2 * q) A
  have hAsecond : (A ∩ secondBlock (4 * q) (2 * q)).card = q := by
    have hAcard := hunif hA
    omega
  have hcompFirst :
      (Aᶜ ∩ firstBlock (4 * q) (2 * q)).card = q := by
    have heq : Aᶜ ∩ firstBlock (4 * q) (2 * q) =
        firstBlock (4 * q) (2 * q) \ A := by
      ext x
      simp [and_comm]
    rw [heq, Finset.card_sdiff]
    have hfirstCard : (firstBlock (4 * q) (2 * q)).card = 2 * q := by
      rw [firstBlock_four_mul_two_mul, card_firstHalf]
    rw [hfirstCard]
    rw [hAfirst]
    omega
  have hcompSecond :
      (Aᶜ ∩ secondBlock (4 * q) (2 * q)).card = q := by
    have heq : Aᶜ ∩ secondBlock (4 * q) (2 * q) =
        secondBlock (4 * q) (2 * q) \ A := by
      ext x
      simp [and_comm]
    rw [heq, Finset.card_sdiff]
    have hsecondCard : (secondBlock (4 * q) (2 * q)).card = 2 * q := by
      rw [secondBlock_four_mul_two_mul, card_secondHalf]
    rw [hsecondCard]
    rw [hAsecond]
    omega
  have hAc : Aᶜ ∈ F :=
    (hblock A Aᶜ (hAfirst.trans hcompFirst.symm)
      (hAsecond.trans hcompSecond.symm)).mp hA
  have hcontra := hinter hA hAc
  simpa using hcontra

/-- A compressed, block-invariant uniform two-intersecting family lies in the
standard strict-majority construction. -/
lemma subset_majority_of_blockInvariant {q : ℕ} (hq : 1 ≤ q)
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F)
    (hleft : LeftCompressed F) (hblock : BlockInvariant F (2 * q)) :
    F ⊆ majorityFamily q := by
  intro A hA
  apply mem_majorityFamily.mpr
  refine ⟨hunif hA, ?_⟩
  by_contra hmajority
  have hle : (A ∩ firstBlock (4 * q) (2 * q)).card ≤ q := by
    rw [firstBlock_four_mul_two_mul]
    omega
  obtain ⟨B, hB, hBmiddle⟩ := exists_middle_member hq hunif hleft hA hle
  exact middle_layer_absent hunif hinter hblock hB hBmiddle

/-- The post-prefix extremal conclusion: every maximum-cardinality compressed
family is contained in the standard strict-majority family. -/
theorem extremal_subset_majority {q : ℕ} (hq : 2 ≤ q)
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    F ⊆ majorityFamily q := by
  have hmiddle : 4 * q = 2 * (2 * q) := by omega
  have hdualUnif : Uniform (2 * q) (dualFamily F) :=
    hunif.dualFamily hmiddle
  have hdualInter : TwoIntersecting (dualFamily F) :=
    hinter.dualFamily hmiddle hunif
  have hdualMax :
      ∀ G : Finset (Finset (Fin (4 * q))),
        Uniform (2 * q) G → TwoIntersecting G →
          G.card ≤ (dualFamily F).card :=
    maximal_dualFamily hmiddle hunif hinter hmax
  have hprefix : PrefixInvariant F (2 * q) :=
    prefixInvariant_two_mul hq hunif hinter hmax hleft
  have hdualPrefix : PrefixInvariant (dualFamily F) (2 * q) :=
    prefixInvariant_two_mul hq hdualUnif hdualInter hdualMax hleft.dualFamily
  have hsuffix : SuffixInvariant F (2 * q) :=
    suffixInvariant_of_dual_prefix hdualPrefix
  exact subset_majority_of_blockInvariant (by omega) hunif hinter hleft
    (blockInvariant_of_prefix_suffix hprefix hsuffix)

/-- Cardinality form used by the main Erdős 83 theorem. -/
theorem extremal_card_le_majority {q : ℕ} (hq : 2 ≤ q)
    {F : Finset (Finset (Fin (4 * q)))}
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F)
    (hmax : ∀ G : Finset (Finset (Fin (4 * q))),
      Uniform (2 * q) G → TwoIntersecting G → G.card ≤ F.card)
    (hleft : LeftCompressed F) :
    F.card ≤ (majorityFamily q).card := by
  exact Finset.card_le_card
    (extremal_subset_majority hq hunif hinter hmax hleft)

end Erdos83

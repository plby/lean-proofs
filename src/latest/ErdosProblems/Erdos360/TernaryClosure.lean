/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Executable ternary closure for Erdős Problem 360

This small module isolates the finite closure computation used to fill the
bounded cases omitted in Balasubramanian--Pandey's affine-alignment argument.
-/

namespace Erdos360

open scoped Pointwise

/-- `p` and `q` ternary-generate `A` if every subset of `A` containing them
and closed under relations `z + a = b + c` already contains all of `A`. -/
def TernaryGenerates (A : Finset ℕ) (p q : ℕ) : Prop :=
  p ∈ A ∧ q ∈ A ∧
    ∀ C : Set ℕ, C ⊆ (A : Set ℕ) → p ∈ C → q ∈ C →
      (∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ z ∈ A,
        z + a = b + c → z ∈ C) →
      (A : Set ℕ) ⊆ C

/-- Executable existential quantification over a finset. -/
def finsetAny {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → Bool) : Bool :=
  Finset.fold (· || ·) false p S

@[simp] lemma finsetAny_eq_true {α : Type*} [DecidableEq α]
    {S : Finset α} {p : α → Bool} :
    finsetAny S p = true ↔ ∃ x ∈ S, p x = true := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [finsetAny]
  | @insert x S hx ih =>
      rw [finsetAny, Finset.fold_insert hx]
      change (p x || Finset.fold (· || ·) false p S) = true ↔ _
      rw [Bool.or_eq_true, show Finset.fold (· || ·) false p S = true ↔
        ∃ y ∈ S, p y = true by simpa [finsetAny] using ih]
      simp

/-- One executable ternary-closure step inside the fixed ambient finset
`A`.  Computing `C + C` once makes the bounded certificates substantially
faster than enumerating triples in `C`. -/
def ternaryClosureStep (A C : Finset ℕ) : Finset ℕ :=
  let sums := C + C
  C ∪ A.filter fun z ↦
    finsetAny C fun a ↦ decide (z + a ∈ sums)

/-- Iteration of `ternaryClosureStep`, starting from a finite seed. -/
def ternaryClosureIterate (A seed : Finset ℕ) : ℕ → Finset ℕ
  | 0 => seed
  | k + 1 => ternaryClosureStep A (ternaryClosureIterate A seed k)

@[simp] lemma mem_ternaryClosureStep {A C : Finset ℕ} {z : ℕ} :
    z ∈ ternaryClosureStep A C ↔
      z ∈ C ∨
        z ∈ A ∧ ∃ a ∈ C, ∃ b ∈ C, ∃ c ∈ C, z + a = b + c := by
  constructor
  · intro hz
    rw [ternaryClosureStep, Finset.mem_union] at hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · right
      obtain ⟨hzA, hz⟩ := Finset.mem_filter.mp hz
      rw [finsetAny_eq_true] at hz
      obtain ⟨a, haC, hza⟩ := hz
      simp only [decide_eq_true_eq] at hza
      obtain ⟨b, hbC, c, hcC, hrel⟩ := Finset.mem_add.mp hza
      exact ⟨hzA, a, haC, b, hbC, c, hcC, hrel.symm⟩
  · rintro (hz | ⟨hzA, a, ha, b, hb, c, hc, hrel⟩)
    · exact Finset.mem_union_left _ hz
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hzA, finsetAny_eq_true.mpr ⟨a, ha, ?_⟩⟩
      simp only [decide_eq_true_eq]
      exact Finset.mem_add.mpr ⟨b, hb, c, hc, hrel.symm⟩

lemma ternaryClosureIterate_mono (A seed : Finset ℕ) (k : ℕ) :
    ternaryClosureIterate A seed k ⊆
      ternaryClosureIterate A seed (k + 1) := by
  intro z hz
  exact mem_ternaryClosureStep.mpr (Or.inl hz)

lemma ternaryClosureIterate_subset_of_closed
    {A seed : Finset ℕ} {C : Set ℕ}
    (hseed : (seed : Set ℕ) ⊆ C)
    (hclosed : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ z ∈ A,
      z + a = b + c → z ∈ C) :
    ∀ k, (ternaryClosureIterate A seed k : Set ℕ) ⊆ C := by
  intro k
  induction k with
  | zero => exact hseed
  | succ k ih =>
      intro z hz
      change z ∈ ternaryClosureStep A (ternaryClosureIterate A seed k) at hz
      rw [mem_ternaryClosureStep] at hz
      rcases hz with hz | ⟨hzA, a, ha, b, hb, c, hc, hrel⟩
      · exact ih hz
      · exact hclosed a (ih ha) b (ih hb) c (ih hc) z hzA hrel

/-- A successful finite closure computation is a certificate for the
universal ternary-generation predicate. -/
lemma ternaryGenerates_of_iterate_eq
    {A : Finset ℕ} {p q k : ℕ}
    (hp : p ∈ A) (hq : q ∈ A)
    (hfull : ternaryClosureIterate A {p, q} k = A) :
    TernaryGenerates A p q := by
  refine ⟨hp, hq, ?_⟩
  intro C _hCA hpC hqC hclosed
  have hseed : (({p, q} : Finset ℕ) : Set ℕ) ⊆ C := by
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hpC
    · exact hqC
  have hiter := ternaryClosureIterate_subset_of_closed hseed hclosed k
  simpa [hfull] using hiter

/-! ## Elementary propagation rules

The proofs in Balasubramanian--Pandey repeatedly use two very small facts
about ternary closure.  Once a closed set contains an adjacent pair, it can
walk through any consecutive run of the ambient set.  It can also cross a
gap whenever the length of that gap occurs as a difference of two points
already in the closed set.  Keeping these facts separate makes the later
dense-set induction independent of the executable closure above. -/

lemma ternaryClosed_succ
    {A : Finset ℕ} {C : Set ℕ} {p x : ℕ}
    (hp : p ∈ C) (hp1 : p + 1 ∈ C) (hx : x ∈ C)
    (hx1A : x + 1 ∈ A)
    (hclosed : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ z ∈ A,
      z + a = b + c → z ∈ C) :
    x + 1 ∈ C := by
  apply hclosed p hp x hx (p + 1) hp1 (x + 1) hx1A
  omega

lemma ternaryClosed_pred
    {A : Finset ℕ} {C : Set ℕ} {p x z : ℕ}
    (hp : p ∈ C) (hp1 : p + 1 ∈ C) (hx : x ∈ C)
    (hzA : z ∈ A) (hzx : z + 1 = x)
    (hclosed : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ w ∈ A,
      w + a = b + c → w ∈ C) :
    z ∈ C := by
  apply hclosed (p + 1) hp1 x hx p hp z hzA
  omega

lemma ternaryClosed_of_difference
    {A : Finset ℕ} {C : Set ℕ} {x u v z : ℕ}
    (hx : x ∈ C) (hu : u ∈ C) (hv : v ∈ C)
    (hzA : z ∈ A) (hrel : z + v = x + u)
    (hclosed : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ w ∈ A,
      w + a = b + c → w ∈ C) :
    z ∈ C :=
  hclosed v hv x hx u hu z hzA hrel

lemma Icc_subset_ternaryClosed
    {A : Finset ℕ} {C : Set ℕ} {p l u : ℕ}
    (hp : p ∈ C) (hp1 : p + 1 ∈ C)
    (hl : l ∈ C) (hIccA : Finset.Icc l u ⊆ A)
    (hclosed : ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, ∀ z ∈ A,
      z + a = b + c → z ∈ C) :
    (Finset.Icc l u : Set ℕ) ⊆ C := by
  intro z hz
  rw [Finset.mem_coe, Finset.mem_Icc] at hz
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hz.1
  induction k with
  | zero => simpa using hl
  | succ k ih =>
      apply ternaryClosed_succ hp hp1 (ih (by omega))
      apply hIccA
      rw [Finset.mem_Icc]
      omega
      exact hclosed

/-- Every nontrivial natural interval is ternary-generated by its first two
points. -/
lemma ternaryGenerates_Icc {l u : ℕ} (hlu : l < u) :
    TernaryGenerates (Finset.Icc l u) l (l + 1) := by
  refine ⟨Finset.mem_Icc.mpr ⟨le_rfl, hlu.le⟩,
    Finset.mem_Icc.mpr ⟨by omega, hlu⟩, ?_⟩
  intro C _hCA hl hl1 hclosed
  exact Icc_subset_ternaryClosed hl hl1 hl (fun _ h ↦ h) hclosed

/-! ## A dense-set difference lemma

The next finite encoding is the elementary counting argument behind
Balasubramanian--Pandey, Lemma 1.  In each block of length `2*d`, two
integers with the same key are either equal or differ by exactly `d`.
Consequently a set which realizes no difference `d` has at most `d` points
in every full block and at most `min q d` in the final block of length `q`.
-/

def differenceBlockKey (d x : ℕ) : ℕ × ℕ :=
  let r := x % (2 * d)
  (x / (2 * d), if r < d then r else r - d)

lemma differenceBlockKey_eq_cases {d x y : ℕ} (hd : 0 < d)
    (hkey : differenceBlockKey d x = differenceBlockKey d y) :
    x = y ∨ x + d = y ∨ y + d = x := by
  let m := 2 * d
  let rx := x % m
  let ry := y % m
  have hm : 0 < m := by dsimp [m]; omega
  have hrx : rx < m := Nat.mod_lt _ hm
  have hry : ry < m := Nat.mod_lt _ hm
  have hxdiv : x = m * (x / m) + rx := by
    simpa [rx, add_comm] using (Nat.mod_add_div x m).symm
  have hydiv : y = m * (y / m) + ry := by
    simpa [ry, add_comm] using (Nat.mod_add_div y m).symm
  have hdiv : x / m = y / m := by
    simpa [differenceBlockKey, m] using congrArg Prod.fst hkey
  have hrem : (if rx < d then rx else rx - d) =
      (if ry < d then ry else ry - d) := by
    simpa [differenceBlockKey, m, rx, ry] using congrArg Prod.snd hkey
  dsimp only [m] at hxdiv hydiv hrx hry hdiv
  rw [hdiv] at hxdiv
  by_cases hx : rx < d <;> by_cases hy : ry < d
  · simp only [if_pos hx, if_pos hy] at hrem
    exact Or.inl (by omega)
  · simp only [if_pos hx, if_neg hy] at hrem
    have hryEq : ry = rx + d := by omega
    exact Or.inr (Or.inl (by omega))
  · simp only [if_neg hx, if_pos hy] at hrem
    have hrxEq : rx = ry + d := by omega
    exact Or.inr (Or.inr (by omega))
  · simp only [if_neg hx, if_neg hy] at hrem
    have hrEq : rx = ry := by omega
    exact Or.inl (by omega)

def differenceBlockKeys (N d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N / (2 * d))).product (Finset.range d) ∪
    ({N / (2 * d)} : Finset ℕ).product
      (Finset.range (min (N % (2 * d)) d))

lemma differenceBlockKey_mem_keys {N d x : ℕ} (hd : 0 < d)
    (hx : x < N) : differenceBlockKey d x ∈ differenceBlockKeys N d := by
  let m := 2 * d
  let R := N / m
  let q := N % m
  let r := x % m
  have hm : 0 < m := by dsimp [m]; omega
  have hr : r < m := Nat.mod_lt _ hm
  have hdecompN : N = m * R + q := by
    simpa [R, q, add_comm] using (Nat.mod_add_div N m).symm
  have hdecompx : x = m * (x / m) + r := by
    simpa [r, add_comm] using (Nat.mod_add_div x m).symm
  have hxdiv : x / m ≤ R := by
    dsimp [R]
    exact Nat.div_le_div_right hx.le
  rw [differenceBlockKeys]
  by_cases hblock : x / m < R
  · apply Finset.mem_union_left
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩
    · change x / (2 * d) < N / (2 * d)
      simpa [m, R] using hblock
    change (if r < d then r else r - d) < d
    split_ifs <;> omega
  · apply Finset.mem_union_right
    have hblockEq : x / m = R := by omega
    have hrq : r < q := by
      rw [hblockEq] at hdecompx
      omega
    apply Finset.mem_product.mpr
    refine ⟨?_, Finset.mem_range.mpr ?_⟩
    · simp only [Finset.mem_singleton]
      change x / (2 * d) = N / (2 * d)
      simpa [m, R] using hblockEq
    change (if r < d then r else r - d) < min q d
    split_ifs <;> omega

lemma card_differenceBlockKeys (N d : ℕ) :
    (differenceBlockKeys N d).card =
      (N / (2 * d)) * d + min (N % (2 * d)) d := by
  classical
  let R := N / (2 * d)
  let q := N % (2 * d)
  have hdisj : Disjoint
      ((Finset.range R).product (Finset.range d))
      (({R} : Finset ℕ).product (Finset.range (min q d))) := by
    rw [Finset.disjoint_left]
    intro z hz h'z
    have hz1 := (Finset.mem_product.mp hz).1
    have h'z1 := (Finset.mem_product.mp h'z).1
    simp only [Finset.mem_range] at hz1
    simp only [Finset.mem_singleton] at h'z1
    omega
  rw [differenceBlockKeys]
  change (((Finset.range R).product (Finset.range d)) ∪
      (({R} : Finset ℕ).product (Finset.range (min q d)))).card = _
  rw [Finset.card_union_of_disjoint hdisj]
  simp [R, q]

lemma card_le_block_bound_of_no_difference
    {A : Finset ℕ} {N d : ℕ} (hd : 0 < d)
    (hAN : A ⊆ Finset.range N)
    (hno : ∀ x ∈ A, x + d ∉ A) :
    A.card ≤ (N / (2 * d)) * d + min (N % (2 * d)) d := by
  classical
  calc
    A.card = (A.image (differenceBlockKey d)).card := by
      rw [Finset.card_image_iff.mpr]
      intro x hx y hy hkey
      rcases differenceBlockKey_eq_cases hd hkey with hxy | hxy | hyx
      · exact hxy
      · exact False.elim (hno x hx (hxy ▸ hy))
      · exact False.elim (hno y hy (hyx ▸ hx))
    _ ≤ (differenceBlockKeys N d).card := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp hz
      exact differenceBlockKey_mem_keys hd (Finset.mem_range.mp (hAN hxA))
    _ = (N / (2 * d)) * d + min (N % (2 * d)) d :=
      card_differenceBlockKeys N d

lemma three_mul_card_le_two_mul_of_no_difference
    {A : Finset ℕ} {N d : ℕ} (hd : 0 < d)
    (hAN : A ⊆ Finset.range N) (hdA : d < A.card)
    (hno : ∀ x ∈ A, x + d ∉ A) :
    3 * A.card ≤ 2 * N := by
  have hbound := card_le_block_bound_of_no_difference hd hAN hno
  let R := N / (2 * d)
  let q := N % (2 * d)
  have hm : 0 < 2 * d := by omega
  have hq : q < 2 * d := Nat.mod_lt _ hm
  have hN : N = 2 * d * R + q := by
    simpa [R, q, add_comm] using (Nat.mod_add_div N (2 * d)).symm
  have hbound' : A.card ≤ R * d + min q d := by
    simpa [R, q] using hbound
  have hAcardN : A.card ≤ N := by
    simpa using Finset.card_le_card hAN
  have hRpos : 0 < R ∨ N ≤ d := by
    by_cases hR : 0 < R
    · exact Or.inl hR
    · right
      have hRzero : R = 0 := Nat.eq_zero_of_not_pos hR
      by_contra hnot
      have hdN : d < N := Nat.lt_of_not_ge hnot
      have hqN : q = N := by
        rw [hRzero] at hN
        simpa using hN.symm
      have hqd : d < q := by omega
      have hkeyBound := hbound'
      rw [hRzero, zero_mul, zero_add, min_eq_right hqd.le] at hkeyBound
      omega
  rcases hRpos with hRpos | hNd
  · by_cases hqd : q < d
    · rw [min_eq_left hqd.le] at hbound'
      nlinarith
    · rw [min_eq_right (Nat.le_of_not_gt hqd)] at hbound'
      by_cases hRtwo : 3 ≤ R
      · nlinarith
      · interval_cases R <;> omega
  · omega

/-- A set of density at least `2/3 + 1/N` realizes every positive
difference smaller than its cardinality. -/
lemma exists_difference_of_dense
    {A : Finset ℕ} {N d : ℕ}
    (hAN : A ⊆ Finset.range N) (hd : 0 < d) (hdA : d < A.card)
    (hdense : 2 * N + 3 ≤ 3 * A.card) :
    ∃ x ∈ A, x + d ∈ A := by
  by_contra h
  push Not at h
  have hsmall := three_mul_card_le_two_mul_of_no_difference hd hAN hdA h
  omega

/-- Translation-invariant form of `exists_difference_of_dense` for a
half-open interval.  Keeping the density estimate in terms of `u - l`
avoids changing coordinates in the later dense-layer induction. -/
lemma exists_difference_of_dense_Ico
    {A : Finset ℕ} {l u d : ℕ}
    (hA : A ⊆ Finset.Ico l u) (hd : 0 < d) (hdA : d < A.card)
    (hdense : 2 * (u - l) + 3 ≤ 3 * A.card) :
    ∃ x ∈ A, x + d ∈ A := by
  let B := A.image fun x ↦ x - l
  have hlinj : Set.InjOn (fun x : ℕ ↦ x - l) A := by
    intro x hx y hy hxy
    obtain ⟨hlx, _hxu⟩ := Finset.mem_Ico.mp (hA hx)
    obtain ⟨hly, _hyu⟩ := Finset.mem_Ico.mp (hA hy)
    change x - l = y - l at hxy
    omega
  have hcard : B.card = A.card := by
    exact Finset.card_image_of_injOn hlinj
  have hB : B ⊆ Finset.range (u - l) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxI := Finset.mem_Ico.mp (hA hx)
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨z, hz, hzd⟩ := exists_difference_of_dense
    (A := B) hB hd (by simpa [hcard] using hdA)
      (by simpa [hcard] using hdense)
  obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz
  obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hzd
  obtain ⟨hlx, _hxu⟩ := Finset.mem_Ico.mp (hA hx)
  obtain ⟨hly, _hyu⟩ := Finset.mem_Ico.mp (hA hy)
  refine ⟨x, hx, ?_⟩
  have hxy : x + d = y := by
    omega
  simpa [hxy] using hy

/-- Translate a finite set of naturals down by `l`.  It is used only when
all elements are at least `l`, so truncated subtraction is injective. -/
def translateDown (A : Finset ℕ) (l : ℕ) : Finset ℕ :=
  A.image fun x ↦ x - l

lemma mem_translateDown {A : Finset ℕ} {l z : ℕ} :
    z ∈ translateDown A l ↔ ∃ x ∈ A, x - l = z := by
  simp [translateDown]

lemma card_translateDown {A : Finset ℕ} {l : ℕ}
    (hl : ∀ x ∈ A, l ≤ x) :
    (translateDown A l).card = A.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  change x - l = y - l at hxy
  have hlx := hl x hx
  have hly := hl y hy
  omega

/-- Ternary generation is invariant under translating an interval back up
from natural quotient coordinates. -/
lemma ternaryGenerates_of_translateDown
    {A : Finset ℕ} {l p q : ℕ}
    (hl : ∀ x ∈ A, l ≤ x)
    (hgen : TernaryGenerates (translateDown A l) p q) :
    TernaryGenerates A (p + l) (q + l) := by
  obtain ⟨xp, hxpA, hxp⟩ := mem_translateDown.mp hgen.1
  obtain ⟨xq, hxqA, hxq⟩ := mem_translateDown.mp hgen.2.1
  have hxpEq : xp = p + l := by
    have := hl xp hxpA
    omega
  have hxqEq : xq = q + l := by
    have := hl xq hxqA
    omega
  refine ⟨hxpEq ▸ hxpA, hxqEq ▸ hxqA, ?_⟩
  intro C hCA hpC hqC hclosed
  let D : Set ℕ := {z | z ∈ translateDown A l ∧ z + l ∈ C}
  have hpD : p ∈ D := by
    exact ⟨hgen.1, hpC⟩
  have hqD : q ∈ D := by
    exact ⟨hgen.2.1, hqC⟩
  have hDclosed : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D,
      ∀ z ∈ translateDown A l, z + a = b + c → z ∈ D := by
    intro a ha b hb c hc z hz hrel
    obtain ⟨xz, hxzA, hxz⟩ := mem_translateDown.mp hz
    have hlz := hl xz hxzA
    have hxzEq : xz = z + l := by omega
    refine ⟨hz, ?_⟩
    apply hclosed (a + l) ha.2 (b + l) hb.2 (c + l) hc.2
      (z + l) (hxzEq ▸ hxzA)
    omega
  have hDall := hgen.2.2 D (fun _ h ↦ h.1) hpD hqD hDclosed
  intro x hxA
  let z := x - l
  have hz : z ∈ translateDown A l :=
    mem_translateDown.mpr ⟨x, hxA, rfl⟩
  have hzD := hDall hz
  have hlx := hl x hxA
  have hzx : z + l = x := by dsimp [z]; omega
  exact hzx ▸ hzD.2

/-! ## The central dense subinterval

The induction in Balasubramanian--Pandey cuts an interval at one of the
three integers nearest its midpoint.  The only combinatorics needed to find
a dense side is that a prefix count grows by at most one when its endpoint
is advanced by one. -/

lemma card_ltFilter_le_succ (A : Finset ℕ) (t : ℕ) :
    (A.filter fun x ↦ x < t).card ≤
      (A.filter fun x ↦ x < t + 1).card := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, by omega⟩

lemma card_ltFilter_succ_le (A : Finset ℕ) (t : ℕ) :
    (A.filter fun x ↦ x < t + 1).card ≤
      (A.filter fun x ↦ x < t).card + 1 := by
  calc
    (A.filter fun x ↦ x < t + 1).card ≤
        (insert t (A.filter fun x ↦ x < t)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter] at hx
      rw [Finset.mem_insert]
      by_cases hxt : x = t
      · exact Or.inl hxt
      · exact Or.inr (Finset.mem_filter.mpr ⟨hx.1, by omega⟩)
    _ ≤ (A.filter fun x ↦ x < t).card + 1 :=
      Finset.card_insert_le _ _

lemma card_ltFilter_add_card_geFilter (A : Finset ℕ) (t : ℕ) :
    (A.filter fun x ↦ x < t).card +
        (A.filter fun x ↦ t ≤ x).card = A.card := by
  have hdisj : Disjoint (A.filter fun x ↦ x < t)
      (A.filter fun x ↦ t ≤ x) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_filter] at hx hy
    omega
  have hunion : (A.filter fun x ↦ x < t) ∪
      (A.filter fun x ↦ t ≤ x) = A := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      exact (lt_or_ge x t).elim (fun h ↦ Or.inl ⟨hx, h⟩)
        (fun h ↦ Or.inr ⟨hx, h⟩)
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

/-- One of the three cuts surrounding `N / 2` has a side which retains the
strict two-thirds density.  This is the exact arithmetic selection used in
the published dense-set induction. -/
lemma exists_central_dense_side
    {A : Finset ℕ} {N : ℕ} (hN : 5 ≤ N)
    (hdense : 2 * N + 3 ≤ 3 * A.card) :
    ∃ t : ℕ,
      (t = N / 2 - 1 ∨ t = N / 2 ∨ t = N / 2 + 1) ∧
        (2 * t + 3 ≤ 3 * (A.filter fun x ↦ x < t).card ∨
          2 * (N - t) + 3 ≤
            3 * (A.filter fun x ↦ t ≤ x).card) := by
  by_contra h
  have hfail : ∀ t : ℕ,
      (t = N / 2 - 1 ∨ t = N / 2 ∨ t = N / 2 + 1) →
        3 * (A.filter fun x ↦ x < t).card < 2 * t + 3 ∧
          3 * (A.filter fun x ↦ t ≤ x).card <
            2 * (N - t) + 3 := by
    intro t ht
    have ht' : ¬(2 * t + 3 ≤ 3 * (A.filter fun x ↦ x < t).card ∨
        2 * (N - t) + 3 ≤
          3 * (A.filter fun x ↦ t ≤ x).card) := by
      intro hs
      exact h ⟨t, ht, hs⟩
    omega
  let m := N / 2
  let L₀ := (A.filter fun x ↦ x < m - 1).card
  let L₁ := (A.filter fun x ↦ x < m).card
  let L₂ := (A.filter fun x ↦ x < m + 1).card
  let R₀ := (A.filter fun x ↦ m - 1 ≤ x).card
  let R₁ := (A.filter fun x ↦ m ≤ x).card
  let R₂ := (A.filter fun x ↦ m + 1 ≤ x).card
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hNm : N = 2 * m ∨ N = 2 * m + 1 := by
    dsimp [m]
    omega
  have hmstep₀ : m - 1 + 1 = m := by omega
  have hL₀₁ : L₀ ≤ L₁ := by
    dsimp [L₀, L₁]
    simpa [hmstep₀] using card_ltFilter_le_succ A (m - 1)
  have hL₁₀ : L₁ ≤ L₀ + 1 := by
    dsimp [L₀, L₁]
    simpa [hmstep₀] using card_ltFilter_succ_le A (m - 1)
  have hL₁₂ : L₁ ≤ L₂ := by
    exact card_ltFilter_le_succ A m
  have hL₂₁ : L₂ ≤ L₁ + 1 := by
    exact card_ltFilter_succ_le A m
  have hpart₀ : L₀ + R₀ = A.card := by
    exact card_ltFilter_add_card_geFilter A (m - 1)
  have hpart₁ : L₁ + R₁ = A.card := by
    exact card_ltFilter_add_card_geFilter A m
  have hpart₂ : L₂ + R₂ = A.card := by
    exact card_ltFilter_add_card_geFilter A (m + 1)
  have hf₀ := hfail (m - 1) (Or.inl (by simp [m]))
  have hf₁ := hfail m (Or.inr (Or.inl (by simp [m])))
  have hf₂ := hfail (m + 1) (Or.inr (Or.inr (by simp [m])))
  change 3 * L₀ < 2 * (m - 1) + 3 ∧
      3 * R₀ < 2 * (N - (m - 1)) + 3 at hf₀
  change 3 * L₁ < 2 * m + 3 ∧
      3 * R₁ < 2 * (N - m) + 3 at hf₁
  change 3 * L₂ < 2 * (m + 1) + 3 ∧
      3 * R₂ < 2 * (N - (m + 1)) + 3 at hf₂
  rcases hNm with hNm | hNm <;> omega

/-- Consecutive occupied points in a subset of `[0,N)` are separated by at
most one plus the number of missing points. -/
lemma consecutive_gap_le_complement_add_one
    {A : Finset ℕ} {N y z : ℕ}
    (hAN : A ⊆ Finset.range N) (_hy : y ∈ A) (hz : z ∈ A)
    (hyz : y < z)
    (hconsec : ∀ w ∈ A, y < w → w < z → False) :
    z - y ≤ N - A.card + 1 := by
  have hmissing : Finset.Ico (y + 1) z ⊆ Finset.range N \ A := by
    intro w hw
    rw [Finset.mem_sdiff, Finset.mem_range]
    have hwI := Finset.mem_Ico.mp hw
    have hzN := Finset.mem_range.mp (hAN hz)
    refine ⟨by omega, ?_⟩
    intro hwA
    exact hconsec w hwA (by omega) hwI.2
  have hcard := Finset.card_le_card hmissing
  rw [Nat.card_Ico, Finset.card_sdiff_of_subset hAN] at hcard
  simp only [Finset.card_range] at hcard
  omega

/-- A dense side at one of the three central cuts has at least one more
point than the complement of the original dense set. -/
lemma complement_add_one_le_of_central_dense
    {N k M t : ℕ} (hN : 5 ≤ N)
    (hglobal : 2 * N + 3 ≤ 3 * k)
    (ht : t = N / 2 - 1 ∨ t = N / 2 ∨ t = N / 2 + 1)
    (hside : 2 * t + 3 ≤ 3 * M ∨
      2 * (N - t) + 3 ≤ 3 * M) :
    N - k + 1 ≤ M := by
  have hNm : N = 2 * (N / 2) ∨ N = 2 * (N / 2) + 1 := by omega
  rcases ht with rfl | rfl | rfl <;>
    rcases hside with hside | hside <;>
    rcases hNm with hNm | hNm <;> omega

/-- If a central dense side is chosen with maximum cardinality among all
six central sides, every consecutive gap of the ambient dense set is
strictly smaller than that cardinality.  The equality case is the only
delicate one: it forces an interval of length `3*M` with exactly one gap of
length `M`; then one of the neighboring central sides contains `M+1`
points and is itself dense, contradicting maximality. -/
lemma consecutive_gap_lt_maximal_central_dense_card
    {A : Finset ℕ} {N M t y z : ℕ}
    (hN : 5 ≤ N) (hAN : A ⊆ Finset.range N)
    (hglobal : 2 * N + 3 ≤ 3 * A.card)
    (ht : t = N / 2 - 1 ∨ t = N / 2 ∨ t = N / 2 + 1)
    (hside : 2 * t + 3 ≤ 3 * M ∨
      2 * (N - t) + 3 ≤ 3 * M)
    (hmaxLeft : ∀ u : ℕ,
      (u = N / 2 - 1 ∨ u = N / 2 ∨ u = N / 2 + 1) →
      2 * u + 3 ≤ 3 * (A.filter fun x ↦ x < u).card →
      (A.filter fun x ↦ x < u).card ≤ M)
    (hmaxRight : ∀ u : ℕ,
      (u = N / 2 - 1 ∨ u = N / 2 ∨ u = N / 2 + 1) →
      2 * (N - u) + 3 ≤ 3 * (A.filter fun x ↦ u ≤ x).card →
      (A.filter fun x ↦ u ≤ x).card ≤ M)
    (hy : y ∈ A) (hz : z ∈ A) (hyz : y < z)
    (hconsec : ∀ w ∈ A, y < w → w < z → False) :
    z - y < M := by
  have hgap := consecutive_gap_le_complement_add_one
    hAN hy hz hyz hconsec
  have hcomp : N - A.card + 1 ≤ M :=
    complement_add_one_le_of_central_dense hN hglobal ht hside
  by_contra hnot
  have hgapEq : z - y = M := by omega
  have hcompEq : N - A.card + 1 = M := by omega
  have hcardAN : A.card ≤ N := by
    simpa using Finset.card_le_card hAN
  have hNcard : N - A.card = M - 1 := by omega
  have hmissing : Finset.Ico (y + 1) z ⊆ Finset.range N \ A := by
    intro w hw
    rw [Finset.mem_sdiff, Finset.mem_range]
    have hwI := Finset.mem_Ico.mp hw
    have hzN := Finset.mem_range.mp (hAN hz)
    refine ⟨by omega, ?_⟩
    intro hwA
    exact hconsec w hwA (by omega) hwI.2
  have hmissingEq : Finset.Ico (y + 1) z = Finset.range N \ A := by
    apply Finset.eq_of_subset_of_card_le hmissing
    rw [Nat.card_Ico, Finset.card_sdiff_of_subset hAN]
    simp only [Finset.card_range]
    omega
  have hNm : N = 2 * (N / 2) ∨ N = 2 * (N / 2) + 1 := by omega
  have hthree : N = 3 * M := by
    rcases ht with rfl | rfl | rfl <;>
      rcases hside with hside | hside <;>
      rcases hNm with hNm | hNm <;> omega
  have hM : 3 ≤ M := by omega
  have hab : y + 1 + (N - z) = 2 * M + 1 := by
    have hzN := Finset.mem_range.mp (hAN hz)
    omega
  by_cases hleft : M + 1 ≤ y + 1
  · have hMmid : M + 1 ≤ N / 2 := by
      rcases hNm with hNm | hNm <;> omega
    have hfullLeft : Finset.range (M + 1) ⊆
        A.filter fun x ↦ x < N / 2 := by
      intro x hx
      have hxM := Finset.mem_range.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨?_, by omega⟩
      by_contra hxA
      have hxDiff : x ∈ Finset.range N \ A := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by omega), hxA⟩
      rw [← hmissingEq] at hxDiff
      have hxI := Finset.mem_Ico.mp hxDiff
      omega
    have hlarge : M + 1 ≤
        (A.filter fun x ↦ x < N / 2).card := by
      simpa using Finset.card_le_card hfullLeft
    have hdenseMid : 2 * (N / 2) + 3 ≤
        3 * (A.filter fun x ↦ x < N / 2).card := by
      rcases hNm with hNm | hNm <;> omega
    have hmax := hmaxLeft (N / 2)
      (Or.inr (Or.inl rfl)) hdenseMid
    omega
  · have hleftSmall : y + 1 ≤ M := by omega
    have hrightLarge : M + 1 ≤ N - z := by omega
    have hcut : N / 2 + 1 ≤ N - (M + 1) := by
      rcases hNm with hNm | hNm <;> omega
    have hfullRight : Finset.Ico (N - (M + 1)) N ⊆
        A.filter fun x ↦ N / 2 + 1 ≤ x := by
      intro x hx
      have hxI := Finset.mem_Ico.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨?_, by omega⟩
      by_contra hxA
      have hxDiff : x ∈ Finset.range N \ A := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hxI.2, hxA⟩
      rw [← hmissingEq] at hxDiff
      have hxGap := Finset.mem_Ico.mp hxDiff
      omega
    have hlarge : M + 1 ≤
        (A.filter fun x ↦ N / 2 + 1 ≤ x).card := by
      have hc := Finset.card_le_card hfullRight
      rw [Nat.card_Ico] at hc
      omega
    have hdenseMid : 2 * (N - (N / 2 + 1)) + 3 ≤
        3 * (A.filter fun x ↦ N / 2 + 1 ≤ x).card := by
      rcases hNm with hNm | hNm <;> omega
    have hmax := hmaxRight (N / 2 + 1)
      (Or.inr (Or.inr rfl)) hdenseMid
    omega

/-! ### A finite index for the six central choices -/

abbrev CentralSideIndex := Fin 3 × Bool

def centralCut (N : ℕ) (i : CentralSideIndex) : ℕ :=
  N / 2 - 1 + i.1

def centralSide (A : Finset ℕ) (N : ℕ)
    (i : CentralSideIndex) : Finset ℕ :=
  if i.2 then A.filter fun x ↦ centralCut N i ≤ x
  else A.filter fun x ↦ x < centralCut N i

def centralSideLength (N : ℕ) (i : CentralSideIndex) : ℕ :=
  if i.2 then N - centralCut N i else centralCut N i

def IsDenseCentralSide (A : Finset ℕ) (N : ℕ)
    (i : CentralSideIndex) : Prop :=
  2 * centralSideLength N i + 3 ≤ 3 * (centralSide A N i).card

lemma centralCut_eq_cases {N : ℕ} (hN : 5 ≤ N)
    (i : CentralSideIndex) :
    centralCut N i = N / 2 - 1 ∨
      centralCut N i = N / 2 ∨
      centralCut N i = N / 2 + 1 := by
  have hm : 2 ≤ N / 2 := by omega
  have hi := i.1.isLt
  have hiCases : i.1.val = 0 ∨ i.1.val = 1 ∨ i.1.val = 2 := by omega
  rcases hiCases with h | h | h <;> simp [centralCut, h] <;> omega

lemma centralCut_pos_lt {N : ℕ} (hN : 5 ≤ N)
    (i : CentralSideIndex) :
    0 < centralCut N i ∧ centralCut N i < N := by
  rcases centralCut_eq_cases hN i with h | h | h <;> rw [h] <;> omega

lemma centralSide_subset {A : Finset ℕ} {N : ℕ}
    (i : CentralSideIndex) : centralSide A N i ⊆ A := by
  intro x hx
  simp only [centralSide] at hx
  split at hx <;> exact (Finset.mem_filter.mp hx).1

lemma centralSide_subset_range {A : Finset ℕ} {N : ℕ}
    (hAN : A ⊆ Finset.range N) (i : CentralSideIndex) :
    centralSide A N i ⊆ Finset.range N :=
  (centralSide_subset i).trans hAN

lemma centralSide_length_lt {N : ℕ} (hN : 5 ≤ N)
    (i : CentralSideIndex) : centralSideLength N i < N := by
  have hcut := centralCut_pos_lt hN i
  simp only [centralSideLength]
  split <;> omega

lemma exists_denseCentralSide
    {A : Finset ℕ} {N : ℕ} (hN : 5 ≤ N)
    (hdense : 2 * N + 3 ≤ 3 * A.card) :
    ∃ i : CentralSideIndex, IsDenseCentralSide A N i := by
  obtain ⟨t, ht, hside⟩ := exists_central_dense_side hN hdense
  have hm : 2 ≤ N / 2 := by omega
  have hstep₁ : N / 2 - 1 + 1 = N / 2 := by omega
  have hstep₂ : N / 2 - 1 + 2 = N / 2 + 1 := by omega
  rcases ht with rfl | rfl | rfl
  · rcases hside with hleft | hright
    · refine ⟨(⟨0, by omega⟩, false), ?_⟩
      simpa [IsDenseCentralSide, centralSideLength, centralSide,
        centralCut] using hleft
    · refine ⟨(⟨0, by omega⟩, true), ?_⟩
      simpa [IsDenseCentralSide, centralSideLength, centralSide,
        centralCut] using hright
  · rcases hside with hleft | hright
    · refine ⟨(⟨1, by omega⟩, false), ?_⟩
      change 2 * (N / 2 - 1 + 1) + 3 ≤
        3 * (A.filter fun x ↦ x < N / 2 - 1 + 1).card
      simpa only [hstep₁] using hleft
    · refine ⟨(⟨1, by omega⟩, true), ?_⟩
      change 2 * (N - (N / 2 - 1 + 1)) + 3 ≤
        3 * (A.filter fun x ↦ N / 2 - 1 + 1 ≤ x).card
      simpa only [hstep₁] using hright
  · rcases hside with hleft | hright
    · refine ⟨(⟨2, by omega⟩, false), ?_⟩
      change 2 * (N / 2 - 1 + 2) + 3 ≤
        3 * (A.filter fun x ↦ x < N / 2 - 1 + 2).card
      simpa only [hstep₂] using hleft
    · refine ⟨(⟨2, by omega⟩, true), ?_⟩
      change 2 * (N - (N / 2 - 1 + 2)) + 3 ≤
        3 * (A.filter fun x ↦ N / 2 - 1 + 2 ≤ x).card
      simpa only [hstep₂] using hright

/-- A maximum-cardinality member of the nonempty six-element family of
dense central sides. -/
lemma exists_maximal_denseCentralSide
    {A : Finset ℕ} {N : ℕ} (hN : 5 ≤ N)
    (hdense : 2 * N + 3 ≤ 3 * A.card) :
    ∃ i : CentralSideIndex,
      IsDenseCentralSide A N i ∧
        ∀ j : CentralSideIndex, IsDenseCentralSide A N j →
          (centralSide A N j).card ≤ (centralSide A N i).card := by
  classical
  let I := (Finset.univ : Finset CentralSideIndex).filter
    (IsDenseCentralSide A N)
  have hI : I.Nonempty := by
    obtain ⟨i, hi⟩ := exists_denseCentralSide hN hdense
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨i, hiI, himax⟩ := Finset.exists_max_image I
    (fun j ↦ (centralSide A N j).card) hI
  refine ⟨i, (Finset.mem_filter.mp hiI).2, ?_⟩
  intro j hj
  exact himax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

lemma consecutive_gap_lt_card_of_maximal_denseCentralSide
    {A : Finset ℕ} {N y z : ℕ} (hN : 5 ≤ N)
    (hAN : A ⊆ Finset.range N)
    (hglobal : 2 * N + 3 ≤ 3 * A.card)
    {i : CentralSideIndex} (hi : IsDenseCentralSide A N i)
    (himax : ∀ j : CentralSideIndex, IsDenseCentralSide A N j →
      (centralSide A N j).card ≤ (centralSide A N i).card)
    (hy : y ∈ A) (hz : z ∈ A) (hyz : y < z)
    (hconsec : ∀ w ∈ A, y < w → w < z → False) :
    z - y < (centralSide A N i).card := by
  have hm : 2 ≤ N / 2 := by omega
  have hstep₁ : N / 2 - 1 + 1 = N / 2 := by omega
  have hstep₂ : N / 2 - 1 + 2 = N / 2 + 1 := by omega
  have ht := centralCut_eq_cases hN i
  have hside : 2 * centralCut N i + 3 ≤
        3 * (centralSide A N i).card ∨
      2 * (N - centralCut N i) + 3 ≤
        3 * (centralSide A N i).card := by
    cases hright : i.2
    · left
      simpa [IsDenseCentralSide, centralSideLength, centralSide,
        hright] using hi
    · right
      simpa [IsDenseCentralSide, centralSideLength, centralSide,
        hright] using hi
  have hmaxLeft : ∀ u : ℕ,
      (u = N / 2 - 1 ∨ u = N / 2 ∨ u = N / 2 + 1) →
      2 * u + 3 ≤ 3 * (A.filter fun x ↦ x < u).card →
      (A.filter fun x ↦ x < u).card ≤
        (centralSide A N i).card := by
    intro u hu huDense
    rcases hu with rfl | rfl | rfl
    · have h := himax (⟨0, by omega⟩, false) (by
        simpa [IsDenseCentralSide, centralSideLength, centralSide,
          centralCut] using huDense)
      simpa [centralSide, centralCut] using h
    · have h := himax (⟨1, by omega⟩, false) (by
        change 2 * (N / 2 - 1 + 1) + 3 ≤
          3 * (A.filter fun x ↦ x < N / 2 - 1 + 1).card
        simpa only [hstep₁] using huDense)
      change (A.filter fun x ↦ x < N / 2 - 1 + 1).card ≤ _ at h
      simpa only [hstep₁] using h
    · have h := himax (⟨2, by omega⟩, false) (by
        change 2 * (N / 2 - 1 + 2) + 3 ≤
          3 * (A.filter fun x ↦ x < N / 2 - 1 + 2).card
        simpa only [hstep₂] using huDense)
      change (A.filter fun x ↦ x < N / 2 - 1 + 2).card ≤ _ at h
      simpa only [hstep₂] using h
  have hmaxRight : ∀ u : ℕ,
      (u = N / 2 - 1 ∨ u = N / 2 ∨ u = N / 2 + 1) →
      2 * (N - u) + 3 ≤ 3 * (A.filter fun x ↦ u ≤ x).card →
      (A.filter fun x ↦ u ≤ x).card ≤
        (centralSide A N i).card := by
    intro u hu huDense
    rcases hu with rfl | rfl | rfl
    · have h := himax (⟨0, by omega⟩, true) (by
        simpa [IsDenseCentralSide, centralSideLength, centralSide,
          centralCut] using huDense)
      simpa [centralSide, centralCut] using h
    · have h := himax (⟨1, by omega⟩, true) (by
        change 2 * (N - (N / 2 - 1 + 1)) + 3 ≤
          3 * (A.filter fun x ↦ N / 2 - 1 + 1 ≤ x).card
        simpa only [hstep₁] using huDense)
      change (A.filter fun x ↦ N / 2 - 1 + 1 ≤ x).card ≤ _ at h
      simpa only [hstep₁] using h
    · have h := himax (⟨2, by omega⟩, true) (by
        change 2 * (N - (N / 2 - 1 + 2)) + 3 ≤
          3 * (A.filter fun x ↦ N / 2 - 1 + 2 ≤ x).card
        simpa only [hstep₂] using huDense)
      change (A.filter fun x ↦ N / 2 - 1 + 2 ≤ x).card ≤ _ at h
      simpa only [hstep₂] using h
  exact consecutive_gap_lt_maximal_central_dense_card hN hAN hglobal
    ht hside hmaxLeft hmaxRight hy hz hyz hconsec

def ConsecutiveGapsLt (A : Finset ℕ) (M : ℕ) : Prop :=
  ∀ y ∈ A, ∀ z ∈ A, y < z →
    (∀ w ∈ A, y < w → w < z → False) → z - y < M

/-- A ternary-generating core propagates through an ambient finite set when
every consecutive ambient gap occurs as a difference inside the core. -/
lemma ternaryGenerates_of_core_and_short_gaps
    {A B : Finset ℕ} {p q : ℕ}
    (hBA : B ⊆ A) (hBne : B.Nonempty)
    (hgen : TernaryGenerates B p q)
    (hdiff : ∀ d : ℕ, 0 < d → d < B.card →
      ∃ u ∈ B, u + d ∈ B)
    (hgaps : ConsecutiveGapsLt A B.card) :
    TernaryGenerates A p q := by
  refine ⟨hBA hgen.1, hBA hgen.2.1, ?_⟩
  intro C hCA hpC hqC hclosed
  let D : Set ℕ := {x | x ∈ B ∧ x ∈ C}
  have hpD : p ∈ D := ⟨hgen.1, hpC⟩
  have hqD : q ∈ D := ⟨hgen.2.1, hqC⟩
  have hDclosed : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ z ∈ B,
      z + a = b + c → z ∈ D := by
    intro a ha b hb c hc z hzB hrel
    exact ⟨hzB, hclosed a ha.2 b hb.2 c hc.2 z (hBA hzB) hrel⟩
  have hBC : (B : Set ℕ) ⊆ C := by
    intro x hx
    exact (hgen.2.2 D (fun _ h ↦ h.1) hpD hqD hDclosed hx).2
  obtain ⟨b₀, hb₀B⟩ := hBne
  have hb₀A : b₀ ∈ A := hBA hb₀B
  have hb₀C : b₀ ∈ C := hBC hb₀B
  have hright : ∀ z ∈ A, b₀ ≤ z → z ∈ C := by
    intro z
    induction z using Nat.strong_induction_on with
    | h z ih =>
        intro hzA hbz
        by_cases hzb : z = b₀
        · simpa [hzb] using hb₀C
        · have hbz' : b₀ < z := by omega
          let P := A.filter fun x ↦ x < z
          have hPne : P.Nonempty := by
            exact ⟨b₀, Finset.mem_filter.mpr ⟨hb₀A, hbz'⟩⟩
          let y := P.max' hPne
          have hyP : y ∈ P := P.max'_mem hPne
          have hyA : y ∈ A := (Finset.mem_filter.mp hyP).1
          have hyz : y < z := (Finset.mem_filter.mp hyP).2
          have hb₀y : b₀ ≤ y := by
            exact P.le_max' b₀ (Finset.mem_filter.mpr ⟨hb₀A, hbz'⟩)
          have hconsec : ∀ w ∈ A, y < w → w < z → False := by
            intro w hwA hyw hwz
            have hwP : w ∈ P := Finset.mem_filter.mpr ⟨hwA, hwz⟩
            have hwy : w ≤ y := P.le_max' w hwP
            omega
          have hgap : z - y < B.card :=
            hgaps y hyA z hzA hyz hconsec
          have hdpos : 0 < z - y := by omega
          obtain ⟨u, huB, hudB⟩ := hdiff (z - y) hdpos hgap
          have hyC : y ∈ C := ih y hyz hyA hb₀y
          apply hclosed u (hBC huB) y hyC (u + (z - y))
            (hBC hudB) z hzA
          omega
  have hleftAux : ∀ k : ℕ, ∀ z ∈ A, z ≤ b₀ →
      b₀ - z = k → z ∈ C := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro z hzA hzb hk
        by_cases hzbEq : z = b₀
        · simpa [hzbEq] using hb₀C
        · have hzb' : z < b₀ := by omega
          let P := A.filter fun x ↦ z < x
          have hPne : P.Nonempty := by
            exact ⟨b₀, Finset.mem_filter.mpr ⟨hb₀A, hzb'⟩⟩
          let x := P.min' hPne
          have hxP : x ∈ P := P.min'_mem hPne
          have hxA : x ∈ A := (Finset.mem_filter.mp hxP).1
          have hzx : z < x := (Finset.mem_filter.mp hxP).2
          have hxb₀ : x ≤ b₀ := by
            exact P.min'_le b₀ (Finset.mem_filter.mpr ⟨hb₀A, hzb'⟩)
          have hconsec : ∀ w ∈ A, z < w → w < x → False := by
            intro w hwA hzw hwx
            have hwP : w ∈ P := Finset.mem_filter.mpr ⟨hwA, hzw⟩
            have hxw : x ≤ w := P.min'_le w hwP
            omega
          have hgap : x - z < B.card :=
            hgaps z hzA x hxA hzx hconsec
          have hdpos : 0 < x - z := by omega
          obtain ⟨u, huB, hudB⟩ := hdiff (x - z) hdpos hgap
          have hdist : b₀ - x < k := by omega
          have hxC : x ∈ C := ih (b₀ - x) hdist x hxA hxb₀ rfl
          apply hclosed (u + (x - z)) (hBC hudB) x hxC u
            (hBC huB) z hzA
          omega
  intro z hzA
  rcases le_total b₀ z with hbz | hzb
  · exact hright z hzA hbz
  · exact hleftAux (b₀ - z) z hzA hzb rfl

/-- Balasubramanian--Pandey's dense structured-set proposition, in the
universal ternary-generation form needed for affine propagation. -/
theorem exists_adjacent_ternaryGenerates_of_dense
    {A : Finset ℕ} {N : ℕ}
    (hAN : A ⊆ Finset.range N)
    (hdense : 2 * N + 3 ≤ 3 * A.card) :
    ∃ p : ℕ, TernaryGenerates A p (p + 1) := by
  induction N using Nat.strong_induction_on generalizing A with
  | h N ih =>
      have hcardle : A.card ≤ N := by
        simpa using Finset.card_le_card hAN
      by_cases hNsmall : N < 5
      · have hcardEq : A.card = N := by omega
        have hAeq : A = Finset.range N :=
          Finset.eq_of_subset_of_card_le hAN (by simpa [hcardEq])
        have hNthree : 3 ≤ N := by omega
        have hrange : Finset.range N = Finset.Icc 0 (N - 1) := by
          ext x
          simp only [Finset.mem_range, Finset.mem_Icc]
          omega
        refine ⟨0, ?_⟩
        rw [hAeq, hrange]
        simpa using ternaryGenerates_Icc (l := 0) (u := N - 1)
          (by omega)
      · have hN : 5 ≤ N := by omega
        obtain ⟨i, hiDense, hiMax⟩ :=
          exists_maximal_denseCentralSide hN hdense
        let t := centralCut N i
        let B := centralSide A N i
        have ht : 0 < t ∧ t < N := centralCut_pos_lt hN i
        have hBA : B ⊆ A := centralSide_subset i
        have hBne : B.Nonempty := by
          apply Finset.card_pos.mp
          change 0 < (centralSide A N i).card
          have hi := hiDense
          simp only [IsDenseCentralSide] at hi
          have hlen : 0 < centralSideLength N i := by
            have hcut := centralCut_pos_lt hN i
            simp only [centralSideLength]
            split <;> omega
          omega
        have hgaps : ConsecutiveGapsLt A B.card := by
          intro y hy z hz hyz hconsec
          exact consecutive_gap_lt_card_of_maximal_denseCentralSide
            hN hAN hdense hiDense hiMax hy hz hyz hconsec
        have hdiff : ∀ d : ℕ, 0 < d → d < B.card →
            ∃ u ∈ B, u + d ∈ B := by
          intro d hd hdB
          cases hright : i.2
          · have hBIco : B ⊆ Finset.Ico 0 t := by
              intro x hx
              have hx' : x ∈ A.filter fun x ↦ x < t := by
                simpa [B, centralSide, hright, t] using hx
              exact Finset.mem_Ico.mpr ⟨Nat.zero_le _,
                (Finset.mem_filter.mp hx').2⟩
            have hBdense : 2 * (t - 0) + 3 ≤ 3 * B.card := by
              have hi := hiDense
              simpa [IsDenseCentralSide, centralSideLength, B,
                centralSide, hright, t] using hi
            exact exists_difference_of_dense_Ico hBIco hd hdB hBdense
          · have hBIco : B ⊆ Finset.Ico t N := by
              intro x hx
              have hx' : x ∈ A.filter fun x ↦ t ≤ x := by
                simpa [B, centralSide, hright, t] using hx
              exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hx').2,
                Finset.mem_range.mp (hAN (hBA hx))⟩
            have hBdense : 2 * (N - t) + 3 ≤ 3 * B.card := by
              have hi := hiDense
              simpa [IsDenseCentralSide, centralSideLength, B,
                centralSide, hright, t] using hi
            exact exists_difference_of_dense_Ico hBIco hd hdB hBdense
        have hBgen : ∃ p : ℕ, TernaryGenerates B p (p + 1) := by
          cases hright : i.2
          · have hBRange : B ⊆ Finset.range t := by
              intro x hx
              have hx' : x ∈ A.filter fun x ↦ x < t := by
                simpa [B, centralSide, hright, t] using hx
              exact Finset.mem_range.mpr (Finset.mem_filter.mp hx').2
            have hBdense : 2 * t + 3 ≤ 3 * B.card := by
              have hi := hiDense
              simpa [IsDenseCentralSide, centralSideLength, B,
                centralSide, hright, t] using hi
            exact ih t ht.2 hBRange hBdense
          · let B' := translateDown B t
            have hBt : ∀ x ∈ B, t ≤ x := by
              intro x hx
              have hx' : x ∈ A.filter fun x ↦ t ≤ x := by
                simpa [B, centralSide, hright, t] using hx
              exact (Finset.mem_filter.mp hx').2
            have hB'Range : B' ⊆ Finset.range (N - t) := by
              intro z hz
              obtain ⟨x, hxB, hxz⟩ := mem_translateDown.mp hz
              have hxN := Finset.mem_range.mp (hAN (hBA hxB))
              exact Finset.mem_range.mpr (by omega)
            have hB'card : B'.card = B.card :=
              card_translateDown hBt
            have hB'dense : 2 * (N - t) + 3 ≤ 3 * B'.card := by
              have hi := hiDense
              have hbase : 2 * (N - t) + 3 ≤ 3 * B.card := by
                simpa [IsDenseCentralSide, centralSideLength, B,
                  centralSide, hright, t] using hi
              simpa [hB'card] using hbase
            obtain ⟨p, hp⟩ := ih (N - t) (by omega) hB'Range hB'dense
            have hup := ternaryGenerates_of_translateDown hBt hp
            refine ⟨p + t, ?_⟩
            convert hup using 1 <;> omega
        obtain ⟨p, hp⟩ := hBgen
        exact ⟨p, ternaryGenerates_of_core_and_short_gaps
          hBA hBne hp hdiff hgaps⟩

end Erdos360

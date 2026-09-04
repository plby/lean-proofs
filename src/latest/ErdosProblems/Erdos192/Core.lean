import Mathlib

/-!
# KE92 shared definitions and basic lemmas

Definitions and foundational lemmas for the Keränen 1992 formalization.
Separated from `KE92.lean` so that bounded verification files can
import this without creating circular dependencies.
-/

namespace Erdos192

/-! ### Finite-word abelian-square-free definitions -/

def infBlock {α : Type*} (f : ℕ → α) (start len : ℕ) : List α :=
  (List.range len).map (fun j => f (start + j))

def InfAbelianSquareFree {α : Type*} [DecidableEq α] (f : ℕ → α) : Prop :=
  ∀ i l, l > 0 → ¬ (infBlock f i l).Perm (infBlock f (i + l) l)

def FinAbelianSquareFree {n : ℕ} (w : List (Fin n)) : Prop :=
  ∀ i l : ℕ, l > 0 → i + 2 * l ≤ w.length →
    ¬ (w.drop i |>.take l).Perm (w.drop (i + l) |>.take l)

def AbelianSquareFree (word : List Nat) : Prop :=
  ∀ i l : Nat, l > 0 → i + 2 * l ≤ word.length →
    ¬ (word.drop i |>.take l).Perm (word.drop (i + l) |>.take l)

def hasAbelianSquareAt (word : List Nat) (i l : Nat) : Bool :=
  if l == 0 then false
  else if i + 2 * l > word.length then false
  else (word.drop i |>.take l).isPerm (word.drop (i + l) |>.take l)

def hasAbelianSquare (word : List Nat) : Bool :=
  (List.range word.length).any fun i =>
    (List.range word.length).any fun l =>
      hasAbelianSquareAt word i l

/-! ### Parikh walk and 3-term APs -/

def parikhCount {k : ℕ} (f : ℕ → Fin k) (n : ℕ) (c : Fin k) : ℕ :=
  ((Finset.range n).filter (fun j => f j = c)).card

def parikhWalk {k : ℕ} (f : ℕ → Fin k) (n : ℕ) : Fin k → ℕ :=
  fun c => parikhCount f n c

def hasParikhAP {k : ℕ} (f : ℕ → Fin k) : Prop :=
  ∃ a b c : ℕ, a < b ∧ b < c ∧
    ∀ d : Fin k, parikhCount f a d + parikhCount f c d = 2 * parikhCount f b d

def parikhAPFree {k : ℕ} (f : ℕ → Fin k) : Prop :=
  ¬ hasParikhAP f

/-! ### Key equivalence: abelian-square-free ↔ Parikh-AP-free -/

theorem infBlock_length {α : Type*} (f : ℕ → α) (s l : ℕ) :
    (infBlock f s l).length = l := by
  simp [infBlock]

theorem parikhCount_block {k : ℕ} (f : ℕ → Fin k) (s l : ℕ) (c : Fin k) :
    ((infBlock f s l).filter (· = c)).length =
      parikhCount f (s + l) c - parikhCount f s c := by
  unfold parikhCount;
  rw [ show { j ∈ Finset.range ( s + l ) | f j = c } = Finset.filter ( fun j => f j = c ) ( Finset.range s ) ∪ Finset.filter ( fun j => f j = c ) ( Finset.Ico s ( s + l ) ) from ?_, Finset.card_union_of_disjoint ];
  · rw [ show { j ∈ Finset.Ico s ( s + l ) | f j = c } = Finset.image ( fun j => s + j ) ( Finset.filter ( fun j => f ( s + j ) = c ) ( Finset.range l ) ) from ?_, Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
    · simp +decide only [add_tsub_cancel_left];
      unfold infBlock
      rw [List.filter_map]
      induction l with
      | zero => simp
      | succ l ih =>
          rw [List.range_succ, List.filter_append, List.map_append,
            List.length_append, ih, Finset.range_add_one, Finset.filter_insert]
          by_cases h : f (s + l) = c
          · simp [h]
          · simp [h]
    · ext; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_range];
      exact ⟨ fun h => ⟨ ‹_› - s, ⟨ by omega, by simpa [ add_tsub_cancel_of_le h.1.1 ] using h.2 ⟩, by omega ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by linarith, by linarith ⟩, ha₂ ⟩ ⟩;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Ico.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
  · grind

theorem infAbelianSquareFree_iff_parikhAPFree {k : ℕ} (f : ℕ → Fin k) :
    InfAbelianSquareFree f ↔ parikhAPFree f := by
  constructor <;> intro h;
  · rintro ⟨ a, b, c, hab, hbc, h ⟩;
    have h_count_eq : ∀ d : Fin k, ((infBlock f a (b - a)).filter (· = d)).length = ((infBlock f b (c - b)).filter (· = d)).length := by
      intro d;
      rw [ parikhCount_block, parikhCount_block ];
      grind;
    have h_perm : (infBlock f a (b - a)).Perm (infBlock f b (c - b)) := by
      rw [ List.perm_iff_count ];
      simp_all +decide [ List.filter_eq ];
    have h_length_eq : b - a = c - b := by
      have := h_perm.length_eq; simp_all +decide [ infBlock ] ;
    rw [ eq_tsub_iff_add_eq_of_le ] at h_length_eq <;> try linarith;
    subst h_length_eq;
    exact ‹InfAbelianSquareFree f› a ( b - a ) ( Nat.sub_pos_of_lt hab ) ( by simpa [ add_assoc, Nat.add_sub_of_le hab.le ] using h_perm );
  · intro i l hl;
    contrapose! h;
    have h_counts : ∀ c : Fin k, parikhCount f (i + l) c - parikhCount f i c = parikhCount f (i + 2 * l) c - parikhCount f (i + l) c := by
      intro c
      have h_count_eq : ((infBlock f i l).filter (· = c)).length = ((infBlock f (i + l) l).filter (· = c)).length := by
        exact h.filter _ |> List.Perm.length_eq;
      rw [ parikhCount_block, parikhCount_block ] at * ; ring_nf at * ; aesop;
    refine' fun h => h ⟨ i, i + l, i + 2 * l, _, _, _ ⟩ <;> simp_all +decide [ two_mul, add_assoc ];
    intro c; specialize h_counts c; rw [ tsub_eq_iff_eq_add_of_le ] at h_counts;
    · linarith [ Nat.sub_add_cancel ( show parikhCount f ( i + ( l + l ) ) c ≥ parikhCount f ( i + l ) c from by exact Finset.card_mono <| by intros x hx; exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| by linarith [ Finset.mem_range.mp <| Finset.mem_filter.mp hx |>.1 ], by aesop ⟩ ) ];
    · exact Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.le_add_right _ _

/-! ### The main theorem (Keränen 1992) — basic infrastructure -/

theorem finASF_prefix {n : ℕ} (w : List (Fin n)) (hw : FinAbelianSquareFree w)
    (m : ℕ) (hm : m ≤ w.length) : FinAbelianSquareFree (w.take m) := by
  intro i l hl;
  rw [ List.drop_take, List.drop_take ];
  intro h;
  convert hw i l hl _ using 1;
  · grind;
  · exact h.trans ( by simp )

theorem finASF_drop {n : ℕ} (w : List (Fin n)) (hw : FinAbelianSquareFree w)
    (k : ℕ) : FinAbelianSquareFree (w.drop k) := by
  intro i l hl hlen hperm
  have hlen' : (k + i) + 2 * l ≤ w.length := by
    simp [List.length_drop] at hlen; omega
  apply hw (k + i) l hl hlen'
  rw [List.drop_drop, List.drop_drop] at hperm
  simp only [Nat.add_assoc] at hperm ⊢
  exact hperm

theorem finASF_subword {n : ℕ} (w : List (Fin n)) (hw : FinAbelianSquareFree w)
    (k m : ℕ) (hm : k + m ≤ w.length) : FinAbelianSquareFree (w.drop k |>.take m) :=
  finASF_prefix _ (finASF_drop w hw k) m (by simp [List.length_drop]; omega)

/-! ## Keränen's 85-uniform morphism -/

def hasAbelianSquareAtFin {n : ℕ} (word : List (Fin n)) (i l : Nat) : Bool :=
  if l == 0 then false
  else if i + 2 * l > word.length then false
  else (word.drop i |>.take l).isPerm (word.drop (i + l) |>.take l)

def isFinASF {n : ℕ} (word : List (Fin n)) : Bool :=
  !(List.range word.length |>.any fun i =>
    List.range word.length |>.any fun l =>
      hasAbelianSquareAtFin word i (l + 1))

def keranenG₀ : List (Fin 4) :=
  [0,1,2,0,2,3,2,1,2,3,
   2,0,3,2,3,1,3,0,1,0,
   2,0,1,0,3,1,0,1,2,1,
   3,1,2,1,0,2,1,2,3,2,
   0,2,1,0,1,3,0,1,0,2,
   0,3,2,1,2,3,2,0,2,3,
   1,2,1,0,2,1,2,3,2,0,
   2,3,2,1,3,2,3,0,3,1,
   3,2,1,2,0]

private def shiftFin4 (w : List (Fin 4)) : List (Fin 4) :=
  w.map fun x => ⟨(x.val + 1) % 4, by omega⟩

def keranenG (c : Fin 4) : List (Fin 4) :=
  match c with
  | ⟨0, _⟩ => keranenG₀
  | ⟨1, _⟩ => shiftFin4 keranenG₀
  | ⟨2, _⟩ => shiftFin4 (shiftFin4 keranenG₀)
  | ⟨3, _⟩ => shiftFin4 (shiftFin4 (shiftFin4 keranenG₀))

def applyKeranenG (w : List (Fin 4)) : List (Fin 4) :=
  w.flatMap keranenG

def keranenIterate : ℕ → List (Fin 4)
  | 0 => [(0 : Fin 4)]
  | n + 1 => applyKeranenG (keranenIterate n)

theorem keranenG_length (c : Fin 4) : (keranenG c).length = 85 := by
  fin_cases c <;> decide

theorem applyKeranenG_length (w : List (Fin 4)) :
    (applyKeranenG w).length = 85 * w.length := by
  induction w with
  | nil => simp [applyKeranenG]
  | cons a t ih =>
    simp only [applyKeranenG, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih, keranenG_length]; simp [List.length]; ring

theorem keranenIterate_length (n : ℕ) : (keranenIterate n).length = 85 ^ n := by
  induction n with
  | zero => simp [keranenIterate]
  | succ n ih => simp only [keranenIterate, applyKeranenG_length, ih, pow_succ]; ring

theorem isFinASF_sound (w : List (Fin 4)) (h : isFinASF w = true) :
    FinAbelianSquareFree w := by
  intro i l hl hlen hperm
  have key : hasAbelianSquareAtFin w i l = true := by
    unfold hasAbelianSquareAtFin
    have h1 : (l == 0) = false := by simp; omega
    have h2 : (i + 2 * l > w.length) = false := by simp; omega
    simp [h1, h2, List.isPerm_iff, hperm]
  have hfalse : isFinASF w = false := by
    unfold isFinASF
    simp only [Bool.eq_false_iff, Bool.not_not_eq]
    rw [List.any_eq_true]
    exact ⟨i, List.mem_range.mpr (by omega), by
      rw [List.any_eq_true]
      exact ⟨l - 1, List.mem_range.mpr (by omega), by
        show hasAbelianSquareAtFin w i (l - 1 + 1) = true
        rw [Nat.sub_add_cancel hl]; exact key⟩⟩
  simp_all

theorem singleton_finASF (c : Fin 4) : FinAbelianSquareFree [c] := by
  intro i l hl hlen; simp at hlen; omega

theorem isFinASF_complete (w : List (Fin 4)) (hw : FinAbelianSquareFree w) :
    isFinASF w = true := by
  contrapose! hw;
  unfold isFinASF at hw;
  simp_all +decide [ List.any_eq_true ];
  obtain ⟨ i, hi, j, hj, h ⟩ := hw;
  unfold hasAbelianSquareAtFin at h;
  simp_all +decide [ List.isPerm_iff ];
  exact fun H => H i ( j + 1 ) ( Nat.succ_pos _ ) h.1 h.2

end Erdos192

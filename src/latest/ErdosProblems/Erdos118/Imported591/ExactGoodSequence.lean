import ErdosProblems.Erdos118.Imported591.GoodSequenceTwo

open Ordinal

namespace Erdos118.Negative.Exact

open WeakPigeon

/-!
This file isolates the literal height-two good sequences used in
Hajnal--Larson, rather than identifying them with arbitrary nested lists.
For `s = [a₀, ..., aₘ₋₁]`, the flattened word is

`m, |a₀|, a₀..., |a₁|, a₁..., ..., |aₘ₋₁|, aₘ₋₁...`.

The source family consists of those `s` for which this word is strictly
increasing.  In particular, each level marker really is the number of
coordinates which follow it in that level.
-/

def levelWord (a : List ℕ) : List ℕ := a.length :: a

def word (s : G2) : List ℕ := s.length :: s.flatMap levelWord

/-- Literal source-good sequences at height two. -/
def G : Type := {s : G2 // (word s).Pairwise (· < ·)}

instance : LT G := ⟨fun s t ↦ G2LT s.1 t.1⟩

instance gRelIsWellOrder :
    IsWellOrder G ((· < ·) : G → G → Prop) := by
  refine
    { wf := InvImage.wf Subtype.val g2IsWellOrder.wf
      trichotomous := ?_ }
  intro a b hab hba
  rcases lt_trichotomy (show OrderedG2 from a.1)
      (show OrderedG2 from b.1) with h | h | h
  · exact (hab h).elim
  · exact Subtype.ext h
  · exact (hba h).elim

noncomputable instance : LinearOrder G := by
  letI : DecidableRel ((· < ·) : G → G → Prop) := Classical.decRel _
  exact linearOrderOfSTO ((· < ·) : G → G → Prop)

instance : WellFoundedLT G := ⟨gRelIsWellOrder.wf⟩

@[simp] theorem levelWord_length (a : List ℕ) :
    (levelWord a).length = a.length + 1 := by
  simp [levelWord]

@[simp] theorem word_ne_nil (s : G2) : word s ≠ [] := by
  simp [word]

/-! ## A source-faithful normalization

At a current lower bound `q`, an input body `a` is sent to a body of length
`q + |a| + 1`.  Its first `|a|` gaps encode `a`; the remaining `q+1` zero
gaps merely pad the body to the length asserted by its marker.  The last
coordinate becomes the lower bound for the next level.
-/

def marker (q : ℕ) (a : List ℕ) : ℕ := q + a.length + 1

def body (q : ℕ) (a : List ℕ) : List ℕ :=
  Erdos590.Larson.intoInc (marker q a + 1)
    (a ++ List.replicate (q + 1) 0)

@[simp] theorem body_length (q : ℕ) (a : List ℕ) :
    (body q a).length = marker q a := by
  simp [body, marker]
  omega

theorem marker_lt_mem_body {q : ℕ} {a : List ℕ} {x : ℕ}
    (hx : x ∈ body q a) : marker q a < x := by
  have h := Erdos590.Larson.mem_intoInc_ge hx
  exact lt_of_lt_of_le (Nat.lt_succ_self (marker q a)) h

theorem level_pairwise (q : ℕ) (a : List ℕ) :
    (marker q a :: body q a).Pairwise (· < ·) := by
  rw [List.pairwise_cons]
  exact ⟨fun _ hx ↦ marker_lt_mem_body hx,
    Erdos590.Larson.pairwise_intoInc _ _⟩

theorem q_lt_marker (q : ℕ) (a : List ℕ) : q < marker q a := by
  simp [marker]

def lastBound (q : ℕ) (a : List ℕ) : ℕ :=
  marker q a + (body q a).sum + 1

theorem marker_lt_lastBound (q : ℕ) (a : List ℕ) :
    marker q a < lastBound q a := by
  simp [lastBound]

theorem nat_le_sum_of_mem {x : ℕ} : ∀ {xs : List ℕ}, x ∈ xs → x ≤ xs.sum
  | [], h => by simp at h
  | y :: ys, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact (nat_le_sum_of_mem h).trans (Nat.le_add_left _ _)

theorem mem_body_lt_lastBound {q : ℕ} {a : List ℕ} {x : ℕ}
    (hx : x ∈ body q a) : x < lastBound q a := by
  have hxsum : x ≤ (body q a).sum := nat_le_sum_of_mem hx
  simp only [lastBound]
  omega

def normalizeTail : ℕ → List (List ℕ) → List (List ℕ)
  | _, [] => []
  | q, a :: s => body q a :: normalizeTail (lastBound q a) s

def normalize (s : G2) : G2 := normalizeTail s.length s

@[simp] theorem normalizeTail_length (q : ℕ) (s : List (List ℕ)) :
    (normalizeTail q s).length = s.length := by
  induction s generalizing q with
  | nil => rfl
  | cons a s ih => simp [normalizeTail, ih]

@[simp] theorem normalize_length (s : G2) : (normalize s).length = s.length := by
  simp [normalize]

theorem normalizeTail_spec : ∀ (q : ℕ) (s : List (List ℕ)),
    (∀ x ∈ (normalizeTail q s).flatMap levelWord, q < x) ∧
      ((normalizeTail q s).flatMap levelWord).Pairwise (· < ·) := by
  intro q s
  induction s generalizing q with
  | nil => simp [normalizeTail]
  | cons a s ih =>
      have htail := ih (lastBound q a)
      have hqmark : q < marker q a := q_lt_marker q a
      have hlevel : (marker q a :: body q a).Pairwise (· < ·) :=
        level_pairwise q a
      have hcross : ∀ x ∈ marker q a :: body q a,
          ∀ y ∈ (normalizeTail (lastBound q a) s).flatMap levelWord,
            x < y := by
        intro x hx y hy
        have hy' := htail.1 y hy
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact (marker_lt_lastBound q a).trans hy'
        · exact (mem_body_lt_lastBound hx).trans hy'
      simp only [normalizeTail, List.flatMap_cons, levelWord, body_length]
      constructor
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hqmark
          · exact hqmark.trans (marker_lt_mem_body hx)
        · exact (q_lt_marker q a).trans
            ((marker_lt_lastBound q a).trans (htail.1 x hx))
      · rw [List.pairwise_append]
        exact ⟨hlevel, htail.2, hcross⟩

theorem normalize_good (s : G2) : (word (normalize s)).Pairwise (· < ·) := by
  rw [word, normalize_length]
  change (s.length :: (normalizeTail s.length s).flatMap levelWord).Pairwise (· < ·)
  rw [List.pairwise_cons]
  exact normalizeTail_spec s.length s

def normalized (s : G2) : G := ⟨normalize s, normalize_good s⟩

/-! The order-preservation proof is kept separate from the structural
validity proof above. -/

theorem lex_append_of_length_eq {α : Type*} {r : α → α → Prop}
    {s t : List α} (h : List.Lex r s t) (hlen : s.length = t.length)
    (u v : List α) : List.Lex r (s ++ u) (t ++ v) := by
  induction h with
  | nil => simp at hlen
  | @rel a b s t hab => exact List.Lex.rel hab
  | @cons a s t h ih =>
      exact List.Lex.cons (ih (by simpa using hlen))

theorem body_SL_mono {q : ℕ} {a b : List ℕ} (hab : SL a b) :
    SL (body q a) (body q b) := by
  change List.Shortlex (· < ·) a b at hab
  change List.Shortlex (· < ·) (body q a) (body q b)
  rw [List.shortlex_def] at hab ⊢
  rcases hab with hlen | ⟨hlen, hlex⟩
  · left
    simp only [body_length, marker]
    omega
  · right
    have hmarker : marker q a = marker q b := by simp [marker, hlen]
    refine ⟨by simp [body_length, hmarker], ?_⟩
    unfold body
    rw [hmarker]
    apply (Erdos590.Larson.lex_intoInc_iff _ _ _).2
    exact lex_append_of_length_eq hlex hlen
      (List.replicate (q + 1) 0) (List.replicate (q + 1) 0)

theorem normalizeTail_lex_mono : ∀ {q : ℕ} {s t : List (List ℕ)},
    List.Lex SL s t →
      List.Lex SL (normalizeTail q s) (normalizeTail q t) := by
  intro q s t hst
  induction hst generalizing q with
  | nil => simp [normalizeTail]
  | @rel a b s t hab =>
      exact List.Lex.rel (body_SL_mono hab)
  | @cons a s t hst ih =>
      simp only [normalizeTail]
      exact List.Lex.cons (ih (q := lastBound q a))

theorem normalize_mono {s t : G2} (hst : G2LT s t) :
    G2LT (normalize s) (normalize t) := by
  change List.Shortlex SL s t at hst
  change List.Shortlex SL (normalize s) (normalize t)
  rw [List.shortlex_def] at hst ⊢
  rcases hst with hlen | ⟨hlen, hlex⟩
  · left
    simpa using hlen
  · right
    refine ⟨by simpa using hlen, ?_⟩
    unfold normalize
    rw [hlen]
    exact normalizeTail_lex_mono hlex

noncomputable def normalizeEmbedding :
    G2LT ↪r ((· < ·) : G → G → Prop) :=
  RelEmbedding.ofMonotone normalized (fun _ _ h ↦ normalize_mono h)

noncomputable def inclusionEmbedding :
    ((· < ·) : G → G → Prop) ↪r
      ((· < ·) : OrderedG2 → OrderedG2 → Prop) :=
  RelEmbedding.ofMonotone (fun s : G ↦ (s.1 : OrderedG2))
    (fun _ _ h ↦ h)

/-- Exact order type of the literal source-good sequences. -/
theorem type_G : typeLT G = ω ^ (ω ^ 2) := by
  apply le_antisymm
  · exact inclusionEmbedding.ordinal_type_le.trans_eq orderedG2_type
  · rw [← g2_type]
    exact normalizeEmbedding.ordinal_type_le

end Erdos118.Negative.Exact

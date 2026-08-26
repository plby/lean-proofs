import ErdosProblems.Erdos118.Ordinal
import ErdosProblems.Erdos118.Imported591.ExactGoodSequence

/-!
Literal height-two good sequences retain their exact order type when all
word coordinates are required to lie in an arbitrary infinite subset of ℕ.
The construction pads bodies and the outer list: simply mapping coordinates
would not preserve the requirement that markers are actual lengths.
-/

open Ordinal

namespace Erdos118.CoordinateModel

open Negative Negative.Exact WeakPigeon Erdos590.Larson

def Supported (H : Set ℕ) : Set G := {s | ∀ x ∈ word s.1, x ∈ H}

def marker (f : ℕ → ℕ) (q : ℕ) (a : List ℕ) : ℕ :=
  f (q + a.length + 1)

def body (f : ℕ → ℕ) (q : ℕ) (a : List ℕ) : List ℕ :=
  (intoInc (marker f q a + 1)
    (a ++ List.replicate (marker f q a - a.length) 0)).map f

theorem length_le_marker {f : ℕ → ℕ} (hf : StrictMono f)
    (q : ℕ) (a : List ℕ) : a.length ≤ marker f q a := by
  have h : q + a.length + 1 ≤ f (q + a.length + 1) := hf.le_apply
  unfold marker
  omega

@[simp] theorem body_length {f : ℕ → ℕ} (hf : StrictMono f)
    (q : ℕ) (a : List ℕ) : (body f q a).length = marker f q a := by
  simp only [body, List.length_map, length_intoInc, List.length_append,
    List.length_replicate]
  exact Nat.add_sub_of_le (length_le_marker hf q a)

theorem q_lt_marker {f : ℕ → ℕ} (hf : StrictMono f)
    (q : ℕ) (a : List ℕ) : q < marker f q a := by
  have h : q + a.length + 1 ≤ f (q + a.length + 1) := hf.le_apply
  unfold marker
  omega

theorem marker_lt_mem_body {f : ℕ → ℕ} (hf : StrictMono f)
    {q : ℕ} {a : List ℕ} {x : ℕ} (hx : x ∈ body f q a) :
    marker f q a < x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have hi' := mem_intoInc_ge hi
  exact lt_of_lt_of_le (by omega) hf.le_apply

theorem level_pairwise {f : ℕ → ℕ} (hf : StrictMono f)
    (q : ℕ) (a : List ℕ) :
    (marker f q a :: body f q a).Pairwise (· < ·) := by
  rw [List.pairwise_cons]
  refine ⟨fun _ hx ↦ marker_lt_mem_body hf hx, ?_⟩
  rw [body, List.pairwise_map]
  exact (pairwise_intoInc _ _).imp (fun h ↦ hf h)

theorem level_supported (f : ℕ → ℕ) (q : ℕ) (a : List ℕ) :
    ∀ x ∈ marker f q a :: body f q a, x ∈ Set.range f := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Set.mem_range_self _
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact Set.mem_range_self _

def lastBound (f : ℕ → ℕ) (q : ℕ) (a : List ℕ) : ℕ :=
  marker f q a + (body f q a).sum + 1

theorem level_lt_lastBound (f : ℕ → ℕ) (q : ℕ) (a : List ℕ) :
    ∀ x ∈ marker f q a :: body f q a, x < lastBound f q a := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · simp [lastBound]
  · have h := nat_le_sum_of_mem hx
    unfold lastBound
    omega

def normalizeTail (f : ℕ → ℕ) : ℕ → G2 → G2
  | _, [] => []
  | q, a :: s => body f q a :: normalizeTail f (lastBound f q a) s

@[simp] theorem normalizeTail_length (f : ℕ → ℕ) (q : ℕ) (s : G2) :
    (normalizeTail f q s).length = s.length := by
  induction s generalizing q with
  | nil => rfl
  | cons a s ih => simp [normalizeTail, ih]

theorem normalizeTail_spec {f : ℕ → ℕ} (hf : StrictMono f)
    (q : ℕ) (s : G2) :
    (∀ x ∈ (normalizeTail f q s).flatMap levelWord, q < x) ∧
    ((normalizeTail f q s).flatMap levelWord).Pairwise (· < ·) ∧
    (∀ x ∈ (normalizeTail f q s).flatMap levelWord, x ∈ Set.range f) := by
  induction s generalizing q with
  | nil => simp [normalizeTail]
  | cons a s ih =>
    have htail := ih (lastBound f q a)
    have hqmark := q_lt_marker hf q a
    have hmarklast := level_lt_lastBound f q a _ (List.mem_cons_self ..)
    have hlevel := level_pairwise hf q a
    have hcross : ∀ x ∈ marker f q a :: body f q a,
        ∀ y ∈ (normalizeTail f (lastBound f q a) s).flatMap levelWord, x < y :=
      fun x hx y hy ↦ (level_lt_lastBound f q a x hx).trans (htail.1 y hy)
    simp only [normalizeTail, List.flatMap_cons, levelWord, body_length hf]
    refine ⟨?_, List.pairwise_append.mpr ⟨hlevel, htail.2.1, hcross⟩, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hqmark
        · exact hqmark.trans (marker_lt_mem_body hf hx)
      · exact hqmark.trans (hmarklast.trans (htail.1 x hx))
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact level_supported f q a x hx
      · exact htail.2.2 x hx

def padded (f : ℕ → ℕ) (s : G2) : G2 :=
  List.replicate (f s.length - s.length) [] ++ s

@[simp] theorem padded_length {f : ℕ → ℕ} (hf : StrictMono f) (s : G2) :
    (padded f s).length = f s.length := by
  simp only [padded, List.length_append, List.length_replicate]
  exact Nat.sub_add_cancel hf.le_apply

def normalize (f : ℕ → ℕ) (s : G2) : G2 :=
  normalizeTail f (f s.length) (padded f s)

@[simp] theorem normalize_length {f : ℕ → ℕ} (hf : StrictMono f) (s : G2) :
    (normalize f s).length = f s.length := by
  simp [normalize, padded_length hf]

theorem normalize_good {f : ℕ → ℕ} (hf : StrictMono f) (s : G2) :
    (word (normalize f s)).Pairwise (· < ·) := by
  rw [word, normalize_length hf, List.pairwise_cons]
  exact ⟨(normalizeTail_spec hf _ _).1, (normalizeTail_spec hf _ _).2.1⟩

theorem normalize_supported {f : ℕ → ℕ} (hf : StrictMono f) (s : G2) :
    ∀ x ∈ word (normalize f s), x ∈ Set.range f := by
  rw [word, normalize_length hf]
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Set.mem_range_self _
  · exact (normalizeTail_spec hf _ _).2.2 x hx

theorem body_SL_mono {f : ℕ → ℕ} (hf : StrictMono f)
    {q : ℕ} {a b : List ℕ} (hab : SL a b) :
    SL (body f q a) (body f q b) := by
  change List.Shortlex (· < ·) a b at hab
  change List.Shortlex (· < ·) (body f q a) (body f q b)
  rw [List.shortlex_def] at hab ⊢
  rcases hab with hlen | ⟨hlen, hlex⟩
  · left
    simp only [body_length hf, marker]
    exact hf (by omega)
  · right
    have hm : marker f q a = marker f q b := by simp [marker, hlen]
    refine ⟨by simp [body_length hf, hm], ?_⟩
    unfold body
    rw [hm]
    have hp := lex_append_of_length_eq hlex hlen
      (List.replicate (marker f q b - a.length) 0)
      (List.replicate (marker f q b - b.length) 0)
    have hi := (lex_intoInc_iff (marker f q b + 1) _ _).2 hp
    have hmap : ∀ {xs ys : List ℕ}, List.Lex (· < ·) xs ys →
        List.Lex (· < ·) (xs.map f) (ys.map f) := by
      intro xs ys h
      induction h with
      | nil => simp
      | rel h => exact List.Lex.rel (hf h)
      | cons _ ih => exact List.Lex.cons ih
    exact hmap hi

theorem normalizeTail_lex_mono {f : ℕ → ℕ} (hf : StrictMono f)
    {q : ℕ} {s t : G2} (hst : List.Lex SL s t) :
    List.Lex SL (normalizeTail f q s) (normalizeTail f q t) := by
  induction hst generalizing q with
  | nil => simp [normalizeTail]
  | rel h => exact List.Lex.rel (body_SL_mono hf h)
  | @cons a s t h ih =>
    exact List.Lex.cons (ih (q := lastBound f q a))

theorem normalize_mono {f : ℕ → ℕ} (hf : StrictMono f)
    {s t : G2} (hst : G2LT s t) : G2LT (normalize f s) (normalize f t) := by
  change List.Shortlex SL s t at hst
  change List.Shortlex SL (normalize f s) (normalize f t)
  rw [List.shortlex_def] at hst ⊢
  rcases hst with hlen | ⟨hlen, hlex⟩
  · left
    simpa only [normalize_length hf] using hf hlen
  · right
    refine ⟨by simp only [normalize_length hf, hlen], ?_⟩
    unfold normalize padded
    rw [hlen]
    apply normalizeTail_lex_mono hf
    induction (List.replicate (f t.length - t.length) ([] : List ℕ)) with
    | nil => exact hlex
    | cons _ _ ih => exact List.Lex.cons ih

def normalized {f : ℕ → ℕ} (hf : StrictMono f) (s : G2) : G :=
  ⟨normalize f s, normalize_good hf s⟩

noncomputable def supportedEmbedding {f : ℕ → ℕ} (hf : StrictMono f)
    {H : Set ℕ} (hH : Set.range f ⊆ H) :
    G2LT ↪r ((· < ·) : Supported H → Supported H → Prop) :=
  RelEmbedding.ofMonotone
    (fun s ↦ ⟨normalized hf s, fun x hx ↦ hH (normalize_supported hf s x hx)⟩)
    (fun _ _ h ↦ normalize_mono hf h)

theorem type_supported {H : Set ℕ} (hH : H.Infinite) :
    typeLT (Supported H) = lambda := by
  rw [lambda_eq_natural_inner_power]
  apply le_antisymm
  · exact (RelEmbedding.ofMonotone
      (r := ((· < ·) : Supported H → Supported H → Prop))
      (s := ((· < ·) : G → G → Prop))
      (fun s : Supported H ↦ s.1) (fun _ _ h ↦ h)).ordinal_type_le.trans_eq type_G
  · rw [← g2_type]
    exact (supportedEmbedding (enumOf_strictMono hH)
      (Set.range_subset_iff.mpr (enumOf_mem hH))).ordinal_type_le

end Erdos118.CoordinateModel

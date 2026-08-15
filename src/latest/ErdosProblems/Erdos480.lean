/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
# Erdős Problem 480

Chung and Graham's reciprocal-jump argument gives the stronger finite bound
`3 / 7`: every thirteen points of `[0,1]` contain a suitable pair.  Sliding
this window and applying finite pigeonhole yields one frequently occurring
gap, from which the stated `liminf` bound follows.
-/

import Mathlib

namespace Erdos480

@[simp] lemma Nat.dist_self_add' (a k : ℕ) : Nat.dist a (a + k) = k := by
  simp [Nat.dist]
@[simp] lemma Nat.dist_add_self' (a k : ℕ) : Nat.dist (a + k) a = k := by
  simp [Nat.dist]

def jumpWeight : List ℕ → ℚ
  | a :: b :: l => 1 / (Nat.dist a b : ℚ) + jumpWeight (b :: l)
  | _ => 0

def HasUpPath (f : ℕ → ℝ) (s : Set ℕ) (c : ℚ) : Prop :=
  ∃ l : List ℕ, l ≠ [] ∧ (∀ i ∈ l, i ∈ s) ∧
    l.IsChain (fun a b => f a ≤ f b) ∧ c ≤ jumpWeight l

def HasMonoPath (f : ℕ → ℝ) (s : Set ℕ) (c : ℚ) : Prop :=
  ∃ l : List ℕ, l ≠ [] ∧ (∀ i ∈ l, i ∈ s) ∧
    (l.IsChain (fun a b => f a ≤ f b) ∨
      l.IsChain (fun a b => f b ≤ f a)) ∧ c ≤ jumpWeight l

lemma HasUpPath.toMono {f : ℕ → ℝ} {s : Set ℕ} {c : ℚ}
    (hp : HasUpPath f s c) : HasMonoPath f s c := by
  obtain ⟨l, hlne, hls, hlchain, hlweight⟩ := hp
  exact ⟨l, hlne, hls, Or.inl hlchain, hlweight⟩

lemma negUpPath_toMono {f : ℕ → ℝ} {s : Set ℕ} {c : ℚ}
    (hp : HasUpPath (fun i => -f i) s c) : HasMonoPath f s c := by
  obtain ⟨l, hlne, hls, hlchain, hlweight⟩ := hp
  refine ⟨l, hlne, hls, Or.inr ?_, hlweight⟩
  simpa only [neg_le_neg_iff] using hlchain

lemma HasUpPath.mono {f : ℕ → ℝ} {s : Set ℕ} {c d : ℚ}
    (hp : HasUpPath f s c) (hdc : d ≤ c) : HasUpPath f s d := by
  obtain ⟨l, hlne, hls, hlchain, hlweight⟩ := hp
  exact ⟨l, hlne, hls, hlchain, hdc.trans hlweight⟩

lemma HasUpPath.mono_set {f : ℕ → ℝ} {s t : Set ℕ} {c : ℚ}
    (hp : HasUpPath f s c) (hst : s ⊆ t) : HasUpPath f t c := by
  obtain ⟨l, hlne, hls, hlchain, hlweight⟩ := hp
  exact ⟨l, hlne, fun i hi => hst (hls i hi), hlchain, hlweight⟩

lemma jumpWeight_prefix_two (a b : ℕ) (l : List ℕ) :
    1 / (Nat.dist a b : ℚ) + jumpWeight l ≤ jumpWeight (a :: b :: l) := by
  cases l <;> simp [jumpWeight]

lemma jumpWeight_suffix_two (l : List ℕ) (x y : ℕ) :
    jumpWeight l + 1 / (Nat.dist x y : ℚ) ≤ jumpWeight (l ++ [x, y]) := by
  induction l with
  | nil => simp [jumpWeight]
  | cons a l ih =>
      cases l with
      | nil => simp [jumpWeight]
      | cons b t =>
          simp only [List.cons_append, jumpWeight]
          calc
            1 / (Nat.dist a b : ℚ) + jumpWeight (b :: t) +
                1 / (Nat.dist x y : ℚ) =
                1 / (Nat.dist a b : ℚ) +
                  (jumpWeight (b :: t) + 1 / (Nat.dist x y : ℚ)) := by ring
            _ ≤ 1 / (Nat.dist a b : ℚ) + jumpWeight (b :: t ++ [x, y]) := by gcongr

lemma jumpWeight_append_ge (l : List ℕ) (x : ℕ) (d : ℚ) (hl : l ≠ [])
    (hedge : ∀ z ∈ l, d ≤ 1 / (Nat.dist z x : ℚ)) :
    jumpWeight l + d ≤ jumpWeight (l ++ [x]) := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
      cases l with
      | nil =>
          simpa [jumpWeight] using hedge a (by simp)
      | cons b t =>
          simp only [List.cons_append, jumpWeight]
          calc
            1 / (Nat.dist a b : ℚ) + jumpWeight (b :: t) + d =
                1 / (Nat.dist a b : ℚ) + (jumpWeight (b :: t) + d) := by ring
            _ ≤ 1 / (Nat.dist a b : ℚ) + jumpWeight (b :: t ++ [x]) := by
              gcongr
              apply ih (by simp)
              intro z hz
              exact hedge z (by simp [hz])

lemma chain_prefix_two {f : ℕ → ℝ} {x y : ℕ} {l : List ℕ}
    (hxy : f x ≤ f y) (hy : ∀ z ∈ l, f y ≤ f z)
    (hl : l.IsChain (fun a b => f a ≤ f b)) :
    (x :: y :: l).IsChain (fun a b => f a ≤ f b) := by
  have hyl : (y :: l).IsChain (fun a b => f a ≤ f b) := by
    apply hl.cons
    intro z hz
    exact hy z (List.mem_of_mem_head? hz)
  apply hyl.cons
  intro z hz
  simp only [List.head?_cons, Option.mem_some_iff] at hz
  subst z
  exact hxy

lemma chain_suffix_two {f : ℕ → ℝ} {x y : ℕ} {l : List ℕ}
    (hl : l.IsChain (fun a b => f a ≤ f b))
    (hx : ∀ z ∈ l, f z ≤ f x) (hxy : f x ≤ f y) :
    (l ++ [x, y]).IsChain (fun a b => f a ≤ f b) := by
  apply hl.append
  · simpa [List.isChain_cons] using hxy
  · intro z hz w hw
    simp only [List.head?_cons, Option.mem_some_iff] at hw
    subst w
    exact hx z (List.mem_of_mem_getLast? hz)

lemma path_prefix_two {f : ℕ → ℝ} {s t : Set ℕ} {c : ℚ} {x y : ℕ}
    (hp : HasUpPath f s c) (hst : s ⊆ t) (hx : x ∈ t) (hy : y ∈ t)
    (hxy : f x ≤ f y) (hymin : ∀ z ∈ s, f y ≤ f z) :
    HasUpPath f t (c + 1 / (Nat.dist x y : ℚ)) := by
  obtain ⟨l, hlne, hls, hlchain, hlweight⟩ := hp
  refine ⟨x :: y :: l, by simp, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨hx, hy, fun z hz => hst (hls z hz)⟩
  · exact chain_prefix_two hxy (fun z hz => hymin z (hls z hz)) hlchain
  · calc
      c + 1 / (Nat.dist x y : ℚ) = 1 / (Nat.dist x y : ℚ) + c := by ring
      _ ≤ 1 / (Nat.dist x y : ℚ) + jumpWeight l := by gcongr
      _ ≤ jumpWeight (x :: y :: l) := jumpWeight_prefix_two x y l

lemma path_suffix_two {f : ℕ → ℝ} {s t : Set ℕ} {c : ℚ} {x y : ℕ}
    (hp : HasUpPath f s c) (hst : s ⊆ t) (hx : x ∈ t) (hy : y ∈ t)
    (hxmax : ∀ z ∈ s, f z ≤ f x) (hxy : f x ≤ f y) :
    HasUpPath f t (c + 1 / (Nat.dist x y : ℚ)) := by
  obtain ⟨l, hlne, hls, hlchain, hlweight⟩ := hp
  refine ⟨l ++ [x, y], by simp [hlne], ?_, ?_, ?_⟩
  · intro z hz
    simp at hz
    rcases hz with hz | rfl | rfl
    · exact hst (hls z hz)
    · exact hx
    · exact hy
  · exact chain_suffix_two hlchain (fun z hz => hxmax z (hls z hz)) hxy
  · calc
      c + 1 / (Nat.dist x y : ℚ) ≤
          jumpWeight l + 1 / (Nat.dist x y : ℚ) := by gcongr
      _ ≤ jumpWeight (l ++ [x, y]) := by
        exact jumpWeight_suffix_two l x y

lemma path_prefix_one {f : ℕ → ℝ} {s t : Set ℕ} {c d : ℚ} {x : ℕ}
    (hp : HasUpPath f s c) (hst : s ⊆ t) (hx : x ∈ t)
    (hxmin : ∀ z ∈ s, f x ≤ f z)
    (hedge : ∀ z ∈ s, d ≤ 1 / (Nat.dist x z : ℚ)) :
    HasUpPath f t (c + d) := by
  obtain ⟨l, hlne, hls, hlchain, hlweight⟩ := hp
  cases l with
  | nil => simp at hlne
  | cons z u =>
      refine ⟨x :: z :: u, by simp, ?_, ?_, ?_⟩
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact hx
        · exact hst (hls w (by simpa using hw))
      · apply hlchain.cons
        intro w hw
        simp only [List.head?_cons, Option.mem_some_iff] at hw
        subst w
        exact hxmin z (hls z (by simp))
      · calc
          c + d ≤ jumpWeight (z :: u) + 1 / (Nat.dist x z : ℚ) := by
            have := hedge z (hls z (by simp))
            linarith
          _ = jumpWeight (x :: z :: u) := by simp [jumpWeight, add_comm]

lemma path_suffix_one {f : ℕ → ℝ} {s t : Set ℕ} {c d : ℚ} {x : ℕ}
    (hp : HasUpPath f s c) (hst : s ⊆ t) (hx : x ∈ t)
    (hxmax : ∀ z ∈ s, f z ≤ f x)
    (hedge : ∀ z ∈ s, d ≤ 1 / (Nat.dist z x : ℚ)) :
    HasUpPath f t (c + d) := by
  obtain ⟨l, hlne, hls, hlchain, hlweight⟩ := hp
  refine ⟨l ++ [x], by simp [hlne], ?_, ?_, ?_⟩
  · intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hst (hls z hz)
    · exact hx
  · apply hlchain.append
    · simp
    · intro z hz w hw
      simp only [List.head?_cons, Option.mem_some_iff] at hw
      subst w
      exact hxmax z (hls z (List.mem_of_mem_getLast? hz))
  · calc
      c + d ≤ jumpWeight l + d := by gcongr
      _ ≤ jumpWeight (l ++ [x]) := by
        apply jumpWeight_append_ge l x d hlne
        intro z hz
        exact hedge z (hls z hz)

lemma one_div_nat_mono {u v : ℕ} (hu : 0 < u) (huv : u ≤ v) :
    (1 / (v : ℚ)) ≤ 1 / (u : ℚ) := by
  apply one_div_le_one_div_of_le
  · exact_mod_cast hu
  · exact_mod_cast huv

lemma middle_low_reciprocal (x X z Z : ℕ)
    (hx : 5 ≤ x) (hx' : x ≤ 7) (hX : 5 ≤ X) (hX' : X ≤ 7)
    (hz : z ≤ 4) (hZ : Z ≤ 4) (hxx : x ≠ X) (hzz : z ≠ Z) :
    (1 / (Nat.dist x z : ℚ)) + 1 / (Nat.dist Z X : ℚ) ≥ 1 / 3 := by
  interval_cases x <;> interval_cases X <;> interval_cases z <;> interval_cases Z <;>
    norm_num [Nat.dist] at *

lemma middle_low_reciprocal_add (a x X z Z : ℕ)
    (hx : a + 5 ≤ x) (hx' : x ≤ a + 7)
    (hX : a + 5 ≤ X) (hX' : X ≤ a + 7)
    (hz : a ≤ z) (hz' : z ≤ a + 4) (hZ : a ≤ Z) (hZ' : Z ≤ a + 4)
    (hxx : x ≠ X) (hzz : z ≠ Z) :
    (1 / (Nat.dist x z : ℚ)) + 1 / (Nat.dist Z X : ℚ) ≥ 1 / 3 := by
  have h := middle_low_reciprocal (x - a) (X - a) (z - a) (Z - a)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have ex : a + (x - a) = x := by omega
  have eX : a + (X - a) = X := by omega
  have ez : a + (z - a) = z := by omega
  have eZ : a + (Z - a) = Z := by omega
  rw [← ex, ← eX, ← ez, ← eZ, Nat.dist_add_add_left, Nat.dist_add_add_left]
  exact h

theorem five_path (f : ℕ → ℝ) (a : ℕ) :
    HasUpPath f (Set.Icc a (a + 4)) 2 := by
  let A := f a
  let B := f (a + 1)
  let C := f (a + 2)
  let D := f (a + 3)
  let E := f (a + 4)
  by_cases hAB : A ≤ B
  · by_cases hBC : B ≤ C
    · refine ⟨[a, a+1, a+2], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
      · simpa [List.isChain_cons, A, B, C] using And.intro hAB hBC
      · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]

    · have hCB : C ≤ B := le_of_not_ge hBC
      by_cases hCD : C ≤ D
      · by_cases hDE : D ≤ E
        · refine ⟨[a+2, a+3, a+4], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
          · simpa [List.isChain_cons, C, D, E] using And.intro hCD hDE
          · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
        · have hED : E ≤ D := le_of_not_ge hDE
          rcases le_total B D with hBD | hDB
          · rcases le_total A C with hAC | hCA
            · refine ⟨[a, a+2, a+1, a+3], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
              · simpa [List.isChain_cons, A, B, C, D] using ⟨hAC, hCB, hBD⟩
              · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
            · refine ⟨[a+2, a, a+1, a+3], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
              · simpa [List.isChain_cons, A, B, C, D] using ⟨hCA, hAB, hBD⟩
              · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
          · rcases le_total C E with hCE | hEC
            · refine ⟨[a+2, a+4, a+3, a+1], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
              · simpa [List.isChain_cons, B, C, D, E] using ⟨hCE, hED, hDB⟩
              · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
            · refine ⟨[a+4, a+2, a+3, a+1], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
              · simpa [List.isChain_cons, B, C, D, E] using ⟨hEC, hCD, hDB⟩
              · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
      · have hDC : D ≤ C := le_of_not_ge hCD
        refine ⟨[a+3, a+2, a+1], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
        · simpa [List.isChain_cons, B, C, D] using And.intro hDC hCB
        · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
  · have hBA : B ≤ A := le_of_not_ge hAB
    by_cases hBC : B ≤ C
    · by_cases hCD : C ≤ D
      · refine ⟨[a+1, a+2, a+3], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
        · simpa [List.isChain_cons, B, C, D] using And.intro hBC hCD
        · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
      · have hDC : D ≤ C := le_of_not_ge hCD
        by_cases hDE : D ≤ E
        · rcases le_total B D with hBD | hDB
          · rcases le_total C E with hCE | hEC
            · refine ⟨[a+1, a+3, a+2, a+4], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
              · simpa [List.isChain_cons, B, C, D, E] using ⟨hBD, hDC, hCE⟩
              · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
            · refine ⟨[a+1, a+3, a+4, a+2], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
              · simpa [List.isChain_cons, B, C, D, E] using ⟨hBD, hDE, hEC⟩
              · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
          · rcases le_total A C with hAC | hCA
            · refine ⟨[a+3, a+1, a, a+2], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
              · simpa [List.isChain_cons, A, B, C, D] using ⟨hDB, hBA, hAC⟩
              · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
            · refine ⟨[a+3, a+1, a+2, a], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
              · simpa [List.isChain_cons, A, B, C, D] using ⟨hDB, hBC, hCA⟩
              · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
        · have hED : E ≤ D := le_of_not_ge hDE
          refine ⟨[a+4, a+3, a+2], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
          · simpa [List.isChain_cons, C, D, E] using And.intro hED hDC
          · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
    · have hCB : C ≤ B := le_of_not_ge hBC
      refine ⟨[a+2, a+1, a], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
      · simpa [List.isChain_cons, A, B, C] using And.intro hCB hBA
      · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]

theorem five_path_of_endpoints (f : ℕ → ℝ) (a : ℕ)
    (hends :
      ((∀ i ∈ Set.Icc a (a + 4), f (a + 3) ≤ f i) ∧
        (∀ i ∈ Set.Icc a (a + 4), f i ≤ f (a + 4))) ∨
      ((∀ i ∈ Set.Icc a (a + 4), f (a + 4) ≤ f i) ∧
        (∀ i ∈ Set.Icc a (a + 4), f i ≤ f (a + 3)))) :
    HasUpPath f (Set.Icc a (a + 4)) (9 / 4) := by
  let A := f a
  let B := f (a + 1)
  let C := f (a + 2)
  let D := f (a + 3)
  let E := f (a + 4)
  rcases hends with hDE | hED
  · have hDA : D ≤ A := hDE.1 a (by simp [Set.mem_Icc])
    have hDB : D ≤ B := hDE.1 (a + 1) (by simp [Set.mem_Icc])
    have hDC : D ≤ C := hDE.1 (a + 2) (by simp [Set.mem_Icc])
    have hAE : A ≤ E := hDE.2 a (by simp [Set.mem_Icc])
    have hBE : B ≤ E := hDE.2 (a + 1) (by simp [Set.mem_Icc])
    have hCE : C ≤ E := hDE.2 (a + 2) (by simp [Set.mem_Icc])
    by_cases hCB : C ≤ B
    · refine ⟨[a+3, a+2, a+1, a+4], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
      · simpa [List.isChain_cons, B, C, D, E] using ⟨hDC, hCB, hBE⟩
      · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
    · have hBC : B ≤ C := le_of_not_ge hCB
      by_cases hAB : A ≤ B
      · refine ⟨[a+3, a, a+1, a+2, a+4], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
        · simpa [List.isChain_cons, A, B, C, D, E] using ⟨hDA, hAB, hBC, hCE⟩
        · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
      · have hBA : B ≤ A := le_of_not_ge hAB
        by_cases hAC : A ≤ C
        · refine ⟨[a+3, a+1, a, a+2, a+4], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
          · simpa [List.isChain_cons, A, B, C, D, E] using ⟨hDB, hBA, hAC, hCE⟩
          · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
        · have hCA : C ≤ A := le_of_not_ge hAC
          refine ⟨[a+3, a+1, a+2, a, a+4], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
          · simpa [List.isChain_cons, A, B, C, D, E] using ⟨hDB, hBC, hCA, hAE⟩
          · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
  · have hEA : E ≤ A := hED.1 a (by simp [Set.mem_Icc])
    have hEB : E ≤ B := hED.1 (a + 1) (by simp [Set.mem_Icc])
    have hEC : E ≤ C := hED.1 (a + 2) (by simp [Set.mem_Icc])
    have hAD : A ≤ D := hED.2 a (by simp [Set.mem_Icc])
    have hBD : B ≤ D := hED.2 (a + 1) (by simp [Set.mem_Icc])
    have hCD : C ≤ D := hED.2 (a + 2) (by simp [Set.mem_Icc])
    by_cases hBC : B ≤ C
    · refine ⟨[a+4, a+1, a+2, a+3], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
      · simpa [List.isChain_cons, B, C, D, E] using ⟨hEB, hBC, hCD⟩
      · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
    · have hCB : C ≤ B := le_of_not_ge hBC
      by_cases hAC : A ≤ C
      · refine ⟨[a+4, a, a+2, a+1, a+3], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
        · simpa [List.isChain_cons, A, B, C, D, E] using ⟨hEA, hAC, hCB, hBD⟩
        · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
      · have hCA : C ≤ A := le_of_not_ge hAC
        by_cases hAB : A ≤ B
        · refine ⟨[a+4, a+2, a, a+1, a+3], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
          · simpa [List.isChain_cons, A, B, C, D, E] using ⟨hEC, hCA, hAB, hBD⟩
          · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
        · have hBA : B ≤ A := le_of_not_ge hAB
          refine ⟨[a+4, a+2, a+1, a, a+3], by simp, by simp [Set.mem_Icc], ?_, ?_⟩
          · simpa [List.isChain_cons, A, B, C, D, E] using ⟨hEC, hCB, hBA, hAD⟩
          · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]

theorem eight_path (f : ℕ → ℝ) (a : ℕ) :
    HasUpPath f (Set.Icc a (a + 7)) (11 / 5) := by
  obtain ⟨x, hx, hxmin⟩ :=
    (Finset.Icc a (a + 7)).exists_min_image f (by simp)
  obtain ⟨X, hX, hXmax⟩ :=
    (Finset.Icc a (a + 7)).exists_max_image f (by simp)
  have hx' : x ∈ Set.Icc a (a + 7) := by simpa using hx
  have hX' : X ∈ Set.Icc a (a + 7) := by simpa using hX
  have hxa : a ≤ x := hx'.1
  have hxa7 : x ≤ a + 7 := hx'.2
  have hXa : a ≤ X := hX'.1
  have hXa7 : X ≤ a + 7 := hX'.2
  have hxmin' : ∀ z ∈ Set.Icc a (a + 7), f x ≤ f z := by
    intro z hz
    exact hxmin z (by simpa using hz)
  have hXmax' : ∀ z ∈ Set.Icc a (a + 7), f z ≤ f X := by
    intro z hz
    exact hXmax z (by simpa using hz)
  by_cases hxl : x ≤ a + 2
  · have hp : HasUpPath f (Set.Icc (x + 1) (x + 5)) 2 := by
      simpa [Nat.add_assoc] using five_path f (x + 1)
    have hres := path_prefix_one hp (t := Set.Icc a (a + 7))
      (fun z hz => by simp only [Set.mem_Icc] at hz ⊢; omega) hx'
      (fun z hz => hxmin' z (by simp only [Set.mem_Icc] at hz ⊢; omega))
      (fun z hz => by
        simp only [Set.mem_Icc] at hz
        apply one_div_nat_mono
        · simp [Nat.dist]
          omega
        · simp [Nat.dist]
          omega) (d := 1 / 5)
    norm_num at hres ⊢
    exact hres
  · by_cases hxr : a + 5 ≤ x
    · have hx5 : 5 ≤ x := by omega
      have hp : HasUpPath f (Set.Icc (x - 5) (x - 1)) 2 := by
        have hp' := five_path f (x - 5)
        have heq : (x - 5) + 4 = x - 1 := by omega
        rw [heq] at hp'
        exact hp'
      have hres := path_prefix_one hp (t := Set.Icc a (a + 7))
        (fun z hz => by simp only [Set.mem_Icc] at hz ⊢; omega) hx'
        (fun z hz => hxmin' z (by simp only [Set.mem_Icc] at hz ⊢; omega))
        (fun z hz => by
          simp only [Set.mem_Icc] at hz
          apply one_div_nat_mono
          · simp [Nat.dist]
            omega
          · simp [Nat.dist]
            omega) (d := 1 / 5)
      norm_num at hres ⊢
      exact hres
    · by_cases hXl : X ≤ a + 2
      · have hp : HasUpPath f (Set.Icc (X + 1) (X + 5)) 2 := by
          simpa [Nat.add_assoc] using five_path f (X + 1)
        have hres := path_suffix_one hp (t := Set.Icc a (a + 7))
          (fun z hz => by simp only [Set.mem_Icc] at hz ⊢; omega) hX'
          (fun z hz => hXmax' z (by simp only [Set.mem_Icc] at hz ⊢; omega))
          (fun z hz => by
            simp only [Set.mem_Icc] at hz
            apply one_div_nat_mono
            · simp [Nat.dist]
              omega
            · simp [Nat.dist]
              omega) (d := 1 / 5)
        norm_num at hres ⊢
        exact hres
      · by_cases hXr : a + 5 ≤ X
        · have hX5 : 5 ≤ X := by omega
          have hp : HasUpPath f (Set.Icc (X - 5) (X - 1)) 2 := by
            have hp' := five_path f (X - 5)
            have heq : (X - 5) + 4 = X - 1 := by omega
            rw [heq] at hp'
            exact hp'
          have hres := path_suffix_one hp (t := Set.Icc a (a + 7))
            (fun z hz => by simp only [Set.mem_Icc] at hz ⊢; omega) hX'
            (fun z hz => hXmax' z (by simp only [Set.mem_Icc] at hz ⊢; omega))
            (fun z hz => by
              simp only [Set.mem_Icc] at hz
              apply one_div_nat_mono
              · simp [Nat.dist]
                omega
              · simp [Nat.dist]
                omega) (d := 1 / 5)
          norm_num at hres ⊢
          exact hres
        · have hxmid : x = a + 3 ∨ x = a + 4 := by omega
          have hXmid : X = a + 3 ∨ X = a + 4 := by omega
          have hends :
              ((∀ i ∈ Set.Icc a (a + 4), f (a + 3) ≤ f i) ∧
                (∀ i ∈ Set.Icc a (a + 4), f i ≤ f (a + 4))) ∨
              ((∀ i ∈ Set.Icc a (a + 4), f (a + 4) ≤ f i) ∧
                (∀ i ∈ Set.Icc a (a + 4), f i ≤ f (a + 3))) := by
            rcases le_total (f (a + 3)) (f (a + 4)) with hDE | hED
            · left
              constructor
              · intro i hi
                have hi' : i ∈ Set.Icc a (a + 7) := by
                  simp only [Set.mem_Icc] at hi ⊢
                  omega
                rcases hxmid with rfl | rfl
                · exact hxmin' i hi'
                · exact hDE.trans (hxmin' i hi')
              · intro i hi
                have hi' : i ∈ Set.Icc a (a + 7) := by
                  simp only [Set.mem_Icc] at hi ⊢
                  omega
                rcases hXmid with rfl | rfl
                · exact (hXmax' i hi').trans hDE
                · exact hXmax' i hi'
            · right
              constructor
              · intro i hi
                have hi' : i ∈ Set.Icc a (a + 7) := by
                  simp only [Set.mem_Icc] at hi ⊢
                  omega
                rcases hxmid with rfl | rfl
                · exact hED.trans (hxmin' i hi')
                · exact hxmin' i hi'
              · intro i hi
                have hi' : i ∈ Set.Icc a (a + 7) := by
                  simp only [Set.mem_Icc] at hi ⊢
                  omega
                rcases hXmid with rfl | rfl
                · exact hXmax' i hi'
                · exact (hXmax' i hi').trans hED
          have hp := five_path_of_endpoints f a hends
          exact (hp.mono_set (by
            intro i hi
            simp only [Set.mem_Icc] at hi ⊢
            omega)).mono (d := 11 / 5) (by norm_num)

theorem thirteen_path_from_end_min (f : ℕ → ℝ) (a x : ℕ)
    (hx : x ∈ Set.Icc a (a + 12))
    (hxmin : ∀ z ∈ Set.Icc a (a + 12), f x ≤ f z)
    (hside : x ≤ a + 4 ∨ a + 8 ≤ x) :
    HasUpPath f (Set.Icc a (a + 12)) (7 / 3) := by
  have hxa : a ≤ x := hx.1
  have hxa12 : x ≤ a + 12 := hx.2
  rcases hside with hright | hleft
  · have hp8 : HasUpPath f (Set.Icc (x + 1) (x + 8)) (11 / 5) := by
      simpa [Nat.add_assoc] using eight_path f (x + 1)
    obtain ⟨y, hy, hymin⟩ :=
      (Finset.Icc (x + 1) (x + 8)).exists_min_image f (by simp)
    have hy' : y ∈ Set.Icc (x + 1) (x + 8) := by simpa using hy
    have hymin' : ∀ z ∈ Set.Icc (x + 1) (x + 8), f y ≤ f z := by
      intro z hz
      exact hymin z (by simpa using hz)
    by_cases hxy7 : Nat.dist x y ≤ 7
    · have hp := path_prefix_two hp8 (t := Set.Icc a (a + 12))
        (fun z hz => by simp only [Set.mem_Icc] at hz ⊢; omega) hx
        (by simp only [Set.mem_Icc] at hy' ⊢; omega)
        (hxmin y (by simp only [Set.mem_Icc] at hy' ⊢; omega)) hymin'
      apply hp.mono (d := 7 / 3)
      have hedge : (1 / 7 : ℚ) ≤ 1 / (Nat.dist x y : ℚ) := by
        apply one_div_nat_mono
        · simp only [Set.mem_Icc] at hy'
          simp [Nat.dist]
          omega
        · exact hxy7
      norm_num at hedge ⊢
      linarith
    · have hxy8 : Nat.dist x y = 8 := by
        simp only [Set.mem_Icc] at hy'
        simp [Nat.dist] at hxy7 ⊢
        omega
      obtain ⟨z, hz, hzmin⟩ :=
        (Finset.Icc (x + 1) (x + 5)).exists_min_image f (by simp)
      have hz' : z ∈ Set.Icc (x + 1) (x + 5) := by simpa using hz
      have hzmin' : ∀ w ∈ Set.Icc (x + 1) (x + 5), f z ≤ f w := by
        intro w hw
        exact hzmin w (by simpa using hw)
      have hp5 : HasUpPath f (Set.Icc (x + 1) (x + 5)) 2 := by
        simpa [Nat.add_assoc] using five_path f (x + 1)
      by_cases hxz3 : Nat.dist x z ≤ 3
      · have hp := path_prefix_two hp5 (t := Set.Icc a (a + 12))
          (fun w hw => by simp only [Set.mem_Icc] at hw ⊢; omega) hx
          (by simp only [Set.mem_Icc] at hz' ⊢; omega)
          (hxmin z (by simp only [Set.mem_Icc] at hz' ⊢; omega)) hzmin'
        apply hp.mono (d := 7 / 3)
        have hedge : (1 / 3 : ℚ) ≤ 1 / (Nat.dist x z : ℚ) := by
          apply one_div_nat_mono
          · simp only [Set.mem_Icc] at hz'
            simp [Nat.dist]
            omega
          · exact hxz3
        norm_num at hedge ⊢
        linarith

      · have hpA := path_prefix_two hp5 (t := Set.Icc (x + 1) (x + 8))
          (fun w hw => by simp only [Set.mem_Icc] at hw ⊢; omega) hy'
          (by simp only [Set.mem_Icc] at hz' ⊢; omega)
          (hymin' z (by simp only [Set.mem_Icc] at hz' ⊢; omega)) hzmin'
        have hpB := path_prefix_one hpA (t := Set.Icc a (a + 12))
          (fun w hw => by simp only [Set.mem_Icc] at hw ⊢; omega) hx
          (fun w hw => hxmin w (by simp only [Set.mem_Icc] at hw ⊢; omega))
          (fun w hw => by
            simp only [Set.mem_Icc] at hw
            apply one_div_nat_mono
            · simp [Nat.dist]
              omega
            · simp [Nat.dist]
              omega) (d := 1 / 8)
        apply hpB.mono (d := 7 / 3)
        have hyz4 : Nat.dist y z ≤ 4 := by
          simp only [Set.mem_Icc] at hy' hz'
          simp [Nat.dist] at hxy8 hxz3 ⊢
          omega
        have hedge : (1 / 4 : ℚ) ≤ 1 / (Nat.dist y z : ℚ) := by
          apply one_div_nat_mono
          · simp only [Set.mem_Icc] at hy' hz'
            simp [Nat.dist] at hxy8 ⊢
            omega
          · exact hyz4
        norm_num at hedge ⊢
        linarith
  · have hx8 : 8 ≤ x := by omega
    have hp8 : HasUpPath f (Set.Icc (x - 8) (x - 1)) (11 / 5) := by
      have hp := eight_path f (x - 8)
      have heq : (x - 8) + 7 = x - 1 := by omega
      rw [heq] at hp
      exact hp
    obtain ⟨y, hy, hymin⟩ :=
      (Finset.Icc (x - 8) (x - 1)).exists_min_image f (by simp; omega)
    have hy' : y ∈ Set.Icc (x - 8) (x - 1) := by simpa using hy
    have hymin' : ∀ z ∈ Set.Icc (x - 8) (x - 1), f y ≤ f z := by
      intro z hz
      exact hymin z (by simpa using hz)
    by_cases hxy7 : Nat.dist x y ≤ 7
    · have hp := path_prefix_two hp8 (t := Set.Icc a (a + 12))
        (fun z hz => by simp only [Set.mem_Icc] at hz ⊢; omega) hx
        (by simp only [Set.mem_Icc] at hy' ⊢; omega)
        (hxmin y (by simp only [Set.mem_Icc] at hy' ⊢; omega)) hymin'
      apply hp.mono (d := 7 / 3)
      have hedge : (1 / 7 : ℚ) ≤ 1 / (Nat.dist x y : ℚ) := by
        apply one_div_nat_mono
        · simp only [Set.mem_Icc] at hy'
          simp [Nat.dist]
          omega
        · exact hxy7
      norm_num at hedge ⊢
      linarith
    · have hxy8 : Nat.dist x y = 8 := by
        simp only [Set.mem_Icc] at hy'
        simp [Nat.dist] at hxy7 ⊢
        omega
      obtain ⟨z, hz, hzmin⟩ :=
        (Finset.Icc (x - 5) (x - 1)).exists_min_image f (by simp; omega)
      have hz' : z ∈ Set.Icc (x - 5) (x - 1) := by simpa using hz
      have hzmin' : ∀ w ∈ Set.Icc (x - 5) (x - 1), f z ≤ f w := by
        intro w hw
        exact hzmin w (by simpa using hw)
      have hp5 : HasUpPath f (Set.Icc (x - 5) (x - 1)) 2 := by
        have hp := five_path f (x - 5)
        have heq : (x - 5) + 4 = x - 1 := by omega
        rw [heq] at hp
        exact hp
      by_cases hxz3 : Nat.dist x z ≤ 3
      · have hp := path_prefix_two hp5 (t := Set.Icc a (a + 12))
          (fun w hw => by simp only [Set.mem_Icc] at hw ⊢; omega) hx
          (by simp only [Set.mem_Icc] at hz' ⊢; omega)
          (hxmin z (by simp only [Set.mem_Icc] at hz' ⊢; omega)) hzmin'
        apply hp.mono (d := 7 / 3)
        have hedge : (1 / 3 : ℚ) ≤ 1 / (Nat.dist x z : ℚ) := by
          apply one_div_nat_mono
          · simp only [Set.mem_Icc] at hz'
            simp [Nat.dist]
            omega
          · exact hxz3
        norm_num at hedge ⊢
        linarith
      · have hpA := path_prefix_two hp5 (t := Set.Icc (x - 8) (x - 1))
          (fun w hw => by simp only [Set.mem_Icc] at hw ⊢; omega) hy'
          (by simp only [Set.mem_Icc] at hz' ⊢; omega)
          (hymin' z (by simp only [Set.mem_Icc] at hz' ⊢; omega)) hzmin'
        have hpB := path_prefix_one hpA (t := Set.Icc a (a + 12))
          (fun w hw => by simp only [Set.mem_Icc] at hw ⊢; omega) hx
          (fun w hw => hxmin w (by simp only [Set.mem_Icc] at hw ⊢; omega))
          (fun w hw => by
            simp only [Set.mem_Icc] at hw
            apply one_div_nat_mono
            · simp [Nat.dist]
              omega
            · simp [Nat.dist]
              omega) (d := 1 / 8)
        apply hpB.mono (d := 7 / 3)
        have hyz4 : Nat.dist y z ≤ 4 := by
          simp only [Set.mem_Icc] at hy' hz'
          simp [Nat.dist] at hxy8 hxz3 ⊢
          omega
        have hedge : (1 / 4 : ℚ) ≤ 1 / (Nat.dist y z : ℚ) := by
          apply one_div_nat_mono
          · simp only [Set.mem_Icc] at hy' hz'
            simp [Nat.dist] at hxy8 ⊢
            omega
          · exact hyz4
        norm_num at hedge ⊢
        linarith

theorem thirteen_path (f : ℕ → ℝ) (a : ℕ) :
    HasMonoPath f (Set.Icc a (a + 12)) (7 / 3) := by
  obtain ⟨x, hxF, hxminF⟩ :=
    (Finset.Icc a (a + 12)).exists_min_image f (by simp)
  obtain ⟨X, hXF, hXmaxF⟩ :=
    (Finset.Icc a (a + 12)).exists_max_image f (by simp)
  have hx : x ∈ Set.Icc a (a + 12) := by simpa using hxF
  have hX : X ∈ Set.Icc a (a + 12) := by simpa using hXF
  have hxmin : ∀ z ∈ Set.Icc a (a + 12), f x ≤ f z := by
    intro z hz
    exact hxminF z (by simpa using hz)
  have hXmax : ∀ z ∈ Set.Icc a (a + 12), f z ≤ f X := by
    intro z hz
    exact hXmaxF z (by simpa using hz)
  by_cases hxside : x ≤ a + 4 ∨ a + 8 ≤ x
  · exact (thirteen_path_from_end_min f a x hx hxmin hxside).toMono
  · have hxmid : a + 5 ≤ x ∧ x ≤ a + 7 := by omega
    by_cases hXside : X ≤ a + 4 ∨ a + 8 ≤ X
    · have hp : HasUpPath (fun i => -f i) (Set.Icc a (a + 12)) (7 / 3) :=
        thirteen_path_from_end_min (fun i => -f i) a X hX
          (fun z hz => neg_le_neg (hXmax z hz)) hXside
      exact negUpPath_toMono hp
    · have hXmid : a + 5 ≤ X ∧ X ≤ a + 7 := by omega
      by_cases hxX : x = X
      · subst X
        refine ⟨[a, a+1, a+2, a+3], by simp, by simp [Set.mem_Icc], Or.inl ?_, ?_⟩
        · have h01 : f a ≤ f (a + 1) :=
            (hXmax a (by simp [Set.mem_Icc])).trans
              (hxmin (a + 1) (by simp [Set.mem_Icc]))
          have h12 : f (a + 1) ≤ f (a + 2) :=
            (hXmax (a + 1) (by simp [Set.mem_Icc])).trans
              (hxmin (a + 2) (by simp [Set.mem_Icc]))
          have h23 : f (a + 2) ≤ f (a + 3) :=
            (hXmax (a + 2) (by simp [Set.mem_Icc])).trans
              (hxmin (a + 3) (by simp [Set.mem_Icc]))
          simpa [List.isChain_cons] using ⟨h01, h12, h23⟩
        · norm_num [jumpWeight, Nat.dist_add_add_left, Nat.dist]
      · obtain ⟨z, hzF, hzminF⟩ :=
          (Finset.Icc a (a + 4)).exists_min_image f (by simp)
        obtain ⟨Z, hZF, hZmaxF⟩ :=
          (Finset.Icc a (a + 4)).exists_max_image f (by simp)
        have hz : z ∈ Set.Icc a (a + 4) := by simpa using hzF
        have hZ : Z ∈ Set.Icc a (a + 4) := by simpa using hZF
        have hzmin : ∀ w ∈ Set.Icc a (a + 4), f z ≤ f w := by
          intro w hw
          exact hzminF w (by simpa using hw)
        have hZmax : ∀ w ∈ Set.Icc a (a + 4), f w ≤ f Z := by
          intro w hw
          exact hZmaxF w (by simpa using hw)
        have build (z Z : ℕ) (hz : z ∈ Set.Icc a (a + 4))
            (hZ : Z ∈ Set.Icc a (a + 4)) (hzZ : z ≠ Z)
            (hzmin : ∀ w ∈ Set.Icc a (a + 4), f z ≤ f w)
            (hZmax : ∀ w ∈ Set.Icc a (a + 4), f w ≤ f Z) :
            HasMonoPath f (Set.Icc a (a + 12)) (7 / 3) := by
          have hp5 := five_path f a
          have hpA := path_prefix_two hp5
            (t := Set.insert x (Set.Icc a (a + 4)))
            (fun w hw => Set.mem_insert_of_mem x hw) (Set.mem_insert x _)
            (Set.mem_insert_of_mem x hz)
            (hxmin z (by simp only [Set.mem_Icc] at hz ⊢; omega)) hzmin
          have hpB := path_suffix_two hpA (t := Set.Icc a (a + 12))
            (fun w hw => by
              rcases hw with rfl | hw
              · exact hx
              · simp only [Set.mem_Icc] at hw ⊢
                omega)
            (by simp only [Set.mem_Icc] at hZ ⊢; omega) hX
            (fun w hw => by
              rcases hw with rfl | hw
              · exact (hxmin Z (by simp only [Set.mem_Icc] at hZ ⊢; omega))
              · exact hZmax w hw)
            (hXmax Z (by simp only [Set.mem_Icc] at hZ ⊢; omega))
          apply HasUpPath.toMono
          apply hpB.mono (d := 7 / 3)
          have hedge := middle_low_reciprocal_add a x X z Z
            hxmid.1 hxmid.2 hXmid.1 hXmid.2 hz.1 hz.2 hZ.1 hZ.2 hxX hzZ
          norm_num at hedge ⊢
          linarith
        by_cases hzZ : z = Z
        · have hmin3 : ∀ w ∈ Set.Icc a (a + 4), f (a + 3) ≤ f w := by
            intro w hw
            exact (hZmax (a + 3) (by simp [Set.mem_Icc])).trans
              (by simpa [hzZ] using hzmin w hw)
          have hmax4 : ∀ w ∈ Set.Icc a (a + 4), f w ≤ f (a + 4) := by
            intro w hw
            exact (by simpa [hzZ] using hZmax w hw : f w ≤ f z).trans
              (hzmin (a + 4) (by simp [Set.mem_Icc]))
          exact build (a + 3) (a + 4) (by simp [Set.mem_Icc])
            (by simp [Set.mem_Icc]) (by omega) hmin3 hmax4
        · exact build z Z hz hZ hzZ hzmin hZmax

def pathVariation (f : ℕ → ℝ) : List ℕ → ℝ
  | a :: b :: l => |f b - f a| + pathVariation f (b :: l)
  | _ => 0

lemma pathVariation_nonneg (f : ℕ → ℝ) (l : List ℕ) :
    0 ≤ pathVariation f l := by
  induction l with
  | nil => simp [pathVariation]
  | cons a l ih =>
      cases l <;> simp [pathVariation]
      positivity

lemma pathVariation_le_one_of_up {f : ℕ → ℝ} {l : List ℕ}
    (hl : l ≠ []) (hmem : ∀ i ∈ l, f i ∈ Set.Icc 0 1)
    (hchain : l.IsChain (fun a b => f a ≤ f b)) :
    pathVariation f l ≤ 1 := by
  have aux : ∀ (a : ℕ) (t : List ℕ),
      (a :: t).IsChain (fun i j => f i ≤ f j) →
      (∀ i ∈ a :: t, f i ∈ Set.Icc 0 1) →
      f a + pathVariation f (a :: t) ≤ 1 := by
    intro a t
    induction t generalizing a with
    | nil => simp [pathVariation]
    | cons b t ih =>
        intro hab hmem'
        have hab' : f a ≤ f b := hab.rel
        have htail := ih b hab.tail (fun i hi => hmem' i (by simp [hi]))
        simp only [pathVariation]
        rw [abs_of_nonneg (sub_nonneg.mpr hab')]
        linarith
  cases l with
  | nil => simp at hl
  | cons a t =>
      have h := aux a t hchain hmem
      have ha0 := (hmem a (by simp)).1
      linarith

lemma pathVariation_le_one_of_down {f : ℕ → ℝ} {l : List ℕ}
    (hl : l ≠ []) (hmem : ∀ i ∈ l, f i ∈ Set.Icc 0 1)
    (hchain : l.IsChain (fun a b => f b ≤ f a)) :
    pathVariation f l ≤ 1 := by
  have aux : ∀ (a : ℕ) (t : List ℕ),
      (a :: t).IsChain (fun i j => f j ≤ f i) →
      (∀ i ∈ a :: t, f i ∈ Set.Icc 0 1) →
      pathVariation f (a :: t) ≤ f a := by
    intro a t
    induction t generalizing a with
    | nil =>
        intro _ hmem'
        simpa [pathVariation] using (hmem' a (by simp)).1
    | cons b t ih =>
        intro hab hmem'
        have hab' : f b ≤ f a := hab.rel
        have htail := ih b hab.tail (fun i hi => hmem' i (by simp [hi]))
        simp only [pathVariation]
        rw [abs_of_nonpos (sub_nonpos.mpr hab')]
        linarith
  cases l with
  | nil => simp at hl
  | cons a t =>
      exact (aux a t hchain hmem).trans (hmem a (by simp)).2

lemma reciprocal_edge_lt (c t : ℝ) (a b : ℕ) (hab : a ≠ b)
    (h : c < (Nat.dist a b : ℝ) * t) :
    c * (((1 / (Nat.dist a b : ℚ) : ℚ) : ℝ)) < t := by
  rw [Rat.cast_div]
  norm_num
  have hd : (0 : ℝ) < Nat.dist a b := by
    exact_mod_cast (Nat.dist_pos_of_ne hab)
  rw [← div_eq_mul_inv]
  apply (div_lt_iff₀ hd).2
  nlinarith

lemma weighted_jump_le_variation {f : ℕ → ℝ} {s : Set ℕ} (l : List ℕ)
    (hmem : ∀ i ∈ l, i ∈ s)
    (hbad : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      (3 / 7 : ℝ) < (Nat.dist a b : ℝ) * |f b - f a|) :
    (3 / 7 : ℝ) * ((jumpWeight l : ℚ) : ℝ) ≤ pathVariation f l := by
  induction l with
  | nil => norm_num [jumpWeight, pathVariation]
  | cons a l ih =>
      cases l with
      | nil => norm_num [jumpWeight, pathVariation]
      | cons b t =>
          have htailmem : ∀ i ∈ b :: t, i ∈ s := by
            intro i hi
            exact hmem i (by simp [hi])
          have htail := ih htailmem
          by_cases hab : a = b
          · subst b
            simpa [jumpWeight, pathVariation] using htail
          · have hedge := reciprocal_edge_lt (3 / 7 : ℝ) |f b - f a| a b hab
              (hbad a (hmem a (by simp)) b (hmem b (by simp)) hab)
            simp only [jumpWeight, pathVariation, Rat.cast_add]
            calc
              3 / 7 *
                  (((1 / (Nat.dist a b : ℚ) : ℚ) : ℝ) +
                    ((jumpWeight (b :: t) : ℚ) : ℝ)) =
                  3 / 7 * (((1 / (Nat.dist a b : ℚ) : ℚ) : ℝ)) +
                    3 / 7 * ((jumpWeight (b :: t) : ℚ) : ℝ) := by ring
              _ ≤ |f b - f a| + pathVariation f (b :: t) :=
                add_le_add hedge.le htail

lemma weighted_jump_lt_variation {f : ℕ → ℝ} {s : Set ℕ} (l : List ℕ)
    (hmem : ∀ i ∈ l, i ∈ s)
    (hbad : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      (3 / 7 : ℝ) < (Nat.dist a b : ℝ) * |f b - f a|)
    (hpos : 0 < jumpWeight l) :
    (3 / 7 : ℝ) * ((jumpWeight l : ℚ) : ℝ) < pathVariation f l := by
  induction l with
  | nil => simp [jumpWeight] at hpos
  | cons a l ih =>
      cases l with
      | nil => simp [jumpWeight] at hpos
      | cons b t =>
          have htailmem : ∀ i ∈ b :: t, i ∈ s := by
            intro i hi
            exact hmem i (by simp [hi])
          have htaille := weighted_jump_le_variation (f := f) (b :: t) htailmem hbad
          by_cases hab : a = b
          · subst b
            have htailpos : 0 < jumpWeight (a :: t) := by
              simpa [jumpWeight] using hpos
            have htail := ih htailmem htailpos
            simpa [jumpWeight, pathVariation] using htail
          · have hedge := reciprocal_edge_lt (3 / 7 : ℝ) |f b - f a| a b hab
              (hbad a (hmem a (by simp)) b (hmem b (by simp)) hab)
            simp only [jumpWeight, pathVariation, Rat.cast_add]
            calc
              3 / 7 *
                  (((1 / (Nat.dist a b : ℚ) : ℚ) : ℝ) +
                    ((jumpWeight (b :: t) : ℚ) : ℝ)) =
                  3 / 7 * (((1 / (Nat.dist a b : ℚ) : ℚ) : ℝ)) +
                    3 / 7 * ((jumpWeight (b :: t) : ℚ) : ℝ) := by ring
              _ < |f b - f a| + pathVariation f (b :: t) :=
                add_lt_add_of_lt_of_le hedge htaille

theorem close_pair_thirteen (f : ℕ → ℝ) (hf : ∀ i, f i ∈ Set.Icc 0 1) :
    ∃ i j : ℕ, i < j ∧ j ≤ 12 ∧
      ((j - i : ℕ) : ℝ) * |f j - f i| ≤ 3 / 7 := by
  obtain ⟨l, hlne, hlmem, hlmono, hlweight⟩ := thirteen_path f 0
  by_contra hnone
  have hbad : ∀ a ∈ Set.Icc 0 12, ∀ b ∈ Set.Icc 0 12, a ≠ b →
      (3 / 7 : ℝ) < (Nat.dist a b : ℝ) * |f b - f a| := by
    intro a ha b hb hab
    rcases lt_or_gt_of_ne hab with hablt | hbalt
    · have hnot : ¬(((b - a : ℕ) : ℝ) * |f b - f a| ≤ 3 / 7) := by
        intro hle
        apply hnone
        exact ⟨a, b, hablt, hb.2, hle⟩
      have hgt := lt_of_not_ge hnot
      simpa [Nat.dist_eq_sub_of_le hablt.le] using hgt
    · have hnot : ¬(((a - b : ℕ) : ℝ) * |f a - f b| ≤ 3 / 7) := by
        intro hle
        apply hnone
        exact ⟨b, a, hbalt, ha.2, hle⟩
      have hgt := lt_of_not_ge hnot
      simpa [Nat.dist_eq_sub_of_le_right hbalt.le, abs_sub_comm] using hgt
  have hvar : pathVariation f l ≤ 1 := by
    rcases hlmono with hup | hdown
    · exact pathVariation_le_one_of_up hlne (fun i hi => hf i) hup
    · exact pathVariation_le_one_of_down hlne (fun i hi => hf i) hdown
  have hwpos : 0 < jumpWeight l := lt_of_lt_of_le (by norm_num) hlweight
  have hstrict := weighted_jump_lt_variation (f := f) l hlmem hbad hwpos
  have hlweightR : (7 / 3 : ℝ) ≤ ((jumpWeight l : ℚ) : ℝ) := by
    have h' : (((7 / 3 : ℚ) : ℚ) : ℝ) ≤ ((jumpWeight l : ℚ) : ℝ) :=
      Rat.cast_le.mpr hlweight
    rw [Rat.cast_div] at h'
    norm_num at h' ⊢
    exact h'
  norm_num at hstrict hlweightR
  nlinarith

theorem frequent_good_gap (x : ℕ → ℝ) (hx : ∀ m, x m ∈ Set.Icc 0 1) :
    ∃ n ∈ (Finset.Icc 1 12 : Finset ℕ),
      ∃ᶠ m in Filter.atTop,
        (n : ℝ) * |x (m + n) - x m| ≤ 3 / 7 := by
  have hall : ∃ᶠ m in Filter.atTop,
      ∃ n ∈ (Finset.Icc 1 12 : Finset ℕ),
        (n : ℝ) * |x (m + n) - x m| ≤ 3 / 7 := by
    rw [Filter.frequently_atTop]
    intro M
    obtain ⟨i, j, hij, hj, hclose⟩ :=
      close_pair_thirteen (fun r => x (M + r)) (fun r => hx (M + r))
    let m := M + i
    let n := j - i
    have hnpos : 1 ≤ n := by omega
    have hnle : n ≤ 12 := by omega
    have hindex : m + n = M + j := by
      dsimp [m, n]
      omega
    refine ⟨m, by simp [m], n, Finset.mem_Icc.mpr ⟨hnpos, hnle⟩, ?_⟩
    rw [hindex]
    simpa [m, n] using hclose
  exact (Finset.frequently_exists (Finset.Icc 1 12)).mp hall

syntax (name := answerSyntax480) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

open Filter

theorem erdos_480 : answer(True) ↔ ∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    ⨅ (n : ℕ+), atTop.liminf (fun m => (n : ℕ) * |x (m + (n : ℕ)) - x m|) ≤
      1 / √5 := by
  constructor
  · intro _ x hx
    obtain ⟨n, hn, hfreq⟩ := frequent_good_gap x hx
    let p : ℕ+ := ⟨n, lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1⟩
    let u : ℕ → ℝ := fun m => (p : ℕ) * |x (m + (p : ℕ)) - x m|
    have hfreq' : ∃ᶠ m in atTop, u m ≤ 3 / 7 := by
      simpa [u, p] using hfreq
    have hu_nonneg : ∀ m, 0 ≤ u m := by
      intro m
      exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
    have hlim : atTop.liminf u ≤ 3 / 7 :=
      Filter.liminf_le_of_frequently_le hfreq'
        (Filter.isBoundedUnder_of_eventually_ge
          (Filter.Eventually.of_forall hu_nonneg))
    have hlim_nonneg : ∀ q : ℕ+,
        0 ≤ atTop.liminf (fun m => (q : ℕ) * |x (m + (q : ℕ)) - x m|) := by
      intro q
      let v : ℕ → ℝ := fun m => (q : ℕ) * |x (m + (q : ℕ)) - x m|
      have hv_nonneg : ∀ m, 0 ≤ v m := by
        intro m
        exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
      have hv_upper : ∀ m, v m ≤ (q : ℕ) := by
        intro m
        have h₁ := hx (m + (q : ℕ))
        have h₂ := hx m
        rcases h₁ with ⟨h₁0, h₁1⟩
        rcases h₂ with ⟨h₂0, h₂1⟩
        have habs : |x (m + (q : ℕ)) - x m| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        dsimp [v]
        calc
          (q : ℕ) * |x (m + (q : ℕ)) - x m| ≤ (q : ℕ) * 1 := by
            gcongr
          _ = (q : ℕ) := by ring
      exact Filter.le_liminf_of_le
        (Filter.isCoboundedUnder_ge_of_eventually_le atTop
          (Filter.Eventually.of_forall hv_upper))
        (Filter.Eventually.of_forall hv_nonneg)
    have hbdd : BddBelow (Set.range fun q : ℕ+ =>
        atTop.liminf (fun m => (q : ℕ) * |x (m + (q : ℕ)) - x m|)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨q, rfl⟩
      exact hlim_nonneg q
    have hsqrt : (3 / 7 : ℝ) ≤ 1 / √5 := by
      have hs : 0 < √(5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
      have hs2 : √(5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      apply (le_div_iff₀ hs).2
      have hsle : √(5 : ℝ) ≤ 7 / 3 := by nlinarith
      nlinarith
    calc
      (⨅ (q : ℕ+), atTop.liminf
          (fun m => (q : ℕ) * |x (m + (q : ℕ)) - x m|)) ≤
          atTop.liminf u := by
            simpa [u, p] using ciInf_le hbdd p
      _ ≤ 3 / 7 := hlim
      _ ≤ 1 / √5 := hsqrt
  · intro _
    trivial

end Erdos480

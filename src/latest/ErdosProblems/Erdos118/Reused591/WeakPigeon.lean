import ErdosProblems.Erdos590

namespace Erdos118.Reused591

open Cardinal Ordinal

namespace WeakPigeon

open Erdos590.Larson (LL IncList)

/-! First prove the finite-level pigeonhole theorem, then lift it to the
shortlex order on all finite lists. -/

def RawLevel (n : ℕ) := {l : List ℕ // l.length = n}

def RawLevelLex {n : ℕ} (a b : RawLevel n) : Prop :=
  List.Lex (· < ·) a.1 b.1

theorem RawLevelLex.irrefl {n : ℕ} (a : RawLevel n) : ¬ RawLevelLex a a :=
  List.lex_irrefl (r := (· < ·)) (fun _ h => Nat.lt_irrefl _ h) a.1

theorem RawLevelLex.trans {n : ℕ} {a b c : RawLevel n}
    (hab : RawLevelLex a b) (hbc : RawLevelLex b c) : RawLevelLex a c :=
  List.lex_trans (fun h₁ h₂ => Nat.lt_trans h₁ h₂) hab hbc

theorem RawLevelLex.trichotomous {n : ℕ} (a b : RawLevel n) :
    RawLevelLex a b ∨ a = b ∨ RawLevelLex b a := by
  by_cases hab : RawLevelLex a b
  · exact Or.inl hab
  by_cases hba : RawLevelLex b a
  · exact Or.inr (Or.inr hba)
  · apply Or.inr; apply Or.inl
    apply Subtype.ext
    exact List.lex_trichotomous (r := (· < ·))
      (fun x y hxy hyx => Nat.le_antisymm (Nat.le_of_not_gt hyx)
        (Nat.le_of_not_gt hxy)) hba hab

instance rawLevelStrictTotal (n : ℕ) :
    IsStrictTotalOrder (RawLevel n) RawLevelLex where
  irrefl := RawLevelLex.irrefl
  trans _ _ _ := RawLevelLex.trans
  trichotomous a b hab hba := by
    rcases RawLevelLex.trichotomous a b with h | rfl | h
    · exact (hab h).elim
    · rfl
    · exact (hba h).elim

noncomputable instance rawLevelLinearOrder (n : ℕ) : LinearOrder (RawLevel n) := by
  letI : DecidableRel (@RawLevelLex n) := Classical.decRel _
  exact linearOrderOfSTO RawLevelLex

instance rawLevelLexWellFounded (n : ℕ) :
    IsWellFounded (RawLevel n) RawLevelLex :=
  ⟨(InvImage.wf Subtype.val (List.Shortlex.wf Nat.lt_wfRel.wf)).mono (by
    intro a b hab
    change List.Shortlex (· < ·) a.1 b.1
    rw [List.shortlex_def]
    exact Or.inr ⟨a.2.trans b.2.symm, hab⟩)⟩

instance rawLevelWellFoundedLT (n : ℕ) : WellFoundedLT (RawLevel n) := by
  constructor
  change WellFounded (@RawLevelLex n)
  exact (rawLevelLexWellFounded n).wf

instance rawLevelIsWellOrder (n : ℕ) : IsWellOrder (RawLevel n) RawLevelLex where
  wf := IsWellFounded.wf
  trichotomous a b hab hba := by
    rcases RawLevelLex.trichotomous a b with h | h | h
    · exact (hab h).elim
    · exact h
    · exact (hba h).elim

def rawLevelSuccEquiv (n : ℕ) : RawLevel (n + 1) ≃ ℕ × RawLevel n where
  toFun x :=
    ⟨x.1.headD 0, ⟨x.1.tail, by
      have hx : x.1 ≠ [] := by
        intro h
        have : 0 = n + 1 := by simpa [h] using x.2
        omega
      rw [List.length_tail, x.2]
      omega⟩⟩
  invFun x := ⟨x.1 :: x.2.1, by simp [x.2.2]⟩
  left_inv x := by
    apply Subtype.ext
    cases h : x.1 with
    | nil =>
        have := x.2
        simp [h] at this
    | cons a as => simp [h]
  right_inv x := by
    rcases x with ⟨a, xs⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp

@[simp] theorem rawLevelSuccEquiv_fst (n x : ℕ) (xs : List ℕ)
    (h : (x :: xs).length = n + 1) :
    (rawLevelSuccEquiv n ⟨x :: xs, h⟩).1 = x := rfl

@[simp] theorem rawLevelSuccEquiv_snd_val (n x : ℕ) (xs : List ℕ)
    (h : (x :: xs).length = n + 1) :
    (rawLevelSuccEquiv n ⟨x :: xs, h⟩).2.1 = xs := rfl

def rawLevelSuccRelIso (n : ℕ) :
    @RawLevelLex (n + 1) ≃r
      Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex n) where
  toEquiv := rawLevelSuccEquiv n
  map_rel_iff' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    cases a with
    | nil => simp at ha
    | cons x xs =>
      cases b with
      | nil => simp at hb
      | cons y ys =>
        simp [RawLevelLex, Prod.lex_def, List.cons_lex_cons_iff]

theorem rawLevel_type (n : ℕ) :
    Ordinal.type (@RawLevelLex n) = ω ^ n := by
  induction n with
  | zero =>
      have huniq : Nonempty (Unique (RawLevel 0)) := by
        let d : RawLevel 0 := ⟨[], rfl⟩
        exact ⟨{
          default := d
          uniq := fun x => Subtype.ext (List.length_eq_zero_iff.mp x.2) }⟩
      exact (Ordinal.type_eq_one_iff_unique (r := @RawLevelLex 0)).2 huniq
  | succ n ih =>
      rw [(rawLevelSuccRelIso n).ordinalType_congr]
      rw [Ordinal.type_prod_lex, ih, Ordinal.type_nat_lt]
      rw [pow_succ]

theorem rawLevel_finite_partition (n k : ℕ)
    (c : RawLevel n → Fin (k + 1)) :
    ∃ i : Fin (k + 1), ∃ e : (@RawLevelLex n) ↪r (@RawLevelLex n),
      ∀ x, c (e x) = i := by
  classical
  induction n with
  | zero =>
      let x0 : RawLevel 0 := ⟨[], rfl⟩
      refine ⟨c x0, RelEmbedding.refl _, ?_⟩
      intro x
      congr 1
      apply Subtype.ext
      exact List.length_eq_zero_iff.mp x.2
  | succ n ih =>
      let iso := rawLevelSuccRelIso n
      let cp : ℕ → RawLevel n → Fin (k + 1) := fun a x => c (iso.symm (a, x))
      choose ci ei hei using fun a => ih (cp a)
      obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber ci
      let H : Set ℕ := ci ⁻¹' {i}
      let : Infinite H := by simpa [H] using hi
      let h : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet H
      let ep : Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex n) ↪r
          Prod.Lex ((· < ·) : ℕ → ℕ → Prop) (@RawLevelLex n) :=
        RelEmbedding.ofMonotone
          (fun p : ℕ × RawLevel n => (h p.1, ei (h p.1) p.2)) (by
            intro a b hab
            rcases a with ⟨a, x⟩
            rcases b with ⟨b, y⟩
            simp only [Prod.lex_def] at hab ⊢
            rcases hab with hab | ⟨rfl, hxy⟩
            · exact Or.inl (h.strictMono hab)
            · exact Or.inr ⟨rfl, (ei (h a)).map_rel_iff.mpr hxy⟩)
      let e := iso.toRelEmbedding.trans (ep.trans iso.symm.toRelEmbedding)
      refine ⟨i, e, ?_⟩
      intro x
      have hhH : h (iso x).1 ∈ H := by
        change Nat.orderEmbeddingOfSet H (iso x).1 ∈ H
        rw [Nat.orderEmbeddingOfSet_apply]
        exact (Nat.Subtype.ofNat H (iso x).1).property
      have hh : ci (h (iso x).1) = i := by simpa [H] using hhH
      change cp (h (iso x).1) (ei (h (iso x).1) (iso x).2) = i
      rw [hei]
      exact hh

noncomputable def rawLevelPadEmbedding {q t : ℕ} (hqt : q ≤ t) :
    (@RawLevelLex q) ↪r (@RawLevelLex t) :=
  RelEmbedding.ofMonotone
    (fun x : RawLevel q =>
      ⟨List.replicate (t - q) 0 ++ x.1, by
        simp only [List.length_append, List.length_replicate, x.2]
        exact Nat.sub_add_cancel hqt⟩)
    (by
      intro x y hxy
      exact List.Lex.append_left _ hxy (List.replicate (t - q) 0))

theorem shortlex_finite_partition (k : ℕ)
    (c : List ℕ → Fin (k + 1)) :
    ∃ i : Fin (k + 1),
      ∃ e : List.Shortlex ((· < ·) : ℕ → ℕ → Prop) ↪r
          List.Shortlex ((· < ·) : ℕ → ℕ → Prop),
        ∀ x, c (e x) = i := by
  classical
  let levelColor : (q : ℕ) → RawLevel q → Fin (k + 1) :=
    fun _ x => c x.1
  choose ci ei hei using fun q => rawLevel_finite_partition q k (levelColor q)
  obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber ci
  let H : Set ℕ := ci ⁻¹' {i}
  let : Infinite H := by simpa [H] using hi
  let h : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet H
  have hh_mem (q : ℕ) : h q ∈ H := by
    change Nat.orderEmbeddingOfSet H q ∈ H
    rw [Nat.orderEmbeddingOfSet_apply]
    exact (Nat.Subtype.ofNat H q).property
  have hh_color (q : ℕ) : ci (h q) = i := by
    simpa [H] using hh_mem q
  have hq_le (q : ℕ) : q ≤ h q := h.strictMono.le_apply
  let mapFun : List ℕ → List ℕ := fun x =>
    (ei (h x.length)
      (rawLevelPadEmbedding (hq_le x.length) ⟨x, rfl⟩)).1
  have mapFun_of_level (q : ℕ) (x : RawLevel q) :
      mapFun x.1 =
        (ei (h q) (rawLevelPadEmbedding (hq_le q) x)).1 := by
    rcases x with ⟨x, hx⟩
    change (ei (h x.length)
      (rawLevelPadEmbedding (hq_le x.length) ⟨x, rfl⟩)).1 = _
    cases hx
    rfl
  have mapFun_length (x : List ℕ) : (mapFun x).length = h x.length := by
    exact (ei (h x.length)
      (rawLevelPadEmbedding (hq_le x.length) ⟨x, rfl⟩)).2
  have hmono : ∀ ⦃x y : List ℕ⦄,
      List.Shortlex (· < ·) x y →
        List.Shortlex (· < ·) (mapFun x) (mapFun y) := by
    intro x y hxy
    rw [List.shortlex_def] at hxy ⊢
    rcases hxy with hlen | ⟨hlen, hlex⟩
    · exact Or.inl <| by
        rw [mapFun_length, mapFun_length]
        exact h.strictMono hlen
    · apply Or.inr
      refine ⟨?_, ?_⟩
      · rw [mapFun_length, mapFun_length, hlen]
      · have hlex' : RawLevelLex (⟨x, rfl⟩ : RawLevel x.length)
            (⟨y, hlen.symm⟩ : RawLevel x.length) := hlex
        have hpad := (rawLevelPadEmbedding (hq_le x.length)).map_rel_iff.mpr hlex'
        have hemb := (ei (h x.length)).map_rel_iff.mpr hpad
        change List.Lex (· < ·) (mapFun x) (mapFun y)
        rw [mapFun_of_level x.length ⟨x, rfl⟩,
          mapFun_of_level x.length ⟨y, hlen.symm⟩]
        exact hemb
  let e : List.Shortlex ((· < ·) : ℕ → ℕ → Prop) ↪r
      List.Shortlex ((· < ·) : ℕ → ℕ → Prop) :=
    RelEmbedding.ofMonotone mapFun hmono
  refine ⟨i, e, ?_⟩
  intro x
  change c (mapFun x) = i
  have he := hei (h x.length)
    (rawLevelPadEmbedding (hq_le x.length) ⟨x, rfl⟩)
  change levelColor (h x.length)
      (ei (h x.length)
        (rawLevelPadEmbedding (hq_le x.length) ⟨x, rfl⟩)) = i
  rw [he]
  exact hh_color x.length

abbrev SL : List ℕ → List ℕ → Prop := List.Shortlex (· < ·)

theorem SL_irrefl (a : List ℕ) : ¬ SL a a := by
  change ¬ List.Shortlex (· < ·) a a
  rw [List.shortlex_def]
  rintro (h | ⟨-, h⟩)
  · exact Nat.lt_irrefl _ h
  · exact List.lex_irrefl Nat.lt_irrefl _ h

theorem SL_trans {a b c : List ℕ} (hab : SL a b) (hbc : SL b c) : SL a c := by
  change List.Shortlex (· < ·) a b at hab
  change List.Shortlex (· < ·) b c at hbc
  change List.Shortlex (· < ·) a c
  rw [List.shortlex_def] at hab hbc ⊢
  rcases hab with hab | ⟨hablen, hab⟩
  · rcases hbc with hbc | ⟨hbclen, -⟩
    · exact Or.inl (hab.trans hbc)
    · exact Or.inl (hbclen ▸ hab)
  · rcases hbc with hbc | ⟨hbclen, hbc⟩
    · exact Or.inl (hablen ▸ hbc)
    · exact Or.inr ⟨hablen.trans hbclen, List.lex_trans Nat.lt_trans hab hbc⟩

instance rawShortlexIsWellOrder : IsWellOrder (List ℕ) SL where
  wf := List.Shortlex.wf Nat.lt_wfRel.wf

noncomputable def rawListCode (s : List ℕ) : Ordinal :=
  ω ^ (s.length : Ordinal) +
    Ordinal.typein (@RawLevelLex s.length) ⟨s, rfl⟩

theorem rawListRank_lt (s : List ℕ) :
    Ordinal.typein (@RawLevelLex s.length) ⟨s, rfl⟩ <
      ω ^ (s.length : Ordinal) := by
  have h := Ordinal.typein_lt_type (@RawLevelLex s.length) ⟨s, rfl⟩
  rw [rawLevel_type, ← Ordinal.opow_natCast] at h
  exact h

theorem rawLevelRank_transport {n m : ℕ} (h : n = m) (t : List ℕ)
    (ht : t.length = m) :
    Ordinal.typein (@RawLevelLex m) (⟨t, ht⟩ : RawLevel m) =
      Ordinal.typein (@RawLevelLex n) (⟨t, ht.trans h.symm⟩ : RawLevel n) := by
  subst m
  rfl

theorem rawListCode_lt_omegaOmega (s : List ℕ) : rawListCode s < ω ^ ω := by
  have h := Ordinal.opow_mul_add_lt_opow
    (b := ω) (u := (s.length : Ordinal)) (v := 1)
    (w := Ordinal.typein (@RawLevelLex s.length) ⟨s, rfl⟩) (x := ω)
    Ordinal.one_lt_omega0 (rawListRank_lt s)
    (Ordinal.natCast_lt_omega0 s.length)
  simpa [rawListCode] using h

theorem rawListCode_strictMono {s t : List ℕ} (hst : SL s t) :
    rawListCode s < rawListCode t := by
  rcases List.shortlex_def.mp hst with hlen | ⟨hlen, hlex⟩
  · have hbelow : rawListCode s < ω ^ (t.length : Ordinal) := by
      have h := Ordinal.opow_mul_add_lt_opow
        (b := ω) (u := (s.length : Ordinal)) (v := 1)
        (w := Ordinal.typein (@RawLevelLex s.length) ⟨s, rfl⟩)
        (x := (t.length : Ordinal)) Ordinal.one_lt_omega0
        (rawListRank_lt s) (by exact_mod_cast hlen)
      simpa [rawListCode] using h
    exact hbelow.trans_le (by simp [rawListCode])
  · unfold rawListCode
    have hrank := rawLevelRank_transport hlen t rfl
    rw [hrank]
    have hexp : ω ^ (t.length : Ordinal) = ω ^ (s.length : Ordinal) := by rw [hlen]
    rw [hexp, add_lt_add_iff_left]
    exact (Ordinal.typein_lt_typein (@RawLevelLex s.length)).2 hlex

noncomputable def rawListCodeEmbedding :
    SL ↪r ((· < ·) : (ω ^ ω).ToType → (ω ^ ω).ToType → Prop) :=
  RelEmbedding.ofMonotone
    (fun s => Ordinal.ToType.mk ⟨rawListCode s, rawListCode_lt_omegaOmega s⟩)
    (fun _ _ h => Ordinal.ToType.mk.strictMono (rawListCode_strictMono h))

theorem rawShortlex_type : Ordinal.type SL = ω ^ ω := by
  apply le_antisymm
  · have h := rawListCodeEmbedding.ordinal_type_le
    simpa [Ordinal.type_toType] using h
  · rw [← Ordinal.iSup_pow_natCast Ordinal.omega0_pos]
    apply Ordinal.iSup_le
    intro n
    rw [← rawLevel_type n]
    exact (RelEmbedding.ofMonotone
      (r := @RawLevelLex n) (s := SL)
      (fun x : RawLevel n => x.1)
      (fun a b hab => List.shortlex_def.2
        (Or.inr ⟨a.2.trans b.2.symm, hab⟩))).ordinal_type_le

/-! Fixed-length lists of raw shortlex lists, ordered lexicographically. -/

def OmegaLevel (r : ℕ) := {l : List (List ℕ) // l.length = r}

def OmegaLevelLex {r : ℕ} (a b : OmegaLevel r) : Prop :=
  List.Lex SL a.1 b.1

theorem OmegaLevelLex.irrefl {r : ℕ} (a : OmegaLevel r) :
    ¬ OmegaLevelLex a a :=
  List.lex_irrefl (r := SL) SL_irrefl a.1

theorem OmegaLevelLex.trans {r : ℕ} {a b c : OmegaLevel r}
    (hab : OmegaLevelLex a b) (hbc : OmegaLevelLex b c) : OmegaLevelLex a c :=
  List.lex_trans (fun h₁ h₂ => SL_trans h₁ h₂) hab hbc

theorem OmegaLevelLex.trichotomous {r : ℕ} (a b : OmegaLevel r) :
    OmegaLevelLex a b ∨ a = b ∨ OmegaLevelLex b a := by
  classical
  let : DecidableRel SL := Classical.decRel _
  by_cases hab : OmegaLevelLex a b
  · exact Or.inl hab
  by_cases hba : OmegaLevelLex b a
  · exact Or.inr (Or.inr hba)
  · apply Or.inr; apply Or.inl
    apply Subtype.ext
    exact List.lex_trichotomous (r := SL)
      (fun x y hxy hyx => by
        rcases trichotomous_of SL x y with h | h | h
        · exact (hxy h).elim
        · exact h
        · exact (hyx h).elim) hba hab

instance omegaLevelStrictTotal (r : ℕ) :
    IsStrictTotalOrder (OmegaLevel r) OmegaLevelLex where
  irrefl := OmegaLevelLex.irrefl
  trans _ _ _ := OmegaLevelLex.trans
  trichotomous a b hab hba := by
    rcases OmegaLevelLex.trichotomous a b with h | rfl | h
    · exact (hab h).elim
    · rfl
    · exact (hba h).elim

noncomputable instance omegaLevelLinearOrder (r : ℕ) : LinearOrder (OmegaLevel r) := by
  letI : DecidableRel (@OmegaLevelLex r) := Classical.decRel _
  exact linearOrderOfSTO OmegaLevelLex

instance omegaLevelLexWellFounded (r : ℕ) :
    IsWellFounded (OmegaLevel r) OmegaLevelLex :=
  ⟨(InvImage.wf Subtype.val (List.Shortlex.wf (List.Shortlex.wf Nat.lt_wfRel.wf))).mono (by
    intro a b hab
    change List.Shortlex SL a.1 b.1
    rw [List.shortlex_def]
    exact Or.inr ⟨a.2.trans b.2.symm, hab⟩)⟩

instance omegaLevelWellFoundedLT (r : ℕ) : WellFoundedLT (OmegaLevel r) := by
  constructor
  change WellFounded (@OmegaLevelLex r)
  exact (omegaLevelLexWellFounded r).wf

instance omegaLevelIsWellOrder (r : ℕ) :
    IsWellOrder (OmegaLevel r) OmegaLevelLex where
  wf := IsWellFounded.wf
  trichotomous a b hab hba := by
    rcases OmegaLevelLex.trichotomous a b with h | h | h
    · exact (hab h).elim
    · exact h
    · exact (hba h).elim

def omegaLevelSuccEquiv (r : ℕ) : OmegaLevel (r + 1) ≃ List ℕ × OmegaLevel r where
  toFun x :=
    ⟨x.1.headD default, ⟨x.1.tail, by
      have hx : x.1 ≠ [] := by
        intro h
        have : 0 = r + 1 := by simpa [h] using x.2
        omega
      rw [List.length_tail, x.2]
      omega⟩⟩
  invFun x := ⟨x.1 :: x.2.1, by simp [x.2.2]⟩
  left_inv x := by
    apply Subtype.ext
    cases h : x.1 with
    | nil =>
        have := x.2
        simp [h] at this
    | cons a as => simp [h]
  right_inv x := by
    rcases x with ⟨a, xs⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp

@[simp] theorem omegaLevelSuccEquiv_fst (r : ℕ) (x : List ℕ)
    (xs : List (List ℕ)) (h : (x :: xs).length = r + 1) :
    (omegaLevelSuccEquiv r ⟨x :: xs, h⟩).1 = x := rfl

@[simp] theorem omegaLevelSuccEquiv_snd_val (r : ℕ) (x : List ℕ)
    (xs : List (List ℕ)) (h : (x :: xs).length = r + 1) :
    (omegaLevelSuccEquiv r ⟨x :: xs, h⟩).2.1 = xs := rfl

def omegaLevelSuccRelIso (r : ℕ) :
    @OmegaLevelLex (r + 1) ≃r Prod.Lex SL (@OmegaLevelLex r) where
  toEquiv := omegaLevelSuccEquiv r
  map_rel_iff' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    cases a with
    | nil => simp at ha
    | cons x xs =>
      cases b with
      | nil => simp at hb
      | cons y ys =>
        simp [OmegaLevelLex, Prod.lex_def, List.cons_lex_cons_iff]

theorem omegaLevel_type (r : ℕ) :
    Ordinal.type (@OmegaLevelLex r) = (ω ^ ω) ^ r := by
  induction r with
  | zero =>
      have huniq : Nonempty (Unique (OmegaLevel 0)) := by
        let d : OmegaLevel 0 := ⟨[], rfl⟩
        exact ⟨{
          default := d
          uniq := fun x => Subtype.ext (List.length_eq_zero_iff.mp x.2) }⟩
      exact (Ordinal.type_eq_one_iff_unique (r := @OmegaLevelLex 0)).2 huniq
  | succ r ih =>
      rw [(omegaLevelSuccRelIso r).ordinalType_congr]
      rw [Ordinal.type_prod_lex, ih, rawShortlex_type]
      rw [pow_succ]

theorem omegaLevel_finite_partition (r k : ℕ)
    (c : OmegaLevel r → Fin (k + 1)) :
    ∃ i : Fin (k + 1),
      ∃ e : (@OmegaLevelLex r) ↪r (@OmegaLevelLex r),
        ∀ x, c (e x) = i := by
  classical
  induction r with
  | zero =>
      let x0 : OmegaLevel 0 := ⟨[], rfl⟩
      refine ⟨c x0, RelEmbedding.refl _, ?_⟩
      intro x
      congr 1
      apply Subtype.ext
      exact List.length_eq_zero_iff.mp x.2
  | succ r ih =>
      let iso := omegaLevelSuccRelIso r
      let cp : List ℕ → OmegaLevel r → Fin (k + 1) := fun a x =>
        c (iso.symm (a, x))
      choose ci ei hei using fun a => ih (cp a)
      obtain ⟨i, h, hh⟩ := shortlex_finite_partition k ci
      let ep : Prod.Lex SL (@OmegaLevelLex r) ↪r
          Prod.Lex SL (@OmegaLevelLex r) :=
        RelEmbedding.ofMonotone
          (fun p : List ℕ × OmegaLevel r => (h p.1, ei (h p.1) p.2)) (by
            intro a b hab
            rcases a with ⟨a, x⟩
            rcases b with ⟨b, y⟩
            simp only [Prod.lex_def] at hab ⊢
            rcases hab with hab | ⟨rfl, hxy⟩
            · exact Or.inl (h.map_rel_iff.mpr hab)
            · exact Or.inr ⟨rfl, (ei (h a)).map_rel_iff.mpr hxy⟩)
      let e := iso.toRelEmbedding.trans (ep.trans iso.symm.toRelEmbedding)
      refine ⟨i, e, ?_⟩
      intro x
      change cp (h (iso x).1) (ei (h (iso x).1) (iso x).2) = i
      rw [hei]
      exact hh (iso x).1

theorem omega_power_finite_pigeonhole (n m : ℕ)
    (f : (ω ^ (ω * (n + 1 : ℕ)) : Ordinal.{0}).ToType → Fin m) :
    ∃ i : Fin m,
      typeLT {x : (ω ^ (ω * (n + 1 : ℕ)) : Ordinal.{0}).ToType // f x = i} =
        (ω ^ (ω * (n + 1 : ℕ)) : Ordinal.{0}) := by
  classical
  cases m with
  | zero =>
      let x0 : (ω ^ (ω * (n + 1 : ℕ)) : Ordinal.{0}).ToType :=
        Ordinal.ToType.mk ⟨0, Ordinal.opow_pos _ Ordinal.omega0_pos⟩
      exact Fin.elim0 (f x0)
  | succ k =>
      let beta : Ordinal := ω ^ (ω * (n + 1 : ℕ))
      have hmodel : Ordinal.type (@OmegaLevelLex (n + 1)) = beta := by
        rw [omegaLevel_type]
        rw [← Ordinal.opow_natCast]
        exact (Ordinal.opow_mul ω ω (n + 1)).symm
      let u : (@OmegaLevelLex (n + 1)) ≃r
          ((· < ·) : beta.ToType → beta.ToType → Prop) :=
        Classical.choice (Ordinal.type_eq.mp
          (hmodel.trans (Ordinal.type_toType beta).symm))
      let c : OmegaLevel (n + 1) → Fin (k + 1) := fun x => f (u x)
      obtain ⟨i, e, he⟩ := omegaLevel_finite_partition (n + 1) k c
      let g : ((· < ·) : beta.ToType → beta.ToType → Prop) ↪r
          ((· < ·) : {x : beta.ToType // f x = i} →
            {x : beta.ToType // f x = i} → Prop) :=
        RelEmbedding.ofMonotone
          (fun x => ⟨u (e (u.symm x)), by exact he (u.symm x)⟩)
          (by
            intro x y hxy
            exact u.map_rel_iff.mpr <| e.map_rel_iff.mpr <| u.symm.map_rel_iff.mpr hxy)
      have hupper : typeLT {x : beta.ToType // f x = i} ≤ beta := by
        exact (Ordinal.type_set_le {x : beta.ToType | f x = i}).trans_eq
          (Ordinal.type_toType beta)
      refine ⟨i, le_antisymm hupper ?_⟩
      have hg := g.ordinal_type_le
      simpa [beta, Ordinal.type_toType] using hg

end WeakPigeon



end Erdos118.Reused591

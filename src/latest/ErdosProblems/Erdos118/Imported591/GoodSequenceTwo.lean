import ErdosProblems.Erdos118.Imported591.WeakPigeon

open Ordinal

namespace Erdos118.Negative

open WeakPigeon

/-- The nested-list presentation of the height-two good sequences
`G_{omega^2}` from Hajnal--Larson. -/
abbrev G2 := List (List ℕ)

/-- Shortlex on the outer list, with raw shortlex on every inner list. -/
abbrev G2LT : G2 → G2 → Prop := List.Shortlex SL

theorem G2LT.irrefl (a : G2) : ¬ G2LT a a := by
  change ¬ List.Shortlex SL a a
  rw [List.shortlex_def]
  rintro (h | ⟨-, h⟩)
  · exact Nat.lt_irrefl _ h
  · exact List.lex_irrefl SL_irrefl _ h

theorem G2LT.trans {a b c : G2} (hab : G2LT a b) (hbc : G2LT b c) :
    G2LT a c := by
  change List.Shortlex SL a b at hab
  change List.Shortlex SL b c at hbc
  change List.Shortlex SL a c
  rw [List.shortlex_def] at hab hbc ⊢
  rcases hab with hab | ⟨hablen, hab⟩
  · rcases hbc with hbc | ⟨hbclen, -⟩
    · exact Or.inl (hab.trans hbc)
    · exact Or.inl (hbclen ▸ hab)
  · rcases hbc with hbc | ⟨hbclen, hbc⟩
    · exact Or.inl (hablen ▸ hbc)
    · exact Or.inr ⟨hablen.trans hbclen, List.lex_trans SL_trans hab hbc⟩

instance g2IsWellOrder : IsWellOrder G2 G2LT where
  wf := List.Shortlex.wf (List.Shortlex.wf Nat.lt_wfRel.wf)

/-- A type synonym carrying the intended nested shortlex order as its
ordinary Lean order.  This is convenient for prefix fibers and subsets,
where `typeLT` expects a `LinearOrder`. -/
def OrderedG2 := G2

instance orderedG2LT : LT OrderedG2 := ⟨G2LT⟩

instance orderedG2RelIsWellOrder :
    IsWellOrder OrderedG2 ((· < ·) : OrderedG2 → OrderedG2 → Prop) := by
  change IsWellOrder G2 G2LT
  exact g2IsWellOrder

noncomputable instance orderedG2LinearOrder : LinearOrder OrderedG2 := by
  letI : DecidableRel ((· < ·) : OrderedG2 → OrderedG2 → Prop) :=
    Classical.decRel _
  exact linearOrderOfSTO ((· < ·) : OrderedG2 → OrderedG2 → Prop)

instance orderedG2WellFoundedLT : WellFoundedLT OrderedG2 :=
  ⟨orderedG2RelIsWellOrder.wf⟩

/-- The ordinal code putting the fixed-length `m` fiber into the interval
`[(omega^omega)^m, (omega^omega)^(m+1))`. -/
noncomputable def g2Code (s : G2) : Ordinal :=
  (ω ^ ω) ^ (s.length : Ordinal) +
    Ordinal.typein (@OmegaLevelLex s.length) ⟨s, rfl⟩

theorem omegaLevelRank_lt (s : G2) :
    Ordinal.typein (@OmegaLevelLex s.length) ⟨s, rfl⟩ <
      (ω ^ ω) ^ (s.length : Ordinal) := by
  have h := Ordinal.typein_lt_type (@OmegaLevelLex s.length) ⟨s, rfl⟩
  rw [omegaLevel_type, ← Ordinal.opow_natCast] at h
  exact h

theorem omegaLevelRank_transport {n m : ℕ} (h : n = m) (t : G2)
    (ht : t.length = m) :
    Ordinal.typein (@OmegaLevelLex m) (⟨t, ht⟩ : OmegaLevel m) =
      Ordinal.typein (@OmegaLevelLex n)
        (⟨t, ht.trans h.symm⟩ : OmegaLevel n) := by
  subst m
  rfl

theorem g2Code_lt_thetaOmega (s : G2) : g2Code s < (ω ^ ω) ^ ω := by
  have h := Ordinal.opow_mul_add_lt_opow
    (b := ω ^ ω) (u := (s.length : Ordinal)) (v := 1)
    (w := Ordinal.typein (@OmegaLevelLex s.length) ⟨s, rfl⟩) (x := ω)
    ((Ordinal.one_lt_opow).2 ⟨Ordinal.one_lt_omega0, Ordinal.omega0_ne_zero⟩)
    (omegaLevelRank_lt s) (Ordinal.natCast_lt_omega0 s.length)
  simpa [g2Code] using h

theorem g2Code_strictMono {s t : G2} (hst : G2LT s t) :
    g2Code s < g2Code t := by
  rcases List.shortlex_def.mp hst with hlen | ⟨hlen, hlex⟩
  · have hbelow : g2Code s < (ω ^ ω) ^ (t.length : Ordinal) := by
      have h := Ordinal.opow_mul_add_lt_opow
        (b := ω ^ ω) (u := (s.length : Ordinal)) (v := 1)
        (w := Ordinal.typein (@OmegaLevelLex s.length) ⟨s, rfl⟩)
        (x := (t.length : Ordinal))
        ((Ordinal.one_lt_opow).2
          ⟨Ordinal.one_lt_omega0, Ordinal.omega0_ne_zero⟩)
        (omegaLevelRank_lt s) (by exact_mod_cast hlen)
      simpa [g2Code] using h
    exact hbelow.trans_le (by simp [g2Code])
  · unfold g2Code
    have hrank := omegaLevelRank_transport hlen t rfl
    rw [hrank]
    have hexp : (ω ^ ω) ^ (t.length : Ordinal) =
        (ω ^ ω) ^ (s.length : Ordinal) := by rw [hlen]
    rw [hexp, add_lt_add_iff_left]
    exact (Ordinal.typein_lt_typein (@OmegaLevelLex s.length)).2 hlex

noncomputable def g2CodeEmbedding :
    G2LT ↪r ((· < ·) : ((ω ^ ω) ^ ω).ToType →
      ((ω ^ ω) ^ ω).ToType → Prop) :=
  RelEmbedding.ofMonotone
    (fun s ↦ Ordinal.ToType.mk ⟨g2Code s, g2Code_lt_thetaOmega s⟩)
    (fun _ _ h ↦ Ordinal.ToType.mk.strictMono (g2Code_strictMono h))

theorem g2_type_thetaOmega : Ordinal.type G2LT = (ω ^ ω) ^ ω := by
  apply le_antisymm
  · have h := g2CodeEmbedding.ordinal_type_le
    simpa [Ordinal.type_toType] using h
  · rw [← Ordinal.iSup_pow_natCast (Ordinal.opow_pos _ Ordinal.omega0_pos)]
    apply Ordinal.iSup_le
    intro n
    rw [← omegaLevel_type n]
    exact (RelEmbedding.ofMonotone
      (r := @OmegaLevelLex n) (s := G2LT)
      (fun x : OmegaLevel n ↦ x.1)
      (fun a b hab ↦ List.shortlex_def.2
        (Or.inr ⟨a.2.trans b.2.symm, hab⟩))).ordinal_type_le

theorem thetaOmega_eq : (ω ^ ω) ^ ω = ω ^ (ω ^ 2) := by
  rw [← Ordinal.opow_mul]
  congr 1
  rw [pow_two]

/-- Exact order type of the height-two good-sequence model. -/
theorem g2_type : Ordinal.type G2LT = ω ^ (ω ^ 2) := by
  rw [g2_type_thetaOmega, thetaOmega_eq]

theorem orderedG2_type : typeLT OrderedG2 = ω ^ (ω ^ 2) := by
  exact g2_type

end Erdos118.Negative

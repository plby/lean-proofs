import ErdosProblems.Erdos590

open Cardinal Ordinal

namespace Erdos118.EMUnary

universe u

/-- A Ramsey relation with triangle as finite alternative makes every
two-colouring of the vertices constant on a full order-type copy. -/
theorem binary_indivisible_of_ramsey_three
    (lambda : Ordinal)
    (hlambda : lambda ≠ 0)
    (hramsey : OrdinalCardinalRamsey lambda lambda 3)
    (p : lambda.ToType → Prop) :
    ∃ e : lambda.ToType ↪o lambda.ToType, ∃ b : Prop, ∀ x, p (e x) ↔ b := by
  classical
  let blue : SimpleGraph lambda.ToType :=
    SimpleGraph.fromRel (fun x y ↦ p x ≠ p y)
  let red : SimpleGraph lambda.ToType := blueᶜ
  have hcompl : IsCompl red blue := by
    exact IsCompl.symm isCompl_compl
  rcases hramsey red blue hcompl with hred | hblue
  · rcases hred with ⟨s, hs, hstype⟩
    have hisoRel : Nonempty
        (((· < ·) : lambda.ToType → lambda.ToType → Prop) ≃r
          ((· < ·) : s → s → Prop)) := by
      apply Ordinal.type_eq.mp
      simpa [Ordinal.type_toType] using hstype.symm
    let iso : lambda.ToType ≃o s :=
      OrderIso.ofRelIsoLT (Classical.choice hisoRel)
    let e : lambda.ToType ↪o lambda.ToType :=
      iso.toOrderEmbedding.trans (OrderEmbedding.subtype s)
    have hnonempty : Nonempty lambda.ToType :=
      Ordinal.nonempty_toType_iff.mpr hlambda
    let x0 : lambda.ToType := Classical.choice hnonempty
    refine ⟨e, p (e x0), ?_⟩
    intro x
    by_cases hx : x = x0
    · subst x
      rfl
    · have hredAdj : red.Adj (e x) (e x0) := by
        apply hs
        · exact (iso x).2
        · exact (iso x0).2
        · exact fun h ↦ hx (e.injective h)
      have hnblue : ¬ blue.Adj (e x) (e x0) := by
        exact (SimpleGraph.compl_adj blue _ _).mp hredAdj |>.2
      have hpeq : p (e x) = p (e x0) := by
        by_contra hne
        apply hnblue
        exact (SimpleGraph.fromRel_adj _ _ _).mpr
          ⟨fun h ↦ hx (e.injective h), Or.inl hne⟩
      rw [hpeq]
  · rcases hblue with ⟨s, hs, hcard⟩
    rcases Cardinal.mk_eq_nat_iff.mp hcard with ⟨q⟩
    let a : s := q.symm 0
    let b : s := q.symm 1
    let c : s := q.symm 2
    have hab : a ≠ b := by
      intro h
      have h' := congrArg q h
      have := congrArg Fin.val h'
      norm_num [a, b] at this
    have hac : a ≠ c := by
      intro h
      have h' := congrArg q h
      have := congrArg Fin.val h'
      norm_num [a, c] at this
    have hbc : b ≠ c := by
      intro h
      have h' := congrArg q h
      have := congrArg Fin.val h'
      norm_num [b, c] at this
    have habAdj : blue.Adj a.1 b.1 := hs a.2 b.2 (fun h ↦ hab (Subtype.ext h))
    have hacAdj : blue.Adj a.1 c.1 := hs a.2 c.2 (fun h ↦ hac (Subtype.ext h))
    have hbcAdj : blue.Adj b.1 c.1 := hs b.2 c.2 (fun h ↦ hbc (Subtype.ext h))
    have hpab : p a.1 ≠ p b.1 := by
      rcases (SimpleGraph.fromRel_adj _ _ _).mp habAdj with ⟨_, h | h⟩
      · exact h
      · exact h.symm
    have hpac : p a.1 ≠ p c.1 := by
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hacAdj with ⟨_, h | h⟩
      · exact h
      · exact h.symm
    have hpbc : p b.1 ≠ p c.1 := by
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hbcAdj with ⟨_, h | h⟩
      · exact h
      · exact h.symm
    by_cases ha : p a.1 <;> by_cases hb : p b.1 <;>
      by_cases hc : p c.1 <;> simp_all

/-- Finite vertex-colour indivisibility, obtained by repeatedly applying
the preceding binary splitting lemma. -/
theorem finite_indivisible_of_ramsey_three
    (lambda : Ordinal)
    (hlambda : lambda ≠ 0)
    (hramsey : OrdinalCardinalRamsey lambda lambda 3) :
    ∀ (k : ℕ) (c : lambda.ToType → Fin (k + 1)),
      ∃ i : Fin (k + 1), ∃ e : lambda.ToType ↪o lambda.ToType,
        ∀ x, c (e x) = i := by
  intro k
  induction k with
  | zero =>
      intro c
      refine ⟨0, OrderEmbedding.id _, ?_⟩
      intro x
      exact Fin.eq_zero _
  | succ k ih =>
      intro c
      obtain ⟨e, b, hb⟩ :=
        binary_indivisible_of_ramsey_three lambda hlambda hramsey
          (fun x ↦ c x = 0)
      by_cases hbt : b
      · refine ⟨0, e, ?_⟩
        intro x
        exact (hb x).mpr hbt
      · have hne : ∀ x, c (e x) ≠ 0 := by
          intro x hx
          exact hbt ((hb x).mp hx)
        let c' : lambda.ToType → Fin (k + 1) :=
          fun x ↦ Fin.pred (c (e x)) (hne x)
        obtain ⟨i, f, hf⟩ := ih c'
        refine ⟨i.succ, f.comp e, ?_⟩
        intro x
        change c (e (f x)) = i.succ
        rw [show c (e (f x)) = (Fin.pred (c (e (f x))) (hne (f x))).succ by
          exact (Fin.succ_pred _ _).symm]
        exact congrArg Fin.succ (hf x)

/-- Unary finite indivisibility for a concrete well-order relation. -/
def RelFiniteIndivisible {A : Type*} (r : A → A → Prop) : Prop :=
  ∀ (k : ℕ) (c : A → Fin (k + 1)),
    ∃ i : Fin (k + 1), ∃ e : r ↪r r, ∀ x, c (e x) = i

/-- Unary finite indivisibility is invariant under relation isomorphism. -/
theorem RelFiniteIndivisible.congr
    {A B : Type*} {r : A → A → Prop} {s : B → B → Prop}
    (h : RelFiniteIndivisible r) (e : r ≃r s) :
    RelFiniteIndivisible s := by
  intro k c
  obtain ⟨i, f, hf⟩ := h k (fun x ↦ c (e x))
  let g : s ↪r s :=
    e.symm.toRelEmbedding |>.trans f |>.trans e.toRelEmbedding
  refine ⟨i, g, ?_⟩
  intro x
  exact hf (e.symm x)

/-- Finite indivisibility is closed under ordinal (block-lexicographic)
products.  In `B × A`, the first coordinate is the block index. -/
theorem RelFiniteIndivisible.prodLex
    {A B : Type*} {r : A → A → Prop} {s : B → B → Prop}
    [IsWellOrder A r] [IsWellOrder B s]
    (hA : RelFiniteIndivisible r) (hB : RelFiniteIndivisible s) :
    RelFiniteIndivisible (Prod.Lex s r) := by
  intro k c
  choose innerColor innerEmb hinner using
    fun b : B ↦ hA k (fun a ↦ c (b, a))
  obtain ⟨i, outerEmb, houter⟩ := hB k innerColor
  let emb : Prod.Lex s r ↪r Prod.Lex s r :=
    RelEmbedding.ofMonotone
      (fun z : B × A ↦
        (outerEmb z.1, innerEmb (outerEmb z.1) z.2)) (by
          intro x y hxy
          cases hxy with
          | left b₁ b₂ h =>
              exact Prod.Lex.left _ _ (outerEmb.map_rel_iff.mpr h)
          | right b h =>
              exact Prod.Lex.right _ ((innerEmb (outerEmb b)).map_rel_iff.mpr h))
  refine ⟨i, emb, ?_⟩
  intro z
  change c (outerEmb z.1, innerEmb (outerEmb z.1) z.2) = i
  rw [hinner, houter]

/-- The base instance on `(ω^ω).ToType`, ready to be iterated by
`RelFiniteIndivisible.prodLex`. -/
theorem omegaOmega_relFiniteIndivisible
    (hramsey : OrdinalCardinalRamsey
      (ω ^ ω : Ordinal.{u}) (ω ^ ω : Ordinal.{u}) 3) :
    RelFiniteIndivisible
      ((· < ·) : (ω ^ ω : Ordinal.{u}).ToType →
        (ω ^ ω : Ordinal.{u}).ToType → Prop) := by
  intro k c
  obtain ⟨i, e, he⟩ := finite_indivisible_of_ramsey_three
    (ω ^ ω) (by simp) hramsey k c
  exact ⟨i, e.ltEmbedding, he⟩

/-- The concrete `n`-fold ordinal product of a type with itself.  The
leftmost coordinate is the outermost block index. -/
def LexPow (A : Type u) : ℕ → Type u
  | 0 => PUnit.{u + 1}
  | n + 1 => A × LexPow A n

def LexPowRel {A : Type u} (r : A → A → Prop) :
    (n : ℕ) → LexPow A n → LexPow A n → Prop
  | 0 => emptyRelation
  | n + 1 => Prod.Lex r (LexPowRel r n)

instance lexPowRelIsWellOrder {A : Type u} (r : A → A → Prop)
    [IsWellOrder A r] (n : ℕ) : IsWellOrder (LexPow A n) (LexPowRel r n) := by
  induction n with
  | zero =>
      simpa [LexPow, LexPowRel] using
        (Subsingleton.isWellOrder (emptyRelation : PUnit.{u + 1} → PUnit.{u + 1} → Prop))
  | succ n ih =>
      simpa [LexPow, LexPowRel] using
        (inferInstance : IsWellOrder (A × LexPow A n)
          (Prod.Lex r (LexPowRel r n)))

theorem type_lexPowRel {A : Type u} (r : A → A → Prop)
    [IsWellOrder A r] (n : ℕ) :
    Ordinal.type (LexPowRel r n) = (Ordinal.type r) ^ n := by
  induction n with
  | zero =>
      simp [LexPowRel, LexPow]
  | succ n ih =>
      change Ordinal.type (Prod.Lex r (LexPowRel r n)) = _
      rw [Ordinal.type_prod_lex (LexPowRel r n) r, ih, pow_succ]

theorem RelFiniteIndivisible.lexPow
    {A : Type u} {r : A → A → Prop} [IsWellOrder A r]
    (h : RelFiniteIndivisible r) (n : ℕ) :
    RelFiniteIndivisible (LexPowRel r n) := by
  induction n with
  | zero =>
      intro k c
      refine ⟨c PUnit.unit, RelEmbedding.refl _, ?_⟩
      intro x
      cases x
      rfl
  | succ n ih =>
      exact ih.prodLex h

/-- From the Ramsey relation at `ω^ω`, every finite vertex colouring of
the exact ordinal power `ω^(ω*n)` has a monochromatic full-order-type copy.
This is the finite-indivisibility input used on the CNF pieces in the
Erdős--Milner block argument. -/
theorem omega_mul_nat_relFiniteIndivisible
    (hramsey : OrdinalCardinalRamsey
      (ω ^ ω : Ordinal.{u}) (ω ^ ω : Ordinal.{u}) 3)
    (n : ℕ) :
    RelFiniteIndivisible
      ((· < ·) : (ω ^ (ω * n) : Ordinal.{u}).ToType →
        (ω ^ (ω * n) : Ordinal.{u}).ToType → Prop) := by
  classical
  let r : (ω ^ ω : Ordinal.{u}).ToType →
      (ω ^ ω : Ordinal.{u}).ToType → Prop := (· < ·)
  have hlex : RelFiniteIndivisible (LexPowRel r n) :=
    (omegaOmega_relFiniteIndivisible hramsey).lexPow n
  have htype :
      Ordinal.type (LexPowRel r n) =
        typeLT (ω ^ (ω * n) : Ordinal.{u}).ToType := by
    calc
      Ordinal.type (LexPowRel r n) = (Ordinal.type r) ^ n :=
        type_lexPowRel r n
      _ = ((ω ^ ω : Ordinal.{u}) ^ n) := by
        rw [show Ordinal.type r = (ω ^ ω : Ordinal.{u}) by
          exact Ordinal.type_toType _]
      _ = ω ^ (ω * n) := by
        rw [← Ordinal.opow_natCast, ← Ordinal.opow_mul]
      _ = typeLT (ω ^ (ω * n) : Ordinal.{u}).ToType :=
        (Ordinal.type_toType _).symm
  let e : LexPowRel r n ≃r
      ((· < ·) : (ω ^ (ω * n) : Ordinal.{u}).ToType →
        (ω ^ (ω * n) : Ordinal.{u}).ToType → Prop) :=
    Classical.choice (Ordinal.type_eq.mp htype)
  exact hlex.congr e

end Erdos118.EMUnary

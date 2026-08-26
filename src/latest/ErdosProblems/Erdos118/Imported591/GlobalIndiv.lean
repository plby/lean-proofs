import ErdosProblems.Erdos118.Imported591.GoodSequenceTwo
import ErdosProblems.Erdos118.Imported591.PieceIndiv

open Ordinal

namespace Erdos118.Positive.GlobalIndiv

open WeakPigeon
open Erdos118.Negative

/-!
The one-step Erdős--Milner argument used later needs finite unary
indivisibility not only below `omega^2`, but also at the limiting exponent
itself.  This file proves that missing endpoint directly on the nested-list
presentation of `omega^(omega^2)`.

The proof is the same two-level diagonal pigeonhole argument already used
in `WeakPigeon.shortlex_finite_partition`.  On every fixed outer length we
use `omegaLevel_finite_partition`; infinitely many lengths have the same
resulting colour, and padding transports an arbitrary length into those
selected levels.
-/

/-- Pad a fixed outer level on the left by empty inner sequences. -/
noncomputable def omegaLevelPadEmbedding {q t : ℕ} (hqt : q ≤ t) :
    (@OmegaLevelLex q) ↪r (@OmegaLevelLex t) :=
  RelEmbedding.ofMonotone
    (fun x : OmegaLevel q ↦
      ⟨List.replicate (t - q) [] ++ x.1, by
        simp only [List.length_append, List.length_replicate, x.2]
        exact Nat.sub_add_cancel hqt⟩)
    (by
      intro x y hxy
      exact List.Lex.append_left _ hxy (List.replicate (t - q) []))

/-- Every finite colouring of the height-two nested shortlex order has a
monochromatic self-copy. -/
theorem g2_finite_partition (k : ℕ) (c : G2 → Fin (k + 1)) :
    ∃ i : Fin (k + 1), ∃ e : G2LT ↪r G2LT, ∀ x, c (e x) = i := by
  classical
  let levelColor : (q : ℕ) → OmegaLevel q → Fin (k + 1) :=
    fun _ x ↦ c x.1
  choose ci ei hei using
    fun q ↦ omegaLevel_finite_partition q k (levelColor q)
  obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber ci
  let H : Set ℕ := ci ⁻¹' {i}
  letI : Infinite H := by simpa [H] using hi
  let h : ℕ ↪o ℕ := Nat.orderEmbeddingOfSet H
  have hh_mem (q : ℕ) : h q ∈ H := by
    change Nat.orderEmbeddingOfSet H q ∈ H
    rw [Nat.orderEmbeddingOfSet_apply]
    exact (Nat.Subtype.ofNat H q).property
  have hh_color (q : ℕ) : ci (h q) = i := by
    simpa [H] using hh_mem q
  have hq_le (q : ℕ) : q ≤ h q := h.strictMono.le_apply
  let mapFun : G2 → G2 := fun x ↦
    (ei (h x.length)
      (omegaLevelPadEmbedding (hq_le x.length) ⟨x, rfl⟩)).1
  have mapFun_of_level (q : ℕ) (x : OmegaLevel q) :
      mapFun x.1 =
        (ei (h q) (omegaLevelPadEmbedding (hq_le q) x)).1 := by
    rcases x with ⟨x, hx⟩
    change (ei (h x.length)
      (omegaLevelPadEmbedding (hq_le x.length) ⟨x, rfl⟩)).1 = _
    cases hx
    rfl
  have mapFun_length (x : G2) : (mapFun x).length = h x.length := by
    exact (ei (h x.length)
      (omegaLevelPadEmbedding (hq_le x.length) ⟨x, rfl⟩)).2
  have hmono : ∀ ⦃x y : G2⦄, G2LT x y → G2LT (mapFun x) (mapFun y) := by
    intro x y hxy
    change List.Shortlex SL x y at hxy
    change List.Shortlex SL (mapFun x) (mapFun y)
    rw [List.shortlex_def] at hxy ⊢
    rcases hxy with hlen | ⟨hlen, hlex⟩
    · exact Or.inl <| by
        rw [mapFun_length, mapFun_length]
        exact h.strictMono hlen
    · apply Or.inr
      refine ⟨?_, ?_⟩
      · rw [mapFun_length, mapFun_length, hlen]
      · have hlex' : OmegaLevelLex
            (⟨x, rfl⟩ : OmegaLevel x.length)
            (⟨y, hlen.symm⟩ : OmegaLevel x.length) := hlex
        have hpad :=
          (omegaLevelPadEmbedding (hq_le x.length)).map_rel_iff.mpr hlex'
        have hemb := (ei (h x.length)).map_rel_iff.mpr hpad
        change List.Lex SL (mapFun x) (mapFun y)
        rw [mapFun_of_level x.length ⟨x, rfl⟩,
          mapFun_of_level x.length ⟨y, hlen.symm⟩]
        exact hemb
  let e : G2LT ↪r G2LT := RelEmbedding.ofMonotone mapFun hmono
  refine ⟨i, e, ?_⟩
  intro x
  change c (mapFun x) = i
  have he := hei (h x.length)
    (omegaLevelPadEmbedding (hq_le x.length) ⟨x, rfl⟩)
  change levelColor (h x.length)
      (ei (h x.length)
        (omegaLevelPadEmbedding (hq_le x.length) ⟨x, rfl⟩)) = i
  rw [he]
  exact hh_color x.length

theorem g2_relFiniteIndivisible : EMUnary.RelFiniteIndivisible G2LT := by
  intro k c
  exact g2_finite_partition k c

noncomputable abbrev lambda : Ordinal.{0} := ω ^ (ω ^ 2)

noncomputable def g2LambdaRelIso :
    G2LT ≃r ((· < ·) : lambda.ToType → lambda.ToType → Prop) := by
  apply Classical.choice
  apply Ordinal.type_eq.mp
  rw [g2_type, Ordinal.type_toType]

/-- Finite unary indivisibility of the full critical ordinal. -/
theorem lambda_relFiniteIndivisible :
    EMUnary.RelFiniteIndivisible
      ((· < ·) : lambda.ToType → lambda.ToType → Prop) :=
  g2_relFiniteIndivisible.congr g2LambdaRelIso

theorem lambda_finitelyIndivisible :
    Erdos118.Schipperus.K4Core.FinitelyIndivisible lambda.ToType :=
  Erdos118.Schipperus.PieceIndiv.k4_of_relFiniteIndivisible
    lambda_relFiniteIndivisible

end Erdos118.Positive.GlobalIndiv

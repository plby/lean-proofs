import ErdosProblems.Erdos171.StructuredCorrelation
import ErdosProblems.Erdos171.UniformWordFibres
import ErdosProblems.Erdos171.RestrictedMDHJ

namespace Erdos171

open Combinatorics

namespace UniformCorrelation

attribute [local instance] Classical.dec

/-- A local finiteness instance for nested block coordinates.  It is local
to this file so consumers may choose their own representation of the split
coordinate cube. -/
noncomputable local instance instFintypeBlockCoord (M s r : ℕ) :
    Fintype (BlockCoord M s r) :=
  Fintype.ofEquiv (Fin (r * M + s)) (BlockCoord.equivFin M s r).symm

namespace FrozenPrefix

open BlockTower

def freeBlockTailNested {t M s q : ℕ} : ∀ {r : ℕ},
    UniformFibres.FrozenPrefix (Word t M) r (q + 1) →
      Subspace (Fin M ⊕ BlockCoord M s q) (Fin t) (BlockCoord M s r)
  | _, .nil _ => default
  | _, .cons z p => fixedLeft z (freeBlockTailNested p)

@[simp] theorem freeBlockTailNested_apply {t M s q : ℕ} : ∀ {r : ℕ}
    (p : UniformFibres.FrozenPrefix (Word t M) r (q + 1))
    (x : Word t M) (y : BlockCoord M s q → Fin t),
    freeBlockTailNested (s := s) p (Subspace.sumWord x y) =
      BlockTower.functionEquiv t M s r
        (p.prepend (x, (BlockTower.functionEquiv t M s q).symm y))
  | _, .nil _, x, y => by
      change Sum.elim x y =
        BlockTower.functionEquiv t M s (q + 1)
          (x, (BlockTower.functionEquiv t M s q).symm y)
      rw [BlockTower.functionEquiv_succ_apply]
      simp
  | _, .cons z p, x, y => by
      rw [freeBlockTailNested, fixedLeft_apply,
        BlockTower.functionEquiv_succ_apply]
      exact congrArg (Sum.elim z)
        (freeBlockTailNested_apply (s := s) p x y)

def freeBlockTail {t M s q r : ℕ}
    (p : UniformFibres.FrozenPrefix (Word t M) r (q + 1)) :
    Subspace (Fin M ⊕ BlockCoord M s q) (Fin t) (Fin (r * M + s)) :=
  (freeBlockTailNested (s := s) p).reindex (Equiv.refl _) (Equiv.refl _)
    (BlockCoord.equivFin M s r)

@[simp] theorem freeBlockTail_apply_sumWord {t M s q r : ℕ}
    (p : UniformFibres.FrozenPrefix (Word t M) r (q + 1))
    (x : Word t M) (y : BlockCoord M s q → Fin t) :
    freeBlockTail p (Subspace.sumWord x y) =
      BlockTower.coordinateWordEquiv t M s r
        (p.prepend (x, (BlockTower.functionEquiv t M s q).symm y)) := by
  funext i
  simp [freeBlockTail, BlockTower.coordinateWordEquiv_apply,
    Subspace.reindex_apply]

end FrozenPrefix

@[simp] theorem defaultSubspace_apply {alpha iota : Type*}
    (x : iota → alpha) :
    (default : Subspace iota alpha iota) x = x := rfl

/-- Change from the block flattening used by `UniformWordFibres` to the
explicit nested-coordinate flattening used by `FrozenPrefix.freeBlockTail`. -/
noncomputable def uniformCoordinatePullback (t M s r : ℕ)
    (A : Finset (Word t (r * M + s))) :
    Finset (Word t (r * M + s)) :=
  A.map (((BlockTower.wordEquiv t M s r).symm.trans
    (BlockTower.coordinateWordEquiv t M s r)).symm.toEmbedding)

@[simp] theorem density_uniformCoordinatePullback (t M s r : ℕ)
    (A : Finset (Word t (r * M + s))) :
    density (uniformCoordinatePullback t M s r A) = density A := by
  rw [uniformCoordinatePullback, density_map_equiv]

@[simp] theorem wordEquiv_mem_uniformCoordinatePullback
    (t M s r : ℕ) (A : Finset (Word t (r * M + s)))
    (z : BlockTower (Word t M) (Word t s) r) :
    BlockTower.wordEquiv t M s r z ∈ uniformCoordinatePullback t M s r A ↔
      BlockTower.coordinateWordEquiv t M s r z ∈ A := by
  simp only [uniformCoordinatePullback, Finset.mem_map,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a, ha, h⟩
    have hz : (BlockTower.coordinateWordEquiv t M s r).symm a = z := by
      apply (BlockTower.wordEquiv t M s r).injective
      exact h
    have haeq : a = BlockTower.coordinateWordEquiv t M s r z := by
      apply (BlockTower.coordinateWordEquiv t M s r).symm.injective
      simpa using hz
    exact haeq ▸ ha
  · intro hz
    exact ⟨BlockTower.coordinateWordEquiv t M s r z, hz, by simp⟩

theorem density_sectionTails_freeBlockTail_eq_wordFibre
    {k M s q r : ℕ}
    (A : Finset (Word (k + 1) (r * M + s)))
    (p : UniformFibres.FrozenPrefix (Word (k + 1) M) r (q + 1))
    (x : Word (k + 1) M) :
    density (sectionTails
      (default : Subspace (Fin M) (Fin (k + 1)) (Fin M))
      (pullbackFinset (FrozenPrefix.freeBlockTail p) A) x) =
      density (UniformWordFibres.wordFibre
        (uniformCoordinatePullback (k + 1) M s r A) p x) := by
  classical
  let e : (BlockCoord M s q → Fin (k + 1)) ≃ Word (k + 1) (q * M + s) :=
    (BlockTower.functionEquiv (k + 1) M s q).symm.trans
      (BlockTower.wordEquiv (k + 1) M s q)
  have hset :
      sectionTails (default : Subspace (Fin M) (Fin (k + 1)) (Fin M))
          (pullbackFinset (FrozenPrefix.freeBlockTail p) A) x =
        (UniformWordFibres.wordFibre
          (uniformCoordinatePullback (k + 1) M s r A) p x).map
            e.symm.toEmbedding := by
    ext y
    simp only [mem_sectionTails, mem_pullbackFinset, Finset.mem_map,
      Equiv.toEmbedding_apply, UniformWordFibres.mem_wordFibre,
      wordEquiv_mem_uniformCoordinatePullback, defaultSubspace_apply]
    change FrozenPrefix.freeBlockTail p (Subspace.sumWord x y) ∈ A ↔ _
    rw [FrozenPrefix.freeBlockTail_apply_sumWord p x y]
    constructor
    · intro hy
      refine ⟨e y, ?_, ?_⟩
      · simpa [e] using hy
      · exact e.symm_apply_apply y
    · rintro ⟨a, ha, hay⟩
      have haeq : a = e y := by
        apply e.symm.injective
        simpa using hay
      subst a
      simpa [e] using ha
  rw [hset]
  exact density_map_equiv e.symm _

theorem pullback_lineFreeOn {alpha eta iota : Type*}
    [Fintype alpha] [DecidableEq alpha] [Fintype eta] [DecidableEq eta]
    (U : Subspace eta alpha iota) (A : Finset (iota → alpha))
    (hA : ¬ ContainsLineOn (A : Set (iota → alpha))) :
    ¬ ContainsLineOn (pullbackFinset U A : Set (eta → alpha)) := by
  intro h
  apply hA
  obtain ⟨l, hl⟩ := h
  refine ⟨U.lineMap l, ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [Subspace.lineMap_apply]
  exact (mem_pullbackFinset U A (l a)).1 (hl ⟨a, rfl⟩)

theorem exists_structured_correlation_at
    (k m0 m : ℕ) (hk : 2 ≤ k) (hm0 : 0 < m0) (hm0m : m0 ≤ m)
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta0_one : delta0 ≤ 1)
    (htheta : 0 < IncrementArithmetic.theta delta0
      (Fintype.card (Line (Fin k) (Fin m0))))
    (htheta_one : IncrementArithmetic.theta delta0
      (Fintype.card (Line (Fin k) (Fin m0))) ≤ 1)
    (herror : (IncrementArithmetic.eta delta0
      (IncrementArithmetic.theta delta0
        (Fintype.card (Line (Fin k) (Fin m0))))) ^ 2 / 2 ≤ delta0 / 2)
    (hface : density (liftFinset (Finset.univ : Finset (Word k m))) <
      IncrementArithmetic.eta delta0
        (IncrementArithmetic.theta delta0
          (Fintype.card (Line (Fin k) (Fin m0)))))
    (hDHJ : ∀ B : Finset (Word k m0), delta0 / 4 ≤ density B →
      ContainsLine (B : Set (Word k m0))) :
    ∃ n : ℕ, ∀ A : Finset (Word (k + 1) n), delta0 ≤ density A →
      ¬ContainsLine (A : Set (Word (k + 1) n)) →
        ∃ W : Subspace (Fin m) (Fin (k + 1)) (Fin n),
        ∃ D : Fin k → Finset (Word (k + 1) m),
          (∀ i, IsLastInsensitive i (D i : Set (Word (k + 1) m))) ∧
          IncrementArithmetic.gamma delta0
              (IncrementArithmetic.eta delta0
                (IncrementArithmetic.theta delta0
                  (Fintype.card (Line (Fin k) (Fin m0))))) k <
            density (familyInter D) ∧
          (density A + IncrementArithmetic.gamma delta0
              (IncrementArithmetic.eta delta0
                (IncrementArithmetic.theta delta0
                  (Fintype.card (Line (Fin k) (Fin m0))))) k) *
              density (familyInter D) <
            density (pullbackFinset W A ∩ familyInter D) := by
  let theta : ℝ := IncrementArithmetic.theta delta0
    (Fintype.card (Line (Fin k) (Fin m0)))
  let eta : ℝ := IncrementArithmetic.eta delta0 theta
  have heta : 0 < eta := IncrementArithmetic.eta_pos hdelta0 htheta
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hm : 0 < m := hm0.trans_le hm0m
  obtain ⟨N, hN⟩ := exists_correlated_subspace_of_uniform_sections
    k m0 m hkpos hm0 hm0m delta0 eta hdelta0 herror hDHJ
  let M := N + 1
  have hM : 0 < M := by simp [M]
  have hk1 : 2 ≤ k + 1 := by omega
  obtain ⟨R, hR⟩ := UniformWordFibres.exists_uniform_wordFibres_zeroSuffix
    (k + 1) M hk1 hM (eta ^ 2 / 2) (by positivity)
  refine ⟨(R + 1) * M, ?_⟩
  intro A hAdense hline
  let A0 := uniformCoordinatePullback (k + 1) M 0 (R + 1) A
  obtain ⟨q, p, hp⟩ := hR A0
  let P := FrozenPrefix.freeBlockTail (s := 0) p
  let B := pullbackFinset P A
  have hlineOnA : ¬ ContainsLineOn (A : Set (Word (k + 1) ((R + 1) * M))) := by
    simpa only [ContainsLine, ContainsLineOn] using hline
  have hlineB : ¬ ContainsLineOn
      (B : Set ((Fin M ⊕ BlockCoord M 0 q) → Fin (k + 1))) :=
    by simpa only [B] using pullback_lineFreeOn P A hlineOnA
  have hsections : ∀ x : Word (k + 1) M,
      density A - eta ^ 2 / 2 ≤
        density (sectionTails
          (default : Subspace (Fin M) (Fin (k + 1)) (Fin M)) B x) := by
    intro x
    rw [density_sectionTails_freeBlockTail_eq_wordFibre
      (M := M) (s := 0) (q := q) (r := R + 1) A p x]
    have hx := hp x
    have hA0 : (A0.dens : ℝ) = (A.dens : ℝ) := by
      calc
        (A0.dens : ℝ) = density A0 := (density_eq_coe_dens A0).symm
        _ = density A := by simp only [A0, density_uniformCoordinatePullback]
        _ = (A.dens : ℝ) := density_eq_coe_dens A
    simpa only [density_eq_coe_dens, hA0] using hx
  have hNM : N ≤ M := by simp [M]
  obtain ⟨V, hVsections, hVcorrelation⟩ :=
    hN M hNM (default : Subspace (Fin M) (Fin (k + 1)) (Fin M))
      B (density A) hAdense hsections
  obtain ⟨W, D, hDins, hDdense, hDcorr⟩ :=
    structured_correlation_of_correlated_sections hk hm V B hlineB
      delta0 (density A) theta hdelta0 hdelta0_one hAdense htheta
      htheta_one hface hVsections hVcorrelation
  refine ⟨P.comp W, D, hDins, hDdense, ?_⟩
  simpa [B, P, theta, pullbackFinset_comp] using hDcorr

end UniformCorrelation

end Erdos171

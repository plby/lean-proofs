import ErdosProblems.Erdos565.BinomialBounds
import ErdosProblems.Erdos565.FiniteAnalysis
import ErdosProblems.Erdos565.Janson

/-!
# The specialised non-Janson container assembly

This file formalises the finite, deterministic assembly in Theorem 5.4 of
Aragão--Campos--Dahia--Filipe--Marciano.  The probabilistic decomposition and the
Janson-container step are exposed as hypotheses of `assemble`; the theorem here
proves that these two fingerprint maps really give one finite family of
containers, proves its cardinality bound, and proves the bad-set covering
conclusion.  In particular, no choice function or unproved declaration is hidden
in the construction.

The paper writes `(2 / q)^(3 q n)` for the final analytic estimate.  The exact
finite bound proved here is the product of the two partial binomial sums.  It is
the form used before applying the (separate) real-valued binomial estimate and
avoids all floor/ceiling ambiguity.
-/

open scoped BigOperators

namespace Erdos565
namespace SpecialContainer

open Hypergraph

variable {V U : Type*}

/-! ## Projection and adjoining the extension vertex -/

section Projection

variable [DecidableEq V] [DecidableEq U]

/-- Adjoin the same distinguished vertex to every edge. -/
def coneAt (v : U) (K : Hypergraph U) : Hypergraph U :=
  K.image fun E ↦ insert v E

@[simp] theorem mem_coneAt {v : U} {K : Hypergraph U} {E : Finset U} :
    E ∈ coneAt v K ↔ ∃ L ∈ K, insert v L = E := by
  simp [coneAt]

theorem coneAt_mono {v : U} {K L : Hypergraph U} (hKL : K ⊆ L) :
    coneAt v K ⊆ coneAt v L := by
  intro E hE
  obtain ⟨A, hAK, rfl⟩ := mem_coneAt.mp hE
  exact mem_coneAt.mpr ⟨A, hKL hAK, rfl⟩

/-- Restrict a hypergraph, project its edges, and adjoin the new vertex. -/
def projectedExtension (π : V → U) (v : U) (H : Hypergraph V)
    (I : Finset V) : Hypergraph U :=
  coneAt v ((H.restrict I).map π)

theorem projectedExtension_mono (π : V → U) (v : U) (H : Hypergraph V)
    {I J : Finset V} (hIJ : I ⊆ J) :
    projectedExtension π v H I ⊆ projectedExtension π v H J := by
  exact coneAt_mono (map_mono (restrict_mono_right H hIJ))

/-- The local extension hypergraph, with the already available family `F`. -/
def extensionUnion (π : V → U) (v : U) (H : Hypergraph V)
    (F : Hypergraph U) (I : Finset V) : Hypergraph U :=
  projectedExtension π v H I ∪ F

theorem extensionUnion_mono (π : V → U) (v : U) (H : Hypergraph V)
    (F : Hypergraph U) {I J : Finset V} (hIJ : I ⊆ J) :
    extensionUnion π v H F I ⊆ extensionUnion π v H F J := by
  intro E hE
  rcases Finset.mem_union.mp hE with hE | hE
  · exact Finset.mem_union_left _ (projectedExtension_mono π v H hIJ hE)
  · exact Finset.mem_union_right _ hE

/-- The bad subsets in the specialised theorem. -/
def IsBad [Fintype U] (π : V → U) (v : U) (H : Hypergraph V)
    (F : Hypergraph U) (p radius : ℝ) (I : Finset V) : Prop :=
  ¬ (extensionUnion π v H F I).IsJanson p radius

/-- Jansonness is upward monotone in the vertex set used for restriction. -/
theorem isJanson_extensionUnion_mono [Fintype U]
    (π : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    {p radius : ℝ} {I J : Finset V} (hIJ : I ⊆ J)
    (hI : (extensionUnion π v H F I).IsJanson p radius) :
    (extensionUnion π v H F J).IsJanson p radius :=
  hI.mono_edges (extensionUnion_mono π v H F hIJ)

theorem isBad_anti [Fintype U]
    (π : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    {p radius : ℝ} {I J : Finset V} (hIJ : I ⊆ J)
    (hJ : IsBad π v H F p radius J) : IsBad π v H F p radius I := by
  intro hI
  exact hJ (isJanson_extensionUnion_mono π v H F hIJ hI)

/-- The auxiliary hypergraph `J'`: its edges are precisely the subsets whose
local extension union is Janson. -/
noncomputable def jansonGeneratingFamily [Fintype V] [Fintype U]
    (π : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    (p radius : ℝ) : Hypergraph V := by
  classical
  exact Finset.univ.powerset.filter fun I ↦
    (extensionUnion π v H F I).IsJanson p radius

@[simp] theorem mem_jansonGeneratingFamily [Fintype V] [Fintype U]
    {π : V → U} {v : U} {H : Hypergraph V} {F : Hypergraph U}
    {p radius : ℝ} {I : Finset V} :
    I ∈ jansonGeneratingFamily π v H F p radius ↔
      (extensionUnion π v H F I).IsJanson p radius := by
  simp [jansonGeneratingFamily]

/-- A bad set is independent in `J'`.  This is the monotonicity step which
starts the fingerprint decomposition in the proof of the specialised theorem. -/
theorem isIndependent_jansonGeneratingFamily_of_isBad
    [Fintype V] [Fintype U]
    (π : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    {p radius : ℝ} {I : Finset V} (hI : IsBad π v H F p radius I) :
    (jansonGeneratingFamily π v H F p radius).IsIndependent I := by
  intro E hE hEI
  apply hI
  exact isJanson_extensionUnion_mono π v H F hEI
    (mem_jansonGeneratingFamily.mp hE)

end Projection

/-! ## Exact finite fingerprint counts -/

section Fingerprints

variable [Fintype V] [DecidableEq V]

/-- All subsets of `V` with at most `k` elements, written as a disjoint
union of uniform layers. -/
def smallSets (k : ℕ) : Finset (Finset V) :=
  (Finset.range (k + 1)).biUnion fun i ↦
    (Finset.univ : Finset V).powersetCard i

@[simp] theorem mem_smallSets {k : ℕ} {S : Finset V} :
    S ∈ smallSets (V := V) k ↔ S.card ≤ k := by
  simp only [smallSets, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨i, hi, hcard⟩
    omega
  · intro hcard
    exact ⟨S.card, by omega, rfl⟩

/-- The exact number appearing before the analytic binomial-tail estimate. -/
def fingerprintCount (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), n.choose i

theorem card_smallSets_le (k : ℕ) :
    (smallSets (V := V) k).card ≤ fingerprintCount (Fintype.card V) k := by
  unfold smallSets fingerprintCount
  calc
    ((Finset.range (k + 1)).biUnion fun i ↦
        (Finset.univ : Finset V).powersetCard i).card
        ≤ ∑ i ∈ Finset.range (k + 1),
            ((Finset.univ : Finset V).powersetCard i).card :=
      Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (k + 1), (Fintype.card V).choose i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp

theorem card_image_smallSets_le (k : ℕ) (f : Finset V → Finset V) :
    ((smallSets (V := V) k).image f).card ≤ fingerprintCount (Fintype.card V) k :=
  (Finset.card_image_le.trans (card_smallSets_le k))

/-- All containers obtained by independently choosing a first fingerprint
of size at most `b` and a second fingerprint of size at most `a`. -/
def assembledContainers (a b : ℕ)
    (ψ : Finset V → Finset V → Finset V) : Finset (Finset V) :=
  (smallSets (V := V) b).biUnion fun T ↦
    (smallSets (V := V) a).image fun S ↦ ψ T S

@[simp] theorem mem_assembledContainers {a b : ℕ}
    {ψ : Finset V → Finset V → Finset V} {X : Finset V} :
    X ∈ assembledContainers a b ψ ↔
      ∃ T, T.card ≤ b ∧ ∃ S, S.card ≤ a ∧ ψ T S = X := by
  simp [assembledContainers]

theorem card_assembledContainers_le (a b : ℕ)
    (ψ : Finset V → Finset V → Finset V) :
    (assembledContainers a b ψ).card ≤
      fingerprintCount (Fintype.card V) b *
        fingerprintCount (Fintype.card V) a := by
  unfold assembledContainers
  calc
    ((smallSets (V := V) b).biUnion fun T ↦
        (smallSets (V := V) a).image fun S ↦ ψ T S).card
        ≤ ∑ _T ∈ smallSets (V := V) b,
            ((smallSets (V := V) a).image fun S ↦ ψ _T S).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _T ∈ smallSets (V := V) b,
            fingerprintCount (Fintype.card V) a := by
      apply Finset.sum_le_sum
      intro T hT
      exact card_image_smallSets_le a (ψ T)
    _ = (smallSets (V := V) b).card *
          fingerprintCount (Fintype.card V) a := by simp
    _ ≤ fingerprintCount (Fintype.card V) b *
          fingerprintCount (Fintype.card V) a := by
      exact Nat.mul_le_mul_right _ (card_smallSets_le b)

/-- When both fingerprint cutoffs are the literal floor `n / d`, the
division-free entropy bound from `BinomialBounds` gives an explicit power.
Later applications with two different cutoffs use the same lemma on the two
factors separately. -/
theorem card_assembledContainers_floor_same_le (d : ℕ) (hd : 0 < d)
    (ψ : Finset V → Finset V → Finset V) :
    (assembledContainers (V := V) (Fintype.card V / d)
        (Fintype.card V / d) ψ).card ≤
      (8 * d) ^ (2 * (Fintype.card V / d)) := by
  calc
    (assembledContainers (V := V) (Fintype.card V / d)
        (Fintype.card V / d) ψ).card
        ≤ fingerprintCount (Fintype.card V) (Fintype.card V / d) *
            fingerprintCount (Fintype.card V) (Fintype.card V / d) :=
      card_assembledContainers_le _ _ ψ
    _ ≤ (8 * d) ^
          (Fintype.card V / d + Fintype.card V / d) := by
      exact BinomialBounds.mul_partialChooseSum_floor_le
        (Fintype.card V) (Fintype.card V) d hd
    _ = (8 * d) ^ (2 * (Fintype.card V / d)) := by
      congr 1
      omega

/-- The cutoff pattern used in Theorem 5.4.  With `q = 1 / (2*d)`, the
first fingerprint has cutoff `n/(2*d)` and the second has cutoff `n/d`.
This is the exact integral counterpart of the corrected exponent `3*q*n`:
the two fingerprints are counted independently. -/
theorem card_assembledContainers_two_cutoffs_le (d : ℕ) (hd : 0 < d)
    (ψ : Finset V → Finset V → Finset V) :
    (assembledContainers (V := V) (Fintype.card V / (2 * d))
        (Fintype.card V / d) ψ).card ≤
      (16 * d) ^
        (Fintype.card V / d + Fintype.card V / (2 * d)) := by
  have h2d : 0 < 2 * d := Nat.mul_pos (by norm_num) hd
  calc
    (assembledContainers (V := V) (Fintype.card V / (2 * d))
        (Fintype.card V / d) ψ).card
        ≤ fingerprintCount (Fintype.card V) (Fintype.card V / d) *
            fingerprintCount (Fintype.card V) (Fintype.card V / (2 * d)) :=
      card_assembledContainers_le _ _ ψ
    _ ≤ (8 * d) ^ (Fintype.card V / d) *
          (8 * (2 * d)) ^ (Fintype.card V / (2 * d)) :=
      Nat.mul_le_mul
        (BinomialBounds.partialChooseSum_floor_le (Fintype.card V) d hd)
        (BinomialBounds.partialChooseSum_floor_le (Fintype.card V) (2 * d) h2d)
    _ ≤ (16 * d) ^ (Fintype.card V / d) *
          (16 * d) ^ (Fintype.card V / (2 * d)) := by
      apply Nat.mul_le_mul
      · exact pow_le_pow_left' (by omega) _
      · rw [show 8 * (2 * d) = 16 * d by omega]
    _ = (16 * d) ^
          (Fintype.card V / d + Fintype.card V / (2 * d)) := by
      rw [pow_add]

end Fingerprints

/-! ## Parameters and output of the specialised theorem -/

/-- The exact parameter inequalities in the specialised non-Janson
container theorem. -/
def ParameterConditions (n s r : ℕ) (q p R R' η : ℝ) : Prop :=
  s ≤ n ∧
  2 ≤ r ∧
  0 < q ∧ q < 1 / 8 ∧
  0 < p ∧ p ≤ q / (2 ^ 11 * (r : ℝ) * (s : ℝ) ^ 2) ∧
  R = p * n / (2 ^ 6 * (r : ℝ)) ∧
  0 ≤ R' ∧ R' ≤ R / 16 ∧
  η = p ^ 4 * (q / 2) ^ (4 * s)

/-- The projection hypotheses from the specialised theorem. -/
def ProjectionConditions [DecidableEq V] [DecidableEq U]
    (π : V → U) (H : Hypergraph V) : Prop :=
  (∀ L : Finset V, L.card ≤ 2 * (L.image π).card) ∧
  (∀ E ∈ H, (E.image π).card = E.card)

/-- Finite output package for the specialised theorem.  The two cardinal
inequalities are denominator-cleared versions of `|X| ≥ n/(8r)` and
`|Y| ≥ |X| - n/(256r)`. -/
structure Output [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    (p radius R : ℝ) (r bound : ℕ) where
  containers : Finset (Finset V)
  card_containers : containers.card ≤ bound
  bad_subset : ∀ I : Finset V, IsBad π v H F p radius I →
    ∃ X ∈ containers, I ⊆ X
  localized : ∀ X ∈ containers,
    Fintype.card V ≤ 8 * r * X.card →
    ∃ Y : Finset V, Y ⊆ X ∧
      256 * r * (X.card - Y.card) ≤ Fintype.card V ∧
      ¬ ((H.restrict Y).map π).IsJanson p R

/-! ## Deterministic assembly theorem -/

section Assembly

variable [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

/-- Assemble the two fingerprint stages in the proof of the specialised
container theorem.

`decompose` is the output of the conditional-probability fingerprint
lemma, `containerStep` is the output of the Janson container theorem for
the corresponding cover, and `localize` is the measure-theoretic
localisation conclusion for a fixed pair of fingerprints. -/
noncomputable def assemble
    (π : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    (p R R' η : ℝ) (r a b : ℕ)
    (cover : Finset V → Hypergraph V)
    (ψ : Finset V → Finset V → Finset V)
    (hn : 0 < Fintype.card V)
    (invalidContainer : ∀ (T S : Finset V), T.card ≤ b →
      ¬ (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent T →
      ψ T S = ∅)
    (decompose : ∀ I : Finset V,
      (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent I →
      ∃ T : Finset V, T.card ≤ b ∧ T ⊆ I ∧
        (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent T ∧
        (cover T).IsIndependent I)
    (containerStep : ∀ (T I : Finset V), T.card ≤ b →
      (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent T →
      (cover T).IsIndependent I →
      ∃ S : Finset V, S.card ≤ a ∧ S ⊆ I ∧ I ⊆ ψ T S)
    (localize : ∀ (T S : Finset V), T.card ≤ b →
      (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent T →
      S.card ≤ a →
      Fintype.card V ≤ 8 * r * (ψ T S).card →
      ∃ Y : Finset V, Y ⊆ ψ T S ∧
        256 * r * ((ψ T S).card - Y.card) ≤ Fintype.card V ∧
        ¬ ((H.restrict Y).map π).IsJanson p R) :
    Output π v H F p (R' + η * R) R r
      (fingerprintCount (Fintype.card V) b *
        fingerprintCount (Fintype.card V) a) := by
  let Xs := assembledContainers (V := V) a b ψ
  refine
    { containers := Xs
      card_containers := card_assembledContainers_le a b ψ
      bad_subset := ?_
      localized := ?_ }
  · intro I hbad
    have hInd := isIndependent_jansonGeneratingFamily_of_isBad
      π v H F hbad
    obtain ⟨T, hTb, hTI, hTInd, hCI⟩ := decompose I hInd
    obtain ⟨S, hSa, hSI, hIψ⟩ := containerStep T I hTb hTInd hCI
    refine ⟨ψ T S, ?_, hIψ⟩
    exact mem_assembledContainers.mpr ⟨T, hTb, S, hSa, rfl⟩
  · intro X hX hXlarge
    obtain ⟨T, hTb, S, hSa, rfl⟩ := mem_assembledContainers.mp hX
    by_cases hTInd :
        (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent T
    · exact localize T S hTb hTInd hSa hXlarge
    · rw [invalidContainer T S hTb hTInd] at hXlarge
      simp at hXlarge
      omega

/-- All hypotheses of the specialised non-Janson container theorem, split
at the three substantial lemmas used by its proof.  The first five fields
are exactly the hypotheses in the published theorem; the remaining fields
are the conditional decomposition, Janson-container, and fixed-container
localisation results which are proved in their dedicated modules. -/
structure AssemblyHypotheses
    (π : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    (q p R R' η : ℝ) (r s a b : ℕ)
    (cover : Finset V → Hypergraph V)
    (ψ : Finset V → Finset V → Finset V) : Prop where
  parameters : ParameterConditions (Fintype.card V) s r q p R R' η
  positive_uniformity : 0 < s
  base_uniform : H.IsUniform s
  available_uniform : F.IsUniform (s + 1)
  available_janson : F.IsJanson p R'
  /-- Every available edge avoids the genuinely new extension vertex. -/
  available_fresh : ∀ E ∈ F, v ∉ E
  projection : ProjectionConditions π H
  /-- The extension vertex is genuinely new: it does not occur in the
  projection of the base vertex set. -/
  fresh : ∀ x, π x ≠ v
  invalidContainer : ∀ (T S : Finset V), T.card ≤ b →
    ¬ (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent T →
    ψ T S = ∅
  decompose : ∀ I : Finset V,
    (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent I →
    ∃ T : Finset V, T.card ≤ b ∧ T ⊆ I ∧
      (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent T ∧
      (cover T).IsIndependent I
  containerStep : ∀ (T I : Finset V), T.card ≤ b →
    (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent T →
    (cover T).IsIndependent I →
    ∃ S : Finset V, S.card ≤ a ∧ S ⊆ I ∧ I ⊆ ψ T S
  /-- The deterministic second-stage container is the actual Janson-form
  container for `cover T`.  The nonempty premise is necessary because the
  radius-zero convention makes the corresponding statement false for the
  empty container. -/
  container_nonJanson : ∀ (T S : Finset V), T.card ≤ b → S.card ≤ a →
    (ψ T S).Nonempty →
    ¬ ((cover T).restrict (ψ T S)).IsJanson p
      ((1 / (256 * (r : ℝ))) * p * (ψ T S).card)
  localize : ∀ (T S : Finset V), T.card ≤ b →
    (jansonGeneratingFamily π v H F p (R' + η * R)).IsIndependent T →
    S.card ≤ a →
    Fintype.card V ≤ 8 * r * (ψ T S).card →
    ∃ Y : Finset V, Y ⊆ ψ T S ∧
      256 * r * ((ψ T S).card - Y.card) ≤ Fintype.card V ∧
      ¬ ((H.restrict Y).map π).IsJanson p R

/-- The specialised non-Janson container conclusion, obtained by plugging
the three independently proved stages into the deterministic assembly.
The exact finite cardinal bound is the product of the two partial binomial
sums; `card_assembledContainers_two_cutoffs_le` turns it into the corrected
three-fingerprint-exponent estimate in the reciprocal-`q` application. -/
noncomputable def specializedNonJansonContainer
    (π : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    (q p R R' η : ℝ) (r s a b : ℕ)
    (cover : Finset V → Hypergraph V)
    (ψ : Finset V → Finset V → Finset V)
    (h : AssemblyHypotheses π v H F q p R R' η r s a b cover ψ) :
    Output π v H F p (R' + η * R) R r
      (fingerprintCount (Fintype.card V) b *
        fingerprintCount (Fintype.card V) a) :=
  assemble π v H F p R R' η r a b cover ψ
    (lt_of_lt_of_le h.positive_uniformity h.parameters.1)
    h.invalidContainer h.decompose h.containerStep h.localize

end Assembly

end SpecialContainer
end Erdos565

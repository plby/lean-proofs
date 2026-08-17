import ErdosProblems.Erdos780.External.TargetChains
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
The alpha-split target complex for the cyclic Tucker labeling.

A vertex is a sign together with a label index.  At a low index there may be
at most one sign in a face; at a high index there may be at most `p - 1`
signs.  The resulting faces form a downward-closed complex of maximum face
cardinality `alpha + (m - alpha) * (p - 1)`.
-/

namespace AllowedFaces

open scoped BigOperators

abbrev Label (p m : ℕ) := ZMod p × Fin m

/-- Vertices of `s` whose second coordinate is `j`. -/
def fiber {p m : ℕ} (s : Finset (Label p m)) (j : Fin m) :
    Finset (Label p m) :=
  s.filter fun v ↦ v.2 = j

/-- Capacity of the `j`th label coordinate. -/
def capacity (p alpha : ℕ) {m : ℕ} (j : Fin m) : ℕ :=
  if j.val < alpha then 1 else p - 1

/-- The alpha-split faces: one sign at a low index, and at most `p - 1`
signs at a high index. -/
def IsAllowed {p m : ℕ} (alpha : ℕ) (s : Finset (Label p m)) : Prop :=
  ∀ j : Fin m, (fiber s j).card ≤ capacity p alpha j

theorem isAllowed_iff {p m alpha : ℕ} {s : Finset (Label p m)} :
    IsAllowed alpha s ↔
      ∀ j : Fin m, (fiber s j).card ≤
        if j.val < alpha then 1 else p - 1 :=
  Iff.rfl

/-- Allowed faces are closed downward. -/
theorem IsAllowed.mono {p m alpha : ℕ} {s t : Finset (Label p m)}
    (hs : IsAllowed alpha s) (hts : t ⊆ s) : IsAllowed alpha t := by
  intro j
  exact (Finset.card_le_card (Finset.filter_subset_filter _ hts)).trans (hs j)

@[simp] theorem isAllowed_empty (p m alpha : ℕ) :
    IsAllowed (p := p) (m := m) alpha ∅ := by
  intro j
  simp [fiber]

/-- Sum of all alpha-split coordinate capacities. -/
theorem sum_capacity {p m alpha : ℕ} (halpha : alpha ≤ m) :
    (∑ j : Fin m, capacity p alpha j) =
      alpha + (m - alpha) * (p - 1) := by
  change (∑ j : Fin m, if j.val < alpha then 1 else p - 1) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ if j < alpha then 1 else p - 1)]
  have hm : m = alpha + (m - alpha) := by omega
  rw [hm, Finset.sum_range_add]
  have hlow :
      (∑ x ∈ Finset.range alpha,
        if x < alpha then 1 else p - 1) = alpha := by
    calc
      _ = ∑ x ∈ Finset.range alpha, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [Finset.mem_range.1 hx]
      _ = alpha := by simp
  have hhigh :
      (∑ x ∈ Finset.range (m - alpha),
        if alpha + x < alpha then 1 else p - 1) =
        (m - alpha) * (p - 1) := by
    calc
      _ = ∑ x ∈ Finset.range (m - alpha), (p - 1) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simp
      _ = (m - alpha) * (p - 1) := by simp
  rw [hlow, hhigh]
  simp

/-- Every allowed face has at most the advertised number of vertices. -/
theorem IsAllowed.card_le {p m alpha : ℕ} {s : Finset (Label p m)}
    (hs : IsAllowed alpha s) (halpha : alpha ≤ m) :
    s.card ≤ alpha + (m - alpha) * (p - 1) := by
  rw [Finset.card_eq_sum_card_fiberwise
    (s := s) (t := Finset.univ) (f := Prod.snd) (by simp)]
  calc
    (∑ j ∈ Finset.univ, (s.filter fun v ↦ v.2 = j).card) ≤
        ∑ j ∈ Finset.univ, capacity p alpha j := by
          exact Finset.sum_le_sum fun j _ ↦ hs j
    _ = alpha + (m - alpha) * (p - 1) := by
      simpa using sum_capacity (p := p) halpha

/-- The set of allowed exterior-basis indices. -/
def allowedFaceSet (p m alpha : ℕ) : Set (Finset (Label p m)) :=
  {s | IsAllowed alpha s}

/-- The span of allowed basis faces in the full exterior-chain coordinate
module `Finset (Label p m) →₀ R`. -/
def allowedChains (R : Type*) [CommRing R] (p m alpha : ℕ) :
    Submodule R (TargetChains.FullChain R (Label p m)) :=
  Finsupp.supported R R (allowedFaceSet p m alpha)

theorem mem_allowedChains {R : Type*} [CommRing R] {p m alpha : ℕ}
    (c : TargetChains.FullChain R (Label p m)) :
    c ∈ allowedChains R p m alpha ↔
      ∀ s ∈ c.support, IsAllowed alpha s := by
  rw [allowedChains, Finsupp.mem_supported]
  rfl

/-- The allowed submodule is exactly the span of its standard basis faces. -/
theorem allowedChains_eq_span {R : Type*} [CommRing R] (p m alpha : ℕ) :
    allowedChains R p m alpha =
      Submodule.span R
        ((fun s : Finset (Label p m) ↦ Finsupp.single s (1 : R)) ''
          allowedFaceSet p m alpha) := by
  exact Finsupp.supported_eq_span_single R (allowedFaceSet p m alpha)

/-- Basis of the allowed submodule, indexed by allowed faces. -/
noncomputable def allowedBasis {R : Type*} [CommRing R] (p m alpha : ℕ) :
    Module.Basis {s : Finset (Label p m) // IsAllowed alpha s}
      R (allowedChains R p m alpha) :=
  Finsupp.basisSingleOne.map
    (Finsupp.supportedEquivFinsupp
      (allowedFaceSet p m alpha)).symm

/-- The homogeneous degree-`q` part, where chain degree `q` means basis
faces of cardinality `q + 1`. -/
def allowedDegreeChains (R : Type*) [CommRing R]
    (p m alpha q : ℕ) :
    Submodule R (TargetChains.FullChain R (Label p m)) :=
  Finsupp.supported R R
    {s | IsAllowed alpha s ∧ s.card = q + 1}

/-- At the first degree above the target dimension, the allowed homogeneous
chain group is zero.  Here `Q` is the maximum allowed face cardinality, so
chain degree `Q` consists of faces of cardinality `Q + 1`. -/
theorem allowedDegreeChains_Q_eq_bot {R : Type*} [CommRing R]
    {p m alpha : ℕ} (halpha : alpha ≤ m) :
    allowedDegreeChains R p m alpha
      (alpha + (m - alpha) * (p - 1)) = ⊥ := by
  apply le_antisymm
  · intro c hc
    change c ∈ Finsupp.supported R R
      {s : Finset (Label p m) |
        IsAllowed alpha s ∧
          s.card = alpha + (m - alpha) * (p - 1) + 1} at hc
    rw [Finsupp.mem_supported] at hc
    rw [Submodule.mem_bot]
    ext s
    by_cases hcs : s ∈ c.support
    · have hs := hc hcs
      have hle := hs.1.card_le halpha
      have hcard := hs.2
      have : ¬ s.card ≤ alpha + (m - alpha) * (p - 1) := by omega
      exact (this hle).elim
    · exact Finsupp.notMem_support_iff.mp hcs
  · exact bot_le

end AllowedFaces

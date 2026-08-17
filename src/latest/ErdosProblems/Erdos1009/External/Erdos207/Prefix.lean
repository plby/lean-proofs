import ErdosProblems.Erdos1009.External.Erdos207.Basic

namespace Erdos207

open Finset

/-- The graph whose edges are the pairs covered by a family of triples. -/
def coveredGraph {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : SimpleGraph V where
  Adj u v := ∃ T ∈ C, u ∈ T.1 ∧ v ∈ T.1 ∧ u ≠ v
  symm := ⟨by
    rintro u v ⟨T, hTC, huT, hvT, huv⟩
    exact ⟨T, hTC, hvT, huT, huv.symm⟩⟩
  loopless := ⟨by
    rintro u ⟨T, hTC, huT, hvT, huu⟩
    exact huu rfl⟩

instance coveredGraph.instDecidableRel {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : DecidableRel (coveredGraph C).Adj :=
  by
    intro u v
    change Decidable (∃ T ∈ C, u ∈ T.1 ∧ v ∈ T.1 ∧ u ≠ v)
    infer_instance

/-- A partial Steiner triple system: no pair is covered by two distinct
triples. -/
def IsPackingOn {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : Prop :=
  ∀ u v : V, u ≠ v → ∀ T ∈ C, u ∈ T.1 → v ∈ T.1 →
    ∀ U ∈ C, u ∈ U.1 → v ∈ U.1 → T = U

/-- Packinghood specialized to `Fin n`. -/
abbrev IsPacking {n : ℕ} (C : TripleSystem n) : Prop := IsPackingOn C

@[simp]
lemma coveredGraph_adj {V : Type*} [DecidableEq V]
    {C : TripleSystemOn V} {u v : V} :
    (coveredGraph C).Adj u v ↔
      ∃ T ∈ C, u ∈ T.1 ∧ v ∈ T.1 ∧ u ≠ v :=
  Iff.rfl

/-- A packing decomposes precisely the graph of the pairs it covers. -/
theorem IsPackingOn.isTriangleDecomposition {V : Type*} [DecidableEq V]
    {C : TripleSystemOn V} (hC : IsPackingOn C) :
    IsTriangleDecomposition (coveredGraph C) C := by
  constructor
  · intro T hTC u huT v hvT huv
    exact ⟨T, hTC, huT, hvT, huv⟩
  · intro u v huv
    obtain ⟨T, hTC, huT, hvT, huv'⟩ := huv
    refine ⟨T, ⟨hTC, huT, hvT⟩, ?_⟩
    intro U hU
    exact (hC u v huv' T hTC huT hvT U hU.1 hU.2.1 hU.2.2).symm

/-- Distinct triples in a packing meet in at most one vertex. -/
lemma IsPackingOn.inter_card_le_one {V : Type*} [DecidableEq V]
    {H : TripleSystemOn V} (hH : IsPackingOn H)
    {T U : TripleOn V} (hTH : T ∈ H) (hUH : U ∈ H) (hTU : T ≠ U) :
    (T.1 ∩ U.1).card ≤ 1 := by
  by_contra hinter
  have hinter' : 1 < (T.1 ∩ U.1).card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hinter'
  have hTmem := Finset.mem_inter.mp hu
  have hUmem := Finset.mem_inter.mp hv
  exact hTU (hH u v huv T hTH hTmem.1 hUmem.1
    U hUH hTmem.2 hUmem.2)

/-- The leave of a partial triple system consists of all as-yet uncovered
pairs. -/
def leaveGraph {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : SimpleGraph V :=
  (coveredGraph C)ᶜ

instance leaveGraph.instDecidableRel {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : DecidableRel (leaveGraph C).Adj :=
  by
    intro u v
    change Decidable (u ≠ v ∧
      ¬ ∃ T ∈ C, u ∈ T.1 ∧ v ∈ T.1 ∧ u ≠ v)
    infer_instance

@[simp]
lemma leaveGraph_adj {V : Type*} [DecidableEq V]
    {C : TripleSystemOn V} {u v : V} :
    (leaveGraph C).Adj u v ↔
      u ≠ v ∧ ¬ ∃ T ∈ C, u ∈ T.1 ∧ v ∈ T.1 ∧ u ≠ v := by
  simp [leaveGraph]

/-- Covered pairs and uncovered pairs are edge-disjoint. -/
lemma coveredGraph_disjoint_leaveGraph {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) :
    Disjoint (coveredGraph C) (leaveGraph C) := by
  exact disjoint_compl_right

/-- Covered pairs together with the leave form the complete graph. -/
lemma coveredGraph_sup_leaveGraph {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) :
    coveredGraph C ⊔ leaveGraph C = SimpleGraph.completeGraph V := by
  simp [leaveGraph]

/-- Removing the edge-disjoint triangles of a packing from an admissible
complete graph preserves the two divisibility conditions. -/
theorem IsPacking.leave_triangleDivisible {n : ℕ} {C : TripleSystem n}
    (hC : IsPacking C) (hadm : Admissible n) :
    TriangleDivisible (leaveGraph C) := by
  classical
  have hsup : TriangleDivisible (coveredGraph C ⊔ leaveGraph C) := by
    simpa only [coveredGraph_sup_leaveGraph] using
      admissible_complete_triangleDivisible hadm
  exact TriangleDivisible.right_of_sup hsup
    hC.isTriangleDecomposition.triangleDivisible
    (coveredGraph_disjoint_leaveGraph C)

/-- A Steiner triple system is precisely a triangle-decomposition of the
complete graph. -/
theorem isSteiner_iff_triangleDecomposition {n : ℕ} {H : TripleSystem n} :
    IsSteiner H ↔ IsTriangleDecomposition (SimpleGraph.completeGraph (Fin n)) H := by
  constructor
  · intro hH
    refine ⟨?_, ?_⟩
    · intro T hTH u hu v hv huv
      simpa using huv
    · intro u v huv
      exact hH u v (by simpa using huv)
  · intro hH u v huv
    exact hH.2 u v (by simpa using huv)

/-- The classical congruence obstruction is necessary for every nonempty
Steiner triple system. -/
theorem IsSteiner.admissible {n : ℕ} {H : TripleSystem n} (hn : 0 < n)
    (hH : IsSteiner H) : Admissible n :=
  complete_triangleDivisible_admissible hn
    ((isSteiner_iff_triangleDecomposition.mp hH).triangleDivisible)

/-- `C` is a `(v,e)`-configuration: it has `e` triples spanning at most `v`
vertices. -/
def IsConfigOn {V : Type*} [DecidableEq V] (v e : ℕ)
    (C : TripleSystemOn V) : Prop :=
  C.card = e ∧ (verticesOn C).card ≤ v

/-- Configurationhood specialized to `Fin n`. -/
abbrev IsConfig {n : ℕ} (v e : ℕ) (C : TripleSystem n) : Prop :=
  IsConfigOn v e C

/-- There is no `(r,r-2)`-configuration for `4 ≤ r ≤ q`. -/
def GirthGreaterOn {V : Type*} [DecidableEq V] (q : ℕ)
    (H : TripleSystemOn V) : Prop :=
  ∀ r : ℕ, 4 ≤ r → r ≤ q →
    ¬ ∃ C : TripleSystemOn V, C ⊆ H ∧ IsConfigOn r (r - 2) C

/-- High girth specialized to `Fin n`. -/
abbrev GirthGreater {n : ℕ} (q : ℕ) (H : TripleSystem n) : Prop :=
  GirthGreaterOn q H

/-- A finite collection of forbidden configurations. -/
abbrev ForbiddenFamilyOn (V : Type*) [DecidableEq V] :=
  Finset (TripleSystemOn V)

/-- A triple family avoids `F` when it contains no member of `F`. -/
def AvoidsForbidden {V : Type*} [DecidableEq V]
    (H : TripleSystemOn V) (F : ForbiddenFamilyOn V) : Prop :=
  ∀ C ∈ F, ¬ C ⊆ H

/-- The canonical finite family of every `(r,r-2)`-configuration with
`4 ≤ r ≤ q`. -/
def forbiddenConfigurationsOn {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) : ForbiddenFamilyOn V :=
  (Icc 4 q).biUnion fun r ↦
    (univ : Finset (TripleSystemOn V)).filter fun C ↦
      C.card = r - 2 ∧ (verticesOn C).card ≤ r

@[simp]
lemma mem_forbiddenConfigurationsOn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {C : TripleSystemOn V} :
    C ∈ forbiddenConfigurationsOn q ↔
      ∃ r : ℕ, 4 ≤ r ∧ r ≤ q ∧ IsConfigOn r (r - 2) C := by
  simp [forbiddenConfigurationsOn, IsConfigOn, and_assoc]

/-- The finite forbidden-family formulation is exactly the quantified girth
definition. -/
theorem avoidsForbidden_forbiddenConfigurationsOn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : TripleSystemOn V} :
    AvoidsForbidden H (forbiddenConfigurationsOn q) ↔
      GirthGreaterOn q H := by
  constructor
  · intro havoid r hr4 hrq
    rintro ⟨C, hCH, hconfig⟩
    exact havoid C (mem_forbiddenConfigurationsOn_iff.mpr
      ⟨r, hr4, hrq, hconfig⟩) hCH
  · intro hgirth C hCforbid hCH
    obtain ⟨r, hr4, hrq, hconfig⟩ :=
      mem_forbiddenConfigurationsOn_iff.mp hCforbid
    exact hgirth r hr4 hrq ⟨C, hCH, hconfig⟩

/-- A triangle can be selected by the constrained process when it is new,
keeps the chosen family a packing, and creates no forbidden member. -/
def IsLegalExtension {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (C : TripleSystemOn V) (T : TripleOn V) : Prop :=
  T ∉ C ∧ IsPackingOn (insert T C) ∧ AvoidsForbidden (insert T C) F

/-- The reflexive-transitive closure of legal greedy insertions.  This is the
support-level object underlying the later finite probability process. -/
inductive GreedyReachable {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (C₀ : TripleSystemOn V) :
    TripleSystemOn V → Prop
  | refl : GreedyReachable F C₀ C₀
  | step {C : TripleSystemOn V} {T : TripleOn V} :
      GreedyReachable F C₀ C → IsLegalExtension F C T →
        GreedyReachable F C₀ (insert T C)

namespace GreedyReachable

lemma isPacking {V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {C₀ C : TripleSystemOn V}
    (h₀ : IsPackingOn C₀) (h : GreedyReachable F C₀ C) :
    IsPackingOn C := by
  induction h with
  | refl => exact h₀
  | step _ hlegal _ => exact hlegal.2.1

lemma avoidsForbidden {V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {C₀ C : TripleSystemOn V}
    (h₀ : AvoidsForbidden C₀ F) (h : GreedyReachable F C₀ C) :
    AvoidsForbidden C F := by
  induction h with
  | refl => exact h₀
  | step _ hlegal _ => exact hlegal.2.2

lemma initial_subset {V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {C₀ C : TripleSystemOn V}
    (h : GreedyReachable F C₀ C) : C₀ ⊆ C := by
  induction h with
  | refl => exact Subset.rfl
  | step _ _ ih => exact ih.trans (subset_insert _ _)

end GreedyReachable

/-- Retain from `A` exactly the triangles legal relative to `C`. -/
noncomputable def legalAvailable {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (C A : TripleSystemOn V) : TripleSystemOn V := by
  classical
  exact A.filter fun T ↦ IsLegalExtension F C T

@[simp]
lemma mem_legalAvailable_iff {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {C A : TripleSystemOn V} {T : TripleOn V} :
    T ∈ legalAvailable F C A ↔ T ∈ A ∧ IsLegalExtension F C T := by
  classical
  simp [legalAvailable]

/-- State of the finite constrained greedy process. -/
structure GreedyStateOn (V : Type*) [DecidableEq V] where
  chosen : TripleSystemOn V
  available : TripleSystemOn V

instance {V : Type*} [DecidableEq V] : DecidableEq (GreedyStateOn V) :=
  fun S T ↦ decidable_of_iff
    (S.chosen = T.chosen ∧ S.available = T.available) ⟨by
      rintro ⟨hchosen, havailable⟩
      cases S
      cases T
      simp_all, by
      intro h
      subst T
      exact ⟨rfl, rfl⟩⟩

instance {V : Type*} [Fintype V] [DecidableEq V] : Finite (GreedyStateOn V) :=
  Finite.of_injective (fun S : GreedyStateOn V ↦ (S.chosen, S.available)) (by
    intro S T h
    cases S
    cases T
    simp_all)

noncomputable instance {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype (GreedyStateOn V) := Fintype.ofFinite _

/-- The state invariant maintained by every supported greedy trajectory. -/
def GreedyInvariant {V : Type*} [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) : Prop :=
  IsPackingOn S.chosen ∧ AvoidsForbidden S.chosen F ∧
    ∀ T ∈ S.available, IsLegalExtension F S.chosen T

/-- Select `T` and recompute the legal part of the remaining availability
set. -/
noncomputable def greedyStep {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V) :
    GreedyStateOn V where
  chosen := insert T S.chosen
  available := legalAvailable F (insert T S.chosen) (S.available.erase T)

lemma GreedyInvariant.step {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    GreedyInvariant F (greedyStep F S T) := by
  have hlegal := hS.2.2 T hT
  refine ⟨hlegal.2.1, hlegal.2.2, ?_⟩
  intro U hU
  exact (mem_legalAvailable_iff.mp hU).2

/-- A fuel-bounded deterministic realization of the greedy process.  A
random process is obtained by supplying a random policy; structural
termination is immediate from the fuel. -/
noncomputable def greedyRun {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (pick : GreedyStateOn V → Option (TripleOn V)) :
    ℕ → GreedyStateOn V → GreedyStateOn V
  | 0, S => S
  | fuel + 1, S =>
      match pick S with
      | none => S
      | some T =>
          if T ∈ S.available then greedyRun F pick fuel (greedyStep F S T) else S

theorem greedyRun_invariant {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {pick : GreedyStateOn V → Option (TripleOn V)}
    (fuel : ℕ) {S : GreedyStateOn V} (hS : GreedyInvariant F S) :
    GreedyInvariant F (greedyRun F pick fuel S) := by
  induction fuel generalizing S with
  | zero => exact hS
  | succ fuel ih =>
      cases hpick : pick S with
      | none => simpa [greedyRun, hpick] using hS
      | some T =>
          by_cases hT : T ∈ S.available
          · simpa [greedyRun, hpick, hT] using ih (hS.step hT)
          · simpa [greedyRun, hpick, hT] using hS

/-- Uniform constrained-greedy transition: choose one available triangle
uniformly, or remain in place if no triangle is available. -/
noncomputable def greedyKernel {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) :
    FiniteLaw (GreedyStateOn V) := by
  classical
  by_cases hA : S.available.Nonempty
  · let hne : Nonempty S.available := ⟨⟨hA.choose, hA.choose_spec⟩⟩
    let next : S.available → GreedyStateOn V := fun T ↦ greedyStep F S T.1
    exact FiniteLaw.map next (@FiniteLaw.uniform S.available _ hne)
  · exact FiniteLaw.pure S

theorem greedyKernel_supported {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (hS : GreedyInvariant F S) :
    FiniteLaw.SupportedOn (GreedyInvariant F) (greedyKernel F S) := by
  classical
  unfold greedyKernel
  split_ifs with hA
  · let hne : Nonempty S.available := ⟨⟨hA.choose, hA.choose_spec⟩⟩
    let next : S.available → GreedyStateOn V := fun T ↦ greedyStep F S T.1
    have hu : FiniteLaw.SupportedOn (fun _ : S.available ↦ True)
        (@FiniteLaw.uniform S.available _ hne) :=
      FiniteLaw.uniform_supported _ fun _ ↦ trivial
    exact hu.map next fun T _ ↦ hS.step T.2
  · exact FiniteLaw.supportedOn_pure _ hS

/-- Law of the finite uniform constrained process after `fuel` transitions. -/
noncomputable def greedyProcessLaw {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (fuel : ℕ) (S : GreedyStateOn V) :
    FiniteLaw (GreedyStateOn V) :=
  FiniteLaw.iterateKernel (greedyKernel F) fuel (FiniteLaw.pure S)

theorem greedyProcessLaw_supported {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {fuel : ℕ} {S : GreedyStateOn V}
    (hS : GreedyInvariant F S) :
    FiniteLaw.SupportedOn (GreedyInvariant F) (greedyProcessLaw F fuel S) := by
  classical
  apply FiniteLaw.SupportedOn.iterateKernel
    (FiniteLaw.supportedOn_pure _ hS) (greedyKernel F)
  intro S' hS'
  exact greedyKernel_supported hS'

theorem greedyProcessLaw_invariant_probability_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {fuel : ℕ} {S : GreedyStateOn V}
    (hS : GreedyInvariant F S) :
    (greedyProcessLaw F fuel S).probability (GreedyInvariant F) = 1 :=
  FiniteLaw.probability_eq_one_of_supported _ _
    (greedyProcessLaw_supported hS)

/-- A triangle-decomposition satisfying the prescribed girth cutoff. -/
def IsHighGirthTriangleDecomposition {V : Type*} [DecidableEq V]
    (q : ℕ) (G : SimpleGraph V) (C : TripleSystemOn V) : Prop :=
  IsTriangleDecomposition G C ∧ GirthGreaterOn q C

/-- All endpoints of every edge of `G` lie in `X`.  This adjacency-based
formulation avoids imposing a decidable-adjacency instance merely to form
`SimpleGraph.support`. -/
def GraphSupportedOn {V : Type*} (G : SimpleGraph V) (X : Set V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∈ X ∧ v ∈ X

/-- The absorption property (A1) of the KSSS high-girth absorber.  The
flexible set `X` is independent in `H`, and every triangle-divisible graph
supported on `X` can be absorbed into a high-girth decomposition of `H ⊔ L`.
-/
def HasHighGirthAbsorptionProperty {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V) : Prop :=
  (∀ u ∈ X, ∀ v ∈ X, u ≠ v → ¬ H.Adj u v) ∧
    ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
      GraphSupportedOn L (X : Set V) → TriangleDivisible L →
      ∃ C : TripleSystemOn V,
        IsHighGirthTriangleDecomposition q (H ⊔ L) C

/-- Polynomial-size existence assertion corresponding to property (A1) of
the efficient absorber theorem.  Property (A2), the localization statement
for the union of all absorber decompositions, is kept separate because it is
used as a well-spreadness input rather than for absorption itself. -/
def PolynomialHighGirthAbsorbers : Prop :=
  ∃ C_A : ℕ, ∀ q : ℕ, ∃ M_A : ℕ, ∀ m : ℕ, 1 ≤ m →
    ∃ N : ℕ, ∃ H : SimpleGraph (Fin N), ∃ X : Finset (Fin N),
      N ≤ M_A * m ^ C_A ∧ X.card = m ∧
        HasHighGirthAbsorptionProperty q H X

end Erdos207

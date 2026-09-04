import ErdosProblems.Erdos59.Core

/-!
# The large-girth reduction and the degree comparison for Erdős problem 59

This file isolates the finite bipartite combinatorics in U2--U3 of
Füredi--Naor--Verstraëte.  A `Bigraph A B` is used rather than a graph on a
tagged sum: this makes the two minimum degrees, and the three breadth-first
layers, explicit in their types.
-/

namespace Erdos59

namespace GirthDegree

open Finset

/-- A finite bipartite graph with named left and right vertex types. -/
structure Bigraph (A B : Type*) where
  Adj : A → B → Prop

namespace Bigraph

variable {A B : Type*}

/-- Edge inclusion for bigraphs on the same two parts. -/
def LE (F G : Bigraph A B) : Prop :=
  ∀ ⦃a b⦄, F.Adj a b → G.Adj a b

/-- The degree of a left vertex. -/
def leftDegree [Fintype B] (G : Bigraph A B) [DecidableRel G.Adj] (a : A) : ℕ :=
  (Finset.univ.filter fun b ↦ G.Adj a b).card

/-- The degree of a right vertex. -/
def rightDegree [Fintype A] (G : Bigraph A B) [DecidableRel G.Adj] (b : B) : ℕ :=
  (Finset.univ.filter fun a ↦ G.Adj a b).card

/-- The usual vertex-distinct formulation of exclusion of a quadrilateral. -/
def NoFourCycle (G : Bigraph A B) : Prop :=
  ∀ ⦃a₀ a₁ b₀ b₁⦄, a₀ ≠ a₁ → b₀ ≠ b₁ →
    G.Adj a₀ b₀ → G.Adj a₁ b₀ → G.Adj a₁ b₁ → G.Adj a₀ b₁ → False

/-- The usual vertex-distinct formulation of exclusion of a hexagon. -/
def NoSixCycle (G : Bigraph A B) : Prop :=
  ∀ ⦃a₀ a₁ a₂ b₀ b₁ b₂⦄,
    a₀ ≠ a₁ → a₁ ≠ a₂ → a₂ ≠ a₀ →
    b₀ ≠ b₁ → b₁ ≠ b₂ → b₂ ≠ b₀ →
    G.Adj a₀ b₀ → G.Adj a₁ b₀ → G.Adj a₁ b₁ →
    G.Adj a₂ b₁ → G.Adj a₂ b₂ → G.Adj a₀ b₂ → False

/-- For a bipartite simple graph, girth at least eight is exactly exclusion
of four- and six-cycles. -/
def GirthAtLeastEight (G : Bigraph A B) : Prop :=
  G.NoFourCycle ∧ G.NoSixCycle

theorem NoFourCycle.mono {F G : Bigraph A B} (hFG : F.LE G) (hG : G.NoFourCycle) :
    F.NoFourCycle := by
  intro a₀ a₁ b₀ b₁ ha hb h₀ h₁ h₂ h₃
  exact hG ha hb (hFG h₀) (hFG h₁) (hFG h₂) (hFG h₃)

theorem NoSixCycle.mono {F G : Bigraph A B} (hFG : F.LE G) (hG : G.NoSixCycle) :
    F.NoSixCycle := by
  intro a₀ a₁ a₂ b₀ b₁ b₂ ha₀ ha₁ ha₂ hb₀ hb₁ hb₂ h₀ h₁ h₂ h₃ h₄ h₅
  exact hG ha₀ ha₁ ha₂ hb₀ hb₁ hb₂
    (hFG h₀) (hFG h₁) (hFG h₂) (hFG h₃) (hFG h₄) (hFG h₅)

theorem GirthAtLeastEight.mono {F G : Bigraph A B} (hFG : F.LE G)
    (hG : G.GirthAtLeastEight) : F.GirthAtLeastEight :=
  ⟨hG.1.mono hFG, hG.2.mono hFG⟩

/-- Exchange the two sides of a bigraph. -/
def swap (G : Bigraph A B) : Bigraph B A where
  Adj b a := G.Adj a b

instance (G : Bigraph A B) [DecidableRel G.Adj] : DecidableRel G.swap.Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (G.Adj _ _))

@[simp] theorem swap_adj (G : Bigraph A B) (a : A) (b : B) :
    G.swap.Adj b a ↔ G.Adj a b := Iff.rfl

@[simp] theorem swap_swap (G : Bigraph A B) : G.swap.swap = G := rfl

theorem NoFourCycle.swap {G : Bigraph A B} (hG : G.NoFourCycle) :
    G.swap.NoFourCycle := by
  intro b₀ b₁ a₀ a₁ hb ha h₀ h₁ h₂ h₃
  exact hG ha hb h₀ h₃ h₂ h₁

theorem NoSixCycle.swap {G : Bigraph A B} (hG : G.NoSixCycle) :
    G.swap.NoSixCycle := by
  intro b₀ b₁ b₂ a₀ a₁ a₂ hb₀ hb₁ hb₂ ha₀ ha₁ ha₂
    h₀ h₁ h₂ h₃ h₄ h₅
  exact hG (Ne.symm ha₂) (Ne.symm ha₁) (Ne.symm ha₀)
    (Ne.symm hb₂) (Ne.symm hb₁) (Ne.symm hb₀) h₀ h₅ h₄ h₃ h₂ h₁

theorem GirthAtLeastEight.swap {G : Bigraph A B} (hG : G.GirthAtLeastEight) :
    G.swap.GirthAtLeastEight := ⟨hG.1.swap, hG.2.swap⟩

section Degrees

variable [Fintype A] [Fintype B]
variable (G : Bigraph A B) [DecidableRel G.Adj]

@[simp] theorem leftDegree_eq_card_filter (a : A) :
    G.leftDegree a = (Finset.univ.filter fun b ↦ G.Adj a b).card := rfl

@[simp] theorem rightDegree_eq_card_filter (b : B) :
    G.rightDegree b = (Finset.univ.filter fun a ↦ G.Adj a b).card := rfl

theorem leftDegree_le_card (a : A) : G.leftDegree a ≤ Fintype.card B := by
  simpa [leftDegree] using
    Finset.card_le_card (Finset.filter_subset (fun b ↦ G.Adj a b) (Finset.univ : Finset B))

theorem rightDegree_le_card (b : B) : G.rightDegree b ≤ Fintype.card A := by
  simpa [rightDegree] using
    Finset.card_le_card (Finset.filter_subset (fun a ↦ G.Adj a b) (Finset.univ : Finset A))

@[simp] theorem swap_leftDegree (b : B) : G.swap.leftDegree b = G.rightDegree b := rfl

@[simp] theorem swap_rightDegree (a : A) : G.swap.rightDegree a = G.leftDegree a := rfl

end Degrees

section LargeGirthReduction

variable [Fintype A] [Fintype B]
variable (G : Bigraph A B) [DecidableRel G.Adj]

/-- The exact output required from the quadrilateral-component forest
selection.  This certificate is deliberately independent of the particular
component representation: the component file only has to provide the chosen
edge relation, inclusion, deletion of all quadrilaterals, and the two local
half-degree estimates. -/
structure QuadrilateralForestCertificate where
  F : Bigraph A B
  decidableAdj : DecidableRel F.Adj
  le_graph : F.LE G
  noFourCycle : F.NoFourCycle
  half_left : ∀ a, G.leftDegree a ≤ 2 * @leftDegree A B _ F decidableAdj a
  half_right : ∀ b, G.rightDegree b ≤ 2 * @rightDegree A B _ F decidableAdj b

/-- FNV U2, with the quadrilateral-component tree selection exposed as its
reusable finite certificate.  Six-cycle freeness passes to the selected
subgraph, while the certificate deletes every four-cycle. -/
theorem exists_largeGirth_halfDegree_subgraph (hG₆ : G.NoSixCycle)
    (C : QuadrilateralForestCertificate G) :
    ∃ (F : Bigraph A B) (inst : DecidableRel F.Adj),
      F.LE G ∧ F.GirthAtLeastEight ∧
      (∀ a, G.leftDegree a ≤ 2 * @leftDegree A B _ F inst a) ∧
      ∀ b, G.rightDegree b ≤ 2 * @rightDegree A B _ F inst b := by
  refine ⟨C.F, C.decidableAdj, C.le_graph, ⟨C.noFourCycle, ?_⟩, C.half_left, C.half_right⟩
  exact hG₆.mono C.le_graph

/-- If the original graph already has no quadrilateral, U2 chooses every
edge.  This is also a useful base case for componentwise constructions. -/
def identityForestCertificate (hG₄ : G.NoFourCycle) :
    QuadrilateralForestCertificate G where
  F := G
  decidableAdj := inferInstance
  le_graph := by intro a b h; exact h
  noFourCycle := hG₄
  half_left := by intro a; omega
  half_right := by intro b; omega

end LargeGirthReduction

section BreadthFirst

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (F : Bigraph A B) [DecidableRel F.Adj]

/-- Non-backtracking length-three paths starting at a left vertex.  The
coordinates are `(first right vertex, middle left vertex, endpoint)`. -/
def leftThreePaths (x : A) : Finset (B × A × B) :=
  Finset.univ.filter fun p ↦
    F.Adj x p.1 ∧ p.2.1 ≠ x ∧ F.Adj p.2.1 p.1 ∧
      p.2.2 ≠ p.1 ∧ F.Adj p.2.1 p.2.2

@[simp] theorem mem_leftThreePaths {x : A} {p : B × A × B} :
    p ∈ F.leftThreePaths x ↔
      F.Adj x p.1 ∧ p.2.1 ≠ x ∧ F.Adj p.2.1 p.1 ∧
        p.2.2 ≠ p.1 ∧ F.Adj p.2.1 p.2.2 := by
  simp [leftThreePaths]

/-- In girth at least eight, two non-backtracking three-paths from the same
root cannot have the same endpoint.  The three cases in the proof close a
quadrilateral, another quadrilateral, or a hexagon. -/
theorem leftThreePath_endpoint_injOn (hF : F.GirthAtLeastEight) (x : A) :
    Set.InjOn (fun p : B × A × B ↦ p.2.2) (F.leftThreePaths x : Set (B × A × B)) := by
  rintro ⟨b, a, c⟩ hp ⟨b', a', c'⟩ hp' hc
  change (b, a, c) ∈ F.leftThreePaths x at hp
  change (b', a', c') ∈ F.leftThreePaths x at hp'
  rw [mem_leftThreePaths] at hp hp'
  rcases hp with ⟨hxb, hax, hab, hcb, hac⟩
  rcases hp' with ⟨hxb', ha'x, ha'b', hc'b', ha'c'⟩
  dsimp only at hc
  subst c'
  by_cases haa' : a = a'
  · subst a'
    have hbb' : b = b' := by
      by_contra hne
      exact hF.1 hax.symm hne hxb hab ha'b' hxb'
    subst b'
    rfl
  · have hbb' : b = b' := by
      by_contra hne
      exfalso
      exact hF.2 hax.symm haa' ha'x (Ne.symm hcb) hc'b' (Ne.symm hne)
        hxb hab hac ha'c' ha'b' hxb'
    subst b'
    exfalso
    exact hF.1 haa' (Ne.symm hcb) hab ha'b' ha'c' hac

/-- The third breadth-first layer from a left root injects into the right
part. -/
theorem card_leftThreePaths_le (hF : F.GirthAtLeastEight) (x : A) :
    (F.leftThreePaths x).card ≤ Fintype.card B := by
  simpa using Finset.card_le_card_of_injOn (fun p : B × A × B ↦ p.2.2)
    (s := F.leftThreePaths x) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _) (F.leftThreePath_endpoint_injOn hF x)

/-- First BFS layer from a left root. -/
def leftFirst (x : A) : Finset B :=
  Finset.univ.filter fun b ↦ F.Adj x b

/-- Children of `b` in the second BFS layer, with the parent deleted. -/
def leftSecond (x : A) (b : B) : Finset A :=
  Finset.univ.filter fun a ↦ a ≠ x ∧ F.Adj a b

/-- Children of `a` in the third BFS layer, with the parent deleted. -/
def leftThird (b : B) (a : A) : Finset B :=
  Finset.univ.filter fun c ↦ c ≠ b ∧ F.Adj a c

/-- The dependent finset of non-backtracking three-paths from `x`. -/
def leftPathSigma (x : A) : Finset (Σ _ : B, Σ _ : A, B) :=
  (F.leftFirst x).sigma fun b ↦
    (F.leftSecond x b).sigma fun a ↦ F.leftThird b a

/-- Forget the dependent packaging of a three-path. -/
def flattenLeftPath : (Σ _ : B, Σ _ : A, B) ↪ (B × A × B) where
  toFun p := (p.1, p.2.1, p.2.2)
  inj' := by
    rintro ⟨b, a, c⟩ ⟨b', a', c'⟩ h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    rfl

theorem card_leftPathSigma_le_leftThreePaths (x : A) :
    (F.leftPathSigma x).card ≤ (F.leftThreePaths x).card := by
  apply Finset.card_le_card_of_injOn (flattenLeftPath (A := A) (B := B))
  · rintro ⟨b, a, c⟩ hp
    change (⟨b, ⟨a, c⟩⟩ : Σ _ : B, Σ _ : A, B) ∈ F.leftPathSigma x at hp
    rw [leftPathSigma, Finset.mem_sigma, Finset.mem_sigma] at hp
    rcases hp with ⟨hb, ha, hc⟩
    simp only [leftFirst, leftSecond, leftThird, Finset.mem_filter,
      Finset.mem_univ, true_and] at hb ha hc
    change (b, a, c) ∈ F.leftThreePaths x
    rw [mem_leftThreePaths]
    exact ⟨hb, ha.1, ha.2, hc.1, hc.2⟩
  · intro p _ q _ hpq
    exact (flattenLeftPath (A := A) (B := B)).injective hpq

/-- Quantitative BFS expansion.  If the first layer has at least `d₀`
vertices, every second-layer fibre has at least `d₁` children, and every
third-layer fibre has at least `d₂` children, then there are at least the
product many non-backtracking three-paths. -/
theorem mul_le_card_leftPathSigma (x : A) (d₀ d₁ d₂ : ℕ)
    (h₀ : d₀ ≤ F.leftDegree x)
    (h₁ : ∀ ⦃b⦄, F.Adj x b → d₁ + 1 ≤ F.rightDegree b)
    (h₂ : ∀ ⦃b a⦄, F.Adj x b → a ≠ x → F.Adj a b →
      d₂ + 1 ≤ F.leftDegree a) :
    d₀ * d₁ * d₂ ≤ (F.leftPathSigma x).card := by
  have hfirst : d₀ ≤ (F.leftFirst x).card := by
    simpa [leftFirst, leftDegree] using h₀
  have hsecond : ∀ b ∈ F.leftFirst x, d₁ ≤ (F.leftSecond x b).card := by
    intro b hb
    have hadj : F.Adj x b := by simpa [leftFirst] using hb
    have hxmem : x ∈ (Finset.univ.filter fun a ↦ F.Adj a b) := by simp [hadj]
    have heq : F.leftSecond x b = (Finset.univ.filter fun a ↦ F.Adj a b).erase x := by
      ext a
      simp [leftSecond, and_left_comm, eq_comm]
    rw [heq, Finset.card_erase_of_mem hxmem]
    simpa [rightDegree] using Nat.sub_le_sub_right (h₁ hadj) 1
  have hthird : ∀ b ∈ F.leftFirst x, ∀ a ∈ F.leftSecond x b,
      d₂ ≤ (F.leftThird b a).card := by
    intro b hb a ha
    have hadj : F.Adj x b := by simpa [leftFirst] using hb
    have hha : a ≠ x ∧ F.Adj a b := by simpa [leftSecond] using ha
    have hax : a ≠ x := hha.1
    have hab : F.Adj a b := hha.2
    have hbmem : b ∈ (Finset.univ.filter fun c ↦ F.Adj a c) := by simp [hab]
    have heq : F.leftThird b a = (Finset.univ.filter fun c ↦ F.Adj a c).erase b := by
      ext c
      simp [leftThird, and_left_comm, eq_comm]
    rw [heq, Finset.card_erase_of_mem hbmem]
    simpa [leftDegree] using Nat.sub_le_sub_right (h₂ hadj hax hab) 1
  rw [leftPathSigma, Finset.card_sigma]
  calc
    d₀ * d₁ * d₂ = d₀ * (d₁ * d₂) := Nat.mul_assoc _ _ _
    _ ≤ (F.leftFirst x).card * (d₁ * d₂) :=
      Nat.mul_le_mul_right (d₁ * d₂) hfirst
    _ = ∑ b ∈ F.leftFirst x, d₁ * d₂ := by simp
    _ ≤ ∑ b ∈ F.leftFirst x, (F.leftSecond x b).card * d₂ := by
      gcongr with b hb
      exact hsecond b hb
    _ = ∑ b ∈ F.leftFirst x, ∑ a ∈ F.leftSecond x b, d₂ := by
      apply Finset.sum_congr rfl
      intro b _
      simp
    _ ≤ ∑ b ∈ F.leftFirst x, ∑ a ∈ F.leftSecond x b,
        (F.leftThird b a).card := by
      gcongr with b hb a ha
      exact hthird b hb a ha
    _ = ∑ b ∈ F.leftFirst x,
        ((F.leftSecond x b).sigma fun a ↦ F.leftThird b a).card := by
      simp only [Finset.card_sigma]

/-- The left-root form of the FNV breadth-first estimate. -/
theorem left_bfs_layer_bound (hF : F.GirthAtLeastEight) (x : A) (d₀ d₁ d₂ : ℕ)
    (h₀ : d₀ ≤ F.leftDegree x)
    (h₁ : ∀ ⦃b⦄, F.Adj x b → d₁ + 1 ≤ F.rightDegree b)
    (h₂ : ∀ ⦃b a⦄, F.Adj x b → a ≠ x → F.Adj a b →
      d₂ + 1 ≤ F.leftDegree a) :
    d₀ * d₁ * d₂ ≤ Fintype.card B :=
  (F.mul_le_card_leftPathSigma x d₀ d₁ d₂ h₀ h₁ h₂).trans
    ((F.card_leftPathSigma_le_leftThreePaths x).trans (F.card_leftThreePaths_le hF x))

/-- The symmetric, right-root form of the breadth-first estimate. -/
theorem right_bfs_layer_bound (hF : F.GirthAtLeastEight) (x : B) (d₀ d₁ d₂ : ℕ)
    (h₀ : d₀ ≤ F.rightDegree x)
    (h₁ : ∀ ⦃a⦄, F.Adj a x → d₁ + 1 ≤ F.leftDegree a)
    (h₂ : ∀ ⦃a b⦄, F.Adj a x → b ≠ x → F.Adj a b →
      d₂ + 1 ≤ F.rightDegree b) :
    d₀ * d₁ * d₂ ≤ Fintype.card A := by
  exact F.swap.left_bfs_layer_bound hF.swap x d₀ d₁ d₂ h₀ h₁ h₂

end BreadthFirst

section DegreeComparison

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

private lemma ceil_half_le_of_le_two_mul {x y : ℕ} (h : x ≤ 2 * y) :
    (x + 1) / 2 ≤ y := by omega

private lemma shifted_half_le_of_le_two_mul {x y : ℕ} (h : x ≤ 2 * y)
    (hy : 1 ≤ y) : (x - 1) / 2 + 1 ≤ y := by omega

/-- FNV U3 for a bipartite graph, stated with the U2 subgraph explicit.
`F` has girth at least eight and retains at least half of every degree of
`G`.  The maximum-degree witness may lie in either part. -/
theorem bipartite_degree_comparison (G F : Bigraph A B)
    [DecidableRel G.Adj] [DecidableRel F.Adj]
    (hF : F.GirthAtLeastEight)
    (hhalfLeft : ∀ a, G.leftDegree a ≤ 2 * F.leftDegree a)
    (hhalfRight : ∀ b, G.rightDegree b ≤ 2 * F.rightDegree b)
    (deltaA deltaB Delta : ℕ)
    (hdeltaA : ∀ a, deltaA ≤ G.leftDegree a)
    (hdeltaB : ∀ b, deltaB ≤ G.rightDegree b)
    (hmax : (∃ a, G.leftDegree a = Delta) ∨ (∃ b, G.rightDegree b = Delta)) :
    Delta * (deltaA - 2) * (deltaB - 2) ≤
      8 * max (Fintype.card A) (Fintype.card B) := by
  let d₀ := (Delta + 1) / 2
  let dA := (deltaA - 1) / 2
  let dB := (deltaB - 1) / 2
  have hs₀ : Delta ≤ 2 * d₀ := by
    dsimp [d₀]
    omega
  have hsA : deltaA - 2 ≤ 2 * dA := by
    dsimp [dA]
    omega
  have hsB : deltaB - 2 ≤ 2 * dB := by
    dsimp [dB]
    omega
  rcases hmax with ⟨a, ha⟩ | ⟨b, hb⟩
  · have hroot : d₀ ≤ F.leftDegree a := by
      have hh := hhalfLeft a
      rw [ha] at hh
      simpa [d₀] using ceil_half_le_of_le_two_mul hh
    have hright : ∀ ⦃b⦄, F.Adj a b → dB + 1 ≤ F.rightDegree b := by
      intro b hab
      have hh : deltaB ≤ 2 * F.rightDegree b := (hdeltaB b).trans (hhalfRight b)
      have hpos : 1 ≤ F.rightDegree b := by
        rw [rightDegree]
        exact Finset.card_pos.mpr ⟨a, by simp [hab]⟩
      simpa [dB] using shifted_half_le_of_le_two_mul hh hpos
    have hleft : ∀ ⦃b a'⦄, F.Adj a b → a' ≠ a → F.Adj a' b →
        dA + 1 ≤ F.leftDegree a' := by
      intro b a' _ _ ha'b
      have hh : deltaA ≤ 2 * F.leftDegree a' := (hdeltaA a').trans (hhalfLeft a')
      have hpos : 1 ≤ F.leftDegree a' := by
        rw [leftDegree]
        exact Finset.card_pos.mpr ⟨b, by simp [ha'b]⟩
      simpa [dA] using shifted_half_le_of_le_two_mul hh hpos
    have hbfs : d₀ * dB * dA ≤ Fintype.card B :=
      F.left_bfs_layer_bound hF a d₀ dB dA hroot hright hleft
    calc
      Delta * (deltaA - 2) * (deltaB - 2) =
          Delta * (deltaB - 2) * (deltaA - 2) := by ac_rfl
      _ ≤ (2 * d₀) * (2 * dB) * (2 * dA) :=
        Nat.mul_le_mul (Nat.mul_le_mul hs₀ hsB) hsA
      _ = 8 * (d₀ * dB * dA) := by ring
      _ ≤ 8 * Fintype.card B := Nat.mul_le_mul_left 8 hbfs
      _ ≤ 8 * max (Fintype.card A) (Fintype.card B) :=
        Nat.mul_le_mul_left 8 (Nat.le_max_right _ _)
  · have hroot : d₀ ≤ F.rightDegree b := by
      have hh := hhalfRight b
      rw [hb] at hh
      simpa [d₀] using ceil_half_le_of_le_two_mul hh
    have hleft : ∀ ⦃a⦄, F.Adj a b → dA + 1 ≤ F.leftDegree a := by
      intro a hab
      have hh : deltaA ≤ 2 * F.leftDegree a := (hdeltaA a).trans (hhalfLeft a)
      have hpos : 1 ≤ F.leftDegree a := by
        rw [leftDegree]
        exact Finset.card_pos.mpr ⟨b, by simp [hab]⟩
      simpa [dA] using shifted_half_le_of_le_two_mul hh hpos
    have hright : ∀ ⦃a b'⦄, F.Adj a b → b' ≠ b → F.Adj a b' →
        dB + 1 ≤ F.rightDegree b' := by
      intro a b' _ _ hab'
      have hh : deltaB ≤ 2 * F.rightDegree b' := (hdeltaB b').trans (hhalfRight b')
      have hpos : 1 ≤ F.rightDegree b' := by
        rw [rightDegree]
        exact Finset.card_pos.mpr ⟨a, by simp [hab']⟩
      simpa [dB] using shifted_half_le_of_le_two_mul hh hpos
    have hbfs : d₀ * dA * dB ≤ Fintype.card A :=
      F.right_bfs_layer_bound hF b d₀ dA dB hroot hleft hright
    calc
      Delta * (deltaA - 2) * (deltaB - 2) ≤
          (2 * d₀) * (2 * dA) * (2 * dB) :=
        Nat.mul_le_mul (Nat.mul_le_mul hs₀ hsA) hsB
      _ = 8 * (d₀ * dA * dB) := by ring
      _ ≤ 8 * Fintype.card A := Nat.mul_le_mul_left 8 hbfs
      _ ≤ 8 * max (Fintype.card A) (Fintype.card B) :=
        Nat.mul_le_mul_left 8 (Nat.le_max_left _ _)

/-- The numerical bridge from a locally balanced bipartition to the general
FNV degree estimate.  Here `H` is the crossing bigraph, `D` is its maximum
degree, and `F` is its U2 large-girth subgraph.  The hypotheses `hDelta` and
`hdelta*` are precisely the degree losses from the locally maximal cut. -/
theorem degree_comparison (H F : Bigraph A B)
    [DecidableRel H.Adj] [DecidableRel F.Adj]
    (hF : F.GirthAtLeastEight)
    (hhalfLeft : ∀ a, H.leftDegree a ≤ 2 * F.leftDegree a)
    (hhalfRight : ∀ b, H.rightDegree b ≤ 2 * F.rightDegree b)
    (n delta Delta D : ℕ)
    (hcard : Fintype.card A + Fintype.card B = n)
    (hdeltaLeft : ∀ a, (delta + 1) / 2 ≤ H.leftDegree a)
    (hdeltaRight : ∀ b, (delta + 1) / 2 ≤ H.rightDegree b)
    (hmax : (∃ a, H.leftDegree a = D) ∨ (∃ b, H.rightDegree b = D))
    (hDelta : Delta ≤ 2 * D) :
    Delta * (delta - 4) ^ 2 ≤ 64 * n := by
  have hU₃ := bipartite_degree_comparison H F hF hhalfLeft hhalfRight
    ((delta + 1) / 2) ((delta + 1) / 2) D hdeltaLeft hdeltaRight hmax
  have hpart : max (Fintype.card A) (Fintype.card B) ≤ n := by
    rw [← hcard]
    apply max_le <;> omega
  have hU₃' : D * (((delta + 1) / 2) - 2) ^ 2 ≤ 8 * n := by
    calc
      D * (((delta + 1) / 2) - 2) ^ 2 =
          D * (((delta + 1) / 2) - 2) * (((delta + 1) / 2) - 2) := by ring
      _ ≤ 8 * max (Fintype.card A) (Fintype.card B) := hU₃
      _ ≤ 8 * n := Nat.mul_le_mul_left 8 hpart
  let d := ((delta + 1) / 2) - 2
  have hscale : delta - 4 ≤ 2 * d := by
    dsimp [d]
    omega
  calc
    Delta * (delta - 4) ^ 2 ≤ (2 * D) * (2 * d) ^ 2 := by
      gcongr
    _ = 8 * (D * d ^ 2) := by ring
    _ ≤ 8 * (8 * n) := Nat.mul_le_mul_left 8 hU₃'
    _ = 64 * n := by ring

end DegreeComparison

end Bigraph

/-! ## A deterministic locally balanced cut -/

section LocallyBalancedCut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Toggle one vertex of a Boolean bipartition. -/
def flipColor (c : V → Bool) (v : V) : V → Bool :=
  fun w ↦ if w = v then !(c w) else c w

private def cutRelSymm (c : V → Bool) : Std.Symm (fun u w ↦ c u ≠ c w) :=
  ⟨fun _ _ ↦ Ne.symm⟩

/-- Edges crossing a Boolean bipartition. -/
def cutEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e ∈ Sym2.fromRel (cutRelSymm c)

@[simp] theorem sym2_mem_cutEdgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (u w : V) :
    s(u, w) ∈ cutEdgeFinset G c ↔ G.Adj u w ∧ c u ≠ c w := by
  simp [cutEdgeFinset, cutRelSymm, SimpleGraph.mem_edgeFinset]

/-- Flipping one vertex toggles precisely its incident edges in the cut. -/
theorem cutEdgeFinset_flipColor (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (v : V) :
    cutEdgeFinset G (flipColor c v) =
      (G.incidenceFinset v \ cutEdgeFinset G c) ∪
        (cutEdgeFinset G c \ G.incidenceFinset v) := by
  ext e
  by_cases he : e ∈ G.edgeFinset
  · induction e using Sym2.inductionOn with | _ u w =>
    have hadj : G.Adj u w := by simpa [SimpleGraph.mem_edgeFinset] using he
    have huw : u ≠ w := G.ne_of_adj hadj
    simp only [sym2_mem_cutEdgeFinset, hadj, true_and, Finset.mem_union,
      Finset.mem_sdiff]
    by_cases hu : u = v
    · subst u
      have hw : w ≠ v := Ne.symm huw
      simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, flipColor,
        hadj, hw]
    · by_cases hw : w = v
      · subst w
        simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, flipColor,
          hadj, hu]
      · simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, flipColor,
          hadj, hu, hw, Ne.symm hu, Ne.symm hw]
  · have hinc : e ∉ G.incidenceFinset v := fun h ↦
      he (G.incidenceFinset_subset v h)
    simp [cutEdgeFinset, he, hinc]

/-- The number of neighbours of `v` lying across the cut. -/
def cutDegree (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (v : V) : ℕ :=
  (G.neighborFinset v |>.filter fun w ↦ c w ≠ c v).card

theorem card_cutEdges_inter_incidence (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (v : V) :
    ((cutEdgeFinset G c) ∩ G.incidenceFinset v).card = cutDegree G c v := by
  let N := (G.neighborFinset v).filter fun w ↦ c w ≠ c v
  have himage : N.map (Sym2.mkEmbedding v) =
      (cutEdgeFinset G c) ∩ G.incidenceFinset v := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.mp he with ⟨w, hw, rfl⟩
      have hw' : G.Adj v w ∧ c w ≠ c v := by simpa [N] using hw
      simp [hw'.1, hw'.2, Ne.symm hw'.2, SimpleGraph.mem_incidenceFinset]
    · intro he
      have hinc : e ∈ G.incidenceFinset v := (Finset.mem_inter.mp he).2
      have hve : v ∈ e := by
        exact ((G.mem_incidenceFinset v e).mp hinc).2
      rcases Sym2.mem_iff_exists.mp hve with ⟨w, rfl⟩
      apply Finset.mem_map.mpr
      refine ⟨w, ?_, rfl⟩
      have hcut := (Finset.mem_inter.mp he).1
      have hh := (sym2_mem_cutEdgeFinset G c v w).mp hcut
      simp [N, hh.1, Ne.symm hh.2]
  rw [← himage, Finset.card_map]
  rfl

/-- A cut is locally balanced when at least half of the edges incident with
each vertex cross it. -/
def IsLocallyBalancedCut (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) : Prop :=
  ∀ v, G.degree v ≤ 2 * cutDegree G c v

/-- Every finite graph has a locally balanced bipartition.  Choose a cut with
the maximum possible number of crossing edges.  If a vertex saw fewer than
half of its incident edges across the cut, flipping it would strictly enlarge
the cut. -/
theorem exists_locallyBalancedCut (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ c : V → Bool, IsLocallyBalancedCut G c := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image (Finset.univ : Finset (V → Bool))
    (fun c ↦ (cutEdgeFinset G c).card) ⟨fun _ ↦ false, Finset.mem_univ _⟩
  refine ⟨c, fun v ↦ ?_⟩
  by_contra hbad
  have hltDegree : 2 * cutDegree G c v < G.degree v := by
    omega
  let C := cutEdgeFinset G c
  let I := G.incidenceFinset v
  have hIC : (C ∩ I).card < (I \ C).card := by
    have hIcard : I.card = G.degree v := by
      simpa [I] using G.card_incidenceFinset_eq_degree v
    have hsplit : (I \ C).card = I.card - (C ∩ I).card := by
      simpa [Finset.inter_comm] using Finset.card_sdiff (s := C) (t := I)
    have hcross : (C ∩ I).card = cutDegree G c v := by
      simpa [C, I] using card_cutEdges_inter_incidence G c v
    omega
  have hCold : C = (C \ I) ∪ (C ∩ I) := by
    ext e
    by_cases he : e ∈ I <;> simp [he]
  have hdisjOld : Disjoint (C \ I) (C ∩ I) := by
    apply Finset.disjoint_left.mpr
    intro e he₀ he₁
    rw [Finset.mem_sdiff] at he₀
    rw [Finset.mem_inter] at he₁
    exact he₀.2 he₁.2
  have hdisjNew : Disjoint (I \ C) (C \ I) := by
    apply Finset.disjoint_left.mpr
    intro e he₀ he₁
    rw [Finset.mem_sdiff] at he₀ he₁
    exact he₀.2 he₁.1
  have hscore : C.card < (cutEdgeFinset G (flipColor c v)).card := by
    have hnew : (cutEdgeFinset G (flipColor c v)).card =
        (I \ C).card + (C \ I).card := by
      rw [cutEdgeFinset_flipColor, show G.incidenceFinset v = I from rfl,
        show cutEdgeFinset G c = C from rfl, Finset.card_union_of_disjoint hdisjNew]
    have hold : C.card = (C \ I).card + (C ∩ I).card := by
      calc
        C.card = ((C \ I) ∪ (C ∩ I)).card := congrArg Finset.card hCold
        _ = _ := Finset.card_union_of_disjoint hdisjOld
    rw [hnew, hold]
    omega
  exact (Nat.not_lt_of_ge (hc (flipColor c v) (Finset.mem_univ _))) hscore

/-- The two vertex types cut out by a Boolean colouring. -/
abbrev CutLeft (c : V → Bool) := {v : V // c v = false}
abbrev CutRight (c : V → Bool) := {v : V // c v = true}

/-- The crossing edges of a cut, regarded as a bigraph. -/
def crossingBigraph (G : SimpleGraph V) (c : V → Bool) :
    Bigraph (CutLeft c) (CutRight c) where
  Adj a b := G.Adj a.1 b.1

instance (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    DecidableRel (crossingBigraph G c).Adj :=
  fun a b ↦ inferInstanceAs (Decidable (G.Adj a.1 b.1))

theorem crossingBigraph_leftDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (a : CutLeft c) :
    (crossingBigraph G c).leftDegree a = cutDegree G c a.1 := by
  let S := Finset.univ.filter fun b : CutRight c ↦ G.Adj a.1 b.1
  have himage : S.map (Function.Embedding.subtype _) =
      (G.neighborFinset a.1).filter fun w ↦ c w ≠ c a.1 := by
    ext w
    simp [S, a.2, SimpleGraph.mem_neighborFinset]
  unfold Bigraph.leftDegree cutDegree
  change S.card = _
  calc
    S.card = (S.map (Function.Embedding.subtype _)).card := by simp
    _ = _ := by rw [himage]

theorem crossingBigraph_rightDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (b : CutRight c) :
    (crossingBigraph G c).rightDegree b = cutDegree G c b.1 := by
  let S := Finset.univ.filter fun a : CutLeft c ↦ G.Adj a.1 b.1
  have himage : S.map (Function.Embedding.subtype _) =
      (G.neighborFinset b.1).filter fun w ↦ c w ≠ c b.1 := by
    ext w
    simp [S, b.2, SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
  unfold Bigraph.rightDegree cutDegree
  change S.card = _
  calc
    S.card = (S.map (Function.Embedding.subtype _)).card := by simp
    _ = _ := by rw [himage]

theorem card_cut_parts (c : V → Bool) :
    Fintype.card (CutLeft c) + Fintype.card (CutRight c) = Fintype.card V := by
  simpa using Fintype.card_congr (Equiv.sumCompl fun v : V ↦ c v = false)

/-- A standard `cycleGraph 6` freeness hypothesis passes to every crossing
bigraph of a Boolean cut. -/
theorem crossingBigraph_noSixCycle_of_free (G : SimpleGraph V)
    (hG : (SimpleGraph.cycleGraph 6).Free G) (c : V → Bool) :
    (crossingBigraph G c).NoSixCycle := by
  intro a₀ a₁ a₂ b₀ b₁ b₂ ha₀ ha₁ ha₂ hb₀ hb₁ hb₂
    h₀ h₁ h₂ h₃ h₄ h₅
  have hfree := (cycleGraph_six_free_iff_forall_not_isC6 G).mp hG
  apply hfree ![a₀.1, b₀.1, a₁.1, b₁.1, a₂.1, b₂.1]
  constructor
  · have hcross : ∀ (a : CutLeft c) (b : CutRight c), a.1 ≠ b.1 := by
      intro a b hab
      have hc := congrArg c hab
      simp [a.2, b.2] at hc
    have ha₀' : a₀.1 ≠ a₁.1 := fun h ↦ ha₀ (Subtype.ext h)
    have ha₁' : a₁.1 ≠ a₂.1 := fun h ↦ ha₁ (Subtype.ext h)
    have ha₂' : a₂.1 ≠ a₀.1 := fun h ↦ ha₂ (Subtype.ext h)
    have hb₀' : b₀.1 ≠ b₁.1 := fun h ↦ hb₀ (Subtype.ext h)
    have hb₁' : b₁.1 ≠ b₂.1 := fun h ↦ hb₁ (Subtype.ext h)
    have hb₂' : b₂.1 ≠ b₀.1 := fun h ↦ hb₂ (Subtype.ext h)
    have hx₀₀ := hcross a₀ b₀
    have hx₀₁ := hcross a₀ b₁
    have hx₀₂ := hcross a₀ b₂
    have hx₁₀ := hcross a₁ b₀
    have hx₁₁ := hcross a₁ b₁
    have hx₁₂ := hcross a₁ b₂
    have hx₂₀ := hcross a₂ b₀
    have hx₂₁ := hcross a₂ b₁
    have hx₂₂ := hcross a₂ b₂
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · simpa [crossingBigraph] using h₀
    · simpa [crossingBigraph] using h₁.symm
    · simpa [crossingBigraph] using h₂
    · simpa [crossingBigraph] using h₃.symm
    · simpa [crossingBigraph] using h₄
    · simpa [crossingBigraph] using h₅.symm

/-- The general constant-64 comparison, assembled from the deterministic
locally balanced cut and U2 on its crossing bigraph.  `hSix` is the direct
typed form of the fact that C6-freeness passes to a spanning subgraph; the
quadrilateral-component development supplies `hforest`. -/
theorem general_degree_comparison_of_u2 (G : SimpleGraph V) [DecidableRel G.Adj]
    (delta Delta : ℕ)
    (hmin : ∀ v, delta ≤ G.degree v)
    (hmax : ∃ v, G.degree v = Delta)
    (hSix : ∀ c : V → Bool, (crossingBigraph G c).NoSixCycle)
    (hforest : ∀ (c : V → Bool), IsLocallyBalancedCut G c →
      Bigraph.QuadrilateralForestCertificate (crossingBigraph G c)) :
    Delta * (delta - 4) ^ 2 ≤ 64 * Fintype.card V := by
  classical
  obtain ⟨c, hc⟩ := exists_locallyBalancedCut G
  let H := crossingBigraph G c
  obtain ⟨vmax, hvmax⟩ := hmax
  obtain ⟨vD, _, hvD⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    (cutDegree G c) ⟨vmax, Finset.mem_univ _⟩
  let D := cutDegree G c vD
  have hmaxH : (∃ a, H.leftDegree a = D) ∨ (∃ b, H.rightDegree b = D) := by
    cases hcolor : c vD with
    | false =>
        left
        refine ⟨⟨vD, hcolor⟩, ?_⟩
        exact crossingBigraph_leftDegree G c ⟨vD, hcolor⟩
    | true =>
        right
        refine ⟨⟨vD, hcolor⟩, ?_⟩
        exact crossingBigraph_rightDegree G c ⟨vD, hcolor⟩
  have hdeltaLeft : ∀ a, (delta + 1) / 2 ≤ H.leftDegree a := by
    intro a
    have h₀ := hmin a.1
    have h₁ := hc a.1
    rw [crossingBigraph_leftDegree]
    omega
  have hdeltaRight : ∀ b, (delta + 1) / 2 ≤ H.rightDegree b := by
    intro b
    have h₀ := hmin b.1
    have h₁ := hc b.1
    rw [crossingBigraph_rightDegree]
    omega
  have hDelta : Delta ≤ 2 * D := by
    have h₀ := hc vmax
    have h₁ := hvD vmax (Finset.mem_univ _)
    rw [hvmax] at h₀
    dsimp [D]
    omega
  let C := hforest c hc
  let : DecidableRel C.F.Adj := C.decidableAdj
  have hFgirth : C.F.GirthAtLeastEight :=
    ⟨C.noFourCycle, (hSix c).mono C.le_graph⟩
  exact Bigraph.degree_comparison H C.F hFgirth C.half_left C.half_right
    (Fintype.card V) delta Delta D (card_cut_parts c) hdeltaLeft hdeltaRight hmaxH hDelta

/-- The deterministic-bipartition form of the general FNV degree comparison,
with standard Mathlib `cycleGraph 6` freeness.  The remaining argument is the
concrete U2 forest selector for each crossing bigraph. -/
theorem degree_comparison (G : SimpleGraph V) [DecidableRel G.Adj]
    (delta Delta : ℕ)
    (hmin : ∀ v, delta ≤ G.degree v)
    (hmax : ∃ v, G.degree v = Delta)
    (hfree : (SimpleGraph.cycleGraph 6).Free G)
    (hforest : ∀ (c : V → Bool), IsLocallyBalancedCut G c →
      Bigraph.QuadrilateralForestCertificate (crossingBigraph G c)) :
    Delta * (delta - 4) ^ 2 ≤ 64 * Fintype.card V := by
  apply general_degree_comparison_of_u2 G delta Delta hmin hmax
  · exact fun c ↦ crossingBigraph_noSixCycle_of_free G hfree c
  · exact hforest

end LocallyBalancedCut

end GirthDegree

end Erdos59

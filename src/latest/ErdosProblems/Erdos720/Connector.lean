import ErdosProblems.Erdos720.Fan

namespace Erdos720

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

open ExtendableState

/-- The three internally separated path systems furnished by two binary fans
joined by a central path. -/
structure RobustConnector (G : SimpleGraph V) (height q : ℕ) where
  leftLeaves : Finset V
  rightLeaves : Finset V
  rootLeft : V
  rootRight : V
  core : Finset V
  leftBase : Finset V
  support : Finset V
  core_subset_leftBase : core ⊆ leftBase
  leftBase_subset_support : leftBase ⊆ support
  card_left : leftLeaves.card = 2 ^ height
  card_right : rightLeaves.card = 2 ^ height
  leftLeaves_subset : leftLeaves ⊆ leftBase
  rightLeaves_subset : rightLeaves ⊆ support
  disjoint_leaves : Disjoint leftLeaves rightLeaves
  centerPath : ExactPathIn G core {rootLeft} rootLeft q rootRight
  leftPaths : ∀ ⦃a⦄, a ∈ leftLeaves →
    ExactPathIn G leftBase core rootLeft height a
  rightPaths : ∀ ⦃b⦄, b ∈ rightLeaves →
    ExactPathIn G support leftBase rootRight height b

lemma robust_connector (G : SimpleGraph V) (M height q : ℕ) (root : V)
    (hM : 1 ≤ M) (hh : 0 < height) (hq : 0 < q)
    (hcap : 1 + q + 2 * (2 ^ (height + 1) - 2) ≤ M)
    (hexp : ∀ X : Finset V, X.card ≤ 2 * M →
      4 * X.card ≤ (setNeighbors G X).card) :
    Nonempty (RobustConnector G height q) := by
  classical
  obtain ⟨S₀, hS₀used, hS₀deg⟩ :=
    ExtendableState.singleton_state (G := G) root hM hexp
  have hpathCap : S₀.used.card + q ≤ M := by
    rw [hS₀used]
    simp
    omega
  have hrootUsed : root ∈ S₀.used := by simp [hS₀used]
  have hrootDeg : S₀.deg root ≤ 1 := by rw [hS₀deg]; simp
  obtain ⟨S₁, ⟨P⟩⟩ := ExtendableState.extend_path hexp hM S₀ root q
    hpathCap hrootUsed hrootDeg
  have hrootRightNe : P.endpoint ≠ root := by
    intro heq
    have hold : P.endpoint ∈ S₀.used := heq.symm ▸ hrootUsed
    exact (Nat.ne_of_gt hq) (P.endpoint_old hold).1
  have hrootDeg₁ : S₁.deg root ≤ 1 := by
    rw [P.root_deg, hS₀deg]
    simp [hq]
  have hleftCap : S₁.used.card + (2 ^ (height + 1) - 2) ≤ M := by
    rw [P.used_card, hS₀used]
    simp
    omega
  have hrootS₁ : root ∈ S₁.used := P.used_mono hrootUsed
  obtain ⟨S₂, ⟨L⟩⟩ := ExtendableState.binary_fan hexp hM S₁ root height
    hleftCap hrootS₁ hrootDeg₁
  have hrightCap : S₂.used.card + (2 ^ (height + 1) - 2) ≤ M := by
    rw [L.used_card, P.used_card, hS₀used]
    simp
    omega
  have hrightS₁ : P.endpoint ∈ S₁.used := P.endpoint_used
  have hrightS₂ : P.endpoint ∈ S₂.used := L.used_mono hrightS₁
  have hrightDeg₂ : S₂.deg P.endpoint ≤ 1 := by
    rw [L.preserve hrightS₁ hrootRightNe]
    exact P.endpoint_deg
  obtain ⟨S₃, ⟨R⟩⟩ := ExtendableState.binary_fan hexp hM S₂ P.endpoint height
    hrightCap hrightS₂ hrightDeg₂
  have hS₁S₂ : S₁.used ⊆ S₂.used := L.used_mono
  have hS₂S₃ : S₂.used ⊆ S₃.used := R.used_mono
  have hS₁S₃ : S₁.used ⊆ S₃.used := fun _ hv => hS₂S₃ (hS₁S₂ hv)
  have hLsubS₃ : L.leaves ⊆ S₃.used := fun _ hv => hS₂S₃ (L.leaves_used hv)
  have hdisj : Disjoint L.leaves R.leaves := by
    rw [Finset.disjoint_left]
    intro a haL haR
    have haS₂ : a ∈ S₂.used := L.leaves_used haL
    exact (Nat.ne_of_gt hh) (R.leaf_old haR haS₂).1
  refine ⟨{
    leftLeaves := L.leaves
    rightLeaves := R.leaves
    rootLeft := root
    rootRight := P.endpoint
    core := S₁.used
    leftBase := S₂.used
    support := S₃.used
    core_subset_leftBase := hS₁S₂
    leftBase_subset_support := hS₂S₃
    card_left := L.card_leaves
    card_right := R.card_leaves
    leftLeaves_subset := L.leaves_used
    rightLeaves_subset := R.leaves_used
    disjoint_leaves := hdisj
    centerPath := by simpa [hS₀used] using P.path
    leftPaths := fun _ ha => L.paths ha
    rightPaths := fun _ hb => R.paths hb }⟩

end Erdos720

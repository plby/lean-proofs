/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Syndetic
import ErdosProblems.Erdos254.TailSubgroup

namespace Erdos254

open Filter Set
open scoped BigOperators Topology

/-- The finite-support, thick-interval step in Fan's Lemma 2.2. -/
lemma thick_subsetSums_of_finite_cover {G : Type*} [AddCommGroup G]
    {B : Set ℕ} (E : Finset ℕ) (hBE : Disjoint B (E : Set ℕ))
    (θ : G) (U : Set G) (J : Set ℕ) (hJ : IsThick J)
    (hB : ∀ n ∈ J, n • θ ∈ U → IsSumOfDistinct B n)
    (hcover : ∀ n : ℕ, ∃ F ⊆ E, n • θ - (∑ a ∈ F, a) • θ ∈ U) :
    IsThick (subsetSums (B ∪ (E : Set ℕ))) := by
  intro L
  obtain ⟨a, ha⟩ := hJ (L + ∑ e ∈ E, e)
  refine ⟨a + ∑ e ∈ E, e, ?_⟩
  intro k hk
  obtain ⟨F, hF, hFU⟩ := hcover (a + (∑ e ∈ E, e) + k)
  let d := ∑ x ∈ F, x
  have hdE : d ≤ ∑ e ∈ E, e := Finset.sum_le_sum_of_subset hF
  have hd : d ≤ a + (∑ e ∈ E, e) + k := by omega
  have hJmem : a + (∑ e ∈ E, e) + k - d ∈ J := by
    have hlen : (∑ e ∈ E, e) + k - d ≤ L + ∑ e ∈ E, e := by omega
    have heq : a + ((∑ e ∈ E, e) + k - d) = a + (∑ e ∈ E, e) + k - d := by omega
    simpa only [heq] using ha ((∑ e ∈ E, e) + k - d) hlen
  have hphase : (a + (∑ e ∈ E, e) + k - d) • θ ∈ U := by
    have heq := congrArg (fun n : ℕ ↦ n • θ) (Nat.sub_add_cancel hd)
    rw [add_nsmul] at heq
    rw [eq_sub_iff_add_eq.mpr heq]
    exact hFU
  have hsumB := hB _ hJmem hphase
  have hsumE : IsSumOfDistinct (E : Set ℕ) d := ⟨F, hF, rfl⟩
  have hsum := hsumB.add hBE hsumE
  simpa only [subsetSums, Set.mem_ofPred_eq, Nat.sub_add_cancel hd] using hsum

/-- Compactness extracts finitely many subset-sum supports from the orbit cover.
The substantive group-theoretic input is that `θ` belongs to the tail subgroup. -/
lemma finite_orbit_cover {G : Type*} [NormedAddCommGroup G] [CompactSpace G]
    (A : Set ℕ) (θ : G) (U : Set G) (hU : IsOpen U)
    (hne : ∃ n : ℕ, n • θ ∈ U)
    (hθ : θ ∈ tailSubgroup A (fun n ↦ n • θ)) :
    ∃ E : Finset ℕ, (E : Set ℕ) ⊆ A ∧
      ∀ n : ℕ, ∃ F ⊆ E, n • θ - (∑ a ∈ F, a) • θ ∈ U := by
  classical
  let H := tailSubgroup A (fun n ↦ n • θ)
  let I := {F : Finset ℕ // (F : Set ℕ) ⊆ A}
  let O : I → Set G := fun F ↦ {x | x - (∑ a ∈ F.1, a) • θ ∈ U}
  have hopen : ∀ F, IsOpen (O F) := fun _ ↦ hU.preimage (continuous_id.sub continuous_const)
  have hcover : (H : Set G) ⊆ ⋃ F, O F := by
    intro x hx
    obtain ⟨n₀, hn₀⟩ := hne
    have huH : n₀ • θ ∈ H := H.nsmul_mem hθ n₀
    have hsub : x - n₀ • θ ∈ tailLimitSet A (fun n ↦ n • θ) := H.sub_mem hx huH
    have hcl := Set.mem_iInter.mp hsub 0
    let V : Set G := {y | x - y ∈ U}
    have hV : IsOpen V := hU.preimage (continuous_const.sub continuous_id)
    have hv : x - n₀ • θ ∈ V := by simpa [V] using hn₀
    obtain ⟨y, hyV, F, hF, rfl⟩ := mem_closure_iff.mp hcl V hV hv
    refine Set.mem_iUnion.mpr ⟨⟨F, fun a ha ↦ (hF a ha).1⟩, ?_⟩
    change x - (∑ a ∈ F, a) • θ ∈ U
    simpa only [V, Set.mem_ofPred_eq, Finset.sum_nsmul_assoc] using hyV
  have hcompact : IsCompact (H : Set G) := (isClosed_tailLimitSet A (fun n ↦ n • θ)).isCompact
  obtain ⟨T, hT⟩ := hcompact.elim_finite_subcover O hopen hcover
  let E := T.biUnion (fun F ↦ F.1)
  refine ⟨E, ?_, ?_⟩
  · intro a ha
    obtain ⟨F, _, haF⟩ := Finset.mem_biUnion.mp ha
    exact F.2 haF
  · intro n
    obtain ⟨F, hFT, hnF⟩ := Set.mem_iUnion₂.mp (hT (H.nsmul_mem hθ n))
    refine ⟨F.1, ?_, hnF⟩
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨F, hFT, ha⟩

end Erdos254

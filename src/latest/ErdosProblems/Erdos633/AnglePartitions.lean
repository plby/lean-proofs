import ErdosProblems.Erdos633.AngleCounting
import Mathlib.Data.Finset.Sort

/-!
# The finite outer-corner partition problem

The local angle obstruction bounds each surviving column total by three.
This file classifies the remaining three nonempty, distinct coefficient rows.
All finite enumeration is checked by ordinary kernel proofs at default limits.
-/

namespace Erdos633

open scoped BigOperators

theorem sum_three_permuted {α : Type*} [AddCommMonoid α]
    (f : Fin 3 → α) (e : Equiv.Perm (Fin 3)) :
    f (e 0) + f (e 1) + f (e 2) = ∑ j, f j := by
  have h := Equiv.sum_comp e f
  norm_num [Fin.sum_univ_succ] at h ⊢
  simpa only [← add_assoc] using h

/-- Equality of ordered triples after a permutation of their positions. -/
def PermutedTriple {α : Type*} (f g : Fin 3 → α) : Prop :=
  ∃ e : Equiv.Perm (Fin 3), ∀ j, f (e j) = g j

theorem PermutedTriple.refl {α : Type*} (f : Fin 3 → α) : PermutedTriple f f :=
  ⟨Equiv.refl _, fun _ => rfl⟩

theorem PermutedTriple.symm {α : Type*} {f g : Fin 3 → α}
    (h : PermutedTriple f g) : PermutedTriple g f := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  intro j
  simpa using (he (e.symm j)).symm

theorem PermutedTriple.trans {α : Type*} {f g h : Fin 3 → α}
    (hfg : PermutedTriple f g) (hgh : PermutedTriple g h) : PermutedTriple f h := by
  obtain ⟨e, he⟩ := hfg
  obtain ⟨d, hd⟩ := hgh
  exact ⟨d.trans e, fun j => (he (d j)).trans (hd j)⟩

theorem permutedTriple_of_at {α : Type*} {f : Fin 3 → α}
    (e : Equiv.Perm (Fin 3)) {a b c : α}
    (h₀ : f (e 0) = a) (h₁ : f (e 1) = b) (h₂ : f (e 2) = c) :
    PermutedTriple f ![a, b, c] := by
  refine ⟨e, ?_⟩
  intro j
  fin_cases j
  · exact h₀
  · exact h₁
  · exact h₂

theorem PermutedTriple.rotate {α : Type*} {f : Fin 3 → α} {a b c : α}
    (h : PermutedTriple f ![a, b, c]) : PermutedTriple f ![b, c, a] := by
  apply h.trans
  refine ⟨(Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1), ?_⟩
  intro j
  fin_cases j <;> simp [Equiv.swap_apply_def]

theorem PermutedTriple.swap_first {α : Type*} {f : Fin 3 → α} {a b c : α}
    (h : PermutedTriple f ![a, b, c]) : PermutedTriple f ![b, a, c] := by
  apply h.trans
  refine ⟨Equiv.swap (0 : Fin 3) 1, ?_⟩
  intro j
  fin_cases j <;> simp [Equiv.swap_apply_def]

theorem PermutedTriple.swap_last {α : Type*} {f : Fin 3 → α} {a b c : α}
    (h : PermutedTriple f ![a, b, c]) : PermutedTriple f ![a, c, b] := by
  apply h.trans
  refine ⟨Equiv.swap (1 : Fin 3) 2, ?_⟩
  intro j
  fin_cases j <;> simp [Equiv.swap_apply_def]

/-- An injective finite sequence can be increasingly reordered. -/
theorem exists_perm_strictMono_nat {n : ℕ} (f : Fin n → ℕ)
    (hf : Function.Injective f) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (fun i => f (e i)) := by
  classical
  let s := Finset.univ.image f
  have hs : s.card = n := by
    simpa [s] using Finset.card_image_of_injective Finset.univ hf
  have hmem (i : Fin n) : ∃ j : Fin n, f j = s.orderEmbOfFin hs i := by
    have h := s.orderEmbOfFin_mem hs i
    simpa only [s, Finset.mem_image, Finset.mem_univ, true_and] using h
  choose g hg using hmem
  have hginj : Function.Injective g := by
    intro i j hij
    apply (s.orderEmbOfFin hs).injective
    rw [← hg i, ← hg j, hij]
  let e : Equiv.Perm (Fin n) :=
    Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, rfl⟩)
  refine ⟨e, ?_⟩
  intro i j hij
  change f (g i) < f (g j)
  rw [hg i, hg j]
  exact (s.orderEmbOfFin hs).strictMono hij

/-- The seventeen increasing triples of distinct nonzero coefficient pairs
whose two positive column sums are at most three. -/
def SortedCornerPartition (x₀ y₀ x₁ y₁ x₂ y₂ : ℕ) : Prop :=
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 0 ∧ y₁ = 2 ∧ x₂ = 1 ∧ y₂ = 0) ∨
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 1 ∧ y₁ = 0 ∧ x₂ = 1 ∧ y₂ = 1) ∨
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 0 ∧ y₁ = 2 ∧ x₂ = 2 ∧ y₂ = 0) ∨
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 1 ∧ y₁ = 0 ∧ x₂ = 1 ∧ y₂ = 2) ∨
  (x₀ = 0 ∧ y₀ = 2 ∧ x₁ = 1 ∧ y₁ = 0 ∧ x₂ = 1 ∧ y₂ = 1) ∨
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 1 ∧ y₁ = 0 ∧ x₂ = 2 ∧ y₂ = 0) ∨
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 1 ∧ y₁ = 0 ∧ x₂ = 2 ∧ y₂ = 1) ∨
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 1 ∧ y₁ = 1 ∧ x₂ = 2 ∧ y₂ = 0) ∨
  (x₀ = 0 ∧ y₀ = 2 ∧ x₁ = 1 ∧ y₁ = 0 ∧ x₂ = 2 ∧ y₂ = 0) ∨
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 0 ∧ y₁ = 2 ∧ x₂ = 3 ∧ y₂ = 0) ∨
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 1 ∧ y₁ = 0 ∧ x₂ = 2 ∧ y₂ = 2) ∨
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 1 ∧ y₁ = 1 ∧ x₂ = 2 ∧ y₂ = 1) ∨
  (x₀ = 0 ∧ y₀ = 1 ∧ x₁ = 1 ∧ y₁ = 2 ∧ x₂ = 2 ∧ y₂ = 0) ∨
  (x₀ = 0 ∧ y₀ = 2 ∧ x₁ = 1 ∧ y₁ = 0 ∧ x₂ = 2 ∧ y₂ = 1) ∨
  (x₀ = 0 ∧ y₀ = 2 ∧ x₁ = 1 ∧ y₁ = 1 ∧ x₂ = 2 ∧ y₂ = 0) ∨
  (x₀ = 0 ∧ y₀ = 3 ∧ x₁ = 1 ∧ y₁ = 0 ∧ x₂ = 2 ∧ y₂ = 0) ∨
  (x₀ = 1 ∧ y₀ = 0 ∧ x₁ = 1 ∧ y₁ = 1 ∧ x₂ = 1 ∧ y₂ = 2)

theorem sorted_corner_partition_exhaustive (x₀ y₀ x₁ y₁ x₂ y₂ : ℕ)
    (hx : 1 ≤ x₀ + x₁ + x₂ ∧ x₀ + x₁ + x₂ ≤ 3)
    (hy : 1 ≤ y₀ + y₁ + y₂ ∧ y₀ + y₁ + y₂ ≤ 3)
    (h₀ : 0 < x₀ + y₀) (h₁ : 0 < x₁ + y₁) (h₂ : 0 < x₂ + y₂)
    (h₀₁ : 4 * x₀ + y₀ < 4 * x₁ + y₁)
    (h₁₂ : 4 * x₁ + y₁ < 4 * x₂ + y₂) :
    SortedCornerPartition x₀ y₀ x₁ y₁ x₂ y₂ := by
  have hxorder : x₀ ≤ x₁ ∧ x₁ ≤ x₂ := by omega
  have hx₀ : x₀ = 0 ∨ x₀ = 1 := by omega
  rcases hx₀ with rfl | rfl
  · have hy₀ : y₀ = 1 ∨ y₀ = 2 ∨ y₀ = 3 := by omega
    rcases hy₀ with rfl | rfl | rfl
    · have hx₁ : x₁ = 0 ∨ x₁ = 1 := by omega
      rcases hx₁ with rfl | rfl
      · have hy₁ : y₁ = 2 := by omega
        have hy₂ : y₂ = 0 := by omega
        subst y₁ y₂
        norm_num [SortedCornerPartition]
        omega
      · have hx₂ : x₂ = 1 ∨ x₂ = 2 := by omega
        rcases hx₂ with rfl | rfl
        · have hy₁ : y₁ = 0 := by omega
          subst y₁
          norm_num [SortedCornerPartition]
          omega
        · have hy₁ : y₁ = 0 ∨ y₁ = 1 ∨ y₁ = 2 := by omega
          rcases hy₁ with rfl | rfl | rfl <;>
            norm_num [SortedCornerPartition] <;> omega
    · have hx₁ : x₁ = 1 := by omega
      subst x₁
      have hx₂ : x₂ = 1 ∨ x₂ = 2 := by omega
      rcases hx₂ with rfl | rfl <;> norm_num [SortedCornerPartition] <;> omega
    · have hx₁ : x₁ = 1 := by omega
      have hx₂ : x₂ = 2 := by omega
      subst x₁ x₂
      norm_num [SortedCornerPartition]
      omega
  · have hx₁ : x₁ = 1 := by omega
    have hx₂ : x₂ = 1 := by omega
    subst x₁ x₂
    norm_num [SortedCornerPartition]
    omega

theorem corner_partition_up_to_permutation (x y : Fin 3 → ℕ)
    (hx : 1 ≤ ∑ j, x j ∧ ∑ j, x j ≤ 3)
    (hy : 1 ≤ ∑ j, y j ∧ ∑ j, y j ≤ 3)
    (hpos : ∀ j, 0 < x j + y j)
    (hinj : Function.Injective (fun j => (x j, y j))) :
    ∃ e : Equiv.Perm (Fin 3),
      SortedCornerPartition (x (e 0)) (y (e 0)) (x (e 1)) (y (e 1))
        (x (e 2)) (y (e 2)) := by
  have hybound (i : Fin 3) : y i ≤ 3 := by
    have h : y i ≤ ∑ j : Fin 3, y j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (y j)) (Finset.mem_univ i)
    omega
  have hcode : Function.Injective (fun j => 4 * x j + y j) := by
    intro i j hij
    change 4 * x i + y i = 4 * x j + y j at hij
    apply hinj
    have hi := hybound i
    have hj := hybound j
    apply Prod.ext
    · change x i = x j
      omega
    · change y i = y j
      omega
  obtain ⟨e, he⟩ := exists_perm_strictMono_nat (fun j => 4 * x j + y j) hcode
  refine ⟨e, sorted_corner_partition_exhaustive _ _ _ _ _ _ ?_ ?_
    (hpos (e 0)) (hpos (e 1)) (hpos (e 2)) (he (by decide)) (he (by decide))⟩
  · have hs := Equiv.sum_comp e x
    norm_num [Fin.sum_univ_succ] at hs hx ⊢
    omega
  · have hs := Equiv.sum_comp e y
    norm_num [Fin.sum_univ_succ] at hs hy ⊢
    omega

/-- The six exceptional outer-angle families. Permuting the two reference
angles is handled explicitly by the final classification theorem. -/
def ExceptionalAnglePattern (α β : ℝ) (θ : Fin 3 → ℝ) : Prop :=
  (3 * α + 2 * β = Real.pi ∧
    (PermutedTriple θ ![α, 2 * α, 2 * β] ∨
      PermutedTriple θ ![2 * α, β, α + β])) ∨
  (3 * α + 3 * β = Real.pi ∧
    (PermutedTriple θ ![α, α + β, α + 2 * β] ∨
      PermutedTriple θ ![α, 2 * β, 2 * α + β] ∨
      PermutedTriple θ ![2 * α, 2 * β, α + β] ∨
      PermutedTriple θ ![α, 2 * α, 3 * β]))

theorem sorted_angle_partition_classification (α β γ : ℝ) (θ : Fin 3 → ℝ)
    (e : Equiv.Perm (Fin 3)) (x₀ y₀ x₁ y₁ x₂ y₂ : ℕ)
    (hsum : α + β + γ = Real.pi)
    (hout : ((x₀ + x₁ + x₂ : ℕ) : ℝ) * α +
      ((y₀ + y₁ + y₂ : ℕ) : ℝ) * β = Real.pi)
    (h₀ : θ (e 0) = x₀ * α + y₀ * β)
    (h₁ : θ (e 1) = x₁ * α + y₁ * β)
    (h₂ : θ (e 2) = x₂ * α + y₂ * β)
    (hpart : SortedCornerPartition x₀ y₀ x₁ y₁ x₂ y₂) :
    PermutedTriple θ ![α, β, γ] ∨
      ExceptionalAnglePattern α β θ ∨ ExceptionalAnglePattern β α θ := by
  have hp := permutedTriple_of_at e h₀ h₁ h₂
  rcases hpart with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    norm_num at hout hp
  · left
    have hg : γ = 2 * β := by linarith
    simpa only [hg] using hp.rotate.rotate
  · left
    have hg : γ = α + β := by linarith
    simpa only [hg] using hp.swap_first
  · right; right; left
    exact ⟨by linarith, Or.inl hp⟩
  · left
    have hg : γ = α + 2 * β := by linarith
    simpa only [hg] using hp.swap_first
  · right; right; left
    refine ⟨by linarith, Or.inr ?_⟩
    simpa only [add_comm] using hp
  · left
    have hg : γ = 2 * α := by linarith
    simpa only [hg] using hp.swap_first
  · left
    have hg : γ = 2 * α + β := by linarith
    simpa only [hg] using hp.swap_first
  · right; left; left
    exact ⟨hout, Or.inr hp.rotate.rotate⟩
  · right; left; left
    exact ⟨hout, Or.inl hp.rotate⟩
  · right; right; right
    exact ⟨by linarith, Or.inr (Or.inr (Or.inr hp))⟩
  · left
    have hg : γ = 2 * α + 2 * β := by linarith
    simpa only [hg] using hp.swap_first
  · right; right; right
    refine ⟨by linarith, Or.inl ?_⟩
    simpa only [add_comm] using hp
  · right; right; right
    refine ⟨by linarith, Or.inr (Or.inl ?_)⟩
    simpa only [add_comm] using hp.swap_last
  · right; left; right
    exact ⟨hout, Or.inr (Or.inl hp.swap_first)⟩
  · right; left; right
    exact ⟨hout, Or.inr (Or.inr (Or.inl hp.rotate.rotate))⟩
  · right; left; right
    exact ⟨hout, Or.inr (Or.inr (Or.inr hp.rotate))⟩
  · right; left; right
    exact ⟨hout, Or.inl hp⟩

/-- Complete classification of the two-type outer-angle partition once the
geometric angle ledger supplies the bounds by three. -/
theorem two_type_angle_partition_classification (α β γ : ℝ) (θ : Fin 3 → ℝ)
    (x y : Fin 3 → ℕ) (hsum : α + β + γ = Real.pi)
    (hx : 1 ≤ ∑ j, x j ∧ ∑ j, x j ≤ 3)
    (hy : 1 ≤ ∑ j, y j ∧ ∑ j, y j ≤ 3)
    (hpos : ∀ j, 0 < x j + y j)
    (hinj : Function.Injective θ)
    (hθ : ∀ j, θ j = (x j : ℝ) * α + (y j : ℝ) * β)
    (hout : ((∑ j, x j : ℕ) : ℝ) * α + ((∑ j, y j : ℕ) : ℝ) * β = Real.pi) :
    PermutedTriple θ ![α, β, γ] ∨
      ExceptionalAnglePattern α β θ ∨ ExceptionalAnglePattern β α θ := by
  have hxy : Function.Injective (fun j => (x j, y j)) := by
    intro i j hij
    apply hinj
    have hxij := congrArg Prod.fst hij
    have hyij := congrArg Prod.snd hij
    change x i = x j at hxij
    change y i = y j at hyij
    rw [hθ i, hθ j, hxij, hyij]
  obtain ⟨e, he⟩ := corner_partition_up_to_permutation x y hx hy hpos hxy
  have hsx : x (e 0) + x (e 1) + x (e 2) = ∑ j, x j := by
    have h := Equiv.sum_comp e x
    norm_num [Fin.sum_univ_succ] at h
    norm_num [Fin.sum_univ_succ]
    omega
  have hsy : y (e 0) + y (e 1) + y (e 2) = ∑ j, y j := by
    have h := Equiv.sum_comp e y
    norm_num [Fin.sum_univ_succ] at h
    norm_num [Fin.sum_univ_succ]
    omega
  apply sorted_angle_partition_classification α β γ θ e _ _ _ _ _ _ hsum
    _ (hθ (e 0)) (hθ (e 1)) (hθ (e 2)) he
  rwa [hsx, hsy]

end Erdos633

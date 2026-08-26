import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic

/-!
# Length estimates for the bilinear BFC argument

These elementary length calculations are used in the bilinear argument of
P. M. Neumann, *An improved bound for BFC p-groups* (1970), §2–3.
All modules in this file are finite, so composition length is a natural
number without any finiteness convention being used as a hypothesis.
-/

namespace Erdos117

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Composition length as a natural number. The lemmas using this definition
explicitly require finite modules. -/
noncomputable def moduleLength (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] : ℕ :=
  (Module.length R M).toNat

theorem coe_moduleLength [Finite M] :
    (moduleLength R M : ℕ∞) = Module.length R M := by
  have : IsArtinian R M := isArtinian_of_finite
  exact ENat.natCast_toNat Module.length_ne_top

theorem moduleLength_eq_of_equiv (e : M ≃ₗ[R] N) :
    moduleLength R M = moduleLength R N := by
  unfold moduleLength
  rw [e.length_eq]

theorem moduleLength_le_of_injective [Finite M] [Finite N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    moduleLength R M ≤ moduleLength R N := by
  have h := Module.length_le_of_injective f hf
  rw [← coe_moduleLength, ← coe_moduleLength] at h
  exact_mod_cast h

theorem moduleLength_le_of_surjective [Finite M] [Finite N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    moduleLength R N ≤ moduleLength R M := by
  have h := Module.length_le_of_surjective f hf
  rw [← coe_moduleLength, ← coe_moduleLength] at h
  exact_mod_cast h

theorem moduleLength_mono [Finite M] {A B : Submodule R M} (h : A ≤ B) :
    moduleLength R A ≤ moduleLength R B :=
  moduleLength_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

theorem moduleLength_strictMono [Finite M] {A B : Submodule R M} (h : A < B) :
    moduleLength R A < moduleLength R B := by
  have : IsArtinian R M := isArtinian_of_finite
  have hlen := Submodule.height_strictMono h
  rw [← Module.length_submodule, ← Module.length_submodule,
    ← coe_moduleLength, ← coe_moduleLength] at hlen
  exact_mod_cast hlen

theorem moduleLength_eq_zero_iff [Finite M] :
    moduleLength R M = 0 ↔ Subsingleton M := by
  have h := Module.length_eq_zero_iff (R := R) (M := M)
  rw [← coe_moduleLength] at h
  exact_mod_cast h

theorem moduleLength_bot : moduleLength R (⊥ : Submodule R M) = 0 := by
  simp [moduleLength]

theorem moduleLength_top : moduleLength R (⊤ : Submodule R M) = moduleLength R M := by
  simp [moduleLength]

theorem moduleLength_quotient_add [Finite M] (A : Submodule R M) :
    moduleLength R (M ⧸ A) + moduleLength R A = moduleLength R M := by
  have : Finite (M ⧸ A) := Finite.of_surjective A.mkQ A.mkQ_surjective
  have h := Module.length_eq_add_of_exact A.subtype A.mkQ A.subtype_injective
    A.mkQ_surjective (LinearMap.exact_subtype_mkQ A)
  rw [← coe_moduleLength, ← coe_moduleLength, ← coe_moduleLength,
    ← Nat.cast_add] at h
  have h' : moduleLength R M = moduleLength R A + moduleLength R (M ⧸ A) := by
    exact_mod_cast h
  omega

theorem moduleLength_eq_add_of_exact {P : Type*} [AddCommGroup P] [Module R P]
    [Finite M] [Finite N] [Finite P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    moduleLength R N = moduleLength R M + moduleLength R P := by
  have h := Module.length_eq_add_of_exact f g hf hg hfg
  rw [← coe_moduleLength, ← coe_moduleLength, ← coe_moduleLength, ← Nat.cast_add] at h
  exact_mod_cast h

theorem moduleLength_prod [Finite M] [Finite N] :
    moduleLength R (M × N) = moduleLength R M + moduleLength R N := by
  have h := Module.length_prod R M N
  rw [← coe_moduleLength, ← coe_moduleLength, ← coe_moduleLength, ← Nat.cast_add] at h
  exact_mod_cast h

theorem moduleLength_map_le [Finite M] [Finite N] (A : Submodule R M) (f : M →ₗ[R] N) :
    moduleLength R (A.map f) ≤ moduleLength R A := by
  let g : A →ₗ[R] A.map f := (f.comp A.subtype).codRestrict (A.map f)
    (fun x => ⟨x, x.property, rfl⟩)
  apply moduleLength_le_of_surjective g
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

theorem moduleLength_sup_add_inf [Finite M] (A B : Submodule R M) :
    moduleLength R ↥(A ⊔ B) + moduleLength R ↥(A ⊓ B) =
      moduleLength R A + moduleLength R B := by
  let f : ↥(A ⊓ B) →ₗ[R] A × B :=
    (Submodule.inclusion (inf_le_left : A ⊓ B ≤ A)).prod
      (-Submodule.inclusion (inf_le_right : A ⊓ B ≤ B))
  let g : A × B →ₗ[R] ↥(A ⊔ B) :=
    (Submodule.inclusion (le_sup_left : A ≤ A ⊔ B)).coprod
      (Submodule.inclusion (le_sup_right : B ≤ A ⊔ B))
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : A × B => (z.1 : M)) h)
  have hg : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have hfg : Function.Exact f g := by
    rintro ⟨x, y⟩
    constructor
    · intro h
      have heq : (x : M) + y = 0 := congrArg Subtype.val h
      have hy : (y : M) = -(x : M) := eq_neg_of_add_eq_zero_right heq
      refine ⟨⟨x, x.property, ?_⟩, ?_⟩
      · change (x : M) ∈ B
        rw [← neg_mem_iff, ← hy]
        exact y.property
      · apply Prod.ext
        · rfl
        · exact Subtype.ext hy.symm
    · rintro ⟨z, hz⟩
      rw [← hz]
      apply Subtype.ext
      exact add_neg_cancel (z : M)
  have h := moduleLength_eq_add_of_exact f g hf hg hfg
  rw [moduleLength_prod] at h
  omega

theorem moduleLength_sup_le [Finite M] (A B : Submodule R M) :
    moduleLength R ↥(A ⊔ B) ≤ moduleLength R A + moduleLength R B := by
  have h := moduleLength_sup_add_inf A B
  omega

theorem moduleLength_finset_sup_le [Finite M] {ι : Type*}
    (s : Finset ι) (A : ι → Submodule R M) :
    moduleLength R ↥(s.sup A) ≤ ∑ i ∈ s, moduleLength R (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty, Finset.sum_empty, moduleLength_bot]
  | @insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (moduleLength_sup_le _ _).trans (Nat.add_le_add_left ih _)

theorem moduleLength_pos_of_ne_bot [Finite M] {A : Submodule R M} (h : A ≠ ⊥) :
    0 < moduleLength R A := by
  have hlen := moduleLength_strictMono (bot_lt_iff_ne_bot.mpr h)
  simpa only [moduleLength_bot] using hlen

theorem moduleLength_submodule_eq_zero_iff [Finite M] (A : Submodule R M) :
    moduleLength R A = 0 ↔ A = ⊥ := by
  constructor
  · intro h
    by_contra hne
    have hpos := moduleLength_pos_of_ne_bot hne
    omega
  · intro h
    rw [h, moduleLength_bot]

theorem moduleLength_map_quotient_add_inf [Finite M] (A B : Submodule R M) :
    moduleLength R (A.map B.mkQ) + moduleLength R ↥(A ⊓ B) = moduleLength R A := by
  have : Finite (M ⧸ B) := Finite.of_surjective B.mkQ B.mkQ_surjective
  let f : ↥(A ⊓ B) →ₗ[R] A := Submodule.inclusion inf_le_left
  let g : A →ₗ[R] A.map B.mkQ := (B.mkQ.comp A.subtype).codRestrict (A.map B.mkQ)
    (fun x => ⟨x, x.property, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfg : Function.Exact f g := by
    intro x
    constructor
    · intro h
      have hx : (x : M) ∈ B := by
        have h0 : B.mkQ (x : M) = 0 := congrArg Subtype.val h
        exact B.ker_mkQ ▸ h0
      exact ⟨⟨x, x.property, hx⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      have hz : (z : M) ∈ LinearMap.ker B.mkQ := B.ker_mkQ.symm ▸ z.property.2
      exact hz
  have h := moduleLength_eq_add_of_exact f g (Submodule.inclusion_injective _) hg hfg
  omega

theorem moduleLength_map_quotient_add [Finite M] {A B : Submodule R M} (h : B ≤ A) :
    moduleLength R (A.map B.mkQ) + moduleLength R B = moduleLength R A := by
  have heq : A ⊓ B = B := inf_eq_right.mpr h
  have hlen := moduleLength_map_quotient_add_inf A B
  rw [heq] at hlen
  exact hlen

theorem moduleLength_map_quotient_add_right [Finite M] (A B : Submodule R M) :
    moduleLength R (A.map B.mkQ) + moduleLength R B = moduleLength R ↥(A ⊔ B) := by
  have h := moduleLength_map_quotient_add (le_sup_right : B ≤ A ⊔ B)
  have heq : (A ⊔ B).map B.mkQ = A.map B.mkQ := by simp
  rw [heq] at h
  exact h

/-- Successive quotienting has the same image length as quotienting by the
sum of the two kernels. -/
theorem moduleLength_map_quotient_sup [Finite M] (A B S : Submodule R M) :
    moduleLength R ((A.map S.mkQ).map (B.map S.mkQ).mkQ) =
      moduleLength R (A.map (S ⊔ B).mkQ) := by
  have : Finite (M ⧸ S) := Finite.of_surjective S.mkQ S.mkQ_surjective
  have h₁ := moduleLength_map_quotient_add_right (A.map S.mkQ) (B.map S.mkQ)
  have h₂ := moduleLength_map_quotient_add_right (A ⊔ B) S
  have h₃ := moduleLength_map_quotient_add_right B S
  have h₄ := moduleLength_map_quotient_add_right A (S ⊔ B)
  have hmap : (A ⊔ B).map S.mkQ = A.map S.mkQ ⊔ B.map S.mkQ :=
    Submodule.map_sup A B S.mkQ
  have hsup : (A ⊔ B) ⊔ S = A ⊔ (S ⊔ B) := by ac_rfl
  have hcomm : B ⊔ S = S ⊔ B := sup_comm _ _
  rw [hmap, hsup] at h₂
  rw [hcomm] at h₃
  omega

/-- A spanning set of a finite module contains a spanning subset with at most
the composition length many elements. -/
theorem exists_small_spanning_subset [Finite M] (s : Set M) (hs : Submodule.span R s = ⊤) :
    ∃ t : Finset M, (t : Set M) ⊆ s ∧ t.card ≤ moduleLength R M ∧
      Submodule.span R (t : Set M) = ⊤ := by
  classical
  have aux : ∀ k : ℕ, ∀ t : Finset M, (t : Set M) ⊆ s →
      moduleLength R M ≤ moduleLength R (Submodule.span R (t : Set M)) + k →
      ∃ t' : Finset M, (t' : Set M) ⊆ s ∧ t'.card ≤ t.card + k ∧
        Submodule.span R (t' : Set M) = ⊤ := by
    intro k
    induction k with
    | zero =>
      intro t ht hlen
      refine ⟨t, ht, by omega, ?_⟩
      by_contra hne
      have hlt := moduleLength_strictMono (lt_top_iff_ne_top.mpr hne)
      rw [moduleLength_top] at hlt
      omega
    | succ k ih =>
      intro t ht hlen
      by_cases htop : Submodule.span R (t : Set M) = ⊤
      · exact ⟨t, ht, by omega, htop⟩
      have hex : ∃ x ∈ s, x ∉ Submodule.span R (t : Set M) := by
        by_contra! h
        apply htop
        apply top_unique
        rw [← hs]
        exact Submodule.span_le.mpr h
      obtain ⟨x, hx, hxt⟩ := hex
      have hsub : Submodule.span R (t : Set M) <
          Submodule.span R ((insert x t : Finset M) : Set M) := by
        apply lt_of_le_of_ne
        · exact Submodule.span_mono (by simp)
        · intro heq
          apply hxt
          rw [heq]
          exact Submodule.subset_span (by simp)
      have hlt := moduleLength_strictMono hsub
      obtain ⟨t', ht', hcard, hspan⟩ := ih (insert x t) (by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact ht hy) (by omega)
      refine ⟨t', ht', ?_, hspan⟩
      have hc := Finset.card_insert_le x t
      omega
  obtain ⟨t, ht, hcard, hspan⟩ := aux (moduleLength R M) ∅ (by simp) (by simp)
  exact ⟨t, ht, by simpa using hcard, hspan⟩

end Erdos117

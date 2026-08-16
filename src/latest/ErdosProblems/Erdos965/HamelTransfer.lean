import ErdosProblems.Erdos965.Countability
import ErdosProblems.Erdos965.CriticalPair
import ErdosProblems.Erdos965.DeltaSystem

open Function Set Module

namespace Erdos965

/-- The finite support of a real in the chosen Hamel basis. -/
noncomputable def hamelSupport (x : ℝ) : Finset HamelIndex :=
  (hamelBasis.repr x).support

/-- Coordinates on a fixed finite support determine the real uniquely. -/
noncomputable def fixedSupportCode (s : Finset HamelIndex)
    (x : {x : ℝ // hamelSupport x = s}) : s → ℚ :=
  fun i ↦ hamelBasis.repr x.1 i.1

theorem fixedSupportCode_injective (s : Finset HamelIndex) :
    Injective (fixedSupportCode s) := by
  intro x y hxy
  apply Subtype.ext
  apply hamelBasis.repr.injective
  ext i
  by_cases hi : i ∈ s
  · exact congrFun hxy ⟨i, hi⟩
  · have hix : i ∉ hamelSupport x.1 := by simpa [x.2]
    have hiy : i ∉ hamelSupport y.1 := by simpa [y.2]
    rw [Finsupp.notMem_support_iff.mp hix, Finsupp.notMem_support_iff.mp hiy]

/-- Only countably many reals have any specified finite Hamel support. -/
theorem fixedSupport_countable (s : Finset HamelIndex) :
    ({x : ℝ | hamelSupport x = s} : Set ℝ).Countable := by
  rw [← Set.countable_coe_iff]
  exact (fixedSupportCode_injective s).countable

/-- An uncountable set of reals has uncountably many Hamel supports. -/
theorem hamelSupport_image_uncountable {A : Set ℝ} (hA : ¬ A.Countable) :
    ¬ (hamelSupport '' A).Countable := by
  apply image_uncountable_of_countable_fibers hamelSupport hA
  intro s
  exact (fixedSupport_countable s).mono fun _ hx ↦ hx.2

/-- The tuple of Hamel coefficients on a finite root. -/
noncomputable def rootCoeff (root : Finset HamelIndex) (x : ℝ) : root → ℚ :=
  fun i ↦ hamelBasis.repr x i.1

/-- On an uncountable subset, the coefficient tuple on a fixed finite root
can be made constant. -/
theorem exists_uncountable_subset_rootCoeff_eq (root : Finset HamelIndex)
    {A : Set ℝ} (hA : ¬ A.Countable) :
    ∃ (q : root → ℚ) (A' : Set ℝ),
      A' ⊆ A ∧ ¬ A'.Countable ∧
        ∀ x ∈ A', ∀ i : root, hamelBasis.repr x i.1 = q i := by
  obtain ⟨q, hq⟩ := uncountable_fiber_of_countable_range (rootCoeff root) hA
  let A' : Set ℝ := {x ∈ A | rootCoeff root x = q}
  refine ⟨q, A', ?_, hq, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hx i
    exact congrFun hx.2 i

theorem hamelSupport_add_subset (x y : ℝ) :
    hamelSupport (x + y) ⊆ hamelSupport x ∪ hamelSupport y := by
  change (hamelBasis.repr (x + y)).support ⊆
    (hamelBasis.repr x).support ∪ (hamelBasis.repr y).support
  rw [map_add]
  exact Finsupp.support_add

/-- If every common nonzero coordinate survives addition, support of a sum
is exactly the union of the supports. -/
theorem hamelSupport_add_eq_union_of_nocancel (x y : ℝ)
    (h : ∀ i, i ∈ hamelSupport x → i ∈ hamelSupport y →
      hamelBasis.repr x i + hamelBasis.repr y i ≠ 0) :
    hamelSupport (x + y) = hamelSupport x ∪ hamelSupport y := by
  apply Finset.Subset.antisymm (hamelSupport_add_subset x y)
  intro i hi
  rw [Finset.mem_union] at hi
  rw [hamelSupport, map_add, Finsupp.mem_support_iff, Finsupp.add_apply]
  rcases hi with hix | hiy
  · by_cases hiy : i ∈ hamelSupport y
    · exact h i hix hiy
    · rw [Finsupp.notMem_support_iff.mp hiy]
      simpa using Finsupp.mem_support_iff.mp hix
  · by_cases hix : i ∈ hamelSupport x
    · exact h i hix hiy
    · rw [Finsupp.notMem_support_iff.mp hix, zero_add]
      exact Finsupp.mem_support_iff.mp hiy

/-- Equal nonzero coefficients on an intersection cannot cancel in
characteristic zero. -/
theorem hamelSupport_add_eq_union_of_eq_on_inter (x y : ℝ)
    (hEq : ∀ i, i ∈ hamelSupport x → i ∈ hamelSupport y →
      hamelBasis.repr x i = hamelBasis.repr y i) :
    hamelSupport (x + y) = hamelSupport x ∪ hamelSupport y := by
  apply hamelSupport_add_eq_union_of_nocancel x y
  intro i hix hiy
  have hiy0 : hamelBasis.repr y i ≠ 0 := Finsupp.mem_support_iff.mp hiy
  rw [hEq i hix hiy]
  simpa [← two_mul] using mul_ne_zero (two_ne_zero' ℚ) hiy0

/-- Support addition on one pair from a Δ-system, after coefficients on its
root have been made equal. -/
theorem hamelSupport_add_eq_union_of_delta_root (root : Finset HamelIndex)
    (x y : ℝ) (hDelta : hamelSupport x ∩ hamelSupport y = root)
    (hCoeff : ∀ i ∈ root, hamelBasis.repr x i = hamelBasis.repr y i) :
    hamelSupport (x + y) = hamelSupport x ∪ hamelSupport y := by
  apply hamelSupport_add_eq_union_of_eq_on_inter x y
  intro i hix hiy
  apply hCoeff i
  rw [← hDelta]
  exact Finset.mem_inter.mpr ⟨hix, hiy⟩

/-- Uniform support addition on a root-coefficient-thinned Δ-system. -/
theorem hamelSupport_add_eq_union_on_thinned_deltaSystem (root : Finset HamelIndex)
    {A : Set ℝ}
    (hDelta : ∀ {x}, x ∈ A → ∀ {y}, y ∈ A → x ≠ y →
      hamelSupport x ∩ hamelSupport y = root)
    (q : root → ℚ)
    (hCoeff : ∀ x ∈ A, ∀ i : root, hamelBasis.repr x i.1 = q i)
    {x y : ℝ} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    hamelSupport (x + y) = hamelSupport x ∪ hamelSupport y := by
  apply hamelSupport_add_eq_union_of_delta_root root x y (hDelta hx hy hxy)
  intro i hi
  exact (hCoeff x hx ⟨i, hi⟩).trans (hCoeff y hy ⟨i, hi⟩).symm

/-- Abstract finite-support anti-Ramsey property needed by the Hamel transfer. -/
def finset_pair_antiramsey (color : Finset HamelIndex → Fin 2) : Prop :=
  ∀ S : Set (Finset HamelIndex), ¬ S.Countable →
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
      a ≠ b ∧ c ≠ d ∧ color (a ∪ b) ≠ color (c ∪ d)

/-- A real coloring witnessing the negative solution to Erdős 965. -/
def exists_bad_real_coloring : Prop :=
  ∃ color : ℝ → Fin 2, ∀ A : Set ℝ, ¬ A.Countable →
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A,
      a ≠ b ∧ c ≠ d ∧ color (a + b) ≠ color (c + d)

/-- An anti-Ramsey coloring of finite Hamel supports transfers to an
anti-Ramsey coloring of the reals. -/
theorem hamel_transfer_finset_pair_antiramsey
    (color : Finset HamelIndex → Fin 2) (hcolor : finset_pair_antiramsey color) :
    exists_bad_real_coloring := by
  let realColor : ℝ → Fin 2 := fun x ↦ color (hamelSupport x)
  refine ⟨realColor, ?_⟩
  intro A hA
  obtain ⟨J, hJA, hJunc, root, hDelta⟩ :=
    exists_uncountable_deltaSystem hamelSupport hA
  obtain ⟨q, K, hKJ, hKunc, hCoeff⟩ :=
    exists_uncountable_subset_rootCoeff_eq root hJunc
  have hSuppK : ¬ (hamelSupport '' K).Countable := hamelSupport_image_uncountable hKunc
  obtain ⟨sa, hsa, sb, hsb, sc, hsc, sd, hsd, hsab, hscd, hcolors⟩ :=
    hcolor (hamelSupport '' K) hSuppK
  obtain ⟨a, haK, rfl⟩ := hsa
  obtain ⟨b, hbK, rfl⟩ := hsb
  obtain ⟨c, hcK, rfl⟩ := hsc
  obtain ⟨d, hdK, rfl⟩ := hsd
  have hab : a ≠ b := fun hab ↦ hsab (congrArg hamelSupport hab)
  have hcd : c ≠ d := fun hcd ↦ hscd (congrArg hamelSupport hcd)
  have hsum_ab : hamelSupport (a + b) = hamelSupport a ∪ hamelSupport b :=
    hamelSupport_add_eq_union_on_thinned_deltaSystem root
      (fun {x} hxK {y} hyK hxy ↦ hDelta (hKJ hxK) (hKJ hyK) hxy)
      q hCoeff haK hbK hab
  have hsum_cd : hamelSupport (c + d) = hamelSupport c ∪ hamelSupport d :=
    hamelSupport_add_eq_union_on_thinned_deltaSystem root
      (fun {x} hxK {y} hyK hxy ↦ hDelta (hKJ hxK) (hKJ hyK) hxy)
      q hCoeff hcK hdK hcd
  refine ⟨a, hJA (hKJ haK), b, hJA (hKJ hbK), c, hJA (hKJ hcK),
    d, hJA (hKJ hdK), hab, hcd, ?_⟩
  simpa [realColor, hsum_ab, hsum_cd] using hcolors

/-- Specialization of the Hamel transfer to the canonical finite-support
coloring. -/
theorem exists_bad_real_coloring_of_finset_pair_antiramsey
    (hcolor : finset_pair_antiramsey supportColor) : exists_bad_real_coloring :=
  hamel_transfer_finset_pair_antiramsey supportColor hcolor

end Erdos965

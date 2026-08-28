import Wikipedia.NoExoticSixSphere.FiniteLoweringPrefix
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Basic

/-!
# Extending a finite controlled lowering prefix

The compact parameter set for the next step is selected using the original
family and the current high-energy subset. Its image lies in the current
crossing domain by the proved finite movement estimate. Relative homotopies
are restricted to the original protected set before concatenation.
-/

open Set

namespace NoExoticSixSphere.FiniteControlledLowering

variable {M Y : Type*} [TopologicalSpace M] [PseudoMetricSpace Y]

def StepProperty (energy : Y → ℝ) (admissible V : Set Y) (floor k cap ξ ζ ρ : ℝ) : Prop :=
  ∀ (p : C(M, Y)), (∀ x, p x ∈ admissible) →
    ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
      ∃ q : C(M, Y), (∀ x ∈ K, energy (q x) < k) ∧
        ∃ G : ContinuousMap.HomotopyRel p q ({x | energy (p x) ≤ floor} ∪ (p ⁻¹' V)ᶜ),
          ∀ t x, G (t, x) ∈ admissible ∧ energy (G (t, x)) ≤ max (energy (p x)) cap ∧
            energy (G (t, x)) ≤ energy (p x) + ξ ∧
            (energy (p x) - energy (G (t, x)) ≤ 2 * ζ → dist (G (t, x)) (p x) ≤ ρ)

namespace Prefix

variable [CompactSpace M] [T2Space Y]
  {energy : Y → ℝ} {admissible : Set Y} {p₀ : C(M, Y)}
  {F : ℕ → Set Y} {k : ℕ → ℝ} {floor A cap ξ ζ ρ : ℝ} {i : ℕ}
  (P : Prefix energy admissible p₀ F k floor A cap ξ ζ ρ i)

include P

theorem nonempty_succ {n : ℕ} (hin : i < n) (hξ : 0 ≤ ξ) (hρ : 0 ≤ ρ)
    (henergy : ContinuousOn energy admissible) (B : ℝ) (hstart : ∀ x, energy (p₀ x) ≤ B)
    (hbudget : B - A + 2 * (n : ℝ) * ξ ≤ 2 * ζ)
    (V : Set Y) (hF : IsCompact (F i))
    (hfit : ∀ y ∈ F i, ∀ z, dist z y ≤ (n : ℝ) * ρ → z ∈ V)
    (hstep : StepProperty (M := M) energy admissible V floor (k i) cap ξ ζ ρ) :
    Nonempty (Prefix energy admissible p₀ F k floor A cap ξ ζ ρ (i + 1)) := by
  let K := p₀ ⁻¹' F i ∩ {x | A ≤ energy (P.family i x)}
  have he : Continuous (fun x ↦ energy (P.family i x)) :=
    henergy.comp_continuous (P.family i).continuous (P.mem i le_rfl)
  have hK : IsCompact K :=
    ((hF.isClosed.preimage p₀.continuous).inter (isClosed_le continuous_const he)).isCompact
  have hKV : K ⊆ (P.family i) ⁻¹' V := fun _ hx ↦
    P.mem_domain_of_high hin.le hξ hρ B hstart hbudget (F i) V hfit hx.1 hx.2
  obtain ⟨q, hqK, G, hG⟩ := hstep (P.family i) (P.mem i le_rfl) K hK hKV
  have hqMem (x) : q x ∈ admissible := by
    simpa only [G.apply_one] using (hG 1 x).1
  have hqGain (x) : energy (q x) ≤ energy (P.family i x) + ξ := by
    simpa only [G.apply_one] using (hG 1 x).2.2.1
  have hqMove (x) : energy (P.family i x) - energy (q x) ≤ 2 * ζ →
      dist (q x) (P.family i x) ≤ ρ := by
    simpa only [G.apply_one] using (hG 1 x).2.2.2
  have hqLow (x) (hx : p₀ x ∈ F i) (hh : A ≤ energy (P.family i x)) : energy (q x) < k i :=
    hqK x ⟨hx, hh⟩
  let Gfixed : ContinuousMap.HomotopyRel (P.family i) q {x | energy (p₀ x) ≤ floor} :=
    { toHomotopy := G.toHomotopy
      prop' := fun t x hx ↦ G.eq_fst t (Or.inl (by
        change energy (P.family i x) ≤ floor
        rw [P.endpoint_fixed hx]
        exact hx)) }
  let J := P.homotopy.trans Gfixed
  have hJ : ∀ t x, J (t, x) ∈ admissible ∧
      energy (J (t, x)) ≤ max (energy (p₀ x)) cap := by
    intro t x
    change (P.homotopy.trans Gfixed) (t, x) ∈ admissible ∧
      energy ((P.homotopy.trans Gfixed) (t, x)) ≤ max (energy (p₀ x)) cap
    rw [ContinuousMap.HomotopyRel.trans_apply]
    split_ifs
    · exact P.control _ x
    · exact ⟨(hG _ x).1, (hG _ x).2.1.trans
        (max_le (P.endpoint_cap x) (le_max_right _ _))⟩
  let family : ℕ → C(M, Y) := fun j ↦ if j ≤ i then P.family j else q
  have hold (j) (hj : j ≤ i) : family j = P.family j := if_pos hj
  have hnext : family (i + 1) = q := if_neg (by omega)
  refine ⟨{
    family := family
    initial := (hold 0 (Nat.zero_le i)).trans P.initial
    mem := ?_
    gain := ?_
    movement := ?_
    lowered := ?_
    homotopy := J.cast rfl hnext.symm
    control := hJ }⟩
  · intro j hj x
    by_cases hji : j ≤ i
    · rw [hold j hji]
      exact P.mem j hji x
    · have heq : j = i + 1 := by omega
      rw [heq, hnext]
      exact hqMem x
  · intro j hj x
    by_cases hji : j < i
    · rw [hold (j + 1) (by omega), hold j hji.le]
      exact P.gain j hji x
    · have heq : j = i := by omega
      subst j
      rw [hnext, hold i le_rfl]
      exact hqGain x
  · intro j hj x
    by_cases hji : j < i
    · rw [hold (j + 1) (by omega), hold j hji.le]
      exact P.movement j hji x
    · have heq : j = i := by omega
      subst j
      rw [hnext, hold i le_rfl]
      exact hqMove x
  · intro j hj x
    by_cases hji : j < i
    · rw [hold (j + 1) (by omega), hold j hji.le]
      exact P.lowered j hji x
    · have heq : j = i := by omega
      subst j
      rw [hnext, hold i le_rfl]
      exact hqLow x

end Prefix

end NoExoticSixSphere.FiniteControlledLowering

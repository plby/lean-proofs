import StackExchange.Puzzling139335.N4Diagonal.Contacts.Triangle
import StackExchange.Puzzling139335.N4Diagonal.Contacts.EqualAngles

/-!
# Facing contacts for every angular gap

Strict gaps have unique supporting extremizers. At equal angles the actual
one-corner placement makes both facing coordinates strictly below one. The
remaining quarter-turn gap is handled by the triangular endpoint bounds.
-/

open Set

namespace Puzzling139335.N4Diagonal.Model

open ThreeCorners

theorem facing_contacts_subset_singletons (m : Model) :
    N4Midline.levelOneContact m.P m.p (perpRay m.θ) ⊆ {m.q} ∧
      N4Midline.levelOneContact m.P m.q (-perpRay m.β) ⊆ {m.p} := by
  rcases eq_or_lt_of_le m.beta_bounds.1 with heq | hlt
  · rw [m.equal_angles_first_contact_eq_empty heq.symm,
      m.equal_angles_last_contact_eq_empty heq.symm]
    exact ⟨empty_subset _, empty_subset _⟩
  · have hgaple : m.β - m.θ ≤ Real.pi / 2 := by
      linarith [m.theta_bounds.1, m.beta_bounds.2]
    rcases lt_or_eq_of_le hgaple with hgaplt | hgapeq
    · exact ⟨N4Diagonal.first_contact_subset_last_corner m.last_cone
        (m.first_inward_bounds m.q_mem).1.2 (by linarith) hgaplt,
        N4Diagonal.last_contact_subset_first_corner m.first_cone
          (m.last_inward_bounds m.p_mem).2.2 (by linarith) hgaplt⟩
    · have hθ : m.θ = 0 := by linarith [m.theta_bounds.1, m.beta_bounds.2]
      have hβ : m.β = Real.pi / 2 := by linarith
      rw [m.first_perp_contact_empty_at_zero hθ,
        m.last_negative_perp_contact_empty_at_half_pi hβ]
      exact ⟨empty_subset _, empty_subset _⟩

theorem first_facing_contact_subset (m : Model) :
    N4Midline.levelOneContact m.P m.p (perpRay m.θ) ⊆ {m.q} :=
  m.facing_contacts_subset_singletons.1

theorem last_facing_contact_subset (m : Model) :
    N4Midline.levelOneContact m.P m.q (-perpRay m.β) ⊆ {m.p} :=
  m.facing_contacts_subset_singletons.2

end Puzzling139335.N4Diagonal.Model

import MagHK.OperatorSpectrum
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Compact resolvent is expressed through an actual compact bounded inverse
of the operator minus a real scalar. No compactness theorem is assumed here. -/
noncomputable section
namespace MagHK.OperatorModel
open MagHK.Ordering

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A compact bounded two-sided inverse at one real resolvent point. For the
semibounded selfadjoint operators used here this is compact resolvent. -/
def CompactResolvent (T : DomainOperator H) : Prop :=
  ∃ E : ℝ, ∃ R : H →L[ℝ] H, IsCompactOperator R ∧
    (∀ f, R f ∈ T.domain) ∧
    (∀ f (h : R f ∈ T.domain), T.map ⟨R f, h⟩ - E • R f = f) ∧
    ∀ ψ (h : ψ ∈ T.domain), R (T.map ⟨ψ, h⟩ - E • ψ) = ψ

theorem CompactResolvent.resolvent_nonempty (T : DomainOperator H)
    (h : CompactResolvent T) : ∃ E : ℝ, ResolventAt T E := by
  obtain ⟨E, R, _, hd, hr, hl⟩ := h
  exact ⟨E, R, hd, hr, hl⟩

end MagHK.OperatorModel

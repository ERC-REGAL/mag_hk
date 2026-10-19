import MagHK.Ordering
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Literal spectrum, eigenspace, and selfadjoint graph definitions for the
unbounded operator interfaces. No operator-theory result is asserted here. -/
noncomputable section
namespace MagHK.OperatorModel
open MagHK.Ordering

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A bounded two-sided inverse of T-E on its actual operator domain. -/
def ResolventAt (T : DomainOperator H) (E : ℝ) : Prop :=
  ∃ R : H →L[ℝ] H,
    (∀ f, R f ∈ T.domain) ∧
    (∀ f (h : R f ∈ T.domain), T.map ⟨R f, h⟩ - E • R f = f) ∧
    ∀ ψ (h : ψ ∈ T.domain), R (T.map ⟨ψ, h⟩ - E • ψ) = ψ

def spectrum (T : DomainOperator H) : Set ℝ := {E | ¬ ResolventAt T E}

def Eigen (T : DomainOperator H) (E : ℝ) (ψ : H) : Prop :=
  ∃ h : ψ ∈ T.domain, ψ ≠ 0 ∧ T.map ⟨ψ, h⟩ = E • ψ

def eigenspace [NormedSpace ℂ H] (T : DomainOperator H) (E : ℝ) : Submodule ℂ H :=
  Submodule.span ℂ {ψ | ∃ h : ψ ∈ T.domain, T.map ⟨ψ, h⟩ = E • ψ}

def multiplicity [NormedSpace ℂ H] (T : DomainOperator H) (E : ℝ) : ℕ :=
  Module.finrank ℂ (eigenspace T E)

/-- The graph equals its Hilbert adjoint graph, with the complex domain and
complex linearity explicit. This is a definition, not an assumed theorem. -/
def SelfAdjoint [InnerProductSpace ℂ H] (T : DomainOperator H) : Prop :=
  Dense (T.domain : Set H) ∧
  (∀ (c : ℂ) ψ, ψ ∈ T.domain → c • ψ ∈ T.domain) ∧
  (∀ (c : ℂ) ψ (h : ψ ∈ T.domain) (hc : c • ψ ∈ T.domain),
    T.map ⟨c • ψ, hc⟩ = c • T.map ⟨ψ, h⟩) ∧
  ∀ ψ f : H, (∃ h : ψ ∈ T.domain, T.map ⟨ψ, h⟩ = f) ↔
    ∀ η (hη : η ∈ T.domain),
      inner ℂ (T.map ⟨η, hη⟩) ψ = inner ℂ η f

end MagHK.OperatorModel


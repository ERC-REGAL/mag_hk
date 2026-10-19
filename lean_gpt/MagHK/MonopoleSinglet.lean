import MagHK.SpinChart
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A simple eigenspace invariant under the actual monopole rotation action
is a singlet. The argument uses the literal operator eigenspace and the
proved special-unitary character calculation. -/
noncomputable section
namespace MagHK.MonopoleSinglet
open MagHK.MonopoleRealization MagHK.SpinChart

theorem simple_eigenstate_fixed (diagonalize : MagHK.Spin.StandardUnitaryDiagonalization)
    (q : ℤ) (R : AngularMomentumAction q) (F : FermionSystem) (E : ℝ)
    (ψ : FermionState) (hψ : OperatorModel.Eigen F E ψ)
    (hsimple : OperatorModel.multiplicity F E = 1)
    (hcov : ∀ U, OperatorModel.Eigen F E (R.pair U ψ)) :
    ∀ U, R.pair U ψ = ψ := by
  have hmem : ψ ∈ OperatorModel.eigenspace F E :=
    Submodule.subset_span ⟨hψ.choose, hψ.choose_spec.2⟩
  have heq : OperatorModel.eigenspace F E = Submodule.span ℂ {ψ} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hsimple hmem hψ.choose_spec.1
  apply MagHK.Spin.invariant_line_fixed diagonalize R.pair ψ hψ.choose_spec.1
  intro U
  have hU := hcov U
  have hm : R.pair U ψ ∈ OperatorModel.eigenspace F E :=
    Submodule.subset_span ⟨hU.choose, hU.choose_spec.2⟩
  rw [heq, Submodule.mem_span_singleton] at hm
  obtain ⟨c, hc⟩ := hm
  exact ⟨c, hc.symm⟩

end MagHK.MonopoleSinglet

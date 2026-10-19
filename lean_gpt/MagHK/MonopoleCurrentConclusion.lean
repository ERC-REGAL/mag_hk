import MagHK.MonopoleCurrentAveraging
import MagHK.MonopoleCurrentTest
import MagHK.MonopoleWeakFlux

/-! A singlet bound state has zero literal marginal current. The proof uses
L¹ rotation averaging, the proved stationary test equation, and the kernel
of the weak derivative. No selected-state marginal regularity is assumed. -/
noncomputable section
namespace MagHK.MonopoleCurrentConclusion
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleCurrent MagHK.SpinChart
open MagHK.MonopoleCovariance MagHK.MonopoleCoordinates MagHK.MonopoleInverse
open MagHK.MonopoleCurrentAveraging
set_option maxHeartbeats 1000000

theorem current_zero
    (weak : MagHK.MonopoleCurrentZero.StandardDistributionKernelLibrary)
    (averaging : StandardRotationFixedSpaceLibrary)
    (q : ℤ) (R : AngularMomentumAction q)
    (S : MagneticFormSystem) (F : FermionSystem) (_hF : FermionFacts F q coulomb)
    (hS : MagneticFormFacts S F q coulomb) (A : MagneticRotations q R S F coulomb hS)
    (E : ℝ) (ψ : FermionState) (hψ : OperatorModel.Eigen F E ψ) (_hnorm : ‖ψ‖ = 1)
    (hfixed : ∀ U, R.pair U ψ = ψ) :
    ∃ φ : S.domain, (φ : PairState) = (ψ : PairState) ∧
      current S φ =ᵐ[chartMeasure] 0 := by
  obtain ⟨hdom, hne, heig⟩ := hψ
  let φ : S.domain := ⟨(ψ : PairState), hS.operator_domain ψ hdom⟩
  have hfix : ∀ U, R.pair U (asFermion S F q coulomb hS φ) =
      asFermion S F q coulomb hS φ := hfixed
  obtain ⟨a, ha, hlocal, hrad⟩ := current_radial averaging q R S F coulomb hS A φ hfix
  have hweak := MagHK.MonopoleCurrentTest.radial_stationary_test S F q coulomb hS
    ψ hdom E heig a hrad
  have hphysical : ∀ᵐ x ∂chartMeasure,
      physicalCurrent S φ (point x) = a x.1 • MagHK.MonopoleQuadrature.direction x.2 := by
    filter_upwards [physicalCurrent_chart S φ, hrad] with x hx hr
    exact hx.trans hr
  have hzero := MagHK.MonopoleWeakFlux.stationary_radial_field_zero weak
    (physicalCurrent S φ) (physicalCurrent_measurable S φ) (physicalCurrent_integrable S φ)
    a hlocal hphysical hweak
  refine ⟨φ, rfl, ?_⟩
  have hchart := point_measurePreserving.quasiMeasurePreserving.ae hzero
  filter_upwards [physicalCurrent_chart S φ, hchart] with x hx hz
  exact hx.symm.trans hz

end MagHK.MonopoleCurrentConclusion

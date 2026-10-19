import MagHK.MonopoleCovariance
import MagHK.MonopoleInverse
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The fixed subspace of the rotation action on L¹ vector fields, followed
by its application to the literal physical marginal current. -/
noncomputable section
namespace MagHK.MonopoleCurrentAveraging
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleCurrent MagHK.SpinChart
open MagHK.MonopoleCovariance MagHK.MonopoleCoordinates MagHK.MonopoleInverse
set_option maxHeartbeats 1000000
abbrev Space := MagHK.MonopoleQuadrature.Space

/-- The universal L¹ fixed-subspace theorem for the proper rotation action.
This is the compact-group averaging theorem for arbitrary vector fields.
There is no Hamiltonian, wavefunction, stationarity or zero-current premise. -/
def StandardRotationFixedSpaceLibrary : Prop :=
  ∀ J : Space → Space, Integrable J →
    (∀ Q : Space ≃ₗᵢ[ℝ] Space, LinearMap.det Q.toLinearMap = 1 →
      (fun x => J (Q x)) =ᵐ[volume] fun x => Q (J x)) →
    ∃ a : ℝ → ℝ, Measurable a ∧
      LocallyIntegrableOn (fun r => r ^ 2 * a r) (Ioi (0 : ℝ)) ∧
      J =ᵐ[volume] fun x => a ‖x‖ • MagHK.MonopoleSphere.normalize x

theorem physical_rotation_ae (q : ℤ) (R : AngularMomentumAction q)
    (S : MagneticFormSystem) (F : FermionSystem) (W : Chart × Chart → ℝ)
    (hS : MagneticFormFacts S F q W) (A : MagneticRotations q R S F W hS)
    (ψ : S.domain)
    (hfixed : ∀ U, R.pair U (asFermion S F q W hS ψ) = asFermion S F q W hS ψ)
    (U : MagHK.Spin.Group) :
    (fun z => physicalCurrent S ψ (R.rotation U⁻¹ z)) =ᵐ[volume]
      fun z => R.rotation U⁻¹ (physicalCurrent S ψ z) := by
  have hmoved := (R.chart_measure U).quasiMeasurePreserving.ae (physicalCurrent_chart S ψ)
  have hchart : ∀ᵐ x ∂chartMeasure,
      physicalCurrent S ψ (R.rotation U⁻¹ (point x)) =
        R.rotation U⁻¹ (physicalCurrent S ψ (point x)) := by
    filter_upwards [hmoved, physicalCurrent_chart S ψ,
      current_fixed_rotation q R S F W hS A ψ hfixed U,
      Measure.quasiMeasurePreserving_snd.ae MagHK.MonopoleTrial.angle_ae] with x hm hj hc hx
    rw [← moved_point q R U x hx, hm, hc, hj]
  have hset : MeasurableSet {z : Space | physicalCurrent S ψ (R.rotation U⁻¹ z) =
      R.rotation U⁻¹ (physicalCurrent S ψ z)} :=
    measurableSet_eq_fun ((physicalCurrent_measurable S ψ).comp
      (R.rotation U⁻¹).continuous.measurable)
      ((R.rotation U⁻¹).continuous.measurable.comp (physicalCurrent_measurable S ψ))
  have h := (ae_map_iff point_continuous.measurable.aemeasurable hset).mpr hchart
  rwa [point_measurePreserving.map_eq] at h

theorem physical_equivariant_ae (q : ℤ) (R : AngularMomentumAction q)
    (S : MagneticFormSystem) (F : FermionSystem) (W : Chart × Chart → ℝ)
    (hS : MagneticFormFacts S F q W) (A : MagneticRotations q R S F W hS)
    (ψ : S.domain)
    (hfixed : ∀ U, R.pair U (asFermion S F q W hS ψ) = asFermion S F q W hS ψ)
    (Q : Space ≃ₗᵢ[ℝ] Space) (hQ : LinearMap.det Q.toLinearMap = 1) :
    (fun z => physicalCurrent S ψ (Q z)) =ᵐ[volume]
      fun z => Q (physicalCurrent S ψ z) := by
  obtain ⟨V, hV⟩ := R.rotation_cover Q hQ
  simpa only [inv_inv, hV] using physical_rotation_ae q R S F W hS A ψ hfixed V⁻¹

theorem current_radial (averaging : StandardRotationFixedSpaceLibrary)
    (q : ℤ) (R : AngularMomentumAction q)
    (S : MagneticFormSystem) (F : FermionSystem) (W : Chart × Chart → ℝ)
    (hS : MagneticFormFacts S F q W) (A : MagneticRotations q R S F W hS)
    (ψ : S.domain)
    (hfixed : ∀ U, R.pair U (asFermion S F q W hS ψ) = asFermion S F q W hS ψ) :
    ∃ a : ℝ → ℝ, Measurable a ∧
      LocallyIntegrableOn (fun r => r ^ 2 * a r) (Ioi (0 : ℝ)) ∧
      current S ψ =ᵐ[chartMeasure]
        fun x => a x.1 • MagHK.MonopoleQuadrature.direction x.2 := by
  obtain ⟨a, ha, hl, hr⟩ := averaging (physicalCurrent S ψ)
    (physicalCurrent_integrable S ψ) (physical_equivariant_ae q R S F W hS A ψ hfixed)
  refine ⟨a, ha, hl, ?_⟩
  have hrchart := point_measurePreserving.quasiMeasurePreserving.ae hr
  filter_upwards [physicalCurrent_chart S ψ, hrchart,
    Measure.quasiMeasurePreserving_fst.ae MagHK.MonopoleExpectation.radialVolume_ae,
    Measure.quasiMeasurePreserving_snd.ae MagHK.MonopoleTrial.angle_ae] with x hj hrad hpos hx
  have hn : ‖point x‖ = x.1 := by
    rw [point, norm_smul, MagHK.MonopoleQuadrature.direction_norm x.2 hx,
      mul_one, Real.norm_eq_abs, abs_of_pos hpos]
  rw [← hj, hrad, hn]
  congr 1
  rw [MagHK.MonopoleSphere.normalize, hn, point, smul_smul,
    inv_mul_cancel₀ hpos.ne', one_smul]

end MagHK.MonopoleCurrentAveraging

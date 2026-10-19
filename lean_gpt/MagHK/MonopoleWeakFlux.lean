import MagHK.MonopoleCurrentZero
import MagHK.MonopoleCoordinates
import MagHK.MonopoleExpectation
import MagHK.MonopoleFlow

/-! Almost-everywhere radial flux needs no continuous current representative.
The scalar distribution kernel and actual Euclidean L1 bound suffice. -/
noncomputable section
namespace MagHK.MonopoleWeakFlux
open MeasureTheory Set
open MagHK.MonopoleCurrentZero MagHK.MonopoleRealization MagHK.MonopoleTrial
open MagHK.MonopoleCoordinates MagHK.MonopoleFlow
open scoped ContDiff ENNReal

theorem stationary_radial_flux_constant_ae (weak : StandardDistributionKernelLibrary)
    (a : ℝ → ℝ) (ha : LocallyIntegrableOn (fun r => r ^ 2 * a r) (Ioi (0 : ℝ)))
    (hweak : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      Function.support χ ⊆ Ioi 0 →
      (∫ r in Ioi (0 : ℝ), deriv χ r * (r ^ 2 * a r)) = 0) :
    ∃ c : ℝ, ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), r ^ 2 * a r = c :=
  weak (Ioi 0) isOpen_Ioi (convex_Ioi (0 : ℝ)).isPreconnected
    (fun r => r ^ 2 * a r) ha hweak

theorem stationary_radial_inverse_square_ae (weak : StandardDistributionKernelLibrary)
    (a : ℝ → ℝ) (ha : LocallyIntegrableOn (fun r => r ^ 2 * a r) (Ioi (0 : ℝ)))
    (hweak : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      Function.support χ ⊆ Ioi 0 →
      (∫ r in Ioi (0 : ℝ), deriv χ r * (r ^ 2 * a r)) = 0) :
    ∃ c : ℝ, ∀ᵐ r ∂radialVolume, a r = c / r ^ 2 := by
  obtain ⟨c, hc⟩ := stationary_radial_flux_constant_ae weak a ha hweak
  have hw : ∀ᵐ r ∂radialVolume, r ^ 2 * a r = c :=
    (withDensity_absolutelyContinuous (volume.restrict (Ioi (0 : ℝ)))
      (fun r => (Real.toNNReal (r ^ 2) : ℝ≥0∞))).ae_le hc
  refine ⟨c, ?_⟩
  filter_upwards [hw, MagHK.MonopoleExpectation.radialVolume_ae] with r hr hpos
  apply (eq_div_iff (pow_ne_zero 2 (ne_of_gt hpos))).mpr
  simpa only [mul_comm] using hr

theorem stationary_radial_field_zero
    (weak : StandardDistributionKernelLibrary)
    (J : MagHK.SpinChart.Space → MagHK.SpinChart.Space) (hm : Measurable J) (hi : Integrable J)
    (a : ℝ → ℝ) (ha : LocallyIntegrableOn (fun r => r ^ 2 * a r) (Ioi (0 : ℝ)))
    (hchart : ∀ᵐ x ∂chartMeasure,
      J (MagHK.SpinChart.point x) = a x.1 • MagHK.MonopoleQuadrature.direction x.2)
    (hweak : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      Function.support χ ⊆ Ioi 0 →
      (∫ r in Ioi (0 : ℝ), deriv χ r * (r ^ 2 * a r)) = 0) :
    J =ᵐ[volume] 0 := by
  obtain ⟨c, hc⟩ := stationary_radial_inverse_square_ae weak a ha hweak
  have he : ∀ᵐ x ∂chartMeasure, J (MagHK.SpinChart.point x) = radialFlux c (MagHK.SpinChart.point x) := by
    filter_upwards [hchart, Measure.quasiMeasurePreserving_fst.ae hc,
      Measure.quasiMeasurePreserving_fst.ae MagHK.MonopoleExpectation.radialVolume_ae,
      Measure.quasiMeasurePreserving_snd.ae angle_ae] with x hx hc hr hp
    have hn : ‖MagHK.SpinChart.point x‖ = x.1 := by
      rw [MagHK.SpinChart.point, norm_smul, Real.norm_eq_abs,
        MagHK.MonopoleQuadrature.direction_norm x.2 hp, mul_one, abs_of_pos hr]
    rw [hx, hc, radialFlux, hn, MagHK.SpinChart.point, smul_smul]
    congr 1
    field_simp [ne_of_gt hr]
    <;> ring
  have hmeas : Measurable (radialFlux c) := by
    unfold radialFlux
    fun_prop
  have he' := (ae_map_iff point_continuous.measurable.aemeasurable
    (measurableSet_eq_fun hm hmeas)).mpr he
  rw [point_measurePreserving.map_eq] at he'
  have hc0 := integrable_radialFlux_zero c (hi.congr he')
  filter_upwards [he'] with x hx
  simpa [hc0, radialFlux] using hx

end MagHK.MonopoleWeakFlux

import MagHK.SpinGeometry

/-! The actual monopole chart measure pushes forward to Euclidean volume. -/
noncomputable section
namespace MagHK.MonopoleCoordinates
open MeasureTheory Set Filter
open MagHK.MonopoleRealization MagHK.MonopoleTrial MagHK.SpinChart
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem point_continuous : Continuous point :=
  continuous_fst.smul (MagHK.MonopoleQuadrature.direction_continuous.comp continuous_snd)

theorem point_spherical (r : ℝ) (p : Angle) :
    point (r, p) = WithLp.toLp 2 (MagHK.MonopoleGeometry.spherical r p) :=
  (MagHK.MonopoleQuadrature.spherical_eq_smul r p).symm

theorem point_measurePreserving : MeasurePreserving point chartMeasure (volume : Measure Space) := by
  refine ⟨point_continuous.measurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf point_continuous.measurable]
  have hm : Measurable (fun x : Chart => f (point x)) := hf.comp point_continuous.measurable
  change (∫⁻ x, f (point x) ∂radialVolume.prod sphereMeasure) = _
  rw [lintegral_prod _ hm.aemeasurable]
  have hw : Measurable (fun r : ℝ => (Real.toNNReal (r ^ 2) : ℝ≥0∞)) := by fun_prop
  change (∫⁻ r, ∫⁻ p, f (point (r, p)) ∂sphereMeasure
    ∂(volume.restrict (Ioi (0 : ℝ))).withDensity (fun r => (Real.toNNReal (r ^ 2) : ℝ≥0∞))) = _
  rw [lintegral_withDensity_eq_lintegral_mul₀' hw.aemeasurable
    hm.lintegral_prod_right.aemeasurable]
  rw [MagHK.MonopoleQuadrature.lintegral_spherical f hf]
  apply lintegral_congr_ae
  apply Eventually.of_forall
  intro r
  change ENNReal.ofReal (r ^ 2) * (∫⁻ p, f (point (r, p)) ∂sphereMeasure) = _
  have hm' : Measurable (fun p : Angle => f (point (r, p))) :=
    hm.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_const_mul _ hm']
  apply lintegral_congr
  intro p
  rw [point_spherical]

/-- Any measurable Euclidean current representative inherits the actual chart L¹ estimate. -/
theorem integrable_of_chart (J : Space → Space) (hJ : AEStronglyMeasurable J)
    (hchart : Integrable (fun x : Chart => J (point x)) chartMeasure) : Integrable J := by
  have hmap : AEStronglyMeasurable J (Measure.map point chartMeasure) := by
    rw [point_measurePreserving.map_eq]
    exact hJ
  have h := (integrable_map_measure hmap point_continuous.measurable.aemeasurable).mpr hchart
  rwa [point_measurePreserving.map_eq] at h

end MagHK.MonopoleCoordinates

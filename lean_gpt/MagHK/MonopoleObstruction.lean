import MagHK.MonopolePairLaw
import MagHK.Correlation

/-! The Coulomb angular obstruction for the actual angular determinant and measure. -/
noncomputable section
namespace MagHK.MonopoleObstruction
open MeasureTheory Set Filter
open MagHK.Monopole MagHK.MonopoleTrial
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem pairDot_interior_ae :
    ∀ᵐ p ∂sphereMeasure.prod sphereMeasure, pairDot p ∈ Ioo (-1 : ℝ) 1 := by
  apply ae_of_ae_map pairDot_continuous.measurable.aemeasurable
  have hquad := MagHK.MonopolePairLaw.sphericalPairQuadrature
  change Measure.map pairDot (sphereMeasure.prod sphereMeasure) = _ at hquad
  rw [hquad]
  apply Measure.ae_smul_measure
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact ae_restrict_mem measurableSet_Ioo

theorem angularDet_nonzero_ae :
    ∀ᵐ p ∂sphereMeasure.prod sphereMeasure, angularDet p.1 p.2 ≠ 0 := by
  filter_upwards [pairDot_interior_ae, angularDet_probability_ae] with p hp hprob
  exact angular_factor_nonzero (pairDot p) (angularDet p.1 p.2) hp.2 hprob

/-- A nonzero radial coefficient cannot absorb the actual Coulomb angular multiplier. -/
theorem no_ae_pair_coulomb_multiple (s t : ℝ) (A B : ℂ)
    (hs : 0 < s) (ht : 0 < t) (hA : A ≠ 0) :
    ¬ (∀ᵐ p : Angle × Angle ∂sphereMeasure.prod sphereMeasure,
      (B + ((1 / pairDistance s t p : ℝ) : ℂ) * A) * angularDet p.1 p.2 = 0) := by
  intro heq
  have hscalar : ∀ᵐ p ∂sphereMeasure.prod sphereMeasure,
      (coulombAngular s t (pairDot p) : ℂ) * A = -B := by
    filter_upwards [heq, angularDet_nonzero_ae,
      Measure.quasiMeasurePreserving_fst.ae angle_ae,
      Measure.quasiMeasurePreserving_snd.ae angle_ae] with p he hp ha hb
    have hzero := (mul_eq_zero.mp he).resolve_right hp
    rw [pairDistance_eq s t p ha hb] at hzero
    change B + (coulombAngular s t (pairDot p) : ℂ) * A = 0 at hzero
    linear_combination hzero
  have hm : Measurable (fun μ : ℝ => (coulombAngular s t μ : ℂ) * A) := by
    unfold coulombAngular
    fun_prop
  have hpush : ∀ᵐ μ ∂Measure.map pairDot (sphereMeasure.prod sphereMeasure),
      (coulombAngular s t μ : ℂ) * A = -B :=
    (ae_map_iff pairDot_continuous.measurable.aemeasurable
      (measurableSet_eq_fun hm measurable_const)).mpr hscalar
  have hquad := MagHK.MonopolePairLaw.sphericalPairQuadrature
  change Measure.map pairDot (sphereMeasure.prod sphereMeasure) = _ at hquad
  rw [hquad, Measure.ae_ennreal_smul_measure_iff (by positivity : ENNReal.ofReal (8 * Real.pi ^ 2) ≠ 0),
    ← Measure.restrict_congr_set Ioo_ae_eq_Icc] at hpush
  exact no_ae_coulomb_multiple s t A (-B) hs ht hA hpush

end MagHK.MonopoleObstruction

import MagHK.MonopoleGeometry
import MagHK.MonopoleSphere
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The equal-area angular chart and actual Euclidean radial projection. -/
noncomputable section
namespace MagHK.MonopoleQuadrature

open MeasureTheory Set Filter Metric
open MagHK.MonopoleGeometry
open MagHK.MonopoleSphere
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000

abbrev Space := WithLp 2 (ℝ × ℂ)

def direction (p : Pair) : Space := WithLp.toLp 2 (spherical 1 p)

theorem direction_continuous : Continuous direction :=
  (WithLp.prod_continuous_toLp 2 ℝ ℂ).comp
    (spherical_continuous.comp (continuous_const.prodMk continuous_id))

theorem circle_norm (φ : ℝ) : ‖circle φ‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← Complex.normSq_eq_norm_sq]
  simp [circle, Complex.normSq_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
    ← pow_two, Real.cos_sq_add_sin_sq]

theorem direction_norm (p : Pair) (hp : p.1 ∈ Icc (-1 : ℝ) 1) : ‖direction p‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖1 * p.1‖ ^ 2 + ‖cylinder (1 * Real.sqrt (1 - p.1 ^ 2)) p.2‖ ^ 2 = 1 ^ 2
  have hq : 0 ≤ 1 - p.1 ^ 2 := by have hl := hp.1; have hu := hp.2; nlinarith
  simp only [cylinder, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    circle_norm, mul_one, sq_abs, Real.sq_sqrt hq]
  ring

theorem spherical_eq_smul (r : ℝ) (p : Pair) :
    WithLp.toLp 2 (spherical r p) = r • direction p := by
  apply WithLp.ofLp_injective
  ext
  · simp [spherical, direction, WithLp.ofLp_smul]
  · simp [spherical, direction, cylinder, WithLp.ofLp_smul, Complex.real_smul]
    ring

theorem spherical_norm (r : ℝ) (hr : 0 < r) (p : Pair)
    (hp : p.1 ∈ Icc (-1 : ℝ) 1) : ‖WithLp.toLp 2 (spherical r p)‖ = r := by
  rw [spherical_eq_smul, norm_smul, direction_norm p hp, mul_one,
    Real.norm_eq_abs, abs_of_pos hr]

theorem spherical_normalize (r : ℝ) (hr : 0 < r) (p : Pair)
    (hp : p.1 ∈ Icc (-1 : ℝ) 1) :
    MagHK.MonopoleSphere.normalize (WithLp.toLp 2 (spherical r p)) = direction p := by
  rw [MagHK.MonopoleSphere.normalize, spherical_norm r hr p hp, spherical_eq_smul, smul_smul,
    inv_mul_cancel₀ hr.ne', one_smul]

theorem sphereMeasure_eq_open : MagHK.MonopoleTrial.sphereMeasure =
    (volume.restrict (Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  unfold MagHK.MonopoleTrial.sphereMeasure MagHK.MonopoleTrial.cosineMeasure
    MagHK.MonopoleTrial.azimuthMeasure MagHK.CylindricalOrbitals.angularMeasure
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc]

theorem lintegral_spherical (f : Space → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Space, f x) = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ p,
      ENNReal.ofReal (r ^ 2) * f (WithLp.toLp 2 (spherical r p)) ∂MagHK.MonopoleTrial.sphereMeasure := by
  rw [← (WithLp.volume_preserving_toLp ℝ ℂ).lintegral_comp hf]
  have hpolar := lintegral_spherical_open (fun x => f (WithLp.toLp 2 x))
    (hf.comp (WithLp.prod_continuous_toLp 2 ℝ ℂ).measurable)
  rw [hpolar]
  apply lintegral_congr_ae
  apply Eventually.of_forall
  intro r
  dsimp only
  rw [sphereMeasure_eq_open, lintegral_prod]
  apply Measurable.aemeasurable
  apply Measurable.const_mul
  exact hf.comp ((WithLp.prod_continuous_toLp 2 ℝ ℂ).comp
    (spherical_continuous.comp (continuous_const.prodMk continuous_id))).measurable

/-- The radius integral of the unit ball, with its exact spherical Jacobian. -/
theorem unitBall_radial_integral :
    (∫⁻ r in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun s => ENNReal.ofReal (s ^ 2)) r) =
      (1 / 3 : ℝ≥0∞) := by
  rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have he : Iio (1 : ℝ) ∩ Ioi 0 = Ioo 0 1 := by ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]; tauto
  rw [he, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
    norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
  · exact (continuous_pow 2).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · exact Eventually.of_forall (fun r => sq_nonneg r)

theorem unitBall_angular_integral (f : Space → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in ball (0 : Space) 1, f (MagHK.MonopoleSphere.normalize x)) =
      (1 / 3 : ℝ≥0∞) * ∫⁻ p, f (direction p) ∂MagHK.MonopoleTrial.sphereMeasure := by
  let g : Space → ℝ≥0∞ := (ball (0 : Space) 1).indicator (fun x => f (MagHK.MonopoleSphere.normalize x))
  have hg : Measurable g := (hf.comp normalize_measurable).indicator measurableSet_ball
  have hcoord := lintegral_spherical g hg
  rw [show (∫⁻ x : Space, g x) = ∫⁻ x in ball (0 : Space) 1, f (MagHK.MonopoleSphere.normalize x) from
    lintegral_indicator measurableSet_ball _] at hcoord
  rw [hcoord]
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ),
        ((Iio (1 : ℝ)).indicator (fun s => ENNReal.ofReal (s ^ 2)) r) *
          ∫⁻ p, f (direction p) ∂MagHK.MonopoleTrial.sphereMeasure := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have he : (fun p => ENNReal.ofReal (r ^ 2) * g (WithLp.toLp 2 (spherical r p))) =ᵐ[
          MagHK.MonopoleTrial.sphereMeasure] (fun p =>
          ((Iio (1 : ℝ)).indicator (fun s => ENNReal.ofReal (s ^ 2)) r) * f (direction p)) := by
        filter_upwards [MagHK.MonopoleTrial.angle_ae] with p hp
        have hb : WithLp.toLp 2 (spherical r p) ∈ ball (0 : Space) 1 ↔ r < 1 := by
          rw [mem_ball_zero_iff, spherical_norm r hr p hp]
        by_cases hr1 : r < 1
        · dsimp only [g]
          rw [Set.indicator_of_mem (hb.mpr hr1), spherical_normalize r hr p hp]
          simp [Set.indicator, hr1]
        · dsimp only [g]
          rw [Set.indicator_of_notMem (fun h => hr1 (hb.mp h))]
          simp [Set.indicator, hr1]
      rw [lintegral_congr_ae he]
      exact lintegral_const_mul _ (hf.comp direction_continuous.measurable)
    _ = _ := by
      have hm : Measurable ((Iio (1 : ℝ)).indicator (fun s => ENNReal.ofReal (s ^ 2))) :=
        (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)).indicator measurableSet_Iio
      rw [lintegral_mul_const _ hm, unitBall_radial_integral]

/-- The explicit dμ dφ chart is the radial projection of actual unit-ball volume. -/
theorem directionMeasure_eq_angularBall :
    Measure.map direction MagHK.MonopoleTrial.sphereMeasure =
      (angularBallMeasure : Measure Space) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf direction_continuous.measurable,
    angularBallMeasure, lintegral_smul_measure,
    lintegral_map hf normalize_measurable, unitBall_angular_integral f hf]
  simp only [smul_eq_mul, ← mul_assoc]
  simp only [one_div]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul]

theorem directionMeasure_invariant (R : Space ≃ₗᵢ[ℝ] Space) :
    Measure.map R (Measure.map direction MagHK.MonopoleTrial.sphereMeasure) =
      Measure.map direction MagHK.MonopoleTrial.sphereMeasure := by
  rw [directionMeasure_eq_angularBall, angularBallMeasure_invariant R]

end MagHK.MonopoleQuadrature

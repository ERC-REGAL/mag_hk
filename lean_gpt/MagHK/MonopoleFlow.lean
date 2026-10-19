import MagHK.MonopolePairLaw
import MagHK.RadialCurrent
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Actual Euclidean integrability and the radial stationary-current argument. -/
noncomputable section
namespace MagHK.MonopoleFlow
open MeasureTheory Set Filter
open MagHK.MonopoleGeometry MagHK.MonopoleQuadrature
open scoped ENNReal
set_option maxHeartbeats 1000000

/-- A radial flux field on Euclidean three-space, defined also at the origin. -/
def radialFlux (c : ℝ) (x : Space) : Space := (c / ‖x‖ ^ 3) • x

theorem radialFlux_measurable (c : ℝ) : Measurable (radialFlux c) := by
  unfold radialFlux
  fun_prop

theorem radialFlux_norm (c r : ℝ) (hr : 0 < r) (p : Pair)
    (hp : p.1 ∈ Icc (-1 : ℝ) 1) :
    ‖radialFlux c (WithLp.toLp 2 (spherical r p))‖ = |c| / r ^ 2 := by
  rw [radialFlux, norm_smul, Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_nonneg (norm_nonneg _), spherical_norm r hr p hp]
  field_simp

/-- A nonzero constant radial flux has infinite actual Euclidean norm integral. -/
theorem radialFlux_lintegral (c : ℝ) (hc : c ≠ 0) :
    (∫⁻ x : Space, ENNReal.ofReal ‖radialFlux c x‖) = ∞ := by
  have hm : Measurable (fun x : Space => ENNReal.ofReal ‖radialFlux c x‖) :=
    ENNReal.measurable_ofReal.comp (radialFlux_measurable c).norm
  rw [lintegral_spherical _ hm]
  have he : (fun r : ℝ => ∫⁻ p, ENNReal.ofReal (r ^ 2) *
      ENNReal.ofReal ‖radialFlux c (WithLp.toLp 2 (spherical r p))‖
      ∂MagHK.MonopoleTrial.sphereMeasure) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun _ => ENNReal.ofReal |c| * ENNReal.ofReal (4 * Real.pi) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hang : (fun p : Pair => ENNReal.ofReal (r ^ 2) *
        ENNReal.ofReal ‖radialFlux c (WithLp.toLp 2 (spherical r p))‖) =ᵐ[
        MagHK.MonopoleTrial.sphereMeasure] fun _ => ENNReal.ofReal |c| := by
      filter_upwards [MagHK.MonopoleTrial.angle_ae] with p hp
      rw [radialFlux_norm c r hr p hp, ← ENNReal.ofReal_mul (sq_nonneg r)]
      congr 1
      field_simp [ne_of_gt (show 0 < r from hr)]
    rw [lintegral_congr_ae hang, lintegral_const, MagHK.MonopolePairLaw.sphereMeasure_univ]
  rw [lintegral_congr_ae he, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioi]
  exact ENNReal.mul_top (by positivity)

/-- The norm-integrability step uses Euclidean volume, not an assumed annular formula. -/
theorem integrable_radialFlux_zero (c : ℝ) (hc : Integrable (radialFlux c)) : c = 0 := by
  by_contra hne
  have hfinite := (hasFiniteIntegral_iff_norm _).mp hc.hasFiniteIntegral
  rw [radialFlux_lintegral c hne] at hfinite
  exact (lt_irrefl ∞) hfinite

end MagHK.MonopoleFlow

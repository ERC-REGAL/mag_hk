import MagHK.Monopole
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The literal radial trial orbital and its normalization. The auxiliary
ell equals the explicit square-root exponent in the revised manuscript. -/

noncomputable section
namespace MagHK.Monopole
open MeasureTheory Set

theorem ell_gamma_argument : ell + 3 / 2 = 1 + Real.sqrt 3 / 2 := by
  unfold ell
  ring

def radialOrbital (s : ℝ) : ℝ :=
  Real.sqrt (2 / Real.Gamma (1 + Real.sqrt 3 / 2)) *
    s ^ ((Real.sqrt 3 - 1) / 2) * Real.exp (-s ^ 2 / 2)

theorem radialOrbital_positive (s : ℝ) (hs : 0 < s) : 0 < radialOrbital s := by
  have harg : 0 < 1 + Real.sqrt 3 / 2 := by positivity
  have hgamma := Real.Gamma_pos_of_pos harg
  unfold radialOrbital
  positivity

theorem radialOrbital_squared_density (s : ℝ) (hs : 0 < s) :
    s ^ 2 * radialOrbital s ^ 2 = radialDensity s := by
  have harg : 0 < 1 + Real.sqrt 3 / 2 := by positivity
  have hgamma := Real.Gamma_pos_of_pos harg
  have he : Real.exp (-s ^ 2 / 2) ^ 2 = Real.exp (-s ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hp : (s ^ ell) ^ (2 : ℕ) = s ^ (2 * ell) := by
    rw [← Real.rpow_mul_natCast hs.le]
    congr 1
    ring
  change s ^ 2 *
    (Real.sqrt (2 / Real.Gamma (1 + Real.sqrt 3 / 2)) * s ^ ell *
      Real.exp (-s ^ 2 / 2)) ^ 2 = _
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), he, hp]
  unfold radialDensity
  rw [ell_gamma_argument, Real.rpow_add hs, Real.rpow_two]
  ring

theorem radialOrbital_normalized :
    (∫ s in Ioi (0 : ℝ), s ^ 2 * radialOrbital s ^ 2) = 1 := by
  have heq : (∫ s in Ioi (0 : ℝ), s ^ 2 * radialOrbital s ^ 2) =
      ∫ s in Ioi (0 : ℝ), radialDensity s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    exact fun s hs => radialOrbital_squared_density s hs
  rw [heq, radialDensity_normalized]

theorem radialOrbital_squared_integrable :
    IntegrableOn (fun s => s ^ 2 * radialOrbital s ^ 2) (Ioi (0 : ℝ)) := by
  apply radialDensity_integrable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (radialOrbital_squared_density s hs).symm

theorem radialOrbital_inverse_square_moment :
    (∫ s in Ioi (0 : ℝ), radialOrbital s ^ 2) = 2 / Real.sqrt 3 := by
  have heq : (∫ s in Ioi (0 : ℝ), radialOrbital s ^ 2) =
      ∫ s in Ioi (0 : ℝ), radialDensity s / s ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    change radialOrbital s ^ 2 = radialDensity s / s ^ 2
    rw [← radialOrbital_squared_density s hs]
    field_simp [ne_of_gt (show 0 < s from hs)]
  rw [heq, radial_inverse_square_moment, reciprocal_radial_moment]

end MagHK.Monopole

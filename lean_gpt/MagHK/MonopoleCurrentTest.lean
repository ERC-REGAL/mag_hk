import MagHK.MonopoleCurrent
import MagHK.MonopoleStationarity
import MagHK.MonopolePairLaw
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded

/-! Reduction of the actual stationary form identity to the scalar radial
distribution identity. Frame orthogonality and both Fubini steps are explicit. -/
noncomputable section
namespace MagHK.MonopoleCurrentTest
open MeasureTheory Set
open MagHK.MonopoleRealization MagHK.MonopoleTrial MagHK.MonopoleCurrent
open MagHK.MonopoleStationarity
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem radial_projection_pair (S : MagneticFormSystem) (φ : S.domain)
    (x y : Chart) (hx : x.2.1 ∈ Icc (-1 : ℝ) 1) :
    inner ℝ (MagHK.MonopoleQuadrature.direction x.2) (pairCurrent S φ (x, y)) =
      radialFluxComponent S φ 0 (x, y) := by
  change inner ℝ (frame 0 x) (pairCurrent S φ (x, y)) = _
  simp only [pairCurrent, inner_sum, real_inner_smul_right, frame_inner x hx]
  simp [radialFluxComponent]

theorem radial_projection_current (S : MagneticFormSystem) (φ : S.domain) :
    ∀ᵐ x ∂chartMeasure,
      inner ℝ (MagHK.MonopoleQuadrature.direction x.2) (current S φ x) =
        2 * ∫ y, radialFluxComponent S φ 0 (x, y) ∂chartMeasure := by
  have hi := (pairCurrent_integrable S φ).prod_right_ae
  filter_upwards [hi, Measure.quasiMeasurePreserving_snd.ae angle_ae] with x hx hangle
  simp only [current, real_inner_smul_right]
  congr 1
  rw [← integral_inner hx]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => radial_projection_pair S φ x y hangle)

theorem radial_stationary_test (S : MagneticFormSystem) (F : FermionSystem)
    (q : ℤ) (W : Chart × Chart → ℝ) (hS : MagneticFormFacts S F q W)
    (ψ : FermionState) (hψ : ψ ∈ F.domain) (E : ℝ)
    (heig : F.map ⟨ψ, hψ⟩ = E • ψ)
    (a : ℝ → ℝ)
    (hcurrent : let φ : S.domain := ⟨(ψ : PairState), hS.operator_domain ψ hψ⟩
      ∀ᵐ x ∂chartMeasure, current S φ x = a x.1 • MagHK.MonopoleQuadrature.direction x.2)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : Function.support χ ⊆ Ioi 0) :
    (∫ r in Ioi (0 : ℝ), deriv χ r * (r ^ 2 * a r)) = 0 := by
  let φ : S.domain := ⟨(ψ : PairState), hS.operator_domain ψ hψ⟩
  have hder : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := hcχ.deriv.exists_bound_of_continuous hder
  have hint : Integrable (fun p : Chart × Chart =>
      deriv χ p.1.1 * radialFluxComponent S φ 0 p) pairMeasure := by
    exact (component_integrable S φ 0).bdd_mul
      (hder.comp (continuous_fst.comp continuous_fst)).aestronglyMeasurable
        (ae_of_all _ (fun p => hC p.1.1))
  have hzero := radial_weak_continuity S F q W hS ψ hψ E heig χ hχ hcχ hsχ
  change (∫ p, deriv χ p.1.1 * radialFluxComponent S φ 0 p ∂pairMeasure) = 0 at hzero
  have hproj : ∀ᵐ x ∂chartMeasure,
      a x.1 = 2 * ∫ y, radialFluxComponent S φ 0 (x, y) ∂chartMeasure := by
    filter_upwards [radial_projection_current S φ, hcurrent,
      Measure.quasiMeasurePreserving_snd.ae angle_ae] with x hp hc hx
    rw [hc, real_inner_smul_right, real_inner_self_eq_norm_sq,
      MagHK.MonopoleQuadrature.direction_norm x.2 hx, one_pow, mul_one] at hp
    exact hp
  have hchart : (∫ x : Chart, deriv χ x.1 * a x.1 ∂chartMeasure) = 0 := by
    calc
      _ = 2 * ∫ x : Chart, deriv χ x.1 *
          (∫ y, radialFluxComponent S φ 0 (x, y) ∂chartMeasure) ∂chartMeasure := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hproj] with x hx
        rw [hx]
        ring
      _ = 2 * ∫ x : Chart, ∫ y, deriv χ x.1 * radialFluxComponent S φ 0 (x, y)
          ∂chartMeasure ∂chartMeasure := by simp_rw [integral_const_mul]
      _ = 2 * ∫ p, deriv χ p.1.1 * radialFluxComponent S φ 0 p ∂pairMeasure := by
        congr 1
        exact (integral_prod _ hint).symm
      _ = 0 := by rw [hzero, mul_zero]
  have hvol : (∫ _p : Angle, (1 : ℝ) ∂sphereMeasure) = 4 * Real.pi := by
    rw [integral_const, Measure.real, MagHK.MonopolePairLaw.sphereMeasure_univ,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.pi)]
    simp
  have he : (∫ x : Chart, deriv χ x.1 * a x.1 ∂chartMeasure) =
      (4 * Real.pi) * ∫ r in Ioi (0 : ℝ), deriv χ r * (r ^ 2 * a r) := by
    calc
      _ = (∫ r, deriv χ r * a r ∂radialVolume) *
          (∫ _p : Angle, (1 : ℝ) ∂sphereMeasure) := by
        simpa only [mul_one, chartMeasure] using integral_prod_mul
          (fun r => deriv χ r * a r) (fun _p : Angle => (1 : ℝ))
      _ = _ := by
        rw [hvol, radialVolume_integral, mul_comm]
        congr 1
        apply integral_congr_ae
        exact ae_of_all _ (fun _ => by ring)
  rw [he] at hchart
  exact (mul_eq_zero.mp hchart).resolve_left (by positivity)

end MagHK.MonopoleCurrentTest

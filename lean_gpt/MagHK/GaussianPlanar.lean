import MagHK.GaussianRealization
import MagHK.PlanarSpectralLibrary

/-! The concrete confining Gaussian planar construction, relative to the
universal standard planar operator library. The Cartesian coefficient
conditions and the confinement hypothesis are proved for the actual fields. -/
noncomputable section

namespace MagHK.GaussianPlanar
open MeasureTheory Set Filter
open MagHK.Noninteracting MagHK.RadialEndpoints MagHK.PartnerAsymptotics
open MagHK.Cartesian MagHK.GaussianDomains MagHK.GaussianRealization
open MagHK.PlanarSpectralLibrary

theorem gaussian_planar_coefficients (t : ℝ) (ht : 0 ≤ t) :
    PlanarCoefficients (gaussianA t) (scalar t) (gaussianVector t) (gaussianScalar t) := by
  refine ⟨gaussianVector_contDiff t ht, gaussianScalar_contDiff t ht,
    ⟨t + 1, gaussianVector_bound t ht⟩, gaussianVector_origin t, ?_, ?_, ?_⟩
  · simp only [gaussianScalar, radiusSq, scalar, zero_pow (by norm_num : 2 ≠ 0),
      zero_add, mul_zero]
  · intro r p hr hp
    have hc : gaussianCoefficient t p = gaussianA t r / r :=
      (eq_div_iff hr.ne').2 (gaussianCoefficient_radial t r p hp)
    simp only [gaussianVector, hc]
  · intro r p _ hp
    simp only [gaussianScalar, scalar, hp]

theorem gaussian_scalar_tendsto_atTop (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (scalar t) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (max 1 (b + 2 + 2 * t))] with r hr
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrb : b + 2 + 2 * t ≤ r := (le_max_right _ _).trans hr
  have h := gaussianScalar_quadratic_lower_bound t r ht
  change b ≤ r ^ 2 - 2 / (1 + t * r ^ 2) - 2 * t / (1 + t * r ^ 2) ^ 2
  nlinarith

/-- Both simple levels and their strict upper gap for the actual planar
operator supplied by the universal confining realization theorem. -/
theorem gaussian_planar_realization (library : StandardPlanarLibrary)
    (t : ℝ) (ht : 0 < t) :
    ∃ S : System,
      Facts S (gaussianA t) (scalar t) (gaussianU t) (gaussianVector t) (gaussianScalar t) ∧
      (∀ E, E ∈ S.spectrum ∧ E ≤ 2 ↔ E = 0 ∨ E = 2) ∧
      S.multiplicity 0 = 1 ∧ S.multiplicity 2 = 1 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ E, 2 < E → E < 2 + ε → E ∉ S.spectrum := by
  obtain ⟨S, hS, hs⟩ := library.confining (gaussianA t) (scalar t) (gaussianU t)
    (gaussianVector t) (gaussianScalar t) (gaussian_coefficients t ht)
    (gaussian_planar_coefficients t ht.le) (gaussian_scalar_tendsto_atTop t ht.le)
  exact ⟨S, hS, gaussian_planar_levels t ht S.radial hS.radial_facts
    S.spectrum S.multiplicity 3 (by norm_num) (hs 3)⟩

end MagHK.GaussianPlanar

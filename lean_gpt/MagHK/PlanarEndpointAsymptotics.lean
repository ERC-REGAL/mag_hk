import MagHK.RadialEndpoints
import MagHK.PartnerAsymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The two local Frobenius branches in the planar factorization appendix.
The only input is a uniform regular-singular ODE theorem for every smooth
coefficient U vanishing at zero and every real energy. -/
noncomputable section
namespace MagHK.PlanarEndpointAsymptotics
open Filter Set MeasureTheory
open scoped Topology ContDiff

def expression (partner : Bool) (U u : ℝ → ℝ) (r : ℝ) : ℝ :=
  -deriv (deriv u) r - deriv u r / r +
    ((if partner then 1 / r ^ 2 + deriv U r else -deriv U r) +
      U r ^ 2 - U r / r) * u r

def Solution (partner : Bool) (U : ℝ → ℝ) (E : ℝ) (u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Ioo 0 1) ∧
    ∀ r, 0 < r → r < 1 → expression partner U u r = E * u r

def LocalSquareIntegrable (u : ℝ → ℝ) : Prop :=
  IntegrableOn (fun r => u r ^ 2 * r) (Ioo 0 1)

structure Branches (U : ℝ → ℝ) (E : ℝ) where
  regular : ℝ → ℝ
  logarithmic : ℝ → ℝ
  partnerRegular : ℝ → ℝ
  partnerSingular : ℝ → ℝ
  regular_solution : Solution false U E regular
  logarithmic_solution : Solution false U E logarithmic
  partnerRegular_solution : Solution true U E partnerRegular
  partnerSingular_solution : Solution true U E partnerSingular
  regular_limit : Tendsto regular (𝓝[>] 0) (𝓝 1)
  regular_derivative : Tendsto (fun r => r * deriv regular r) (𝓝[>] 0) (𝓝 0)
  logarithmic_limit : Tendsto (fun r => logarithmic r / Real.log r) (𝓝[>] 0) (𝓝 1)
  logarithmic_derivative : Tendsto (fun r => r * deriv logarithmic r) (𝓝[>] 0) (𝓝 1)
  partnerRegular_limit : Tendsto (fun r => partnerRegular r / r) (𝓝[>] 0) (𝓝 1)
  partnerRegular_derivative : Tendsto (deriv partnerRegular) (𝓝[>] 0) (𝓝 1)
  partnerSingular_limit : Tendsto (fun r => r * partnerSingular r) (𝓝[>] 0) (𝓝 1)
  partnerSingular_derivative :
    Tendsto (fun r => r ^ 2 * deriv partnerSingular r) (𝓝[>] 0) (𝓝 (-1))
  zero_wronskian : ∀ r, 0 < r → r < 1 →
    r * (regular r * deriv logarithmic r - deriv regular r * logarithmic r) = 1
  partner_wronskian : ∀ r, 0 < r → r < 1 →
    r * (partnerRegular r * deriv partnerSingular r -
      deriv partnerRegular r * partnerSingular r) = -2
  regular_L2 : LocalSquareIntegrable regular
  logarithmic_L2 : LocalSquareIntegrable logarithmic
  regular_energy : IntegrableOn (fun r => (deriv regular r) ^ 2 * r) (Ioo 0 1)
  logarithmic_energy : ¬ IntegrableOn (fun r => (deriv logarithmic r) ^ 2 * r) (Ioo 0 1)
  partnerRegular_L2 : LocalSquareIntegrable partnerRegular
  partnerSingular_not_L2 : ¬ LocalSquareIntegrable partnerSingular

/-- Uniform smooth regular-singular Sturm–Liouville theory. No coefficient,
energy, eigenstate, or boundary conclusion from either example is assumed. -/
def StandardPlanarFrobeniusLibrary : Prop :=
  ∀ U : ℝ → ℝ, ContDiff ℝ ∞ U → U 0 = 0 →
    ∀ E : ℝ, Nonempty (Branches U E)

theorem gaussian_branches (library : StandardPlanarFrobeniusLibrary)
    (t E : ℝ) (ht : 0 ≤ t) : Nonempty (Branches (MagHK.RadialEndpoints.gaussianU t) E) :=
  library _ ((MagHK.PartnerAsymptotics.gaussianU_contDiff t ht).of_le le_top)
    (MagHK.RadialEndpoints.gaussianU_at_zero t) E

theorem bounded_branches (library : StandardPlanarFrobeniusLibrary)
    (t E : ℝ) (ht : 0 ≤ t) : Nonempty (Branches (MagHK.Noninteracting.profileU t) E) :=
  library _ ((MagHK.RadialEndpoints.profileU_contDiff t ht).of_le le_top)
    (MagHK.RadialEndpoints.profileU_at_zero t) E

end MagHK.PlanarEndpointAsymptotics

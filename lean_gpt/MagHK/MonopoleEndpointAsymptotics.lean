import MagHK.MonopoleEndpointDomains

/-! Exact asymptotic content of the standard singular-oscillator endpoint
input. This supplements the domain and solution-space dimension theorem.
The input is uniform in every nonnegative index and every real spectral
parameter. No monopole charge, selected angular sector or chosen ground
state occurs in it.
-/
noncomputable section
namespace MagHK.MonopoleEndpointAsymptotics
open MeasureTheory Set Filter
open MagHK.MonopoleEndpointDomains
open scoped ContDiff Topology

/-- The ordinary Wronskian of two actual scalar functions. -/
def wronskian (u v : ℝ → ℂ) (r : ℝ) : ℂ :=
  u r * deriv v r - deriv u r * v r

/-- Actual classical solutions of the singular-oscillator equation. -/
def Solution (ell E : ℝ) (u : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ 2 u (Ioi 0) ∧ ∀ r, 0 < r →
    expression (ell * (ell + 1)) u r = (E : ℂ) * u r

/-- Frobenius and large-radius asymptotics for the full singular oscillator.
The origin limits remain valid at resonant indices, where lower-order
logarithmic terms may be present in the nonprincipal solution. -/
structure AsymptoticBasis (ell E : ℝ) where
  principal : ℝ → ℂ
  singular : ℝ → ℂ
  decaying : ℝ → ℂ
  growing : ℝ → ℂ
  principal_solution : Solution ell E principal
  singular_solution : Solution ell E singular
  decaying_solution : Solution ell E decaying
  growing_solution : Solution ell E growing
  origin_independent : wronskian principal singular 1 ≠ 0
  infinity_independent : wronskian decaying growing 1 ≠ 0
  principal_origin : Tendsto (fun r => principal r / (r ^ (ell + 1) : ℝ))
    (𝓝[>] 0) (𝓝 1)
  principal_derivative : Tendsto (fun r => deriv principal r / (r ^ ell : ℝ))
    (𝓝[>] 0) (𝓝 (ell + 1 : ℝ))
  singular_origin : Tendsto (fun r => singular r / (r ^ (-ell) : ℝ))
    (𝓝[>] 0) (𝓝 1)
  singular_derivative : Tendsto (fun r => deriv singular r / (r ^ (-ell - 1) : ℝ))
    (𝓝[>] 0) (𝓝 (-ell : ℝ))
  decaying_infinity : Tendsto
    (fun r => decaying r / (r ^ ((E - 1) / 2) * Real.exp (-r ^ 2 / 2) : ℝ))
    atTop (𝓝 1)
  growing_infinity : Tendsto
    (fun r => growing r / (r ^ (-(E + 1) / 2) * Real.exp (r ^ 2 / 2) : ℝ))
    atTop (𝓝 1)
  principal_local_L2 : MemLp principal 2 (volume.restrict (Ioo 0 1))
  singular_local_L2 : MemLp singular 2 (volume.restrict (Ioo 0 1)) ↔ ell < 1 / 2
  decaying_L2 : MemLp decaying 2 (volume.restrict (Ioi 1))
  growing_not_L2 : ¬MemLp growing 2 (volume.restrict (Ioi 1))
  /-- The singular Frobenius branch has infinite energy whenever ell > 0.
  The strict inequality is necessary, since at ell = 0 a nonzero constant
  branch need not have infinite derivative energy. -/
  singular_infinite_energy : 0 < ell → ¬IntegrableOn
    (fun r => ‖deriv singular r‖ ^ 2 + (ell * (ell + 1) / r ^ 2) * ‖singular r‖ ^ 2)
    (Ioo 0 1)

/-- Standard regular-singular and irregular-singular ODE asymptotics. The
four displayed limits and their L²/form consequences are explicit above. -/
def StandardOscillatorAsymptoticsLibrary : Prop :=
  ∀ ell E : ℝ, 0 ≤ ell → Nonempty (AsymptoticBasis ell E)

/-- Both independent origin behaviors and both independent infinity
behaviors for every actual monopole angular sector, with either charge. -/
theorem monopole_asymptotic_basis (lib : StandardOscillatorAsymptoticsLibrary)
    (q : ℤ) (k : ℕ) (E : ℝ) (hc : 0 ≤ angularCoefficient q k) :
    Nonempty (AsymptoticBasis (radialIndex q k) E) := by
  apply lib
  unfold radialIndex
  have hs : 1 ≤ Real.sqrt (1 + 4 * angularCoefficient q k) := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    nlinarith
  linarith

/-- In particular, the two actual twice-charge-one sectors used in the
counterexample have the same endpoint asymptotic basis conclusions. -/
theorem opposite_asymptotic_basis (lib : StandardOscillatorAsymptoticsLibrary)
    (k : ℕ) (E : ℝ) :
    Nonempty (AsymptoticBasis (radialIndex 1 k) E) ∧
      Nonempty (AsymptoticBasis (radialIndex (-1) k) E) := by
  have h := monopole_asymptotic_basis lib 1 k E (coefficient_one_nonneg k)
  exact ⟨h, by simpa only [index_opposite] using h⟩

end MagHK.MonopoleEndpointAsymptotics
